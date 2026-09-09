import Erlean.Semantics.Machine

/-!
An explicit single-node actor profile. Scheduling, signal delivery, and logical
milliseconds are supplied by choices; no fairness or wall-clock equivalence is
implicit. Ordinary messages, asynchronous local links, process monitors, and exit
signals are supported without trap_exit. Registered names, priority signals,
distribution, monitor options, exit_signal/2, and stacktrace-bearing termination
notifications remain unsupported. Timeout readiness is checked on a process
step, with an available mailbox entry preferred over timeout, matching the
receive wait interface rather than claiming a real-time scheduler model.
The discarded recv_next/remove_message result is represented by atom ok as an
internal unit convention; arbitrary Core observing that result is outside scope.
Simultaneous opposite-endpoint link establishment is rejected explicitly rather
than approximating OTP's full link handshake. Link/unlink generations suppress
stale in-flight effects, including a link request not yet activated at its target.
-/

namespace Erlean.Runtime

open Core Semantics

inductive ProcessStatus where
  | running
  | waiting
  | finished (outcome : Outcome)
  deriving Repr, BEq

structure Process where
  pid : Nat
  state : LocalState
  mailbox : Values := []
  cursor : Nat := 0
  deadline : Option Nat := none
  status : ProcessStatus := .running
  deriving Repr, BEq

inductive SignalKind where
  | message
  | exit (linkId : Option Nat) (selfNormal : Bool)
  | down (reference : Nat)
  | monitor (reference : Nat)
  | demonitor (reference : Nat)
  | link (id : Nat)
  | unlink (id : Nat)
  deriving Repr, BEq

structure Signal where
  id : Nat
  sender : Nat
  recipient : Nat
  message : Value
  kind : SignalKind := .message
  deriving Repr, BEq

structure Monitor where
  reference : Nat
  owner : Nat
  target : Nat
  enabled : Bool := true
  registered : Bool := false
  deriving Repr, BEq

/-- Each endpoint activates independently. IDs distinguish stale exit/unlink
    signals from a later link between the same pair. -/
structure Link where
  id : Nat
  left : Nat
  right : Nat
  leftActive : Bool := true
  rightActive : Bool := false
  leftCancelled : Bool := false
  rightCancelled : Bool := false
  deriving Repr, BEq

def Link.active (link : Link) (pid : Nat) : Bool :=
  (link.left == pid && link.leftActive) || (link.right == pid && link.rightActive)

def Link.peer (link : Link) (pid : Nat) : Nat :=
  if link.left == pid then link.right else link.left

def Link.setActive (link : Link) (pid : Nat) (active : Bool) : Link :=
  if link.left == pid then { link with leftActive := active, leftCancelled := !active }
  else if link.right == pid then { link with rightActive := active, rightCancelled := !active }
  else link

def Link.activate (link : Link) (pid : Nat) : Link :=
  if (link.left == pid && link.leftCancelled) || (link.right == pid && link.rightCancelled) then link
  else link.setActive pid true

def Link.connects (link : Link) (first second : Nat) : Bool :=
  (link.left == first && link.right == second) || (link.left == second && link.right == first)

structure System where
  processes : List Process
  pending : List Signal := []
  now : Nat := 0
  nextPid : Nat := 1
  nextReference : Nat := 0
  nextSignal : Nat := 0
  nextLink : Nat := 0
  links : List Link := []
  monitors : List Monitor := []
  deriving Repr, BEq

inductive Choice where
  | run (pid : Nat)
  | deliver (signalId : Nat)
  | advanceTime (to : Nat)
  deriving Repr, BEq, DecidableEq

inductive ChoiceError where
  | unknownProcess
  | finishedProcess
  | blockedProcess
  | unknownSignal
  | signalOrder
  | timeMustIncrease
  | invalidFreshIdentity
  | modelFault
  deriving Repr, BEq, DecidableEq

def System.lookup (system : System) (pid : Nat) : Option Process :=
  system.processes.find? (fun process => process.pid == pid)

def System.update (system : System) (process : Process) : System :=
  { system with processes := system.processes.map fun old =>
      if old.pid == process.pid then process else old }

def System.alive (system : System) (pid : Nat) : Bool :=
  match system.lookup pid with
  | none => false
  | some process => match process.status with
    | .finished _ => false
    | _ => true

def System.enqueue (system : System) (sender recipient : Nat) (kind : SignalKind)
    (message : Value := .nil) : System :=
  { system with
    pending := system.pending ++ [{ id := system.nextSignal, sender, recipient, message, kind }]
    nextSignal := system.nextSignal + 1 }

/-- Runtime model faults do not become Erlang process death notifications. Error
    and throw termination need stacktraces if another process observes the reason. -/
def finishProcess (system : System) (process : Process) (outcome : Outcome) : System := Id.run do
  let notifyLinks := system.links.filter (fun link => link.active process.pid)
  let notifyMonitors := system.monitors.filter (fun monitor =>
    monitor.target == process.pid && monitor.registered)
  let reason : Option Value := match outcome with
    | .returned _ => some (.atom "normal")
    | .raised ⟨.exit, reason⟩ => some reason
    | _ => none
  let outcome := if reason.isNone && (!notifyLinks.isEmpty || !notifyMonitors.isEmpty) then
      match outcome with
      | .fault _ => outcome
      | _ => .fault (.unsupported "Observed process termination requires stacktrace semantics")
    else outcome
  let mut updated := system.update { process with status := .finished outcome }
  match reason with
  | none => return updated
  | some reason =>
    for link in notifyLinks do
      updated := updated.enqueue process.pid (link.peer process.pid) (.exit (some link.id) false) reason
    for monitor in notifyMonitors do
      updated := updated.enqueue process.pid monitor.owner (.down monitor.reference) reason
    updated := { updated with
      links := updated.links.map (fun link => link.setActive process.pid false)
      monitors := updated.monitors.map fun monitor =>
        if monitor.target == process.pid then { monitor with registered := false }
        else if monitor.owner == process.pid then { monitor with enabled := false, registered := false }
        else monitor }
    return updated

def returnValues (process : Process) (values : Values) : Process :=
  { process with state := { process.state with control := .ret values }, status := .running }

def raiseReason (process : Process) (reason : String) : Process :=
  { process with
    state := { process.state with control := .raise ⟨.error, .atom reason⟩ }
    status := .running }

def unsupportedProcess (process : Process) (operation : String) : Process :=
  { process with status := .finished (.fault (.unsupported operation)) }

def decodeList : Value → Option Values
  | .nil => some []
  | .cons head tail => (decodeList tail).map (head :: ·)
  | _ => none

/-- A valid finite timeout is an unsigned 32-bit millisecond interval. -/
def decodeTimeout : Value → Option (Option Nat)
  | .atom "infinity" => some none
  | .integer (.ofNat value) => if value ≤ 4294967295 then some (some value) else none
  | _ => none

def request (world : CodeWorld) (system : System) (process : Process)
    (name : String) (args : Values) : Except ChoiceError System := do
  let ret (values : Values) := system.update (returnValues process values)
  let badarg := system.update (raiseReason process "badarg")
  if !Value.publicList args then
    return system.update (unsupportedProcess process "Actor observation of opaque exception information")
  match name, args with
  | "self", [] => return ret [.pid process.pid]
  | "make_ref", [] =>
    return { (ret [.reference system.nextReference]) with nextReference := system.nextReference + 1 }
  | "monitor", [.atom "process", .pid target] =>
    let reference := system.nextReference
    let monitor : Monitor := { reference, owner := process.pid, target }
    let updated := { (ret [.reference reference]) with
      monitors := system.monitors ++ [monitor], nextReference := reference + 1 }
    return updated.enqueue process.pid target (.monitor reference)
  | "monitor", [.atom "process", .atom _]
  | "monitor", [.atom "process", .tuple _] =>
    return system.update (unsupportedProcess process "Registered or distributed process monitor")
  | "monitor", [.atom "port", _] | "monitor", [.atom "time_offset", _] =>
    return system.update (unsupportedProcess process "Non-process monitor")
  | "monitor", [_, _] => return badarg
  | "demonitor", [.reference reference] =>
    match system.monitors.find? (fun monitor => monitor.reference == reference) with
    | none => return ret [.atom "true"]
    | some monitor =>
      if monitor.owner != process.pid then return badarg
      let updated := { (ret [.atom "true"]) with
        monitors := system.monitors.map fun (entry : Monitor) =>
          if entry.reference == reference then { entry with enabled := false } else entry }
      return updated.enqueue process.pid monitor.target (.demonitor reference)
  | "demonitor", [_] => return badarg
  | "link", [.pid target] =>
    if !system.alive target then return system.update (raiseReason process "noproc")
    if target == process.pid || system.links.any (fun link =>
        link.active process.pid && link.peer process.pid == target) then return ret [.atom "true"]
    if system.links.any (fun link => link.connects process.pid target && link.active target) then
      return system.update (unsupportedProcess process "Concurrent link establishment outside lifecycle profile")
    let link : Link := { id := system.nextLink, left := process.pid, right := target }
    let updated := { (ret [.atom "true"]) with
      links := system.links ++ [link], nextLink := system.nextLink + 1 }
    return updated.enqueue process.pid target (.link link.id)
  | "link", [_] => return badarg
  | "unlink", [.pid target] =>
    let links := system.links.filter (fun link => link.connects process.pid target)
    let mut updated := ret [.atom "true"]
    for link in links do
      updated := updated.enqueue process.pid target (.unlink link.id)
    return { updated with
      links := updated.links.map fun link =>
        if links.any (fun old => old.id == link.id) then link.setActive process.pid false else link }
  | "unlink", [_] => return badarg
  | "exit", [.pid target, reason] =>
    if target == process.pid then
      let reason := if reason == .atom "kill" then Value.atom "killed" else reason
      return finishProcess system process (.raised ⟨.exit, reason⟩)
    return (ret [.atom "true"]).enqueue process.pid target (.exit none false) reason
  | "exit", [_, _] => return badarg
  | "spawn", [.atom moduleName, .atom functionName, argumentList] =>
    let some arguments := decodeList argumentList | return badarg
    unless world.any (fun mod => mod.name == moduleName) do
      return system.update (unsupportedProcess process s!"unlinked spawn module {moduleName}")
    if (system.lookup system.nextPid).isSome then throw .invalidFreshIdentity
    let child : Process := {
      pid := system.nextPid
      state := initialCall moduleName functionName arguments }
    let updated := ret [.pid system.nextPid]
    return { updated with processes := updated.processes ++ [child], nextPid := system.nextPid + 1 }
  | "spawn", [_, _, _] => return badarg
  | "send", [.pid recipient, message] =>
    if system.pending.any (fun signal => signal.id == system.nextSignal) then
      throw .invalidFreshIdentity
    let signal : Signal := {
      id := system.nextSignal
      sender := process.pid
      recipient := recipient
      message := message }
    return { (ret [message]) with
      pending := system.pending ++ [signal]
      nextSignal := system.nextSignal + 1 }
  | "send", [.atom _, _] | "send", [.tuple _, _] =>
    return system.update (unsupportedProcess process "Registered or distributed send destination")
  | "send", [_, _] => return badarg
  | "recv_peek_message", [] =>
    match process.mailbox[process.cursor]? with
    | some message => return ret [.atom "true", message]
    | none => return ret [.atom "false", .atom "undefined"]
  | "recv_next", [] =>
    if process.cursor < process.mailbox.length then
      return system.update (returnValues { process with cursor := process.cursor + 1 } [.atom "ok"])
    else return system.update { process with
      status := .finished (.fault (.invalid "Receive cursor has no message to skip")) }
  | "remove_message", [] =>
    if process.cursor < process.mailbox.length then
      let mailbox := process.mailbox.take process.cursor ++ process.mailbox.drop (process.cursor + 1)
      return system.update (returnValues {
        process with mailbox := mailbox, cursor := 0, deadline := none } [.atom "ok"])
    else return system.update { process with
      status := .finished (.fault (.invalid "Receive cursor has no message to remove")) }
  | "recv_wait_timeout", [timeout] =>
    let some duration := decodeTimeout timeout
      | return system.update (raiseReason process "timeout_value")
    let deadline := match process.deadline, duration with
      | some deadline, _ => some deadline
      | none, some milliseconds => some (system.now + milliseconds)
      | none, none => none
    if process.cursor < process.mailbox.length then
      return system.update (returnValues { process with deadline := deadline } [.atom "false"])
    else if deadline.any (fun deadline => deadline ≤ system.now) then
      return system.update (returnValues { process with cursor := 0, deadline := none } [.atom "true"])
    else if process.status == .waiting then throw .blockedProcess
    else return system.update { process with deadline := deadline, status := .waiting }
  | _, _ => return system.update (unsupportedProcess process s!"runtime {name}/{args.length}")

/-- Signal handlers preserve endpoint-local unlink/demonitor suppression. -/
def handleSignal (system : System) (signal : Signal) : System :=
  match signal.kind with
  | .monitor reference =>
    match system.monitors.find? (fun monitor => monitor.reference == reference) with
    | none => system
    | some monitor =>
      if system.alive signal.recipient then
        { system with monitors := system.monitors.map fun entry =>
          if entry.reference == reference then { entry with registered := true } else entry }
      else system.enqueue signal.recipient monitor.owner (.down reference) (.atom "noproc")
  | .demonitor reference =>
    { system with monitors := system.monitors.map fun monitor =>
      if monitor.reference == reference then { monitor with registered := false } else monitor }
  | .link id =>
    if system.alive signal.recipient then
      { system with links := system.links.map fun link =>
        if link.id == id then link.activate signal.recipient else link }
    else system.enqueue signal.recipient signal.sender (.exit (some id) false) (.atom "noproc")
  | .unlink id =>
    { system with links := system.links.map fun link =>
      if link.id == id then link.setActive signal.recipient false else link }
  | .down reference =>
    match system.lookup signal.recipient with
    | none => system
    | some process =>
      if !(system.alive process.pid) || !(system.monitors.any (fun monitor =>
          monitor.reference == reference && monitor.owner == process.pid && monitor.enabled)) then system
      else
        let message := Value.tuple [.atom "DOWN", .reference reference, .atom "process",
          .pid signal.sender, signal.message]
        let updated := system.update { process with mailbox := process.mailbox ++ [message] }
        { updated with monitors := updated.monitors.map fun monitor =>
          if monitor.reference == reference then { monitor with enabled := false } else monitor }
  | .message =>
    match system.lookup signal.recipient with
    | none => system
    | some process =>
      if system.alive process.pid then
        system.update { process with mailbox := process.mailbox ++ [signal.message] }
      else system
  | .exit linkId selfNormal =>
    match system.lookup signal.recipient with
    | none => system
    | some process =>
      if !(system.alive process.pid) then system
      else
        let active := match linkId with
          | none => true
          | some id => system.links.any (fun link => link.id == id && link.active process.pid)
        if !active then system
        else
          let updated := match linkId with
            | none => system
            | some id => { system with links := system.links.map fun link =>
                if link.id == id then link.setActive process.pid false else link }
          if signal.message == .atom "normal" && !selfNormal then updated
          else
            let reason := if linkId.isNone && signal.message == .atom "kill" then
                Value.atom "killed" else signal.message
            finishProcess updated process (.raised ⟨.exit, reason⟩)

/-- FIFO applies across every signal kind for a sender-recipient pair. -/
def deliver (system : System) (signalId : Nat) : Except ChoiceError System := do
  let some signal := system.pending.find? (fun signal => signal.id == signalId)
    | throw .unknownSignal
  let earlier := system.pending.takeWhile (fun signal => signal.id != signalId)
  if earlier.any (fun prior => prior.sender == signal.sender && prior.recipient == signal.recipient) then
    throw .signalOrder
  let remaining := { system with pending := system.pending.filter (fun signal => signal.id != signalId) }
  return handleSignal remaining signal

def stepSystem (world : CodeWorld) (system : System) (choice : Choice) :
    Except ChoiceError System := do
  if system.processes.any (fun process => match process.status with
      | .finished (.fault _) => true
      | _ => false) then throw .modelFault
  match choice with
  | .advanceTime to =>
    if system.now < to then return { system with now := to }
    else throw .timeMustIncrease
  | .deliver signalId => deliver system signalId
  | .run pid =>
    let some process := system.lookup pid | throw .unknownProcess
    match process.status with
    | .finished _ => throw .finishedProcess
    | _ =>
      match process.state.control with
      | .runtime name args => request world system process name args
      | _ =>
        if process.status == .waiting then throw .blockedProcess
        match stepLocal world process.state with
        | .next state => return system.update { process with state := state }
        | .halt outcome => return finishProcess system process outcome

def initialSystem (moduleName functionName : String) (arguments : Values) : System :=
  { processes := [{ pid := 0, state := initialCall moduleName functionName arguments }] }

/-- Execute a supplied schedule; an invalid choice never becomes a process error. -/
def replay (world : CodeWorld) : System → List Choice → Except ChoiceError System
  | system, [] => .ok system
  | system, choice :: rest => do replay world (← stepSystem world system choice) rest

end Erlean.Runtime
