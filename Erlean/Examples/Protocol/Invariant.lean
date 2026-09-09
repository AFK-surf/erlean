import Erlean.Examples.Protocol.Basic
import Erlean.Examples.Protocol.Phases
import Erlean.Logic.Segment

/-!
State predicate and structural components of the closed-exchange proof. The network lemmas below
prove preservation by every accepted ordinary-message delivery, independently of
the chosen scheduler. Pure local intervals cover intermediate continuation states.
Runtime preservation and the complete schedule induction are separate modules.
-/

namespace Erlean.Examples.ProtocolInvariant

open Core Semantics Erlean.Runtime Erlean.Examples.Protocol Erlean.Logic

/-- A local interval has no hidden runtime action: it uses the same local runner
    as the system stepper, which faults if asked to cross a runtime suspension. -/
def LocalInterval (world : CodeWorld) (endpoint current : LocalState) : Prop :=
  ReachesBoundary (stepLocal world) current endpoint

theorem localInterval_endpoint (world : CodeWorld) (endpoint : LocalState) :
    LocalInterval world endpoint endpoint := ⟨0, rfl⟩

theorem localInterval_next
    (interval : LocalInterval world endpoint current)
    (beforeEndpoint : current ≠ endpoint)
    (stepped : stepLocal world current = .next next) :
    LocalInterval world endpoint next := by
  obtain ⟨remaining, reaches⟩ := interval
  cases remaining with
  | zero =>
    have equal : current = endpoint := by simpa [runLocal, run] using reaches
    exact False.elim (beforeEndpoint equal)
  | succ remaining =>
    exact ⟨remaining, by simpa [runLocal, run, stepped] using reaches⟩

/-- An interval cannot terminate before reaching its designated boundary. -/
theorem localInterval_no_halt
    (interval : LocalInterval world endpoint current)
    (beforeEndpoint : current ≠ endpoint) :
    stepLocal world current ≠ .halt outcome := by
  intro halted
  obtain ⟨remaining, reaches⟩ := interval
  cases remaining with
  | zero =>
    have equal : current = endpoint := by simpa [runLocal, run] using reaches
    exact beforeEndpoint equal
  | succ remaining => simp [run, halted] at reaches

def AllowedMailbox (client server reference : Nat) (payload : Value)
    (recipient : Nat) (message : Value) : Prop :=
  (recipient = server ∧
    (message = requestPayload client reference payload ∨ message = .atom "stop")) ∨
  (recipient = client ∧ message = replyPayload reference payload)

def MailboxesRespect (allowed : Nat → Value → Prop) (system : System) : Prop :=
  ∀ process ∈ system.processes, ∀ message ∈ process.mailbox, allowed process.pid message

def PendingRespect (allowed : Nat → Value → Prop) (system : System) : Prop :=
  ∀ signal ∈ system.pending, signal.kind = .message ∧ allowed signal.recipient signal.message

def NetworkRespect (allowed : Nat → Value → Prop) (system : System) : Prop :=
  MailboxesRespect allowed system ∧ PendingRespect allowed system

theorem initial_network (allowed : Nat → Value → Prop) (payload : Value) :
    NetworkRespect allowed (initialSystem "actor_protocol" "exchange" [payload]) := by
  simp [NetworkRespect, MailboxesRespect, PendingRespect, initialSystem]

theorem mailboxes_update (previous : MailboxesRespect allowed system)
    (replacementValid : ∀ message ∈ replacement.mailbox, allowed replacement.pid message) :
    MailboxesRespect allowed (system.update replacement) := by
  intro process member message queued
  obtain ⟨old, oldMember, replaced⟩ := List.mem_map.mp member
  by_cases same : (old.pid == replacement.pid) = true
  · have equal : replacement = process := by simpa [same] using replaced
    subst process
    simp [same] at queued ⊢
    exact replacementValid message queued
  · have equal : old = process := by simpa [same] using replaced
    subst process
    simp [same] at queued ⊢
    exact previous old oldMember message queued

/-- Ordinary delivery appends the exact queued payload. It changes neither the
    recipient's local continuation nor the other processes' mailbox contents. -/
theorem handle_message_network
    (previous : NetworkRespect allowed system)
    (ordinary : signal.kind = .message)
    (messageValid : allowed signal.recipient signal.message) :
    NetworkRespect allowed (handleSignal system signal) := by
  cases found : system.lookup signal.recipient with
  | none => simpa [handleSignal, ordinary, found] using previous
  | some process =>
    by_cases alive : system.alive process.pid = true
    · have member : process ∈ system.processes :=
        List.mem_of_find?_eq_some found
      have identity : process.pid = signal.recipient := by
        have selected := List.find?_some found
        simpa using selected
      have updated : MailboxesRespect allowed
          (system.update { process with mailbox := process.mailbox ++ [signal.message] }) := by
        apply mailboxes_update previous.1
        intro message queued
        rcases List.mem_append.mp queued with original | appended
        · exact previous.1 process member message original
        · have equal : message = signal.message := by simpa using appended
          subst message
          simpa [identity] using messageValid
      have pending : PendingRespect allowed
          (system.update { process with mailbox := process.mailbox ++ [signal.message] }) :=
        previous.2
      simpa [NetworkRespect, handleSignal, ordinary, found, alive] using And.intro updated pending
    · simpa [handleSignal, ordinary, found, alive] using previous

/-- Queue filtering preserves every message's established provenance. -/
theorem network_filter (previous : NetworkRespect allowed system) (keep : Signal → Bool) :
    NetworkRespect allowed { system with pending := system.pending.filter keep } := by
  refine ⟨previous.1, ?_⟩
  intro signal member
  exact previous.2 signal (List.mem_filter.mp member).1

/-- This preservation result quantifies over every accepted delivery choice.
    It assumes the concrete network property before delivery, not an invariant
    preservation premise or a selected deterministic scheduler. -/
theorem deliver_network (previous : NetworkRespect allowed system)
    (accepted : deliver system signalId = .ok next) : NetworkRespect allowed next := by
  cases found : system.pending.find? (fun signal => signal.id == signalId) with
  | none => simp [deliver, found] at accepted
  | some signal =>
    have valid := previous.2 signal (List.mem_of_find?_eq_some found)
    by_cases blocked : (system.pending.takeWhile (fun entry => entry.id != signalId)).any
        (fun prior => prior.sender == signal.sender && prior.recipient == signal.recipient) = true
    · simp [deliver, found, blocked, Functor.map, Except.map] at accepted
    · have equal : handleSignal
          { system with pending := system.pending.filter (fun entry => entry.id != signalId) }
          signal = next := by
        simpa [deliver, found, blocked, Pure.pure, Except.pure, Functor.map, Except.map] using accepted
      rw [← equal]
      exact handle_message_network (network_filter previous _) valid.1 valid.2

theorem time_network (previous : NetworkRespect allowed system) (to : Nat) :
    NetworkRespect allowed { system with now := to } := previous

/-- The endpoint is the actual imported server's send suspension; the known
    17-step local segment supplies a concrete inhabitant of this phase. -/
def ServerSending (client reference : Nat) (payload : Value) (process : Process) : Prop :=
  ∃ context stack,
    context.moduleName = "actor_protocol" ∧
    context.env.lookup 3 = some (.pid client) ∧
    context.env.lookup 4 = some (.reference reference) ∧
    context.env.lookup 5 = some payload ∧
    LocalInterval [importedActorProtocolModule]
      {
        control := .runtime "send" [.pid client, replyPayload reference payload]
        context := context
        stack := .seq context (.apply (.funRef "server" 0) []) :: stack }
      process.state

/-- The client segment keeps its original continuation, so it can subsequently
    send the server's stop message and return to the exchange entry point. -/
def ClientReturning (payload : Value) (process : Process) : Prop :=
  ∃ context stack,
    context.moduleName = "actor_protocol" ∧
    context.env.lookup 12 = some payload ∧
    LocalInterval [importedActorProtocolModule]
      { control := .ret [.tuple [.atom "ok", payload]], context, stack }
      process.state

/-- The imported server's checked prefix supplies the interval immediately after
    successful mailbox removal; the interval includes every intermediate frame. -/
theorem server_sending_after_remove (context : Context) (stack : List Frame)
    (client reference : Nat) (payload : Value) (pid : Nat)
    (moduleName : context.moduleName = "actor_protocol")
    (clientBound : context.env.lookup 3 = some (.pid client))
    (referenceBound : context.env.lookup 4 = some (.reference reference))
    (payloadBound : context.env.lookup 5 = some payload)
    (publicPayload : payload.isPublic = true) :
    ServerSending client reference payload {
      pid := pid
      state := {
        control := .ret [.atom "ok"]
        context := context
        stack := .seq context serverAfterRemoveBody :: stack } } := by
  refine ⟨context, stack, moduleName, clientBound, referenceBound, payloadBound, 17, ?_⟩
  exact server_send_prefix [importedActorProtocolModule] context stack client reference payload
    clientBound referenceBound payloadBound publicPayload

/-- Every actual pure step preserves the server send phase, independently of
    steps or message deliveries taken by the other process in between. -/
theorem server_sending_next (phase : ServerSending client reference payload process)
    (advanced : stepLocal [importedActorProtocolModule] process.state = .next state) :
    ServerSending client reference payload { process with state := state } := by
  obtain ⟨context, stack, moduleName, clientBound, referenceBound, payloadBound, segment⟩ := phase
  refine ⟨context, stack, moduleName, clientBound, referenceBound, payloadBound, ?_⟩
  exact reachesBoundary_next segment advanced (by rfl)

/-- A runtime request while in the server send interval is necessarily the exact
    reply endpoint. It cannot be an unaccounted-for effect hidden inside a prefix. -/
theorem server_sending_runtime (phase : ServerSending client reference payload process)
    (runtime : process.state.control = .runtime name arguments) :
    name = "send" ∧ arguments = [.pid client, replyPayload reference payload] := by
  obtain ⟨context, stack, _, _, _, _, segment⟩ := phase
  have stopped : stepLocal [importedActorProtocolModule] process.state =
      .halt (.fault (.unsupported s!"Actor runtime required: {name}/{arguments.length}")) := by
    simp [stepLocal, runtime, unsupported]
  have endpoint := reachesBoundary_halt segment stopped
  have control := congrArg LocalState.control endpoint
  rw [runtime] at control
  exact Control.runtime.inj control

theorem client_returning_after_remove (context : Context) (stack : List Frame)
    (payload : Value) (pid : Nat)
    (moduleName : context.moduleName = "actor_protocol")
    (payloadBound : context.env.lookup 12 = some payload) :
    ClientReturning payload {
      pid := pid
      state := {
        control := .ret [.atom "ok"]
        context := context
        stack := .seq context (.tuple [.lit (.atom "ok"), .var 12]) :: stack } } := by
  refine ⟨context, stack, moduleName, payloadBound, 6, ?_⟩
  exact client_result_prefix [importedActorProtocolModule] context stack payload payloadBound

/-- Explicit identities for the closed exchange created by initialSystem and its
    single spawn/make_ref path. Their allocation proof is still a control case. -/
def ClosedExchangeNetwork (payload : Value) (system : System) : Prop :=
  NetworkRespect (AllowedMailbox 0 1 0 payload) system ∧
  system.links = [] ∧ system.monitors = [] ∧
  ∀ process ∈ system.processes, process.pid = 0 ∨ process.pid = 1

theorem initial_closed_exchange_network (payload : Value) :
    ClosedExchangeNetwork payload (initialSystem "actor_protocol" "exchange" [payload]) := by
  refine ⟨initial_network _ payload, rfl, rfl, ?_⟩
  simp [initialSystem]


def ClientStage.requiredMessage (payload : Value) : ClientStage → Option Value
  | .remove => some (replyPayload 0 payload)
  | _ => none

def ServerStage.requiredMessage (payload : Value) : ServerStage → Option Value
  | .removeRequest => some (requestPayload 0 0 payload)
  | .removeStop => some (.atom "stop")
  | _ => none

/-- The message selected before a remove boundary remains at the cursor while
    other processes run or ordinary deliveries append to this mailbox. -/
def RequiredMessage (expected : Option Value) (process : Process) : Prop :=
  ∀ message, expected = some message → process.mailbox[process.cursor]? = some message

theorem requiredMessage_append (required : RequiredMessage expected process) (suffix : Values) :
    RequiredMessage expected { process with mailbox := process.mailbox ++ suffix } := by
  intro message selected
  have present := required message selected
  obtain ⟨bound, _⟩ := List.getElem?_eq_some_iff.mp present
  simpa [List.getElem?_append_left bound] using present

/-- A finished root is distinguished from its final still-running return state. -/
def ClientControl (payload : Value) (stage : ClientStage) (process : Process) : Prop :=
  process.pid = 0 ∧ process.cursor = 0 ∧ process.deadline = none ∧
  RequiredMessage (stage.requiredMessage payload) process ∧
  match process.status with
  | .finished outcome => stage = .done ∧ outcome = .returned [.tuple [.atom "ok", payload]]
  | _ => BoundaryPhase (stage.boundary payload) process.state

def ServerControl (payload : Value) (process : Process) : Prop :=
  process.pid = 1 ∧ process.cursor = 0 ∧ process.deadline = none ∧
  match process.status with
  | .finished outcome => outcome = .returned [.atom "ok"]
  | _ => ∃ stage : ServerStage,
      RequiredMessage (stage.requiredMessage payload) process ∧
      BoundaryPhase (stage.boundary payload) process.state

theorem clientControl_append (control : ClientControl payload stage process) (suffix : Values) :
    ClientControl payload stage { process with mailbox := process.mailbox ++ suffix } := by
  obtain ⟨pid, cursor, deadline, required, state⟩ := control
  exact ⟨pid, cursor, deadline, requiredMessage_append required suffix, state⟩

theorem serverControl_append (control : ServerControl payload process) (suffix : Values) :
    ServerControl payload { process with mailbox := process.mailbox ++ suffix } := by
  obtain ⟨pid, cursor, deadline, state⟩ := control
  refine ⟨pid, cursor, deadline, ?_⟩
  cases status : process.status <;> simp only [status] at state ⊢
  · obtain ⟨stage, required, segment⟩ := state
    exact ⟨stage, requiredMessage_append required suffix, segment⟩
  · obtain ⟨stage, required, segment⟩ := state
    exact ⟨stage, requiredMessage_append required suffix, segment⟩
  · exact state

theorem clientControl_next (control : ClientControl payload stage process)
    (advanced : stepLocal [importedActorProtocolModule] process.state = .next next) :
    ClientControl payload stage { process with state := next } := by
  obtain ⟨pid, cursor, deadline, required, state⟩ := control
  refine ⟨pid, cursor, deadline, required, ?_⟩
  cases status : process.status <;> simp only [status] at state ⊢
  · exact boundaryPhase_next state advanced
  · exact boundaryPhase_next state advanced
  · exact state

theorem serverControl_next (control : ServerControl payload process)
    (advanced : stepLocal [importedActorProtocolModule] process.state = .next next) :
    ServerControl payload { process with state := next } := by
  obtain ⟨pid, cursor, deadline, state⟩ := control
  refine ⟨pid, cursor, deadline, ?_⟩
  cases status : process.status <;> simp only [status] at state ⊢
  · obtain ⟨stage, required, segment⟩ := state
    exact ⟨stage, required, boundaryPhase_next segment advanced⟩
  · obtain ⟨stage, required, segment⟩ := state
    exact ⟨stage, required, boundaryPhase_next segment advanced⟩
  · exact state

def SignalFresh (system : System) : Prop :=
  ∀ signal ∈ system.pending, signal.id < system.nextSignal

theorem signalFresh_guard (fresh : SignalFresh system) :
    system.pending.any (fun signal => signal.id == system.nextSignal) = false := by
  cases result : system.pending.any (fun signal => signal.id == system.nextSignal) with
  | false => rfl
  | true =>
    obtain ⟨signal, member, identity⟩ := List.any_eq_true.mp result
    have equal : signal.id = system.nextSignal := by simpa using identity
    have bound := fresh signal member
    omega

theorem signalFresh_enqueue (fresh : SignalFresh system) (sender recipient : Nat)
    (kind : SignalKind) (message : Value) :
    SignalFresh (system.enqueue sender recipient kind message) := by
  intro signal member
  rcases List.mem_append.mp member with old | added
  · have bound := fresh signal old
    exact Nat.lt_succ_of_lt bound
  · have equal : signal = { id := system.nextSignal, sender, recipient, kind, message } := by
      simpa using added
    subst signal
    exact Nat.lt_succ_self _

theorem signalFresh_filter (fresh : SignalFresh system) (keep : Signal → Bool) :
    SignalFresh { system with pending := system.pending.filter keep } := by
  intro signal member
  exact fresh signal (List.mem_filter.mp member).1

/-- State predicate for the closed imported exchange. Counters
    and exact process population are tied to client phases, not assumed as an
    unrelated precondition on every step. Required-message witnesses connect
    mailbox removal to the value selected before a runtime suspension. -/
def ClosedExchange (payload : Value) (system : System) : Prop :=
  NetworkRespect (AllowedMailbox 0 1 0 payload) system ∧
  SignalFresh system ∧
  system.links = [] ∧ system.monitors = [] ∧
  ∃ stage client,
    ClientControl payload stage client ∧
    system.nextReference = stage.referenceCounter ∧
    (if stage = .spawn then
      system.processes = [client] ∧ system.nextPid = 1
    else
      ∃ server, system.processes = [client, server] ∧ system.nextPid = 2 ∧
        ServerControl payload server)

theorem closedExchange_filter (invariant : ClosedExchange payload system) (keep : Signal → Bool) :
    ClosedExchange payload { system with pending := system.pending.filter keep } := by
  obtain ⟨network, fresh, links, monitors, shape⟩ := invariant
  exact ⟨network_filter network keep, signalFresh_filter fresh keep, links, monitors, shape⟩

theorem closedExchange_time (invariant : ClosedExchange payload system) (to : Nat) :
    ClosedExchange payload { system with now := to } := invariant

theorem initial_closedExchange (payload : Value) (publicPayload : payload.isPublic = true) :
    ClosedExchange payload (initialSystem "actor_protocol" "exchange" [payload]) := by
  let client : Process := { pid := 0, state := initialCall "actor_protocol" "exchange" [payload] }
  have clientValid : ClientControl payload .spawn client := by
    refine ⟨rfl, rfl, rfl, ?_, ?_⟩
    · intro message impossible
      cases impossible
    · obtain ⟨endpoint, found, segment⟩ := clientSpawn_segment payload publicPayload
      exact ⟨endpoint, found, (actualBoundary_sound found).2, segment⟩
  refine ⟨initial_network _ payload, ?_, rfl, rfl, .spawn, client, clientValid, rfl, ?_⟩
  · simp [SignalFresh, initialSystem]
  · simp [initialSystem, client]

/-- Appending an allowed ordinary message preserves the exact client/server
    population, control phases, allocator counters, and selected-message witness. -/
theorem closedExchange_append (invariant : ClosedExchange payload system)
    (found : system.lookup recipient = some process)
    (messageValid : AllowedMailbox 0 1 0 payload recipient message) :
    ClosedExchange payload (system.update { process with mailbox := process.mailbox ++ [message] }) := by
  obtain ⟨network, fresh, links, monitors, stage, client, clientValid, referenceCounter, population⟩ := invariant
  have member : process ∈ system.processes := List.mem_of_find?_eq_some found
  have identity : process.pid = recipient := by
    have selected := List.find?_some found
    simpa using selected
  have mailboxValid : MailboxesRespect (AllowedMailbox 0 1 0 payload)
      (system.update { process with mailbox := process.mailbox ++ [message] }) := by
    apply mailboxes_update network.1
    intro entry queued
    rcases List.mem_append.mp queued with original | appended
    · exact network.1 process member entry original
    · have equal : entry = message := by simpa using appended
      subst entry
      simpa [identity] using messageValid
  have newNetwork : NetworkRespect (AllowedMailbox 0 1 0 payload)
      (system.update { process with mailbox := process.mailbox ++ [message] }) :=
    ⟨mailboxValid, network.2⟩
  by_cases spawning : stage = .spawn
  · simp only [spawning, if_pos] at population
    have equal : process = client := by simpa [population.1] using member
    subst process
    refine ⟨newNetwork, fresh, links, monitors, stage,
      { client with mailbox := client.mailbox ++ [message] },
      clientControl_append clientValid [message], referenceCounter, ?_⟩
    simp [spawning, System.update, population.1, population.2]
  · simp only [spawning, if_false] at population
    obtain ⟨server, processes, nextPid, serverValid⟩ := population
    have alternatives : process = client ∨ process = server := by simpa [processes] using member
    rcases alternatives with equal | equal
    · subst process
      refine ⟨newNetwork, fresh, links, monitors, stage,
        { client with mailbox := client.mailbox ++ [message] },
        clientControl_append clientValid [message], referenceCounter, ?_⟩
      simp only [spawning, if_false]
      refine ⟨server, ?_, nextPid, serverValid⟩
      simp [System.update, processes, clientValid.1, serverValid.1]
    · subst process
      refine ⟨newNetwork, fresh, links, monitors, stage, client, clientValid, referenceCounter, ?_⟩
      simp only [spawning, if_false]
      refine ⟨{ server with mailbox := server.mailbox ++ [message] }, ?_, nextPid,
        serverControl_append serverValid [message]⟩
      simp [System.update, processes, clientValid.1, serverValid.1]

theorem closedExchange_handle_message (invariant : ClosedExchange payload system)
    (ordinary : signal.kind = .message)
    (messageValid : AllowedMailbox 0 1 0 payload signal.recipient signal.message) :
    ClosedExchange payload (handleSignal system signal) := by
  cases found : system.lookup signal.recipient with
  | none => simpa [handleSignal, ordinary, found] using invariant
  | some process =>
    by_cases alive : system.alive process.pid = true
    · simpa [handleSignal, ordinary, found, alive] using
        closedExchange_append invariant found messageValid
    · simpa [handleSignal, ordinary, found, alive] using invariant

/-- Every accepted delivery preserves the complete candidate predicate, including
    the witness connecting receive selection to the message that will be removed. -/
theorem closedExchange_deliver (invariant : ClosedExchange payload system)
    (accepted : deliver system signalId = .ok next) : ClosedExchange payload next := by
  cases found : system.pending.find? (fun signal => signal.id == signalId) with
  | none => simp [deliver, found] at accepted
  | some signal =>
    have valid := invariant.1.2 signal (List.mem_of_find?_eq_some found)
    by_cases blocked : (system.pending.takeWhile (fun entry => entry.id != signalId)).any
        (fun prior => prior.sender == signal.sender && prior.recipient == signal.recipient) = true
    · simp [deliver, found, blocked, Functor.map, Except.map] at accepted
    · have equal : handleSignal
          { system with pending := system.pending.filter (fun entry => entry.id != signalId) }
          signal = next := by
        simpa [deliver, found, blocked, Pure.pure, Except.pure, Functor.map, Except.map] using accepted
      rw [← equal]
      exact closedExchange_handle_message (closedExchange_filter invariant _) valid.1 valid.2

theorem update_pair_client {system : System} {client server replacement : Process}
    (population : system.processes = [client, server])
    (clientPid : client.pid = 0) (serverPid : server.pid = 1) (replacementPid : replacement.pid = 0) :
    (system.update replacement).processes = [replacement, server] := by
  simp [System.update, population, clientPid, serverPid, replacementPid]

theorem update_pair_server {system : System} {client server replacement : Process}
    (population : system.processes = [client, server])
    (clientPid : client.pid = 0) (serverPid : server.pid = 1) (replacementPid : replacement.pid = 1) :
    (system.update replacement).processes = [client, replacement] := by
  simp [System.update, population, clientPid, serverPid, replacementPid]

theorem network_replace_process (network : NetworkRespect allowed system)
    (mailbox : ∀ message ∈ replacement.mailbox, allowed replacement.pid message) :
    NetworkRespect allowed (system.update replacement) :=
  ⟨mailboxes_update network.1 mailbox, network.2⟩

theorem network_enqueue_message (network : NetworkRespect allowed system)
    (messageValid : allowed recipient message) (sender : Nat) :
    NetworkRespect allowed (system.enqueue sender recipient .message message) := by
  refine ⟨network.1, ?_⟩
  intro signal member
  rcases List.mem_append.mp member with original | added
  · exact network.2 signal original
  · have equal : signal = { id := system.nextSignal, sender, recipient, message } := by
      simpa using added
    subst signal
    exact ⟨rfl, messageValid⟩

/-- Constructor for runtime cases after the sole child has been spawned. -/
theorem closedExchange_pair
    (network : NetworkRespect (AllowedMailbox 0 1 0 payload) system)
    (fresh : SignalFresh system) (links : system.links = []) (monitors : system.monitors = [])
    (population : system.processes = [client, server])
    (clientValid : ClientControl payload stage client) (serverValid : ServerControl payload server)
    (afterSpawn : stage ≠ .spawn) (pidCounter : system.nextPid = 2)
    (referenceCounter : system.nextReference = stage.referenceCounter) :
    ClosedExchange payload system := by
  refine ⟨network, fresh, links, monitors, stage, client, clientValid, referenceCounter, ?_⟩
  simp only [afterSpawn, if_false]
  exact ⟨server, population, pidCounter, serverValid⟩

/-- Pure Core steps cannot change the mailbox witness or allocation phase. -/
theorem closedExchange_next (invariant : ClosedExchange payload system)
    (found : system.lookup pid = some process)
    (advanced : stepLocal [importedActorProtocolModule] process.state = .next state) :
    ClosedExchange payload (system.update { process with state := state }) := by
  obtain ⟨network, fresh, links, monitors, stage, client, clientValid, referenceCounter, population⟩ := invariant
  have member : process ∈ system.processes := List.mem_of_find?_eq_some found
  have newNetwork : NetworkRespect (AllowedMailbox 0 1 0 payload)
      (system.update { process with state := state }) :=
    network_replace_process network (network.1 process member)
  by_cases spawning : stage = .spawn
  · simp only [spawning, if_pos] at population
    have equal : process = client := by simpa [population.1] using member
    subst process
    refine ⟨newNetwork, fresh, links, monitors, stage, { client with state := state },
      clientControl_next clientValid advanced, referenceCounter, ?_⟩
    simp [spawning, System.update, population.1, population.2]
  · simp only [spawning, if_false] at population
    obtain ⟨server, processes, nextPid, serverValid⟩ := population
    have alternatives : process = client ∨ process = server := by simpa [processes] using member
    rcases alternatives with equal | equal
    · subst process
      exact closedExchange_pair newNetwork fresh links monitors
        (update_pair_client processes clientValid.1 serverValid.1 clientValid.1)
        (clientControl_next clientValid advanced) serverValid spawning nextPid referenceCounter
    · subst process
      exact closedExchange_pair newNetwork fresh links monitors
        (update_pair_server processes clientValid.1 serverValid.1 serverValid.1)
        clientValid (serverControl_next serverValid advanced) spawning nextPid referenceCounter

end Erlean.Examples.ProtocolInvariant
