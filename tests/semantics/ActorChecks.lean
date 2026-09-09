import Erlean.Import.Lower
import Erlean.Runtime.Scheduler

open Erlean.Core Erlean.Import Erlean.Semantics Erlean.Runtime

-- Structural replay identity is not a protocol correctness theorem.
example (world : CodeWorld) (system : Erlean.Runtime.System) :
    replay world system [] = .ok system := rfl

private def assertTrue (condition : Bool) (label : String) : IO Unit :=
  unless condition do throw (IO.userError label)

private def expectError (result : Except ChoiceError Erlean.Runtime.System)
    (expected : ChoiceError) (label : String) : IO Unit :=
  match result with
  | .error actual => assertTrue (actual == expected) label
  | .ok _ => throw (IO.userError s!"{label}: unexpectedly accepted choice")

private def takeStep (system : Erlean.Runtime.System) (choice : Choice) : IO Erlean.Runtime.System :=
  match stepSystem [] system choice with
  | .ok next => pure next
  | .error reason => throw (IO.userError s!"Unexpected actor choice error: {repr reason}")

private def getProcess (system : Erlean.Runtime.System) (pid : Nat := 0) : IO Process :=
  match system.lookup pid with
  | some process => pure process
  | none => throw (IO.userError s!"Missing process {pid}")

private def actor (pid : Nat) (name : String) (args : Values) : Process :=
  { pid, state := { control := .runtime name args, context := ⟨"test", []⟩ } }

private def setRequest (system : Erlean.Runtime.System) (name : String) (args : Values) :
    IO Erlean.Runtime.System := do
  let process ← getProcess system
  return system.update { process with
    state := { process.state with control := .runtime name args }, status := .running }

def main : IO Unit := do
  let idle := actor 0 "self" []
  let fifo : Erlean.Runtime.System := {
    processes := [idle]
    pending := [
      { id := 0, sender := 1, recipient := 0, message := .atom "first" },
      { id := 1, sender := 1, recipient := 0, message := .atom "second" }]
    nextSignal := 2 }
  expectError (stepSystem [] fifo (.deliver 1)) .signalOrder
    "same sender-recipient signals cannot overtake each other"
  let first ← takeStep fifo (.deliver 0)
  let second ← takeStep first (.deliver 1)
  assertTrue ((← getProcess second).mailbox == [.atom "first", .atom "second"])
    "FIFO delivery preserves mailbox order"
  match replay [] fifo [.deliver 0, .deliver 1] with
  | .ok replayed => assertTrue (replayed == second) "explicit schedule replay"
  | .error reason => throw (IO.userError s!"Replay failed: {repr reason}")

  let scan : Erlean.Runtime.System := { processes := [{
    (actor 0 "recv_peek_message" []) with mailbox := [.atom "unmatched", .atom "wanted"] }] }
  let peeked ← takeStep scan (.run 0)
  assertTrue ((← getProcess peeked).state.control == .ret [.atom "true", .atom "unmatched"])
    "receive peeks without consuming"
  let skipped ← takeStep (← setRequest peeked "recv_next" []) (.run 0)
  let selected ← takeStep (← setRequest skipped "remove_message" []) (.run 0)
  let selectedProcess ← getProcess selected
  assertTrue (selectedProcess.mailbox == [.atom "unmatched"] && selectedProcess.cursor == 0)
    "selective receive removes only selected entry and resets cursor"

  let timer : Erlean.Runtime.System := { processes := [actor 0 "recv_wait_timeout" [.integer 10]] }
  let waiting ← takeStep timer (.run 0)
  assertTrue ((← getProcess waiting).deadline == some 10 && waiting.now == 0)
    "waiting establishes deadline without advancing time"
  expectError (stepSystem [] waiting (.run 0)) .blockedProcess "waiting is not a fuel-consuming loop"
  let later ← takeStep waiting (.advanceTime 4)
  expectError (stepSystem [] later (.run 0)) .blockedProcess "unexpired wait remains blocked"
  let delivered ← takeStep (later.enqueue 1 0 .message (.atom "unmatched")) (.deliver 0)
  let awakened ← takeStep delivered (.run 0)
  assertTrue ((← getProcess awakened).state.control == .ret [.atom "false"] &&
      (← getProcess awakened).deadline == some 10)
    "message wakeup retains original receive deadline"
  let scanned ← takeStep (← setRequest awakened "recv_next" []) (.run 0)
  let waitingAgain ← takeStep (← setRequest scanned "recv_wait_timeout" [.integer 10]) (.run 0)
  assertTrue ((← getProcess waitingAgain).deadline == some 10 && waitingAgain.now == 4)
    "rescan does not restart timeout budget"
  let expired ← takeStep (← takeStep waitingAgain (.advanceTime 10)) (.run 0)
  let expiredProcess ← getProcess expired
  assertTrue (expiredProcess.state.control == .ret [.atom "true"] &&
      expiredProcess.deadline == none && expiredProcess.mailbox == [.atom "unmatched"])
    "timeout preserves unmatched messages and clears deadline"
  let invalidTimer : Erlean.Runtime.System := {
    processes := [actor 0 "recv_wait_timeout" [.integer (-1)]] }
  let invalidResult ← takeStep invalidTimer (.run 0)
  assertTrue ((← getProcess invalidResult).state.control == .raise ⟨.error, .atom "timeout_value"⟩)
    "invalid timeout is a language exception"

  let down := Value.tuple [.atom "DOWN", .reference 3, .atom "process", .pid 1, .atom "normal"]
  let monitoring : Erlean.Runtime.System := {
    processes := [{ (actor 0 "demonitor" [.reference 3]) with mailbox := [down] }, actor 1 "self" []]
    monitors := [{ reference := 3, owner := 0, target := 1 }]
    pending := [{ id := 0, sender := 1, recipient := 0, message := .atom "normal", kind := .down 3 }]
    nextSignal := 1
    nextReference := 4
    nextPid := 2 }
  let disabled ← takeStep monitoring (.run 0)
  let suppressed ← takeStep disabled (.deliver 0)
  assertTrue ((← getProcess suppressed).mailbox == [down])
    "demonitor suppresses in-flight DOWN but preserves already queued DOWN"

  let linked : Erlean.Runtime.System := {
    processes := [actor 0 "unlink" [.pid 1], actor 1 "self" []]
    links := [{ id := 7, left := 0, right := 1, rightActive := true }]
    pending := [
      { id := 0, sender := 1, recipient := 0, message := .atom "stale", kind := .exit (some 7) false },
      { id := 1, sender := 1, recipient := 0, message := .atom "direct", kind := .exit none false }]
    nextSignal := 2
    nextLink := 8
    nextPid := 2 }
  let unlinked ← takeStep linked (.run 0)
  let staleSuppressed ← takeStep unlinked (.deliver 0)
  assertTrue (staleSuppressed.alive 0) "unlink suppresses stale linked exit"
  let directDelivered ← takeStep staleSuppressed (.deliver 1)
  assertTrue ((← getProcess directDelivered).status == .finished (.raised ⟨.exit, .atom "direct"⟩))
    "unlink does not suppress direct exit signals"

  let unsupported : Erlean.Runtime.System := { processes := [actor 0 "process_flag" []] }
  let faulted ← takeStep unsupported (.run 0)
  expectError (stepSystem [] faulted (.advanceTime 1)) .modelFault
    "model faults stop future system transitions"

  let artifact ← readArtifact "tests/fixtures/erlang/actor_protocol/core.json"
  let .ok report := lowerModule artifact | throw (IO.userError "Actor protocol import failed")
  assertTrue (report.rejected.isEmpty && report.module.check) "complete actor protocol import"
  for value in [Value.integer 42, Value.tuple [.atom "payload", .integer 7]] do
    let initial := initialSystem "actor_protocol" "exchange" [value]
    let execution := schedule [report.module] 10000 initial 0 []
    let root ← getProcess execution.system
    assertTrue (execution.stopped == "root-finished" &&
        root.status == .finished (.returned [.tuple [.atom "ok", value]]))
      "imported actor request-reply exchange"
    match replay [report.module] initial execution.choices with
    | .ok replayed => assertTrue (replayed == execution.system) "imported exchange replay identity"
    | .error reason => throw (IO.userError s!"Imported replay failed: {repr reason}")
  IO.println "Actor choice, lifecycle, receive, and replay regressions passed."
