import Erlean.Runtime.Actors

namespace Erlean.Runtime

/-- This scheduler is a debugging strategy, not a fairness assumption or a
    replacement for quantifying over accepted system choices. -/
structure ScheduleResult where
  system : System
  choices : List Choice
  stopped : String
  deriving Repr

private def eligible (world : Core.CodeWorld) (system : System) (cursor : Nat) :
    Option (Choice × System × Nat) := Id.run do
  let choices := system.processes.map (fun p => Choice.run p.pid) ++
    system.pending.map (fun s => Choice.deliver s.id)
  for offset in List.range choices.length do
    let index := (cursor + offset) % choices.length
    if let some choice := choices[index]? then
      if let .ok next := stepSystem world system choice then
        return some (choice, next, index + 1)
  let deadlines := system.processes.filterMap fun p =>
    if p.status == .waiting then p.deadline.filter (system.now < ·) else none
  match deadlines.foldl (fun current value => some (min (current.getD value) value)) none with
  | none => return none
  | some time =>
    match stepSystem world system (.advanceTime time) with
    | .ok next => return some (.advanceTime time, next, cursor)
    | .error _ => return none

/-- Bounded replayable scheduling. A model fault in any child aborts the run.
    Time advances only when no process or delivery choice can make progress. -/
def schedule (world : Core.CodeWorld) : Nat → System → Nat → List Choice → ScheduleResult
  | 0, system, _, trace => ⟨system, trace.reverse, "exhausted"⟩
  | fuel + 1, system, cursor, trace =>
    if system.processes.any (fun p => match p.status with
        | .finished (.fault _) => true | _ => false) then
      ⟨system, trace.reverse, "model-fault"⟩
    else if (system.lookup 0).any (fun p => match p.status with
        | .finished _ => true | _ => false) then
      ⟨system, trace.reverse, "root-finished"⟩
    else match eligible world system cursor with
      | none => ⟨system, trace.reverse, "blocked"⟩
      | some (choice, next, cursor) => schedule world fuel next cursor (choice :: trace)

end Erlean.Runtime
