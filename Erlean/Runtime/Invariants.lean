import Erlean.Runtime.Actors
import Init.Data.List.Monadic
import Init.Data.List.Find

set_option maxRecDepth 2048
set_option maxHeartbeats 800000

namespace Erlean.Runtime

open Core Semantics

/-- Every mailbox scan cursor points at an existing entry or the end position.
    This structural invariant does not imply protocol authenticity or liveness. -/
def CursorBounds (system : System) : Prop :=
  ∀ process ∈ system.processes, process.cursor ≤ process.mailbox.length

theorem cursorBounds_of_processes_eq {before after : System}
    (h : CursorBounds before) (same : after.processes = before.processes) : CursorBounds after := by
  intro process member
  exact h process (same ▸ member)

theorem cursorBounds_update {system : System} {process : Process}
    (h : CursorBounds system) (hp : process.cursor ≤ process.mailbox.length) :
    CursorBounds (system.update process) := by
  intro current member
  obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp member
  split
  · exact hp
  · exact h old oldMember

theorem cursorBounds_lookup {system : System} {pid : Nat} {process : Process}
    (h : CursorBounds system) (found : system.lookup pid = some process) :
    process.cursor ≤ process.mailbox.length := by
  exact h process (List.mem_of_find?_eq_some found)

@[simp] theorem enqueue_processes (system : System) (sender recipient : Nat)
    (kind : SignalKind) (message : Value) :
    (system.enqueue sender recipient kind message).processes = system.processes := rfl

private theorem foldl_processes {α : Type} (entries : List α) (step : System → α → System)
    (same : ∀ system entry, (step system entry).processes = system.processes) (system : System) :
    (entries.foldl step system).processes = system.processes := by
  induction entries generalizing system with
  | nil => rfl
  | cons entry rest ih =>
    simpa only [List.foldl_cons, same] using ih (step system entry)

private theorem foldl_enqueue_processes {α : Type} (entries : List α)
    (sender recipient : α → Nat) (kind : α → SignalKind) (message : Value) (system : System) :
    (entries.foldl (fun current entry =>
      current.enqueue (sender entry) (recipient entry) (kind entry) message) system).processes =
      system.processes :=
  foldl_processes entries (fun current entry =>
    current.enqueue (sender entry) (recipient entry) (kind entry) message) (fun _ _ => rfl) system

@[simp] private theorem forIn_enqueue_processes {α : Type} (entries : List α)
    (sender recipient : α → Nat) (kind : α → SignalKind) (message : Value) (system : System) :
    ((forIn entries system (fun entry current =>
      ForInStep.yield (current.enqueue (sender entry) (recipient entry) (kind entry) message)) :
        Id System)).processes = system.processes := by
  have loop := List.forIn_pure_yield_eq_foldl (m := Id) (l := entries)
    (fun entry current => current.enqueue (sender entry) (recipient entry) (kind entry) message) system
  change (Id.run (forIn entries system (fun entry current =>
    pure (ForInStep.yield (current.enqueue (sender entry) (recipient entry) (kind entry) message))))).processes = _
  rw [loop]
  exact foldl_enqueue_processes entries sender recipient kind message system

private theorem finishProcess_bounds {system : System} {process : Process}
    (h : CursorBounds system) (hp : process.cursor ≤ process.mailbox.length) (outcome : Outcome) :
    CursorBounds (finishProcess system process outcome) := by
  unfold finishProcess
  simp only [Id.run, pure, bind]
  split
  all_goals
    simp only [CursorBounds, forIn_enqueue_processes]
    apply cursorBounds_update h
    exact hp

private theorem update_mailbox_append {system : System} {process : Process}
    (h : CursorBounds system) (hp : process.cursor ≤ process.mailbox.length) (message : Value) :
    CursorBounds (system.update { process with mailbox := process.mailbox ++ [message] }) := by
  apply cursorBounds_update h
  simp only [List.length_append, List.length_singleton]
  omega

theorem handleSignal_cursorBounds {system : System} (h : CursorBounds system) (signal : Signal) :
    CursorBounds (handleSignal system signal) := by
  unfold handleSignal
  repeat' first
    | exact h
    | (apply update_mailbox_append h; apply cursorBounds_lookup h; assumption)
    | (apply finishProcess_bounds
       · exact h
       · apply cursorBounds_lookup h
         assumption)
    | (simp only [Bool.not_true, Bool.false_eq_true, if_false])
    | split

theorem deliver_cursorBounds {system next : System} (h : CursorBounds system) (signalId : Nat)
    (success : deliver system signalId = .ok next) : CursorBounds next := by
  unfold deliver at success
  simp only [bind, pure, Except.bind, Except.pure] at success
  split at success
  · split at success
    · simp at success
    · cases success
      apply handleSignal_cursorBounds
      exact h
  · simp at success

private theorem cursorBounds_append {system : System} (h : CursorBounds system)
    (process : Process) (hp : process.cursor ≤ process.mailbox.length) :
    CursorBounds { system with processes := system.processes ++ [process] } := by
  intro current member
  rcases List.mem_append.mp member with member | member
  · exact h current member
  · have same : current = process := List.mem_singleton.mp member
    subst current
    exact hp

private theorem cursorBounds_fold_enqueue {α : Type} (entries : List α)
    (sender recipient : α → Nat) (kind : α → SignalKind) (message : Value) {system : System}
    (h : CursorBounds system) :
    CursorBounds (entries.foldl (fun current entry =>
      current.enqueue (sender entry) (recipient entry) (kind entry) message) system) := by
  exact cursorBounds_of_processes_eq h (foldl_enqueue_processes entries sender recipient kind message system)

@[simp] private theorem except_forIn_enqueue {α : Type} (entries : List α)
    (sender recipient : α → Nat) (kind : α → SignalKind) (message : Value) (system : System) :
    (forIn entries system (fun entry current =>
      Except.ok (ForInStep.yield (current.enqueue (sender entry) (recipient entry) (kind entry) message)))) =
      (Except.ok (entries.foldl (fun current entry =>
        current.enqueue (sender entry) (recipient entry) (kind entry) message) system) : Except ChoiceError System) := by
  simpa only [pure, Except.pure] using
    (List.forIn_pure_yield_eq_foldl (m := Except ChoiceError) (l := entries)
      (fun (entry : α) (current : System) =>
        current.enqueue (sender entry) (recipient entry) (kind entry) message) system)

theorem request_cursorBounds {system next : System} {process : Process}
    (h : CursorBounds system) (hp : process.cursor ≤ process.mailbox.length)
    (world : CodeWorld) (name : String) (args : Values)
    (success : request world system process name args = .ok next) : CursorBounds next := by
  unfold request at success
  repeat' first
    | (simp only [except_forIn_enqueue, bind, pure, throw, throwThe, Except.bind, Except.pure] at success)
    | (split at success)
  all_goals try cases success
  all_goals
    first
      | exact h
      | (solve | apply finishProcess_bounds h hp)
      | (apply cursorBounds_update h
         try simp only [returnValues, raiseReason, unsupportedProcess]
         omega)
      | (apply cursorBounds_append
         · apply cursorBounds_update h
           exact hp
         · exact Nat.zero_le _)
      | (apply cursorBounds_fold_enqueue
         apply cursorBounds_update h
         exact hp)

theorem stepSystem_cursorBounds {system next : System} (h : CursorBounds system)
    (world : CodeWorld) (choice : Choice)
    (success : stepSystem world system choice = .ok next) : CursorBounds next := by
  unfold stepSystem at success
  repeat' first
    | (simp only [bind, pure, throw, throwThe, Except.bind, Except.pure] at success)
    | (split at success)
  all_goals first
    | exact request_cursorBounds h (by apply cursorBounds_lookup h; assumption) world _ _ success
    | exact deliver_cursorBounds h _ success
    | (cases success <;> first
       | exact h
       | exact finishProcess_bounds h (cursorBounds_lookup h (by assumption)) _
       | (have hp := cursorBounds_lookup h (by assumption)
          apply cursorBounds_update h
          exact hp))

theorem replay_cursorBounds {system next : System} (h : CursorBounds system)
    (world : CodeWorld) (choices : List Choice)
    (success : replay world system choices = .ok next) : CursorBounds next := by
  induction choices generalizing system with
  | nil => cases success; exact h
  | cons choice rest ih =>
    simp only [replay] at success
    cases stepped : stepSystem world system choice with
    | error reason => simp [stepped, bind, Except.bind] at success
    | ok intermediate =>
      simp [stepped, bind, Except.bind] at success
      exact ih (stepSystem_cursorBounds h world choice stepped) success

theorem initialSystem_cursorBounds (moduleName functionName : String) (arguments : Values) :
    CursorBounds (initialSystem moduleName functionName arguments) := by
  simp [CursorBounds, initialSystem]

/-- Every finite sequence of accepted choices preserves cursor bounds, independent
    of the scheduling strategy and without a fairness assumption. -/
theorem initial_replay_cursorBounds (world : CodeWorld) (moduleName functionName : String)
    (arguments : Values) (choices : List Choice) (next : System)
    (success : replay world (initialSystem moduleName functionName arguments) choices = .ok next) :
    CursorBounds next :=
  replay_cursorBounds (initialSystem_cursorBounds moduleName functionName arguments) world choices success

end Erlean.Runtime
