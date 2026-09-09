import Erlean.Runtime.Actors
import Init.Data.List.Monadic

set_option maxRecDepth 2048
set_option maxHeartbeats 800000

namespace Erlean.Runtime

open Core Semantics

/-- Every pending signal was allocated before the next signal identifier.
    This property is independent of signal payloads and scheduling strategy. -/
def SignalBounds (system : System) : Prop :=
  ∀ signal ∈ system.pending, signal.id < system.nextSignal

theorem signalBounds_enqueue {system : System} (h : SignalBounds system)
    (sender recipient : Nat) (kind : SignalKind) (message : Value) :
    SignalBounds (system.enqueue sender recipient kind message) := by
  intro signal member
  rcases List.mem_append.mp member with old | fresh
  · have before := h signal old
    exact Nat.lt_succ_of_lt before
  · have same := List.mem_singleton.mp fresh
    subst signal
    exact Nat.lt_succ_self _

theorem signalBounds_filter {system : System} (h : SignalBounds system) (keep : Signal → Bool) :
    SignalBounds { system with pending := system.pending.filter keep } := by
  intro signal member
  exact h signal (List.mem_filter.mp member).1

private theorem signalBounds_fold_enqueue {α : Type} (entries : List α)
    (sender recipient : α → Nat) (kind : α → SignalKind) (message : Value) {system : System}
    (h : SignalBounds system) :
    SignalBounds (entries.foldl (fun current entry =>
      current.enqueue (sender entry) (recipient entry) (kind entry) message) system) := by
  induction entries generalizing system with
  | nil => exact h
  | cons entry rest ih =>
    exact ih (signalBounds_enqueue h (sender entry) (recipient entry) (kind entry) message)

@[simp] private theorem id_forIn_enqueue {α : Type} (entries : List α)
    (sender recipient : α → Nat) (kind : α → SignalKind) (message : Value) (system : System) :
    ((forIn entries system (fun entry current =>
      ForInStep.yield (current.enqueue (sender entry) (recipient entry) (kind entry) message))) : Id System) =
      entries.foldl (fun current entry =>
        current.enqueue (sender entry) (recipient entry) (kind entry) message) system := by
  simpa only [pure] using
    (List.forIn_pure_yield_eq_foldl (m := Id) (l := entries)
      (fun (entry : α) (current : System) =>
        current.enqueue (sender entry) (recipient entry) (kind entry) message) system)

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

theorem finishProcess_signalBounds {system : System} (h : SignalBounds system)
    (process : Process) (outcome : Outcome) : SignalBounds (finishProcess system process outcome) := by
  unfold finishProcess
  simp only [Id.run, pure, bind]
  split
  all_goals
    try simp only [id_forIn_enqueue]
    repeat' first
      | exact h
      | apply signalBounds_fold_enqueue

theorem handleSignal_signalBounds {system : System} (h : SignalBounds system) (signal : Signal) :
    SignalBounds (handleSignal system signal) := by
  unfold handleSignal
  repeat' first
    | exact h
    | exact signalBounds_enqueue h _ _ _ _
    | (apply finishProcess_signalBounds; exact h)
    | (simp only [Bool.not_true, Bool.false_eq_true, if_false])
    | split

theorem deliver_signalBounds {system next : System} (h : SignalBounds system) (signalId : Nat)
    (success : deliver system signalId = .ok next) : SignalBounds next := by
  unfold deliver at success
  simp only [bind, pure, Except.bind, Except.pure] at success
  split at success
  · split at success
    · simp at success
    · cases success
      apply handleSignal_signalBounds
      exact signalBounds_filter h _
  · simp at success

theorem request_signalBounds {system next : System} (h : SignalBounds system)
    (process : Process) (world : CodeWorld) (name : String) (args : Values)
    (success : request world system process name args = .ok next) : SignalBounds next := by
  unfold request at success
  repeat' first
    | (simp only [except_forIn_enqueue, bind, pure, throw, throwThe, Except.bind, Except.pure] at success)
    | (split at success)
  all_goals try cases success
  all_goals first
    | exact h
    | (apply signalBounds_enqueue; exact h)
    | (apply signalBounds_fold_enqueue; exact h)
    | (apply finishProcess_signalBounds; exact h)

theorem stepSystem_signalBounds {system next : System} (h : SignalBounds system)
    (world : CodeWorld) (choice : Choice)
    (success : stepSystem world system choice = .ok next) : SignalBounds next := by
  unfold stepSystem at success
  repeat' first
    | (simp only [bind, pure, throw, throwThe, Except.bind, Except.pure] at success)
    | (split at success)
  all_goals first
    | exact request_signalBounds h _ world _ _ success
    | exact deliver_signalBounds h _ success
    | (cases success <;> first
       | exact h
       | exact finishProcess_signalBounds h _ _)

theorem replay_signalBounds {system next : System} (h : SignalBounds system)
    (world : CodeWorld) (choices : List Choice)
    (success : replay world system choices = .ok next) : SignalBounds next := by
  induction choices generalizing system with
  | nil => cases success; exact h
  | cons choice rest ih =>
    simp only [replay] at success
    cases stepped : stepSystem world system choice with
    | error reason => simp [stepped, bind, Except.bind] at success
    | ok intermediate =>
      simp [stepped, bind, Except.bind] at success
      exact ih (stepSystem_signalBounds h world choice stepped) success

theorem initialSystem_signalBounds (moduleName functionName : String) (arguments : Values) :
    SignalBounds (initialSystem moduleName functionName arguments) := by
  simp [SignalBounds, initialSystem]

theorem initial_replay_signalBounds (world : CodeWorld) (moduleName functionName : String)
    (arguments : Values) (choices : List Choice) (next : System)
    (success : replay world (initialSystem moduleName functionName arguments) choices = .ok next) :
    SignalBounds next :=
  replay_signalBounds (initialSystem_signalBounds moduleName functionName arguments) world choices success

/-- A reachable allocator never collides with a currently pending signal. -/
theorem pending_nextSignal_fresh {system : System} (h : SignalBounds system) :
    system.pending.any (fun signal => signal.id == system.nextSignal) = false := by
  simp only [List.any_eq_false, beq_iff_eq]
  intro signal member
  exact Nat.ne_of_lt (h signal member)

end Erlean.Runtime
