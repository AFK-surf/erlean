import Std

/-!
Finite traces for pure deterministic controllers. Effects are returned data;
these results do not assert that an external runtime executes them, delivers
events fairly, or implements an actor mailbox protocol.
-/

namespace Erlean.Logic.Controller

universe u v w x y

variable {State : Type u} {Event : Type v} {Effect : Type w}

/-- Evaluate a finite event sequence, preserving the order of emitted effects. -/
def run (step : State → Event → State × List Effect) :
    State → List Event → State × List Effect
  | state, [] => (state, [])
  | state, event :: rest =>
    let current := step state event
    let later := run step current.1 rest
    (later.1, current.2 ++ later.2)

@[simp] theorem run_nil (step : State → Event → State × List Effect) (state : State) :
    run step state [] = (state, []) := rfl

theorem run_append (step : State → Event → State × List Effect)
    (state : State) (first second : List Event) :
    run step state (first ++ second) =
      let front := run step state first
      let back := run step front.1 second
      (back.1, front.2 ++ back.2) := by
  induction first generalizing state with
  | nil => simp [run]
  | cons event rest ih => simp [run, ih, List.append_assoc]

/-- A genuine one-event preservation theorem suffices for arbitrary finite
    traces. There is no bounded-event enumeration in this result. -/
theorem run_invariant (step : State → Event → State × List Effect)
    (invariant : State → Prop)
    (preserves : ∀ state event, invariant state → invariant (step state event).1)
    (state : State) (events : List Event) (initial : invariant state) :
    invariant (run step state events).1 := by
  induction events generalizing state with
  | nil => exact initial
  | cons event rest ih => exact ih (step state event).1 (preserves state event initial)

/-- Invariant preservation and per-step effect safety lift together. -/
theorem run_safe (step : State → Event → State × List Effect)
    (invariant : State → Prop) (allowed : Effect → Prop)
    (preserves : ∀ state event, invariant state → invariant (step state event).1)
    (emits : ∀ state event, invariant state →
      ∀ effect ∈ (step state event).2, allowed effect)
    (state : State) (events : List Event) (initial : invariant state) :
    invariant (run step state events).1 ∧
      ∀ effect ∈ (run step state events).2, allowed effect := by
  induction events generalizing state with
  | nil => exact ⟨initial, by simp [run]⟩
  | cons event rest ih =>
    obtain ⟨finalInvariant, safeTail⟩ :=
      ih (step state event).1 (preserves state event initial)
    refine ⟨finalInvariant, ?_⟩
    intro effect member
    change effect ∈ (step state event).2 ++ (run step (step state event).1 rest).2 at member
    rcases List.mem_append.mp member with current | later
    · exact emits state event initial effect current
    · exact safeTail effect later

variable {Concrete : Type x} {Output : Type y}

/-- A relational controller trace can instantiate each transition with an
    actual compiled-module evaluation rather than a second total function. -/
inductive Trace (transition : Concrete → Event → Concrete → List Output → Prop) :
    Concrete → List Event → Concrete → List Output → Prop where
  | nil (state : Concrete) : Trace transition state [] state []
  | cons (first : transition state event middle emitted)
      (rest : Trace transition middle events finish later) :
      Trace transition state (event :: events) finish (emitted ++ later)

/-- Unlike forward simulation alone, this rule covers every trace of the given
    relation, provided every concrete transition preserves the invariant. -/
theorem Trace.invariant
    (transition : Concrete → Event → Concrete → List Output → Prop)
    (property : Concrete → Prop)
    (preserves : ∀ state event next effects,
      property state → transition state event next effects → property next)
    (trace : Trace transition state events finish effects) (initial : property state) :
    property finish := by
  induction trace with
  | nil state => exact initial
  | cons first rest ih => exact ih (preserves _ _ _ _ initial first)

theorem Trace.safe
    (transition : Concrete → Event → Concrete → List Output → Prop)
    (property : Concrete → Prop) (allowed : Output → Prop)
    (preserves : ∀ state event next effects,
      property state → transition state event next effects → property next)
    (emits : ∀ state event next effects,
      property state → transition state event next effects →
        ∀ effect ∈ effects, allowed effect)
    (trace : Trace transition state events finish effects) (initial : property state) :
    property finish ∧ ∀ effect ∈ effects, allowed effect := by
  induction trace with
  | nil state => exact ⟨initial, by simp⟩
  | cons first rest ih =>
    obtain ⟨last, laterSafe⟩ := ih (preserves _ _ _ _ initial first)
    refine ⟨last, ?_⟩
    intro effect member
    rcases List.mem_append.mp member with current | later
    · exact emits _ _ _ _ initial first effect current
    · exact laterSafe effect later

/-- Lift a proved one-event compiled refinement to every finite event sequence.
    The transition premise is deliberately explicit: this is a reusable lifting
    rule, not a claim that an unverified concrete controller is correct. -/
theorem trace_of_refinement
    (step : State → Event → State × List Effect)
    (transition : Concrete → Event → Concrete → List Output → Prop)
    (encodeState : State → Concrete) (encodeEffect : Effect → Output)
    (invariant : State → Prop)
    (preserves : ∀ state event, invariant state → invariant (step state event).1)
    (refines : ∀ state event, invariant state →
      transition (encodeState state) event (encodeState (step state event).1)
        ((step state event).2.map encodeEffect))
    (state : State) (events : List Event) (initial : invariant state) :
    Trace transition (encodeState state) events (encodeState (run step state events).1)
      ((run step state events).2.map encodeEffect) := by
  induction events generalizing state with
  | nil => exact .nil (encodeState state)
  | cons event rest ih =>
    have current := refines state event initial
    have later := ih (step state event).1 (preserves state event initial)
    simpa only [run, List.map_append] using Trace.cons current later

/-- Safety can be transported through a relational refinement without asserting
    anything about external effect execution or infinite schedules. -/
theorem refined_trace_safe
    (step : State → Event → State × List Effect)
    (transition : Concrete → Event → Concrete → List Output → Prop)
    (encodeState : State → Concrete) (encodeEffect : Effect → Output)
    (invariant : State → Prop) (allowed : Effect → Prop)
    (preserves : ∀ state event, invariant state → invariant (step state event).1)
    (emits : ∀ state event, invariant state →
      ∀ effect ∈ (step state event).2, allowed effect)
    (refines : ∀ state event, invariant state →
      transition (encodeState state) event (encodeState (step state event).1)
        ((step state event).2.map encodeEffect))
    (state : State) (events : List Event) (initial : invariant state) :
    Trace transition (encodeState state) events (encodeState (run step state events).1)
        ((run step state events).2.map encodeEffect) ∧
      invariant (run step state events).1 ∧
      ∀ effect ∈ (run step state events).2, allowed effect :=
  ⟨trace_of_refinement step transition encodeState encodeEffect invariant preserves refines state events initial,
    run_safe step invariant allowed preserves emits state events initial⟩

end Erlean.Logic.Controller
