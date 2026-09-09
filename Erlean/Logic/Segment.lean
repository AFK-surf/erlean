import Erlean.Semantics.Execution

namespace Erlean.Logic

open Semantics

/-- A pure segment ends at a designated suspension state before observing its
    terminal local transition. This predicate is useful for actor phase proofs:
    intermediate Core frames need not be enumerated individually. -/
def ReachesBoundary (step : State → Transition State Result) (state boundary : State) : Prop :=
  ∃ fuel, run step fuel state = .exhausted boundary

theorem reachesBoundary_self (step : State → Transition State Result) (state : State) :
    ReachesBoundary step state state := ⟨0, rfl⟩

/-- A locally terminal state on a pure segment must already be its boundary. -/
theorem reachesBoundary_halt (segment : ReachesBoundary step state boundary)
    (stopped : step state = .halt result) : state = boundary := by
  obtain ⟨fuel, reached⟩ := segment
  cases fuel with
  | zero => simpa [run] using reached
  | succ fuel => simp [run, stopped] at reached

/-- Every actual pure step preserves a segment whose boundary suspends locally. -/
theorem reachesBoundary_next (segment : ReachesBoundary step state boundary)
    (advanced : step state = .next next)
    (suspends : step boundary = .halt result) : ReachesBoundary step next boundary := by
  obtain ⟨fuel, reached⟩ := segment
  cases fuel with
  | zero =>
    have equal : state = boundary := by simpa [run] using reached
    subst state
    rw [suspends] at advanced
    contradiction
  | succ fuel => exact ⟨fuel, by simpa [run, advanced] using reached⟩

/-- Compose checked prefixes with a remaining pure segment. -/
theorem reachesBoundary_prefix (prefixRun : run step fuel start = .exhausted middle)
    (segment : ReachesBoundary step middle boundary) : ReachesBoundary step start boundary := by
  obtain ⟨remaining, reached⟩ := segment
  refine ⟨fuel + remaining, ?_⟩
  rw [run_add, prefixRun]
  exact reached

inductive BoundarySearch (State Result : Type) where
  | found (state : State)
  | halted (result : Result)
  | exhausted (state : State)
  deriving Repr

/-- Bounded symbolic stepping stops before the designated runtime boundary.
    Success is accompanied by the soundness theorem below, not a native axiom. -/
def seekBoundary (step : State → Transition State Result) (isBoundary : State → Bool) :
    Nat → State → BoundarySearch State Result
  | 0, state => if isBoundary state then .found state else .exhausted state
  | fuel + 1, state =>
    if isBoundary state then .found state
    else match step state with
      | .halt result => .halted result
      | .next next => seekBoundary step isBoundary fuel next

theorem seekBoundary_sound
    (found : seekBoundary step isBoundary fuel state = .found boundary) :
    ReachesBoundary step state boundary ∧ isBoundary boundary = true := by
  induction fuel generalizing state with
  | zero =>
    simp only [seekBoundary] at found
    split at found
    · cases found
      exact ⟨reachesBoundary_self step boundary, by assumption⟩
    · contradiction
  | succ fuel ih =>
    simp only [seekBoundary] at found
    split at found
    · cases found
      exact ⟨reachesBoundary_self step boundary, by assumption⟩
    · cases advanced : step state with
      | halt result => simp [advanced] at found
      | next next =>
        obtain ⟨segment, boundaryProof⟩ := ih (by simpa [advanced] using found)
        exact ⟨reachesBoundary_prefix (fuel := 1) (by simp [run, advanced]) segment, boundaryProof⟩

end Erlean.Logic
