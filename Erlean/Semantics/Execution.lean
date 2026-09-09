/-!
# Total stepping and finite execution

This module does not assume an Erlang-specific state representation. A halt may
represent a program outcome, a model fault, or a suspended runtime request.
Exhausting fuel always retains the state needed to resume execution.
-/

namespace Erlean.Semantics

inductive Transition (State Result : Type) where
  | next (state : State)
  | halt (result : Result)
  deriving Repr, BEq, DecidableEq

inductive RunResult (State Result : Type) where
  | exhausted (state : State)
  | halted (result : Result)
  deriving Repr, BEq, DecidableEq

def run (step : State → Transition State Result) : Nat → State → RunResult State Result
  | 0, state => .exhausted state
  | fuel + 1, state =>
    match step state with
    | .next next => run step fuel next
    | .halt result => .halted result

def resume (step : State → Transition State Result) (fuel : Nat) :
    RunResult State Result → RunResult State Result
  | .exhausted state => run step fuel state
  | .halted result => .halted result

/-- A semantic step advances execution, without confusing a stop with a step. -/
def Step (step : State → Transition State Result) (before after : State) : Prop :=
  step before = .next after

theorem step_deterministic (step : State → Transition State Result)
    (h₁ : Step step s t₁) (h₂ : Step step s t₂) : t₁ = t₂ := by
  unfold Step at h₁ h₂
  exact Transition.next.inj (h₁.symm.trans h₂)

/-- Finite evaluation ending at a reported result. This is independent of fuel. -/
inductive Evaluates (step : State → Transition State Result) : State → Result → Prop where
  | halt : step state = .halt result → Evaluates step state result
  | next : step state = .next next → Evaluates step next result → Evaluates step state result

theorem run_halted_sound (step : State → Transition State Result) (fuel : Nat)
    (h : run step fuel state = .halted result) : Evaluates step state result := by
  induction fuel generalizing state with
  | zero => simp [run] at h
  | succ fuel ih =>
    cases hs : step state with
    | halt value =>
      simp [run, hs] at h
      subst value
      exact .halt hs
    | next next =>
      simp [run, hs] at h
      exact .next hs (ih h)

theorem evaluates_complete (h : Evaluates step state result) :
    ∃ fuel, run step fuel state = .halted result := by
  induction h with
  | halt hs => exact ⟨1, by simp [run, hs]⟩
  | next hs _ ih =>
    obtain ⟨fuel, hf⟩ := ih
    exact ⟨fuel + 1, by simp [run, hs, hf]⟩

theorem evaluates_iff_run : Evaluates step state result ↔
    ∃ fuel, run step fuel state = .halted result :=
  ⟨evaluates_complete, fun ⟨fuel, h⟩ => run_halted_sound step fuel h⟩

/-- Running in two budgets has exactly the same result as their sum. -/
theorem run_add (step : State → Transition State Result) (first second : Nat)
    (state : State) :
    run step (first + second) state = resume step second (run step first state) := by
  induction first generalizing state with
  | zero => simp [run, resume]
  | succ first ih =>
    cases hs : step state with
    | halt result => simp [run, resume, hs, Nat.succ_add]
    | next next => simpa [run, hs, Nat.succ_add] using ih next

theorem halted_stable (h : run step fuel state = .halted result) (extra : Nat) :
    run step (fuel + extra) state = .halted result := by
  rw [run_add, h]
  rfl

end Erlean.Semantics
