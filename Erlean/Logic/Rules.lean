import Erlean.Logic.Contract

namespace Erlean.Logic

open Semantics

/-- A checked finite prefix can be composed with any remaining execution. -/
theorem evaluates_of_prefix
    (initial : run step fuel start = .exhausted middle)
    (suffix : Evaluates step middle result) : Evaluates step start result := by
  obtain ⟨remaining, h⟩ := evaluates_complete suffix
  apply run_halted_sound step (fuel + remaining)
  rw [run_add, initial]
  exact h

theorem run_of_prefix
    (initial : run step fuel start = .exhausted middle) (remaining : Nat) :
    run step (fuel + remaining) start = run step remaining middle := by
  rw [run_add, initial]
  rfl

end Erlean.Logic
