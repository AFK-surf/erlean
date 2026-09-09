import Erlean.Examples.ImportedIdentity
import Erlean.Logic.Contract

namespace Erlean.Examples

open Core Semantics Logic

/-- A kernel-checked execution of the imported OTP 29 identity function,
    parametric in every value represented by the initial semantic profile. -/
theorem identity_run (value : Value) :
    runLocal 32 [importedModule] (initialCall "identity" "identity" [value]) =
      .halted (.returned [value]) := by
  cbv

theorem identity_totalCorrect :
    TotalCorrect [importedModule] "identity" "identity"
      (fun args => ∃ value, args = [value])
      (fun args result => result = .returned args) := by
  apply totalCorrect_of_evaluates
  intro args hp
  obtain ⟨value, rfl⟩ := hp
  refine ⟨.returned [value], ?_, trivial, rfl⟩
  exact run_halted_sound (stepLocal [importedModule]) 32 (identity_run value)

end Erlean.Examples
