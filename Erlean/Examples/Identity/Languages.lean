import Erlean.Examples.Identity.ImportedGleam
import Erlean.Examples.Identity.ImportedElixir
import Erlean.Logic.Contract

namespace Erlean.Examples

open Core Semantics Logic

/-- Execution of the imported Gleam identity is parametric in the modeled value.
    This proves the Core artifact's behavior, not compiler correctness. -/
theorem gleam_identity_run (value : Value) :
    runLocal 32 [importedGleamModule] (initialCall "gleam_identity" "identity" [value]) =
      .halted (.returned [value]) := by
  cbv

theorem gleam_identity_totalCorrect :
    TotalCorrect [importedGleamModule] "gleam_identity" "identity"
      (fun args => ∃ value, args = [value])
      (fun args result => result = .returned args) := by
  apply totalCorrect_of_evaluates
  intro args hp
  obtain ⟨value, rfl⟩ := hp
  refine ⟨.returned [value], ?_, trivial, rfl⟩
  exact run_halted_sound (stepLocal [importedGleamModule]) 32 (gleam_identity_run value)

/-- The Elixir-generated module is retained whole, including its metadata function. -/
theorem elixir_identity_run (value : Value) :
    runLocal 32 [importedElixirModule] (initialCall "Elixir.ErleanIdentity" "identity" [value]) =
      .halted (.returned [value]) := by
  simp [runLocal, run, initialCall, stepLocal, startCollect, finishCollect,
    nextControl, invoke, lookupFunction, importedElixirModule, Env.lookup,
    patternsObservationAllowed, patternObservationAllowed,
    matchPatterns, BEq.beq, List.beq, Value.equal]

theorem elixir_identity_totalCorrect :
    TotalCorrect [importedElixirModule] "Elixir.ErleanIdentity" "identity"
      (fun args => ∃ value, args = [value])
      (fun args result => result = .returned args) := by
  apply totalCorrect_of_evaluates
  intro args hp
  obtain ⟨value, rfl⟩ := hp
  refine ⟨.returned [value], ?_, trivial, rfl⟩
  exact run_halted_sound (stepLocal [importedElixirModule]) 32 (elixir_identity_run value)

end Erlean.Examples
