import Erlean.Examples.Identity.ImportedErlang
import Erlean.Examples.Modular.Imported
import Erlean.Logic.Modular

namespace Erlean.Examples

open Core Semantics Logic

/-- The dependency contract below is proved for this exact linked world. -/
def modularWorld : CodeWorld := [importedModularClient, importedModule]

/-- A compact view of the dependency entry. The checked dispatch prefixes below
    establish its connection to the actual emitted function definitions. -/
def identityDependencyEntry (value : Value) : LocalState :=
  { control := .eval (.caseE (.var 0)
      [([.var 1], .lit (.atom "true"), .var 1),
       ([.var 1], .lit (.atom "true"),
        .primop "match_fail" [.tuple [.lit (.atom "function_clause"), .var 1]])])
    context := ⟨"identity", [(0, value)]⟩ }

theorem linked_identity_run (value : Value) :
    runLocal 32 modularWorld (initialCall "identity" "identity" [value]) =
      .halted (.returned [value]) := by
  cbv

/-- Prove the dependency once, with the client's linked module present. -/
theorem linked_identity_totalCorrect :
    TotalCorrect modularWorld "identity" "identity"
      (fun args => ∃ value, args = [value])
      (fun args result => result = .returned args) := by
  apply totalCorrect_of_evaluates
  intro args precondition
  obtain ⟨value, rfl⟩ := precondition
  exact ⟨.returned [value], run_halted_sound _ 32 (linked_identity_run value), trivial, rfl⟩

/-- Dependency dispatch stops before evaluating its body. -/
theorem identity_dependency_dispatch (value : Value) :
    runLocal 7 modularWorld (initialCall "identity" "identity" [value]) =
      .exhausted (identityDependencyEntry value) := by
  cbv

/-- Client execution reaches the same dependency entry, with no pending frame. -/
theorem modular_client_dispatch (value : Value) :
    runLocal 20 modularWorld (initialCall "modular_client" "relay" [value]) =
      .exhausted (identityDependencyEntry value) := by
  cbv

/-- The client proof applies the dependency theorem. It checks only the caller
    prefix and dependency dispatch, without reevaluating the dependency body. -/
theorem modular_relay_totalCorrect :
    TotalCorrect modularWorld "modular_client" "relay"
      (fun args => ∃ value, args = [value])
      (fun args result => result = .returned args) := by
  apply totalCorrect_of_dependency linked_identity_totalCorrect (fun args => args)
  · intro args precondition
    exact precondition
  · intro args precondition
    obtain ⟨value, rfl⟩ := precondition
    exact ⟨identityDependencyEntry value, 20, 7,
      modular_client_dispatch value, identity_dependency_dispatch value⟩
  · intro args result _ postcondition
    exact postcondition

end Erlean.Examples
