import Erlean.Semantics.Preservation

namespace Erlean.Semantics

open Core

/-!
Consequences of lexical preservation for variable evaluation only.

These results do not exclude unrelated model faults, establish termination, or
apply to actor-driver transitions. The initial-call corollaries use one immutable
checked code world and a finite prefix executed by `runLocal`.
-/

theorem lexicallyScoped_variable_lookup (state : LocalState) (id : VarId)
    (scopeProof : LexicallyScoped state) (control : state.control = .eval (.var id)) :
    ∃ value, state.context.env.lookup id = some value := by
  have expressionScope : ScopedExpr state.context (.var id) := by
    have current := scopeProof.control
    rw [control] at current
    exact current
  exact scoped_variable_lookup state.context id expressionScope

/-- A variable evaluation with lexical coverage takes a value-return step. -/
theorem lexicallyScoped_variable_step (world : CodeWorld) (state : LocalState) (id : VarId)
    (scopeProof : LexicallyScoped state) (control : state.control = .eval (.var id)) :
    ∃ value, stepLocal world state = .next { state with control := .ret [value] } := by
  obtain ⟨value, lookup⟩ := lexicallyScoped_variable_lookup state id scopeProof control
  exact ⟨value, by simp [stepLocal, control, lookup, nextControl]⟩

/-- This excludes precisely the variable lookup failure branch, not all faults
    at other expression forms or subsequent steps. -/
theorem lexicallyScoped_variable_not_unbound (world : CodeWorld) (state : LocalState)
    (id : VarId) (scopeProof : LexicallyScoped state)
    (control : state.control = .eval (.var id)) :
    stepLocal world state ≠ .halt (.fault (.invalid s!"Unbound variable {id}")) := by
  obtain ⟨value, step⟩ := lexicallyScoped_variable_step world state id scopeProof control
  rw [step]
  intro impossible
  cases impossible

/-- Every variable encountered after a finite local execution prefix from an
    initial call has a binding, when the linked code world is checked. -/
theorem initialCall_reachable_variable_lookup (world : CodeWorld)
    (moduleName functionName : String) (args : Values) (fuel : Nat)
    (reached : LocalState) (id : VarId) (checked : CheckedWorld world)
    (execution : runLocal fuel world (initialCall moduleName functionName args) = .exhausted reached)
    (control : reached.control = .eval (.var id)) :
    ∃ value, reached.context.env.lookup id = some value := by
  have scopeProof := runLocal_preserves_lexical_scope world
    (initialCall moduleName functionName args) reached fuel checked
    (initialCall_lexicallyScoped moduleName functionName args) execution
  exact lexicallyScoped_variable_lookup reached id scopeProof control

theorem initialCall_reachable_variable_not_unbound (world : CodeWorld)
    (moduleName functionName : String) (args : Values) (fuel : Nat)
    (reached : LocalState) (id : VarId) (checked : CheckedWorld world)
    (execution : runLocal fuel world (initialCall moduleName functionName args) = .exhausted reached)
    (control : reached.control = .eval (.var id)) :
    stepLocal world reached ≠ .halt (.fault (.invalid s!"Unbound variable {id}")) := by
  have scopeProof := runLocal_preserves_lexical_scope world
    (initialCall moduleName functionName args) reached fuel checked
    (initialCall_lexicallyScoped moduleName functionName args) execution
  exact lexicallyScoped_variable_not_unbound world reached id scopeProof control

end Erlean.Semantics
