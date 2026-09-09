import Erlean.Logic.Contract
import Erlean.Semantics.Observation

namespace Erlean.Logic

open Core Semantics

/-- Public contracts reject opaque exception information at the observation
    boundary. Internal machine contracts alone do not establish this property. -/
def ObservableTotalCorrect (world : CodeWorld) (moduleName functionName : String)
    (pre : Values → Prop) (post : Values → Outcome → Prop) : Prop :=
  TotalCorrect world moduleName functionName pre fun args result =>
    SupportedOutcome (observeOutcome result) ∧ post args (observeOutcome result)

theorem observableTotalCorrect_of_totalCorrect
    (contract : TotalCorrect world moduleName functionName pre post)
    (observable : ∀ args result, pre args → post args result → observeOutcome result = result) :
    ObservableTotalCorrect world moduleName functionName pre post := by
  refine ⟨?_, contract.2⟩
  intro args hp result evaluation
  obtain ⟨supported, satisfied⟩ := contract.1 args hp result evaluation
  refine ⟨supported, ?_⟩
  change SupportedOutcome (observeOutcome result) ∧ post args (observeOutcome result)
  rw [observable args result hp satisfied]
  exact ⟨supported, satisfied⟩

end Erlean.Logic
