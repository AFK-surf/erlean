import Erlean.Semantics.Machine

namespace Erlean.Logic

open Core Semantics

/-- Reported model faults are never accepted as program outcomes. -/
def SupportedOutcome : Outcome → Prop
  | .returned _ | .raised _ => True
  | .fault _ => False

/-- All finite outcomes satisfy the postcondition and remain inside the model.
    This sequential definition permits divergence. -/
def PartialCorrect (world : CodeWorld) (moduleName functionName : String)
    (pre : Values → Prop) (post : Values → Outcome → Prop) : Prop :=
  ∀ args, pre args → ∀ result,
    Evaluates (stepLocal world) (initialCall moduleName functionName args) result →
      SupportedOutcome result ∧ post args result

/-- Partial correctness with termination for every input in the precondition. -/
def TotalCorrect (world : CodeWorld) (moduleName functionName : String)
    (pre : Values → Prop) (post : Values → Outcome → Prop) : Prop :=
  PartialCorrect world moduleName functionName pre post ∧
    ∀ args, pre args → ∃ result,
      Evaluates (stepLocal world) (initialCall moduleName functionName args) result

theorem evaluates_deterministic (first : Evaluates step state a)
    (second : Evaluates step state b) : a = b := by
  obtain ⟨n, hn⟩ := evaluates_complete first
  obtain ⟨m, hm⟩ := evaluates_complete second
  have ha := halted_stable hn m
  have hb := halted_stable hm n
  rw [Nat.add_comm m n] at hb
  exact RunResult.halted.inj (ha.symm.trans hb)

theorem totalCorrect_of_evaluates
    (h : ∀ args, pre args → ∃ result,
      Evaluates (stepLocal world) (initialCall moduleName functionName args) result ∧
        SupportedOutcome result ∧ post args result) :
    TotalCorrect world moduleName functionName pre post := by
  constructor
  · intro args hp result hr
    obtain ⟨expected, he, hs, hpost⟩ := h args hp
    have eq := evaluates_deterministic hr he
    subst result
    exact ⟨hs, hpost⟩
  · intro args hp
    obtain ⟨result, he, _, _⟩ := h args hp
    exact ⟨result, he⟩

end Erlean.Logic
