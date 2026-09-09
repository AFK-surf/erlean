import Erlean.Logic.Rules

namespace Erlean.Logic

open Core Semantics

/-- Remove a checked finite prefix from a terminating execution. -/
theorem evaluates_after_prefix
    (initial : run step fuel start = .exhausted middle)
    (execution : Evaluates step start result) : Evaluates step middle result := by
  induction fuel generalizing start with
  | zero =>
      have eq : start = middle := by simpa [run] using initial
      subst start
      exact execution
  | succ fuel ih =>
      cases execution with
      | halt stopped => simp [run, stopped] at initial
      | next advanced remaining =>
          exact ih (by simpa [run, advanced] using initial) remaining

/-- Two entries can reuse the same remaining execution after checked prefixes.
    Both prefixes run in the same semantic world; no linking assumption is hidden. -/
def CommonEntry (step : State → Transition State Result) (caller dependency : State) : Prop :=
  ∃ middle callerFuel dependencyFuel,
    run step callerFuel caller = .exhausted middle ∧
    run step dependencyFuel dependency = .exhausted middle

theorem evaluates_of_common_entry (entry : CommonEntry step caller dependency)
    (execution : Evaluates step dependency result) : Evaluates step caller result := by
  obtain ⟨middle, callerFuel, dependencyFuel, callerPrefix, dependencyPrefix⟩ := entry
  exact evaluates_of_prefix callerPrefix (evaluates_after_prefix dependencyPrefix execution)

/-- Reuse an established dependency contract after proving argument adaptation,
    entry compatibility, and the required postcondition implication.

    This first modular rule handles calls whose continuations agree at entry,
    including tail delegation. It does not assert arbitrary frame lifting or
    preservation of a theorem when the linked code world changes. -/
theorem totalCorrect_of_dependency
    (dependency : TotalCorrect world dependencyModule dependencyFunction dependencyPre dependencyPost)
    (adapt : Values → Values)
    (adapt_pre : ∀ args, callerPre args → dependencyPre (adapt args))
    (entry : ∀ args, callerPre args →
      CommonEntry (stepLocal world)
        (initialCall callerModule callerFunction args)
        (initialCall dependencyModule dependencyFunction (adapt args)))
    (adapt_post : ∀ args result, callerPre args → dependencyPost (adapt args) result →
      callerPost args result) :
    TotalCorrect world callerModule callerFunction callerPre callerPost := by
  apply totalCorrect_of_evaluates
  intro args precondition
  obtain ⟨result, execution⟩ := dependency.2 (adapt args) (adapt_pre args precondition)
  obtain ⟨supported, postcondition⟩ :=
    dependency.1 (adapt args) (adapt_pre args precondition) result execution
  exact ⟨result, evaluates_of_common_entry (entry args precondition) execution,
    supported, adapt_post args result precondition postcondition⟩

end Erlean.Logic
