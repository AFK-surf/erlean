import Erlean.Semantics.Machine

/-!
# A bounded proof tactic for one local transition

`erlean_step [contracts]` proves a single `stepLocal world state = .next next`
or `stepLocal world state = .halt outcome` equation. It does not construct an
execution trace or simplify a remaining runner. The equation guard runs before
any simplification, including the definitional-equality fast path.

The default whitelist exposes collection/call dispatch and pattern matching,
but does not unfold built-ins, map built-ins, or the code world. Supply checked
operation contracts for symbolic inputs. Supplied rules are ordinary `simp only`
arguments; callers can explicitly opt into additional definitions, with the
usual termination and performance responsibilities. No global simp set is used.

Each branch must close the goal. Failure leaves no partially simplified goal.
This is proof convenience, not a different executable semantics or completeness
claim. Symbolic control flow, unresolved pattern comparisons, and closed literal
codec normalization may require separate client lemmas.
-/

namespace Erlean.Logic

open Core Semantics

macro "erlean_step" "[" contracts:term,* "]" : tactic => `(tactic|
  (first
   | change stepLocal _ _ = Transition.next _
   | change stepLocal _ _ = Transition.halt _)
  <;> first
  | rfl
  | (simp only [$[$contracts:term],*] <;> rfl)
  | (rw [stepLocal]
     simp only [finishCollect, invoke, String.reduceEq, String.reduceBEq,
       decide_true, decide_false,
       List.nil_append, List.cons_append, BEq.beq,
       Bool.true_eq_false, Bool.false_eq_true, ↓reduceIte, $[$contracts:term],*] <;> rfl)
  | (rw [stepLocal]
     simp only [patternsObservationAllowed, patternObservationAllowed,
       literalObservationAllowed, literalListObservationAllowed,
       matchPatterns, matchPattern, BEq.beq, List.beq,
       String.reduceEq, String.reduceBEq, decide_true, decide_false,
       Value.equal, Value.equalList, List.nil_append, List.cons_append,
       Option.bind_some, Option.bind_none,
       Bool.true_and, Bool.false_and, Bool.and_true, Bool.and_false,
       Bool.not_true, Bool.not_false, Bool.true_eq_false, Bool.false_eq_true,
       ↓reduceIte, ↓reduceDIte, $[$contracts:term],*] <;> rfl))

macro "erlean_step" : tactic => `(tactic| erlean_step [])

section Examples

example (world : CodeWorld) (value : Value) (context : Context) (stack : List Frame) :
    stepLocal world ⟨.eval (.lit value), context, stack⟩ =
      .next ⟨.ret [value], context, stack⟩ := by
  erlean_step

example (world : CodeWorld) (values : Values) (context : Context) :
    stepLocal world ⟨.ret values, context, []⟩ = .halt (.returned values) := by
  erlean_step

example (world : CodeWorld) (state next : LocalState)
    (contract : stepLocal world state = .next next) :
    stepLocal world state = .next next := by
  erlean_step [contract]

example (world : CodeWorld) (value : Value) (context : Context)
    (stack : List Frame) (binder : VarId) (guard body : Expr) :
    stepLocal world ⟨.select [value] [([.var binder], guard, body)], context, stack⟩ =
      .next ⟨.eval guard, { context with env := [(binder, value)] ++ context.env },
        .guard context [(binder, value)] [value] body [] :: stack⟩ := by
  erlean_step

-- The guard rejects even a reflexive runner equation: this tactic must not
-- consume a remaining execution relation by accident.
example (world : CodeWorld) (fuel : Nat) (state : LocalState) :
    run (stepLocal world) fuel state = run (stepLocal world) fuel state := by
  fail_if_success erlean_step
  rfl

end Examples

end Erlean.Logic
