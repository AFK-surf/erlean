import Erlean.Examples.HigherOrder.Imported
import Erlean.Examples.Sequential.Reverse

namespace Erlean.Examples

open Core Semantics Logic

def mapBody : Expr :=
  match importedHigherOrderModule.functions with
  | fn :: _ => fn.body
  | [] => .lit .nil

def identityCallback (original : Value) : Value :=
  .closure "higher_order" 0 [(1, original), (0, original)] []

def mapState (original xs : Value) (stack : List Frame) : LocalState :=
  { control := .eval mapBody
    context := ⟨"higher_order", [(0, identityCallback original), (1, xs)]⟩
    stack := stack }

def mapContinuationContext (original head tail : Value) : Context :=
  ⟨"higher_order", [(5, head), (2, identityCallback original), (3, head), (4, tail),
    (0, identityCallback original), (1, .cons head tail)]⟩

def mapContinuation (original head tail : Value) : Frame :=
  .bind (mapContinuationContext original head tail) [6] (.cons (.var 5) (.var 6))

theorem map_nil (original : Value) (stack : List Frame) :
    runLocal 11 [importedHigherOrderModule] (mapState original .nil stack) =
      .exhausted {
        control := .ret [.nil]
        context := ⟨"higher_order", [(2, identityCallback original), (0, identityCallback original), (1, .nil)]⟩
        stack := stack } := by
  simp [runLocal, run, mapState, mapBody, importedHigherOrderModule, stepLocal,
    nextControl, startCollect, finishCollect, Env.lookup, patternsObservationAllowed, patternObservationAllowed,
    literalObservationAllowed, matchPatterns, matchPattern,
    BEq.beq, List.beq, Value.equal]

theorem map_cons (original head tail : Value) (stack : List Frame) :
    runLocal 33 [importedHigherOrderModule] (mapState original (.cons head tail) stack) =
      .exhausted (mapState original tail (mapContinuation original head tail :: stack)) := by
  simp [runLocal, run, mapState, mapBody, importedHigherOrderModule, stepLocal,
    nextControl, startCollect, finishCollect, Env.lookup, patternsObservationAllowed, patternObservationAllowed,
    literalObservationAllowed, matchPatterns, matchPattern,
    BEq.beq, List.beq, Value.equal, identityCallback, applyClosure, recursiveEnv,
    invoke, lookupFunction, mapContinuation, mapContinuationContext]

theorem map_finish (original head tail mapped : Value) (inner : Context) (stack : List Frame) :
    runLocal 6 [importedHigherOrderModule]
      { control := .ret [mapped], context := inner, stack := mapContinuation original head tail :: stack } =
      .exhausted {
        control := .ret [.cons head mapped]
        context := { mapContinuationContext original head tail with
          env := (6, mapped) :: (mapContinuationContext original head tail).env }
        stack := stack } := by
  simp [runLocal, run, stepLocal, mapContinuation, mapContinuationContext,
    nextControl, startCollect, finishCollect, Env.lookup]

/-- The recursive contract is parametric in the caller's continuation stack. -/
theorem map_returns (original : Value) (xs : List Value) (stack : List Frame) :
    ∃ fuel context, runLocal fuel [importedHigherOrderModule] (mapState original (encodeList xs) stack) =
      .exhausted { control := .ret [encodeList xs], context := context, stack := stack } := by
  induction xs generalizing stack with
  | nil => exact ⟨11, _, map_nil original stack⟩
  | cons head tail ih =>
    obtain ⟨fuel, context, h⟩ := ih (mapContinuation original head (encodeList tail) :: stack)
    refine ⟨33 + (fuel + 6),
      { mapContinuationContext original head (encodeList tail) with
        env := (6, encodeList tail) :: (mapContinuationContext original head (encodeList tail)).env }, ?_⟩
    rw [show runLocal (33 + (fuel + 6)) [importedHigherOrderModule]
        (mapState original (encodeList (head :: tail)) stack) =
        runLocal (fuel + 6) [importedHigherOrderModule]
          (mapState original (encodeList tail) (mapContinuation original head (encodeList tail) :: stack)) from
      run_of_prefix (map_cons original head (encodeList tail) stack) (fuel + 6)]
    rw [show runLocal (fuel + 6) [importedHigherOrderModule]
        (mapState original (encodeList tail) (mapContinuation original head (encodeList tail) :: stack)) =
        runLocal 6 [importedHigherOrderModule]
          { control := .ret [encodeList tail], context := context, stack := mapContinuation original head (encodeList tail) :: stack }
          from run_of_prefix h 6]
    exact map_finish original head (encodeList tail) (encodeList tail) context stack

theorem identityCallback_make (xs : Value) :
    makeClosureValue [importedHigherOrderModule]
      ⟨"higher_order", [(1, xs), (0, xs)]⟩ 0 = .ok (identityCallback xs) := by
  cbv

theorem map_identity_entry (xs : Value) :
    runLocal 23 [importedHigherOrderModule] (initialCall "higher_order" "map_identity" [xs]) =
      .exhausted (mapState xs xs []) := by
  simp [runLocal, run, initialCall, mapState, mapBody, importedHigherOrderModule, stepLocal,
    nextControl, startCollect, finishCollect, Env.lookup, patternsObservationAllowed, patternObservationAllowed,
    matchPatterns, BEq.beq,
    List.beq, Value.equal, identityCallback, invoke, lookupFunction, makeClosureValue,
    Pure.pure, Except.pure, Bind.bind, Except.bind]

theorem map_identity_evaluates (xs : List Value) :
    Evaluates (stepLocal [importedHigherOrderModule])
      (initialCall "higher_order" "map_identity" [encodeList xs])
      (.returned [encodeList xs]) := by
  obtain ⟨fuel, context, h⟩ := map_returns (encodeList xs) xs []
  apply evaluates_of_prefix (map_identity_entry (encodeList xs))
  exact evaluates_of_prefix h (.halt rfl)

theorem map_identity_totalCorrect :
    TotalCorrect [importedHigherOrderModule] "higher_order" "map_identity"
      (fun args => ∃ xs, args = [encodeList xs])
      (fun args result => result = .returned args) := by
  apply totalCorrect_of_evaluates
  intro args hp
  obtain ⟨xs, rfl⟩ := hp
  exact ⟨.returned [encodeList xs], map_identity_evaluates xs, trivial, rfl⟩

end Erlean.Examples
