import Erlean.Examples.Sequential.Imported
import Erlean.Logic.Rules

namespace Erlean.Examples

open Core Semantics Logic

def encodeList (values : List Value) : Value := values.foldr Value.cons .nil

def reverseWorkerBody : Expr :=
  .caseE (.values [.var 0, .var 1])
    [([.lit .nil, .var 2], .lit (.atom "true"), .var 2),
     ([.cons (.var 2) (.var 3), .var 4], .lit (.atom "true"),
      .apply (.funRef "reverse_acc" 2) [.var 3, .cons (.var 2) (.var 4)]),
     ([.var 2, .var 3], .lit (.atom "true"),
      .primop "match_fail" [.tuple [.lit (.atom "function_clause"), .var 2, .var 3]])]

/-- Link the compact proof view to the unmodified imported definition. -/
theorem reverseWorker_imported :
    lookupFunction [importedSequentialModule] "sequential" "reverse_acc" 2 =
      some ⟨"reverse_acc", [0, 1], reverseWorkerBody⟩ := by
  cbv

def reverseWorkerState (xs acc : Value) : LocalState :=
  { control := .eval reverseWorkerBody
    context := ⟨"sequential", [(0, xs), (1, acc)]⟩ }

theorem reverseWorker_nil (acc : Value) :
    runLocal 12 [importedSequentialModule] (reverseWorkerState .nil acc) =
      .halted (.returned [acc]) := by
  simp [runLocal, run, reverseWorkerState, reverseWorkerBody, stepLocal,
    nextControl, startCollect, finishCollect, Env.lookup, patternsObservationAllowed, patternObservationAllowed,
    literalObservationAllowed, matchPatterns, matchPattern,
    BEq.beq, List.beq, Value.equal]

theorem reverseWorker_cons (head tail acc : Value) :
    runLocal 22 [importedSequentialModule] (reverseWorkerState (.cons head tail) acc) =
      .exhausted (reverseWorkerState tail (.cons head acc)) := by
  simp [runLocal, run, reverseWorkerState, reverseWorkerBody, stepLocal,
    nextControl, startCollect, finishCollect, Env.lookup, patternsObservationAllowed, patternObservationAllowed,
    literalObservationAllowed, matchPatterns, matchPattern,
    BEq.beq, List.beq, Value.equal, invoke, importedSequentialModule,
    lookupFunction]

theorem reverse_entry (xs : Value) :
    runLocal 20 [importedSequentialModule] (initialCall "sequential" "reverse" [xs]) =
      .exhausted (reverseWorkerState xs .nil) := by
  simp [runLocal, run, initialCall, reverseWorkerState, reverseWorkerBody, stepLocal,
    nextControl, startCollect, finishCollect, Env.lookup, patternsObservationAllowed, patternObservationAllowed,
    matchPatterns,
    BEq.beq, List.beq, Value.equal, invoke, importedSequentialModule, lookupFunction]

/-- Induction is over source list length, not a fixed interpreter budget. -/
theorem reverseWorker_evaluates (xs : List Value) (acc : Value) :
    Evaluates (stepLocal [importedSequentialModule])
      (reverseWorkerState (encodeList xs) acc)
      (.returned [xs.reverse.foldr Value.cons acc]) := by
  induction xs generalizing acc with
  | nil => exact run_halted_sound _ 12 (reverseWorker_nil acc)
  | cons head tail ih =>
    have composed := evaluates_of_prefix (reverseWorker_cons head (encodeList tail) acc)
      (ih (.cons head acc))
    simpa [encodeList, List.reverse_cons, List.foldr_append] using composed

theorem reverse_evaluates (xs : List Value) :
    Evaluates (stepLocal [importedSequentialModule])
      (initialCall "sequential" "reverse" [encodeList xs])
      (.returned [encodeList xs.reverse]) :=
  evaluates_of_prefix (reverse_entry (encodeList xs)) (reverseWorker_evaluates xs .nil)

theorem encodeList_injective (xs ys : List Value) (h : encodeList xs = encodeList ys) : xs = ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all [encodeList]
  | cons head tail ih =>
    cases ys with
    | nil => simp [encodeList] at h
    | cons other rest =>
      have eq := Value.cons.inj h
      rw [eq.1, ih rest eq.2]

theorem reverse_totalCorrect :
    TotalCorrect [importedSequentialModule] "sequential" "reverse"
      (fun args => ∃ xs, args = [encodeList xs])
      (fun args result => ∀ xs, args = [encodeList xs] →
        result = .returned [encodeList xs.reverse]) := by
  apply totalCorrect_of_evaluates
  intro args hp
  obtain ⟨xs, rfl⟩ := hp
  refine ⟨.returned [encodeList xs.reverse], reverse_evaluates xs, trivial, ?_⟩
  intro ys h
  have eq := encodeList_injective xs ys (List.cons.inj h).1
  subst ys
  rfl

end Erlean.Examples
