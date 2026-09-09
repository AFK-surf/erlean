import Erlean.Examples.DijkstraHelpers

namespace Erlean.Examples.Dijkstra

open Core Semantics Logic DijkstraCertificate

def expandState (vertex distance : Nat) (edges : Graph)
    (queue : DijkstraAlgorithm.Distances) (stack : List Frame) : LocalState :=
  callState expandFunction [encodeNat vertex, encodeNat distance, encodeGraph edges,
    encodeQueue queue] stack

theorem expandState_stack (vertex distance : Nat) (edges : Graph)
    (queue : DijkstraAlgorithm.Distances) (stack : List Frame) :
    (expandState vertex distance edges queue stack).stack = stack := rfl

theorem insertState_stack (vertex distance : Nat)
    (queue : DijkstraAlgorithm.Distances) (stack : List Frame) :
    (insertState vertex distance queue stack).stack = stack := rfl

def expandContext (vertex distance : Nat) (edge : Edge) (rest : Graph)
    (queue : DijkstraAlgorithm.Distances) : Context :=
  ⟨"dijkstra", [(4, encodeNat vertex), (5, encodeNat distance),
    (6, encodeNat edge.source), (7, encodeNat edge.target), (8, encodeNat edge.weight),
    (9, encodeGraph rest), (10, encodeQueue queue),
    (0, encodeNat vertex), (1, encodeNat distance),
    (2, encodeGraph (edge :: rest)), (3, encodeQueue queue)]⟩

def expandInsertContext (vertex distance : Nat) (edge : Edge) (rest : Graph)
    (queue : DijkstraAlgorithm.Distances) : Context :=
  { expandContext vertex distance edge rest queue with
    env := (11, encodeNat (distance + edge.weight)) ::
      (expandContext vertex distance edge rest queue).env }

def expandInsertContinuation (vertex distance : Nat) (edge : Edge) (rest : Graph)
    (queue : DijkstraAlgorithm.Distances) : Frame :=
  .bind (expandInsertContext vertex distance edge rest queue) [12]
    (.apply (.funRef "expand" 4) [.var 4, .var 5, .var 9, .var 12])

def expandKeepClauses : List Clause :=
  [([.tuple [.var 11, .var 12]], .lit (.atom "true"),
      .tuple [.var 11, .cons (.tuple [.var 6, .var 7, .var 8]) (.var 12)]),
   ([.var 11], .lit (.atom "true"),
      .primop "match_fail" [.tuple [.lit (.atom "badmatch"), .var 11]])]

def expandKeepContinuation (vertex distance : Nat) (edge : Edge) (rest : Graph)
    (queue : DijkstraAlgorithm.Distances) : Frame :=
  .select (expandContext vertex distance edge rest queue) expandKeepClauses

local macro "expand_simp" : tactic => `(tactic|
  simp_all [runLocal, run, expandState, callState, expandFunction, insertState,
    insertFunction, importedDijkstraModule, world, stepLocal, nextControl,
    startCollect, finishCollect, Env.lookup, patternsObservationAllowed,
    patternObservationAllowed, literalObservationAllowed, matchPatterns, matchPattern,
    BEq.beq, List.beq, Value.equal, Value.isPublic, Value.publicList,
    Value.exactComparable, invoke, lookupFunction, builtin, boolean,
    encodeGraph, encodeEdge, encodeQueue, encodeEntry, encodeList, encodeNat,
    expandContext, expandInsertContext, expandInsertContinuation,
    expandKeepContinuation, expandKeepClauses,
    Pure.pure, Except.pure, Bind.bind, Except.bind, Int.natCast_add])

theorem expand_nil (vertex distance : Nat) (queue : DijkstraAlgorithm.Distances)
    (stack : List Frame) :
    runLocal 19 world (expandState vertex distance [] queue stack) =
      .exhausted {
        control := .ret [.tuple [encodeQueue queue, encodeGraph []]]
        context := ⟨"dijkstra", [(4, encodeNat vertex), (5, encodeNat distance),
          (6, encodeQueue queue), (0, encodeNat vertex), (1, encodeNat distance),
          (2, encodeGraph []), (3, encodeQueue queue)]⟩
        stack := stack } := by
  expand_simp

theorem expand_outgoing_prefix (vertex distance : Nat) (edge : Edge) (rest : Graph)
    (queue : DijkstraAlgorithm.Distances) (stack : List Frame)
    (outgoing : edge.source = vertex) :
    runLocal 50 world (expandState vertex distance (edge :: rest) queue stack) =
      .exhausted (insertState edge.target (distance + edge.weight) queue
        (expandInsertContinuation vertex distance edge rest queue :: stack)) := by
  expand_simp

theorem expand_after_insert (vertex distance : Nat) (edge : Edge) (rest : Graph)
    (queue inserted : DijkstraAlgorithm.Distances) (inner : Context) (stack : List Frame) :
    runLocal 12 world {
      control := .ret [encodeQueue inserted]
      context := inner
      stack := expandInsertContinuation vertex distance edge rest queue :: stack } =
      .exhausted (expandState vertex distance rest inserted stack) := by
  expand_simp

theorem expand_keep_prefix (vertex distance : Nat) (edge : Edge) (rest : Graph)
    (queue : DijkstraAlgorithm.Distances) (stack : List Frame)
    (outgoing : edge.source ≠ vertex) :
    runLocal 42 world (expandState vertex distance (edge :: rest) queue stack) =
      .exhausted (expandState vertex distance rest queue
        (expandKeepContinuation vertex distance edge rest queue :: stack)) := by
  have opposite : vertex ≠ edge.source := Ne.symm outgoing
  have unequal : ((vertex : Int) == (edge.source : Int)) = false :=
    beq_eq_false_iff_ne.mpr (fun same => opposite (Int.ofNat.inj same))
  expand_simp

theorem expand_keep_finish (vertex distance : Nat) (edge : Edge) (rest remaining : Graph)
    (queue expanded : DijkstraAlgorithm.Distances) (inner : Context) (stack : List Frame) :
    runLocal 19 world {
      control := .ret [.tuple [encodeQueue expanded, encodeGraph remaining]]
      context := inner
      stack := expandKeepContinuation vertex distance edge rest queue :: stack } =
      .exhausted {
        control := .ret [.tuple [encodeQueue expanded, encodeGraph (edge :: remaining)]]
        context := {
          expandContext vertex distance edge rest queue with
          env := [(11, encodeQueue expanded), (12, encodeGraph remaining)] ++
            (expandContext vertex distance edge rest queue).env }
        stack := stack } := by
  expand_simp

/-- The actual imported expansion agrees with the pure model for arbitrary
    finite edges and queue, preserving an arbitrary caller continuation. -/
theorem expand_returns (vertex distance : Nat) (edges : Graph)
    (queue : DijkstraAlgorithm.Distances) (stack : List Frame) :
    Returns (expandState vertex distance edges queue stack)
      (.tuple [encodeQueue (DijkstraAlgorithm.expand vertex distance edges queue).1,
        encodeGraph (DijkstraAlgorithm.expand vertex distance edges queue).2]) := by
  induction edges generalizing queue stack with
  | nil => exact ⟨19, _, expand_nil vertex distance queue stack⟩
  | cons edge rest inductionHypothesis =>
    by_cases outgoing : edge.source = vertex
    · obtain ⟨insertFuel, insertContext, inserted⟩ :=
        insert_returns edge.target (distance + edge.weight) queue
          (expandInsertContinuation vertex distance edge rest queue :: stack)
      obtain ⟨restFuel, restContext, restReturned⟩ := inductionHypothesis
        (DijkstraAlgorithm.insert edge.target (distance + edge.weight) queue) stack
      refine ⟨50 + (insertFuel + (12 + restFuel)), restContext, ?_⟩
      simp only [runLocal, insertState_stack, expandState_stack] at inserted restReturned ⊢
      rw [run_of_prefix (expand_outgoing_prefix vertex distance edge rest queue stack outgoing)]
      rw [run_of_prefix inserted]
      rw [run_of_prefix (expand_after_insert vertex distance edge rest queue _ insertContext stack)]
      simpa [DijkstraAlgorithm.expand, outgoing] using restReturned
    · obtain ⟨restFuel, restContext, restReturned⟩ := inductionHypothesis queue
        (expandKeepContinuation vertex distance edge rest queue :: stack)
      refine ⟨42 + (restFuel + 19), {
        expandContext vertex distance edge rest queue with
        env := [(11, encodeQueue (DijkstraAlgorithm.expand vertex distance rest queue).1),
          (12, encodeGraph (DijkstraAlgorithm.expand vertex distance rest queue).2)] ++
          (expandContext vertex distance edge rest queue).env }, ?_⟩
      simp only [runLocal, expandState_stack] at restReturned ⊢
      rw [run_of_prefix (expand_keep_prefix vertex distance edge rest queue stack outgoing)]
      rw [run_of_prefix restReturned]
      simpa [runLocal, DijkstraAlgorithm.expand, outgoing] using
        expand_keep_finish vertex distance edge rest
          (DijkstraAlgorithm.expand vertex distance rest queue).2 queue
          (DijkstraAlgorithm.expand vertex distance rest queue).1 restContext stack

def nonnegativeState (number : Nat) (stack : List Frame) : LocalState :=
  callState nonnegativeFunction [encodeNat number] stack

def validEdgesState (edges : Graph) (stack : List Frame) : LocalState :=
  callState validEdgesFunction [encodeGraph edges] stack

local macro "validation_simp" : tactic => `(tactic|
  simp_all [runLocal, run, nonnegativeState, validEdgesState, callState,
    nonnegativeFunction, validEdgesFunction, importedDijkstraModule, world,
    stepLocal, nextControl, startCollect, finishCollect, Env.lookup,
    patternsObservationAllowed, patternObservationAllowed, literalObservationAllowed,
    matchPatterns, matchPattern, BEq.beq, List.beq, Value.equal,
    Value.isPublic, Value.publicList, Value.exactComparable,
    invoke, lookupFunction, builtin, boolean,
    encodeGraph, encodeEdge, encodeList, encodeNat,
    Pure.pure, Except.pure, Bind.bind, Except.bind])

theorem nonnegative_nat_prefix (number : Nat) (stack : List Frame) :
    runLocal 27 world (nonnegativeState number stack) = .exhausted {
      control := .ret [.atom "true"]
      context := ⟨"dijkstra", [(1, encodeNat number), (0, encodeNat number)]⟩
      stack := stack } := by
  have nonnegative : (0 : Int) ≤ (number : Int) := by omega
  validation_simp

theorem nonnegative_returns (number : Nat) (stack : List Frame) :
    Returns (nonnegativeState number stack) (.atom "true") :=
  ⟨27, _, nonnegative_nat_prefix number stack⟩

theorem valid_edges_nil (stack : List Frame) :
    runLocal 7 world (validEdgesState [] stack) = .exhausted {
      control := .ret [.atom "true"]
      context := ⟨"dijkstra", [(0, encodeGraph [])]⟩
      stack := stack } := by
  validation_simp

/-- Every encoded edge passes all three source-level integer and sign checks.
    No validation branch is bypassed in this execution prefix. -/
theorem valid_edges_cons (edge : Edge) (rest : Graph) (stack : List Frame) :
    runLocal 126 world (validEdgesState (edge :: rest) stack) =
      .exhausted (validEdgesState rest stack) := by
  have sourceNonnegative : (0 : Int) ≤ (edge.source : Int) := by omega
  have targetNonnegative : (0 : Int) ≤ (edge.target : Int) := by omega
  have weightNonnegative : (0 : Int) ≤ (edge.weight : Int) := by omega
  validation_simp

theorem valid_edges_returns (edges : Graph) (stack : List Frame) :
    Returns (validEdgesState edges stack) (.atom "true") := by
  induction edges generalizing stack with
  | nil => exact ⟨7, _, valid_edges_nil stack⟩
  | cons edge rest inductionHypothesis =>
    obtain ⟨fuel, context, returned⟩ := inductionHypothesis stack
    refine ⟨126 + fuel, context, ?_⟩
    simp only [runLocal] at returned ⊢
    rw [run_of_prefix (valid_edges_cons edge rest stack)]
    exact returned

end Erlean.Examples.Dijkstra
