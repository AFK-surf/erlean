import Erlean.Examples.Dijkstra.ExecutionBase
import Erlean.Examples.Dijkstra.Model

namespace Erlean.Examples.Dijkstra

open Core Semantics Logic

def settledContext (vertex other distance : Nat) (rest : DijkstraAlgorithm.Distances) : Context :=
  ⟨"dijkstra", [(2, encodeNat vertex), (3, encodeNat other), (4, encodeNat distance),
    (5, encodeQueue rest), (0, encodeNat vertex), (1, encodeQueue ((other, distance) :: rest))]⟩

def insertContext (vertex distance other oldDistance : Nat)
    (rest : DijkstraAlgorithm.Distances) : Context :=
  ⟨"dijkstra", [(3, encodeNat vertex), (4, encodeNat distance), (5, encodeNat other),
    (6, encodeNat oldDistance), (7, encodeQueue rest),
    (0, encodeNat vertex), (1, encodeNat distance),
    (2, encodeQueue ((other, oldDistance) :: rest))]⟩

def insertContinuation (vertex distance other oldDistance : Nat)
    (rest : DijkstraAlgorithm.Distances) : Frame :=
  .bind (insertContext vertex distance other oldDistance rest) [8]
    (.cons (.tuple [.var 5, .var 6]) (.var 8))

macro "dijkstra_helper_simp" : tactic => `(tactic|
  simp_all [runLocal, run, world, callState, settledState, insertState, reverseState,
    settledFunction, insertFunction, reverseFunction, importedDijkstraModule,
    stepLocal, nextControl, startCollect, finishCollect, Env.lookup,
    patternsObservationAllowed, patternObservationAllowed, literalObservationAllowed,
    matchPatterns, matchPattern, BEq.beq, List.beq, Value.equal,
    Value.isPublic, Value.publicList, Value.exactComparable,
    builtin, boolean, invoke, lookupFunction, encodeNat, encodeEntry, encodeQueue,
    encodeList, encodeBool, settledContext, insertContext, insertContinuation])

theorem settled_nil (vertex : Nat) (stack : List Frame) :
    runLocal 11 world (settledState vertex [] stack) = .exhausted {
      control := .ret [.atom "false"],
      context := ⟨"dijkstra", [(2, encodeNat vertex), (0, encodeNat vertex), (1, .nil)]⟩,
      stack := stack } := by
  dijkstra_helper_simp

theorem settled_found (vertex distance : Nat) (rest : DijkstraAlgorithm.Distances)
    (stack : List Frame) :
    runLocal 26 world (settledState vertex ((vertex, distance) :: rest) stack) =
      .exhausted {
        control := .ret [.atom "true"],
        context := settledContext vertex vertex distance rest, stack := stack } := by
  dijkstra_helper_simp

theorem settled_skip (vertex other distance : Nat) (rest : DijkstraAlgorithm.Distances)
    (different : vertex ≠ other) (stack : List Frame) :
    runLocal 33 world (settledState vertex ((other, distance) :: rest) stack) =
      .exhausted (settledState vertex rest stack) := by
  have integerDifferent : ((vertex : Int) == (other : Int)) = false := by
    apply beq_eq_false_iff_ne.mpr
    intro equal
    exact different (Int.ofNat.inj equal)
  have naturalDifferent : (vertex == other) = false := by simp [different]
  dijkstra_helper_simp

theorem settled_returns (vertex : Nat) (queue : DijkstraAlgorithm.Distances)
    (stack : List Frame) :
    Returns (settledState vertex queue stack) (encodeBool (DijkstraAlgorithm.seen vertex queue)) := by
  induction queue with
  | nil => exact ⟨11, _, settled_nil vertex stack⟩
  | cons entry rest ih =>
    rcases entry with ⟨other, distance⟩
    by_cases same : vertex = other
    · subst other
      refine ⟨26, settledContext vertex vertex distance rest, ?_⟩
      simpa [DijkstraAlgorithm.seen, encodeBool, settledState, callState] using
        settled_found vertex distance rest stack
    · obtain ⟨fuel, context, h⟩ := ih
      refine ⟨33 + fuel, context, ?_⟩
      rw [show runLocal (33 + fuel) world (settledState vertex ((other, distance) :: rest) stack) =
        runLocal fuel world (settledState vertex rest stack) from
          run_of_prefix (settled_skip vertex other distance rest same stack) fuel]
      have unequal : (other == vertex) = false := by simp [Ne.symm same]
      simpa [DijkstraAlgorithm.seen, unequal, settledState, callState] using h

theorem insert_nil (vertex distance : Nat) (stack : List Frame) :
    runLocal 21 world (insertState vertex distance [] stack) = .exhausted {
      control := .ret [encodeQueue [(vertex, distance)]],
      context := ⟨"dijkstra", [(3, encodeNat vertex), (4, encodeNat distance),
        (0, encodeNat vertex), (1, encodeNat distance), (2, .nil)]⟩,
      stack := stack } := by
  dijkstra_helper_simp

theorem insert_before (vertex distance other oldDistance : Nat)
    (rest : DijkstraAlgorithm.Distances) (before : distance ≤ oldDistance) (stack : List Frame) :
    runLocal 44 world (insertState vertex distance ((other, oldDistance) :: rest) stack) =
      .exhausted {
        control := .ret [encodeQueue ((vertex, distance) :: (other, oldDistance) :: rest)],
        context := insertContext vertex distance other oldDistance rest, stack := stack } := by
  dijkstra_helper_simp

theorem insert_after (vertex distance other oldDistance : Nat)
    (rest : DijkstraAlgorithm.Distances) (after : ¬ distance ≤ oldDistance) (stack : List Frame) :
    runLocal 38 world (insertState vertex distance ((other, oldDistance) :: rest) stack) =
      .exhausted (insertState vertex distance rest
        (insertContinuation vertex distance other oldDistance rest :: stack)) := by
  dijkstra_helper_simp

theorem insert_finish (vertex distance other oldDistance : Nat)
    (rest result : DijkstraAlgorithm.Distances) (context : Context) (stack : List Frame) :
    runLocal 10 world {
      control := .ret [encodeQueue result], context := context,
      stack := insertContinuation vertex distance other oldDistance rest :: stack } =
    .exhausted {
      control := .ret [encodeQueue ((other, oldDistance) :: result)],
      context := { insertContext vertex distance other oldDistance rest with
        env := (8, encodeQueue result) :: (insertContext vertex distance other oldDistance rest).env },
      stack := stack } := by
  dijkstra_helper_simp

theorem insert_returns (vertex distance : Nat) (queue : DijkstraAlgorithm.Distances)
    (stack : List Frame) :
    Returns (insertState vertex distance queue stack)
      (encodeQueue (DijkstraAlgorithm.insert vertex distance queue)) := by
  induction queue generalizing stack with
  | nil => exact ⟨21, _, insert_nil vertex distance stack⟩
  | cons entry rest ih =>
    rcases entry with ⟨other, oldDistance⟩
    by_cases before : distance ≤ oldDistance
    · refine ⟨44, insertContext vertex distance other oldDistance rest, ?_⟩
      simpa [DijkstraAlgorithm.insert, before, insertState, callState] using
        insert_before vertex distance other oldDistance rest before stack
    · obtain ⟨fuel, context, h⟩ :=
        ih (insertContinuation vertex distance other oldDistance rest :: stack)
      refine ⟨38 + (fuel + 10),
        { insertContext vertex distance other oldDistance rest with
          env := (8, encodeQueue (DijkstraAlgorithm.insert vertex distance rest)) ::
            (insertContext vertex distance other oldDistance rest).env }, ?_⟩
      rw [show runLocal (38 + (fuel + 10)) world
          (insertState vertex distance ((other, oldDistance) :: rest) stack) =
          runLocal (fuel + 10) world (insertState vertex distance rest
            (insertContinuation vertex distance other oldDistance rest :: stack)) from
        run_of_prefix (insert_after vertex distance other oldDistance rest before stack) (fuel + 10)]
      rw [show runLocal (fuel + 10) world (insertState vertex distance rest
          (insertContinuation vertex distance other oldDistance rest :: stack)) =
          runLocal 10 world {
            control := .ret [encodeQueue (DijkstraAlgorithm.insert vertex distance rest)],
            context := context,
            stack := insertContinuation vertex distance other oldDistance rest :: stack } from
        run_of_prefix h 10]
      simpa [DijkstraAlgorithm.insert, before, insertState, callState] using
        insert_finish vertex distance other oldDistance rest
          (DijkstraAlgorithm.insert vertex distance rest) context stack

theorem reverse_nil (acc : Value) (stack : List Frame) :
    runLocal 11 world (reverseState .nil acc stack) = .exhausted {
      control := .ret [acc],
      context := ⟨"dijkstra", [(2, acc), (0, .nil), (1, acc)]⟩,
      stack := stack } := by
  dijkstra_helper_simp

theorem reverse_cons (head tail acc : Value) (stack : List Frame) :
    runLocal 22 world (reverseState (.cons head tail) acc stack) =
      .exhausted (reverseState tail (.cons head acc) stack) := by
  dijkstra_helper_simp

theorem reverse_returns (xs : List Value) (acc : Value) (stack : List Frame) :
    Returns (reverseState (encodeList xs) acc stack) (xs.reverse.foldr Value.cons acc) := by
  induction xs generalizing acc with
  | nil => exact ⟨11, _, reverse_nil acc stack⟩
  | cons head tail ih =>
    obtain ⟨fuel, context, h⟩ := ih (.cons head acc)
    refine ⟨22 + fuel, context, ?_⟩
    rw [show runLocal (22 + fuel) world (reverseState (encodeList (head :: tail)) acc stack) =
      runLocal fuel world (reverseState (encodeList tail) (.cons head acc) stack) from
        run_of_prefix (reverse_cons head (encodeList tail) acc stack) fuel]
    simpa [List.reverse_cons, List.foldr_append, reverseState, callState] using h

theorem reverse_queue_returns (queue acc : DijkstraAlgorithm.Distances)
    (stack : List Frame) :
    Returns (reverseState (encodeQueue queue) (encodeQueue acc) stack)
      (encodeQueue (queue.reverse ++ acc)) := by
  simpa [encodeQueue, encodeList, List.map_append, List.map_reverse, List.foldr_append] using
    reverse_returns (queue.map encodeEntry) (encodeQueue acc) stack

end Erlean.Examples.Dijkstra
