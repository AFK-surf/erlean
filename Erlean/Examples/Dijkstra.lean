import Erlean.Examples.DijkstraSearch
import Erlean.Examples.DijkstraAlgorithm

/-!
Universal total correctness for the retained OTP Core implementation of Dijkstra.
The mathematical graph-size termination proof is composed with execution of the
actual source validators, recursive search, and final reversal. No certificate,
successful-run assumption, or fixed graph-size limit appears in the final
contract. Vertices and weights are nonnegative unbounded integers encoded from
Lean naturals; malformed inputs are outside this contract.
-/

namespace Erlean.Examples.Dijkstra

open Core Semantics Logic DijkstraCertificate

def distancesContext (source : Nat) (graph : Graph) : Context :=
  ⟨"dijkstra", [(2, encodeNat source), (3, encodeGraph graph),
    (0, encodeNat source), (1, encodeGraph graph)]⟩

def distancesSourceCases : List Clause :=
  match distancesFunction.body with
  | .caseE _ ((_, _, .caseE _ branches) :: _) => branches
  | _ => []

def distancesEdgesCases : List Clause :=
  match distancesSourceCases with
  | (_, _, .caseE _ branches) :: _ => branches
  | _ => []

def distancesReverseBody : Expr :=
  match distancesEdgesCases with
  | (_, _, .letE _ _ body) :: _ => body
  | _ => .lit .nil

def distancesSourceFrame (source : Nat) (graph : Graph) : Frame :=
  .select (distancesContext source graph) distancesSourceCases

def distancesEdgesFrame (source : Nat) (graph : Graph) : Frame :=
  .select (distancesContext source graph) distancesEdgesCases

def distancesReverseFrame (source : Nat) (graph : Graph) : Frame :=
  .bind (distancesContext source graph) [4] distancesReverseBody

local macro "distances_simp" : tactic => `(tactic|
  simp_all [runLocal, run, world, initialCall, callState,
    distancesFunction, nonnegativeState, nonnegativeFunction, validEdgesState,
    validEdgesFunction, searchState, searchFunction, reverseState, reverseFunction,
    importedDijkstraModule, stepLocal, nextControl, startCollect, finishCollect,
    Env.lookup, patternsObservationAllowed, patternObservationAllowed,
    literalObservationAllowed, matchPatterns, matchPattern, BEq.beq, List.beq,
    Value.equal, Value.isPublic, Value.publicList, Value.exactComparable,
    builtin, boolean, invoke, lookupFunction, encodeNat, encodeEntry, encodeQueue,
    encodeGraph, encodeEdge, encodeList, distancesContext, distancesSourceCases,
    distancesEdgesCases, distancesReverseBody, distancesSourceFrame,
    distancesEdgesFrame, distancesReverseFrame,
    Pure.pure, Except.pure, Bind.bind, Except.bind])

theorem distances_source_entry (source : Nat) (graph : Graph) :
    runLocal 25 world (initialCall "dijkstra" "distances" [encodeNat source, encodeGraph graph]) =
      .exhausted (nonnegativeState source [distancesSourceFrame source graph]) := by
  distances_simp

theorem distances_source_resume (source : Nat) (graph : Graph) (context : Context) :
    runLocal 10 world {
      control := .ret [.atom "true"]
      context := context
      stack := [distancesSourceFrame source graph] } =
      .exhausted (validEdgesState graph [distancesEdgesFrame source graph]) := by
  distances_simp

theorem distances_edges_resume (source : Nat) (graph : Graph) (context : Context) :
    runLocal 22 world {
      control := .ret [.atom "true"]
      context := context
      stack := [distancesEdgesFrame source graph] } =
      .exhausted (searchState [(source, 0)] graph [] [distancesReverseFrame source graph]) := by
  distances_simp

theorem distances_search_resume (source : Nat) (graph : Graph)
    (result : DijkstraAlgorithm.Distances) (context : Context) :
    runLocal 8 world {
      control := .ret [encodeQueue result]
      context := context
      stack := [distancesReverseFrame source graph] } =
      .exhausted (reverseState (encodeQueue result) (encodeQueue []) []) := by
  distances_simp

/-- This statement simulates a model result; the universal theorem below
    discharges its computed-result premise for every finite input graph. -/
theorem distances_evaluates (source : Nat) (graph : Graph)
    (result : DijkstraAlgorithm.Distances)
    (computed : DijkstraAlgorithm.distances source graph = some result) :
    Evaluates (stepLocal world)
      (initialCall "dijkstra" "distances" [encodeNat source, encodeGraph graph])
      (.returned [encodeQueue result]) := by
  cases searched : DijkstraAlgorithm.search (graph.length + 1) [(source, 0)] graph [] with
  | none => simp [DijkstraAlgorithm.distances, searched] at computed
  | some settled =>
    have resultEqual : settled.reverse = result := by
      simpa [DijkstraAlgorithm.distances, searched] using computed
    obtain ⟨sourceFuel, sourceContext, sourceRun⟩ :=
      nonnegative_returns source [distancesSourceFrame source graph]
    have sourceChecked := prefix_compose (distances_source_entry source graph) sourceRun
    have toEdges := prefix_compose sourceChecked (distances_source_resume source graph sourceContext)
    obtain ⟨edgesFuel, edgesContext, edgesRun⟩ :=
      valid_edges_returns graph [distancesEdgesFrame source graph]
    have edgesChecked := prefix_compose toEdges edgesRun
    have toSearch := prefix_compose edgesChecked (distances_edges_resume source graph edgesContext)
    obtain ⟨searchFuel, searchContext, searchRun⟩ := search_returns (graph.length + 1)
      [(source, 0)] graph [] settled [distancesReverseFrame source graph] searched
    have searchedCore := prefix_compose toSearch searchRun
    have toReverse := prefix_compose searchedCore
      (distances_search_resume source graph settled searchContext)
    obtain ⟨reverseFuel, reverseContext, reverseRun⟩ := reverse_queue_returns settled [] []
    have returned := prefix_compose toReverse reverseRun
    have finish : runLocal 1 world {
        control := .ret [encodeQueue (settled.reverse ++ [])]
        context := reverseContext
        stack := [] } = .halted (.returned [encodeQueue result]) := by
      simp [runLocal, run, stepLocal, resultEqual]
    exact evaluates_of_prefix returned (run_halted_sound _ 1 finish)

/-- Every arbitrary finite nonnegative graph executes to completion in the
    imported Core semantics and returns its attained shortest distances. -/
theorem dijkstra_terminates_correct (source : Nat) (graph : Graph) :
    ∃ result,
      Evaluates (stepLocal world)
        (initialCall "dijkstra" "distances" [encodeNat source, encodeGraph graph])
        (.returned [encodeQueue result]) ∧
      DijkstraAlgorithm.ResultCorrect graph source result := by
  obtain ⟨result, computed, correct⟩ := DijkstraAlgorithm.distances_total source graph
  exact ⟨result, distances_evaluates source graph result computed, correct⟩

/-- Universally quantified graph/source parameters avoid any dependence on
    decoding or an unproved input-encoding injectivity assumption. -/
theorem dijkstra_total_correct (source : Nat) (graph : Graph) :
    TotalCorrect world "dijkstra" "distances"
      (fun args => args = [encodeNat source, encodeGraph graph])
      (fun _ outcome => ∃ result,
        outcome = .returned [encodeQueue result] ∧
        DijkstraAlgorithm.ResultCorrect graph source result) := by
  apply totalCorrect_of_evaluates
  intro args inputs
  subst args
  obtain ⟨result, evaluated, correct⟩ := dijkstra_terminates_correct source graph
  exact ⟨.returned [encodeQueue result], evaluated, trivial, result, rfl, correct⟩

end Erlean.Examples.Dijkstra
