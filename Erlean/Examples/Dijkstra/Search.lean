import Erlean.Examples.Dijkstra.Expand

namespace Erlean.Examples.Dijkstra

open Core Semantics Logic DijkstraCertificate

def searchState (queue : List (Nat × Nat)) (edges : Graph)
    (settled : List (Nat × Nat)) (stack : List Frame) : LocalState :=
  callState searchFunction [encodeQueue queue, encodeGraph edges, encodeQueue settled] stack

def searchContext (vertex distance : Nat) (queue : List (Nat × Nat))
    (edges : Graph) (settled : List (Nat × Nat)) : Context :=
  ⟨"dijkstra", [(3, encodeNat vertex), (4, encodeNat distance), (5, encodeQueue queue),
    (6, encodeGraph edges), (7, encodeQueue settled),
    (0, encodeQueue ((vertex, distance) :: queue)), (1, encodeGraph edges),
    (2, encodeQueue settled)]⟩

/-- Fixed syntactic views; the prefix equations below check these against the
    retained imported body. They are not replacements for source execution. -/
def searchSeenCases : List Clause :=
  match searchFunction.body with
  | .caseE _ (_ :: (_, _, .caseE _ branches) :: _) => branches
  | _ => []

def searchExpandedCases : List Clause :=
  match searchSeenCases with
  | _ :: (_, _, .caseE _ branches) :: _ => branches
  | _ => []

def searchSeenFrame (vertex distance : Nat) (queue : List (Nat × Nat))
    (edges : Graph) (settled : List (Nat × Nat)) : Frame :=
  .select (searchContext vertex distance queue edges settled) searchSeenCases

def searchExpandedFrame (vertex distance : Nat) (queue : List (Nat × Nat))
    (edges : Graph) (settled : List (Nat × Nat)) : Frame :=
  .select (searchContext vertex distance queue edges settled) searchExpandedCases

local macro "search_simp" : tactic => `(tactic|
  simp_all [runLocal, run, world, callState, searchState, searchFunction,
    settledState, settledFunction, expandState, expandFunction, importedDijkstraModule,
    stepLocal, nextControl, startCollect, finishCollect, Env.lookup,
    patternsObservationAllowed, patternObservationAllowed, literalObservationAllowed,
    matchPatterns, matchPattern, BEq.beq, List.beq, Value.equal,
    Value.isPublic, Value.publicList, Value.exactComparable,
    builtin, boolean, invoke, lookupFunction, encodeNat, encodeEntry, encodeQueue,
    encodeGraph, encodeEdge, encodeList, encodeBool, searchContext,
    searchSeenFrame, searchExpandedFrame, searchSeenCases, searchExpandedCases])

theorem search_nil (edges : Graph) (settled : List (Nat × Nat)) (stack : List Frame) :
    runLocal 13 world (searchState [] edges settled stack) = .exhausted {
      control := .ret [encodeQueue settled],
      context := ⟨"dijkstra", [(3, encodeGraph edges), (4, encodeQueue settled),
        (0, .nil), (1, encodeGraph edges), (2, encodeQueue settled)]⟩,
      stack := stack } := by
  search_simp

theorem search_seen_entry (vertex distance : Nat) (queue settled : List (Nat × Nat))
    (edges : Graph) (stack : List Frame) :
    runLocal 21 world (searchState ((vertex, distance) :: queue) edges settled stack) =
      .exhausted (settledState vertex settled
        (searchSeenFrame vertex distance queue edges settled :: stack)) := by
  search_simp

theorem search_stale_resume (vertex distance : Nat) (queue settled : List (Nat × Nat))
    (edges : Graph) (context : Context) (stack : List Frame) :
    runLocal 13 world {
      control := .ret [.atom "true"], context := context,
      stack := searchSeenFrame vertex distance queue edges settled :: stack } =
      .exhausted (searchState queue edges settled stack) := by
  search_simp

theorem search_fresh_resume (vertex distance : Nat) (queue settled : List (Nat × Nat))
    (edges : Graph) (context : Context) (stack : List Frame) :
    runLocal 17 world {
      control := .ret [.atom "false"], context := context,
      stack := searchSeenFrame vertex distance queue edges settled :: stack } =
      .exhausted (expandState vertex distance edges queue
        (searchExpandedFrame vertex distance queue edges settled :: stack)) := by
  search_simp

theorem search_expanded_resume (vertex distance : Nat)
    (queue settled nextQueue : List (Nat × Nat)) (edges remaining : Graph)
    (context : Context) (stack : List Frame) :
    runLocal 21 world {
      control := .ret [.tuple [encodeQueue nextQueue, encodeGraph remaining]], context := context,
      stack := searchExpandedFrame vertex distance queue edges settled :: stack } =
      .exhausted (searchState nextQueue remaining ((vertex, distance) :: settled) stack) := by
  search_simp

theorem prefix_compose
    (first : runLocal n world start = .exhausted middle)
    (second : runLocal m world middle = .exhausted finish) :
    runLocal (n + m) world start = .exhausted finish := by
  rw [show runLocal (n + m) world start = runLocal m world middle from run_of_prefix first m]
  exact second

theorem returns_of_tail_prefix
    (advance : runLocal n world start = .exhausted middle)
    (returned : Returns middle value) (sameStack : middle.stack = start.stack) :
    Returns start value := by
  obtain ⟨fuel, context, finished⟩ := returned
  refine ⟨n + fuel, context, ?_⟩
  simpa only [sameStack] using prefix_compose advance finished

/-- The graph-sized model fuel is a proof index, not a runtime fuel argument.
    Each successful recursive model computation is simulated by finitely many
    actual imported Core steps, with the caller's stack left untouched. -/
theorem search_returns (fuel : Nat) (queue : List (Nat × Nat)) (edges : Graph)
    (settled result : List (Nat × Nat)) (stack : List Frame)
    (computed : DijkstraAlgorithm.search fuel queue edges settled = some result) :
    Returns (searchState queue edges settled stack) (encodeQueue result) := by
  induction fuel generalizing queue edges settled stack result with
  | zero =>
    cases queue with
    | nil =>
      have equal : settled = result := by simpa [DijkstraAlgorithm.search] using computed
      subst result
      exact ⟨13, _, search_nil edges settled stack⟩
    | cons head rest => simp [DijkstraAlgorithm.search] at computed
  | succ fuel ih =>
    cases queue with
    | nil =>
      have equal : settled = result := by simpa [DijkstraAlgorithm.search] using computed
      subst result
      exact ⟨13, _, search_nil edges settled stack⟩
    | cons head rest =>
      rcases head with ⟨vertex, distance⟩
      obtain ⟨seenFuel, seenContext, seenRun⟩ := settled_returns vertex settled
        (searchSeenFrame vertex distance rest edges settled :: stack)
      have initialPrefix := search_seen_entry vertex distance rest settled edges stack
      cases seen : DijkstraAlgorithm.seen vertex settled with
      | true =>
        have recursive : DijkstraAlgorithm.search fuel rest edges settled = some result := by
          simpa [DijkstraAlgorithm.search, seen] using computed
        have actualSeen : runLocal seenFuel world
            (settledState vertex settled (searchSeenFrame vertex distance rest edges settled :: stack)) =
            .exhausted {
              control := .ret [.atom "true"], context := seenContext,
              stack := searchSeenFrame vertex distance rest edges settled :: stack } := by
          simpa [seen, encodeBool, settledState, callState] using seenRun
        have combinedPrefix := prefix_compose (prefix_compose initialPrefix actualSeen)
          (search_stale_resume vertex distance rest settled edges seenContext stack)
        exact returns_of_tail_prefix combinedPrefix (ih rest edges settled result stack recursive) rfl
      | false =>
        let expanded := DijkstraAlgorithm.expand vertex distance edges rest
        have recursive : DijkstraAlgorithm.search fuel expanded.1 expanded.2
            ((vertex, distance) :: settled) = some result := by
          simpa [DijkstraAlgorithm.search, seen, expanded] using computed
        have actualSeen : runLocal seenFuel world
            (settledState vertex settled (searchSeenFrame vertex distance rest edges settled :: stack)) =
            .exhausted {
              control := .ret [.atom "false"], context := seenContext,
              stack := searchSeenFrame vertex distance rest edges settled :: stack } := by
          simpa [seen, encodeBool, settledState, callState] using seenRun
        have toExpand := prefix_compose (prefix_compose initialPrefix actualSeen)
          (search_fresh_resume vertex distance rest settled edges seenContext stack)
        obtain ⟨expandFuel, expandContext, expandedRun⟩ := expand_returns vertex distance edges rest
          (searchExpandedFrame vertex distance rest edges settled :: stack)
        have actualExpanded : runLocal expandFuel world
            (expandState vertex distance edges rest
              (searchExpandedFrame vertex distance rest edges settled :: stack)) =
            .exhausted {
              control := .ret [.tuple [encodeQueue expanded.1, encodeGraph expanded.2]],
              context := expandContext,
              stack := searchExpandedFrame vertex distance rest edges settled :: stack } := by
          simpa [expanded, expandState, callState] using expandedRun
        have combinedPrefix := prefix_compose (prefix_compose toExpand actualExpanded)
          (search_expanded_resume vertex distance rest settled expanded.1 edges expanded.2 expandContext stack)
        exact returns_of_tail_prefix combinedPrefix
          (ih expanded.1 expanded.2 ((vertex, distance) :: settled) result stack recursive) rfl

end Erlean.Examples.Dijkstra
