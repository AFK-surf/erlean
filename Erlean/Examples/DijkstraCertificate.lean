import Std

/-!
Executable certificates for shortest distances in finite directed graphs with
nonnegative natural-number weights. Soundness ranges over all finite walks,
including walks with repeated vertices and zero-weight cycles. This verifies a
supplied result, not the termination or correctness of a shortest-path algorithm.
-/

namespace Erlean.Examples.DijkstraCertificate

structure Edge where
  source : Nat
  target : Nat
  weight : Nat
  deriving DecidableEq, Repr

abbrev Graph := List Edge

structure Label where
  vertex : Nat
  distance : Nat
  path : List Edge
  deriving DecidableEq, Repr

abbrev Labels := List Label

def lookup : Labels → Nat → Option Nat
  | [], _ => none
  | label :: rest, vertex =>
    if label.vertex = vertex then some label.distance else lookup rest vertex

/-- Walks are unrestricted finite graph walks, not just certificate paths. -/
inductive Walk (graph : Graph) : Nat → Nat → Nat → Prop where
  | nil (vertex : Nat) : Walk graph vertex vertex 0
  | cons (edge : Edge) (member : edge ∈ graph)
      (rest : Walk graph edge.target target cost) :
      Walk graph edge.source target (edge.weight + cost)

/-- Check a supplied edge sequence against its endpoints and claimed cost. -/
def checkPath (graph : Graph) (source target cost : Nat) : List Edge → Bool
  | [] => decide (source = target ∧ cost = 0)
  | edge :: rest =>
    decide (edge ∈ graph ∧ edge.source = source ∧ edge.weight ≤ cost) &&
      checkPath graph edge.target target (cost - edge.weight) rest

theorem checkPath_sound (path : List Edge)
    (checked : checkPath graph source target cost path = true) :
    Walk graph source target cost := by
  induction path generalizing source cost with
  | nil =>
    have facts : source = target ∧ cost = 0 := by simpa [checkPath] using checked
    rcases facts with ⟨rfl, rfl⟩
    exact .nil _
  | cons edge rest ih =>
    have facts : (edge ∈ graph ∧ edge.source = source ∧ edge.weight ≤ cost) ∧
        checkPath graph edge.target target (cost - edge.weight) rest = true := by
      simpa only [checkPath, Bool.and_eq_true, decide_eq_true_eq] using checked
    have remainder := ih facts.2
    have total : edge.weight + (cost - edge.weight) = cost := by omega
    have walk := Walk.cons edge facts.1.1 remainder
    simpa only [facts.1.2.1, total] using walk

def checkLabel (graph : Graph) (source : Nat) (labels : Labels) (label : Label) : Bool :=
  decide (lookup labels label.vertex = some label.distance) &&
    checkPath graph source label.vertex label.distance label.path

/-- An edge out of a labeled vertex must lead to a labeled vertex, whose
    potential is at most the source potential plus the edge weight. -/
def checkEdge (labels : Labels) (edge : Edge) : Bool :=
  match lookup labels edge.source with
  | none => true
  | some distance =>
    match lookup labels edge.target with
    | none => false
    | some targetDistance => decide (targetDistance ≤ distance + edge.weight)

def checkCertificate (graph : Graph) (source : Nat) (labels : Labels) : Bool :=
  decide (lookup labels source = some 0) &&
    labels.all (checkLabel graph source labels) && graph.all (checkEdge labels)

theorem lookup_some_label (labels : Labels)
    (found : lookup labels vertex = some distance) :
    ∃ label ∈ labels, label.vertex = vertex ∧ label.distance = distance := by
  induction labels with
  | nil => simp [lookup] at found
  | cons label rest ih =>
    by_cases equal : label.vertex = vertex
    · have same : label.distance = distance := by simpa [lookup, equal] using found
      exact ⟨label, by simp, equal, same⟩
    · have tail : lookup rest vertex = some distance := by simpa [lookup, equal] using found
      obtain ⟨witness, member, endpoint, cost⟩ := ih tail
      exact ⟨witness, List.mem_cons_of_mem _ member, endpoint, cost⟩

theorem checkEdge_sound (checked : checkEdge labels edge = true)
    (found : lookup labels edge.source = some distance) :
    ∃ targetDistance, lookup labels edge.target = some targetDistance ∧
      targetDistance ≤ distance + edge.weight := by
  cases targetFound : lookup labels edge.target with
  | none => simp [checkEdge, found, targetFound] at checked
  | some targetDistance =>
    refine ⟨targetDistance, rfl, ?_⟩
    simpa [checkEdge, found, targetFound] using checked

/-- Triangle inequalities propagate along every walk, without enumerating it
    in the certificate or imposing a bound on its length. -/
theorem walk_potential_bound
    (edges : ∀ edge ∈ graph, checkEdge labels edge = true)
    (walk : Walk graph start target cost)
    (found : lookup labels start = some distance) :
    ∃ targetDistance, lookup labels target = some targetDistance ∧
      targetDistance ≤ distance + cost := by
  induction walk generalizing distance with
  | nil vertex =>
    exact ⟨distance, found, by omega⟩
  | cons edge member rest ih =>
    obtain ⟨middle, middleFound, edgeBound⟩ := checkEdge_sound (edges edge member) found
    obtain ⟨finish, finishFound, restBound⟩ := ih middleFound
    exact ⟨finish, finishFound, by omega⟩

/-- Every listed distance is attained and minimal among all walks; vertices
    omitted from the labels are unreachable from the source. -/
def ShortestDistances (graph : Graph) (source : Nat) (labels : Labels) : Prop :=
  (∀ vertex distance, lookup labels vertex = some distance →
    Walk graph source vertex distance ∧
      ∀ cost, Walk graph source vertex cost → distance ≤ cost) ∧
  (∀ vertex, lookup labels vertex = none →
    ∀ cost, ¬ Walk graph source vertex cost)

theorem checkCertificate_sound
    (checked : checkCertificate graph source labels = true) :
    ShortestDistances graph source labels := by
  have facts : (lookup labels source = some 0 ∧
      labels.all (checkLabel graph source labels) = true) ∧
      graph.all (checkEdge labels) = true := by
    simpa only [checkCertificate, Bool.and_eq_true, decide_eq_true_eq] using checked
  have labelChecks : ∀ label ∈ labels, checkLabel graph source labels label = true :=
    List.all_eq_true.mp facts.1.2
  have edgeChecks : ∀ edge ∈ graph, checkEdge labels edge = true :=
    List.all_eq_true.mp facts.2
  constructor
  · intro vertex distance found
    obtain ⟨label, member, endpoint, labelDistance⟩ := lookup_some_label labels found
    have checkedLabel := labelChecks label member
    have checkedPath : checkPath graph source label.vertex label.distance label.path = true :=
      ((Bool.and_eq_true _ _).mp checkedLabel).2
    constructor
    · simpa only [endpoint, labelDistance] using checkPath_sound label.path checkedPath
    · intro cost walk
      obtain ⟨potential, reached, bound⟩ := walk_potential_bound edgeChecks walk facts.1.1
      have equal : potential = distance := Option.some.inj (reached.symm.trans found)
      omega
  · intro vertex absent cost walk
    obtain ⟨distance, reached, _⟩ := walk_potential_bound edgeChecks walk facts.1.1
    simp [absent] at reached

end Erlean.Examples.DijkstraCertificate
