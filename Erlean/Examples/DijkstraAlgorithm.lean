import Erlean.Examples.DijkstraModel

namespace Erlean.Examples.DijkstraAlgorithm

open DijkstraCertificate (Edge Graph Walk)

theorem seen_eq_true : seen vertex settled = true ↔
    ∃ entry ∈ settled, entry.1 = vertex := by
  simp [seen, List.any_eq_true]

theorem mem_insert : entry ∈ insert vertex distance queue ↔
    entry = (vertex, distance) ∨ entry ∈ queue := by
  induction queue with
  | nil => simp [insert]
  | cons head rest ih =>
    simp only [insert]
    split <;> simp_all [List.mem_cons, or_assoc, or_comm]

theorem length_insert : (insert vertex distance queue).length = queue.length + 1 := by
  induction queue with
  | nil => rfl
  | cons head rest ih =>
    simp only [insert]
    split <;> simp_all <;> omega

theorem ordered_insert (ordered : Ordered queue) : Ordered (insert vertex distance queue) := by
  induction queue with
  | nil => simp [insert, Ordered]
  | cons head rest ih =>
    obtain ⟨lower, tail⟩ := ordered
    by_cases first : distance ≤ head.2
    · simp only [insert, first, if_pos, Ordered]
      refine ⟨?_, lower, tail⟩
      intro entry member
      rcases List.mem_cons.mp member with rfl | member
      · exact first
      · exact Nat.le_trans first (lower entry member)
    · simp only [insert, first, if_false, Ordered]
      refine ⟨?_, ih tail⟩
      intro entry member
      rcases mem_insert.mp member with rfl | member
      · omega
      · exact lower entry member

theorem expand_ordered (ordered : Ordered queue) :
    Ordered (expand vertex distance remaining queue).1 := by
  induction remaining generalizing queue with
  | nil => exact ordered
  | cons edge rest ih =>
    simp only [expand]
    split
    · exact ih (ordered_insert ordered)
    · exact ih ordered

theorem expand_resource :
    (expand vertex distance remaining queue).1.length +
      (expand vertex distance remaining queue).2.length = queue.length + remaining.length := by
  induction remaining generalizing queue with
  | nil => simp [expand]
  | cons edge rest ih =>
    simp only [expand]
    split
    · have resource := ih (queue := insert edge.target (distance + edge.weight) queue)
      simp only [length_insert, List.length_cons] at resource ⊢
      omega
    · have resource := ih (queue := queue)
      simp only [List.length_cons]
      omega

theorem expand_remaining : edge ∈ (expand vertex distance remaining queue).2 ↔
    edge ∈ remaining ∧ edge.source ≠ vertex := by
  induction remaining generalizing queue with
  | nil => simp [expand]
  | cons head rest ih =>
    by_cases same : head.source = vertex
    · simp only [expand, same, if_pos, ih, List.mem_cons]
      constructor
      · intro ⟨member, different⟩
        exact ⟨Or.inr member, different⟩
      · intro ⟨member, different⟩
        rcases member with rfl | member
        · exact False.elim (different same)
        · exact ⟨member, different⟩
    · simp only [expand, same, if_false, List.mem_cons, ih]
      constructor
      · intro member
        rcases member with rfl | ⟨member, different⟩
        · exact ⟨Or.inl rfl, same⟩
        · exact ⟨Or.inr member, different⟩
      · intro ⟨member, different⟩
        rcases member with rfl | member
        · exact Or.inl rfl
        · exact Or.inr ⟨member, different⟩

theorem expand_queue : entry ∈ (expand vertex distance remaining queue).1 ↔
    entry ∈ queue ∨ ∃ edge ∈ remaining,
      edge.source = vertex ∧ entry = (edge.target, distance + edge.weight) := by
  induction remaining generalizing queue with
  | nil => simp [expand]
  | cons head rest ih =>
    by_cases same : head.source = vertex
    · simp only [expand, same, if_pos, ih]
      constructor
      · intro member
        rcases member with inserted | ⟨edge, member, source, equal⟩
        · rcases mem_insert.mp inserted with equal | old
          · exact Or.inr ⟨head, by simp, same, equal⟩
          · exact Or.inl old
        · exact Or.inr ⟨edge, List.mem_cons_of_mem _ member, source, equal⟩
      · intro member
        rcases member with old | ⟨edge, member, source, equal⟩
        · exact Or.inl (mem_insert.mpr (Or.inr old))
        · rcases List.mem_cons.mp member with rfl | member
          · exact Or.inl (mem_insert.mpr (Or.inl equal))
          · exact Or.inr ⟨edge, member, source, equal⟩
    · simp only [expand, same, if_false, ih]
      constructor
      · intro member
        rcases member with old | ⟨edge, member, source, equal⟩
        · exact Or.inl old
        · exact Or.inr ⟨edge, List.mem_cons_of_mem _ member, source, equal⟩
      · intro member
        rcases member with old | ⟨edge, member, source, equal⟩
        · exact Or.inl old
        · rcases List.mem_cons.mp member with rfl | member
          · exact False.elim (same source)
          · exact Or.inr ⟨edge, member, source, equal⟩

theorem walk_append_edge (walk : Walk graph source vertex distance)
    (member : edge ∈ graph) (endpoint : edge.source = vertex) :
    Walk graph source edge.target (distance + edge.weight) := by
  induction walk with
  | nil vertex =>
    have extended := Walk.cons edge member (Walk.nil edge.target)
    simpa [endpoint] using extended
  | cons first firstMember rest ih =>
    have extended := Walk.cons first firstMember (ih endpoint)
    simpa [Nat.add_assoc] using extended

/-- The frontier remembers a candidate across every edge leaving a settled
    vertex. Settled labels are no greater than any queued candidate. -/
structure Invariant (graph : Graph) (source : Nat)
    (queue : Distances) (remaining : Graph) (settled : Distances) : Prop where
  ordered : Ordered queue
  attained : ∀ entry ∈ settled ++ queue, Walk graph source entry.1 entry.2
  distinct : ∀ left ∈ settled, ∀ right ∈ settled, left.1 = right.1 → left = right
  lower : ∀ label ∈ settled, ∀ candidate ∈ queue, label.2 ≤ candidate.2
  frontier : ∀ label ∈ settled, ∀ edge ∈ graph, edge.source = label.1 →
    ∃ candidate ∈ settled ++ queue,
      candidate.1 = edge.target ∧ candidate.2 ≤ label.2 + edge.weight
  remaining : ∀ edge, edge ∈ remaining ↔
    edge ∈ graph ∧ ∀ label ∈ settled, label.1 ≠ edge.source
  origin : ∃ entry ∈ settled ++ queue, entry.1 = source ∧ entry.2 = 0

theorem initial_invariant (graph : Graph) (source : Nat) :
    Invariant graph source [(source, 0)] graph [] := by
  constructor
  · simp [Ordered]
  · intro entry member
    have equal : entry = (source, 0) := by simpa using member
    subst entry
    exact .nil source
  · simp
  · simp
  · simp
  · simp
  · exact ⟨(source, 0), by simp, rfl, rfl⟩

theorem stale_dominates
    (invariant : Invariant graph source (head :: rest) remaining settled)
    (stale : seen head.1 settled = true)
    (member : entry ∈ settled ++ (head :: rest)) :
    ∃ replacement ∈ settled ++ rest,
      replacement.1 = entry.1 ∧ replacement.2 ≤ entry.2 := by
  rcases List.mem_append.mp member with old | queued
  · exact ⟨entry, List.mem_append.mpr (Or.inl old), rfl, Nat.le_refl _⟩
  · rcases List.mem_cons.mp queued with rfl | tail
    · obtain ⟨known, knownMember, same⟩ := seen_eq_true.mp stale
      exact ⟨known, List.mem_append.mpr (Or.inl knownMember), same,
        invariant.lower known knownMember entry (by simp)⟩
    · exact ⟨entry, List.mem_append.mpr (Or.inr tail), rfl, Nat.le_refl _⟩

theorem invariant_stale
    (invariant : Invariant graph source (head :: rest) remaining settled)
    (stale : seen head.1 settled = true) :
    Invariant graph source rest remaining settled := by
  constructor
  · exact invariant.ordered.2
  · intro entry member
    apply invariant.attained
    rcases List.mem_append.mp member with old | tail
    · exact List.mem_append.mpr (Or.inl old)
    · exact List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ tail))
  · exact invariant.distinct
  · intro label member candidate queued
    exact invariant.lower label member candidate (List.mem_cons_of_mem _ queued)
  · intro label member edge edgeMember endpoint
    obtain ⟨candidate, queued, target, bound⟩ := invariant.frontier label member edge edgeMember endpoint
    obtain ⟨replacement, retained, same, lower⟩ := stale_dominates invariant stale queued
    exact ⟨replacement, retained, same.trans target, by omega⟩
  · exact invariant.remaining
  · obtain ⟨entry, member, vertex, distance⟩ := invariant.origin
    obtain ⟨replacement, retained, same, lower⟩ := stale_dominates invariant stale member
    exact ⟨replacement, retained, same.trans vertex, by omega⟩

theorem settle_retains (member : entry ∈ settled ++ (head :: rest)) :
    entry ∈ (head :: settled) ++ (expand head.1 head.2 remaining rest).1 := by
  rcases List.mem_append.mp member with old | queued
  · exact List.mem_append.mpr (Or.inl (List.mem_cons_of_mem _ old))
  · rcases List.mem_cons.mp queued with rfl | tail
    · exact List.mem_append.mpr (Or.inl (by simp))
    · exact List.mem_append.mpr (Or.inr (expand_queue.mpr (Or.inl tail)))

theorem invariant_settle
    (invariant : Invariant graph source (head :: rest) remaining settled)
    (fresh : seen head.1 settled = false) :
    Invariant graph source (expand head.1 head.2 remaining rest).1
      (expand head.1 head.2 remaining rest).2 (head :: settled) := by
  have different : ∀ label ∈ settled, label.1 ≠ head.1 := by
    intro label member equal
    have yes := seen_eq_true.mpr ⟨label, member, equal⟩
    simp [fresh] at yes
  have headWalk := invariant.attained head (List.mem_append.mpr (Or.inr (by simp)))
  have queueLower : ∀ candidate ∈ (expand head.1 head.2 remaining rest).1,
      head.2 ≤ candidate.2 := by
    intro candidate queued
    rcases expand_queue.mp queued with old | ⟨edge, member, endpoint, rfl⟩
    · exact invariant.ordered.1 candidate old
    · omega
  constructor
  · exact expand_ordered invariant.ordered.2
  · intro entry member
    rcases List.mem_append.mp member with old | queued
    · rcases List.mem_cons.mp old with rfl | old
      · exact headWalk
      · exact invariant.attained entry (List.mem_append.mpr (Or.inl old))
    · rcases expand_queue.mp queued with old | ⟨edge, edgeMember, endpoint, rfl⟩
      · exact invariant.attained entry
          (List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ old)))
      · exact walk_append_edge headWalk ((invariant.remaining edge).mp edgeMember).1 endpoint
  · intro left leftMember right rightMember equal
    rcases List.mem_cons.mp leftMember with leftHead | leftTail
    · rcases List.mem_cons.mp rightMember with rightHead | rightTail
      · exact leftHead.trans rightHead.symm
      · exact False.elim (different right rightTail
          (equal.symm.trans (congrArg Prod.fst leftHead)))
    · rcases List.mem_cons.mp rightMember with rightHead | rightTail
      · exact False.elim (different left leftTail
          (equal.trans (congrArg Prod.fst rightHead)))
      · exact invariant.distinct left leftTail right rightTail equal
  · intro label member candidate queued
    rcases List.mem_cons.mp member with rfl | member
    · exact queueLower candidate queued
    · exact Nat.le_trans (invariant.lower label member head (by simp)) (queueLower candidate queued)
  · intro label member edge edgeMember endpoint
    rcases List.mem_cons.mp member with sameHead | member
    · subst label
      have unprocessed : edge ∈ remaining := (invariant.remaining edge).mpr
        ⟨edgeMember, by intro label member same; exact different label member (same.trans endpoint)⟩
      refine ⟨(edge.target, head.2 + edge.weight), ?_, rfl, Nat.le_refl _⟩
      exact List.mem_append.mpr (Or.inr
        (expand_queue.mpr (Or.inr ⟨edge, unprocessed, endpoint, rfl⟩)))
    · obtain ⟨candidate, queued, target, bound⟩ := invariant.frontier label member edge edgeMember endpoint
      exact ⟨candidate, settle_retains queued, target, bound⟩
  · intro edge
    rw [expand_remaining, invariant.remaining edge]
    constructor
    · intro ⟨⟨member, absent⟩, other⟩
      refine ⟨member, ?_⟩
      intro label labelMember
      rcases List.mem_cons.mp labelMember with rfl | labelMember
      · exact Ne.symm other
      · exact absent label labelMember
    · intro ⟨member, absent⟩
      exact ⟨⟨member, fun label labelMember => absent label (List.mem_cons_of_mem _ labelMember)⟩,
        Ne.symm (absent head (by simp))⟩
  · obtain ⟨entry, member, vertex, distance⟩ := invariant.origin
    exact ⟨entry, settle_retains member, vertex, distance⟩

/-- Once the queue is empty, the frontier inequalities extend to every walk. -/
theorem terminal_walk_bound
    (invariant : Invariant graph source [] remaining settled)
    (walk : Walk graph start target cost)
    (member : label ∈ settled) (endpoint : label.1 = start) :
    ∃ finish ∈ settled, finish.1 = target ∧ finish.2 ≤ label.2 + cost := by
  induction walk generalizing label with
  | nil vertex => exact ⟨label, member, endpoint, by omega⟩
  | cons edge edgeMember rest ih =>
    obtain ⟨middle, live, target, bound⟩ :=
      invariant.frontier label member edge edgeMember endpoint.symm
    have middleMember : middle ∈ settled := by simpa using live
    obtain ⟨finish, finishMember, finishTarget, finishBound⟩ := ih middleMember target
    exact ⟨finish, finishMember, finishTarget, by omega⟩

def MembersCorrect (graph : Graph) (source : Nat) (result : Distances) : Prop :=
  (∀ entry ∈ result, Walk graph source entry.1 entry.2 ∧
    ∀ cost, Walk graph source entry.1 cost → entry.2 ≤ cost) ∧
  (∀ vertex cost, Walk graph source vertex cost → ∃ entry ∈ result, entry.1 = vertex)

theorem invariant_terminal
    (invariant : Invariant graph source [] remaining settled) :
    MembersCorrect graph source settled := by
  obtain ⟨origin, live, originVertex, originDistance⟩ := invariant.origin
  have originMember : origin ∈ settled := by simpa using live
  constructor
  · intro entry member
    refine ⟨invariant.attained entry (by simpa using member), ?_⟩
    intro cost walk
    obtain ⟨finish, finishMember, target, bound⟩ :=
      terminal_walk_bound invariant walk originMember originVertex
    have equal := invariant.distinct finish finishMember entry member target
    simpa [equal, originDistance] using bound
  · intro vertex cost walk
    obtain ⟨finish, member, target, _⟩ :=
      terminal_walk_bound invariant walk originMember originVertex
    exact ⟨finish, member, target⟩

/-- Every recursive step consumes one unit of queue-plus-unprocessed-edge
    resource, regardless of repeated candidates, cycles, or parallel edges. -/
theorem search_total
    (invariant : Invariant graph source queue remaining settled)
    (resource : queue.length + remaining.length ≤ fuel) :
    ∃ result, search fuel queue remaining settled = some result ∧
      MembersCorrect graph source result := by
  induction fuel generalizing queue remaining settled with
  | zero =>
    cases queue with
    | nil => exact ⟨settled, rfl, invariant_terminal invariant⟩
    | cons head rest => simp at resource
  | succ fuel ih =>
    cases queue with
    | nil => exact ⟨settled, rfl, invariant_terminal invariant⟩
    | cons head rest =>
      cases stale : seen head.1 settled with
      | true =>
        have smaller : rest.length + remaining.length ≤ fuel := by
          simp only [List.length_cons] at resource
          omega
        obtain ⟨result, ran, correct⟩ := ih (invariant_stale invariant stale) smaller
        exact ⟨result, by simpa [search, stale] using ran, correct⟩
      | false =>
        have conserved := expand_resource (vertex := head.1) (distance := head.2)
          (remaining := remaining) (queue := rest)
        have smaller : (expand head.1 head.2 remaining rest).1.length +
            (expand head.1 head.2 remaining rest).2.length ≤ fuel := by
          simp only [List.length_cons] at resource
          omega
        obtain ⟨result, ran, correct⟩ := ih (invariant_settle invariant stale) smaller
        exact ⟨result, by simpa [search, stale] using ran, correct⟩

theorem lookup_some_member (result : Distances)
    (found : lookup result vertex = some distance) : (vertex, distance) ∈ result := by
  induction result with
  | nil => simp [lookup] at found
  | cons entry rest ih =>
    by_cases same : entry.1 = vertex
    · have equal : entry.2 = distance := by simpa [lookup, same] using found
      have pair : entry = (vertex, distance) := Prod.ext same equal
      simp [pair]
    · have tail : lookup rest vertex = some distance := by simpa [lookup, same] using found
      exact List.mem_cons_of_mem _ (ih tail)

theorem lookup_exists_of_member (result : Distances)
    (member : entry ∈ result) : ∃ distance, lookup result entry.1 = some distance := by
  induction result with
  | nil => simp at member
  | cons head rest ih =>
    by_cases same : head.1 = entry.1
    · exact ⟨head.2, by simp [lookup, same]⟩
    · have tail : entry ∈ rest := by
        rcases List.mem_cons.mp member with rfl | member
        · exact False.elim (same rfl)
        · exact member
      obtain ⟨distance, found⟩ := ih tail
      exact ⟨distance, by simpa [lookup, same] using found⟩

theorem membersCorrect_resultCorrect (correct : MembersCorrect graph source result) :
    ResultCorrect graph source result := by
  constructor
  · intro vertex distance found
    exact correct.1 (vertex, distance) (lookup_some_member result found)
  · intro vertex absent cost walk
    obtain ⟨entry, member, target⟩ := correct.2 vertex cost walk
    obtain ⟨distance, found⟩ := lookup_exists_of_member result member
    simp [target, absent] at found

theorem membersCorrect_reverse (correct : MembersCorrect graph source result) :
    MembersCorrect graph source result.reverse := by
  constructor
  · intro entry member
    exact correct.1 entry (by simpa using member)
  · intro vertex cost walk
    obtain ⟨entry, member, endpoint⟩ := correct.2 vertex cost walk
    exact ⟨entry, by simpa using member, endpoint⟩

/-- Universal total correctness of this mathematical Dijkstra algorithm. Every
    finite directed Nat-weight graph terminates within |E|+1 queue removals and
    returns exactly its reachable vertices with attained shortest distances. -/
theorem distances_total (source : Nat) (graph : Graph) :
    ∃ result, distances source graph = some result ∧ ResultCorrect graph source result := by
  obtain ⟨result, ran, correct⟩ := search_total (initial_invariant graph source)
    (fuel := graph.length + 1) (by simp; omega)
  refine ⟨result.reverse, ?_, membersCorrect_resultCorrect (membersCorrect_reverse correct)⟩
  simp [distances, ran]

theorem distances_correct (source : Nat) (graph : Graph)
    (ran : distances source graph = some result) : ResultCorrect graph source result := by
  obtain ⟨actual, computed, correct⟩ := distances_total source graph
  have equal : actual = result := Option.some.inj (computed.symm.trans ran)
  simpa [equal] using correct

theorem distances_ne_none (source : Nat) (graph : Graph) : distances source graph ≠ none := by
  obtain ⟨result, computed, _⟩ := distances_total source graph
  simp [computed]

end Erlean.Examples.DijkstraAlgorithm
