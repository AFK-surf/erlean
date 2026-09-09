import Erlean.Core.MapKey
import Init.Data.List.Pairwise

namespace Erlean.Core.FiniteMap

abbrev Entries (α : Type u) := List (MapKey × α)

/-- A canonical map contains strictly ordered, therefore distinct, keys. -/
def Sorted (entries : Entries α) : Prop :=
  entries.Pairwise (fun left right => MapKey.before left.1 right.1 = true)

instance (entries : Entries α) : Decidable (Sorted entries) :=
  inferInstanceAs (Decidable (entries.Pairwise
    (fun left right => MapKey.before left.1 right.1 = true)))

def lookup (key : MapKey) : Entries α → Option α
  | [] => none
  | (other, value) :: rest => if key = other then some value else lookup key rest

/-- Ordered insertion overwrites the value at an existing key. -/
def insert (key : MapKey) (value : α) : Entries α → Entries α
  | [] => [(key, value)]
  | (other, previous) :: rest =>
    if key = other then (key, value) :: rest
    else if MapKey.before key other then (key, value) :: (other, previous) :: rest
    else (other, previous) :: insert key value rest

/-- Erasure removes every occurrence, even for a noncanonical input list. -/
def erase (key : MapKey) : Entries α → Entries α
  | [] => []
  | (other, value) :: rest =>
    if key = other then erase key rest else (other, value) :: erase key rest

private theorem before_ne (left right : MapKey)
    (less : MapKey.before left right = true) : left ≠ right := by
  intro equal
  subst right
  simp [MapKey.before_irrefl] at less

private theorem reverse_before (left right : MapKey) (different : left ≠ right)
    (notLess : MapKey.before left right ≠ true) : MapKey.before right left = true := by
  rcases MapKey.before_trichotomy left right with less | equal | greater
  · exact False.elim (notLess less)
  · exact False.elim (different equal)
  · exact greater

@[simp] theorem lookup_nil (key : MapKey) : lookup key ([] : Entries α) = none := rfl

@[simp] theorem lookup_cons_same (key : MapKey) (value : α) (entries : Entries α) :
    lookup key ((key, value) :: entries) = some value := by
  simp [lookup]

theorem lookup_cons_other (key other : MapKey) (value : α) (entries : Entries α)
    (different : key ≠ other) :
    lookup key ((other, value) :: entries) = lookup key entries := by
  simp [lookup, different]

@[simp] theorem lookup_insert_same (key : MapKey) (value : α) (entries : Entries α) :
    lookup key (insert key value entries) = some value := by
  induction entries with
  | nil => simp [insert]
  | cons entry rest ih =>
    rcases entry with ⟨other, previous⟩
    by_cases equal : key = other
    · simp [insert, equal]
    · by_cases less : MapKey.before key other = true <;>
        simp [insert, equal, less, lookup, ih]

theorem lookup_insert_other (key other : MapKey) (value : α) (entries : Entries α)
    (different : other ≠ key) :
    lookup other (insert key value entries) = lookup other entries := by
  induction entries with
  | nil => simp [insert, lookup, different]
  | cons entry rest ih =>
    rcases entry with ⟨head, previous⟩
    by_cases equal : key = head
    · subst head
      simp [insert, lookup, different]
    · by_cases less : MapKey.before key head = true <;>
        simp [insert, equal, less, lookup, different, ih]

/-- Insertion changes exactly one observable key. -/
theorem lookup_insert (key other : MapKey) (value : α) (entries : Entries α) :
    lookup other (insert key value entries) =
      if other = key then some value else lookup other entries := by
  by_cases equal : other = key
  · subst other
    simp
  · simp [equal, lookup_insert_other key other value entries equal]

@[simp] theorem lookup_erase_same (key : MapKey) (entries : Entries α) :
    lookup key (erase key entries) = none := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    rcases entry with ⟨other, value⟩
    by_cases equal : key = other
    · subst other
      simpa [erase] using ih
    · simp [erase, equal, lookup, ih]

theorem lookup_erase_other (key other : MapKey) (entries : Entries α)
    (different : other ≠ key) :
    lookup other (erase key entries) = lookup other entries := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    rcases entry with ⟨head, value⟩
    by_cases equal : key = head
    · subst head
      simp [erase, lookup, different, ih]
    · simp [erase, equal, lookup, ih]

/-- Erasure preserves every other lookup, with no sortedness premise. -/
theorem lookup_erase (key other : MapKey) (entries : Entries α) :
    lookup other (erase key entries) =
      if other = key then none else lookup other entries := by
  by_cases equal : other = key
  · subst other
    simp
  · simp [equal, lookup_erase_other key other entries equal]

theorem mem_of_lookup (key : MapKey) (value : α) (entries : Entries α)
    (found : lookup key entries = some value) : (key, value) ∈ entries := by
  induction entries with
  | nil => simp [lookup] at found
  | cons entry rest ih =>
    rcases entry with ⟨other, previous⟩
    by_cases equal : key = other
    · subst other
      have values : previous = value := by simpa [lookup] using found
      subst previous
      simp
    · have tail : lookup key rest = some value := by simpa [lookup, equal] using found
      exact List.mem_cons_of_mem _ (ih tail)

theorem lookup_none_of_forall_ne (key : MapKey) (entries : Entries α)
    (absent : ∀ entry ∈ entries, key ≠ entry.1) : lookup key entries = none := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    rcases entry with ⟨other, value⟩
    have head := absent (other, value) (by simp)
    have tail : ∀ entry ∈ rest, key ≠ entry.1 := by
      intro entry member
      exact absent entry (List.mem_cons_of_mem _ member)
    simp [lookup, head, ih tail]

/-- Every output entry is either the inserted pair or an unchanged input pair. -/
theorem mem_insert (key : MapKey) (value : α) (entries : Entries α)
    (entry : MapKey × α) (member : entry ∈ insert key value entries) :
    entry = (key, value) ∨ entry ∈ entries := by
  induction entries with
  | nil => simpa [insert] using member
  | cons head rest ih =>
    rcases head with ⟨other, previous⟩
    by_cases equal : key = other
    · simp only [insert, if_pos equal, List.mem_cons] at member
      rcases member with same | tail
      · exact Or.inl same
      · exact Or.inr (List.mem_cons_of_mem _ tail)
    · by_cases less : MapKey.before key other = true
      · have alternatives : entry = (key, value) ∨ entry ∈ (other, previous) :: rest := by
          simpa [insert, equal, less] using member
        rcases alternatives with same | tail
        · exact Or.inl same
        · exact Or.inr tail
      · have reduced : entry = (other, previous) ∨ entry ∈ insert key value rest := by
          simpa [insert, equal, less] using member
        rcases reduced with same | tail
        · exact Or.inr (by simp [same])
        · rcases ih tail with fresh | old
          · exact Or.inl fresh
          · exact Or.inr (List.mem_cons_of_mem _ old)

/-- Erasure cannot introduce an entry. -/
theorem mem_erase (key : MapKey) (entries : Entries α)
    (entry : MapKey × α) (member : entry ∈ erase key entries) : entry ∈ entries := by
  induction entries with
  | nil => simp [erase] at member
  | cons head rest ih =>
    rcases head with ⟨other, value⟩
    by_cases equal : key = other
    · have tail : entry ∈ erase key rest := by simpa [erase, equal] using member
      exact List.mem_cons_of_mem _ (ih tail)
    · have alternatives : entry = (other, value) ∨ entry ∈ erase key rest := by
        simpa [erase, equal] using member
      rcases alternatives with same | tail
      · simp [same]
      · exact List.mem_cons_of_mem _ (ih tail)

@[simp] theorem sorted_nil : Sorted ([] : Entries α) := List.Pairwise.nil

theorem sorted_insert (key : MapKey) (value : α) (entries : Entries α)
    (sorted : Sorted entries) : Sorted (insert key value entries) := by
  induction entries with
  | nil => simp [Sorted, insert]
  | cons head rest ih =>
    rcases head with ⟨other, previous⟩
    obtain ⟨headLess, tailSorted⟩ := List.pairwise_cons.mp sorted
    by_cases equal : key = other
    · subst other
      simp only [insert]
      exact List.pairwise_cons.mpr ⟨headLess, tailSorted⟩
    · by_cases less : MapKey.before key other = true
      · have allLess : ∀ entry ∈ (other, previous) :: rest,
            MapKey.before key entry.1 = true := by
          intro entry member
          rcases List.mem_cons.mp member with same | tail
          · simpa [same] using less
          · exact MapKey.before_trans key other entry.1 less (headLess entry tail)
        simp only [insert, if_neg equal, if_pos less]
        apply List.pairwise_cons.mpr
        exact ⟨allLess, sorted⟩
      · have greater := reverse_before key other equal less
        have allLess : ∀ entry ∈ insert key value rest,
            MapKey.before other entry.1 = true := by
          intro entry member
          rcases mem_insert key value rest entry member with same | old
          · simpa [same] using greater
          · exact headLess entry old
        simp only [insert, if_neg equal, if_neg less]
        apply List.pairwise_cons.mpr
        exact ⟨allLess, ih tailSorted⟩

theorem sorted_erase (key : MapKey) (entries : Entries α)
    (sorted : Sorted entries) : Sorted (erase key entries) := by
  induction entries with
  | nil => exact sorted_nil
  | cons head rest ih =>
    rcases head with ⟨other, value⟩
    obtain ⟨headLess, tailSorted⟩ := List.pairwise_cons.mp sorted
    by_cases equal : key = other
    · simpa [erase, equal] using ih tailSorted
    · have allLess : ∀ entry ∈ erase key rest, MapKey.before other entry.1 = true := by
        intro entry member
        exact headLess entry (mem_erase key rest entry member)
      simp only [erase, if_neg equal]
      apply List.pairwise_cons.mpr
      exact ⟨allLess, ih tailSorted⟩

private theorem lookup_head_absent (key : MapKey) (value : α) (entries : Entries α)
    (sorted : Sorted ((key, value) :: entries)) : lookup key entries = none := by
  apply lookup_none_of_forall_ne
  intro entry member
  exact before_ne key entry.1 ((List.pairwise_cons.mp sorted).1 entry member)

/-- Canonical representations with equal lookups are equal as entry lists.
    Values need no equality decision procedure or ordering. -/
theorem ext_sorted (left right : Entries α) (leftSorted : Sorted left)
    (rightSorted : Sorted right) (same : ∀ key, lookup key left = lookup key right) :
    left = right := by
  induction left generalizing right with
  | nil =>
    cases right with
    | nil => rfl
    | cons head tail =>
      rcases head with ⟨key, value⟩
      have impossible := same key
      simp [lookup] at impossible
  | cons head tail ih =>
    rcases head with ⟨key, value⟩
    cases right with
    | nil =>
      have impossible := same key
      simp [lookup] at impossible
    | cons other rest =>
      rcases other with ⟨otherKey, otherValue⟩
      have keys : key = otherKey := by
        by_cases different : key = otherKey
        · exact different
        apply False.elim
        have leftFound : lookup otherKey ((key, value) :: tail) = some otherValue := by
          simpa [lookup] using same otherKey
        have rightFound : lookup key ((otherKey, otherValue) :: rest) = some value := by
          simpa [lookup] using (same key).symm
        have leftMember := mem_of_lookup otherKey otherValue _ leftFound
        have rightMember := mem_of_lookup key value _ rightFound
        have leftTail : (otherKey, otherValue) ∈ tail := by
          simpa [different, Ne.symm different] using leftMember
        have rightTail : (key, value) ∈ rest := by
          simpa [different, Ne.symm different] using rightMember
        have less := (List.pairwise_cons.mp leftSorted).1 _ leftTail
        have greater := (List.pairwise_cons.mp rightSorted).1 _ rightTail
        have impossible := MapKey.before_asymm key otherKey less
        simp [greater] at impossible
      subst otherKey
      have values : value = otherValue := by simpa [lookup] using same key
      subst otherValue
      have tails : ∀ query, lookup query tail = lookup query rest := by
        intro query
        by_cases equal : query = key
        · subst query
          rw [lookup_head_absent key value tail leftSorted,
            lookup_head_absent key value rest rightSorted]
        · simpa [lookup, equal] using same query
      have equal := ih rest (List.pairwise_cons.mp leftSorted).2
        (List.pairwise_cons.mp rightSorted).2 tails
      simp [equal]

theorem insert_overwrite (key : MapKey) (first second : α) (entries : Entries α)
    (sorted : Sorted entries) :
    insert key second (insert key first entries) = insert key second entries := by
  apply ext_sorted _ _ (sorted_insert _ _ _ (sorted_insert _ _ _ sorted))
    (sorted_insert _ _ _ sorted)
  intro query
  by_cases equal : query = key <;> simp [lookup_insert, equal]

theorem erase_idempotent (key : MapKey) (entries : Entries α) (sorted : Sorted entries) :
    erase key (erase key entries) = erase key entries := by
  apply ext_sorted _ _ (sorted_erase _ _ (sorted_erase _ _ sorted)) (sorted_erase _ _ sorted)
  intro query
  by_cases equal : query = key <;> simp [lookup_erase, equal]

end Erlean.Core.FiniteMap
