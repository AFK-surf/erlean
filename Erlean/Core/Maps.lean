import Erlean.Core.Equality

namespace Erlean.Core

mutual
/-- Supported keys survive the bridge without changing their exact identity. -/
theorem MapKey.toValue_toMapKey (key : MapKey) : key.toValue.toMapKey = some key := by
  match key with
  | .integer _ | .atom _ | .nil | .bitstring _ | .pid _ | .reference _ =>
    simp [MapKey.toValue, Value.toMapKey]
  | .cons head tail =>
    simp [MapKey.toValue, Value.toMapKey, MapKey.toValue_toMapKey head, MapKey.toValue_toMapKey tail]
  | .tuple keys =>
    simp [MapKey.toValue, Value.toMapKey, MapKey.toValues_toMapKeys keys]
termination_by sizeOf key

theorem MapKey.toValues_toMapKeys (keys : List MapKey) :
    Value.toMapKeys (MapKey.toValues keys) = some keys := by
  match keys with
  | [] => simp [MapKey.toValues, Value.toMapKeys]
  | key :: rest =>
    simp [MapKey.toValues, Value.toMapKeys, MapKey.toValue_toMapKey key,
      MapKey.toValues_toMapKeys rest]
termination_by sizeOf keys
end

mutual
theorem MapKey.toValue_comparable (key : MapKey) : key.toValue.exactComparable = true := by
  match key with
  | .integer _ | .atom _ | .nil | .bitstring _ | .pid _ | .reference _ =>
    simp [MapKey.toValue, Value.exactComparable]
  | .cons head tail =>
    simp [MapKey.toValue, Value.exactComparable, MapKey.toValue_comparable head,
      MapKey.toValue_comparable tail]
  | .tuple keys =>
    simp [MapKey.toValue, Value.exactComparable, MapKey.toValues_comparable keys]
termination_by sizeOf key

theorem MapKey.toValues_comparable (keys : List MapKey) :
    Value.comparableList (MapKey.toValues keys) = true := by
  match keys with
  | [] => simp [MapKey.toValues, Value.comparableList]
  | key :: rest =>
    simp [MapKey.toValues, Value.comparableList, MapKey.toValue_comparable key,
      MapKey.toValues_comparable rest]
termination_by sizeOf keys
end

theorem MapKey.toValue_public (key : MapKey) : key.toValue.isPublic = true :=
  Value.public_of_exactComparable key.toValue (MapKey.toValue_comparable key)

theorem MapKey.toValue_injective (left right : MapKey)
    (equal : left.toValue = right.toValue) : left = right := by
  have keys := congrArg Value.toMapKey equal
  simpa [MapKey.toValue_toMapKey] using keys

theorem Value.publicEntries_iff (entries : List (MapKey × Value)) :
    Value.publicEntries entries = true ↔ ∀ entry ∈ entries, entry.2.isPublic = true := by
  induction entries with
  | nil => simp [Value.publicEntries]
  | cons entry rest ih =>
    rcases entry with ⟨key, value⟩
    simp [Value.publicEntries, ih]

theorem Value.comparableEntries_iff (entries : List (MapKey × Value)) :
    Value.comparableEntries entries = true ↔
      ∀ entry ∈ entries, entry.2.exactComparable = true := by
  induction entries with
  | nil => simp [Value.comparableEntries]
  | cons entry rest ih =>
    rcases entry with ⟨key, value⟩
    simp [Value.comparableEntries, ih]

theorem Value.map_public_iff (entries : List (MapKey × Value)) :
    (Value.map entries).isPublic = true ↔
      FiniteMap.Sorted entries ∧ ∀ entry ∈ entries, entry.2.isPublic = true := by
  simp [Value.isPublic, Value.mapOrdered, Value.publicEntries_iff]

theorem Value.map_comparable_iff (entries : List (MapKey × Value)) :
    (Value.map entries).exactComparable = true ↔
      FiniteMap.Sorted entries ∧ ∀ entry ∈ entries, entry.2.exactComparable = true := by
  simp [Value.exactComparable, Value.mapOrdered, Value.comparableEntries_iff]

theorem Value.map_insert_public (key : MapKey) (value : Value)
    (entries : List (MapKey × Value))
    (publicMap : (Value.map entries).isPublic = true)
    (publicValue : value.isPublic = true) :
    (Value.map (FiniteMap.insert key value entries)).isPublic = true := by
  obtain ⟨sorted, publicEntries⟩ := (Value.map_public_iff entries).mp publicMap
  apply (Value.map_public_iff _).mpr
  refine ⟨FiniteMap.sorted_insert key value entries sorted, ?_⟩
  intro entry member
  rcases FiniteMap.mem_insert key value entries entry member with fresh | old
  · subst entry
    exact publicValue
  · exact publicEntries entry old

theorem Value.map_insert_comparable (key : MapKey) (value : Value)
    (entries : List (MapKey × Value))
    (comparableMap : (Value.map entries).exactComparable = true)
    (comparableValue : value.exactComparable = true) :
    (Value.map (FiniteMap.insert key value entries)).exactComparable = true := by
  obtain ⟨sorted, comparableEntries⟩ := (Value.map_comparable_iff entries).mp comparableMap
  apply (Value.map_comparable_iff _).mpr
  refine ⟨FiniteMap.sorted_insert key value entries sorted, ?_⟩
  intro entry member
  rcases FiniteMap.mem_insert key value entries entry member with fresh | old
  · subst entry
    exact comparableValue
  · exact comparableEntries entry old

theorem Value.map_erase_public (key : MapKey) (entries : List (MapKey × Value))
    (publicMap : (Value.map entries).isPublic = true) :
    (Value.map (FiniteMap.erase key entries)).isPublic = true := by
  obtain ⟨sorted, publicEntries⟩ := (Value.map_public_iff entries).mp publicMap
  apply (Value.map_public_iff _).mpr
  refine ⟨FiniteMap.sorted_erase key entries sorted, ?_⟩
  intro entry member
  exact publicEntries entry (FiniteMap.mem_erase key entries entry member)

theorem Value.map_erase_comparable (key : MapKey) (entries : List (MapKey × Value))
    (comparableMap : (Value.map entries).exactComparable = true) :
    (Value.map (FiniteMap.erase key entries)).exactComparable = true := by
  obtain ⟨sorted, comparableEntries⟩ := (Value.map_comparable_iff entries).mp comparableMap
  apply (Value.map_comparable_iff _).mpr
  refine ⟨FiniteMap.sorted_erase key entries sorted, ?_⟩
  intro entry member
  exact comparableEntries entry (FiniteMap.mem_erase key entries entry member)

theorem Value.map_lookup_public (key : MapKey) (value : Value)
    (entries : List (MapKey × Value))
    (publicMap : (Value.map entries).isPublic = true)
    (found : FiniteMap.lookup key entries = some value) : value.isPublic = true := by
  have publicEntries := ((Value.map_public_iff entries).mp publicMap).2
  exact publicEntries (key, value) (FiniteMap.mem_of_lookup key value entries found)

theorem Value.map_lookup_comparable (key : MapKey) (value : Value)
    (entries : List (MapKey × Value))
    (comparableMap : (Value.map entries).exactComparable = true)
    (found : FiniteMap.lookup key entries = some value) : value.exactComparable = true := by
  have comparableEntries := ((Value.map_comparable_iff entries).mp comparableMap).2
  exact comparableEntries (key, value) (FiniteMap.mem_of_lookup key value entries found)

/-- Canonicality makes the stored representation extensional. This is why
    structural equality of these entry lists implements order-independent map
    equality, rather than exposing the order of source insertions. -/
theorem Value.map_equal_iff_lookup (left right : List (MapKey × Value))
    (leftComparable : (Value.map left).exactComparable = true)
    (rightComparable : (Value.map right).exactComparable = true) :
    (Value.map left == Value.map right) = true ↔
      ∀ key, FiniteMap.lookup key left = FiniteMap.lookup key right := by
  rw [Value.beq_eq_true _ _ leftComparable]
  constructor
  · intro equal
    have entries := Value.map.inj equal
    intro key
    rw [entries]
  · intro same
    exact congrArg Value.map (FiniteMap.ext_sorted left right
      ((Value.map_comparable_iff left).mp leftComparable).1
      ((Value.map_comparable_iff right).mp rightComparable).1 same)

end Erlean.Core

