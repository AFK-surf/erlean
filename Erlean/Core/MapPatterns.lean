import Erlean.Core.Maps
import Erlean.Core.PatternObservation

namespace Erlean.Core

/-- A singleton map pattern inspects only the selected field. Canonicality is
    required, but unrelated fields need not satisfy literal-comparison rules. -/
theorem matchPattern_map_singleton (key : MapKey) (pattern : Pattern)
    (entries : FiniteMap.Entries Value) (ordered : Value.mapOrdered entries = true) :
    matchPattern (.map [key] [pattern]) (.map entries) =
      (FiniteMap.lookup key entries).bind (matchPattern pattern) := by
  rw [matchPattern]
  cases found : FiniteMap.lookup key entries with
  | none =>
    simp [ordered, selectMapValues, List.mapM, List.mapM.loop, found]
  | some value =>
    cases matched : matchPattern pattern value <;>
      simp [ordered, selectMapValues, List.mapM, List.mapM.loop, found,
        matchPatterns, matched]

/-- A missing key fails the pattern without observing a stored value. A present
    key requires only the selected value's pattern-observation permission. -/
theorem patternObservationAllowed_map_singleton (key : MapKey) (pattern : Pattern)
    (entries : FiniteMap.Entries Value) (ordered : Value.mapOrdered entries = true) :
    patternObservationAllowed (.map [key] [pattern]) (.map entries) =
      match FiniteMap.lookup key entries with
      | none => true
      | some value => patternObservationAllowed pattern value := by
  rw [patternObservationAllowed]
  cases found : FiniteMap.lookup key entries <;>
    simp [ordered, selectMapValues, List.mapM, List.mapM.loop, found,
      patternsObservationAllowed]

/-- Atom literals can discriminate every public value without assigning an
    identity to floats or functions. Their outer constructors already differ. -/
theorem literalObservationAllowed_atom_public (name : String) (value : Value)
    (publicValue : value.isPublic = true) :
    literalObservationAllowed (.atom name) value = true := by
  cases value <;> simp_all [literalObservationAllowed, Value.isPublic]

/-- Bitstring literals can inspect public bitstrings or reject other outer
    constructors. This does not permit float or function equality. -/
theorem literalObservationAllowed_bitstring_public (bits : List Bool) (value : Value)
    (publicValue : value.isPublic = true) :
    literalObservationAllowed (.bitstring bits) value = true := by
  cases value <;> simp_all [literalObservationAllowed, Value.isPublic]

private theorem publicMap_ordered (entries : FiniteMap.Entries Value)
    (publicMap : (Value.map entries).isPublic = true) : Value.mapOrdered entries = true := by
  have parts : Value.mapOrdered entries = true ∧ Value.publicEntries entries = true := by
    simpa only [Value.isPublic, Bool.and_eq_true] using publicMap
  exact parts.1

theorem patternObservationAllowed_map_atom (key : MapKey) (name : String)
    (entries : FiniteMap.Entries Value) (publicMap : (Value.map entries).isPublic = true) :
    patternObservationAllowed (.map [key] [.lit (.atom name)]) (.map entries) = true := by
  rw [patternObservationAllowed_map_singleton key _ entries (publicMap_ordered entries publicMap)]
  cases found : FiniteMap.lookup key entries with
  | none => rfl
  | some value =>
    dsimp only []
    rw [patternObservationAllowed.eq_def]
    exact literalObservationAllowed_atom_public name value
      (Value.map_lookup_public key value entries publicMap found)

theorem patternObservationAllowed_map_bitstring (key : MapKey) (bits : List Bool)
    (entries : FiniteMap.Entries Value) (publicMap : (Value.map entries).isPublic = true) :
    patternObservationAllowed (.map [key] [.lit (.bitstring bits)]) (.map entries) = true := by
  rw [patternObservationAllowed_map_singleton key _ entries (publicMap_ordered entries publicMap)]
  cases found : FiniteMap.lookup key entries with
  | none => rfl
  | some value =>
    dsimp only []
    rw [patternObservationAllowed.eq_def]
    exact literalObservationAllowed_bitstring_public bits value
      (Value.map_lookup_public key value entries publicMap found)

end Erlean.Core
