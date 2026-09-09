import Erlean.Core.Maps
import Erlean.Semantics.Machine

namespace Erlean.Semantics

open Core

/-- Open-input rewrite rules for map execution. These rules retain canonical
    public-map premises and do not assume function equality. -/
theorem withMap_public (state : LocalState) (entries : FiniteMap.Entries Value)
    (body : FiniteMap.Entries Value → Transition LocalState Outcome)
    (publicMap : (Value.map entries).isPublic = true) :
    withMap state (.map entries) body = body entries := by
  have parts : Value.mapOrdered entries = true ∧ Value.publicEntries entries = true := by
    simpa only [Value.isPublic, Bool.and_eq_true] using publicMap
  simp [withMap, parts.1, parts.2]

theorem withMapKey_supported (key : MapKey)
    (body : MapKey → Transition LocalState Outcome) :
    withMapKey key.toValue body = body key := by
  simp [withMapKey, MapKey.toValue_toMapKey]

theorem withMapKey_of_toMapKey (key : Value) (mapKey : MapKey)
    (body : MapKey → Transition LocalState Outcome)
    (supported : key.toMapKey = some mapKey) :
    withMapKey key body = body mapKey := by
  simp [withMapKey, supported]

theorem mapBuiltin_get_default_of_toMapKey (state : LocalState)
    (key : Value) (mapKey : MapKey) (entries : FiniteMap.Entries Value) (default : Value)
    (publicMap : (Value.map entries).isPublic = true)
    (publicKey : key.isPublic = true) (publicDefault : default.isPublic = true)
    (supported : key.toMapKey = some mapKey) :
    mapBuiltin state "get" [key, .map entries, default] =
      nextControl state (.ret [(FiniteMap.lookup mapKey entries).getD default]) := by
  simp [mapBuiltin, Value.publicList, publicMap, publicKey, publicDefault,
    withMap_public state entries _ publicMap, withMapKey_of_toMapKey key mapKey _ supported]

theorem mapBuiltin_put_of_toMapKey (state : LocalState)
    (key : Value) (mapKey : MapKey) (value : Value) (entries : FiniteMap.Entries Value)
    (publicMap : (Value.map entries).isPublic = true)
    (publicKey : key.isPublic = true) (publicValue : value.isPublic = true)
    (supported : key.toMapKey = some mapKey) :
    mapBuiltin state "put" [key, value, .map entries] =
      nextControl state (.ret [.map (FiniteMap.insert mapKey value entries)]) := by
  simp [mapBuiltin, Value.publicList, publicMap, publicKey, publicValue,
    withMap_public state entries _ publicMap, withMapKey_of_toMapKey key mapKey _ supported]

theorem mapBuiltin_remove_of_toMapKey (state : LocalState)
    (key : Value) (mapKey : MapKey) (entries : FiniteMap.Entries Value)
    (publicMap : (Value.map entries).isPublic = true)
    (publicKey : key.isPublic = true) (supported : key.toMapKey = some mapKey) :
    mapBuiltin state "remove" [key, .map entries] =
      nextControl state (.ret [.map (FiniteMap.erase mapKey entries)]) := by
  simp [mapBuiltin, Value.publicList, publicMap, publicKey,
    withMap_public state entries _ publicMap, withMapKey_of_toMapKey key mapKey _ supported]

theorem mapBuiltin_find_of_toMapKey (state : LocalState)
    (key : Value) (mapKey : MapKey) (entries : FiniteMap.Entries Value)
    (publicMap : (Value.map entries).isPublic = true)
    (publicKey : key.isPublic = true) (supported : key.toMapKey = some mapKey) :
    mapBuiltin state "find" [key, .map entries] =
      match FiniteMap.lookup mapKey entries with
      | some value => nextControl state (.ret [.tuple [.atom "ok", value]])
      | none => nextControl state (.ret [.atom "error"]) := by
  simp [mapBuiltin, Value.publicList, publicMap, publicKey,
    withMap_public state entries _ publicMap,
    withMapKey_of_toMapKey key mapKey _ supported] <;> rfl

theorem mapBuiltin_merge (state : LocalState) (left right : FiniteMap.Entries Value)
    (publicLeft : (Value.map left).isPublic = true)
    (publicRight : (Value.map right).isPublic = true) :
    mapBuiltin state "merge" [.map left, .map right] =
      nextControl state (.ret [.map (right.foldl (fun entries pair =>
        FiniteMap.insert pair.1 pair.2 entries) left)]) := by
  simp [mapBuiltin, Value.publicList, publicLeft, publicRight,
    withMap_public state left _ publicLeft, withMap_public state right _ publicRight]

theorem mapBuiltin_get (state : LocalState) (key : MapKey)
    (entries : FiniteMap.Entries Value)
    (publicMap : (Value.map entries).isPublic = true) :
    mapBuiltin state "get" [key.toValue, .map entries] =
      match FiniteMap.lookup key entries with
      | some value => nextControl state (.ret [value])
      | none => raiseError state (.tuple [.atom "badkey", key.toValue]) := by
  simp [mapBuiltin, Value.publicList, publicMap, MapKey.toValue_public,
    withMap_public state entries _ publicMap, withMapKey_supported]
  rfl

theorem mapBuiltin_get_default (state : LocalState) (key : MapKey)
    (entries : FiniteMap.Entries Value) (default : Value)
    (publicMap : (Value.map entries).isPublic = true) (defaultPublic : default.isPublic = true) :
    mapBuiltin state "get" [key.toValue, .map entries, default] =
      nextControl state (.ret [(FiniteMap.lookup key entries).getD default]) := by
  simp [mapBuiltin, Value.publicList, publicMap, defaultPublic, MapKey.toValue_public,
    withMap_public state entries _ publicMap, withMapKey_supported]

theorem mapBuiltin_put (state : LocalState) (key : MapKey) (value : Value)
    (entries : FiniteMap.Entries Value)
    (publicMap : (Value.map entries).isPublic = true) (valuePublic : value.isPublic = true) :
    mapBuiltin state "put" [key.toValue, value, .map entries] =
      nextControl state (.ret [.map (FiniteMap.insert key value entries)]) := by
  simp [mapBuiltin, Value.publicList, publicMap, valuePublic, MapKey.toValue_public,
    withMap_public state entries _ publicMap, withMapKey_supported]

theorem mapBuiltin_remove (state : LocalState) (key : MapKey)
    (entries : FiniteMap.Entries Value)
    (publicMap : (Value.map entries).isPublic = true) :
    mapBuiltin state "remove" [key.toValue, .map entries] =
      nextControl state (.ret [.map (FiniteMap.erase key entries)]) := by
  simp [mapBuiltin, Value.publicList, publicMap, MapKey.toValue_public,
    withMap_public state entries _ publicMap, withMapKey_supported]

theorem mapBuiltin_find (state : LocalState) (key : MapKey)
    (entries : FiniteMap.Entries Value)
    (publicMap : (Value.map entries).isPublic = true) :
    mapBuiltin state "find" [key.toValue, .map entries] =
      match FiniteMap.lookup key entries with
      | some value => nextControl state (.ret [.tuple [.atom "ok", value]])
      | none => nextControl state (.ret [.atom "error"]) :=
  mapBuiltin_find_of_toMapKey state key.toValue key entries publicMap
    (MapKey.toValue_public key) (MapKey.toValue_toMapKey key)

end Erlean.Semantics
