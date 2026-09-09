import Erlean.Semantics.Machine
import Erlean.Semantics.Observation
import Erlean.Core.Equality
import Erlean.Core.MapPatterns

open Erlean.Core Erlean.Semantics

private def context : LocalState := ⟨.ret [], ⟨"map_checks", []⟩, []⟩
private def key : MapKey := .atom "key"
private def funValue : Value := .function "example" "identity" 1

-- Recursive semantic functions use equation lemmas, not definitional evaluation
-- of their well-founded implementations. All conclusions remain kernel checked.
local macro "map_check" : tactic => `(tactic|
  simp [key, funValue, Value.isPublic, Value.exactComparable,
    Value.publicEntries, Value.comparableEntries, Value.publicList,
    Value.mapOrdered, FiniteMap.Sorted, MapKey.before_irrefl, Value.toMapKey,
    mapBuiltin, withMap, withMapKey, matchPattern, matchPatterns,
    selectMapValues, List.mapM, List.mapM.loop, patternObservationAllowed,
    patternsObservationAllowed, literalObservationAllowed,
    finishMap, missingExactKeys, updateMapEntries,
    FiniteMap.lookup, FiniteMap.insert])

-- Function values can cross maps without inventing function-key identity.
example : (Value.map [(key, funValue)]).isPublic = true := by map_check
example : (Value.map [(key, funValue)]).exactComparable = false := by map_check
example : funValue.toMapKey = none := by map_check
example : (Value.map []).toMapKey = none := by map_check
example : mapBuiltin context "get" [.atom "key", .map [(key, funValue)]] =
    nextControl context (.ret [funValue]) := by map_check
example : matchPattern (.map [key] [.var 7]) (.map [(key, funValue)]) =
    some [(7, funValue)] := by map_check
example : patternObservationAllowed (.map [key] [.var 7])
    (.map [(key, funValue)]) = true := by map_check
example : patternObservationAllowed (.lit (.map [(key, funValue)]))
    (.map [(key, funValue)]) = false := by map_check

-- Scalar-field discrimination does not assign equality to function values.
example : patternObservationAllowed (.map [key] [.lit (.atom "ready")])
    (.map [(key, funValue)]) = true := by
  apply patternObservationAllowed_map_atom
  map_check

example : matchPattern (.map [key] [.lit (.atom "ready")])
    (.map [(key, funValue)]) = none := by
  rw [matchPattern_map_singleton key _ _ (by map_check)]
  simp [key, funValue, FiniteMap.lookup, matchPattern, BEq.beq, Value.equal]

-- Raw malformed representations never become public comparable maps.
example : (Value.map [(key, .nil), (key, .nil)]).isPublic = false := by map_check
example : (Value.map [(key, .nil), (key, .nil)]).exactComparable = false := by map_check
example : (Value.map [(key, .exceptionInfo "error")]).isPublic = false := by map_check
example : patternObservationAllowed (.map [] [])
    (.map [(key, .nil), (key, .nil)]) = false := by map_check

-- Selected fields alone determine map-pattern observation requirements.
example : patternObservationAllowed (.map [] [])
    (.map [(key, funValue)]) = true := by map_check
example : matchPattern (.map [] []) (.map [(key, funValue)]) = some [] := by map_check
example : matchPattern (.map [key] []) (.map [(key, funValue)]) = none := by map_check
example : finishMap context [true] [.map [], .atom "key", .nil] =
    raiseError context (.tuple [.atom "badkey", .atom "key"]) := by map_check
example : finishMap context [false, true]
    [.map [], .atom "key", .integer 1, .atom "key", .integer 2] =
    nextControl context (.ret [.map [(key, .integer 2)]]) := by map_check
example : finishMap context [true, false]
    [.map [], .atom "key", .integer 1, .atom "key", .integer 2] =
    raiseError context (.tuple [.atom "badkey", .atom "key"]) := by map_check

def main : IO Unit :=
  IO.println "Map boundary regressions passed. Finite checks do not replace universal map laws."
