import Erlean.Core.ValueRules
import Erlean.Core.PatternObservation

open Erlean.Core

-- Transport does not grant arithmetic, key identity, or literal equality.
example (bits : UInt64) : (Value.floatBits bits).exactComparable = false := by simp
example (bits : UInt64) : (Value.floatBits bits).toMapKey = none := by
  simp [Value.toMapKey]
example (bits : UInt64) :
    (Value.floatBits bits).isPublic = FloatBits.isFinite bits := by simp
example (left right : UInt64) :
    literalObservationAllowed (.floatBits left) (.floatBits right) = false := by
  rw [literalObservationAllowed]
example (bits : UInt64) : patternObservationAllowed (.var 0) (.floatBits bits) = true := by
  rw [patternObservationAllowed]
example (bits : UInt64) :
    (Value.map [(.atom "payload", .floatBits bits)]).exactComparable = false := by
  simp [Value.comparableEntries]
example : (Value.floatBits 0).isPublic = true := by
  rw [Value.isPublic]
  decide
example : (Value.floatBits 9218868437227405312).isPublic = false := by
  rw [Value.isPublic]
  decide

def main : IO Unit :=
  IO.println "Finite-float transport boundary proofs passed. Numeric operations remain unsupported."
