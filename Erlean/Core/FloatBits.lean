import Init.Data.UInt.Basic
import Init.Data.String.Basic
import Init.Data.List.Lemmas

namespace Erlean.Core.FloatBits

/-- Finite IEEE 754 binary64 encodings exclude the all-ones exponent.
    This is a transport predicate, not floating-point arithmetic semantics. -/
def isFinite (bits : UInt64) : Bool :=
  (bits.toNat / 2 ^ 52) % 2048 != 2047

private def hexValue (digit : Char) : Option Nat :=
  let n := digit.toNat
  if 48 ≤ n && n ≤ 57 then some (n - 48)
  else if 97 ≤ n && n ≤ 102 then some (n - 87)
  else if 65 ≤ n && n ≤ 70 then some (n - 55)
  else none

private def parseDigits : List Char → Nat → Option Nat
  | [], accumulator => some accumulator
  | digit :: rest, accumulator => do
    let nibble ← hexValue digit
    parseDigits rest (16 * accumulator + nibble)

/-- Parse exactly sixteen most-significant-digit-first hexadecimal digits.
    Both cases are accepted. NaNs and infinities are explicitly rejected;
    negative zero and subnormal encodings are retained without conversion. -/
def parseHex (text : String) : Except String UInt64 :=
  if text.toList.length != 16 then
    .error "Float encoding must contain exactly 16 hexadecimal digits"
  else match parseDigits text.toList 0 with
    | none => .error "Invalid hexadecimal digit in float encoding"
    | some value =>
      let bits := UInt64.ofNat value
      if isFinite bits then .ok bits
      else .error "NaN and infinity are outside the finite float profile"

private def hexDigit (nibble : Nat) : Char :=
  Char.ofNat (if nibble < 10 then 48 + nibble else 87 + nibble)

private def encodeDigits : Nat → Nat → List Char
  | 0, _ => []
  | width + 1, value =>
    encodeDigits width (value / 16) ++ [hexDigit (value % 16)]

/-- Render the raw bits as sixteen lowercase hexadecimal digits. Encoding does
    not itself admit a value into the finite-float semantic profile. -/
def encodeHex (bits : UInt64) : String :=
  String.ofList (encodeDigits 16 bits.toNat)

private theorem encodeDigits_length (width value : Nat) :
    (encodeDigits width value).length = width := by
  induction width generalizing value with
  | zero => rfl
  | succ width ih => simp [encodeDigits, ih]

theorem encodeHex_length (bits : UInt64) : (encodeHex bits).toList.length = 16 := by
  simp only [encodeHex, String.toList_ofList, encodeDigits_length]

/-- Every successfully decoded encoding satisfies the explicit finite boundary. -/
theorem parseHex_finite (text : String) (bits : UInt64)
    (accepted : parseHex text = .ok bits) : isFinite bits = true := by
  unfold parseHex at accepted
  split at accepted
  · cases accepted
  · split at accepted
    · cases accepted
    · dsimp only at accepted
      split at accepted
      · cases accepted
        assumption
      · cases accepted

-- Closed boundary checks are kernel proofs, not a general codec-roundtrip proof.
example : parseHex "0000000000000000" = .ok 0 := by rfl
example : parseHex "8000000000000000" = .ok 9223372036854775808 := by rfl
example : parseHex "0000000000000001" = .ok 1 := by rfl
example : parseHex "7fefffffffffffff" = .ok 9218868437227405311 := by rfl
example : parseHex "7FEFFFFFFFFFFFFF" = .ok 9218868437227405311 := by rfl
example : (parseHex "7ff0000000000000").isOk = false := by decide
example : (parseHex "fff0000000000000").isOk = false := by decide
example : (parseHex "7ff8000000000001").isOk = false := by decide
example : (parseHex "000000000000000g").isOk = false := by decide
example : (parseHex "000000000000000").isOk = false := by decide
example : (parseHex "00000000000000000").isOk = false := by decide
example : encodeHex 0 = "0000000000000000" := by decide
example : encodeHex 9223372036854775808 = "8000000000000000" := by decide
example : encodeHex 1 = "0000000000000001" := by decide
example : encodeHex 9218868437227405311 = "7fefffffffffffff" := by decide

end Erlean.Core.FloatBits
