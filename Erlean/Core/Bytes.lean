import Init.Data.Int.DivMod.Lemmas
import Init.Data.List.Lemmas
import Lean.Elab.Tactic.Omega
import Erlean.Core.Syntax

namespace Erlean.Core

/-- Low-order bits first, used internally to state the binary expansion proof. -/
def encodeLowBits : Nat → Nat → List Bool
  | 0, _ => []
  | width + 1, value => (value % 2 == 1) :: encodeLowBits width (value / 2)

def decodeLowBits : List Bool → Nat
  | [] => 0
  | bit :: rest => (if bit then 1 else 0) + 2 * decodeLowBits rest

theorem encodeLowBits_length (width value : Nat) :
    (encodeLowBits width value).length = width := by
  induction width generalizing value with
  | zero => rfl
  | succ width ih => simp [encodeLowBits, ih]

theorem decodeLowBits_encodeLowBits (width value : Nat)
    (bound : value < 2 ^ width) :
    decodeLowBits (encodeLowBits width value) = value := by
  induction width generalizing value with
  | zero =>
      have zero : value = 0 := by
        have : value < 1 := by simpa using bound
        omega
      subst value
      rfl
  | succ width ih =>
      have quotientBound : value / 2 < 2 ^ width := by
        rw [Nat.pow_succ] at bound
        omega
      simp only [encodeLowBits, decodeLowBits, ih (value / 2) quotientBound]
      by_cases bit : value % 2 = 1
      · simp [bit]
        omega
      · have bitFalse : (value % 2 == 1) = false := by simp [bit]
        simp [bitFalse]
        omega

/-- Encode an unsigned eight-bit segment in most-significant-bit-first order.
    Euclidean remainder retains the low eight bits even for negative integers. -/
def encodeByte (value : Int) : List Bool :=
  (encodeLowBits 8 (value % 256).toNat).reverse

/-- Decode exactly one unsigned byte. Other input lengths are rejected. -/
def decodeByte (bits : List Bool) : Option Int :=
  if bits.length = 8 then some (Int.ofNat (decodeLowBits bits.reverse)) else none

@[simp] theorem encodeByte_length (value : Int) : (encodeByte value).length = 8 := by
  simp [encodeByte, encodeLowBits_length]

theorem decodeByte_eq_none_of_length_ne (bits : List Bool) (h : bits.length ≠ 8) :
    decodeByte bits = none := by
  simp [decodeByte, h]

/-- Round-trip normalization is modulo 256 for every integer, including negatives. -/
theorem decodeByte_encodeByte_mod (value : Int) :
    decodeByte (encodeByte value) = some (value % 256) := by
  have nonnegative : 0 ≤ value % 256 := Int.emod_nonneg value (by decide)
  have bounded : value % 256 < 256 := Int.emod_lt_of_pos value (by decide)
  have natBound : (value % 256).toNat < 2 ^ 8 := by
    change (value % 256).toNat < 256
    omega
  unfold decodeByte
  rw [encodeByte_length]
  simp only [↓reduceIte, encodeByte, List.reverse_reverse,
    decodeLowBits_encodeLowBits 8 (value % 256).toNat natBound]
  exact congrArg some (Int.toNat_of_nonneg nonnegative)

theorem decodeByte_encodeByte (value : Int) (nonnegative : 0 ≤ value)
    (bounded : value < 256) : decodeByte (encodeByte value) = some value := by
  rw [decodeByte_encodeByte_mod, Int.emod_eq_of_lt nonnegative bounded]

/-- Decode exactly the requested number of bytes, rejecting any trailing bits. -/
def decodeByteValues : Nat → List Bool → Option Values
  | 0, bits => if bits.isEmpty then some [] else none
  | count + 1, bits => do
    let value ← decodeByte (bits.take 8)
    let rest ← decodeByteValues count (bits.drop 8)
    pure (.integer value :: rest)

def encodeByteValues (values : Values) : Option (List Bool) := do
  let bytes ← values.mapM fun value => match value with
    | .integer n => some (encodeByte n)
    | _ => none
  pure bytes.flatten

theorem decodeByteValues_single (value : Int) :
    decodeByteValues 1 (encodeByte value) = some [.integer (value % 256)] := by
  have take : (encodeByte value).take 8 = encodeByte value := by
    rw [← encodeByte_length value]
    exact List.take_length
  have drop : (encodeByte value).drop 8 = [] := by
    rw [← encodeByte_length value]
    exact List.drop_length
  simp [decodeByteValues, take, drop, decodeByte_encodeByte_mod]

end Erlean.Core
