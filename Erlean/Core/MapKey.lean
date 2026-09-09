import Init.Data.List.Lex
import Lean.Elab.Tactic.Omega

namespace Erlean.Core

/-- Comparable map keys in the initial map profile. Floats, functions, and
    maps used as keys are deliberately absent. The order below is an internal
    canonical representation order, not Erlang's observable term order. -/
inductive MapKey where
  | integer (value : Int)
  | atom (name : String)
  | nil
  | cons (head tail : MapKey)
  | tuple (elements : List MapKey)
  | bitstring (bits : List Bool)
  | pid (id : Nat)
  | reference (id : Nat)
  deriving Repr

namespace MapKey

private def integerCode : Int → List Nat
  | .ofNat n => [0, n]
  | .negSucc n => [1, n]

private def bitCode (bit : Bool) : Nat := if bit then 1 else 0

/-- A length prefix makes a child segment unambiguous without exponentially
    large numeric pairing. The serialized representation has linear size. -/
private def frame (payload suffix : List Nat) : List Nat :=
  payload.length :: (payload ++ suffix)

private theorem frame_injective (a b c d : List Nat)
    (equal : frame a b = frame c d) : a = c ∧ b = d := by
  obtain ⟨lengths, contents⟩ := List.cons.inj equal
  exact ⟨List.append_inj_left contents lengths, List.append_inj_right contents lengths⟩

mutual
def code : MapKey → List Nat
  | .integer value => 0 :: integerCode value
  | .atom name => 1 :: name.toList.map Char.toNat
  | .nil => [2]
  | .cons head tail => 3 :: frame (code head) (code tail)
  | .tuple elements => 4 :: listCode elements
  | .bitstring bits => 5 :: bits.map bitCode
  | .pid id => [6, id]
  | .reference id => [7, id]
termination_by key => sizeOf key

def listCode : List MapKey → List Nat
  | [] => []
  | head :: tail => frame (code head) (listCode tail)
termination_by keys => sizeOf keys
end

mutual
theorem code_injective (left right : MapKey) (equal : code left = code right) : left = right := by
  match left, right with
  | .integer a, .integer b =>
    cases a <;> cases b <;> simp_all [code, integerCode]
  | .atom a, .atom b =>
    rw [code, code] at equal
    have chars : a.toList.map Char.toNat = b.toList.map Char.toNat := (List.cons.inj equal).2
    have lists : a.toList = b.toList :=
      (List.map_inj_right (fun _ _ same => Char.toNat_inj.mp same)).mp chars
    exact congrArg MapKey.atom (String.toList_injective lists)
  | .nil, .nil => rfl
  | .cons a b, .cons c d =>
    rw [code, code] at equal
    have parts := frame_injective (code a) (code b) (code c) (code d) (List.cons.inj equal).2
    rw [code_injective a c parts.1, code_injective b d parts.2]
  | .tuple a, .tuple b =>
    rw [code, code] at equal
    exact congrArg MapKey.tuple (listCode_injective a b (List.cons.inj equal).2)
  | .bitstring a, .bitstring b =>
    rw [code, code] at equal
    have bits : a.map bitCode = b.map bitCode := (List.cons.inj equal).2
    have lists : a = b :=
      (List.map_inj_right (fun x y same => by cases x <;> cases y <;> simp_all [bitCode])).mp bits
    exact congrArg MapKey.bitstring lists
  | .pid a, .pid b => simpa [code] using equal
  | .reference a, .reference b => simpa [code] using equal
  | .integer _, .atom _ => simp [code] at equal
  | .integer _, .nil => simp [code] at equal
  | .integer _, .cons _ _ => simp [code] at equal
  | .integer _, .tuple _ => simp [code] at equal
  | .integer _, .bitstring _ => simp [code] at equal
  | .integer _, .pid _ => simp [code] at equal
  | .integer _, .reference _ => simp [code] at equal
  | .atom _, .integer _ => simp [code] at equal
  | .atom _, .nil => simp [code] at equal
  | .atom _, .cons _ _ => simp [code] at equal
  | .atom _, .tuple _ => simp [code] at equal
  | .atom _, .bitstring _ => simp [code] at equal
  | .atom _, .pid _ => simp [code] at equal
  | .atom _, .reference _ => simp [code] at equal
  | .nil, .integer _ => simp [code] at equal
  | .nil, .atom _ => simp [code] at equal
  | .nil, .cons _ _ => simp [code] at equal
  | .nil, .tuple _ => simp [code] at equal
  | .nil, .bitstring _ => simp [code] at equal
  | .nil, .pid _ => simp [code] at equal
  | .nil, .reference _ => simp [code] at equal
  | .cons _ _, .integer _ => simp [code] at equal
  | .cons _ _, .atom _ => simp [code] at equal
  | .cons _ _, .nil => simp [code] at equal
  | .cons _ _, .tuple _ => simp [code] at equal
  | .cons _ _, .bitstring _ => simp [code] at equal
  | .cons _ _, .pid _ => simp [code] at equal
  | .cons _ _, .reference _ => simp [code] at equal
  | .tuple _, .integer _ => simp [code] at equal
  | .tuple _, .atom _ => simp [code] at equal
  | .tuple _, .nil => simp [code] at equal
  | .tuple _, .cons _ _ => simp [code] at equal
  | .tuple _, .bitstring _ => simp [code] at equal
  | .tuple _, .pid _ => simp [code] at equal
  | .tuple _, .reference _ => simp [code] at equal
  | .bitstring _, .integer _ => simp [code] at equal
  | .bitstring _, .atom _ => simp [code] at equal
  | .bitstring _, .nil => simp [code] at equal
  | .bitstring _, .cons _ _ => simp [code] at equal
  | .bitstring _, .tuple _ => simp [code] at equal
  | .bitstring _, .pid _ => simp [code] at equal
  | .bitstring _, .reference _ => simp [code] at equal
  | .pid _, .integer _ => simp [code] at equal
  | .pid _, .atom _ => simp [code] at equal
  | .pid _, .nil => simp [code] at equal
  | .pid _, .cons _ _ => simp [code] at equal
  | .pid _, .tuple _ => simp [code] at equal
  | .pid _, .bitstring _ => simp [code] at equal
  | .pid _, .reference _ => simp [code] at equal
  | .reference _, .integer _ => simp [code] at equal
  | .reference _, .atom _ => simp [code] at equal
  | .reference _, .nil => simp [code] at equal
  | .reference _, .cons _ _ => simp [code] at equal
  | .reference _, .tuple _ => simp [code] at equal
  | .reference _, .bitstring _ => simp [code] at equal
  | .reference _, .pid _ => simp [code] at equal
termination_by sizeOf left

theorem listCode_injective (left right : List MapKey)
    (equal : listCode left = listCode right) : left = right := by
  match left, right with
  | [], [] => rfl
  | [], _ :: _ | _ :: _, [] => simp [listCode, frame] at equal
  | a :: rest, b :: tail =>
    rw [listCode, listCode] at equal
    have parts := frame_injective (code a) (listCode rest) (code b) (listCode tail) equal
    rw [code_injective a b parts.1, listCode_injective rest tail parts.2]
termination_by sizeOf left
end

instance : DecidableEq MapKey := fun left right =>
  if equal : code left = code right then isTrue (code_injective left right equal)
  else isFalse (fun same => equal (congrArg code same))

instance : BEq MapKey := ⟨fun left right => code left == code right⟩

theorem beq_eq_true (left right : MapKey) : (left == right) = true ↔ left = right := by
  change (code left == code right) = true ↔ left = right
  simp only [beq_iff_eq]
  exact ⟨code_injective left right, congrArg code⟩

instance : LawfulBEq MapKey where
  eq_of_beq := fun h => (beq_eq_true _ _).mp h
  rfl := (beq_eq_true _ _).mpr rfl

/-- Strict lexicographic order on the injective canonical encoding. -/
def before (left right : MapKey) : Bool :=
  decide (List.Lex (fun a b : Nat => a < b) (code left) (code right))

theorem before_irrefl (key : MapKey) : before key key = false := by
  simp only [before, decide_eq_false_iff_not]
  exact List.lex_irrefl Nat.lt_irrefl (code key)

theorem before_trans (a b c : MapKey)
    (first : before a b = true) (second : before b c = true) : before a c = true := by
  simp only [before, decide_eq_true_eq] at *
  exact List.lex_trans Nat.lt_trans first second

theorem before_asymm (a b : MapKey) (first : before a b = true) : before b a = false := by
  simp only [before, decide_eq_true_eq, decide_eq_false_iff_not] at *
  exact List.lex_asymm Nat.lt_asymm first

theorem before_trichotomy (a b : MapKey) :
    before a b = true ∨ a = b ∨ before b a = true := by
  by_cases first : List.Lex (fun x y : Nat => x < y) (code a) (code b)
  · exact Or.inl (by simpa only [before, decide_eq_true_eq] using first)
  · by_cases second : List.Lex (fun x y : Nat => x < y) (code b) (code a)
    · exact Or.inr (Or.inr (by simpa only [before, decide_eq_true_eq] using second))
    · have equal : code a = code b := List.lex_trichotomous (fun x y hxy hyx => by omega) second first
      exact Or.inr (Or.inl (code_injective a b equal))

theorem before_ne (a b : MapKey) (less : before a b = true) : a ≠ b := by
  intro equal
  subst b
  simp [before_irrefl] at less

theorem before_of_ne_of_not_before (a b : MapKey)
    (different : a ≠ b) (notBefore : before b a = false) : before a b = true := by
  rcases before_trichotomy a b with less | equal | greater
  · exact less
  · exact False.elim (different equal)
  · simp [notBefore] at greater

def compare (a b : MapKey) : Ordering :=
  if before a b then .lt else if before b a then .gt else .eq

theorem compare_eq_iff (a b : MapKey) : compare a b = .eq ↔ a = b := by
  constructor
  · intro equal
    rcases before_trichotomy a b with less | same | greater
    · simp [compare, less] at equal
    · exact same
    · have reverse := before_asymm b a greater
      simp [compare, reverse, greater] at equal
  · intro equal
    subst b
    simp [compare, before_irrefl]

end MapKey
end Erlean.Core
