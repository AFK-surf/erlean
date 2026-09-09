import Erlean.Core.Syntax

namespace Erlean.Core

mutual
/-- Comparable data can be observed publicly. This does not make closure or
    named-function identity observable. -/
theorem Value.public_of_exactComparable (value : Value)
    (comparable : value.exactComparable = true) : value.isPublic = true := by
  match value with
  | .cons head tail =>
    have parts : head.exactComparable = true ∧ tail.exactComparable = true := by
      simpa only [Value.exactComparable, Bool.and_eq_true] using comparable
    simp [Value.isPublic, Value.public_of_exactComparable head parts.1,
      Value.public_of_exactComparable tail parts.2]
  | .tuple values =>
    simpa only [Value.isPublic] using Value.publicList_of_comparableList values
      (by simpa only [Value.exactComparable] using comparable)
  | .function _ _ _ | .closure _ _ _ _ | .exceptionInfo _ =>
    simp [Value.exactComparable] at comparable
  | .integer _ | .atom _ | .nil | .bitstring _ | .pid _ | .reference _ =>
    simp [Value.isPublic]
termination_by sizeOf value

theorem Value.publicList_of_comparableList (values : List Value)
    (comparable : Value.comparableList values = true) : Value.publicList values = true := by
  match values with
  | [] => simp [Value.publicList]
  | value :: rest =>
    have parts : value.exactComparable = true ∧ Value.comparableList rest = true := by
      simpa only [Value.comparableList, Bool.and_eq_true] using comparable
    simp [Value.publicList, Value.public_of_exactComparable value parts.1,
      Value.publicList_of_comparableList rest parts.2]
termination_by sizeOf values
end

mutual
/-- Structural equality reflects propositional equality on the supported data
    domain. Only the left operand needs a comparability premise for reflection;
    the executable equality BIF continues to check both operands. -/
theorem Value.equal_eq_true (left right : Value)
    (comparable : left.exactComparable = true) : left.equal right = true ↔ left = right := by
  match left with
  | .integer _ | .atom _ | .nil | .bitstring _ | .pid _ | .reference _ =>
    cases right <;> simp [Value.equal]
  | .cons head tail =>
    have parts : head.exactComparable = true ∧ tail.exactComparable = true := by
      simpa only [Value.exactComparable, Bool.and_eq_true] using comparable
    cases right with
    | cons other rest =>
      simp only [Value.equal, Bool.and_eq_true, Value.cons.injEq,
        Value.equal_eq_true head other parts.1, Value.equal_eq_true tail rest parts.2]
    | _ => simp [Value.equal]
  | .tuple values =>
    cases right with
    | tuple others =>
      simpa only [Value.equal, Value.tuple.injEq] using
        Value.equalList_eq_true values others
          (by simpa only [Value.exactComparable] using comparable)
    | _ => simp [Value.equal]
  | .function _ _ _ | .closure _ _ _ _ | .exceptionInfo _ =>
    simp [Value.exactComparable] at comparable
termination_by sizeOf left

theorem Value.equalList_eq_true (left right : List Value)
    (comparable : Value.comparableList left = true) :
    Value.equalList left right = true ↔ left = right := by
  match left, right with
  | [], [] | [], _ :: _ | _ :: _, [] => simp [Value.equalList]
  | value :: rest, other :: tail =>
    have parts : value.exactComparable = true ∧ Value.comparableList rest = true := by
      simpa only [Value.comparableList, Bool.and_eq_true] using comparable
    simp only [Value.equalList, Bool.and_eq_true, List.cons.injEq,
      Value.equal_eq_true value other parts.1, Value.equalList_eq_true rest tail parts.2]
termination_by sizeOf left
end

theorem Value.equal_self (value : Value) (comparable : value.exactComparable = true) :
    value.equal value = true := (Value.equal_eq_true value value comparable).mpr rfl

theorem Value.beq_eq_true (left right : Value) (comparable : left.exactComparable = true) :
    (left == right) = true ↔ left = right := Value.equal_eq_true left right comparable

theorem Value.beq_self (value : Value) (comparable : value.exactComparable = true) :
    (value == value) = true := Value.equal_self value comparable

theorem Value.equal_eq_false (left right : Value) (comparable : left.exactComparable = true) :
    left.equal right = false ↔ left ≠ right := by
  cases compared : left.equal right with
  | false =>
    have different : left ≠ right := by
      intro equal
      have same := (Value.equal_eq_true left right comparable).mpr equal
      simp [compared] at same
    simp [different]
  | true =>
    have equal := (Value.equal_eq_true left right comparable).mp compared
    simp [equal]

theorem Value.beq_eq_false (left right : Value) (comparable : left.exactComparable = true) :
    (left == right) = false ↔ left ≠ right := Value.equal_eq_false left right comparable

end Erlean.Core
