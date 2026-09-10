import Erlean.Semantics.Machine

namespace Erlean.Semantics

open Erlean.Core

/-- A proper left operand appends to any right tail, including an improper
    tail. Publicness is a separate builtin admission condition. -/
theorem appendValues_list (values : List Value) (tail : Value) :
    appendValues (values.foldr Value.cons .nil) tail =
      some (values.foldr Value.cons tail) := by
  induction values with
  | nil => rfl
  | cons head rest ih => simp [List.foldr, appendValues, ih]

theorem list_tail_public (values : List Value) (tail : Value)
    (publicValues : Value.publicList values = true) (publicTail : tail.isPublic = true) :
    (values.foldr Value.cons tail).isPublic = true := by
  induction values with
  | nil => exact publicTail
  | cons head rest ih =>
    have parts : head.isPublic = true ∧ Value.publicList rest = true := by
      simpa only [Value.publicList, Bool.and_eq_true] using publicValues
    simpa only [List.foldr, Value.isPublic, parts.1, Bool.true_and] using ih parts.2

theorem builtin_append_list (machine : LocalState) (values : List Value) (tail : Value)
    (publicValues : Value.publicList values = true) (publicTail : tail.isPublic = true) :
    builtin machine "++" [values.foldr Value.cons .nil, tail] =
      nextControl machine (.ret [values.foldr Value.cons tail]) := by
  have publicLeft := list_tail_public values .nil publicValues (by simp [Value.isPublic])
  simp [builtin, Value.publicList, publicLeft, publicTail, appendValues_list]

/-- Any non-list final tail makes a cons chain an improper left operand. -/
theorem appendValues_improper (values : List Value) (endValue tail : Value)
    (notNil : endValue ≠ .nil)
    (notCons : ∀ head rest, endValue ≠ .cons head rest) :
    appendValues (values.foldr Value.cons endValue) tail = none := by
  have base : appendValues endValue tail = none := by
    cases endValue <;> simp_all [appendValues]
  induction values with
  | nil => exact base
  | cons head rest ih => simp [List.foldr, appendValues, ih]

theorem builtin_append_improper (machine : LocalState) (values : List Value)
    (endValue tail : Value)
    (publicValues : Value.publicList values = true)
    (publicEnd : endValue.isPublic = true) (publicTail : tail.isPublic = true)
    (notNil : endValue ≠ .nil)
    (notCons : ∀ head rest, endValue ≠ .cons head rest) :
    builtin machine "++" [values.foldr Value.cons endValue, tail] =
      raiseError machine (.atom "badarg") := by
  have publicLeft := list_tail_public values endValue publicValues publicEnd
  simp [builtin, Value.publicList, publicLeft, publicTail,
    appendValues_improper values endValue tail notNil notCons]

end Erlean.Semantics
