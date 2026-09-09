import Erlean.Core.Syntax

namespace Erlean.Core.Value

/-- Constructor rules avoid repeatedly preprocessing the full mutually recursive
    predicate equations in executable-semantics proofs. Closure captures remain
    opaque; these rules do not assign observable function identities. -/
@[simp] theorem isPublic_integer (n : Int) :
    (.integer n : Value).isPublic = (true) := by rw [Value.isPublic]

@[simp] theorem isPublic_floatBits (bits : UInt64) :
    (.floatBits bits : Value).isPublic = FloatBits.isFinite bits := by rw [Value.isPublic]

@[simp] theorem isPublic_atom (name : String) :
    (.atom name : Value).isPublic = (true) := by rw [Value.isPublic]

@[simp] theorem isPublic_nil  :
    (.nil : Value).isPublic = (true) := by rw [Value.isPublic]

@[simp] theorem isPublic_cons (head tail : Value) :
    (.cons head tail : Value).isPublic = (head.isPublic && tail.isPublic) := by rw [Value.isPublic]

@[simp] theorem isPublic_tuple (values : List Value) :
    (.tuple values : Value).isPublic = (Value.publicList values) := by rw [Value.isPublic]

@[simp] theorem isPublic_map (entries : List (MapKey × Value)) :
    (.map entries : Value).isPublic = (Value.mapOrdered entries && Value.publicEntries entries) := by rw [Value.isPublic]

@[simp] theorem isPublic_bitstring (bits : List Bool) :
    (.bitstring bits : Value).isPublic = (true) := by rw [Value.isPublic]

@[simp] theorem isPublic_pid (id : Nat) :
    (.pid id : Value).isPublic = (true) := by rw [Value.isPublic]

@[simp] theorem isPublic_reference (id : Nat) :
    (.reference id : Value).isPublic = (true) := by rw [Value.isPublic]

@[simp] theorem isPublic_function (moduleName name : String) (arity : Nat) :
    (.function moduleName name arity : Value).isPublic = (true) := by rw [Value.isPublic]

@[simp] theorem isPublic_closure (moduleName : String) (code : Nat) (captured : List (VarId × Value))
    (group : List (VarId × Nat)) :
    (.closure moduleName code captured group : Value).isPublic = (true) := by rw [Value.isPublic]

@[simp] theorem isPublic_exceptionInfo (kind : String) :
    (.exceptionInfo kind : Value).isPublic = (false) := by rw [Value.isPublic]

@[simp] theorem exactComparable_integer (n : Int) :
    (.integer n : Value).exactComparable = (true) := by rw [Value.exactComparable]

@[simp] theorem exactComparable_floatBits (bits : UInt64) :
    (.floatBits bits : Value).exactComparable = (false) := by rw [Value.exactComparable]

@[simp] theorem exactComparable_atom (name : String) :
    (.atom name : Value).exactComparable = (true) := by rw [Value.exactComparable]

@[simp] theorem exactComparable_nil  :
    (.nil : Value).exactComparable = (true) := by rw [Value.exactComparable]

@[simp] theorem exactComparable_cons (head tail : Value) :
    (.cons head tail : Value).exactComparable = (head.exactComparable && tail.exactComparable) := by rw [Value.exactComparable]

@[simp] theorem exactComparable_tuple (values : List Value) :
    (.tuple values : Value).exactComparable = (Value.comparableList values) := by rw [Value.exactComparable]

@[simp] theorem exactComparable_map (entries : List (MapKey × Value)) :
    (.map entries : Value).exactComparable = (Value.mapOrdered entries && Value.comparableEntries entries) := by rw [Value.exactComparable]

@[simp] theorem exactComparable_bitstring (bits : List Bool) :
    (.bitstring bits : Value).exactComparable = (true) := by rw [Value.exactComparable]

@[simp] theorem exactComparable_pid (id : Nat) :
    (.pid id : Value).exactComparable = (true) := by rw [Value.exactComparable]

@[simp] theorem exactComparable_reference (id : Nat) :
    (.reference id : Value).exactComparable = (true) := by rw [Value.exactComparable]

@[simp] theorem exactComparable_function (moduleName name : String) (arity : Nat) :
    (.function moduleName name arity : Value).exactComparable = (false) := by rw [Value.exactComparable]

@[simp] theorem exactComparable_closure (moduleName : String) (code : Nat) (captured : List (VarId × Value))
    (group : List (VarId × Nat)) :
    (.closure moduleName code captured group : Value).exactComparable = (false) := by rw [Value.exactComparable]

@[simp] theorem exactComparable_exceptionInfo (kind : String) :
    (.exceptionInfo kind : Value).exactComparable = (false) := by rw [Value.exactComparable]

end Erlean.Core.Value
