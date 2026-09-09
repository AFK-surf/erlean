namespace Erlean.Core

abbrev VarId := Nat

/-- The sequential value profile includes finite closures and opaque exception
    information. Presence of a value constructor does not imply public transport. -/
inductive Value where
  | integer (value : Int)
  | atom (name : String)
  | nil
  | cons (head tail : Value)
  | tuple (elements : List Value)
  /-- Canonical bits shared by literals and supported binary operations. -/
  | bitstring (bits : List Bool)
  | pid (id : Nat)
  | reference (id : Nat)
  | function (moduleName name : String) (arity : Nat)
  /-- Finite lexical captures and a recursive code-group descriptor. -/
  | closure (moduleName : String) (code : Nat) (captured : List (VarId × Value))
      (group : List (VarId × Nat))
  /-- Opaque compiler exception information; never an observable Erlang term. -/
  | exceptionInfo (kind : String)
  deriving Repr

mutual
/-- Structural comparison for the restricted value profile, kept transparent
    to proof rewriting rather than using a nested deriving handler. -/
def Value.equal (left right : Value) : Bool :=
  match left, right with
  | .integer a, .integer b => a == b
  | .atom a, .atom b => a == b
  | .nil, .nil => true
  | .cons a b, .cons c d => a.equal c && b.equal d
  | .tuple xs, .tuple ys => Value.equalList xs ys
  | .bitstring xs, .bitstring ys => xs == ys
  | .pid a, .pid b => a == b
  | .reference a, .reference b => a == b
  | .function m f a, .function n g b => m == n && f == g && a == b
  | .closure m c env group, .closure n d other bindings =>
    m == n && c == d && group == bindings && Value.equalEnv env other
  | .exceptionInfo a, .exceptionInfo b => a == b
  | _, _ => false
termination_by sizeOf left

def Value.equalList (left right : List Value) : Bool :=
  match left, right with
  | [], [] => true
  | x :: xs, y :: ys => x.equal y && Value.equalList xs ys
  | _, _ => false
termination_by sizeOf left

def Value.equalEnv (left right : List (VarId × Value)) : Bool :=
  match left, right with
  | [], [] => true
  | (id, value) :: rest, (other, rhs) :: remaining =>
    id == other && value.equal rhs && Value.equalEnv rest remaining
  | _, _ => false
termination_by sizeOf left
end

instance : BEq Value := ⟨Value.equal⟩

mutual
/-- Public data excludes internal exception information. Closure environments
    remain opaque, since ordinary function values do not expose their captures. -/
def Value.isPublic (value : Value) : Bool :=
  match value with
  | .exceptionInfo _ => false
  | .cons head tail => head.isPublic && tail.isPublic
  | .tuple values => Value.publicList values
  | _ => true
termination_by sizeOf value

def Value.publicList (values : List Value) : Bool :=
  match values with
  | [] => true
  | value :: rest => value.isPublic && Value.publicList rest
termination_by sizeOf values
end

mutual
/-- Exact comparison is supported for data only; fun identity is unmodeled. -/
def Value.exactComparable (value : Value) : Bool :=
  match value with
  | .exceptionInfo _ | .function _ _ _ | .closure _ _ _ _ => false
  | .cons head tail => head.exactComparable && tail.exactComparable
  | .tuple values => Value.comparableList values
  | _ => true
termination_by sizeOf value

def Value.comparableList (values : List Value) : Bool :=
  match values with
  | [] => true
  | value :: rest => value.exactComparable && Value.comparableList rest
termination_by sizeOf values
end

/-- Core multiple returns are not Erlang tuple values. -/
abbrev Values := List Value

abbrev Env := List (VarId × Value)

namespace Env

def lookup (env : Env) (id : VarId) : Option Value :=
  match env with
  | [] => none
  | (key, value) :: rest => if key = id then some value else lookup rest id

@[simp] theorem lookup_nil (id : VarId) : lookup [] id = none := rfl

@[simp] theorem lookup_cons_self (env : Env) (id : VarId) (value : Value) :
    lookup ((id, value) :: env) id = some value := by
  simp [lookup]

theorem lookup_cons_other (env : Env) (id key : VarId) (value : Value)
    (h : key ≠ id) : lookup ((key, value) :: env) id = lookup env id := by
  simp [lookup, h]

end Env

inductive Pattern where
  | wild
  | var (id : VarId)
  | alias (id : VarId) (pattern : Pattern)
  | lit (value : Value)
  | cons (head tail : Pattern)
  | tuple (elements : List Pattern)
  /-- Exact sequence of unsigned eight-bit integer segment patterns. -/
  | bytes (elements : List Pattern)
  deriving Repr, BEq

/-- Name-resolved syntax for the initial sequential implementation slice.
    Presence of a constructor does not assert execution support. -/
inductive Expr where
  | lit (value : Value)
  | var (id : VarId)
  | values (elements : List Expr)
  | letE (binders : List VarId) (argument body : Expr)
  | seq (first second : Expr)
  | cons (head tail : Expr)
  | tuple (elements : List Expr)
  /-- Ordered unsigned eight-bit integer segment construction. -/
  | bytes (elements : List Expr)
  | call (moduleName functionName : Expr) (arguments : List Expr)
  | apply (function : Expr) (arguments : List Expr)
  | primop (name : String) (arguments : List Expr)
  | funRef (name : String) (arity : Nat)
  | makeClosure (code : Nat)
  | letrec (bindings : List (VarId × Nat)) (body : Expr)
  | tryE (argument : Expr) (binders : List VarId) (body : Expr)
      (exceptionBinders : List VarId) (handler : Expr)
  | catchE (body : Expr)
  | caseE (argument : Expr) (clauses : List (List Pattern × Expr × Expr))
  deriving Repr, BEq

/-- Clause components are the patterns, guard, and body, respectively. -/
abbrev Clause := List Pattern × Expr × Expr

structure FunctionDef where
  name : String
  params : List VarId
  body : Expr
  deriving Repr, BEq

structure ClosureDef where
  params : List VarId
  body : Expr
  outerScope : List VarId
  recursiveBindings : List (VarId × Nat) := []
  deriving Repr, BEq

structure Module where
  name : String
  exports : List (String × Nat)
  functions : List FunctionDef
  closureCode : List ClosureDef := []
  deriving Repr, BEq

abbrev CodeWorld := List Module

end Erlean.Core
