namespace Erlean.Core

abbrev VarId := Nat

/-- The initial value profile, including static module function references.
    Other Erlang terms and captured closures remain unsupported. -/
inductive Value where
  | integer (value : Int)
  | atom (name : String)
  | nil
  | cons (head tail : Value)
  | tuple (elements : List Value)
  | function (moduleName name : String) (arity : Nat)
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
  | .function m f a, .function n g b => m == n && f == g && a == b
  | _, _ => false
termination_by sizeOf left

def Value.equalList (left right : List Value) : Bool :=
  match left, right with
  | [], [] => true
  | x :: xs, y :: ys => x.equal y && Value.equalList xs ys
  | _, _ => false
termination_by sizeOf left
end

instance : BEq Value := ⟨Value.equal⟩

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
  | lit (value : Value)
  | cons (head tail : Pattern)
  | tuple (elements : List Pattern)
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
  | call (moduleName functionName : Expr) (arguments : List Expr)
  | apply (function : Expr) (arguments : List Expr)
  | primop (name : String) (arguments : List Expr)
  | funRef (name : String) (arity : Nat)
  | caseE (argument : Expr) (clauses : List (List Pattern × Expr × Expr))
  deriving Repr, BEq

/-- Clause components are the patterns, guard, and body, respectively. -/
abbrev Clause := List Pattern × Expr × Expr

structure FunctionDef where
  name : String
  params : List VarId
  body : Expr
  deriving Repr, BEq

structure Module where
  name : String
  exports : List (String × Nat)
  functions : List FunctionDef
  deriving Repr, BEq

abbrev CodeWorld := List Module

end Erlean.Core
