import Erlean.Core.Syntax
import Erlean.Core.Match
import Erlean.Semantics.Execution

namespace Erlean.Semantics

open Core

inductive ExceptionClass where
  | error | exit | throw
  deriving Repr, BEq, DecidableEq

/-- The initial profile reports exception class and reason, without stack inspection. -/
structure Exception where
  kind : ExceptionClass
  reason : Value
  deriving Repr, BEq

inductive Fault where
  | invalid (message : String)
  | unsupported (operation : String)
  deriving Repr, BEq, DecidableEq

inductive Outcome where
  | returned (values : Values)
  | raised (exception : Exception)
  | fault (fault : Fault)
  deriving Repr, BEq

structure Context where
  moduleName : String
  env : Env
  deriving Repr, BEq

inductive Collect where
  | values | tuple | cons | call | apply
  | primop (name : String)
  deriving Repr, BEq

inductive Frame where
  | collect (action : Collect) (context : Context) (done : Values) (rest : List Expr)
  | bind (context : Context) (binders : List VarId) (body : Expr)
  | seq (context : Context) (body : Expr)
  | select (context : Context) (clauses : List Clause)
  | guard (context : Context) (matched : Env) (values : Values)
      (body : Expr) (rest : List Clause)
  deriving Repr, BEq

inductive Control where
  | eval (expression : Expr)
  | ret (values : Values)
  | raise (exception : Exception)
  | select (values : Values) (clauses : List Clause)
  deriving Repr, BEq

structure LocalState where
  control : Control
  context : Context
  stack : List Frame := []
  deriving Repr, BEq

def nextControl (state : LocalState) (control : Control) :
    Transition LocalState Outcome := .next { state with control }

def invalid (message : String) : Transition LocalState Outcome :=
  .halt (.fault (.invalid message))

def unsupported (operation : String) : Transition LocalState Outcome :=
  .halt (.fault (.unsupported operation))

def raiseError (state : LocalState) (reason : Value) :
    Transition LocalState Outcome := nextControl state (.raise ⟨.error, reason⟩)

def boolean (value : Bool) : Value := .atom (if value then "true" else "false")

/-- Explicit, intentionally small BIF profile. Other BIFs are model faults. -/
def builtin (state : LocalState) (name : String) (args : Values) :
    Transition LocalState Outcome :=
  let ret (value : Value) := nextControl state (.ret [value])
  let badarg := raiseError state (.atom "badarg")
  let badarith := raiseError state (.atom "badarith")
  match name, args with
  | "+", [.integer a, .integer b] => ret (.integer (a + b))
  | "-", [.integer a, .integer b] => ret (.integer (a - b))
  | "*", [.integer a, .integer b] => ret (.integer (a * b))
  | "+", [_, _] | "-", [_, _] | "*", [_, _] => badarith
  | "is_integer", [v] => ret (boolean (match v with | .integer _ => true | _ => false))
  | "is_atom", [v] => ret (boolean (match v with | .atom _ => true | _ => false))
  | "is_tuple", [v] => ret (boolean (match v with | .tuple _ => true | _ => false))
  | "hd", [.cons h _] => ret h
  | "tl", [.cons _ t] => ret t
  | "hd", [_] | "tl", [_] => badarg
  | "error", [reason] => nextControl state (.raise ⟨.error, reason⟩)
  | "exit", [reason] => nextControl state (.raise ⟨.exit, reason⟩)
  | "throw", [reason] => nextControl state (.raise ⟨.throw, reason⟩)
  | _, _ => unsupported s!"BIF erlang:{name}/{args.length}"

def lookupFunction (world : CodeWorld) (moduleName name : String) (arity : Nat) :
    Option FunctionDef := do
  let mod ← world.find? (fun m => m.name == moduleName)
  mod.functions.find? (fun f => f.name == name && f.params.length == arity)

def invoke (world : CodeWorld) (state : LocalState) (moduleName name : String)
    (args : Values) (external : Bool) : Transition LocalState Outcome :=
  if moduleName == "erlang" then builtin state name args
  else
    match world.find? (fun m => m.name == moduleName) with
    | none => unsupported s!"unlinked module {moduleName}"
    | some mod =>
      if external && !(mod.exports.contains (name, args.length)) then
        raiseError state (.atom "undef")
      else
        match lookupFunction world moduleName name args.length with
        | none => raiseError state (.atom "undef")
        | some function =>
          .next { state with
            control := .eval function.body
            context := ⟨moduleName, function.params.zip args⟩ }

def makeClosureValue (world : CodeWorld) (context : Context) (index : Nat) : Except Fault Value := do
  let some mod := world.find? (fun m => m.name == context.moduleName)
    | throw (.invalid "Closure module is not linked")
  let some defn := mod.closureCode[index]? | throw (.invalid "Closure code index is invalid")
  let captured ← defn.outerScope.mapM fun id => do
    let some value := context.env.lookup id | throw (.invalid "Closure capture is unbound")
    pure (id, value)
  return .closure context.moduleName index captured defn.recursiveBindings

/-- Rebuild recursive bindings from finite descriptors, without cyclic values. -/
def recursiveEnv (moduleName : String) (captured : Env) (group : List (VarId × Nat)) : Env :=
  group.map fun (id, index) => (id, .closure moduleName index captured group)

def applyClosure (world : CodeWorld) (state : LocalState) (moduleName : String)
    (index : Nat) (captured : Env) (group : List (VarId × Nat)) (args : Values) :
    Transition LocalState Outcome :=
  match world.find? (fun m => m.name == moduleName) with
  | none => unsupported s!"unlinked closure module {moduleName}"
  | some mod =>
    match mod.closureCode[index]? with
    | none => invalid "Closure code index is invalid"
    | some defn =>
      if defn.recursiveBindings != group || captured.map Prod.fst != defn.outerScope then
        invalid "Closure descriptor does not match its code"
      else if defn.params.length != args.length then
        raiseError state (.tuple [.atom "badarity", .tuple [
          .closure moduleName index captured group, args.foldr Value.cons .nil]])
      else .next { state with
        control := .eval defn.body
        context := ⟨moduleName, defn.params.zip args ++ recursiveEnv moduleName captured group ++ captured⟩ }

def finishCollect (world : CodeWorld) (state : LocalState) (action : Collect)
    (values : Values) : Transition LocalState Outcome :=
  match action, values with
  | .values, _ => nextControl state (.ret values)
  | .tuple, _ => nextControl state (.ret [.tuple values])
  | .cons, [head, tail] => nextControl state (.ret [.cons head tail])
  | .call, .atom mod :: .atom name :: args => invoke world state mod name args true
  | .call, _ => raiseError state (.atom "badarg")
  | .apply, .function mod name arity :: args =>
    if arity == args.length then invoke world state mod name args false
    else raiseError state (.tuple [.atom "badarity", .tuple [.function mod name arity,
      args.foldr Value.cons .nil]])
  | .apply, .closure mod index captured group :: args => applyClosure world state mod index captured group args
  | .apply, value :: _ => raiseError state (.tuple [.atom "badfun", value])
  | .primop "match_fail", [.tuple (.atom "function_clause" :: _)] =>
    raiseError state (.atom "function_clause")
  | .primop "match_fail", [reason] => raiseError state reason
  | .primop name, _ => unsupported s!"primop {name}/{values.length}"
  | _, _ => invalid "Malformed constructor or application arity"

def startCollect (world : CodeWorld) (state : LocalState) (action : Collect)
    (expressions : List Expr) : Transition LocalState Outcome :=
  match expressions with
  | [] => finishCollect world state action []
  | first :: rest => .next { state with
      control := .eval first
      stack := .collect action state.context [] rest :: state.stack }

/-- One total machine transition. Recursion in Core consumes machine steps. -/
def stepLocal (world : CodeWorld) (state : LocalState) : Transition LocalState Outcome :=
  match state.control with
  | .eval expression =>
    match expression with
    | .lit value => nextControl state (.ret [value])
    | .var id =>
      match state.context.env.lookup id with
      | some value => nextControl state (.ret [value])
      | none => invalid s!"Unbound variable {id}"
    | .funRef name arity =>
      nextControl state (.ret [.function state.context.moduleName name arity])
    | .makeClosure index =>
      match makeClosureValue world state.context index with
      | .ok value => nextControl state (.ret [value])
      | .error fault => .halt (.fault fault)
    | .letrec bindings body =>
      match bindings.mapM (fun (id, index) =>
        (makeClosureValue world state.context index).map (id, ·)) with
      | .error fault => .halt (.fault fault)
      | .ok env => .next { state with
          control := .eval body
          context := { state.context with env := env ++ state.context.env } }
    | .values elements => startCollect world state .values elements
    | .tuple elements => startCollect world state .tuple elements
    | .cons head tail => startCollect world state .cons [head, tail]
    | .call mod name args => startCollect world state .call (mod :: name :: args)
    | .apply function args => startCollect world state .apply (function :: args)
    | .primop name args => startCollect world state (.primop name) args
    | .letE binders argument body => .next { state with
        control := .eval argument
        stack := .bind state.context binders body :: state.stack }
    | .seq first second => .next { state with
        control := .eval first
        stack := .seq state.context second :: state.stack }
    | .caseE argument clauses => .next { state with
        control := .eval argument
        stack := .select state.context clauses :: state.stack }
  | .ret values =>
    match state.stack with
    | [] => .halt (.returned values)
    | frame :: stack =>
      match frame with
      | .collect action context done rest =>
        match values with
        | [value] =>
          match rest with
          | [] => finishCollect world { state with context, stack } action (done ++ [value])
          | first :: rest => .next {
              control := .eval first
              context := context
              stack := .collect action context (done ++ [value]) rest :: stack }
        | _ => invalid "Expected a single value in an operand position"
      | .bind context binders body =>
        if binders.length == values.length then
          .next {
            control := .eval body
            context := { context with env := binders.zip values ++ context.env }
            stack := stack }
        else invalid "Core let binding arity mismatch"
      | .seq context body => .next { control := .eval body, context, stack }
      | .select context clauses => .next { control := .select values clauses, context, stack }
      | .guard context matched scrutinee body rest =>
        if values == [.atom "true"] then
          .next {
            control := .eval body
            context := { context with env := matched ++ context.env }
            stack := stack }
        else .next { control := .select scrutinee rest, context, stack }
  | .select values clauses =>
    match clauses with
    | [] => invalid "Core case exhausted without a compiler-generated failure clause"
    | (patterns, guard, body) :: rest =>
      match Core.matchPatterns patterns values with
      | none => nextControl state (.select values rest)
      | some matched => .next {
          control := .eval guard
          context := { state.context with env := matched ++ state.context.env }
          stack := .guard state.context matched values body rest :: state.stack }
  | .raise exception =>
    match state.stack with
    | [] => .halt (.raised exception)
    | .guard context _ values _ rest :: stack =>
      if exception.kind == .error then
        .next { control := .select values rest, context, stack }
      else .next { state with stack }
    | _ :: stack => .next { state with stack }

def runLocal (fuel : Nat) (world : CodeWorld) (state : LocalState) :
    RunResult LocalState Outcome := run (stepLocal world) fuel state

def initialCall (moduleName functionName : String) (arguments : Values) : LocalState :=
  { control := .eval (.call (.lit (.atom moduleName)) (.lit (.atom functionName))
      (arguments.map Expr.lit))
    context := ⟨moduleName, []⟩ }

end Erlean.Semantics
