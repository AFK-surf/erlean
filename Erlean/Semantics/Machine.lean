import Erlean.Core.Syntax
import Erlean.Core.FiniteMap
import Erlean.Core.Match
import Erlean.Core.PatternObservation
import Erlean.Semantics.Execution

namespace Erlean.Semantics

open Core

inductive ExceptionClass where
  | error | exit | throw
  deriving Repr, BEq, DecidableEq

def ExceptionClass.name : ExceptionClass → String
  | .error => "error"
  | .exit => "exit"
  | .throw => "throw"

def ExceptionClass.ofName : String → Option ExceptionClass
  | "error" => some .error
  | "exit" => some .exit
  | "throw" => some .throw
  | _ => none

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
  | values | tuple | bytes | cons | call | apply
  | primop (name : String)
  | map (exact : List Bool)
  deriving Repr, BEq

inductive Frame where
  | collect (action : Collect) (context : Context) (done : Values) (rest : List Expr)
  | bind (context : Context) (binders : List VarId) (body : Expr)
  | seq (context : Context) (body : Expr)
  | select (context : Context) (clauses : List Clause)
  | guard (context : Context) (matched : Env) (values : Values)
      (body : Expr) (rest : List Clause)
  | tryFrame (context : Context) (binders : List VarId) (body : Expr)
      (exceptionBinders : List VarId) (handler : Expr)
  | catchFrame (context : Context)
  deriving Repr, BEq

inductive Control where
  | eval (expression : Expr)
  | ret (values : Values)
  | raise (exception : Exception)
  | select (values : Values) (clauses : List Clause)
  /-- Runtime suspension consumed by the actor driver, never by the local runner. -/
  | runtime (name : String) (arguments : Values)
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

/-- Apply already evaluated pairs in the selected Core pair order. The collector
    evaluates every operand first; finishMap separately excludes ambiguous OTP
    failure ordering before this helper runs. -/
def updateMapEntries (state : LocalState) : List Bool → Values →
    FiniteMap.Entries Value → Transition LocalState Outcome
  | [], [], entries => nextControl state (.ret [.map entries])
  | exact :: rest, key :: value :: operands, entries =>
    match key.toMapKey with
    | none => unsupported "Map key outside the finite key profile"
    | some mapKey =>
      if !value.isPublic then unsupported "Opaque or malformed map value"
      else if exact && (FiniteMap.lookup mapKey entries).isNone then
        raiseError state (.tuple [.atom "badkey", key])
      else updateMapEntries state rest operands (FiniteMap.insert mapKey value entries)
  | _, _, _ => invalid "Malformed Core map operand arity"

/-- Count distinct exact keys missing at their first write, using a shadow map
    that inserts even failing updates. OTP may reorder literal-key groups; more
    than one missing key would make the observable badkey reason ambiguous.
    Unsupported keys and malformed arities remain the execution helper's faults. -/
def missingExactKeys : List Bool → Values → FiniteMap.Entries Value → Nat
  | exact :: rest, key :: value :: operands, entries =>
    match key.toMapKey with
    | none => missingExactKeys rest operands entries
    | some mapKey =>
      (if exact && (FiniteMap.lookup mapKey entries).isNone then 1 else 0) +
        missingExactKeys rest operands (FiniteMap.insert mapKey value entries)
  | _, _, _ => 0

def finishMap (state : LocalState) (exact : List Bool) (operands : Values) :
    Transition LocalState Outcome :=
  match operands with
  | .map entries :: pairs =>
    if !Value.mapOrdered entries then invalid "Noncanonical finite map"
    else if !Value.publicEntries entries then unsupported "Opaque or malformed map value"
    else if missingExactKeys exact pairs entries > 1 then
      unsupported "Ambiguous exact-map update failure"
    else updateMapEntries state exact pairs entries
  | base :: _ =>
    if !base.isPublic then unsupported "Opaque or malformed map base"
    else raiseError state (.tuple [.atom "badmap", base])
  | [] => invalid "Core map requires a base operand"

/-- Shared checked map operand boundary. These are model faults, not invented
    Erlang exceptions, when an input lies outside the implemented profile. -/
def withMap (state : LocalState) (value : Value)
    (body : FiniteMap.Entries Value → Transition LocalState Outcome) :
    Transition LocalState Outcome :=
  match value with
  | .map entries =>
    if !Value.mapOrdered entries then invalid "Noncanonical finite map"
    else if !Value.publicEntries entries then unsupported "Opaque or malformed map value"
    else body entries
  | _ =>
    if !value.isPublic then unsupported "Opaque or malformed map operand"
    else raiseError state (.tuple [.atom "badmap", value])

def withMapKey (key : Value) (body : MapKey → Transition LocalState Outcome) :
    Transition LocalState Outcome :=
  match key.toMapKey with
  | some mapKey => body mapKey
  | none => unsupported "Map key outside the finite key profile"

/-- The finite maps module profile. Values may contain functions; only keys are
    restricted by conversion to MapKey. The right map wins during merge. -/
def mapBuiltin (state : LocalState) (name : String) (args : Values) :
    Transition LocalState Outcome :=
  let ret (value : Value) := nextControl state (.ret [value])
  if !Value.publicList args then unsupported "Opaque or malformed maps argument"
  else match name, args with
  | "get", [key, map] => withMap state map fun entries => withMapKey key fun mapKey =>
    match FiniteMap.lookup mapKey entries with
    | some value => ret value
    | none => raiseError state (.tuple [.atom "badkey", key])
  | "get", [key, map, default] => withMap state map fun entries => withMapKey key fun mapKey =>
    ret ((FiniteMap.lookup mapKey entries).getD default)
  | "find", [key, map] => withMap state map fun entries => withMapKey key fun mapKey =>
    match FiniteMap.lookup mapKey entries with
    | some value => ret (.tuple [.atom "ok", value])
    | none => ret (.atom "error")
  | "is_key", [key, map] => withMap state map fun entries => withMapKey key fun mapKey =>
    ret (boolean (FiniteMap.lookup mapKey entries).isSome)
  | "put", [key, value, map] => withMap state map fun entries => withMapKey key fun mapKey =>
    ret (.map (FiniteMap.insert mapKey value entries))
  | "update", [key, value, map] => withMap state map fun entries => withMapKey key fun mapKey =>
    if (FiniteMap.lookup mapKey entries).isSome then
      ret (.map (FiniteMap.insert mapKey value entries))
    else raiseError state (.tuple [.atom "badkey", key])
  | "remove", [key, map] => withMap state map fun entries => withMapKey key fun mapKey =>
    ret (.map (FiniteMap.erase mapKey entries))
  | "take", [key, map] => withMap state map fun entries => withMapKey key fun mapKey =>
    match FiniteMap.lookup mapKey entries with
    | some value => ret (.tuple [value, .map (FiniteMap.erase mapKey entries)])
    | none => ret (.atom "error")
  | "merge", [left, right] => withMap state left fun leftEntries =>
    withMap state right fun rightEntries =>
      ret (.map (rightEntries.foldl (fun entries pair =>
        FiniteMap.insert pair.1 pair.2 entries) leftEntries))
  | _, _ => unsupported s!"BIF maps:{name}/{args.length}"

/-- Explicit, intentionally small BIF profile. Other BIFs are model faults. -/
def builtin (state : LocalState) (name : String) (args : Values) :
    Transition LocalState Outcome :=
  let ret (value : Value) := nextControl state (.ret [value])
  let badarg := raiseError state (.atom "badarg")
  let badarith := raiseError state (.atom "badarith")
  let unknown := unsupported s!"BIF erlang:{name}/{args.length}"
  if !Value.publicList args then unsupported "BIF observation of opaque exception information"
  else match name with
  | "self" | "make_ref" => match args with
    | [] => nextControl state (.runtime name args)
    | _ => unknown
  | "spawn" => match args with
    | [_, _, _] => nextControl state (.runtime name args)
    | _ => unknown
  | "send" | "monitor" => match args with
    | [_, _] => nextControl state (.runtime name args)
    | _ => unknown
  | "demonitor" | "link" | "unlink" => match args with
    | [_] => nextControl state (.runtime name args)
    | _ => unknown
  | "!" => match args with
    | [_, _] => nextControl state (.runtime "send" args)
    | _ => unknown
  | "+" => match args with
    | [.integer a, .integer b] => ret (.integer (a + b))
    | [_, _] => badarith
    | _ => unknown
  | "-" => match args with
    | [.integer a, .integer b] => ret (.integer (a - b))
    | [_, _] => badarith
    | _ => unknown
  | "*" => match args with
    | [.integer a, .integer b] => ret (.integer (a * b))
    | [_, _] => badarith
    | _ => unknown
  | "=<" => match args with
    | [.integer a, .integer b] => ret (boolean (decide (a ≤ b)))
    | _ => unknown
  | "=:=" | "==" => match args with
    | [a, b] =>
      if a.exactComparable && b.exactComparable then ret (boolean (a == b))
      else unsupported "Exact equality involving function identity or exception information"
    | _ => unknown
  | "=/=" | "/=" => match args with
    | [a, b] =>
      if a.exactComparable && b.exactComparable then ret (boolean (!(a == b)))
      else unsupported "Equality involving function identity or exception information"
    | _ => unknown
  | "and" => match args with
    | [.atom a, .atom b] =>
      if (a == "true" || a == "false") && (b == "true" || b == "false") then
        ret (boolean (a == "true" && b == "true"))
      else badarg
    | [_, _] => badarg
    | _ => unknown
  | "is_integer" => match args with
    | [v] => ret (boolean (match v with | .integer _ => true | _ => false))
    | _ => unknown
  | "is_atom" => match args with
    | [v] => ret (boolean (match v with | .atom _ => true | _ => false))
    | _ => unknown
  | "is_tuple" => match args with
    | [v] => ret (boolean (match v with | .tuple _ => true | _ => false))
    | _ => unknown
  | "is_map" => match args with
    | [v] => ret (boolean (match v with | .map _ => true | _ => false))
    | _ => unknown
  | "is_binary" => match args with
    | [v] => ret (boolean (match v with
        | .bitstring bits => bits.length % 8 == 0 | _ => false))
    | _ => unknown
  | "map_size" => match args with
    | [v] => withMap state v fun entries => ret (.integer (Int.ofNat entries.length))
    | _ => unknown
  | "map_get" => match args with
    | [key, map] => mapBuiltin state "get" [key, map]
    | _ => unknown
  | "is_map_key" => match args with
    | [key, map] => mapBuiltin state "is_key" [key, map]
    | _ => unknown
  | "hd" => match args with
    | [.cons head _] => ret head
    | [_] => badarg
    | _ => unknown
  | "tl" => match args with
    | [.cons _ tail] => ret tail
    | [_] => badarg
    | _ => unknown
  | "error" => match args with
    | [reason] => nextControl state (.raise ⟨.error, reason⟩)
    | _ => unknown
  | "exit" => match args with
    | [reason] => nextControl state (.raise ⟨.exit, reason⟩)
    | [_, _] => nextControl state (.runtime name args)
    | _ => unknown
  | "throw" => match args with
    | [reason] => nextControl state (.raise ⟨.throw, reason⟩)
    | _ => unknown
  | _ => unknown

def lookupFunction (world : CodeWorld) (moduleName name : String) (arity : Nat) :
    Option FunctionDef := do
  let mod ← world.find? (fun m => m.name == moduleName)
  mod.functions.find? (fun f => f.name == name && f.params.length == arity)

def invoke (world : CodeWorld) (state : LocalState) (moduleName name : String)
    (args : Values) (external : Bool) : Transition LocalState Outcome :=
  if moduleName == "erlang" then builtin state name args
  else if moduleName == "maps" then mapBuiltin state name args
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
  | .map exact, _ => finishMap state exact values
  | .bytes, _ =>
    match encodeByteValues values with
    | some bits => nextControl state (.ret [.bitstring bits])
    | none => raiseError state (.atom "badarg")
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
  | .primop "raise", [.exceptionInfo kind, reason] =>
    match ExceptionClass.ofName kind with
    | some cls => nextControl state (.raise ⟨cls, reason⟩)
    | none => invalid "Unknown class in opaque exception information"
  | .primop "raise", _ => invalid "Core raise requires opaque exception information and reason"
  | .primop "recv_peek_message", [] => nextControl state (.runtime "recv_peek_message" [])
  | .primop "recv_next", [] => nextControl state (.runtime "recv_next" [])
  | .primop "remove_message", [] => nextControl state (.runtime "remove_message" [])
  | .primop "recv_wait_timeout", [timeout] => nextControl state (.runtime "recv_wait_timeout" [timeout])
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
  | .runtime name args => unsupported s!"Actor runtime required: {name}/{args.length}"
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
    | .map exact operands => startCollect world state (.map exact) operands
    | .bytes elements => startCollect world state .bytes elements
    | .cons head tail => startCollect world state .cons [head, tail]
    | .call mod name args => startCollect world state .call (mod :: name :: args)
    | .apply function args => startCollect world state .apply (function :: args)
    | .primop name args => startCollect world state (.primop name) args
    | .letE binders argument body => .next { state with
        control := .eval argument
        stack := .bind state.context binders body :: state.stack }
    | .tryE argument binders body exceptionBinders handler =>
      if exceptionBinders.length == 2 || exceptionBinders.length == 3 then
        .next { state with
          control := .eval argument
          stack := .tryFrame state.context binders body exceptionBinders handler :: state.stack }
      else invalid "Core try exception binding arity mismatch"
    | .catchE body => .next { state with
        control := .eval body
        stack := .catchFrame state.context :: state.stack }
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
      | .tryFrame context binders body _ _ =>
        if binders.length == values.length then
          .next {
            control := .eval body
            context := { context with env := binders.zip values ++ context.env }
            stack := stack }
        else invalid "Core try normal binding arity mismatch"
      | .catchFrame context =>
        if values.length == 1 then .next { control := .ret values, context, stack }
        else invalid "Core catch requires a single result"
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
      if !Core.patternsObservationAllowed patterns values then
        unsupported "Pattern observation of opaque exception information"
      else match Core.matchPatterns patterns values with
      | none => nextControl state (.select values rest)
      | some matched => .next {
          control := .eval guard
          context := { state.context with env := matched ++ state.context.env }
          stack := .guard state.context matched values body rest :: state.stack }
  | .raise exception =>
    match state.stack with
    | [] => .halt (.raised exception)
    | .tryFrame context _ _ binders handler :: stack =>
      let values := if binders.length == 2 then
          [.atom exception.kind.name, exception.reason]
        else [.atom exception.kind.name, exception.reason, .exceptionInfo exception.kind.name]
      if binders.length == 2 || binders.length == 3 then
        .next {
          control := .eval handler
          context := { context with env := binders.zip values ++ context.env }
          stack := stack }
      else invalid "Core try exception binding arity mismatch"
    | .catchFrame context :: stack =>
      match exception.kind with
      | .throw => .next { control := .ret [exception.reason], context, stack }
      | .exit => .next { control := .ret [.tuple [.atom "EXIT", exception.reason]], context, stack }
      | .error => unsupported "Old catch of error requires observable stacktrace semantics"
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
