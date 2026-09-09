import Erlean.Import.RawCore
import Erlean.Core.Scope

namespace Erlean.Import

open Core

private def properList : Term → Except String (List Term)
  | .nil => .ok []
  | .list xs .nil => .ok xs
  | _ => .error "Expected a proper list in a Core record"

private def atom : Term → Except String String
  | .atom s => .ok s
  | _ => .error "Expected an atom"

private def literal : Term → Except String Term
  | .tuple [.atom "c_literal", _, value] => .ok value
  | _ => .error "Expected a c_literal record"

private def variableName : Term → Except String Term
  | .tuple [.atom "c_var", _, name] => .ok name
  | _ => .error "Expected a c_var record"

private def signature : Term → Except String (String × Nat)
  | .tuple [.atom name, .integer (.ofNat arity)] => .ok (name, arity)
  | _ => .error "Expected a function name/arity pair"

/-- Decode canonical bitstring literals without discarding nonzero padding. -/
def lowerBitstring (count : Nat) (hex : String) : Except String Value := do
  unless hex.length == 2 * ((count + 7) / 8) do
    throw "Bitstring byte encoding does not match its length"
  let nibbles ← hex.toList.mapM fun c => do
    if '0' ≤ c && c ≤ '9' then pure (c.toNat - '0'.toNat)
    else if 'a' ≤ c && c ≤ 'f' then pure (c.toNat - 'a'.toNat + 10)
    else if 'A' ≤ c && c ≤ 'F' then pure (c.toNat - 'A'.toNat + 10)
    else throw "Invalid hexadecimal digit in bitstring literal"
  let bits := nibbles.flatMap fun n =>
    [n / 8 % 2 == 1, n / 4 % 2 == 1, n / 2 % 2 == 1, n % 2 == 1]
  unless (bits.drop count).all (· == false) do
    throw "Bitstring literal has nonzero unused padding bits"
  return .bitstring (bits.take count)

def lowerValue : Nat → Term → Except String Value
  | 0, _ => .error "Literal nesting exceeds the import depth limit"
  | fuel + 1, term => do
    match term with
    | .atom name => return .atom name
    | .integer n => return .integer n
    | .nil => return .nil
    | .tuple items => return .tuple (← items.mapM (lowerValue fuel))
    | .list items tail =>
      let items ← items.mapM (lowerValue fuel)
      return items.foldr Value.cons (← lowerValue fuel tail)
    | .float _ => throw "Unsupported literal: float"
    | .bitstring bits hex => lowerBitstring bits hex
    | .map _ => throw "Unsupported literal: map"

abbrev NameScope := List (Term × VarId)

private def lookup (scope : NameScope) (name : Term) : Except String VarId :=
  match scope.find? (fun entry => entry.1 == name) with
  | some (_, id) => .ok id
  | none => .error s!"Unbound Core variable: {repr name}"

private def bind (scope : NameScope) (names : List Term) : Except String (List VarId × NameScope) := do
  unless (names.eraseDups.length == names.length) do throw "Duplicate Core binder"
  let ids := (List.range names.length).map (· + scope.length)
  return (ids, names.zip ids ++ scope)

private def tagOf : Term → String
  | .tuple (.atom tag :: _) => tag
  | _ => "malformed record"

/-- This profile accepts only statically specified unsigned integer bytes. -/
private def byteSegmentValue : Term → Except String Term
  | .tuple [.atom "c_bitstr", _, value, size, unit, type, flags] => do
    unless (← literal size) == .integer 8 do
      throw "Unsupported binary segment size: expected literal 8"
    unless (← literal unit) == .integer 1 do
      throw "Unsupported binary segment unit: expected literal 1"
    unless (← literal type) == .atom "integer" do
      throw "Unsupported binary segment type: expected integer"
    unless (← properList (← literal flags)) == [.atom "unsigned", .atom "big"] do
      throw "Unsupported binary segment flags: expected [unsigned,big]"
    return value
  | _ => .error "Malformed binary segment: expected a c_bitstr record"

private def bytePatternSegmentValue (segment : Term) : Except String Term := do
  let value ← byteSegmentValue segment
  match value with
  | .tuple [.atom "c_var", _, _]
  | .tuple [.atom "c_literal", _, .integer _] => return value
  | _ => throw "Unsupported byte pattern: expected a variable or integer literal"

private def patternNames : Nat → Term → Except String (List Term)
  | 0, _ => .error "Pattern nesting exceeds the import depth limit"
  | fuel + 1, term => do
    match term with
    | .tuple [.atom "c_var", _, name] => return [name]
    | .tuple [.atom "c_alias", _, binder, pattern] =>
      return (← variableName binder) :: (← patternNames fuel pattern)
    | .tuple [.atom "c_literal", _, _] => return []
    | .tuple [.atom "c_cons", _, head, tail] =>
      return (← patternNames fuel head) ++ (← patternNames fuel tail)
    | .tuple [.atom "c_tuple", _, items] =>
      return (← (← properList items).mapM (patternNames fuel)).flatten
    | .tuple [.atom "c_binary", _, segments] =>
      let values ← (← properList segments).mapM bytePatternSegmentValue
      return (← values.mapM (patternNames fuel)).flatten
    | _ => throw s!"Unsupported or malformed Core pattern: {tagOf term}"

private def lowerPattern : Nat → NameScope → Term → Except String Pattern
  | 0, _, _ => .error "Pattern nesting exceeds the import depth limit"
  | fuel + 1, scope, term => do
    match term with
    | .tuple [.atom "c_var", _, name] => return .var (← lookup scope name)
    | .tuple [.atom "c_alias", _, binder, pattern] =>
      return .alias (← lookup scope (← variableName binder)) (← lowerPattern fuel scope pattern)
    | .tuple [.atom "c_literal", _, value] => return .lit (← lowerValue fuel value)
    | .tuple [.atom "c_cons", _, head, tail] =>
      return .cons (← lowerPattern fuel scope head) (← lowerPattern fuel scope tail)
    | .tuple [.atom "c_tuple", _, items] =>
      return .tuple (← (← properList items).mapM (lowerPattern fuel scope))
    | .tuple [.atom "c_binary", _, segments] =>
      let values ← (← properList segments).mapM bytePatternSegmentValue
      return .bytes (← values.mapM (lowerPattern fuel scope))
    | _ => throw s!"Unsupported or malformed Core pattern: {tagOf term}"

private abbrev ClosureTable := List (Option ClosureDef)
private abbrev LowerM := StateT ClosureTable (Except String)

private def reserveClosure : LowerM Nat := do
  let table ← get
  set (table ++ [none])
  return table.length

private def fillClosure (code : Nat) (definition : ClosureDef) : LowerM Unit := do
  let table ← get
  match table[code]? with
  | some none => set (table.set code (some definition))
  | _ => throw "Invalid or already filled closure code slot"

/-- Extract closure code while resolving lexical binders. Recursive groups reserve
    every code slot before any member body is lowered. -/
private def lowerExprM : Nat → NameScope → Term → LowerM Expr
  | 0, _, _ => throw "Expression nesting exceeds the import depth limit"
  | fuel + 1, scope, term => do
    match term with
    | .tuple [.atom "c_literal", _, value] => return .lit (← lowerValue fuel value)
    | .tuple [.atom "c_var", _, name] =>
      match scope.find? (fun entry => entry.1 == name) with
      | some (_, id) => return .var id
      | none =>
        match name with
        | .tuple [.atom fn, .integer (.ofNat arity)] => return .funRef fn arity
        | _ => return .var (← lookup scope name)
    | .tuple [.atom "c_fun", _, params, body] =>
      let names ← (← properList params).mapM (fun x => do pure (← variableName x))
      let (ids, inner) ← bind scope names
      let code ← reserveClosure
      let body ← lowerExprM fuel inner body
      fillClosure code { params := ids, body, outerScope := scope.map Prod.snd }
      return .makeClosure code
    | .tuple [.atom "c_letrec", _, definitions, body] =>
      let definitions ← properList definitions
      let definitions ← definitions.mapM fun definition => do
        let .tuple [key, value] := definition | throw "Malformed letrec definition"
        let name ← variableName key
        let (_, arity) ← signature name
        let .tuple [.atom "c_fun", _, params, fnBody] := value
          | throw "Expected a c_fun in letrec"
        let params ← (← properList params).mapM (fun x => do pure (← variableName x))
        unless params.length == arity do throw "Letrec function arity mismatch"
        pure (name, params, fnBody)
      let (ids, groupScope) ← bind scope (definitions.map (·.1))
      let codes ← definitions.mapM fun _ => reserveClosure
      let bindings := ids.zip codes
      for (definition, code) in definitions.zip codes do
        let (params, inner) ← bind groupScope definition.2.1
        let fnBody ← lowerExprM fuel inner definition.2.2
        fillClosure code {
          params := params
          body := fnBody
          outerScope := scope.map Prod.snd
          recursiveBindings := bindings }
      return .letrec bindings (← lowerExprM fuel groupScope body)
    | .tuple [.atom "c_values", _, items] =>
      return .values (← (← properList items).mapM (lowerExprM fuel scope))
    | .tuple [.atom "c_tuple", _, items] =>
      return .tuple (← (← properList items).mapM (lowerExprM fuel scope))
    | .tuple [.atom "c_binary", _, segments] =>
      let values ← (← properList segments).mapM (fun segment => do pure (← byteSegmentValue segment))
      return .bytes (← values.mapM (lowerExprM fuel scope))
    | .tuple [.atom "c_cons", _, head, tail] =>
      return .cons (← lowerExprM fuel scope head) (← lowerExprM fuel scope tail)
    | .tuple [.atom "c_seq", _, first, second] =>
      return .seq (← lowerExprM fuel scope first) (← lowerExprM fuel scope second)
    | .tuple [.atom "c_let", _, vars, argument, body] =>
      let names ← (← properList vars).mapM (fun x => do pure (← variableName x))
      let (ids, inner) ← bind scope names
      return .letE ids (← lowerExprM fuel scope argument) (← lowerExprM fuel inner body)
    | .tuple [.atom "c_try", _, argument, vars, body, evars, handler] =>
      let names ← (← properList vars).mapM (fun x => do pure (← variableName x))
      let exceptionNames ← (← properList evars).mapM (fun x => do pure (← variableName x))
      unless exceptionNames.length == 2 || exceptionNames.length == 3 do
        throw "Core try requires two or three exception binders"
      let (ids, inner) ← bind scope names
      let (exceptionIds, handlerScope) ← bind scope exceptionNames
      return .tryE (← lowerExprM fuel scope argument) ids
        (← lowerExprM fuel inner body) exceptionIds (← lowerExprM fuel handlerScope handler)
    | .tuple [.atom "c_catch", _, body] => return .catchE (← lowerExprM fuel scope body)
    | .tuple [.atom "c_call", _, mod, fn, args] =>
      return .call (← lowerExprM fuel scope mod) (← lowerExprM fuel scope fn)
        (← (← properList args).mapM (lowerExprM fuel scope))
    | .tuple [.atom "c_apply", _, fn, args] =>
      return .apply (← lowerExprM fuel scope fn)
        (← (← properList args).mapM (lowerExprM fuel scope))
    | .tuple [.atom "c_case", _, argument, clauses] =>
      let clauses ← (← properList clauses).mapM fun clause => do
        let .tuple [.atom "c_clause", _, patterns, guard, body] := clause
          | throw "Expected a c_clause record"
        let patterns ← properList patterns
        let names := (← patterns.mapM (fun x => do pure (← patternNames fuel x))).flatten
        let (_, inner) ← bind scope names
        return (← patterns.mapM (fun x => do pure (← lowerPattern fuel inner x)),
          ← lowerExprM fuel inner guard, ← lowerExprM fuel inner body)
      return .caseE (← lowerExprM fuel scope argument) clauses
    | .tuple [.atom "c_primop", _, name, args] =>
      let name ← atom (← literal name)
      let args ← properList args
      if (name == "match_fail" && args.length == 1) || (name == "raise" && args.length == 2) ||
          (["recv_peek_message", "recv_next", "remove_message"].contains name && args.isEmpty) ||
          (name == "recv_wait_timeout" && args.length == 1) then
        return .primop name (← args.mapM (lowerExprM fuel scope))
      throw s!"Unsupported primop: {name}/{args.length}"
    | _ => throw s!"Unsupported or malformed Core construct: {tagOf term}"

/-- Standalone lowering cannot retain a module closure code table. -/
def lowerExpr (depth : Nat) (scope : NameScope) (term : Term) : Except String Expr := do
  let (expression, table) ← (lowerExprM depth scope term).run []
  unless table.isEmpty do throw "Closure expressions require module-level lowering"
  return expression

structure FunctionDiagnostic where
  name : String
  arity : Nat
  message : String
  deriving Repr, BEq

structure ModuleReport where
  module : Core.Module
  rejected : List FunctionDiagnostic
  /-- Includes every record tag in the retained RawCore tree. -/
  constructs : List String
  /-- Calls still require runtime support or linked dependency implementations. -/
  callObligations : List String
  deriving Repr

private def inventory : Nat → Term → List String
  | 0, _ => ["<inventory-depth-exceeded>"]
  | fuel + 1, term =>
    match term with
    | .tuple items =>
      let here := match items with
        | .atom tag :: _ => if tag.startsWith "c_" then [tag] else []
        | _ => []
      here ++ items.flatMap (inventory fuel)
    | .list items tail => items.flatMap (inventory fuel) ++ inventory fuel tail
    | .map entries => entries.flatMap (fun (k, v) => inventory fuel k ++ inventory fuel v)
    | _ => []

private def callInventory : Nat → Term → List String
  | 0, _ => ["<call-inventory-depth-exceeded>"]
  | fuel + 1, term =>
    match term with
    | .tuple items =>
      let here := match items with
        | [.atom "c_call", _, mod, fn, args] =>
          match literal mod >>= atom, literal fn >>= atom, properList args with
          | .ok m, .ok f, .ok xs => [s!"{m}:{f}/{xs.length}"]
          | _, _, _ => ["<dynamic remote call>"]
        | [.atom "c_apply", _, _, _] => ["<local or dynamic apply>"]
        | _ => []
      here ++ items.flatMap (callInventory fuel)
    | .list items tail => items.flatMap (callInventory fuel) ++ callInventory fuel tail
    | .map entries => entries.flatMap (fun (k, v) => callInventory fuel k ++ callInventory fuel v)
    | _ => []

private def lowerFunction (depth : Nat) (name : String) (arity : Nat) (term : Term) :
    LowerM FunctionDef := do
  let .tuple [.atom "c_fun", _, params, body] := term | throw "Expected a c_fun definition"
  let names ← (← properList params).mapM (fun x => do pure (← variableName x))
  unless names.length == arity do throw "Function arity does not match its parameter count"
  let (ids, scope) ← bind [] names
  let body ← lowerExprM depth scope body
  let fn : FunctionDef := {name, params := ids, body}
  unless fn.scopeCheck do throw "Lowered function failed scope validation"
  return fn

/-- Partial module coverage is explicit; rejected functions are never replaced by stubs. -/
def lowerModule (artifact : Artifact) (depth : Nat := 4096) : Except String ModuleReport := do
  let .tuple [.atom "c_module", _, name, exports, _, definitions] := artifact.core
    | throw "Expected a c_module record"
  let name ← atom (← literal name)
  unless name == artifact.moduleName do throw "Module name disagrees with artifact metadata"
  let exports ← (← properList exports).mapM fun x => variableName x >>= signature
  let definitions ← properList definitions
  let mut functions := []
  let mut rejected := []
  let mut signatures : List (String × Nat) := []
  let mut closureTable : ClosureTable := []
  for definition in definitions do
    let .tuple [key, value] := definition | throw "Malformed module function definition"
    let (fn, arity) ← signature (← variableName key)
    if signatures.contains (fn, arity) then throw "Duplicate function definition"
    signatures := signatures ++ [(fn, arity)]
    match (lowerFunction depth fn arity value).run closureTable with
    | .ok (body, table) =>
      functions := functions ++ [body]
      closureTable := table
    | .error message => rejected := rejected ++ [{name := fn, arity, message}]
  unless exports.eraseDups.length == exports.length do throw "Duplicate module export"
  unless exports.all signatures.contains do throw "Export references an undefined function"
  let constructs := (inventory depth artifact.core).eraseDups
  let callObligations := (callInventory depth artifact.core).eraseDups
  let closureCode ← closureTable.mapM fun slot =>
    match slot with
    | some definition => pure definition
    | none => throw "Unfilled closure code slot after module lowering"
  return { module := {name, exports, functions, closureCode}, rejected, constructs, callObligations }

end Erlean.Import
