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
    | .bitstring _ _ => throw "Unsupported literal: bitstring"
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

private def patternNames : Nat → Term → Except String (List Term)
  | 0, _ => .error "Pattern nesting exceeds the import depth limit"
  | fuel + 1, term => do
    match term with
    | .tuple [.atom "c_var", _, name] => return [name]
    | .tuple [.atom "c_literal", _, _] => return []
    | .tuple [.atom "c_cons", _, head, tail] =>
      return (← patternNames fuel head) ++ (← patternNames fuel tail)
    | .tuple [.atom "c_tuple", _, items] =>
      return (← (← properList items).mapM (patternNames fuel)).flatten
    | _ => throw s!"Unsupported or malformed Core pattern: {tagOf term}"

private def lowerPattern : Nat → NameScope → Term → Except String Pattern
  | 0, _, _ => .error "Pattern nesting exceeds the import depth limit"
  | fuel + 1, scope, term => do
    match term with
    | .tuple [.atom "c_var", _, name] => return .var (← lookup scope name)
    | .tuple [.atom "c_literal", _, value] => return .lit (← lowerValue fuel value)
    | .tuple [.atom "c_cons", _, head, tail] =>
      return .cons (← lowerPattern fuel scope head) (← lowerPattern fuel scope tail)
    | .tuple [.atom "c_tuple", _, items] =>
      return .tuple (← (← properList items).mapM (lowerPattern fuel scope))
    | _ => throw s!"Unsupported or malformed Core pattern: {tagOf term}"

/-- Resolve lexical binders. IDs are fresh within each lexical scope. -/
def lowerExpr : Nat → NameScope → Term → Except String Expr
  | 0, _, _ => .error "Expression nesting exceeds the import depth limit"
  | fuel + 1, scope, term => do
    match term with
    | .tuple [.atom "c_literal", _, value] => return .lit (← lowerValue fuel value)
    | .tuple [.atom "c_var", _, name] =>
      match name with
      | .tuple [.atom fn, .integer (.ofNat arity)] => return .funRef fn arity
      | _ => return .var (← lookup scope name)
    | .tuple [.atom "c_values", _, items] =>
      return .values (← (← properList items).mapM (lowerExpr fuel scope))
    | .tuple [.atom "c_tuple", _, items] =>
      return .tuple (← (← properList items).mapM (lowerExpr fuel scope))
    | .tuple [.atom "c_cons", _, head, tail] =>
      return .cons (← lowerExpr fuel scope head) (← lowerExpr fuel scope tail)
    | .tuple [.atom "c_seq", _, first, second] =>
      return .seq (← lowerExpr fuel scope first) (← lowerExpr fuel scope second)
    | .tuple [.atom "c_let", _, vars, argument, body] =>
      let names ← (← properList vars).mapM variableName
      let (ids, inner) ← bind scope names
      return .letE ids (← lowerExpr fuel scope argument) (← lowerExpr fuel inner body)
    | .tuple [.atom "c_call", _, mod, fn, args] =>
      return .call (← lowerExpr fuel scope mod) (← lowerExpr fuel scope fn)
        (← (← properList args).mapM (lowerExpr fuel scope))
    | .tuple [.atom "c_apply", _, fn, args] =>
      return .apply (← lowerExpr fuel scope fn)
        (← (← properList args).mapM (lowerExpr fuel scope))
    | .tuple [.atom "c_case", _, argument, clauses] =>
      let clauses ← (← properList clauses).mapM fun clause => do
        let .tuple [.atom "c_clause", _, patterns, guard, body] := clause
          | throw "Expected a c_clause record"
        let patterns ← properList patterns
        let names := (← patterns.mapM (patternNames fuel)).flatten
        let (_, inner) ← bind scope names
        return (← patterns.mapM (lowerPattern fuel inner),
          ← lowerExpr fuel inner guard, ← lowerExpr fuel inner body)
      return .caseE (← lowerExpr fuel scope argument) clauses
    | .tuple [.atom "c_primop", _, name, args] =>
      let name ← atom (← literal name)
      let args ← properList args
      if name == "match_fail" && args.length == 1 then
        return .primop name (← args.mapM (lowerExpr fuel scope))
      throw s!"Unsupported primop: {name}/{args.length}"
    | _ => throw s!"Unsupported or malformed Core construct: {tagOf term}"

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
    Except String FunctionDef := do
  let .tuple [.atom "c_fun", _, params, body] := term | throw "Expected a c_fun definition"
  let names ← (← properList params).mapM variableName
  unless names.length == arity do throw "Function arity does not match its parameter count"
  let (ids, scope) ← bind [] names
  let body ← lowerExpr depth scope body
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
  for definition in definitions do
    let .tuple [key, value] := definition | throw "Malformed module function definition"
    let (fn, arity) ← signature (← variableName key)
    if signatures.contains (fn, arity) then throw "Duplicate function definition"
    signatures := signatures ++ [(fn, arity)]
    match lowerFunction depth fn arity value with
    | .ok body => functions := functions ++ [body]
    | .error message => rejected := rejected ++ [{name := fn, arity, message}]
  unless exports.eraseDups.length == exports.length do throw "Duplicate module export"
  unless exports.all signatures.contains do throw "Export references an undefined function"
  let constructs := (inventory depth artifact.core).eraseDups
  let callObligations := (callInventory depth artifact.core).eraseDups
  return { module := {name, exports, functions}, rejected, constructs, callObligations }

end Erlean.Import
