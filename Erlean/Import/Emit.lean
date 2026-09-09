import Erlean.Core.Syntax

namespace Erlean.Import.Emit

open Core

private structure Output where
  namePrefix : String
  next : Nat := 0
  declarations : Array String := #[]

private def save (type body : String) : StateM Output String := do
  let state ← get
  let name := s!"{state.namePrefix}_part_{state.next}"
  let declarations := state.declarations.push
    s!"private def {name} : {type} :=\n{body}\n"
  set { state with next := state.next + 1, declarations := declarations }
  return name

/-- Bound list syntax independently of the number of functions or operands. -/
private def list (type : String) (items : List String) : StateM Output String := do
  if items.length ≤ 24 then
    return "[" ++ String.intercalate ", " items ++ "]"
  else
    let tail ← list type (items.drop 24)
    save s!"List ({type})"
      (String.intercalate " :: " (items.take 24) ++ " :: " ++ tail)
termination_by items.length

private def literal [Repr α] (value : α) : String := "(" ++ reprStr value ++ ")"

/-- Small subtrees remain readable literals. Larger expressions reference
    transparent chunks without changing any constructor or operand order. -/
private partial def expression (value : Expr) : StateM Output String := do
  let printed := literal value
  if printed.length ≤ 1536 then return printed
  let app (name : String) (args : List String) :=
    "Erlean.Core.Expr." ++ name ++ " " ++ String.intercalate " " args
  let expressions (xs : List Expr) := do
    return "(" ++ (← list "Erlean.Core.Expr" (← xs.mapM expression)) ++ ")"
  let render : Unit → StateM Output String := fun _ => do
    match value with
      | .lit v => pure (app "lit" [literal v])
      | .var v => pure (app "var" [literal v])
      | .values xs => do return app "values" [← expressions xs]
      | .letE vars arg body => do return app "letE" [literal vars, ← expression arg, ← expression body]
      | .seq a b => do return app "seq" [← expression a, ← expression b]
      | .cons a b => do return app "cons" [← expression a, ← expression b]
      | .tuple xs => do return app "tuple" [← expressions xs]
      | .map exact xs => do return app "map" [literal exact, ← expressions xs]
      | .bytes xs => do return app "bytes" [← expressions xs]
      | .call m f xs => do return app "call" [← expression m, ← expression f, ← expressions xs]
      | .apply f xs => do return app "apply" [← expression f, ← expressions xs]
      | .primop name xs => do return app "primop" [literal name, ← expressions xs]
      | .funRef name arity => pure (app "funRef" [literal name, literal arity])
      | .makeClosure code => pure (app "makeClosure" [literal code])
      | .letrec bindings body => do return app "letrec" [literal bindings, ← expression body]
      | .tryE arg vars body evars handler => do
        return app "tryE" [← expression arg, literal vars, ← expression body,
          literal evars, ← expression handler]
      | .catchE body => do return app "catchE" [← expression body]
      | .caseE arg clauses => do
        let arg ← expression arg
        let clauses ← clauses.mapM fun (patterns, guard, body) => do
          return "(" ++ literal patterns ++ ", " ++ (← expression guard) ++
            ", " ++ (← expression body) ++ ")"
        return app "caseE" [arg, "(" ++ (← list "Erlean.Core.Clause" clauses) ++ ")"]
  let body ← render ()
  save "Erlean.Core.Expr" body

/-- Emit transparent source chunks for the exact imported AST. This is an
    auditable serialization, not a verified compiler translation. -/
def moduleSource (value : Core.Module) (declaration : String) : String := Id.run do
  let generate : StateM Output String := do
    let functions ← value.functions.mapM fun function => do
      let body ← expression function.body
      save "Erlean.Core.FunctionDef"
        ("{ name := " ++ literal function.name ++ ", params := " ++
          literal function.params ++ ", body := " ++ body ++ " }")
    let closures ← value.closureCode.mapM fun closure => do
      let body ← expression closure.body
      save "Erlean.Core.ClosureDef"
        ("{ params := " ++ literal closure.params ++ ", body := " ++ body ++
          ", outerScope := " ++ literal closure.outerScope ++
          ", recursiveBindings := " ++ literal closure.recursiveBindings ++ " }")
    let functions ← list "Erlean.Core.FunctionDef" functions
    let closures ← list "Erlean.Core.ClosureDef" closures
    let exports ← list "String × Nat" (value.exports.map literal)
    return "{ name := " ++ literal value.name ++ "\n  exports := " ++ exports ++
      "\n  functions := " ++ functions ++ "\n  closureCode := " ++ closures ++ " }"
  let (body, state) := generate.run { namePrefix := declaration }
  -- Delay reducibility until assembly is checked. Clients retain the same
  -- projection reduction behavior as a literal, without eager assembly work.
  let attributes := if state.next == 0 then "" else
    "\nattribute [reducible] " ++ String.intercalate " "
      ((List.range state.next).map fun index => s!"{declaration}_part_{index}") ++ "\n"
  return "import Erlean.Core.Syntax\n\nnamespace Erlean.Examples\n\n" ++
    String.join state.declarations.toList ++
    "/-- Generated from a pinned OTP Core artifact by the erlean importer. -/\n" ++
    "def " ++ declaration ++ " : Erlean.Core.Module :=\n" ++ body ++
    "\n" ++ attributes ++ "\nend Erlean.Examples\n"

end Erlean.Import.Emit
