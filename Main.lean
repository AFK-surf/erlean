import Erlean

open Lean Erlean.Core Erlean.Import Erlean.Semantics

private def checked {α : Type} : Except String α → IO α
  | .ok value => pure value
  | .error message => throw (IO.userError message)

private def string (value : String) : Lean.Json := .str value

private def encodeValue : Value → Lean.Json
  | .integer value => Lean.Json.mkObj [("tag", string "integer"), ("value", string (toString value))]
  | .atom value => Lean.Json.mkObj [("tag", string "atom"), ("value", string value)]
  | .nil => Lean.Json.mkObj [("tag", string "nil")]
  | .cons head tail => Lean.Json.mkObj [("tag", string "cons"),
      ("head", encodeValue head), ("tail", encodeValue tail)]
  | .tuple values => Lean.Json.mkObj [("tag", string "tuple"),
      ("items", .arr (values.map encodeValue).toArray)]
  | .function mod name arity => Lean.Json.mkObj [("tag", string "function"),
      ("module", string mod), ("name", string name), ("arity", toJson arity)]

private def load (path : String) : IO ModuleReport := do
  checked (lowerModule (← readArtifact path))

private def complete (report : ModuleReport) : IO Unit := do
  unless report.rejected.isEmpty do
    throw (IO.userError s!"Module contains rejected functions: {repr report.rejected}")
  unless report.module.check do
    throw (IO.userError "Module failed scope/export validation")

private def inspect (path : String) : IO Unit := do
  let report ← load path
  let rejected := report.rejected.map fun item => Lean.Json.mkObj [
    ("name", string item.name), ("arity", toJson item.arity), ("reason", string item.message)]
  IO.println (Lean.Json.mkObj [
    ("module", string report.module.name),
    ("accepted_functions", toJson report.module.functions.length),
    ("rejected", .arr rejected.toArray),
    ("constructs", toJson report.constructs),
    ("call_obligations", toJson report.callObligations)]).compress

private def execute (path name args : String) (fuel : Nat) : IO UInt32 := do
  let report ← load path
  complete report
  let json ← checked (Lean.Json.parse args)
  let raw ← checked json.getArr?
  let values ← raw.toList.mapM fun j => checked (decodeTerm 4096 j >>= lowerValue 4096)
  match runLocal fuel [report.module] (initialCall report.module.name name values) with
  | .halted (.returned values) =>
    IO.println (Lean.Json.mkObj [("status", string "returned"),
      ("values", .arr (values.map encodeValue).toArray)]).compress
    return 0
  | .halted (.raised exception) =>
    let kind := match exception.kind with
      | .error => "error" | .exit => "exit" | .throw => "throw"
    IO.println (Lean.Json.mkObj [("status", string "raised"),
      ("class", string kind), ("reason", encodeValue exception.reason)]).compress
    return 0
  | .halted (.fault fault) =>
    IO.eprintln s!"Model fault: {repr fault}"
    return 1
  | .exhausted _ =>
    IO.eprintln s!"Fuel exhausted after {fuel} steps; this does not establish divergence."
    return 2

/-- Emit an auditable Lean literal, not a claim of verified source translation. -/
private def emit (path : String) (declaration : String := "importedModule") : IO Unit := do
  unless !declaration.isEmpty && declaration.toList.all (fun c => c.isAlpha || c == '_') do
    throw (IO.userError "Declaration name must contain only letters and underscores")
  let report ← load path
  complete report
  IO.println "import Erlean.Core.Syntax"
  IO.println ""
  IO.println "namespace Erlean.Examples"
  IO.println ""
  IO.println "/-- Generated from a pinned OTP Core artifact by the erlean importer. -/"
  IO.println s!"def {declaration} : Erlean.Core.Module :=\n{reprStr report.module}"
  IO.println ""
  IO.println "end Erlean.Examples"

def main (args : List String) : IO UInt32 := do
  try
    match args with
    | ["inspect", path] => inspect path; return 0
    | ["emit", path] => emit path; return 0
    | ["emit", path, declaration] => emit path declaration; return 0
    | ["run", path, name, values] => execute path name values 100000
    | ["run", path, name, values, fuel] =>
      let some fuel := fuel.toNat? | throw (IO.userError "Fuel must be a natural number")
      execute path name values fuel
    | _ =>
      IO.eprintln "Usage: erlean inspect ARTIFACT | emit ARTIFACT [DECLARATION] | run ARTIFACT FUNCTION JSON_ARGUMENTS [FUEL]"
      return 2
  catch error =>
    IO.eprintln s!"erlean: {error}"
    return 1
