import Erlean
import Erlean.Runtime.Scheduler

open Lean Erlean.Core Erlean.Import Erlean.Semantics

private def checked {α : Type} : Except String α → IO α
  | .ok value => pure value
  | .error message => throw (IO.userError message)

private def string (value : String) : Lean.Json := .str value

private def encodeBits (bits : List Bool) : String :=
  String.ofList ((List.range (2 * ((bits.length + 7) / 8))).map fun index =>
    let nibble := (List.range 4).foldl (fun value offset =>
      value * 2 + if bits[index * 4 + offset]?.getD false then 1 else 0) 0
    "0123456789abcdef".toList[nibble]?.getD '0')

private def encodeValue : Value → Except String Lean.Json
  | .integer value => pure (Lean.Json.mkObj [("tag", string "integer"), ("value", string (toString value))])
  | .atom value => pure (Lean.Json.mkObj [("tag", string "atom"), ("value", string value)])
  | .nil => pure (Lean.Json.mkObj [("tag", string "nil")])
  | .cons head tail => do
    return Lean.Json.mkObj [("tag", string "cons"), ("head", ← encodeValue head), ("tail", ← encodeValue tail)]
  | .tuple values => do
    return Lean.Json.mkObj [("tag", string "tuple"), ("items", .arr (← values.mapM encodeValue).toArray)]
  | .bitstring bits => pure (Lean.Json.mkObj [("tag", string "bitstring"),
      ("bits", string (toString bits.length)), ("hex", string (encodeBits bits))])
  | .function mod name arity => pure (Lean.Json.mkObj [("tag", string "function"),
      ("module", string mod), ("name", string name), ("arity", toJson arity)])
  | .closure mod code _ _ => pure (Lean.Json.mkObj [("tag", string "closure"),
      ("module", string mod), ("code", toJson code)])
  | .exceptionInfo _ => .error "Internal exception information cannot be serialized"
  | .pid id => pure (Lean.Json.mkObj [("tag", string "pid"), ("id", toJson id)])
  | .reference id => pure (Lean.Json.mkObj [("tag", string "reference"), ("id", toJson id)])

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

private def executeWorld (world : CodeWorld) (moduleName name args : String) (fuel : Nat) : IO UInt32 := do
  let json ← checked (Lean.Json.parse args)
  let raw ← checked json.getArr?
  let values ← raw.toList.mapM fun j => checked (decodeTerm 4096 j >>= lowerValue 4096)
  let result := match runLocal fuel world (initialCall moduleName name values) with
    | .halted outcome => RunResult.halted (observeOutcome outcome)
    | .exhausted state => .exhausted state
  match result with
  | .halted (.returned values) =>
    let encoded ← checked (values.mapM encodeValue)
    IO.println (Lean.Json.mkObj [("status", string "returned"),
      ("values", .arr encoded.toArray)]).compress
    return 0
  | .halted (.raised exception) =>
    let kind := match exception.kind with
      | .error => "error" | .exit => "exit" | .throw => "throw"
    let reason ← checked (encodeValue exception.reason)
    IO.println (Lean.Json.mkObj [("status", string "raised"),
      ("class", string kind), ("reason", reason)]).compress
    return 0
  | .halted (.fault fault) =>
    IO.eprintln s!"Model fault: {repr fault}"
    return 1
  | .exhausted _ =>
    IO.eprintln s!"Fuel exhausted after {fuel} steps; this does not establish divergence."
    return 2

private def execute (path name args : String) (fuel : Nat) : IO UInt32 := do
  let report ← load path
  complete report
  executeWorld [report.module] report.module.name name args fuel

private def executeLinked (paths : List String) (moduleName name args : String) : IO UInt32 := do
  let reports ← paths.mapM load
  reports.forM complete
  let world := reports.map ModuleReport.module
  unless (world.map Module.name).eraseDups.length == world.length do
    throw (IO.userError "Linked modules must have unique names")
  executeWorld world moduleName name args 100000

private def encodeChoice : Erlean.Runtime.Choice → Lean.Json
  | .run pid => Lean.Json.mkObj [("run", toJson pid)]
  | .deliver id => Lean.Json.mkObj [("deliver", toJson id)]
  | .advanceTime time => Lean.Json.mkObj [("time", toJson time)]

private def decodeChoice (json : Lean.Json) : Except String Erlean.Runtime.Choice := do
  if let .ok value := json.getObjVal? "run" then return .run (← value.getNat?)
  if let .ok value := json.getObjVal? "deliver" then return .deliver (← value.getNat?)
  if let .ok value := json.getObjVal? "time" then return .advanceTime (← value.getNat?)
  throw "Expected a run, deliver, or time schedule choice"

private def actorExecute (path name args : String) (tracePath : Option String := none)
    (replayPath : Option String := none) : IO UInt32 := do
  let report ← load path
  complete report
  let raw ← checked ((← checked (Lean.Json.parse args)).getArr?)
  let values ← raw.toList.mapM fun j => checked (decodeTerm 4096 j >>= lowerValue 4096)
  let world := [report.module]
  let initial := Erlean.Runtime.initialSystem report.module.name name values
  let result ← match replayPath with
    | none => pure (Erlean.Runtime.schedule world 100000 initial 0 [])
    | some path => do
      let json ← checked (Lean.Json.parse (← IO.FS.readFile path))
      let choices ← checked ((← checked json.getArr?).toList.mapM decodeChoice)
      match Erlean.Runtime.replay world initial choices with
      | .error error => throw (IO.userError s!"Invalid replay choice: {repr error}")
      | .ok system => pure ({ system, choices, stopped := "replayed" } : Erlean.Runtime.ScheduleResult)
  if let some path := tracePath then
    IO.FS.writeFile path (Lean.Json.arr (result.choices.map encodeChoice).toArray).compress
  for process in result.system.processes do
    if let .finished (.fault fault) := process.status then
      IO.eprintln s!"Actor model fault in pid {process.pid}: {repr fault}"
      return 1
  let some root := result.system.lookup 0 | throw (IO.userError "Actor root is absent")
  match root.status with
  | .finished outcome =>
    match observeOutcome outcome with
    | .returned values =>
      let encoded ← checked (values.mapM encodeValue)
      IO.println (Lean.Json.mkObj [("status", string "returned"),
        ("values", .arr encoded.toArray)]).compress
      return 0
    | .raised exception =>
      let reason ← checked (encodeValue exception.reason)
      let fields := if exception.kind == .exit then
          [("status", string "exited"), ("reason", reason)]
        else [("status", string "raised"), ("class", string exception.kind.name), ("reason", reason)]
      IO.println (Lean.Json.mkObj fields).compress
      return 0
    | .fault fault => IO.eprintln s!"Actor observation fault: {repr fault}"; return 1
  | _ =>
    IO.eprintln s!"Actor schedule {result.stopped} after {result.choices.length} choices; no liveness conclusion."
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
    | "run-linked" :: moduleName :: name :: values :: paths =>
      executeLinked paths moduleName name values
    | ["actor-run", path, name, values] => actorExecute path name values
    | ["actor-run", path, name, values, trace] => actorExecute path name values (some trace)
    | ["actor-replay", path, name, values, trace] => actorExecute path name values none (some trace)
    | _ =>
      IO.eprintln "Usage: erlean inspect ARTIFACT | emit ARTIFACT [DECLARATION] | run ARTIFACT FUNCTION JSON_ARGUMENTS [FUEL] | run-linked MODULE FUNCTION JSON_ARGUMENTS ARTIFACTS... | actor-run ARTIFACT FUNCTION JSON_ARGUMENTS [TRACE_FILE] | actor-replay ARTIFACT FUNCTION JSON_ARGUMENTS TRACE_FILE"
      return 2
  catch error =>
    IO.eprintln s!"erlean: {error}"
    return 1
