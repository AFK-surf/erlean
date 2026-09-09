import Lean.Data.Json

namespace Erlean.Import

/-- Lossless interchange terms, including annotations and unsupported literals. -/
inductive Term where
  | atom (value : String)
  | integer (value : Int)
  | float (bits : String)
  | bitstring (bits : Nat) (hex : String)
  | nil
  | list (items : List Term) (tail : Term)
  | tuple (items : List Term)
  | map (entries : List (Term × Term))
  deriving Repr, BEq

private def field (j : Lean.Json) (key : String) : Except String Lean.Json :=
  j.getObjVal? key

private def stringField (j : Lean.Json) (key : String) : Except String String := do
  (← field j key).getStr?

private def isHex (s : String) : Bool :=
  s.toList.all (fun c => c.isDigit || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F'))

/-- The depth bound protects the importer; exhaustion is an import error. -/
def decodeTerm : Nat → Lean.Json → Except String Term
  | 0, _ => .error "RawCore nesting exceeds the import depth limit"
  | depth + 1, j => do
    match ← stringField j "tag" with
    | "atom" => return .atom (← stringField j "value")
    | "integer" =>
      let s ← stringField j "value"
      match s.toInt? with
      | some n => return .integer n
      | none => throw s!"Invalid integer: {s}"
    | "float" =>
      let bits ← stringField j "bits"
      unless bits.length == 16 && isHex bits do throw "Float bits must be 16 hexadecimal digits"
      return .float bits
    | "bitstring" =>
      let count ← stringField j "bits"
      let some bits := count.toNat? | throw "Invalid bitstring length"
      let hex ← stringField j "hex"
      unless hex.length == 2 * ((bits + 7) / 8) && isHex hex do
        throw "Bitstring byte encoding does not match its length"
      return .bitstring bits hex
    | "nil" => return .nil
    | "tuple" =>
      return .tuple (← (← (← field j "items").getArr?).toList.mapM (decodeTerm depth))
    | "list" =>
      let items ← (← (← field j "items").getArr?).toList.mapM (decodeTerm depth)
      return .list items (← decodeTerm depth (← field j "tail"))
    | "map" =>
      let entries ← (← (← field j "entries").getArr?).toList.mapM fun pair => do
        let xs ← pair.getArr?
        unless xs.size == 2 do throw "Map entry must contain exactly two terms"
        return (← decodeTerm depth xs[0]!, ← decodeTerm depth xs[1]!)
      return .map entries
    | tag => throw s!"Unknown RawCore term tag: {tag}"

structure Artifact where
  otpVersion : String
  moduleName : String
  core : Term
  /-- Preserve all exporter provenance fields for downstream manifest checks. -/
  document : Lean.Json

def decodeArtifact (j : Lean.Json) (depth : Nat := 4096) : Except String Artifact := do
  unless (← stringField j "format") == "erlean.raw-core" do throw "Unsupported artifact format"
  unless (← (← field j "version").getNat?) == 1 do throw "Unsupported artifact version"
  let otpVersion ← stringField j "otp_version"
  unless otpVersion == "29.0.6" || otpVersion == "29.0.2" do
    throw "Artifact must target a supported exact OTP profile: 29.0.2 or 29.0.6"
  let moduleName ← stringField j "module"
  let core ← decodeTerm depth (← field j "core")
  return { otpVersion, moduleName, core, document := j }

def readArtifact (path : System.FilePath) : IO Artifact := do
  let text ← IO.FS.readFile path
  let result := Lean.Json.parse text >>= decodeArtifact
  match result with
  | .ok artifact => return artifact
  | .error message => throw (IO.userError message)

end Erlean.Import
