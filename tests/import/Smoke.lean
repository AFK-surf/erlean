import Erlean.Import.Lower

open Erlean.Import Erlean.Core

private def isOkEq [BEq α] (result : Except String α) (expected : α) : Bool :=
  match result with
  | .ok actual => actual == expected
  | .error _ => false

private def assertTrue (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def expectError {α : Type} (result : Except String α) (label : String) : IO Unit :=
  match result with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError s!"Expected rejection: {label}")

private def parseTerm (text : String) : Except String Term := do
  decodeTerm 64 (← Lean.Json.parse text)

private def record (tag : String) (fields : List Term) : Term :=
  .tuple (.atom tag :: .nil :: fields)

def main : IO Unit := do
  expectError (parseTerm "{\"tag\":\"unknown\"}") "unknown term tag"
  expectError (parseTerm "{\"tag\":\"integer\",\"value\":\"12x\"}") "invalid integer"
  expectError (parseTerm "{\"tag\":\"float\",\"bits\":\"xyz\"}") "invalid float bits"
  expectError (parseTerm "{\"tag\":\"bitstring\",\"bits\":\"9\",\"hex\":\"00\"}")
    "bitstring length mismatch"
  expectError (parseTerm "{\"tag\":\"map\",\"entries\":[[]]}") "malformed map entry"
  assertTrue
    (isOkEq (parseTerm "{\"tag\":\"integer\",\"value\":\"1234567890123456789012345678901234567890\"}")
      (.integer 1234567890123456789012345678901234567890)) "arbitrary precision integer"
  assertTrue
    (isOkEq (parseTerm "{\"tag\":\"integer\",\"value\":\"-123456789012345678901234567890\"}")
      (.integer (-123456789012345678901234567890))) "negative arbitrary precision integer"
  expectError (decodeTerm 0 Lean.Json.null) "depth limit"
  expectError (lowerExpr 64 [] (record "c_var" [.integer 99])) "unbound variable"
  expectError (lowerExpr 64 [] (record "c_receive" [])) "unsupported construct"
  expectError (lowerValue 64 (.float "3ff0000000000000")) "unsupported value profile"
  expectError (lowerBitstring 3 "a1") "nonzero bitstring padding"
  expectError (lowerBitstring 8 "zz") "invalid bitstring digit"
  assertTrue (isOkEq (lowerBitstring 3 "a0") (.bitstring [true, false, true]))
    "partial-byte bitstring"
  let expected := Value.bitstring [true, false, true, false, true, true, true, true]
  assertTrue (isOkEq (lowerBitstring 8 "Af") expected &&
    isOkEq (lowerBitstring 8 "af") expected) "canonical bitstring representation"
  expectError (lowerExpr 64 [] (record "c_primop"
    [record "c_literal" [.atom "recv_marker_reserve"], .nil])) "unsupported later-stage primop"
  let literal := fun value => record "c_literal" [value]
  let flags := Term.list [.atom "unsigned", .atom "big"] .nil
  let segment := fun size unit kind options => record "c_bitstr"
    [literal (.integer 42), size, literal unit, literal kind, literal options]
  let binary := fun segment => record "c_binary" [.list [segment] .nil]
  assertTrue (isOkEq (lowerExpr 64 [] (binary
    (segment (literal (.integer 8)) (.integer 1) (.atom "integer") flags)))
    (.bytes [.lit (.integer 42)])) "fixed unsigned-byte segment"
  for size in [literal (.integer 7), literal (.integer 16), record "c_var" [.integer 0]] do
    expectError (lowerExpr 64 [] (binary
      (segment size (.integer 1) (.atom "integer") flags))) "unsupported byte size"
  for options in [Term.list [.atom "signed", .atom "big"] .nil,
      .list [.atom "unsigned", .atom "little"] .nil,
      .list [.atom "unsigned", .atom "native"] .nil, .nil] do
    expectError (lowerExpr 64 [] (binary
      (segment (literal (.integer 8)) (.integer 1) (.atom "integer") options)))
      "unsupported byte flags"
  expectError (lowerExpr 64 [] (binary
    (segment (literal (.integer 8)) (.integer 8) (.atom "integer") flags))) "unsupported byte unit"
  expectError (lowerExpr 64 [] (binary
    (segment (literal (.integer 8)) (.integer 1) (.atom "float") flags))) "unsupported byte type"
  let var := record "c_var" [.integer 0]
  expectError (lowerExpr 64 [] (record "c_let"
    [.list [var, var] .nil, record "c_literal" [.nil], var])) "duplicate binder"
  let shadow := record "c_let"
    [.list [var] .nil, record "c_literal" [.integer 7], var]
  assertTrue (isOkEq (lowerExpr 64 [(.integer 0, 0)] shadow)
    (.letE [1] (.lit (.integer 7)) (.var 1))) "lexical shadowing"
  let artifact ← readArtifact "tests/fixtures/erlang/identity/core.json"
  let .ok report := lowerModule artifact | throw (IO.userError "Real OTP fixture failed to lower")
  assertTrue (artifact.otpVersion == "29.0.6") "exact OTP patch"
  expectError (decodeArtifact (Lean.Json.mkObj
    [("format", .str "erlean.raw-core"), ("version", Lean.toJson (1 : Nat)),
      ("otp_version", .str "29.0.5")])) "different OTP patch"
  assertTrue (report.module.name == "identity") "real module name"
  assertTrue report.rejected.isEmpty "unexpected rejected fixture function"
  assertTrue report.module.check "real module scope/export validation"
  assertTrue (report.module.functions.any (fun fn =>
    fn.name == "identity" && fn.params == [0])) "identity signature"
  assertTrue (report.callObligations.contains "erlang:get_module_info/1")
    "module_info dependency must remain visible"
  let fnName := record "c_var" [.tuple [.atom "unsupported", .integer 0]]
  let unsupportedCore := record "c_module"
    [record "c_literal" [.atom "unsupported"], .list [fnName] .nil, .nil,
      .list [.tuple [fnName, record "c_fun" [.nil, record "c_receive" []]]] .nil]
  let unsupportedArtifact : Artifact := {
    otpVersion := "29.0.6"
    moduleName := "unsupported"
    core := unsupportedCore
    document := .null }
  let .ok partialReport := lowerModule unsupportedArtifact
    | throw (IO.userError "Expected a partial coverage report")
  assertTrue (partialReport.rejected.length == 1) "unsupported function must be reported"
  assertTrue partialReport.module.functions.isEmpty "unsupported function must not become a stub"
  assertTrue (partialReport.module.exports == [("unsupported", 0)])
    "unsupported export must remain visible"
  assertTrue (!partialReport.module.check) "partial module must fail full validation"
  let badExport := record "c_module"
    [record "c_literal" [.atom "unsupported"], .list [fnName] .nil, .nil, .nil]
  expectError (lowerModule {unsupportedArtifact with core := badExport}) "undefined export"
  expectError (lowerModule {unsupportedArtifact with moduleName := "wrong"}) "metadata mismatch"
  IO.println "Import checks passed: lossless decoding, rejection, scope, OTP 29.0.6 fixture."
