import Erlean.Import.Lower
import Erlean.Semantics.Machine

open Erlean.Core Erlean.Import Erlean.Semantics

-- These reduction checks establish only the stated representation properties.
example (kind : String) : (Value.exceptionInfo kind).isPublic = false := by simp [Value.isPublic]
example (kind : String) : (Value.tuple [.exceptionInfo kind]).isPublic = false := by simp [Value.isPublic, Value.publicList]
example (moduleName : String) (code : Nat) (captured : Env)
    (group : List (VarId × Nat)) :
    (Value.closure moduleName code captured group).exactComparable = false := by simp [Value.exactComparable]

private def assertTrue (condition : Bool) (label : String) : IO Unit :=
  unless condition do throw (IO.userError label)

private def expect (expr : Expr) (result : Outcome) (label : String) : IO Unit := do
  let initial : LocalState := {control := .eval expr, context := ⟨"test", []⟩}
  assertTrue (runLocal 1000 [] initial == .halted result) label

private def bifCall (name : String) (args : List Expr) : Expr :=
  .call (.lit (.atom "erlang")) (.lit (.atom name)) args

private def errorE (reason : String) : Expr := bifCall "error" [.lit (.atom reason)]

def main : IO Unit := do
  expect (.tryE (.values [.lit (.integer 3), .lit (.integer 5)]) [0, 1]
      (.tuple [.var 1, .var 0]) [0, 1, 2] (.lit (.atom "wrong")))
    (.returned [.tuple [.integer 5, .integer 3]])
    "try normal binders preserve multiple-value order"
  expect (.tryE (.values []) [0] (.var 0) [0, 1] (.lit (.atom "wrong")))
    (.fault (.invalid "Core try normal binding arity mismatch"))
    "try normal arity mismatch is a model fault"
  expect (.tryE (.lit .nil) [] (.lit .nil) [0] (.lit .nil))
    (.fault (.invalid "Core try exception binding arity mismatch"))
    "try rejects an invalid exception binder count before evaluating"
  expect (.tryE (errorE "original") [0] (.var 0) [0, 1]
      (.tuple [.var 0, .var 1]))
    (.returned [.tuple [.atom "error", .atom "original"]])
    "two-variable try binds exception class and reason"
  expect (.tryE (.lit (.atom "normal")) [0] (errorE "normal_body")
      [0, 1, 2] (.lit (.atom "wrong")))
    (.raised ⟨.error, .atom "normal_body"⟩)
    "try does not catch errors in its normal continuation"
  expect (.tryE (errorE "original") [0] (.var 0)
      [0, 1, 2] (errorE "handler_body"))
    (.raised ⟨.error, .atom "handler_body"⟩)
    "try does not catch errors in its handler continuation"
  expect (.tryE (bifCall "throw" [.lit (.atom "original")]) [0] (.var 0)
      [0, 1, 2] (.primop "raise" [.var 2, .lit (.atom "replacement")]))
    (.raised ⟨.throw, .atom "replacement"⟩)
    "raise restores class from opaque information and takes its explicit reason"
  expect (.tryE (errorE "original") [0] (.var 0) [0, 1, 2]
      (bifCall "is_atom" [.var 2]))
    (.fault (.unsupported "BIF observation of opaque exception information"))
    "BIFs cannot inspect opaque exception information"
  expect (.tryE (errorE "original") [0] (.var 0) [0, 1, 2]
      (bifCall "is_tuple" [.tuple [.var 2]]))
    (.fault (.unsupported "BIF observation of opaque exception information"))
    "opaque information remains protected inside visible compound values"
  expect (.tryE (.primop "unimplemented" []) [0] (.var 0)
      [0, 1, 2] (.lit (.atom "wrong")))
    (.fault (.unsupported "primop unimplemented/0"))
    "try must not convert model faults into language exceptions"
  let truth := Expr.lit (.atom "true")
  let inspectToken := Expr.caseE (.var 2)
    [([.lit .nil], truth, .lit (.atom "wrong")),
     ([.wild], truth, .lit (.atom "fallback"))]
  expect (.tryE (errorE "original") [0] (.var 0) [0, 1, 2] inspectToken)
    (.fault (.unsupported "Pattern observation of opaque exception information"))
    "opaque literal inspection cannot silently become pattern mismatch"
  let inspectNested := Expr.caseE (.tuple [.var 2])
    [([.lit (.tuple [.nil])], truth, .lit (.atom "wrong"))]
  expect (.tryE (errorE "original") [0] (.var 0) [0, 1, 2] inspectNested)
    (.fault (.unsupported "Pattern observation of opaque exception information"))
    "literal comparison rejects inspection nested in a tuple"
  let inspectShape := Expr.caseE (.var 2)
    [([.tuple []], truth, .lit (.atom "wrong"))]
  expect (.tryE (errorE "original") [0] (.var 0) [0, 1, 2] inspectShape)
    (.fault (.unsupported "Pattern observation of opaque exception information"))
    "constructor patterns cannot discriminate opaque exception information"
  let transport := Expr.caseE (.tuple [.var 2])
    [([.tuple [.alias 3 (.var 4)]], truth, .primop "raise" [.var 4, .var 1])]
  expect (.tryE (errorE "original") [0] (.var 0) [0, 1, 2] transport)
    (.raised ⟨.error, .atom "original"⟩)
    "constructor fields may transport opaque information through aliases"
  let outerMismatch := Expr.caseE (.tuple [.var 2])
    [([.lit .nil], truth, .lit (.atom "wrong")),
     ([.wild], truth, .lit (.atom "allowed"))]
  expect (.tryE (errorE "original") [0] (.var 0) [0, 1, 2] outerMismatch)
    (.returned [.atom "allowed"])
    "outer shape mismatch does not inspect a nested token"
  expect (.catchE (bifCall "throw" [.lit (.integer 7)])) (.returned [.integer 7])
    "old catch unwraps throw"
  expect (.catchE (bifCall "exit" [.lit (.integer 7)]))
    (.returned [.tuple [.atom "EXIT", .integer 7]]) "old catch wraps exit"
  expect (.catchE (errorE "reason"))
    (.fault (.unsupported "Old catch of error requires observable stacktrace semantics"))
    "old catch must not fabricate an error stacktrace"
  expect (.catchE (.values []))
    (.fault (.invalid "Core catch requires a single result"))
    "old catch rejects malformed multiple-value results"
  expect (bifCall "=:=" [.lit (.tuple [.integer 7]), .lit (.tuple [.integer 7])])
    (.returned [.atom "true"]) "exact equality accepts structural data"
  expect (bifCall "=:=" [.lit (.function "m" "f" 0), .lit (.function "m" "f" 0)])
    (.fault (.unsupported "Exact equality involving function identity or exception information"))
    "exact equality must not expose structural function identity"
  expect (.letE [7] (.lit (.integer 99))
      (.tryE (.letE [8] (.lit (.integer 1)) (errorE "original")) [8] (.var 8)
        [8, 9, 10] (.var 7)))
    (.returned [.integer 99]) "exception unwinding restores the lexical try context"

  let artifact ← readArtifact "tests/fixtures/erlang/exceptions/core.json"
  let .ok report := lowerModule artifact | throw (IO.userError "Exception fixture import failed")
  assertTrue (report.rejected.isEmpty && report.module.check) "complete exception fixture import"
  let check (name : String) (args : Values) (result : Outcome) : IO Unit :=
    assertTrue (runLocal 10000 [report.module] (initialCall "exceptions" name args) ==
      .halted result) s!"Imported exception fixture: {name}"
  for kind in ["throw", "error", "exit"] do
    check "handle" [.atom kind, .integer 7] (.returned [.tuple [.atom kind, .integer 7]])
  check "handle" [.atom "normal", .integer 7] (.returned [.integer 7])
  check "try_of" [.tuple [.atom "ok", .integer 7]] (.returned [.integer 7])
  check "try_of" [.integer 7] (.raised ⟨.error, .tuple [.atom "try_clause", .integer 7]⟩)
  check "nested" [.integer 7] (.returned [.tuple [.atom "outer", .tuple [.atom "inner", .integer 7]]])
  check "after_success" [.integer 7] (.returned [.integer 7])
  check "after_failure" [.integer 7] (.raised ⟨.error, .integer 7⟩)
  check "after_override" [.integer 7] (.raised ⟨.error, .integer 7⟩)
  check "guard_error" [.nil] (.returned [.atom "fallback"])
  check "guard_error" [.cons (.atom "true") .nil] (.returned [.atom "matched"])
  check "catch_throw" [.integer 7] (.returned [.integer 7])
  check "catch_exit" [.integer 7] (.returned [.tuple [.atom "EXIT", .integer 7]])
  IO.println "Exception regressions passed."
