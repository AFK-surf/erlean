import Erlean.Import.Lower
import Erlean.Semantics.Machine

open Erlean.Core Erlean.Import Erlean.Semantics

private def assertTrue (condition : Bool) (label : String) : IO Unit :=
  unless condition do throw (IO.userError label)

private def expect (world : CodeWorld) (expr : Expr) (result : Outcome) (label : String) : IO Unit :=
  let initial : LocalState := {control := .eval expr, context := ⟨"test", []⟩}
  assertTrue (runLocal 1000 world initial == .halted result) label

private def callBif (name : String) (args : List Expr) : Expr :=
  .call (.lit (.atom "erlang")) (.lit (.atom name)) args

def main : IO Unit := do
  expect [] (callBif "=<" [.lit (.integer (-5)), .lit (.integer 2)])
    (.returned [.atom "true"]) "integer order includes negative integers"
  expect [] (callBif "=<" [.lit (.integer 7), .lit (.integer 7)])
    (.returned [.atom "true"]) "integer order is non-strict"
  expect [] (callBif "=<" [.lit (.integer 8), .lit (.integer 7)])
    (.returned [.atom "false"]) "integer order rejects a greater left operand"
  expect [] (callBif "=<" [.lit (.atom "a"), .lit (.atom "b")])
    (.fault (.unsupported "BIF erlang:=</2"))
    "non-integer term ordering remains explicitly outside the profile"
  expect [] (.letE [0, 1] (.values [.lit (.integer 3), .lit (.integer 5)])
    (.tuple [.var 1, .var 0])) (.returned [.tuple [.integer 5, .integer 3]])
    "Core multiple values must bind independently of tuple values"
  expect [] (.letE [0] (.values [.lit (.integer 3), .lit (.integer 5)]) (.var 0))
    (.fault (.invalid "Core let binding arity mismatch")) "binding arity mismatch"
  expect [] (.var 0) (.fault (.invalid "Unbound variable 0")) "unbound machine variable"
  let truth := Expr.lit (.atom "true")
  let failingGuard := callBif "hd" [.lit .nil]
  let guardCase := Expr.caseE (.lit (.integer 7))
    [([.var 0], failingGuard, .lit (.atom "wrong")),
     ([.var 1], truth, .var 1)]
  expect [] guardCase (.returned [.integer 7]) "guard error falls through to the next clause"
  let unsupportedGuard := Expr.caseE (.lit (.integer 7))
    [([.var 0], callBif "get_module_info" [.lit (.atom "test")], .var 0),
     ([.wild], truth, .lit (.atom "wrong"))]
  expect [] unsupportedGuard (.fault (.unsupported "BIF erlang:get_module_info/1"))
    "model faults must not become guard failure"
  let first := callBif "error" [.lit (.atom "first")]
  let second := callBif "error" [.lit (.atom "second")]
  expect [] (.tuple [first, second]) (.raised ⟨.error, .atom "first"⟩)
    "tuple operands evaluate from left to right"
  expect [] (.cons first second) (.raised ⟨.error, .atom "first"⟩)
    "cons operands evaluate from head to tail"
  let artifact ← readArtifact "tests/fixtures/erlang/sequential/core.json"
  let .ok report := lowerModule artifact | throw (IO.userError "Sequential import failed")
  assertTrue (report.rejected.isEmpty && report.module.check) "complete sequential module"
  let world := [report.module]
  let values := [.integer 1, .atom "two", .tuple [.integer 3]]
  let input := values.foldr Value.cons .nil
  assertTrue (runLocal 10000 world (initialCall "sequential" "reverse" [input]) ==
    .halted (.returned [values.reverse.foldr Value.cons .nil])) "recursive reverse"
  assertTrue (runLocal 10000 world (initialCall "sequential" "context" [.integer 99]) ==
    .halted (.returned [.tuple [.atom "other", .integer 99, .integer 99]]))
    "local calls restore caller bindings between operands"
  assertTrue (runLocal 10000 world (initialCall "sequential" "reverse" [.atom "bad"]) ==
    .halted (.raised ⟨.error, .atom "function_clause"⟩))
    "match_fail function_clause removes stack argument metadata from the reason"
  let initial := initialCall "sequential" "reverse" [input]
  assertTrue (resume (stepLocal world) 10000 (runLocal 17 world initial) ==
    runLocal 10017 world initial) "fuel resumption preserves execution"
  match runLocal 1000 world (initialCall "sequential" "loop" []) with
  | .halted _ => throw (IO.userError "Recursive loop unexpectedly halted")
  | .exhausted state =>
      assertTrue (state.stack.length < 8) "tail recursion must not accumulate return frames"
  IO.println "Sequential machine regressions passed."
