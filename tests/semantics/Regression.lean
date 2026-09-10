import Erlean.Import.Lower
import Erlean.Semantics.Machine
import Erlean.Logic.Controller

namespace ControllerRegression

open Erlean.Logic.Controller

private def step (state : Nat) (emit : Bool) : Nat × List Nat :=
  (state + 1, if emit then [state, state + 1] else [])

private def transition (state : Nat) (event : Bool) (next : Nat) (effects : List Nat) : Prop :=
  (next, effects) = step state event

-- Empty and multiple-effect steps form a real trace, with ordered outputs.
example : Trace transition 0 [false, true] 2 [1, 2] := by
  have first : transition 0 false 1 [] := rfl
  have second : transition 1 true 2 [1, 2] := rfl
  exact .cons first (.cons second (.nil 2))

example (execution : Trace transition 0 [false, true] finish effects) :
    (finish, effects) = (2, [1, 2]) := by
  simpa [step, run] using Trace.exact step transition (fun _ _ _ _ h => h) execution

example (execution : Trace transition state [] finish effects) :
    (finish, effects) = (state, []) :=
  Trace.exact step transition (fun _ _ _ _ h => h) execution

end ControllerRegression

open Erlean.Core Erlean.Import Erlean.Semantics

private def assertTrue (condition : Bool) (label : String) : IO Unit :=
  unless condition do throw (IO.userError label)

private def expect (world : CodeWorld) (expr : Expr) (result : Outcome) (label : String) : IO Unit :=
  let initial : LocalState := {control := .eval expr, context := ⟨"test", []⟩}
  assertTrue (runLocal 1000 world initial == .halted result) label

private def callBif (name : String) (args : List Expr) : Expr :=
  .call (.lit (.atom "erlang")) (.lit (.atom name)) args

private def callMapBif (name : String) (args : List Expr) : Expr :=
  .call (.lit (.atom "maps")) (.lit (.atom name)) args

/-- A binary value built from the UTF-8 bytes of its text. -/
private def bytes (text : String) : Value :=
  .bitstring (text.toUTF8.toList.flatMap fun byte => encodeByte (Int.ofNat byte.toNat))

private def listValue (values : List Value) : Value := values.foldr Value.cons .nil

def main : IO Unit := do
  expect [] (callBif "++" [.lit .nil, .lit (.atom "tail")])
    (.returned [.atom "tail"]) "append permits an arbitrary right tail"
  expect [] (callBif "++" [.lit (.cons (.integer 1) .nil), .lit (.atom "tail")])
    (.returned [.cons (.integer 1) (.atom "tail")]) "append can construct an improper result"
  expect [] (callBif "++" [.lit (.cons (.integer 1) .nil),
      .lit (.cons (.integer 2) .nil)])
    (.returned [.cons (.integer 1) (.cons (.integer 2) .nil)])
    "append preserves left then right element order"
  expect [] (callBif "++" [.lit (.cons (.integer 1) (.atom "tail")), .lit .nil])
    (.raised ⟨.error, .atom "badarg"⟩) "append rejects an improper left list"
  expect [] (callBif "++" [.lit (.atom "left"), .lit .nil])
    (.raised ⟨.error, .atom "badarg"⟩) "append rejects a non-list left operand"
  expect [] (callBif "++" [.lit .nil])
    (.fault (.unsupported "BIF erlang:++/1")) "append does not invent unsupported arities"
  expect [] (callBif "++" [.lit .nil, .lit (.exceptionInfo "error")])
    (.fault (.unsupported "BIF observation of opaque exception information"))
    "append does not expose protected exception information"
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
  expect [] (callBif "<" [.lit (.integer 1), .lit (.integer 2)])
    (.returned [.atom "true"]) "integer less-than accepts a smaller left operand"
  expect [] (callBif "<" [.lit (.integer 2), .lit (.integer 2)])
    (.returned [.atom "false"]) "integer less-than is strict"
  expect [] (callBif ">" [.lit (.integer 2), .lit (.integer 1)])
    (.returned [.atom "true"]) "integer greater-than accepts a greater left operand"
  expect [] (callBif ">=" [.lit (.integer (-3)), .lit (.integer (-3))])
    (.returned [.atom "true"]) "integer greater-or-equal includes equality"
  expect [] (callBif ">=" [.lit (.integer 2), .lit (.integer 3)])
    (.returned [.atom "false"]) "integer greater-or-equal rejects a greater right operand"
  expect [] (callBif "<" [.lit (.atom "a"), .lit (.atom "b")])
    (.fault (.unsupported "BIF erlang:</2"))
    "comparisons outside the integer profile stay model faults"
  expect [] (callBif "min" [.lit (.integer 3), .lit (.integer 5)])
    (.returned [.integer 3]) "integer minimum selects the smaller operand"
  expect [] (callBif "max" [.lit (.integer 3), .lit (.integer 5)])
    (.returned [.integer 5]) "integer maximum selects the larger operand"
  expect [] (callBif "min" [.lit (.atom "a"), .lit (.integer 1)])
    (.fault (.unsupported "BIF erlang:min/2"))
    "minimum outside the integer profile stays a model fault"
  expect [] (callBif "or" [.lit (.atom "false"), .lit (.atom "true")])
    (.returned [.atom "true"]) "boolean or accepts a true right operand"
  expect [] (callBif "or" [.lit (.atom "false"), .lit (.atom "false")])
    (.returned [.atom "false"]) "boolean or rejects two false operands"
  expect [] (callBif "or" [.lit (.atom "nil"), .lit (.atom "true")])
    (.raised ⟨.error, .atom "badarg"⟩) "boolean or rejects a non-boolean operand"
  expect [] (callBif "not" [.lit (.atom "true")])
    (.returned [.atom "false"]) "boolean not negates true"
  expect [] (callBif "not" [.lit (.atom "nil")])
    (.raised ⟨.error, .atom "badarg"⟩) "boolean not rejects a non-boolean operand"
  expect [] (callBif "not" [])
    (.fault (.unsupported "BIF erlang:not/0"))
    "boolean not does not invent unsupported arities"
  expect [] (callBif "is_list" [.lit (listValue [.integer 1, .integer 2])])
    (.returned [.atom "true"]) "is_list accepts a proper list"
  expect [] (callBif "is_list" [.lit .nil])
    (.returned [.atom "true"]) "is_list accepts the empty list"
  expect [] (callBif "is_list" [.lit (.cons (.integer 1) (.atom "tail"))])
    (.returned [.atom "true"])
    "is_list tests only the outer constructor and does not require a proper tail"
  expect [] (callBif "is_list" [.lit (.atom "a")])
    (.returned [.atom "false"]) "is_list rejects a non-list"
  expect [] (callBif "is_boolean" [.lit (.atom "false")])
    (.returned [.atom "true"]) "is_boolean accepts false"
  expect [] (callBif "is_boolean" [.lit (.atom "nil")])
    (.returned [.atom "false"]) "is_boolean rejects the atom nil"
  expect [] (callBif "is_float" [.lit (.floatBits 0)])
    (.returned [.atom "true"]) "is_float accepts a finite float encoding"
  expect [] (callBif "is_float" [.lit (.integer 0)])
    (.returned [.atom "false"]) "is_float rejects an integer"
  expect [] (callBif "byte_size" [.lit (bytes "ab")])
    (.returned [.integer 2]) "byte_size counts whole bytes"
  expect [] (callBif "byte_size" [.lit (.bitstring [])])
    (.returned [.integer 0]) "byte_size accepts the empty binary"
  expect [] (callBif "byte_size" [.lit (.bitstring [true])])
    (.raised ⟨.error, .atom "badarg"⟩) "byte_size rejects a partial byte"
  expect [] (callBif "length" [.lit (listValue [.integer 1, .integer 2, .integer 3])])
    (.returned [.integer 3]) "length counts proper list elements"
  expect [] (callBif "length" [.lit (.cons (.integer 1) (.atom "tail"))])
    (.raised ⟨.error, .atom "badarg"⟩) "length rejects an improper list"
  expect [] (callBif "binary_to_list" [.lit (bytes "AB")])
    (.returned [listValue [.integer 65, .integer 66]])
    "binary_to_list yields byte integers in order"
  expect [] (callBif "binary_to_list" [.lit (.integer 1)])
    (.raised ⟨.error, .atom "badarg"⟩) "binary_to_list rejects a non-binary"
  expect [] (callBif "iolist_to_binary" [.lit (listValue [.integer 65, bytes "B"])])
    (.returned [bytes "AB"]) "iolist_to_binary flattens nested binaries"
  expect [] (callBif "iolist_to_binary" [.lit (listValue [.integer 65,
      listValue [.integer 66]])])
    (.returned [bytes "AB"]) "iolist_to_binary flattens nested lists"
  expect [] (callBif "iolist_to_binary" [.lit .nil])
    (.returned [.bitstring []]) "iolist_to_binary accepts the empty list"
  expect [] (callBif "iolist_to_binary" [.lit (listValue [.integer 256])])
    (.raised ⟨.error, .atom "badarg"⟩) "iolist_to_binary rejects an out-of-range byte"
  expect [] (callBif "iolist_to_binary" [.lit (.cons (.integer 65) (.atom "tail"))])
    (.raised ⟨.error, .atom "badarg"⟩) "iolist_to_binary rejects an improper tail"
  let twoKeys : Value := .map [(.atom "a", .integer 1), (.atom "b", .integer 2)]
  expect [] (callMapBif "next" [callMapBif "iterator" [.lit twoKeys, .lit (.atom "ordered")]])
    (.returned [.tuple [.atom "a", .integer 1, .iterator [(.atom "b", .integer 2)]]])
    "ordered iteration yields canonical entry order"
  expect [] (callMapBif "next" [callMapBif "iterator" [.lit twoKeys, .lit (.atom "reversed")]])
    (.returned [.tuple [.atom "b", .integer 2, .iterator [(.atom "a", .integer 1)]]])
    "reversed iteration yields reverse canonical order"
  expect [] (callMapBif "next" [callMapBif "iterator" [.lit (.map []), .lit (.atom "ordered")]])
    (.returned [.atom "none"]) "an exhausted iterator reports none"
  expect [] (callMapBif "next" [.lit (.atom "not_an_iterator")])
    (.raised ⟨.error, .atom "badarg"⟩) "maps:next rejects a non-iterator operand"
  expect [] (callMapBif "iterator" [.lit twoKeys, .lit (.atom "sideways")])
    (.raised ⟨.error, .atom "badarg"⟩) "maps:iterator rejects an unknown order"
  expect [] (callMapBif "keys" [.lit twoKeys])
    (.returned [listValue [.atom "a", .atom "b"]]) "maps:keys lists canonical keys"
  expect [] (callMapBif "values" [.lit twoKeys])
    (.returned [listValue [.integer 1, .integer 2]])
    "maps:values lists values in canonical key order"
  expect [] (callMapBif "with" [.lit (listValue [.atom "b"]), .lit twoKeys])
    (.returned [.map [(.atom "b", .integer 2)]]) "maps:with keeps only named keys"
  expect [] (callMapBif "with" [.lit (listValue [.atom "missing"]), .lit twoKeys])
    (.returned [.map []]) "maps:with drops absent keys"
  expect [] (callMapBif "with" [.lit (.atom "a"), .lit twoKeys])
    (.raised ⟨.error, .atom "badarg"⟩) "maps:with rejects a non-list key operand"
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
