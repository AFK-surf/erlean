import Erlean.Import.Emit

open Erlean.Core

/-!
Print a generated serialization stress test for a second, kernel-checked Lean
compilation. This tests exact syntax preservation, not execution or acceptance
of the synthetic module by the Core feature-profile checker.
-/

private def constructors : Expr :=
  .tuple [
    .lit (.tuple [.integer (-7), .atom "quoted\"name", .bitstring [true, false]]),
    .var 7,
    .values [.var 0, .lit .nil],
    .letE [3, 1] (.values [.var 0, .var 2]) (.var 3),
    .seq (.lit (.atom "first")) (.var 0),
    .cons (.var 0) (.lit .nil),
    .tuple [],
    .map [false, true] [.var 0, .lit (.atom "a"), .var 1, .lit (.integer 2), .var 3],
    .bytes [.lit (.integer 255), .var 0],
    .call (.lit (.atom "erlang")) (.lit (.atom "is_map")) [.var 0],
    .apply (.funRef "quoted\"function" 2) [.var 1, .var 0],
    .primop "match_fail" [.var 0],
    .funRef "fixture_0" 1,
    .makeClosure 1,
    .letrec [(5, 1), (3, 0)] (.apply (.var 5) [.var 3]),
    .tryE (.var 0) [3, 2] (.var 3) [4, 5, 6] (.tuple [.var 4, .var 6]),
    .catchE (.var 0),
    .caseE (.var 0) [
      ([.alias 2 (.tuple [.var 3, .wild])], .lit (.atom "true"), .var 2),
      ([.cons (.lit (.integer 0)) (.var 4)], .lit (.atom "false"), .var 4),
      ([.map [.atom "a"] [.bytes [.var 5]]], .lit (.atom "true"), .var 5)]
  ]

private def largeBody : Expr :=
  .caseE (.var 0) (List.replicate 32
    ([.var 1], .lit (.atom "true"),
      .tuple (List.replicate 64 (.seq (.lit (.integer 42)) (.var 1)))))

/-- One large descendant forces every child-bearing renderer branch without
    multiplying the stress body's size. This is serialization-only syntax. -/
private def wrappedBody : Expr :=
  .letE [3, 1] (.values [])
    (.seq (.lit (.atom "before"))
      (.cons (.lit (.integer 1))
        (.values [
          .map [false] [.lit (.map []), .lit (.atom "key"),
            .bytes [
              .call (.lit (.atom "module")) (.lit (.atom "function")) [
                .apply (.funRef "callee" 1) [
                  .primop "synthetic" [
                    .letrec [(5, 1), (3, 0)]
                      (.tryE (.lit .nil) [6] (.catchE largeBody) [7, 8, 9] (.var 8))]]]]]])))

private def smallFunction (index : Nat) : FunctionDef :=
  { name := "fixture_" ++ toString index
    params := [0]
    body := .tuple [.lit (.integer (Int.ofNat index)), .var 0] }

private def closures : List ClosureDef := [
  { params := [0, 4]
    body := .tuple [.var 7, .var 2, .apply (.var 5) [.var 0, .var 4]]
    outerScope := [7, 2]
    recursiveBindings := [(5, 1), (3, 0)] },
  { params := [0]
    body := .apply (.var 3) [.var 0]
    outerScope := [9, 2, 7]
    recursiveBindings := [(3, 0)] }
]

private def stress : Erlean.Core.Module :=
  { name := "emitter_stress"
    exports := (List.range 96).map (fun index => ("fixture_" ++ toString index, 1))
    functions := (List.range 96).map smallFunction ++ [
      { name := "large", params := [0], body := wrappedBody },
      { name := "constructors", params := [0, 1, 2], body := constructors }]
    closureCode := closures }

def main : IO Unit := do
  IO.print (Erlean.Import.Emit.moduleSource stress "importedStress")
  IO.println ""
  IO.println "namespace EmitterRegression"
  IO.println "open Erlean.Core"
  -- The small constructor/closure literals form an independent unsplit
  -- baseline. Large function and table expectations use compact expressions.
  IO.println s!"private def expectedConstructors : Expr :=\n{reprStr constructors}"
  IO.println s!"private def expectedClosures : List ClosureDef :=\n{reprStr closures}"
  IO.println "private def expectedSmall (index : Nat) : FunctionDef :="
  IO.println "  { name := \"fixture_\" ++ toString index, params := [0],"
  IO.println "    body := .tuple [.lit (.integer (Int.ofNat index)), .var 0] }"
  IO.println "private def expectedLarge : Expr :="
  IO.println "  .caseE (.var 0) (List.replicate 32"
  IO.println "    ([.var 1], .lit (.atom \"true\"),"
  IO.println "      .tuple (List.replicate 64 (.seq (.lit (.integer 42)) (.var 1)))))"
  IO.println "private def expectedWrapped : Expr :="
  IO.println "  .letE [3, 1] (.values [])"
  IO.println "    (.seq (.lit (.atom \"before\"))"
  IO.println "      (.cons (.lit (.integer 1))"
  IO.println "        (.values ["
  IO.println "          .map [false] [.lit (.map []), .lit (.atom \"key\"),"
  IO.println "            .bytes ["
  IO.println "              .call (.lit (.atom \"module\")) (.lit (.atom \"function\")) ["
  IO.println "                .apply (.funRef \"callee\" 1) ["
  IO.println "                  .primop \"synthetic\" ["
  IO.println "                    .letrec [(5, 1), (3, 0)]"
  IO.println "                      (.tryE (.lit .nil) [6] (.catchE expectedLarge) [7, 8, 9] (.var 8))]]]]]])))"
  IO.println "private def expected : Erlean.Core.Module :="
  IO.println "  { name := \"emitter_stress\""
  IO.println "    exports := (List.range 96).map (fun index => (\"fixture_\" ++ toString index, 1))"
  IO.println "    functions := (List.range 96).map expectedSmall ++ ["
  IO.println "      { name := \"large\", params := [0], body := expectedWrapped },"
  IO.println "      { name := \"constructors\", params := [0, 1, 2], body := expectedConstructors }]"
  IO.println "    closureCode := expectedClosures }"
  IO.println ""
  IO.println "/-- Kernel-checked equality of the entire emitted AST, including tables and capture metadata. -/"
  IO.println "example : Erlean.Examples.importedStress = expected := rfl"
  IO.println "end EmitterRegression"
