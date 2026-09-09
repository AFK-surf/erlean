import Erlean.Core.Syntax

namespace Erlean.Examples

/-- Generated from a pinned OTP Core artifact by the erlean importer. -/
def importedElixirModule : Erlean.Core.Module :=
{ name := "Elixir.ErleanIdentity",
  exports := [("__info__", 1),
              ("empty", 0),
              ("identity", 1),
              ("module_info", 0),
              ("module_info", 1),
              ("pair", 2),
              ("prepend", 2)],
  functions := [{ name := "__info__",
                  params := [0],
                  body := Erlean.Core.Expr.caseE
                            (Erlean.Core.Expr.var 0)
                            [([Erlean.Core.Pattern.lit (Erlean.Core.Value.atom "module")],
                              Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                              Erlean.Core.Expr.lit (Erlean.Core.Value.atom "Elixir.ErleanIdentity")),
                             ([Erlean.Core.Pattern.lit (Erlean.Core.Value.atom "functions")],
                              Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                              Erlean.Core.Expr.lit
                                (Erlean.Core.Value.cons
                                  (Erlean.Core.Value.tuple
                                    [Erlean.Core.Value.atom "empty", Erlean.Core.Value.integer 0])
                                  (Erlean.Core.Value.cons
                                    (Erlean.Core.Value.tuple
                                      [Erlean.Core.Value.atom "identity", Erlean.Core.Value.integer 1])
                                    (Erlean.Core.Value.cons
                                      (Erlean.Core.Value.tuple
                                        [Erlean.Core.Value.atom "pair", Erlean.Core.Value.integer 2])
                                      (Erlean.Core.Value.cons
                                        (Erlean.Core.Value.tuple
                                          [Erlean.Core.Value.atom "prepend", Erlean.Core.Value.integer 2])
                                        (Erlean.Core.Value.nil)))))),
                             ([Erlean.Core.Pattern.lit (Erlean.Core.Value.atom "macros")],
                              Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                              Erlean.Core.Expr.lit (Erlean.Core.Value.nil)),
                             ([Erlean.Core.Pattern.lit (Erlean.Core.Value.atom "struct")],
                              Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                              Erlean.Core.Expr.lit (Erlean.Core.Value.atom "nil")),
                             ([Erlean.Core.Pattern.lit (Erlean.Core.Value.atom "exports_md5")],
                              Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                              Erlean.Core.Expr.lit
                                (Erlean.Core.Value.bitstring
                                  [true, false, true, true, true, true, true, true, false, false, false, false, true,
                                   true, true, true, false, true, false, false, true, false, false, false, false, true,
                                   false, true, true, true, true, true, false, true, true, false, true, false, false,
                                   false, false, true, true, true, true, false, false, false, false, false, false,
                                   false, false, true, false, true, true, true, true, false, false, true, true, false,
                                   false, false, false, false, true, true, true, true, true, true, false, true, true,
                                   false, false, false, false, true, true, false, true, true, false, false, true, true,
                                   false, true, true, false, false, true, true, true, true, true, true, true, true,
                                   false, false, true, false, true, true, true, true, false, false, true, false, false,
                                   false, false, true, false, true, true, false, false, true, true, true, false])),
                             ([Erlean.Core.Pattern.alias
                                 1
                                 (Erlean.Core.Pattern.lit (Erlean.Core.Value.atom "attributes"))],
                              Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                              Erlean.Core.Expr.call
                                (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "erlang"))
                                (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "get_module_info"))
                                [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "Elixir.ErleanIdentity"),
                                 Erlean.Core.Expr.var 1]),
                             ([Erlean.Core.Pattern.alias
                                 1
                                 (Erlean.Core.Pattern.lit (Erlean.Core.Value.atom "compile"))],
                              Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                              Erlean.Core.Expr.call
                                (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "erlang"))
                                (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "get_module_info"))
                                [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "Elixir.ErleanIdentity"),
                                 Erlean.Core.Expr.var 1]),
                             ([Erlean.Core.Pattern.alias 1 (Erlean.Core.Pattern.lit (Erlean.Core.Value.atom "md5"))],
                              Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                              Erlean.Core.Expr.call
                                (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "erlang"))
                                (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "get_module_info"))
                                [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "Elixir.ErleanIdentity"),
                                 Erlean.Core.Expr.var 1]),
                             ([Erlean.Core.Pattern.lit (Erlean.Core.Value.atom "deprecated")],
                              Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                              Erlean.Core.Expr.lit (Erlean.Core.Value.nil)),
                             ([Erlean.Core.Pattern.var 1],
                              Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                              Erlean.Core.Expr.primop
                                "match_fail"
                                [Erlean.Core.Expr.tuple
                                   [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "function_clause"),
                                    Erlean.Core.Expr.var 1]])] },
                { name := "empty",
                  params := [],
                  body := Erlean.Core.Expr.caseE
                            (Erlean.Core.Expr.values [])
                            [([],
                              Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                              Erlean.Core.Expr.lit (Erlean.Core.Value.nil)),
                             ([],
                              Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                              Erlean.Core.Expr.primop
                                "match_fail"
                                [Erlean.Core.Expr.lit
                                   (Erlean.Core.Value.tuple [Erlean.Core.Value.atom "function_clause"])])] },
                { name := "identity",
                  params := [0],
                  body := Erlean.Core.Expr.caseE
                            (Erlean.Core.Expr.var 0)
                            [([Erlean.Core.Pattern.var 1],
                              Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                              Erlean.Core.Expr.var 1),
                             ([Erlean.Core.Pattern.var 1],
                              Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                              Erlean.Core.Expr.primop
                                "match_fail"
                                [Erlean.Core.Expr.tuple
                                   [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "function_clause"),
                                    Erlean.Core.Expr.var 1]])] },
                { name := "pair",
                  params := [0, 1],
                  body := Erlean.Core.Expr.caseE
                            (Erlean.Core.Expr.values [Erlean.Core.Expr.var 0, Erlean.Core.Expr.var 1])
                            [([Erlean.Core.Pattern.var 2, Erlean.Core.Pattern.var 3],
                              Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                              Erlean.Core.Expr.tuple [Erlean.Core.Expr.var 2, Erlean.Core.Expr.var 3]),
                             ([Erlean.Core.Pattern.var 2, Erlean.Core.Pattern.var 3],
                              Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                              Erlean.Core.Expr.primop
                                "match_fail"
                                [Erlean.Core.Expr.tuple
                                   [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "function_clause"),
                                    Erlean.Core.Expr.var 2,
                                    Erlean.Core.Expr.var 3]])] },
                { name := "prepend",
                  params := [0, 1],
                  body := Erlean.Core.Expr.caseE
                            (Erlean.Core.Expr.values [Erlean.Core.Expr.var 0, Erlean.Core.Expr.var 1])
                            [([Erlean.Core.Pattern.var 2, Erlean.Core.Pattern.var 3],
                              Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                              Erlean.Core.Expr.cons (Erlean.Core.Expr.var 2) (Erlean.Core.Expr.var 3)),
                             ([Erlean.Core.Pattern.var 2, Erlean.Core.Pattern.var 3],
                              Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                              Erlean.Core.Expr.primop
                                "match_fail"
                                [Erlean.Core.Expr.tuple
                                   [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "function_clause"),
                                    Erlean.Core.Expr.var 2,
                                    Erlean.Core.Expr.var 3]])] },
                { name := "module_info",
                  params := [],
                  body := Erlean.Core.Expr.caseE
                            (Erlean.Core.Expr.values [])
                            [([],
                              Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                              Erlean.Core.Expr.call
                                (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "erlang"))
                                (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "get_module_info"))
                                [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "Elixir.ErleanIdentity")]),
                             ([],
                              Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                              Erlean.Core.Expr.primop
                                "match_fail"
                                [Erlean.Core.Expr.lit
                                   (Erlean.Core.Value.tuple [Erlean.Core.Value.atom "function_clause"])])] },
                { name := "module_info",
                  params := [0],
                  body := Erlean.Core.Expr.caseE
                            (Erlean.Core.Expr.var 0)
                            [([Erlean.Core.Pattern.var 1],
                              Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                              Erlean.Core.Expr.call
                                (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "erlang"))
                                (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "get_module_info"))
                                [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "Elixir.ErleanIdentity"),
                                 Erlean.Core.Expr.var 1]),
                             ([Erlean.Core.Pattern.var 1],
                              Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                              Erlean.Core.Expr.primop
                                "match_fail"
                                [Erlean.Core.Expr.tuple
                                   [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "function_clause"),
                                    Erlean.Core.Expr.var 1]])] }],
  closureCode := [] }

end Erlean.Examples
