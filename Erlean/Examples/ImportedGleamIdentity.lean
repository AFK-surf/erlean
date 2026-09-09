import Erlean.Core.Syntax

namespace Erlean.Examples

/-- Generated from a pinned OTP Core artifact by the erlean importer. -/
def importedGleamModule : Erlean.Core.Module :=
{ name := "gleam_identity",
  exports := [("empty", 0), ("identity", 1), ("module_info", 0), ("module_info", 1), ("pair", 2), ("prepend", 2)],
  functions := [{ name := "identity",
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
                                [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "gleam_identity")]),
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
                                [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "gleam_identity"),
                                 Erlean.Core.Expr.var 1]),
                             ([Erlean.Core.Pattern.var 1],
                              Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                              Erlean.Core.Expr.primop
                                "match_fail"
                                [Erlean.Core.Expr.tuple
                                   [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "function_clause"),
                                    Erlean.Core.Expr.var 1]])] }] }

end Erlean.Examples
