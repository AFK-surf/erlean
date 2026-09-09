import Erlean.Core.Syntax

namespace Erlean.Examples

/-- Generated from a pinned OTP Core artifact by the erlean importer. -/
def importedModularClient : Erlean.Core.Module :=
{ name := "modular_client",
  exports := [("module_info", 0), ("module_info", 1), ("relay", 1)],
  functions := [{ name := "relay",
                  params := [0],
                  body := Erlean.Core.Expr.caseE
                            (Erlean.Core.Expr.var 0)
                            [([Erlean.Core.Pattern.var 1],
                              Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                              Erlean.Core.Expr.call
                                (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "identity"))
                                (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "identity"))
                                [Erlean.Core.Expr.var 1]),
                             ([Erlean.Core.Pattern.var 1],
                              Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                              Erlean.Core.Expr.primop
                                "match_fail"
                                [Erlean.Core.Expr.tuple
                                   [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "function_clause"),
                                    Erlean.Core.Expr.var 1]])] },
                { name := "module_info",
                  params := [],
                  body := Erlean.Core.Expr.caseE
                            (Erlean.Core.Expr.values [])
                            [([],
                              Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                              Erlean.Core.Expr.call
                                (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "erlang"))
                                (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "get_module_info"))
                                [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "modular_client")]),
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
                                [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "modular_client"),
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
