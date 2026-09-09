import Erlean.Core.Syntax

namespace Erlean.Examples

/-- Generated from a pinned OTP Core artifact by the erlean importer. -/
def importedSequentialModule : Erlean.Core.Module :=
{ name := "sequential",
  exports := [("append", 2),
              ("arithmetic", 2),
              ("classify", 1),
              ("cons_order", 0),
              ("context", 1),
              ("identity", 1),
              ("loop", 0),
              ("module_info", 0),
              ("module_info", 1),
              ("reverse", 1),
              ("tuple_order", 0)],
  functions := [{ name := "reverse",
                  params := [0],
                  body := Erlean.Core.Expr.caseE
                            (Erlean.Core.Expr.var 0)
                            [([Erlean.Core.Pattern.var 1],
                              Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                              Erlean.Core.Expr.apply
                                (Erlean.Core.Expr.funRef "reverse_acc" 2)
                                [Erlean.Core.Expr.var 1, Erlean.Core.Expr.lit (Erlean.Core.Value.nil)]),
                             ([Erlean.Core.Pattern.var 1],
                              Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                              Erlean.Core.Expr.primop
                                "match_fail"
                                [Erlean.Core.Expr.tuple
                                   [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "function_clause"),
                                    Erlean.Core.Expr.var 1]])] },
                { name := "reverse_acc",
                  params := [0, 1],
                  body := Erlean.Core.Expr.caseE
                            (Erlean.Core.Expr.values [Erlean.Core.Expr.var 0, Erlean.Core.Expr.var 1])
                            [([Erlean.Core.Pattern.lit (Erlean.Core.Value.nil), Erlean.Core.Pattern.var 2],
                              Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                              Erlean.Core.Expr.var 2),
                             ([Erlean.Core.Pattern.cons (Erlean.Core.Pattern.var 2) (Erlean.Core.Pattern.var 3),
                               Erlean.Core.Pattern.var 4],
                              Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                              Erlean.Core.Expr.apply
                                (Erlean.Core.Expr.funRef "reverse_acc" 2)
                                [Erlean.Core.Expr.var 3,
                                 Erlean.Core.Expr.cons (Erlean.Core.Expr.var 2) (Erlean.Core.Expr.var 4)]),
                             ([Erlean.Core.Pattern.var 2, Erlean.Core.Pattern.var 3],
                              Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                              Erlean.Core.Expr.primop
                                "match_fail"
                                [Erlean.Core.Expr.tuple
                                   [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "function_clause"),
                                    Erlean.Core.Expr.var 2,
                                    Erlean.Core.Expr.var 3]])] },
                { name := "append",
                  params := [0, 1],
                  body := Erlean.Core.Expr.caseE
                            (Erlean.Core.Expr.values [Erlean.Core.Expr.var 0, Erlean.Core.Expr.var 1])
                            [([Erlean.Core.Pattern.lit (Erlean.Core.Value.nil), Erlean.Core.Pattern.var 2],
                              Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                              Erlean.Core.Expr.var 2),
                             ([Erlean.Core.Pattern.cons (Erlean.Core.Pattern.var 2) (Erlean.Core.Pattern.var 3),
                               Erlean.Core.Pattern.var 4],
                              Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                              Erlean.Core.Expr.letE
                                [5]
                                (Erlean.Core.Expr.apply
                                  (Erlean.Core.Expr.funRef "append" 2)
                                  [Erlean.Core.Expr.var 3, Erlean.Core.Expr.var 4])
                                (Erlean.Core.Expr.cons (Erlean.Core.Expr.var 2) (Erlean.Core.Expr.var 5))),
                             ([Erlean.Core.Pattern.var 2, Erlean.Core.Pattern.var 3],
                              Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                              Erlean.Core.Expr.primop
                                "match_fail"
                                [Erlean.Core.Expr.tuple
                                   [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "function_clause"),
                                    Erlean.Core.Expr.var 2,
                                    Erlean.Core.Expr.var 3]])] },
                { name := "classify",
                  params := [0],
                  body := Erlean.Core.Expr.caseE
                            (Erlean.Core.Expr.var 0)
                            [([Erlean.Core.Pattern.var 1],
                              Erlean.Core.Expr.call
                                (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "erlang"))
                                (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "is_integer"))
                                [Erlean.Core.Expr.var 1],
                              Erlean.Core.Expr.lit (Erlean.Core.Value.atom "integer")),
                             ([Erlean.Core.Pattern.var 1],
                              Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                              Erlean.Core.Expr.lit (Erlean.Core.Value.atom "other")),
                             ([Erlean.Core.Pattern.var 1],
                              Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                              Erlean.Core.Expr.primop
                                "match_fail"
                                [Erlean.Core.Expr.tuple
                                   [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "function_clause"),
                                    Erlean.Core.Expr.var 1]])] },
                { name := "arithmetic",
                  params := [0, 1],
                  body := Erlean.Core.Expr.caseE
                            (Erlean.Core.Expr.values [Erlean.Core.Expr.var 0, Erlean.Core.Expr.var 1])
                            [([Erlean.Core.Pattern.var 2, Erlean.Core.Pattern.var 3],
                              Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                              Erlean.Core.Expr.letE
                                [4]
                                (Erlean.Core.Expr.call
                                  (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "erlang"))
                                  (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "*"))
                                  [Erlean.Core.Expr.var 3, Erlean.Core.Expr.lit (Erlean.Core.Value.integer 2)])
                                (Erlean.Core.Expr.call
                                  (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "erlang"))
                                  (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "+"))
                                  [Erlean.Core.Expr.var 2, Erlean.Core.Expr.var 4])),
                             ([Erlean.Core.Pattern.var 2, Erlean.Core.Pattern.var 3],
                              Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                              Erlean.Core.Expr.primop
                                "match_fail"
                                [Erlean.Core.Expr.tuple
                                   [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "function_clause"),
                                    Erlean.Core.Expr.var 2,
                                    Erlean.Core.Expr.var 3]])] },
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
                { name := "context",
                  params := [0],
                  body := Erlean.Core.Expr.caseE
                            (Erlean.Core.Expr.var 0)
                            [([Erlean.Core.Pattern.var 1],
                              Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                              Erlean.Core.Expr.letE
                                [2]
                                (Erlean.Core.Expr.apply
                                  (Erlean.Core.Expr.funRef "identity" 1)
                                  [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "other")])
                                (Erlean.Core.Expr.letE
                                  [3]
                                  (Erlean.Core.Expr.apply
                                    (Erlean.Core.Expr.funRef "identity" 1)
                                    [Erlean.Core.Expr.var 1])
                                  (Erlean.Core.Expr.tuple
                                    [Erlean.Core.Expr.var 2, Erlean.Core.Expr.var 1, Erlean.Core.Expr.var 3]))),
                             ([Erlean.Core.Pattern.var 1],
                              Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                              Erlean.Core.Expr.primop
                                "match_fail"
                                [Erlean.Core.Expr.tuple
                                   [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "function_clause"),
                                    Erlean.Core.Expr.var 1]])] },
                { name := "tuple_order",
                  params := [],
                  body := Erlean.Core.Expr.caseE
                            (Erlean.Core.Expr.values [])
                            [([],
                              Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                              Erlean.Core.Expr.letE
                                [0]
                                (Erlean.Core.Expr.call
                                  (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "erlang"))
                                  (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "error"))
                                  [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "first")])
                                (Erlean.Core.Expr.letE
                                  [1]
                                  (Erlean.Core.Expr.call
                                    (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "erlang"))
                                    (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "error"))
                                    [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "second")])
                                  (Erlean.Core.Expr.tuple [Erlean.Core.Expr.var 0, Erlean.Core.Expr.var 1]))),
                             ([],
                              Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                              Erlean.Core.Expr.primop
                                "match_fail"
                                [Erlean.Core.Expr.lit
                                   (Erlean.Core.Value.tuple [Erlean.Core.Value.atom "function_clause"])])] },
                { name := "cons_order",
                  params := [],
                  body := Erlean.Core.Expr.caseE
                            (Erlean.Core.Expr.values [])
                            [([],
                              Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                              Erlean.Core.Expr.letE
                                [0]
                                (Erlean.Core.Expr.call
                                  (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "erlang"))
                                  (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "error"))
                                  [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "first")])
                                (Erlean.Core.Expr.letE
                                  [1]
                                  (Erlean.Core.Expr.call
                                    (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "erlang"))
                                    (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "error"))
                                    [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "second")])
                                  (Erlean.Core.Expr.cons (Erlean.Core.Expr.var 0) (Erlean.Core.Expr.var 1)))),
                             ([],
                              Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                              Erlean.Core.Expr.primop
                                "match_fail"
                                [Erlean.Core.Expr.lit
                                   (Erlean.Core.Value.tuple [Erlean.Core.Value.atom "function_clause"])])] },
                { name := "loop",
                  params := [],
                  body := Erlean.Core.Expr.caseE
                            (Erlean.Core.Expr.values [])
                            [([],
                              Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                              Erlean.Core.Expr.apply (Erlean.Core.Expr.funRef "loop" 0) []),
                             ([],
                              Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                              Erlean.Core.Expr.primop
                                "match_fail"
                                [Erlean.Core.Expr.lit
                                   (Erlean.Core.Value.tuple [Erlean.Core.Value.atom "function_clause"])])] },
                { name := "module_info",
                  params := [],
                  body := Erlean.Core.Expr.caseE
                            (Erlean.Core.Expr.values [])
                            [([],
                              Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                              Erlean.Core.Expr.call
                                (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "erlang"))
                                (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "get_module_info"))
                                [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "sequential")]),
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
                                [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "sequential"), Erlean.Core.Expr.var 1]),
                             ([Erlean.Core.Pattern.var 1],
                              Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                              Erlean.Core.Expr.primop
                                "match_fail"
                                [Erlean.Core.Expr.tuple
                                   [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "function_clause"),
                                    Erlean.Core.Expr.var 1]])] }] }

end Erlean.Examples
