import Erlean.Core.Syntax

namespace Erlean.Examples

/-- Generated from a pinned OTP Core artifact by the erlean importer. -/
def importedDijkstraModule : Erlean.Core.Module :=
{ name := "dijkstra",
  exports := [("distances", 2), ("module_info", 0), ("module_info", 1)],
  functions := [{ name := "distances",
                  params := [0, 1],
                  body := Erlean.Core.Expr.caseE
                            (Erlean.Core.Expr.values [Erlean.Core.Expr.var 0, Erlean.Core.Expr.var 1])
                            [([Erlean.Core.Pattern.var 2, Erlean.Core.Pattern.var 3],
                              Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                              Erlean.Core.Expr.caseE
                                (Erlean.Core.Expr.apply
                                  (Erlean.Core.Expr.funRef "nonnegative_integer" 1)
                                  [Erlean.Core.Expr.var 2])
                                [([Erlean.Core.Pattern.lit (Erlean.Core.Value.atom "true")],
                                  Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                                  Erlean.Core.Expr.caseE
                                    (Erlean.Core.Expr.apply
                                      (Erlean.Core.Expr.funRef "valid_edges" 1)
                                      [Erlean.Core.Expr.var 3])
                                    [([Erlean.Core.Pattern.lit (Erlean.Core.Value.atom "true")],
                                      Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                                      Erlean.Core.Expr.letE
                                        [4]
                                        (Erlean.Core.Expr.apply
                                          (Erlean.Core.Expr.funRef "search" 3)
                                          [Erlean.Core.Expr.cons
                                             (Erlean.Core.Expr.tuple
                                               [Erlean.Core.Expr.var 2,
                                                Erlean.Core.Expr.lit (Erlean.Core.Value.integer 0)])
                                             (Erlean.Core.Expr.lit (Erlean.Core.Value.nil)),
                                           Erlean.Core.Expr.var 3,
                                           Erlean.Core.Expr.lit (Erlean.Core.Value.nil)])
                                        (Erlean.Core.Expr.apply
                                          (Erlean.Core.Expr.funRef "reverse" 2)
                                          [Erlean.Core.Expr.var 4, Erlean.Core.Expr.lit (Erlean.Core.Value.nil)])),
                                     ([Erlean.Core.Pattern.lit (Erlean.Core.Value.atom "false")],
                                      Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                                      Erlean.Core.Expr.call
                                        (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "erlang"))
                                        (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "error"))
                                        [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "badarg")]),
                                     ([Erlean.Core.Pattern.var 4],
                                      Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                                      Erlean.Core.Expr.primop
                                        "match_fail"
                                        [Erlean.Core.Expr.tuple
                                           [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "case_clause"),
                                            Erlean.Core.Expr.var 4]])]),
                                 ([Erlean.Core.Pattern.lit (Erlean.Core.Value.atom "false")],
                                  Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                                  Erlean.Core.Expr.call
                                    (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "erlang"))
                                    (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "error"))
                                    [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "badarg")]),
                                 ([Erlean.Core.Pattern.var 4],
                                  Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                                  Erlean.Core.Expr.primop
                                    "match_fail"
                                    [Erlean.Core.Expr.tuple
                                       [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "case_clause"),
                                        Erlean.Core.Expr.var 4]])]),
                             ([Erlean.Core.Pattern.var 2, Erlean.Core.Pattern.var 3],
                              Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                              Erlean.Core.Expr.primop
                                "match_fail"
                                [Erlean.Core.Expr.tuple
                                   [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "function_clause"),
                                    Erlean.Core.Expr.var 2,
                                    Erlean.Core.Expr.var 3]])] },
                { name := "nonnegative_integer",
                  params := [0],
                  body := Erlean.Core.Expr.caseE
                            (Erlean.Core.Expr.var 0)
                            [([Erlean.Core.Pattern.var 1],
                              Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                              Erlean.Core.Expr.caseE
                                (Erlean.Core.Expr.call
                                  (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "erlang"))
                                  (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "is_integer"))
                                  [Erlean.Core.Expr.var 1])
                                [([Erlean.Core.Pattern.lit (Erlean.Core.Value.atom "true")],
                                  Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                                  Erlean.Core.Expr.call
                                    (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "erlang"))
                                    (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "=<"))
                                    [Erlean.Core.Expr.lit (Erlean.Core.Value.integer 0), Erlean.Core.Expr.var 1]),
                                 ([Erlean.Core.Pattern.lit (Erlean.Core.Value.atom "false")],
                                  Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                                  Erlean.Core.Expr.lit (Erlean.Core.Value.atom "false")),
                                 ([Erlean.Core.Pattern.var 2],
                                  Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                                  Erlean.Core.Expr.primop
                                    "match_fail"
                                    [Erlean.Core.Expr.tuple
                                       [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "case_clause"),
                                        Erlean.Core.Expr.var 2]])]),
                             ([Erlean.Core.Pattern.var 1],
                              Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                              Erlean.Core.Expr.primop
                                "match_fail"
                                [Erlean.Core.Expr.tuple
                                   [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "function_clause"),
                                    Erlean.Core.Expr.var 1]])] },
                { name := "valid_edges",
                  params := [0],
                  body := Erlean.Core.Expr.caseE
                            (Erlean.Core.Expr.var 0)
                            [([Erlean.Core.Pattern.lit (Erlean.Core.Value.nil)],
                              Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                              Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true")),
                             ([Erlean.Core.Pattern.cons
                                 (Erlean.Core.Pattern.tuple
                                   [Erlean.Core.Pattern.var 1, Erlean.Core.Pattern.var 2, Erlean.Core.Pattern.var 3])
                                 (Erlean.Core.Pattern.var 4)],
                              Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                              Erlean.Core.Expr.caseE
                                (Erlean.Core.Expr.apply
                                  (Erlean.Core.Expr.funRef "nonnegative_integer" 1)
                                  [Erlean.Core.Expr.var 1])
                                [([Erlean.Core.Pattern.lit (Erlean.Core.Value.atom "false")],
                                  Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                                  Erlean.Core.Expr.lit (Erlean.Core.Value.atom "false")),
                                 ([Erlean.Core.Pattern.lit (Erlean.Core.Value.atom "true")],
                                  Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                                  Erlean.Core.Expr.caseE
                                    (Erlean.Core.Expr.apply
                                      (Erlean.Core.Expr.funRef "nonnegative_integer" 1)
                                      [Erlean.Core.Expr.var 2])
                                    [([Erlean.Core.Pattern.lit (Erlean.Core.Value.atom "false")],
                                      Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                                      Erlean.Core.Expr.lit (Erlean.Core.Value.atom "false")),
                                     ([Erlean.Core.Pattern.lit (Erlean.Core.Value.atom "true")],
                                      Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                                      Erlean.Core.Expr.caseE
                                        (Erlean.Core.Expr.apply
                                          (Erlean.Core.Expr.funRef "nonnegative_integer" 1)
                                          [Erlean.Core.Expr.var 3])
                                        [([Erlean.Core.Pattern.lit (Erlean.Core.Value.atom "false")],
                                          Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                                          Erlean.Core.Expr.lit (Erlean.Core.Value.atom "false")),
                                         ([Erlean.Core.Pattern.lit (Erlean.Core.Value.atom "true")],
                                          Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                                          Erlean.Core.Expr.apply
                                            (Erlean.Core.Expr.funRef "valid_edges" 1)
                                            [Erlean.Core.Expr.var 4]),
                                         ([Erlean.Core.Pattern.var 5],
                                          Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                                          Erlean.Core.Expr.primop
                                            "match_fail"
                                            [Erlean.Core.Expr.tuple
                                               [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "case_clause"),
                                                Erlean.Core.Expr.var 5]])]),
                                     ([Erlean.Core.Pattern.var 5],
                                      Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                                      Erlean.Core.Expr.primop
                                        "match_fail"
                                        [Erlean.Core.Expr.tuple
                                           [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "case_clause"),
                                            Erlean.Core.Expr.var 5]])]),
                                 ([Erlean.Core.Pattern.var 5],
                                  Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                                  Erlean.Core.Expr.primop
                                    "match_fail"
                                    [Erlean.Core.Expr.tuple
                                       [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "case_clause"),
                                        Erlean.Core.Expr.var 5]])]),
                             ([Erlean.Core.Pattern.var 1],
                              Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                              Erlean.Core.Expr.lit (Erlean.Core.Value.atom "false")),
                             ([Erlean.Core.Pattern.var 1],
                              Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                              Erlean.Core.Expr.primop
                                "match_fail"
                                [Erlean.Core.Expr.tuple
                                   [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "function_clause"),
                                    Erlean.Core.Expr.var 1]])] },
                { name := "search",
                  params := [0, 1, 2],
                  body := Erlean.Core.Expr.caseE
                            (Erlean.Core.Expr.values
                              [Erlean.Core.Expr.var 0, Erlean.Core.Expr.var 1, Erlean.Core.Expr.var 2])
                            [([Erlean.Core.Pattern.lit (Erlean.Core.Value.nil),
                               Erlean.Core.Pattern.var 3,
                               Erlean.Core.Pattern.var 4],
                              Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                              Erlean.Core.Expr.var 4),
                             ([Erlean.Core.Pattern.cons
                                 (Erlean.Core.Pattern.tuple [Erlean.Core.Pattern.var 3, Erlean.Core.Pattern.var 4])
                                 (Erlean.Core.Pattern.var 5),
                               Erlean.Core.Pattern.var 6,
                               Erlean.Core.Pattern.var 7],
                              Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                              Erlean.Core.Expr.caseE
                                (Erlean.Core.Expr.apply
                                  (Erlean.Core.Expr.funRef "settled" 2)
                                  [Erlean.Core.Expr.var 3, Erlean.Core.Expr.var 7])
                                [([Erlean.Core.Pattern.lit (Erlean.Core.Value.atom "true")],
                                  Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                                  Erlean.Core.Expr.apply
                                    (Erlean.Core.Expr.funRef "search" 3)
                                    [Erlean.Core.Expr.var 5, Erlean.Core.Expr.var 6, Erlean.Core.Expr.var 7]),
                                 ([Erlean.Core.Pattern.lit (Erlean.Core.Value.atom "false")],
                                  Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                                  Erlean.Core.Expr.caseE
                                    (Erlean.Core.Expr.apply
                                      (Erlean.Core.Expr.funRef "expand" 4)
                                      [Erlean.Core.Expr.var 3,
                                       Erlean.Core.Expr.var 4,
                                       Erlean.Core.Expr.var 6,
                                       Erlean.Core.Expr.var 5])
                                    [([Erlean.Core.Pattern.tuple
                                         [Erlean.Core.Pattern.var 8, Erlean.Core.Pattern.var 9]],
                                      Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                                      Erlean.Core.Expr.apply
                                        (Erlean.Core.Expr.funRef "search" 3)
                                        [Erlean.Core.Expr.var 8,
                                         Erlean.Core.Expr.var 9,
                                         Erlean.Core.Expr.cons
                                           (Erlean.Core.Expr.tuple [Erlean.Core.Expr.var 3, Erlean.Core.Expr.var 4])
                                           (Erlean.Core.Expr.var 7)]),
                                     ([Erlean.Core.Pattern.var 8],
                                      Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                                      Erlean.Core.Expr.primop
                                        "match_fail"
                                        [Erlean.Core.Expr.tuple
                                           [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "badmatch"),
                                            Erlean.Core.Expr.var 8]])]),
                                 ([Erlean.Core.Pattern.var 8],
                                  Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                                  Erlean.Core.Expr.primop
                                    "match_fail"
                                    [Erlean.Core.Expr.tuple
                                       [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "case_clause"),
                                        Erlean.Core.Expr.var 8]])]),
                             ([Erlean.Core.Pattern.var 3, Erlean.Core.Pattern.var 4, Erlean.Core.Pattern.var 5],
                              Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                              Erlean.Core.Expr.primop
                                "match_fail"
                                [Erlean.Core.Expr.tuple
                                   [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "function_clause"),
                                    Erlean.Core.Expr.var 3,
                                    Erlean.Core.Expr.var 4,
                                    Erlean.Core.Expr.var 5]])] },
                { name := "settled",
                  params := [0, 1],
                  body := Erlean.Core.Expr.caseE
                            (Erlean.Core.Expr.values [Erlean.Core.Expr.var 0, Erlean.Core.Expr.var 1])
                            [([Erlean.Core.Pattern.var 2, Erlean.Core.Pattern.lit (Erlean.Core.Value.nil)],
                              Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                              Erlean.Core.Expr.lit (Erlean.Core.Value.atom "false")),
                             ([Erlean.Core.Pattern.var 2,
                               Erlean.Core.Pattern.cons
                                 (Erlean.Core.Pattern.tuple [Erlean.Core.Pattern.var 3, Erlean.Core.Pattern.var 4])
                                 (Erlean.Core.Pattern.var 5)],
                              Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                              Erlean.Core.Expr.caseE
                                (Erlean.Core.Expr.call
                                  (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "erlang"))
                                  (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "=:="))
                                  [Erlean.Core.Expr.var 2, Erlean.Core.Expr.var 3])
                                [([Erlean.Core.Pattern.lit (Erlean.Core.Value.atom "true")],
                                  Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                                  Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true")),
                                 ([Erlean.Core.Pattern.lit (Erlean.Core.Value.atom "false")],
                                  Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                                  Erlean.Core.Expr.apply
                                    (Erlean.Core.Expr.funRef "settled" 2)
                                    [Erlean.Core.Expr.var 2, Erlean.Core.Expr.var 5]),
                                 ([Erlean.Core.Pattern.var 6],
                                  Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                                  Erlean.Core.Expr.primop
                                    "match_fail"
                                    [Erlean.Core.Expr.tuple
                                       [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "case_clause"),
                                        Erlean.Core.Expr.var 6]])]),
                             ([Erlean.Core.Pattern.var 2, Erlean.Core.Pattern.var 3],
                              Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                              Erlean.Core.Expr.primop
                                "match_fail"
                                [Erlean.Core.Expr.tuple
                                   [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "function_clause"),
                                    Erlean.Core.Expr.var 2,
                                    Erlean.Core.Expr.var 3]])] },
                { name := "expand",
                  params := [0, 1, 2, 3],
                  body := Erlean.Core.Expr.caseE
                            (Erlean.Core.Expr.values
                              [Erlean.Core.Expr.var 0,
                               Erlean.Core.Expr.var 1,
                               Erlean.Core.Expr.var 2,
                               Erlean.Core.Expr.var 3])
                            [([Erlean.Core.Pattern.var 4,
                               Erlean.Core.Pattern.var 5,
                               Erlean.Core.Pattern.lit (Erlean.Core.Value.nil),
                               Erlean.Core.Pattern.var 6],
                              Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                              Erlean.Core.Expr.tuple
                                [Erlean.Core.Expr.var 6, Erlean.Core.Expr.lit (Erlean.Core.Value.nil)]),
                             ([Erlean.Core.Pattern.var 4,
                               Erlean.Core.Pattern.var 5,
                               Erlean.Core.Pattern.cons
                                 (Erlean.Core.Pattern.tuple
                                   [Erlean.Core.Pattern.var 6, Erlean.Core.Pattern.var 7, Erlean.Core.Pattern.var 8])
                                 (Erlean.Core.Pattern.var 9),
                               Erlean.Core.Pattern.var 10],
                              Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                              Erlean.Core.Expr.caseE
                                (Erlean.Core.Expr.call
                                  (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "erlang"))
                                  (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "=:="))
                                  [Erlean.Core.Expr.var 4, Erlean.Core.Expr.var 6])
                                [([Erlean.Core.Pattern.lit (Erlean.Core.Value.atom "true")],
                                  Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                                  Erlean.Core.Expr.letE
                                    [11]
                                    (Erlean.Core.Expr.call
                                      (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "erlang"))
                                      (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "+"))
                                      [Erlean.Core.Expr.var 5, Erlean.Core.Expr.var 8])
                                    (Erlean.Core.Expr.letE
                                      [12]
                                      (Erlean.Core.Expr.apply
                                        (Erlean.Core.Expr.funRef "insert" 3)
                                        [Erlean.Core.Expr.var 7, Erlean.Core.Expr.var 11, Erlean.Core.Expr.var 10])
                                      (Erlean.Core.Expr.apply
                                        (Erlean.Core.Expr.funRef "expand" 4)
                                        [Erlean.Core.Expr.var 4,
                                         Erlean.Core.Expr.var 5,
                                         Erlean.Core.Expr.var 9,
                                         Erlean.Core.Expr.var 12]))),
                                 ([Erlean.Core.Pattern.lit (Erlean.Core.Value.atom "false")],
                                  Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                                  Erlean.Core.Expr.caseE
                                    (Erlean.Core.Expr.apply
                                      (Erlean.Core.Expr.funRef "expand" 4)
                                      [Erlean.Core.Expr.var 4,
                                       Erlean.Core.Expr.var 5,
                                       Erlean.Core.Expr.var 9,
                                       Erlean.Core.Expr.var 10])
                                    [([Erlean.Core.Pattern.tuple
                                         [Erlean.Core.Pattern.var 11, Erlean.Core.Pattern.var 12]],
                                      Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                                      Erlean.Core.Expr.tuple
                                        [Erlean.Core.Expr.var 11,
                                         Erlean.Core.Expr.cons
                                           (Erlean.Core.Expr.tuple
                                             [Erlean.Core.Expr.var 6, Erlean.Core.Expr.var 7, Erlean.Core.Expr.var 8])
                                           (Erlean.Core.Expr.var 12)]),
                                     ([Erlean.Core.Pattern.var 11],
                                      Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                                      Erlean.Core.Expr.primop
                                        "match_fail"
                                        [Erlean.Core.Expr.tuple
                                           [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "badmatch"),
                                            Erlean.Core.Expr.var 11]])]),
                                 ([Erlean.Core.Pattern.var 11],
                                  Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                                  Erlean.Core.Expr.primop
                                    "match_fail"
                                    [Erlean.Core.Expr.tuple
                                       [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "case_clause"),
                                        Erlean.Core.Expr.var 11]])]),
                             ([Erlean.Core.Pattern.var 4,
                               Erlean.Core.Pattern.var 5,
                               Erlean.Core.Pattern.var 6,
                               Erlean.Core.Pattern.var 7],
                              Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                              Erlean.Core.Expr.primop
                                "match_fail"
                                [Erlean.Core.Expr.tuple
                                   [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "function_clause"),
                                    Erlean.Core.Expr.var 4,
                                    Erlean.Core.Expr.var 5,
                                    Erlean.Core.Expr.var 6,
                                    Erlean.Core.Expr.var 7]])] },
                { name := "insert",
                  params := [0, 1, 2],
                  body := Erlean.Core.Expr.caseE
                            (Erlean.Core.Expr.values
                              [Erlean.Core.Expr.var 0, Erlean.Core.Expr.var 1, Erlean.Core.Expr.var 2])
                            [([Erlean.Core.Pattern.var 3,
                               Erlean.Core.Pattern.var 4,
                               Erlean.Core.Pattern.lit (Erlean.Core.Value.nil)],
                              Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                              Erlean.Core.Expr.cons
                                (Erlean.Core.Expr.tuple [Erlean.Core.Expr.var 3, Erlean.Core.Expr.var 4])
                                (Erlean.Core.Expr.lit (Erlean.Core.Value.nil))),
                             ([Erlean.Core.Pattern.var 3,
                               Erlean.Core.Pattern.var 4,
                               Erlean.Core.Pattern.cons
                                 (Erlean.Core.Pattern.tuple [Erlean.Core.Pattern.var 5, Erlean.Core.Pattern.var 6])
                                 (Erlean.Core.Pattern.var 7)],
                              Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                              Erlean.Core.Expr.caseE
                                (Erlean.Core.Expr.call
                                  (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "erlang"))
                                  (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "=<"))
                                  [Erlean.Core.Expr.var 4, Erlean.Core.Expr.var 6])
                                [([Erlean.Core.Pattern.lit (Erlean.Core.Value.atom "true")],
                                  Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                                  Erlean.Core.Expr.cons
                                    (Erlean.Core.Expr.tuple [Erlean.Core.Expr.var 3, Erlean.Core.Expr.var 4])
                                    (Erlean.Core.Expr.cons
                                      (Erlean.Core.Expr.tuple [Erlean.Core.Expr.var 5, Erlean.Core.Expr.var 6])
                                      (Erlean.Core.Expr.var 7))),
                                 ([Erlean.Core.Pattern.lit (Erlean.Core.Value.atom "false")],
                                  Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                                  Erlean.Core.Expr.letE
                                    [8]
                                    (Erlean.Core.Expr.apply
                                      (Erlean.Core.Expr.funRef "insert" 3)
                                      [Erlean.Core.Expr.var 3, Erlean.Core.Expr.var 4, Erlean.Core.Expr.var 7])
                                    (Erlean.Core.Expr.cons
                                      (Erlean.Core.Expr.tuple [Erlean.Core.Expr.var 5, Erlean.Core.Expr.var 6])
                                      (Erlean.Core.Expr.var 8))),
                                 ([Erlean.Core.Pattern.var 8],
                                  Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                                  Erlean.Core.Expr.primop
                                    "match_fail"
                                    [Erlean.Core.Expr.tuple
                                       [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "case_clause"),
                                        Erlean.Core.Expr.var 8]])]),
                             ([Erlean.Core.Pattern.var 3, Erlean.Core.Pattern.var 4, Erlean.Core.Pattern.var 5],
                              Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                              Erlean.Core.Expr.primop
                                "match_fail"
                                [Erlean.Core.Expr.tuple
                                   [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "function_clause"),
                                    Erlean.Core.Expr.var 3,
                                    Erlean.Core.Expr.var 4,
                                    Erlean.Core.Expr.var 5]])] },
                { name := "reverse",
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
                                (Erlean.Core.Expr.funRef "reverse" 2)
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
                { name := "module_info",
                  params := [],
                  body := Erlean.Core.Expr.caseE
                            (Erlean.Core.Expr.values [])
                            [([],
                              Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                              Erlean.Core.Expr.call
                                (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "erlang"))
                                (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "get_module_info"))
                                [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "dijkstra")]),
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
                                [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "dijkstra"), Erlean.Core.Expr.var 1]),
                             ([Erlean.Core.Pattern.var 1],
                              Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                              Erlean.Core.Expr.primop
                                "match_fail"
                                [Erlean.Core.Expr.tuple
                                   [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "function_clause"),
                                    Erlean.Core.Expr.var 1]])] }],
  closureCode := [] }

end Erlean.Examples
