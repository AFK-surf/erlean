import Erlean.Core.Syntax

namespace Erlean.Examples

private def importedDijkstraModule_part_0 : Erlean.Core.Expr :=
Erlean.Core.Expr.caseE (Erlean.Core.Expr.apply (Erlean.Core.Expr.funRef "nonnegative_integer" 1) [Erlean.Core.Expr.var 2]) ([(([Erlean.Core.Pattern.lit (Erlean.Core.Value.atom "true")]), (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true")), (Erlean.Core.Expr.caseE
  (Erlean.Core.Expr.apply (Erlean.Core.Expr.funRef "valid_edges" 1) [Erlean.Core.Expr.var 3])
  [([Erlean.Core.Pattern.lit (Erlean.Core.Value.atom "true")],
    Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
    Erlean.Core.Expr.letE
      [4]
      (Erlean.Core.Expr.apply
        (Erlean.Core.Expr.funRef "search" 3)
        [Erlean.Core.Expr.cons
           (Erlean.Core.Expr.tuple [Erlean.Core.Expr.var 2, Erlean.Core.Expr.lit (Erlean.Core.Value.integer 0)])
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
      [Erlean.Core.Expr.tuple [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "case_clause"), Erlean.Core.Expr.var 4]])])), (([Erlean.Core.Pattern.lit (Erlean.Core.Value.atom "false")]), (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true")), (Erlean.Core.Expr.call
  (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "erlang"))
  (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "error"))
  [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "badarg")])), (([Erlean.Core.Pattern.var 4]), (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true")), (Erlean.Core.Expr.primop
  "match_fail"
  [Erlean.Core.Expr.tuple [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "case_clause"), Erlean.Core.Expr.var 4]]))])
private def importedDijkstraModule_part_1 : Erlean.Core.Expr :=
Erlean.Core.Expr.caseE (Erlean.Core.Expr.values [Erlean.Core.Expr.var 0, Erlean.Core.Expr.var 1]) ([(([Erlean.Core.Pattern.var 2, Erlean.Core.Pattern.var 3]), (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true")), importedDijkstraModule_part_0), (([Erlean.Core.Pattern.var 2, Erlean.Core.Pattern.var 3]), (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true")), (Erlean.Core.Expr.primop
  "match_fail"
  [Erlean.Core.Expr.tuple
     [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "function_clause"), Erlean.Core.Expr.var 2, Erlean.Core.Expr.var 3]]))])
private def importedDijkstraModule_part_2 : Erlean.Core.FunctionDef :=
{ name := ("distances"), params := ([0, 1]), body := importedDijkstraModule_part_1 }
private def importedDijkstraModule_part_3 : Erlean.Core.FunctionDef :=
{ name := ("nonnegative_integer"), params := ([0]), body := (Erlean.Core.Expr.caseE
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
             [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "case_clause"), Erlean.Core.Expr.var 2]])]),
   ([Erlean.Core.Pattern.var 1],
    Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
    Erlean.Core.Expr.primop
      "match_fail"
      [Erlean.Core.Expr.tuple
         [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "function_clause"), Erlean.Core.Expr.var 1]])]) }
private def importedDijkstraModule_part_4 : Erlean.Core.Expr :=
Erlean.Core.Expr.caseE (Erlean.Core.Expr.apply (Erlean.Core.Expr.funRef "nonnegative_integer" 1) [Erlean.Core.Expr.var 1]) ([(([Erlean.Core.Pattern.lit (Erlean.Core.Value.atom "false")]), (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true")), (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "false"))), (([Erlean.Core.Pattern.lit (Erlean.Core.Value.atom "true")]), (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true")), (Erlean.Core.Expr.caseE
  (Erlean.Core.Expr.apply (Erlean.Core.Expr.funRef "nonnegative_integer" 1) [Erlean.Core.Expr.var 2])
  [([Erlean.Core.Pattern.lit (Erlean.Core.Value.atom "false")],
    Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
    Erlean.Core.Expr.lit (Erlean.Core.Value.atom "false")),
   ([Erlean.Core.Pattern.lit (Erlean.Core.Value.atom "true")],
    Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
    Erlean.Core.Expr.caseE
      (Erlean.Core.Expr.apply (Erlean.Core.Expr.funRef "nonnegative_integer" 1) [Erlean.Core.Expr.var 3])
      [([Erlean.Core.Pattern.lit (Erlean.Core.Value.atom "false")],
        Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
        Erlean.Core.Expr.lit (Erlean.Core.Value.atom "false")),
       ([Erlean.Core.Pattern.lit (Erlean.Core.Value.atom "true")],
        Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
        Erlean.Core.Expr.apply (Erlean.Core.Expr.funRef "valid_edges" 1) [Erlean.Core.Expr.var 4]),
       ([Erlean.Core.Pattern.var 5],
        Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
        Erlean.Core.Expr.primop
          "match_fail"
          [Erlean.Core.Expr.tuple
             [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "case_clause"), Erlean.Core.Expr.var 5]])]),
   ([Erlean.Core.Pattern.var 5],
    Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
    Erlean.Core.Expr.primop
      "match_fail"
      [Erlean.Core.Expr.tuple [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "case_clause"), Erlean.Core.Expr.var 5]])])), (([Erlean.Core.Pattern.var 5]), (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true")), (Erlean.Core.Expr.primop
  "match_fail"
  [Erlean.Core.Expr.tuple [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "case_clause"), Erlean.Core.Expr.var 5]]))])
private def importedDijkstraModule_part_5 : Erlean.Core.Expr :=
Erlean.Core.Expr.caseE (Erlean.Core.Expr.var 0) ([(([Erlean.Core.Pattern.lit (Erlean.Core.Value.nil)]), (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true")), (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"))), (([Erlean.Core.Pattern.cons
   (Erlean.Core.Pattern.tuple [Erlean.Core.Pattern.var 1, Erlean.Core.Pattern.var 2, Erlean.Core.Pattern.var 3])
   (Erlean.Core.Pattern.var 4)]), (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true")), importedDijkstraModule_part_4), (([Erlean.Core.Pattern.var 1]), (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true")), (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "false"))), (([Erlean.Core.Pattern.var 1]), (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true")), (Erlean.Core.Expr.primop
  "match_fail"
  [Erlean.Core.Expr.tuple [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "function_clause"), Erlean.Core.Expr.var 1]]))])
private def importedDijkstraModule_part_6 : Erlean.Core.FunctionDef :=
{ name := ("valid_edges"), params := ([0]), body := importedDijkstraModule_part_5 }
private def importedDijkstraModule_part_7 : Erlean.Core.Expr :=
Erlean.Core.Expr.caseE (Erlean.Core.Expr.apply (Erlean.Core.Expr.funRef "settled" 2) [Erlean.Core.Expr.var 3, Erlean.Core.Expr.var 7]) ([(([Erlean.Core.Pattern.lit (Erlean.Core.Value.atom "true")]), (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true")), (Erlean.Core.Expr.apply
  (Erlean.Core.Expr.funRef "search" 3)
  [Erlean.Core.Expr.var 5, Erlean.Core.Expr.var 6, Erlean.Core.Expr.var 7])), (([Erlean.Core.Pattern.lit (Erlean.Core.Value.atom "false")]), (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true")), (Erlean.Core.Expr.caseE
  (Erlean.Core.Expr.apply
    (Erlean.Core.Expr.funRef "expand" 4)
    [Erlean.Core.Expr.var 3, Erlean.Core.Expr.var 4, Erlean.Core.Expr.var 6, Erlean.Core.Expr.var 5])
  [([Erlean.Core.Pattern.tuple [Erlean.Core.Pattern.var 8, Erlean.Core.Pattern.var 9]],
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
      [Erlean.Core.Expr.tuple [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "badmatch"), Erlean.Core.Expr.var 8]])])), (([Erlean.Core.Pattern.var 8]), (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true")), (Erlean.Core.Expr.primop
  "match_fail"
  [Erlean.Core.Expr.tuple [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "case_clause"), Erlean.Core.Expr.var 8]]))])
private def importedDijkstraModule_part_8 : Erlean.Core.Expr :=
Erlean.Core.Expr.caseE (Erlean.Core.Expr.values [Erlean.Core.Expr.var 0, Erlean.Core.Expr.var 1, Erlean.Core.Expr.var 2]) ([(([Erlean.Core.Pattern.lit (Erlean.Core.Value.nil), Erlean.Core.Pattern.var 3, Erlean.Core.Pattern.var 4]), (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true")), (Erlean.Core.Expr.var 4)), (([Erlean.Core.Pattern.cons
   (Erlean.Core.Pattern.tuple [Erlean.Core.Pattern.var 3, Erlean.Core.Pattern.var 4])
   (Erlean.Core.Pattern.var 5),
 Erlean.Core.Pattern.var 6,
 Erlean.Core.Pattern.var 7]), (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true")), importedDijkstraModule_part_7), (([Erlean.Core.Pattern.var 3, Erlean.Core.Pattern.var 4, Erlean.Core.Pattern.var 5]), (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true")), (Erlean.Core.Expr.primop
  "match_fail"
  [Erlean.Core.Expr.tuple
     [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "function_clause"),
      Erlean.Core.Expr.var 3,
      Erlean.Core.Expr.var 4,
      Erlean.Core.Expr.var 5]]))])
private def importedDijkstraModule_part_9 : Erlean.Core.FunctionDef :=
{ name := ("search"), params := ([0, 1, 2]), body := importedDijkstraModule_part_8 }
private def importedDijkstraModule_part_10 : Erlean.Core.Expr :=
Erlean.Core.Expr.caseE (Erlean.Core.Expr.values [Erlean.Core.Expr.var 0, Erlean.Core.Expr.var 1]) ([(([Erlean.Core.Pattern.var 2, Erlean.Core.Pattern.lit (Erlean.Core.Value.nil)]), (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true")), (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "false"))), (([Erlean.Core.Pattern.var 2,
 Erlean.Core.Pattern.cons
   (Erlean.Core.Pattern.tuple [Erlean.Core.Pattern.var 3, Erlean.Core.Pattern.var 4])
   (Erlean.Core.Pattern.var 5)]), (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true")), (Erlean.Core.Expr.caseE
  (Erlean.Core.Expr.call
    (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "erlang"))
    (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "=:="))
    [Erlean.Core.Expr.var 2, Erlean.Core.Expr.var 3])
  [([Erlean.Core.Pattern.lit (Erlean.Core.Value.atom "true")],
    Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
    Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true")),
   ([Erlean.Core.Pattern.lit (Erlean.Core.Value.atom "false")],
    Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
    Erlean.Core.Expr.apply (Erlean.Core.Expr.funRef "settled" 2) [Erlean.Core.Expr.var 2, Erlean.Core.Expr.var 5]),
   ([Erlean.Core.Pattern.var 6],
    Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
    Erlean.Core.Expr.primop
      "match_fail"
      [Erlean.Core.Expr.tuple [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "case_clause"), Erlean.Core.Expr.var 6]])])), (([Erlean.Core.Pattern.var 2, Erlean.Core.Pattern.var 3]), (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true")), (Erlean.Core.Expr.primop
  "match_fail"
  [Erlean.Core.Expr.tuple
     [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "function_clause"), Erlean.Core.Expr.var 2, Erlean.Core.Expr.var 3]]))])
private def importedDijkstraModule_part_11 : Erlean.Core.FunctionDef :=
{ name := ("settled"), params := ([0, 1]), body := importedDijkstraModule_part_10 }
private def importedDijkstraModule_part_12 : Erlean.Core.Expr :=
Erlean.Core.Expr.caseE (Erlean.Core.Expr.call
  (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "erlang"))
  (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "=:="))
  [Erlean.Core.Expr.var 4, Erlean.Core.Expr.var 6]) ([(([Erlean.Core.Pattern.lit (Erlean.Core.Value.atom "true")]), (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true")), (Erlean.Core.Expr.letE
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
      [Erlean.Core.Expr.var 4, Erlean.Core.Expr.var 5, Erlean.Core.Expr.var 9, Erlean.Core.Expr.var 12])))), (([Erlean.Core.Pattern.lit (Erlean.Core.Value.atom "false")]), (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true")), (Erlean.Core.Expr.caseE
  (Erlean.Core.Expr.apply
    (Erlean.Core.Expr.funRef "expand" 4)
    [Erlean.Core.Expr.var 4, Erlean.Core.Expr.var 5, Erlean.Core.Expr.var 9, Erlean.Core.Expr.var 10])
  [([Erlean.Core.Pattern.tuple [Erlean.Core.Pattern.var 11, Erlean.Core.Pattern.var 12]],
    Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
    Erlean.Core.Expr.tuple
      [Erlean.Core.Expr.var 11,
       Erlean.Core.Expr.cons
         (Erlean.Core.Expr.tuple [Erlean.Core.Expr.var 6, Erlean.Core.Expr.var 7, Erlean.Core.Expr.var 8])
         (Erlean.Core.Expr.var 12)]),
   ([Erlean.Core.Pattern.var 11],
    Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
    Erlean.Core.Expr.primop
      "match_fail"
      [Erlean.Core.Expr.tuple [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "badmatch"), Erlean.Core.Expr.var 11]])])), (([Erlean.Core.Pattern.var 11]), (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true")), (Erlean.Core.Expr.primop
  "match_fail"
  [Erlean.Core.Expr.tuple [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "case_clause"), Erlean.Core.Expr.var 11]]))])
private def importedDijkstraModule_part_13 : Erlean.Core.Expr :=
Erlean.Core.Expr.caseE (Erlean.Core.Expr.values [Erlean.Core.Expr.var 0, Erlean.Core.Expr.var 1, Erlean.Core.Expr.var 2, Erlean.Core.Expr.var 3]) ([(([Erlean.Core.Pattern.var 4,
 Erlean.Core.Pattern.var 5,
 Erlean.Core.Pattern.lit (Erlean.Core.Value.nil),
 Erlean.Core.Pattern.var 6]), (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true")), (Erlean.Core.Expr.tuple [Erlean.Core.Expr.var 6, Erlean.Core.Expr.lit (Erlean.Core.Value.nil)])), (([Erlean.Core.Pattern.var 4,
 Erlean.Core.Pattern.var 5,
 Erlean.Core.Pattern.cons
   (Erlean.Core.Pattern.tuple [Erlean.Core.Pattern.var 6, Erlean.Core.Pattern.var 7, Erlean.Core.Pattern.var 8])
   (Erlean.Core.Pattern.var 9),
 Erlean.Core.Pattern.var 10]), (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true")), importedDijkstraModule_part_12), (([Erlean.Core.Pattern.var 4, Erlean.Core.Pattern.var 5, Erlean.Core.Pattern.var 6, Erlean.Core.Pattern.var 7]), (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true")), (Erlean.Core.Expr.primop
  "match_fail"
  [Erlean.Core.Expr.tuple
     [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "function_clause"),
      Erlean.Core.Expr.var 4,
      Erlean.Core.Expr.var 5,
      Erlean.Core.Expr.var 6,
      Erlean.Core.Expr.var 7]]))])
private def importedDijkstraModule_part_14 : Erlean.Core.FunctionDef :=
{ name := ("expand"), params := ([0, 1, 2, 3]), body := importedDijkstraModule_part_13 }
private def importedDijkstraModule_part_15 : Erlean.Core.Expr :=
Erlean.Core.Expr.caseE (Erlean.Core.Expr.values [Erlean.Core.Expr.var 0, Erlean.Core.Expr.var 1, Erlean.Core.Expr.var 2]) ([(([Erlean.Core.Pattern.var 3, Erlean.Core.Pattern.var 4, Erlean.Core.Pattern.lit (Erlean.Core.Value.nil)]), (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true")), (Erlean.Core.Expr.cons
  (Erlean.Core.Expr.tuple [Erlean.Core.Expr.var 3, Erlean.Core.Expr.var 4])
  (Erlean.Core.Expr.lit (Erlean.Core.Value.nil)))), (([Erlean.Core.Pattern.var 3,
 Erlean.Core.Pattern.var 4,
 Erlean.Core.Pattern.cons
   (Erlean.Core.Pattern.tuple [Erlean.Core.Pattern.var 5, Erlean.Core.Pattern.var 6])
   (Erlean.Core.Pattern.var 7)]), (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true")), (Erlean.Core.Expr.caseE
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
      [Erlean.Core.Expr.tuple [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "case_clause"), Erlean.Core.Expr.var 8]])])), (([Erlean.Core.Pattern.var 3, Erlean.Core.Pattern.var 4, Erlean.Core.Pattern.var 5]), (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true")), (Erlean.Core.Expr.primop
  "match_fail"
  [Erlean.Core.Expr.tuple
     [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "function_clause"),
      Erlean.Core.Expr.var 3,
      Erlean.Core.Expr.var 4,
      Erlean.Core.Expr.var 5]]))])
private def importedDijkstraModule_part_16 : Erlean.Core.FunctionDef :=
{ name := ("insert"), params := ([0, 1, 2]), body := importedDijkstraModule_part_15 }
private def importedDijkstraModule_part_17 : Erlean.Core.FunctionDef :=
{ name := ("reverse"), params := ([0, 1]), body := (Erlean.Core.Expr.caseE
  (Erlean.Core.Expr.values [Erlean.Core.Expr.var 0, Erlean.Core.Expr.var 1])
  [([Erlean.Core.Pattern.lit (Erlean.Core.Value.nil), Erlean.Core.Pattern.var 2],
    Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
    Erlean.Core.Expr.var 2),
   ([Erlean.Core.Pattern.cons (Erlean.Core.Pattern.var 2) (Erlean.Core.Pattern.var 3), Erlean.Core.Pattern.var 4],
    Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
    Erlean.Core.Expr.apply
      (Erlean.Core.Expr.funRef "reverse" 2)
      [Erlean.Core.Expr.var 3, Erlean.Core.Expr.cons (Erlean.Core.Expr.var 2) (Erlean.Core.Expr.var 4)]),
   ([Erlean.Core.Pattern.var 2, Erlean.Core.Pattern.var 3],
    Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
    Erlean.Core.Expr.primop
      "match_fail"
      [Erlean.Core.Expr.tuple
         [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "function_clause"),
          Erlean.Core.Expr.var 2,
          Erlean.Core.Expr.var 3]])]) }
private def importedDijkstraModule_part_18 : Erlean.Core.FunctionDef :=
{ name := ("module_info"), params := ([]), body := (Erlean.Core.Expr.caseE
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
      [Erlean.Core.Expr.lit (Erlean.Core.Value.tuple [Erlean.Core.Value.atom "function_clause"])])]) }
private def importedDijkstraModule_part_19 : Erlean.Core.FunctionDef :=
{ name := ("module_info"), params := ([0]), body := (Erlean.Core.Expr.caseE
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
         [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "function_clause"), Erlean.Core.Expr.var 1]])]) }
/-- Generated from a pinned OTP Core artifact by the erlean importer. -/
def importedDijkstraModule : Erlean.Core.Module :=
{ name := ("dijkstra")
  exports := [(("distances", 2)), (("module_info", 0)), (("module_info", 1))]
  functions := [importedDijkstraModule_part_2, importedDijkstraModule_part_3, importedDijkstraModule_part_6, importedDijkstraModule_part_9, importedDijkstraModule_part_11, importedDijkstraModule_part_14, importedDijkstraModule_part_16, importedDijkstraModule_part_17, importedDijkstraModule_part_18, importedDijkstraModule_part_19]
  closureCode := [] }

attribute [reducible] importedDijkstraModule_part_0 importedDijkstraModule_part_1 importedDijkstraModule_part_2 importedDijkstraModule_part_3 importedDijkstraModule_part_4 importedDijkstraModule_part_5 importedDijkstraModule_part_6 importedDijkstraModule_part_7 importedDijkstraModule_part_8 importedDijkstraModule_part_9 importedDijkstraModule_part_10 importedDijkstraModule_part_11 importedDijkstraModule_part_12 importedDijkstraModule_part_13 importedDijkstraModule_part_14 importedDijkstraModule_part_15 importedDijkstraModule_part_16 importedDijkstraModule_part_17 importedDijkstraModule_part_18 importedDijkstraModule_part_19

end Erlean.Examples
