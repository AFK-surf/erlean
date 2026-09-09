import Erlean.Core.Syntax

namespace Erlean.Examples

private def importedHigherOrderModule_part_0 : Erlean.Core.FunctionDef :=
{ name := ("map"), params := ([0, 1]), body := (Erlean.Core.Expr.caseE
  (Erlean.Core.Expr.values [Erlean.Core.Expr.var 0, Erlean.Core.Expr.var 1])
  [([Erlean.Core.Pattern.var 2, Erlean.Core.Pattern.lit (Erlean.Core.Value.nil)],
    Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
    Erlean.Core.Expr.lit (Erlean.Core.Value.nil)),
   ([Erlean.Core.Pattern.var 2, Erlean.Core.Pattern.cons (Erlean.Core.Pattern.var 3) (Erlean.Core.Pattern.var 4)],
    Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
    Erlean.Core.Expr.letE
      [5]
      (Erlean.Core.Expr.apply (Erlean.Core.Expr.var 2) [Erlean.Core.Expr.var 3])
      (Erlean.Core.Expr.letE
        [6]
        (Erlean.Core.Expr.apply (Erlean.Core.Expr.funRef "map" 2) [Erlean.Core.Expr.var 2, Erlean.Core.Expr.var 4])
        (Erlean.Core.Expr.cons (Erlean.Core.Expr.var 5) (Erlean.Core.Expr.var 6)))),
   ([Erlean.Core.Pattern.var 2, Erlean.Core.Pattern.var 3],
    Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
    Erlean.Core.Expr.primop
      "match_fail"
      [Erlean.Core.Expr.tuple
         [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "function_clause"),
          Erlean.Core.Expr.var 2,
          Erlean.Core.Expr.var 3]])]) }
private def importedHigherOrderModule_part_1 : Erlean.Core.FunctionDef :=
{ name := ("map_identity"), params := ([0]), body := (Erlean.Core.Expr.caseE
  (Erlean.Core.Expr.var 0)
  [([Erlean.Core.Pattern.var 1],
    Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
    Erlean.Core.Expr.letE
      [2]
      (Erlean.Core.Expr.makeClosure 0)
      (Erlean.Core.Expr.apply (Erlean.Core.Expr.funRef "map" 2) [Erlean.Core.Expr.var 2, Erlean.Core.Expr.var 1])),
   ([Erlean.Core.Pattern.var 1],
    Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
    Erlean.Core.Expr.primop
      "match_fail"
      [Erlean.Core.Expr.tuple
         [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "function_clause"), Erlean.Core.Expr.var 1]])]) }
private def importedHigherOrderModule_part_2 : Erlean.Core.FunctionDef :=
{ name := ("module_info"), params := ([]), body := (Erlean.Core.Expr.caseE
  (Erlean.Core.Expr.values [])
  [([],
    Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
    Erlean.Core.Expr.call
      (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "erlang"))
      (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "get_module_info"))
      [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "higher_order")]),
   ([],
    Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
    Erlean.Core.Expr.primop
      "match_fail"
      [Erlean.Core.Expr.lit (Erlean.Core.Value.tuple [Erlean.Core.Value.atom "function_clause"])])]) }
private def importedHigherOrderModule_part_3 : Erlean.Core.FunctionDef :=
{ name := ("module_info"), params := ([0]), body := (Erlean.Core.Expr.caseE
  (Erlean.Core.Expr.var 0)
  [([Erlean.Core.Pattern.var 1],
    Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
    Erlean.Core.Expr.call
      (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "erlang"))
      (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "get_module_info"))
      [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "higher_order"), Erlean.Core.Expr.var 1]),
   ([Erlean.Core.Pattern.var 1],
    Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
    Erlean.Core.Expr.primop
      "match_fail"
      [Erlean.Core.Expr.tuple
         [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "function_clause"), Erlean.Core.Expr.var 1]])]) }
private def importedHigherOrderModule_part_4 : Erlean.Core.ClosureDef :=
{ params := ([2]), body := (Erlean.Core.Expr.caseE
  (Erlean.Core.Expr.var 2)
  [([Erlean.Core.Pattern.var 3], Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"), Erlean.Core.Expr.var 3),
   ([Erlean.Core.Pattern.var 3],
    Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
    Erlean.Core.Expr.primop
      "match_fail"
      [Erlean.Core.Expr.tuple
         [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "function_clause"), Erlean.Core.Expr.var 3]])]), outerScope := ([1, 0]), recursiveBindings := ([]) }
/-- Generated from a pinned OTP Core artifact by the erlean importer. -/
def importedHigherOrderModule : Erlean.Core.Module :=
{ name := ("higher_order")
  exports := [(("map", 2)), (("map_identity", 1)), (("module_info", 0)), (("module_info", 1))]
  functions := [importedHigherOrderModule_part_0, importedHigherOrderModule_part_1, importedHigherOrderModule_part_2, importedHigherOrderModule_part_3]
  closureCode := [importedHigherOrderModule_part_4] }

attribute [reducible] importedHigherOrderModule_part_0 importedHigherOrderModule_part_1 importedHigherOrderModule_part_2 importedHigherOrderModule_part_3 importedHigherOrderModule_part_4

end Erlean.Examples
