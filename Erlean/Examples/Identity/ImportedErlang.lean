import Erlean.Core.Syntax

namespace Erlean.Examples

private def importedModule_part_0 : Erlean.Core.FunctionDef :=
{ name := ("identity"), params := ([0]), body := (Erlean.Core.Expr.caseE
  (Erlean.Core.Expr.var 0)
  [([Erlean.Core.Pattern.var 1], Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"), Erlean.Core.Expr.var 1),
   ([Erlean.Core.Pattern.var 1],
    Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
    Erlean.Core.Expr.primop
      "match_fail"
      [Erlean.Core.Expr.tuple
         [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "function_clause"), Erlean.Core.Expr.var 1]])]) }
private def importedModule_part_1 : Erlean.Core.FunctionDef :=
{ name := ("pair"), params := ([0, 1]), body := (Erlean.Core.Expr.caseE
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
          Erlean.Core.Expr.var 3]])]) }
private def importedModule_part_2 : Erlean.Core.FunctionDef :=
{ name := ("answer"), params := ([]), body := (Erlean.Core.Expr.caseE
  (Erlean.Core.Expr.values [])
  [([], Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"), Erlean.Core.Expr.lit (Erlean.Core.Value.integer 42)),
   ([],
    Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
    Erlean.Core.Expr.primop
      "match_fail"
      [Erlean.Core.Expr.lit (Erlean.Core.Value.tuple [Erlean.Core.Value.atom "function_clause"])])]) }
private def importedModule_part_3 : Erlean.Core.FunctionDef :=
{ name := ("module_info"), params := ([]), body := (Erlean.Core.Expr.caseE
  (Erlean.Core.Expr.values [])
  [([],
    Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
    Erlean.Core.Expr.call
      (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "erlang"))
      (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "get_module_info"))
      [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "identity")]),
   ([],
    Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
    Erlean.Core.Expr.primop
      "match_fail"
      [Erlean.Core.Expr.lit (Erlean.Core.Value.tuple [Erlean.Core.Value.atom "function_clause"])])]) }
private def importedModule_part_4 : Erlean.Core.FunctionDef :=
{ name := ("module_info"), params := ([0]), body := (Erlean.Core.Expr.caseE
  (Erlean.Core.Expr.var 0)
  [([Erlean.Core.Pattern.var 1],
    Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
    Erlean.Core.Expr.call
      (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "erlang"))
      (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "get_module_info"))
      [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "identity"), Erlean.Core.Expr.var 1]),
   ([Erlean.Core.Pattern.var 1],
    Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
    Erlean.Core.Expr.primop
      "match_fail"
      [Erlean.Core.Expr.tuple
         [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "function_clause"), Erlean.Core.Expr.var 1]])]) }
/-- Generated from a pinned OTP Core artifact by the erlean importer. -/
def importedModule : Erlean.Core.Module :=
{ name := ("identity")
  exports := [(("answer", 0)), (("identity", 1)), (("module_info", 0)), (("module_info", 1)), (("pair", 2))]
  functions := [importedModule_part_0, importedModule_part_1, importedModule_part_2, importedModule_part_3, importedModule_part_4]
  closureCode := [] }

attribute [reducible] importedModule_part_0 importedModule_part_1 importedModule_part_2 importedModule_part_3 importedModule_part_4

end Erlean.Examples
