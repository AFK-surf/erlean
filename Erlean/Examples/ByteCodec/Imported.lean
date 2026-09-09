import Erlean.Core.Syntax

namespace Erlean.Examples

private def importedByteCodec_part_0 : Erlean.Core.FunctionDef :=
{ name := ("encode"), params := ([0]), body := (Erlean.Core.Expr.caseE
  (Erlean.Core.Expr.var 0)
  [([Erlean.Core.Pattern.var 1],
    Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
    Erlean.Core.Expr.bytes [Erlean.Core.Expr.var 1]),
   ([Erlean.Core.Pattern.var 1],
    Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
    Erlean.Core.Expr.primop
      "match_fail"
      [Erlean.Core.Expr.tuple
         [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "function_clause"), Erlean.Core.Expr.var 1]])]) }
private def importedByteCodec_part_1 : Erlean.Core.FunctionDef :=
{ name := ("decode"), params := ([0]), body := (Erlean.Core.Expr.caseE
  (Erlean.Core.Expr.var 0)
  [([Erlean.Core.Pattern.bytes [Erlean.Core.Pattern.var 1]],
    Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
    Erlean.Core.Expr.tuple [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "ok"), Erlean.Core.Expr.var 1]),
   ([Erlean.Core.Pattern.var 1],
    Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
    Erlean.Core.Expr.lit (Erlean.Core.Value.atom "error")),
   ([Erlean.Core.Pattern.var 1],
    Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
    Erlean.Core.Expr.primop
      "match_fail"
      [Erlean.Core.Expr.tuple
         [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "function_clause"), Erlean.Core.Expr.var 1]])]) }
private def importedByteCodec_part_2 : Erlean.Core.FunctionDef :=
{ name := ("encode_pair"), params := ([0, 1]), body := (Erlean.Core.Expr.caseE
  (Erlean.Core.Expr.values [Erlean.Core.Expr.var 0, Erlean.Core.Expr.var 1])
  [([Erlean.Core.Pattern.var 2, Erlean.Core.Pattern.var 3],
    Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
    Erlean.Core.Expr.bytes [Erlean.Core.Expr.var 2, Erlean.Core.Expr.var 3]),
   ([Erlean.Core.Pattern.var 2, Erlean.Core.Pattern.var 3],
    Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
    Erlean.Core.Expr.primop
      "match_fail"
      [Erlean.Core.Expr.tuple
         [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "function_clause"),
          Erlean.Core.Expr.var 2,
          Erlean.Core.Expr.var 3]])]) }
private def importedByteCodec_part_3 : Erlean.Core.FunctionDef :=
{ name := ("decode_pair"), params := ([0]), body := (Erlean.Core.Expr.caseE
  (Erlean.Core.Expr.var 0)
  [([Erlean.Core.Pattern.bytes [Erlean.Core.Pattern.var 1, Erlean.Core.Pattern.var 2]],
    Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
    Erlean.Core.Expr.tuple
      [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "ok"), Erlean.Core.Expr.var 1, Erlean.Core.Expr.var 2]),
   ([Erlean.Core.Pattern.var 1],
    Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
    Erlean.Core.Expr.lit (Erlean.Core.Value.atom "error")),
   ([Erlean.Core.Pattern.var 1],
    Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
    Erlean.Core.Expr.primop
      "match_fail"
      [Erlean.Core.Expr.tuple
         [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "function_clause"), Erlean.Core.Expr.var 1]])]) }
private def importedByteCodec_part_4 : Erlean.Core.FunctionDef :=
{ name := ("roundtrip"), params := ([0]), body := (Erlean.Core.Expr.caseE
  (Erlean.Core.Expr.var 0)
  [([Erlean.Core.Pattern.var 1],
    Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
    Erlean.Core.Expr.letE
      [2]
      (Erlean.Core.Expr.apply (Erlean.Core.Expr.funRef "encode" 1) [Erlean.Core.Expr.var 1])
      (Erlean.Core.Expr.apply (Erlean.Core.Expr.funRef "decode" 1) [Erlean.Core.Expr.var 2])),
   ([Erlean.Core.Pattern.var 1],
    Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
    Erlean.Core.Expr.primop
      "match_fail"
      [Erlean.Core.Expr.tuple
         [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "function_clause"), Erlean.Core.Expr.var 1]])]) }
private def importedByteCodec_part_5 : Erlean.Core.FunctionDef :=
{ name := ("module_info"), params := ([]), body := (Erlean.Core.Expr.caseE
  (Erlean.Core.Expr.values [])
  [([],
    Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
    Erlean.Core.Expr.call
      (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "erlang"))
      (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "get_module_info"))
      [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "byte_codec")]),
   ([],
    Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
    Erlean.Core.Expr.primop
      "match_fail"
      [Erlean.Core.Expr.lit (Erlean.Core.Value.tuple [Erlean.Core.Value.atom "function_clause"])])]) }
private def importedByteCodec_part_6 : Erlean.Core.FunctionDef :=
{ name := ("module_info"), params := ([0]), body := (Erlean.Core.Expr.caseE
  (Erlean.Core.Expr.var 0)
  [([Erlean.Core.Pattern.var 1],
    Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
    Erlean.Core.Expr.call
      (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "erlang"))
      (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "get_module_info"))
      [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "byte_codec"), Erlean.Core.Expr.var 1]),
   ([Erlean.Core.Pattern.var 1],
    Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
    Erlean.Core.Expr.primop
      "match_fail"
      [Erlean.Core.Expr.tuple
         [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "function_clause"), Erlean.Core.Expr.var 1]])]) }
/-- Generated from a pinned OTP Core artifact by the erlean importer. -/
def importedByteCodec : Erlean.Core.Module :=
{ name := ("byte_codec")
  exports := [(("decode", 1)), (("decode_pair", 1)), (("encode", 1)), (("encode_pair", 2)), (("module_info", 0)), (("module_info", 1)), (("roundtrip", 1))]
  functions := [importedByteCodec_part_0, importedByteCodec_part_1, importedByteCodec_part_2, importedByteCodec_part_3, importedByteCodec_part_4, importedByteCodec_part_5, importedByteCodec_part_6]
  closureCode := [] }

attribute [reducible] importedByteCodec_part_0 importedByteCodec_part_1 importedByteCodec_part_2 importedByteCodec_part_3 importedByteCodec_part_4 importedByteCodec_part_5 importedByteCodec_part_6

end Erlean.Examples
