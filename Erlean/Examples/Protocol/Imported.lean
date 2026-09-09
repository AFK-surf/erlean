import Erlean.Core.Syntax

namespace Erlean.Examples

private def importedActorProtocolModule_part_0 : Erlean.Core.FunctionDef :=
{ name := ("start"), params := ([]), body := (Erlean.Core.Expr.caseE
  (Erlean.Core.Expr.values [])
  [([],
    Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
    Erlean.Core.Expr.call
      (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "erlang"))
      (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "spawn"))
      [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "actor_protocol"),
       Erlean.Core.Expr.lit (Erlean.Core.Value.atom "server"),
       Erlean.Core.Expr.lit (Erlean.Core.Value.nil)]),
   ([],
    Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
    Erlean.Core.Expr.primop
      "match_fail"
      [Erlean.Core.Expr.lit (Erlean.Core.Value.tuple [Erlean.Core.Value.atom "function_clause"])])]) }
private def importedActorProtocolModule_part_1 : Erlean.Core.FunctionDef :=
{ name := ("exchange"), params := ([0]), body := (Erlean.Core.Expr.caseE
  (Erlean.Core.Expr.var 0)
  [([Erlean.Core.Pattern.var 1],
    Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
    Erlean.Core.Expr.letE
      [2]
      (Erlean.Core.Expr.apply (Erlean.Core.Expr.funRef "start" 0) [])
      (Erlean.Core.Expr.letE
        [3]
        (Erlean.Core.Expr.apply
          (Erlean.Core.Expr.funRef "request" 3)
          [Erlean.Core.Expr.var 2, Erlean.Core.Expr.var 1, Erlean.Core.Expr.lit (Erlean.Core.Value.atom "infinity")])
        (Erlean.Core.Expr.seq
          (Erlean.Core.Expr.call
            (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "erlang"))
            (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "!"))
            [Erlean.Core.Expr.var 2, Erlean.Core.Expr.lit (Erlean.Core.Value.atom "stop")])
          (Erlean.Core.Expr.var 3)))),
   ([Erlean.Core.Pattern.var 1],
    Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
    Erlean.Core.Expr.primop
      "match_fail"
      [Erlean.Core.Expr.tuple
         [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "function_clause"), Erlean.Core.Expr.var 1]])]) }
private def importedActorProtocolModule_part_2 : Erlean.Core.FunctionDef :=
{ name := ("server"), params := ([]), body := (Erlean.Core.Expr.caseE
  (Erlean.Core.Expr.values [])
  [([],
    Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
    Erlean.Core.Expr.letrec [(0, 0)] (Erlean.Core.Expr.apply (Erlean.Core.Expr.var 0) [])),
   ([],
    Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
    Erlean.Core.Expr.primop
      "match_fail"
      [Erlean.Core.Expr.lit (Erlean.Core.Value.tuple [Erlean.Core.Value.atom "function_clause"])])]) }
private def importedActorProtocolModule_part_3 : Erlean.Core.Expr :=
Erlean.Core.Expr.caseE (Erlean.Core.Expr.values [Erlean.Core.Expr.var 0, Erlean.Core.Expr.var 1, Erlean.Core.Expr.var 2]) ([(([Erlean.Core.Pattern.var 3, Erlean.Core.Pattern.var 4, Erlean.Core.Pattern.var 5]), (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true")), (Erlean.Core.Expr.letE
  [6]
  (Erlean.Core.Expr.call
    (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "erlang"))
    (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "make_ref"))
    [])
  (Erlean.Core.Expr.letE
    [7]
    (Erlean.Core.Expr.call
      (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "erlang"))
      (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "self"))
      [])
    (Erlean.Core.Expr.seq
      (Erlean.Core.Expr.call
        (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "erlang"))
        (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "!"))
        [Erlean.Core.Expr.var 3,
         Erlean.Core.Expr.tuple
           [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "request"),
            Erlean.Core.Expr.var 7,
            Erlean.Core.Expr.var 6,
            Erlean.Core.Expr.var 4]])
      (Erlean.Core.Expr.letrec [(8, 1)] (Erlean.Core.Expr.apply (Erlean.Core.Expr.var 8) [])))))), (([Erlean.Core.Pattern.var 3, Erlean.Core.Pattern.var 4, Erlean.Core.Pattern.var 5]), (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true")), (Erlean.Core.Expr.primop
  "match_fail"
  [Erlean.Core.Expr.tuple
     [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "function_clause"),
      Erlean.Core.Expr.var 3,
      Erlean.Core.Expr.var 4,
      Erlean.Core.Expr.var 5]]))])
private def importedActorProtocolModule_part_4 : Erlean.Core.FunctionDef :=
{ name := ("request"), params := ([0, 1, 2]), body := importedActorProtocolModule_part_3 }
private def importedActorProtocolModule_part_5 : Erlean.Core.FunctionDef :=
{ name := ("poll"), params := ([]), body := (Erlean.Core.Expr.caseE
  (Erlean.Core.Expr.values [])
  [([],
    Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
    Erlean.Core.Expr.letrec [(0, 2)] (Erlean.Core.Expr.apply (Erlean.Core.Expr.var 0) [])),
   ([],
    Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
    Erlean.Core.Expr.primop
      "match_fail"
      [Erlean.Core.Expr.lit (Erlean.Core.Value.tuple [Erlean.Core.Value.atom "function_clause"])])]) }
private def importedActorProtocolModule_part_6 : Erlean.Core.FunctionDef :=
{ name := ("wait_only"), params := ([0]), body := (Erlean.Core.Expr.caseE
  (Erlean.Core.Expr.var 0)
  [([Erlean.Core.Pattern.var 1],
    Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
    Erlean.Core.Expr.letrec [(2, 3)] (Erlean.Core.Expr.apply (Erlean.Core.Expr.var 2) [])),
   ([Erlean.Core.Pattern.var 1],
    Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
    Erlean.Core.Expr.primop
      "match_fail"
      [Erlean.Core.Expr.tuple
         [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "function_clause"), Erlean.Core.Expr.var 1]])]) }
private def importedActorProtocolModule_part_7 : Erlean.Core.FunctionDef :=
{ name := ("module_info"), params := ([]), body := (Erlean.Core.Expr.caseE
  (Erlean.Core.Expr.values [])
  [([],
    Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
    Erlean.Core.Expr.call
      (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "erlang"))
      (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "get_module_info"))
      [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "actor_protocol")]),
   ([],
    Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
    Erlean.Core.Expr.primop
      "match_fail"
      [Erlean.Core.Expr.lit (Erlean.Core.Value.tuple [Erlean.Core.Value.atom "function_clause"])])]) }
private def importedActorProtocolModule_part_8 : Erlean.Core.FunctionDef :=
{ name := ("module_info"), params := ([0]), body := (Erlean.Core.Expr.caseE
  (Erlean.Core.Expr.var 0)
  [([Erlean.Core.Pattern.var 1],
    Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
    Erlean.Core.Expr.call
      (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "erlang"))
      (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "get_module_info"))
      [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "actor_protocol"), Erlean.Core.Expr.var 1]),
   ([Erlean.Core.Pattern.var 1],
    Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
    Erlean.Core.Expr.primop
      "match_fail"
      [Erlean.Core.Expr.tuple
         [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "function_clause"), Erlean.Core.Expr.var 1]])]) }
private def importedActorProtocolModule_part_9 : Erlean.Core.Expr :=
Erlean.Core.Expr.caseE (Erlean.Core.Expr.var 1) ([(([Erlean.Core.Pattern.lit (Erlean.Core.Value.atom "true")]), (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true")), (Erlean.Core.Expr.caseE
  (Erlean.Core.Expr.var 2)
  [([Erlean.Core.Pattern.tuple
       [Erlean.Core.Pattern.lit (Erlean.Core.Value.atom "request"),
        Erlean.Core.Pattern.var 3,
        Erlean.Core.Pattern.var 4,
        Erlean.Core.Pattern.var 5]],
    Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
    Erlean.Core.Expr.seq
      (Erlean.Core.Expr.primop "remove_message" [])
      (Erlean.Core.Expr.seq
        (Erlean.Core.Expr.call
          (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "erlang"))
          (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "!"))
          [Erlean.Core.Expr.var 3,
           Erlean.Core.Expr.tuple
             [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "reply"), Erlean.Core.Expr.var 4, Erlean.Core.Expr.var 5]])
        (Erlean.Core.Expr.apply (Erlean.Core.Expr.funRef "server" 0) []))),
   ([Erlean.Core.Pattern.lit (Erlean.Core.Value.atom "stop")],
    Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
    Erlean.Core.Expr.seq
      (Erlean.Core.Expr.primop "remove_message" [])
      (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "ok"))),
   ([Erlean.Core.Pattern.var 3],
    Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
    Erlean.Core.Expr.seq (Erlean.Core.Expr.primop "recv_next" []) (Erlean.Core.Expr.apply (Erlean.Core.Expr.var 0) []))])), (([Erlean.Core.Pattern.lit (Erlean.Core.Value.atom "false")]), (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true")), (Erlean.Core.Expr.letE
  [3]
  (Erlean.Core.Expr.primop "recv_wait_timeout" [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "infinity")])
  (Erlean.Core.Expr.caseE
    (Erlean.Core.Expr.var 3)
    [([Erlean.Core.Pattern.lit (Erlean.Core.Value.atom "true")],
      Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
      Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true")),
     ([Erlean.Core.Pattern.lit (Erlean.Core.Value.atom "false")],
      Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
      Erlean.Core.Expr.apply (Erlean.Core.Expr.var 0) [])])))])
private def importedActorProtocolModule_part_10 : Erlean.Core.Expr :=
Erlean.Core.Expr.letE ([1, 2]) (Erlean.Core.Expr.primop "recv_peek_message" []) importedActorProtocolModule_part_9
private def importedActorProtocolModule_part_11 : Erlean.Core.ClosureDef :=
{ params := ([]), body := importedActorProtocolModule_part_10, outerScope := ([]), recursiveBindings := ([(0, 0)]) }
private def importedActorProtocolModule_part_12 : Erlean.Core.Expr :=
Erlean.Core.Expr.caseE (Erlean.Core.Expr.var 9) ([(([Erlean.Core.Pattern.lit (Erlean.Core.Value.atom "true")]), (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true")), (Erlean.Core.Expr.caseE
  (Erlean.Core.Expr.var 10)
  [([Erlean.Core.Pattern.tuple
       [Erlean.Core.Pattern.lit (Erlean.Core.Value.atom "reply"),
        Erlean.Core.Pattern.var 11,
        Erlean.Core.Pattern.var 12]],
    Erlean.Core.Expr.call
      (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "erlang"))
      (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "=:="))
      [Erlean.Core.Expr.var 11, Erlean.Core.Expr.var 6],
    Erlean.Core.Expr.seq
      (Erlean.Core.Expr.primop "remove_message" [])
      (Erlean.Core.Expr.tuple [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "ok"), Erlean.Core.Expr.var 12])),
   ([Erlean.Core.Pattern.var 11],
    Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
    Erlean.Core.Expr.seq (Erlean.Core.Expr.primop "recv_next" []) (Erlean.Core.Expr.apply (Erlean.Core.Expr.var 8) []))])), (([Erlean.Core.Pattern.lit (Erlean.Core.Value.atom "false")]), (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true")), (Erlean.Core.Expr.letE
  [11]
  (Erlean.Core.Expr.primop "recv_wait_timeout" [Erlean.Core.Expr.var 5])
  (Erlean.Core.Expr.caseE
    (Erlean.Core.Expr.var 11)
    [([Erlean.Core.Pattern.lit (Erlean.Core.Value.atom "true")],
      Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
      Erlean.Core.Expr.lit (Erlean.Core.Value.atom "timeout")),
     ([Erlean.Core.Pattern.lit (Erlean.Core.Value.atom "false")],
      Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
      Erlean.Core.Expr.apply (Erlean.Core.Expr.var 8) [])])))])
private def importedActorProtocolModule_part_13 : Erlean.Core.Expr :=
Erlean.Core.Expr.letE ([9, 10]) (Erlean.Core.Expr.primop "recv_peek_message" []) importedActorProtocolModule_part_12
private def importedActorProtocolModule_part_14 : Erlean.Core.ClosureDef :=
{ params := ([]), body := importedActorProtocolModule_part_13, outerScope := ([7, 6, 3, 4, 5, 0, 1, 2]), recursiveBindings := ([(8, 1)]) }
private def importedActorProtocolModule_part_15 : Erlean.Core.Expr :=
Erlean.Core.Expr.caseE (Erlean.Core.Expr.var 1) ([(([Erlean.Core.Pattern.lit (Erlean.Core.Value.atom "true")]), (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true")), (Erlean.Core.Expr.caseE
  (Erlean.Core.Expr.var 2)
  [([Erlean.Core.Pattern.tuple
       [Erlean.Core.Pattern.lit (Erlean.Core.Value.atom "reply"),
        Erlean.Core.Pattern.var 3,
        Erlean.Core.Pattern.var 4]],
    Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
    Erlean.Core.Expr.seq
      (Erlean.Core.Expr.primop "remove_message" [])
      (Erlean.Core.Expr.tuple [Erlean.Core.Expr.var 3, Erlean.Core.Expr.var 4])),
   ([Erlean.Core.Pattern.var 3],
    Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
    Erlean.Core.Expr.seq (Erlean.Core.Expr.primop "recv_next" []) (Erlean.Core.Expr.apply (Erlean.Core.Expr.var 0) []))])), (([Erlean.Core.Pattern.lit (Erlean.Core.Value.atom "false")]), (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true")), (Erlean.Core.Expr.letE
  [3]
  (Erlean.Core.Expr.primop "recv_wait_timeout" [Erlean.Core.Expr.lit (Erlean.Core.Value.integer 0)])
  (Erlean.Core.Expr.caseE
    (Erlean.Core.Expr.var 3)
    [([Erlean.Core.Pattern.lit (Erlean.Core.Value.atom "true")],
      Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
      Erlean.Core.Expr.lit (Erlean.Core.Value.atom "empty")),
     ([Erlean.Core.Pattern.lit (Erlean.Core.Value.atom "false")],
      Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
      Erlean.Core.Expr.apply (Erlean.Core.Expr.var 0) [])])))])
private def importedActorProtocolModule_part_16 : Erlean.Core.Expr :=
Erlean.Core.Expr.letE ([1, 2]) (Erlean.Core.Expr.primop "recv_peek_message" []) importedActorProtocolModule_part_15
private def importedActorProtocolModule_part_17 : Erlean.Core.ClosureDef :=
{ params := ([]), body := importedActorProtocolModule_part_16, outerScope := ([]), recursiveBindings := ([(0, 2)]) }
private def importedActorProtocolModule_part_18 : Erlean.Core.ClosureDef :=
{ params := ([]), body := (Erlean.Core.Expr.letE
  [3]
  (Erlean.Core.Expr.primop "recv_wait_timeout" [Erlean.Core.Expr.var 1])
  (Erlean.Core.Expr.caseE
    (Erlean.Core.Expr.var 3)
    [([Erlean.Core.Pattern.lit (Erlean.Core.Value.atom "true")],
      Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
      Erlean.Core.Expr.lit (Erlean.Core.Value.atom "elapsed")),
     ([Erlean.Core.Pattern.lit (Erlean.Core.Value.atom "false")],
      Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
      Erlean.Core.Expr.apply (Erlean.Core.Expr.var 2) [])])), outerScope := ([1, 0]), recursiveBindings := ([(2, 3)]) }
/-- Generated from a pinned OTP Core artifact by the erlean importer. -/
def importedActorProtocolModule : Erlean.Core.Module :=
{ name := ("actor_protocol")
  exports := [(("exchange", 1)), (("module_info", 0)), (("module_info", 1)), (("poll", 0)), (("request", 3)), (("server", 0)), (("start", 0)), (("wait_only", 1))]
  functions := [importedActorProtocolModule_part_0, importedActorProtocolModule_part_1, importedActorProtocolModule_part_2, importedActorProtocolModule_part_4, importedActorProtocolModule_part_5, importedActorProtocolModule_part_6, importedActorProtocolModule_part_7, importedActorProtocolModule_part_8]
  closureCode := [importedActorProtocolModule_part_11, importedActorProtocolModule_part_14, importedActorProtocolModule_part_17, importedActorProtocolModule_part_18] }

attribute [reducible] importedActorProtocolModule_part_0 importedActorProtocolModule_part_1 importedActorProtocolModule_part_2 importedActorProtocolModule_part_3 importedActorProtocolModule_part_4 importedActorProtocolModule_part_5 importedActorProtocolModule_part_6 importedActorProtocolModule_part_7 importedActorProtocolModule_part_8 importedActorProtocolModule_part_9 importedActorProtocolModule_part_10 importedActorProtocolModule_part_11 importedActorProtocolModule_part_12 importedActorProtocolModule_part_13 importedActorProtocolModule_part_14 importedActorProtocolModule_part_15 importedActorProtocolModule_part_16 importedActorProtocolModule_part_17 importedActorProtocolModule_part_18

end Erlean.Examples
