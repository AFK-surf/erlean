-module(closures).
-export([capture/2, make_adder/1, named_sum/2, nested/3, map_add/2]).

capture(Offset, Value) ->
    Add = fun(X) -> X + Offset end,
    Add(Value).

make_adder(Offset) ->
    fun(X) -> X + Offset end.

named_sum(Offset, Values) ->
    Sum = fun Recur([], Acc) -> Acc;
              Recur([Head | Tail], Acc) -> Recur(Tail, Head + Acc)
          end,
    Sum(Values, Offset).

nested(A, B, C) ->
    Outer = fun(X) -> fun(Y) -> A + X + Y end end,
    Inner = Outer(B),
    Inner(C).

map_add(Offset, Values) ->
    Add = fun(X) -> X + Offset end,
    Map = fun Recur([]) -> [];
              Recur([Head | Tail]) -> [Add(Head) | Recur(Tail)]
          end,
    Map(Values).
