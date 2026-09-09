-module(higher_order).
-export([map/2, map_identity/1]).

map(_Function, []) -> [];
map(Function, [Head | Tail]) -> [Function(Head) | map(Function, Tail)].

map_identity(Values) -> map(fun(Value) -> Value end, Values).
