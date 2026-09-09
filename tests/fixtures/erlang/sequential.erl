-module(sequential).
-export([reverse/1, append/2, classify/1, arithmetic/2, context/1,
         tuple_order/0, cons_order/0, loop/0, identity/1]).

reverse(Xs) -> reverse_acc(Xs, []).
reverse_acc([], Acc) -> Acc;
reverse_acc([H | T], Acc) -> reverse_acc(T, [H | Acc]).

append([], Ys) -> Ys;
append([H | T], Ys) -> [H | append(T, Ys)].

classify(X) when is_integer(X) -> integer;
classify(_) -> other.

arithmetic(X, Y) -> X + Y * 2.
identity(X) -> X.
context(X) -> {identity(other), X, identity(X)}.
tuple_order() -> {erlang:error(first), erlang:error(second)}.
cons_order() -> [erlang:error(first) | erlang:error(second)].
loop() -> loop().
