-module(identity).
-export([identity/1, pair/2, answer/0]).

identity(Value) -> Value.
pair(Left, Right) -> {Left, Right}.
answer() -> 42.
