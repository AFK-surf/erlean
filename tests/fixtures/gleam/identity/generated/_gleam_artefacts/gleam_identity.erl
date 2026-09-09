-module(gleam_identity).
-compile([no_auto_import, nowarn_ignored, nowarn_unused_vars, nowarn_unused_function, nowarn_nomatch, inline]).
-export([identity/1, pair/2, empty/0, prepend/2]).

-file("src/gleam_identity.gleam", 1).
-spec identity(I) -> I.
identity(Value) ->
    Value.

-file("src/gleam_identity.gleam", 5).
-spec pair(J, K) -> {J, K}.
pair(Left, Right) ->
    {Left, Right}.

-file("src/gleam_identity.gleam", 9).
-spec empty() -> list(any()).
empty() ->
    [].

-file("src/gleam_identity.gleam", 13).
-spec prepend(N, list(N)) -> list(N).
prepend(Head, Tail) ->
    [Head | Tail].

