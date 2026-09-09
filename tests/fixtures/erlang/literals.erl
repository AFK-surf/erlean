-module(literals).
-export([terms/0]).

terms() ->
    {1234567890123456789012345678901234567890,
     -1234567890123456789012345678901234567890,
     1.0, <<5:3>>, [a | b], #{1 => integer_key, 1.0 => float_key},
     'atom with spaces'}.
