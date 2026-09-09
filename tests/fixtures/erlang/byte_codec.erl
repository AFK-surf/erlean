-module(byte_codec).
-export([encode/1, decode/1, encode_pair/2, decode_pair/1, roundtrip/1]).

%% Proposed codec profile: fixed 8-bit unsigned big-endian integer segments.
%% The roundtrip contract will require integer inputs in the range 0 through 255.
encode(Byte) -> <<Byte:8/unsigned-big-integer>>.

decode(<<Byte:8/unsigned-big-integer>>) -> {ok, Byte};
decode(_) -> error.

encode_pair(First, Second) ->
    <<First:8/unsigned-big-integer, Second:8/unsigned-big-integer>>.

decode_pair(<<First:8/unsigned-big-integer, Second:8/unsigned-big-integer>>) ->
    {ok, First, Second};
decode_pair(_) -> error.

roundtrip(Byte) -> decode(encode(Byte)).
