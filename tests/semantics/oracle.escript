#!/usr/bin/env escript
%%! -noshell
-mode(compile).

main([Source, Function, Arguments]) ->
    VersionFile = filename:join([code:root_dir(), "releases", "29", "OTP_VERSION"]),
    {ok, VersionBytes} = file:read_file(VersionFile),
    <<"29.0.6">> = string:trim(VersionBytes),
    {Module, Beam} = load_artifact(Source),
    {module, Module} = code:load_binary(Module, Source, Beam),
    Args = [decode(X) || X <- json:decode(list_to_binary(Arguments))],
    Result = try apply(Module, list_to_atom(Function), Args) of
        Value -> #{status => returned, values => [encode(Value)]}
    catch Class:Reason ->
        #{status => raised, class => Class, reason => encode(Reason)}
    end,
    io:put_chars([json:encode(Result), $\n]).

load_artifact(Source) ->
    case filename:extension(Source) of
        ".beam" ->
            {ok, {Module, _}} = beam_lib:chunks(Source, [exports]),
            {ok, Beam} = file:read_file(Source),
            {Module, Beam};
        ".erl" ->
            Options = [binary, no_copt, deterministic, return_errors, return_warnings],
            {ok, Module, Beam, _Warnings} = compile:noenv_file(Source, Options),
            {Module, Beam}
    end.

decode(#{<<"tag">> := <<"integer">>, <<"value">> := Value}) -> binary_to_integer(Value);
decode(#{<<"tag">> := <<"atom">>, <<"value">> := Value}) -> binary_to_atom(Value);
decode(#{<<"tag">> := <<"nil">>}) -> [];
decode(#{<<"tag">> := <<"bitstring">>, <<"bits">> := Count, <<"hex">> := Hex}) ->
    N = binary_to_integer(Count),
    <<Bits:N/bitstring, _/bitstring>> = binary:decode_hex(Hex),
    Bits;
decode(#{<<"tag">> := <<"tuple">>, <<"items">> := Items}) ->
    list_to_tuple([decode(X) || X <- Items]);
decode(#{<<"tag">> := <<"list">>, <<"items">> := Items, <<"tail">> := Tail}) ->
    lists:foldr(fun(X, Acc) -> [decode(X) | Acc] end, decode(Tail), Items).

encode(X) when is_integer(X) -> #{tag => integer, value => integer_to_binary(X)};
encode(X) when is_atom(X) -> #{tag => atom, value => atom_to_binary(X)};
encode([]) -> #{tag => nil};
encode([H | T]) -> #{tag => cons, head => encode(H), tail => encode(T)};
encode(X) when is_tuple(X) -> #{tag => tuple, items => [encode(V) || V <- tuple_to_list(X)]};
encode(X) when is_bitstring(X) ->
    N = bit_size(X), Pad = (8 - N rem 8) rem 8,
    #{tag => bitstring, bits => integer_to_binary(N),
      hex => binary:encode_hex(<<X/bitstring, 0:Pad>>, lowercase)}.
