#!/usr/bin/env escript
%%! -noshell +S 1:1 +A 1
-mode(compile).

main([Source, Function, Arguments]) ->
    try run(Source, Function, Arguments)
    catch Class:Reason ->
        io:format(standard_error, "Actor oracle failed: ~p:~p~n", [Class, Reason]),
        halt(1)
    end;
main(_) ->
    io:format(standard_error, "Usage: actor_oracle.escript SOURCE FUNCTION JSON_ARGUMENTS~n", []),
    halt(2).

run(Source, Function, Arguments) ->
    VersionFile = filename:join([code:root_dir(), "releases", "29", "OTP_VERSION"]),
    {ok, VersionBytes} = file:read_file(VersionFile),
    <<"29.0.6">> = string:trim(VersionBytes),
    %% These are the pinned export flags with to_core omitted to produce BEAM.
    Options = [binary, no_copt, deterministic, return_errors, return_warnings],
    {ok, Module, Beam, _Warnings} = compile:noenv_file(Source, Options),
    {module, Module} = code:load_binary(Module, Source, Beam),
    Args = [decode(X) || X <- json:decode(list_to_binary(Arguments))],
    Parent = self(),
    Token = make_ref(),
    {Pid, Monitor} = spawn_monitor(fun() ->
        Outcome = try apply(Module, list_to_atom(Function), Args) of
            Value -> #{status => returned, values => [encode(Value)]}
        catch
            exit:Reason -> #{status => exited, reason => encode(Reason)};
            Class:Reason -> #{status => raised, class => Class, reason => encode(Reason)}
        end,
        Parent ! {Token, Outcome}
    end),
    Result = receive
        {Token, Outcome} ->
            %% The reporting process has finished the scenario; wait for its
            %% termination to ensure the observer monitor is also consumed.
            receive {'DOWN', Monitor, process, Pid, _} -> Outcome end;
        {'DOWN', Monitor, process, Pid, Reason} ->
            %% Exit signals (including self-normal) bypass exception handlers.
            #{status => exited, reason => encode(Reason)}
    after 10000 ->
        exit(Pid, kill),
        error(oracle_watchdog_expired)
    end,
    io:put_chars([json:encode(Result), $\n]).

decode(#{<<"tag">> := <<"integer">>, <<"value">> := Value}) -> binary_to_integer(Value);
decode(#{<<"tag">> := <<"atom">>, <<"value">> := Value}) -> binary_to_atom(Value);
decode(#{<<"tag">> := <<"nil">>}) -> [];
decode(#{<<"tag">> := <<"tuple">>, <<"items">> := Items}) ->
    list_to_tuple([decode(X) || X <- Items]);
decode(#{<<"tag">> := <<"list">>, <<"items">> := Items, <<"tail">> := Tail}) ->
    lists:foldr(fun(X, Acc) -> [decode(X) | Acc] end, decode(Tail), Items);
decode(#{<<"tag">> := <<"bitstring">>, <<"bits">> := Count, <<"hex">> := Hex}) ->
    N = binary_to_integer(Count),
    <<Bits:N/bitstring, _/bitstring>> = binary:decode_hex(Hex),
    Bits;
decode(Value) -> error({unsupported_oracle_input, Value}).

encode(X) when is_integer(X) -> #{tag => integer, value => integer_to_binary(X)};
encode(X) when is_atom(X) -> #{tag => atom, value => atom_to_binary(X)};
encode([]) -> #{tag => nil};
encode([H | T]) -> #{tag => cons, head => encode(H), tail => encode(T)};
encode(X) when is_tuple(X) -> #{tag => tuple, items => [encode(V) || V <- tuple_to_list(X)]};
encode(X) when is_bitstring(X) ->
    N = bit_size(X), Pad = (8 - N rem 8) rem 8,
    #{tag => bitstring, bits => integer_to_binary(N),
      hex => binary:encode_hex(<<X/bitstring, 0:Pad>>, lowercase)};
encode(Value) -> error({unsupported_oracle_output, Value}).
