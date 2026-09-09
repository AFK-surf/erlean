#!/usr/bin/env escript
%%! -noshell
-mode(compile).

%% A portable OTP oracle for trusted test modules. JSON output preserves exact
%% integer, float-bit, and bitstring representations. Maps have no output order.
main(Arguments) ->
    try
        {Version, Command} = options(Arguments),
        check_version(Version),
        Result = execute(Command),
        io:put_chars([json:encode(Result), $\n])
    catch Class:Reason ->
        io:format(standard_error, "otp_oracle: ~p:~p~n", [Class, Reason]),
        halt(1)
    end.

options(["--otp", Version | Command]) when Version =:= "29.0.2"; Version =:= "29.0.6" ->
    {Version, Command};
options(["--otp", Version | _]) -> error({unsupported_otp_profile, Version});
options(Command) -> {"29.0.6", Command}.

check_version(Version) ->
    VersionFile = filename:join([code:root_dir(), "releases", "29", "OTP_VERSION"]),
    {ok, VersionBytes} = file:read_file(VersionFile),
    Running = string:trim(VersionBytes),
    case Running =:= list_to_binary(Version) of
        true -> ok;
        false -> error({otp_patch_mismatch, Version, Running})
    end.

execute(["--batch", Source, CasesFile | Dependencies]) ->
    {ok, CasesJson} = file:read_file(CasesFile),
    Cases = json:decode(CasesJson),
    true = is_list(Cases),
    %% Validate every case before executing any case. Encode the complete result
    %% before publishing it, so validation failures cannot leak partial results.
    Prepared = [prepare_case(Case) || Case <- Cases],
    Module = load_test_module(Source, Dependencies),
    [evaluate(Module, Function, Args) || {Function, Args} <- Prepared];
execute([Source, Function, Arguments | Dependencies]) ->
    false = lists:prefix("--", Source),
    Args = json:decode(list_to_binary(Arguments)),
    true = is_list(Args),
    Decoded = [decode(X) || X <- Args],
    Module = load_test_module(Source, Dependencies),
    evaluate(Module, list_to_atom(Function), Decoded);
execute(_) ->
    error("Usage: otp_oracle.escript [--otp VERSION] SOURCE FUNCTION JSON [DEPS] | "
          "[--otp VERSION] --batch SOURCE CASES_JSON_FILE [DEPS]").

prepare_case(#{<<"function">> := Function, <<"arguments">> := Arguments})
        when is_binary(Function), is_list(Arguments) ->
    {binary_to_atom(Function), [decode(X) || X <- Arguments]};
prepare_case(_) -> error(invalid_batch_case).

load_test_module(Source, Dependencies) ->
    lists:foreach(fun(Dependency) ->
        {Name, Code} = load_artifact(Dependency),
        {module, Name} = code:load_binary(Name, Dependency, Code)
    end, Dependencies),
    {Module, Beam} = load_artifact(Source),
    {module, Module} = code:load_binary(Module, Source, Beam),
    Module.

evaluate(Module, Function, Args) ->
    Outcome = try apply(Module, Function, Args) of
        Value -> {returned, Value}
    catch Class:Reason ->
        {raised, Class, Reason}
    end,
    case Outcome of
        {returned, Result} -> #{status => returned, values => [encode(Result)]};
        {raised, ExceptionClass, ExceptionReason} ->
            #{status => raised, class => ExceptionClass, reason => encode(ExceptionReason)}
    end.

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
decode(#{<<"tag">> := <<"float">>, <<"bits">> := Hex}) ->
    <<Value:64/float>> = binary:decode_hex(Hex),
    Value;
decode(#{<<"tag">> := <<"atom">>, <<"value">> := Value}) -> binary_to_atom(Value);
decode(#{<<"tag">> := <<"nil">>}) -> [];
decode(#{<<"tag">> := <<"bitstring">>, <<"bits">> := Count, <<"hex">> := Hex}) ->
    N = binary_to_integer(Count),
    <<Bits:N/bitstring, _/bitstring>> = binary:decode_hex(Hex),
    Bits;
decode(#{<<"tag">> := <<"tuple">>, <<"items">> := Items}) ->
    list_to_tuple([decode(X) || X <- Items]);
decode(#{<<"tag">> := <<"map">>, <<"entries">> := Entries}) ->
    maps:from_list([{decode(K), decode(V)} || [K, V] <- Entries]);
decode(#{<<"tag">> := <<"cons">>, <<"head">> := Head, <<"tail">> := Tail}) ->
    [decode(Head) | decode(Tail)];
decode(#{<<"tag">> := <<"list">>, <<"items">> := Items, <<"tail">> := Tail}) ->
    lists:foldr(fun(X, Acc) -> [decode(X) | Acc] end, decode(Tail), Items).

encode(X) when is_integer(X) -> #{tag => integer, value => integer_to_binary(X)};
encode(X) when is_float(X) ->
    #{tag => float, bits => binary:encode_hex(<<X:64/float>>, lowercase)};
encode(X) when is_atom(X) -> #{tag => atom, value => atom_to_binary(X)};
encode([]) -> #{tag => nil};
encode([H | T]) -> #{tag => cons, head => encode(H), tail => encode(T)};
encode(X) when is_tuple(X) -> #{tag => tuple, items => [encode(V) || V <- tuple_to_list(X)]};
encode(X) when is_map(X) ->
    #{tag => map, entries => [[encode(K), encode(V)] || {K, V} <- maps:to_list(X)]};
encode(X) when is_bitstring(X) ->
    N = bit_size(X), Pad = (8 - N rem 8) rem 8,
    #{tag => bitstring, bits => integer_to_binary(N),
      hex => binary:encode_hex(<<X/bitstring, 0:Pad>>, lowercase)}.
