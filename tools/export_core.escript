#!/usr/bin/env escript
%%! -noshell
-mode(compile).

main(["--check-encoding"]) ->
    #{<<"value">> := <<"-1234567890123456789012345678901234567890">>} =
        term(-1234567890123456789012345678901234567890),
    #{<<"bits">> := <<"3">>, <<"hex">> := <<"a0">>} = term(<<5:3>>),
    #{<<"bits">> := <<"8000000000000000">>} = term(-0.0),
    io:format("Direct term encoding checks passed.~n", []);
main(["--forms", Source, Output]) ->
    guarded_export(Source, Output, forms, <<"29.0.6">>);
main(["--otp", Expected, "--forms", Source, Output]) ->
    guarded_export(Source, Output, forms, list_to_binary(Expected));
main(["--otp", Expected, Source, Output]) ->
    guarded_export(Source, Output, file, list_to_binary(Expected));
main([Source, Output]) ->
    guarded_export(Source, Output, file, <<"29.0.6">>);
main(_) ->
    io:format(standard_error, "Usage: asdf exec escript tools/export_core.escript [--otp 29.0.2|29.0.6] [--forms] SOURCE OUTPUT_DIRECTORY~n", []),
    halt(2).

guarded_export(Source, Output, Kind, Expected) ->
    try export(Source, Output, Kind, Expected)
    catch Class:Reason:Stack ->
        io:format(standard_error, "Core export failed: ~p:~p~n~p~n", [Class, Reason, Stack]),
        halt(1)
    end.

export(Source, Output, Kind, Expected) ->
    case Expected of
        <<"29.0.2">> -> ok;
        <<"29.0.6">> -> ok;
        _ -> error({unsupported_otp_profile, Expected})
    end,
    VersionFile = filename:join([code:root_dir(), "releases", "29", "OTP_VERSION"]),
    {ok, VersionBytes} = file:read_file(VersionFile),
    Version = string:trim(VersionBytes),
    case Version of
        Expected -> ok;
        _ -> error({unsupported_otp_patch, Version, expected, Expected})
    end,
    Options = [to_core, binary, no_copt, deterministic, return_errors, return_warnings],
    Compiled = case Kind of
        file -> compile:noenv_file(Source, Options);
        forms ->
            %% Only consume trusted local compiler output, never untrusted ETF.
            {ok, FormsBytes} = file:read_file(Source),
            compile:noenv_forms(binary_to_term(FormsBytes), Options)
    end,
    {Module, Core, Warnings} = case Compiled of
        {ok, M, C, W} -> {M, C, W};
        Other -> error({compile_failed, Other})
    end,
    %% Reject compiler-internal node kinds that have no declared record layout.
    Counts = cerl_trees:fold(fun inventory_node/2,
                           #{<<"constructs">> => #{}, <<"calls">> => #{},
                             <<"primops">> => #{}, <<"dynamic_calls">> => 0}, Core),
    Artifact = #{<<"format">> => <<"erlean.raw-core">>, <<"version">> => 1,
                 <<"otp_version">> => Version,
                 <<"module">> => atom_to_binary(Module), <<"core">> => term(Core)},
    CoreBytes = encode(Artifact),
    {ok, SourceBytes} = file:read_file(Source),
    {ok, ExporterBytes} = file:read_file(escript:script_name()),
    _ = application:load(compiler),
    {ok, CompilerVersion} = application:get_key(compiler, vsn),
    Manifest = #{<<"format">> => <<"erlean.import-manifest">>, <<"version">> => 1,
                 <<"otp_version">> => Version,
                 <<"source_language">> => <<"erlang">>,
                 <<"source_compiler">> => <<"OTP compiler">>,
                 <<"source_compiler_version">> => list_to_binary(CompilerVersion),
                 <<"source">> => list_to_binary(Source),
                 <<"source_sha256">> => hash(SourceBytes),
                 <<"core_sha256">> => hash(CoreBytes),
                 <<"exporter_sha256">> => hash(ExporterBytes),
                 <<"compiler_options">> => [atom_to_binary(O) || O <- Options],
                 <<"extraction_stage">> => <<"to_core + no_copt; after v3_core, before sys_core_bsm">>,
                 <<"semantic_profile">> => <<"raw-only-v1">>,
                 <<"system_architecture">> => list_to_binary(erlang:system_info(system_architecture)),
                 <<"endianness">> => atom_to_binary(erlang:system_info(endian)),
                 <<"warnings">> => term(Warnings)},
    ok = filelib:ensure_dir(filename:join(Output, "placeholder")),
    ok = file:write_file(filename:join(Output, "core.json"), CoreBytes),
    ok = file:write_file(filename:join(Output, "manifest.json"), encode(Manifest)),
    ok = file:write_file(filename:join(Output, "inventory.json"), encode(Counts)),
    io:format("Exported ~p with OTP ~s to ~s~n", [Module, Version, Output]).

inventory_node(Node, Acc0) ->
    Type = cerl:type(Node),
    Supported = [alias, apply, binary, bitstr, call, 'case', 'catch', clause,
                 cons, 'fun', 'let', letrec, literal, map, map_pair, module,
                 primop, 'receive', seq, 'try', tuple, values, var],
    case lists:member(Type, Supported) of
        true -> ok;
        false -> error({unsupported_core_node, Type, cerl:get_ann(Node)})
    end,
    Acc = bump(<<"constructs">>, atom_to_binary(Type), Acc0),
    case Type of
        call ->
            M = cerl:call_module(Node), F = cerl:call_name(Node),
            case cerl:is_c_atom(M) andalso cerl:is_c_atom(F) of
                true -> bump(<<"calls">>, iolist_to_binary(io_lib:format("~p:~p/~p",
                    [cerl:atom_val(M), cerl:atom_val(F), cerl:call_arity(Node)])), Acc);
                false -> Acc#{<<"dynamic_calls">> := maps:get(<<"dynamic_calls">>, Acc) + 1}
            end;
        primop -> bump(<<"primops">>, atom_to_binary(cerl:atom_val(cerl:primop_name(Node))), Acc);
        _ -> Acc
    end.

bump(Group, Key, Acc) ->
    Counts = maps:get(Group, Acc),
    Acc#{Group := maps:update_with(Key, fun(N) -> N + 1 end, 1, Counts)}.

%% Every Erlang term is tagged; JSON numbers never carry language integers.
term(A) when is_atom(A) -> #{<<"tag">> => <<"atom">>, <<"value">> => atom_to_binary(A)};
term(I) when is_integer(I) -> #{<<"tag">> => <<"integer">>, <<"value">> => integer_to_binary(I)};
term(F) when is_float(F) -> #{<<"tag">> => <<"float">>, <<"bits">> => hex(<<F:64/float>>)};
term([]) -> #{<<"tag">> => <<"nil">>};
term([_ | _] = L) ->
    {Items, Tail} = list_parts(L, []),
    #{<<"tag">> => <<"list">>, <<"items">> => Items, <<"tail">> => term(Tail)};
term(T) when is_tuple(T) ->
    #{<<"tag">> => <<"tuple">>, <<"items">> => [term(E) || E <- tuple_to_list(T)]};
term(M) when is_map(M) ->
    #{<<"tag">> => <<"map">>,
      <<"entries">> => [[term(K), term(V)] || {K, V} <- lists:sort(maps:to_list(M))]};
term(B) when is_bitstring(B) ->
    N = bit_size(B), Pad = (8 - N rem 8) rem 8,
    #{<<"tag">> => <<"bitstring">>, <<"bits">> => integer_to_binary(N),
      <<"hex">> => hex(<<B/bitstring, 0:Pad>>)};
term(T) -> error({unsupported_literal_or_annotation, T}).

list_parts([H | T], Acc) -> list_parts(T, [term(H) | Acc]);
list_parts(Tail, Acc) -> {lists:reverse(Acc), Tail}.

hex(B) -> binary:encode_hex(B, lowercase).
hash(B) -> hex(crypto:hash(sha256, B)).
encode(Term) -> iolist_to_binary([json:encode(Term), $\n]).
