-module(actor_protocol).
-export([start/0, server/0, request/3, poll/0, wait_only/1, exchange/1]).

%% Proposed actor fixture; no actor execution support is claimed by its presence.
start() -> spawn(?MODULE, server, []).

exchange(Value) ->
    Server = start(),
    Answer = request(Server, Value, infinity),
    Server ! stop,
    Answer.

server() ->
    receive
        {request, From, Reference, Value} ->
            From ! {reply, Reference, Value},
            server();
        stop -> ok
    end.

request(Server, Value, Timeout) ->
    Reference = make_ref(),
    Server ! {request, self(), Reference, Value},
    receive
        {reply, Reference, Reply} -> {ok, Reply}
    after Timeout -> timeout
    end.

%% Unmatched messages must remain in the mailbox after this zero-timeout scan.
poll() ->
    receive
        {reply, Reference, Reply} -> {Reference, Reply}
    after 0 -> empty
    end.

wait_only(Timeout) ->
    receive after Timeout -> elapsed end.
