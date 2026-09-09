-module(dijkstra).
-export([distances/2]).

%% Directed graphs use {From, To, Weight} triples with natural-number vertices
%% and nonnegative integer weights. Parallel edges, self-loops, and zero cycles
%% are allowed. Results contain only reachable vertices, in settlement order.
distances(Source, Edges) ->
    case nonnegative_integer(Source) of
        true ->
            case valid_edges(Edges) of
                true -> reverse(search([{Source, 0}], Edges, []), []);
                false -> error(badarg)
            end;
        false -> error(badarg)
    end.

%% Keep comparison behind the type test in an explicit case. The restricted
%% semantics intentionally does not implement Erlang's cross-type term order.
nonnegative_integer(Value) ->
    case is_integer(Value) of
        true -> 0 =< Value;
        false -> false
    end.

valid_edges([]) -> true;
valid_edges([{From, To, Weight} | Rest]) ->
    case nonnegative_integer(From) of
        false -> false;
        true ->
            case nonnegative_integer(To) of
                false -> false;
                true ->
                    case nonnegative_integer(Weight) of
                        false -> false;
                        true -> valid_edges(Rest)
                    end
            end
    end;
valid_edges(_) -> false.

search([], _, Settled) -> Settled;
search([{Vertex, Distance} | Queue], Edges, Settled) ->
    case settled(Vertex, Settled) of
        true -> search(Queue, Edges, Settled);
        false ->
            {NextQueue, Remaining} = expand(Vertex, Distance, Edges, Queue),
            search(NextQueue, Remaining, [{Vertex, Distance} | Settled])
    end.

settled(_, []) -> false;
settled(Vertex, [{Other, _} | Rest]) ->
    case Vertex =:= Other of
        true -> true;
        false -> settled(Vertex, Rest)
    end.

%% Consuming outgoing edges makes queue length plus remaining edge count drop
%% on every search iteration, including duplicate queue entries.
expand(_, _, [], Queue) -> {Queue, []};
expand(Vertex, Distance, [{From, To, Weight} | Rest], Queue) ->
    case Vertex =:= From of
        true -> expand(Vertex, Distance, Rest, insert(To, Distance + Weight, Queue));
        false ->
            {NextQueue, Remaining} = expand(Vertex, Distance, Rest, Queue),
            {NextQueue, [{From, To, Weight} | Remaining]}
    end.

%% New entries precede existing entries at equal distance. Correct distances do
%% not depend on this tie convention, but settlement order is deterministic.
insert(Vertex, Distance, []) -> [{Vertex, Distance}];
insert(Vertex, Distance, [{Other, OtherDistance} | Rest]) ->
    case Distance =< OtherDistance of
        true -> [{Vertex, Distance}, {Other, OtherDistance} | Rest];
        false -> [{Other, OtherDistance} | insert(Vertex, Distance, Rest)]
    end.

reverse([], Result) -> Result;
reverse([Head | Tail], Result) -> reverse(Tail, [Head | Result]).
