-module(erlean_maps).
-export([literal/0, construct/4, assoc/3, exact/3, mixed/5, exact_then_assoc/5,
         literal_pattern/1, nested_pattern/1, empty_pattern/1,
         guard_lookup/2, exact_equal/2, equal/2, not_equal/2, exact_not_equal/2,
         binary_id/1, is_map_value/1, get/2, has_key/2, size/1,
         library_get/2, library_get_default/3, library_find/2, library_put/3,
         library_update/3, library_remove/2, library_take/2, library_merge/2,
         key_order/1, value_order/1, pair_order/1, exact_value_order/1,
         base_order/0, ambiguous_exact/1, packed_pattern/1]).

%% This module must not be named maps: the oracle also calls OTP's maps module.
literal() -> #{answer => 42, nested => #{items => [a, b]}, 1 => integer_key}.
construct(K1, V1, K2, V2) -> #{K1 => V1, K2 => V2}.
assoc(Map, Key, Value) -> Map#{Key => Value}.
exact(Map, Key, Value) -> Map#{Key := Value}.
mixed(Map, K1, V1, K2, V2) -> Map#{K1 => V1, K2 := V2}.
exact_then_assoc(Map, K1, V1, K2, V2) -> Map#{K1 := V1, K2 => V2}.
ambiguous_exact(Map) -> Map#{z := 1, a := 2}.

literal_pattern(#{answer := Value}) -> {found, Value};
literal_pattern(_) -> absent.

packed_pattern(#{status := <<"ready">>}) -> ready;
packed_pattern(#{status := <<5:3>>}) -> partial;
packed_pattern(_) -> absent.

nested_pattern(#{outer := #{inner := Value}}) -> {found, Value};
nested_pattern(_) -> absent.

empty_pattern(#{}) -> matched;
empty_pattern(_) -> absent.

guard_lookup(Key, Map) when is_map(Map), is_map_key(Key, Map) -> map_get(Key, Map);
guard_lookup(_, _) -> absent.

exact_equal(Left, Right) -> Left =:= Right.
equal(Left, Right) -> Left == Right.
not_equal(Left, Right) -> Left /= Right.
exact_not_equal(Left, Right) -> Left =/= Right.
binary_id(Value) when is_binary(Value), Value =/= <<>> -> accepted;
binary_id(_) -> rejected.
is_map_value(Value) -> is_map(Value).
get(Key, Map) -> map_get(Key, Map).
has_key(Key, Map) -> is_map_key(Key, Map).
size(Map) -> map_size(Map).
library_get(Key, Map) -> maps:get(Key, Map).
library_get_default(Key, Map, Default) -> maps:get(Key, Map, Default).
library_find(Key, Map) -> maps:find(Key, Map).
library_put(Key, Value, Map) -> maps:put(Key, Value, Map).
library_update(Key, Value, Map) -> maps:update(Key, Value, Map).
library_remove(Key, Map) -> maps:remove(Key, Map).
library_take(Key, Map) -> maps:take(Key, Map).
library_merge(Left, Right) -> maps:merge(Left, Right).

%% Raised operands distinguish evaluation order from update validation order.
key_order(Map) -> Map#{(erlang:error(first_key)) => value}.
value_order(Map) -> Map#{key => erlang:error(first_value)}.
pair_order(Map) ->
    Map#{(erlang:error(first_key)) => erlang:error(first_value),
         (erlang:error(second_key)) => erlang:error(second_value)}.
exact_value_order(Map) -> Map#{missing := first, other := erlang:error(later_value)}.
base_order() -> (erlang:error(base))#{(erlang:error(key)) => erlang:error(value)}.
