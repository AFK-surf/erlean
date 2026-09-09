-module(erlean_float_transport).
-export([identity/1, literal/0, wrap/1, nested/1, put_get/2, plus/2, minus/2,
         multiply/2, equal/2, exact_equal/2, key/1]).

%% Float values are transported without assigning numeric or equality semantics.
identity(Value) -> Value.
literal() -> #{payload => 1.5}.
wrap(Value) -> [Value, {payload, Value}].
nested(Value) -> #{outer => #{payload => Value}}.
put_get(Value, Map) -> maps:get(payload, maps:put(payload, Value, Map)).

%% These operations delimit the unsupported profile in the compatibility test.
plus(Left, Right) -> Left + Right.
minus(Left, Right) -> Left - Right.
multiply(Left, Right) -> Left * Right.
equal(Left, Right) -> Left == Right.
exact_equal(Left, Right) -> Left =:= Right.
key(Value) -> #{Value => payload}.
