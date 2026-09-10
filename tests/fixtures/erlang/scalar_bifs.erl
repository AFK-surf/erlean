%% Scalar and structural BIF coverage: integer comparison, strict boolean
%% operators, type predicates, byte and element accounting, byte extraction,
%% and iolist flattening. Each exported function returns a term that both the
%% portable oracle and the imported Core encode directly, so a difference is
%% observable without inspecting map ordering or opaque runtime terms.
-module(scalar_bifs).
-export([less/2, greater/2, at_least/2, minimum/2, maximum/2, either/2,
         negate/1, list_shape/1, boolean_shape/1, float_shape/1, byte_count/1,
         element_count/1, byte_values/1, flatten/1]).

less(A, B) -> A < B.
greater(A, B) -> A > B.
at_least(A, B) -> A >= B.
minimum(A, B) -> erlang:min(A, B).
maximum(A, B) -> erlang:max(A, B).
either(A, B) -> A or B.
negate(A) -> not A.
list_shape(Value) -> is_list(Value).
boolean_shape(Value) -> is_boolean(Value).
float_shape(Value) -> is_float(Value).
byte_count(Value) -> byte_size(Value).
element_count(Value) -> length(Value).
byte_values(Value) -> binary_to_list(Value).
flatten(Value) -> iolist_to_binary(Value).
