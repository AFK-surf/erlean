-module(modular_client).
-export([relay/1]).

relay(Value) -> identity:identity(Value).
