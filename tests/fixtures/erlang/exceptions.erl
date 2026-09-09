-module(exceptions).
-export([handle/2, try_of/1, nested/1, after_success/1, after_failure/1,
         after_override/1, guard_error/1, catch_throw/1, catch_exit/1]).

handle(Class, Reason) ->
    try raise(Class, Reason)
    catch
        throw:Caught -> {throw, Caught};
        error:Caught -> {error, Caught};
        exit:Caught -> {exit, Caught}
    end.

raise(throw, Reason) -> throw(Reason);
raise(error, Reason) -> error(Reason);
raise(exit, Reason) -> exit(Reason);
raise(normal, Value) -> Value.

try_of(Value) ->
    try Value of
        {ok, Result} -> Result
    catch
        error:Reason -> {caught, Reason}
    end.

nested(Value) ->
    try
        try error(Value)
        catch error:Reason -> throw({inner, Reason})
        end
    catch throw:OuterReason -> {outer, OuterReason}
    end.

after_success(Value) ->
    try Value after cleanup(Value) end.

after_failure(Value) ->
    try error(Value) after cleanup(Value) end.

after_override(Value) ->
    try error(original) after error(Value) end.

cleanup(Value) -> {discarded, Value}.

guard_error(Value) when hd(Value) -> matched;
guard_error(_) -> fallback.

catch_throw(Value) -> catch throw(Value).

catch_exit(Value) -> catch exit(Value).
