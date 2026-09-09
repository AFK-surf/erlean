-module(actor_lifecycle).
-export([worker/0, monitor_normal/0, monitor_kill/0, demonitor_before_exit/0,
         normal_signal_ignored/0, linked_normal/0, linked_failure/0,
         unlink_failure/0, link_dead/0, self_normal/0]).

%% Proposed lifecycle fixture. Execute each scenario in an isolated process.
%% All scenarios use local pids and the default trap_exit=false setting.
worker() ->
    receive
        stop -> ok;
        {fail, Reason} -> exit(Reason);
        {ping, From} -> From ! pong, worker()
    end.

monitor_normal() ->
    Pid = spawn(?MODULE, worker, []),
    Reference = monitor(process, Pid),
    Pid ! stop,
    receive {'DOWN', Reference, process, Pid, Reason} -> Reason end.

monitor_kill() ->
    Pid = spawn(?MODULE, worker, []),
    Reference = monitor(process, Pid),
    exit(Pid, kill),
    receive {'DOWN', Reference, process, Pid, Reason} -> Reason end.

demonitor_before_exit() ->
    Pid = spawn(?MODULE, worker, []),
    Removed = monitor(process, Pid),
    demonitor(Removed),
    Retained = monitor(process, Pid),
    Pid ! stop,
    receive {'DOWN', Retained, process, Pid, normal} -> ok end,
    receive
        {'DOWN', Removed, process, Pid, _} -> unexpected_down
    after 0 -> removed
    end.

normal_signal_ignored() ->
    Pid = spawn(?MODULE, worker, []),
    Reference = monitor(process, Pid),
    exit(Pid, normal),
    Pid ! {ping, self()},
    receive pong -> ok end,
    Pid ! stop,
    receive {'DOWN', Reference, process, Pid, normal} -> survived end.

linked_normal() ->
    Pid = spawn(?MODULE, worker, []),
    Reference = monitor(process, Pid),
    link(Pid),
    Pid ! stop,
    receive {'DOWN', Reference, process, Pid, normal} -> survived end.

%% The caller must exit with boom, so an external observer should monitor it.
linked_failure() ->
    Pid = spawn(?MODULE, worker, []),
    link(Pid),
    Pid ! {fail, boom},
    receive after infinity -> unreachable end.

unlink_failure() ->
    Pid = spawn(?MODULE, worker, []),
    Reference = monitor(process, Pid),
    link(Pid),
    unlink(Pid),
    Pid ! {fail, boom},
    receive {'DOWN', Reference, process, Pid, boom} -> survived end.

link_dead() ->
    Pid = spawn(?MODULE, worker, []),
    Reference = monitor(process, Pid),
    Pid ! stop,
    receive {'DOWN', Reference, process, Pid, normal} -> ok end,
    try link(Pid) of
        _ -> unexpected_link
    catch
        error:noproc -> noproc
    end.

%% OTP 29 preserves exit/2's self-normal quirk; exit_signal/2 differs here.
self_normal() ->
    exit(self(), normal),
    unreachable.
