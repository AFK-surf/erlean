import Erlean.Examples.Protocol.Runtime

namespace Erlean.Examples.ProtocolInvariant

open Core Semantics Erlean.Runtime Erlean.Examples.Protocol Erlean.Logic

theorem client_program_halt
    (publicPayload : payload.isPublic = true)
    (valid : ClientControl payload stage process) (active : ProcessActive process)
    (halted : stepLocal [importedActorProtocolModule] process.state = .halt outcome)
    (notRuntime : ∀ name args, process.state.control ≠ .runtime name args) :
    stage = .done ∧ outcome = .returned [.tuple [.atom "ok", payload]] := by
  obtain ⟨endpoint, found, _, segment⟩ := client_active_phase valid active
  have equal := reachesBoundary_halt segment halted
  apply clientBoundary_program_halt payload publicPayload stage endpoint found
  · simpa [← equal] using halted
  · intro name args
    simpa [← equal] using notRuntime name args

theorem server_program_halt
    (publicPayload : payload.isPublic = true)
    (valid : ServerControl payload process) (active : ProcessActive process)
    (halted : stepLocal [importedActorProtocolModule] process.state = .halt outcome)
    (notRuntime : ∀ name args, process.state.control ≠ .runtime name args) :
    outcome = .returned [.atom "ok"] := by
  obtain ⟨stage, _, endpoint, found, _, segment⟩ := server_active_phase valid active
  have equal := reachesBoundary_halt segment halted
  apply serverBoundary_program_halt payload publicPayload stage endpoint found
  · simpa [← equal] using halted
  · intro name args
    simpa [← equal] using notRuntime name args

/-- A normal program return in this closed profile generates no lifecycle
    signals, because no links or monitors have been established. -/
theorem finish_return_no_lifecycle (system : System) (process : Process) (values : Values)
    (links : system.links = []) (monitors : system.monitors = []) :
    finishProcess system process (.returned values) =
      system.update { process with status := .finished (.returned values) } := by
  cases system
  simp_all [finishProcess, System.update]

theorem closedExchange_halt (invariant : ClosedExchange payload system)
    (found : system.lookup pid = some process)
    (active : ProcessActive process) (publicPayload : payload.isPublic = true)
    (halted : stepLocal [importedActorProtocolModule] process.state = .halt outcome)
    (notRuntime : ∀ name args, process.state.control ≠ .runtime name args) :
    ClosedExchange payload (finishProcess system process outcome) := by
  obtain ⟨network, fresh, links, monitors, stage, client, clientValid, referenceCounter, population⟩ := invariant
  have member : process ∈ system.processes := List.mem_of_find?_eq_some found
  by_cases spawning : stage = .spawn
  · simp only [spawning, if_pos] at population
    have equal : process = client := by simpa [population.1] using member
    subst process
    have finished := client_program_halt publicPayload clientValid active halted notRuntime
    simp [spawning] at finished
  · simp only [spawning, if_false] at population
    obtain ⟨server, processes, nextPid, serverValid⟩ := population
    have alternatives : process = client ∨ process = server := by simpa [processes] using member
    rcases alternatives with equal | equal
    · subst process
      obtain ⟨stageDone, outcomeDone⟩ := client_program_halt publicPayload clientValid active halted notRuntime
      subst stage
      subst outcome
      rw [finish_return_no_lifecycle system client _ links monitors]
      have newClient : ClientControl payload .done
          { client with status := .finished (.returned [.tuple [.atom "ok", payload]]) } :=
        ⟨clientValid.1, clientValid.2.1, clientValid.2.2.1,
          clientValid.2.2.2.1, rfl, rfl⟩
      exact closedExchange_pair
        (network_replace_process network (network.1 client member)) fresh links monitors
        (update_pair_client processes clientValid.1 serverValid.1 clientValid.1)
        newClient serverValid (by decide) nextPid referenceCounter
    · subst process
      have outcomeDone := server_program_halt publicPayload serverValid active halted notRuntime
      subst outcome
      rw [finish_return_no_lifecycle system server _ links monitors]
      have newServer : ServerControl payload
          { server with status := .finished (.returned [.atom "ok"]) } :=
        ⟨serverValid.1, serverValid.2.1, serverValid.2.2.1, rfl⟩
      exact closedExchange_pair
        (network_replace_process network (network.1 server member)) fresh links monitors
        (update_pair_server processes clientValid.1 serverValid.1 serverValid.1)
        clientValid newServer spawning nextPid referenceCounter

/-- The remaining local branch of stepSystem contains no runtime operation. -/
theorem closedExchange_local_result (invariant : ClosedExchange payload system)
    (found : system.lookup pid = some process)
    (active : ProcessActive process) (publicPayload : payload.isPublic = true)
    (notRuntime : ∀ name args, process.state.control ≠ .runtime name args)
    (accepted : (if process.status == .waiting then Except.error ChoiceError.blockedProcess
      else match stepLocal [importedActorProtocolModule] process.state with
        | .next state => Except.ok (system.update { process with state := state })
        | .halt outcome => Except.ok (finishProcess system process outcome)) = .ok next) :
    ClosedExchange payload next := by
  split at accepted
  · contradiction
  · cases advanced : stepLocal [importedActorProtocolModule] process.state with
    | next state =>
      have equal : system.update { process with state := state } = next := by
        simpa [advanced] using accepted
      rw [← equal]
      exact closedExchange_next invariant found advanced
    | halt outcome =>
      have equal : finishProcess system process outcome = next := by
        simpa [advanced] using accepted
      rw [← equal]
      exact closedExchange_halt invariant found active publicPayload advanced notRuntime

/-- Preservation is proved for the executable system step, including arbitrary
    accepted scheduling, delivery, and logical-time choices. -/
theorem closedExchange_step {choice : Choice} (invariant : ClosedExchange payload system)
    (publicPayload : payload.isPublic = true)
    (accepted : stepSystem [importedActorProtocolModule] system choice = .ok next) :
    ClosedExchange payload next := by
  cases choice with
    | advanceTime to =>
      simp only [stepSystem] at accepted
      split at accepted
      · simp [throw, throwThe, Bind.bind, Except.bind, Pure.pure, Except.pure] at accepted
      · split at accepted
        · have equal : { system with now := to } = next := by
            simpa [Pure.pure, Except.pure] using accepted
          rw [← equal]
          exact closedExchange_time invariant to
        · simp [throw, throwThe] at accepted
    | deliver signalId =>
      simp only [stepSystem] at accepted
      split at accepted
      · simp [throw, throwThe, Bind.bind, Except.bind] at accepted
      · exact closedExchange_deliver invariant accepted
    | run pid =>
      simp only [stepSystem] at accepted
      split at accepted
      · simp [throw, throwThe, Bind.bind, Except.bind, Pure.pure, Except.pure] at accepted
      rename_i noFault
      simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at accepted
      cases found : system.lookup pid with
      | none => simp [found, throw, throwThe] at accepted
      | some process =>
        simp only [found] at accepted
        cases status : process.status with
        | finished outcome => simp [status, throw, throwThe] at accepted
        | running =>
          have waitingTest : (ProcessStatus.running == ProcessStatus.waiting) = false := rfl
          have active : ProcessActive process := by simp [ProcessActive, status]
          simp only [status] at accepted
          cases control : process.state.control with
          | runtime name arguments =>
            exact request_closedExchange invariant found active control publicPayload
              (by simpa only [control] using accepted)
          | eval expression | ret values | raise exception | select values clauses =>
            cases advanced : stepLocal [importedActorProtocolModule] process.state with
            | next state =>
              have equal : system.update { process with state := state } = next := by
                simpa [control, status, waitingTest, advanced, Bind.bind, Except.bind,
                  Pure.pure, Except.pure] using accepted
              rw [← equal]
              exact closedExchange_next invariant found advanced
            | halt outcome =>
              have equal : finishProcess system process outcome = next := by
                simpa [control, status, waitingTest, advanced, Bind.bind, Except.bind,
                  Pure.pure, Except.pure] using accepted
              rw [← equal]
              exact closedExchange_halt invariant found active publicPayload advanced
                (by intro name args; simp [control])
        | waiting =>
          have waitingTest : (ProcessStatus.waiting == ProcessStatus.waiting) = true := rfl
          have active : ProcessActive process := by simp [ProcessActive, status]
          simp only [status] at accepted
          cases control : process.state.control with
          | runtime name arguments =>
            exact request_closedExchange invariant found active control publicPayload
              (by simpa only [control] using accepted)
          | eval expression | ret values | raise exception | select values clauses =>
            simp [control, waitingTest, throw, throwThe, MonadExceptOf.throw] at accepted

/-- Replay induction has no invariant-preservation premise: each actual accepted
    transition is discharged by closedExchange_step. -/
theorem closedExchange_replay (invariant : ClosedExchange payload system)
    (publicPayload : payload.isPublic = true)
    (accepted : replay [importedActorProtocolModule] system choices = .ok finalSystem) :
    ClosedExchange payload finalSystem := by
  induction choices generalizing system with
  | nil =>
    have equal : system = finalSystem := by simpa [replay] using accepted
    simpa [← equal] using invariant
  | cons choice rest inductionHypothesis =>
    cases advanced : stepSystem [importedActorProtocolModule] system choice with
    | error error => simp [replay, advanced, Bind.bind, Except.bind] at accepted
    | ok middle =>
      exact inductionHypothesis
        (closedExchange_step invariant publicPayload advanced)
        (by simpa [replay, advanced, Bind.bind, Except.bind] using accepted)

/-- Every finite accepted schedule of the actual imported exchange preserves
    the closed protocol invariant. Fairness and eventual termination are not
    assumed or claimed by this safety theorem. -/
theorem exchange_allSchedules (payload : Value) (publicPayload : payload.isPublic = true)
    (choices : List Choice) (finalSystem : System)
    (accepted : replay [importedActorProtocolModule]
      (initialSystem "actor_protocol" "exchange" [payload]) choices = .ok finalSystem) :
    ClosedExchange payload finalSystem :=
  closedExchange_replay (initial_closedExchange payload publicPayload) publicPayload accepted

theorem closedExchange_root_return (invariant : ClosedExchange payload system)
    (found : system.lookup 0 = some root)
    (finished : root.status = .finished outcome) :
    outcome = .returned [.tuple [.atom "ok", payload]] := by
  obtain ⟨_, _, _, _, stage, client, clientValid, _, population⟩ := invariant
  have member : root ∈ system.processes := List.mem_of_find?_eq_some found
  have rootPid : root.pid = 0 := by
    have selected := List.find?_some found
    simpa [System.lookup] using selected
  have rootClient : root = client := by
    by_cases spawning : stage = .spawn
    · simp only [spawning, if_pos] at population
      simpa [population.1] using member
    · simp only [spawning, if_false] at population
      obtain ⟨server, processes, _, serverValid⟩ := population
      have alternatives : root = client ∨ root = server := by simpa [processes] using member
      rcases alternatives with same | same
      · exact same
      · have impossible : (0 : Nat) = 1 := by
          calc 0 = root.pid := rootPid.symm
               _ = server.pid := congrArg Process.pid same
               _ = 1 := serverValid.1
        contradiction
  subst root
  have validOutcome := clientValid.2.2.2.2
  simp only [finished] at validOutcome
  exact validOutcome.2

/-- A terminated root returns precisely the original public payload in its
    protocol reply, for every accepted schedule of the imported Core module. -/
theorem exchange_reply_correct (payload : Value) (publicPayload : payload.isPublic = true)
    (choices : List Choice) (finalSystem : System)
    (accepted : replay [importedActorProtocolModule]
      (initialSystem "actor_protocol" "exchange" [payload]) choices = .ok finalSystem)
    (found : finalSystem.lookup 0 = some root)
    (finished : root.status = .finished outcome) :
    outcome = .returned [.tuple [.atom "ok", payload]] :=
  closedExchange_root_return
    (exchange_allSchedules payload publicPayload choices finalSystem accepted) found finished

/-- Any in-flight message addressed to the client is the expected protocol reply
    carrying the original payload and its fresh reference. -/
theorem exchange_pendingRepliesAuthentic
    (payload : Value) (publicPayload : payload.isPublic = true)
    (choices : List Choice) (finalSystem : System)
    (accepted : replay [importedActorProtocolModule]
      (initialSystem "actor_protocol" "exchange" [payload]) choices = .ok finalSystem)
    (queued : signal ∈ finalSystem.pending) (recipient : signal.recipient = 0) :
    signal.kind = .message ∧ signal.message = replyPayload 0 payload := by
  have network := (exchange_allSchedules payload publicPayload choices finalSystem accepted).1
  have authentic := network.2 signal queued
  exact ⟨authentic.1, by simpa [AllowedMailbox, recipient] using authentic.2⟩

end Erlean.Examples.ProtocolInvariant
