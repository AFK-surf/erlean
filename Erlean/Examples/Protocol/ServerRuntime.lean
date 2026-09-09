import Erlean.Examples.Protocol.RuntimeBase

namespace Erlean.Examples.ProtocolInvariant

open Core Semantics Erlean.Runtime Erlean.Examples.Protocol Erlean.Logic

theorem request_server_closedExchange
    (invariant : ClosedExchange payload system)
    (found : system.lookup pid = some process)
    (serverPid : process.pid = 1) (active : ProcessActive process)
    (runtime : process.state.control = .runtime name arguments)
    (publicPayload : payload.isPublic = true)
    (accepted : request [importedActorProtocolModule] system process name arguments = .ok next) :
    ClosedExchange payload next := by
  obtain ⟨network, fresh, links, monitors, clientStage, client, clientValid,
    referenceCounter, population⟩ := invariant
  have member : process ∈ system.processes := List.mem_of_find?_eq_some found
  have notSpawn : clientStage ≠ .spawn := by
    intro spawning
    simp only [spawning, if_pos] at population
    have equal : process = client := by simpa [population.1] using member
    have := clientValid.1
    simp [← equal, serverPid] at this
  simp only [notSpawn, if_false] at population
  obtain ⟨server, population, nextPid, serverValid⟩ := population
  have equal : process = server := by
    have alternatives : process = client ∨ process = server := by simpa [population] using member
    rcases alternatives with same | same
    · have := clientValid.1
      simp [← same, serverPid] at this
    · exact same
  subst server
  obtain ⟨stage, selected, phase⟩ := server_active_phase serverValid active
  have closeUpdate : ∀ replacement,
      ServerControl payload replacement →
      (∀ message ∈ replacement.mailbox, AllowedMailbox 0 1 0 payload replacement.pid message) →
      ClosedExchange payload (system.update replacement) := by
    intro replacement valid mailbox
    exact closedExchange_pair (network_replace_process network mailbox) fresh links monitors
      (update_pair_server population clientValid.1 serverPid valid.1)
      clientValid valid notSpawn nextPid referenceCounter
  have oldMailbox := network.1 process member
  have cursor := serverValid.2.1
  have deadline := serverValid.2.2.1
  cases stage with
  | peek =>
    obtain ⟨rfl, rfl⟩ := runtime_control_of_map phase runtime serverPeek_control
    cases queued : process.mailbox[process.cursor]? with
    | none =>
      have nextPhase : BoundaryPhase (ServerStage.wait.boundary payload)
          { process.state with control := .ret [.atom "false", .atom "undefined"] } :=
        boundaryPhase_resume_to phase runtime rfl serverWait_eq
      have valid := serverControl_resume serverPid cursor deadline
        (stage := ServerStage.wait) (requiredMessage_none process) nextPhase
      have equal : system.update (returnValues process [.atom "false", .atom "undefined"]) = next := by
        simpa [request, queued, Value.publicList, Pure.pure, Except.pure] using accepted
      rw [← equal]
      exact closeUpdate _ valid oldMailbox
    | some message =>
      have messageMember : message ∈ process.mailbox := List.mem_of_getElem? queued
      have allowed := oldMailbox message messageMember
      have alternatives : message = requestPayload 0 0 payload ∨ message = .atom "stop" := by
        simpa [AllowedMailbox, serverPid] using allowed
      rcases alternatives with equal | equal
      · subst message
        have nextPhase : BoundaryPhase (ServerStage.removeRequest.boundary payload)
            { process.state with control := .ret [.atom "true", requestPayload 0 0 payload] } :=
          boundaryPhase_resume_to phase runtime rfl (serverRemoveRequest_eq payload publicPayload)
        have required : RequiredMessage (ServerStage.removeRequest.requiredMessage payload) process := by
          intro message identity
          have equal : message = requestPayload 0 0 payload := by simpa [ServerStage.requiredMessage] using identity.symm
          simpa [equal] using queued
        have valid := serverControl_resume serverPid cursor deadline required nextPhase
        have equal : system.update (returnValues process [.atom "true", requestPayload 0 0 payload]) = next := by
          simpa [request, queued, Value.publicList, Pure.pure, Except.pure] using accepted
        rw [← equal]
        exact closeUpdate _ valid oldMailbox
      · subst message
        have nextPhase : BoundaryPhase (ServerStage.removeStop.boundary payload)
            { process.state with control := .ret [.atom "true", .atom "stop"] } :=
          boundaryPhase_resume_to phase runtime rfl serverRemoveStop_eq
        have required : RequiredMessage (ServerStage.removeStop.requiredMessage payload) process := by
          intro message identity
          have equal : message = .atom "stop" := by simpa [ServerStage.requiredMessage] using identity.symm
          simpa [equal] using queued
        have valid := serverControl_resume serverPid cursor deadline required nextPhase
        have equal : system.update (returnValues process [.atom "true", .atom "stop"]) = next := by
          simpa [request, queued, Value.publicList, Pure.pure, Except.pure] using accepted
        rw [← equal]
        exact closeUpdate _ valid oldMailbox
  | wait =>
    obtain ⟨rfl, rfl⟩ := runtime_control_of_map phase runtime serverWait_control
    by_cases ready : process.cursor < process.mailbox.length
    · have nextPhase : BoundaryPhase (ServerStage.peek.boundary payload)
          { process.state with control := .ret [.atom "false"] } :=
        boundaryPhase_resume_to phase runtime serverWait_loop serverPeek_eq
      have valid := serverControl_resume serverPid cursor deadline
        (stage := ServerStage.peek) (requiredMessage_none process) nextPhase
      have equal : system.update (returnValues process [.atom "false"]) = next := by
        simpa [request, decodeTimeout, returnValues, deadline, ready, Value.publicList, Value.isPublic,
          Pure.pure, Except.pure] using accepted
      rw [← equal]
      exact closeUpdate _ valid oldMailbox
    · by_cases waiting : (process.status == .waiting) = true
      · simp [request, decodeTimeout, deadline, ready, waiting, Value.publicList, Value.isPublic,
          throw] at accepted
      · have equal : system.update { process with status := .waiting } = next := by
          simpa [request, decodeTimeout, deadline, ready, waiting, Value.publicList, Value.isPublic,
            Pure.pure, Except.pure] using accepted
        rw [← equal]
        exact closeUpdate _ (serverControl_waiting serverValid active) oldMailbox
  | removeRequest =>
    obtain ⟨rfl, rfl⟩ := runtime_control_of_map phase runtime
      (serverRemoveRequest_control payload publicPayload)
    have queued := selected (requestPayload 0 0 payload) rfl
    have bound := (List.getElem?_eq_some_iff.mp queued).1
    have nonempty : 0 < process.mailbox.length := by omega
    let replacement : Process := { process with mailbox := process.mailbox.drop 1, cursor := 0, deadline := none }
    have nextPhase : BoundaryPhase (ServerStage.sendReply.boundary payload)
        { replacement.state with control := .ret [.atom "ok"] } :=
      boundaryPhase_resume_to phase runtime rfl (serverSendReply_eq payload publicPayload)
    have valid := serverControl_resume serverPid (process := replacement) rfl rfl
      (stage := ServerStage.sendReply) (requiredMessage_none replacement) nextPhase
    have mailbox : ∀ message ∈ replacement.mailbox, AllowedMailbox 0 1 0 payload replacement.pid message := by
      intro message queued
      exact oldMailbox message (List.mem_of_mem_drop queued)
    have equal : system.update (returnValues replacement [.atom "ok"]) = next := by
      simpa [request, cursor, nonempty, replacement, Value.publicList, Pure.pure, Except.pure] using accepted
    rw [← equal]
    exact closeUpdate _ valid mailbox
  | sendReply =>
    obtain ⟨rfl, rfl⟩ := runtime_control_of_map phase runtime
      (serverSendReply_control payload publicPayload)
    have nextPhase : BoundaryPhase (ServerStage.peek.boundary payload)
        { process.state with control := .ret [replyPayload 0 payload] } :=
      boundaryPhase_resume_to phase runtime (serverSendReply_loop payload publicPayload) serverPeek_eq
    have valid := serverControl_resume serverPid cursor deadline
      (stage := ServerStage.peek) (requiredMessage_none process) nextPhase
    let replacement := returnValues process [replyPayload 0 payload]
    let updated := (system.update replacement).enqueue process.pid 0 .message (replyPayload 0 payload)
    have validNetwork : NetworkRespect (AllowedMailbox 0 1 0 payload) updated :=
      network_enqueue_message (network_replace_process (replacement := replacement) network oldMailbox)
        (Or.inr ⟨rfl, rfl⟩) process.pid
    have equal : updated = next := by
      simpa [request, signalFresh_guard fresh, Value.publicList, Value.isPublic,
        replyPayload, publicPayload, Pure.pure, Except.pure, updated,
        replacement, System.enqueue, System.update] using accepted
    rw [← equal]
    exact closedExchange_pair validNetwork (signalFresh_enqueue fresh _ _ _ _) links monitors
      (update_pair_server population clientValid.1 serverPid valid.1)
      clientValid valid notSpawn nextPid referenceCounter
  | removeStop =>
    obtain ⟨rfl, rfl⟩ := runtime_control_of_map phase runtime serverRemoveStop_control
    have queued := selected (.atom "stop") rfl
    have bound := (List.getElem?_eq_some_iff.mp queued).1
    have nonempty : 0 < process.mailbox.length := by omega
    let replacement : Process := { process with mailbox := process.mailbox.drop 1, cursor := 0, deadline := none }
    have nextPhase : BoundaryPhase (ServerStage.done.boundary payload)
        { replacement.state with control := .ret [.atom "ok"] } :=
      boundaryPhase_resume_to phase runtime rfl serverDone_eq
    have valid := serverControl_resume serverPid (process := replacement) rfl rfl
      (stage := ServerStage.done) (requiredMessage_none replacement) nextPhase
    have mailbox : ∀ message ∈ replacement.mailbox, AllowedMailbox 0 1 0 payload replacement.pid message := by
      intro message queued
      exact oldMailbox message (List.mem_of_mem_drop queued)
    have equal : system.update (returnValues replacement [.atom "ok"]) = next := by
      simpa [request, cursor, nonempty, replacement, Value.publicList, Pure.pure, Except.pure] using accepted
    rw [← equal]
    exact closeUpdate _ valid mailbox
  | done =>
    have chosen := boundaryPhase_runtime phase runtime
    have control := serverDone_control
    simp [ServerStage.boundary] at chosen
    simp [chosen, runtime] at control

end Erlean.Examples.ProtocolInvariant
