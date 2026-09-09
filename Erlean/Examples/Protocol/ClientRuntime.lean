import Erlean.Examples.Protocol.RuntimeBase

set_option maxRecDepth 2048
set_option maxHeartbeats 800000

namespace Erlean.Examples.ProtocolInvariant

open Core Semantics Erlean.Runtime Erlean.Examples.Protocol Erlean.Logic

theorem request_client_closedExchange
    (invariant : ClosedExchange payload system)
    (found : system.lookup pid = some process)
    (clientPid : process.pid = 0) (active : ProcessActive process)
    (runtime : process.state.control = .runtime name arguments)
    (publicPayload : payload.isPublic = true)
    (accepted : request [importedActorProtocolModule] system process name arguments = .ok next) :
    ClosedExchange payload next := by
  obtain ⟨network, fresh, links, monitors, stage, client, clientValid,
    referenceCounter, population⟩ := invariant
  have member : process ∈ system.processes := List.mem_of_find?_eq_some found
  have equalClient : process = client := by
    by_cases spawning : stage = .spawn
    · simp only [spawning, if_pos] at population
      simpa [population.1] using member
    · simp only [spawning, if_false] at population
      obtain ⟨server, population, _, serverValid⟩ := population
      have alternatives : process = client ∨ process = server := by simpa [population] using member
      rcases alternatives with same | same
      · exact same
      · have serverPid := serverValid.1
        simp [← same, clientPid] at serverPid
  subst client
  have phase := client_active_phase clientValid active
  have cursor := clientValid.2.1
  have deadline := clientValid.2.2.1
  have selected := clientValid.2.2.2.1
  have oldMailbox := network.1 process member
  have afterSpawn : stage ≠ .spawn → ∃ server,
      system.processes = [process, server] ∧ system.nextPid = 2 ∧ ServerControl payload server := by
    intro notSpawn
    simpa only [notSpawn, if_false] using population
  have closeUpdate : ∀ (nextStage : ClientStage) (replacement : Process),
      stage ≠ .spawn → nextStage ≠ .spawn →
      system.nextReference = nextStage.referenceCounter →
      ClientControl payload nextStage replacement →
      (∀ message ∈ replacement.mailbox, AllowedMailbox 0 1 0 payload replacement.pid message) →
      ClosedExchange payload (system.update replacement) := by
    intro nextStage replacement notSpawn nextNotSpawn counter valid mailbox
    obtain ⟨server, population, nextPid, serverValid⟩ := afterSpawn notSpawn
    exact closedExchange_pair (network_replace_process network mailbox) fresh links monitors
      (update_pair_client population clientPid serverValid.1 valid.1)
      valid serverValid nextNotSpawn nextPid counter
  cases stage with
  | spawn =>
    obtain ⟨rfl, rfl⟩ := runtime_control_of_map phase runtime (clientSpawn_control payload publicPayload)
    simp only [if_pos] at population
    have nextPhase : BoundaryPhase (ClientStage.newReference.boundary payload)
        { process.state with control := .ret [.pid 1] } :=
      boundaryPhase_resume_to phase runtime rfl (clientNewReference_eq payload)
    have valid := clientControl_resume clientPid cursor deadline
      (stage := ClientStage.newReference) (requiredMessage_none process) nextPhase
    let replacement := returnValues process [.pid 1]
    let server : Process := { pid := 1, state := initialCall "actor_protocol" "server" [] }
    have serverValid : ServerControl payload server := by
      refine ⟨rfl, rfl, rfl, ServerStage.peek, requiredMessage_none server, ?_⟩
      obtain ⟨endpoint, found, segment⟩ := serverPeek_segment
      exact ⟨endpoint, found, (actualBoundary_sound found).2, segment⟩
    let updated : System := { (system.update replacement) with
      processes := (system.update replacement).processes ++ [server], nextPid := 2 }
    have linked : [importedActorProtocolModule].any (fun mod => mod.name == "actor_protocol") = true := rfl
    have equal : updated = next := by
      simpa [request, decodeList, linked, population.1, population.2, System.lookup,
        clientPid, Value.publicList, Value.isPublic, Pure.pure, Except.pure,
        updated, replacement, server] using accepted
    have updatedNetwork : NetworkRespect (AllowedMailbox 0 1 0 payload) updated := by
      refine ⟨?_, network.2⟩
      intro current present message queued
      rcases List.mem_append.mp present with existing | added
      · exact (network_replace_process (replacement := replacement) network oldMailbox).1 current existing message queued
      · have same : current = server := List.mem_singleton.mp added
        subst current
        simp [server] at queued
    rw [← equal]
    apply closedExchange_pair updatedNetwork fresh links monitors
      (clientValid := valid) (serverValid := serverValid) (afterSpawn := by decide)
    · simp [updated, System.update, population.1, clientPid, replacement, returnValues]
    · rfl
    · exact referenceCounter
  | newReference =>
    obtain ⟨rfl, rfl⟩ := runtime_control_of_map phase runtime (clientNewReference_control payload publicPayload)
    have counter : system.nextReference = 0 := referenceCounter
    have nextPhase : BoundaryPhase (ClientStage.self.boundary payload)
        { process.state with control := .ret [.reference 0] } :=
      boundaryPhase_resume_to phase runtime rfl (clientSelf_eq payload)
    have valid := clientControl_resume clientPid cursor deadline
      (stage := ClientStage.self) (requiredMessage_none process) nextPhase
    let replacement := returnValues process [.reference 0]
    let updated : System := { (system.update replacement) with nextReference := 1 }
    have equal : updated = next := by
      simpa [request, counter, Value.publicList, Pure.pure, Except.pure,
        updated, replacement] using accepted
    obtain ⟨server, population, nextPid, serverValid⟩ := afterSpawn (by decide)
    rw [← equal]
    exact closedExchange_pair (network_replace_process network oldMailbox) fresh links monitors
      (update_pair_client population clientPid serverValid.1 valid.1)
      valid serverValid (by decide) nextPid rfl
  | self =>
    obtain ⟨rfl, rfl⟩ := runtime_control_of_map phase runtime (clientSelf_control payload publicPayload)
    have nextPhase : BoundaryPhase (ClientStage.sendRequest.boundary payload)
        { process.state with control := .ret [.pid 0] } :=
      boundaryPhase_resume_to phase runtime rfl (clientSendRequest_eq payload publicPayload)
    have valid := clientControl_resume clientPid cursor deadline
      (stage := ClientStage.sendRequest) (requiredMessage_none process) nextPhase
    have equal : system.update (returnValues process [.pid 0]) = next := by
      simpa [request, clientPid, Value.publicList, Pure.pure, Except.pure] using accepted
    rw [← equal]
    exact closeUpdate .sendRequest _ (by decide) (by decide) referenceCounter valid oldMailbox
  | sendRequest =>
    obtain ⟨rfl, rfl⟩ := runtime_control_of_map phase runtime (clientSendRequest_control payload publicPayload)
    have nextPhase : BoundaryPhase (ClientStage.peek.boundary payload)
        { process.state with control := .ret [requestPayload 0 0 payload] } :=
      boundaryPhase_resume_to phase runtime rfl (clientPeek_eq payload publicPayload)
    have valid := clientControl_resume clientPid cursor deadline
      (stage := ClientStage.peek) (requiredMessage_none process) nextPhase
    let replacement := returnValues process [requestPayload 0 0 payload]
    let updated := (system.update replacement).enqueue process.pid 1 .message (requestPayload 0 0 payload)
    have updatedNetwork : NetworkRespect (AllowedMailbox 0 1 0 payload) updated :=
      network_enqueue_message (network_replace_process (replacement := replacement) network oldMailbox)
        (Or.inl ⟨rfl, Or.inl rfl⟩) process.pid
    have equal : updated = next := by
      simpa [request, signalFresh_guard fresh, Value.publicList, Value.isPublic,
        requestPayload, publicPayload, Pure.pure, Except.pure, updated,
        replacement, System.enqueue, System.update] using accepted
    obtain ⟨server, population, nextPid, serverValid⟩ := afterSpawn (by decide)
    rw [← equal]
    exact closedExchange_pair updatedNetwork (signalFresh_enqueue fresh _ _ _ _) links monitors
      (update_pair_client population clientPid serverValid.1 valid.1)
      valid serverValid (by decide) nextPid referenceCounter
  | peek =>
    obtain ⟨rfl, rfl⟩ := runtime_control_of_map phase runtime (clientPeek_control payload publicPayload)
    cases queued : process.mailbox[process.cursor]? with
    | none =>
      have nextPhase : BoundaryPhase (ClientStage.wait.boundary payload)
          { process.state with control := .ret [.atom "false", .atom "undefined"] } :=
        boundaryPhase_resume_to phase runtime rfl (clientWait_eq payload publicPayload)
      have valid := clientControl_resume clientPid cursor deadline
        (stage := ClientStage.wait) (requiredMessage_none process) nextPhase
      have equal : system.update (returnValues process [.atom "false", .atom "undefined"]) = next := by
        simpa [request, queued, Value.publicList, Pure.pure, Except.pure] using accepted
      rw [← equal]
      exact closeUpdate .wait _ (by decide) (by decide) referenceCounter valid oldMailbox
    | some message =>
      have messageMember : message ∈ process.mailbox := List.mem_of_getElem? queued
      have allowed := oldMailbox message messageMember
      have same : message = replyPayload 0 payload := by
        simpa [AllowedMailbox, clientPid] using allowed
      subst message
      have nextPhase : BoundaryPhase (ClientStage.remove.boundary payload)
          { process.state with control := .ret [.atom "true", replyPayload 0 payload] } :=
        boundaryPhase_resume_to phase runtime rfl (clientRemove_eq payload publicPayload)
      have required : RequiredMessage (ClientStage.remove.requiredMessage payload) process := by
        intro message identity
        have same : message = replyPayload 0 payload := by
          simpa [ClientStage.requiredMessage] using identity.symm
        simpa [same] using queued
      have valid := clientControl_resume clientPid cursor deadline required nextPhase
      have equal : system.update (returnValues process [.atom "true", replyPayload 0 payload]) = next := by
        simpa [request, queued, Value.publicList, Pure.pure, Except.pure] using accepted
      rw [← equal]
      exact closeUpdate .remove _ (by decide) (by decide) referenceCounter valid oldMailbox
  | wait =>
    obtain ⟨rfl, rfl⟩ := runtime_control_of_map phase runtime (clientWait_control payload publicPayload)
    by_cases ready : process.cursor < process.mailbox.length
    · have nextPhase : BoundaryPhase (ClientStage.peek.boundary payload)
          { process.state with control := .ret [.atom "false"] } :=
        boundaryPhase_resume_to phase runtime (clientWait_loop payload publicPayload)
          (clientPeek_eq payload publicPayload)
      have valid := clientControl_resume clientPid cursor deadline
        (stage := ClientStage.peek) (requiredMessage_none process) nextPhase
      have equal : system.update (returnValues process [.atom "false"]) = next := by
        simpa [request, decodeTimeout, returnValues, deadline, ready, Value.publicList, Value.isPublic,
          Pure.pure, Except.pure] using accepted
      rw [← equal]
      exact closeUpdate .peek _ (by decide) (by decide) referenceCounter valid oldMailbox
    · by_cases waiting : (process.status == .waiting) = true
      · simp [request, decodeTimeout, deadline, ready, waiting, Value.publicList, Value.isPublic,
          throw, throwThe] at accepted
      · have equal : system.update { process with status := .waiting } = next := by
          simpa [request, decodeTimeout, deadline, ready, waiting, Value.publicList, Value.isPublic,
            Pure.pure, Except.pure] using accepted
        rw [← equal]
        exact closeUpdate .wait _ (by decide) (by decide) referenceCounter
          (clientControl_waiting clientValid active) oldMailbox
  | remove =>
    obtain ⟨rfl, rfl⟩ := runtime_control_of_map phase runtime (clientRemove_control payload publicPayload)
    have queued := selected (replyPayload 0 payload) rfl
    have bound := (List.getElem?_eq_some_iff.mp queued).1
    have nonempty : 0 < process.mailbox.length := by omega
    let replacement : Process := { process with mailbox := process.mailbox.drop 1, cursor := 0, deadline := none }
    have nextPhase : BoundaryPhase (ClientStage.sendStop.boundary payload)
        { replacement.state with control := .ret [.atom "ok"] } :=
      boundaryPhase_resume_to phase runtime rfl (clientSendStop_eq payload publicPayload)
    have valid := clientControl_resume clientPid (process := replacement) rfl rfl
      (stage := ClientStage.sendStop) (requiredMessage_none replacement) nextPhase
    have mailbox : ∀ message ∈ replacement.mailbox, AllowedMailbox 0 1 0 payload replacement.pid message := by
      intro message queued
      exact oldMailbox message (List.mem_of_mem_drop queued)
    have equal : system.update (returnValues replacement [.atom "ok"]) = next := by
      simpa [request, cursor, nonempty, replacement, Value.publicList, Pure.pure, Except.pure] using accepted
    rw [← equal]
    exact closeUpdate .sendStop _ (by decide) (by decide) referenceCounter valid mailbox
  | sendStop =>
    obtain ⟨rfl, rfl⟩ := runtime_control_of_map phase runtime (clientSendStop_control payload publicPayload)
    have nextPhase : BoundaryPhase (ClientStage.done.boundary payload)
        { process.state with control := .ret [.atom "stop"] } :=
      boundaryPhase_resume_to phase runtime rfl (clientDone_eq payload publicPayload)
    have valid := clientControl_resume clientPid cursor deadline
      (stage := ClientStage.done) (requiredMessage_none process) nextPhase
    let replacement := returnValues process [.atom "stop"]
    let updated := (system.update replacement).enqueue process.pid 1 .message (.atom "stop")
    have updatedNetwork : NetworkRespect (AllowedMailbox 0 1 0 payload) updated :=
      network_enqueue_message (network_replace_process (replacement := replacement) network oldMailbox)
        (Or.inl ⟨rfl, Or.inr rfl⟩) process.pid
    have equal : updated = next := by
      simpa [request, signalFresh_guard fresh, Value.publicList, Value.isPublic,
        Pure.pure, Except.pure, updated, replacement, System.enqueue, System.update] using accepted
    obtain ⟨server, population, nextPid, serverValid⟩ := afterSpawn (by decide)
    rw [← equal]
    exact closedExchange_pair updatedNetwork (signalFresh_enqueue fresh _ _ _ _) links monitors
      (update_pair_client population clientPid serverValid.1 valid.1)
      valid serverValid (by decide) nextPid referenceCounter
  | done =>
    have chosen := boundaryPhase_runtime phase runtime
    have control := clientDone_control payload publicPayload
    simp [ClientStage.boundary] at chosen
    simp [chosen, runtime] at control

end Erlean.Examples.ProtocolInvariant
