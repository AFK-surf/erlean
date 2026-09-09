import Erlean.Examples.ProtocolInvariant

namespace Erlean.Examples.ProtocolInvariant

open Core Semantics Erlean.Runtime Erlean.Examples.Protocol Erlean.Logic

def ProcessActive (process : Process) : Prop :=
  match process.status with
  | .finished _ => False
  | _ => True

theorem client_active_phase (valid : ClientControl payload stage process)
    (active : ProcessActive process) :
    BoundaryPhase (stage.boundary payload) process.state := by
  obtain ⟨_, _, _, _, phase⟩ := valid
  cases status : process.status <;> simp_all [ProcessActive]

theorem server_active_phase (valid : ServerControl payload process)
    (active : ProcessActive process) :
    ∃ stage : ServerStage, RequiredMessage (stage.requiredMessage payload) process ∧
      BoundaryPhase (stage.boundary payload) process.state := by
  obtain ⟨_, _, _, phase⟩ := valid
  cases status : process.status <;> simp_all [ProcessActive]

theorem boundaryPhase_resume (phase : BoundaryPhase boundary state)
    (runtime : state.control = .runtime name arguments)
    (resumed : resumeBoundary boundary response = some endpoint) :
    BoundaryPhase (some endpoint) { state with control := .ret response } := by
  have chosen := boundaryPhase_runtime phase runtime
  have found : actualBoundary { state with control := .ret response } = some endpoint := by
    simpa [resumeBoundary, chosen] using resumed
  obtain ⟨segment, terminal⟩ := actualBoundary_sound found
  exact ⟨endpoint, rfl, terminal, segment⟩

theorem boundaryPhase_resume_to (phase : BoundaryPhase boundary state)
    (runtime : state.control = .runtime name arguments)
    (resumed : resumeBoundary boundary response = nextBoundary)
    (found : nextBoundary = some endpoint) :
    BoundaryPhase nextBoundary { state with control := .ret response } := by
  rw [found]
  exact boundaryPhase_resume phase runtime (resumed.trans found)

theorem runtime_control_of_map (phase : BoundaryPhase boundary state)
    (runtime : state.control = .runtime name arguments)
    (control : boundary.map LocalState.control = some (.runtime expectedName expectedArgs)) :
    name = expectedName ∧ arguments = expectedArgs := by
  have chosen := boundaryPhase_runtime phase runtime
  simpa [chosen, runtime] using control

theorem requiredMessage_none (process : Process) : RequiredMessage none process := by
  intro message impossible
  cases impossible

theorem clientControl_resume {process : Process} {stage : ClientStage}
    (pid : process.pid = 0) (cursor : process.cursor = 0)
    (deadline : process.deadline = none)
    (required : RequiredMessage (stage.requiredMessage payload) process)
    (phase : BoundaryPhase (stage.boundary payload)
      { process.state with control := .ret response }) :
    ClientControl payload stage (returnValues process response) :=
  ⟨pid, cursor, deadline, required, phase⟩

theorem serverControl_resume {process : Process} {stage : ServerStage}
    (pid : process.pid = 1) (cursor : process.cursor = 0)
    (deadline : process.deadline = none)
    (required : RequiredMessage (stage.requiredMessage payload) process)
    (phase : BoundaryPhase (stage.boundary payload)
      { process.state with control := .ret response }) :
    ServerControl payload (returnValues process response) :=
  ⟨pid, cursor, deadline, stage, required, phase⟩

theorem clientControl_waiting (valid : ClientControl payload stage process)
    (active : ProcessActive process) :
    ClientControl payload stage { process with status := .waiting } :=
  ⟨valid.1, valid.2.1, valid.2.2.1, valid.2.2.2.1,
    client_active_phase (process := process) valid active⟩

theorem serverControl_waiting (valid : ServerControl payload process)
    (active : ProcessActive process) :
    ServerControl payload { process with status := .waiting } :=
  ⟨valid.1, valid.2.1, valid.2.2.1, server_active_phase (process := process) valid active⟩

end Erlean.Examples.ProtocolInvariant
