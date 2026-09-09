import Erlean.Examples.ProtocolClientRuntime
import Erlean.Examples.ProtocolServerRuntime

namespace Erlean.Examples.ProtocolInvariant

open Core Semantics Erlean.Runtime Erlean.Examples.Protocol Erlean.Logic

/-- Every accepted runtime request in the closed exchange preserves the protocol
    predicate. The process identity split follows from the reachable population. -/
theorem request_closedExchange
    (invariant : ClosedExchange payload system)
    (found : system.lookup pid = some process)
    (active : ProcessActive process)
    (runtime : process.state.control = .runtime name arguments)
    (publicPayload : payload.isPublic = true)
    (accepted : request [importedActorProtocolModule] system process name arguments = .ok next) :
    ClosedExchange payload next := by
  have identities : process.pid = 0 ∨ process.pid = 1 := by
    obtain ⟨_, _, _, _, stage, client, valid, _, population⟩ := invariant
    have member : process ∈ system.processes := List.mem_of_find?_eq_some found
    by_cases spawning : stage = .spawn
    · simp only [spawning, if_pos] at population
      have same : process = client := by simpa [population.1] using member
      exact Or.inl (by simpa [same] using valid.1)
    · simp only [spawning, if_false] at population
      obtain ⟨server, population, _, serverValid⟩ := population
      have alternatives : process = client ∨ process = server := by simpa [population] using member
      rcases alternatives with same | same
      · exact Or.inl (by simpa [same] using valid.1)
      · exact Or.inr (by simpa [same] using serverValid.1)
  rcases identities with identity | identity
  · exact request_client_closedExchange invariant found identity active runtime publicPayload accepted
  · exact request_server_closedExchange invariant found identity active runtime publicPayload accepted

end Erlean.Examples.ProtocolInvariant
