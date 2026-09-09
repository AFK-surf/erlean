import Erlean.Core.Equality
import Erlean.Logic.Controller
import Erlean.Examples.Identity.Contract
import Erlean.Examples.Identity.Languages
import Erlean.Examples.Sequential.Reverse
import Erlean.Examples.HigherOrder.Contract
import Erlean.Examples.Modular.Contract
import Erlean.Examples.ByteCodec.Contract
import Erlean.Examples.Protocol.Basic
import Erlean.Semantics.Preservation
import Erlean.Semantics.VariableSafety
import Erlean.Logic.Segment
import Erlean.Runtime.Invariants
import Erlean.Runtime.SignalBounds
import Erlean.Examples.Protocol.Phases
import Erlean.Examples.Protocol.Safety
import Erlean.Examples.Dijkstra.Correctness

#print axioms Erlean.Examples.identity_totalCorrect
#print axioms Erlean.Examples.gleam_identity_totalCorrect
#print axioms Erlean.Examples.elixir_identity_totalCorrect
#print axioms Erlean.Examples.reverse_totalCorrect
#print axioms Erlean.Examples.map_identity_totalCorrect
#print axioms Erlean.Examples.modular_relay_totalCorrect
#print axioms Erlean.Examples.byte_roundtrip_totalCorrect
#print axioms Erlean.Core.decodeByte_encodeByte_mod
#print axioms Erlean.Examples.byte_roundtrip_observableTotalCorrect
#print axioms Erlean.Examples.Protocol.replay_acceptedTrace
#print axioms Erlean.Examples.Protocol.accepted_delivery_fifo
#print axioms Erlean.Examples.Protocol.server_send_prefix
#print axioms Erlean.Examples.Protocol.client_result_prefix
#print axioms Erlean.Semantics.stepLocal_preserves_lexical_scope
#print axioms Erlean.Semantics.runLocal_preserves_lexical_scope
#print axioms Erlean.Logic.seekBoundary_sound
#print axioms Erlean.Semantics.initialCall_reachable_variable_not_unbound
#print axioms Erlean.Runtime.initial_replay_cursorBounds
#print axioms Erlean.Runtime.pending_nextSignal_fresh
#print axioms Erlean.Runtime.initial_replay_signalBounds
#print axioms Erlean.Examples.ProtocolInvariant.clientBoundary_program_halt
#print axioms Erlean.Examples.ProtocolInvariant.serverBoundary_program_halt
#print axioms Erlean.Examples.ProtocolInvariant.clientWait_loop
#print axioms Erlean.Examples.ProtocolInvariant.serverSendReply_loop
#print axioms Erlean.Examples.ProtocolInvariant.exchange_allSchedules
#print axioms Erlean.Examples.ProtocolInvariant.exchange_reply_correct
#print axioms Erlean.Examples.ProtocolInvariant.exchange_pendingRepliesAuthentic
#print axioms Erlean.Examples.DijkstraCertificate.checkCertificate_sound
#print axioms Erlean.Examples.DijkstraAlgorithm.distances_total
#print axioms Erlean.Examples.Dijkstra.search_returns
#print axioms Erlean.Examples.Dijkstra.dijkstra_terminates_correct
#print axioms Erlean.Examples.Dijkstra.dijkstra_total_correct
#print axioms Erlean.Core.Value.equal_eq_true
#print axioms Erlean.Core.Value.public_of_exactComparable
#print axioms Erlean.Logic.Controller.Trace.safe
#print axioms Erlean.Logic.Controller.trace_of_refinement
