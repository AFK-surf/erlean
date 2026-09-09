import Erlean.Examples.Identity
import Erlean.Examples.LanguageIdentity
import Erlean.Examples.Reverse
import Erlean.Examples.HigherOrder
import Erlean.Examples.Modular
import Erlean.Examples.ByteCodec
import Erlean.Examples.Protocol
import Erlean.Semantics.Preservation
import Erlean.Semantics.VariableSafety
import Erlean.Logic.Segment
import Erlean.Runtime.Invariants
import Erlean.Runtime.SignalBounds
import Erlean.Examples.ProtocolPhases

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
