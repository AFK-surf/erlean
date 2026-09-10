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
import Erlean.Core.Maps
import Erlean.Core.MapPatterns
import Erlean.Semantics.Maps
import Erlean.Semantics.Lists

import Erlean.Logic.Segment
import Erlean.Logic.Frames
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
#print axioms Erlean.Semantics.extendedBuiltin_preserves
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
#print axioms Erlean.Core.MapKey.code_injective
#print axioms Erlean.Core.MapKey.before_trans
#print axioms Erlean.Core.MapKey.before_trichotomy
#print axioms Erlean.Core.FiniteMap.lookup_insert
#print axioms Erlean.Core.FiniteMap.lookup_erase
#print axioms Erlean.Core.FiniteMap.sorted_insert
#print axioms Erlean.Core.FiniteMap.sorted_erase
#print axioms Erlean.Core.FiniteMap.ext_sorted
#print axioms Erlean.Core.MapKey.toValue_toMapKey
#print axioms Erlean.Core.Value.map_equal_iff_lookup
#print axioms Erlean.Core.Value.map_insert_public
#print axioms Erlean.Core.Value.map_erase_public
#print axioms Erlean.Core.Value.map_lookup_default_public
#print axioms Erlean.Core.Value.map_lookup_default_comparable
#print axioms Erlean.Semantics.mapBuiltin_put
#print axioms Erlean.Semantics.mapBuiltin_get
#print axioms Erlean.Semantics.withMapKey_of_toMapKey
#print axioms Erlean.Semantics.mapBuiltin_get_default_of_toMapKey
#print axioms Erlean.Semantics.mapBuiltin_put_of_toMapKey
#print axioms Erlean.Semantics.mapBuiltin_remove_of_toMapKey
#print axioms Erlean.Semantics.mapBuiltin_find_of_toMapKey
#print axioms Erlean.Semantics.mapBuiltin_find
#print axioms Erlean.Semantics.mapBuiltin_merge
#print axioms Erlean.Semantics.run_next
#print axioms Erlean.Semantics.run_halt
#print axioms Erlean.Logic.stepLocal_next_appendStack
#print axioms Erlean.Logic.reachesBoundary_appendStack
#print axioms Erlean.Core.matchPattern_map_singleton
#print axioms Erlean.Core.patternObservationAllowed_map_singleton
#print axioms Erlean.Core.literalObservationAllowed_atom_public
#print axioms Erlean.Core.literalObservationAllowed_bitstring_public
#print axioms Erlean.Core.patternObservationAllowed_map_atom
#print axioms Erlean.Core.patternObservationAllowed_map_bitstring
#print axioms Erlean.Semantics.mapBuiltin_remove
#print axioms Erlean.Core.Value.public_of_exactComparable
#print axioms Erlean.Core.FloatBits.parseHex_finite
#print axioms Erlean.Core.FloatBits.encodeHex_length
#print axioms Erlean.Logic.Controller.Trace.safe
#print axioms Erlean.Logic.Controller.Trace.exact
#print axioms Erlean.Logic.Controller.trace_of_refinement
#print axioms Erlean.Semantics.appendValues_list
#print axioms Erlean.Semantics.builtin_append_list
#print axioms Erlean.Semantics.builtin_append_improper
