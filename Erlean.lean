import Erlean.Core.Scope
import Erlean.Core.Match
import Erlean.Core.Checks
import Erlean.Core.Environment
import Erlean.Import.Lower
import Erlean.Semantics.Machine
import Erlean.Semantics.Preservation
import Erlean.Semantics.VariableSafety
import Erlean.Logic.Segment
import Erlean.Semantics.Observation
import Erlean.Logic.ObservableContract
import Erlean.Examples.Identity
import Erlean.Examples.LanguageIdentity
import Erlean.Examples.Reverse
import Erlean.Examples.HigherOrder
import Erlean.Examples.Modular
import Erlean.Examples.ByteCodec
import Erlean.Examples.Protocol
import Erlean.Runtime.Invariants
import Erlean.Runtime.SignalBounds
import Erlean.Examples.ProtocolPhases
import Erlean.Examples.ProtocolSafety
import Erlean.Examples.Dijkstra

/-!
# erlean

Executable Core Erlang semantics and verification for a restricted OTP 29 profile.
-/
