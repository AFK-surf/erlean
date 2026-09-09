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
import Erlean.Examples.Identity.Contract
import Erlean.Examples.Identity.Languages
import Erlean.Examples.Sequential.Reverse
import Erlean.Examples.HigherOrder.Contract
import Erlean.Examples.Modular.Contract
import Erlean.Examples.ByteCodec.Contract
import Erlean.Examples.Protocol.Basic
import Erlean.Runtime.Invariants
import Erlean.Runtime.SignalBounds
import Erlean.Examples.Protocol.Phases
import Erlean.Examples.Protocol.Safety
import Erlean.Examples.Dijkstra.Correctness

/-!
# erlean

Executable Core Erlang semantics and verification for a restricted OTP 29 profile.
-/
