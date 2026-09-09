import Erlean.Examples.Protocol.Basic
import Erlean.Logic.Segment

/-!
Exact pure-segment endpoints for the imported actor protocol. Failed boundary
searches remain explicit; these definitions contain no fallback local state.
-/

namespace Erlean.Examples.ProtocolInvariant

open Core Semantics Erlean.Runtime Erlean.Examples.Protocol Erlean.Logic

/-- Runtime suspension or an empty-stack program outcome is a pure boundary. -/
def isActorBoundary (state : LocalState) : Bool :=
  match state.control with
  | .runtime _ _ => true
  | .ret _ | .raise _ => state.stack.isEmpty
  | _ => false

/-- Failure to reach a boundary has no fallback state. The search is over the
    actual imported code and the actual local transition function. -/
def actualBoundary (start : LocalState) : Option LocalState :=
  match seekBoundary (stepLocal [importedActorProtocolModule]) isActorBoundary 128 start with
  | .found endpoint => some endpoint
  | _ => none

def resumeBoundary (boundary : Option LocalState) (response : Values) : Option LocalState := do
  let state ← boundary
  actualBoundary { state with control := .ret response }

theorem actualBoundary_sound (found : actualBoundary start = some endpoint) :
    ReachesBoundary (stepLocal [importedActorProtocolModule]) start endpoint ∧
      isActorBoundary endpoint = true := by
  unfold actualBoundary at found
  cases search : seekBoundary (stepLocal [importedActorProtocolModule]) isActorBoundary 128 start with
  | found state =>
    simp [search] at found
    subst state
    exact seekBoundary_sound search
  | halted outcome => simp [search] at found
  | exhausted state => simp [search] at found

theorem isActorBoundary_halts (boundary : isActorBoundary state = true) :
    ∃ outcome, stepLocal world state = .halt outcome := by
  cases control : state.control with
  | eval expression => simp [isActorBoundary, control] at boundary
  | select values clauses => simp [isActorBoundary, control] at boundary
  | runtime name args =>
      exact ⟨.fault (.unsupported s!"Actor runtime required: {name}/{args.length}"),
        by simp [stepLocal, control, unsupported]⟩
  | ret values =>
      cases stack : state.stack with
      | nil => exact ⟨.returned values, by simp [stepLocal, control, stack]⟩
      | cons frame rest => simp [isActorBoundary, control, stack] at boundary
  | raise exception =>
      cases stack : state.stack with
      | nil => exact ⟨.raised exception, by simp [stepLocal, control, stack]⟩
      | cons frame rest => simp [isActorBoundary, control, stack] at boundary

def BoundaryPhase (boundary : Option LocalState) (state : LocalState) : Prop :=
  ∃ endpoint, boundary = some endpoint ∧ isActorBoundary endpoint = true ∧
    ReachesBoundary (stepLocal [importedActorProtocolModule]) state endpoint

theorem boundaryPhase_actual (found : actualBoundary start = some endpoint) :
    BoundaryPhase (actualBoundary start) start :=
  ⟨endpoint, found, (actualBoundary_sound found).2, (actualBoundary_sound found).1⟩

theorem boundaryPhase_next (phase : BoundaryPhase boundary state)
    (advanced : stepLocal [importedActorProtocolModule] state = .next next) :
    BoundaryPhase boundary next := by
  obtain ⟨endpoint, chosen, terminal, segment⟩ := phase
  obtain ⟨outcome, halted⟩ := isActorBoundary_halts (world := [importedActorProtocolModule]) terminal
  exact ⟨endpoint, chosen, terminal, reachesBoundary_next segment advanced halted⟩

theorem boundaryPhase_runtime (phase : BoundaryPhase boundary state)
    (runtime : state.control = .runtime name arguments) : boundary = some state := by
  obtain ⟨endpoint, chosen, _, segment⟩ := phase
  have halted : stepLocal [importedActorProtocolModule] state =
      .halt (.fault (.unsupported s!"Actor runtime required: {name}/{arguments.length}")) := by
    simp [stepLocal, runtime, unsupported]
  have equal := reachesBoundary_halt segment halted
  simpa [equal] using chosen

def clientSpawn (payload : Value) : Option LocalState :=
  actualBoundary (initialCall "actor_protocol" "exchange" [payload])

def clientNewReference (payload : Value) : Option LocalState :=
  resumeBoundary (clientSpawn payload) [.pid 1]

def clientSelf (payload : Value) : Option LocalState :=
  resumeBoundary (clientNewReference payload) [.reference 0]

def clientSendRequest (payload : Value) : Option LocalState :=
  resumeBoundary (clientSelf payload) [.pid 0]

def clientPeek (payload : Value) : Option LocalState :=
  resumeBoundary (clientSendRequest payload) [requestPayload 0 0 payload]

def clientWait (payload : Value) : Option LocalState :=
  resumeBoundary (clientPeek payload) [.atom "false", .atom "undefined"]

def clientRemove (payload : Value) : Option LocalState :=
  resumeBoundary (clientPeek payload) [.atom "true", replyPayload 0 payload]

def clientSendStop (payload : Value) : Option LocalState :=
  resumeBoundary (clientRemove payload) [.atom "ok"]

def clientDone (payload : Value) : Option LocalState :=
  resumeBoundary (clientSendStop payload) [.atom "stop"]

def serverPeek : Option LocalState :=
  actualBoundary (initialCall "actor_protocol" "server" [])

def serverWait : Option LocalState :=
  resumeBoundary serverPeek [.atom "false", .atom "undefined"]

def serverRemoveRequest (payload : Value) : Option LocalState :=
  resumeBoundary serverPeek [.atom "true", requestPayload 0 0 payload]

def serverSendReply (payload : Value) : Option LocalState :=
  resumeBoundary (serverRemoveRequest payload) [.atom "ok"]

def serverRemoveStop : Option LocalState :=
  resumeBoundary serverPeek [.atom "true", .atom "stop"]

def serverDone : Option LocalState :=
  resumeBoundary serverRemoveStop [.atom "ok"]

inductive ClientStage where
  | spawn | newReference | self | sendRequest | peek | wait | remove | sendStop | done
  deriving DecidableEq

def ClientStage.boundary (payload : Value) : ClientStage → Option LocalState
  | .spawn => clientSpawn payload
  | .newReference => clientNewReference payload
  | .self => clientSelf payload
  | .sendRequest => clientSendRequest payload
  | .peek => clientPeek payload
  | .wait => clientWait payload
  | .remove => clientRemove payload
  | .sendStop => clientSendStop payload
  | .done => clientDone payload

def ClientStage.referenceCounter : ClientStage → Nat
  | .spawn | .newReference => 0
  | _ => 1

inductive ServerStage where
  | peek | wait | removeRequest | sendReply | removeStop | done
  deriving DecidableEq

def ServerStage.boundary (payload : Value) : ServerStage → Option LocalState
  | .peek => serverPeek
  | .wait => serverWait
  | .removeRequest => serverRemoveRequest payload
  | .sendReply => serverSendReply payload
  | .removeStop => serverRemoveStop
  | .done => serverDone

/-- Memoized normal-form views of successful concrete boundary searches.
    Equations below connect these views to the actual imported machine. -/
def clientSpawnState (payload : Value) : LocalState :=
{ control := Erlean.Semantics.Control.runtime
               "spawn"
               [Erlean.Core.Value.atom "actor_protocol", Erlean.Core.Value.atom "server", Erlean.Core.Value.nil],
  context := { moduleName := "actor_protocol", env := [] },
  stack := [Erlean.Semantics.Frame.bind
              { moduleName := "actor_protocol",
                env := [(1, payload),
                        (0, payload)] }
              [2]
              (Erlean.Core.Expr.letE
                [3]
                (Erlean.Core.Expr.apply
                  (Erlean.Core.Expr.funRef "request" 3)
                  [Erlean.Core.Expr.var 2,
                   Erlean.Core.Expr.var 1,
                   Erlean.Core.Expr.lit (Erlean.Core.Value.atom "infinity")])
                (Erlean.Core.Expr.seq
                  (Erlean.Core.Expr.call
                    (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "erlang"))
                    (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "!"))
                    [Erlean.Core.Expr.var 2, Erlean.Core.Expr.lit (Erlean.Core.Value.atom "stop")])
                  (Erlean.Core.Expr.var 3)))] }

def clientNewReferenceState (payload : Value) : LocalState :=
{ control := Erlean.Semantics.Control.runtime "make_ref" [],
  context := { moduleName := "actor_protocol",
               env := [(3, Erlean.Core.Value.pid 1),
                       (4, payload),
                       (5, Erlean.Core.Value.atom "infinity"),
                       (0, Erlean.Core.Value.pid 1),
                       (1, payload),
                       (2, Erlean.Core.Value.atom "infinity")] },
  stack := [Erlean.Semantics.Frame.bind
              { moduleName := "actor_protocol",
                env := [(3, Erlean.Core.Value.pid 1),
                        (4, payload),
                        (5, Erlean.Core.Value.atom "infinity"),
                        (0, Erlean.Core.Value.pid 1),
                        (1, payload),
                        (2, Erlean.Core.Value.atom "infinity")] }
              [6]
              (Erlean.Core.Expr.letE
                [7]
                (Erlean.Core.Expr.call
                  (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "erlang"))
                  (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "self"))
                  [])
                (Erlean.Core.Expr.seq
                  (Erlean.Core.Expr.call
                    (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "erlang"))
                    (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "!"))
                    [Erlean.Core.Expr.var 3,
                     Erlean.Core.Expr.tuple
                       [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "request"),
                        Erlean.Core.Expr.var 7,
                        Erlean.Core.Expr.var 6,
                        Erlean.Core.Expr.var 4]])
                  (Erlean.Core.Expr.letrec [(8, 1)] (Erlean.Core.Expr.apply (Erlean.Core.Expr.var 8) [])))),
            Erlean.Semantics.Frame.bind
              { moduleName := "actor_protocol",
                env := [(2, Erlean.Core.Value.pid 1),
                        (1, payload),
                        (0, payload)] }
              [3]
              (Erlean.Core.Expr.seq
                (Erlean.Core.Expr.call
                  (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "erlang"))
                  (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "!"))
                  [Erlean.Core.Expr.var 2, Erlean.Core.Expr.lit (Erlean.Core.Value.atom "stop")])
                (Erlean.Core.Expr.var 3))] }

def clientSelfState (payload : Value) : LocalState :=
{ control := Erlean.Semantics.Control.runtime "self" [],
  context := { moduleName := "actor_protocol",
               env := [(6, Erlean.Core.Value.reference 0),
                       (3, Erlean.Core.Value.pid 1),
                       (4, payload),
                       (5, Erlean.Core.Value.atom "infinity"),
                       (0, Erlean.Core.Value.pid 1),
                       (1, payload),
                       (2, Erlean.Core.Value.atom "infinity")] },
  stack := [Erlean.Semantics.Frame.bind
              { moduleName := "actor_protocol",
                env := [(6, Erlean.Core.Value.reference 0),
                        (3, Erlean.Core.Value.pid 1),
                        (4, payload),
                        (5, Erlean.Core.Value.atom "infinity"),
                        (0, Erlean.Core.Value.pid 1),
                        (1, payload),
                        (2, Erlean.Core.Value.atom "infinity")] }
              [7]
              (Erlean.Core.Expr.seq
                (Erlean.Core.Expr.call
                  (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "erlang"))
                  (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "!"))
                  [Erlean.Core.Expr.var 3,
                   Erlean.Core.Expr.tuple
                     [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "request"),
                      Erlean.Core.Expr.var 7,
                      Erlean.Core.Expr.var 6,
                      Erlean.Core.Expr.var 4]])
                (Erlean.Core.Expr.letrec [(8, 1)] (Erlean.Core.Expr.apply (Erlean.Core.Expr.var 8) []))),
            Erlean.Semantics.Frame.bind
              { moduleName := "actor_protocol",
                env := [(2, Erlean.Core.Value.pid 1),
                        (1, payload),
                        (0, payload)] }
              [3]
              (Erlean.Core.Expr.seq
                (Erlean.Core.Expr.call
                  (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "erlang"))
                  (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "!"))
                  [Erlean.Core.Expr.var 2, Erlean.Core.Expr.lit (Erlean.Core.Value.atom "stop")])
                (Erlean.Core.Expr.var 3))] }

def clientSendRequestState (payload : Value) : LocalState :=
{ control := Erlean.Semantics.Control.runtime
               "send"
               [Erlean.Core.Value.pid 1,
                Erlean.Core.Value.tuple
                  [Erlean.Core.Value.atom "request",
                   Erlean.Core.Value.pid 0,
                   Erlean.Core.Value.reference 0,
                   payload]],
  context := { moduleName := "actor_protocol",
               env := [(7, Erlean.Core.Value.pid 0),
                       (6, Erlean.Core.Value.reference 0),
                       (3, Erlean.Core.Value.pid 1),
                       (4, payload),
                       (5, Erlean.Core.Value.atom "infinity"),
                       (0, Erlean.Core.Value.pid 1),
                       (1, payload),
                       (2, Erlean.Core.Value.atom "infinity")] },
  stack := [Erlean.Semantics.Frame.seq
              { moduleName := "actor_protocol",
                env := [(7, Erlean.Core.Value.pid 0),
                        (6, Erlean.Core.Value.reference 0),
                        (3, Erlean.Core.Value.pid 1),
                        (4, payload),
                        (5, Erlean.Core.Value.atom "infinity"),
                        (0, Erlean.Core.Value.pid 1),
                        (1, payload),
                        (2, Erlean.Core.Value.atom "infinity")] }
              (Erlean.Core.Expr.letrec [(8, 1)] (Erlean.Core.Expr.apply (Erlean.Core.Expr.var 8) [])),
            Erlean.Semantics.Frame.bind
              { moduleName := "actor_protocol",
                env := [(2, Erlean.Core.Value.pid 1),
                        (1, payload),
                        (0, payload)] }
              [3]
              (Erlean.Core.Expr.seq
                (Erlean.Core.Expr.call
                  (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "erlang"))
                  (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "!"))
                  [Erlean.Core.Expr.var 2, Erlean.Core.Expr.lit (Erlean.Core.Value.atom "stop")])
                (Erlean.Core.Expr.var 3))] }

def clientPeekState (payload : Value) : LocalState :=
{ control := Erlean.Semantics.Control.runtime "recv_peek_message" [],
  context := { moduleName := "actor_protocol",
               env := [(8,
                        Erlean.Core.Value.closure
                          "actor_protocol"
                          1
                          [(7, Erlean.Core.Value.pid 0),
                           (6, Erlean.Core.Value.reference 0),
                           (3, Erlean.Core.Value.pid 1),
                           (4, payload),
                           (5, Erlean.Core.Value.atom "infinity"),
                           (0, Erlean.Core.Value.pid 1),
                           (1, payload),
                           (2, Erlean.Core.Value.atom "infinity")]
                          [(8, 1)]),
                       (7, Erlean.Core.Value.pid 0),
                       (6, Erlean.Core.Value.reference 0),
                       (3, Erlean.Core.Value.pid 1),
                       (4, payload),
                       (5, Erlean.Core.Value.atom "infinity"),
                       (0, Erlean.Core.Value.pid 1),
                       (1, payload),
                       (2, Erlean.Core.Value.atom "infinity")] },
  stack := [Erlean.Semantics.Frame.bind
              { moduleName := "actor_protocol",
                env := [(8,
                         Erlean.Core.Value.closure
                           "actor_protocol"
                           1
                           [(7, Erlean.Core.Value.pid 0),
                            (6, Erlean.Core.Value.reference 0),
                            (3, Erlean.Core.Value.pid 1),
                            (4, payload),
                            (5, Erlean.Core.Value.atom "infinity"),
                            (0, Erlean.Core.Value.pid 1),
                            (1, payload),
                            (2, Erlean.Core.Value.atom "infinity")]
                           [(8, 1)]),
                        (7, Erlean.Core.Value.pid 0),
                        (6, Erlean.Core.Value.reference 0),
                        (3, Erlean.Core.Value.pid 1),
                        (4, payload),
                        (5, Erlean.Core.Value.atom "infinity"),
                        (0, Erlean.Core.Value.pid 1),
                        (1, payload),
                        (2, Erlean.Core.Value.atom "infinity")] }
              [9, 10]
              (Erlean.Core.Expr.caseE
                (Erlean.Core.Expr.var 9)
                [([Erlean.Core.Pattern.lit (Erlean.Core.Value.atom "true")],
                  Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                  Erlean.Core.Expr.caseE
                    (Erlean.Core.Expr.var 10)
                    [([Erlean.Core.Pattern.tuple
                         [Erlean.Core.Pattern.lit (Erlean.Core.Value.atom "reply"),
                          Erlean.Core.Pattern.var 11,
                          Erlean.Core.Pattern.var 12]],
                      Erlean.Core.Expr.call
                        (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "erlang"))
                        (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "=:="))
                        [Erlean.Core.Expr.var 11, Erlean.Core.Expr.var 6],
                      Erlean.Core.Expr.seq
                        (Erlean.Core.Expr.primop "remove_message" [])
                        (Erlean.Core.Expr.tuple
                          [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "ok"), Erlean.Core.Expr.var 12])),
                     ([Erlean.Core.Pattern.var 11],
                      Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                      Erlean.Core.Expr.seq
                        (Erlean.Core.Expr.primop "recv_next" [])
                        (Erlean.Core.Expr.apply (Erlean.Core.Expr.var 8) []))]),
                 ([Erlean.Core.Pattern.lit (Erlean.Core.Value.atom "false")],
                  Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                  Erlean.Core.Expr.letE
                    [11]
                    (Erlean.Core.Expr.primop "recv_wait_timeout" [Erlean.Core.Expr.var 5])
                    (Erlean.Core.Expr.caseE
                      (Erlean.Core.Expr.var 11)
                      [([Erlean.Core.Pattern.lit (Erlean.Core.Value.atom "true")],
                        Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                        Erlean.Core.Expr.lit (Erlean.Core.Value.atom "timeout")),
                       ([Erlean.Core.Pattern.lit (Erlean.Core.Value.atom "false")],
                        Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                        Erlean.Core.Expr.apply (Erlean.Core.Expr.var 8) [])]))]),
            Erlean.Semantics.Frame.bind
              { moduleName := "actor_protocol",
                env := [(2, Erlean.Core.Value.pid 1),
                        (1, payload),
                        (0, payload)] }
              [3]
              (Erlean.Core.Expr.seq
                (Erlean.Core.Expr.call
                  (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "erlang"))
                  (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "!"))
                  [Erlean.Core.Expr.var 2, Erlean.Core.Expr.lit (Erlean.Core.Value.atom "stop")])
                (Erlean.Core.Expr.var 3))] }

def clientWaitState (payload : Value) : LocalState :=
{ control := Erlean.Semantics.Control.runtime "recv_wait_timeout" [Erlean.Core.Value.atom "infinity"],
  context := { moduleName := "actor_protocol",
               env := [(9, Erlean.Core.Value.atom "false"),
                       (10, Erlean.Core.Value.atom "undefined"),
                       (8,
                        Erlean.Core.Value.closure
                          "actor_protocol"
                          1
                          [(7, Erlean.Core.Value.pid 0),
                           (6, Erlean.Core.Value.reference 0),
                           (3, Erlean.Core.Value.pid 1),
                           (4, payload),
                           (5, Erlean.Core.Value.atom "infinity"),
                           (0, Erlean.Core.Value.pid 1),
                           (1, payload),
                           (2, Erlean.Core.Value.atom "infinity")]
                          [(8, 1)]),
                       (7, Erlean.Core.Value.pid 0),
                       (6, Erlean.Core.Value.reference 0),
                       (3, Erlean.Core.Value.pid 1),
                       (4, payload),
                       (5, Erlean.Core.Value.atom "infinity"),
                       (0, Erlean.Core.Value.pid 1),
                       (1, payload),
                       (2, Erlean.Core.Value.atom "infinity")] },
  stack := [Erlean.Semantics.Frame.bind
              { moduleName := "actor_protocol",
                env := [(9, Erlean.Core.Value.atom "false"),
                        (10, Erlean.Core.Value.atom "undefined"),
                        (8,
                         Erlean.Core.Value.closure
                           "actor_protocol"
                           1
                           [(7, Erlean.Core.Value.pid 0),
                            (6, Erlean.Core.Value.reference 0),
                            (3, Erlean.Core.Value.pid 1),
                            (4, payload),
                            (5, Erlean.Core.Value.atom "infinity"),
                            (0, Erlean.Core.Value.pid 1),
                            (1, payload),
                            (2, Erlean.Core.Value.atom "infinity")]
                           [(8, 1)]),
                        (7, Erlean.Core.Value.pid 0),
                        (6, Erlean.Core.Value.reference 0),
                        (3, Erlean.Core.Value.pid 1),
                        (4, payload),
                        (5, Erlean.Core.Value.atom "infinity"),
                        (0, Erlean.Core.Value.pid 1),
                        (1, payload),
                        (2, Erlean.Core.Value.atom "infinity")] }
              [11]
              (Erlean.Core.Expr.caseE
                (Erlean.Core.Expr.var 11)
                [([Erlean.Core.Pattern.lit (Erlean.Core.Value.atom "true")],
                  Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                  Erlean.Core.Expr.lit (Erlean.Core.Value.atom "timeout")),
                 ([Erlean.Core.Pattern.lit (Erlean.Core.Value.atom "false")],
                  Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                  Erlean.Core.Expr.apply (Erlean.Core.Expr.var 8) [])]),
            Erlean.Semantics.Frame.bind
              { moduleName := "actor_protocol",
                env := [(2, Erlean.Core.Value.pid 1),
                        (1, payload),
                        (0, payload)] }
              [3]
              (Erlean.Core.Expr.seq
                (Erlean.Core.Expr.call
                  (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "erlang"))
                  (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "!"))
                  [Erlean.Core.Expr.var 2, Erlean.Core.Expr.lit (Erlean.Core.Value.atom "stop")])
                (Erlean.Core.Expr.var 3))] }

def clientRemoveState (payload : Value) : LocalState :=
{ control := Erlean.Semantics.Control.runtime "remove_message" [],
  context := { moduleName := "actor_protocol",
               env := [(11, Erlean.Core.Value.reference 0),
                       (12, payload),
                       (9, Erlean.Core.Value.atom "true"),
                       (10,
                        Erlean.Core.Value.tuple
                          [Erlean.Core.Value.atom "reply",
                           Erlean.Core.Value.reference 0,
                           payload]),
                       (8,
                        Erlean.Core.Value.closure
                          "actor_protocol"
                          1
                          [(7, Erlean.Core.Value.pid 0),
                           (6, Erlean.Core.Value.reference 0),
                           (3, Erlean.Core.Value.pid 1),
                           (4, payload),
                           (5, Erlean.Core.Value.atom "infinity"),
                           (0, Erlean.Core.Value.pid 1),
                           (1, payload),
                           (2, Erlean.Core.Value.atom "infinity")]
                          [(8, 1)]),
                       (7, Erlean.Core.Value.pid 0),
                       (6, Erlean.Core.Value.reference 0),
                       (3, Erlean.Core.Value.pid 1),
                       (4, payload),
                       (5, Erlean.Core.Value.atom "infinity"),
                       (0, Erlean.Core.Value.pid 1),
                       (1, payload),
                       (2, Erlean.Core.Value.atom "infinity")] },
  stack := [Erlean.Semantics.Frame.seq
              { moduleName := "actor_protocol",
                env := [(11, Erlean.Core.Value.reference 0),
                        (12, payload),
                        (9, Erlean.Core.Value.atom "true"),
                        (10,
                         Erlean.Core.Value.tuple
                           [Erlean.Core.Value.atom "reply",
                            Erlean.Core.Value.reference 0,
                            payload]),
                        (8,
                         Erlean.Core.Value.closure
                           "actor_protocol"
                           1
                           [(7, Erlean.Core.Value.pid 0),
                            (6, Erlean.Core.Value.reference 0),
                            (3, Erlean.Core.Value.pid 1),
                            (4, payload),
                            (5, Erlean.Core.Value.atom "infinity"),
                            (0, Erlean.Core.Value.pid 1),
                            (1, payload),
                            (2, Erlean.Core.Value.atom "infinity")]
                           [(8, 1)]),
                        (7, Erlean.Core.Value.pid 0),
                        (6, Erlean.Core.Value.reference 0),
                        (3, Erlean.Core.Value.pid 1),
                        (4, payload),
                        (5, Erlean.Core.Value.atom "infinity"),
                        (0, Erlean.Core.Value.pid 1),
                        (1, payload),
                        (2, Erlean.Core.Value.atom "infinity")] }
              (Erlean.Core.Expr.tuple [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "ok"), Erlean.Core.Expr.var 12]),
            Erlean.Semantics.Frame.bind
              { moduleName := "actor_protocol",
                env := [(2, Erlean.Core.Value.pid 1),
                        (1, payload),
                        (0, payload)] }
              [3]
              (Erlean.Core.Expr.seq
                (Erlean.Core.Expr.call
                  (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "erlang"))
                  (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "!"))
                  [Erlean.Core.Expr.var 2, Erlean.Core.Expr.lit (Erlean.Core.Value.atom "stop")])
                (Erlean.Core.Expr.var 3))] }

def clientSendStopState (payload : Value) : LocalState :=
{ control := Erlean.Semantics.Control.runtime "send" [Erlean.Core.Value.pid 1, Erlean.Core.Value.atom "stop"],
  context := { moduleName := "actor_protocol",
               env := [(3,
                        Erlean.Core.Value.tuple
                          [Erlean.Core.Value.atom "ok", payload]),
                       (2, Erlean.Core.Value.pid 1),
                       (1, payload),
                       (0, payload)] },
  stack := [Erlean.Semantics.Frame.seq
              { moduleName := "actor_protocol",
                env := [(3,
                         Erlean.Core.Value.tuple
                           [Erlean.Core.Value.atom "ok", payload]),
                        (2, Erlean.Core.Value.pid 1),
                        (1, payload),
                        (0, payload)] }
              (Erlean.Core.Expr.var 3)] }

def clientDoneState (payload : Value) : LocalState :=
{ control := Erlean.Semantics.Control.ret
               [Erlean.Core.Value.tuple
                  [Erlean.Core.Value.atom "ok", payload]],
  context := { moduleName := "actor_protocol",
               env := [(3,
                        Erlean.Core.Value.tuple
                          [Erlean.Core.Value.atom "ok", payload]),
                       (2, Erlean.Core.Value.pid 1),
                       (1, payload),
                       (0, payload)] },
  stack := [] }

def serverPeekState : LocalState :=
{ control := Erlean.Semantics.Control.runtime "recv_peek_message" [],
  context := { moduleName := "actor_protocol", env := [(0, Erlean.Core.Value.closure "actor_protocol" 0 [] [(0, 0)])] },
  stack := [Erlean.Semantics.Frame.bind
              { moduleName := "actor_protocol", env := [(0, Erlean.Core.Value.closure "actor_protocol" 0 [] [(0, 0)])] }
              [1, 2]
              (Erlean.Core.Expr.caseE
                (Erlean.Core.Expr.var 1)
                [([Erlean.Core.Pattern.lit (Erlean.Core.Value.atom "true")],
                  Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                  Erlean.Core.Expr.caseE
                    (Erlean.Core.Expr.var 2)
                    [([Erlean.Core.Pattern.tuple
                         [Erlean.Core.Pattern.lit (Erlean.Core.Value.atom "request"),
                          Erlean.Core.Pattern.var 3,
                          Erlean.Core.Pattern.var 4,
                          Erlean.Core.Pattern.var 5]],
                      Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                      Erlean.Core.Expr.seq
                        (Erlean.Core.Expr.primop "remove_message" [])
                        (Erlean.Core.Expr.seq
                          (Erlean.Core.Expr.call
                            (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "erlang"))
                            (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "!"))
                            [Erlean.Core.Expr.var 3,
                             Erlean.Core.Expr.tuple
                               [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "reply"),
                                Erlean.Core.Expr.var 4,
                                Erlean.Core.Expr.var 5]])
                          (Erlean.Core.Expr.apply (Erlean.Core.Expr.funRef "server" 0) []))),
                     ([Erlean.Core.Pattern.lit (Erlean.Core.Value.atom "stop")],
                      Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                      Erlean.Core.Expr.seq
                        (Erlean.Core.Expr.primop "remove_message" [])
                        (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "ok"))),
                     ([Erlean.Core.Pattern.var 3],
                      Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                      Erlean.Core.Expr.seq
                        (Erlean.Core.Expr.primop "recv_next" [])
                        (Erlean.Core.Expr.apply (Erlean.Core.Expr.var 0) []))]),
                 ([Erlean.Core.Pattern.lit (Erlean.Core.Value.atom "false")],
                  Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                  Erlean.Core.Expr.letE
                    [3]
                    (Erlean.Core.Expr.primop
                      "recv_wait_timeout"
                      [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "infinity")])
                    (Erlean.Core.Expr.caseE
                      (Erlean.Core.Expr.var 3)
                      [([Erlean.Core.Pattern.lit (Erlean.Core.Value.atom "true")],
                        Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                        Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true")),
                       ([Erlean.Core.Pattern.lit (Erlean.Core.Value.atom "false")],
                        Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                        Erlean.Core.Expr.apply (Erlean.Core.Expr.var 0) [])]))])] }

def serverWaitState : LocalState :=
{ control := Erlean.Semantics.Control.runtime "recv_wait_timeout" [Erlean.Core.Value.atom "infinity"],
  context := { moduleName := "actor_protocol",
               env := [(1, Erlean.Core.Value.atom "false"),
                       (2, Erlean.Core.Value.atom "undefined"),
                       (0, Erlean.Core.Value.closure "actor_protocol" 0 [] [(0, 0)])] },
  stack := [Erlean.Semantics.Frame.bind
              { moduleName := "actor_protocol",
                env := [(1, Erlean.Core.Value.atom "false"),
                        (2, Erlean.Core.Value.atom "undefined"),
                        (0, Erlean.Core.Value.closure "actor_protocol" 0 [] [(0, 0)])] }
              [3]
              (Erlean.Core.Expr.caseE
                (Erlean.Core.Expr.var 3)
                [([Erlean.Core.Pattern.lit (Erlean.Core.Value.atom "true")],
                  Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                  Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true")),
                 ([Erlean.Core.Pattern.lit (Erlean.Core.Value.atom "false")],
                  Erlean.Core.Expr.lit (Erlean.Core.Value.atom "true"),
                  Erlean.Core.Expr.apply (Erlean.Core.Expr.var 0) [])])] }

def serverRemoveRequestState (payload : Value) : LocalState :=
{ control := Erlean.Semantics.Control.runtime "remove_message" [],
  context := { moduleName := "actor_protocol",
               env := [(3, Erlean.Core.Value.pid 0),
                       (4, Erlean.Core.Value.reference 0),
                       (5, payload),
                       (1, Erlean.Core.Value.atom "true"),
                       (2,
                        Erlean.Core.Value.tuple
                          [Erlean.Core.Value.atom "request",
                           Erlean.Core.Value.pid 0,
                           Erlean.Core.Value.reference 0,
                           payload]),
                       (0, Erlean.Core.Value.closure "actor_protocol" 0 [] [(0, 0)])] },
  stack := [Erlean.Semantics.Frame.seq
              { moduleName := "actor_protocol",
                env := [(3, Erlean.Core.Value.pid 0),
                        (4, Erlean.Core.Value.reference 0),
                        (5, payload),
                        (1, Erlean.Core.Value.atom "true"),
                        (2,
                         Erlean.Core.Value.tuple
                           [Erlean.Core.Value.atom "request",
                            Erlean.Core.Value.pid 0,
                            Erlean.Core.Value.reference 0,
                            payload]),
                        (0, Erlean.Core.Value.closure "actor_protocol" 0 [] [(0, 0)])] }
              (Erlean.Core.Expr.seq
                (Erlean.Core.Expr.call
                  (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "erlang"))
                  (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "!"))
                  [Erlean.Core.Expr.var 3,
                   Erlean.Core.Expr.tuple
                     [Erlean.Core.Expr.lit (Erlean.Core.Value.atom "reply"),
                      Erlean.Core.Expr.var 4,
                      Erlean.Core.Expr.var 5]])
                (Erlean.Core.Expr.apply (Erlean.Core.Expr.funRef "server" 0) []))] }

def serverSendReplyState (payload : Value) : LocalState :=
{ control := Erlean.Semantics.Control.runtime
               "send"
               [Erlean.Core.Value.pid 0,
                Erlean.Core.Value.tuple
                  [Erlean.Core.Value.atom "reply",
                   Erlean.Core.Value.reference 0,
                   payload]],
  context := { moduleName := "actor_protocol",
               env := [(3, Erlean.Core.Value.pid 0),
                       (4, Erlean.Core.Value.reference 0),
                       (5, payload),
                       (1, Erlean.Core.Value.atom "true"),
                       (2,
                        Erlean.Core.Value.tuple
                          [Erlean.Core.Value.atom "request",
                           Erlean.Core.Value.pid 0,
                           Erlean.Core.Value.reference 0,
                           payload]),
                       (0, Erlean.Core.Value.closure "actor_protocol" 0 [] [(0, 0)])] },
  stack := [Erlean.Semantics.Frame.seq
              { moduleName := "actor_protocol",
                env := [(3, Erlean.Core.Value.pid 0),
                        (4, Erlean.Core.Value.reference 0),
                        (5, payload),
                        (1, Erlean.Core.Value.atom "true"),
                        (2,
                         Erlean.Core.Value.tuple
                           [Erlean.Core.Value.atom "request",
                            Erlean.Core.Value.pid 0,
                            Erlean.Core.Value.reference 0,
                            payload]),
                        (0, Erlean.Core.Value.closure "actor_protocol" 0 [] [(0, 0)])] }
              (Erlean.Core.Expr.apply (Erlean.Core.Expr.funRef "server" 0) [])] }

def serverRemoveStopState : LocalState :=
{ control := Erlean.Semantics.Control.runtime "remove_message" [],
  context := { moduleName := "actor_protocol",
               env := [(1, Erlean.Core.Value.atom "true"),
                       (2, Erlean.Core.Value.atom "stop"),
                       (0, Erlean.Core.Value.closure "actor_protocol" 0 [] [(0, 0)])] },
  stack := [Erlean.Semantics.Frame.seq
              { moduleName := "actor_protocol",
                env := [(1, Erlean.Core.Value.atom "true"),
                        (2, Erlean.Core.Value.atom "stop"),
                        (0, Erlean.Core.Value.closure "actor_protocol" 0 [] [(0, 0)])] }
              (Erlean.Core.Expr.lit (Erlean.Core.Value.atom "ok"))] }

def serverDoneState : LocalState :=
{ control := Erlean.Semantics.Control.ret [Erlean.Core.Value.atom "ok"],
  context := { moduleName := "actor_protocol",
               env := [(1, Erlean.Core.Value.atom "true"),
                       (2, Erlean.Core.Value.atom "stop"),
                       (0, Erlean.Core.Value.closure "actor_protocol" 0 [] [(0, 0)])] },
  stack := [] }

/- The following tactic performs kernel-checked rewriting of the actual imported
   machine. It never replaces an unsuccessful search with a fabricated endpoint. -/
macro "protocol_boundary" : tactic => `(tactic|
  simp_all [clientSpawnState, clientNewReferenceState, clientSelfState, clientSendRequestState, clientPeekState, clientWaitState, clientRemoveState, clientSendStopState, clientDoneState, serverPeekState, serverWaitState, serverRemoveRequestState, serverSendReplyState, serverRemoveStopState, serverDoneState,
    clientSpawn, clientNewReference, clientSelf, clientSendRequest,
    clientPeek, clientWait, clientRemove, clientSendStop, clientDone,
    serverPeek, serverWait, serverRemoveRequest, serverSendReply, serverRemoveStop, serverDone,
    actualBoundary, resumeBoundary, seekBoundary, isActorBoundary, initialCall,
    stepLocal, nextControl, startCollect, finishCollect, invoke, builtin,
    lookupFunction, makeClosureValue, recursiveEnv, applyClosure, importedActorProtocolModule,
    Env.lookup, matchPatterns, matchPattern, patternsObservationAllowed,
    patternObservationAllowed, literalObservationAllowed, literalListObservationAllowed,
    Value.publicList, Value.isPublic, Value.exactComparable, Value.comparableList,
    Value.equal, Value.equalList, Value.equalEnv, BEq.beq, List.beq,
    requestPayload, replyPayload, Pure.pure, Except.pure, Bind.bind, Except.bind,
    Functor.map, Except.map, Option.bind, Option.map, List.mapM_cons, List.mapM_nil])

theorem clientSpawn_eq (payload : Value) :
    clientSpawn payload = some (clientSpawnState payload) := by
  cbv

theorem clientNewReference_eq (payload : Value) :
    clientNewReference payload = some (clientNewReferenceState payload) := by
  simp only [clientNewReference, resumeBoundary, clientSpawn_eq payload, Bind.bind, Option.bind]
  cbv

theorem clientSelf_eq (payload : Value) :
    clientSelf payload = some (clientSelfState payload) := by
  simp only [clientSelf, resumeBoundary, clientNewReference_eq payload, Bind.bind, Option.bind]
  cbv

theorem clientSendRequest_eq (payload : Value) (publicPayload : payload.isPublic = true) :
    clientSendRequest payload = some (clientSendRequestState payload) := by
  simp only [clientSendRequest, resumeBoundary, clientSelf_eq payload, Bind.bind, Option.bind]
  protocol_boundary

theorem clientPeek_eq (payload : Value) (publicPayload : payload.isPublic = true) :
    clientPeek payload = some (clientPeekState payload) := by
  simp only [clientPeek, resumeBoundary, clientSendRequest_eq payload publicPayload, Bind.bind, Option.bind]
  cbv

theorem clientWait_eq (payload : Value) (publicPayload : payload.isPublic = true) :
    clientWait payload = some (clientWaitState payload) := by
  simp only [clientWait, resumeBoundary, clientPeek_eq payload publicPayload, Bind.bind, Option.bind]
  protocol_boundary

theorem clientRemove_eq (payload : Value) (publicPayload : payload.isPublic = true) :
    clientRemove payload = some (clientRemoveState payload) := by
  simp only [clientRemove, resumeBoundary, clientPeek_eq payload publicPayload, Bind.bind, Option.bind]
  cbv

theorem clientSendStop_eq (payload : Value) (publicPayload : payload.isPublic = true) :
    clientSendStop payload = some (clientSendStopState payload) := by
  simp only [clientSendStop, resumeBoundary, clientRemove_eq payload publicPayload, Bind.bind, Option.bind]
  protocol_boundary

theorem clientDone_eq (payload : Value) (publicPayload : payload.isPublic = true) :
    clientDone payload = some (clientDoneState payload) := by
  simp only [clientDone, resumeBoundary, clientSendStop_eq payload publicPayload, Bind.bind, Option.bind]
  protocol_boundary

theorem serverPeek_eq :
    serverPeek = some (serverPeekState) := by
  cbv

theorem serverWait_eq :
    serverWait = some (serverWaitState) := by
  simp only [serverWait, resumeBoundary, serverPeek_eq, Bind.bind, Option.bind]
  cbv

theorem serverRemoveRequest_eq (payload : Value) (_publicPayload : payload.isPublic = true) :
    serverRemoveRequest payload = some (serverRemoveRequestState payload) := by
  simp only [serverRemoveRequest, resumeBoundary, serverPeek_eq, Bind.bind, Option.bind]
  protocol_boundary

theorem serverSendReply_eq (payload : Value) (publicPayload : payload.isPublic = true) :
    serverSendReply payload = some (serverSendReplyState payload) := by
  simp only [serverSendReply, resumeBoundary, serverRemoveRequest_eq payload publicPayload, Bind.bind, Option.bind]
  protocol_boundary

theorem serverRemoveStop_eq :
    serverRemoveStop = some (serverRemoveStopState) := by
  simp only [serverRemoveStop, resumeBoundary, serverPeek_eq, Bind.bind, Option.bind]
  cbv

theorem serverDone_eq :
    serverDone = some (serverDoneState) := by
  simp only [serverDone, resumeBoundary, serverRemoveStop_eq, Bind.bind, Option.bind]
  cbv

theorem clientSpawn_control (payload : Value) (_publicPayload : payload.isPublic = true) :
    (clientSpawn payload).map LocalState.control =
      some (.runtime "spawn" [.atom "actor_protocol", .atom "server", .nil]) := by
  rw [clientSpawn_eq payload]
  rfl

theorem clientNewReference_control (payload : Value) (_publicPayload : payload.isPublic = true) :
    (clientNewReference payload).map LocalState.control = some (.runtime "make_ref" []) := by
  rw [clientNewReference_eq payload]
  rfl

theorem clientSelf_control (payload : Value) (_publicPayload : payload.isPublic = true) :
    (clientSelf payload).map LocalState.control = some (.runtime "self" []) := by
  rw [clientSelf_eq payload]
  rfl

theorem clientSendRequest_control (payload : Value) (publicPayload : payload.isPublic = true) :
    (clientSendRequest payload).map LocalState.control =
      some (.runtime "send" [.pid 1, requestPayload 0 0 payload]) := by
  rw [clientSendRequest_eq payload publicPayload]
  rfl

theorem clientPeek_control (payload : Value) (publicPayload : payload.isPublic = true) :
    (clientPeek payload).map LocalState.control = some (.runtime "recv_peek_message" []) := by
  rw [clientPeek_eq payload publicPayload]
  rfl

theorem clientWait_control (payload : Value) (publicPayload : payload.isPublic = true) :
    (clientWait payload).map LocalState.control =
      some (.runtime "recv_wait_timeout" [.atom "infinity"]) := by
  rw [clientWait_eq payload publicPayload]
  rfl

theorem clientRemove_control (payload : Value) (publicPayload : payload.isPublic = true) :
    (clientRemove payload).map LocalState.control = some (.runtime "remove_message" []) := by
  rw [clientRemove_eq payload publicPayload]
  rfl

theorem clientSendStop_control (payload : Value) (publicPayload : payload.isPublic = true) :
    (clientSendStop payload).map LocalState.control = some (.runtime "send" [.pid 1, .atom "stop"]) := by
  rw [clientSendStop_eq payload publicPayload]
  rfl

theorem clientDone_control (payload : Value) (publicPayload : payload.isPublic = true) :
    (clientDone payload).map LocalState.control = some (.ret [.tuple [.atom "ok", payload]]) := by
  rw [clientDone_eq payload publicPayload]
  rfl

theorem clientDone_stack (payload : Value) (publicPayload : payload.isPublic = true) :
    (clientDone payload).map LocalState.stack = some [] := by
  rw [clientDone_eq payload publicPayload]
  rfl

theorem serverPeek_control : serverPeek.map LocalState.control = some (.runtime "recv_peek_message" []) := by
  rw [serverPeek_eq]
  rfl

theorem serverWait_control :
    serverWait.map LocalState.control = some (.runtime "recv_wait_timeout" [.atom "infinity"]) := by
  rw [serverWait_eq]
  rfl

theorem serverRemoveRequest_control (payload : Value) (publicPayload : payload.isPublic = true) :
    (serverRemoveRequest payload).map LocalState.control = some (.runtime "remove_message" []) := by
  rw [serverRemoveRequest_eq payload publicPayload]
  rfl

theorem serverSendReply_control (payload : Value) (publicPayload : payload.isPublic = true) :
    (serverSendReply payload).map LocalState.control =
      some (.runtime "send" [.pid 0, replyPayload 0 payload]) := by
  rw [serverSendReply_eq payload publicPayload]
  rfl

theorem serverRemoveStop_control :
    serverRemoveStop.map LocalState.control = some (.runtime "remove_message" []) := by
  rw [serverRemoveStop_eq]
  rfl

theorem serverDone_control : serverDone.map LocalState.control = some (.ret [.atom "ok"]) := by
  rw [serverDone_eq]
  rfl

theorem serverDone_stack : serverDone.map LocalState.stack = some [] := by
  rw [serverDone_eq]
  rfl

/-- Infinite waits resume the exact receive-loop endpoint, including captures
    and the original client continuation, rather than just the same control tag. -/
theorem clientWait_loop (payload : Value) (publicPayload : payload.isPublic = true) :
    resumeBoundary (clientWait payload) [.atom "false"] = clientPeek payload := by
  rw [clientWait_eq payload publicPayload, clientPeek_eq payload publicPayload]
  simp only [resumeBoundary, Bind.bind, Option.bind]
  protocol_boundary

theorem serverWait_loop : resumeBoundary serverWait [.atom "false"] = serverPeek := by
  rw [serverWait_eq, serverPeek_eq]
  simp only [resumeBoundary, Bind.bind, Option.bind]
  protocol_boundary

theorem serverSendReply_loop (payload : Value) (publicPayload : payload.isPublic = true) :
    resumeBoundary (serverSendReply payload) [replyPayload 0 payload] = serverPeek := by
  rw [serverSendReply_eq payload publicPayload, serverPeek_eq]
  simp only [resumeBoundary, Bind.bind, Option.bind]
  protocol_boundary

theorem boundary_exists_of_control (boundary : Option LocalState) (control : Control)
    (observed : boundary.map LocalState.control = some control) :
    ∃ state, boundary = some state ∧ state.control = control := by
  cases found : boundary with
  | none => simp [found] at observed
  | some state => exact ⟨state, rfl, by simpa [found] using observed⟩

/-- Every successful resumed endpoint has a checked local segment starting at
    the actual runtime response state. -/
theorem resumeBoundary_sound (boundary : Option LocalState) (response : Values)
    (before after : LocalState) (found : boundary = some before)
    (resumed : resumeBoundary boundary response = some after) :
    ReachesBoundary (stepLocal [importedActorProtocolModule])
      { before with control := .ret response } after ∧ isActorBoundary after = true := by
  apply actualBoundary_sound
  simpa [resumeBoundary, found, Bind.bind, Option.bind] using resumed

theorem clientSpawn_segment (payload : Value) (publicPayload : payload.isPublic = true) :
    ∃ endpoint, clientSpawn payload = some endpoint ∧
      ReachesBoundary (stepLocal [importedActorProtocolModule])
        (initialCall "actor_protocol" "exchange" [payload]) endpoint := by
  obtain ⟨endpoint, found, _⟩ := boundary_exists_of_control _ _ (clientSpawn_control payload publicPayload)
  exact ⟨endpoint, found, (actualBoundary_sound found).1⟩

theorem serverPeek_segment :
    ∃ endpoint, serverPeek = some endpoint ∧
      ReachesBoundary (stepLocal [importedActorProtocolModule])
        (initialCall "actor_protocol" "server" []) endpoint := by
  obtain ⟨endpoint, found, _⟩ := boundary_exists_of_control _ _ serverPeek_control
  exact ⟨endpoint, found, (actualBoundary_sound found).1⟩

def ClientStage.expectedControl (payload : Value) : ClientStage → Control
  | .spawn => .runtime "spawn" [.atom "actor_protocol", .atom "server", .nil]
  | .newReference => .runtime "make_ref" []
  | .self => .runtime "self" []
  | .sendRequest => .runtime "send" [.pid 1, requestPayload 0 0 payload]
  | .peek => .runtime "recv_peek_message" []
  | .wait => .runtime "recv_wait_timeout" [.atom "infinity"]
  | .remove => .runtime "remove_message" []
  | .sendStop => .runtime "send" [.pid 1, .atom "stop"]
  | .done => .ret [.tuple [.atom "ok", payload]]

def ServerStage.expectedControl (payload : Value) : ServerStage → Control
  | .peek => .runtime "recv_peek_message" []
  | .wait => .runtime "recv_wait_timeout" [.atom "infinity"]
  | .removeRequest => .runtime "remove_message" []
  | .sendReply => .runtime "send" [.pid 0, replyPayload 0 payload]
  | .removeStop => .runtime "remove_message" []
  | .done => .ret [.atom "ok"]

theorem clientBoundary_control (payload : Value) (publicPayload : payload.isPublic = true)
    (stage : ClientStage) :
    (stage.boundary payload).map LocalState.control = some (stage.expectedControl payload) := by
  cases stage with
  | spawn => exact clientSpawn_control payload publicPayload
  | newReference => exact clientNewReference_control payload publicPayload
  | self => exact clientSelf_control payload publicPayload
  | sendRequest => exact clientSendRequest_control payload publicPayload
  | peek => exact clientPeek_control payload publicPayload
  | wait => exact clientWait_control payload publicPayload
  | remove => exact clientRemove_control payload publicPayload
  | sendStop => exact clientSendStop_control payload publicPayload
  | done => exact clientDone_control payload publicPayload

theorem serverBoundary_control (payload : Value) (publicPayload : payload.isPublic = true)
    (stage : ServerStage) :
    (stage.boundary payload).map LocalState.control = some (stage.expectedControl payload) := by
  cases stage with
  | peek => exact serverPeek_control
  | wait => exact serverWait_control
  | removeRequest => exact serverRemoveRequest_control payload publicPayload
  | sendReply => exact serverSendReply_control payload publicPayload
  | removeStop => exact serverRemoveStop_control
  | done => exact serverDone_control

/-- A client boundary that halts as a program, rather than suspending for the
    actor runtime, is exactly its successful final phase. -/
theorem clientBoundary_program_halt (payload : Value) (publicPayload : payload.isPublic = true)
    (stage : ClientStage) (endpoint : LocalState) {outcome : Outcome}
    (found : stage.boundary payload = some endpoint)
    (halted : stepLocal [importedActorProtocolModule] endpoint = .halt outcome)
    (notRuntime : ∀ name args, endpoint.control ≠ .runtime name args) :
    stage = .done ∧ outcome = .returned [.tuple [.atom "ok", payload]] := by
  have atControl : endpoint.control = stage.expectedControl payload := by
    simpa [found] using clientBoundary_control payload publicPayload stage
  cases stage <;> simp only [ClientStage.expectedControl] at atControl
  all_goals try exact False.elim (notRuntime _ _ atControl)
  have doneFound : clientDone payload = some endpoint := found
  have empty : endpoint.stack = [] := by simpa [doneFound] using clientDone_stack payload publicPayload
  have outcomeEq : (Transition.halt (.returned [.tuple [.atom "ok", payload]]) :
      Transition LocalState Outcome) = .halt outcome := by
    simpa [stepLocal, atControl, empty] using halted
  exact ⟨rfl, (Transition.halt.inj outcomeEq).symm⟩

theorem serverBoundary_program_halt (payload : Value) (publicPayload : payload.isPublic = true)
    (stage : ServerStage) (endpoint : LocalState) {outcome : Outcome}
    (found : stage.boundary payload = some endpoint)
    (halted : stepLocal [importedActorProtocolModule] endpoint = .halt outcome)
    (notRuntime : ∀ name args, endpoint.control ≠ .runtime name args) :
    outcome = .returned [.atom "ok"] := by
  have atControl : endpoint.control = stage.expectedControl payload := by
    simpa [found] using serverBoundary_control payload publicPayload stage
  cases stage <;> simp only [ServerStage.expectedControl] at atControl
  all_goals try exact False.elim (notRuntime _ _ atControl)
  have doneFound : serverDone = some endpoint := found
  have empty : endpoint.stack = [] := by simpa [doneFound] using serverDone_stack
  have outcomeEq : (Transition.halt (.returned [.atom "ok"]) : Transition LocalState Outcome) =
      .halt outcome := by
    simpa [stepLocal, atControl, empty] using halted
  exact (Transition.halt.inj outcomeEq).symm

end Erlean.Examples.ProtocolInvariant
