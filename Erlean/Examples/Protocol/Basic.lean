import Erlean.Runtime.Actors
import Erlean.Examples.Protocol.Imported

/-!
Kernel-checked building blocks over the executable actor model: replay
composition, FIFO eligibility, and exact imported send/return handler segments.
These local facts alone are not an all-schedule protocol invariant. The complete
control-state proof is organized in the ProtocolPhases, ProtocolInvariant,
ProtocolRuntime, and ProtocolSafety modules; no macro-model refinement is assumed.
-/

namespace Erlean.Examples.Protocol

open Core Semantics Erlean.Runtime

/-- Each transition in this trace is accepted by the actual system stepper. -/
inductive AcceptedTrace (world : CodeWorld) : System → List Choice → System → Prop where
  | nil (system : System) : AcceptedTrace world system [] system
  | cons (accepted : stepSystem world start choice = .ok middle)
      (remaining : AcceptedTrace world middle rest finish) :
      AcceptedTrace world start (choice :: rest) finish

theorem replay_append (world : CodeWorld) (system : System) (first second : List Choice) :
    replay world system (first ++ second) =
      (replay world system first >>= fun middle => replay world middle second) := by
  induction first generalizing system with
  | nil => rfl
  | cons choice rest ih =>
    cases accepted : stepSystem world system choice with
    | error reason => simp [replay, accepted, Bind.bind, Except.bind]
    | ok middle => simpa [replay, accepted, Bind.bind, Except.bind] using ih (system := middle)

theorem acceptedTrace_replay (trace : AcceptedTrace world start choices finish) :
    replay world start choices = .ok finish := by
  induction trace with
  | nil => rfl
  | cons accepted _ ih => simp [replay, accepted, Bind.bind, Except.bind, ih]

theorem replay_acceptedTrace
    (executed : replay world start choices = .ok finish) :
    AcceptedTrace world start choices finish := by
  induction choices generalizing start with
  | nil =>
    simp [replay] at executed
    subst finish
    exact .nil start
  | cons choice rest ih =>
    cases accepted : stepSystem world start choice with
    | error reason => simp [replay, accepted, Bind.bind, Except.bind] at executed
    | ok middle =>
      have suffix : replay world middle rest = .ok finish := by
        simpa [replay, accepted, Bind.bind, Except.bind] using executed
      exact .cons accepted (ih suffix)

/-- Eligibility is checked across all signal kinds for each ordered endpoint pair,
    not merely across ordinary mailbox messages. -/
theorem accepted_delivery_fifo (system next : System) (signalId : Nat) (selected : Signal)
    (found : system.pending.find? (fun signal => signal.id == signalId) = some selected)
    (accepted : deliver system signalId = .ok next) :
    (system.pending.takeWhile (fun signal => signal.id != signalId)).any
      (fun prior => prior.sender == selected.sender && prior.recipient == selected.recipient) = false := by
  cases eligibility : (system.pending.takeWhile (fun signal => signal.id != signalId)).any
      (fun prior => prior.sender == selected.sender && prior.recipient == selected.recipient) with
  | false => rfl
  | true => simp [deliver, found, eligibility, Functor.map, Except.map] at accepted

def replyPayload (reference : Nat) (payload : Value) : Value :=
  .tuple [.atom "reply", .reference reference, payload]

def requestPayload (client reference : Nat) (payload : Value) : Value :=
  .tuple [.atom "request", .pid client, .reference reference, payload]

/-- Select the first message clause from a concrete lowered receive closure.
    Failure remains explicit if the imported artifact's structure changes. -/
def importedReceiveClause (index : Nat) : Option Clause := do
  let code ← importedActorProtocolModule.closureCode[index]?
  let .letE _ _ (.caseE _ peekClauses) := code.body | none
  let (_, _, messageCase) ← peekClauses[0]?
  let .caseE _ clauses := messageCase | none
  clauses[0]?

def serverRequestPattern : Pattern :=
  .tuple [.lit (.atom "request"), .var 3, .var 4, .var 5]

def serverReplyBody : Expr :=
  .seq (.primop "remove_message" [])
    (.seq (.call (.lit (.atom "erlang")) (.lit (.atom "!"))
      [.var 3, .tuple [.lit (.atom "reply"), .var 4, .var 5]])
      (.apply (.funRef "server" 0) []))

theorem imported_server_clause :
    importedReceiveClause 0 = some
      ([serverRequestPattern], .lit (.atom "true"), serverReplyBody) := by
  rfl

theorem server_pattern_binds_request (client reference : Nat) (payload : Value) :
    matchPattern serverRequestPattern (requestPayload client reference payload) =
      some [(3, .pid client), (4, .reference reference), (5, payload)] := by
  simp [serverRequestPattern, requestPayload, matchPattern, matchPatterns, BEq.beq, Value.equal]

def clientReplyPattern : Pattern :=
  .tuple [.lit (.atom "reply"), .var 11, .var 12]

def clientReplyGuard : Expr :=
  .call (.lit (.atom "erlang")) (.lit (.atom "=:=")) [.var 11, .var 6]

def clientReplyBody : Expr :=
  .seq (.primop "remove_message" []) (.tuple [.lit (.atom "ok"), .var 12])

theorem imported_client_clause :
    importedReceiveClause 1 = some ([clientReplyPattern], clientReplyGuard, clientReplyBody) := by
  rfl

theorem client_pattern_binds_reply (reference : Nat) (payload : Value) :
    matchPattern clientReplyPattern (replyPayload reference payload) =
      some [(11, .reference reference), (12, payload)] := by
  simp [clientReplyPattern, replyPayload, matchPattern, matchPatterns, BEq.beq, Value.equal]

/-- Concrete proof boundaries using the actual imported continuation expressions.
    These definitions do not claim that every reachable state is at a boundary;
    the intervening local evaluation states still need simulation cases. -/
def ServerAtMatchedRequest (process : Process) (client reference : Nat) (payload : Value) : Prop :=
  process.state.context.moduleName = "actor_protocol" ∧
  process.state.control = .eval serverReplyBody ∧
  process.state.context.env.lookup 3 = some (.pid client) ∧
  process.state.context.env.lookup 4 = some (.reference reference) ∧
  process.state.context.env.lookup 5 = some payload

def ServerAtSend (process : Process) (client reference : Nat) (payload : Value) : Prop :=
  process.state.context.moduleName = "actor_protocol" ∧
  process.state.control = .runtime "send" [.pid client, replyPayload reference payload]

def ClientAtMatchedReply (process : Process) (reference : Nat) (payload : Value) : Prop :=
  process.state.context.moduleName = "actor_protocol" ∧
  process.state.control = .eval clientReplyBody ∧
  process.state.context.env.lookup 6 = some (.reference reference) ∧
  process.state.context.env.lookup 11 = some (.reference reference) ∧
  process.state.context.env.lookup 12 = some payload

/-- Observable safety property for the closed exchange scenario: every ordinary
    server-to-client signal carries the right reply. -/
def PendingRepliesAuthentic (system : System) (server client reference : Nat)
    (payload : Value) : Prop :=
  ∀ signal ∈ system.pending,
    signal.kind = .message → signal.sender = server → signal.recipient = client →
      signal.message = replyPayload reference payload

/-- Exact runtime boundary for a server reply: both the return value and the
    enqueued message preserve the reference and payload supplied by the caller.
    An imported-handler proof must separately establish that its arguments have
    this shape and originate from the matched request. -/
theorem send_reply_exact (world : CodeWorld) (system : System) (process : Process)
    (recipient reference : Nat) (payload : Value)
    (publicPayload : payload.isPublic = true)
    (freshSignal : system.pending.any (fun signal => signal.id == system.nextSignal) = false) :
    request world system process "send" [.pid recipient, replyPayload reference payload] =
      .ok ((system.update (returnValues process [replyPayload reference payload])).enqueue
        process.pid recipient .message (replyPayload reference payload)) := by
  simp [request, replyPayload, Value.publicList, Value.isPublic, publicPayload,
    freshSignal, System.enqueue, System.update, Pure.pure, Except.pure]

def serverAfterRemoveBody : Expr :=
  .seq (.call (.lit (.atom "erlang")) (.lit (.atom "!"))
    [.var 3, .tuple [.lit (.atom "reply"), .var 4, .var 5]])
    (.apply (.funRef "server" 0) [])

/-- The actual imported handler suspends before removing the matched message. -/
theorem server_remove_prefix (world : CodeWorld) (context : Context) (stack : List Frame) :
    runLocal 2 world { control := .eval serverReplyBody, context, stack } =
      .exhausted {
        control := .runtime "remove_message" []
        context := context
        stack := .seq context serverAfterRemoveBody :: stack } := by
  simp [runLocal, run, stepLocal, serverReplyBody, serverAfterRemoveBody,
    startCollect, finishCollect, nextControl]

/-- After the actor runtime acknowledges removal, the concrete server expression
    sends exactly the values bound by the request pattern. The caller stack is
    arbitrary and is preserved underneath the server's recursive continuation. -/
theorem server_send_prefix (world : CodeWorld) (context : Context) (stack : List Frame)
    (client reference : Nat) (payload : Value)
    (clientBound : context.env.lookup 3 = some (.pid client))
    (referenceBound : context.env.lookup 4 = some (.reference reference))
    (payloadBound : context.env.lookup 5 = some payload)
    (publicPayload : payload.isPublic = true) :
    runLocal 17 world {
      control := .ret [.atom "ok"]
      context := context
      stack := .seq context serverAfterRemoveBody :: stack } =
      .exhausted {
        control := .runtime "send" [.pid client, replyPayload reference payload]
        context := context
        stack := .seq context (.apply (.funRef "server" 0) []) :: stack } := by
  simp [runLocal, run, stepLocal, serverAfterRemoveBody, replyPayload,
    startCollect, finishCollect, nextControl, invoke, builtin,
    clientBound, referenceBound, payloadBound, Value.publicList, Value.isPublic, publicPayload]

theorem client_remove_prefix (world : CodeWorld) (context : Context) (stack : List Frame) :
    runLocal 2 world { control := .eval clientReplyBody, context, stack } =
      .exhausted {
        control := .runtime "remove_message" []
        context := context
        stack := .seq context (.tuple [.lit (.atom "ok"), .var 12]) :: stack } := by
  simp [runLocal, run, stepLocal, clientReplyBody, startCollect, finishCollect, nextControl]

/-- A matched reply resumes the original caller with its exact payload. This
    finite prefix ends before the arbitrary outer continuation is evaluated. -/
theorem client_result_prefix (world : CodeWorld) (context : Context) (stack : List Frame)
    (payload : Value) (payloadBound : context.env.lookup 12 = some payload) :
    runLocal 6 world {
      control := .ret [.atom "ok"]
      context := context
      stack := .seq context (.tuple [.lit (.atom "ok"), .var 12]) :: stack } =
      .exhausted { control := .ret [.tuple [.atom "ok", payload]], context, stack } := by
  simp [runLocal, run, stepLocal, startCollect, finishCollect, nextControl, payloadBound]

end Erlean.Examples.Protocol
