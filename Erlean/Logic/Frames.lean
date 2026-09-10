import Erlean.Semantics.Machine
import Erlean.Logic.Segment

namespace Erlean.Logic

open Core Semantics

/-- Add an outer continuation without changing the current control or context. -/
def appendStack (state : LocalState) (suffix : List Frame) : LocalState :=
  { state with stack := state.stack ++ suffix }

private def appendTransition (suffix : List Frame) :
    Transition LocalState Outcome → Transition LocalState Outcome
  | .next state => .next (appendStack state suffix)
  | .halt outcome => .halt outcome

private theorem updateMapEntries_append (state : LocalState) (suffix : List Frame)
    (exact : List Bool) (operands : Values) (entries : FiniteMap.Entries Value) :
    updateMapEntries (appendStack state suffix) exact operands entries =
      appendTransition suffix (updateMapEntries state exact operands entries) := by
  induction exact generalizing operands entries with
  | nil => cases operands <;> rfl
  | cons flag rest ih =>
      cases operands with
      | nil => rfl
      | cons key operands =>
          cases operands with
          | nil => rfl
          | cons value operands =>
              simp only [updateMapEntries]
              repeat' first
                | exact ih _ _
                | rfl
                | split <;> try simp_all only []

private theorem finishMap_append (state : LocalState) (suffix : List Frame)
    (exact : List Bool) (operands : Values) :
    finishMap (appendStack state suffix) exact operands =
      appendTransition suffix (finishMap state exact operands) := by
  unfold finishMap
  repeat' first
    | exact updateMapEntries_append state suffix _ _ _
    | rfl
    | split <;> try simp_all only []

private theorem withMap_append (state : LocalState) (suffix : List Frame) (value : Value)
    (body lifted : FiniteMap.Entries Value → Transition LocalState Outcome)
    (commutes : ∀ entries, lifted entries = appendTransition suffix (body entries)) :
    withMap (appendStack state suffix) value lifted =
      appendTransition suffix (withMap state value body) := by
  unfold withMap
  repeat' first
    | exact commutes _
    | rfl
    | split <;> try simp_all only []

private theorem withMapKey_append (suffix : List Frame) (key : Value)
    (body lifted : MapKey → Transition LocalState Outcome)
    (commutes : ∀ mapKey, lifted mapKey = appendTransition suffix (body mapKey)) :
    withMapKey key lifted = appendTransition suffix (withMapKey key body) := by
  unfold withMapKey
  split
  · exact commutes _
  · rfl

private theorem mapBuiltin_append (state : LocalState) (suffix : List Frame)
    (name : String) (args : Values) :
    mapBuiltin (appendStack state suffix) name args =
      appendTransition suffix (mapBuiltin state name args) := by
  unfold mapBuiltin
  repeat' first
    | rfl
    | with_reducible apply withMap_append state suffix
      intro entries
    | with_reducible apply withMapKey_append suffix
      intro key
    | split <;> try simp_all only []

private theorem extendedBuiltin_append (state : LocalState) (suffix : List Frame)
    (name : String) (args : Values) :
    extendedBuiltin (appendStack state suffix) name args =
      appendTransition suffix (extendedBuiltin state name args) := by
  unfold extendedBuiltin
  repeat' first
    | rfl
    | split <;> try simp_all only []

private theorem builtin_append (state : LocalState) (suffix : List Frame)
    (name : String) (args : Values) :
    builtin (appendStack state suffix) name args =
      appendTransition suffix (builtin state name args) := by
  unfold builtin
  repeat' first
    | rfl
    | with_reducible exact mapBuiltin_append state suffix _ _
    | with_reducible exact extendedBuiltin_append state suffix _ _
    | with_reducible apply withMap_append state suffix
      intro entries
    | split <;> try simp_all only []

private theorem invoke_append (world : CodeWorld) (state : LocalState)
    (suffix : List Frame) (moduleName name : String) (args : Values) (external : Bool) :
    invoke world (appendStack state suffix) moduleName name args external =
      appendTransition suffix (invoke world state moduleName name args external) := by
  unfold invoke
  repeat' first
    | rfl
    | exact builtin_append state suffix _ _
    | exact mapBuiltin_append state suffix _ _
    | split <;> try simp_all only []

private theorem applyClosure_append (world : CodeWorld) (state : LocalState)
    (suffix : List Frame) (moduleName : String) (index : Nat) (captured : Env)
    (group : List (VarId × Nat)) (args : Values) :
    applyClosure world (appendStack state suffix) moduleName index captured group args =
      appendTransition suffix (applyClosure world state moduleName index captured group args) := by
  unfold applyClosure
  repeat' first
    | rfl
    | split <;> try simp_all only []

private theorem finishCollect_append (world : CodeWorld) (state : LocalState)
    (suffix : List Frame) (action : Collect) (values : Values) :
    finishCollect world (appendStack state suffix) action values =
      appendTransition suffix (finishCollect world state action values) := by
  unfold finishCollect
  repeat' first
    | rfl
    | exact finishMap_append state suffix _ _
    | exact invoke_append world state suffix _ _ _ _
    | exact applyClosure_append world state suffix _ _ _ _ _
    | split <;> try simp_all only []

private theorem startCollect_append (world : CodeWorld) (state : LocalState)
    (suffix : List Frame) (action : Collect) (expressions : List Expr) :
    startCollect world (appendStack state suffix) action expressions =
      appendTransition suffix (startCollect world state action expressions) := by
  cases expressions with
  | nil => exact finishCollect_append world state suffix action []
  | cons first rest => rfl

private theorem eval_append (world : CodeWorld) (expression : Expr) (context : Context)
    (stack suffix : List Frame) :
    stepLocal world ⟨.eval expression, context, stack ++ suffix⟩ =
      appendTransition suffix (stepLocal world ⟨.eval expression, context, stack⟩) := by
  cases expression <;> simp only [stepLocal]
  all_goals repeat' first
    | rfl
    | (rw [← startCollect_append]; rfl)
    | split <;> try simp_all only []

private theorem select_append (world : CodeWorld) (values : Values)
    (clauses : List Clause) (context : Context) (stack suffix : List Frame) :
    stepLocal world ⟨.select values clauses, context, stack ++ suffix⟩ =
      appendTransition suffix (stepLocal world ⟨.select values clauses, context, stack⟩) := by
  simp only [stepLocal]
  repeat' first
    | rfl
    | split <;> try simp_all only []

private theorem ret_cons_append (world : CodeWorld) (values : Values)
    (context : Context) (frame : Frame) (stack suffix : List Frame) :
    stepLocal world ⟨.ret values, context, (frame :: stack) ++ suffix⟩ =
      appendTransition suffix (stepLocal world ⟨.ret values, context, frame :: stack⟩) := by
  cases frame <;> simp only [stepLocal, List.cons_append]
  all_goals repeat' first
    | rfl
    | (rw [← finishCollect_append]; rfl)
    | split <;> try simp_all only []

private theorem raise_cons_append (world : CodeWorld) (exception : Exception)
    (context : Context) (frame : Frame) (stack suffix : List Frame) :
    stepLocal world ⟨.raise exception, context, (frame :: stack) ++ suffix⟩ =
      appendTransition suffix (stepLocal world ⟨.raise exception, context, frame :: stack⟩) := by
  cases frame <;> simp only [stepLocal, List.cons_append]
  all_goals repeat' first
    | rfl
    | split <;> try simp_all only []

/-- Every actual next transition preserves an appended outer continuation.
    The premise excludes empty-stack return and raise halts. An appended frame
    may handle either boundary, so there is no corresponding arbitrary-halt law.
    The code world is the same on both sides. -/
theorem stepLocal_next_appendStack (world : CodeWorld) (state next : LocalState)
    (suffix : List Frame) (advanced : stepLocal world state = .next next) :
    stepLocal world (appendStack state suffix) = .next (appendStack next suffix) := by
  rcases state with ⟨control, context, stack⟩
  cases control with
  | eval expression =>
      change stepLocal world ⟨.eval expression, context, stack ++ suffix⟩ = _
      rw [eval_append, advanced]
      rfl
  | select values clauses =>
      change stepLocal world ⟨.select values clauses, context, stack ++ suffix⟩ = _
      rw [select_append, advanced]
      rfl
  | ret values =>
      cases stack with
      | nil => simp [stepLocal] at advanced
      | cons frame rest =>
          change stepLocal world ⟨.ret values, context, (frame :: rest) ++ suffix⟩ = _
          rw [ret_cons_append, advanced]
          rfl
  | raise exception =>
      cases stack with
      | nil => simp [stepLocal] at advanced
      | cons frame rest =>
          change stepLocal world ⟨.raise exception, context, (frame :: rest) ++ suffix⟩ = _
          rw [raise_cons_append, advanced]
          rfl
  | runtime name args => simp [stepLocal, unsupported] at advanced

/-- Lift a finite checked prefix, stopping before its boundary transition.
    No return, exception, or runtime behavior of that boundary is assumed. -/
theorem reachesBoundary_appendStack (world : CodeWorld) (state boundary : LocalState)
    (suffix : List Frame) (segment : ReachesBoundary (stepLocal world) state boundary) :
    ReachesBoundary (stepLocal world) (appendStack state suffix) (appendStack boundary suffix) := by
  obtain ⟨fuel, reached⟩ := segment
  refine ⟨fuel, ?_⟩
  induction fuel generalizing state with
  | zero =>
      have equal : state = boundary := by simpa [run] using reached
      subst state
      rfl
  | succ fuel ih =>
      cases advanced : stepLocal world state with
      | halt outcome => simp [run, advanced] at reached
      | next middle =>
          have remaining : run (stepLocal world) fuel middle = .exhausted boundary := by
            simpa [run, advanced] using reached
          rw [run, stepLocal_next_appendStack world state middle suffix advanced]
          exact ih middle remaining

end Erlean.Logic
