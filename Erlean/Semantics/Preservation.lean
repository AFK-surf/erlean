import Erlean.Core.Environment
import Erlean.Semantics.Machine

namespace Erlean.Semantics

open Core

/-!
Lexical preservation prerequisites and checked transition rules.

The invariant uses a covered static scope. Requiring the scope checker to accept
all runtime environment keys would incorrectly make binder freshness depend on
irrelevant saved bindings. These predicates concern variable availability only;
they do not establish arity correctness, closure validity, or absence of faults.

The final theorem composes lexical transition rules, checked named/closure entry,
and recursive-group key preservation. Runtime requests are terminal for this
local-step theorem; actor-driver transitions require a separate argument.
-/

def ScopedExpr (context : Context) (expression : Expr) : Prop :=
  ∃ scope, Env.Covers context.env scope ∧ WellScoped scope expression

def ScopedExpressions (context : Context) (expressions : List Expr) : Prop :=
  ∃ scope, Env.Covers context.env scope ∧ scopeCheckList scope expressions = true

def ScopedClauses (context : Context) (clauses : List Clause) : Prop :=
  ∃ scope, Env.Covers context.env scope ∧ scopeCheckClauses scope clauses = true

def ScopedBinding (context : Context) (binders : List VarId) (body : Expr) : Prop :=
  ∃ scope, Env.Covers context.env scope ∧ WellScoped (binders ++ scope) body

def FrameScoped : Frame → Prop
  | .collect _ context _ rest => ScopedExpressions context rest
  | .bind context binders body => ScopedBinding context binders body
  | .seq context body => ScopedExpr context body
  | .select context clauses => ScopedClauses context clauses
  | .guard context matched _ body rest =>
      ScopedExpr { context with env := matched ++ context.env } body ∧
        ScopedClauses context rest
  | .tryFrame context binders body exceptionBinders handler =>
      ScopedBinding context binders body ∧ ScopedBinding context exceptionBinders handler
  | .catchFrame _ => True

def StackScoped (stack : List Frame) : Prop :=
  ∀ frame ∈ stack, FrameScoped frame

@[simp] theorem stackScoped_cons (frame : Frame) (stack : List Frame) :
    StackScoped (frame :: stack) ↔ FrameScoped frame ∧ StackScoped stack := by
  simp [StackScoped]

def ControlScoped (context : Context) : Control → Prop
  | .eval expression => ScopedExpr context expression
  | .select _ clauses => ScopedClauses context clauses
  | .ret _ | .raise _ | .runtime _ _ => True

structure LexicallyScoped (state : LocalState) : Prop where
  control : ControlScoped state.context state.control
  frames : StackScoped state.stack

/-- Value-return, exception, and runtime controls need no expression scope;
    `nextControl` keeps the already checked continuation unchanged. -/
theorem nextControl_preserves (state after : LocalState) (control : Control)
    (frames : StackScoped state.stack) (transition : nextControl state control = .next after)
    (controlScopedProof : ControlScoped state.context control) : LexicallyScoped after := by
  have stateEq : ({ state with control := control } : LocalState) = after :=
    Transition.next.inj transition
  rw [← stateEq]
  exact ⟨controlScopedProof, frames⟩

theorem scoped_variable_lookup (context : Context) (id : VarId)
    (h : ScopedExpr context (.var id)) : ∃ value, context.env.lookup id = some value := by
  obtain ⟨scope, covered, checked⟩ := h
  exact covered id ((wellScoped_var_iff scope id).mp checked)

theorem scoped_binding_extend (context : Context) (binders : List VarId)
    (body : Expr) (values : Values) (h : ScopedBinding context binders body)
    (arity : binders.length = values.length) :
    ScopedExpr { context with env := binders.zip values ++ context.env } body := by
  obtain ⟨scope, covered, checked⟩ := h
  exact ⟨binders ++ scope,
    Env.covers_append _ _ _ _ (Env.covers_zip binders values arity) covered, checked⟩

theorem scoped_expressions_cons (context : Context) (first : Expr) (rest : List Expr)
    (h : ScopedExpressions context (first :: rest)) :
    ScopedExpr context first ∧ ScopedExpressions context rest := by
  obtain ⟨scope, covered, checked⟩ := h
  have parts : scopeCheck scope first = true ∧ scopeCheckList scope rest = true := by
    simpa [scopeCheckList] using checked
  exact ⟨⟨scope, covered, parts.1⟩, ⟨scope, covered, parts.2⟩⟩

/-- A nonempty operand collection preserves the saved-context invariant. -/
theorem startCollect_nonempty_preserves (world : CodeWorld) (state after : LocalState)
    (action : Collect) (first : Expr) (rest : List Expr)
    (expressions : ScopedExpressions state.context (first :: rest))
    (frames : StackScoped state.stack)
    (transition : startCollect world state action (first :: rest) = .next after) :
    LexicallyScoped after := by
  have parts := scoped_expressions_cons state.context first rest expressions
  have stateEq : ({
      state with
      control := .eval first
      stack := .collect action state.context [] rest :: state.stack } : LocalState) = after := by
    exact Transition.next.inj transition
  rw [← stateEq]
  exact ⟨parts.1, (stackScoped_cons _ _).mpr ⟨parts.2, frames⟩⟩

theorem step_let_preserves (world : CodeWorld) (context : Context) (stack : List Frame)
    (binders : List VarId) (argument body : Expr) (after : LocalState)
    (before : LexicallyScoped ⟨.eval (.letE binders argument body), context, stack⟩)
    (transition : stepLocal world ⟨.eval (.letE binders argument body), context, stack⟩ =
      .next after) : LexicallyScoped after := by
  obtain ⟨scope, covered, checked⟩ := before.control
  have parts := (wellScoped_let_iff scope binders argument body).mp checked
  have stateEq : ({
      control := .eval argument
      context := context
      stack := .bind context binders body :: stack } : LocalState) = after := by
    exact Transition.next.inj transition
  rw [← stateEq]
  exact ⟨⟨scope, covered, parts.1.2⟩,
    (stackScoped_cons _ _).mpr ⟨⟨scope, covered, parts.2⟩, before.frames⟩⟩

theorem step_seq_preserves (world : CodeWorld) (context : Context) (stack : List Frame)
    (first second : Expr) (after : LocalState)
    (before : LexicallyScoped ⟨.eval (.seq first second), context, stack⟩)
    (transition : stepLocal world ⟨.eval (.seq first second), context, stack⟩ = .next after) :
    LexicallyScoped after := by
  obtain ⟨scope, covered, checked⟩ := before.control
  have parts := (wellScoped_seq_iff scope first second).mp checked
  have stateEq : ({
      control := .eval first
      context := context
      stack := .seq context second :: stack } : LocalState) = after := by
    exact Transition.next.inj transition
  rw [← stateEq]
  exact ⟨⟨scope, covered, parts.1⟩,
    (stackScoped_cons _ _).mpr ⟨⟨scope, covered, parts.2⟩, before.frames⟩⟩

theorem step_case_preserves (world : CodeWorld) (context : Context) (stack : List Frame)
    (argument : Expr) (clauses : List Clause) (after : LocalState)
    (before : LexicallyScoped ⟨.eval (.caseE argument clauses), context, stack⟩)
    (transition : stepLocal world ⟨.eval (.caseE argument clauses), context, stack⟩ =
      .next after) : LexicallyScoped after := by
  obtain ⟨scope, covered, checked⟩ := before.control
  have parts : WellScoped scope argument ∧ scopeCheckClauses scope clauses = true := by
    simpa [WellScoped, scopeCheck] using checked
  have stateEq : ({
      control := .eval argument
      context := context
      stack := .select context clauses :: stack } : LocalState) = after := by
    exact Transition.next.inj transition
  rw [← stateEq]
  exact ⟨⟨scope, covered, parts.1⟩,
    (stackScoped_cons _ _).mpr ⟨⟨scope, covered, parts.2⟩, before.frames⟩⟩

theorem step_bind_return_preserves (world : CodeWorld) (context current : Context)
    (stack : List Frame) (binders : List VarId) (body : Expr) (values : Values)
    (after : LocalState)
    (before : LexicallyScoped ⟨.ret values, current, .bind context binders body :: stack⟩)
    (arity : binders.length = values.length)
    (transition : stepLocal world ⟨.ret values, current, .bind context binders body :: stack⟩ =
      .next after) : LexicallyScoped after := by
  have frames := (stackScoped_cons _ _).mp before.frames
  have stateEq : ({
      control := .eval body
      context := { context with env := binders.zip values ++ context.env }
      stack := stack } : LocalState) = after := by
    apply @Transition.next.inj LocalState Outcome
    simpa [stepLocal, arity] using transition
  rw [← stateEq]
  exact ⟨scoped_binding_extend context binders body values frames.1 arity, frames.2⟩

theorem step_seq_return_preserves (world : CodeWorld) (context current : Context)
    (stack : List Frame) (body : Expr) (values : Values) (after : LocalState)
    (before : LexicallyScoped ⟨.ret values, current, .seq context body :: stack⟩)
    (transition : stepLocal world ⟨.ret values, current, .seq context body :: stack⟩ =
      .next after) : LexicallyScoped after := by
  have frames := (stackScoped_cons _ _).mp before.frames
  have stateEq : ({
      control := .eval body
      context := context
      stack := stack } : LocalState) =
      after := by exact Transition.next.inj transition
  rw [← stateEq]
  exact ⟨frames.1, frames.2⟩

theorem step_select_return_preserves (world : CodeWorld) (context current : Context)
    (stack : List Frame) (clauses : List Clause) (values : Values) (after : LocalState)
    (before : LexicallyScoped ⟨.ret values, current, .select context clauses :: stack⟩)
    (transition : stepLocal world ⟨.ret values, current, .select context clauses :: stack⟩ =
      .next after) : LexicallyScoped after := by
  have frames := (stackScoped_cons _ _).mp before.frames
  have stateEq : ({
      control := .select values clauses
      context := context
      stack := stack } : LocalState) = after := by exact Transition.next.inj transition
  rw [← stateEq]
  exact ⟨frames.1, frames.2⟩

theorem step_guard_return_preserves (world : CodeWorld) (context current : Context)
    (stack : List Frame) (matched : Env) (scrutinee values : Values) (body : Expr)
    (rest : List Clause) (after : LocalState)
    (before : LexicallyScoped
      ⟨.ret values, current, .guard context matched scrutinee body rest :: stack⟩)
    (transition : stepLocal world
      ⟨.ret values, current, .guard context matched scrutinee body rest :: stack⟩ = .next after) :
    LexicallyScoped after := by
  have frames := (stackScoped_cons _ _).mp before.frames
  have guarded : ScopedExpr { context with env := matched ++ context.env } body ∧
      ScopedClauses context rest := frames.1
  by_cases succeeds : (values == [.atom "true"]) = true
  · have stateEq : ({
      control := .eval body
      context := { context with env := matched ++ context.env }
      stack := stack } : LocalState) = after := by
      apply @Transition.next.inj LocalState Outcome
      simpa [stepLocal, succeeds] using transition
    rw [← stateEq]
    exact ⟨guarded.1, frames.2⟩
  · have stateEq : ({
      control := .select scrutinee rest
      context := context
      stack := stack } : LocalState) = after := by
      apply @Transition.next.inj LocalState Outcome
      simpa [stepLocal, succeeds] using transition
    rw [← stateEq]
    exact ⟨guarded.2, frames.2⟩

theorem step_try_return_preserves (world : CodeWorld) (context current : Context)
    (stack : List Frame) (binders exceptionBinders : List VarId) (body handler : Expr)
    (values : Values) (after : LocalState)
    (before : LexicallyScoped
      ⟨.ret values, current, .tryFrame context binders body exceptionBinders handler :: stack⟩)
    (arity : binders.length = values.length)
    (transition : stepLocal world
      ⟨.ret values, current, .tryFrame context binders body exceptionBinders handler :: stack⟩ =
      .next after) : LexicallyScoped after := by
  have frames := (stackScoped_cons _ _).mp before.frames
  have handlers : ScopedBinding context binders body ∧
      ScopedBinding context exceptionBinders handler := frames.1
  have stateEq : ({
      control := .eval body
      context := { context with env := binders.zip values ++ context.env }
      stack := stack } : LocalState) = after := by
    apply @Transition.next.inj LocalState Outcome
    simpa [stepLocal, arity] using transition
  rw [← stateEq]
  exact ⟨scoped_binding_extend context binders body values handlers.1 arity, frames.2⟩

theorem step_catch_return_preserves (world : CodeWorld) (context current : Context)
    (stack : List Frame) (values : Values) (after : LocalState)
    (before : LexicallyScoped ⟨.ret values, current, .catchFrame context :: stack⟩)
    (arity : values.length = 1)
    (transition : stepLocal world ⟨.ret values, current, .catchFrame context :: stack⟩ =
      .next after) : LexicallyScoped after := by
  have frames := (stackScoped_cons _ _).mp before.frames
  have stateEq : ({
      control := .ret values
      context := context
      stack := stack } : LocalState) =
      after := by
    apply @Transition.next.inj LocalState Outcome
    simpa [stepLocal, arity] using transition
  rw [← stateEq]
  exact ⟨trivial, frames.2⟩

theorem step_try_preserves (world : CodeWorld) (context : Context) (stack : List Frame)
    (argument : Expr) (binders : List VarId) (body : Expr)
    (exceptionBinders : List VarId) (handler : Expr) (after : LocalState)
    (before : LexicallyScoped
      ⟨.eval (.tryE argument binders body exceptionBinders handler), context, stack⟩)
    (transition : stepLocal world
      ⟨.eval (.tryE argument binders body exceptionBinders handler), context, stack⟩ = .next after) :
    LexicallyScoped after := by
  obtain ⟨scope, covered, checked⟩ := before.control
  have parts :
      ((((freshBinders scope binders = true ∧ freshBinders scope exceptionBinders = true) ∧
        (exceptionBinders.length = 2 ∨ exceptionBinders.length = 3)) ∧
        WellScoped scope argument) ∧ WellScoped (binders ++ scope) body) ∧
        WellScoped (exceptionBinders ++ scope) handler := by
    simpa [WellScoped, scopeCheck] using checked
  have validArity := parts.1.1.1.2
  have stateEq : ({
      control := .eval argument
      context := context
      stack := .tryFrame context binders body exceptionBinders handler :: stack } : LocalState) =
      after := by
    apply @Transition.next.inj LocalState Outcome
    simpa [stepLocal, validArity] using transition
  rw [← stateEq]
  exact ⟨⟨scope, covered, parts.1.1.2⟩,
    (stackScoped_cons _ _).mpr
      ⟨⟨⟨scope, covered, parts.1.2⟩, ⟨scope, covered, parts.2⟩⟩, before.frames⟩⟩

theorem step_catch_preserves (world : CodeWorld) (context : Context) (stack : List Frame)
    (body : Expr) (after : LocalState)
    (before : LexicallyScoped ⟨.eval (.catchE body), context, stack⟩)
    (transition : stepLocal world ⟨.eval (.catchE body), context, stack⟩ = .next after) :
    LexicallyScoped after := by
  obtain ⟨scope, covered, checked⟩ := before.control
  have bodyChecked : WellScoped scope body := by
    simpa [WellScoped, scopeCheck] using checked
  have stateEq : ({
      control := .eval body
      context := context
      stack := .catchFrame context :: stack } : LocalState) = after := by
    exact Transition.next.inj transition
  rw [← stateEq]
  exact ⟨⟨scope, covered, bodyChecked⟩, (stackScoped_cons _ _).mpr ⟨trivial, before.frames⟩⟩

/-- Successful matching covers every guard/body binder and preserves saved clauses. -/
theorem matched_clause_scoped (context : Context) (patterns : List Pattern)
    (guard body : Expr) (rest : List Clause) (values : Values) (matched : Env)
    (clauses : ScopedClauses context ((patterns, guard, body) :: rest))
    (matching : matchPatterns patterns values = some matched) :
    ScopedExpr { context with env := matched ++ context.env } guard ∧
      FrameScoped (.guard context matched values body rest) := by
  obtain ⟨scope, covered, checked⟩ := clauses
  have parts :
      ((freshBinders scope (patterns.flatMap Pattern.binders) = true ∧
        WellScoped (patterns.flatMap Pattern.binders ++ scope) guard) ∧
        WellScoped (patterns.flatMap Pattern.binders ++ scope) body) ∧
        scopeCheckClauses scope rest = true := by
    simpa [scopeCheckClauses, WellScoped] using checked
  have extended := matchPatterns_extend_coverage patterns values matched context.env scope matching covered
  exact ⟨⟨patterns.flatMap Pattern.binders ++ scope, extended, parts.1.1.2⟩,
    ⟨⟨patterns.flatMap Pattern.binders ++ scope, extended, parts.1.2⟩,
      ⟨scope, covered, parts.2⟩⟩⟩

theorem step_matched_clause_preserves (world : CodeWorld) (context : Context)
    (stack : List Frame) (patterns : List Pattern) (guard body : Expr)
    (rest : List Clause) (values : Values) (matched : Env) (after : LocalState)
    (before : LexicallyScoped ⟨.select values ((patterns, guard, body) :: rest), context, stack⟩)
    (allowed : patternsObservationAllowed patterns values = true)
    (matching : matchPatterns patterns values = some matched)
    (transition : stepLocal world
      ⟨.select values ((patterns, guard, body) :: rest), context, stack⟩ = .next after) :
    LexicallyScoped after := by
  have parts := matched_clause_scoped context patterns guard body rest values matched
    before.control matching
  have stateEq : ({
      control := .eval guard
      context := { context with env := matched ++ context.env }
      stack := .guard context matched values body rest :: stack } : LocalState) = after := by
    apply @Transition.next.inj LocalState Outcome
    simpa [stepLocal, allowed, matching] using transition
  rw [← stateEq]
  exact ⟨parts.1, (stackScoped_cons _ _).mpr ⟨parts.2, before.frames⟩⟩

theorem step_unmatched_clause_preserves (world : CodeWorld) (context : Context)
    (stack : List Frame) (patterns : List Pattern) (guard body : Expr)
    (rest : List Clause) (values : Values) (after : LocalState)
    (before : LexicallyScoped ⟨.select values ((patterns, guard, body) :: rest), context, stack⟩)
    (allowed : patternsObservationAllowed patterns values = true)
    (matching : matchPatterns patterns values = none)
    (transition : stepLocal world
      ⟨.select values ((patterns, guard, body) :: rest), context, stack⟩ = .next after) :
    LexicallyScoped after := by
  obtain ⟨scope, covered, checked⟩ := before.control
  have restChecked : scopeCheckClauses scope rest = true := by
    simp only [scopeCheckClauses, Bool.and_eq_true] at checked
    exact checked.2
  have stateEq : ({
      control := .select values rest
      context := context
      stack := stack } : LocalState) = after := by
    apply @Transition.next.inj LocalState Outcome
    simpa [stepLocal, nextControl, allowed, matching] using transition
  rw [← stateEq]
  exact ⟨⟨scope, covered, restChecked⟩, before.frames⟩

def CheckedWorld (world : CodeWorld) : Prop :=
  ∀ mod ∈ world, Module.check mod = true

/-- A checked module contributes scope-checked named definitions. -/
theorem checked_function_scope (world : CodeWorld) (moduleName name : String)
    (arity : Nat) (fn : FunctionDef) (checked : CheckedWorld world)
    (found : lookupFunction world moduleName name arity = some fn) :
    WellScoped fn.params fn.body ∧ fn.params.length = arity := by
  cases hm : world.find? (fun m => m.name == moduleName) with
  | none => simp [lookupFunction, hm] at found
  | some mod =>
      have hf : mod.functions.find? (fun f => f.name == name && f.params.length == arity) =
          some fn := by simpa [lookupFunction, hm] using found
      have moduleChecked := checked mod (List.mem_of_find?_eq_some hm)
      have functionChecks : mod.functions.all FunctionDef.scopeCheck = true := by
        simp only [Module.check, Bool.and_eq_true] at moduleChecked
        exact moduleChecked.1.1.2
      have functionChecked := List.all_eq_true.mp functionChecks fn (List.mem_of_find?_eq_some hf)
      have bodyChecked : WellScoped fn.params fn.body := by
        exact ((Bool.and_eq_true _ _).mp functionChecked).2
      have signature : fn.name = name ∧ fn.params.length = arity := by
        simpa using List.find?_some hf
      exact ⟨bodyChecked, signature.2⟩

/-- Named-call entry preserves lexical scope under an actual checked-world
    premise. This lemma checks the destination of invocation, not its BIF branch. -/
theorem checked_function_entry_scoped (world : CodeWorld) (moduleName name : String)
    (args : Values) (fn : FunctionDef) (stack : List Frame)
    (checked : CheckedWorld world)
    (found : lookupFunction world moduleName name args.length = some fn)
    (frames : StackScoped stack) :
    LexicallyScoped ⟨.eval fn.body, ⟨moduleName, fn.params.zip args⟩, stack⟩ := by
  have facts := checked_function_scope world moduleName name args.length fn checked found
  exact ⟨⟨fn.params, Env.covers_zip fn.params args facts.2, facts.1⟩, frames⟩

theorem env_covers_keys (env : Env) : Env.Covers env (env.map Prod.fst) := by
  rw [Env.covers_iff_mem_keys]
  intro id member
  exact member

theorem recursiveEnv_keys (moduleName : String) (captured : Env)
    (group : List (VarId × Nat)) :
    (recursiveEnv moduleName captured group).map Prod.fst = group.map Prod.fst := by
  simp [recursiveEnv, List.map_map]

theorem checked_closure_scope (world : CodeWorld) (mod : Core.Module)
    (index : Nat) (defn : ClosureDef) (checked : CheckedWorld world)
    (member : mod ∈ world) (found : mod.closureCode[index]? = some defn) :
    WellScoped (defn.params ++ defn.recursiveBindings.map Prod.fst ++ defn.outerScope)
      defn.body := by
  have moduleChecked := checked mod member
  have closureChecks : mod.closureCode.all (ClosureDef.check mod.closureCode) = true := by
    exact ((Bool.and_eq_true _ _).mp moduleChecked).2
  have closureChecked := List.all_eq_true.mp closureChecks defn (List.mem_of_getElem? found)
  simp only [ClosureDef.check, Bool.and_eq_true] at closureChecked
  exact closureChecked.1.2

/-- Closure entry uses the checks already performed by `applyClosure`: exact
    capture keys, recursive descriptor agreement, and parameter arity. -/
theorem checked_closure_entry_scoped (world : CodeWorld) (mod : Core.Module)
    (moduleName : String) (index : Nat) (defn : ClosureDef) (captured : Env)
    (group : List (VarId × Nat)) (args : Values) (stack : List Frame)
    (checked : CheckedWorld world) (member : mod ∈ world)
    (found : mod.closureCode[index]? = some defn)
    (captureKeys : captured.map Prod.fst = defn.outerScope)
    (descriptor : group = defn.recursiveBindings)
    (arity : defn.params.length = args.length) (frames : StackScoped stack) :
    LexicallyScoped
      ⟨.eval defn.body,
       ⟨moduleName, defn.params.zip args ++ recursiveEnv moduleName captured group ++ captured⟩,
       stack⟩ := by
  have capturedCovered : Env.Covers captured defn.outerScope := by
    rw [← captureKeys]
    exact env_covers_keys captured
  have recursiveCovered : Env.Covers (recursiveEnv moduleName captured group)
      (defn.recursiveBindings.map Prod.fst) := by
    rw [← descriptor, ← recursiveEnv_keys moduleName captured group]
    exact env_covers_keys (recursiveEnv moduleName captured group)
  have covered := Env.covers_append _ _ _ _ (Env.covers_zip defn.params args arity)
    (Env.covers_append _ _ _ _ recursiveCovered capturedCovered)
  refine ⟨?_, frames⟩
  refine ⟨defn.params ++ defn.recursiveBindings.map Prod.fst ++ defn.outerScope, ?_,
    checked_closure_scope world mod index defn checked member found⟩
  simpa only [List.append_assoc] using covered

/-- Mapping closure creation over a recursive group preserves exactly its keys. -/
theorem closure_mapM_keys (create : Nat → Except Fault Value)
    (bindings : List (VarId × Nat)) (env : Env)
    (success : bindings.mapM (fun (id, index) => (create index).map (id, ·)) = .ok env) :
    env.map Prod.fst = bindings.map Prod.fst := by
  induction bindings generalizing env with
  | nil =>
      have empty : env = [] := by simpa [Pure.pure, Except.pure] using success.symm
      subst env
      rfl
  | cons entry rest ih =>
      rcases entry with ⟨id, index⟩
      rw [List.mapM_cons] at success
      dsimp only at success
      cases hc : create index with
      | error fault => simp [hc, Bind.bind, Except.bind, Except.map] at success
      | ok value =>
          rw [hc] at success
          cases hr : rest.mapM (fun (id, index) => (create index).map (id, ·)) with
          | error fault =>
              rw [hr] at success
              simp [Bind.bind, Except.bind, Except.map] at success
          | ok restEnv =>
              rw [hr] at success
              have eq : (id, value) :: restEnv = env := by
                simpa [Pure.pure, Except.pure, Bind.bind, Except.bind,
                  Functor.map, Except.map] using success
              subst env
              simp only [List.map_cons]
              exact congrArg (List.cons id) (ih restEnv hr)

theorem step_letrec_preserves (world : CodeWorld) (context : Context)
    (stack : List Frame) (bindings : List (VarId × Nat)) (body : Expr)
    (env : Env) (after : LocalState)
    (before : LexicallyScoped ⟨.eval (.letrec bindings body), context, stack⟩)
    (created : bindings.mapM (fun (id, index) =>
      (makeClosureValue world context index).map (id, ·)) = .ok env)
    (transition : stepLocal world ⟨.eval (.letrec bindings body), context, stack⟩ = .next after) :
    LexicallyScoped after := by
  obtain ⟨scope, covered, checked⟩ := before.control
  have bodyChecked : WellScoped (bindings.map Prod.fst ++ scope) body := by
    simp only [WellScoped, scopeCheck, Bool.and_eq_true] at checked
    exact checked.2
  have keys := closure_mapM_keys (makeClosureValue world context) bindings env created
  have newCovered : Env.Covers env (bindings.map Prod.fst) := by
    rw [← keys]
    exact env_covers_keys env
  have stateEq : ({
      control := .eval body
      context := { context with env := env ++ context.env }
      stack := stack } : LocalState) =
      after := by
    apply @Transition.next.inj LocalState Outcome
    simpa [stepLocal, created] using transition
  rw [← stateEq]
  exact ⟨⟨_, Env.covers_append _ _ _ _ newCovered covered, bodyChecked⟩, before.frames⟩

theorem builtin_preserves (state after : LocalState) (name : String) (args : Values)
    (frames : StackScoped state.stack)
    (transition : builtin state name args = .next after) : LexicallyScoped after := by
  unfold builtin at transition
  repeat' split at transition
  all_goals simp only [nextControl, raiseError, unsupported] at transition
  all_goals cases transition
  all_goals exact ⟨trivial, frames⟩

theorem invoke_preserves (world : CodeWorld) (state after : LocalState)
    (moduleName name : String) (args : Values) (external : Bool)
    (checked : CheckedWorld world) (frames : StackScoped state.stack)
    (transition : invoke world state moduleName name args external = .next after) :
    LexicallyScoped after := by
  unfold invoke at transition
  split at transition
  · exact builtin_preserves state after name args frames transition
  · cases hm : world.find? (fun m => m.name == moduleName) with
    | none => simp [hm, unsupported] at transition
    | some mod =>
        simp only [hm] at transition
        split at transition
        · exact nextControl_preserves state after _ frames transition trivial
        · cases hf : lookupFunction world moduleName name args.length with
          | none =>
              simp only [hf] at transition
              exact nextControl_preserves state after _ frames transition trivial
          | some fn =>
              simp only [hf] at transition
              have stateEq := Transition.next.inj transition
              rw [← stateEq]
              exact checked_function_entry_scoped world moduleName name args fn state.stack
                checked hf frames

theorem applyClosure_preserves (world : CodeWorld) (state after : LocalState)
    (moduleName : String) (index : Nat) (captured : Env) (group : List (VarId × Nat))
    (args : Values) (checked : CheckedWorld world) (frames : StackScoped state.stack)
    (transition : applyClosure world state moduleName index captured group args = .next after) :
    LexicallyScoped after := by
  unfold applyClosure at transition
  cases hm : world.find? (fun m => m.name == moduleName) with
  | none => simp [hm, unsupported] at transition
  | some mod =>
      simp only [hm] at transition
      cases hd : mod.closureCode[index]? with
      | none => simp [hd, invalid] at transition
      | some defn =>
          simp only [hd] at transition
          split at transition
          · simp [invalid] at transition
          · rename_i descriptorChecks
            have descriptors : defn.recursiveBindings = group ∧
                captured.map Prod.fst = defn.outerScope := by
              simpa using descriptorChecks
            split at transition
            · exact nextControl_preserves state after _ frames transition trivial
            · rename_i arityCheck
              have arity : defn.params.length = args.length := by simpa using arityCheck
              have stateEq := Transition.next.inj transition
              rw [← stateEq]
              exact checked_closure_entry_scoped world mod moduleName index defn captured group
                args state.stack checked (List.mem_of_find?_eq_some hm) hd
                descriptors.2 descriptors.1.symm arity frames

theorem finishCollect_preserves (world : CodeWorld) (state after : LocalState)
    (action : Collect) (values : Values) (checked : CheckedWorld world)
    (frames : StackScoped state.stack)
    (transition : finishCollect world state action values = .next after) :
    LexicallyScoped after := by
  unfold finishCollect at transition
  repeat' first
    | exact nextControl_preserves state after _ frames transition trivial
    | exact invoke_preserves world state after _ _ _ _ checked frames transition
    | exact applyClosure_preserves world state after _ _ _ _ _ checked frames transition
    | solve | simp [unsupported, invalid] at transition
    | split at transition

theorem startCollect_preserves (world : CodeWorld) (state after : LocalState)
    (action : Collect) (expressions : List Expr) (checked : CheckedWorld world)
    (expressionScopes : ScopedExpressions state.context expressions)
    (frames : StackScoped state.stack)
    (transition : startCollect world state action expressions = .next after) :
    LexicallyScoped after := by
  cases expressions with
  | nil => exact finishCollect_preserves world state after action [] checked frames transition
  | cons first rest =>
      exact startCollect_nonempty_preserves world state after action first rest
        expressionScopes frames transition

theorem step_eval_preserves (world : CodeWorld) (context : Context) (stack : List Frame)
    (expression : Expr) (after : LocalState) (checked : CheckedWorld world)
    (before : LexicallyScoped ⟨.eval expression, context, stack⟩)
    (transition : stepLocal world ⟨.eval expression, context, stack⟩ = .next after) :
    LexicallyScoped after := by
  cases expression with
  | lit value => exact nextControl_preserves _ after _ before.frames transition trivial
  | var id =>
      obtain ⟨value, lookup⟩ := scoped_variable_lookup context id before.control
      simp only [stepLocal, lookup] at transition
      exact nextControl_preserves _ after _ before.frames transition trivial
  | funRef name arity => exact nextControl_preserves _ after _ before.frames transition trivial
  | makeClosure index =>
      cases hc : makeClosureValue world context index with
      | error fault => simp [stepLocal, hc] at transition
      | ok value =>
          simp only [stepLocal, hc] at transition
          exact nextControl_preserves _ after _ before.frames transition trivial
  | letrec bindings body =>
      cases created : bindings.mapM (fun (id, index) =>
        (makeClosureValue world context index).map (id, ·)) with
      | error fault => simp [stepLocal, created] at transition
      | ok env =>
          exact step_letrec_preserves world context stack bindings body env after
            before created transition
  | letE binders argument body =>
      exact step_let_preserves world context stack binders argument body after before transition
  | seq first second =>
      exact step_seq_preserves world context stack first second after before transition
  | caseE argument clauses =>
      exact step_case_preserves world context stack argument clauses after before transition
  | tryE argument binders body exceptionBinders handler =>
      exact step_try_preserves world context stack argument binders body exceptionBinders handler
        after before transition
  | catchE body => exact step_catch_preserves world context stack body after before transition
  | values elements =>
      obtain ⟨scope, covered, expressionChecked⟩ := before.control
      exact startCollect_preserves world _ after .values elements checked
        ⟨scope, covered, by simpa [WellScoped, scopeCheck] using expressionChecked⟩
        before.frames transition
  | tuple elements =>
      obtain ⟨scope, covered, expressionChecked⟩ := before.control
      exact startCollect_preserves world _ after .tuple elements checked
        ⟨scope, covered, by simpa [WellScoped, scopeCheck] using expressionChecked⟩
        before.frames transition
  | bytes elements =>
      obtain ⟨scope, covered, expressionChecked⟩ := before.control
      exact startCollect_preserves world _ after .bytes elements checked
        ⟨scope, covered, by simpa [WellScoped, scopeCheck] using expressionChecked⟩
        before.frames transition
  | cons head tail =>
      obtain ⟨scope, covered, expressionChecked⟩ := before.control
      exact startCollect_preserves world _ after .cons [head, tail] checked
        ⟨scope, covered, by simpa [WellScoped, scopeCheck, scopeCheckList] using expressionChecked⟩
        before.frames transition
  | call moduleName name args =>
      obtain ⟨scope, covered, expressionChecked⟩ := before.control
      exact startCollect_preserves world _ after .call (moduleName :: name :: args) checked
        ⟨scope, covered, by
          simpa [WellScoped, scopeCheck, scopeCheckList, and_assoc] using expressionChecked⟩
        before.frames transition
  | apply fn args =>
      obtain ⟨scope, covered, expressionChecked⟩ := before.control
      exact startCollect_preserves world _ after .apply (fn :: args) checked
        ⟨scope, covered, by simpa [WellScoped, scopeCheck, scopeCheckList] using expressionChecked⟩
        before.frames transition
  | primop name args =>
      obtain ⟨scope, covered, expressionChecked⟩ := before.control
      exact startCollect_preserves world _ after (.primop name) args checked
        ⟨scope, covered, by simpa [WellScoped, scopeCheck] using expressionChecked⟩
        before.frames transition

theorem step_collect_return_preserves (world : CodeWorld) (context current : Context)
    (stack : List Frame) (action : Collect) (done values : Values) (rest : List Expr)
    (after : LocalState) (checked : CheckedWorld world)
    (before : LexicallyScoped ⟨.ret values, current, .collect action context done rest :: stack⟩)
    (transition : stepLocal world
      ⟨.ret values, current, .collect action context done rest :: stack⟩ = .next after) :
    LexicallyScoped after := by
  have frames := (stackScoped_cons _ _).mp before.frames
  cases values with
  | nil => simp [stepLocal, invalid] at transition
  | cons value remaining =>
      cases remaining with
      | cons other remaining => simp [stepLocal, invalid] at transition
      | nil =>
          cases rest with
          | nil =>
              exact finishCollect_preserves world
                ⟨.ret [value], context, stack⟩ after action (done ++ [value]) checked frames.2 transition
          | cons first rest =>
              have parts := scoped_expressions_cons context first rest frames.1
              have stateEq : ({
                  control := .eval first
                  context := context
                  stack := .collect action context (done ++ [value]) rest :: stack } : LocalState) =
                  after := Transition.next.inj transition
              rw [← stateEq]
              exact ⟨parts.1, (stackScoped_cons _ _).mpr ⟨parts.2, frames.2⟩⟩

theorem step_ret_preserves (world : CodeWorld) (context : Context) (stack : List Frame)
    (values : Values) (after : LocalState) (checked : CheckedWorld world)
    (before : LexicallyScoped ⟨.ret values, context, stack⟩)
    (transition : stepLocal world ⟨.ret values, context, stack⟩ = .next after) :
    LexicallyScoped after := by
  cases stack with
  | nil => simp [stepLocal] at transition
  | cons frame stack =>
      cases frame with
      | collect action saved done rest =>
          exact step_collect_return_preserves world saved context stack action done values rest after
            checked before transition
      | bind saved binders body =>
          by_cases arity : binders.length = values.length
          · exact step_bind_return_preserves world saved context stack binders body values after
              before arity transition
          · simp [stepLocal, arity, invalid] at transition
      | seq saved body =>
          exact step_seq_return_preserves world saved context stack body values after before transition
      | select saved clauses =>
          exact step_select_return_preserves world saved context stack clauses values after before transition
      | guard saved matched scrutinee body rest =>
          exact step_guard_return_preserves world saved context stack matched scrutinee values body rest
            after before transition
      | tryFrame saved binders body exceptionBinders handler =>
          by_cases arity : binders.length = values.length
          · exact step_try_return_preserves world saved context stack binders exceptionBinders body handler
              values after before arity transition
          · simp [stepLocal, arity, invalid] at transition
      | catchFrame saved =>
          by_cases arity : values.length = 1
          · exact step_catch_return_preserves world saved context stack values after before arity transition
          · simp [stepLocal, arity, invalid] at transition

theorem step_select_preserves (world : CodeWorld) (context : Context) (stack : List Frame)
    (values : Values) (clauses : List Clause) (after : LocalState)
    (before : LexicallyScoped ⟨.select values clauses, context, stack⟩)
    (transition : stepLocal world ⟨.select values clauses, context, stack⟩ = .next after) :
    LexicallyScoped after := by
  cases clauses with
  | nil => simp [stepLocal, invalid] at transition
  | cons clause rest =>
      rcases clause with ⟨patterns, guard, body⟩
      by_cases allowed : patternsObservationAllowed patterns values = true
      · cases matching : matchPatterns patterns values with
        | none =>
            exact step_unmatched_clause_preserves world context stack patterns guard body rest values after
              before allowed matching transition
        | some matched =>
            exact step_matched_clause_preserves world context stack patterns guard body rest values matched after
              before allowed matching transition
      · simp [stepLocal, allowed, unsupported] at transition

theorem step_try_raise_preserves (world : CodeWorld) (context current : Context)
    (stack : List Frame) (normalBinders binders : List VarId) (body handler : Expr)
    (exception : Exception) (after : LocalState)
    (before : LexicallyScoped
      ⟨.raise exception, current, .tryFrame context normalBinders body binders handler :: stack⟩)
    (transition : stepLocal world
      ⟨.raise exception, current, .tryFrame context normalBinders body binders handler :: stack⟩ =
      .next after) : LexicallyScoped after := by
  have frames := (stackScoped_cons _ _).mp before.frames
  have handlers : ScopedBinding context normalBinders body ∧
      ScopedBinding context binders handler := frames.1
  by_cases two : binders.length = 2
  · have stateEq : ({
        control := .eval handler
        context := { context with env := binders.zip [.atom exception.kind.name, exception.reason] ++ context.env }
        stack := stack } : LocalState) = after := by
      apply @Transition.next.inj LocalState Outcome
      simpa [stepLocal, two] using transition
    rw [← stateEq]
    exact ⟨scoped_binding_extend context binders handler _ handlers.2 (by simpa using two), frames.2⟩
  · by_cases three : binders.length = 3
    · have stateEq : ({
          control := .eval handler
          context := { context with env := binders.zip [.atom exception.kind.name, exception.reason, .exceptionInfo exception.kind.name] ++ context.env }
          stack := stack } : LocalState) = after := by
        apply @Transition.next.inj LocalState Outcome
        simpa [stepLocal, two, three] using transition
      rw [← stateEq]
      exact ⟨scoped_binding_extend context binders handler _ handlers.2 (by simpa using three), frames.2⟩
    · simp [stepLocal, two, three, invalid] at transition

theorem step_guard_raise_preserves (world : CodeWorld) (context current : Context)
    (stack : List Frame) (matched : Env) (values : Values) (body : Expr)
    (rest : List Clause) (exception : Exception) (after : LocalState)
    (before : LexicallyScoped
      ⟨.raise exception, current, .guard context matched values body rest :: stack⟩)
    (transition : stepLocal world
      ⟨.raise exception, current, .guard context matched values body rest :: stack⟩ = .next after) :
    LexicallyScoped after := by
  have frames := (stackScoped_cons _ _).mp before.frames
  have guarded : ScopedExpr { context with env := matched ++ context.env } body ∧
      ScopedClauses context rest := frames.1
  by_cases isError : (exception.kind == .error) = true
  · have stateEq : ({
        control := .select values rest
        context := context
        stack := stack } : LocalState) = after := by
      apply @Transition.next.inj LocalState Outcome
      simpa [stepLocal, isError] using transition
    rw [← stateEq]
    exact ⟨guarded.2, frames.2⟩
  · have stateEq : ({
        control := .raise exception
        context := current
        stack := stack } : LocalState) = after := by
      apply @Transition.next.inj LocalState Outcome
      simpa [stepLocal, isError] using transition
    rw [← stateEq]
    exact ⟨trivial, frames.2⟩

theorem step_raise_preserves (world : CodeWorld) (context : Context) (stack : List Frame)
    (exception : Exception) (after : LocalState)
    (before : LexicallyScoped ⟨.raise exception, context, stack⟩)
    (transition : stepLocal world ⟨.raise exception, context, stack⟩ = .next after) :
    LexicallyScoped after := by
  cases stack with
  | nil => simp [stepLocal] at transition
  | cons frame stack =>
      have frames := (stackScoped_cons _ _).mp before.frames
      cases frame with
      | tryFrame saved binders body exceptionBinders handler =>
          exact step_try_raise_preserves world saved context stack binders exceptionBinders body handler
            exception after before transition
      | guard saved matched values body rest =>
          exact step_guard_raise_preserves world saved context stack matched values body rest
            exception after before transition
      | catchFrame saved =>
          rcases exception with ⟨kind, reason⟩
          cases kind with
          | error => simp [stepLocal, unsupported] at transition
          | exit =>
              have stateEq := Transition.next.inj transition
              rw [← stateEq]
              exact ⟨trivial, frames.2⟩
          | throw =>
              have stateEq := Transition.next.inj transition
              rw [← stateEq]
              exact ⟨trivial, frames.2⟩
      | collect action saved done rest =>
          have stateEq := Transition.next.inj transition
          rw [← stateEq]
          exact ⟨trivial, frames.2⟩
      | bind saved binders body =>
          have stateEq := Transition.next.inj transition
          rw [← stateEq]
          exact ⟨trivial, frames.2⟩
      | seq saved body =>
          have stateEq := Transition.next.inj transition
          rw [← stateEq]
          exact ⟨trivial, frames.2⟩
      | select saved clauses =>
          have stateEq := Transition.next.inj transition
          rw [← stateEq]
          exact ⟨trivial, frames.2⟩

/-- Every successful local step preserves lexical variable availability in
    the active control and all saved continuation frames of a checked world.
    This does not assert freedom from model faults or OTP semantic equivalence. -/
theorem stepLocal_preserves_lexical_scope (world : CodeWorld) (state after : LocalState)
    (checked : CheckedWorld world) (before : LexicallyScoped state)
    (transition : stepLocal world state = .next after) : LexicallyScoped after := by
  rcases state with ⟨control, context, stack⟩
  cases control with
  | eval expression => exact step_eval_preserves world context stack expression after checked before transition
  | ret values => exact step_ret_preserves world context stack values after checked before transition
  | select values clauses => exact step_select_preserves world context stack values clauses after before transition
  | raise exception => exact step_raise_preserves world context stack exception after before transition
  | runtime name args => simp [stepLocal, unsupported] at transition

theorem runLocal_preserves_lexical_scope (world : CodeWorld) (state after : LocalState)
    (fuel : Nat) (checked : CheckedWorld world) (before : LexicallyScoped state)
    (execution : runLocal fuel world state = .exhausted after) : LexicallyScoped after := by
  induction fuel generalizing state with
  | zero =>
      have stateEq : state = after := by simpa [runLocal, run] using execution
      rw [← stateEq]
      exact before
  | succ fuel ih =>
      cases transition : stepLocal world state with
      | halt outcome => simp [runLocal, run, transition] at execution
      | next middle =>
          exact ih middle (stepLocal_preserves_lexical_scope world state middle checked before transition)
            (by simpa [runLocal, run, transition] using execution)

theorem literal_operands_scope (scope : List VarId) (values : Values) :
    scopeCheckList scope (values.map Expr.lit) = true := by
  induction values with
  | nil => simp [scopeCheckList]
  | cons value rest ih => simp [scopeCheckList, scopeCheck, ih]

theorem initialCall_lexicallyScoped (moduleName name : String) (args : Values) :
    LexicallyScoped (initialCall moduleName name args) := by
  refine ⟨⟨[], ?_, ?_⟩, ?_⟩
  · intro id member
    cases member
  · simp [WellScoped, scopeCheck, literal_operands_scope]
  · intro frame member
    cases member

end Erlean.Semantics
