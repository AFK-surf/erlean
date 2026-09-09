import Erlean.Core.Syntax

namespace Erlean.Core

/-- Fresh binders make the importer's unique-name convention executable. -/
def freshBinders (scope binders : List VarId) : Bool :=
  binders.all (fun id => !scope.contains id) && decide binders.Nodup

theorem freshBinders_iff (scope binders : List VarId) :
    freshBinders scope binders = true ↔
      (∀ id ∈ binders, id ∉ scope) ∧ binders.Nodup := by
  simp [freshBinders]

def Pattern.binders : Pattern → List VarId
  | .wild | .lit _ => []
  | .var id => [id]
  | .alias id pattern => id :: pattern.binders
  | .cons head tail => head.binders ++ tail.binders
  | .tuple elements => elements.flatMap Pattern.binders

mutual
/-- Check lexical scope without assigning dynamic Core result arities. -/
def scopeCheck (scope : List VarId) (expr : Expr) : Bool :=
  match expr with
  | .lit _ | .funRef _ _ | .makeClosure _ => true
  | .letrec bindings body =>
      let ids := bindings.map Prod.fst
      freshBinders scope ids && scopeCheck (ids ++ scope) body
  | .var id => scope.contains id
  | .tryE argument binders body exceptionBinders handler =>
      freshBinders scope binders && freshBinders scope exceptionBinders &&
        (exceptionBinders.length == 2 || exceptionBinders.length == 3) &&
        scopeCheck scope argument && scopeCheck (binders ++ scope) body &&
        scopeCheck (exceptionBinders ++ scope) handler
  | .catchE body => scopeCheck scope body
  | .values elements | .tuple elements => scopeCheckList scope elements
  | .letE binders argument body =>
      freshBinders scope binders && scopeCheck scope argument &&
        scopeCheck (binders ++ scope) body
  | .seq first second | .cons first second =>
      scopeCheck scope first && scopeCheck scope second
  | .call moduleName functionName arguments =>
      scopeCheck scope moduleName && scopeCheck scope functionName &&
        scopeCheckList scope arguments
  | .apply function arguments =>
      scopeCheck scope function && scopeCheckList scope arguments
  | .primop _ arguments => scopeCheckList scope arguments
  | .caseE argument clauses =>
      scopeCheck scope argument && scopeCheckClauses scope clauses
termination_by sizeOf expr

def scopeCheckList (scope : List VarId) (expressions : List Expr) : Bool :=
  match expressions with
  | [] => true
  | expression :: rest => scopeCheck scope expression && scopeCheckList scope rest
termination_by sizeOf expressions

def scopeCheckClauses (scope : List VarId) (clauses : List Clause) : Bool :=
  match clauses with
  | [] => true
  | (patterns, guard, body) :: rest =>
      let binders := patterns.flatMap Pattern.binders
      freshBinders scope binders && scopeCheck (binders ++ scope) guard &&
        scopeCheck (binders ++ scope) body && scopeCheckClauses scope rest
termination_by sizeOf clauses
end

/-- Scope validity is the accepted-input predicate for the executable checker.
    This does not prove source name resolution or OTP compatibility. -/
def WellScoped (scope : List VarId) (expr : Expr) : Prop :=
  scopeCheck scope expr = true

instance (scope : List VarId) (expr : Expr) : Decidable (WellScoped scope expr) :=
  inferInstanceAs (Decidable (scopeCheck scope expr = true))

@[simp] theorem wellScoped_lit (scope : List VarId) (value : Value) :
    WellScoped scope (.lit value) := by simp [WellScoped, scopeCheck]

@[simp] theorem wellScoped_var_iff (scope : List VarId) (id : VarId) :
    WellScoped scope (.var id) ↔ id ∈ scope := by
  simp [WellScoped, scopeCheck]

theorem scopeCheckList_iff (scope : List VarId) (expressions : List Expr) :
    scopeCheckList scope expressions = true ↔
      ∀ expression ∈ expressions, WellScoped scope expression := by
  induction expressions with
  | nil => simp [scopeCheckList]
  | cons expression rest ih => simp [scopeCheckList, ih, WellScoped]

@[simp] theorem wellScoped_seq_iff (scope : List VarId) (first second : Expr) :
    WellScoped scope (.seq first second) ↔
      WellScoped scope first ∧ WellScoped scope second := by
  simp [WellScoped, scopeCheck]

@[simp] theorem wellScoped_let_iff (scope binders : List VarId) (argument body : Expr) :
    WellScoped scope (.letE binders argument body) ↔
      (freshBinders scope binders = true ∧ WellScoped scope argument) ∧
      WellScoped (binders ++ scope) body := by
  simp [WellScoped, scopeCheck]

def FunctionDef.scopeCheck (fn : FunctionDef) : Bool :=
  decide fn.params.Nodup && Core.scopeCheck fn.params fn.body

mutual
/-- Validate code-table references and their required lexical captures. -/
def closureRefsCheck (code : List ClosureDef) (scope : List VarId) (expr : Expr) : Bool :=
  match expr with
  | .lit _ | .var _ | .funRef _ _ => true
  | .makeClosure index =>
    match code[index]? with
    | none => false
    | some defn => defn.outerScope.all scope.contains
  | .letrec bindings body =>
    bindings.all (fun (_, index) => match code[index]? with
      | none => false
      | some defn => defn.recursiveBindings == bindings && defn.outerScope.all scope.contains) &&
      closureRefsCheck code (bindings.map Prod.fst ++ scope) body
  | .values xs | .tuple xs => closureRefsList code scope xs
  | .tryE argument binders body exceptionBinders handler =>
    closureRefsCheck code scope argument && closureRefsCheck code (binders ++ scope) body &&
      closureRefsCheck code (exceptionBinders ++ scope) handler
  | .catchE body => closureRefsCheck code scope body
  | .letE ids arg body => closureRefsCheck code scope arg && closureRefsCheck code (ids ++ scope) body
  | .seq first second | .cons first second =>
    closureRefsCheck code scope first && closureRefsCheck code scope second
  | .call mod fn args => closureRefsCheck code scope mod && closureRefsCheck code scope fn &&
    closureRefsList code scope args
  | .apply fn args => closureRefsCheck code scope fn && closureRefsList code scope args
  | .primop _ args => closureRefsList code scope args
  | .caseE arg clauses => closureRefsCheck code scope arg && closureRefsClauses code scope clauses
termination_by sizeOf expr

def closureRefsList (code : List ClosureDef) (scope : List VarId) (xs : List Expr) : Bool :=
  match xs with
  | [] => true
  | x :: rest => closureRefsCheck code scope x && closureRefsList code scope rest
termination_by sizeOf xs

def closureRefsClauses (code : List ClosureDef) (scope : List VarId) (clauses : List Clause) : Bool :=
  match clauses with
  | [] => true
  | (patterns, guard, body) :: rest =>
    let inner := patterns.flatMap Pattern.binders ++ scope
    closureRefsCheck code inner guard && closureRefsCheck code inner body &&
      closureRefsClauses code scope rest
termination_by sizeOf clauses
end

def ClosureDef.check (code : List ClosureDef) (defn : ClosureDef) : Bool :=
  let group := defn.recursiveBindings.map Prod.fst
  let scope := defn.params ++ group ++ defn.outerScope
  decide defn.outerScope.Nodup && freshBinders defn.outerScope group &&
    freshBinders (group ++ defn.outerScope) defn.params && scopeCheck scope defn.body &&
    closureRefsCheck code scope defn.body

/-- Check function names/arity uniqueness and that every export is defined. -/
def Module.check (mod : Module) : Bool :=
  let signatures := mod.functions.map (fun fn => (fn.name, fn.params.length))
  decide signatures.Nodup && decide mod.exports.Nodup &&
    mod.exports.all signatures.contains && mod.functions.all FunctionDef.scopeCheck &&
    mod.functions.all (fun fn => closureRefsCheck mod.closureCode fn.params fn.body) &&
    mod.closureCode.all (ClosureDef.check mod.closureCode)

end Erlean.Core
