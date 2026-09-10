import Erlean.Core.Scope
import Erlean.Core.Bytes

namespace Erlean.Core

/-- Select literal map keys without inspecting any stored value. Duplicate
    pattern keys select the same field again; extra map entries are ignored. -/
def selectMapValues (keys : List MapKey) (entries : List (MapKey × Value)) : Option Values :=
  keys.mapM (fun key => FiniteMap.lookup key entries)

mutual
/-- Matching for linear, fresh patterns accepted by the scope checker.
    Literal comparison is restricted to the initial value profile. -/
def matchPattern (pattern : Pattern) (value : Value) : Option Env :=
  match pattern, value with
  | .wild, _ => some []
  | .var id, value => some [(id, value)]
  | .alias id pattern, value => do
      let env ← matchPattern pattern value
      pure ((id, value) :: env)
  | .lit expected, value => if expected == value then some [] else none
  | .cons head tail, .cons first rest => do
      let headEnv ← matchPattern head first
      let tailEnv ← matchPattern tail rest
      pure (headEnv ++ tailEnv)
  | .tuple patterns, .tuple values => matchPatterns patterns values
  | .map keys patterns, .map entries => do
      if !Value.mapOrdered entries then none else do
        let values ← selectMapValues keys entries
        matchPatterns patterns values
  | .bytes patterns, .bitstring bits => do
      let values ← decodeByteValues patterns.length bits
      matchPatterns patterns values
  | _, _ => none
termination_by sizeOf pattern

def matchPatterns (patterns : List Pattern) (values : Values) : Option Env :=
  match patterns, values with
  | [], [] => some []
  | pattern :: rest, value :: remaining => do
      let env ← matchPattern pattern value
      let restEnv ← matchPatterns rest remaining
      pure (env ++ restEnv)
  | _, _ => none
termination_by sizeOf patterns
end

@[simp] theorem matchPattern_wild (value : Value) :
    matchPattern .wild value = some [] := by simp [matchPattern]

@[simp] theorem matchPattern_var (id : VarId) (value : Value) :
    matchPattern (.var id) value = some [(id, value)] := by simp [matchPattern]

@[simp] theorem matchPatterns_nil : matchPatterns [] [] = some [] := by
  simp [matchPatterns]

@[simp] theorem matchPattern_tuple (patterns : List Pattern) (values : Values) :
    matchPattern (.tuple patterns) (.tuple values) = matchPatterns patterns values := by
  simp [matchPattern]

theorem matchPattern_cons_success (head tail : Pattern) (first rest : Value)
    (headEnv tailEnv : Env)
    (headMatch : matchPattern head first = some headEnv)
    (tailMatch : matchPattern tail rest = some tailEnv) :
    matchPattern (.cons head tail) (.cons first rest) = some (headEnv ++ tailEnv) := by
  simp [matchPattern, headMatch, tailMatch]

theorem matchPatterns_cons_success (pattern : Pattern) (patterns : List Pattern)
    (value : Value) (values : Values) (env restEnv : Env)
    (headMatch : matchPattern pattern value = some env)
    (tailMatch : matchPatterns patterns values = some restEnv) :
    matchPatterns (pattern :: patterns) (value :: values) = some (env ++ restEnv) := by
  simp [matchPatterns, headMatch, tailMatch]

/-- Matching preserves the lexical, left-to-right order of pattern bindings. -/
theorem match_cons_variables (headId tailId : VarId) (head tail : Value) :
    matchPattern (.cons (.var headId) (.var tailId)) (.cons head tail) =
      some [(headId, head), (tailId, tail)] := by
  simp [matchPattern]

mutual
/-- A successful match binds exactly the variables declared by its pattern. -/
theorem matchPattern_keys (pattern : Pattern) (value : Value) (env : Env)
    (h : matchPattern pattern value = some env) :
    env.map Prod.fst = pattern.binders := by
  match pattern, value with
  | .wild, _ => simpa [matchPattern, Pattern.binders] using h.symm
  | .var id, value =>
      have he : [(id, value)] = env := by simpa [matchPattern] using h
      subst env
      simp [Pattern.binders]
  | .alias id pattern, value =>
      cases hm : matchPattern pattern value with
      | none => simp [matchPattern, hm] at h
      | some inner =>
          have he : (id, value) :: inner = env := by simpa [matchPattern, hm] using h
          subst env
          simp [Pattern.binders, matchPattern_keys pattern value inner hm]
  | .lit expected, value =>
      by_cases equal : (expected == value) = true
      · have he : [] = env := by simpa [matchPattern, equal] using h
        subst env
        simp [Pattern.binders]
      · simp [matchPattern, equal] at h
  | .cons head tail, .cons first rest =>
      cases hh : matchPattern head first with
      | none => simp [matchPattern, hh] at h
      | some headEnv =>
          cases ht : matchPattern tail rest with
          | none => simp [matchPattern, hh, ht] at h
          | some tailEnv =>
              have he : headEnv ++ tailEnv = env := by
                simpa [matchPattern, hh, ht] using h
              subst env
              simp [Pattern.binders, List.map_append,
                matchPattern_keys head first headEnv hh,
                matchPattern_keys tail rest tailEnv ht]
  | .tuple patterns, .tuple values =>
      simpa [Pattern.binders] using
        matchPatterns_keys patterns values env (by simpa [matchPattern] using h)
  | .map keys patterns, .map entries =>
      by_cases ordered : Value.mapOrdered entries = true
      · cases selected : selectMapValues keys entries with
        | none => simp [matchPattern, ordered, selected] at h
        | some values =>
          simpa [Pattern.binders] using
            matchPatterns_keys patterns values env (by simpa [matchPattern, ordered, selected] using h)
      · simp [matchPattern, ordered] at h
  | .bytes patterns, .bitstring bits =>
      cases hd : decodeByteValues patterns.length bits with
      | none => simp [matchPattern, hd] at h
      | some values =>
          simpa [Pattern.binders] using
            matchPatterns_keys patterns values env (by simpa [matchPattern, hd] using h)
  | .bytes _, .integer _ | .bytes _, .floatBits _ | .bytes _, .atom _ | .bytes _, .nil
  | .bytes _, .cons _ _ | .bytes _, .tuple _ | .bytes _, .function _ _ _
  | .bytes _, .closure _ _ _ _ | .bytes _, .exceptionInfo _
  | .bytes _, .pid _ | .bytes _, .reference _ | .bytes _, .iterator _
  | .cons _ _, .pid _ | .cons _ _, .reference _ | .cons _ _, .iterator _
  | .tuple _, .pid _ | .tuple _, .reference _ | .tuple _, .iterator _ =>
      simp [matchPattern] at h
  | .cons _ _, .integer _ | .cons _ _, .floatBits _ | .cons _ _, .atom _ | .cons _ _, .nil
  | .cons _ _, .tuple _ | .cons _ _, .bitstring _ | .cons _ _, .function _ _ _
  | .cons _ _, .closure _ _ _ _
  | .cons _ _, .exceptionInfo _
  | .tuple _, .integer _ | .tuple _, .floatBits _ | .tuple _, .atom _ | .tuple _, .nil
  | .tuple _, .cons _ _ | .tuple _, .bitstring _ | .tuple _, .function _ _ _ =>
      simp [matchPattern] at h
  | .tuple _, .closure _ _ _ _ | .tuple _, .exceptionInfo _ => simp [matchPattern] at h
  | .cons _ _, .map _ | .tuple _, .map _ | .bytes _, .map _
  | .map _ _, .integer _ | .map _ _, .floatBits _ | .map _ _, .atom _ | .map _ _, .nil
  | .map _ _, .cons _ _ | .map _ _, .tuple _ | .map _ _, .bitstring _
  | .map _ _, .pid _ | .map _ _, .reference _ | .map _ _, .function _ _ _
  | .map _ _, .closure _ _ _ _ | .map _ _, .exceptionInfo _
  | .map _ _, .iterator _ => simp [matchPattern] at h
termination_by sizeOf pattern

theorem matchPatterns_keys (patterns : List Pattern) (values : Values) (env : Env)
    (h : matchPatterns patterns values = some env) :
    env.map Prod.fst = patterns.flatMap Pattern.binders := by
  match patterns, values with
  | [], [] =>
      have he : [] = env := by simpa [matchPatterns] using h
      subst env
      rfl
  | [], _ :: _ | _ :: _, [] => simp [matchPatterns] at h
  | pattern :: rest, value :: remaining =>
      cases hh : matchPattern pattern value with
      | none => simp [matchPatterns, hh] at h
      | some headEnv =>
          cases ht : matchPatterns rest remaining with
          | none => simp [matchPatterns, hh, ht] at h
          | some tailEnv =>
              have he : headEnv ++ tailEnv = env := by
                simpa [matchPatterns, hh, ht] using h
              subst env
              simp [List.map_append, matchPattern_keys pattern value headEnv hh,
                matchPatterns_keys rest remaining tailEnv ht]
termination_by sizeOf patterns
end

end Erlean.Core
