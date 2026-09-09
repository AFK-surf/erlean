import Erlean.Core.Match
import Init.Data.List.Zip

namespace Erlean.Core

namespace Env

/-- Every variable in the scope has a value in the environment. Duplicate keys
    are permitted: lookup consistently uses the first binding. -/
def Covers (env : Env) (scope : List VarId) : Prop :=
  ∀ id ∈ scope, ∃ value, env.lookup id = some value

theorem lookup_exists_iff_mem_keys (env : Env) (id : VarId) :
    (∃ value, env.lookup id = some value) ↔ id ∈ env.map Prod.fst := by
  induction env with
  | nil => simp [lookup]
  | cons entry rest ih =>
      rcases entry with ⟨key, value⟩
      by_cases h : key = id
      · subst key
        simp [lookup]
      · simp [lookup, h, Ne.symm h, ih]

theorem lookup_none_iff_not_mem_keys (env : Env) (id : VarId) :
    env.lookup id = none ↔ id ∉ env.map Prod.fst := by
  constructor
  · intro hnone hmem
    obtain ⟨value, hvalue⟩ := (lookup_exists_iff_mem_keys env id).mpr hmem
    rw [hnone] at hvalue
    cases hvalue
  · intro hmem
    cases hlookup : env.lookup id with
    | none => rfl
    | some value =>
        exact False.elim (hmem ((lookup_exists_iff_mem_keys env id).mp ⟨value, hlookup⟩))

theorem covers_iff_mem_keys (env : Env) (scope : List VarId) :
    Covers env scope ↔ ∀ id ∈ scope, id ∈ env.map Prod.fst := by
  simp only [Covers, lookup_exists_iff_mem_keys]

/-- Prefix bindings shadow the back without losing its available keys. -/
theorem lookup_append (front back : Env) (id : VarId) :
    (front ++ back).lookup id =
      match front.lookup id with
      | some value => some value
      | none => back.lookup id := by
  induction front with
  | nil => simp [lookup]
  | cons entry rest ih =>
      rcases entry with ⟨key, value⟩
      by_cases h : key = id
      · simp [lookup, h]
      · simp [lookup, h, ih]

theorem lookup_append_of_some (front back : Env) (id : VarId) (value : Value)
    (h : front.lookup id = some value) :
    (front ++ back).lookup id = some value := by
  rw [lookup_append, h]

theorem lookup_append_of_none (front back : Env) (id : VarId)
    (h : front.lookup id = none) :
    (front ++ back).lookup id = back.lookup id := by
  rw [lookup_append, h]

theorem covers_append_left (front back : Env) (scope : List VarId)
    (h : Covers front scope) : Covers (front ++ back) scope := by
  rw [covers_iff_mem_keys] at h ⊢
  intro id hscope
  simp only [List.map_append, List.mem_append]
  exact Or.inl (h id hscope)

theorem covers_append_right (front back : Env) (scope : List VarId)
    (h : Covers back scope) : Covers (front ++ back) scope := by
  rw [covers_iff_mem_keys] at h ⊢
  intro id hscope
  simp only [List.map_append, List.mem_append]
  exact Or.inr (h id hscope)

theorem covers_append (front back : Env) (frontScope backScope : List VarId)
    (hp : Covers front frontScope) (hs : Covers back backScope) :
    Covers (front ++ back) (frontScope ++ backScope) := by
  intro id hmem
  rcases List.mem_append.mp hmem with hfront | hback
  · exact covers_append_left front back frontScope hp id hfront
  · exact covers_append_right front back backScope hs id hback

/-- Arity agreement prevents zip from silently dropping a parameter binding. -/
theorem zip_keys_of_length_eq (params : List VarId) (values : Values)
    (h : params.length = values.length) :
    (params.zip values).map Prod.fst = params := by
  exact List.map_fst_zip (Nat.le_of_eq h)

theorem covers_zip (params : List VarId) (values : Values)
    (h : params.length = values.length) : Covers (params.zip values) params := by
  rw [covers_iff_mem_keys, zip_keys_of_length_eq params values h]
  intro id hmem
  exact hmem

end Env

theorem matchPattern_covers (pattern : Pattern) (value : Value) (env : Env)
    (h : matchPattern pattern value = some env) :
    Env.Covers env pattern.binders := by
  rw [Env.covers_iff_mem_keys, matchPattern_keys pattern value env h]
  intro id hmem
  exact hmem

theorem matchPatterns_covers (patterns : List Pattern) (values : Values) (env : Env)
    (h : matchPatterns patterns values = some env) :
    Env.Covers env (patterns.flatMap Pattern.binders) := by
  rw [Env.covers_iff_mem_keys, matchPatterns_keys patterns values env h]
  intro id hmem
  exact hmem

/-- Pattern bindings extend an already covered scope. This is an environment
    lemma, not a preservation theorem for the full machine state. -/
theorem matchPatterns_extend_coverage (patterns : List Pattern) (values : Values)
    (matched outer : Env) (scope : List VarId)
    (hmatch : matchPatterns patterns values = some matched)
    (houter : Env.Covers outer scope) :
    Env.Covers (matched ++ outer) (patterns.flatMap Pattern.binders ++ scope) := by
  exact Env.covers_append matched outer (patterns.flatMap Pattern.binders) scope
    (matchPatterns_covers patterns values matched hmatch) houter

end Erlean.Core
