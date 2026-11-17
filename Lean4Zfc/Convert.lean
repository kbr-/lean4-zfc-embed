import Lean4Zfc.Infer

/-!
A type inferencer that converts where the judgement's own rules justify it.

`infer` types a term by the structural rules, and also a term whose binder domains or application
heads have a type that is a sort or a function type only after unfolding constants and contracting
redexes. Each step it takes is one rule of Lean4Lean's judgement applied to types the function has
itself inferred and compared syntactically: a stored unfolding from the list `eqs` (`extra`), a
contraction (`beta`), a step under an application (`appDF`), a chain of steps at one sort (`trans`),
and the retyping of a term at a converted type (`defeqDF`). No inversion lemma and no unique typing
is used.

Conversion calls inference on terms that are not subterms, so everything runs on fuel.
`infer_sound` holds for every fuel: a result is a typing in the judgement, given that the
equations in `eqs` are stored in the environment.
-/

namespace Lean4Zfc

open Lean4Lean

/-- The unfolding of `c` at the levels `ls` by a stored equation of `eqs`, with its type. -/
def findUnfold (eqs : List VDefEq) (U : Nat) (c : Lean.Name) (ls : List VLevel) :
    Option (VExpr × VExpr) :=
  eqs.findSome? fun df =>
    if df.lhs.instL ls = .const c ls ∧ ls.length = df.uvars ∧ (∀ l ∈ ls, l.WF U) then
      some (df.rhs.instL ls, df.type.instL ls)
    else none

theorem findUnfold_sound {env : VEnv} {eqs : List VDefEq} {U : Nat}
    (heqs : ∀ df ∈ eqs, env.defeqs df) {Γ : List VExpr} {c : Lean.Name} {ls : List VLevel}
    {e' A : VExpr} (h : findUnfold eqs U c ls = some (e', A)) :
    env.IsDefEq U Γ (.const c ls) e' A := by
  obtain ⟨df, hmem, hdf⟩ := List.exists_of_findSome?_eq_some h
  split at hdf
  · rename_i hc
    cases hdf
    have := VEnv.IsDefEq.extra (Γ := Γ) (heqs df hmem) hc.2.2 hc.2.1
    rw [hc.1] at this
    exact this
  · cases hdf

mutual

/-- A type of `e` in the context `Γ`, on the fuel given. -/
def infer (env : VEnv) (eqs : List VDefEq) (U : Nat) : Nat → List VExpr → VExpr → Option VExpr
  | 0, _, _ => none
  | _ + 1, Γ, .bvar i => lookupTy Γ i
  | _ + 1, _, .sort l => if l.WF U then some (.sort (.succ l)) else none
  | _ + 1, _, .const c ls =>
    match env.constants c with
    | some ci =>
      if (∀ l ∈ ls, l.WF U) ∧ ls.length = ci.uvars then some (ci.type.instL ls) else none
    | none => none
  | n + 1, Γ, .app f a =>
    match infer env eqs U n Γ f, infer env eqs U n Γ a with
    | some Tf, some A' =>
      match whnfTy env eqs U n Γ Tf with
      | some (.forallE A B) =>
        if A = A' ∨ (stepsTo env eqs U n Γ A A').isSome ∨ (stepsTo env eqs U n Γ A' A).isSome then
          some (B.inst a)
        else none
      | _ => none
    | _, _ => none
  | n + 1, Γ, .lam A b =>
    match sortOf env eqs U n Γ A, infer env eqs U n (A :: Γ) b with
    | some _, some B => some (.forallE A B)
    | _, _ => none
  | n + 1, Γ, .forallE A B =>
    match sortOf env eqs U n Γ A, sortOf env eqs U n (A :: Γ) B with
    | some u, some v => some (.sort (.imax u v))
    | _, _ => none

/-- The level `u` with `e : Sort u`, after conversion of `e`'s inferred type. -/
def sortOf (env : VEnv) (eqs : List VDefEq) (U : Nat) : Nat → List VExpr → VExpr → Option VLevel
  | 0, _, _ => none
  | n + 1, Γ, e =>
    match infer env eqs U n Γ e with
    | some T =>
      match whnfTy env eqs U n Γ T with
      | some (.sort u) => some u
      | _ => none
    | none => none

/-- The type `T` itself when it is a sort or a function type, and otherwise what it steps to, if
that is one. -/
def whnfTy (env : VEnv) (eqs : List VDefEq) (U : Nat) : Nat → List VExpr → VExpr → Option VExpr
  | 0, _, _ => none
  | n + 1, Γ, T =>
    match T with
    | .sort u => some (.sort u)
    | .forallE A B => some (.forallE A B)
    | T =>
      match red env eqs U n Γ T with
      | some (T', .sort s) => chase env eqs U n Γ T' s
      | _ => none

/-- Steps from `T`, each at the sort `s`, until a sort or a function type. -/
def chase (env : VEnv) (eqs : List VDefEq) (U : Nat) :
    Nat → List VExpr → VExpr → VLevel → Option VExpr
  | 0, _, _, _ => none
  | n + 1, Γ, T, s =>
    match T with
    | .sort u => some (.sort u)
    | .forallE A B => some (.forallE A B)
    | T =>
      match red env eqs U n Γ T with
      | some (T', S) => if S = .sort s then chase env eqs U n Γ T' s else none
      | none => none

/-- Some level `s` when `T` steps to `target` at the sort `s`, every step at that sort. -/
def stepsTo (env : VEnv) (eqs : List VDefEq) (U : Nat) :
    Nat → List VExpr → VExpr → VExpr → Option VLevel
  | 0, _, _, _ => none
  | n + 1, Γ, T, target =>
    match red env eqs U n Γ T with
    | some (T', .sort s) =>
      if T' = target then some s else stepsToAt env eqs U n Γ T' target s
    | _ => none

/-- `s` when `T` steps to `target`, every step at the sort `s`. -/
def stepsToAt (env : VEnv) (eqs : List VDefEq) (U : Nat) :
    Nat → List VExpr → VExpr → VExpr → VLevel → Option VLevel
  | 0, _, _, _, _ => none
  | n + 1, Γ, T, target, s =>
    match red env eqs U n Γ T with
    | some (T', S) =>
      if S = .sort s then
        if T' = target then some s else stepsToAt env eqs U n Γ T' target s
      else none
    | none => none

/-- One head step of `e`, with the type the step is taken at. -/
def red (env : VEnv) (eqs : List VDefEq) (U : Nat) :
    Nat → List VExpr → VExpr → Option (VExpr × VExpr)
  | 0, _, _ => none
  | n + 1, Γ, e =>
    match e with
    | .const c ls => findUnfold eqs U c ls
    | .app (.lam A b) a =>
      match infer env eqs U n (A :: Γ) b, infer env eqs U n Γ a with
      | some B, some A' => if A' = A then some (b.inst a, B.inst a) else none
      | _, _ => none
    | .app f a =>
      match red env eqs U n Γ f, infer env eqs U n Γ a with
      | some (f', .forallE A B), some A' =>
        if A' = A then some (.app f' a, B.inst a) else none
      | _, _ => none
    | _ => none

end

/-- What each function's result means in the judgement. -/
structure Sound (env : VEnv) (eqs : List VDefEq) (U : Nat) (n : Nat) : Prop where
  infer : ∀ {Γ e A}, infer env eqs U n Γ e = some A → env.HasType U Γ e A
  sortOf : ∀ {Γ e u}, sortOf env eqs U n Γ e = some u → env.HasType U Γ e (.sort u)
  whnfTy : ∀ {Γ T T'}, whnfTy env eqs U n Γ T = some T' →
    T' = T ∨ ∃ s, env.IsDefEq U Γ T T' (.sort s)
  chase : ∀ {Γ T s T'}, chase env eqs U n Γ T s = some T' →
    T' = T ∨ env.IsDefEq U Γ T T' (.sort s)
  red : ∀ {Γ e e' A}, red env eqs U n Γ e = some (e', A) → env.IsDefEq U Γ e e' A
  stepsTo : ∀ {Γ T target s}, stepsTo env eqs U n Γ T target = some s →
    ∃ s', env.IsDefEq U Γ T target (.sort s')
  stepsToAt : ∀ {Γ T target s r}, stepsToAt env eqs U n Γ T target s = some r →
    env.IsDefEq U Γ T target (.sort s)

/-- Retyping at a converted type. -/
theorem retype {env : VEnv} {U : Nat} {Γ : List VExpr} {e T T' : VExpr}
    (h : env.HasType U Γ e T) (hw : T' = T ∨ ∃ s, env.IsDefEq U Γ T T' (.sort s)) :
    env.HasType U Γ e T' := by
  rcases hw with rfl | ⟨s, hs⟩
  · exact h
  · exact .defeqDF hs h

theorem sound {env : VEnv} {eqs : List VDefEq} {U : Nat}
    (heqs : ∀ df ∈ eqs, env.defeqs df) : ∀ n, Sound env eqs U n
  | 0 => by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> rename_i h <;>
      simp [infer, sortOf, whnfTy, chase, red, stepsTo, stepsToAt] at h
  | n + 1 => by
    have ih : Sound env eqs U n := sound heqs n
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro Γ e A h
      cases e with
      | bvar i => exact .bvar (lookupTy_sound (by simpa [infer] using h))
      | sort l =>
        simp only [infer] at h
        split at h
        · cases h; exact VEnv.HasType.sort ‹_›
        · cases h
      | const c ls =>
        simp only [infer] at h
        split at h
        · rename_i ci hc
          split at h
          · rename_i hw
            cases h
            exact VEnv.HasType.const hc hw.1 hw.2
          · cases h
        · cases h
      | app f a =>
        simp only [infer] at h
        split at h
        · rename_i Tf A' hf ha
          split at h
          · rename_i A₀ B hw
            have hF := retype (ih.infer hf) (ih.whnfTy hw)
            have hA := ih.infer ha
            split at h
            · rename_i hc
              cases h
              rcases hc with heq | h1 | h2
              · subst heq
                exact VEnv.HasType.app hF hA
              · obtain ⟨s, hs⟩ := Option.isSome_iff_exists.1 h1
                obtain ⟨s', hd⟩ := ih.stepsTo hs
                exact VEnv.HasType.app hF (.defeqDF (.symm hd) hA)
              · obtain ⟨s, hs⟩ := Option.isSome_iff_exists.1 h2
                obtain ⟨s', hd⟩ := ih.stepsTo hs
                exact VEnv.HasType.app hF (.defeqDF hd hA)
            · cases h
          · cases h
        · cases h
      | lam A₀ b =>
        simp only [infer] at h
        split at h
        · rename_i u B hA hb
          cases h
          exact VEnv.HasType.lam (ih.sortOf hA) (ih.infer hb)
        · cases h
      | forallE A₀ B =>
        simp only [infer] at h
        split at h
        · rename_i u v hA hB
          cases h
          exact VEnv.HasType.forallE (ih.sortOf hA) (ih.sortOf hB)
        · cases h
    · intro Γ e u h
      simp only [sortOf] at h
      split at h
      · rename_i T hT
        split at h
        · rename_i u' hw
          cases h
          exact retype (ih.infer hT) (ih.whnfTy hw)
        · cases h
      · cases h
    · intro Γ T T' h
      simp only [whnfTy] at h
      split at h
      · cases h; exact .inl rfl
      · cases h; exact .inl rfl
      · split at h
        · rename_i T₁ s hr
          rcases ih.chase h with rfl | hc
          · exact .inr ⟨s, ih.red hr⟩
          · exact .inr ⟨s, .trans (ih.red hr) hc⟩
        · cases h
    · intro Γ T s T' h
      simp only [chase] at h
      split at h
      · cases h; exact .inl rfl
      · cases h; exact .inl rfl
      · split at h
        · rename_i T₁ S hr
          split at h
          · rename_i hS
            subst hS
            rcases ih.chase h with rfl | hc
            · exact .inr (ih.red hr)
            · exact .inr (.trans (ih.red hr) hc)
          · cases h
        · cases h
    · intro Γ e e' A h
      simp only [red] at h
      split at h
      · exact findUnfold_sound heqs h
      · split at h
        · rename_i B A' hb ha
          split at h
          · rename_i heq
            cases h
            subst heq
            exact .beta (ih.infer hb) (ih.infer ha)
          · cases h
        · cases h
      · split at h
        · rename_i f' A₀ B A' hf ha
          split at h
          · rename_i heq
            cases h
            subst heq
            exact .appDF (ih.red hf) (ih.infer ha)
          · cases h
        · cases h
      · cases h
    · intro Γ T target s h
      simp only [stepsTo] at h
      split at h
      · rename_i T' s' hr
        split at h
        · rename_i heq
          subst heq
          exact ⟨s', ih.red hr⟩
        · exact ⟨s', .trans (ih.red hr) (ih.stepsToAt h)⟩
      · cases h
    · intro Γ T target s r h
      simp only [stepsToAt] at h
      split at h
      · rename_i T' S hr
        split at h
        · rename_i hS
          subst hS
          split at h
          · rename_i heq
            subst heq
            exact ih.red hr
          · exact .trans (ih.red hr) (ih.stepsToAt h)
        · cases h
      · cases h

/-- What `infer` returns is a type of the term in Lean4Lean's judgement, whatever the fuel. -/
theorem infer_sound {env : VEnv} {eqs : List VDefEq} {U : Nat}
    (heqs : ∀ df ∈ eqs, env.defeqs df) {n : Nat} {Γ : List VExpr} {e A : VExpr}
    (h : infer env eqs U n Γ e = some A) : env.HasType U Γ e A :=
  (sound heqs n).infer h

/-- What `sortOf` returns is a sort of the term in Lean4Lean's judgement. -/
theorem sortOf_sound {env : VEnv} {eqs : List VDefEq} {U : Nat}
    (heqs : ∀ df ∈ eqs, env.defeqs df) {n : Nat} {Γ : List VExpr} {e : VExpr} {u : VLevel}
    (h : sortOf env eqs U n Γ e = some u) : env.HasType U Γ e (.sort u) :=
  (sound heqs n).sortOf h

end Lean4Zfc
