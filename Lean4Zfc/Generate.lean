import Lean4Zfc.Checked
import Lean4Zfc.Infer

/-!
A certified Lean4Lean environment computed from the environment Con-Leche's checker returns.

`generate cenv` walks the checker's constants, oldest first. A constant enters the Lean4Lean
environment when its type translates back to a Lean4Lean term and `inferType` types that term at a
sort in the environment built so far. A constant whose type is `@Eq T a b`, with `a` and `b` typed
at `T` by `inferType`, also adds the stored equation `a ≡ b : T`. Everything else is left out, and
so, by failing to type, is every later constant that mentions something left out.

`generate_certOrdered` proves the result certified against `cenv`, with no hypothesis, so
`generated_consistent` needs only the checker's acceptance. The generated environment holds no
equation the export does not state as a theorem: Con-Leche's model speaks of constants and of
`Eq`, not of the checker's reduction rules.
-/

namespace Lean4Zfc

open Lean4Lean

deriving instance DecidableEq for VDefEq

/-- Con-Leche's names as Lean's. -/
def untrName : ConLeche.Name → Lean.Name
  | .anonymous => .anonymous
  | .str p s => .str (untrName p) s
  | .num p n => .num (untrName p) n

theorem trName_untrName : ∀ n : ConLeche.Name, trName (untrName n) = n
  | .anonymous => rfl
  | .str p s => by simp [untrName, trName, trName_untrName p]
  | .num p n => by simp [untrName, trName, trName_untrName p]

/-- A Con-Leche level as a Lean4Lean level under the parameter names `ps`, where it has one. -/
def untrLevel (ps : List ConLeche.Name) : ConLeche.Level → Option VLevel
  | .zero => some .zero
  | .succ u => (untrLevel ps u).map .succ
  | .max u v =>
    match untrLevel ps u, untrLevel ps v with
    | some a, some b => some (.max a b)
    | _, _ => none
  | .imax u v =>
    match untrLevel ps u, untrLevel ps v with
    | some a, some b => some (.imax a b)
    | _, _ => none
  | .param n => if ps.idxOf n < ps.length then some (.param (ps.idxOf n)) else none

theorem trLevel_untrLevel {ps : List ConLeche.Name} :
    ∀ {u : ConLeche.Level} {l : VLevel}, untrLevel ps u = some l → trLevel ps l = u
  | .zero, _, h => by cases h; rfl
  | .succ u, l, h => by
    simp only [untrLevel, Option.map_eq_some_iff] at h
    obtain ⟨a, ha, rfl⟩ := h
    simp [trLevel, trLevel_untrLevel ha]
  | .max u v, l, h => by
    simp only [untrLevel] at h
    split at h
    · rename_i a b ha hb
      cases h
      simp [trLevel, trLevel_untrLevel ha, trLevel_untrLevel hb]
    · cases h
  | .imax u v, l, h => by
    simp only [untrLevel] at h
    split at h
    · rename_i a b ha hb
      cases h
      simp [trLevel, trLevel_untrLevel ha, trLevel_untrLevel hb]
    · cases h
  | .param n, l, h => by
    simp only [untrLevel] at h
    split at h
    · rename_i hlt
      cases h
      simp [trLevel, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
    · cases h

def untrLevels (ps : List ConLeche.Name) : List ConLeche.Level → Option (List VLevel)
  | [] => some []
  | u :: us =>
    match untrLevel ps u, untrLevels ps us with
    | some l, some ls => some (l :: ls)
    | _, _ => none

theorem trLevel_untrLevels {ps : List ConLeche.Name} :
    ∀ {us : List ConLeche.Level} {ls : List VLevel},
      untrLevels ps us = some ls → ls.map (trLevel ps) = us
  | [], _, h => by cases h; rfl
  | u :: us, ls, h => by
    simp only [untrLevels] at h
    split at h
    · rename_i l ls' hl hls
      cases h
      simp [trLevel_untrLevel hl, trLevel_untrLevels hls]
    · cases h

/-- A Con-Leche term as a Lean4Lean term, where it has one: no free variable, `let`, literal or
projection. -/
def untrExpr (ps : List ConLeche.Name) : ConLeche.Expr → Option VExpr
  | .bvar i => some (.bvar i)
  | .sort u => (untrLevel ps u).map .sort
  | .const n us => (untrLevels ps us).map (.const (untrName n))
  | .app f a =>
    match untrExpr ps f, untrExpr ps a with
    | some f', some a' => some (.app f' a')
    | _, _ => none
  | .lam A b =>
    match untrExpr ps A, untrExpr ps b with
    | some A', some b' => some (.lam A' b')
    | _, _ => none
  | .forallE A B =>
    match untrExpr ps A, untrExpr ps B with
    | some A', some B' => some (.forallE A' B')
    | _, _ => none
  | _ => none

theorem trExpr_untrExpr {ps : List ConLeche.Name} :
    ∀ {e : ConLeche.Expr} {v : VExpr}, untrExpr ps e = some v → trExpr ps v = e
  | .bvar i, _, h => by cases h; rfl
  | .sort u, v, h => by
    simp only [untrExpr, Option.map_eq_some_iff] at h
    obtain ⟨l, hl, rfl⟩ := h
    simp [trExpr, trLevel_untrLevel hl]
  | .const n us, v, h => by
    simp only [untrExpr, Option.map_eq_some_iff] at h
    obtain ⟨ls, hls, rfl⟩ := h
    simp [trExpr, trName_untrName, trLevel_untrLevels hls]
  | .app f a, v, h => by
    simp only [untrExpr] at h
    split at h
    · rename_i f' a' hf ha
      cases h
      simp [trExpr, trExpr_untrExpr hf, trExpr_untrExpr ha]
    · cases h
  | .lam A b, v, h => by
    simp only [untrExpr] at h
    split at h
    · rename_i A' b' hA hb
      cases h
      simp [trExpr, trExpr_untrExpr hA, trExpr_untrExpr hb]
    · cases h
  | .forallE A B, v, h => by
    simp only [untrExpr] at h
    split at h
    · rename_i A' B' hA hB
      cases h
      simp [trExpr, trExpr_untrExpr hA, trExpr_untrExpr hB]
    · cases h
  | .fvar _ _, _, h => by simp [untrExpr] at h
  | .letE _ _ _, _, h => by simp [untrExpr] at h
  | .lit _, _, h => by simp [untrExpr] at h
  | .proj _ _ _, _, h => by simp [untrExpr] at h

/-- Each constant's level parameter names, read from the checker's environment. -/
def lpOf (cenv : ConLeche.Env) (c : Lean.Name) : List ConLeche.Name :=
  match cenv.find? (trName c) with
  | some ci => ci.toConstantVal.levelParams
  | none => []

/-- What the generator has built: the environment, and the names and equations it put in. -/
structure Generated where
  env : VEnv
  names : List Lean.Name
  eqs : List VDefEq

/-- Add the checker's constant `ci`, if its type translates back and is typed at a sort. -/
def stepConst (cenv : ConLeche.Env) (g : Generated) (ci : ConLeche.ConstantInfo) :
    Option Generated :=
  if cenv.find? ci.name = some ci ∧ ci.toConstantVal.levelParams.Nodup then
    match untrExpr ci.toConstantVal.levelParams ci.toConstantVal.type with
    | some ty =>
      match inferType g.env ci.toConstantVal.levelParams.length [] ty with
      | some (.sort _) =>
        match g.env.addConst (untrName ci.name) ⟨ci.toConstantVal.levelParams.length, ty⟩ with
        | some env' => some ⟨env', untrName ci.name :: g.names, g.eqs⟩
        | none => none
      | _ => none
    | none => none
  else none

/-- Add the equation the checker's constant `ci` states, if its type is `@Eq T a b` with both
sides typed at `T`. -/
def stepEq (cenv : ConLeche.Env) (g : Generated) (ci : ConLeche.ConstantInfo) :
    Option Generated :=
  if ci ∈ cenv.consts ∧ ci.toConstantVal.levelParams.Nodup then
    match untrExpr ci.toConstantVal.levelParams ci.toConstantVal.type with
    | some (.app (.app (.app (.const c [u]) T) a) b) =>
      if c = untrName ConLeche.eqName ∧
          inferType g.env ci.toConstantVal.levelParams.length [] T = some (.sort u) ∧
          inferType g.env ci.toConstantVal.levelParams.length [] a = some T ∧
          inferType g.env ci.toConstantVal.levelParams.length [] b = some T then
        some ⟨g.env.addDefEq ⟨ci.toConstantVal.levelParams.length, a, b, T⟩, g.names,
          ⟨ci.toConstantVal.levelParams.length, a, b, T⟩ :: g.eqs⟩
      else none
    | _ => none
  else none

def step (cenv : ConLeche.Env) (g : Generated) (ci : ConLeche.ConstantInfo) : Generated :=
  let g₁ := (stepConst cenv g ci).getD g
  (stepEq cenv g₁ ci).getD g₁

/-- The generator's run over the checker's constants, oldest first. -/
def generated (cenv : ConLeche.Env) : Generated :=
  cenv.consts.reverse.foldl (step cenv) ⟨.empty, [], []⟩

/-- The Lean4Lean environment generated from the checker's environment. -/
def generate (cenv : ConLeche.Env) : VEnv := (generated cenv).env

/-- What the generator maintains: the environment is certified, and it holds the names and the
equations recorded beside it. -/
structure Generated.Good (cenv : ConLeche.Env) (g : Generated) : Prop where
  cert : CertOrdered cenv (lpOf cenv) g.env
  names : ∀ n ∈ g.names, (g.env.constants n).isSome
  eqs : ∀ df ∈ g.eqs, g.env.defeqs df

theorem stepConst_good {cenv : ConLeche.Env} {g g' : Generated} {ci : ConLeche.ConstantInfo}
    (hg : g.Good cenv) (h : stepConst cenv g ci = some g') : g'.Good cenv := by
  unfold stepConst at h
  split at h
  · rename_i hc
    obtain ⟨hfind, hnd⟩ := hc
    split at h
    · rename_i ty hty
      split at h
      · rename_i u hinf
        split at h
        · rename_i env' hadd
          cases h
          have hmem : ci ∈ cenv.consts := by
            unfold ConLeche.Env.find? at hfind
            exact List.mem_of_find?_eq_some hfind
          have hlp : lpOf cenv (untrName ci.name) = ci.toConstantVal.levelParams := by
            simp [lpOf, trName_untrName, hfind]
          have hconst : env'.constants =
              fun m => if untrName ci.name = m then
                some ⟨ci.toConstantVal.levelParams.length, ty⟩ else g.env.constants m := by
            unfold VEnv.addConst at hadd
            split at hadd
            · cases hadd
            · cases hadd; rfl
          have hdefeqs : env'.defeqs = g.env.defeqs := by
            unfold VEnv.addConst at hadd
            split at hadd
            · cases hadd
            · cases hadd; rfl
          refine ⟨?_, ?_, ?_⟩
          · refine .const hg.cert ⟨u, inferType_sound hinf⟩ hadd ?_
            refine ⟨ci, hmem, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · rw [trName_untrName]; exact hfind
            · rw [trName_untrName]
            · exact hlp.symm
            · rw [hlp]; exact hnd
            · rw [hlp]
            · rw [hlp]; exact (trExpr_untrExpr hty).symm
          · intro n hn
            rw [hconst]
            simp only
            split
            · rfl
            · cases hn with
              | head => contradiction
              | tail _ hn => exact hg.names n hn
          · intro df hdf
            rw [hdefeqs]
            exact hg.eqs df hdf
        · cases h
      · cases h
    · cases h
  · cases h

theorem stepEq_good {cenv : ConLeche.Env} {g g' : Generated} {ci : ConLeche.ConstantInfo}
    (hg : g.Good cenv) (h : stepEq cenv g ci = some g') : g'.Good cenv := by
  unfold stepEq at h
  split at h
  · rename_i hc
    obtain ⟨hmem, hnd⟩ := hc
    split at h
    · rename_i c u T a b hty
      split at h
      · rename_i hcond
        obtain ⟨hc, hT, ha, hb⟩ := hcond
        cases h
        refine ⟨?_, ?_, ?_⟩
        · refine .defeq (u := u) hg.cert ⟨inferType_sound ha, inferType_sound hb⟩
            (inferType_sound hT) ⟨ci, _, hmem, hnd, rfl, ?_⟩
          have := trExpr_untrExpr hty
          subst hc
          simpa [trExpr, eqExpr, trName_untrName] using this.symm
        · intro n hn
          exact hg.names n hn
        · intro df hdf
          cases hdf with
          | head => exact Or.inl rfl
          | tail _ hdf => exact Or.inr (hg.eqs df hdf)
      · cases h
    · cases h
  · cases h

theorem step_good {cenv : ConLeche.Env} {g : Generated} (ci : ConLeche.ConstantInfo)
    (hg : g.Good cenv) : (step cenv g ci).Good cenv := by
  have h1 : ((stepConst cenv g ci).getD g).Good cenv := by
    cases h : stepConst cenv g ci with
    | none => exact hg
    | some g' => exact stepConst_good hg h
  have h2 : ∀ g₁ : Generated, g₁.Good cenv → ((stepEq cenv g₁ ci).getD g₁).Good cenv := by
    intro g₁ hg₁
    cases h : stepEq cenv g₁ ci with
    | none => exact hg₁
    | some g' => exact stepEq_good hg₁ h
  exact h2 _ h1

theorem generated_good (cenv : ConLeche.Env) : (generated cenv).Good cenv := by
  have key : ∀ (l : List ConLeche.ConstantInfo) (g : Generated), g.Good cenv →
      (l.foldl (step cenv) g).Good cenv := by
    intro l
    induction l with
    | nil => exact fun _ h => h
    | cons ci l ih => exact fun g h => ih _ (step_good ci h)
  exact key _ _ ⟨.empty, (fun _ h => by cases h), (fun _ h => by cases h)⟩

/-- The generated environment is certified against the checker's environment. -/
theorem generate_certOrdered (cenv : ConLeche.Env) :
    CertOrdered cenv (lpOf cenv) (generate cenv) :=
  (generated_good cenv).cert

universe w

/-- If Con-Leche's checker accepts the declarations `ds`, giving `cenv`, the Lean4Lean environment
generated from `cenv` types no closed term at `∀ (p : Prop), p`, in any model of the set theory. -/
theorem generated_consistent (V : Type w) [ConLeche.SetTheory V]
    (pins : List ConLeche.NatOpPinSet) (maxNatSize : Nat) (ds : Array ConLeche.Declaration)
    {cenv : ConLeche.Env}
    (accepted : ConLeche.Cached.checkDecls .verified pins maxNatSize ds = .ok cenv) {U : Nat} :
    ¬ ∃ e, (generate cenv).HasType U [] e falseE :=
  checked_consistent V pins maxNatSize ds accepted (generate_certOrdered cenv)

end Lean4Zfc
