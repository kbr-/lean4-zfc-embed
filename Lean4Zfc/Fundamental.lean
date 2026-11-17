import Lean4Zfc.Interp

/-!
The fundamental theorem for Lean4Lean's judgement in a value-directed set interpretation.

No use is made of unique typing, sort inversion or strengthening: the induction is over
`IsDefEqStrong`, which Lean4Lean derives from `IsDefEq` for an ordered environment.
-/

namespace Lean4Zfc

open Lean4Lean ConLeche ConLeche.SetTheory ConLeche.SetModel

universe w

variable {V : Type w} [SetTheory V]

/-- A model of an environment: each constant's value lies in its type's denotation, and each
stored equation holds, at every level valuation and variable environment. -/
structure EnvModel (env : VEnv) (cval : Name → List Nat → V) : Prop where
  const : ∀ {c ci}, env.constants c = some ci → ∀ (L : List Nat) (ρ : Nat → V),
    cval c L ∈ˢ interp cval L ρ ci.type
  defeq : ∀ {df}, env.defeqs df → ∀ (L : List Nat) (ρ : Nat → V),
    interp cval L ρ df.lhs = interp cval L ρ df.rhs ∧
      interp cval L ρ df.lhs ∈ˢ interp cval L ρ df.type

/-- The variable environment `ρ` satisfies the context `Γ`. -/
def Sat (cval : Name → List Nat → V) (L : List Nat) : List VExpr → (Nat → V) → Prop
  | [], _ => True
  | A :: Γ, ρ => ρ 0 ∈ˢ interp cval L (fun i => ρ (i + 1)) A ∧ Sat cval L Γ (fun i => ρ (i + 1))

variable {cval : Name → List Nat → V} {L : List Nat}

theorem Sat.push {Γ : List VExpr} {ρ : Nat → V} {A : VExpr} {x : V}
    (h : Sat cval L Γ ρ) (hx : x ∈ˢ interp cval L ρ A) : Sat cval L (A :: Γ) (push x ρ) :=
  ⟨hx, h⟩

theorem Sat.lookup {Γ : List VExpr} {ρ : Nat → V} {i : Nat} {A : VExpr}
    (h : Sat cval L Γ ρ) (hl : Lookup Γ i A) : ρ i ∈ˢ interp cval L ρ A := by
  induction hl generalizing ρ with
  | zero =>
    rw [VExpr.lift, interp_liftN]
    simpa using h.1
  | succ _ ih =>
    rw [VExpr.lift, interp_liftN]
    simpa using ih h.2

theorem map_eval_congr {ls ls' : List VLevel} (h : List.Forall₂ (· ≈ ·) ls ls') :
    ls.map (VLevel.eval L) = ls'.map (VLevel.eval L) := by
  induction h with
  | nil => rfl
  | cons h _ ih => simp [ih, VLevel.equiv_def.1 h L]

theorem fundamental {env : VEnv} {U : Nat} {Γ : List VExpr} {e e' A : VExpr}
    (M : EnvModel env cval) (H : env.IsDefEqStrong U Γ e e' A) :
    ∀ (L : List Nat) (ρ : Nat → V), Sat cval L Γ ρ →
      interp cval L ρ e = interp cval L ρ e' ∧ interp cval L ρ e ∈ˢ interp cval L ρ A := by
  induction H with
  | bvar hl _ _ _ => intro L ρ hρ; exact ⟨rfl, hρ.lookup hl⟩
  | symm _ ih =>
    intro L ρ hρ
    obtain ⟨h1, h2⟩ := ih L ρ hρ
    exact ⟨h1.symm, h1 ▸ h2⟩
  | trans _ _ ih1 ih2 =>
    intro L ρ hρ
    obtain ⟨h1, h2⟩ := ih1 L ρ hρ
    obtain ⟨h3, _⟩ := ih2 L ρ hρ
    exact ⟨h1.trans h3, h2⟩
  | sortDF _ _ h =>
    intro L ρ _
    have := VLevel.equiv_def.1 h L
    refine ⟨by simp [interp, this], ?_⟩
    simp only [interp, VLevel.eval]
    exact univ_mem_univ _
  | constDF hc _ _ _ hls _ _ _ _ _ =>
    intro L ρ _
    refine ⟨by simp [interp, map_eval_congr hls], ?_⟩
    rw [interp_instL]
    exact M.const hc _ _
  | appDF _ _ _ _ _ _ _ _ _ ihf iha _ =>
    intro L ρ hρ
    obtain ⟨hf, hfm⟩ := ihf L ρ hρ
    obtain ⟨ha, ham⟩ := iha L ρ hρ
    refine ⟨by simp [interp, hf, ha], ?_⟩
    rw [interp_inst0]
    exact app_mem_piV hfm ham
  | lamDF _ _ _ _ _ _ _ ihA ihB _ ihb _ =>
    intro L ρ hρ
    obtain ⟨hA, _⟩ := ihA L ρ hρ
    have hb := fun x (hx : x ∈ˢ interp cval L ρ _) => ihb L (push x ρ) (hρ.push hx)
    have hB := fun x (hx : x ∈ˢ interp cval L ρ _) => (ihB L (push x ρ) (hρ.push hx)).2
    refine ⟨?_, ?_⟩
    · simp only [interp]
      rw [← hA]
      exact lamV_congr fun x hx => (hb x hx).1
    · simp only [interp]
      exact lamV_mem (fun x hx => (hb x hx).2) (fun x hx => IsTy_of_mem_univ (hB x hx))
  | forallEDF _ _ _ _ _ ihA ihb _ =>
    intro L ρ hρ
    obtain ⟨hA, hAm⟩ := ihA L ρ hρ
    have hb := fun x (hx : x ∈ˢ interp cval L ρ _) => ihb L (push x ρ) (hρ.push hx)
    refine ⟨?_, ?_⟩
    · simp only [interp]
      rw [← hA]
      exact piV_congr fun x hx => (hb x hx).1
    · simp only [interp, VLevel.eval, Lean.Nat.imax]
      exact piV_mem_univ hAm (fun x hx => (hb x hx).2)
  | defeqDF _ _ _ ihAB ihe =>
    intro L ρ hρ
    obtain ⟨hAB, _⟩ := ihAB L ρ hρ
    obtain ⟨h1, h2⟩ := ihe L ρ hρ
    exact ⟨h1, hAB ▸ h2⟩
  | beta _ _ _ _ _ _ _ _ _ _ _ ihe' _ ihee =>
    intro L ρ hρ
    obtain ⟨_, he'm⟩ := ihe' L ρ hρ
    obtain ⟨_, hm⟩ := ihee L ρ hρ
    refine ⟨?_, ?_⟩
    · simp only [interp]
      rw [app_lamV he'm, interp_inst0]
    · simp only [interp]
      rw [app_lamV he'm, ← interp_inst0]
      exact hm
  | eta _ _ _ _ _ _ _ _ _ ihB _ ihe _ _ =>
    intro L ρ hρ
    obtain ⟨_, hem⟩ := ihe L ρ hρ
    have hB := fun x (hx : x ∈ˢ interp cval L ρ _) =>
      IsTy_of_mem_univ (ihB L (push x ρ) (hρ.push hx)).2
    simp only [interp] at hem
    refine ⟨?_, ?_⟩
    · simp only [interp, interp_lift, push]
      exact lamV_eta hem hB
    · simp only [interp, interp_lift, push]
      rw [lamV_eta hem hB]
      exact hem
  | proofIrrel _ _ _ ihp ihh ihh' =>
    intro L ρ hρ
    have hp := (ihp L ρ hρ).2
    simp only [interp, VLevel.eval] at hp
    exact ⟨(mem_univ_zero hp (ihh L ρ hρ).2).trans (mem_univ_zero hp (ihh' L ρ hρ).2).symm,
      (ihh L ρ hρ).2⟩
  | extra hdf _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    intro L ρ _
    rw [interp_instL, interp_instL, interp_instL]
    exact M.defeq hdf _ _

/-- `∀ (p : Prop), p`. -/
def falseE : VExpr := .forallE (.sort .zero) (.bvar 0)

theorem interp_falseE_empty (ρ : Nat → V) (y : V) : ¬ y ∈ˢ interp cval L ρ falseE := by
  intro hy
  simp only [falseE, interp, VLevel.eval, push] at hy
  exact not_mem_empty _ (app_mem_piV hy (empty_mem_univ 0))

/-- An ordered environment with a model types no closed term at `∀ (p : Prop), p`. -/
theorem no_proof_of_false {env : VEnv} {U : Nat} (henv : env.Ordered) (M : EnvModel env cval) :
    ¬ ∃ e, env.HasType U [] e falseE := by
  rintro ⟨e, he⟩
  have H := VEnv.IsDefEq.strong henv (Γ := []) trivial he
  exact interp_falseE_empty (L := []) (fun _ => (empty : V)) _ (fundamental M H [] _ trivial).2

/-- The hypotheses are satisfiable: the empty environment has a model, under any `cval`. -/
theorem envModel_empty : EnvModel (V := V) VEnv.empty cval where
  const h := nomatch h
  defeq h := False.elim h

/-- The empty environment types no closed term at `∀ (p : Prop), p`, in any set theory. -/
theorem empty_consistent (V : Type w) [SetTheory V] {U : Nat} :
    ¬ ∃ e, VEnv.empty.HasType U [] e falseE :=
  no_proof_of_false (cval := fun _ _ => (empty : V)) .empty envModel_empty

end Lean4Zfc
