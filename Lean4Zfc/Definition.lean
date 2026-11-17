import Lean4Zfc.Fundamental
import Lean4Lean.Theory.VDecl

/-!
A definition step extends a model of the environment.
-/

namespace Lean4Zfc

open Lean4Lean ConLeche ConLeche.SetTheory ConLeche.SetModel

universe w

variable {V : Type w} [SetTheory V]

/-- Every constant the term mentions is defined in the environment. -/
def ConstsIn (env : VEnv) : VExpr → Prop
  | .bvar _ => True
  | .sort _ => True
  | .const c ls => ∃ ci, env.constants c = some ci ∧ ls.length = ci.uvars
  | .app f a => ConstsIn env f ∧ ConstsIn env a
  | .lam A b => ConstsIn env A ∧ ConstsIn env b
  | .forallE A B => ConstsIn env A ∧ ConstsIn env B

theorem ConstsIn.mono {env env' : VEnv} (h : env ≤ env') {e : VExpr} :
    ConstsIn env e → ConstsIn env' e := by
  induction e with
  | bvar _ => exact id
  | sort _ => exact id
  | const c _ => exact fun ⟨ci, hc, hl⟩ => ⟨ci, h.1 hc, hl⟩
  | app f a ihf iha => exact fun ⟨h1, h2⟩ => ⟨ihf h1, iha h2⟩
  | lam A b ihA ihb => exact fun ⟨h1, h2⟩ => ⟨ihA h1, ihb h2⟩
  | forallE A B ihA ihB => exact fun ⟨h1, h2⟩ => ⟨ihA h1, ihB h2⟩

theorem ConstsIn.liftN {env : VEnv} {e : VExpr} {n k : Nat} (h : ConstsIn env e) :
    ConstsIn env (e.liftN n k) := by
  induction e generalizing k with
  | bvar _ => trivial
  | sort _ => trivial
  | const c _ => exact h
  | app f a ihf iha => exact ⟨ihf h.1, iha h.2⟩
  | lam A b ihA ihb => exact ⟨ihA h.1, ihb h.2⟩
  | forallE A B ihA ihB => exact ⟨ihA h.1, ihB h.2⟩

theorem ConstsIn.instL {env : VEnv} {e : VExpr} {ls : List VLevel} (h : ConstsIn env e) :
    ConstsIn env (e.instL ls) := by
  induction e with
  | bvar _ => trivial
  | sort _ => trivial
  | const c us =>
    obtain ⟨ci, hc, hl⟩ := h
    exact ⟨ci, hc, by simpa using hl⟩
  | app f a ihf iha => exact ⟨ihf h.1, iha h.2⟩
  | lam A b ihA ihb => exact ⟨ihA h.1, ihb h.2⟩
  | forallE A B ihA ihB => exact ⟨ihA h.1, ihB h.2⟩

theorem ConstsIn.inst {env : VEnv} {e a : VExpr} {k : Nat} (h : ConstsIn env e)
    (ha : ConstsIn env a) : ConstsIn env (e.inst a k) := by
  induction e generalizing k with
  | bvar i =>
    simp only [VExpr.inst, VExpr.instVar]
    split
    · trivial
    · split
      · exact ha.liftN
      · trivial
  | sort _ => trivial
  | const c _ => exact h
  | app f b ihf ihb => exact ⟨ihf h.1, ihb h.2⟩
  | lam A b ihA ihb => exact ⟨ihA h.1, ihb h.2⟩
  | forallE A B ihA ihB => exact ⟨ihA h.1, ihB h.2⟩

theorem ConstsIn.lookup {env : VEnv} {Γ : List VExpr} {i : Nat} {A : VExpr}
    (hl : Lookup Γ i A) (hΓ : ∀ B ∈ Γ, ConstsIn env B) : ConstsIn env A := by
  induction hl with
  | zero => exact (hΓ _ (List.mem_cons_self ..)).liftN
  | succ _ ih => exact (ih fun B hB => hΓ B (List.mem_cons_of_mem _ hB)).liftN

theorem ctx_cons {env : VEnv} {Γ : List VExpr} {A : VExpr} (hA : ConstsIn env A)
    (hΓ : ∀ B ∈ Γ, ConstsIn env B) : ∀ B ∈ A :: Γ, ConstsIn env B := by
  intro B hB
  rcases List.mem_cons.1 hB with rfl | hB
  · exact hA
  · exact hΓ B hB

/-- A derivation mentions only defined constants, given that the environment's own types do. -/
theorem constsIn_of_isDefEq {env : VEnv} {U : Nat} {Γ : List VExpr} {e1 e2 A : VExpr}
    (hT : env.OnTypes fun _ e A => ConstsIn env e ∧ ConstsIn env A)
    (H : env.IsDefEq U Γ e1 e2 A) (hΓ : ∀ B ∈ Γ, ConstsIn env B) :
    ConstsIn env e1 ∧ ConstsIn env e2 ∧ ConstsIn env A := by
  induction H with
  | bvar hl => exact ⟨trivial, trivial, ConstsIn.lookup hl hΓ⟩
  | symm _ ih => exact ⟨(ih hΓ).2.1, (ih hΓ).1, (ih hΓ).2.2⟩
  | trans _ _ ih1 ih2 => exact ⟨(ih1 hΓ).1, (ih2 hΓ).2.1, (ih1 hΓ).2.2⟩
  | sortDF _ _ _ => exact ⟨trivial, trivial, trivial⟩
  | constDF hc _ _ hlen hls =>
    obtain ⟨_, h, _⟩ := hT.1 hc
    exact ⟨⟨_, hc, hlen⟩, ⟨_, hc, hls.length_eq ▸ hlen⟩, h.instL⟩
  | appDF _ _ ihf iha =>
    exact ⟨⟨(ihf hΓ).1, (iha hΓ).1⟩, ⟨(ihf hΓ).2.1, (iha hΓ).2.1⟩,
      (ihf hΓ).2.2.2.inst (iha hΓ).1⟩
  | lamDF _ _ ihA ihb =>
    have hb := ihb (ctx_cons (ihA hΓ).1 hΓ)
    exact ⟨⟨(ihA hΓ).1, hb.1⟩, ⟨(ihA hΓ).2.1, hb.2.1⟩, ⟨(ihA hΓ).1, hb.2.2⟩⟩
  | forallEDF _ _ ihA ihb =>
    have hb := ihb (ctx_cons (ihA hΓ).1 hΓ)
    exact ⟨⟨(ihA hΓ).1, hb.1⟩, ⟨(ihA hΓ).2.1, hb.2.1⟩, trivial⟩
  | defeqDF _ _ ihAB ihe => exact ⟨(ihe hΓ).1, (ihe hΓ).2.1, (ihAB hΓ).2.1⟩
  | beta _ _ ihe ihe' =>
    have ha := ihe' hΓ
    have hb := ihe (ctx_cons ha.2.2 hΓ)
    exact ⟨⟨⟨ha.2.2, hb.1⟩, ha.1⟩, hb.1.inst ha.1, hb.2.2.inst ha.1⟩
  | eta _ ihe =>
    have he := ihe hΓ
    exact ⟨⟨he.2.2.1, he.1.liftN, trivial⟩, he.1, he.2.2⟩
  | proofIrrel _ _ _ ihp ihh ihh' => exact ⟨(ihh hΓ).1, (ihh' hΓ).1, (ihp hΓ).1⟩
  | extra hdf _ _ =>
    obtain ⟨⟨h1, h2⟩, h3, _⟩ := hT.2 hdf
    exact ⟨h1.instL, h3.instL, h2.instL⟩

theorem Ordered.constsIn {env : VEnv} (H : env.Ordered) :
    env.OnTypes fun _ e A => ConstsIn env e ∧ ConstsIn env A :=
  H.induction (fun env _ e A => ConstsIn env e ∧ ConstsIn env A)
    (fun h => .imp (ConstsIn.mono h) (ConstsIn.mono h))
    (fun _ ih h =>
      have r := constsIn_of_isDefEq ih h (by simp)
      ⟨r.1, r.2.2⟩)

variable {cval cval' : Name → List Nat → V} {L L' : List Nat}

/-- `interp` reads `cval` only at the constants the term mentions. -/
theorem interp_congr_cval {env : VEnv} {e : VExpr}
    (h : ∀ c, (∃ ci, env.constants c = some ci) → cval c = cval' c) (he : ConstsIn env e)
    (ρ : Nat → V) : interp cval L ρ e = interp cval' L ρ e := by
  induction e generalizing ρ with
  | bvar _ => rfl
  | sort _ => rfl
  | const c ls =>
    obtain ⟨ci, hc, _⟩ := he
    simp only [interp]; rw [h c ⟨ci, hc⟩]
  | app f a ihf iha => simp only [interp]; rw [ihf he.1, iha he.2]
  | lam A b ihA ihb =>
    simp only [interp]; rw [ihA he.1]; congr 1; funext x; exact ihb he.2 _
  | forallE A B ihA ihB =>
    simp only [interp]; rw [ihA he.1]; congr 1; funext x; exact ihB he.2 _

/-- `interp` of a term closed above `k` reads the variable environment only below `k`. -/
theorem interp_closed {e : VExpr} {k : Nat} (h : e.ClosedN k) {ρ ρ' : Nat → V}
    (hρ : ∀ i, i < k → ρ i = ρ' i) : interp cval L ρ e = interp cval L ρ' e := by
  induction e generalizing k ρ ρ' with
  | bvar i => exact hρ i h
  | sort _ => rfl
  | const _ _ => rfl
  | app f a ihf iha => simp only [interp]; rw [ihf h.1 hρ, iha h.2 hρ]
  | lam A b ihA ihb =>
    simp only [interp]; rw [ihA h.1 hρ]; congr 1; funext x
    refine ihb h.2 fun i hi => ?_
    cases i with
    | zero => rfl
    | succ i => exact hρ i (Nat.lt_of_succ_lt_succ hi)
  | forallE A B ihA ihB =>
    simp only [interp]; rw [ihA h.1 hρ]; congr 1; funext x
    refine ihB h.2 fun i hi => ?_
    cases i with
    | zero => rfl
    | succ i => exact hρ i (Nat.lt_of_succ_lt_succ hi)

theorem eval_congr_WF {l : VLevel} {U : Nat} (h : l.WF U)
    (hL : ∀ i, i < U → L.getD i 0 = L'.getD i 0) : l.eval L = l.eval L' := by
  induction l with
  | zero => rfl
  | succ l ih => simp only [VLevel.eval]; rw [ih h]
  | max a b iha ihb => simp only [VLevel.eval]; rw [iha h.1, ihb h.2]
  | imax a b iha ihb => simp only [VLevel.eval]; rw [iha h.1, ihb h.2]
  | param i => exact hL i h

/-- `interp` of a term whose levels are well-formed at `U` reads only the first `U` level values. -/
theorem interp_levelWF {e : VExpr} {U : Nat} (h : e.LevelWF U)
    (hL : ∀ i, i < U → L.getD i 0 = L'.getD i 0) (ρ : Nat → V) :
    interp cval L ρ e = interp cval L' ρ e := by
  induction e generalizing ρ with
  | bvar _ => rfl
  | sort u => simp only [interp]; rw [eval_congr_WF h hL]
  | const c ls =>
    simp only [interp]
    congr 1
    exact List.map_congr_left fun l hl => eval_congr_WF (h l hl) hL
  | app f a ihf iha => simp only [interp]; rw [ihf h.1, iha h.2]
  | lam A b ihA ihb => simp only [interp]; rw [ihA h.1]; congr 1; funext x; exact ihb h.2 _
  | forallE A B ihA ihB => simp only [interp]; rw [ihA h.1]; congr 1; funext x; exact ihB h.2 _

theorem params_eval_getD (U : Nat) (L : List Nat) (i : Nat) (hi : i < U) :
    L.getD i 0 = ((VLevel.params U).map (VLevel.eval L)).getD i 0 := by
  simp [VLevel.params, VLevel.eval, List.getD, hi]

/-- A definition step extends a model: the new constant denotes its value, and the constants
already defined keep theirs. -/
theorem EnvModel.addDef {env env' : VEnv} (henv : env.Ordered) (M : EnvModel env cval)
    {ci : VDefVal} (hv : env.HasType ci.uvars [] ci.value ci.type)
    (hadd : env.addConst ci.name ci.toVConstant = some env') :
    ∃ cval' : Name → List Nat → V, EnvModel (env'.addDefEq ci.toDefEq) cval' ∧
      ∀ c, (∃ c', env.constants c = some c') → cval c = cval' c := by
  classical
  let ρ0 : Nat → V := fun _ => empty
  let cval' : Name → List Nat → V := fun n L =>
    if n = ci.name then interp cval L ρ0 ci.value else cval n L
  have hfresh : env.constants ci.name = none := by
    unfold VEnv.addConst at hadd; split at hadd <;> simp_all
  have hagree : ∀ c, (∃ c', env.constants c = some c') → cval c = cval' c := by
    rintro c ⟨c', hc⟩
    have hne : c ≠ ci.name := by rintro rfl; rw [hfresh] at hc; cases hc
    funext L; simp [cval', hne]
  have hT := Ordered.constsIn henv
  have hcv := constsIn_of_isDefEq hT hv (by simp)
  have hcl := VEnv.IsDefEq.closedN' henv.closed hv trivial
  have hlv := VEnv.IsDefEq.levelWF hv trivial
  have hnil : ∀ i, i < 0 → ρ0 i = (fun _ => (empty : V)) i := fun i hi => absurd hi (Nat.not_lt_zero i)
  have hmem : ∀ L (ρ : Nat → V), interp cval L ρ0 ci.value ∈ˢ interp cval L ρ ci.type := by
    intro L ρ
    have H := VEnv.IsDefEq.strong henv (Γ := []) trivial hv
    have h := (fundamental M H L ρ0 trivial).2
    rwa [interp_closed hcl.2.2 (ρ := ρ0) (ρ' := ρ)
      (fun i hi => absurd hi (Nat.not_lt_zero i))] at h
  have henv' : env'.constants = fun n => if ci.name = n then some ci.toVConstant else env.constants n := by
    unfold VEnv.addConst at hadd; rw [hfresh] at hadd; cases hadd; rfl
  have hdefeqs : env'.defeqs = env.defeqs := by
    unfold VEnv.addConst at hadd; rw [hfresh] at hadd; cases hadd; rfl
  refine ⟨cval', ⟨?_, ?_⟩, hagree⟩
  · intro c ci' hc L ρ
    have hc' : env'.constants c = some ci' := hc
    rw [henv'] at hc'
    by_cases hn : ci.name = c
    · subst hn
      simp at hc'
      subst hc'
      show (if ci.name = ci.name then _ else _) ∈ˢ _
      rw [ite_eq_left rfl, ← interp_congr_cval hagree hcv.2.2]
      exact hmem L ρ
    · simp [hn] at hc'
      have hne : c ≠ ci.name := fun h => hn h.symm
      obtain ⟨_, h, _⟩ := hT.1 hc'
      show (if c = ci.name then _ else _) ∈ˢ _
      rw [ite_eq_right hne, ← interp_congr_cval hagree h]
      exact M.const hc' L ρ
  · intro df hdf L ρ
    rcases hdf with rfl | hdf
    · have e1 : interp cval' L ρ ci.value = interp cval L ρ0 ci.value := by
        rw [← interp_congr_cval hagree hcv.1]
        exact interp_closed hcl.1 (fun i hi => absurd hi (Nat.not_lt_zero i))
      have e2 : interp cval ((VLevel.params ci.uvars).map (VLevel.eval L)) ρ0 ci.value =
          interp cval L ρ0 ci.value :=
        (interp_levelWF hlv.1 (params_eval_getD _ L) ρ0).symm
      have hl : interp cval' L ρ (.const ci.name (VLevel.params ci.uvars)) =
          interp cval L ρ0 ci.value := by
        show (if ci.name = ci.name then _ else _) = _
        rw [ite_eq_left rfl]
        exact e2
      refine ⟨hl.trans e1.symm, ?_⟩
      show interp cval' L ρ (.const ci.name (VLevel.params ci.uvars)) ∈ˢ interp cval' L ρ ci.type
      rw [hl, ← interp_congr_cval hagree hcv.2.2]
      exact hmem L ρ
    · rw [hdefeqs] at hdf
      obtain ⟨⟨h1, h2⟩, h3, _⟩ := hT.2 hdf
      have h := M.defeq hdf L ρ
      rw [interp_congr_cval hagree h1, interp_congr_cval hagree h3,
        interp_congr_cval hagree h2] at h
      exact h

end Lean4Zfc
