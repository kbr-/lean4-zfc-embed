import Lean4Zfc.Definition
import ConLeche.Denotes

/-!
A Con-Leche model of a checked environment gives a model of a Lean4Lean environment it
certifies.

Lean4Lean's terms are translated into Con-Leche's, and Con-Leche's `Denotes` of a translated term
is `interp` of the term, with the constants' values read from the Con-Leche model.
Lean4Lean numbers a declaration's level parameters; Con-Leche names them. The translation of a
declaration takes the list `ps` of its parameter names, in order.
-/

namespace Lean4Zfc

open Lean4Lean ConLeche.SetTheory ConLeche.SetModel

universe w

variable {V : Type w} [ConLeche.SetTheory V]

/-- Lean's names as Con-Leche's. -/
def trName : Lean.Name → ConLeche.Name
  | .anonymous => .anonymous
  | .str p s => .str (trName p) s
  | .num p n => .num (trName p) n

/-- A level under the parameter names `ps`: parameter `i` is named `ps[i]`. -/
def trLevel (ps : List ConLeche.Name) : VLevel → ConLeche.Level
  | .zero => .zero
  | .succ l => .succ (trLevel ps l)
  | .max a b => .max (trLevel ps a) (trLevel ps b)
  | .imax a b => .imax (trLevel ps a) (trLevel ps b)
  | .param i => .param (ps.getD i .anonymous)

/-- The Con-Leche level assignment giving the parameter named `ps[i]` the value `L[i]`. -/
def assign : List ConLeche.Name → List Nat → ConLeche.Name → Nat
  | [], _, _ => 0
  | p :: ps, L, n => if p = n then L.headD 0 else assign ps L.tail n

theorem assign_getElem {ps : List ConLeche.Name} (hnd : ps.Nodup) (L : List Nat) {i : Nat}
    (hi : i < ps.length) : assign ps L (ps[i]) = L.getD i 0 := by
  induction ps generalizing L i with
  | nil => exact absurd hi (Nat.not_lt_zero _)
  | cons p ps ih =>
    obtain ⟨hp, hnd'⟩ := List.nodup_cons.1 hnd
    cases i with
    | zero => cases L <;> simp [assign]
    | succ i =>
      have hi' : i < ps.length := Nat.lt_of_succ_lt_succ hi
      have hne : p ≠ ps[i] := fun h => hp (h ▸ List.getElem_mem hi')
      simp only [List.getElem_cons_succ, assign, ite_eq_right hne]
      rw [ih hnd' L.tail hi']
      cases L <;> simp

/-- Substituting the levels `us` for the parameters `ps` reads the level at that position. -/
theorem substFn_getElem (φ : ConLeche.Name → Nat) {ps : List ConLeche.Name} (hnd : ps.Nodup)
    {us : List ConLeche.Level} (hlen : us.length = ps.length) {i : Nat} (hi : i < ps.length) :
    ConLeche.Level.substFn φ ps us (ps[i]) = ConLeche.Level.eval φ (us[i]'(hlen ▸ hi)) := by
  induction ps generalizing us i with
  | nil => exact absurd hi (Nat.not_lt_zero _)
  | cons p ps ih =>
    obtain ⟨hp, hnd'⟩ := List.nodup_cons.1 hnd
    cases us with
    | nil => simp at hlen
    | cons u us =>
      cases i with
      | zero => simp [ConLeche.Level.substFn]
      | succ i =>
        have hi' : i < ps.length := Nat.lt_of_succ_lt_succ hi
        have hne : p ≠ ps[i] := fun h => hp (h ▸ List.getElem_mem hi')
        simp only [List.getElem_cons_succ, ConLeche.Level.substFn, ite_eq_right hne]
        exact ih hnd' (by simpa using hlen) hi'

theorem eval_trLevel {ps : List ConLeche.Name} (hnd : ps.Nodup) (L : List Nat) {l : VLevel}
    (hl : l.WF ps.length) :
    ConLeche.Level.eval (assign ps L) (trLevel ps l) = l.eval L := by
  induction l with
  | zero => rfl
  | succ l ih => simp [trLevel, ConLeche.Level.eval, VLevel.eval, ih hl]
  | max a b iha ihb =>
    simp [trLevel, ConLeche.Level.eval, VLevel.eval, iha hl.1, ihb hl.2, Nat.max_def]
  | imax a b iha ihb =>
    simp [trLevel, ConLeche.Level.eval, VLevel.eval, iha hl.1, ihb hl.2, Lean.Nat.imax,
      Nat.max_def]
  | param i =>
    have hi : i < ps.length := hl
    simp only [trLevel, ConLeche.Level.eval, VLevel.eval]
    rw [show ps.getD i .anonymous = ps[i] by simp [List.getD, hi]]
    exact assign_getElem hnd L hi

def trExpr (ps : List ConLeche.Name) : VExpr → ConLeche.Expr
  | .bvar i => .bvar i
  | .sort u => .sort (trLevel ps u)
  | .const c ls => .const (trName c) (ls.map (trLevel ps))
  | .app f a => .app (trExpr ps f) (trExpr ps a)
  | .lam A b => .lam (trExpr ps A) (trExpr ps b)
  | .forallE A B => .forallE (trExpr ps A) (trExpr ps B)

/-- `e` is `e'` with some of its chains `Nat.succ (… Nat.zero)` written as `Nat` literals: the
form a translated term takes when the stored one holds literals, which Lean4Lean's terms lack. -/
inductive LitEq : ConLeche.Expr → ConLeche.Expr → Prop
  | refl (e : ConLeche.Expr) : LitEq e e
  | app {f f' a a' : ConLeche.Expr} : LitEq f f' → LitEq a a' → LitEq (.app f a) (.app f' a')
  | lam {A A' b b' : ConLeche.Expr} : LitEq A A' → LitEq b b' → LitEq (.lam A b) (.lam A' b')
  | forallE {A A' b b' : ConLeche.Expr} :
    LitEq A A' → LitEq b b' → LitEq (.forallE A b) (.forallE A' b')
  | natLit {n : Nat} {e' : ConLeche.Expr} :
    LitEq (ConLeche.natLitToConstructor n) e' → LitEq (.lit (.natVal n)) e'

/-- Related terms denote the same: Con-Leche reads a literal as its constructor form. -/
theorem LitEq.denotes {cval : ConLeche.Name → (ConLeche.Name → Nat) → V} {cenv : ConLeche.Env}
    {φ : ConLeche.Name → Nat} {e e' : ConLeche.Expr} (h : LitEq e e') :
    ∀ {ρ : Nat → V} {X : V}, ConLeche.Denotes cval cenv φ ρ e' X →
      ConLeche.Denotes cval cenv φ ρ e X := by
  induction h with
  | refl => exact id
  | app _ _ ihf iha =>
    intro ρ X hd
    cases hd with
    | app hf ha => exact .app (ihf hf) (iha ha)
  | lam _ _ ihA ihb =>
    intro ρ X hd
    cases hd with
    | lam hA hF => exact .lam (ihA hA) fun x hx => ihb (hF x hx)
  | forallE _ _ ihA ihb =>
    intro ρ X hd
    cases hd with
    | pi hA hB => exact .pi (ihA hA) fun x hx => ihb (hB x hx)
  | natLit _ ih =>
    intro ρ X hd
    exact .natLit (ih hd)

/-- The converse direction. -/
theorem LitEq.denotes_rev {cval : ConLeche.Name → (ConLeche.Name → Nat) → V}
    {cenv : ConLeche.Env} {φ : ConLeche.Name → Nat} {e e' : ConLeche.Expr} (h : LitEq e e') :
    ∀ {ρ : Nat → V} {X : V}, ConLeche.Denotes cval cenv φ ρ e X →
      ConLeche.Denotes cval cenv φ ρ e' X := by
  induction h with
  | refl => exact id
  | app _ _ ihf iha =>
    intro ρ X hd
    cases hd with
    | app hf ha => exact .app (ihf hf) (iha ha)
  | lam _ _ ihA ihb =>
    intro ρ X hd
    cases hd with
    | lam hA hF => exact .lam (ihA hA) fun x hx => ihb (hF x hx)
  | forallE _ _ ihA ihb =>
    intro ρ X hd
    cases hd with
    | pi hA hB => exact .pi (ihA hA) fun x hx => ihb (hB x hx)
  | natLit _ ih =>
    intro ρ X hd
    cases hd with
    | natLit h => exact ih h

omit [ConLeche.SetTheory V] in
theorem conLeche_push (x : V) (ρ : Nat → V) : ConLeche.push x ρ = push x ρ := by
  funext i
  cases i <;> rfl

variable {cenv : ConLeche.Env}

/-- The constants' values read from a Con-Leche model, where `lp c` lists the level parameter
names of the constant `c`. -/
def cvalOf (M : ConLeche.Model V cenv) (lp : Lean.Name → List ConLeche.Name) :
    Lean.Name → List Nat → V :=
  fun c L => M.cval (trName c) (assign (lp c) L)

/-- The Lean4Lean constant `c` is certified by a stored Con-Leche constant of the translated name
and type, whose level parameters are `lp c`: distinct names, as many as `c` has parameters. -/
def CertConst (cenv : ConLeche.Env) (lp : Lean.Name → List ConLeche.Name) (c : Lean.Name)
    (vc : VConstant) : Prop :=
  ∃ ci, ci ∈ cenv.consts ∧ cenv.find? (trName c) = some ci ∧ ci.name = trName c ∧
    ci.toConstantVal.levelParams = lp c ∧ (lp c).Nodup ∧ (lp c).length = vc.uvars ∧
    LitEq ci.toConstantVal.type (trExpr (lp c) vc.type)

/-- A constant's value reads only its own level parameters. -/
def ParamsOnly (M : ConLeche.Model V cenv) : Prop :=
  ∀ n ci, cenv.find? n = some ci → ∀ ψ₁ ψ₂ : ConLeche.Name → Nat,
    (∀ p ∈ ci.toConstantVal.levelParams, ψ₁ p = ψ₂ p) → M.cval n ψ₁ = M.cval n ψ₂

/-- Con-Leche's `Denotes` of a translated term is `interp` of the term. -/
theorem denotes_tr (M : ConLeche.Model V cenv) (hpar : ParamsOnly M)
    {lp : Lean.Name → List ConLeche.Name} {env : VEnv}
    (hcert : ∀ {c vc}, env.constants c = some vc → CertConst cenv lp c vc)
    {ps : List ConLeche.Name} (hnd : ps.Nodup)
    {e : VExpr} (he : ConstsIn env e) (hl : e.LevelWF ps.length) (L : List Nat) (ρ : Nat → V) :
    ConLeche.Denotes M.cval cenv (assign ps L) ρ (trExpr ps e) (interp (cvalOf M lp) L ρ e) := by
  induction e generalizing ρ with
  | bvar i => simp only [trExpr, interp]; exact .bvar
  | sort u => simp only [trExpr, interp]; rw [← eval_trLevel hnd L hl]; exact .sort
  | const c ls =>
    obtain ⟨vc, hc, hlen⟩ := he
    obtain ⟨ci, _, hf, _, hps, hqnd, hqlen, _⟩ := hcert hc
    have hlen' : (ls.map (trLevel ps)).length = (lp c).length := by
      rw [List.length_map, hlen, hqlen]
    have key : M.cval (trName c)
        (ConLeche.Level.substFn (assign ps L) ci.toConstantVal.levelParams
          (ls.map (trLevel ps))) =
        cvalOf M lp c (ls.map (VLevel.eval L)) := by
      refine hpar _ ci hf _ _ fun p hp => ?_
      rw [hps] at hp ⊢
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hp
      have hi' : i < ls.length := by rw [hlen, ← hqlen]; exact hi
      rw [substFn_getElem _ hqnd hlen' hi, assign_getElem hqnd _ hi]
      simp only [List.getElem_map]
      rw [eval_trLevel hnd L (hl _ (List.getElem_mem hi'))]
      simp [List.getD, hi']
    simp only [trExpr, interp]
    rw [← key]
    exact .const hf (hps ▸ hlen')
  | app f a ihf iha =>
    simp only [trExpr, interp]; exact .app (ihf he.1 hl.1 ρ) (iha he.2 hl.2 ρ)
  | lam A b ihA ihb =>
    simp only [trExpr, interp]
    exact .lam (ihA he.1 hl.1 ρ) (fun x _ => by rw [conLeche_push]; exact ihb he.2 hl.2 _)
  | forallE A B ihA ihB =>
    simp only [trExpr, interp]
    exact .pi (ihA he.1 hl.1 ρ) (fun x _ => by rw [conLeche_push]; exact ihB he.2 hl.2 _)

/-- `@Eq.{u} T a b` in Con-Leche's syntax, under the parameter names `ps`. -/
def eqExpr (ps : List ConLeche.Name) (u : VLevel) (T a b : VExpr) : ConLeche.Expr :=
  .app (.app (.app (.const ConLeche.eqName [trLevel ps u]) (trExpr ps T)) (trExpr ps a))
    (trExpr ps b)

/-- The level parameters `0, …, n - 1`, a constant's own. -/
def params (n : Nat) : List VLevel := (List.range n).map .param

theorem params_eval (L : List Nat) {n i : Nat} (hi : i < n) :
    ((params n).map (VLevel.eval L)).getD i 0 = L.getD i 0 := by
  simp [params, List.getD, hi, VLevel.eval]

/-- The equation `c ≡ v : A` unfolding the constant `c`, taken at its own level parameters. -/
def unfoldEq (c : Lean.Name) (vc : VConstant) (v : VExpr) : VDefEq :=
  ⟨vc.uvars, .const c (params vc.uvars), v, vc.type⟩

/-- A stored definition's value denotes the definition's own value. Con-Leche's `Model` does not
state this; `Checked.lean` proves it of the model read off the checker's invariant. -/
def DefnLaw (M : ConLeche.Model V cenv) : Prop :=
  ∀ cv value hint, ConLeche.ConstantInfo.defnInfo cv value hint ∈ cenv.consts →
    ∀ (φ : ConLeche.Name → Nat) (ρ : Nat → V),
      ConLeche.Denotes M.cval cenv φ ρ value (M.cval cv.name φ)

/-- A Lean4Lean environment built step by step, each constant certified by a stored Con-Leche
constant, each stored equation by a stored constant whose type is the equation, and each
unfolding of a constant by a stored definition of its name whose value is the translated
right-hand side. -/
inductive CertOrdered (cenv : ConLeche.Env) (lp : Lean.Name → List ConLeche.Name) :
    VEnv → Prop where
  | delta {env : VEnv} {c : Lean.Name} {vc : VConstant} {v : VExpr} :
    CertOrdered cenv lp env → env.constants c = some vc → (unfoldEq c vc v).WF env →
    (∃ cv value hint, ConLeche.ConstantInfo.defnInfo cv value hint ∈ cenv.consts ∧
      cv.name = trName c ∧ LitEq value (trExpr (lp c) v)) →
    CertOrdered cenv lp (env.addDefEq (unfoldEq c vc v))
  | empty : CertOrdered cenv lp .empty
  | const {env env' : VEnv} {n : Lean.Name} {ci : VConstant} :
    CertOrdered cenv lp env → ci.WF env → env.addConst n ci = some env' →
    CertConst cenv lp n ci → CertOrdered cenv lp env'
  | defeq {env : VEnv} {df : VDefEq} {u : VLevel} :
    CertOrdered cenv lp env → df.WF env → env.HasType df.uvars [] df.type (.sort u) →
    (∃ ci ps, ci ∈ cenv.consts ∧ ps.Nodup ∧ ps.length = df.uvars ∧
      LitEq ci.toConstantVal.type (eqExpr ps u df.type df.lhs df.rhs)) →
    CertOrdered cenv lp (env.addDefEq df)

variable {lp : Lean.Name → List ConLeche.Name}

theorem CertOrdered.ordered {env : VEnv} (h : CertOrdered cenv lp env) : env.Ordered := by
  induction h with
  | empty => exact .empty
  | const _ h1 h2 _ ih => exact .const ih h1 h2
  | defeq _ h1 _ _ ih => exact .defeq ih h1
  | delta _ _ h1 _ ih => exact .defeq ih h1

theorem CertOrdered.certConst {env : VEnv} (h : CertOrdered cenv lp env) :
    ∀ {c vc}, env.constants c = some vc → CertConst cenv lp c vc := by
  induction h with
  | empty => intro c vc hc; cases hc
  | @const env env' n ci _ _ hadd hcc ih =>
    intro c vc hc
    unfold VEnv.addConst at hadd
    split at hadd
    · cases hadd
    · cases hadd
      simp only at hc
      split at hc
      · rename_i hn
        subst hn
        cases hc
        exact hcc
      · exact ih hc
  | defeq _ _ _ _ ih => intro c vc hc; exact ih hc
  | delta _ _ _ _ ih => intro c vc hc; exact ih hc

/-- The constants of a certified environment take values in their types' denotations. -/
theorem CertOrdered.constMem {env : VEnv} (h : CertOrdered cenv lp env)
    (M : ConLeche.Model V cenv) (hpar : ParamsOnly M) {c : Lean.Name} {vc : VConstant}
    (hc : env.constants c = some vc) (L : List Nat) (ρ : Nat → V) :
    cvalOf M lp c L ∈ˢ interp (cvalOf M lp) L ρ vc.type := by
  obtain ⟨ci, hmem, _, hname, _, hnd, hlen, hty⟩ := h.certConst hc
  obtain ⟨T, hT, hin⟩ := M.mem ci hmem (assign (lp c) L) ρ
  obtain ⟨_, hC, _⟩ := (Ordered.constsIn h.ordered).1 hc
  obtain ⟨_, hty'⟩ := h.ordered.constWF hc
  have hlw : vc.type.LevelWF (lp c).length := hlen ▸ (VEnv.IsDefEq.levelWF hty' trivial).1
  have := ConLeche.Denotes_functional hT
    (hty.denotes (denotes_tr M hpar h.certConst hnd hC hlw L ρ))
  subst this
  rw [hname] at hin
  exact hin

theorem CertOrdered.envModel {env : VEnv} (h : CertOrdered cenv lp env)
    (M : ConLeche.Model V cenv) (hpar : ParamsOnly M) (hdl : DefnLaw M) :
    EnvModel env (cvalOf M lp) := by
  refine ⟨fun hc L ρ => h.constMem M hpar hc L ρ, ?_⟩
  induction h with
  | @delta env c vc v hprev hc hwf hcert ih =>
    intro df' hdf L ρ
    rcases hdf with rfl | hdf
    · have hord := hprev.ordered
      have Mprev : EnvModel env (cvalOf M lp) :=
        ⟨fun hc L ρ => hprev.constMem M hpar hc L ρ, ih⟩
      have ha := (fundamental Mprev (VEnv.IsDefEq.strong hord (Γ := []) trivial hwf.1) L ρ trivial).2
      have hT2 := constsIn_of_isDefEq (Ordered.constsIn hord) hwf.2 (by simp)
      have hL2 := VEnv.IsDefEq.levelWF hwf.2 trivial
      obtain ⟨ci, _, hf, _, hps, hnd, hlen, _⟩ := hprev.certConst hc
      obtain ⟨cv, value, hint, hmemd, hcvn, hlit⟩ := hcert
      have hlw : v.LevelWF (lp c).length := hlen ▸ hL2.1
      have hd1 := hdl cv value hint hmemd (assign (lp c) L) ρ
      have hd2 : ConLeche.Denotes M.cval cenv (assign (lp c) L) ρ value
          (interp (cvalOf M lp) L ρ v) :=
        hlit.denotes (denotes_tr M hpar hprev.certConst hnd hT2.1 hlw L ρ)
      have e1 : M.cval cv.name (assign (lp c) L) = interp (cvalOf M lp) L ρ v := by
        first
          | exact ConLeche.Denotes_functional hd1 hd2
          | exact (ConLeche.Denotes_functional hd2 hd1).symm
      refine ⟨?_, ha⟩
      show interp (cvalOf M lp) L ρ (.const c (params vc.uvars)) = interp (cvalOf M lp) L ρ v
      rw [← e1, hcvn]
      simp only [interp]
      refine hpar _ ci hf _ _ fun p hp => ?_
      rw [hps] at hp
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hp
      rw [assign_getElem hnd _ hi, assign_getElem hnd _ hi]
      exact params_eval L (hlen ▸ hi)
    · exact ih hdf L ρ
  | empty => intro df hdf; exact hdf.elim
  | @const env env' n ci _ _ hadd _ ih =>
    intro df hdf L ρ
    have : env'.defeqs = env.defeqs := by
      unfold VEnv.addConst at hadd; split at hadd <;> cases hadd; rfl
    rw [this] at hdf
    exact ih hdf L ρ
  | @defeq env df u hprev hwf hT hcert ih =>
    intro df' hdf L ρ
    rcases hdf with rfl | hdf
    · have hord := hprev.ordered
      have Mprev : EnvModel env (cvalOf M lp) :=
        ⟨fun hc L ρ => hprev.constMem M hpar hc L ρ, ih⟩
      have ha := (fundamental Mprev (VEnv.IsDefEq.strong hord (Γ := []) trivial hwf.1) L ρ trivial).2
      have hb := (fundamental Mprev (VEnv.IsDefEq.strong hord (Γ := []) trivial hwf.2) L ρ trivial).2
      have hTm := (fundamental Mprev (VEnv.IsDefEq.strong hord (Γ := []) trivial hT) L ρ trivial).2
      have hT1 := constsIn_of_isDefEq (Ordered.constsIn hord) hwf.1 (by simp)
      have hT2 := constsIn_of_isDefEq (Ordered.constsIn hord) hwf.2 (by simp)
      have hL1 := VEnv.IsDefEq.levelWF hwf.1 trivial
      have hL2 := VEnv.IsDefEq.levelWF hwf.2 trivial
      have hLu := (VEnv.IsDefEq.levelWF hT trivial).2.2
      obtain ⟨ci, ps, hmem, hnd, hlen, hty⟩ := hcert
      rw [← hlen] at hL1 hL2 hLu
      simp only [interp] at hTm
      rw [← eval_trLevel hnd L hLu] at hTm
      obtain ⟨X, hX, hin⟩ := M.mem ci hmem (assign ps L) ρ
      replace hX := hty.denotes_rev hX
      unfold eqExpr at hX
      cases hX with
      | app hf3 hb' =>
        cases hf3 with
        | app hf2 ha' =>
          cases hf2 with
          | app hE hA' =>
            have eA := ConLeche.Denotes_functional hA'
              (denotes_tr M hpar hprev.certConst hnd hT1.2.2 hL1.2.2 L ρ)
            have ea := ConLeche.Denotes_functional ha'
              (denotes_tr M hpar hprev.certConst hnd hT1.1 hL1.1 L ρ)
            have eb := ConLeche.Denotes_functional hb'
              (denotes_tr M hpar hprev.certConst hnd hT2.1 hL2.1 L ρ)
            subst eA ea eb
            rw [M.eq_equality _ _ _ _ _ _ _ hE hTm ha hb] at hin
            exact ⟨eq_of_mem_eqv hin, ha⟩
    · exact ih hdf L ρ

/-- A certified environment types no closed term at `∀ (p : Prop), p`. -/
theorem CertOrdered.consistent {env : VEnv} {U : Nat} (h : CertOrdered cenv lp env)
    (M : ConLeche.Model V cenv) (hpar : ParamsOnly M) (hdl : DefnLaw M) :
    ¬ ∃ e, env.HasType U [] e falseE :=
  no_proof_of_false h.ordered (h.envModel M hpar hdl)

end Lean4Zfc
