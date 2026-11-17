import Lean4Zfc.Example.PUnitRun
import Lean4Zfc.Falsity
import Lean4Lean.Theory.Typing.Meta

/-!
A certified environment, by hand: an inductive type, its recursor and a stored equation.

The Lean4Lean environment `env` holds the inductive type `PUnit`, its constructors `PUnit.unit` and
`PUnit.other`, its recursor `PUnit.rec` (which has a level parameter), the constant `f`, and the
stored equation `f ≡ PUnit.other`. Each constant is certified against the constant of the same name
in the environment Con-Leche's checker returns for the export of `Lean4Zfc.Example.PUnitRun`, and
the equation against the theorem `f_eq` there. So `env` types no closed term at `∀ (p : Prop), p`
(`env_consistent`), and the equation is derivable in it (`f_defeq`).

The checker's run and the comparisons of stored constants are evaluated by compiled code
(`native_decide`), so the theorems of this module depend on axioms of compiled evaluation beside
`propext`, `Classical.choice` and `Quot.sound`. The general theorems they instantiate do not.
-/

namespace Lean4Zfc.Example.PUnit

open Lean4Lean

/-- The environment the checker returns on the export. -/
def cenv : ConLeche.Env :=
  match run with
  | .ok e => e
  | .error _ => ConLeche.Env.empty

theorem run_ok : run = .ok cenv := by
  have h : (match run with | .ok _ => true | .error _ => false) = true := by native_decide
  unfold cenv
  cases hr : run with
  | ok e => rfl
  | error e => rw [hr] at h; cases h

/-- The checker accepted a list of declarations with result `cenv`. -/
theorem accepted : ∃ ds, ConLeche.Cached.checkDecls .verified ConLeche.natOpPinSets
    ConLeche.Cached.maxNatSizeDefault ds = .ok cenv := by
  have h := run_ok
  unfold run runOn at h
  cases hA : ConLeche.Frontend.builtinPreludeE with
  | error e => rw [hA] at h; cases h
  | ok pre =>
    cases hB : ConLeche.Frontend.parseExportD text with
    | error e => rw [hA, hB] at h; cases h
    | ok r =>
      rw [hA, hB] at h
      exact ⟨_, h⟩

/-- A computable check of `CertConst`. -/
def certCheck (cenv : ConLeche.Env) (lps : List ConLeche.Name) (c : Lean.Name)
    (vc : VConstant) : Bool :=
  match cenv.consts.find? (·.name == trName c) with
  | some ci =>
    decide (ci.name = trName c) && decide (ci.toConstantVal.levelParams = lps) &&
      decide lps.Nodup && decide (lps.length = vc.uvars) &&
      decide (ci.toConstantVal.type = trExpr lps vc.type)
  | none => false

theorem certConst_of_check {cenv : ConLeche.Env} {lp : Lean.Name → List ConLeche.Name}
    {c : Lean.Name} {vc : VConstant} (h : certCheck cenv (lp c) c vc = true) :
    CertConst cenv lp c vc := by
  unfold certCheck at h
  split at h
  · rename_i ci hf
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
    exact ⟨ci, List.mem_of_find?_eq_some hf, hf, h1, h2, h3, h4, h5⟩
  · cases h

/-- A computable check of the certificate of a stored equation. -/
def eqCheck (cenv : ConLeche.Env) (c : ConLeche.Name) (ps : List ConLeche.Name) (u : VLevel)
    (df : VDefEq) : Bool :=
  match cenv.consts.find? (·.name == c) with
  | some ci =>
    decide ps.Nodup && decide (ps.length = df.uvars) &&
      decide (ci.toConstantVal.type = eqExpr ps u df.type df.lhs df.rhs)
  | none => false

theorem cert_of_eqCheck {cenv : ConLeche.Env} {c : ConLeche.Name} {ps : List ConLeche.Name}
    {u : VLevel} {df : VDefEq} (h : eqCheck cenv c ps u df = true) :
    ∃ ci ps, ci ∈ cenv.consts ∧ ps.Nodup ∧ ps.length = df.uvars ∧
      ci.toConstantVal.type = eqExpr ps u df.type df.lhs df.rhs := by
  unfold eqCheck at h
  split at h
  · rename_i ci hf
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    exact ⟨ci, ps, List.mem_of_find?_eq_some hf, h1, h2, h3⟩
  · cases h

/-- The recursor's level parameter is named `u` in the export; the other constants have none. -/
def lp : Lean.Name → List ConLeche.Name :=
  fun c => if c = `PUnit.rec then [trName `u] else []

def pUnit : VExpr := .const `PUnit []

/-- `∀ (motive : PUnit → Sort u) (unit : motive PUnit.unit) (other : motive PUnit.other)
(t : PUnit), motive t`. -/
def recType : VExpr :=
  .forallE (.forallE pUnit (.sort (.param 0)))
    (.forallE (.app (.bvar 0) (.const `PUnit.unit []))
      (.forallE (.app (.bvar 1) (.const `PUnit.other []))
        (.forallE pUnit (.app (.bvar 3) (.bvar 0)))))

/-- `PUnit : Type`. -/
def vPUnit : VConstant := ⟨0, .sort (.succ .zero)⟩
/-- A constant of type `PUnit`: each constructor, and `f`. -/
def vElem : VConstant := ⟨0, pUnit⟩
def vRec : VConstant := ⟨1, recType⟩

def env1 : VEnv :=
  { VEnv.empty with constants := fun m => if `PUnit = m then some vPUnit else VEnv.empty.constants m }
def env2 : VEnv :=
  { env1 with constants := fun m => if `PUnit.unit = m then some vElem else env1.constants m }
def env3 : VEnv :=
  { env2 with constants := fun m => if `PUnit.other = m then some vElem else env2.constants m }
def env4 : VEnv :=
  { env3 with constants := fun m => if `PUnit.rec = m then some vRec else env3.constants m }
def env5 : VEnv :=
  { env4 with constants := fun m => if `f = m then some vElem else env4.constants m }

/-- The stored equation `f ≡ PUnit.other : PUnit`. -/
def fEq : VDefEq := ⟨0, .const `f [], .const `PUnit.other [], pUnit⟩

/-- `PUnit`, its constructors and recursor, `f`, and the stored equation. -/
def env : VEnv := env5.addDefEq fEq

theorem pUnit_wf : vPUnit.WF VEnv.empty :=
  ⟨.succ (.succ .zero),
    VEnv.IsDefEq.sortDF (l := .succ .zero) (l' := .succ .zero) (by trivial) (by trivial) rfl⟩

theorem elem_wf {env : VEnv} (h : env.constants `PUnit = some vPUnit) : vElem.WF env :=
  ⟨.succ .zero, VEnv.IsDefEq.constDF (ci := vPUnit) h (by simp) (by simp) rfl .nil⟩

theorem rec_wf : vRec.WF env3 := by
  have hP : env3.constants `PUnit = some vPUnit := by simp [env3, env2, env1]
  have hU : env3.constants `PUnit.unit = some vElem := by simp [env3, env2, env1]
  have hO : env3.constants `PUnit.other = some vElem := by simp [env3, env2]
  refine ⟨.imax (.imax (.succ .zero) (.succ (.param 0)))
    (.imax (.param 0) (.imax (.param 0) (.imax (.succ .zero) (.param 0)))), ?_⟩
  have tP : ∀ Γ, env3.HasType 1 Γ pUnit (.sort (.succ .zero)) := fun Γ =>
    VEnv.HasType.const' (ci := vPUnit) hP (by simp) rfl rfl
  have tU : ∀ Γ, env3.HasType 1 Γ (.const `PUnit.unit []) pUnit := fun Γ =>
    VEnv.HasType.const' (ci := vElem) hU (by simp) rfl rfl
  have tO : ∀ Γ, env3.HasType 1 Γ (.const `PUnit.other []) pUnit := fun Γ =>
    VEnv.HasType.const' (ci := vElem) hO (by simp) rfl rfl
  have wp : VLevel.WF 1 (.param 0) := by simp [VLevel.WF]
  let A0 : VExpr := .forallE pUnit (.sort (.param 0))
  let B1 : VExpr := .app (.bvar 0) (.const `PUnit.unit [])
  let B2 : VExpr := .app (.bvar 1) (.const `PUnit.other [])
  have tA0 : env3.HasType 1 [] A0 (.sort (.imax (.succ .zero) (.succ (.param 0)))) :=
    .forallE (tP _) (.sort wp)
  have tB1 : env3.HasType 1 [A0] B1 (.sort (.param 0)) :=
    VEnv.HasType.app' (A := pUnit) (B := .sort (.param 0)) (.bvar (by lookup_tac)) (tU _) rfl
  have tB2 : env3.HasType 1 [B1, A0] B2 (.sort (.param 0)) :=
    VEnv.HasType.app' (A := pUnit) (B := .sort (.param 0)) (.bvar (by lookup_tac)) (tO _) rfl
  have tB3 : env3.HasType 1 [pUnit, B2, B1, A0] (.app (.bvar 3) (.bvar 0)) (.sort (.param 0)) :=
    VEnv.HasType.app' (A := pUnit) (B := .sort (.param 0)) (.bvar (by lookup_tac))
      (.bvar (by lookup_tac)) rfl
  exact .forallE tA0 (.forallE tB1 (.forallE tB2 (.forallE (tP _) tB3)))

/-! The comparisons with the checker's stored constants, one compiled evaluation each. -/

theorem check_pUnit : certCheck cenv (lp `PUnit) `PUnit vPUnit = true := by native_decide
theorem check_unit : certCheck cenv (lp `PUnit.unit) `PUnit.unit vElem = true := by native_decide
theorem check_other : certCheck cenv (lp `PUnit.other) `PUnit.other vElem = true := by
  native_decide
theorem check_rec : certCheck cenv (lp `PUnit.rec) `PUnit.rec vRec = true := by native_decide
theorem check_f : certCheck cenv (lp `f) `f vElem = true := by native_decide
theorem check_fEq : eqCheck cenv (trName `f_eq) [] (.succ .zero) fEq = true := by native_decide

/-- `env` is certified against the checker's result. -/
theorem certOrdered : CertOrdered cenv lp env := by
  have c0 : CertOrdered cenv lp VEnv.empty := .empty
  have c1 : CertOrdered cenv lp env1 :=
    .const c0 pUnit_wf (addConst_of_none rfl) (certConst_of_check check_pUnit)
  have c2 : CertOrdered cenv lp env2 :=
    .const c1 (elem_wf (by simp [env1])) (addConst_of_none (by simp [env1, VEnv.empty]))
      (certConst_of_check check_unit)
  have c3 : CertOrdered cenv lp env3 :=
    .const c2 (elem_wf (by simp [env2, env1])) (addConst_of_none (by simp [env2, env1, VEnv.empty]))
      (certConst_of_check check_other)
  have c4 : CertOrdered cenv lp env4 :=
    .const c3 rec_wf (addConst_of_none (by simp [env3, env2, env1, VEnv.empty]))
      (certConst_of_check check_rec)
  have c5 : CertOrdered cenv lp env5 :=
    .const c4 (elem_wf (by simp [env4, env3, env2, env1]))
      (addConst_of_none (by simp [env4, env3, env2, env1, VEnv.empty]))
      (certConst_of_check check_f)
  have hP : env5.constants `PUnit = some vPUnit := by simp [env5, env4, env3, env2, env1]
  have hO : env5.constants `PUnit.other = some vElem := by simp [env5, env4, env3, env2]
  have hF : env5.constants `f = some vElem := by simp [env5]
  have tyF : env5.HasType 0 [] (.const `f []) pUnit :=
    VEnv.HasType.const' (ci := vElem) hF (by simp) rfl rfl
  have tyO : env5.HasType 0 [] (.const `PUnit.other []) pUnit :=
    VEnv.HasType.const' (ci := vElem) hO (by simp) rfl rfl
  have tyP : env5.HasType 0 [] pUnit (.sort (.succ .zero)) :=
    VEnv.HasType.const' (ci := vPUnit) hP (by simp) rfl rfl
  exact .defeq (df := fEq) (u := .succ .zero) c5 ⟨tyF, tyO⟩ tyP
    (cert_of_eqCheck check_fEq)

/-- `env` types no closed term at `∀ (p : Prop), p`, in any model of the set theory. -/
theorem env_consistent (V : Type w) [ConLeche.SetTheory V] {U : Nat} :
    ¬ ∃ e, env.HasType U [] e falseE := by
  obtain ⟨ds, hds⟩ := accepted
  exact checked_consistent V _ _ ds hds certOrdered

/-- The stored equation is used: `f` and `PUnit.other` are definitionally equal in `env`. -/
theorem f_defeq : env.IsDefEq 0 [] (.const `f []) (.const `PUnit.other []) pUnit :=
  .extra (df := fEq) (ls := []) (by simp [env, VEnv.addDefEq]) (by simp) rfl

end Lean4Zfc.Example.PUnit
