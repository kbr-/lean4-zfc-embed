import Lean4Zfc.Bridge
import ConLeche.Model.Denotes
import ConLeche.Verify.Cached.MainC

/-!
Derivations of Lean4Lean's judgement over an environment certified by one Con-Leche's
checker accepts are sound, in any model of the set theory.
-/

namespace Lean4Zfc

open Lean4Lean

universe w

variable {V : Type w} [ConLeche.SetTheory V] {cenv : ConLeche.Env}

/-- The model Con-Leche reads off its invariant gives each constant a value that reads only the
constant's own level parameters. -/
theorem paramsOnly_ofEnvModelM (m : ConLeche.Model.EnvModelM V cenv) :
    ParamsOnly (ConLeche.Model.Model.ofEnvModelM m) := by
  intro n ci hf ψ₁ ψ₂ h
  show ConLeche.Model.cvalOf m.base2.acval n ψ₁ = ConLeche.Model.cvalOf m.base2.acval n ψ₂
  unfold ConLeche.Model.cvalOf
  rw [m.base2.acval_params n ci hf ψ₁ ψ₂ h]

omit [ConLeche.SetTheory V] in
theorem fvarsBelow_zero : ∀ {e : ConLeche.Expr}, e.hasFvar = false →
    ConLeche.Expr.fvarsBelow 0 e := by
  intro e
  induction e <;> simp_all [ConLeche.Expr.fvarsBelow, ConLeche.Expr.hasFvar]

/-- In the model Con-Leche reads off its invariant, a stored definition's value denotes the
definition's own value: the invariant says the value reads to the constant's leaf
(`defn_reads`), and a reading is a denotation (`Denotes_of_denote`). -/
theorem defnLaw_ofEnvModelM (m : ConLeche.Model.EnvModelM V cenv) :
    DefnLaw (ConLeche.Model.Model.ofEnvModelM m) := by
  intro cv value hint hmem φ ρ
  have hr := m.defn_reads φ cv value ⟨hint, hmem⟩
  obtain ⟨hnf, _, _, hlb⟩ := (m.base2.wf.consts _ hmem).2.2.2.2.1 cv value hint rfl
  have hbr := ConLeche.Model.Denotes_of_denote (V := V) m.base2.cval_closed 0 value hr
    (fvarsBelow_zero hnf) hlb ρ
  rw [ConLeche.Expr.closeN_of_hasFvar _ 0 0 hnf,
    ConLeche.Model.interp_cvalOf m.base2.cval_closed] at hbr
  exact hbr

/-- If Con-Leche's checker accepts the declarations `ds`, giving the environment `cenv`, then a
Lean4Lean environment certified against `cenv` types no closed term at `∀ (p : Prop), p`: every
derivation of the abstract judgement over it is sound, whether or not a checker would find it. -/
theorem checked_consistent (V : Type w) [ConLeche.SetTheory V]
    (pins : List ConLeche.NatOpPinSet) (maxNatSize : Nat) (ds : Array ConLeche.Declaration)
    (accepted : ConLeche.Cached.checkDecls .verified pins maxNatSize ds = .ok cenv)
    {lp : Lean.Name → List ConLeche.Name} {env : VEnv} {U : Nat}
    (h : CertOrdered cenv lp env) :
    ¬ ∃ e, env.HasType U [] e falseE := by
  obtain ⟨m⟩ := ConLeche.Cached.checkDecls_sound (V := V) accepted
  exact h.consistent (ConLeche.Model.Model.ofEnvModelM m) (paramsOnly_ofEnvModelM m)
    (defnLaw_ofEnvModelM m)

end Lean4Zfc
