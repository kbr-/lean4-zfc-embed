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

end Lean4Zfc
