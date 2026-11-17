import Lean4Zfc.Built
import Lean4Zfc.Checked
import Lean4Zfc.Generate
import ConLecheBridge.Carneiro

/-!
Consistency of Lean4Lean's theory relative to inaccessible cardinals.

`ConLecheBridge.OmegaInaccessibles` says there is a strictly increasing `ℕ`-indexed sequence of
inaccessible cardinals, the hypothesis of lean4lean-model's `consistency` statement. Con-Leche's
bridge builds from it a model of its set theory on Mathlib's `ZFSet`, the universe chain being the
levels of the cumulative hierarchy at those cardinals. The theorems here feed that model to
the library's theorems, which hold in any model of the set theory.
-/

namespace Lean4Zfc

open Lean4Lean

universe u

/-- Assuming a strictly increasing `ℕ`-indexed sequence of inaccessible cardinals, an environment
built from definitions, opaque constants and examples types no closed term at `∀ (p : Prop), p`. -/
theorem consistent_of_omegaInaccessibles (h : ConLecheBridge.OmegaInaccessibles.{u})
    {ds : List VDecl} {env : VEnv} {U : Nat} (hb : Built ds env) :
    ¬ ∃ e, env.HasType U [] e falseE := by
  obtain ⟨⟨V, inst⟩⟩ := ConLecheBridge.carneiro_implies_conleche h
  exact Built.consistent V hb

/-- Assuming a strictly increasing `ℕ`-indexed sequence of inaccessible cardinals: if Con-Leche's
checker accepts the declarations `ds`, giving `cenv`, then a Lean4Lean environment certified
against `cenv` types no closed term at `∀ (p : Prop), p`. -/
theorem checked_consistent_of_omegaInaccessibles (h : ConLecheBridge.OmegaInaccessibles.{u})
    (pins : List ConLeche.NatOpPinSet) (maxNatSize : Nat) (ds : Array ConLeche.Declaration)
    {cenv : ConLeche.Env}
    (accepted : ConLeche.Cached.checkDecls .verified pins maxNatSize ds = .ok cenv)
    {lp : Lean.Name → List ConLeche.Name} {env : VEnv} {U : Nat}
    (hc : CertOrdered cenv lp env) :
    ¬ ∃ e, env.HasType U [] e falseE := by
  obtain ⟨⟨V, inst⟩⟩ := ConLecheBridge.carneiro_implies_conleche h
  exact checked_consistent V pins maxNatSize ds accepted hc

/-- Assuming a strictly increasing `ℕ`-indexed sequence of inaccessible cardinals: if Con-Leche's
checker accepts the declarations `ds`, giving `cenv`, then the Lean4Lean environment generated
from `cenv` types no closed term at `∀ (p : Prop), p`. No certificate is supplied: the
environment and its certificate are computed from `cenv`. -/
theorem generated_consistent_of_omegaInaccessibles (h : ConLecheBridge.OmegaInaccessibles.{u})
    (pins : List ConLeche.NatOpPinSet) (maxNatSize : Nat) (ds : Array ConLeche.Declaration)
    {cenv : ConLeche.Env}
    (accepted : ConLeche.Cached.checkDecls .verified pins maxNatSize ds = .ok cenv) {U : Nat} :
    ¬ ∃ e, (generate cenv).HasType U [] e falseE :=
  checked_consistent_of_omegaInaccessibles h pins maxNatSize ds accepted
    (generate_certOrdered cenv)

end Lean4Zfc
