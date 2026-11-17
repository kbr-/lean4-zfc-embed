import Lean4Zfc.Fundamental

/-!
What the consistency statements say, checked from both sides.

The statements conclude that an environment types no closed term at `falseE`. `falseE` is a
proposition of every environment, so the conclusion is about a type of the theory. And the
conclusion fails for some ordered environment: the one holding a single constant of type `falseE`.
So the hypothesis of the consistency theorems, a model of the environment, is what excludes it.
-/

namespace Lean4Zfc

open Lean4Lean ConLeche ConLeche.SetTheory ConLeche.SetModel

universe w

variable {V : Type w} [SetTheory V]

/-- `∀ (p : Prop), p` is a proposition in every environment. -/
theorem falseE_isType (env : VEnv) (U : Nat) :
    env.HasType U [] falseE (.sort (.imax (.succ .zero) .zero)) :=
  .forallEDF (.sortDF (l := .zero) (l' := .zero) trivial trivial rfl) (.bvar .zero)

/-- Adding a constant under a name the environment does not hold. -/
theorem addConst_of_none {env : VEnv} {n : Lean.Name} {ci : VConstant}
    (h : env.constants n = none) :
    env.addConst n ci =
      some { env with constants := fun m => if n = m then some ci else env.constants m } := by
  unfold VEnv.addConst
  rw [h]

/-- A constant whose type is `∀ (p : Prop), p`. -/
def badConst : VConstant := ⟨0, falseE⟩

/-- The environment holding only the constant `bad : ∀ (p : Prop), p`. -/
def badEnv : VEnv :=
  { VEnv.empty with
    constants := fun m => if `bad = m then some badConst else VEnv.empty.constants m }

theorem badEnv_ordered : badEnv.Ordered :=
  .const .empty ⟨_, falseE_isType _ _⟩ (addConst_of_none rfl)

/-- An ordered environment that types a closed term at `∀ (p : Prop), p`. -/
theorem badEnv_proves_false : ∃ e, badEnv.HasType 0 [] e falseE :=
  ⟨.const `bad [],
    VEnv.IsDefEq.constDF (ci := badConst) (by simp [badEnv]) (by simp) (by simp) rfl .nil⟩

/-- That environment has no model, under any values of its constants. -/
theorem badEnv_no_model {cval : Name → List Nat → V} : ¬ EnvModel badEnv cval :=
  fun M => no_proof_of_false badEnv_ordered M badEnv_proves_false

end Lean4Zfc
