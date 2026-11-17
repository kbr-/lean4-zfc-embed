import Lean4Zfc.Example.PUnit
import Lean4Zfc.Generate

/-!
The generator run on the example's export.

Nothing here is written by hand about the environment: `generate cenv` is computed from what the
checker returned. `generated_names` shows the generator kept every constant of the checker's
environment, the prelude's (`Eq`, `Nat`, `Quot`, their constructors and recursors) with the
export's, and `generated_eqs` that it found the equation `f ≡ PUnit.other` twice: as the type of
the constant `f_eq`, and as the unfolding of the definition `f`. So `generated_f_defeq` derives `f ≡ PUnit.other` in the generated environment, and
`generated_env_consistent` is the consistency statement for it.
-/

namespace Lean4Zfc.Example.PUnit

open Lean4Lean

/-- The generator keeps every constant of the checker's environment. -/
theorem generated_names :
    (generated cenv).names = cenv.consts.map (fun ci => untrName ci.name) := by native_decide

/-- The names it keeps, written out. -/
theorem generated_names_listed :
    (generated cenv).names =
      [`f_eq, `f, `PUnit.rec, `PUnit.other, `PUnit.unit, `PUnit, `Bool.rec, `Bool.true,
        `Bool.false, `Bool, `And.rec, `And.intro, `And, `Quot.sound, `Quot.ind, `Quot.lift,
        `Quot.mk, `Quot, `False.rec, `False, `Empty.rec, `Empty, `Nat.rec, `Nat.succ, `Nat.zero,
        `Nat, `Eq.rec, `Eq.refl, `Eq] := by native_decide

/-- The generator finds the equation twice: from the type of the theorem `f_eq`, and as the
unfolding of the definition `f`. -/
theorem generated_eqs : (generated cenv).eqs = [fEq, fEq] := by native_decide

/-- Each listed name is a constant of the generated environment. -/
theorem generated_constant {n : Lean.Name} (h : n ∈ (generated cenv).names) :
    ((generate cenv).constants n).isSome :=
  (generated_good cenv).names n h

/-- The generated environment holds the recursor. -/
theorem generated_rec : ((generate cenv).constants `PUnit.rec).isSome :=
  generated_constant (by rw [generated_names_listed]; decide)

/-- The generated environment derives `f ≡ PUnit.other : PUnit`. -/
theorem generated_f_defeq :
    (generate cenv).IsDefEq 0 [] (.const `f []) (.const `PUnit.other []) pUnit := by
  have h : (generate cenv).defeqs fEq :=
    (generated_good cenv).eqs fEq (by rw [generated_eqs]; exact List.mem_cons_self)
  exact .extra (df := fEq) (ls := []) h (by simp) rfl

universe w

/-- The generated environment types no closed term at `∀ (p : Prop), p`. -/
theorem generated_env_consistent (V : Type w) [ConLeche.SetTheory V] {U : Nat} :
    ¬ ∃ e, (generate cenv).HasType U [] e falseE := by
  obtain ⟨ds, h⟩ := accepted
  exact generated_consistent V _ _ ds h

end Lean4Zfc.Example.PUnit
