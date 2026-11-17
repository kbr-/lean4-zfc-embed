import Lean4Zfc.Falsity
import Lean4Lean.Theory.Typing.Env

/-!
Lean4Lean's own predicate `VEnv.WF` on the environment with an axiom of type `∀ (p : Prop), p`.

Two things the README says of `VEnv.WF` are checked here: it accepts that environment, as one
`axiom` step, and a theorem naming it depends on `sorryAx`, because the predicate mentions inductive
declarations, whose definition is `sorry` in Lean4Lean. The proof below uses only the `axiom` rule.
-/

open Lean4Lean Lean4Zfc

/-- The axiom `bad : ∀ (p : Prop), p`, as a declaration. -/
def badAxiom : VConstVal := { uvars := 0, type := falseE, name := `bad }

theorem badEnv_wf : badEnv.WF :=
  ⟨[.axiom badAxiom], .decl (.axiom ⟨_, falseE_isType _ _⟩ (addConst_of_none rfl)) .empty⟩

/-- info: 'badEnv_wf' depends on axioms: [propext, sorryAx, Quot.sound] -/
#guard_msgs in
#print axioms badEnv_wf
