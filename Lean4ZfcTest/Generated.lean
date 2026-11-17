import Lean4Zfc
import Lean4Zfc.Example.PUnitGenerated

/-!
Checks of the generator.

The general theorems' axioms are pinned: none beyond `propext`, `Classical.choice` and
`Quot.sound`. The example's are those and the compiled evaluations it makes: the checker's run and
the generator's two outputs.
-/

/-- info: 'Lean4Zfc.inferType_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Lean4Zfc.inferType_sound

/-- info: 'Lean4Zfc.trExpr_untrExpr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Lean4Zfc.trExpr_untrExpr

/--
info: 'Lean4Zfc.generate_certOrdered' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Zfc.generate_certOrdered

/--
info: 'Lean4Zfc.generated_consistent' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Zfc.generated_consistent

/--
info: 'Lean4Zfc.Example.PUnit.generated_env_consistent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Lean4Zfc.Example.PUnit.run_ok._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms Lean4Zfc.Example.PUnit.generated_env_consistent

/--
info: 'Lean4Zfc.Example.PUnit.generated_f_defeq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Lean4Zfc.Example.PUnit.generated_eqs._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms Lean4Zfc.Example.PUnit.generated_f_defeq

/--
info: 'Lean4Zfc.Example.PUnit.generated_rec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Lean4Zfc.Example.PUnit.generated_names_listed._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms Lean4Zfc.Example.PUnit.generated_rec
