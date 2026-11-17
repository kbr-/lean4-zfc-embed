import Lean4Zfc.Example.PUnit

/-!
The example's axioms, pinned: the three standard ones and those of the compiled evaluations it
makes (the checker's run, five comparisons of constants and one of an equation).
-/

/--
info: 'Lean4Zfc.Example.PUnit.env_consistent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Lean4Zfc.Example.PUnit.check_f._native.native_decide.ax_1_1,
 Lean4Zfc.Example.PUnit.check_fEq._native.native_decide.ax_1_1,
 Lean4Zfc.Example.PUnit.check_other._native.native_decide.ax_1_1,
 Lean4Zfc.Example.PUnit.check_pUnit._native.native_decide.ax_1_1,
 Lean4Zfc.Example.PUnit.check_rec._native.native_decide.ax_1_1,
 Lean4Zfc.Example.PUnit.check_unit._native.native_decide.ax_1_1,
 Lean4Zfc.Example.PUnit.run_ok._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms Lean4Zfc.Example.PUnit.env_consistent

/-- info: 'Lean4Zfc.Example.PUnit.f_defeq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Lean4Zfc.Example.PUnit.f_defeq
