import Lean4Zfc

/-!
The axioms each general theorem depends on, pinned: a `sorry`, or an axiom of compiled evaluation,
reaching one of them changes the printed list and fails this module's build.
-/

/--
info: 'Lean4Zfc.fundamental' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Zfc.fundamental

/--
info: 'Lean4Zfc.no_proof_of_false' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Zfc.no_proof_of_false

/--
info: 'Lean4Zfc.empty_consistent' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Zfc.empty_consistent

/--
info: 'Lean4Zfc.EnvModel.addDef' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Zfc.EnvModel.addDef

/--
info: 'Lean4Zfc.Built.consistent' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Zfc.Built.consistent

/-- info: 'Lean4Zfc.falseE_isType' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Lean4Zfc.falseE_isType

/-- info: 'Lean4Zfc.badEnv_proves_false' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Lean4Zfc.badEnv_proves_false

/--
info: 'Lean4Zfc.badEnv_no_model' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Zfc.badEnv_no_model
