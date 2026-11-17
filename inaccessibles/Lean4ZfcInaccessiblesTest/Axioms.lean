import Lean4ZfcInaccessibles

/-!
The axioms of the two theorems under inaccessible cardinals, pinned: a `sorry` anywhere beneath
them, in this repository or in a dependency, fails this module's build.
-/

/--
info: 'Lean4Zfc.consistent_of_omegaInaccessibles' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Zfc.consistent_of_omegaInaccessibles

/--
info: 'Lean4Zfc.checked_consistent_of_omegaInaccessibles' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Zfc.checked_consistent_of_omegaInaccessibles
