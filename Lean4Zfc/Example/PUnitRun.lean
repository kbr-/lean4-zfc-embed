import Lean4Zfc.Checked
import ConLeche.Driver.CheckMain

/-!
Con-Leche's checker run on a small export.

The export is Con-Leche's test fixture `tests/e2e/corner_punit_own.ndjson`, which declares

    inductive PUnit : Type where
      | unit : PUnit
      | other : PUnit

    def f : PUnit := PUnit.other

followed by one theorem written by hand in the export's format (`data/f_eq.ndjson`):

    theorem f_eq : @Eq PUnit f PUnit.other := @Eq.refl PUnit PUnit.other

`Eq` comes from the checker's built-in prelude. `textFalse` is the same export with the theorem's
type changed to the false equation `@Eq PUnit f PUnit.unit` (`data/f_eq_false.ndjson`), which the
checker must reject; `Lean4ZfcTest/Example.lean` checks that it does.

The runs are in a module of their own so that other modules can evaluate them by compiled code.

Lake does not track the data files: after changing one, change this file too (or remove its build
outputs), or the build reuses the run of the old data.
-/

namespace Lean4Zfc.Example.PUnit

open ConLeche

def text : String :=
  (include_str "data/corner_punit_own.ndjson") ++ (include_str "data/f_eq.ndjson")

/-- The export with `f_eq` stated as the false equation `f = PUnit.unit`. -/
def textFalse : String :=
  (include_str "data/corner_punit_own.ndjson") ++ (include_str "data/f_eq_false.ndjson")

/-- The checker's run on an export, as its binary's accept path computes it. -/
def runOn (text : String) : Except (CheckError × Nat) Env := do
  let pre ← Frontend.builtinPreludeE
  let r ← Frontend.parseExportD text
  Cached.checkDecls .verified natOpPinSets Cached.maxNatSizeDefault
    (Frontend.preparePrelude pre r.decls)

/-- The checker's run on the example's export. -/
def run : Except (CheckError × Nat) Env := runOn text

end Lean4Zfc.Example.PUnit
