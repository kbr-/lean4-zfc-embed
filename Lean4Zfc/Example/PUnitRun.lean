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

`Eq` comes from the checker's built-in prelude. The run is in a module of its own so that
`Lean4Zfc.Example.PUnit` can evaluate it by compiled code.

Lake does not track the two data files: after changing one, change this file too (or remove its
build outputs), or the build reuses the run of the old data.
-/

namespace Lean4Zfc.Example.PUnit

open ConLeche

def text : String :=
  (include_str "data/corner_punit_own.ndjson") ++ (include_str "data/f_eq.ndjson")

/-- The checker's run on the export, as its binary's accept path computes it. -/
def run : Except (CheckError × Nat) Env := do
  let pre ← Frontend.builtinPreludeE
  let r ← Frontend.parseExportD text
  Cached.checkDecls .verified natOpPinSets Cached.maxNatSizeDefault
    (Frontend.preparePrelude pre r.decls)

end Lean4Zfc.Example.PUnit
