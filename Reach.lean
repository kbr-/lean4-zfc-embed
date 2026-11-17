import Lean4Zfc.Example.PUnitRun
import Lean4Zfc.Generate

/-!
`reach FILE...`: how much of each export the generator keeps.

For each file it runs Con-Leche's checker on the export, as the example does, and, when the
checker accepts, the generator on the checker's result. One line per file: the count of constants
in the checker's environment, the count the generated environment holds, the count of stored
equations, and the first names left out. It measures; the theorems about the generator do not
depend on it.
-/

open Lean4Zfc

/-- The report line for one export's text. -/
def reachLine (path text : String) : String :=
  match Example.PUnit.runOn text with
  | .error _ => s!"{path}\tnot accepted"
  | .ok cenv =>
    let g := generated cenv
    let all := cenv.consts.map (fun ci => untrName ci.name)
    let dropped := all.reverse.filter (fun n => !g.names.contains n)
    s!"{path}\tconstants {all.length}\tkept {g.names.length}\tequations {g.eqs.length}" ++
      s!"\tfirst left out {dropped.take 5}"

def main (args : List String) : IO Unit := do
  for path in args do
    let text ← IO.FS.readFile path
    IO.println (reachLine path text)
    (← IO.getStdout).flush
