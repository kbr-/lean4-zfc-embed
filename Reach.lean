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

/-- The report for one export's text, to follow the file's name on its line. -/
def reachReport (text : String) : String :=
  match Example.PUnit.runOn text with
  | .error _ => "not accepted"
  | .ok cenv =>
    let g := generated cenv
    let all := cenv.consts.map (fun ci => untrName ci.name)
    let dropped := all.reverse.filter (fun n => !g.names.contains n)
    s!"constants {all.length}\tkept {g.names.length}\tequations {g.eqs.length}" ++
      s!"\tfirst left out {dropped.take 5}"

/-- Each file's name is written before its export is read, so a run that does not finish names
the file it stopped on. -/
def main (args : List String) : IO Unit := do
  let out ← IO.getStdout
  for path in args do
    out.putStr s!"{path}\t"
    out.flush
    let text ← IO.FS.readFile path
    out.putStrLn (reachReport text)
    out.flush
