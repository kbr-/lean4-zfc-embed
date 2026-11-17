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

/-- The first construct of a term, in reading order, that Lean4Lean's terms have no counterpart
for, or a level the parameter names `ps` don't cover. -/
def blocker (ps : List ConLeche.Name) : ConLeche.Expr → Option String
  | .fvar _ _ => some "a free variable"
  | .letE _ _ _ => some "a let"
  | .lit _ => some "a literal"
  | .proj _ _ _ => some "a projection"
  | .sort u => if (untrLevel ps u).isNone then some "a level outside its parameters" else none
  | .const _ us =>
    if (untrLevels ps us).isNone then some "a level outside its parameters" else none
  | .app f a => (blocker ps f).orElse fun _ => blocker ps a
  | .lam A b => (blocker ps A).orElse fun _ => blocker ps b
  | .forallE A B => (blocker ps A).orElse fun _ => blocker ps B
  | .bvar _ => none

/-- Which of the generator's conditions the constant `ci` fails in the generated state `g`. For
the first constant left out, `g` may be the final state: the constants before it were all kept,
and its type mentions none after it. -/
def whyLeftOut (cenv : ConLeche.Env) (g : Generated) (ci : ConLeche.ConstantInfo) :
    String :=
  if cenv.find? ci.name ≠ some ci then "another constant bears its name"
  else if ¬ ci.toConstantVal.levelParams.Nodup then "its level parameter names repeat"
  else
    match untrExpr ci.toConstantVal.levelParams ci.toConstantVal.type with
    | none =>
      s!"its type has {(blocker ci.toConstantVal.levelParams ci.toConstantVal.type).getD
        "a construct the translation refuses"}"
    | some ty =>
      match sortOf g.env g.eqs ci.toConstantVal.levelParams.length fuel [] ty with
      | none => "the inferencer does not type its type at a sort"
      | some _ => "its name is taken"

/-- The report for the environment the checker returned. -/
def generatedReport (cenv : ConLeche.Env) : String :=
  let g := generated cenv
  let dropped := cenv.consts.reverse.filter (fun ci => !g.names.contains (untrName ci.name))
  let why := match dropped with
    | [] => ""
    | ci :: _ => s!"\tthe first because {whyLeftOut cenv g ci}"
  s!"constants {cenv.consts.length}\tkept {g.names.length}\tequations {g.eqs.length}" ++
    s!"\tfirst left out {(dropped.take 5).map (fun ci => untrName ci.name)}" ++ why

/-- Each file's name is written before its export is read, and the checker's answer before the
generator starts, so a run that does not finish shows the file and the side it stopped on. -/
def main (args : List String) : IO Unit := do
  let out ← IO.getStdout
  for path in args do
    out.putStr s!"{path}\t"
    out.flush
    let text ← IO.FS.readFile path
    match Example.PUnit.runOn text with
    | .error _ => out.putStrLn "not accepted"
    | .ok cenv =>
      out.putStr "accepted\t"
      out.flush
      out.putStrLn (generatedReport cenv)
    out.flush
