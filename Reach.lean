import Lean4Zfc.Example.PUnitRun
import Lean4Zfc.Generate
import Lean4Zfc.Tally

/-!
`reach FILE...`: how much of each export the generator keeps. `reach --measure DIR SECONDS JOBS`
runs that on every `.ndjson` file of `DIR`, each as a child stopped after `SECONDS`, `JOBS` at a
time. `reach --summary FILE` prints the totals of a saved measurement (`Lean4Zfc/Tally.lean`).

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
  | .lit (.natVal n) => if n ≤ litBound then none else some s!"a Nat literal above {litBound}"
  | .lit (.strVal _) => some "a string literal"
  | .proj _ _ _ => some "a projection"
  | .sort u => if (untrLevel ps u).isNone then some "a level outside its parameters" else none
  | .const _ us =>
    if (untrLevels ps us).isNone then some "a level outside its parameters" else none
  | .app f a => (blocker ps f).orElse fun _ => blocker ps a
  | .lam A b => (blocker ps A).orElse fun _ => blocker ps b
  | .forallE A B => (blocker ps A).orElse fun _ => blocker ps B
  | .bvar _ => none

/-- A level, written with its parameters by index. -/
def levelText : Lean4Lean.VLevel → String
  | .zero => "0"
  | .succ l => s!"{levelText l}+1"
  | .max a b => s!"max ({levelText a}) ({levelText b})"
  | .imax a b => s!"imax ({levelText a}) ({levelText b})"
  | .param i => s!"u{i}"

/-- What a type's head is: its head constant's name, or the kind of term at its head. -/
def headName : Lean4Lean.VExpr → String
  | .app f _ => headName f
  | .const c _ => c.toString
  | .forallE _ _ => "a ∀"
  | .sort l => s!"Sort ({levelText l})"
  | .lam _ _ => "a λ"
  | .bvar _ => "a bound variable"

/-- Where `infer` gives up on `e` in the context `Γ`: the innermost subterm it fails on, read by
the cases of `infer`, the class of failure first. It reads `infer`'s results and decides nothing
the theorems state. -/
def stuck (env : Lean4Lean.VEnv) (eqs : List Lean4Lean.VDefEq) (U : Nat)
    (Γ : List Lean4Lean.VExpr) : Lean4Lean.VExpr → String
  | .bvar _ => "a bound variable outside its context"
  | .sort _ => "a level outside its parameters"
  | .const c _ =>
    match env.constants c with
    | none => s!"a constant not kept: {c}"
    | some _ => s!"a constant at levels it does not take: {c}"
  | .app f a =>
    match infer env eqs U fuel Γ f, infer env eqs U fuel Γ a with
    | none, _ => stuck env eqs U Γ f
    | _, none => stuck env eqs U Γ a
    | some Tf, some A' =>
      match whnfTy env eqs U fuel Γ Tf with
      | some (.forallE A _) =>
        s!"an argument whose type does not convert to the domain: {headName A'} against {headName A}"
      | _ => s!"a head whose type is no function: {headName Tf}"
  | .lam A b =>
    match sortOf env eqs U fuel Γ A with
    | none =>
      match infer env eqs U fuel Γ A with
      | none => stuck env eqs U Γ A
      | some T => s!"a domain whose type is no sort: {headName T}"
    | some _ =>
      match infer env eqs U fuel (A :: Γ) b with
      | none => stuck env eqs U (A :: Γ) b
      | some _ => "nothing within the fuel"
  | .forallE A B =>
    match sortOf env eqs U fuel Γ A with
    | none =>
      match infer env eqs U fuel Γ A with
      | none => stuck env eqs U Γ A
      | some T => s!"a domain whose type is no sort: {headName T}"
    | some _ =>
      match infer env eqs U fuel (A :: Γ) B with
      | none => stuck env eqs U (A :: Γ) B
      | some T => s!"a body whose type is no sort: {headName T}"

/-- Which of the generator's conditions the constant `ci` fails in the state `g` the generator
reached just before it. -/
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
      let U := ci.toConstantVal.levelParams.length
      match sortOf g.env g.eqs U fuel [] ty with
      | none =>
        let at_ := match infer g.env g.eqs U fuel [] ty with
          | none => stuck g.env g.eqs U [] ty
          | some T => s!"a type whose type is no sort: {headName T}"
        s!"the inferencer does not type its type at a sort; it stops at {at_}"
      | some _ => "its name is taken"

/-- The report for the environment the checker returned. -/
def generatedReport (cenv : ConLeche.Env) : String :=
  let g := generated cenv
  let dropped := cenv.consts.reverse.filter (fun ci => !g.names.contains (untrName ci.name))
  let why := match dropped with
    | [] => ""
    | ci :: _ =>
      let before := (cenv.consts.reverse.takeWhile fun c => decide (c ≠ ci)).foldl (step cenv)
        ⟨.empty, [], []⟩
      s!"\tthe first because {whyLeftOut cenv before ci}"
  s!"constants {cenv.consts.length}\tkept {g.names.length}\tequations {g.eqs.length}" ++
    s!"\tfirst left out {(dropped.take 5).map (fun ci => untrName ci.name)}" ++ why

/-- One file's line of a measurement: this program run on `path` as a child under `timeout`, its
output kept whole, and the marker `Lean4Zfc/Tally.lean` reads when the limit stopped it. -/
def measureFile (self : System.FilePath) (secs : Nat) (path : System.FilePath) : IO String := do
  let out ← IO.Process.output
    { cmd := "timeout", args := #[toString secs, self.toString, path.fileName.getD ""],
      cwd := path.parent }
  let line := "\n".intercalate ((out.stdout.splitOn "\n").filter (· ≠ ""))
  if out.exitCode == 124 then return s!"{line}\t[stopped at the {secs}-second limit]"
  else return line

/-- Every `.ndjson` file of `dir`, in name order, measured `jobs` at a time, each line printed in
that order once its file is done. -/
def measureDir (dir : System.FilePath) (secs jobs : Nat) : IO Unit := do
  let self ← IO.appPath
  let files := ((← dir.readDir).filter (·.fileName.endsWith ".ndjson")).map (·.path)
  let files := files.qsort (·.toString < ·.toString)
  let out ← IO.getStdout
  let mut rest := files.toList
  while !rest.isEmpty do
    let tasks ← (rest.take jobs).mapM fun p => IO.asTask (measureFile self secs p)
    for t in tasks do
      out.putStrLn (← IO.ofExcept t.get)
      out.flush
    rest := rest.drop jobs

/-- Each file's name is written before its export is read, and the checker's answer before the
generator starts, so a run that does not finish shows the file and the side it stopped on. -/
def main (args : List String) : IO Unit := do
  let out ← IO.getStdout
  if let ["--summary", file] := args then
    out.putStrLn (tally (← IO.FS.readFile file)).render
    return
  if let ["--measure", dir, secs, jobs] := args then
    measureDir dir secs.toNat! jobs.toNat!
    return
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
