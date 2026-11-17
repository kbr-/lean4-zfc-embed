/-!
The totals of a saved `reach` measurement.

A measurement has one line per export file: the file's name, then `not accepted`; or `accepted`
followed by the counts `constants N`, `kept N`, `equations N`; or, where the run was abandoned at
its time limit, a marker `[stopped …]` after whatever the run had printed, `accepted` included
when the checker had answered. `tally` sums them into every part of the partition, so a sentence
quoting the figures is written from one printed line.
-/

namespace Lean4Zfc

/-- The parts of a measurement. `files` is the sum of the four kinds of line. -/
structure Tally where
  files : Nat := 0
  notAccepted : Nat := 0
  finished : Nat := 0
  stoppedAfterAccepting : Nat := 0
  noAnswer : Nat := 0
  constants : Nat := 0
  kept : Nat := 0
  equations : Nat := 0
  keptWhole : Nat := 0
  deriving BEq, Repr

/-- The number after `pre` in the first field that starts with it. -/
def fieldNat (fields : List String) (pre : String) : Option Nat :=
  fields.findSome? fun f => if f.startsWith pre then (f.drop pre.length).toNat? else none

/-- Add one line of a measurement; a blank line, or one fitting none of the forms, adds nothing. -/
def tallyLine (t : Tally) (line : String) : Tally :=
  let fields := line.splitOn "\t"
  if line.all Char.isWhitespace then t
  else if (line.splitOn "[stopped").length > 1 then
    if fields.contains "accepted" then
      { t with files := t.files + 1, stoppedAfterAccepting := t.stoppedAfterAccepting + 1 }
    else { t with files := t.files + 1, noAnswer := t.noAnswer + 1 }
  else if fields.contains "not accepted" then
    { t with files := t.files + 1, notAccepted := t.notAccepted + 1 }
  else
    match fieldNat fields "constants ", fieldNat fields "kept ", fieldNat fields "equations " with
    | some c, some k, some e =>
      { t with files := t.files + 1, finished := t.finished + 1, constants := t.constants + c,
               kept := t.kept + k, equations := t.equations + e,
               keptWhole := t.keptWhole + if c = k then 1 else 0 }
    | _, _, _ => t

/-- The totals of a whole measurement. -/
def tally (text : String) : Tally := (text.splitOn "\n").foldl tallyLine {}

/-- The totals as one line, every part named. -/
def Tally.render (t : Tally) : String :=
  s!"files {t.files}: not accepted {t.notAccepted}; accepted, generator finished {t.finished}; " ++
  s!"accepted, generator stopped at the limit {t.stoppedAfterAccepting}; " ++
  s!"no answer from the checker within the limit {t.noAnswer}; " ++
  s!"accepted in all {t.finished + t.stoppedAfterAccepting}; " ++
  s!"in the finished environments: constants {t.constants}, kept {t.kept}, " ++
  s!"stored equations {t.equations}, kept whole {t.keptWhole}"

end Lean4Zfc
