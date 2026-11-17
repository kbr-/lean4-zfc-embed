/-!
The totals of a saved `reach` measurement.

A measurement has one line per export file: the file's name, then `not accepted`; or `accepted`
followed by the counts `constants N`, `kept N`, `equations N`; or, where the run was abandoned at
its time limit, a marker `[stopped …]` after whatever the run had printed, `accepted` included
when the checker had answered. A line of any other form, such as what a run that died left, is
counted as unread. `tally` sums them into every part of the partition, so a sentence quoting the
figures is written from one printed line, and `tally_partition` proves that no line is lost: the
five kinds add up to the lines that are not blank.
-/

namespace Lean4Zfc

/-- The parts of a measurement. `files` is the sum of the five kinds of line. -/
structure Tally where
  files : Nat := 0
  notAccepted : Nat := 0
  finished : Nat := 0
  stoppedAfterAccepting : Nat := 0
  noAnswer : Nat := 0
  unread : Nat := 0
  constants : Nat := 0
  kept : Nat := 0
  equations : Nat := 0
  keptWhole : Nat := 0
  deriving BEq, Repr

/-- The number after `pre` in the first field that starts with it. -/
def fieldNat (fields : List String) (pre : String) : Option Nat :=
  fields.findSome? fun f => if f.startsWith pre then (f.drop pre.length).toNat? else none

/-- A line with nothing but white space. -/
def blank (line : String) : Bool := line.all Char.isWhitespace

/-- Add one line of a measurement; a blank line adds nothing, and a line fitting none of the forms
is counted as unread. -/
def tallyLine (t : Tally) (line : String) : Tally :=
  let fields := line.splitOn "\t"
  if blank line then t
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
    | _, _, _ => { t with files := t.files + 1, unread := t.unread + 1 }

/-- The totals of a whole measurement. -/
def tally (text : String) : Tally := (text.splitOn "\n").foldl tallyLine {}

/-- The kinds of line add up to the lines counted. -/
def Tally.Whole (t : Tally) : Prop :=
  t.files = t.notAccepted + t.finished + t.stoppedAfterAccepting + t.noAnswer + t.unread

theorem tallyLine_whole {t : Tally} (h : t.Whole) (line : String) : (tallyLine t line).Whole := by
  unfold tallyLine Tally.Whole at *
  simp only
  repeat' split
  all_goals first | omega | (simp only at *; omega)

theorem tallyLine_files (t : Tally) (line : String) :
    (tallyLine t line).files = t.files + if blank line then 0 else 1 := by
  unfold tallyLine
  simp only
  repeat' split
  all_goals simp_all

theorem foldl_whole (lines : List String) {t : Tally} (h : t.Whole) :
    (lines.foldl tallyLine t).Whole := by
  induction lines generalizing t with
  | nil => exact h
  | cons l ls ih => exact ih (tallyLine_whole h l)

theorem foldl_files (lines : List String) (t : Tally) :
    (lines.foldl tallyLine t).files = t.files + (lines.filter (fun l => !blank l)).length := by
  induction lines generalizing t with
  | nil => simp
  | cons l ls ih =>
    rw [List.foldl_cons, ih, tallyLine_files]
    by_cases hb : blank l <;> simp [hb] <;> omega

/-- No line is lost: every line that is not blank is counted, in exactly one of the five kinds. -/
theorem tally_partition (text : String) :
    (tally text).files = ((text.splitOn "\n").filter (fun l => !blank l)).length ∧
    (tally text).Whole := by
  refine ⟨?_, foldl_whole _ (by simp [Tally.Whole])⟩
  have := foldl_files (text.splitOn "\n") {}
  simpa [tally] using this

/-- The totals as one line, every part named. -/
def Tally.render (t : Tally) : String :=
  s!"files {t.files}: not accepted {t.notAccepted}; accepted, generator finished {t.finished}; " ++
  s!"accepted, generator stopped at the limit {t.stoppedAfterAccepting}; " ++
  s!"no answer from the checker within the limit {t.noAnswer}; " ++
  s!"lines of no known form {t.unread}; " ++
  s!"accepted in all {t.finished + t.stoppedAfterAccepting}; " ++
  s!"in the finished environments: constants {t.constants}, kept {t.kept}, " ++
  s!"stored equations {t.equations}, kept whole {t.keptWhole}"

end Lean4Zfc
