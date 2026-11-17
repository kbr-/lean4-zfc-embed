import Lean4Zfc.Tally

/-!
The tally of a measurement, on a sample holding each form of line once or twice, its totals worked
out by hand: two finished files (5 of 5 kept, and 7 of 9), one not accepted, one stopped after the
checker accepted, one with no answer from the checker, two lines of no known form (a run that
failed after the checker accepted, and one that printed its name alone), and a blank last line.
-/

open Lean4Zfc

def sample : String :=
  "a.ndjson\taccepted\tconstants 5\tkept 5\tequations 1\tfirst left out []\n" ++
  "b.ndjson\taccepted\tconstants 9\tkept 7\tequations 0\tfirst left out [X]\tthe first because y\n" ++
  "c.ndjson\tnot accepted\n" ++
  "d.ndjson\taccepted\t\t[stopped at the 30-second limit]\n" ++
  "e.ndjson\t\t[stopped at the 30-second limit]\n" ++
  "f.ndjson\taccepted\t\t[failed with exit code 137]\n" ++
  "g.ndjson\n"

#guard tally sample ==
  { files := 7, notAccepted := 1, finished := 2, stoppedAfterAccepting := 1, noAnswer := 1,
    unread := 2, constants := 14, kept := 12, equations := 1, keptWhole := 1 }

-- A line fitting no form is counted, as unread, and blank lines are not lines.
#guard tally "garbage\n" == { files := 1, unread := 1 }
#guard tally "\n \n\t\n" == {}
