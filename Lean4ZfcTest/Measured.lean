import Lean4Zfc.Tally

/-!
The README's figures, pinned to the saved measurement they come from.

`measurements/con-leche-e2e.tsv` is the output of `reach --measure` over the export fixtures of
Con-Leche's `tests/e2e/`, with a limit of thirty seconds a file. The guard fails the build when
the totals of that file are not the ones the README's section Limits states.

Lake does not track the file: after replacing it, change this file too (or remove its build
outputs), or the build reuses the check of the old one.
-/

open Lean4Zfc

def savedMeasurement : String := include_str "../measurements/con-leche-e2e.tsv"

#guard tally savedMeasurement ==
  { files := 580, notAccepted := 240, finished := 328, stoppedAfterAccepting := 10, noAnswer := 2,
    unread := 0, constants := 20764, kept := 20544, equations := 4870, keptWhole := 253 }
