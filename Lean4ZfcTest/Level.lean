import Lean4Zfc.Level

/-!
Level equivalence on the pairs the measurement found blocking conversion, each worked out by hand
from `eval` (`imax x y` is `0` when `y` is `0`, `max x y` otherwise), and on pairs whose values
differ under some assignment, which `levelEquiv_sound` already forbids it to relate.
-/

open Lean4Zfc Lean4Lean

def one : VLevel := .succ .zero
def u (i : Nat) : VLevel := .param i

/-- `imax 1 0` repeated around `0`, the shape of a chain the measurement printed. -/
def imaxChain : Nat → VLevel → VLevel
  | 0, l => l
  | n + 1, l => .imax one (imaxChain n l)

-- Equal under every assignment: each must be related.
#guard levelEquiv (.imax one one) one
#guard levelEquiv (.max one one) one
#guard levelEquiv (.imax .zero .zero) .zero
#guard levelEquiv (.imax .zero one) one
#guard levelEquiv (.imax one .zero) .zero
#guard levelEquiv (.imax (.succ (u 0)) (.succ (u 0))) (.succ (u 0))
#guard levelEquiv (.succ (.max (u 1) (u 0))) (.max (.succ (u 1)) (.succ (u 0)))
#guard levelEquiv (.max one (.succ (.succ (u 0)))) (.succ (.succ (u 0)))
#guard levelEquiv (imaxChain 40 .zero) .zero
#guard levelEquiv (imaxChain 40 one) one

-- Different under some assignment: none may be related.
#guard !levelEquiv one .zero
#guard !levelEquiv (u 0) (u 1)
#guard !levelEquiv (.max (u 0) (u 1)) (u 0)
#guard !levelEquiv (.imax (u 0) (u 1)) (.max (u 0) (u 1))
#guard !levelEquiv (.imax one (u 0)) one
