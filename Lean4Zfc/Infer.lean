import Lean4Lean.Theory.Typing.Lemmas

/-!
What the type inferencer of `Convert.lean` needs first: decidable equality of Lean4Lean's terms,
and the type of a variable in a context.
-/

namespace Lean4Zfc

open Lean4Lean

deriving instance DecidableEq for VLevel
deriving instance DecidableEq for VExpr

/-- The type of the variable `i` in the context `Γ`: its entry, lifted past the entries before. -/
def lookupTy : List VExpr → Nat → Option VExpr
  | [], _ => none
  | A :: _, 0 => some A.lift
  | _ :: Γ, i + 1 => (lookupTy Γ i).map VExpr.lift

theorem lookupTy_sound : ∀ {Γ : List VExpr} {i : Nat} {A : VExpr},
    lookupTy Γ i = some A → Lookup Γ i A
  | [], _, _, h => by cases h
  | _ :: _, 0, _, h => by cases h; exact .zero
  | _ :: Γ, i + 1, A, h => by
    simp only [lookupTy, Option.map_eq_some_iff] at h
    obtain ⟨A', h', rfl⟩ := h
    exact .succ (lookupTy_sound h')

end Lean4Zfc
