import Lean4Zfc.Infer

/-!
A sound check that one universe level is at most another under every assignment of its
parameters, and from it a check of level equivalence, the side condition of the judgement's rule
`sortDF`.

`leq a b = true` gives `a ≤ b`, Lean4Lean's order: `a.eval ls ≤ b.eval ls` for every list `ls` of
parameter values. The check reads the levels' syntax by a few rules, each a fact about `Nat.max`
and `Nat.imax`; it is not complete, and its callers refuse a pair it misses.
-/

namespace Lean4Zfc

open Lean4Lean

/-- `l` is zero under every assignment, by its syntax. -/
def isZeroLevel : VLevel → Bool
  | .zero => true
  | .max a b => isZeroLevel a && isZeroLevel b
  | .imax _ b => isZeroLevel b
  | _ => false

theorem isZeroLevel_sound : ∀ {l : VLevel}, isZeroLevel l = true → ∀ ls, l.eval ls = 0
  | .zero, _, _ => rfl
  | .max a b, h, ls => by
    simp only [isZeroLevel, Bool.and_eq_true] at h
    simp only [VLevel.eval, isZeroLevel_sound h.1 ls, isZeroLevel_sound h.2 ls]; rfl
  | .imax _ b, h, ls => by
    simp only [VLevel.eval, isZeroLevel_sound (l := b) h ls, Lean.Nat.imax]; rfl
  | .succ _, h, _ => by simp [isZeroLevel] at h
  | .param _, h, _ => by simp [isZeroLevel] at h

/-- `a` is at most `b` under every assignment, by rules on the levels' syntax. It tries the rules
for `a`'s form and then those for `b`'s, each recursing into both parts of a `max` or an `imax`, so
its cost can grow exponentially with the size of the two levels. -/
def leq (a b : VLevel) : Bool :=
  if a = b then true
  else
    (match a with
      | .zero => true
      | .max a₁ a₂ => leq a₁ b && leq a₂ b
      | .imax a₁ a₂ => isZeroLevel a₂ || (leq a₁ b && leq a₂ b)
      | .succ (.max x y) => leq (.succ x) b && leq (.succ y) b
      | _ => false) ||
    (match b with
      | .max b₁ b₂ => leq a b₁ || leq a b₂
      | .imax _ b₂ => leq a b₂
      | .succ b' => (match a with | .succ a' => leq a' b' | _ => false) || leq a b'
      | _ => false)
termination_by sizeOf a + sizeOf b

theorem imax_le {x y z : Nat} (h : y = 0 ∨ (x ≤ z ∧ y ≤ z)) : Lean.Nat.imax x y ≤ z := by
  unfold Lean.Nat.imax
  split
  · exact Nat.zero_le _
  · rcases h with h | ⟨h1, h2⟩
    · contradiction
    · exact Nat.max_le.mpr ⟨h1, h2⟩

theorem le_imax {x y z : Nat} (h : z ≤ y) : z ≤ Lean.Nat.imax x y := by
  unfold Lean.Nat.imax
  split
  · omega
  · exact Nat.le_trans h (Nat.le_max_right _ _)

theorem leq_sound (a b : VLevel) (h : leq a b = true) (ls : List Nat) :
    a.eval ls ≤ b.eval ls := by
  unfold leq at h
  split at h
  · subst_vars; exact Nat.le_refl _
  · simp only [Bool.or_eq_true] at h
    rcases h with h | h
    · split at h
      · exact Nat.zero_le _
      · rename_i a₁ a₂ _
        simp only [Bool.and_eq_true] at h
        have h1 := leq_sound a₁ b h.1 ls
        have h2 := leq_sound a₂ b h.2 ls
        exact Nat.max_le.mpr ⟨h1, h2⟩
      · rename_i a₁ a₂ _
        simp only [Bool.or_eq_true, Bool.and_eq_true] at h
        apply imax_le
        rcases h with h | ⟨h1, h2⟩
        · exact .inl (isZeroLevel_sound h ls)
        · exact .inr ⟨leq_sound a₁ b h1 ls, leq_sound a₂ b h2 ls⟩
      · rename_i x y _
        simp only [Bool.and_eq_true] at h
        have h1 := leq_sound (.succ x) b h.1 ls
        have h2 := leq_sound (.succ y) b h.2 ls
        simp only [VLevel.eval, Nat.max_def] at h1 h2 ⊢
        split <;> omega
      · simp at h
    · split at h
      · rename_i b₁ b₂ _
        simp only [Bool.or_eq_true] at h
        simp only [VLevel.eval]
        rcases h with h | h
        · exact Nat.le_trans (leq_sound a b₁ h ls) (Nat.le_max_left _ _)
        · exact Nat.le_trans (leq_sound a b₂ h ls) (Nat.le_max_right _ _)
      · rename_i b₁ b₂ _
        simp only [VLevel.eval]
        exact le_imax (leq_sound a b₂ h ls)
      · rename_i b' _
        simp only [Bool.or_eq_true] at h
        simp only [VLevel.eval]
        rcases h with h | h
        · split at h
          · rename_i a' _
            have := leq_sound a' b' h ls
            simp only [VLevel.eval]
            omega
          · simp at h
        · have := leq_sound a b' h ls
          omega
      · simp at h
termination_by sizeOf a + sizeOf b

/-- `a` and `b` have the same value under every assignment, by `leq` both ways. -/
def levelEquiv (a b : VLevel) : Bool := leq a b && leq b a

theorem levelEquiv_sound {a b : VLevel} (h : levelEquiv a b = true) : a ≈ b := by
  simp only [levelEquiv, Bool.and_eq_true] at h
  exact VLevel.le_antisymm_iff.mpr ⟨fun ls => leq_sound a b h.1 ls, fun ls => leq_sound b a h.2 ls⟩

end Lean4Zfc
