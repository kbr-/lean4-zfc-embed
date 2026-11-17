import Lean4Lean.Theory.Typing.Strong
import ConLeche.SetModel.Ops

/-!
A value-directed set interpretation of Lean4Lean's `VExpr`, and its substitution lemmas.

Binders read their regime (proposition or data) off the values, through Con-Leche's `piV` and
`lamV`; no typing judgement is consulted.
-/

namespace Lean4Zfc

open Lean4Lean ConLeche ConLeche.SetTheory ConLeche.SetModel

universe w

variable {V : Type w} [SetTheory V]

/-- Extend a variable environment at index `0`. -/
def push (x : V) (ρ : Nat → V) : Nat → V
  | 0 => x
  | i + 1 => ρ i

/-- The set a term denotes, given a value for each constant at each level valuation `cval`,
a level valuation `L` and a variable environment `ρ`. -/
noncomputable def interp (cval : Name → List Nat → V) (L : List Nat) : (Nat → V) → VExpr → V
  | ρ, .bvar i => ρ i
  | _, .sort u => univ (u.eval L)
  | _, .const c ls => cval c (ls.map (VLevel.eval L))
  | ρ, .app f a => app (interp cval L ρ f) (interp cval L ρ a)
  | ρ, .lam A b => lamV (interp cval L ρ A) (fun x => interp cval L (push x ρ) b)
  | ρ, .forallE A B => piV (interp cval L ρ A) (fun x => interp cval L (push x ρ) B)

variable {cval : Name → List Nat → V} {L : List Nat}

omit [SetTheory V] in
theorem push_liftVar (x : V) (ρ : Nat → V) (n k : Nat) :
    (fun i => push x ρ (liftVar n i (k + 1))) = push x (fun i => ρ (liftVar n i k)) := by
  funext i
  cases i with
  | zero => simp [push]
  | succ i => simp [push]

theorem interp_liftN (e : VExpr) (n k : Nat) (ρ : Nat → V) :
    interp cval L ρ (e.liftN n k) = interp cval L (fun i => ρ (liftVar n i k)) e := by
  induction e generalizing k ρ with
  | bvar i => simp [VExpr.liftN, interp]
  | sort u => simp [VExpr.liftN, interp]
  | const c ls => simp [VExpr.liftN, interp]
  | app f a ihf iha => simp [VExpr.liftN, interp, ihf, iha]
  | lam A b ihA ihb =>
    simp only [VExpr.liftN, interp, ihA]
    congr 1
    funext x
    rw [ihb, push_liftVar]
  | forallE A B ihA ihB =>
    simp only [VExpr.liftN, interp, ihA]
    congr 1
    funext x
    rw [ihB, push_liftVar]

theorem interp_lift (e : VExpr) (x : V) (ρ : Nat → V) :
    interp cval L (push x ρ) e.lift = interp cval L ρ e := by
  rw [VExpr.lift, interp_liftN]
  congr 1
  funext i
  simp [push]

/-- The environment reading index `k` as the value of `a` (weakened past `k` binders). -/
noncomputable def substEnv (cval : Name → List Nat → V) (L : List Nat) (a : VExpr) (k : Nat)
    (ρ : Nat → V) : Nat → V :=
  fun i => if i < k then ρ i else if i = k then interp cval L (fun j => ρ (j + k)) a else ρ (i - 1)

theorem push_substEnv (x : V) (a : VExpr) (k : Nat) (ρ : Nat → V) :
    substEnv cval L a (k + 1) (push x ρ) = push x (substEnv cval L a k ρ) := by
  funext i
  cases i with
  | zero => simp [substEnv, push]
  | succ i =>
    simp only [substEnv, push, Nat.succ_lt_succ_iff, Nat.succ.injEq]
    split
    · rfl
    · split
      · congr 1
      · rename_i h1 h2
        have : 0 < i := by omega
        obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
        simp

theorem interp_inst (e a : VExpr) (k : Nat) (ρ : Nat → V) :
    interp cval L ρ (e.inst a k) = interp cval L (substEnv cval L a k ρ) e := by
  induction e generalizing k ρ with
  | bvar i =>
    simp only [VExpr.inst, VExpr.instVar, interp, substEnv]
    split
    · simp [interp]
    · split
      · rw [interp_liftN]; congr 1; funext j; simp
      · simp [interp]
  | sort u => simp [VExpr.inst, interp]
  | const c ls => simp [VExpr.inst, interp]
  | app f b ihf ihb => simp [VExpr.inst, interp, ihf, ihb]
  | lam A b ihA ihb =>
    simp only [VExpr.inst, interp, ihA]
    congr 1
    funext x
    rw [ihb, push_substEnv]
  | forallE A B ihA ihB =>
    simp only [VExpr.inst, interp, ihA]
    congr 1
    funext x
    rw [ihB, push_substEnv]

theorem substEnv_zero (a : VExpr) (ρ : Nat → V) :
    substEnv cval L a 0 ρ = push (interp cval L ρ a) ρ := by
  funext i
  cases i with
  | zero => simp [substEnv, push]
  | succ i => simp [substEnv, push]

theorem interp_inst0 (e a : VExpr) (ρ : Nat → V) :
    interp cval L ρ (e.inst a) = interp cval L (push (interp cval L ρ a) ρ) e := by
  rw [interp_inst, substEnv_zero]

theorem interp_instL (e : VExpr) (ls : List VLevel) (ρ : Nat → V) :
    interp cval L ρ (e.instL ls) = interp cval (ls.map (VLevel.eval L)) ρ e := by
  induction e generalizing ρ with
  | bvar i => simp [VExpr.instL, interp]
  | sort u => simp [VExpr.instL, interp, VLevel.eval_inst]
  | const c us => simp [VExpr.instL, interp, VLevel.eval_inst, Function.comp_def]
  | app f a ihf iha => simp [VExpr.instL, interp, ihf, iha]
  | lam A b ihA ihb => simp only [VExpr.instL, interp, ihA]; congr 1; funext x; rw [ihb]
  | forallE A B ihA ihB => simp only [VExpr.instL, interp, ihA]; congr 1; funext x; rw [ihB]

end Lean4Zfc
