import Lean4Lean.Theory.Typing.Lemmas

/-!
A type inferencer for Lean4Lean's terms that reduces nothing.

`inferType env U Γ e` computes a type of `e`, and `inferType_sound` proves that a result is a type
of `e` in Lean4Lean's judgement. An application is typed only when the function's inferred type is
literally a `forallE` whose domain is the argument's inferred type, and a binder only when its
parts' inferred types are literally sorts: no definitional equality is decided. So it types fewer
terms than the judgement does, and every term it types is typed by the judgement.
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

/-- A type of `e` in the context `Γ`, with `U` level parameters, found without any reduction. -/
def inferType (env : VEnv) (U : Nat) : List VExpr → VExpr → Option VExpr
  | Γ, .bvar i => lookupTy Γ i
  | _, .sort l => if l.WF U then some (.sort (.succ l)) else none
  | _, .const c ls =>
    match env.constants c with
    | some ci =>
      if (∀ l ∈ ls, l.WF U) ∧ ls.length = ci.uvars then some (ci.type.instL ls) else none
    | none => none
  | Γ, .app f a =>
    match inferType env U Γ f, inferType env U Γ a with
    | some (.forallE A B), some A' => if A = A' then some (B.inst a) else none
    | _, _ => none
  | Γ, .lam A b =>
    match inferType env U Γ A, inferType env U (A :: Γ) b with
    | some (.sort _), some B => some (.forallE A B)
    | _, _ => none
  | Γ, .forallE A B =>
    match inferType env U Γ A, inferType env U (A :: Γ) B with
    | some (.sort u), some (.sort v) => some (.sort (.imax u v))
    | _, _ => none

/-- What `inferType` returns is a type of the term in Lean4Lean's judgement. -/
theorem inferType_sound {env : VEnv} {U : Nat} : ∀ {e : VExpr} {Γ : List VExpr} {A : VExpr},
    inferType env U Γ e = some A → env.HasType U Γ e A
  | .bvar i, Γ, A, h => .bvar (lookupTy_sound h)
  | .sort l, Γ, A, h => by
    simp only [inferType] at h
    split at h
    · cases h; exact VEnv.HasType.sort ‹_›
    · cases h
  | .const c ls, Γ, A, h => by
    simp only [inferType] at h
    split at h
    · rename_i ci hc
      split at h
      · rename_i hw
        cases h
        exact VEnv.HasType.const hc hw.1 hw.2
      · cases h
    · cases h
  | .app f a, Γ, A, h => by
    simp only [inferType] at h
    split at h
    · rename_i A₀ B A' hf ha
      split at h
      · rename_i heq
        cases h
        subst heq
        exact VEnv.HasType.app (inferType_sound hf) (inferType_sound ha)
      · cases h
    · cases h
  | .lam A₀ b, Γ, A, h => by
    simp only [inferType] at h
    split at h
    · rename_i u B hA hb
      cases h
      exact VEnv.HasType.lam (inferType_sound hA) (inferType_sound hb)
    · cases h
  | .forallE A₀ B, Γ, A, h => by
    simp only [inferType] at h
    split at h
    · rename_i u v hA hB
      cases h
      exact VEnv.HasType.forallE (inferType_sound hA) (inferType_sound hB)
    · cases h

end Lean4Zfc
