import Lean4Zfc.Definition
import Lean4Lean.Theory.Typing.EnvLemmas

/-!
Environments built from definitions, opaque constants and examples have a model, hence type
no closed term at `∀ (p : Prop), p`.
-/

namespace Lean4Zfc

open Lean4Lean ConLeche ConLeche.SetTheory ConLeche.SetModel

universe w

variable {V : Type w} [SetTheory V]

/-- The declaration steps: the `def`, `opaque` and `example` rules of Lean4Lean's
`VDecl.WF`, with the same premises. -/
inductive DeclStep : VEnv → VDecl → VEnv → Prop where
  | def {env env' : VEnv} {ci : VDefVal} :
    env.HasType ci.uvars [] ci.value ci.type →
    env.addConst ci.name ci.toVConstant = some env' →
    DeclStep env (.def ci) (env'.addDefEq ci.toDefEq)
  | opaque {env env' : VEnv} {ci : VDefVal} :
    env.HasType ci.uvars [] ci.value ci.type →
    env.addConst ci.name ci.toVConstant = some env' →
    DeclStep env (.opaque ci) env'
  | example {env : VEnv} {ci : VDefVal} :
    env.HasType ci.uvars [] ci.value ci.type →
    DeclStep env (.example ci) env

/-- An environment built from the empty one by a list of modelled steps (latest first). -/
inductive Built : List VDecl → VEnv → Prop where
  | empty : Built [] .empty
  | decl {env env' : VEnv} {d : VDecl} {ds : List VDecl} :
    DeclStep env d env' → Built ds env → Built (d :: ds) env'

theorem DeclStep.ordered {env env' : VEnv} {d : VDecl} (h : DeclStep env d env')
    (ih : env.Ordered) : env'.Ordered := by
  cases h with
  | «def» h1 h2 =>
    refine .defeq (.const ih (h1.isType ih ⟨⟩) h2) ⟨?_, ?_⟩
    · simp [VDefVal.toDefEq]
      rw [← (h1.levelWF ⟨⟩).2.2.instL_id]
      exact .const (VEnv.addConst_self h2) VLevel.id_WF (by simp)
    · exact h1.mono (VEnv.addConst_le h2)
  | «opaque» h1 h2 => exact .const ih (h1.isType ih ⟨⟩) h2
  | «example» _ => exact ih

theorem DeclStep.model {env env' : VEnv} {d : VDecl} (h : DeclStep env d env')
    (henv : env.Ordered) {cval : Name → List Nat → V} (M : EnvModel env cval) :
    ∃ cval' : Name → List Nat → V, EnvModel env' cval' := by
  cases h with
  | «def» h1 h2 =>
    obtain ⟨cval', M', _⟩ := M.addDef henv h1 h2
    exact ⟨cval', M'⟩
  | «opaque» h1 h2 =>
    obtain ⟨cval', M', _⟩ := M.addDef henv h1 h2
    exact ⟨cval', ⟨fun hc => M'.const hc, fun hdf => M'.defeq (.inr hdf)⟩⟩
  | «example» _ => exact ⟨cval, M⟩

theorem Built.ordered_model {ds : List VDecl} {env : VEnv} (h : Built ds env) :
    env.Ordered ∧ ∃ cval : Name → List Nat → V, EnvModel env cval := by
  induction h with
  | empty => exact ⟨.empty, fun _ _ => SetTheory.empty, envModel_empty⟩
  | decl hd _ ih =>
    obtain ⟨hord, cval, M⟩ := ih
    exact ⟨hd.ordered hord, hd.model hord M⟩

/-- An environment built from definitions, opaque constants and examples types no closed term at
`∀ (p : Prop), p`, given any model `V` of the set theory. -/
theorem Built.consistent (V : Type w) [SetTheory V] {ds : List VDecl} {env : VEnv} {U : Nat}
    (h : Built ds env) : ¬ ∃ e, env.HasType U [] e falseE := by
  obtain ⟨hord, cval, M⟩ := h.ordered_model (V := V)
  exact no_proof_of_false hord M

end Lean4Zfc
