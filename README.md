# Lean 4's type theory in set theory

A Lean proof that the type theory of Lean 4, as [Lean4Lean](https://github.com/digama0/lean4lean)
formalizes it, has a sound interpretation in set theory, so that an environment with a model proves
no falsity; and that two families of environments have a model, assuming a sequence of inaccessible
cardinals: those built from definitions, and those certified against a run of a checker. A certified
environment and its certificate are computed from the checker's result by a function proved correct;
it holds the constants that function can type, which can be fewer than the checker's. The sets are
any model of the set theory of [Con-Leche](https://github.com/leanprover/con-leche); under the
cardinal hypothesis Con-Leche builds one on Mathlib's type `ZFSet` of sets.

Both packages build with Lean v4.35.0, the one under `inaccessibles/` against an existing build of
Mathlib and not from a fresh clone, and the general theorems depend on no axiom beyond `propext`,
`Classical.choice` and `Quot.sound`. Read the section Limits before citing a result: the theorems
are about Lean4Lean's theory and about environments built from definitions or certified against a
checker's run, and say nothing of the official kernel.

## What is proved

The theory is Lean4Lean's judgement `VEnv.IsDefEq env U Γ e e' A`: in the environment `env`, with
`U` level parameters and the context `Γ`, the terms `e` and `e'` are definitionally equal at type
`A`. Typing is the case `e = e'`. An environment is a set of constants with their types and a set of
stored equations; definitions, inductive types and quotients enter the theory only through those.

**The interpretation** (`Lean4Zfc/Interp.lean`). `interp cval L ρ e` is a set: the denotation of the
term `e`, given a value `cval` for each constant, a value `L` for each level parameter and a value
`ρ` for each bound variable. A sort denotes Con-Leche's universe `univ` at the value of its level. A
binder is read as a proposition or as data from the values it ranges over, through Con-Leche's
operations `piV` and `lamV`, so the interpretation consults no typing judgement.

**Soundness** (`Lean4Zfc/Fundamental.lean`). A model of an environment, `EnvModel env cval`, asks
two things at every level valuation: each constant's value is a member of the denotation of its
type, and the two sides of each stored equation have the same denotation.

```lean
theorem fundamental {env : VEnv} {U : Nat} {Γ : List VExpr} {e e' A : VExpr}
    (M : EnvModel env cval) (H : env.IsDefEqStrong U Γ e e' A) :
    ∀ (L : List Nat) (ρ : Nat → V), Sat cval L Γ ρ →
      interp cval L ρ e = interp cval L ρ e' ∧ interp cval L ρ e ∈ˢ interp cval L ρ A
```

`IsDefEqStrong` is a form of the judgement whose rules carry extra premises, which Lean4Lean derives
from `IsDefEq` for an ordered environment (`IsDefEq.strong`). So an ordered environment with a model
types no closed term at `∀ (p : Prop), p`, written `falseE` (`no_proof_of_false`). The proof uses
neither unique typing nor inversion of sorts. In Lean4Lean, `Theory/Typing/Injectivity.lean` leaves
the inversion of sorts and two more lemmas as `sorry`, and the proof of unique typing calls it.

**Environments with a model.** These are proved to have one.

- `Built.consistent` (`Lean4Zfc/Built.lean`): every environment built from the empty one by
  definitions, opaque constants and examples.
- `checked_consistent` (`Lean4Zfc/Checked.lean`): every environment *certified* against one that
  Con-Leche's checker accepts. Con-Leche proves that an environment its checker accepts has a model
  of its constants (`Cached.checkDecls_sound`), and its checker accepts inductive types, the
  quotient constants and the axioms `propext` and `Classical.choice`. A certificate,
  `CertOrdered cenv lp env`, builds the Lean4Lean environment `env` one constant and one stored
  equation at a time, each typed in the theory and each matched in the accepted environment `cenv`:
  a constant by the stored constant of the same name, level parameters and type, an equation by a
  stored constant whose type is that equation.
- `generated_consistent` (`Lean4Zfc/Generate.lean`): the environment `generate cenv`, computed from
  the accepted environment `cenv`. The generator walks the checker's constants, oldest first, and
  adds each one whose type is a Lean4Lean term typed at a sort by `inferType`
  (`Lean4Zfc/Infer.lean`), a type inferencer that reduces nothing and is proved sound
  (`inferType_sound`); a constant whose type is an equation `@Eq T a b` with both sides typed at `T`
  also adds the stored equation. `generate_certOrdered` proves the result certified, with no
  hypothesis, so this theorem asks only the checker's acceptance.

**From inaccessible cardinals** (`inaccessibles/Lean4ZfcInaccessibles.lean`). The hypothesis is the
one of the `consistency` statement in lean4lean-model, a strictly increasing sequence of
inaccessible cardinals:

```lean
def OmegaInaccessibles : Prop :=
  ∃ κ : ℕ → Cardinal.{u}, StrictMono κ ∧ ∀ n, (κ n).IsInaccessible
```

```lean
theorem consistent_of_omegaInaccessibles (h : ConLecheBridge.OmegaInaccessibles.{u})
    {ds : List VDecl} {env : VEnv} {U : Nat} (hb : Built ds env) :
    ¬ ∃ e, env.HasType U [] e falseE

theorem checked_consistent_of_omegaInaccessibles (h : ConLecheBridge.OmegaInaccessibles.{u})
    (pins : List ConLeche.NatOpPinSet) (maxNatSize : Nat) (ds : Array ConLeche.Declaration)
    {cenv : ConLeche.Env}
    (accepted : ConLeche.Cached.checkDecls .verified pins maxNatSize ds = .ok cenv)
    {lp : Lean.Name → List ConLeche.Name} {env : VEnv} {U : Nat}
    (hc : CertOrdered cenv lp env) :
    ¬ ∃ e, env.HasType U [] e falseE

theorem generated_consistent_of_omegaInaccessibles (h : ConLecheBridge.OmegaInaccessibles.{u})
    (pins : List ConLeche.NatOpPinSet) (maxNatSize : Nat) (ds : Array ConLeche.Declaration)
    {cenv : ConLeche.Env}
    (accepted : ConLeche.Cached.checkDecls .verified pins maxNatSize ds = .ok cenv) {U : Nat} :
    ¬ ∃ e, (generate cenv).HasType U [] e falseE
```

## Why the theorems have hypotheses about the environment

Lean4Lean has its own predicate for well-formed environments, `VEnv.WF`. It is not used here. Its
rule for an axiom asks only that the axiom's type is a type, so it accepts an environment with an
axiom of type `∀ (p : Prop), p`; `Lean4Zfc/Falsity.lean` proves that such an environment is ordered
and does type a closed term at `falseE` (`badEnv_proves_false`), and hence has no model.
`Lean4ZfcTest/UpstreamWF.lean` proves that `VEnv.WF` holds of that environment (`badEnv_wf`). So the
conclusion of lean4lean-model's `consistency` statement, which is stated over every `VEnv.WF`
environment under the cardinal hypothesis, fails for one of them: that statement can hold only if no
such sequence of cardinals exists. And the predicate mentions inductive declarations, which
Lean4Lean's `Theory/Inductive.lean` defines as `sorry`, so every theorem naming `VEnv.WF` depends on
`sorryAx`.

The same file proves that `falseE` is a proposition in every environment (`falseE_isType`): the
theorems' conclusion is about a type of the theory.

## The example

`Lean4Zfc/Example/` certifies one small environment twice: by hand, and with the generator. It runs
Con-Leche's checker inside Lean on Con-Leche's test fixture `tests/e2e/corner_punit_own.ndjson`,
which declares

```lean
inductive PUnit : Type where
  | unit : PUnit
  | other : PUnit

def f : PUnit := PUnit.other
```

followed by one theorem written in the export's format, `f_eq : @Eq PUnit f PUnit.other`. The
Lean4Lean environment holds `PUnit`, its two constructors, its recursor (which has a level
parameter) and `f`, each certified against the constant the checker stored, and the stored equation
`f ≡ PUnit.other`, certified by `f_eq`. `env_consistent` concludes that it types no closed term at
`falseE`, and `f_defeq` derives the equation in it.

The checker's run and each comparison of stored constants is evaluated by compiled code
(`native_decide`), so `env_consistent` depends on seven axioms of compiled evaluation beside the
three standard ones. The general theorems do not, and the library's root module does not import the
example. With `f_eq` changed to the false equation `f = PUnit.unit` (`data/f_eq_false.ndjson`), the
checker rejects the export: `Lean4ZfcTest/Example.lean` proves it (`false_export_rejected`).

`Lean4Zfc/Example/PUnitGenerated.lean` runs the generator on the same result of the checker. It
keeps every constant the checker's environment holds, the export's and the prelude's
(`generated_names`), and finds the one equation (`generated_eqs`); `generated_f_defeq` derives
`f ≡ PUnit.other` in the generated environment and `generated_env_consistent` is its consistency.
The generator's two outputs are evaluated by compiled code as well.

Lake does not track the example's data files: after changing one, change
`Lean4Zfc/Example/PUnitRun.lean` too, or the build reuses the run of the old data.

## Limits

- **The theory is Lean4Lean's.** Its terms have variables, sorts, constants, application, `fun` and
  `∀`, and no `let`, projections or literals. No comparison of its rules with a release of Lean is
  made here.
- **Nothing is said about the official kernel**, or about any checker's implementation beyond what
  Con-Leche proves of its own.
- **The generator is partial.** It leaves out a constant whose type has a `let`, a literal or a
  projection, or that `inferType` can't type without reduction, or whose level parameter names
  repeat, and with it every later constant that mentions it; evaluating `(generated cenv).names`
  lists what it kept. Run on the 580 export fixtures of Con-Leche's `tests/e2e/` (`lake exe reach`;
  a file with no result after one second was abandoned), this repository's run of the checker
  accepted 338, did not accept 240 and gave no answer on 2. On 328 of the accepted the generator
  finished, and of the 20764 constants of those environments, each count including the prelude's, it
  kept 19040, keeping 153 environments whole; the totals are sums over the lines `reach` prints. On
  the other ten, among them `tower_beqpair`, which Con-Leche's own binary accepts at once, the
  generator did not finish within the second; how long it takes there was not measured. The
  generated environment holds an equation only where a constant of the accepted environment has it
  as its type, `@Eq T a b`: a definition's unfolding and a recursor's computation rule are not added
  from the checker's reduction. Whether Con-Leche's checker and Lean4Lean's theory accept the same
  environments is not addressed.
- **The result is a Lean theorem with a hypothesis.** `OmegaInaccessibles` is assumed, over
  Mathlib's `ZFSet`. No theorem of first-order set theory about an encoding of the type theory is
  derived from it.
- **Con-Leche's coverage is taken from Con-Leche.** That its checker accepts `propext` and
  `Classical.choice` is read from its `ConLeche/Kernel/StdAxioms.lean`; no export using them was run
  here.

## Layout

| Path | Holds |
|---|---|
| `Lean4Zfc/Interp.lean` | The interpretation and its substitution lemmas |
| `Lean4Zfc/Fundamental.lean` | `EnvModel`, `fundamental`, `no_proof_of_false` |
| `Lean4Zfc/Falsity.lean` | `falseE_isType`, `badEnv_proves_false`, `badEnv_no_model` |
| `Lean4Zfc/Definition.lean` | `EnvModel.addDef`: a definition extends a model |
| `Lean4Zfc/Built.lean` | `Built`, `Built.consistent` |
| `Lean4Zfc/Bridge.lean` | The translation into Con-Leche's terms, `CertOrdered`, `CertOrdered.consistent` |
| `Lean4Zfc/Checked.lean` | `checked_consistent` |
| `Lean4Zfc/Infer.lean` | `inferType`, `inferType_sound` |
| `Lean4Zfc/Generate.lean` | `generate`, `generate_certOrdered`, `generated_consistent` |
| `Lean4Zfc/Example/` | The example, certified by hand and by the generator, and its data |
| `Reach.lean` | `lake exe reach FILE...`: how many constants of each export the generator keeps |
| `Lean4ZfcTest/` | The axioms of each theorem, pinned: a `sorry` reaching one fails the build; the rejected false export; `badEnv_wf` |
| `inaccessibles/` | A Lake package of its own, the only part that needs Mathlib: the theorems above |
| `patches/` | The changes that build Lean4Lean's theory at Lean v4.35.0 |

## Building

Both packages require their dependencies by path from sibling checkouts, so that existing builds are
reused. Beside this repository, in `../lean4-zfc-sources/`:

- `con-leche`: [Con-Leche](https://github.com/leanprover/con-leche) at
  `d88e04e9b25ca48e5f9f90c07f2493fbc2b489e8`, which pins Lean v4.35.0.
- `lean4lean-435`: [Lean4Lean](https://github.com/digama0/lean4lean) at
  `67f63b0c818920dfaed2ad07ccff187a6a8fe1e3` with `patches/lean4lean-v4.35.0.patch` applied
  (`git apply`). Upstream pins Lean v4.33.0-rc2; the patch changes the toolchain file, requires
  Batteries by path, and removes one rewrite that no longer applies.
- `batteries-435`: [Batteries](https://github.com/leanprover-community/batteries) at its tag
  `v4.35.0`.

Then, with Lean v4.35.0 installed through Elan:

```sh
lake build                       # the library, the example and their axiom checks
cd inaccessibles && lake build   # the theorems under inaccessible cardinals
```

The second build needs Mathlib at its tag `v4.35.0`; `inaccessibles/lake-manifest.json` pins the
revisions. To reuse a Mathlib already built on the machine, link `inaccessibles/.lake/packages` to
its package directory before building.

## Sources and licence

This repository is under the Apache License 2.0, as are Lean4Lean and Con-Leche. It contains no code
of either; `Lean4Zfc/Example/data/corner_punit_own.ndjson` is Con-Leche's test fixture, unchanged,
and `patches/lean4lean-v4.35.0.patch` is a change to Lean4Lean's files.
