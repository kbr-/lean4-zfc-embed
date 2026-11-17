# Lean 4's type theory in set theory

A Lean proof that the type theory of Lean 4, as [Lean4Lean](https://github.com/digama0/lean4lean)
formalizes it, has a sound interpretation in set theory, and so proves no falsity, assuming a
sequence of inaccessible cardinals. The sets are any model of the set theory of
[Con-Leche](https://github.com/leanprover/con-leche); under the cardinal hypothesis Con-Leche
builds one on Mathlib's type `ZFSet` of sets.

Everything here is checked by Lean v4.35.0, and the general theorems depend on no axiom beyond
`propext`, `Classical.choice` and `Quot.sound`. Read the section Limits before citing a result:
the theorems are about Lean4Lean's theory and about environments given with a certificate, and say
nothing of the official kernel.

## What is proved

The theory is Lean4Lean's judgement `VEnv.IsDefEq env U Γ e e' A`: in the environment `env`, with
`U` level parameters and the context `Γ`, the terms `e` and `e'` are definitionally equal at type
`A`. Typing is the case `e = e'`. An environment is a set of constants with their types and a set
of stored equations; definitions, inductive types and quotients enter the theory only through
those.

**The interpretation** (`Lean4Zfc/Interp.lean`). `interp cval L ρ e` is a set: the denotation of
the term `e`, given a value `cval` for each constant, a value `L` for each level parameter and a
value `ρ` for each bound variable. A sort denotes Con-Leche's universe `univ` at the value of its
level. A binder is read as a proposition or as data from the values it ranges over,
through Con-Leche's operations `piV` and `lamV`, so the interpretation consults no typing
judgement.

**Soundness** (`Lean4Zfc/Fundamental.lean`). A model of an environment, `EnvModel env cval`, asks
two things at every level valuation: each constant's value is a member of the denotation of its
type, and the two sides of each stored equation have the same denotation.

```lean
theorem fundamental {env : VEnv} {U : Nat} {Γ : List VExpr} {e e' A : VExpr}
    (M : EnvModel env cval) (H : env.IsDefEqStrong U Γ e e' A) :
    ∀ (L : List Nat) (ρ : Nat → V), Sat cval L Γ ρ →
      interp cval L ρ e = interp cval L ρ e' ∧ interp cval L ρ e ∈ˢ interp cval L ρ A
```

`IsDefEqStrong` is a form of the judgement whose rules carry extra premises, which Lean4Lean
derives from `IsDefEq` for an ordered environment (`IsDefEq.strong`). So an ordered environment
with a model types no closed term at `∀ (p : Prop), p`, written `falseE` (`no_proof_of_false`).
The proof uses neither unique typing nor inversion of sorts. In Lean4Lean,
`Theory/Typing/Injectivity.lean` leaves the inversion of sorts and two more lemmas as `sorry`, and
the proof of unique typing calls it.

**Environments with a model.** These are proved to have one.

- `Built.consistent` (`Lean4Zfc/Built.lean`): every environment built from the empty one by
  definitions, opaque constants and examples.
- `checked_consistent` (`Lean4Zfc/Checked.lean`): every environment *certified* against one that
  Con-Leche's checker accepts. Con-Leche proves that an environment its checker accepts has a model
  of its constants (`Cached.checkDecls_sound`), and its checker accepts inductive types, the
  quotient constants and the axioms `propext` and `Classical.choice`. A certificate,
  `CertOrdered cenv lp env`, builds the Lean4Lean environment `env` one constant and one stored
  equation at a time, each typed in the theory and each matched in the accepted environment
  `cenv`: a constant by the stored constant of the same name, level parameters and type, an
  equation by a stored constant whose type is that equation.

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
```

## Why the theorems have hypotheses about the environment

Lean4Lean has its own predicate for well-formed environments, `VEnv.WF`. It is not used here. Its rule for an axiom asks only that the axiom's type is a type, so it accepts an
environment with an axiom of type `∀ (p : Prop), p`; `Lean4Zfc/Falsity.lean` proves that such an
environment is ordered and does type a closed term at `falseE` (`badEnv_proves_false`), and hence
has no model. And the predicate mentions inductive declarations, which Lean4Lean's
`Theory/Inductive.lean` defines as `sorry`, so every theorem naming `VEnv.WF` depends on `sorryAx`.

The same file proves that `falseE` is a proposition in every environment (`falseE_isType`): the
theorems' conclusion is about a type of the theory.

## The example

`Lean4Zfc/Example/` certifies one small environment by hand, to show the certificate can be given.
It runs Con-Leche's checker inside Lean on Con-Leche's test fixture
`tests/e2e/corner_punit_own.ndjson`, which declares

```lean
inductive PUnit : Type where
  | unit : PUnit
  | other : PUnit

def f : PUnit := PUnit.other
```

followed by one theorem written in the export's format, `f_eq : @Eq PUnit f PUnit.other`. The
Lean4Lean environment holds `PUnit`, its two constructors, its recursor (which has a level
parameter) and `f`, each certified against the constant the checker stored, and the stored
equation `f ≡ PUnit.other`, certified by `f_eq`. `env_consistent` concludes that it types no closed
term at `falseE`, and `f_defeq` derives the equation in it.

The checker's run and each comparison of stored constants is evaluated by compiled code
(`native_decide`), so the example's theorems depend on seven axioms of compiled evaluation beside
the three standard ones. The general theorems do not, and the library's root module does not
import the example. With `f_eq` changed to the false equation `f = PUnit.unit`, the checker rejects
the export and the build fails.

Lake does not track the example's two data files: after changing one, change
`Lean4Zfc/Example/PUnitRun.lean` too, or the build reuses the run of the old data.

## Limits

- **The theory is Lean4Lean's.** Its terms have variables, sorts, constants, application, `fun`
  and `∀`, and no `let`, projections or literals. No comparison of its rules with a release of
  Lean is made here.
- **Nothing is said about the official kernel**, or about any checker's implementation beyond
  what Con-Leche proves of its own.
- **A certificate is a hypothesis.** It needs, for every constant and stored equation, a typing
  derivation in Lean4Lean's theory. Nothing here produces a certificate from an export: the
  example's is written by hand. Whether Con-Leche's checker and Lean4Lean's theory accept the same
  environments is not addressed.
- **The result is a Lean theorem with a hypothesis.** `OmegaInaccessibles` is assumed, over
  Mathlib's `ZFSet`. No theorem of first-order set theory about an encoding of the type theory is
  derived from it.
- **Con-Leche's coverage is taken from Con-Leche.** That its checker accepts `propext` and
  `Classical.choice` is read from its `Kernel/StdAxioms.lean`; no export using them was run here.

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
| `Lean4Zfc/Example/` | The certified example and its data |
| `Lean4ZfcTest/` | The axioms of each theorem, pinned: a `sorry` reaching one fails the build |
| `inaccessibles/` | A Lake package of its own, the only part that needs Mathlib: the two theorems above |
| `patches/` | The changes that build Lean4Lean's theory at Lean v4.35.0 |

## Building

Both packages require their dependencies by path from sibling checkouts, so that existing builds
are reused. Beside this repository, in `../lean4-zfc-sources/`:

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
cd inaccessibles && lake build   # the two theorems under inaccessible cardinals
```

The second build needs Mathlib at its tag `v4.35.0`; `inaccessibles/lake-manifest.json` pins the
revisions. To reuse a Mathlib already built on the machine, link `inaccessibles/.lake/packages` to
its package directory before building.

## Sources and licence

This repository is under the Apache License 2.0, as are Lean4Lean and Con-Leche. It contains no
code of either; `Lean4Zfc/Example/data/corner_punit_own.ndjson` is Con-Leche's test fixture,
unchanged, and `patches/lean4lean-v4.35.0.patch` is a change to Lean4Lean's files.
