# Finite tensorization statement preparation: validation

Date: 2026-09-03 (Asia/Shanghai). Node: `lem:poincare-finite-tensorization`.
Issue: [#7](https://github.com/human-ai-mathematics/kls-lean/issues/7), confirmed by the
GitHub sub-issue endpoint under #1. Baseline/current HEAD:
`4801ca958778ae02cc0d81fc7ec805a4e96a894c`, branch `main`.

## Delivered state

The working tree was clean at the start. The current candidate is local, uncommitted and
unpublished. The node is **drafted / checked_by: null**. No human freeze or proof acceptance
has occurred, and no proof agent was started. GitHub issue creation/parent linkage is complete;
creating the issue did not publish the Lean skeleton.

Five reusable/project Lean modules and one default-build solution entry point were added.
There are 53 candidate public declarations: 49 theorem statements, three definitions, and one
probability instance. Exactly 52 new mathematical obligations use `sorry` (49 theorem bodies,
two norm-preservation fields, and the probability instance). The `piMeasure` definition itself
is the concrete measure pushforward. The new linear maps are concrete constructions, with
norm-preservation proof fields deferred. No existing proof was changed.

## Required repository commands

From the repository root:

```text
$ python3 research/check_ledger.py
1 ledger(s), 3 nodes. 0 error(s).

$ python3 -m unittest discover -s research/tests -p 'test_*.py'
Ran 24 tests
OK

$ cd formalization && lake build
Build completed successfully (2959 jobs).
```

All commands exited zero. The default build reports exactly 52 expected new
`declaration uses sorry` warnings and no other warnings. It compiles the Euclidean statements
and typed applications through `solutions/LemPoincareFiniteTensorization.lean`, which is an
additional root of the existing default `Issue2Solutions` target. This is local compilation
with the pinned dependency cache, not a claim of a fresh clean-checkout proof build or remote CI
for the uncommitted changes.

The retained Mathlib audit also exits zero:

```bash
cd formalization
lake env lean ../research/explorations/2026-09-03-finite-tensorization-mathlib-api.lean
```

It checks the actual projection, splitting, reindexing, measure, finite-induction and
transport APIs, and synthesizes the dependent `PiLp 2` Hilbert, complete, Borel and
second-countable instances. Earlier exploratory spelling/pretty-printer errors were corrected;
the delivered scripts and signatures elaborate successfully.

## Candidate snapshots and Euclidean checks

The complete output of

```bash
cd formalization
lake env lean ../solutions/LemPoincareFiniteTensorization.lean
```

is [the 454-line signature snapshot](2026-09-03-finite-tensorization-signatures.txt), containing
all 53 public types with implicit and universe/typeclass parameters exposed.
SHA-256 including the final newline:
`26f387cbaaf2ce631c02dd79bfebf36f5514e922dd60bf8287fc7a690ac6aed4`.
The verbatim drafted ledger `statement` string has SHA-256 (without an extra newline)
`61ff1d1a7e1258d7cc3e68dae5ebc8111fefb9ac4d4baab1e10b797c948366ab`.
Both are reproduced in the [candidate review package](../decisions/2026-09-03-finite-tensorization-candidate.md).

`Project/PoincareFiniteTensorization.lean` contains arbitrary-dimension family fixed/optimal
statements, binary reverse/equality statements, and explicit empty, singleton, all-zero and
individual mixed-zero-factor statements. Its typed applications check the generic API for:

- arbitrary finite dependent Euclidean families and fixed constants;
- binary `(0,n)` and `(n,0)` dimensions;
- an empty `Fin 0` family, both fixed constant zero and optimal constant zero;
- a zero-dimensional `Fin 1` family;
- two zero-dimensional factors.

The standalone empty statement has no factor probability assumptions, since there are no
factors. The generic theorem still states a probability instance for every index, which is
vacuous when the index is empty. The singleton statement accepts every natural-number
dimension. These are statement/application elaboration checks with placeholders, not proofs
that the new conclusions hold.

## Preservation of the proved nodes

A byte comparison against HEAD verified that all 13 pre-existing tracked Lean files, toolchain
and manifest files are unchanged. In particular, `Basic.lean`, the linear-test/covariance API,
all accepted binary product/variance/admissibility/tensorization proofs, both project wrappers,
and both solution certificates are unchanged. The root aggregate module is also unchanged;
neither proved certificate's local import closure reaches a new draft module.

Both pre-existing ledger node objects compare equal to the baseline, including their
statements and `proved` / `checked_by: lean` metadata. The unchanged checker passed their
certificate and recursive local-import escape-token guards. No weakening of the checker,
schema rules or Python tests was needed.

The output of `#check @FunctionalInequalities.Poincare.Holds.prod` and
`#check @FunctionalInequalities.Poincare.constant_prod_le` matches the accepted
`2026-09-03-tensorization-freeze.md` text **byte for byte**. Its hash remains
`75e576722a02a1c49588534389331ed1f493fec233ee21756e348c23f8424d0a`.
The frozen binary ledger-statement hash remains
`a261a6b244ad4e7ea36dd0478f268e8f2d9fad6b5cd99e22317f36bd99075234`.

A fresh `#print axioms` inspection of 14 existing declarations reports only the accepted
foundation; none contains `sorryAx`:

```text
'Solutions.LemLinearTestLower.certificate' depends on axioms: [propext, Classical.choice, Quot.sound]
'FunctionalInequalities.Project.LinearTestLower.covariance' depends on axioms: [propext, Classical.choice, Quot.sound]
'FunctionalInequalities.Project.LinearTestLower.certificate' depends on axioms: [propext, Classical.choice, Quot.sound]
'FunctionalInequalities.Project.LinearTestLower.euclidean' depends on axioms: [propext, Classical.choice, Quot.sound]
'FunctionalInequalities.Poincare.Holds.prod' depends on axioms: [propext, Classical.choice, Quot.sound]
'FunctionalInequalities.Poincare.constant_prod_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'FunctionalInequalities.Project.PoincareTensorization.fixed_constant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'FunctionalInequalities.Project.PoincareTensorization.optimal_constant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'FunctionalInequalities.Project.PoincareTensorization.certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'FunctionalInequalities.Project.PoincareTensorization.euclidean_fixed_constant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'FunctionalInequalities.Project.PoincareTensorization.euclidean_optimal_constant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'FunctionalInequalities.Project.PoincareTensorization.euclidean_certificate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Solutions.LemPoincareTensorization.certificate' depends on axioms: [propext, Classical.choice, Quot.sound]
'Solutions.LemPoincareTensorization.euclidean_certificate' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The inspected names are exactly those in the output above, obtained after importing
`solutions.LemLinearTestLower` and `solutions.LemPoincareTensorization`. To reproduce, run
`#print axioms` on each displayed name with `lake env lean` in the current project.
This audit certifies continued foundation dependencies of the existing proofs; the new draft
is deliberately unproved and is not represented as passing a proof axiom audit.

## Human handoff

Statement preparation is complete. Review the entire candidate signature/definition/ledger
package, especially factor normalization, dependent Hilbert norm, Option ordering, the real
cast of the finite supremum, empty-zero convention, extended infinity/nonattainment handling,
and integrability assumptions in the lifting/transport helpers. Append a human freeze record
before the separate proof phase. The future proof certificate, promotion and final-commit CI
remain Issue #7 acceptance tasks, not accomplishments of this draft stage.
