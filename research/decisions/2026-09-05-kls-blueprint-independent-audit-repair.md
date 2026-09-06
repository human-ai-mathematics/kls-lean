# KLS Blueprint independent-audit repair

**Decision date:** 2026-09-05 (Asia/Shanghai).

**Type:** Blueprint interface choice and debt-reduction repair.

## Authority and decision rule

The repository owner asked for the alternatives identified by the independent prompt audit to be
resolved in whichever way best supports later Lean formalization and proof while leaving the least
semantic debt.  This record covers that follow-up repair.  It does not rewrite the earlier
`2026-09-05-kls-blueprint-freeze-review-followup.md` snapshot; for the current interface choices
and validation counts, this newer record supersedes that snapshot.

The working tree is based on `70ca1c19c4d207a31716c2e589c0b096521a5490`.  No commit, push,
remote-CI claim, Lean proof claim, or human freeze claim is made here.

## Chosen interfaces

### Log-concavity and density

- `def:log-concave-law` uses compact sets.  Their Minkowski combination is compact and hence
  Borel, so the definition does not force Lean to evaluate a measure on a potentially non-Borel
  set.
- `thm:compact-borell-logconcavity-equivalence` is the named bridge to the literature's
  inner-measure Borell formulation for Borel sets.  Keeping the bridge separate prevents an
  implementation from silently substituting Mathlib outer measure for inner measure.
- `thm:borell-logconcave-density` works on the intrinsic affine-support direction.  Its convex
  carrier is the closed convex hull of the topological support; the statement records a conull
  interior, an upper-semicontinuous log-concave density, positivity, local upper and lower bounds,
  all moments, and the zero-dimensional convention needed by later energy arguments.

### Sequential closure rather than an unspecified core

- `thm:smooth-gradient-raw-core-agreement-density` now assumes an explicit open conull set and a
  density that is positive almost everywhere with locally essentially bounded density and
  reciprocal.
- Its formal conclusion is raw agreement on tests and `IsSequentialCoreFor` for the energy defined
  by sequential `L²` relaxation.  Graph-norm density is deliberately left in
  `q:smooth-gradient-raw-core-agreement`; it is not conflated with the existing Lean predicate.

### Named isoperimetric and affine frontends

- `thm:klartag-density-frontend-identification` isolates the nontrivial identification between
  affine-support outer Minkowski boundary measure, the smooth-boundary density formula, and the
  intrinsic locally-Lipschitz Poincare formulation.  The node stays `\notready` until its precise
  regularization source and density-representative convention are frozen.
- `lem:ambient-intrinsic-covariance` records the restriction, operator-norm, nondegeneracy, and
  zero-dimensional facts that whitening needs.
- `def:affine-poincare-constant` defines `C_P^aff` from a globally Lipschitz covariance
  pre-energy by sequential `L²` relaxation.  It is a closed-form route constant, not the raw
  locally-Lipschitz optimum.
- `thm:affine-covariance-relaxation-closed` records closability, agreement on the test class, and
  agreement with the pinned CMH closed covariance form under the translation-induced `L²`
  isometry.  It does not claim literal equality between carriers with different affine origins.
- `lem:affine-poincare-translation-invariance` makes the centered-to-arbitrary-law step explicit
  rather than silently changing the quantifier in the CMH corollary.
- `thm:affine-isotropic-reduction` now names three equivalent uniform formulations: isotropic
  literature Poincare, ambient covariance-scaled literature Poincare, and bounded `C_P^aff`.
  `thm:cmh-recovery-affine-poincare-bound` packages the two pinned upstream facts actually used by
  the CMH route: lower semicontinuity of `C_P^aff` along ambient-`W₂` recovery and the regular-class
  inequality `C_P^aff ≤ CMH`.  The route corollary consumes this named theorem rather than hiding
  either input in proof prose.

### Route composition

- Repository integration metadata is named `adapters`, not `prerequisites`.
- The checker requires the root of `conj:kls.adapters` to be `all_of`, and a negative unit test
  rejects `any_of`.  This prevents a later metadata edit from turning jointly required analytic
  identifications into alternatives.
- The refuted `eldan-weighted-package-v1` branch is unchanged.

## Provenance and status

The Cattiaux--Guillin bibliography entry now distinguishes the cited 2018 arXiv equation from the
2020 publication metadata.

Seven named nodes were added by this repair:

1. `thm:compact-borell-logconcavity-equivalence`;
2. `thm:klartag-density-frontend-identification`;
3. `lem:ambient-intrinsic-covariance`;
4. `def:affine-poincare-constant`;
5. `thm:affine-covariance-relaxation-closed`;
6. `lem:affine-poincare-translation-invariance`;
7. `thm:cmh-recovery-affine-poincare-bound`.

Only the Klartag frontend node receives a new `\notready` marker because its public normalization
is still deliberately unfrozen.  The other six statements have fixed interfaces but open proofs;
under the Blueprint status contract, an open proof alone is not a reason for `\notready`.  No
`\leanok` marker, Lean source file, production ledger entry, or source pin was changed.  The
working tree has 73 labels and 13 `\notready` nodes.

## Local validation

The resulting working tree passed:

- `python3 research/check_ledger.py`:
  `1 ledger(s), 4 nodes. 0 error(s).`
- `python3 research/check_blueprint.py`:
  `1 Blueprint schema v2, 7 chapter file(s), 73 labels, 4 active routes. 0 error(s).`
- `python3 -m unittest discover -s research/tests -p 'test_*.py'`:
  `Ran 63 tests`; `OK`.
- `git diff --check`: exit status zero with no output.
- `/tmp/kls-blueprint-venv/bin/python formalization/blueprint/build.py all`: PDF, web output, and
  `checkdecls` completed successfully.

The generated PDF has 27 A4 pages.  The final LaTeX and BibTeX logs have no unresolved reference,
undefined citation, multiply-defined label, overfull box, or BibTeX warning.  Eight underfull-box
layout warnings remain; one is in the edited open-core paragraph and seven predate this repair.
No full page-by-page visual inspection is claimed.  `lake build` was not rerun because no Lean
source or declaration mapping changed.

During the final status inspection, four untracked files with a ` 2` suffix and 2026-09-04
timestamps became visible: `formalization/FunctionalInequalities/Poincare/README 2.md`,
`formalization/blueprint/route-composition 2.yaml`, `research/check_blueprint 2.py`, and
`research/tests/test_check_blueprint 2.py`.  They are older, divergent snapshots and are not read
by the validated commands above.  This repair did not create, edit, delete, or adopt them; cleanup
requires a separate owner decision.
