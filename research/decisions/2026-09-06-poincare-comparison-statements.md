# First batch of Poincaré comparison statements

Date: 2026-09-06. After foundation cleanup and strict review, the user requested the next Lean
statements according to the plan. Following the foundation guide and Blueprint order, this
batch first prepares ambient/intrinsic and legacy/relaxed bridges, without beginning the
literature frontend, whitening, or long-route proofs.

**Status: both nodes are `drafted / checked_by: null`; all 12 comparison theorems retain `sorry`.**
This is neither a human freeze nor proof acceptance. Starting HEAD is
`70ca1c19c4d207a31716c2e589c0b096521a5490`; earlier uncommitted work is preserved.

## Entry points

- [Comparison guide](../../formalization/FunctionalInequalities/Poincare/Euclidean/README.md): purpose, scope, and concrete use first, followed by proof routes and sources.
- [Ambient/intrinsic statement entry](../../solutions/LemAmbientIntrinsicPoincareComparison.lean): 5 declarations and 4 application checks.
- [Legacy/relaxed statement entry](../../solutions/LemLegacyRelaxedPoincareComparison.lean): 7 comparisons, a check of the raw test-family definition, and 8 application checks.
- [Ledger](../a-series/ledger.yaml): complete specifications and statuses of both new nodes.

Both entries join the default `Solutions` target, but no new proof wrapper named `certificate`
is added. Four new modules follow mathematical responsibility in the existing subject hierarchy,
without draft/proved path separation:

| Module | Definition or statement |
| --- | --- |
| `Poincare.Relaxation` | `TestFamily.ofPreEnergy`; `holds_ofPreEnergy_iff`; `constant_ofPreEnergy_eq` |
| `Energy.Euclidean.AffineComparison` | `SmoothGradientTest.exists_intrinsic_restriction`; `SmoothGradientTest.exists_ambient_extension`; `smoothGradientRelaxation_eq_intrinsicAffineSmoothGradientRelaxation` |
| `Poincare.Euclidean.AffineComparison` | `smoothGradientRelaxationHolds_iff_intrinsicAffine`; `smoothGradientRelaxationConstant_eq_intrinsicAffine` |
| `Poincare.Euclidean.LegacyComparison` | `holds_iff_smoothGradientPreEnergy`; `holds_iff_smoothGradientRelaxation`; `constant_eq_smoothGradientRelaxation`; `holds_iff_intrinsicAffineSmoothGradientRelaxation`; `constant_eq_intrinsicAffineSmoothGradientRelaxation` |

Declarations retain the `FunctionalInequalities` root namespace. `ofPreEnergy` is a direct
definition without a proof placeholder; the other 12 theorems are candidate interfaces awaiting proof.

## Mathematical generality and semantic review

### Abstract comparison

`TestFamily.ofPreEnergy μ P` uses `P.Test`, variance `L2.variance μ (P.toAmbient f)`, and energy
`P.energy f`. `μ` may be a probability law on any measurable space, and `P` any instance of the
existing `PreEnergy` interface on its real `L²`.

Finite comparisons always use `C : NNReal`; the relaxed inequality quantifies only over the
finite-energy domain. Relaxation does not increase energy on concrete tests, giving one
direction. The converse uses the existing finite recovery theorem and variance continuity at
each finite-energy point. Thus no dense realization, quadraticity, Markov property, raw/core
agreement, or agreement of raw energy on realization fibers is needed.

The route retains `C = 0`, avoids `0 * infinity` at infinite-energy points, and assumes no
optimal test. Empty test classes are covered: the raw inequality is vacuous and the finite
domain of relaxation empty. Equality of constants is in `ENNReal`, without converting infinity
to a real number.

### Coordinate comparison

`E` is any finite-dimensional complete real inner product space with Borel structure and
second-countable norm topology; `μ : ProbabilityMeasure E` is arbitrary. No second moments,
density, log-concavity, positive dimension, or nondegenerate covariance are added.

The restriction statement gives pointwise restriction along `Probability.reconstruct μ`,
realization equality under `toIntrinsicL2`, and a raw-energy inequality. Extension only asserts
a globally smooth test with the correct restriction and realization and equal raw energy,
without fixing helper implementation. The proof should use orthogonal projection onto affine
support; the off-support branch of existing `intrinsicMap` is merely measurable and cannot
serve as a globally smooth extension.

The final energy equality lives on the same original `L²(μ)` and quantifies over every element,
including infinite-energy points. It does not claim that each raw ambient test's normal energy
equals its restriction's energy. Variance is unchanged when comparing the relaxed constants;
no hidden coordinate-origin independence or raw/core premise is needed.

### Legacy frontend

Both raw test classes require ordinary `ContDiff ℝ ∞`, `MemLp f 2 μ`, and integrable squared
gradient. `L2.variance_toLp` aligns variance; the finite gradient integrals coincide.
Legacy `Holds` uses `(C : ℝ)`, while the new finite constant is `C : NNReal`, whose explicit
type supplies legacy nonnegativity.

Normalization is always `Var ≤ C ∫ ‖gradient‖²`, with no extra factor two. Equality of valid
finite-constant sets gives optimal-constant equality without attainment of the legacy infimum.

## Sources and Blueprint correspondence

| Local Blueprint node | New Lean mapping |
| --- | --- |
| `thm:ambient-intrinsic-relaxation-equality` | `Energy.Euclidean.smoothGradientRelaxation_eq_intrinsicAffineSmoothGradientRelaxation` |
| `cor:ambient-intrinsic-constant-equality` | `Poincare.Euclidean.smoothGradientRelaxationConstant_eq_intrinsicAffine` |
| `thm:legacy-relaxed-holds-equivalence` | `Poincare.Euclidean.holds_iff_smoothGradientRelaxation` |
| `thm:legacy-canonical-constant-comparison` | `Poincare.Euclidean.constant_eq_intrinsicAffineSmoothGradientRelaxation` |

The exact scope and proof routes come from local Blueprint chapters 30 and 45. The abstract
pre-energy version and two test operations are local interfaces extracted for subsequent
proofs, not attributed to an unchecked paper.

This round reread `modules/01-definitions.tex` at historical pin
`kls-exploration@cd4a894a0faf40c0180f80b1a31eec1fdb6cb576`: Definition 2.1 on lines 17–25
supplies variance/gradient normalization; lines 6–15 concern `exp(-U)` densities and the
Langevin generator. It does not directly supply all these frontend equivalences for arbitrary
Borel probabilities or a spectral-gap identification. The current long-route source pin is unchanged.

The Blueprint adds only four `lean` links, retaining `notready` and adding no `leanok`.
Existing sidecar route statuses and mathematical dependencies are not promoted.

## Scope and next work

This batch does not define the literature's locally Lipschitz constant, log-concave laws,
isotropic laws, or the main KLS proposition; nor does it prove Dirichlet, Cheeger, raw/core,
whitening, or long-route conclusions. Connecting existing frontends first gives later KLS
statements a clear constant interface while retaining the explicit literature-frontend boundary.

All Gaussian applications merely check candidate-interface calls. The old Gaussian certificate
remains proved; transfer through this draft to the selected constant still depends on
`sorryAx` and is not new Gaussian certification.

Only the statement layer is extended; interfaces are not automatically frozen. Subsequent
proofs use the stated assumptions and conclusions. If review calls for interface changes,
retain draft status and append a decision, without rewriting earlier freeze or acceptance history.

## Verification artifacts

Temporary snapshots and full logs:

```text
/var/folders/6l/9qg2d8995s55q_4r1pfg83940000gn/T/kls-bridge-statements-20260906-s5zdn3p8/
```

SHA-256 of the two ledger statement strings (UTF-8, no added newline):

```text
ambient/intrinsic ddb7b7ddcb37690e392fbc9e8f27f323fbe1da0849e687fae48697eab7e0ecd7
legacy/relaxed    9ab94cdb9d87ca092f141a4f724003475e00b139a6ff03b97eab9eb83af6487a
```

## Final local verification

| Check | Result |
| --- | --- |
| Four new modules and two statement entries | All compiled |
| Default `lake build` | Passed, 3240 jobs; only 12 expected proof-placeholder warnings |
| Concrete entry-point applications | All 12 passed, including dimension zero, empty tests, Dirac, Gaussian, and infinite constants |
| Lean code block in the guide | Checked separately with `warningAsError=true` |
| Ledger | 6 nodes: 4 proved, 2 drafted; 0 errors |
| Blueprint | 73 labels, 4 active routes; 0 errors |
| Python tests | 63 passed |
| Blueprint PDF, web, checkdecls | All succeeded; all four new declaration links resolve |
| Final PDF | 27 pages; physical pages 13 and 16 inspected, no overflow, clipping, or overlap in modified paragraphs |
| Final TeX log | No overfull boxes, undefined references/citations, or duplicate labels; 8 underfull notices |
| Local links in edited documents | All targets exist |
| `git diff --check` | Passed |

Internal-expression comparison reuses the current baseline from strict review. Types, universe
parameters, reducible definition bodies, and transitive axioms of all 691 existing project
declarations are identical; none were deleted. The 15 added internal declarations are the
12 candidate theorems, `ofPreEnergy`, and two proof helpers generated by Lean for that definition.
Only those 12 candidate theorems depend on `sorryAx`; no new unsafe or partial declarations.

Source import-closure checks confirm that the root aggregate, `Poincare.Foundation`, and four
proved certificates do not depend on the four draft modules. The four proved ledger objects,
all old certificates, and both axiom-audit files are unchanged. All `leanok` and `notready`
markers agree by Blueprint node.

Full evidence is in the temporary directory's `lake-build.log`, `declaration-comparison.json`,
`import-boundaries.json`, `guide-example.log`, and `blueprint-build-final.log`.
No commit, push, remote CI, or change to existing historical records was made in this round.
