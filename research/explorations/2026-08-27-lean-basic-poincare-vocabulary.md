# Lean basic Poincaré vocabulary

**Date:** 2026-08-27 (Asia/Taipei)

**Branch:** `codex/issue-2-linear-test-lower`

**Ledger node:** `lem:linear-test-lower`

**Scope:** Phase C foundation only; no ledger edit, node certificate, or claim of Lean
certification.

## Bounded objective

Introduce the smallest reusable Lean interface needed to state a fixed-constant Poincaré
inequality without hard-coding the eventual linear projection. The interface must make the
$L^2$, differentiability, and finite-energy assumptions visible, and it must compile in the
pinned Lean/mathlib `v4.33.0` project.

## Representation decisions

The fixed constant `C` and Dirichlet energy are represented in `ℝ`. This keeps the initial
inequality in the same codomain as `ProbabilityTheory.variance` and the Bochner integral.
`HasPoincare μ C` explicitly includes `0 ≤ C`. This decision applies only to a finite candidate
constant. The later optimal-constant layer should use `ℝ≥0∞` so that the absence of any finite
Poincaré constant is represented by `⊤` rather than silently discarded.

The energy uses the squared operator norm of a continuous linear Fréchet derivative field
$Df(x)\colon E\to\mathbb R$:

```lean
dirichletEnergy μ Df = ∫ x, ‖Df x‖ ^ 2 ∂μ
```

For scalar-valued functions on a real Hilbert space this is the norm of the gradient, while the
continuous-linear-map representation matches Mathlib's derivative API directly and does not
require finite dimensionality in the basic module.

Admissibility is a proposition on `μ`, `f`, and an explicit derivative field `Df`. It records:

- `MemLp f 2 μ`;
- `HasFDerivAt f (Df x) x` almost everywhere; and
- integrability of `x ↦ ‖Df x‖ ^ 2`.

Keeping the derivative field explicit makes later linear-map calculations direct. The field is
not ambiguous: `HasFDerivAt.unique` proves that two admissible derivative witnesses for the same
function agree almost everywhere, and `integral_congr_ae` then proves their energies equal.

`HasPoincare μ C` also carries `IsProbabilityMeasure μ`, so the probability normalization is
part of the proposition rather than an ambient, easily omitted assumption.

## Mathlib API probe

The temporary probe `/private/tmp/kls-basic-probe.lean` compiled with the following declarations:

- `ProbabilityTheory.variance` and `variance_nonneg`;
- `MeasureTheory.MemLp` and `Integrable`;
- `HasFDerivAt` and `HasFDerivAt.unique`;
- `MeasureTheory.integral_nonneg` and `integral_congr_ae`;
- `MeasureTheory.IsProbabilityMeasure`; and
- `mul_le_mul_of_nonneg_right`.

The basic module imports exactly:

```lean
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Probability.Moments.Variance
```

## Implemented declarations

- `FunctionalInequalities.IsAdmissible`;
- `FunctionalInequalities.dirichletEnergy` and `dirichletEnergy_nonneg`;
- `IsAdmissible.derivative_ae_eq` and `IsAdmissible.dirichletEnergy_eq`;
- `FunctionalInequalities.HasPoincare`;
- projections of its probability and constant-nonnegativity facts;
- `HasPoincare.variance_le`; and
- `HasPoincare.mono` for enlargement of a valid constant.

The root `FunctionalInequalities` module imports `FunctionalInequalities.Basic`, so the default
Lake target compiles the new vocabulary.

## Alternatives rejected or deferred

- A fixed constant in `ℝ≥0∞` was deferred because multiplying real variance and energy by an
  extended value would complicate the first linear-test theorem. Extended nonnegative reals are
  still required for the later optimal constant.
- A fixed constant in `ℝ≥0` was not used because it would introduce coercions into every real
  inequality without solving the `+∞` case.
- A gradient-valued energy was deferred because it requires an inner-product space at the basic
  layer. The Fréchet derivative works on general real normed spaces and specializes to the
  gradient in the target setting.
- Bundling `f` and `Df` into a test-function structure was rejected for now. A relational
  admissibility predicate keeps concrete functions syntactically visible and avoids coercion
  machinery in the linear-test proof.
- General Sobolev or weak-derivative admissibility is outside this phase. The current interface is
  a smooth test-function core. Before final ledger certification, an independent semantic audit
  must confirm that the chosen optimal-constant definition matches the manuscript's intended
  Poincaré constant or add the necessary closure theorem.

## Validation

- `lake env lean /private/tmp/kls-basic-probe.lean` — passed.
- `#print axioms` for derivative uniqueness, energy independence, and constant monotonicity —
  only the standard Mathlib axioms `propext`, `Classical.choice`, and `Quot.sound`; no admitted
  theorem.
- `cd formalization && lake build` — passed; 2,941 jobs, including
  `FunctionalInequalities.Basic` and the root module.

Repository-wide validation and the final staged diff check are recorded in the session handoff
and pushed commit report.

## Next exact proof action

Define the centered covariance continuous linear operator from
`ProbabilityTheory.covarianceBilin` and prove its quadratic-form identity using
`covarianceBilin_self`. Then prove admissibility and the energy identity for
$x \mapsto \langle v,x\rangle$, with the zero-dimensional spectral case still kept explicit.
Do not add the node-specific certificate or edit either ledger yet.
