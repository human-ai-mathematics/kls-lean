# One-dimensional Gaussian Poincaré: candidate-statement review package

Date: 2026-09-04 (Asia/Shanghai).
Baseline: `10e4c707491830ebe9d07f7bfc5e65efeddc7e2e`, branch `main`.
Node: `lem:poincare-gaussian-one-dimensional`.
Status: **drafted / checked_by: null; not yet frozen or proved.**

The user's request this round was: “Proceed that way: write the statements first again, clearly
identify sources, make the material easy to use, and follow formech's style.” This document
implements authorization to prepare statements; it does not interpret that as approval of
complete signatures not yet shown. All 20 new mathematical declarations retain `by sorry`.
This round creates no GitHub issue, commit, or push.

## Targets and examples first

Both main entry points cover every real mean m and nonnegative variance v:

```lean
theorem holds_gaussianReal (m : ℝ) (v : NNReal) :
    Holds (ProbabilityTheory.gaussianReal m v) (v : ℝ)

theorem constant_gaussianReal (m : ℝ) (v : NNReal) :
    constant (ProbabilityTheory.gaussianReal m v) = (v : ENNReal)
```

The namespace is `FunctionalInequalities.Poincare`. The first says v is valid; the second
says v is optimal. Examples: the standard Gaussian has constant 1; mean 3 and variance 4 give
constant 4; variance 0 gives a point mass at the mean with constant 0. All examples are checked
through the same generic interface.

Entry points:

- [Mathematical explanation, examples, file tree, and build steps](../../formalization/FunctionalInequalities/Poincare/Gaussian/README.md).
- [Sources for each item, Mathlib APIs, and dependency route](../explorations/2026-09-04-gaussian-poincare-design.md).
- [All 20 complete signatures printed by Lean](../explorations/2026-09-04-gaussian-poincare-signatures.txt).
- [Sole statement entry point and 7 type applications](../../solutions/LemPoincareGaussianOneDimensional.lean).
- [Verification and semantic review for this round](../explorations/2026-09-04-gaussian-poincare-validation.md).

## Interface choices for review

1. Retain existing `Admissible`: global smoothness, Gaussian L², and integrable squared-gradient energy.
2. Neither main conclusion assumes positive variance; only density-proof helpers use `v ≠ 0`.
3. The sharp constant is variance v. The lower bound uses the identity function; the optimum retains the `ENNReal` infimum.
4. The 20 declarations comprise 2 main results and 18 helpers. Finite-interval estimates use global C¹; Tonelli interfaces allow infinite nonnegative integrands; real-integral steps retain explicit integrability.
5. Split library files into `Gaussian/Density.lean` and `Gaussian/Real.lean`; initially place generic interval helpers in Real. The solution only checks types; assemble a named certificate after proving the statements.

These are candidate contracts. Review may adjust helpers. Once a freeze is approved, the
independent proof phase must preserve the approved full signatures, semantic definitions,
and ledger statement. Record any required change as a new issue for human handling first.

## Sources and project extensions

The manuscript's [Gaussian covariance family](https://github.com/human-ai-mathematics/kls-conjecture-search/blob/cd4a894a0faf40c0180f80b1a31eec1fdb6cb576/modules/03-tier1-gaussian.tex#L10-L37)
is the source for centered Gaussians with positive definite covariance; this round takes its
one-dimensional Poincaré part. Normalization comes from
[Definition 2.1](https://github.com/human-ai-mathematics/kls-conjecture-search/blob/cd4a894a0faf40c0180f80b1a31eec1fdb6cb576/modules/01-definitions.tex#L17-L25);
the linear-test lower bound is in
[Remark 3.8](https://github.com/human-ai-mathematics/kls-conjecture-search/blob/cd4a894a0faf40c0180f80b1a31eec1fdb6cb576/modules/02-results-toolkit.tex#L108-L117).

Arbitrary means, zero variance, the exact smooth finite-energy test domain, and the `ENNReal`
encoding are local extensions or choices. The direct density/interval-integral route is a
local derivation; the manuscript obtains the upper bound through Bakry–Émery/LSI.
Each Lean docstring identifies its provenance; helpers are not misrepresented as original
literature theorems.

Formech is only a presentation reference: mathematical meaning, file diagram, quantifiers,
examples, model boundaries, and copyable build commands. The source/API record specifies the
pinned reference and how it is used. Itemwise attribution and freezing follow KLS's own rules.

## Complete source signatures

All candidate signatures are listed by source file below, omitting the shared `:= by sorry`.
Every new declaration is in `FunctionalInequalities.Poincare`; `Admissible.` and `Holds.`
denote the respective subnamespaces. The full signature snapshot separately records actual
elaboration output, including implicit parameters, typeclasses, and universes.

### Density.lean (7 declarations)

```lean
theorem hasDerivAt_gaussianPDFReal (m : ℝ) {v : NNReal} (hv : v ≠ 0) (x : ℝ) :
    HasDerivAt (gaussianPDFReal m v)
      (-((x - m) / (v : ℝ)) * gaussianPDFReal m v x) x

theorem tendsto_gaussianPDFReal_atTop (m : ℝ) {v : NNReal} (hv : v ≠ 0) :
    Tendsto (gaussianPDFReal m v) atTop (𝓝 0)

theorem tendsto_gaussianPDFReal_atBot (m : ℝ) {v : NNReal} (hv : v ≠ 0) :
    Tendsto (gaussianPDFReal m v) atBot (𝓝 0)

theorem integrable_centered_gaussianPDFReal (m : ℝ) {v : NNReal} (hv : v ≠ 0) :
    Integrable (fun x : ℝ ↦ (x - m) * gaussianPDFReal m v x) volume

theorem integral_Ioi_centered_gaussianPDFReal (m : ℝ) {v : NNReal} (hv : v ≠ 0)
    (t : ℝ) (ht : m ≤ t) :
    (∫ x in Set.Ioi t, (x - m) * gaussianPDFReal m v x) =
      (v : ℝ) * gaussianPDFReal m v t

theorem integral_Iio_centered_gaussianPDFReal (m : ℝ) {v : NNReal} (hv : v ≠ 0)
    (t : ℝ) (ht : t ≤ m) :
    (∫ x in Set.Iio t, (m - x) * gaussianPDFReal m v x) =
      (v : ℝ) * gaussianPDFReal m v t

theorem integrable_gaussianReal_iff (m : ℝ) {v : NNReal} (hv : v ≠ 0) (f : ℝ → ℝ) :
    Integrable f (gaussianReal m v) ↔
      Integrable (fun x ↦ gaussianPDFReal m v x * f x) volume
```

### Real.lean (13 declarations)

```lean
theorem interval_sq_sub_le_integral_sq_deriv (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (a b : ℝ) (hab : a ≤ b) :
    (f b - f a) ^ 2 ≤ (b - a) * ∫ t in a..b, (deriv f t) ^ 2

theorem Admissible.variance_le_integral_sq_sub {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {f : ℝ → ℝ} (hf : Admissible μ f) (c : ℝ) :
    variance f μ ≤ ∫ x, (f x - c) ^ 2 ∂μ

theorem Admissible.integrable_gaussianPDFReal_mul_sq_sub {m : ℝ} {v : NNReal}
    {f : ℝ → ℝ} (hf : Admissible (gaussianReal m v) f) (hv : v ≠ 0) (c : ℝ) :
    Integrable (fun x ↦ gaussianPDFReal m v x * (f x - c) ^ 2) volume

theorem Admissible.integrable_gaussianPDFReal_mul_sq_deriv {m : ℝ} {v : NNReal}
    {f : ℝ → ℝ} (hf : Admissible (gaussianReal m v) f) (hv : v ≠ 0) :
    Integrable (fun x ↦ gaussianPDFReal m v x * (deriv f x) ^ 2) volume

theorem lintegral_gaussian_right_triangle (m : ℝ) {v : NNReal} (hv : v ≠ 0)
    (g : ℝ → ENNReal) (hg : Measurable g) :
    (∫⁻ x in Set.Ioi m,
      ENNReal.ofReal (x - m) * gaussianPDF m v x * ∫⁻ t in Set.Ioo m x, g t) =
      (v : ENNReal) * ∫⁻ t in Set.Ioi m, gaussianPDF m v t * g t

theorem lintegral_gaussian_left_triangle (m : ℝ) {v : NNReal} (hv : v ≠ 0)
    (g : ℝ → ENNReal) (hg : Measurable g) :
    (∫⁻ x in Set.Iio m,
      ENNReal.ofReal (m - x) * gaussianPDF m v x * ∫⁻ t in Set.Ioo x m, g t) =
      (v : ENNReal) * ∫⁻ t in Set.Iio m, gaussianPDF m v t * g t

theorem Admissible.integral_Ioi_sq_sub_gaussian_le {m : ℝ} {v : NNReal} {f : ℝ → ℝ}
    (hf : Admissible (gaussianReal m v) f) (hv : v ≠ 0) :
    (∫ x in Set.Ioi m, gaussianPDFReal m v x * (f x - f m) ^ 2) ≤
      (v : ℝ) * ∫ x in Set.Ioi m, gaussianPDFReal m v x * (deriv f x) ^ 2

theorem Admissible.integral_Iio_sq_sub_gaussian_le {m : ℝ} {v : NNReal} {f : ℝ → ℝ}
    (hf : Admissible (gaussianReal m v) f) (hv : v ≠ 0) :
    (∫ x in Set.Iio m, gaussianPDFReal m v x * (f x - f m) ^ 2) ≤
      (v : ℝ) * ∫ x in Set.Iio m, gaussianPDFReal m v x * (deriv f x) ^ 2

theorem Admissible.integral_sq_sub_gaussian_le {m : ℝ} {v : NNReal} {f : ℝ → ℝ}
    (hf : Admissible (gaussianReal m v) f) (hv : v ≠ 0) :
    (∫ x, (f x - f m) ^ 2 ∂gaussianReal m v) ≤
      (v : ℝ) * energy (gaussianReal m v) f

theorem holds_gaussianReal_zero (m : ℝ) : Holds (gaussianReal m 0) 0

theorem holds_gaussianReal (m : ℝ) (v : NNReal) :
    Holds (gaussianReal m v) (v : ℝ)

theorem Holds.gaussianReal_variance_le {m : ℝ} {v : NNReal} {C : ℝ}
    (h : Holds (gaussianReal m v) C) : (v : ℝ) ≤ C

theorem constant_gaussianReal (m : ℝ) (v : NNReal) :
    constant (gaussianReal m v) = (v : ENNReal)
```

## Complete ledger snapshot

The node actually added in this round is shown below. `checked_by: null` deliberately retains uncertified status.

```json
{
  "id": "lem:poincare-gaussian-one-dimensional",
  "kind": "lemma",
  "status": "drafted",
  "source": "Gaussian covariance family fam:gaussian-covariance, modules/03-tier1-gaussian.tex lines 10-37, at kls-exploration commit cd4a894a0faf40c0180f80b1a31eec1fdb6cb576; Poincare normalization from Definition 2.1 and sharpness from Remark 3.8. Arbitrary means, the zero-variance Dirac case, the smooth finite-energy test domain, and the direct density proof route are explicit local specifications. Exact source correspondence and helper provenance: research/explorations/2026-09-04-gaussian-poincare-design.md.",
  "statement": "For every real mean m and every nonnegative variance v : NNReal, let gamma = ProbabilityTheory.gaussianReal m v, a probability measure on the real line. For the unchanged Poincare.Admissible class of globally smooth real-valued functions f with MemLp f 2 gamma and integrable squared canonical gradient, Poincare.Holds gamma (v : Real): for every such f, Var_gamma(f) <= (v : Real) * integral ||gradient f||^2 dgamma. On the real line the canonical gradient equals the ordinary derivative. Moreover Poincare.constant gamma = (v : ENNReal), where constant is the existing ENNReal infimum over finite NNReal constants satisfying Holds. The parameter v is the variance, not the standard deviation; the energy has no extra factor. No restriction on m or positivity premise on v occurs in either conclusion. At v = 0, gamma is Measure.dirac m and the fixed and optimal constants are zero. The identity test is admissible, has variance v and energy one, and supplies the matching lower bound for every finite valid constant. Positive-variance density helpers are used only under v != 0. No boundedness, compact support, additional derivative-integrability, test-function decay, or infimum-attainment assumption is imposed. This claim concerns the current smooth L2 finite-energy domain; it does not identify a closed Sobolev or spectral-gap domain or assert a multivariate, log-Sobolev, or transport-entropy theorem.",
  "lean_solution": "solutions/LemPoincareGaussianOneDimensional.lean",
  "checked_by": null
}
```

## Review-version identifiers and next steps

- SHA-256 of the complete compiled-signature file: `8103fa2acdfa4f2ed7df32b3d72496c65863de9c34da8b3c8c3148a893c763ca`.
- SHA-256 of the ledger `statement` string (UTF-8, no appended newline): `07fa78f7a1a97217da6726a4f09fe043191413447e9a01715f850d9a38625574`.

These identifiers pin this candidate revision; **they are not a human freeze record**.
Type checking passed for the 20 declarations, 7 type applications, and the future certificate
proposition. The three older nodes remain proved. Consult the linked verification record for
details. After user review, if the full contracts are approved, append a freeze record and
hand the work to the independent proof phase.
