# Frozen Issue 2 Stage 1B specification: foundational lemmas and optimal constant

## Purpose

Extend the human-accepted Stage 1A vocabulary with only the foundational facts needed by later
Issue 2 layers. This stage proves elementary properties of Dirichlet energy and fixed Poincaré
constants, then defines the extended optimal Poincaré constant and proves its finite-versus-`⊤`
boundary.

Stage 1A is supplied as the read-only module `AcceptedStage1A`. Its accepted explicit function
binder in `HasPoincare` is intentional and must not be rewritten.

## Ambient setting

Continue inside namespace `Issue2Autoformalization.Stage1A` over a real Hilbert space $E$ with:

- `NormedAddCommGroup E`;
- `InnerProductSpace ℝ E`;
- `CompleteSpace E`; and
- `MeasurableSpace E` whenever a measure-theoretic declaration needs it.

Use the accepted `IsAdmissible`, `dirichletEnergy`, and `HasPoincare` definitions without
redeclaring or modifying them.

## Required energy and derivative lemmas

Prove exactly these declarations.

1. `dirichletEnergy_nonneg (μ : Measure E) (f : E → ℝ)`:

   $$0 \le \operatorname{dirichletEnergy}_\mu(f).$$

2. `norm_fderiv_eq_norm_gradient (f : E → ℝ) (x : E)`:

   $$\lVert Df(x)\rVert = \lVert \nabla f(x)\rVert.$$

   Here `Df(x)` is Mathlib's real Fréchet derivative `fderiv ℝ f x`. This theorem must not require
   a measurable-space structure on $E$.

3. `dirichletEnergy_eq_fderiv (μ : Measure E) (f : E → ℝ)`:

   $$
   \operatorname{dirichletEnergy}_\mu(f)
   = \int_E \lVert Df(x)\rVert^2\,d\mu(x).
   $$

## Required fixed-constant lemmas

Inside the nested namespace `HasPoincare`, prove exactly:

1. `isProbabilityMeasure`: a proof of `HasPoincare μ C` yields `IsProbabilityMeasure μ`;
2. `constant_nonneg`: a proof of `HasPoincare μ C` yields `0 ≤ C`;
3. `variance_le`: for any admissible `f`, a proof of `HasPoincare μ C` yields
   `variance f μ ≤ C * dirichletEnergy μ f`; and
4. `mono`: if `HasPoincare μ C` and `C ≤ C'`, then `HasPoincare μ C'`.

The monotonicity proof must use energy nonnegativity and may not strengthen the admissible test
class or add assumptions.

## Required optimal constant

Define `optimalPoincareConstant (μ : Measure E) : ENNReal` to be the infimum, in `ENNReal`, of all
finite nonnegative valid constants:

```lean
⨅ C : {C : NNReal // HasPoincare μ (C : ℝ)}, (C.1 : ENNReal)
```

The empty infimum is therefore `⊤`. Prove exactly these declarations:

1. `optimalPoincareConstant_le`: every `C : NNReal` satisfying `HasPoincare μ (C : ℝ)` upper-bounds
   `optimalPoincareConstant μ` after coercion to `ENNReal`;
2. `le_optimalPoincareConstant`: if `L : ENNReal` is no larger than every finite nonnegative valid
   constant, then `L ≤ optimalPoincareConstant μ`;
3. `optimalPoincareConstant_eq_top_of_no_finite`: if no `C : NNReal` is valid, then the optimal
   constant is `⊤`;
4. `optimalPoincareConstant_ne_top_of_hasPoincare`: any finite nonnegative valid constant implies
   that the optimal constant is not `⊤`; and
5. `optimalPoincareConstant_eq_top_iff`: the optimal constant equals `⊤` exactly when no
   `C : NNReal` satisfies `HasPoincare μ (C : ℝ)`.

## Required names and output boundary

The candidate must import `AcceptedStage1A` and add exactly these requested public declarations in
namespace `Issue2Autoformalization.Stage1A`:

- `dirichletEnergy_nonneg`;
- `norm_fderiv_eq_norm_gradient`;
- `dirichletEnergy_eq_fderiv`;
- `HasPoincare.isProbabilityMeasure`;
- `HasPoincare.constant_nonneg`;
- `HasPoincare.variance_le`;
- `HasPoincare.mono`;
- `optimalPoincareConstant`;
- `optimalPoincareConstant_le`;
- `le_optimalPoincareConstant`;
- `optimalPoincareConstant_eq_top_of_no_finite`;
- `optimalPoincareConstant_ne_top_of_hasPoincare`; and
- `optimalPoincareConstant_eq_top_iff`.

Comments and local proof terms are allowed. No other public definition, lemma, theorem, axiom,
instance, notation, or macro may be added.

## Explicit non-goals

Do not formalize linear tests, Rayleigh quotients, covariance operators, eigenvalues, the final
Issue 2 lower bound, or any KLS target outside Issue 2. Do not create a natural-language dossier,
review, certificate, ledger entry, or manuscript edit. This remains a blind experimental
reconstruction followed by human review.
