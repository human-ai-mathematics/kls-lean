---
type: audit
date: "2026-08-29"
---

# Lean linear-test certificate — semantic alignment audit

## Scope

This audit compares ledger node `lem:linear-test-lower` against all four active semantic layers:

- the Poincaré normalization in `modules/01-definitions.tex`, label `def:poincare`;
- the manuscript claim in `modules/02-results-toolkit.tex`, label
  `rem:rayleigh-lower-only`;
- the analytic dossier `solutions/glm-linear-baselines.tex`, lemma
  `lem:sol-linear-test-lower`; and
- the compiled theorem `Solutions.LemLinearTestLower.lem_linear_test_lower` in
  `solutions/LemLinearTestLower.lean`.

This is a semantic audit, not a replacement for Lean compilation and not an agent proof review.
No numerical evidence is used.

## Term-by-term alignment

### Ambient measure and moment hypothesis

The dossier states a probability measure on $\mathbb R^D$ with finite covariance. The Lean
certificate takes
`μ : Measure (EuclideanSpace ℝ (Fin D))`, an `IsProbabilityMeasure μ` instance, and
`MemLp id 2 μ`. In finite-dimensional Euclidean space, this is the coordinate-free finite
second-moment hypothesis needed to define every covariance entry and to put each linear test in
$L^2(\mu)$. The machine statement therefore makes the dossier's implicit analytic hypotheses
explicit without strengthening its conclusion.

### Poincaré normalization and admissible tests

The manuscript uses

$$
\operatorname{Var}_\mu(f)\le C\int\lVert\nabla f\rVert^2\,d\mu.
$$

`HasPoincare μ C` uses the same factor-one normalization. `IsAdmissible μ f` selects globally
smooth $L^2$ tests whose squared gradient is integrable. The extra integrability field prevents
Mathlib's totalized real integral from assigning a misleading value to a nonintegrable energy.
Tests with infinite energy are irrelevant to a finite Rayleigh lower bound; no closed-domain
equivalence is used in the proof.

The Lean certificate quantifies over every admissible test, including constants. This safely
subsumes the dossier's phrase “admissible nonconstant test” rather than omitting any test required
by the node.

### Gradient energy

`dirichletEnergy μ f` is exactly the integral of $\lVert\nabla f\rVert^2$. The theorem
`norm_fderiv_eq_norm_gradient` and its integrated form
`dirichletEnergy_eq_fderiv` identify this with the operator norm of the Fréchet derivative, so
the implementation and manuscript use the same Dirichlet form. For
$f_v(x)=\langle v,x\rangle$, Lean proves `gradient (linearTest v) x = v` and hence energy
$\lVert v\rVert^2$ under probability normalization.

### Optimal constant and zero-energy cases

Finite candidate constants are real and nonnegative. `optimalPoincareConstant μ : ENNReal` is
the infimum of all finite valid constants, so it is $+\infty$ exactly when no finite Poincaré
inequality holds. This matches the dossier's $C_P(\mu)\in[0,+\infty]$.

The machine quotient maps variance and energy separately to `ENNReal` before division. Thus
positive variance divided by zero energy is $+\infty$, while $0/0=0$. Under positive energy a
separate theorem proves equality with the ordinary real quotient printed in the manuscript. The
certificate therefore covers, rather than silently discards, all denominator boundary cases.

### Centered covariance and largest eigenvalue

The Lean object is the Riesz operator of Mathlib's centered `covarianceBilin`; it is deliberately
not Mathlib's uncentered second-moment `covarianceOperator`. Under `MemLp id 2 μ`, its quadratic
form equals

$$
\operatorname{Var}_\mu\langle v,X\rangle
=v^T\operatorname{Cov}_\mu v.
$$

`covarianceRayleighMax` is the supremum of the centered operator's Rayleigh quotient and is proved
equal to the unit-sphere covariance supremum. In nontrivial finite dimension it is an actual
eigenvalue by the formal Rayleigh--Ritz theorem. `lambdaMaxCovariance` is its faithful `ENNReal`
representation. The zero-dimensional convention is $0$, so the theorem also covers `D = 0`.

### Final inequality

For every finite valid constant $C$, Lean derives

$$
v^T\operatorname{Cov}_\mu v\le C\lVert v\rVert^2
$$

from the admissible linear test, takes the Rayleigh supremum, and then lower-bounds every finite
valid $C$ before passing to the infimum. Consequently

$$
\lambda_{\max}(\operatorname{Cov}_\mu)
\le C_P(\mu),
$$

with the correct direction and with the $C_P=+\infty$ case included. This is exactly the
mathematical content of the ledger node.

## Excluded equivalences

The certificate does not prove that the selected globally smooth finite-energy core has the same
optimal constant as a closed Sobolev Dirichlet form, nor that this constant is the reciprocal of
a separately defined spectral gap. Those are valid future formalization targets, but neither is
used by the linear-test lower bound and neither is certified here.

## Finding

No statement, normalization, quantifier, covariance-centering, or extended-value mismatch was
found within the node's stated finite-dimensional finite-covariance scope. The node-specific Lean
certificate covers both clauses of the ledger sentence. It is therefore semantically appropriate
for the sole ledger orchestrator to retain the analytic dossier and bind this node through
`checked_by: lean` and `lean_solution: solutions/LemLinearTestLower.lean`.

## Independent-review addendum: initial finding held

The independent audit
`research/reviews/2026-08-29-lean-linear-test-independent-semantic-audit.md` subsequently found
that the finite-second-moment, exact zero-energy quotient, dimension-zero, and mixed-provenance
conventions were explicit in Lean but not on every active natural-language surface. Its
`HOLD / revise` supersedes the initial no-mismatch finding above. This file is preserved as
append-only history; the repairs and a new independent follow-up audit determine the final state.

## Follow-up resolution

After the manuscript, ledger, dossier, and per-node provenance repairs, the cold follow-up audit
`research/reviews/2026-08-29-lean-linear-test-semantic-followup.md` returned scoped `PASS` with no
residual mismatch. That follow-up, not the initial finding in this file, is the current semantic
alignment record.
