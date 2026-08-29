# Frozen Issue 2 Stage 1A specification: foundational Poincaré vocabulary

## Purpose

Formalize only the foundational vocabulary needed later by the Issue 2 linear-test lower bound.
This stage introduces three definitions and proves no theorem.

## Ambient setting

Work over a real Hilbert space $E$ with the following Lean structure available:

- `NormedAddCommGroup E`;
- `InnerProductSpace ℝ E`;
- `CompleteSpace E`; and
- `MeasurableSpace E`.

Let `μ : Measure E` and `f : E → ℝ`.

## Required definitions

### 1. Admissible test functions

Define `IsAdmissible μ f : Prop` as a structure with exactly these three fields:

1. `smooth'`: $f$ is infinitely continuously differentiable over $\mathbb R$;
2. `memLp_two`: $f$ belongs to $L^2(\mu)$; and
3. `energy_integrable`: the real-valued function
   $x \mapsto \lVert \nabla f(x)\rVert^2$ is integrable with respect to $\mu$.

This is the smooth finite-energy test core. The third field is required explicitly so that the
totalized real Bochner integral cannot silently represent a nonintegrable energy by zero.

### 2. Dirichlet energy

Define `dirichletEnergy μ f : ℝ` to be

$$
\int_E \lVert \nabla f(x)\rVert^2\,d\mu(x).
$$

Use Mathlib's canonical `gradient`.

### 3. Fixed-constant Poincaré predicate

Define `HasPoincare μ C : Prop`, for `C : ℝ`, to assert all three conditions:

1. $\mu$ is a probability measure;
2. $C \ge 0$; and
3. every `IsAdmissible μ f` satisfies

$$
\operatorname{Var}_\mu(f) \le C\,\mathcal E_\mu(f),
$$

where the right-hand side uses the `dirichletEnergy` defined in this stage and the left-hand side
uses Mathlib's probability `variance`.

## Required names and output boundary

The candidate must define exactly these requested top-level declarations inside namespace
`Issue2Autoformalization.Stage1A`:

- `IsAdmissible`;
- `dirichletEnergy`;
- `HasPoincare`.

The `IsAdmissible` structure necessarily generates its three named field projections and standard
Lean structure machinery. Beyond those generated declarations, the candidate may add comments and
local implementation details but no other public definition, structure, lemma, theorem, axiom,
instance, notation, or macro.

## Explicit non-goals

Do not define or prove anything about:

- nonnegativity or monotonicity;
- Fréchet derivatives;
- the optimal Poincaré constant;
- linear tests or their gradients;
- Rayleigh quotients;
- covariance operators or eigenvalues;
- the final Issue 2 lower bound; or
- any other KLS result.

The candidate is an experimental reconstruction for later human review. It does not modify or
recertify the existing Issue 2 theorem.
