# kls-lean

Lean 4/mathlib formalizations of foundational results related to the KLS conjecture and
functional inequalities.

The current milestone is the machine-checked linear-test lower bound for the optimal Poincaré
constant from [Issue #2](https://github.com/numina-functional-inequalities/kls-lean/issues/2):

$$
C_P(\mu) \geq \lambda_{\max}(\operatorname{Cov}_\mu).
$$

The formal theorem applies to finite-dimensional probability measures with finite second moment.
It makes the admissible test class, extended-value conventions, centered covariance operator, and
dimension-zero convention explicit.

## Repository layout

- `formalization/FunctionalInequalities/Basic.lean`: admissible tests, Dirichlet energy, and fixed
  and optimal Poincaré constants.
- `formalization/FunctionalInequalities/Poincare.lean`: linear tests, Rayleigh quotients, centered
  covariance, and the eigenvalue bridge.
- `formalization/FunctionalInequalities/Project/LinearTestLower.lean`: reusable project theorem.
- `solutions/LemLinearTestLower.lean`: thin certificate for Issue #2.
- `LEAN_DESIGN.md`: normalization choices, semantic scope, and known limitations.

## Build

The project pins Lean and mathlib to `v4.33.0`:

```bash
cd formalization
lake build
```

The default build compiles both the reusable library and the root-level Issue #2 certificate.
See `formalization/README.md` for dependency and module details.

## Scope

This repository currently certifies only the linear-test Poincaré lower bound. Gaussian
Poincaré, tensorization, log-Sobolev inequalities, Bakry–Émery, Otto–Villani, stochastic
localization, and the KLS conjecture itself remain future, separately reviewed targets.
