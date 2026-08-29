# Frozen informal specification: linear-test Poincaré lower bound

## Scope

Autoformalize the proposition below. Generate only a Lean definition whose value is a `Prop`;
do not prove the proposition in this phase.

## Mathematical statement

Let $D\in\mathbb N$, including $D=0$, and let $\mu$ be a probability measure on the Euclidean
space $\mathbb R^D$. Assume that the identity random vector belongs to $L^2(\mu)$, equivalently
that $\mu$ has finite second moment.

The required proposition is the conjunction of both clauses:

1. Every admissible smooth real-valued test $f$ in $L^2(\mu)$ with finite gradient energy has its
   extended Poincaré Rayleigh quotient bounded above by the extended optimal Poincaré constant of
   $\mu$.
2. The largest centered-covariance Rayleigh value of $\mu$ is bounded above by the same extended
   optimal Poincaré constant.

Use the repository's existing definitions of admissibility, extended Rayleigh quotient, optimal
Poincaré constant, and largest centered-covariance Rayleigh value. Do not redefine them.

## Required boundary conventions

- The optimal constant and quotients are extended nonnegative real values.
- The existing quotient definition carries the conventions $0/0=0$ and $a/0=+\infty$ for
  $a>0$.
- Dimension zero is included; the existing empty covariance Rayleigh supremum is $0$.
- Do not add nontriviality, density, log-concavity, finite-constant, positive-energy, or
  positive-variance assumptions.
- Do not weaken the result to only the covariance clause or only a fixed test.

## Output contract

Keep the name `candidateLinearTestLowerStatement`. The candidate must be a Lean definition ending
in `: Prop := ...`, not a theorem and not a proof. Preserve explicit probability and finite-second-
moment hypotheses in its binders. Replace the `HUMANIZE2_UNATTEMPTED` sentinel completely.
