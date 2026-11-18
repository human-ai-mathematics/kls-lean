# Tau Ceti adjoint-composition dependency review

The Lean 4.35.0 package uses [Tau Ceti #37118](https://github.com/TauCetiProject/TauCeti/pull/37118)
for density and self-adjointness of the maximal-domain composition of an adjoint with its
closed densely defined operator. The corresponding result in Weidmann's *Linear Operators
in Hilbert Spaces*, Chapter 5, supports the closed weighted-gradient semigroup in the KLS
formalization of BKL arXiv:2610.05474v1.

The two provider files are byte-identical to those in the
[upstream Bors commit](https://github.com/TauCetiProject/TauCeti/commit/dbba028bef10f3b992707ea201a6449acc26ce6d).
The Lean 4.35 backport adds just those files to `4705013d` as
`84e562f6feeb2de8f5318992e63fb8054f7d6c46`. The manifest digest is `e67f86a213dcf705b1536c5aa3db1ca27ef74d6b82b2de3fd9989461d75fdb10`.
Mathlib stays at `56a005855ea17e0b0958f73ec801ae140b0a1679`.

The KLS operator construction retains its domain as the same intersection of submodules.
A private equality identifies it with `LinearPMap.adjointComp` by matching domain membership
and application. The two public results keep their real Hilbert space hypotheses. The
positive-parameter resolvent and graph-norm convergence continue to use the existing weak-form
arguments. The KLS and independent BKL statement baselines retain their existing roots,
elaborated declaration closures and external leaves.
