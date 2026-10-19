# Lean library design

The library provides reusable analysis, probability, energy and Poincaré interfaces, with literature-specific proofs in `KLS/`.
Use the [formalization guide](formalization/README.md) for layout and builds, the [calling examples](examples/README.md) for imports and clients,
the [generated API directory](formalization/API.md) for compiler-derived signatures,
and the [naming guide](research/naming.md) for public API conventions.

The proved target is `FunctionalInequalities.KLS.kls : KLS.Conjecture`. The [paper register](research/progress/LITERATURE.md)
owns theorem scope and coverage; the [current handoff](HANDOFF.md) owns current work and receipt pointers.
The [classical KLS gate](research/audits/KLS/Classical/README.md) checks, with independently written Mathlib-only statements,
that the target yields the classical convex-body, locally Lipschitz and covariance-normalized formulations.

## Mathematical layers

| Owner | Responsibility | Scope boundary |
| --- | --- | --- |
| [Analysis](formalization/FunctionalInequalities/Analysis/) | Operators, semigroups, convexity, matrices, weak derivatives and geometric analysis | Each theorem states its own structure; the abstract real Hilbert-space layer does not require finite dimension |
| [Probability](formalization/FunctionalInequalities/Probability/) and [L2](formalization/FunctionalInequalities/L2/) | Probability laws, covariance, affine support, moments and Hilbert-space classes | Probability transport and L² pullback are separate operations |
| [Energy](formalization/FunctionalInequalities/Energy/README.md) | Extended energies, finite domains, relaxation and gradient realizations | Closed quadratic, Markov and Dirichlet properties are separate statements |
| [Poincare](formalization/FunctionalInequalities/Poincare/README.md) | Valid bounds, optimal constants, products and frontend comparisons | An optimal constant belongs to a specified test domain and energy |
| [KLS](formalization/FunctionalInequalities/KLS/README.md) | Log-concave models and source-specific BKL, Letwin and CEK applications | Preserve the pinned source hypotheses, constants and dimensions |
| [Certificates](solutions/README.md) | Registered consumers of the mathematical owners | [Paper-coverage criteria](research/progress/LITERATURE.md#when-a-paper-is-covered) |

Dependency direction runs from applications to their prerequisites. Prefer the owning module as an import.
The aggregate `FunctionalInequalities` is useful for exploration; [examples](examples/README.md) identify narrower entry points.

## Energy and test frontends

| Frontend | Mathematical object | Reading entry |
| --- | --- | --- |
| `Poincare.SmoothTest` | Globally smooth L² functions with finite squared-gradient energy | [Test domain and constant](formalization/FunctionalInequalities/Poincare/SmoothTest/Basic.lean) |
| `Energy.SmoothGradient` | The sequential L² relaxation of the smooth-gradient pre-energy | [Energy guide](formalization/FunctionalInequalities/Energy/README.md) |
| `Energy.WeightedGradient` | A gradient weighted by an explicitly chosen operator | [Weighted tests](formalization/FunctionalInequalities/Energy/WeightedGradient/Basic.lean) |
| `Energy.CovarianceGradient` | Covariance-weighted gradient energy and affine transport | [Covariance energy](formalization/FunctionalInequalities/Energy/CovarianceGradient/Basic.lean) |
| `Poincare.LocalSlope` | The literature local-slope inequality on its finite-energy L² tests | [Validity and intrinsic constant](formalization/FunctionalInequalities/Poincare/LocalSlope/Basic.lean) |

`Ambient` and `Intrinsic` distinguish the coordinate carrier. Intrinsic coordinates use the direction of the affine support,
so the KLS target includes singular supports and dimension zero. For log-concave laws, the
[proved comparisons](formalization/FunctionalInequalities/KLS/LogConcave/Poincare.lean) identify the relevant optimal constants.
Retain each comparison's hypotheses when changing frontend.

The local-slope energy is the integral of the squared pointwise slope, with no factor of one half.
Zero-energy tests are included. Finite constants use `NNReal`; optimal values use `ENNReal` and may be infinite.
Every conversion from an extended integral to a real quantity must retain the required finiteness premise.

## Transport and operators

Pushforward laws live in `Probability`; pullbacks of L² classes live in `L2`. Covariance-energy invariance and
Poincaré-constant invariance belong to their respective owners. General linear equivalences and isometries have distinct APIs.

The abstract semigroup construction starts with a closed densely defined operator between real Hilbert spaces.
Its [semigroup laws](formalization/FunctionalInequalities/Analysis/Semigroup/Generated/Laws.lean) are independent of a probability model.
A concrete heat or localization application supplies the additional analytic and probabilistic hypotheses.

## API changes and validation

Interfaces may evolve with new proof consumers; there is no default promise of backward compatibility.
Follow the [placement and delivery workflow](research/workflow.md) before a module split, path move or public API change.
Keep path migrations separate from namespace and declaration migrations, with complete maps and current consumers updated.

New proofs require strict compilation, an actual client and the appropriate axiom checks.
Documentation-only organization requires link, scope and preservation checks. It does not advance a proof or certificate,
and it does not turn an earlier receipt into verification of a new source and documentation snapshot.
See [verification commands and trust scope](research/verification.md).
