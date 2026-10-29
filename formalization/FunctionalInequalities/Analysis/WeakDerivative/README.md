# Weak directional derivatives

These modules retain the existing `FunctionalInequalities.Analysis` declarations and their
actual hypotheses. They support the weak regular-class Letwin chain; they do not by themselves
construct a moment potential, prove Hessian evolution or establish the constant-8 theorem.

| Module | Responsibility |
| --- | --- |
| [Basic](Basic.lean) | Weak directional derivative, uniqueness, classical/a.e. identification and the C1 product |
| [Mollification](Mollification.lean) | Convolution and weak derivatives from difference bounds |
| [Approximation](Approximation.lean) | Cutoff gluing and common-support smooth approximations |
| [Products](Products.lean) | Weak product rules for global L2, compact-local L2 and locally bounded factors, finite sums and Leibniz products, compact C1 cutoff multiplication, and shared compact-local L2 integrability helpers |
| [ChainRule](ChainRule.lean) | Lipschitz negative exponential, C1 Lipschitz compositions of bounded compact and bounded noncompact data, shifted logarithms and real powers, and a bounded weak log extension |
| [PowerTests](PowerTests.lean) | Cutoff power energy variables `χ (δ + max w 0)^q` and square tests `χ² (δ + max w 0)^q` with exact weak derivatives, under global or cutoff-local nonnegativity |
| [Testing](Testing.lean) | Curl identity against compact rough H1 tests, bounded-test domination, extension of tested divergence identities to bounded weak tests, and zero integral of integrable weak derivatives |
| [Sobolev](Sobolev.lean) | Weak Sobolev bounds for bounded compact weak H1 data: critical GNS for n > 2, every finite q >= 2 for n = 2 (L6 is the q = 6 case), essential L-infinity for n = 1 |
| [Caccioppoli](Caccioppoli.lean) | Generic Caccioppoli inequality for bounded weak supersolutions with a.e. elliptic coefficients, and the logarithmic and power energies |
| [Representation](Representation.lean) | Riesz-potential representation and critical John–Nirenberg integrability for bounded weak H1_loc data on bounded convex domains, n ≥ 2, with the one-dimensional replacement |
| [Moser](Moser.lean) | Moser essential and norm endpoints from given cutoff power energies, separately for n > 2, n = 2 and n = 1 |
| [Harnack](Harnack.lean) | Weak Harnack inequality (Gilbarg–Trudinger Theorem 8.18, bounded symmetric pure-divergence case) for given bounded weak supersolutions, every n > 0 |

The compact-local L2 helpers shared across modules are public in `Products`; the remaining limit arguments stay
private to `ChainRule` and `Testing`. Local L2, global L2 and bounded hypotheses remain distinct. The generic
[smooth ball cutoff](../Cutoff/SmoothBall.lean) and [Lipschitz ball cutoff](../Cutoff/LipschitzBall.lean) have
different profiles and regularity.

`Sobolev` and `Caccioppoli` are H1 supports: the `Sobolev` n = 2 bounds carry an explicit support-measure factor, and
the n = 1 bound is essential, not pointwise. `Moser` takes its cutoff power energies as premises; `Harnack` derives them
from `Caccioppoli` for given bounded weak supersolutions and does not claim the unbounded, nonsymmetric, lower-order or
domain-only Theorem 8.18.
