# Metric BV perimeter interface, 2026-09-26

The object is the perimeter of a Borel set in the closed measure support of
the intrinsic affine law. `KLS/Geometry/Perimeter/MetricBV.lean` defines it as
an extended-real infimum over sequences in the De Ponti--Mondino `Lip_b`
class: functions have bounded values and bounded support, converge to the
indicator in the actual measure's `L¹`, and pay the liminf of the integral
of `Energy.LocalSlope.apply`. The measure-facing API requires the Borel
measurable structure of the metric topology. The imported local slope is
zero at isolated points. `closedSupportLaw` uses `Measure.comap Subtype.val` and proves its
probability mass from the conullness of the closed support; set masses are
identified with the original measure of their images.

Ambrosio--Di Marino--Gigli Definition 3.3 initially allows arbitrary Lipschitz
tests; their Remark 3.4 reduces to bounded-support tests. The local Lean
definition matches the De Ponti--Mondino test class directly, but does not
prove equivalence with the unrestricted-test definition.

`KLS/Geometry/Cheeger/BVConstant.lean` defines the half-mass and symmetric
BV infima and specializes the former to the actual intrinsic support law.
The half-mass infimum is `⊤` in zero affine dimension. The proved complement
symmetry currently covers finite metric spaces, where reflection preserves
bounded support. It does not assert symmetry for an arbitrary unbounded
support. This distinction matters: `1-f` loses bounded support when the
carrier is unbounded. A cutoff/diagonal approximation is still required.

The existing `relativePerimeter ρ Ω U` integrates a density over a smooth
domain boundary inside an open region. It is not metric BV perimeter.
No previously committed public signature or numerical π-Buser proof was changed.

The following literature interfaces remain to be formalized:

1. General complement symmetry for the bounded-support test class and the
   equivalence of half-mass and symmetric BV Cheeger conventions.
2. Ambrosio--Di Marino--Gigli Lemma 2.1, transferring lower to upper
   Minkowski content after `L¹` relaxation, and Theorem 3.6, identifying
   relaxed content with BV perimeter. Finite-content sets require the
   existing closure-mass lemma; recovery sets require nondegenerate mass and
   convergence of the minimum denominator.
3. Comparison of intrinsic open enlargements on the closed support with
   the affine-carrier `Isoperimetry.constant`, including singular laws and
   unbounded support. Only after these steps can the unconditional final
   equality be added.

The Blueprint therefore retains the BV identification as a literature
comparison. This round does not prove the full RCD theory, dimension-free
KLS, or equality of the two perimeters for each set.
