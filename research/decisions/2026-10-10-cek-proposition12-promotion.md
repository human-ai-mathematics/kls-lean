# CEK Proposition 12 promotion (2026-10-10)

Source: Cordero-Erausquin–Klartag, *Moment measures*, arXiv:1304.0630v1, Proposition 12 (38). The root-accepted scratch
proof (`build/reviews/2026-10-09-moment-map-letwin-parallel/independent-p12-attainment/`) was migrated under the
root-reviewed revision-3 map into an isolated candidate, independently accepted by root
(`independent-p12-integration-review/ACCEPTANCE.json`, 67ff0a85…), and applied as the exact 25-path patch (c895a87a…).
The complete map, including the compiler-observed private and generated names, is
[`2026-10-10-cek-proposition12-promotion-map.json`](../api-migration/2026-10-10-cek-proposition12-promotion-map.json).
It is a scratch promotion: no production API is renamed, and no alias is created.

Placement (61 declarations, 13 destination modules):

- `Analysis/Convex/`: `SupportingPlane.lean` (supporting affine plane at an interior point), `Affine.lean` (affine
  subtraction, finite-shift algebra, Legendre covariance, normalization; measure-free), and `legendre_norm` in
  `Legendre.lean`.
- `Probability/ConvexSupport.lean`: the source-condition adapter
  `zero_mem_interior_convexHull_support_of_integral_eq_zero`.
- `Probability/MomentMeasure/`: `Integrability`, `Truncation`, `Affine`, `Coercivity`, `Normalization`, `Baseline`, and
  `log_sub_ge_of_integral_limits` in `ConjugateMass.lean`.
- `KLS/CEK/` (new per-paper folder, two modules): `Competitors.lean` (competitor reduction and the finite ceiling) and
  `VariationalMaximum.lean` (maximizing sequence, limit witness, `exists_variational_maximum`). No lower-level module
  imports it.

Mechanical corrections recorded during candidate construction (no proof body changed): measure-free `Analysis` owners do
not open `MeasureTheory`; the measure binders of the source variable context are not replayed for the pure `EReal`
lemma `sub_coe_cancel_shift`; `MomentMeasure/Baseline.lean` imports `Mathlib.Analysis.Normed.Module.FiniteDimension`
(the plan listed none; the accepted file had it transitively). The unreferenced simp auxiliary
`norm_baseline_finite._simp_1_3` is compiled as `._simp_1_4` with identical type and value.

Scope: Proposition 12 attainment over every admissible competitor, with Legendre mass one and a lower semicontinuous
witness. The coercivity route does not give Lemma 15's constant. Essential continuity, the Euler–Lagrange
identification, Theorem 2 existence and uniqueness, and the regularity bridge remain open. No paper coverage or ledger
certificate changes.
