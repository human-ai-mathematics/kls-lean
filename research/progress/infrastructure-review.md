# Infrastructure review of the available assessments

Current scope review of the four task nodes whose infrastructure assessment is `available` at
the pinned Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`. For each node it states the
Lean statement, the actual source modules and audit clients that carry the assessment, and
the explicit boundary. It is hashed as task evidence alongside the pre-existing source evidence;
it changes no status and removes no source check.

## `thm:logconcave-cheeger-poincare-comparison`

Blueprint: every finite-dimensional log-concave probability law satisfies `C_P^lit(μ) ≤ 4 Ψ_KLS(μ)²`
and `Ψ_KLS(μ)² ≤ π C_P^lit(μ)` (Cheeger–Buser comparison), proved as
`KLS.LogConcave.literatureConstant_le_four_mul_inverseScale_sq`,
`KLS.Isoperimetry.smoothTest_constant_le` and `KLS.LogConcave.inverseScale_sq_le_pi_literature`.

- **Cheeger half.** Cheeger's inequality for the Minkowski Cheeger infimum
  (`KLS/Geometry/Cheeger/Inequality.lean`) holds for an arbitrary Borel probability law: no density,
  absolute continuity, nonatomicity or log-concavity is assumed, and dimension zero gives the
  constant `0`. The log-concave frontend identification transports it to `C_P^lit`.
- **Buser half.** The constant `π` is obtained in the smooth convex tilted model from the heat
  correlation and the `π`-coefficient perimeter estimate (`KLS/LogConcave/SmoothBuser.lean`) and
  passed to an arbitrary nonsmooth log-concave law by normalized Gaussian convolution, Poincaré
  upper stability and setwise convergence, then transported to any finite-dimensional affine
  support including dimension zero (`KLS/LogConcave/Density/GaussianSmoothing/Buser.lean`). The
  one-dimensional constant-12 bound (`KLS/LogConcave/Line/Buser.lean`) is retained as a separate
  result.
- **Infrastructure.** The heat semigroup `P_t = exp(-t T̄†T̄)` of the closed weighted gradient and
  its generator, Markov, domain-stability, Γ/Γ₂, operator-core, interior-regularity, gradient,
  reverse-Poincaré, chain-rule, interpolation, decay and correlation layers are proved in
  `Analysis/Semigroup/` and `KLS/LogConcave/HeatSemigroup/`, with audit clients
  `Semigroup*Audit.lean`, `VonNeumannAudit.lean`, `Yosida*Audit.lean`, `Generator*Audit.lean`,
  `BakryEmery*Audit.lean`, `Heat*Audit.lean` and `GaussianBuserPassageAudit.lean` and route
  statements `SemigroupGenerationRouteStatements.lean`, `VonNeumannRouteStatements.lean`,
  `YosidaLimitRouteStatements.lean`, `GeneratedSemigroupRouteStatements.lean`,
  `MarkovRouteStatements.lean` and `BakryEmeryRouteStatements.lean`. The abstract strong-convergence
  statement for merely nonnegative commuting families is false and is recorded as a
  counterexample (`Analysis/Semigroup/Exponential/Counterexample.lean`); the proved limit uses the
  actual Yosida approximation.
- **Boundary.** Neither half gives the dimension-free KLS bound by itself; no gaps remain open.

## `thm:smooth-gradient-relaxation-two-cheeger`

Blueprint: the unconditional identity `𝓔^can_μ = 2 Ch_μ` for every Borel probability law on a
finite-dimensional inner product space, certified by
`Solutions.ThmSmoothGradientRelaxationTwoCheeger.certificate`.

- `SmoothGradient.relaxation_eq_localSlope` (`Energy/Cheeger/Identification.lean`): the inequality
  `≤` is the density of smooth tests in the local-slope energy (`Energy/Euclidean/Slope/Density.lean`:
  Borel measurability of the local slope, McShane patches on a slope-adapted partition, smooth
  recovery of globally Lipschitz tests in `Slope/Recovery.lean`, a cutoff for admissible tests),
  the inequality `≥` the unconditional `SmoothGradient.localSlope_relaxation_le`.
- The two Cheeger conventions agree by collapsing the asymptotic-Lipschitz sandwich of
  `Slope/Comparison.lean`; the absolutely continuous special case
  (`cor:absolutely-continuous-relaxation-two-cheeger`) and the log-concave case
  (`KLS/LogConcave/Cheeger.lean`) are consequences.
- Audit clients: `EnergySlopeComparisonAudit.lean`, `EnergySlopeRecoveryAudit.lean`,
  `EnergySlopeDensityAudit.lean`; route statements `EnergySlopeRouteStatements.lean`.
- **Boundary.** Nothing here is a Poincaré inequality, a finiteness statement or a Cheeger–Buser
  comparison. Closest literature: Eriksson-Bique, Calc. Var. PDE 62 (2023), Thm 1.1;
  Ambrosio–Gigli–Savaré, Rev. Mat. Iberoam. 29 (2013), §8.3.

## `lem:relative-perimeter-smoothing`

Blueprint: for a log-concave law `ν` with Borell density `ρ` on `Ω`, every smooth domain `U` with
finite relative perimeter `P_ρ(U)` admits globally smooth Lipschitz `0 ≤ u_j ≤ 1` with
`u_j → 1_U` in `L¹(ν)` and `limsup ∫ ‖∇u_j‖ dν ≤ P_ρ(U)`; unbounded domains and carriers and
dimension zero are included. Proved as `KLS.RelativePerimeter.exists_smooth_recovery_sequence`
(`KLS/Geometry/Perimeter/Recovery.lean`) by outward dilation combined with a vanishing
mollification radius.

- **Infrastructure.** The recovery statement itself needs no coarea or Sard input. The wider
  perimeter program that this node anchors is proved: weighted coarea for `C¹`, globally
  Lipschitz and locally Lipschitz maps (`Analysis/Coarea/`), Hausdorff slicing and surface
  slicing, smooth Sard and the sharp finite-regularity Sard theorem (`Analysis/Sard/Sharp.lean`),
  the compact Whitney extension (`Analysis/Whitney/`), the linear area formula, the codimension-`m`
  coarea formula for Lipschitz and locally Lipschitz maps (`Analysis/Lipschitz/`,
  `Analysis/Vector/`), the rank-deficient stratification, and the smooth-domain Gauss–Green layer.
  Audit clients carry each step (`*CoareaAudit.lean`, `*SliceAudit.lean`, `Whitney*Audit.lean`,
  `Sard*Audit.lean`, `Vector*Audit.lean`, `RankDeficient*Audit.lean`, `ExponentObstructionAudit.lean`)
  with the route statements `WeightedCoareaRouteStatements.lean`, `SharpSardRouteStatements.lean`,
  `RankDeficientRouteStatements.lean`, `StratumSlicingRouteStatements.lean`,
  `LipschitzVectorCoareaRouteStatements.lean` and `LocallyLipschitzVectorCoareaRouteStatements.lean`.
- **Boundary.** The Federer area formula in general codimension is not proved
  (`AreaFormulaRouteStatements.lean` is a type-check file); the proved area formula is codimension
  one. No separate ledger certificate is attached to this node; its `leanok` rests on the exact
  theorem above.

## `lem:relative-perimeter-cheeger-infimum`

Blueprint (Appendix A): the Minkowski Cheeger infimum `h_M` over Borel sets and the smooth
relative-perimeter infimum `h_S` over smooth domains agree, `h_M = h_S`, for a log-concave law
with Borell density, together with the `h_μ = h_ν^{sm,rel}` and `Ψ_KLS(μ) = ψ_ν` clauses of the
frontend identification; both infima are `⊤` when no admissible set exists, in particular in
dimension zero. Certified by `Solutions.LemRelativePerimeterCheegerInfimum.certificate`.

- `h_M ≤ h_S`: smooth recovery of a smooth domain and the Minkowski coarea inequality
  (`KLS/Geometry/Cheeger/Infimum.lean`, `Analysis/Coarea/Isoperimetry.lean`).
- `h_S ≤ h_M`: distance cutoffs of a Borel set of finite content, their mollification, smooth
  Sard for almost every strict superlevel set and the weighted `C¹` coarea formula for the
  density, with the balance error subtracted rather than multiplied so that no finiteness of
  `h_S` is used (`KLS/Geometry/Cheeger/Equality.lean`, `DistanceCutoff.lean`, `Median.lean`,
  `SmoothDomain/RegularSuperlevel.lean`).
- Audit clients: `CheegerEqualityAudit.lean`, `CheegerInequalityAudit.lean`,
  `LipschitzCoareaMigrationAudit.lean`; route statements `CheegerInfimumRouteStatements.lean`,
  `CheegerInequalityRouteStatements.lean`.
- **Boundary.** The node contains no Poincaré inequality and no Cheeger–Buser comparison; those
  belong to `thm:logconcave-cheeger-poincare-comparison` above.
