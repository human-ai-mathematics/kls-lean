# Handoff baseline before file management (2026-10-11)

This dated record freezes the repository-root `HANDOFF.md` before the authorized file-management batch. It is historical context, not a change to mathematical scope, proof status, controller ownership or authorization. The body is preserved byte-for-byte inside the Markdown source block; its paths retain their original repository-root interpretation. A working link directory is provided below.

Original SHA-256: `36429e815332bc66d98727fd75583a4ce60b6d86a6ce132f19aff2f25c063600`.

````markdown
# Current KLS handoff

Updated 2026-10-11. This file holds the current state only; earlier versions are preserved in the
[2026-10-11 Letwin A.4/A.5 source integration](research/decisions/2026-10-11-letwin-a4-a5-source-integration.md), the
[2026-10-11 protocol/scheduling correction](research/decisions/2026-10-11-bkl-a4-protocol-scheduling-correction.md), the
[2026-10-11 handoff correction](research/decisions/2026-10-11-handoff-controller-correction.md), the
[2026-10-11 cutoff-profile adoption](research/decisions/2026-10-11-cutoff-profile-adoption.md), the
[2026-10-10 Stage 1 record](research/decisions/2026-10-10-bkl-stage1-integration.md), the
[2026-10-08 handoff history](research/decisions/2026-10-08-handoff-history.md), the
[2026-10-07 history](research/decisions/2026-10-07-handoff-history.md) and the
[2026-10-02 history](research/decisions/2026-10-02-handoff-history.md), and are not current task
authorization. Exact results, scopes and certificates are in the
[paper register](research/progress/LITERATURE.md) and the [node register](research/progress/STATUS.md).

## State

- Local `main` = `7c0145c4028687dccc4837f3d46410477c14ebe6` (BKL Theorem 3.1 certified, per-paper
  folders); `origin/main` = `ca59365726bca899f26cdd889dcc62850089eb09`. Everything listed under
  "Uncommitted" below is in the working tree only (no commit, push, tag or remote CI has been made
  for it; the owner decides when to commit). Remote Lean certification passed for `36e7c78` only;
  later work is verified locally.
- 30 ledger certificates. The 30th is `prop:bkl-suspension` (`solutions/PropBklSuspension.lean`):
  Bizeul–Klartag–Lehec Proposition 7.1 in the source form, conditional on its own hypothesis
  `CumulantBound d b` (the universal cumulant bound of Theorem 4.1), all dimensions. The 29th is
  `thm:bkl-taylor-criterion` (Theorem 3.1). `FunctionalInequalities.KLS.kls` in `KLS/Target.lean` is
  the one intentional hole, outside every certificate closure. Dimension-free KLS is open.
- Covered papers: Ambrosio–Di Marino–Gigli Theorem 3.6 and Bakry–Gentil–Ledoux Corollary 4.8.2
  (`⇑`). No BKL or Letwin paper is covered: BKL Theorem 1.1 is formalized only conditionally on
  Theorem 4.1 (Eldan localization, open); the Section 2 regular approximation is complete in that
  conditional form; Letwin Theorems 1.1–1.2 and the moment-map Stein kernel of an arbitrary law remain
  open (the Gaussian has the identity kernel).
- Verification: the integrated snapshot (everything under "Uncommitted", including the 2026-10-11 Letwin Lemma A.4/A.5
  source integration) is checked by the full local verifier `python3 research/verify.py` run after all proof and metadata
  edits. Its current result is `build/verification/latest.json`, valid only while its status is `passed` and its snapshot
  hash matches the working tree; the timestamped receipt statement is kept in ignored build evidence, so no tracked file
  changes after the receipt. The previous full receipt `20261010T093056.948739Z` covers its own snapshot only (the Stage 1
  integration), not the later adoptions; its paragraph is preserved in
  [the A.4/A.5 integration record](research/decisions/2026-10-11-letwin-a4-a5-source-integration.md). Still open: the
  SDE/Itô dynamics, CEK essential continuity, Euler–Lagrange identification and Theorem 2, the regularity bridge (H2),
  the Letwin moment map, Theorem 2.5 and the quadratic-form bound with constant 8, BKL Theorem 1.1 and `KLS.kls`.

## Uncommitted (2026-10-07–11, continuous BKL goal)

Execution record, worker provenance (`accepted-statements.csv`), Codex reviews and the integration
requests INT-2 … INT-7 are in `build/reviews/2026-10-07-bkl-continuous/` (not tracked). Historical completed proof bodies
came from the Luna API (`gpt-5.6-luna`) and Codex scratch work, independently accepted before
integration. New construction follows the API-first addendum, with no Luna dispatch;
Claude remains the sole reviewed production editor (placement and metadata).

- **Letwin Lemmas A.4/A.5 source integration (Stage 2A; adopted 2026-10-11; full local receipt of this snapshot
  required):** Codex-accepted exact candidates (support tree v3, the cutoff module R3, the closed lower owner T.2, the
  final client accepted by Root, source SHA-256 `6f70011e…`; bundle
  `build/reviews/2026-10-11-bkl-a4-goal-setup/claude-w-final-integration-candidate-v1/`).
  New `Analysis/Convex/Coercivity.lean`, `Analysis/CutoffConservativity.lean`,
  `Analysis/BakryEmery/IntegrationByParts/InverseHessianCutoff.lean`, `Analysis/BakryEmery/UniformIntervalPotential.lean`
  and `Analysis/BakryEmery/IntegrationByParts/UniformIntervalClient.lean`; the A.4 supports appended to
  `HessianOperator.lean`, the energy identity/bound and A.5 for given cutoffs to `IntegrationByParts/InverseHessian.lean`.
  Lemma A.4 (`exists_scaled_cutoffs_hessianInverseOperator`, every real `R ≥ 1`, `∫ |Lχ_R| dν ≤ C/R`, and the natural
  form `exists_cutoffs_hessianInverseOperator`) holds for every source-class potential, the moment-map properties being
  hypotheses; A.5 holds for given cutoffs; the client
  `uniformInterval_tanhSq_integrable_and_integral_hessianInverseOperator_eq_zero` applies both to the uniform law on
  `(−√3, √3)` with `f = tanh²(√3y/2)`. Letwin LA4 `⇑`, LA5 partial; the paper is not covered. Blueprint
  `lem:letwin-a4-supports`, `lem:letwin-a4-cutoffs`, `lem:letwin-a5-cutoffs`, `lem:letwin-uniform-interval-source`,
  `lem:letwin-uniform-interval-client`; six new `BKL/Letwin*Audit.lean` clients. Record:
  [A.4/A.5 source integration](research/decisions/2026-10-11-letwin-a4-a5-source-integration.md).

- **Letwin Lemma A.4 scalar and positivity supports (adopted 2026-10-11, before the source integration above):** the cutoff
  profile, majorant and natural-index exhaustion, the tail primitive, the affine rescaling and the real-parameter
  exhaustion in `Analysis/CutoffProfile.lean`, and the inverse-Hessian quadratic positivity in
  `Analysis/BakryEmery/MongeAmpere.lean`, each from a Codex-accepted exact candidate with its audit
  (`BKL/LetwinCutoffProfileAudit.lean`, `LetwinCutoffPrimitiveAudit.lean`, `LetwinRescalingPositivityAudit.lean`,
  `LetwinRealExhaustionAudit.lean`). They are consumed by the source construction of the item above: Lemma A.4 for every
  source-class potential (real `R ≥ 1` and natural index), Lemma A.5 for given cutoffs, the uniform-interval source facts
  and the nonconstant client. Their adoption entries are preserved verbatim in
  [the A.4/A.5 integration record](research/decisions/2026-10-11-letwin-a4-a5-source-integration.md); records:
  [profile](research/decisions/2026-10-11-cutoff-profile-adoption.md),
  [tail primitive](research/decisions/2026-10-11-cutoff-primitive-adoption.md),
  [rescaling/positivity](research/decisions/2026-10-11-rescaling-positivity-adoption.md),
  [real exhaustion](research/decisions/2026-10-11-real-exhaustion-adoption.md).
- **BKL/Letwin Stage 1 (adopted 2026-10-10; full local receipt `20261010T093056.948739Z`):** the root-accepted combined
  candidate (`build/reviews/2026-10-10-bkl-staged-orchestration/claude-stage1-combined/`) adds deterministic supports
  only. (i) BKL (74) grouped for `M = A⁻¹`: `Dᵐ⟪v, A⁻¹v⟫(0)[h] = 2m κ_m(h) + 2 L_m(h)` with `L_m` from (72), for
  every compactly supported law with invertible covariance, every `m ≥ 3` and any representative slot
  (`Analysis/BakryEmery/CumulantLeibniz.lean`, `iteratedFDeriv_inner_centeredGradient_zero_grouped_of_compact`, Astra
  v5), with the ordered-mask partition facts (`Analysis/IteratedDerivative/Bilinear.lean`, `selected_mask_partition`,
  Astra v6). (ii) The covariance step of the proof of Letwin Theorem 1.2 (p. 14, preceding (2.21)):
  `Cov(|M|^{1/2} X) = |M|` for isotropic `X` and every real symmetric `M`, singular, indefinite and dimension zero
  included (`KLS/Isotropic.lean`, `Isotropic.covarianceBilin_map_sqrt_abs_matrix`, Astra v5), with spectral supports
  in the new `Analysis/Matrix/Sign.lean`; `Analysis/Matrix{Trace,Positivity,DeterminantDerivative}.lean` moved
  byte-identically to `Analysis/Matrix/` (map `research/api-migration/2026-10-10-analysis-matrix-family-map.json`,
  no aliases or wrappers). Blueprint `lem:bkl-grouped-drift-expansion`, `lem:letwin-mapped-covariance`;
  `literature.json` BKL E7274 and Letwin CZ14 `⇑` (reviewed stronger), BKL L43 and Letwin T12 partial; audits
  `research/audits/BKL/{GroupedCumulantAudit,SelectedPartitionAudit,MappedCovarianceAudit}.lean`. Open: the
  stochastic (73) and Lemma 4.3, Theorem 4.1, the Stein-kernel identity (2.21), Letwin Theorems 2.5 and 1.2; no
  certificate. Record: [Stage 1 integration](research/decisions/2026-10-10-bkl-stage1-integration.md).
- **CEK Proposition 12 (adopted 2026-10-10):** the root-accepted 25-path patch
  (`build/reviews/2026-10-09-moment-map-letwin-parallel/p12-integration-candidate/`, acceptance 67ff0a85…) adds
  `Analysis/Convex/{SupportingPlane,Affine}.lean`, `Probability/MomentMeasure/{Integrability,Truncation,Affine,Coercivity,
  Normalization,Baseline}.lean` and `KLS/CEK/{Competitors,VariationalMaximum}.lean`, extends `Legendre`, `ConvexSupport`
  (Theorem 2 conditions give the interior-hull hypothesis) and `ConjugateMass`, and adds two CEK audits.
  `KLS.CEK.exists_variational_maximum` is Proposition 12 (38) with lower semicontinuity added (`literature.json` P12 `⇑`);
  Lemma 15's constant is not proved (different coercivity route), Lemma 17 stays partial (no composed source-form
  declaration). Map: `research/api-migration/2026-10-10-cek-proposition12-promotion-map.json`; Blueprint
  `lem:cek-zero-interior`, `lem:cek-coercivity`, `thm:cek-variational-maximum`. No certificate; Theorem 2 open.
- **CEK convex duality and Lemma 17 (adopted 2026-10-09):** the root-accepted 13-file patch
  (`build/reviews/2026-10-09-moment-map-letwin-parallel/integration-candidate/`, acceptance c645fee4…) adds
  `Analysis/Convex/{Legendre,AffineMaximum,PointwiseCompactness,RadialExtension}.lean`,
  `Probability/MomentMeasure/{Basic,ConjugateMass,Compactness}.lean`, extends `Probability/ConvexSupport.lean`
  (CEK Lemma 16 for finite measures; the nine existing constants are unchanged) and adds `research/audits/CEK/`.
  Lemma 17 holds with one subsequence and one limit for both inequalities, with `0 ∈ interior (convexHull ℝ μ.support)`
  explicit. The Theorem 2 conditions give that hypothesis through
  `Probability.zero_mem_interior_convexHull_support_of_integral_eq_zero` (adopted with Proposition 12, above), but no
  declaration states the composition in the source form, so `literature.json` L17 stays partial. Map:
  `research/api-migration/2026-10-09-cek-scratch-promotion-map.json` (scratch promotion, no production rename);
  Blueprint `lem:cek-point-control`, `lem:legendre-convexification`, `lem:cek-compactness`; L16 `alternative` (⇑).
  Lemmas 14–15 (source constants), essential continuity, the Euler–Lagrange identification and Theorem 2 remain open;
  the four unused statement definitions (`HasMomentMeasure`, …) stay deferred in lane A scratch. Superseded wording:
  [2026-10-10 handoff history](research/decisions/2026-10-10-handoff-history.md).
- **Proposition 7.1 (certified, conditional):** joint law of the Laplace-noise suspension, density
  (109), log-concavity (110), isotropy, (111)–(112), Hilbert–Schmidt step, `β → ∞`, affine-orthogonal
  decomposition, (113) and (107) (`CumulantBound d b` is the `(d+1)`-cumulant bound, as in
  `SuspensionLaw.lean`): `KLS/BKL/Suspension*.lean`, `KLS/BKL/Proposition71.lean`,
  `L2/AffineDecomposition.lean`, `Probability/{Product,QuadraticTilt}.lean`, `Probability/Line/Laplace.lean`.
- **Theorem 1.1 conditional on Theorem 4.1 (no certificate):** `KLS/BKL/Reduction.lean`:
  `KLS.localSlope_le_of_cumulantBound_all` and `KLS.conjecture_of_cumulantBound` — under the universal
  cumulant bounds `CumulantBound d ((d!)² K^d)` (all `d ≥ 2`, `K ≥ 1`), every isotropic log-concave law has
  `C_P ≤ 2·C_{3.1}·K` and `KLS.Conjecture` follows; `KLS.kls` stays open. Built from the p. 30 reduction
  and the complete Section 2 reduction to isotropic regular laws (`KLS/LogConcave/IsotropicReduction.lean`).
- **p. 30 reduction (conditional, no certificate):** `KLS/BKL/Reduction.lean`:
  `RegularPotential.poincare_le_of_cumulantBound` — under `CumulantBound d ((d!)² K^d)` for all `d ≥ 2`,
  every isotropic regular law has `C_P ≤ 2·C_{3.1}·K` (Theorem 3.1 with `R = √(2K)`, Proposition 7.1
  for `d ≥ 2`, the first Taylor tensor is the centered first moment and Bessel for `d = 1`).
- **Section 2, regular approximation (complete in conditional form; see `IsotropicReduction`):**
  Gaussian smoothing as a producer of regular potentials (`δ ≤ ∇² ≤ 2s + δ`:
  `GaussianSmoothing/{Hessian,Posterior,Growth,Regular,Moments}.lean`; posterior covariance identity,
  quantitative Borell moments in `BorellRepresentation/Moments.lean`, polynomial growth of all
  derivatives, covariance `Cov μ + Id/(2s)`, weak convergence `μ*γ_{n+1} → μ` in
  `GaussianSmoothing/Approximation.lean`); regular potentials under affine maps and the
  centering/whitening to isotropic regular laws (`KLS/LogConcave/{Regular,RegularAffine,RegularIsotropic}.lean`,
  tilt transport in `Probability/Transport.lean`); the weak-limit transfer of the Poincaré bound to the
  literature constant (`Poincare/SmoothTest/WeakLimit.lean`, `KLS/LogConcave/WeakLimit.lean`);
  generic helpers `Analysis/IteratedDerivative/Log.lean`, `Analysis/TemperateGrowth.lean`,
  `Analysis/BakryEmery/Tilt/LocalDerivatives.lean`.
- **Letwin supports (arXiv:2607.24164v1):** Lemma A.3, (2.12), Lemma 2.3 in conditional generic form
  (`Analysis/BakryEmery/IntegrationByParts/Basic.lean`, `Analysis/Tensor/Coordinate.lean`,
  `KLS/Isotropic.lean`); Definition 2.6 Stein kernels, the `H^{-1}` norm (2.19), A.7 and Lemma 2.9
  (`Probability/Stein/{Kernel,DualBound}.lean`, `Energy/DualNorm.lean`, `L2/Pairing.lean`,
  `KLS/LogConcave/Stein.lean`); the standard Gaussian has the identity Stein kernel
  (client-only audit `research/audits/BKL/GaussianSteinAudit.lean`). The general moment-map kernel
  of an arbitrary law (Lemma 2.2, Proposition 2.8) is not constructed.
- **Letwin (2.3) and the Hessian–Stein kernel (2026-10-08):** the generic Hessian
  product rule, the nondivergence operator `L_{A,b}` for an arbitrary symmetric coefficient field and
  its Leibniz rule (`Analysis/BakryEmery/Calculus.lean`; clients in `research/audits/BKL/NondivergenceAudit.lean`,
  including the cross-direction product exposing an off-diagonal entry); Lemma 2.7's analytic part for a
  given potential, `τ = ∇²φ ∘ (∇φ)⁻¹` as a Stein kernel under explicit gradient injectivity
  (`Probability/Stein/HessianKernel.lean`, `KLS/LogConcave/HessianStein.lean`); the derivative (2.5) of
  the inverse Hessian, the inverse-Hessian operator with its Leibniz rule, and the right-hand-side
  derivative of the Monge–Ampère log-det equation taken as a hypothesis
  (`Analysis/{RingInverseDerivative,OperatorCoordinates}.lean`, `Analysis/BakryEmery/{HessianOperator,MongeAmpere}.lean`).
  Jacobi's formula and the first and second derivatives (2.4), (2.6) of the Monge–Ampère equation for a
  given smooth φ with positive definite Hessian satisfying the zero-order equation, with both
  right-hand matrices positive semidefinite (`Analysis/Matrix/{DeterminantDerivative,Positivity}.lean`,
  `Analysis/BakryEmery/MongeAmpere.lean`). The moment map of an arbitrary law (Lemma 2.2, the zero-order
  equation itself), strict positive definiteness, the Hilbert–Schmidt `L²` bound and Theorems 1.2/2.5
  remain open.
- **BKL Lemma 4.2 in source scope (conditional):** third-cumulant identity, polynomial `L²` membership
  and `Σ_{jk} κ₃(u,e_j,e_k)² ≤ 8‖u‖²` from one exponential radius (`Analysis/BakryEmery/LocalCumulant.lean`);
  every isotropic log-concave law satisfying the Letwin quadratic bound has `R₃ ≤ 8 Id`, and
  `CumulantBound 2 8` follows if all do (`KLS/BKL/LocalThirdCumulant.lean`). The Laplace law is in scope
  (it has no exponential moment at its own rate, so the older all-radii statement in `Cumulant.lean`
  excluded it). Letwin Theorem 1.2 is an explicit hypothesis, not proved.
- **BKL Theorem 4.1, base `m = 2` (unconditional, no certificate):** for any law with one exponential
  moment the second cumulant is the centered second moment, i.e. the covariance pairing
  (`Analysis/BakryEmery/LocalCumulant.lean`); for isotropic log-concave laws `κ₂(u,v) = ⟨u,v⟩`, Parseval, and
  `CumulantBound 1 1` in every dimension (`KLS/BKL/SecondCumulant.lean`). The all-order Theorem 4.1 is open.
- **BKL (67), deterministic parameter response (no stochastic calculus):** the posterior
  `μ e^{⟨c,x⟩ − ½⟨Qx,x⟩}/Z` of a compactly supported prior for every `(c,Q)` including the initial pair,
  uniform norm moments, and the covariance derivative along signed parameter lines; the coercive case
  for arbitrary priors and polynomial statistics; the isotropic initial response `⟨u,h⟩`
  (`Probability/Posterior/{Exponent,CompactPrior,Coercive,CompactQuadratic}.lean`,
  `KLS/BKL/PosteriorResponse.lean`); the posterior as a probability law with the prior's support and
  affine support, and for isotropic compact priors a self-adjoint strictly positive invertible covariance
  with canonical inverse `Cov⁻¹` (`Probability/Posterior/CompactDomain.lean`, `Probability/Covariance/Positivity.lean`,
  `Analysis/PositiveOperator.lean`, `KLS/BKL/PosteriorDomain.lean`); the deterministic generator of the
  posterior expectation, `C^∞` in `c` with covariance gradient/Hessian, `Q`-derivative and the cancellation
  `D_c[Ma] + ∂_Q[M] + ½ tr_M D²_c = 0` for every symmetric `M` (`Probability/Posterior/Generator.lean`;
  with the cancellation at the source rate `M = Cov(μ_{c,Q})⁻¹` for compact isotropic priors and rate `Id`
  at the initial pair in `KLS/BKL/PosteriorDomain.lean`); log-concavity of the posterior of a
  log-concave compact prior for self-adjoint `Q ≥ 0` (`KLS/LogConcave/Density/ConcaveTilt.lean`,
  `KLS.compactPosterior_logConcave`); the diffusion coefficient `A^{-1/2}` as the principal inverse square
  root of the posterior covariance with its full coefficient algebra (`Analysis/PrincipalInverseSqrt.lean`,
  `Isotropic.compactPosterior_inverseSqrt_spec`); the coefficient regularity of (67): posterior expectation,
  mean and covariance jointly `C^∞` in `(c,Q)` (`Probability/Posterior/JointRegularity.lean`), `Cov⁻¹` and
  `Cov⁻¹a` jointly `C^∞` and `Cov⁻¹ᐟ²` with the coefficient triple locally Lipschitz on the whole parameter
  space (`Analysis/Matrix/Positivity.lean` Sylvester estimate, `Analysis/PrincipalInverseSqrt.lean` section
  `LocalLipschitz`, `KLS/BKL/PosteriorDomain.lean` section `JointCoefficients`,
  `Isotropic.locallyLipschitz_coefficients67`); Letwin (2.2) for a given potential: inverse-Hessian
  divergence, flux form and the compact-test integration by parts for `L`
  (`Analysis/BakryEmery/MongeAmpere.lean` section `Divergence`, `IntegrationByParts/InverseHessian.lean`).
  The strong solution of (67), non-explosion, the equations (68)–(71), Itô, the martingale property, the
  moment-map producer (Letwin Lemmas 2.1–2.2) and the compact approximation of general laws are not
  formalized; the external StochLean closures stay evidence under `build/reviews/` (no adoption).
- **CGF jets and the root sandwich (2026-10-08):** for the cumulant-generating function `Λ` of a compactly
  supported law, `∇Λ(0) = ∫ x dμ` and `D(∇Λ − ∇Λ(0))(0) = Cov μ` (BKL p. 20 before (74);
  `Analysis/BakryEmery/LocalCumulant.lean` section `GradientJets`, with `cumulantVector` as the Riesz vector of
  the last cumulant slot), and `σ A σ = 1` for the principal inverse square root
  (`Analysis/PrincipalInverseSqrt.lean`, `inverseSqrt_mul_mul_inverseSqrt`): the canonical root whitens the
  covariance, and the same principal root transports the centred posterior to an isotropic law (the canonical
  standardisation bullet below). The higher jets `Dʳ(∇Λ − ∇Λ(0))(0)[h] = cumulantVector μ h` for all `r ≥ 1` are
  proved from two generic supports in `Analysis/IteratedDerivative/GradientJet.lean`. The generic permutation symmetry
  of raw iterated derivatives and the raw bilinear Leibniz expansion over all subset allocations
  (`Analysis/IteratedDerivative/{Symmetry,Bilinear}.lean`, Blueprint `lem:iterated-derivative-symmetry-leibniz`) are
  in production. The singleton terms of (74), `⟪κ₂(w,·), A⁻¹ κ_{k+1}(h,·)⟫ = κ_{k+1}(h, w)` for invertible covariance `A`
  (`LocalCumulant.lean` section `SingletonAllocation`, Blueprint `lem:bkl-singleton-allocation`), are in production. The
  raw (74) expansion at a fixed law, `Dᵐ⟪v, M v⟫(0)[h] = Σ_{∅≠J⊊[m]} ⟪κ_{|J|+1}(h_J,·), M κ_{m−|J|+1}(h_{Jᶜ},·)⟫` for any
  continuous linear `M` (`Analysis/BakryEmery/CumulantLeibniz.lean`, Blueprint `lem:bkl-raw-drift-expansion`), is in
  production; so are the cumulant permutation symmetry (`LocalCumulant.lean` section `CumulantSymmetry`) and the
  Boolean-mask complement pairing (`IteratedDerivative/Bilinear.lean`), the supports of the grouping. The grouping
  of (74) for `M = A⁻¹` as `2m κ_m + 2 L_m` with (72) is formalized (Stage 1 bullet above); the stochastic (71)/(73) are not.
- **Noise and non-explosion supports (2026-10-08, later):** covariance Cauchy–Schwarz
  (`Probability/Covariance/CauchySchwarz.lean`), the variance of a whitened statistic under an actual sandwich
  `S Cov S = 1` (`Probability/Covariance/Whitening.lean` section `WhitenedStatistic`; the sandwich is a
  hypothesis) and the trace energy `Σ (tr B_i)² ≤ n Σ (B_i)²_{jk}` (`Analysis/Matrix/Trace.lean` section
  `TraceEnergy`), the third-moment contraction `Σ (∫ x_i x_j x_k)² ≤ ∫ ‖x‖⁶` (`Probability/Moments.lean`) and the
  covariance radius bound `‖Cov μ_{c,Q}‖ ≤ r²` for priors in the closed `r`-ball (`KLS/BKL/PosteriorDomain.lean`
  section `CovarianceRadius`); Blueprint `lem:bkl-localization-supports`. The noise coefficient of (68) is bounded:
  `‖D_c(∫ f dμ_{·,Q})(c) ∘ Cov⁻¹ᐟ²‖² ≤ Var f ≤ C²` for `|f| ≤ C` on the prior support (`PosteriorDomain.lean` section
  `NoiseBound`, Blueprint `lem:bkl-noise-bound`). Deterministic supports and coefficient bounds only: no covariance
  dynamics, stochastic integral, Itô, strong solution or non-explosion theorem. The canonical sixth moment
  `∫ ‖Cov⁻¹ᐟ²(x − a)‖⁶ dμ_{c,Q} ≤ 6!(log 3/(8√(n+1)))⁻⁶ · 3^{3/4}/(1 − 3^{-1/4})` for a compact isotropic log-concave
  prior and self-adjoint PSD `Q` (`PosteriorDomain.lean` section `SixthMoment`, Blueprint
  `lem:bkl-posterior-sixth-moment`). The deterministic (69) entry identity `(P H_i P)_{jk} = ∫ (σV)_j(σV)_k(σV)_i dμ_{c,Q}`
  with the same principal root, for every finite `(c, Q)` incl. signed non-symmetric `Q` (`PosteriorDomain.lean` section
  `NoiseEntries`, generic form `Probability/CoordinateThirdMoment.lean`; Blueprint `lem:bkl-noise-entries`). The energy
  bounds on these slices are not formalized.
- **Ball-conditioning supports (2026-10-08, late):** the eighth-moment tail bounds `ν(B(0,R)ᶜ) ≤ M₈/R⁸` and
  `∫_{Bᶜ} ‖x‖⁴ ≤ M₈/R⁴` with the derived fourth integrability (`Probability/Moments.lean` section `MomentTails`,
  Blueprint `lem:moment-tails-eighth`), the first supports of the Letwin A.1 approximation dependency of the
  moment-potential producer; the half mass `2M₈ ≤ R⁸ ⇒ ν(B(0,R)) ≥ 1/2 > 0` (same section). The law conditioned on the
  open ball, `conditionOnBall` (Mathlib `cond`, positive ball mass), with the exact and degree-four quantitative errors
  of the expectation of `|f| ≤ C(1 + ‖x‖⁴)` (`Probability/Conditioning.lean`, Blueprint `lem:ball-conditioning`). No
  smoothing, covariance convergence or whitening of the conditioned sequence.
- **Uniform halfspace mass (2026-10-09):** for a Borel probability measure on a finite-dimensional real inner product
  space and `x₀` in the interior of the convex hull of its support, some `m ∈ (0, 1]` bounds the mass of every strict open
  halfspace through `x₀` (`Probability/ConvexSupport.lean`, Blueprint `lem:uniform-halfspace-mass`): the probability
  specialization of bound (54) in the proof of Cordero-Erausquin–Klartag Lemma 16. Lemma 16 itself, the existence of a
  moment potential and Letwin's quadratic-form bound with constant 8 are not formalized.
- **Canonical standardisation (2026-10-08, later):** for a compact isotropic prior and every finite `(c, Q)`, the
  principal root `Cov(μ_{c,Q})^{-1/2}` as a continuous linear equivalence transports the centred posterior to an
  isotropic law (`KLS/BKL/PosteriorDomain.lean` section `CanonicalStandardisation`; Blueprint
  `lem:bkl-canonical-standardisation`; the transported law of (75)–(77) with the same principal root). No rotation of
  the Brownian driver, SDE, Itô or non-explosion claim.
- **Metadata:** Blueprint nodes `lem:bkl-*`, `lem:letwin-*`, `prop:bkl-suspension`; `literature.json`
  (BKL2026 P71 `same`, E7274 `⇑`, T11/T41/L42/L43/E67 partial; Letwin2026 CZ14/LA4 `⇑`,
  L23/LA3/LA5/T25/D26/L27/L29/LA7/E23/T12 partial); audits
  `research/audits/BKL/*Audit.lean`; progress views regenerated from a temporary index.

## Next

Current controller: Codex chat `01a128eb-e254-7d63-bd15-05abfcb7aaec` (predecessor
`01a12708-9c39-7f33-aa23-3b135e6d1de2`, historical). On 2026-10-11 the owner requested a
new goal after the preceding goal stalled. The Goal service returned `active` for the bounded
[BKL Stage 2A goal](research/handoffs/2026-10-11-bkl-a4-goal.md): complete Letwin arXiv:2607.24164v1
Lemma A.4 and consume its actual cutoffs in A.5. The predecessor `01a12661-eb02-7580-9fbd-e91e778454cf`
was observed idle after a failed compaction turn and an interrupted subsequent turn; its unfinished exact
Stage 2 objective is not declared complete. Earlier controllers and superseded scheduling claims are
historical. Their prior current-state wording is retained in the
[goal transition record](research/decisions/2026-10-11-bkl-a4-goal-transition.md).

Stage 2A is integrated: Letwin Lemma A.4 for every source-class potential and every real `R ≥ 1` (with the
natural-index `C/(n+1)` form), Lemma A.5 for given cutoffs, and the nonconstant uniform-interval source-law client (see
"Uncommitted"). Its completion gate is the full local receipt of the integrated snapshot (`build/verification/latest.json`,
see "State"); until that receipt passes, Stage 2A is not complete. It makes no claim about the moment map of an
arbitrary law, Letwin Theorems 2.5, 1.1–1.2, BKL Lemma 4.2 without its hypothesis, Theorems 4.1/1.1 or `KLS.kls`. The
superseded Stage 2A execution notes (current units, transport diagnostic, packet classifications) are preserved
verbatim in [the integration record](research/decisions/2026-10-11-letwin-a4-a5-source-integration.md); authoritative
packet handles remain in `build/reviews/2026-10-11-bkl-a4-goal-setup/STATE.json`.

BKL arXiv:2610.05474v1 Theorem 1.1 remains the primary objective. Other papers are pursued only
for cited results and necessary prerequisites with an explicit BKL consumer. The exact dependency chain
is A.4 -> A.5 -> Letwin Theorem 2.5 -> Theorem 1.2 (constant 8) -> BKL Lemma 4.2 -> Theorem 4.1
-> Theorem 1.1. General CEK Theorem 2/uniqueness and full Letwin paper coverage remain deferred.

The established API-first roles continue: Codex coordinates and accepts; strong API models construct
proofs (prefer Astra, minimum GPT-5.6 Sol, no Luna); the existing reviewed Claude conversation is the
sole production integrator. Preserve the broad dirty tree and actual index. The new goal record
supersedes older controller/active-goal passages in the dated scope, API policy and staged-goal plans.

1. **Stage 2A integrated:** source A.4, A.5 for given cutoffs and the uniform-interval client; complete once the full
   local receipt of the integrated snapshot passes.
2. **Open parent Stage 2 (next):** Letwin Theorem 1.2, including necessary moment-map/regularity,
   Proposition 2.8, Theorem 2.5 and the Stein-kernel identity (2.21); no desired estimate as a premise.
3. **Later BKL stages:** original Eldan localization/SDE/Ito/non-explosion and cumulant dynamics;
   universal Theorem 4.1; unconditional Theorem 1.1 and `KLS.kls`. Existing Theorem 3.1,
   conditional Proposition 7.1 and Section 2 reduction are retained.
4. **Publication outside this goal:** commit, push, tags and remote Lean certification require separate
   owner authorization. No new proof or certificate status changes at goal setup.

## Open owner decisions

- Stochastic calculus for Theorem 4.1 and priorities 5–6: build it here or build on external Lean
  efforts; evidence and a recommendation are in
  [the options record](research/decisions/2026-10-03-stochastic-calculus-options.md).
- E. Milman Lemma 4.1 is recorded as `same`, although the real-infimum quantile differs from the
  paper's `−∞` in the degenerate case `f = 0`, `1 − ε < 0`; accept the convention or relabel it.
- Upstreaming generic infrastructure to Mathlib after an API cleanup (the `C^∞` symmetry of
  iterated derivatives is a candidate).
- CI cost: project build cache or a self-hosted runner while the repository is private.
- External stochastic closure (339 StochLean modules at pin `e6741e18`, Apache-2.0 per the root audit) for
  BKL Theorem 4.1: adopt as a vendored separate Lake package (R1) or keep as evidence (R0); see
  `build/reviews/2026-10-07-bkl-continuous/reviews/STOCHASTIC-EXTERNAL-REUSE-SCHEME-20261008.md` and
  `…/COEFFICIENT-SDE-MOMENTMAP-PROPOSALS-20261008.md` (the pinned closure has no SDE theorem; the
  Letwin moment-map producer is out of reach at the pin and stays an explicit hypothesis).

## Delivery

Follow [research/workflow.md](research/workflow.md): select work by paper and target theorem,
run change-appropriate checks, stage canonical metadata and regenerate progress with
`python3 research/progress/update.py`. Remote CI is Lean-only, on manual dispatch or a
`milestone/**` tag.
````

## Working link directory

- [2026-10-11 Letwin A.4/A.5 source integration](2026-10-11-letwin-a4-a5-source-integration.md)
- [2026-10-11 protocol/scheduling correction](2026-10-11-bkl-a4-protocol-scheduling-correction.md)
- [2026-10-11 handoff correction](2026-10-11-handoff-controller-correction.md)
- [2026-10-11 cutoff-profile adoption](2026-10-11-cutoff-profile-adoption.md)
- [2026-10-10 Stage 1 record](2026-10-10-bkl-stage1-integration.md)
- [2026-10-08 handoff history](2026-10-08-handoff-history.md)
- [2026-10-07 history](2026-10-07-handoff-history.md)
- [2026-10-02 history](2026-10-02-handoff-history.md)
- [paper register](../progress/LITERATURE.md)
- [node register](../progress/STATUS.md)
- [the A.4/A.5 integration record](2026-10-11-letwin-a4-a5-source-integration.md)
- [A.4/A.5 source integration](2026-10-11-letwin-a4-a5-source-integration.md)
- [profile](2026-10-11-cutoff-profile-adoption.md)
- [tail primitive](2026-10-11-cutoff-primitive-adoption.md)
- [rescaling/positivity](2026-10-11-rescaling-positivity-adoption.md)
- [real exhaustion](2026-10-11-real-exhaustion-adoption.md)
- [Stage 1 integration](2026-10-10-bkl-stage1-integration.md)
- [2026-10-10 handoff history](2026-10-10-handoff-history.md)
- [BKL Stage 2A goal](../handoffs/2026-10-11-bkl-a4-goal.md)
- [goal transition record](2026-10-11-bkl-a4-goal-transition.md)
- [the integration record](2026-10-11-letwin-a4-a5-source-integration.md)
- [the options record](2026-10-03-stochastic-calculus-options.md)
- [research/workflow.md](../workflow.md)
