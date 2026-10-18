# Remaining source-process comment archive

Date: 2026-10-18. Baseline: `b9ebbc3c41462fa269f4240ab5a95c703192aea2`.

Verbatim original comment passages from the primary library, certificate-entry and example scope.
Current sources retain mathematical statements, assumptions, literature locators and useful proof explanations.
Internal task/route labels, model/job provenance, rounds, migration and obsolete progress narration are historical here.
No non-comment code or existing historical record changes. Certificate states remain unchanged.
The full receipt of the published baseline retains its original snapshot; this documentation-only batch does not renew it.

## Original comments

### `formalization/FunctionalInequalities/Analysis/BakryEmery/Bochner/Basic.lean`

Original comment 1, line 7:

````lean
/-!
# Convex Hessians and the local Bochner identity: `B1`, `B3`, `B4`

Route obligations `B1`, `B3` and `B4` of `research/decisions/2026-09-20-bakry-emery-route.md`, for
the diffusion generator `ℒ f = Δ f - ⟪∇U, ∇f⟫` on a finite-dimensional real inner product space
`E`, with `Γ` and `Γ₂` as defined in `Gamma.lean`.

* `B1` (`bilinearIteratedFDerivTwo_nonneg_of_convexOn`): a `C²` convex function has a positive
  semidefinite Hessian, `0 ≤ D²U(x)(v, v)`. The proof restricts `U` to the line `t ↦ U (x + t v)`,
  whose convexity makes its derivative monotone (`ConvexOn.monotoneOn_deriv`) and hence its second
  derivative at `0` nonnegative (`Monotone.deriv_nonneg`); that second derivative is `D²U(x)(v, v)`.
* `B3` (`gammaTwo_eq_hessianSqStdBasis_add`, `bochner_stdBasis`): for `C³` `f` and `C²` `U`,

  `Γ₂(f) = ℒ(‖∇f‖²)/2 - ⟪∇f, ∇(ℒf)⟫ = ∑ᵢ ∑ⱼ (D²f(eᵢ, eⱼ))² + D²U(∇f, ∇f)`,

  where `eᵢ` is the **fixed** standard orthonormal basis `stdOrthonormalBasis ℝ E`. The double sum
  is the square of the Hessian in that basis (`hessianSqStdBasis`); its independence of the basis
  is not proved here, so no invariant Hilbert–Schmidt notation is introduced. The third-order
  derivatives `∑ⱼ ∂ⱼf ∑ᵢ ∂ᵢ∂ᵢ∂ⱼf` produced by `Δ‖∇f‖²/2` and by `⟪∇f, ∇Δf⟫` cancel exactly, after
  the commutation `∂ⱼ∂ᵢ∂ᵢ f = ∂ᵢ∂ᵢ∂ⱼ f` (`fderiv_fderiv_fderiv_apply_comm`); the drift
  contributions `-⟪∇U, ∇‖∇f‖²⟫/2` and `+⟪∇f, ∇⟪∇U, ∇f⟫⟫` leave exactly `+D²U(∇f, ∇f)` after the
  symmetry `∂ᵢ∂ⱼf = ∂ⱼ∂ᵢf` (route `B2`).
* `B4` (`gammaTwo_nonneg`, `bochner_nonneg_stdBasis`): for convex `U`, `0 ≤ Γ₂(f)`, as a sum of
  squares plus a value of the positive semidefinite Hessian of `U`.

* Improved Bochner (`norm_gradient_norm_gradient_sq_le`): for convex `U` and `C³` `f`,
  `‖∇‖∇f‖²‖² ≤ 4 ‖∇f‖² Γ₂(f)`, by Cauchy–Schwarz in the standard basis. Its consequence
  `weightedLaplacian_sqrt_sub_div_nonneg` is the pointwise `L¹` self-improvement inequality
  `0 ≤ ℒ(√(ε + Γ(f)) - √ε) - Γ(f, ℒf)/√(ε + Γ(f))` for `ε > 0`, via the chain rule
  `weightedLaplacian_comp`.

The identity holds in every finite dimension, including dimension zero, where both double sums are
empty.

## What this is not

Pointwise identities for classical smooth functions. Nothing is said about the heat semigroup
`P_t`, about `Γ(P_t f) ≤ P_t Γ(f)` or any gradient estimate, about non-smooth or lower-dimensional
log-concave laws, or about Buser's inequality.
-/
````

Original comment 2, line 59:

````lean
/-! ### `B1`: convexity gives a positive semidefinite Hessian -/
````

Original comment 3, line 105:

````lean
/-- **Route `B1`**: the Hessian of a `C²` convex function is positive semidefinite,
`0 ≤ D²U(x)(v, v)` for all `x v`. -/
````

Original comment 4, line 290:

````lean
/-! ### `B3` and `B4` -/
````

Original comment 5, line 296:

````lean
/-- **Route `B3`, the Bochner identity in the standard orthonormal basis**: for `C²` `U` and `C³`
`f`, `Γ₂(f) = ∑ᵢ ∑ⱼ (D²f(eᵢ, eⱼ))² + D²U(∇f, ∇f)`. -/
````

Original comment 6, line 315:

````lean
/-- **Route `B3` in expanded form**: for `C³` `U` and `f`,
`(Δ‖∇f‖² - ⟪∇U, ∇‖∇f‖²⟫)/2 - ⟪∇f, ∇(Δf - ⟪∇U, ∇f⟫)⟫ = ∑ᵢ ∑ⱼ (D²f(eᵢ, eⱼ))² + D²U(∇f, ∇f)`. -/
````

Original comment 7, line 329:

````lean
/-- **Route `B4`**: for a `C²` convex potential and a `C³` function, `0 ≤ Γ₂(f)`. -/
````

Original comment 8, line 336:

````lean
/-- **Route `B4` in expanded form**: for a `C³` convex potential and a `C³` function,
`0 ≤ (Δ‖∇f‖² - ⟪∇U, ∇‖∇f‖²⟫)/2 - ⟪∇f, ∇(Δf - ⟪∇U, ∇f⟫)⟫`. -/
````

### `formalization/FunctionalInequalities/Analysis/BakryEmery/Cumulant/Leibniz.lean`

Original comment 12, line 148:

````lean
/-- Exact deterministic grouping of BKL arXiv:2610.05474v1, (72)–(74), at a fixed law: the `2m`
singleton/complement allocations give `2m * kappa_m`, and all middle allocations pair to twice the sum over the
middle masks containing the slot `i0` (72). It assumes only compact support and invertibility of the actual
covariance, for every `m ≥ 3`; it contains no stochastic process, Itô formula or cumulant evolution conclusion.
Proof body: independently accepted Astra v5 (`round1.lean` ca257ea4…), verbatim. -/
````

### `formalization/FunctionalInequalities/Analysis/BakryEmery/Cumulant/Local.lean`

Original comment 13, line 14:

````lean
/-!
# Third cumulants from one exponential moment

Bizeul–Klartag–Lehec arXiv:2610.05474v1, Lemma 4.2, in its source scope: log-concavity guarantees
some positive exponential radius (Borell) but not, in general, every exponential moment, so the third-cumulant
identity and the Hilbert–Schmidt contraction bound are derived here from a single radius `r > 0`
with `∫ e^{r‖x‖} dμ < ∞`: `κ₃(u,v,w) = ∫⟪u,x⟫⟪v,x⟫⟪w,x⟫` for centered `μ`, polynomial `L²`
membership, and `∑_{jk} κ₃(u,e_j,e_k)² ≤ 8‖u‖²` under isotropy and the Letwin quadratic bound
(contraction argument as in `Cumulant`, whose all-radii version keeps its own provenance); the second
cumulant of any such law is the centered second moment, i.e. the covariance pairing. A law with
compact support has every exponential moment. The log-concave adapter and the Eldan base case are
in `KLS/BKL/LocalThirdCumulant.lean`. Proof bodies: Codex route (bundles `Local-Third-Cumulant` and
`Local-Second-Cumulant`, independently accepted); statements and placement: Claude.
-/
````

Original comment 14, line 512:

````lean
/-! BKL arXiv:2610.05474v1, p. 20, the sentence before (74): for `Λ = logLaplace μ` of a compactly supported law
and `v(z) = ∇Λ(z) − ∇Λ(0)`, `v(0) = 0`, `Dv(0) = A` (the covariance) and, for every `r ≥ 1`,
`Dʳv(0)[h] = cumulantVector μ (List.ofFn h)`, i.e. `⟪Dʳv(0)[h], w⟫ = κ_{r+1}(h, w)` (generic supports in
`Analysis/IteratedDerivative/GradientJet.lean`). Proof bodies: Luna (`gpt-5.6-luna`, CGF1-M and CGF1-C round 8)
with two recorded closing-line repairs by Claude each, and the CGF1-J2c round-8 body (Claude assembly v2, independently
accepted); statements, `cumulantVector` and placement: Claude. -/
````

### `formalization/FunctionalInequalities/Analysis/BakryEmery/Curvature.lean`

Original comment 15, line 4:

````lean
/-!
# The curvature condition `CD(ρ, ∞)` for a potential with Hessian bounded below

Bakry–Gentil–Ledoux, *Analysis and Geometry of Markov Diffusion Operators* (2014), discussion before
Corollary 4.8.2: for `ℒ f = Δ f - ⟪∇U, ∇f⟫` and `Γ(f) = ‖∇f‖²`, the Bochner identity
`Γ₂(f) = ‖∇∇f‖² + ∇∇U(∇f, ∇f)` shows that `∇∇U ≥ ρ Id` implies `CD(ρ, ∞)`, that is
`Γ₂(f) ≥ ρ Γ(f)`.

This file proves that pointwise statement (`mul_gamma_le_gammaTwo`), that a Hessian bounded below
by `ρ ≥ 0` makes `U` convex, and the integrated form against `μ = m.tilted (-U)`:
`∫ Γ₂(f) dμ = ∫ (ℒf)² dμ` for compactly supported `C³` functions `f`, hence
`ρ ∫ Γ(f) dμ ≤ ∫ (ℒf)² dμ`, the inequality behind BGL Proposition 4.8.3. The Hessian bound is
`∀ x v, ρ * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ U x v v`.

Compactly supported coercivity (`compact_ordinary_diffusion_coercivity`): for `U` of class `C²` and a smooth compactly
supported `u`, the functions `∇∇U(∇u, ∇u)` and `(ℒu)²` are `μ`-integrable and `∫ ∇∇U(∇u, ∇u) dμ ≤ ∫ (ℒu)² dμ`, from
`Γ₂(u) = ‖∇∇u‖² + ∇∇U(∇u, ∇u)` and the integrated identity; no lower Hessian bound is assumed. This concerns the ordinary
weighted Laplacian `ℒ`, not the inverse-Hessian operator: support for the finite-energy Brascamp–Lieb argument of Letwin,
arXiv:2607.24164v1, Lemma A.6, not that lemma. Proof bodies: strong-API candidate (gpt-6-astra,
`api-finite-energy-bl-compiler-v6`, cadc3b6c…), verbatim; placement: Claude.
-/
````

### `formalization/FunctionalInequalities/Analysis/BakryEmery/Gamma.lean`

Original comment 17, line 21:

````lean
/-! ### The carré du champ and `B0` -/
````

Original comment 18, line 83:

````lean
/-- **Route `B0`, the carré-du-champ product identity**: for `C²` functions `f`, `g` and any
potential `U`, `(ℒ(fg) - f ℒg - g ℒf) / 2 = Γ(f, g) = ⟪∇f, ∇g⟫`. -/
````

Original comment 19, line 101:

````lean
/-- `Γ₂` written out in gradients and Laplacians, exactly the left-hand side of route `B3`. -/
````

### `formalization/FunctionalInequalities/Analysis/BakryEmery/HessianOperator.lean`

Original comment 20, line 7:

````lean
/-!
# The Hessian operator, its inverse and the inverse-Hessian diffusion operator

Letwin arXiv:2607.24164v1, pp. 5–7: for a smooth potential `φ` with positive definite Hessian, the
Hessian operator `∇²φ(x) = D(∇φ)(x)` is a self-adjoint unit with positive definite inverse; the
inverse Hessian is symmetric, inverts the Hessian in coordinates, and satisfies the derivative formula
(2.5) `∂_k ((∇²φ)⁻¹)_{ij} = −Σ_{a,c} ((∇²φ)⁻¹)_{ia} ∂_{kac}φ ((∇²φ)⁻¹)_{cj}` (operator and coordinate
forms). The operator `L = Σ ((∇²φ)⁻¹)_{ij} ∂_{ij} − Σ (∂_i V ∘ ∇φ) ∂_i` of (2.3) with the inverse Hessian as
coefficient field has the Leibniz rule. The potential `φ` is given (Letwin Lemma 2.2, moment-map
existence, is not provided); no Monge–Ampère equation, Lemma 2.4, Lemma 2.6, Brascamp–Lieb or
positive-semidefinite estimate is used or claimed. Proof bodies: Codex route bundle `MA-Inverse`
(independently accepted); statements and placement: Claude.

Letwin Lemma A.4 (p. 17) supporting results for the operator `L` of a given potential: the self-generator identity
`L φ = n − ⟨∇V(∇φ), ∇φ⟩` at a point with positive definite Hessian (`hessianInverseOperator_self`), its uniform bound
when `∇φ` takes values in a bounded `K` and `V` is `C¹` on an open set containing `closure K`
(`bounded_hessianInverseOperator_self`, compact-image bound of the pointwise identity), and the composition rule
`L(h ∘ W) = h′(W) LW + h″(W) Σ_{ij} ((∇²φ)⁻¹)_{ij} ∂_iW ∂_jW` for `C²` `W`, `h` with no hypothesis on `φ`
(`hessianInverseOperator_comp`). The minimum of `φ` is in `Analysis/Convex/Coercivity.lean`; the cutoffs `η(W/R)` and
their defect bound (Lemma A.4) are constructed in `IntegrationByParts/InverseHessian/Cutoff.lean`. Not provided: the
moment map. Proof bodies: Codex API jobs
`letwin-a4-self-astra-high-v2` (ff901785…), `letwin-a4-bounded-astra-high-v2` (f666a094…) and
`letwin-a4-chain-astra-high-v4` (d2f84023…), independently verified; statements and placement: Claude.

Also for Lemma A.4: the coefficient extraction `Σ_ij A_ij ∂_iφ ∂_j(h ∘ φ) = h′(φ) Σ_ij A_ij ∂_iφ ∂_jφ` in any orthonormal
basis (`sum_inverseHessianEntry_mul_fderiv_comp`, used by the energy identity in `IntegrationByParts/InverseHessian/Basic.lean`)
and the pointwise defect domination
`|L(e((φ − c)/R))| ≤ |R⁻¹e′((φ − c)/R)| |Lφ| + R⁻² |e″((φ − c)/R)| |Σ_ij A_ij ∂_iφ ∂_jφ|` for `C²` `φ`, `e` and all real
`c`, `R` (`abs_hessianInverseOperator_comp_sub_div_le`; the affine rescaling comes from the scalar leaf
`Analysis/Cutoff/Profile.lean`). Proof bodies: Codex API jobs `letwin-a4-energy-pointwise-astra-high-responses-v2`
(e0a237b1…) and `letwin-a4-pointwise-defect-astra-high-responses-v2` (one compiler-reported unused tactic removed,
a2f63c12…), independently verified, verbatim. The operator `L f` of a `C²` `f` is continuous for smooth `φ` with
positive definite Hessian and `V` `C¹` on an open set containing the gradient range
(`continuous_hessianInverseOperator`; `letwin-a4-operator-continuity-astra-feedback-responses-v7`, dadbfa97…).
-/
````

Original comment 21, line 494:

````lean
/-- **Operator continuity** (Letwin Lemma A.4, p. 17, measurability of `Lχ_R`, hence `Lχ_R ∈ L¹(ν)` by domination):
for smooth `φ` with positive definite Hessian, `V` `C¹` on an open set containing the gradient range and `C²` `f`,
`L f` is continuous. Proof body: Codex API job `letwin-a4-operator-continuity-astra-feedback-responses-v7`
(dadbfa97…), independently verified, verbatim. -/
````

### `formalization/FunctionalInequalities/Analysis/BakryEmery/HessianTrace.lean`

Original comment 22, line 3:

````lean
/-!
# Trace evolution of the Hessian under the inverse-Hessian operator

For a smooth `φ` on a finite-dimensional real inner-product space, `stdHessianMatrix φ x` is the Hessian matrix of `φ` in the
standard orthonormal basis (index type `StdBasisIndex E`), `stdHessianMatrixDeriv φ x a` its derivative along the `a`-th
basis vector, and `stdHessianMatrixGenerator φ V x` its entrywise image under the inverse-Hessian operator
`L = hessianInverseOperator φ V`. For every constant real matrix `B` and every point `x`
(`hessianInverseOperator_trace_stdHessianMatrix_sq`):
`L tr(B H B H) = 2 tr(B H B (L H)) + 2 Σ_ab A^{ab} tr(B ∂_a H B ∂_b H)` with `A = (∇²φ)⁻¹` (`inverseHessianEntry`), the
pointwise trace identity (2.8) of Letwin, arXiv:2607.24164v1, in the proof of Theorem 2.5. There is no positive
semidefiniteness, commutation or Monge–Ampère premise. Not provided: the substitution of the twice-differentiated
Monge–Ampère equation, (2.10), the tensor comparison and the trace bound of Theorem 2.5. Proof bodies: strong-API candidate
(gpt-6-astra, `api-trace-nonconstant-client-v10`, b37b32bf…; generic part verbatim from `api-trace-square-patch-v7`),
verbatim up to the declaration names; placement and names: Claude.

Monge–Ampère substitution (section `MongeAmpereTrace`). For a GIVEN smooth `φ` with positive definite Hessian at every
point satisfying the zero-order Monge–Ampère relation `log det ∇²φ = −φ + V(∇φ)`, with `V` smooth only on an open `U ⊇
closure K` and `range ∇φ ⊆ K`: Letwin (2.9), `L H = −H + H ∇²V(∇φ) H + G` with the inverse-Hessian third-derivative Gram
matrix `G = stdThirdGram φ x` (`stdHessianMatrixGenerator_apply_on_range`, `stdHessianMatrixGenerator_eq_on_range`), and
(2.10) for every constant real `B` (`traceGenerator_210_on_range`). If moreover `K` is open, `V` convex on `K` and `B`
positive semidefinite, the three remainders `Σ A^{ab} tr(B∂_aH B∂_bH)`, `tr(BHB·H∇²V(∇φ)H)` and `tr(BHB·G)` are
nonnegative, hence `L tr(BHBH) + 2 tr(BHBH) ≥ 0` pointwise (`traceGeneratorCondition_on_range`). This is the pointwise
condition before Lemma A.5; its integration (A.4/A.5 for this trace function), the moment map of an arbitrary source law
and the trace bound of Theorem 2.5 are not provided. Proof bodies: strong-API candidate (gpt-6-astra,
`api-trace-monge-ampere-210-v3`, de34b430…), verbatim up to the declaration names; placement and names: Claude.
-/
````

### `formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts/Basic.lean`

Original comment 24, line 6:

````lean
/-!
# Weighted integration by parts

Haar integration by parts and its tilted-measure specialization. The pointwise
weighted Laplacian and its regularity are provided by Laplacian.lean; no convexity is used. The
compact-test directional identity `∫ ∂ᵥF · g = −∫ F · ∂ᵥg` for smooth `F`, `g` with either one compactly
supported derives its integrability from the compact support (Codex route bundle
`MA-Metric-IntegrationByParts`, independently accepted; statement and placement: Claude).
-/
````

Original comment 29, line 200:

````lean
/-- **Weighted integration by parts for a tilted Haar measure** (route obligation `G0`): with
`μ = m.tilted (-U)` the normalised law of density `exp (-U)`, a `C¹` potential `U`, a `C²`
compactly supported `f` and a `C¹` function `g`,
`∫ ⟪∇f, ∇g⟫ dμ = ∫ (-ℒf) g dμ` where `ℒf = Δf - ⟪∇U, ∇f⟫`. -/
````

Original comment 30, line 251:

````lean
/-- **Weighted directional integration by parts** (Letwin arXiv:2607.24164v1, Lemma A.3, pp. 16–17):
for smooth `φ, f, g` with `∫ e^{-φ} dm = 1` and the four integrands `(∂_v f) g`, `f ∂_v g`, `f g ∂_v φ`,
`f g` integrable under `ν = e^{-φ} m`,
`∫ (∂_v f) g dν = ∫ f ((∂_v φ) g − ∂_v g) dν`. Codex proof
(`build/reviews/2026-10-07-bkl-continuous/queue/letwin-prerequisite/Letwin-A3-Codex-Proof.lean`,
independently accepted). -/
````

Original comment 31, line 331:

````lean
/-- **Mean Hessian equals the gradient second moment** under `e^{-φ}m` (Letwin Lemma 2.3, step 1; Luna, task
LW-L23a, closing step repaired at integration): the directional integration by parts applied to `∂_u φ` and
`g = 1`. -/
````

### `formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts/ConvexHessian.lean`

Original comment 32, line 7:

````lean
/-!
# Hessian integrability and the mean Hessian of a convex potential

Letwin, arXiv:2607.24164v1, Lemma 2.3 (analytic part), for a given smooth convex potential `φ` with
`e^{-φ}` a probability density on a finite-dimensional inner product space and `∇φ ∈ L²(ν)`,
`ν = e^{-φ} dx`: the diagonal Hessian entries are integrable (cutoff integration by parts, uniform
bound, Fatou), hence all mixed entries, and `∫ ∂_u∂_v φ dν = ∫ ∂_uφ ∂_vφ dν`. No Hessian
integrability, regularity, growth or exponential moment is assumed. The isotropy adapter is in
`KLS/Isotropic.lean`. Proof bodies: root Codex (bundle `Convex-Hessian-Moment`, independently
accepted); statements and placement: Claude.
-/
````

### `formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts/InverseHessian/Basic.lean`

Original comment 34, line 5:

````lean
/-!
# Integration by parts for the inverse-Hessian operator (Letwin (2.2), compact tests)

Letwin arXiv:2607.24164v1, pp. 6–7: for a given smooth potential `φ` with everywhere positive definite
Hessian, `∫ e^{−φ} = 1` and the zero-order Monge–Ampère equation `log det ∇²φ = −φ + V ∘ ∇φ` with `V`
smooth on an open set containing the gradient range (the source has `V` smooth near the closure of the
bounded convex `K = ∇φ(ℝⁿ)`), the operator `L f = Σ_{ij} A_{ij} ∂_{ij}f − Σ_i ∂_iV(∇φ) ∂_if`, `A = (∇²φ)⁻¹`,
satisfies the weighted integration by parts `∫ (Lf) g dν = −∫ Σ_{ij} A_{ij} ∂_if ∂_jg dν`, `dν = e^{−φ}dx`,
for smooth `f`, `g` with one of them compactly supported; hence `∫ Lf dν = 0` and the integrated symmetry
`∫ (Lf) g dν = ∫ f (Lg) dν` on compact smooth tests. Haar integrability comes from the compact test; the
normalisation gives integrability of `e^{−φ}` and the probability property of `ν`. Lemma A.5 holds for given cutoffs
with the conclusions of Lemma A.4 (`integrable_and_integral_hessianInverseOperator_eq_zero_of_cutoffs`, through the
generic `integrable_and_integral_eq_zero_of_cutoff_defect`). The cutoffs themselves (Lemma A.4) are constructed
downstream in `IntegrationByParts/InverseHessian/Cutoff.lean`: `exists_scaled_cutoffs_hessianInverseOperator` for real
`R ≥ 1` and its natural-index form `exists_cutoffs_hessianInverseOperator`, whose conclusions are exactly the cutoff
premises of Lemma A.5 here. Not provided: a moment map for an arbitrary law, a closed `L²` generator, Brascamp–Lieb
(A.6), Theorem 2.5 or Proposition 2.8. Proof bodies of the compact-test results: Codex route bundle
`MA-Metric-IntegrationByParts` (independently accepted); statements and placement: Claude.
-/
````

Original comment 36, line 184:

````lean
/-- **Letwin Lemma A.5 for the inverse-Hessian operator, given cutoffs** (p. 18): for a given potential as in (2.2),
smooth bounded `f` with `Lf + c f ≥ 0`, `c > 0`, and smooth compactly supported cutoffs with the conclusions of
Lemma A.4 (`0 ≤ χ_n ≤ 1`, `χ_n → 1`, `‖Lχ_n‖_{L¹(ν)} → 0`), `Lf ∈ L¹(ν)` and `∫ Lf dν = 0`. The symmetry and the
cutoff-product integrability are derived from (2.2) and continuity. The cutoffs are a premise here; for a potential in
the Lemma A.4 source class they are supplied by `exists_cutoffs_hessianInverseOperator`
(`IntegrationByParts/InverseHessian/Cutoff.lean`). Proof body: independently checked Astra (`round1.lean` 365a8d73…),
verbatim. -/
````

Original comment 37, line 281:

````lean
/-- **Energy identity** (Letwin Lemma A.4, p. 17: (2.2) with `f = φ`, `g = h ∘ φ`): for a given potential as in (2.2)
and smooth `h` with `h ∘ φ` compactly supported, `∫ (Lφ) h(φ) dν = −∫ h′(φ) Σ_ij A_ij ∂_iφ ∂_jφ dν`. No minimum,
cutoff or bound is a premise. Proof body: Codex API job `letwin-a4-energy-identity-from-pointwise-astra-high-responses-v6`
(9fd2dc24…), independently verified, verbatim. -/
````

Original comment 38, line 311:

````lean
/-- **Weighted energy bound** (Letwin Lemma A.4, p. 17: `R⁻² ∫ w(W/R) Γ dν = ∫ q_R(W) LW dν ≤ ‖q_R‖_∞ ‖LW‖_{L¹}`): under
the hypotheses of the energy identity, `|Lφ| ≤ D` and `|h| ≤ M`, the energy integrand `h′(φ) Γφ` is integrable and
`−∫ h′(φ) Γφ dν ≤ D M`. No energy inequality or global integrability of `Γφ` is a premise. Proof body: Codex API job
`letwin-a4-local-sum-equality-astra-medium-v4` (c4f53c4c…), independently verified, verbatim. -/
````

### `formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts/InverseHessian/Cutoff.lean`

Original comment 39, line 4:

````lean
/-!
# Letwin Lemma A.4: the cutoff family (source construction)

Letwin, arXiv:2607.24164v1, Lemma A.4 (p. 17), for a given potential in the source class: smooth convex `φ` with gradient
image in a bounded `K`, `V` smooth on an open `U ⊇ closure K`, the pointwise Monge–Ampère equation, positive definite
Hessian and `∫ e^{−φ} dm = 1`, in any finite dimension and for any additive Haar measure `m`.
`exists_scaled_cutoffs_hessianInverseOperator` constructs, for every real `R ≥ 1`, `χ_R = η((φ − c)/R)` with
`c = min φ − 1` and `η = smoothTransition (2 − ·)`: smooth, compactly supported, `[0,1]`-valued, monotone in `R` on
`[1, ∞)`, tending to `1`, with `Lχ_R ∈ L¹(ν)` and one constructed `C ≥ 0` such that `∫ |Lχ_R| dν ≤ C/R`, so the defect
tends to `0`. The minimum of `φ` and its compact sublevel sets (from convexity and the normalization), the
self-generator bound, the profile bounds, the weighted energy estimate and the integrability of `Lχ_R` are derived in
the proof, never assumed. The natural-index corollary `exists_cutoffs_hessianInverseOperator` takes `χ_n = χ_{n+1}`, with
the same `C` and the bound `C/(n+1)`; its conclusions are the cutoff premises of Lemma A.5
(`integrable_and_integral_hessianInverseOperator_eq_zero_of_cutoffs`). The moment map itself is not constructed: the
source-class properties are hypotheses.

Private local supports: compact support through a compact sublevel set, the shifted tail primitive, the source-form
pointwise defect bound and one scalar monotonicity step. Proof bodies: the fixed source construction (Codex) with the
independently verified Codex API helper and unit proofs (`letwin-a4-support-compact/shifted/defect-astra-v1`,
`letwin-a4-support-add-monotonicity-astra-v1` after scalar `add_comm` normalization) and, for the natural-index
corollary, the independently verified Codex API proof (`letwin-a4-natural-from-actual-astra-v1`), verbatim; placement:
Claude.
-/
````

### `formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts/WeakLaplacian.lean`

Original comment 60, line 5:

````lean
/-!
# Rough weak pairing for the ordinary weighted Laplacian

Weak counterpart of `integral_inner_gradient_tilted`: the ordinary weighted Laplacian `ℒv = Δv - ⟪∇U, ∇v⟫` of a
compactly supported smooth test, at a C1 potential `U` with `∫ e^{-U} = 1`, paired with a globally bounded weak
function. Support for Letwin arXiv:2607.24164v1 Lemma A.6 at C^{1,1}. Proof body: accepted Codex closed assembly
(light variant without the inverse-Hessian import), verbatim.
-/
````

### `formalization/FunctionalInequalities/Analysis/BakryEmery/InverseHessianEnergy.lean`

Original comment 62, line 3:

````lean
/-!
# The inverse-Hessian energy of a gradient

For a potential `U` with pointwise positive definite Hessian `H = hessianOperator U x` and a test `f`, the energy is
`⟪∇f, H⁻¹ ∇f⟫` with the ring inverse `H⁻¹`. Young's inequality `2⟪v, w⟫ ≤ ⟪v, H⁻¹ v⟫ + D²U(w, w)`
(`hessian_inverse_young`, no uniform curvature constant); `⟪∇f x, v⟫ = Df(x) v` (`gradient_pairing_eq_fderiv`); the energy
in any orthonormal basis is `Σ_ij (H⁻¹)_ij ∂_i f ∂_j f` (`inverse_hessian_energy_eq_coordinate_sum`); for smooth `U` and `C¹`
`f` it is continuous (`continuous_inverse_hessian_gradient_energy`), and it is nonnegative
(`inverse_hessian_gradient_energy_nonneg`) in every dimension, zero included. Used by the scalar Brascamp–Lieb inequality
(`KLS/LogConcave/BrascampLieb.lean`); the smooth inverse entries come from `MongeAmpere.lean`, so these facts sit above it
rather than in `HessianOperator.lean`. Proof bodies: strong-API candidate (gpt-6-astra, `api-scalar-bl-extended-gaussian-v5`,
394a24b1…), verbatim, with the candidate's section variable context; placement: Claude.
-/
````

### `formalization/FunctionalInequalities/Analysis/BakryEmery/MongeAmpere.lean`

Original comment 64, line 11:

````lean
/-!
# The Monge–Ampère log-determinant relation: right-hand-side derivative

Letwin arXiv:2607.24164v1, (2.2)–(2.4): for a smooth `φ` and a `V` smooth on an open set containing
the gradient image, the zero-order equation `log det ∇²φ = −φ + V ∘ ∇φ` (a hypothesis here)
differentiates on its right-hand side to `−Dφ + DV(∇φ)[∇²φ ·]`; Jacobi's formula for the Hessian gives the
left-hand side, hence the first derivative (2.4) of the equation; differentiating once more gives (2.6)
with the inverse-Hessian operator, whose two right-hand-side matrices (`∇²φ ∇²V(∇φ) ∇²φ` for convex `V`,
and the inverse-Hessian-weighted third-derivative Gram matrix) are positive semidefinite. Section
`QuadraticForm` (Letwin Lemma A.4, p. 17): at a point with positive definite `C²` Hessian, the inverse-Hessian quadratic
form `Σ_ij ((∇²φ)⁻¹)_{ij} a_i a_j` is nonnegative in every orthonormal basis and every rank
(`sum_inverseHessianEntry_mul_mul_nonneg`; proof body: Codex API job `letwin-a4-inverse-quadratic-nonneg-astra-high-v1`
with the existing inverse-matrix lemma explicitly instantiated, 99d92f10…, independently verified). Section
`Divergence`: the coordinate divergence of the inverse Hessian `Σ_i ∂_i A_{ij} = Σ_i A_{ij} ∂_iφ − ∂_jV(∇φ)`
(from the zero-order equation, Jacobi and the third-slot commutation), the flux form
`Σ_i ∂_i (e^{−φ} A_{ij}) = −e^{−φ} ∂_jV(∇φ)` and the density divergence form of the operator `L` of (2.2). The
potential `φ` is given; moment-map existence (Lemma 2.2), Theorem 2.5, Brascamp–Lieb and Proposition 2.8 are
not provided. Proof bodies: Codex route bundles `MA-Inverse`, `MA-Jacobi`, `MA-Second-Derivative` and
`MA-Metric-IntegrationByParts` (independently accepted); statements and placement: Claude.
-/
````

### `formalization/FunctionalInequalities/Analysis/BakryEmery/Tilt/LocalDerivatives.lean`

Original comment 65, line 4:

````lean
/-!
# Local all-order derivatives of exponentially weighted integrals

Bizeul–Klartag–Lehec arXiv:2610.05474v1, Section 2 (p. 5), regular approximation: inside a single
exponential radius `r` (integrability of `e^{t‖x‖}‖g(x)‖` for `t < r`), the function
`z ↦ ∫ e^{⟪z,x⟫} g(x) dμ` has all derivatives given by the moment tensors `∫ e^{⟪z,x⟫} ∏⟪x,h_j⟫ g dμ`
for `‖z‖ < r`; at `z = 0` the Laplace transform of a probability law has `D^d L_μ(0)(h) = ∫ ∏⟪x,h_j⟫ dμ`
with operator norm at most the norm moment `∫ ‖x‖^d dμ`. This extends the one-radius calculus of
`Tilt.Local` (it must not import the Borell moment module, which depends on this family).
Proof bodies: Codex q_batch (bundle `Gaussian-AllOrder-Growth`, independently accepted); statements
and placement: Claude.
-/
````

Original comment 66, line 168:

````lean
/-- **The first Taylor tensor is the centered first moment**: for `f ∈ L²(μ)`,
`T_1 f (w) = ∫ ⟪w, x⟫ f(x) dμ − (∫ f dμ) ∫ ⟪w, x⟫ dμ` (BKL p. 30, the `d = 1` coefficient; Luna, task
RED-D1c). -/
````

### `formalization/FunctionalInequalities/Analysis/Convex/Affine.lean`

Original comment 75, line 4:

````lean
/-!
# Affine subtraction from extended-real potentials

`affineSubtract a b φ x = φ x - (⟪a, x⟫ + b)`: finite shifts commute with suprema, the Legendre transform is translated
accordingly (`legendre_affineSubtract`), convex real epigraphs are preserved, finite shifts cancel in `EReal`, and a
touching plane at `0` normalizes a potential to be nonnegative and zero at the origin. Pointwise; no measure.

Declaration blocks are verbatim from the root-accepted CEK Proposition 12 bundle (`independent-p12-attainment`, ACCEPTANCE 848aa45b…) under the reviewed rev3 migration map.
-/
````

### `formalization/FunctionalInequalities/Analysis/Convex/AffineMaximum.lean`

Original comment 76, line 4:

````lean
/-!
# Finite affine maxima below a Legendre transform

`affineMaximum s hs a y` is the maximum of the affine functions `y ↦ ⟪x, y⟫ - a x` over a nonempty finite set `s`
(`continuous_affineMaximum`). Every open neighbourhood of `0` in a finite-dimensional space contains such a set whose
convex hull has `0` in its interior, including in dimension zero (`exists_finite_hull_neighborhood`), and then the
maximum grows at least linearly with a constant independent of intercepts bounded at the vertices
(`affineMaximum_coercive`). With intercepts `(ψ ·).toReal` at finite values it lies below `legendre ψ`
(`affineMaximum_le_legendre`); convergence at the finitely many vertices gives one eventual uniform lower bound for the
transforms of a sequence (`eventually_affineMaximum_sub_le_legendre`, Cordero-Erausquin–Klartag, *Moment measures*,
arXiv:1304.0630v1, (60)).

This is the geometric part of the proof of Lemma 17, (56b); the integration step is in
`Probability/MomentMeasure/ConjugateMass.lean`. Declaration blocks are verbatim from ConjugateMass (90a65ba7…) of the
root-accepted Lemma 17 bundle (ACCEPTANCE ec6d356c…).
-/
````

### `formalization/FunctionalInequalities/Analysis/Convex/BoundedConjugate.lean`

Original comment 77, line 8:

````lean
/-!
# Extended-real potentials with bounded effective domain and their conjugates

For an extended-real potential `φ` on a real inner-product space whose effective domain lies in `closedBall 0 L`:
`closedBallCap φ L` is `φ` on the ball and `⊤` outside, lower semicontinuous with `φ`
(`closedBallCap_lowerSemicontinuous`); in finite dimension a proper lower semicontinuous `φ` attains a real minimum
(`exists_real_global_minimum_of_bounded_domain`); a real floor `m` gives `φ* x ≤ L‖x‖ − m`
(`legendre_le_of_real_lower_bound`), so the conjugate is finite everywhere (`legendre_finite_of_bounded_domain`); a real
representative `ψ` of a finite conjugate is convex (`real_convexOn_legendre`) and `L`-Lipschitz
(`lipschitzWith_real_legendre`), and satisfies the real Fenchel inequality at finite points (`real_legendre_fenchel`).
Infinite values are excluded before every real conversion. Used by the bounded-source producer of
`KLS/CEK/BoundedPrimal.lean`. Proof bodies: strong-API candidate (gpt-6-astra, `api-bounded-primal-geometry-v11`,
d77ddfc1…), verbatim up to the name `cap ↦ closedBallCap`; the candidate's variable context is kept (its `omit` lines name
the measurable-space binders, which no statement here uses); placement: Claude.
-/
````

### `formalization/FunctionalInequalities/Analysis/Convex/Coercivity.lean`

Original comment 78, line 5:

````lean
/-!
# Minimum and compact sublevels of a convex potential with integrable `e^{-φ}`

Letwin arXiv:2607.24164v1, Lemma A.4 (p. 17), first sentence of the proof: a finite convex `φ` on a finite-dimensional
real inner product space with `e^{-φ}` integrable for an additive Haar measure attains its minimum, and every sublevel
set is compact (`exists_forall_le_and_isCompact_sublevel_of_convexOn_integrable_exp_neg`). No minimum, coercivity or
bounded-sublevel premise; the source normalisation `∫ e^{-φ} = 1` only supplies the integrability. Dimension zero is
included. Route: every sublevel has finite Haar volume; a convex set of finite volume containing a ball is bounded
(otherwise it contains arbitrarily many disjoint translates of a smaller ball); closed and bounded sublevels are
compact, and the minimum over the nonempty sublevel `{φ ≤ φ 0}` is global. Proof body: Codex API job
`letwin-a4-coercive-astra-high-v6` (source 14da3e46…, independently verified); statement and placement: Claude.
-/
````

### `formalization/FunctionalInequalities/Analysis/Convex/Legendre.lean`

Original comment 81, line 8:

````lean
/-!
# Extended-real potentials and the Legendre transform

For `φ : E → EReal` on a real inner product space, `legendre φ y = ⨆ x, ⟪x, y⟫ - φ x` is the actual extended-real
Legendre transform, with no selected maximizers. `ConvexPotential φ` excludes `-∞` and asks for a convex real epigraph;
`ProperPotential φ` excludes `-∞` and asks for one finite value.

* Order reversal `legendre_antitone`; exclusion of `-∞` (`legendre_ne_bot`, and `legendre_ne_bot_iff`: exactly a nonempty
  effective domain); the Fenchel inequality `fenchel_le`, `biconjugate_le` and `triconjugate_eq`. No convexity of the
  primal is assumed.
* For every input, `lowerSemicontinuous_legendre` and `convex_epigraph_legendre`; `convexPotential_legendre` from a
  nonempty effective domain.
* The lower truncation `lowerTruncate φ M = max φ (-M)` of Cordero-Erausquin–Klartag, *Moment measures*
  (arXiv:1304.0630v1), (61), and its convexification `lowerTruncate_convexification` (proof of Proposition 12): the
  biconjugate is a convex, lower semicontinuous proper potential between `-M` and the truncation, with the same transform.
* `legendre_eq_interior_sup`: if `K` is open and convex with `0 ∈ K`, and `ψ` is radially closed and `⊤` off `closure K`,
  the transform is the supremum of its affine terms over `K` (proof of Lemma 17, (56b)).

Measure-free; the exponential density, mass and the CEK functional are in `Probability/MomentMeasure/`. Declaration blocks
are verbatim from the root-accepted Lemma 17 bundle (`independent-lemma17`, ACCEPTANCE ec6d356c…): lane A definitions
(6433a0f6…) and prerequisites (5ec2f621…), round 2 convexification (7df876d9…) and `legendre_eq_interior_sup` from
ConjugateMass (90a65ba7…).
-/
````

### `formalization/FunctionalInequalities/Analysis/Convex/LegendreVariation/Attainment.lean`

Original comment 82, line 8:

````lean
/-!
# Attainment of the Legendre supremum and the gradient of the conjugate

For a proper (`ProperPotential`) extended-real `φ` on a finite-dimensional real inner-product space (dimension zero
included) and a point `y` in the interior of the finite domain `{q | φ* q ≠ ⊤}` of its Legendre transform `φ*`:

* every maximizing affine term is the dual gradient: if `⟪z, y⟫ − φ z = φ* y` and `q ↦ (φ* q).toReal` is differentiable
  at `y`, then `z = ∇(φ*)(y)` (`conjugate_maximizer_eq_gradient`);
* the tilted primal grows linearly, `a‖z‖ − b ≤ φ z − ⟪z, y⟫` with `a > 0` (`exists_coercive_tilt_of_mem_interior_legendre_domain`),
  so `z ↦ ⟪z, y⟫ − φ z` has the data of `exists_finite_maximum_of_upperSemicontinuous_linear_decay` when `φ` is lower
  semicontinuous (`tiltedObjective_data`);
* hence the supremum is attained, and the maximizer is the dual gradient when the conjugate is differentiable
  (`exists_legendre_maximizer_with_gradient_identity`).

No convexity, differentiability, nonnegativity or global finiteness of `φ` is assumed. Pointwise prerequisites of
Cordero-Erausquin–Klartag, arXiv:1304.0630v1, (42) (Berman–Berndtsson, arXiv:1207.6128v1, Lemma 2.7 / Appendix 6); not the
integral first variation, the source moment map or its push-forward. Proof bodies: strong-API constructions (reviewed;
revalidated literal sources `MaximizerGradient`, `CoerciveTiltFixed`, `TiltedObjectiveFixed`, `ActualArgmax`), verbatim
up to the namespace of `conjugate_maximizer_eq_gradient` (formerly `KLSConstruction.API.FirstVariation`); placement: Claude.
-/
````

### `formalization/FunctionalInequalities/Analysis/Convex/LegendreVariation/Derivative.lean`

Original comment 83, line 6:

````lean
/-!
# The first variation of the Legendre transform

Let `φ` be proper and lower semicontinuous on a finite-dimensional real inner-product space (dimension zero included), let
`y` be interior to the finite domain of `φ*` and let `q ↦ (φ* q).toReal` be differentiable at `y`.

* Near-maximizers concentrate at the dual gradient: for every `ε > 0` there is `δ > 0` such that every `z` with
  `φ* y − δ ≤ ⟪z, y⟫ − φ z` satisfies `‖z − ∇(φ*)(y)‖ < ε` (`exists_delta_nearMaximizer_norm_sub_gradient_lt`).
* For every bounded continuous real `b`, `t ↦ (φ + t b)*(y)` is differentiable at `0` with derivative `−b(∇(φ*)(y))`
  (`hasDerivAt_legendre_add_smul_of_dualDifferentiable`); `φ` may take `⊤`.

No maximizing family, derivative formula, primal differentiability, global finiteness or nonnegativity is assumed. This is
the pointwise first variation behind Cordero-Erausquin–Klartag, arXiv:1304.0630v1, (42) (Berman–Berndtsson,
arXiv:1207.6128v1, Lemma 2.7 second point / Appendix 6); the integral first variation (Euler–Lagrange) for a source law, the
gradient push-forward, source regularity and CEK Theorem 2 are not provided. Proof bodies: strong-API constructions
(reviewed; revalidated literal sources `LegendreNearMaxFixed`, `LegendreVariationFixed`), verbatim; placement: Claude.
-/
````

### `formalization/FunctionalInequalities/Analysis/Convex/LegendreVariation/Perturbation.lean`

Original comment 84, line 3:

````lean
/-!
# Bounded perturbations of the Legendre transform

For a proper extended-real `φ`, a real perturbation `b` with `|b| ≤ M` and `t ∈ ℝ`, the actual extended-real Legendre
supremum moves by at most `|t| M` in both directions, `φ* q − |t|M ≤ (φ + t b)* q ≤ φ* q + |t|M`, with the whole `EReal`
supremum kept, infinite values included (`legendre_bounded_perturbation`); consequently, at a point where `φ*` is finite, the
perturbed conjugates form a finite real curve within `|t| M` of `φ* y` (`legendre_bounded_perturbation_finite_curve`). No
convexity or global finiteness of `φ` is assumed. Pointwise prerequisites of Cordero-Erausquin–Klartag, arXiv:1304.0630v1,
(42). Proof bodies: strong-API constructions (reviewed; revalidated literal sources `LegendreBoundedPerturbationFixed`,
`LegendreFiniteCurveFixed`), verbatim; placement: Claude.
-/
````

### `formalization/FunctionalInequalities/Analysis/Convex/PointwiseCompactness.lean`

Original comment 85, line 6:

````lean
/-!
# Pointwise compactness of bounded convex functions

A sequence of nonnegative real convex functions on an open set `K` of a finite-dimensional real normed space, bounded at
every point of `K`, has one strictly increasing subsequence converging at every point of `K`, and the limit is convex on
`K` (`exists_subseq_tendsto_of_convexOn_of_bddAbove`; `K = ∅` allowed). This is the case of Rockafellar, *Convex Analysis*,
Theorem 10.9, used in the proof of Cordero-Erausquin–Klartag, *Moment measures* (arXiv:1304.0630v1), Lemma 17.

Proof: the pointwise supremum is convex and finite on `K`, hence locally bounded, giving common local Lipschitz bounds; a
subsequence converges on a countable dense subset (one diagonal extraction over `ℕ` coordinates) and the convergence extends
to all of `K` by the Cauchy criterion; convexity passes to the limit. Four private helpers. Statement: Claude (frozen
fcb8f05d…); proof: Codex source specialization, root-accepted (CEK17-P1-ConvexSubseq-Raw-Root ACCEPTANCE 9d501183…).
-/
````

### `formalization/FunctionalInequalities/Analysis/Convex/RadialExtension.lean`

Original comment 86, line 8:

````lean
/-!
# Radial extension of a convex function

A nonnegative real convex function `g` on an open convex set `K ∋ 0` with `g 0 = 0` extends to `ψ : E → EReal` that is
nonnegative, vanishes at `0`, has convex real epigraph and Borel `toENNReal`, equals `g` on `K`, is `⊤` off `closure K`, and
equals at every point its radial limit `lim_{t → 1⁻} ψ (t • x)` (`exists_radial_extension_of_convexOn`). No boundedness,
lower semicontinuity, closure or envelope hypothesis is used; boundary values are radial limits (no claim either way about
equality with a lower-semicontinuous closure).

This is the extension step in the proof of Cordero-Erausquin–Klartag, *Moment measures* (arXiv:1304.0630v1), Lemma 17.
Construction (private): `ψ x = ⨆ n, radialCut (radialScale n) x` with `radialScale n = 1 − 1/(n + 2)`, the value at
`radialScale n • x` when that point lies in `K` and `⊤` otherwise; a countable supremum, hence Borel, and equal to the source's
monotone radial limit. Statement: Claude (frozen e2a7b7ed…); proof: Codex source specialization, root-accepted
(CEK17-R-Radial-Raw-Root ACCEPTANCE 3c339bcf…).
-/
````

### `formalization/FunctionalInequalities/Analysis/Convex/SupportingPlane.lean`

Original comment 88, line 6:

````lean
/-!
# Supporting affine plane at an interior point of the effective domain

For an extended-real potential with convex real epigraph, no value `-∞`, and `0` in the interior of its effective
domain, a supporting affine function touching at `0` is produced by Hahn–Banach separation
(`exists_supporting_affine_at_zero`); it is not supplied as a premise.

Declaration blocks are verbatim from the root-accepted CEK Proposition 12 bundle (`independent-p12-attainment`, ACCEPTANCE 848aa45b…) under the reviewed rev3 migration map.
-/
````

### `formalization/FunctionalInequalities/Analysis/Cutoff/Conservativity.lean`

Original comment 89, line 5:

````lean
/-!
# Conservativity from cutoffs with a vanishing defect

For a probability law `μ`, a bounded `f` of any sign, `c > 0` and `g` with `g + c f ≥ 0`, cutoffs `0 ≤ χ_n ≤ 1` with
`χ_n → 1` and defects `d_n ∈ L¹(μ)` with `∫ |d_n| dμ → 0` such that `∫ χ_n g = ∫ f d_n`, the function `g` is integrable and
`∫ g dμ = 0`: Fatou's lemma gives integrability of `g + c f`, then dominated convergence. Generic tool; the analytic core of
Letwin arXiv:2607.24164v1, Lemma A.5 (p. 18), with `g = Lf`, `d_n = Lχ_n`. Neither the integrability of `g` nor its zero
integral is assumed. Same generic cutoff role as `Analysis/CutoffIntegrability.lean` (Fatou integrability from bounded
cutoff integrals), but a separate module: it needs the dominated-convergence and probability-measure imports, under which
the existing `integrable_of_cutoff_bounds` would elaborate different instance terms; it does not import that module.
Proof body: independently accepted Astra (`round1.lean` b2c168a5…), verbatim; statement and placement: Root/Claude.
-/
````

### `formalization/FunctionalInequalities/Analysis/Cutoff/Integrability.lean`

Original comment 90, line 4:

````lean
/-!
# Integrability from uniformly bounded cutoff integrals

A nonnegative function whose cutoffs `c_n h` (with `0 ≤ c_n → 1` pointwise) have uniformly bounded
integrals is integrable, by Fatou's lemma. Generic tool, used to pass from compactly supported
integration by parts to global integrability (Letwin Lemma 2.3 supports). Proof body: root Codex
(bundle `Convex-Hessian-Moment`, independently accepted); statement and placement: Claude.
-/
````

### `formalization/FunctionalInequalities/Analysis/Cutoff/Profile.lean`

Original comment 92, line 5:

````lean
/-!
# Scalar cutoff profile for the noncompact integration by parts

Letwin arXiv:2607.24164v1, Lemma A.4 (p. 17), scalar part: the profile `η t = smoothTransition (2 − t)` with its
support and derivative bounds (`smoothTransition_two_sub_cutoff`), a smooth compactly supported majorant `w ≥ |η″|`
(`exists_majorant_abs_deriv_deriv_smoothTransition_two_sub`), and the monotone exhaustion `η(a/(n+1)) ↑ 1`
(`monotone_and_tendsto_smoothTransition_two_sub_div_succ`), and the tail primitive `q_R t = R⁻¹ ∫_{t/R}^3 w` of a
smooth nonnegative `w` vanishing off `(0, 3)` with `q_R′ t = −R⁻² w(t/R)`, `0 ≤ q_R ≤ R⁻¹ ∫_0^3 w` and `q_R = 0` on
`t ≥ 3R` (`inv_mul_intervalIntegral_div_three_cutoff`), and the affine rescaling
`(f((· − c)/R))′(t) = R⁻¹ f′((t − c)/R)`, `″ = (R⁻¹)² f″((t − c)/R)` for arbitrary `f`, `c`, `R`, `t`
(`deriv_comp_sub_div_and_deriv_deriv`; Lean total-derivative conventions, `R = 0` included), and the real-parameter
exhaustion: `R ↦ η(a/R)` is monotone on `(0, ∞)` and tends to `1` (`monotoneOn_and_tendsto_smoothTransition_two_sub_div`).
Generic real-variable tools; the cutoffs `η(W/R)` and the
quantitative generator defect of Lemma A.4 are not provided here. Proof bodies: Codex API jobs
`letwin-a4-scalar-profile-astra-high-v2` (156e2d03…), `letwin-a4-scalar-majorant-astra-high-takeover-v2` (2489dec3…),
`letwin-a4-scalar-monotone-astra-high-v1` (4bb28339…) and `letwin-a4-scalar-primitive-astra-high-takeover-v6`
(5f48742c…; exactly three compiler-reported unused tactics removed, 21912ed5…) and
`letwin-a4-scalar-rescaling-astra-high-goal-v1` (explicitly specialized shift lemma and two compiler-reported tactic
cleanups, 4f36afcd…) and `letwin-a4-real-exhaustion-astra-high-goal-v2` (obsolete guessed API names replaced by the exact
existing lemmas, b3b01128…), independently verified, verbatim;
statements and placement: Claude.
-/
````

### `formalization/FunctionalInequalities/Analysis/DiagonalSelector.lean`

Original comment 93, line 4:

````lean
/-!
# Diagonal selection in pseudometric spaces

Generic tool: from row limits `G n k → F n` (`k → ∞`) and an outer limit `F n → x`, choose indices
`k n ≥ n` with `G n (k n) → x`. Used for the joint Gaussian-then-quadratic regular approximation
(Bizeul–Klartag–Lehec arXiv:2610.05474v1, Section 2). Proof body: Codex q (bundle
`Gaussian-Quadratic-Diagonal`, independently accepted); statement and placement: Claude.
-/
````

### `formalization/FunctionalInequalities/Analysis/Extremum.lean`

Original comment 94, line 6:

````lean
/-!
# Finite maxima of upper semicontinuous extended-real functions

`exists_finite_maximum_of_upperSemicontinuous_linear_decay`: on a finite-dimensional real inner-product space (dimension zero
included), an upper semicontinuous `G : E → EReal` that never takes `⊤`, takes a finite value somewhere and satisfies a linear
decay `G x ≤ b − a‖x‖` with `a > 0` attains a finite global maximum. Values `⊥` elsewhere are allowed and no maximizing point
is supplied. A generic tool, used for the attainment of the Legendre supremum
(`Analysis/Convex/LegendreVariation/Attainment.lean`). Proof body: strong-API construction (reviewed; revalidated literal
source `USCAttainmentFixed`, b5cd3f64…), verbatim; placement: Claude.
-/
````

### `formalization/FunctionalInequalities/Analysis/Graph/OpenIntegral.lean`

Original comment 96, line 4:

````lean
/-! # Weighted graph area over an open parameter domain

Obligation `L8` of the weighted coarea route: the weighted change of variables
`setLIntegral_image_graphChartMap` of `Analysis/Graph/Integral.lean` requires the graph function to
be `C¹` on the **whole** parameter space.  Here it is localized to a function that is `C¹` only on
an open set `O`, for measurable parameter sets `S ⊆ O`.

A `ContDiffOn` function on an open set does **not** extend to a globally `C¹` function — `1 / x`
on `(0, ∞)` is the standard counterexample — so the localization is genuinely countable and cannot
be done by one global extension.  What is true, and is what `exists_contDiff_one_eqOn_ball` proves,
is that every point of `O` has a ball on which some globally `C¹` function agrees with the given
one: multiply by a `ContDiffBump` supported inside `O`.  This is the interior localization the route
prescribes; it is **not** the Whitney extension from a closed set, which is the separate unproved
obligation `L6`.

Second countability then extracts a countable subfamily of such balls covering `O`, `disjointed`
turns it into countably many pairwise disjoint measurable pieces of `S`, and the graph map is
injective (`graphMap_injective`), so the images of the pieces are disjoint and measurable.  Both
sides of the identity are countably additive over those pieces, and on each piece the global
theorem applies to the local extension; the gradients agree because the functions agree on an
**open** ball around each point (`Filter.EventuallyEq.gradient_eq`).

`Analysis/Sard/Smooth.lean` already contains the `C^∞` analogue `exists_contDiff_eventuallyEq`, with
an eventual equality rather than an explicit ball.  It is deliberately left untouched: generalizing
its order or strengthening its conclusion would change a published signature, so the `C¹` variant
needed here is proved separately.

No integrability, boundedness or finiteness hypothesis is used; the weight may be unbounded or
identically `∞`, `S` need not be bounded or of finite measure, and `O = ∅` or `S = ∅` are covered.
-/
````

Original comment 97, line 102:

````lean
/-- **Weighted graph area over an open parameter domain** (obligation `L8`).  The graph function is
`C¹` only on the open set `O`, and the parameter set is any measurable `S ⊆ O`.

No integrability of the weight, no boundedness or finite measure of `S`, and no global regularity
of `v` outside `O`; `O = ∅` and `S = ∅` are covered. -/
````

### `formalization/FunctionalInequalities/Analysis/Hausdorff/SurfaceSlicing.lean`

Original comment 98, line 5:

````lean
/-!
# Eilenberg slicing bound and compact-slice measurability in the normalized surface measure

Normalized wrapper of `Analysis.exists_measurable_majorant` and of
`Analysis.measurable_hausdorffMeasure_inter_levelSet` for the codimension-one
`KLS.surfaceMeasure` of `Analysis/Hausdorff/Measure.lean`. The measure and the conclusions are
unchanged: `surfaceMeasure V` stays `(ω_{n-1} / 2^{n-1}) • μH[n-1]` with the repository's
natural-subtraction convention, and the two statements are a genuine measurable majorant for the
slice function and a genuine almost-everywhere vanishing of the slice measure, not statements about
a substitute measure.

`exists_measurable_majorant` carries the explicit constant `eilenbergConstant V = 4 ω_{n-1} / ω_n`,
which is positive in every dimension (`eilenbergConstant_pos`); it is `2` in Mathlib's
diameter-gauge normalization, rescaled once for the fibre measure and once for the ambient measure.
Above dimension zero `Analysis.hausdorffMeasure_finrank_eq_smul_volume` turns the ambient
`μH[n] S` into `(2^n / ω_n) • volume S`, and `(n - 1 : ℕ) + 1 = n` in `ℝ` because `1 ≤ n`.  In
dimension zero the natural subtraction gives `surfaceMeasure V = hausdorffNormalized V 0`, the
space is a subsingleton, so `u` is constant on `S` and the one-point majorant of
`Analysis.exists_measurable_majorant_of_eqOn` applies with integral zero.  Dimension zero is
therefore not treated by declaring `ℋ⁰` to be the zero measure — it is the counting measure of a
one-point space — and no nondegeneracy of `V` is required.

`ae_surfaceMeasure_inter_levelSet_eq_zero` is the null case: a Lebesgue-null `S` makes the bound
vanish, and the majorant — unlike the slice function — is measurable, so `lintegral_eq_zero_iff`
applies.  `S` is not assumed measurable, bounded or nonempty, `u` is Lipschitz on `S` only, and
`K = 0` is allowed.  `CompleteSpace V` is not among the hypotheses because it is never used; a
caller that has it available applies the statements unchanged.

`measurable_surfaceMeasure_inter_levelSet` is the separate compact-slice statement: for `S`
**compact** and `u` merely continuous, the slice measure is a Borel measurable function of the
level.  It is not a consequence of the majorant bound — that bound says nothing about the slice
function's measurability — and it is proved in `Analysis/Hausdorff/Content.lean` through the
scalewise open-cover costs, whose scale limit is `μH[d]` and each of which is upper semicontinuous
in the level.  Only the positive normalizing scalar is added here, so no dimension split is
needed. The later declarations in this module prove the Borel-set bridge L4 and
measurable-weight version L5, with almost-everywhere measurability under a Lipschitz bound on
the set. `LevelSetMeasurable` exposes L5 at `S = Set.univ` under the original Analysis name.
-/
````

### `formalization/FunctionalInequalities/Analysis/IteratedDerivative/Bilinear.lean`

Original comment 99, line 5:

````lean
/-!
# Raw Leibniz expansion of a bilinear image of two `C^∞` maps

Generic calculus support for the spatial drift algebra of Bizeul–Klartag–Lehec arXiv:2610.05474v1,
p. 21, (72)–(74): for a continuous bilinear `B : F →L[ℝ] G →L[ℝ] H` and globally `C^∞` maps `f, g`
on a real normed space, the `m`-th raw iterated derivative of `y ↦ B (f y) (g y)` is the sum over
all Boolean subset indicators `q : Fin m → Bool` of `B (D^{|q|} f [h_q]) (D^{m−|q|} g [h_{¬q}])`, each
allocation with coefficient `1` and slots kept in their inherited increasing order (`selected`); no
factorial, Taylor normalisation or symmetry is involved. Proof bodies: Codex bundle
`Cumulant-Leibniz-Drift` with the reviewer's private linter-scope correction only (accepted owned
snapshot `Takeover-Cumulant-Drift-20261008`, source sha 49b27e53…); statements, namespace and
placement: Claude (frozen namespace `ReviewCumulantDrift` mapped to `FunctionalInequalities.Analysis`).
-/
````

Original comment 100, line 175:

````lean
/-- Boolean-mask partition facts for the actual ordered `selected` lists (BKL arXiv:2610.05474v1, (72)–(74),
singleton and middle allocations): lengths add up to `m`, the two selections together are a permutation of the
slots, an indicator of one slot selects exactly that slot, and a selection of length `1` comes from such an
indicator. Repeated slot values and `m = 0` are included. Proof body: independently accepted Astra v6
(`round1.lean` 788c3d48…), verbatim. -/
````

### `formalization/FunctionalInequalities/Analysis/IteratedDerivative/GradientJet.lean`

Original comment 101, line 5:

````lean
/-!
# Iterated derivatives of a shifted map and of a gradient

Generic calculus supports for the jets of the centred cumulant-generating-function gradient
(Bizeul–Klartag–Lehec arXiv:2610.05474v1, p. 20, the sentence before (74); consumer
`Analysis/BakryEmery/Cumulant/Local.lean` section `GradientJets`):

* `iteratedFDeriv_sub_const_of_pos`: for `r ≥ 1`, subtracting a constant does not change the `r`-th
  iterated derivative of a smooth map between real normed spaces (no inner product, dimension,
  completeness or measure assumption);
* `inner_iteratedFDeriv_gradient_apply`: on a complete real inner product space,
  `⟪Dʳ(∇f)(x)[h], w⟫ = Dʳ⁺¹f(x)[h, w]` with `w` in the last slot.

Proof bodies: Luna unit CGF1-J2a (round 8 with recorded Claude closing repairs: import, pointwise
subtraction lemma, definitional `exact`) and Luna unit CGF1-J2b (round 5), both independently accepted
2026-10-08; statements and placement: Claude.
-/
````

### `formalization/FunctionalInequalities/Analysis/IteratedDerivative/Log.lean`

Original comment 102, line 5:

````lean
/-!
# Iterated derivatives of `log ∘ f` at a normalized point

Generic calculus support (used for the polynomial growth of the derivatives of a smoothed
log-density, Bizeul–Klartag–Lehec arXiv:2610.05474v1, Section 2, p. 5): the raw derivatives of
`log` at `1` are `(-1)^n n!`, and for `f` smooth and positive near `x` with `f x = 1` and
`‖D^i f(x)‖ ≤ D^i`, the Faà di Bruno bound gives `‖D^n (log ∘ f)(x)‖ ≤ (n!)² D^n`. Raw iterated
Fréchet derivatives, not Taylor coefficients. Proof bodies: root Codex (bundle
`Log-Composition-Bounds`, independently accepted); statements and placement: Claude.
-/
````

### `formalization/FunctionalInequalities/Analysis/IteratedDerivative/Symmetry.lean`

Original comment 103, line 4:

````lean
/-!
# Permutation symmetry of raw iterated derivatives of real `C^∞` maps

Generic calculus support for the cumulant algebra of Bizeul–Klartag–Lehec arXiv:2610.05474v1,
pp. 20–21 ((71)–(74)): for a globally `C^∞` map between real normed spaces, successive directional
derivatives along a list (`directional`, inherited order) commute under adjacent swaps by genuine
real `C²` symmetry, hence under every permutation, and the list convention is exactly the raw
iterated Fréchet derivative, so `iteratedFDeriv ℝ m f x (h ∘ σ) = iteratedFDeriv ℝ m f x h`. No
analytic, finite-dimensional, complete, Hilbert or measure premise; no tensor symmetry is assumed.
Proof bodies: Codex bundle `Cumulant-Leibniz-Drift` (accepted owned snapshot
`Takeover-Cumulant-Drift-20261008`, source sha 39f3cea9…); statements, namespace and placement: Claude
(the frozen namespace `ReviewCumulantDrift` is mapped to `FunctionalInequalities.Analysis`, no alias).
-/
````

### `formalization/FunctionalInequalities/Analysis/Lipschitz/Annuli.lean`

Original comment 104, line 4:

````lean
/-! # The half-open annuli of a normed space

`X3` of the route recorded in
`research/decisions/2026-09-19-locally-lipschitz-vector-coarea-route.md`: the bookkeeping that
turns a *local* hypothesis into a countable sum.  The sets `k ≤ ‖x‖ < k + 1` are measurable,
pairwise disjoint, cover the space, and each of them sits inside the **open** ball of radius
`k + 1`, which is therefore a neighbourhood of each of its points — the last clause is what lets a
statement true near every point of the piece be used on the whole piece.

This is the codimension-`m` copy of the decomposition used by
`KLS/Geometry/Coarea/LocallyLipschitz.lean`, isolated here because the vector assembly needs the
same four facts.  Nothing about the dimension, the inner product or the measure is used: only the
norm, and for measurability the Borel structure.
-/
````

### `formalization/FunctionalInequalities/Analysis/Lipschitz/C1Pieces.lean`

Original comment 105, line 5:

````lean
/-! # Exact C¹ pieces of a Lipschitz function
L6a extracts compact jets; L6 extends each jet. Difference sets give a disjoint measurable
partition of a conull set. Both values and ambient derivatives are preserved pointwise. -/
````

Original comment 106, line 18:

````lean
/-- **L7**: exact C¹ representatives on countably many disjoint measurable pieces,
covering almost every point, with the original ambient derivative on each piece. -/
````

### `formalization/FunctionalInequalities/Analysis/Lipschitz/Extension.lean`

Original comment 110, line 4:

````lean
/-! # A Lipschitz extension into a finite-dimensional inner-product space

`X1` of the route recorded in
`research/decisions/2026-09-19-locally-lipschitz-vector-coarea-route.md`: a map into a
finite-dimensional real inner-product space that is Lipschitz on a set agrees on that set with a
map that is Lipschitz on the **whole** space.

**This is not Kirszbraun's theorem.**  Nothing whatever is claimed about the constant: it is
existentially quantified, and the construction below loses a factor `√m`.  The extension is the
componentwise McShane extension `LipschitzOnWith.extend_pi` on `Fin m → ℝ` with the sup norm,
transported to the target through the linear isometry `(stdOrthonormalBasis ℝ W).repr` onto
`EuclideanSpace ℝ (Fin m)` and the `PiLp` equivalences `WithLp.ofLp`, `WithLp.toLp`, whose Lipschitz
constants are `1` and `m ^ (1 / 2)`.  It is bookkeeping, not analysis, and it is all the locally
Lipschitz coarea route needs, because the globally Lipschitz formula it feeds only asks for *some*
constant.

The source is an arbitrary pseudometric space: no completeness, separability, boundedness or
nonemptiness of the set is used, and the zero-dimensional target is allowed.
-/
````

Original comment 111, line 31:

````lean
/-- **`X1`: a map Lipschitz on a set extends to a globally Lipschitz map into the same
finite-dimensional inner-product space.**  The Lipschitz constant of the extension is existentially
quantified and **no optimality is claimed**; this is the componentwise McShane extension, not
Kirszbraun's theorem. -/
````

### `formalization/FunctionalInequalities/Analysis/Lipschitz/Jet.lean`

Original comment 112, line 156:

````lean
/-- **L6a**: compact jets covering almost every point of a Lipschitz function.
The statement holds for every additive Haar measure on a finite-dimensional real normed space. -/
````

### `formalization/FunctionalInequalities/Analysis/Lipschitz/Local.lean`

Original comment 113, line 7:

````lean
/-! # From the globally Lipschitz coarea formula to the locally Lipschitz one

`X2`, `X4` and `X5` of the route recorded in
`research/decisions/2026-09-19-locally-lipschitz-vector-coarea-route.md`.

`X2` is the compactness step: a locally Lipschitz map on a finite-dimensional space is Lipschitz on
every closed ball.  `X4` is the locality step: two maps agreeing on an open set have the same
differential and the same level sets on any piece inside it.  `X5` is the assembly, and it is the
codimension-`m` transcription of the scalar argument of
`KLS/Geometry/Coarea/LocallyLipschitz.lean`, step for step: the annuli of
`Analysis/Lipschitz/Annuli.lean` cut the ambient set into countably many disjoint measurable
pieces, on the piece of index `n` the map is replaced by a **globally** Lipschitz extension
supplied by `Analysis/Lipschitz/Extension.lean`, the hypothesis is applied to that extension, `X4`
carries the coarea Jacobian and the level sets back to the original map, and countable additivity
sums the pieces.

`X5` is stated as an **implication**: the globally Lipschitz codimension-`m` coarea formula is not
proved here and is not assumed to hold; it is a hypothesis.  Nothing in this file proves a coarea
formula, and the relation `k + finrank ℝ W = finrank ℝ V` between the codimension and the
dimensions is never used — it belongs to the hypothesis, which carries its own.

No boundedness, finiteness, integrability, positive-dimension or critical-set hypothesis is added:
`S` is an arbitrary measurable set and the weight `g` may be identically infinite.
-/
````

Original comment 114, line 39:

````lean
/-- **`X2`: a locally Lipschitz map is Lipschitz on every closed ball.**  The closed balls of a
finite-dimensional normed space are compact, and a locally Lipschitz map is Lipschitz on a compact
set.  No relation between the constant and the radius is claimed. -/
````

Original comment 115, line 49:

````lean
/-- **`X4`: agreement on an open set transfers the differential and the level sets to any piece
inside it.**  The differential is a local notion, so `Filter.EventuallyEq.fderiv_eq` applies at each
point of the piece; the level sets agree by set extensionality.  No differentiability is assumed:
where neither map is differentiable both `fderiv`s are `0` and the identity still holds. -/
````

Original comment 116, line 71:

````lean
/-- **`X5`: the codimension-`m` coarea formula for globally Lipschitz maps implies the one for
locally Lipschitz maps.**  The hypothesis `hL` is the globally Lipschitz statement, which is **not**
proved here; the conclusion is the same statement with `LipschitzWith K u` weakened to
`LocallyLipschitz u`, so no global Lipschitz constant and no modulus of continuity survives.

The proof is the codimension-`m` copy of `KLS.coarea_of_locallyLipschitz`: half-open annuli, a
globally Lipschitz extension on each of them, locality of the differential and of the level sets,
and countable additivity.  The slice `AEMeasurable` conclusion is assembled by `AEMeasurable.tsum`
from the per-piece ones, because a locally Lipschitz map need not be Lipschitz on an unbounded
`S`. -/
````

Original comment 117, line 99:

````lean
-- Globally Lipschitz representatives of `u` on the closed balls: `X2` then `X1`.
````

Original comment 118, line 117:

````lean
-- `X4` on the open ball of radius `n + 1`, which contains the `n`-th piece.
````

Original comment 119, line 159:

````lean
/-- **`N0`: the codimension-`m` coarea formula for locally Lipschitz maps.**  `coarea_of_contDiff`
with `ContDiff ℝ 1 u` replaced by `LocallyLipschitz u`: no global Lipschitz constant, no `C¹`
regularity, no hypothesis on the critical set, no boundedness of `S`, no positivity of the
codimension.  It is `X5` applied to the proved globally Lipschitz formula `coarea_of_lipschitz`
(`L0`), and it is the common generalization of `L0` and of `coarea_of_contDiff`.  **It is not a
Sard theorem.** -/
````

### `formalization/FunctionalInequalities/Analysis/Lipschitz/VectorCoarea.lean`

Original comment 123, line 141:

````lean
/-- **`L0`: the codimension-`m` coarea formula for Lipschitz maps.**  Exactly
`coarea_of_contDiff` with `ContDiff ℝ 1 u` replaced by `LipschitzWith K u`; the density
`coareaJacobian (fderiv ℝ u x)` is unchanged, `fderiv` being junk on the Lebesgue-null set of
non-differentiability.

No hypothesis on the critical set, no finiteness, boundedness, integrability or regular-value
hypothesis, and no positivity of the codimension.  **It is not a Sard theorem.** -/
````

### `formalization/FunctionalInequalities/Analysis/Matrix/DeterminantDerivative.lean`

Original comment 125, line 9:

````lean
/-!
# Derivative of the determinant and of the log-determinant (Jacobi's formula)

The determinant of a real square matrix is a continuous multilinear map of its rows; its derivative
in a direction `N` is the sum of row replacements and, for invertible `M`, equals `det M · tr(M⁻¹ N)`.
Hence `D(log det)(M)[N] = tr(M⁻¹ N)`, also along a differentiable matrix-valued map. Proof bodies:
Codex route bundle `MA-Jacobi` (independently accepted); statements and placement: Claude.
-/
````

### `formalization/FunctionalInequalities/Analysis/Matrix/Integral.lean`

Original comment 126, line 4:

````lean
/-!
# Trace energies of symmetric matrix fields under a measure

Letwin, arXiv:2607.24164v1, Theorem 2.5, the extension step from positive semidefinite to all symmetric `B`, for a
measurable field `H : Ω → Matrix ι ι ℝ` of positive semidefinite matrices under an arbitrary measure `ν` on an arbitrary
measurable space, over every finite index type (the empty one included): if every positive semidefinite `A` has
`x ↦ tr(A H(x) A H(x))` integrable with `∫ tr(A H A H) dν ≤ C tr(A²)` for a real `C`, then every symmetric `B` has the
same (`symmetric_trace_integral_extension_mul`, a.e. form `symmetric_trace_integral_extension_mul_of_ae_posSemidef`; the
source coefficient `C = 2` is `symmetric_trace_integral_extension`). The integrability for `B` is derived (pointwise Jordan domination of
`Matrix/Sign.lean` and `Matrix/Trace/Energy.lean`); no finiteness of `ν`, nonemptiness or commutation is assumed. The positive
semidefinite bound is a named hypothesis: it is not constructed here, nor is the moment map, Brascamp–Lieb or Theorem
2.5 itself. Proof body: strong-API candidate (gpt-6-astra, `api-symmetric-client-patch-v9`, 1376c19e…), verbatim.
-/
````

### `formalization/FunctionalInequalities/Analysis/Matrix/Positivity.lean`

Original comment 129, line 9:

````lean
/-!
# Positive semidefinite Gram matrices with a Kronecker weight

`F (A ⊗ A) Fᵀ` is positive semidefinite for positive semidefinite `A`; written out, this is the
four-index Gram matrix used for the third-derivative term of Letwin's Lemma 2.4. Proof bodies: Codex
route bundle `MA-Second-Derivative` (independently accepted); statements and placement: Claude.

Quadratic floors and the Sylvester estimate: `matrixEntries A` is the Euclidean (Frobenius) view of the
entries; `QuadraticFloor S a` is `a‖v‖² ≤ ⟪v, S v⟫`; a positive definite matrix has a positive floor, a floor
is stable under Frobenius-small perturbations, and for floors `a`, `b` and symmetric `T` the identity
`S(S−T) + (S−T)T = S² − T²` (no commutation) gives `‖S − T‖_F ≤ ‖S² − T²‖_F / (a + b)`. Used for the local
Lipschitz property of the principal inverse square root (`Analysis/PrincipalInverseSqrt.lean`). Proof bodies:
Codex q_batch bundle `Principal-Root-Regularity` (independently accepted); statements and placement: Claude.

Inverse-quadratic Young inequality (`inverse_quadratic_young`): for a positive definite real matrix `H` over any finite
index type (the empty one included), `2 (v ⬝ᵥ w) ≤ v ⬝ᵥ H⁻¹ v + w ⬝ᵥ H w`, from the nonnegative quadratic form of
`w − H⁻¹ v`; no commutation or identity restriction. Support for Letwin, arXiv:2607.24164v1, Lemma A.6. Proof body:
strong-API candidate (gpt-6-astra, `api-finite-energy-bl-compiler-v6`, cadc3b6c…), verbatim; placement: Claude.

Trace pairings of positive semidefinite matrices (`sum_entry_mul_nonneg`, `trace_mul_nonneg`): for real positive
semidefinite `A`, `C` over any finite index type (the empty one included), `Σ_ij A_ij C_ij ≥ 0` (through the Kronecker
product) and `tr(AC) ≥ 0`; the product itself is not claimed positive semidefinite. Trace-weighted Gram matrices
(`traceGram_posSemidef`): for positive semidefinite `B` and symmetric `T a`, the matrix `(tr(B T_a B T_b))_{ab}` is positive
semidefinite. Supports for Letwin, arXiv:2607.24164v1, (2.10). Proof bodies: strong-API candidate (gpt-6-astra,
`api-trace-monge-ampere-210-v3`, de34b430…), verbatim, in the candidate's variable context; placement: Claude.
-/
````

### `formalization/FunctionalInequalities/Analysis/Matrix/Sign.lean`

Original comment 130, line 6:

````lean
/-!
# Absolute value and sign of a real symmetric matrix

For a real symmetric matrix `M`: `M * M ≥ 0`; `|M| = CFC.sqrt (M * M)` and `S = CFC.sqrt |M|` agree with the real
continuous functional calculus and are positive semidefinite (`symmetric_matrix_sqrt_real_cfc_bridge`); with
`sign M = cfc sign M`, `S * S = |M|`, `S * sign M * S = M`, and `sign M ^ 2 = 1` when `M` is a unit
(`symmetric_matrix_sign_factorization`). Singular and indefinite `M` are included. Support for the covariance step
of the proof of Letwin, arXiv:2607.24164v1, Theorem 1.2 (p. 14, preceding (2.21)). Proof bodies: root-accepted API scratch (`MatrixSqrtBridgeFixed` 0378ae4d…,
`MatrixSignFixed` d6c0d1bd…), verbatim, with exactly their accepted imports.
-/
````

Original comment 131, line 235:

````lean
/-! ### Jordan decomposition of a real symmetric matrix

For every real symmetric `B`, the continuous functional calculus parts `P = cfc (max · 0) B` and
`N = cfc (max (−·) 0) B` are positive semidefinite with `B = P − N`, `P N = N P = 0` and
`tr(B²) = tr(P²) + tr(N²)` (`symmetric_jordan_decomposition`; no decomposition is assumed, the empty index type
included); with the trace domination of `Matrix/Trace/Energy.lean` this gives `symmetric_jordan_trace_support`. Support for
Letwin, arXiv:2607.24164v1, Theorem 2.5; not the theorem itself. Proof bodies: strong-API candidate (gpt-6-astra,
`api-symmetric-compiler-patch-v3`, e735387e…), verbatim.
-/
````

### `formalization/FunctionalInequalities/Analysis/Matrix/Trace/Energy.lean`

Original comment 132, line 20:

````lean
/-! ### Positive spectral functions and trace energy of symmetric matrices

Support for Letwin, arXiv:2607.24164v1, Theorem 2.5 (the extension from positive semidefinite to all symmetric `B`):
a nonnegative real function of a symmetric matrix is positive semidefinite (`cfc_posSemidef_of_nonneg`, through the
orthonormal spectral representation `cfc_eq_mul_diagonal_mul`); for positive semidefinite `P`, `N` and symmetric `H`
the mixed trace `tr(P H N H)` is nonnegative (`trace_cross_nonneg`); a positive semidefinite weight makes the trace
energy `tr(B H B H)` of a symmetric `B` nonnegative (`trace_energy_nonneg`); and
`tr((P − N) H (P − N) H) ≤ tr(P H P H) + tr(N H N H)` without commutation (`jordan_trace_domination`). Arbitrary
finite index types, including the empty one. Not provided here: the measure extension, the moment map, Brascamp–Lieb
or Theorem 2.5 itself. Proof bodies: strong-API candidate (gpt-6-astra, `api-symmetric-compiler-patch-v3`, e735387e…),
verbatim; the two one-use helpers are private.
-/
````

### `formalization/FunctionalInequalities/Analysis/Matrix/TraceGram.lean`

Original comment 133, line 5:

````lean
/-!
# Trace-Gram coordinates for symmetric three-tensors

For a fully symmetric tensor `T` and a weight matrix `R`, the trace Gram matrix `(tr(R Tᵢ R Tⱼ))ᵢⱼ` is the
coordinate form of Letwin's tensor term. This module states Letwin arXiv:2607.24164v1 (2.12) in these coordinates
and derives the pointwise comparison `0 ≤ D`, `4 D ≤ g + 2 tr(B H B H)` used for the energy estimate (2.14).
All finite dimensions are included; `B` may be singular. Proof bodies: accepted Codex closed assemblies,
verbatim; the four-sum identity is a private one-use support.
-/
````

### `formalization/FunctionalInequalities/Analysis/Matrix/WeakDerivative.lean`

Original comment 134, line 6:

````lean
/-!
# Weak derivatives of finite matrix polynomials

Bounded weak matrix fields with compact-local L2 entry derivatives have exact
first directional derivatives of their determinants and trace quadratics.
Ambient and matrix dimensions may differ; zero dimensions and arbitrary real
constant matrices are retained. No C1/C2 regularity, symmetry, positivity or
invertibility of the rough field is assumed for these polynomial rules. The inverse-density identification additionally takes a locally essentially bounded inverse pair, its given local-L2 weak derivatives and the a.e. inverse identity; it proves the explicit inverse formula without classical differentiability. Supporting interfaces for Letwin
arXiv:2607.24164v1 Theorem 2.5 and compact Theorem 1.2, constant 8; these do not
establish Hessian evolution, an integrated trace estimate or the main bound.
Proof bodies: independently accepted W3p5/W3p6 API candidates, verbatim;
private finite matrix identities: previously checked client algebra, verbatim; the four-fold trace
product identity `trace_mul_mul_mul_eq_sum` lives in `Matrix/Trace/Algebra.lean`. `bounded_trace_quadratic_weak_derivative_data`
packages bounded trace data of `tr(B A B A)` for globally bounded rough fields.
-/
````

### `formalization/FunctionalInequalities/Analysis/Matrix/WeakTrace.lean`

Original comment 139, line 4:

````lean
/-!
# Weak trace contraction of rough matrix fields

Generic finite trace/integral algebra behind the weak trace identity of Letwin arXiv:2607.24164v1 (2.8)/(2.10):
a fixed-test finite integral contraction from given L1 coordinate pairings, local integrability of the contracted
coefficients from compact-local Lp entry data, and the full contracted identity
`integral_trace_quadratic_flux_eq_neg_density` for arbitrary rough fields `H`, `R`, `E`, `T`, `ρ`. No Hessian,
potential or source premise; all finite dimensions. Actual Hessian-evolution specializations live in
`KLS/CEK/MomentRegularity/TraceStein.lean`. Proof bodies: accepted Codex closed assemblies (independent A5a closed assembly,
local coefficient packet), verbatim up to reviewed helper names; one-use supports are private.
-/
````

### `formalization/FunctionalInequalities/Analysis/Mollification/Hessian.lean`

Original comment 141, line 4:

````lean
/-!
# Mollifying functions with Lipschitz gradient

Smooth approximation of a `C¹` function with Lipschitz gradient by normalized bump convolutions, with gradients
converging locally uniformly and Hessians converging almost everywhere (support for the weak Piola identity and the
weak Bochner formula on the moment-map route to Letwin arXiv:2607.24164v1). Proof body: GPT (Letwin sub-controller task
L-T8a); statement by the Letwin sub-controller; placement: Claude.
-/
````

### `formalization/FunctionalInequalities/Analysis/Operator/Coordinates.lean`

Original comment 142, line 9:

````lean
/-!
# Orthonormal coordinates of operators

Entries `⟪b i, M (b j)⟫` of a continuous linear operator in an orthonormal basis: products, triple
products, entries of derivatives, and the coordinate form of the inverse derivative; and the full matrix
`operatorMatrix b T = LinearMap.toMatrixOrthonormal b T` with its inverse `operatorOfMatrix`, positivity,
unit and inverse transfer (identified with the entries by `operatorMatrix_apply_eq_operatorEntry`), and the
continuous linear charts `operatorOfMatrixL`/`operatorMatrixL` between Euclidean matrix entries and operators
(finite-dimensional norm comparison; no identification of the Frobenius and operator norms). Proof bodies:
Codex route bundles `MA-Inverse`, `Principal-Inverse-SquareRoot` and `Principal-Root-Regularity` (independently
accepted); statements and placement: Claude.
-/
````

### `formalization/FunctionalInequalities/Analysis/Operator/InverseSqrt.lean`

Original comment 143, line 5:

````lean
/-!
# The principal inverse square root of a positive operator

For a positive invertible operator `A` on a finite-dimensional real inner product space, the principal
(positive) inverse square root `A^{-1/2}` is obtained from Mathlib's canonical matrix square root
`CFC.sqrt` of the inverse matrix in an orthonormal basis, pulled back to an operator. It is positive,
self-adjoint, satisfies `σ² = σσ* = Ring.inverse A` and `A σσ* = σσ* A = 1`, is a unit, strictly positive,
unique among positive operators with that square, and independent of the basis. Used for the diffusion
coefficient `A_t^{-1/2}` of the BKL localization (67) (`KLS/BKL/PosteriorDomain.lean`). At the pinned
Mathlib the real continuous functional calculus on `E →L[ℝ] E` itself is not available (no instance is
claimed). The root sandwiches the operator to the identity, `σ A σ = 1`, so it whitens the covariance; no
transported-law whitening API (image law with mean `0` and covariance `Id`) is claimed yet. Section `LocalLipschitz`: along a positive definite matrix profile the canonical
`CFC.sqrt` is locally Lipschitz (relative continuity of `CFC.sqrt` on the nonnegative cone, a local positive floor,
and the Sylvester estimate of `Matrix/Positivity`), and `inverseSqrt ∘ A` is locally Lipschitz whenever `Ring.inverse ∘ A`
is `C¹` with positive invertible values; nothing is claimed off the self-adjoint positive cone. Proof bodies: Codex
bkl bundle `Principal-Inverse-SquareRoot` and Codex q_batch bundle `Principal-Root-Regularity` (both independently
accepted); statements and placement: Claude.
-/
````

Original comment 144, line 129:

````lean
/-- **Root sandwich** `σ A σ = 1` for a positive unit `A` and `σ = inverseSqrt A`: from `A σσ = 1` and `σ` a unit,
`(σ A σ) σ = σ`, so `σ A σ = 1` (no commutation of `σ` with `A` is used). Proof body: Luna (`gpt-5.6-luna`, NB2
round 1); statement: Claude. -/
````

### `formalization/FunctionalInequalities/Analysis/Operator/Positive.lean`

Original comment 145, line 4:

````lean
/-!
# Strictly positive operators and their inverses

Generic facts about a continuous linear operator `T` on a real inner product space with
`⟪T v, v⟫ > 0` for `v ≠ 0`: it is a unit in finite dimension, has a two-sided inverse, any right inverse
of a self-adjoint positive `T` is self-adjoint and strictly positive, and any right inverse of a unit is
the canonical `Ring.inverse`. Used for the covariance of the BKL localization posterior. Proof bodies:
Codex bkl bundle `Posterior-Covariance-Domain` (independently accepted) and its Codex root reviewer
(`eq_ringInverse_of_comp_eq_id`); statements and placement: Claude.
-/
````

Original comment 146, line 80:

````lean
/-- Any right inverse of a unit equals the canonical `Ring.inverse` (Codex reviewer, independent root review
of the Posterior-Covariance-Domain bundle). -/
````

### `formalization/FunctionalInequalities/Analysis/RingInverseDerivative.lean`

Original comment 147, line 3:

````lean
/-!
# Derivative of the inverse of an operator-valued function

For `H : E → R` into a complete normed algebra with `H x` a unit, `y ↦ Ring.inverse (H y)` is
differentiable at `x` with derivative `v ↦ −H(x)⁻¹ (DH(x)[v]) H(x)⁻¹` (noncommutative order kept).
Used for the derivative of the inverse Hessian (Letwin (2.5)). Proof bodies: Codex route bundle
`MA-Inverse` (independently accepted); statements and placement: Claude.
-/
````

### `formalization/FunctionalInequalities/Analysis/Semigroup/Exponential/Contraction.lean`

Original comment 148, line 5:

````lean
/-!
# The exponential of a bounded nonnegative operator is a contraction

`S5` of the semigroup-generation route
(`research/decisions/2026-09-19-semigroup-generation-route.md`), proved here as
`norm_exp_neg_smul_apply_le` and restated verbatim as `route_S5`. See `Form.lean` for `S1`, `S2`
and `S4`, and `Resolvent.lean` for `S3`.

The route applies this to the Yosida approximation `L_s = (1 - J_s)/s`, a bounded nonnegative
self-adjoint operator, to see that `NormedSpace.exp (-t • L_s)` is a contraction for `t ≥ 0`.
Nothing here is specific to `L_s`: the statement is about an arbitrary bounded operator on a real
Hilbert space.

## Proof: monotonicity of the norm along the orbit

Write `u t = exp (t • (-L)) f`. Mathlib's `hasDerivAt_exp_smul_const'` gives `u' t = -L (u t)`, so
the product rule for the inner product (`HasDerivAt.inner`) gives
`(d/dt) ‖u t‖² = -2 ⟪L (u t), u t⟫ ≤ 0`. The function `t ↦ ‖u t‖²` is therefore antitone on all of
`ℝ` (`antitone_of_deriv_nonpos`), and evaluating at `0 ≤ t` against `u 0 = f` gives
`‖u t‖² ≤ ‖f‖²`. No spectral theory, no functional calculus and no operator-norm estimate is used;
the conclusion is pointwise in `f`, as the route states it.

## Route hypothesis not used

The route assumes `L` self-adjoint, `⟪L f, g⟫ = ⟪f, L g⟫`. The proof never uses it: the derivative
of `⟪u t, u t⟫` is `⟪u t, -L (u t)⟫ + ⟪-L (u t), u t⟫`, and both terms are `-⟪L (u t), u t⟫` by
symmetry of the **real inner product** alone (`real_inner_comm`). The module therefore proves the
stronger statement `norm_exp_neg_smul_apply_le` for every bounded nonnegative `L`, and `route_S5`
accepts and discards the self-adjointness hypothesis, exactly as `S2` discards `0 < s` and `S3`
discards density. The hypothesis `0 ≤ t` **is** used: for `t < 0` the orbit norm is larger, not
smaller, than `‖f‖`.

## Deliberately out of scope

`S6`–`S8` (strong convergence of the Yosida exponentials, the semigroup and strong-continuity
laws, the generator) are not proved here. This is one step of the abstract semigroup
construction; it is not the Markov property, not Bakry–Émery calculus, and not any step of
Buser's inequality. `thm:logconcave-cheeger-poincare-comparison` gains no progress marker from
this module.
-/
````

Original comment 149, line 90:

````lean
/-- **`S5`, strengthened.** If `L` is a bounded nonnegative operator on a real Hilbert space, then
`exp (-t • L)` is a contraction for every `t ≥ 0`, pointwise: `‖exp (-t • L) f‖ ≤ ‖f‖`.

The route's self-adjointness hypothesis is not needed and not assumed. -/
````

Original comment 150, line 103:

````lean
/-- **`S5` of the semigroup-generation route**, stated verbatim as in
`research/audits/SemigroupGenerationRouteStatements.lean` and discharged from
`norm_exp_neg_smul_apply_le`.

The route hypothesis `∀ f g, ⟪L f, g⟫ = ⟪f, L g⟫` (self-adjointness) is accepted here and **not
used**; the stronger unconditional statement is `norm_exp_neg_smul_apply_le`. -/
````

### `formalization/FunctionalInequalities/Analysis/Semigroup/Exponential/Counterexample.lean`

Original comment 151, line 20:

````lean
/-- The coefficient of the counterexample to the abstract `S6`: the indicator of `counterSet`,
i.e. `1` on `{1/(n+1) | n : ℕ}` and `0` elsewhere. -/
````

Original comment 152, line 39:

````lean
/-- The counterexample family is nonnegative, as the abstract `S6` demands. -/
````

Original comment 153, line 45:

````lean
/-- The counterexample family commutes, as the abstract `S6` demands: scalar multiples of the
identity always do. -/
````

Original comment 154, line 110:

````lean
/-- `Y0`: **the abstract `S6` is false**.  A family of nonnegative, pairwise commuting bounded
operators on `ℝ` need not have `exp (-t • L s) f` convergent as `s ↓ 0`.  Witness:
`counterFamily`, at `f = 1` and `t = 1`, whose values along `1/(n+1)` and along `2/(2n+3)` are the
distinct constants `Real.exp (-1)` and `1`. -/
````

### `formalization/FunctionalInequalities/Analysis/Semigroup/Exponential/Dissipation.lean`

Original comment 155, line 3:

````lean
/-!
# Energy dissipation along the orbit of a bounded symmetric operator

`Exponential/Contraction.lean` differentiates `u ↦ ‖exp (-u • L) y‖ ^ 2` once and concludes that
it is antitone (`S5`).  This module differentiates the same orbit **twice** and records the two
resulting quantitative estimates: for `L` bounded and symmetric, `u ≥ 0` and `v = exp (-u • L) y`,

* `two_mul_inner_exp_neg_smul_le`: `2 u ⟪L v, v⟫ ≤ ‖y‖ ² - ‖v‖ ²`;
* `two_mul_norm_apply_exp_neg_smul_sq_le`: `2 u ‖L v‖ ² ≤ ⟪L y, y⟫ - ⟪L v, v⟫`,
  which additionally needs `L` nonnegative.

Spectrally both are the elementary inequality `1 - exp (-x) ≥ x exp (-x)` for `x ≥ 0`, once at the
level of the norm and once at the level of the quadratic form.  The proofs use no spectral
calculus, no square root of `L` and no functional calculus: each estimate is the statement that an
explicit real function of `u` with value `0` at `u = 0` has nonnegative derivative
`4 u ‖L v‖ ²`, respectively `4 u ⟪L (L v), L v⟫`, on `[0, ∞)`.

## Why both levels are needed

Applied to the Yosida approximation `L_s` of `T†T` and passed to the limit `s ↓ 0`, the first
estimate gives `2 t ‖T (P_t f)‖ ² ≤ ‖f‖ ² - ‖P_t f‖ ²` and the second gives
`2 t ‖T†T (P_t f)‖ ² ≤ ‖T f‖ ² - ‖T (P_t f)‖ ²`.  Together with the density arguments of
`Generated/FormDomain.lean` those are exactly the positive-time regularity statements
`Generated/Smoothing.lean` proves for arbitrary `L²` data.

## Deliberately out of scope

Nothing here mentions a partially defined operator, an adjoint, the Yosida approximation, the
generated semigroup, the Markov property, Bakry–Émery calculus or Buser's inequality.  This is
bounded-operator material on a real Hilbert space: no measure, no log-concavity, no KLS quantity.
The sharp constants of the scalar maxima (`sup x exp (-x) = 1/e`) are **not** used or claimed.
-/
````

### `formalization/FunctionalInequalities/Analysis/Semigroup/Exponential/Limit.lean`

Original comment 156, line 4:

````lean
/-!
# Strong limits of exponentials of commuting nonnegative bounded operators

`Y6` and `Y7` of the Yosida-limit route
(`research/decisions/2026-09-19-yosida-limit-route.md`, statements in
`research/audits/YosidaLimitRouteStatements.lean`), proved here and restated verbatim as
`route_Y6` and `route_Y7`.

* `Y6` (`norm_exp_neg_smul_sub_le`) is the analytic core: for bounded **commuting** nonnegative
  operators `A, B` on a real Hilbert space and `t ≥ 0`,
  `‖exp (-t • A) f - exp (-t • B) f‖ ≤ t ‖A f - B f‖`, pointwise in `f`.
* `Y7` (`exists_limit_exp_neg_smul`) is the **corrected** abstract `S6`: a family `L s hs` of
  nonnegative commuting bounded operators whose values are Cauchy as `s ↓ 0` on a dense set has
  `exp (-t • L s hs) f` convergent as `s ↓ 0` for every `f` and every `t ≥ 0`. The Cauchy
  hypothesis on a dense set is what `S6` of
  `research/audits/SemigroupGenerationRouteStatements.lean` was missing; `Y0` of the route file
  records the counterexample to the uncorrected statement.

## Proof of `Y6`: differentiate the interpolation path

With `φ τ = exp (τ • (-A)) (exp ((τ - t) • B) f)` the product rule
(`HasDerivAt.clm_apply`, `hasDerivAt_exp_smul_const`) gives
`φ' τ = exp (τ • (-A)) ((-A) (exp ((τ - t) • B) f)) + exp (τ • (-A)) (exp ((τ - t) • B) (B f))`,
and `Commute.exp_right` moves `A` past `exp ((τ - t) • B)`, so
`φ' τ = exp (τ • (-A)) (exp ((τ - t) • B) (B f - A f))`. On `[0, t]` both exponentials are
contractions by `S5` (`norm_exp_neg_smul_apply_le`), so `‖φ' τ‖ ≤ ‖A f - B f‖`, and the mean value
inequality `norm_image_sub_le_of_norm_deriv_le_segment'` applied to `φ t - φ 0` is the claim. No
operator norm is ever estimated: everything is pointwise in `f`, which avoids the
`ContinuousLinearMap` norm instance diamond.

## Proof of `Y7`: Cauchy on a dense set, then everywhere

`exists_limit_of_cauchy_along_pos` is the completeness step, stated for an arbitrary family
`u : ∀ s : ℝ, 0 < s → H₀` in a complete normed group: an `ε`–`δ` Cauchy family as `s ↓ 0`
converges. It is proved by extracting the sequence `u (1 / (n + 1))`, which is `CauchySeq`, and
comparing an arbitrary small `s` with a far enough member of that sequence. `Y6` makes the family
`s ↦ exp (-t • L s hs) v` Cauchy for `v` in the dense set, and the contraction bound `S5` upgrades
this to every `f` by an `ε/3` argument through a nearby `v ∈ D`.

## Route hypotheses used, and the general form of the lemmas

Every hypothesis of `Y6` is used: nonnegativity of `A` and of `B` each supply one of the two
contraction estimates on `‖φ' τ‖`, commutation supplies the cancellation in `φ'`, and `0 ≤ t` is
needed both for the contraction estimates and for `[0, t]` to be the correct interval. `Y7` uses
all four of its hypotheses through `Y6` and `S5`. The module lemmas differ from the route
propositions only in binder shape (explicit `ε`, `s`, `r` instead of the route's implicit ones)
and in that `exists_limit_of_cauchy_along_pos` is stated for a bare complete normed group; the
verbatim route statements are `route_Y6` and `route_Y7`.

## Deliberately out of scope

`Y8` (`S6` for the actual Yosida approximation `L_s = s⁻¹ (1 - J_s)`) is **not** proved here: this
module mentions no unbounded operator `T`, no resolvent and no adjoint. `S7` (the semigroup and
strong-continuity laws of the limit) and `S8` (the generator is `T†T`) are not stated. Nothing
here is the Markov property, Bakry–Émery calculus, a heat kernel estimate or any step of Buser's
inequality; `thm:logconcave-cheeger-poincare-comparison` gains no progress marker from this
module.
-/
````

Original comment 157, line 75:

````lean
/-- Restatement of `S5` (`norm_exp_neg_smul_apply_le`) for a **nonpositive** scalar: if `L` is
bounded and nonnegative and `c ≤ 0`, then `exp (c • L)` is a pointwise contraction. -/
````

Original comment 158, line 82:

````lean
/-- Restatement of `S5` (`norm_exp_neg_smul_apply_le`) with the sign on the **operator**: if `L`
is bounded and nonnegative and `0 ≤ c`, then `exp (c • (-L))` is a pointwise contraction. This is
the normal form produced by `hasDerivAt_exp_smul_const` along the orbit of `-L`. -/
````

Original comment 161, line 203:

````lean
/-- **`Y7`, the corrected abstract `S6`.** Let `L s hs` be bounded, nonnegative and pairwise
commuting for `s > 0`, and suppose the values `L s hs v` are Cauchy as `s ↓ 0` for every `v` in a
dense set `D`. Then for every `f : H₀` and every `t ≥ 0` the family `exp (-t • L s hs) f`
converges as `s ↓ 0`.

`Y6` gives the Cauchy property of `exp (-t • L s hs) v` for `v ∈ D`, the contraction bound `S5`
transports it to every `f` by an `ε/3` argument, and `exists_limit_of_cauchy_along_pos` produces
the limit. -/
````

### `formalization/FunctionalInequalities/Analysis/Semigroup/Exponential/MeanValue.lean`

Original comment 165, line 5:

````lean
/-!
# A mean value bound for `exp (-t • A) f - f + t • A f`

`G2` of the generated-semigroup route
(`research/decisions/2026-09-19-generated-semigroup-route.md`, statements in
`research/audits/GeneratedSemigroupRouteStatements.lean`), proved here as
`norm_exp_neg_smul_sub_add_smul_le` and restated verbatim as `route_G2`.

For a bounded operator `A` on a complete normed space, a vector `f`, `0 ≤ t` and a real `C`: if
`‖exp (-τ • A) (A f) - A f‖ ≤ C` for every `τ ∈ [0, t]`, then

`‖exp (-t • A) f - f + t • A f‖ ≤ C * t`.

This is the quantitative statement that `exp (-t • A) f = f - t • A f + O(t)` with a constant
controlled by the motion of `A f` along the orbit; the route uses it with `A = L_s` the Yosida
approximation to identify the generator of the limit semigroup.

## Proof

The path `φ τ = exp (-τ • A) f - f + τ • A f` has `φ 0 = 0` and, by
`hasDerivAt_exp_smul_const` evaluated at the fixed vector `f` (`HasDerivAt.clm_apply` against
`hasDerivAt_const`) plus the derivative `A f` of `τ ↦ τ • A f`,

`φ' τ = -(exp (-τ • A) (A f)) + A f`,

recorded as `hasDerivAt_exp_neg_smul_path`. Its norm is `‖exp (-τ • A) (A f) - A f‖ ≤ C` on
`[0, t]`, so the mean value inequality
`norm_image_sub_le_of_norm_deriv_le_segment'` on `[0, t]`, evaluated at `t`, gives
`‖φ t - φ 0‖ ≤ C * (t - 0)`. Everything is pointwise in `f`: no operator norm of `A` or of an
exponential is ever estimated, which avoids the `ContinuousLinearMap` norm instance diamond.
Nonnegativity of `A` is not assumed and not needed, nor is `0 ≤ C`: for `t = 0` both sides
are `0`.

## Route hypotheses not used

The route states `G2` on a real Hilbert space, `[InnerProductSpace ℝ H₀] [CompleteSpace H₀]`. The
inner product plays no role — no symmetry, no nonnegativity, no Cauchy–Schwarz — so the module
lemmas are proved for an arbitrary `[NormedSpace ℝ H₀] [CompleteSpace H₀]`, and `route_G2`
accepts the `InnerProductSpace` instance and discards it. Completeness **is** used: it supplies
`CompleteSpace (H₀ →L[ℝ] H₀)`, the hypothesis under which `NormedSpace.exp` is differentiable.
The hypothesis `0 ≤ t` **is** used, so that `[0, t]` is the correct interval and `t` its right
endpoint. This follows the precedent of `S2`, `S3`, `S5` and `V1`, which likewise prove the
general statement and keep a verbatim wrapper.

## Deliberately out of scope

`G1` (uniformity on `[0, t]` of the `S6` convergence) and `G3`/`S8` (the generator of the limit
semigroup is `-T†T`) are **not** proved here; neither are `P1`–`P8` (`S7`). This module mentions
no unbounded operator `T`, no adjoint, no resolvent and no Yosida approximation: it is a
statement about a single bounded operator. Nothing here is the Markov property, Bakry–Émery
calculus, a small-time heat estimate, localization or any step of Buser's inequality;
`thm:logconcave-cheeger-poincare-comparison` gains no progress marker from this module.
-/
````

Original comment 166, line 67:

````lean
/-- The path `σ ↦ exp (-σ • A) f - f + σ • A f` used in `G2` is differentiable, with derivative
`-(exp (-τ • A) (A f)) + A f`.

This is `hasDerivAt_exp_smul_const` for the operator `-A`, evaluated at the fixed vector `f`,
plus the derivative `A f` of the linear term; the constant `-f` contributes nothing. -/
````

Original comment 167, line 95:

````lean
/-- **`G2`, for an arbitrary complete normed space.** Let `A` be a bounded operator, `f` a vector,
`0 ≤ t` and `C : ℝ`. If `‖exp (-τ • A) (A f) - A f‖ ≤ C` for every `τ ∈ [0, t]`, then

`‖exp (-t • A) f - f + t • A f‖ ≤ C * t`.

No nonnegativity, symmetry or inner product is needed, and `C` is not assumed nonnegative (for
`t = 0` both sides vanish). See the module docstring for the proof. -/
````

Original comment 168, line 122:

````lean
/-- **`G2` of the generated-semigroup route**, stated verbatim as in
`research/audits/GeneratedSemigroupRouteStatements.lean` and discharged from
`norm_exp_neg_smul_sub_add_smul_le`.

The route's `InnerProductSpace ℝ H₀` instance is accepted here and **not used**; the general
statement, for any complete normed space over `ℝ`, is `norm_exp_neg_smul_sub_add_smul_le`. -/
````

### `formalization/FunctionalInequalities/Analysis/Semigroup/Generated/Basic.lean`

Original comment 169, line 3:

````lean
/-!
# The semigroup generated by `T†T`: naming the limit

Definitions only. `S6` (`Analysis/Semigroup/Yosida/Limit.lean`, `exists_limit_exp_neg_smul_yosida`)
gives, for `T` closed and densely defined, every `t ≥ 0` and every `f`, *some* limit of
`exp (-t • L_s) f` as `s ↓ 0`, where `L_s = yosida T hT hs` is the Yosida approximation of `T†T`.
This module names that limit: `Generated.apply T hT hd t f` is the chosen limit for `t ≥ 0` and `f`
itself for `t < 0`. Formally it is `P_t f = exp (-t T†T) f`.

Everything about `P_t` beyond its defining convergence — linearity, contraction, symmetry, the
semigroup law `P_{t+u} = P_t P_u`, strong continuity (`S7`) and the generator identity
`(P_t f - f)/t → -T†T f` on `D(T†T)` (`S8`) — is **not** proved in this module. `S7` is
`Analysis/Semigroup/Generated/Laws.lean` and `S8` is `Analysis/Semigroup/Generated/Generator.lean`;
`research/audits/GeneratedSemigroupRouteStatements.lean` states the route obligations as they
stood at its snapshot and certifies nothing. Nothing here is the
Markov property, Bakry–Émery calculus, a heat estimate or any step of Buser's inequality.
-/
````

Original comment 170, line 30:

````lean
/-- `P_t f`: the strong limit of `exp (-t • L_s) f` as `s ↓ 0` for `t ≥ 0` (chosen from `S6`), and
`f` for `t < 0`. Formally `exp (-t T†T) f`. -/
````

### `formalization/FunctionalInequalities/Analysis/Semigroup/Generated/FormDomain.lean`

Original comment 171, line 5:

````lean
/-!
# Form-domain invariance and energy contraction for `P_t = exp (-t T†T)`

`Generated/Domain.lean` (`S0a`) keeps the **operator** domain `D(T†T)` invariant.  This module
extends the gradient interface to the whole **form** domain `D(T)`, for `T` closed and densely
defined between real Hilbert spaces:

* `norm_map_apply_le_of_generator` (`F0`): `‖T (P_t f)‖ ≤ ‖T f‖` for `f ∈ D(T†T)`, with
  `inner_adjointComp_apply_le` its Dirichlet-form phrasing `⟪T†T (P_t f), P_t f⟫ ≤ ⟪T†T f, f⟫`;
* `exists_seq_mem_adjointComp_domain_tendsto_graph` (`F1`): `D(T†T)` is dense in `D(T)` **for the
  graph norm of `T`** — every `f ∈ D(T)` is the limit of `f_n ∈ D(T†T)` with `T f_n → T f`;
* `preserves_form_domain` (`F2`): `P_t f ∈ D(T)` for every `f ∈ D(T)` and `t ≥ 0`;
* `norm_map_apply_le` (`F3`): `‖T (P_t f)‖ ≤ ‖T f‖` for every `f ∈ D(T)` and `t ≥ 0`.

`F2` and `F3` are delivered together by `exists_mem_domain_norm_map_apply_le`, because the
membership witness is what the norm even refers to.

## Proofs

`F0`.  `V1` turns the energy into the form: `‖T x‖ ² = ⟪T†T x, x⟫` for `x ∈ D(T†T)`
(`inner_adjointComp_self`).  With `S0a`'s invariance and commutation, symmetry `P4` and the
semigroup law `P6`,

`‖T (P_t f)‖ ² = ⟪T†T (P_t f), P_t f⟫ = ⟪P_t (T†T f), P_t f⟫ = ⟪T†T f, P_{2t} f⟫
  = ⟪T f, T (P_{2t} f)⟫ ≤ ‖T f‖ ‖T (P_{2t} f)‖`,

which is `norm_map_apply_sq_le_mul`: the energy at time `t` is controlled by the **doubled** time.
The `L²` contraction `P3` bounds all these energies at once by `‖T†T f‖ ‖f‖`
(`norm_map_apply_sq_le_mul_norm`), so `M = sup_{t ≥ 0} ‖T (P_t f)‖` is finite and satisfies
`M ² ≤ ‖T f‖ M`, i.e. `M ≤ ‖T f‖`.  No time derivative, no monotonicity theorem and no spectral
calculus is used, and the doubling step is applied to a supremum rather than iterated.

`F1`.  Take `f_n = J_{1/(n+1)} f`.  `V2` puts `J_s f` in `D(T†T)`, `R1` gives `f_n → f` in `H₀`,
and `exists_delta_norm_map_resolventDomain_sub_map_lt` of `Resolvent/Limit.lean` gives
`T f_n → T f` in `H₁`.  The second convergence is the substantive one; a uniform energy bound
would not suffice.

`F2`–`F3`.  For `f ∈ D(T)` take `f_n` from `F1`.  Then `P_t f_n ∈ D(T†T) ⊆ D(T)`, and `F0` applied
to the differences `f_n - f_m ∈ D(T†T)` gives
`‖T (P_t f_n) - T (P_t f_m)‖ ≤ ‖T f_n - T f_m‖`, so `T (P_t f_n)` is Cauchy and converges in `H₁`;
`P_t f_n → P_t f` because `P_t` is bounded.  **Closedness of `T`** identifies the limit, giving
`P_t f ∈ D(T)` and `T (P_t f) = lim T (P_t f_n)`, whose norm is at most `lim ‖T f_n‖ = ‖T f‖`
by `F0`.

## Deliberately out of scope

Nothing here regularizes an arbitrary `L²` datum: positive-time membership of `P_t g` in `D(T†T)`
for general `g`, a `C/t` generator bound, classical smooth representatives, preservation of
compactly supported smooth functions, pointwise gradient estimates, gradient commutation,
`Γ`/`Γ₂` estimates, their `L¹` self-improvement, BGL, small-time BV bounds, general-law passage
and Buser's inequality all remain open.  This is general real Hilbert space material: no measure,
no log-concavity and no KLS quantity.
-/
````

Original comment 172, line 82:

````lean
/-! ### `F0`: energy contraction on the generator domain -/
````

Original comment 173, line 84:

````lean
/-- The doubling estimate: for `f ∈ D(T†T)`, `t ≥ 0` and `u = 2t`,

`‖T (P_t f)‖ ² ≤ ‖T f‖ ‖T (P_u f)‖`.

`V1` (`inner_adjointComp_self`), the `S0a` commutation `generator_comm`, symmetry `P4` and the
semigroup law `P6`, closed by Cauchy–Schwarz.  The membership witnesses are hypotheses so that
`u` can be any expression equal to `t + t`. -/
````

Original comment 174, line 110:

````lean
/-- The energies along the orbit of `f ∈ D(T†T)` are bounded, uniformly in `t ≥ 0`:

`‖T (P_t f)‖ ² = ⟪P_t (T†T f), P_t f⟫ ≤ ‖T†T f‖ ‖f‖`,

using only the `S0a` commutation and the `L²` contraction `P3`. -/
````

Original comment 175, line 128:

````lean
/-- **`F0`: the semigroup contracts the energy on the generator domain.**  For `f ∈ D(T†T)` and
`t ≥ 0`, `‖T (P_t f)‖ ≤ ‖T f‖`.

The supremum `M` of `‖T (P_t f)‖` over all `t ≥ 0` is finite by
`norm_map_apply_sq_le_mul_norm`, and `norm_map_apply_sq_le_mul` gives `y ² ≤ ‖T f‖ M` for every
`y` in that family, hence `M ² ≤ ‖T f‖ M` and `M ≤ ‖T f‖`.  Time zero is allowed. -/
````

Original comment 176, line 176:

````lean
/-- **`F0`, Dirichlet-form phrasing.**  For `f ∈ D(T†T)` and `t ≥ 0`,
`⟪T†T (P_t f), P_t f⟫ ≤ ⟪T†T f, f⟫`. -/
````

Original comment 177, line 187:

````lean
/-! ### `F1`: `D(T†T)` is dense in `D(T)` for the graph norm -/
````

Original comment 178, line 190:

````lean
/-- **`F1`.**  Every `f ∈ D(T)` is approximated in the **graph norm** of `T` by elements of
`D(T†T)`: there is a sequence `u n ∈ D(T†T)` with `u n → f` in `H₀` **and** `T (u n) → T f`
in `H₁`.

The sequence is `u n = J_{1/(n+1)} f`.  Membership is `V2`
(`mem_adjointComp_domain_resolventDomain`), the `H₀` convergence is `R2`, and the `H₁`
convergence is `exists_delta_norm_map_resolventDomain_sub_map_lt`. -/
````

Original comment 179, line 216:

````lean
/-! ### `F2`–`F3`: form-domain invariance and energy contraction -/
````

Original comment 180, line 218:

````lean
/-- **`F2` and `F3` together.**  For every `f ∈ D(T)` and every `t ≥ 0` the semigroup value
`P_t f` lies in `D(T)`, and `‖T (P_t f)‖ ≤ ‖T f‖`.

The membership witness and the estimate are produced in one statement because the estimate
mentions the witness.  `preserves_form_domain` and `norm_map_apply_le` are the two halves. -/
````

Original comment 181, line 271:

````lean
/-- **`F2`: the form domain is invariant.**  For `f ∈ D(T)` and `t ≥ 0`, `P_t f ∈ D(T)`.  Time
zero and the zero vector are allowed, and the datum is only assumed to be in the form domain. -/
````

Original comment 182, line 278:

````lean
/-- **`F3`: the semigroup contracts the energy on the whole form domain.**  For `f ∈ D(T)`,
`t ≥ 0` and any witness of `P_t f ∈ D(T)`, `‖T (P_t f)‖ ≤ ‖T f‖`.  The gradient is `T` in the
closed-operator sense; no classical representative is claimed. -/
````

### `formalization/FunctionalInequalities/Analysis/Semigroup/Generated/Generator.lean`

Original comment 183, line 48:

````lean
/-- **`G1` on `D(T†T)`.** For `b ∈ D(T†T)`, `0 ≤ t` and `ε > 0` there is `δ > 0` such that for
every `0 < s < δ` **and every `τ ∈ [0, t]` simultaneously**

`‖exp (-τ • L_s) b - P_τ b‖ ≤ ε`.

The point is the uniformity in `τ`: the `S6` convergence `Generated.yosida_limit` is a pointwise
statement at a fixed time, whereas the bound here has a single `δ` for the whole interval.

Proof: `Y6` bounds `‖exp (-τ • L_s) b - exp (-τ • L_r) b‖` by `τ ‖L_s b - L_r b‖ ≤ t ‖L_s b - L_r b‖`,
and `Y5` makes `‖L_s b - T†T b‖ < ε / (2 (t + 1))` for `s < δ`; letting `r ↓ 0` at the fixed `τ`
through `Generated.yosida_limit` and squeezing removes the auxiliary parameter. -/
````

Original comment 184, line 108:

````lean
/-- **`G1`.** For every `g : H₀`, every `0 ≤ t` and every `ε > 0` there is `δ > 0` such that for
all `0 < s < δ` and **all** `τ ∈ [0, t]`

`‖exp (-τ • L_s) g - P_τ g‖ < ε`,

i.e. the `S6` convergence of `Generated.yosida_limit` is uniform on compact time intervals.

Proof: approximate `g` within `ε/3` by `b ∈ D(T†T)` (`dense_adjointComp_domain`), apply
`Generated.yosida_error_le` to `b` with `ε/3`, and absorb the two
approximation errors with the contraction bounds `S5` (`norm_exp_neg_smul_apply_le`) and `P3`
(`Generated.norm_apply_le`). -/
````

Original comment 185, line 147:

````lean
/-- **The quantitative form of `S8`.** For `f ∈ D(T†T)` and `ε > 0` there is `δ > 0` with

`‖P_t f - f + t • T†T f‖ ≤ (7 ε / 8) * t` for every `0 < t < δ`,

i.e. `P_t f = f - t • T†T f + o(t)` as `t ↓ 0`, with an explicit modulus.

Proof: `G2` applied to `A = L_s` needs `‖exp (-τ • L_s) (L_s f) - L_s f‖` bounded on all of
`[0, t]`, which is exactly what `G1` (uniformity in `τ`), `Y5` and `P7` supply; then `s ↓ 0` at
the fixed `t` through `Generated.yosida_limit`, squeezed by `le_of_forall_pos_add_le`. -/
````

Original comment 186, line 182:

````lean
-- The hypothesis of `G2`, uniformly on `[0, t]`.
````

Original comment 187, line 232:

````lean
/-- **`G3` = `S8`: the generator of `P_t` is `-T†T` on `D(T†T)`.** For `f ∈ D(T†T)` and `ε > 0`
there is `δ > 0` with

`‖t⁻¹ • (P_t f - f) + T†T f‖ < ε` for every `0 < t < δ`,

that is, `(P_t f - f)/t → -T†T f` as `t ↓ 0`.

Immediate from the quantitative form `Generated.generator_error_le` after dividing by
`t > 0`. -/
````

### `formalization/FunctionalInequalities/Analysis/Semigroup/Generated/Laws.lean`

Original comment 191, line 107:

````lean
/-- **`P3`**: `P_t` is a contraction, `‖P_t f‖ ≤ ‖f‖`.  `S5` (`norm_exp_neg_smul_apply_le` applied
to the nonnegative operator `L_s`) passes to the limit. -/
````

Original comment 196, line 190:

````lean
/-- `P_t` packaged as a `ContinuousLinearMap` of operator norm at most `1`, using `P2` and `P3`.
`Generated.operator_apply` identifies it with `Generated.apply`. -/
````

Original comment 198, line 228:

````lean
/-- **`P4`**: `P_t` is symmetric, `⟪P_t f, g⟫ = ⟪f, P_t g⟫`.  Each `exp (-t • L_s)` is symmetric,
and the defect `⟪P_t f, g⟫ - ⟪f, P_t g⟫` is bounded by `ε * (‖g‖ + ‖f‖)` for every `ε > 0`. -/
````

Original comment 200, line 283:

````lean
/-- **`P6`**: the semigroup law `P_{t + u} = P_t ∘ P_u`.  `exp (-(t+u) • L_s)` factors as
`exp (-t • L_s) ∘ exp (-u • L_s)` (`exp_neg_add_smul_apply`); the error splits as
`‖exp (-u • L_s) f - P_u f‖` (after the contraction `S5`) plus
`‖exp (-t • L_s) (P_u f) - P_t (P_u f)‖`, and `P1` identifies the limit. -/
````

Original comment 202, line 359:

````lean
/-- **`P7`**: strong continuity at `0`.  For `f ∈ D(T†T)` this is
`Generated.displacement_le`; a general `f` is approximated within `ε/3` by some
`g ∈ D(T†T)` (`dense_adjointComp_domain`), and the contraction `P3` together with linearity
transfers the bound. -/
````

Original comment 203, line 396:

````lean
/-- **`P8`**: `t ↦ P_t f` is continuous on `[0, ∞)`.  For `t₀ ≤ t` the semigroup law gives
`P_t f - P_{t₀} f = P_{t₀} (P_{t - t₀} f - f)`, which the contraction `P3` bounds by
`‖P_{t - t₀} f - f‖`; for `t ≤ t₀` exchange the roles.  Then apply `P7`. -/
````

### `formalization/FunctionalInequalities/Analysis/Semigroup/Generated/Smoothing.lean`

Original comment 204, line 4:

````lean
/-!
# Positive-time smoothing for `P_t = exp (-t T†T)`

`Generated/Domain.lean` (`S0a`) and `Generated/FormDomain.lean` (`F0`–`F4`) both start from a
datum that already lies in `D(T†T)` or `D(T)`. This module removes that assumption: for `T` closed
and densely defined and **every** `g : H₀`,

* `mem_domain_apply_of_pos` / `two_mul_norm_map_apply_sq_le`: `t > 0` implies `P_t g ∈ D(T)` and
  `2 t ‖T (P_t g)‖ ² ≤ ‖g‖ ²`;
* `mem_adjointComp_domain_apply_of_pos` / `mul_norm_adjointComp_apply_le`: `t > 0` implies
  `P_t g ∈ D(T†T)` and `t ‖T†T (P_t g)‖ ≤ ‖g‖`.
* `pow_three_mul_norm_map_adjointComp_apply_sq_le`: `t³ ‖T (T†T (P_t g))‖² ≤ 4 ‖g‖²`;
* `tendsto_map_apply_of_pos` / `tendsto_map_adjointComp_apply_of_pos`: both fields converge
  under convergence of the initial data, at each fixed strictly positive time.

These are the two statements that the audits of the previous two rounds carried as
**type-checked candidates only**; they are now proved. The constants are the ones the proof
produces: `‖T (P_t g)‖ ≤ ‖g‖ / √(2t)` and `‖T†T (P_t g)‖ ≤ ‖g‖ / t`. The sharp scalar maxima
`sup_{λ ≥ 0} λ exp (-2tλ) = 1/(2et)` and `sup_{λ ≥ 0} λ ² exp (-2tλ) = 1/(et) ²` are **not**
claimed, so the sharp constants `1/√(2et)` and `1/(et)` remain unproved.

## Proofs

**On `D(T†T)` the estimates come from the bounded level.** `Exponential/Dissipation.lean` proves,
for a bounded symmetric `L` and `u ≥ 0` with `v = exp (-u • L) y`,
`2 u ⟪L v, v⟫ ≤ ‖y‖ ² - ‖v‖ ²` and (for `L ≥ 0`) `2 u ‖L v‖ ² ≤ ⟪L y, y⟫ - ⟪L v, v⟫`. Applied to
the Yosida approximation `L_s` and passed to the limit `s ↓ 0` along any positive null sequence,
using `L_s (exp (-t • L_s) f) = exp (-t • L_s) (L_s f)`, `Y5` and `S6`, they become

`2 t ‖T (P_t f)‖ ² ≤ ‖f‖ ² - ‖P_t f‖ ²` and `2 t ‖T†T (P_t f)‖ ² ≤ ‖T f‖ ² - ‖T (P_t f)‖ ²`

for `f ∈ D(T†T)` (`two_mul_norm_map_apply_sq_le_sub`, `two_mul_norm_adjointComp_apply_sq_le_sub`),
after rewriting `⟪T†T (P_t f), P_t f⟫ = ‖T (P_t f)‖ ²` with `V1` and `T†T (P_t f) = P_t (T†T f)`
with `S0a`.

**Off the domain the estimates are transported by density.** Each estimate is applied to
differences, which turns it into a Cauchy estimate: from `g_n → g` with `g_n ∈ D(T†T)` the
sequence `T (P_t g_n)` is Cauchy because `2 t ‖T (P_t (g_n - g_m))‖ ² ≤ ‖g_n - g_m‖ ²`, and
`exists_mem_domain_apply_eq_of_tendsto` (closedness of `T`) identifies the limit. The same
argument with `F1`'s graph-norm approximation and closedness of `T†T` (self-adjoint, so closed)
upgrades the second estimate to every `f ∈ D(T)`
(`mem_adjointComp_domain_apply_of_mem_domain`). Composing the two through
`P_t = P_{t/2} P_{t/2}` gives the operator-domain statement for arbitrary data.

## Deliberately out of scope

A **classical** or smooth representative of `P_t g`, pointwise gradient bounds, gradient
commutation, `Γ`/`Γ₂` estimates for the semigroup and their `L¹` self-improvement, BGL, small-time
BV bounds, general-law passage and Buser's inequality are all still open. The generator image
is in `D(T)` with the bound above, but no smooth operator-core statement is proved. This is
general real Hilbert space material: no measure, no log-concavity and no KLS quantity.
-/
````

Original comment 205, line 76:

````lean
/-- `S6` along a sequence: `exp (-t • L_{s n}) g → P_t g` for any positive null sequence `s`. -/
````

Original comment 207, line 104:

````lean
/-- The mixed limit `L_{s n} (exp (-t • L_{s n}) f) → P_t (T†T f)` for `f ∈ D(T†T)`.

`L_s` commutes with its own exponential (`exp_neg_smul_apply_comm`), so the sequence equals
`exp (-t • L_{s n}) (L_{s n} f)`; the contraction property absorbs `L_{s n} f - T†T f` and `S6`
handles the remaining `exp (-t • L_{s n}) (T†T f) - P_t (T†T f)`. -/
````

Original comment 208, line 145:

````lean
/-- **Norm-level dissipation.** For `f ∈ D(T†T)` and `t ≥ 0`,

`2 t ‖T (P_t f)‖ ² ≤ ‖f‖ ² - ‖P_t f‖ ²`.

`two_mul_inner_exp_neg_smul_le` for the Yosida approximation, passed to the limit along
`s n = 1 / (n + 1)`; the left-hand side is `2 t ⟪T†T (P_t f), P_t f⟫` by `V1` and `S0a`. -/
````

Original comment 210, line 315:

````lean
/-- **Form-domain data enter the generator domain at positive times**, with the estimate
`2 t ‖T†T (P_t f)‖ ² ≤ ‖T f‖ ²`.

Same transport one level up: `F1` supplies `u n ∈ D(T†T)` with `u n → f` **and** `T (u n) → T f`,
`two_mul_norm_adjointComp_apply_sq_le_sub` applied to differences makes `T†T (P_t (u n))` Cauchy,
and `T†T` is self-adjoint, hence closed, so it absorbs the limit. -/
````

Original comment 211, line 399:

````lean
/-- **Positive-time smoothing into the generator domain.**  For every `g : H₀` and `t > 0`,
`P_t g ∈ D(T†T)`.  This is the statement `S0a` carried as a type-checked candidate. -/
````

Original comment 212, line 415:

````lean
/-- **Second-order positive-time regularity.**  For every `g : H₀` and every `t > 0`, the
generator image `T†T (P_t g)` again lies in the **form** domain `D(T)`.

Split the time, `P_t = P_{t/2} P_{t/2}`.  The inner half puts `g` in `D(T†T)` (`E4`), so
commutation gives `T†T (P_t g) = P_{t/2} (T†T (P_{t/2} g))`, and the outer half sends that
`H₀`-vector into `D(T)` (`E2`).  Nothing beyond `E2`, `E4` and `S0a`'s commutation is used; in
particular no classical representative and no second application of the adjoint. -/
````

### `formalization/FunctionalInequalities/Analysis/Semigroup/Resolvent/Basic.lean`

Original comment 213, line 4:

````lean
/-!
# The resolvent: unique solvability of the weak equation

`S3` of the semigroup-generation route
(`research/decisions/2026-09-19-semigroup-generation-route.md`), proved here as
`existsUnique_weakResolvent`. See `Resolvent/Form.lean` for `S1`, `S2` and `S4`.

The proof uses **orthogonal projection, not Lax–Milgram**. Rescaling the second coordinate by
`√s` turns the shifted form into the ambient inner product of `WithLp 2 (H₀ × H₁)`: for
`g = (u, √s • T u)` and `h = (v, √s • T v)`,
`⟪g, h⟫ = ⟪u, v⟫ + s ⟪T u, T v⟫`, while the datum becomes `⟪f, v⟫ = ⟪(f, 0), h⟫`. A solution is
therefore exactly the orthogonal projection of `(f, 0)` onto the rescaled graph, which is closed
because `T` is. No coercive bilinear form, no `IsCoercive` and no Riesz representation is needed.

Two hypotheses of the route statement turn out to be unnecessary and are **not** assumed by the
theorems here: uniqueness needs neither closedness nor density, and existence needs closedness but
**not density** — density matters only if one wants to identify the solution as `(1 + s T*T)⁻¹ f`
through the adjoint, which this module does not do.

`S5`–`S8` are not proved here.
-/
````

Original comment 214, line 38:

````lean
/-- `S3`, uniqueness half: the weak resolvent equation has at most one solution.

The difference of two solutions is tested against itself, giving `‖w‖² + s ‖T w‖² = 0`; strict
positivity of `s` is not even needed for the norm to vanish, but it is kept to match the route.
No closedness, density or Lax–Milgram input is used. -/
````

Original comment 215, line 89:

````lean
/-- `S3`'s ambient space: the transported graph of a closed operator is a Hilbert space.

This is the space on which the shifted form of `S2` is coercive, so it is exactly the input
Lax–Milgram needs. The existence half of `S3` is still open. -/
````

Original comment 216, line 150:

````lean
/-- `S3`, existence half: the weak resolvent equation has a solution.

The solution is the orthogonal projection of `(f, 0)` onto the rescaled graph; density of the
domain is **not** needed, only closedness. -/
````

Original comment 217, line 172:

````lean
/-- `S3`: the weak resolvent equation is uniquely solvable for every datum. -/
````

Original comment 218, line 178:

````lean
/-! ## The resolvent as a bounded operator

`S3` gives unique solvability, so the solution map is a well-defined function; linearity follows
from uniqueness, the norm bound from `S4`, and self-adjointness from symmetry of the form. This is
the operator `J_s = (1 + s T*T)⁻¹` that the Yosida approximation of `S5`–`S8` is built from.
-/
````

### `formalization/FunctionalInequalities/Analysis/Semigroup/Resolvent/Form.lean`

Original comment 219, line 4:

````lean
/-!
# The form domain of a closed operator, and the weak resolvent equation

First three obligations of the semigroup-generation route
(`research/decisions/2026-09-19-semigroup-generation-route.md`), which is gap 1 of the five
recorded for `thm:logconcave-cheeger-poincare-comparison`.

For a densely defined operator `T : H₀ →ₗ.[ℝ] H₁` the energy form is `E(u) = ‖T u‖²`, unbounded on
`H₀` but bounded on the form domain `D(T)` in the graph norm. This module supplies the three
statements that make the Lax–Milgram construction of the resolvent applicable:

* `completeSpace_graph` (`S1`): the graph of a closed operator is complete, which is the
  completeness the form domain needs;
* `min_one_mul_graphNormSq_le` (`S2`): the shifted form `⟪u, v⟫ + s ⟪T u, T v⟫` is coercive in the
  graph norm, with explicit constant `min 1 s`;
* `norm_le_of_weak_resolvent` and `inner_nonneg_of_weak_resolvent` (`S4`): any solution of the weak
  resolvent equation is a contraction of the datum and pairs nonnegatively with it.

Nothing here constructs the resolvent, the Yosida approximation or the semigroup; those are `S3`,
`S5`–`S8` of the route and are not proved. This module is general real Hilbert space material: it
mentions no measure, no log-concavity and no KLS quantity.
-/
````

Original comment 220, line 38:

````lean
/-- `S1`: the graph of a closed operator is a complete space.

`LinearPMap.IsClosed` is by definition closedness of the graph as a set, so this is the closed
subspace of the complete product `H₀ × H₁`. It is the completeness that makes the form domain
`D(T)`, carrying the inner product `⟪u, v⟫ + ⟪T u, T v⟫`, a Hilbert space. -/
````

Original comment 221, line 47:

````lean
/-- `S2`: coercivity of the shifted form in the graph norm.

The quadratic form `u ↦ ‖u‖² + s ‖T u‖²` dominates `min 1 s` times the squared graph norm. This is
the coercivity hypothesis that `IsCoercive` asks for, with an explicit constant.

The route stated this for `s > 0`, but positivity is not needed and is therefore not assumed: for
`s ≤ 1` the claim reduces to `(s - 1) ‖u‖² ≤ 0` and for `s > 1` to `‖T u‖² ≤ s ‖T u‖²`. Neither
closedness nor density is used either. -/
````

Original comment 222, line 80:

````lean
/-- `S4`, first half: a solution of the weak resolvent equation is a contraction of its datum,
so the resolvent is norm-nonexpansive. Test against `u` and apply Cauchy–Schwarz. -/
````

Original comment 223, line 94:

````lean
/-- `S4`, second half: a solution pairs nonnegatively with its datum, so the resolvent is a
nonnegative operator. The pairing equals the squared graph norm. -/
````

### `formalization/FunctionalInequalities/Analysis/Semigroup/Resolvent/Limit.lean`

Original comment 224, line 3:

````lean
/-!
# Resolvent limits: `J_s → 1` as `s ↓ 0`, and commutation

Part B (`R1`–`R3`) of the von Neumann route recorded in
`research/decisions/2026-09-19-von-neumann-route.md`, restated in
`research/audits/VonNeumannRouteStatements.lean`:

* `R1`, `norm_resolventCLM_sub_sq_le`: for `f ∈ D(T)`, `‖J_s f - f‖ ^ 2 ≤ s * ‖T f‖ ^ 2`;
* `R2`, `exists_delta_norm_resolventCLM_sub_lt`: `J_s → 1` strongly as `s ↓ 0`, in `ε`–`δ` form
  (`resolventCLM` carries the proof `0 < s` as an argument, so this is how the route states it);
* `R3`, `resolventCLM_comp_comm`: the resolvents commute, `J_s J_r = J_r J_s`.

The same module also proves the **graph-norm** convergence that the Bakry–Émery form-domain stage
needs and that `R1`–`R3` do not give: for `f ∈ D(T)`, `T (J_s f) → T f` in `H₁`
(`exists_delta_norm_map_resolventDomain_sub_map_lt`), together with the two-parameter energy
identity `resolventDomain_energy_identity` behind it, antitonicity of `s ↦ ‖T (J_s f)‖ ^ 2`
(`norm_map_resolventDomain_sq_le_of_le`), its Cauchy consequence
(`norm_map_resolventDomain_sub_sq_le_sub`), the energy contraction
`‖T (J_s f)‖ ≤ ‖T f‖` (`norm_map_resolventDomain_le`) and the defect bound
`norm_map_resolventDomain_sub_map_sq_le`.  See the section below.

Everything is proved from the **weak equation** `WeakResolvent T s f u` of `Resolvent/Form.lean`
and the unique solvability of `Resolvent/Basic.lean`.  In particular:

**The adjoint never appears.**  No declaration here refers to `LinearPMap.adjoint`, to
`adjointComp` or to `adjointCompDomain`; the module does not import
`FunctionalInequalities.Analysis.Semigroup.AdjointComp`, and it proves none of `V1`–`V5` of the
same route.  It also proves nothing about `S6`–`S8` of the semigroup-generation route (the Yosida
exponentials, the semigroup laws, the generator), nothing about the Markov property or
Bakry–Émery calculus, and no step of Buser's inequality.  This is general real Hilbert space
material: no measure, no log-concavity, no KLS quantity.

## Strengthenings over the route statements

`R1` is proved through the **sharper** `norm_resolventCLM_sub_sq_le_quarter`, with the constant
`s ‖T f‖ ^ 2 / 4` (the route asks only for `s ‖T f‖ ^ 2`).  The sharp form is the honest output of
the computation `‖u - f‖ ^ 2 = -s ‖T u‖ ^ 2 + s ⟪T u, T f⟫ ≤ s ‖T f‖ ^ 2 / 4`, so the route's
bound is kept verbatim as a wrapper.  No route hypothesis is dropped: `R1` and `R3` use
closedness only through `resolventCLM`, `R2` genuinely needs density, and completeness of `H₀`
and `H₁` is required for `resolventCLM` to exist at all.  The route's `R3` suggests routing
through the resolvent identity `J_s - J_r = (r - s) J_s T†T J_r`; the proof here instead shows
that `s • J_s f - r • J_r f + (r - s) • J_s (J_r f)` solves the weak equation with datum `0`,
hence vanishes, which is the same identity with the adjoint removed.
-/
````

Original comment 225, line 59:

````lean
/-! ## `R1` — quantitative convergence on the domain -/
````

Original comment 226, line 61:

````lean
/-- The exact form of `R1`'s computation: testing the weak equation for `u = J_s f` against
`v = u - f ∈ D(T)` gives `‖u - f‖ ^ 2 = -s ‖T u‖ ^ 2 + s ⟪T u, T f⟫`.

This is the only place where the weak equation is used in the proof of `R1`. -/
````

Original comment 227, line 88:

````lean
/-- `R1`, sharp form: for `f ∈ D(T)`, `‖J_s f - f‖ ^ 2 ≤ s ‖T f‖ ^ 2 / 4`.

Sharper than the route's `R1` by the factor `4`: the computation
`‖u - f‖ ^ 2 = -s ‖T u‖ ^ 2 + s ⟪T u, T f⟫` is closed by Cauchy–Schwarz and
`s (‖T u‖ - ‖T f‖ / 2) ^ 2 ≥ 0`, so the bound `‖T u‖ ≤ ‖T f‖` suggested by the route sketch is
not needed. -/
````

Original comment 228, line 107:

````lean
/-- `R1` of the von Neumann route: for `f ∈ D(T)`, `‖J_s f - f‖ ^ 2 ≤ s ‖T f‖ ^ 2`.

The route's statement, obtained from the sharp `norm_resolventCLM_sub_sq_le_quarter`. -/
````

Original comment 229, line 115:

````lean
/-! ## `R2` — strong convergence to the identity -/
````

Original comment 230, line 117:

````lean
/-- `R2` of the von Neumann route: `J_s f → f` as `s ↓ 0`, for every `f : H₀`.

Stated in `ε`–`δ` form because `resolventCLM` carries the proof `0 < s` as an argument.  Split
`‖J_s f - f‖ ≤ ‖J_s (f - g)‖ + ‖J_s g - g‖ + ‖g - f‖` for `g ∈ D(T)` within `ε / 3` of `f`
(density), bound the outer terms by the contraction property `norm_resolventCLM_le` and the middle
term by `R1`, and take `δ = (ε / 3) ^ 2 / (‖T g‖ ^ 2 + 1)`. -/
````

Original comment 231, line 162:

````lean
/-! ## `R3` — the resolvents commute -/
````

Original comment 232, line 193:

````lean
/-- `R3` of the von Neumann route: the resolvents commute, `J_s J_r = J_r J_s`.

From `resolventDomain_identity`: `w = J_s (J_r f)` satisfies the weak `r`-equation with datum
`J_s f`, so `w = J_r (J_s f)` by uniqueness. -/
````

Original comment 233, line 226:

````lean
/-! ## Graph-norm convergence of the resolvent

`R1`–`R3` above measure `J_s f - f` in the norm of `H₀` only.  Buser's route needs the
convergence in the **graph norm** of `T`: for `f ∈ D(T)` also `T (J_s f) → T f`.  That does not
follow from `R1`–`R3`, and it is not a consequence of the `H₀`-contraction of `J_s` either: the
energies `‖T (J_s f)‖` have to be shown to converge, not merely to stay bounded.

Everything here is again proved from the weak equation alone; the adjoint still never appears,
and no spectral calculus, functional calculus or weak compactness argument is used.  The engine is
the two-parameter identity `resolventDomain_energy_identity`, obtained by testing the `s`-equation
against `J_s f - J_r f` and the `r`-equation against `J_r f - J_s f` and adding.  It simultaneously
gives

* the energy is antitone in `s` (`norm_map_resolventDomain_sq_le_of_le`), and
* a Cauchy estimate for the energies' increments
  (`norm_map_resolventDomain_sub_sq_le_sub`),

so the monotone bounded family `s ↦ ‖T (J_s f)‖ ^ 2` forces `T (J_s f)` to be a Cauchy family.
Completeness of `H₁` produces a limit and **closedness of `T`** identifies it with `T f`. -/
````

Original comment 234, line 376:

````lean
/-- **Graph-norm convergence of the resolvent.** For `f ∈ D(T)` and every `ε > 0` there is
`δ > 0` with `‖T (J_s f) - T f‖ < ε` for every `0 < s < δ`; together with `R1` this says that
`J_s f → f` in the graph norm of `T`, i.e. that `J_s f` approximates `f` in the form domain.

Stated in `ε`–`δ` form because `resolventDomain` carries the proof `0 < s` as an argument.

Proof.  Along `s_n = 1 / (n + 1)` the energies `‖T (J_{s_n} f)‖ ^ 2` are monotone
(`norm_map_resolventDomain_sq_le_of_le`) and bounded by `‖T f‖ ^ 2`
(`norm_map_resolventDomain_le`), and the increments control the distances
(`norm_map_resolventDomain_sub_sq_le_sub`), so `T (J_{s_n} f)` converges in `H₁`; `R1` makes
`J_{s_n} f → f` in `H₀`, and **closedness of `T`** identifies the limit as `T f`.  Hence
`‖T (J_{s_n} f)‖ → ‖T f‖`, and `norm_map_resolventDomain_sub_map_sq_le` with antitonicity of the
energy transfers the resulting estimate from the sequence to every small `s`. -/
````

### `formalization/FunctionalInequalities/Analysis/Semigroup/VonNeumann.lean`

Original comment 235, line 4:

````lean
/-!
# von Neumann's theorem for `T†T`

Part A (`V1`–`V5`) of the von Neumann route recorded in
`research/decisions/2026-09-19-von-neumann-route.md`, for a closed densely defined operator
`T : H₀ →ₗ.[ℝ] H₁` between real Hilbert spaces.  `T†T` is `Analysis.Semigroup.adjointComp T`
(`AdjointComp.lean`) and `J_s = (1 + s T†T)⁻¹` is `Analysis.Semigroup.resolventCLM`
(`Resolvent.lean`, built from the weak equation `WeakResolvent` of `Form.lean`).

What is proved here:

* `V1` = `inner_adjointComp` / `inner_adjointComp_apply`: `⟪T†T x, y⟫ = ⟪T x, T y⟫` for
  `x ∈ D(T†T)`, `y ∈ D(T)`;
* `V2` = `resolvent_add_smul_adjointComp` (with the two halves
  `mem_adjointComp_domain_resolventDomain` and `adjointComp_resolventDomain`):
  `J_s f ∈ D(T†T)` and `(1 + s T†T) J_s f = f`;
* `V3` = `isSelfAdjoint_adjointComp`: `T†T` is self-adjoint;
* `V4` = `dense_adjointComp_domain`: `D(T†T)` is dense;
* `V5` = `sub_resolvent_eq_smul`: `f - J_s f = s • J_s (T†T f)` for `f ∈ D(T†T)`.

Two further consequences of `V1` concern `J = I + T†T` on `{e ∈ D(T†T) : T†T e ∈ D(T)}`:
the expansion `norm_add_adjointComp_sq_add_norm_sq` of its graph norm,
`‖Je‖² + ‖T(Je)‖² = ‖e‖² + 3‖Te‖² + 3‖T†Te‖² + ‖T(T†Te)‖²`, and the resulting four-field
convergence `tendsto_of_tendsto_add_adjointComp`.

## Unused route hypotheses (stronger statements, verbatim wrappers kept)

Following the precedent of `Form.lean` (`S2` drops `0 < s`, `S3` drops `Dense`) and
`Resolvent.lean` (`S5` drops self-adjointness), hypotheses that turn out to be unnecessary are
**not** assumed:

* `V1` is proved without `T.IsClosed` (the route statement does not carry it either) and
  without `CompleteSpace H₁`: `inner_adjointComp` and the verbatim wrapper
  `inner_adjointComp_apply` live in the section before `CompleteSpace H₁` is introduced.  Only
  density of `D(T)` is used, and it is genuinely needed because Mathlib's `LinearPMap.adjoint`
  carries a junk value on a non-dense domain.
* The domain half of `V2`, `mem_adjointComp_domain_resolventDomain`, needs **no density**: that
  `T (J_s f) ∈ D(T†)` follows from `mem_adjoint_domain_of_exists` applied to the weak equation,
  and only the identification of the value `T† (T (J_s f)) = s⁻¹ (f - J_s f)`
  (`adjointComp_resolventDomain`) uses `adjoint_apply_eq`, hence density.

## Deviation from the route sketch

The route sketches `V4` as "immediate from `V3` and `IsSelfAdjoint.dense_domain`".  That order is
not available: `LinearPMap.IsFormalAdjoint.le_adjoint`, which turns symmetry of `T†T` into
`T†T ≤ (T†T)†`, already requires `D(T†T)` to be dense.  So `V4` is proved first, by the direct
argument the route also records (if `g ⊥ D(T†T)` then `g = u + T†T u` with `u = J_1 g`, and
`0 = ⟪u, g⟫ = ‖u‖² + ‖T u‖²`), and `V3` is then derived from it.

## Deliberately out of scope

Nothing here proves `S6`–`S8` of the semigroup-generation route (Yosida exponentials, their
strong convergence, the semigroup), nothing proves Part B (`R1`–`R3`, the resolvent limits), and
nothing here concerns Buser's inequality, the Markov property, Bakry–Émery calculus or any KLS
quantity.  This module is general real Hilbert space material: no measure, no log-concavity.
-/
````

Original comment 236, line 71:

````lean
/-- `V1`: `T†T` acts through the form.

For `x ∈ D(T†T)` and `y ∈ D(T)` one has `⟪T†T x, y⟫ = ⟪T x, T y⟫`.  This is
`LinearPMap.adjoint_isFormalAdjoint` read through `adjointComp_apply`; density of `D(T)` is
needed because Mathlib's adjoint is a junk value otherwise.  Neither `T.IsClosed` nor
completeness of `H₁` is used.  The membership of `y` is taken as a hypothesis rather than
packaged into a subtype, so that the lemma rewrites against goals mentioning a bare `y : H₀`. -/
````

Original comment 237, line 84:

````lean
/-- `V1`, in the verbatim shape of the route statement: the pairing version of
`inner_adjointComp` with `y` presented as an element of `T.domain`. -/
````

Original comment 238, line 91:

````lean
/-- The Dirichlet form of `T†T`: for `x ∈ D(T†T)`, `⟪T†T x, x⟫ = ‖T x‖ ^ 2`.

`V1` with `y = x`, which is legitimate because `D(T†T) ⊆ D(T)`.  This is the form that the
semigroup contracts; `FunctionalInequalities.KLS.LogConcave.inner_adjointComp_self_eq` is its
specialization to the closed weighted gradient.  Neither `T.IsClosed` nor completeness of `H₁`
is used. -/
````

Original comment 239, line 102:

````lean
/-- `T†T` is symmetric: it is a formal adjoint of itself.

Both sides of `⟪T†T x, y⟫ = ⟪x, T†T y⟫` equal `⟪T x, T y⟫` by `V1`, the right-hand one after a
real inner-product flip.  This is the input that `LinearPMap.IsFormalAdjoint.le_adjoint` turns
into `T†T ≤ (T†T)†` once `D(T†T)` is known to be dense. -/
````

Original comment 240, line 114:

````lean
/-- **The graph norm of `(I + T†T) e`.** For `e ∈ D(T†T)` with `T†T e ∈ D(T)`,
`‖e + T†T e‖² + ‖T e + T (T†T e)‖² = ‖e‖² + 3 ‖T e‖² + 3 ‖T†T e‖² + ‖T (T†T e)‖²`.

Both cross terms are `V1`: `⟪e, T†T e⟫ = ‖T e‖²` and `⟪T e, T (T†T e)⟫ = ‖T†T e‖²`. Only
density of `D(T)` is used. -/
````

Original comment 241, line 230:

````lean
/-- `V2`, domain half: the weak solution `J_s f` lies in `D(T†T)`.

From the weak equation `⟪u, v⟫ + s ⟪T u, T v⟫ = ⟪f, v⟫` the vector `T u` pairs continuously
against `T v`, with representative `w = s⁻¹ (f - u)`, so `T u ∈ D(T†)` by
`LinearPMap.mem_adjoint_domain_of_exists`.  **Density of `D(T)` is not needed for this half**
(see the module docstring). -/
````

Original comment 242, line 251:

````lean
/-- `V2`, value half: `T† (T (J_s f)) = s⁻¹ (f - J_s f)`.

The same representative `w = s⁻¹ (f - u)` that witnesses membership in `D(T†)` is the value of
the adjoint, by `LinearPMap.adjoint_apply_eq`; this step does use density of `D(T)`.  The
membership proof is taken as an argument so that the statement does not depend on how it was
produced. -/
````

Original comment 243, line 273:

````lean
/-- `V2`: the resolvent inverts `1 + s T†T`.

For `s > 0` and every datum `f`, the weak solution `J_s f` lies in `D(T†T)` and satisfies
`J_s f + s • T†T (J_s f) = f`.  This is the verbatim route statement, assembled from
`mem_adjointComp_domain_resolventDomain` and `adjointComp_resolventDomain`. -/
````

Original comment 244, line 288:

````lean
/-- `1 + T†T` is surjective: every `z : H₀` is `x + T†T x` for some `x ∈ D(T†T)`.

This is `V2` at `s = 1`, and it is the only consequence of `V2` used in the proofs of `V3` and
`V4`. -/
````

Original comment 245, line 302:

````lean
/-- `V4`: `D(T†T)` is dense.

Proved directly, not from `V3` (see the module docstring for why the route's order is not
available).  If `g` is orthogonal to `D(T†T)`, write `g = x + T†T x` with `x ∈ D(T†T)` by
surjectivity of `1 + T†T`; then `0 = ⟪x, g⟫ = ‖x‖² + ‖T x‖²` by `V1`, so `x = 0` and `g = 0`.
A submodule of a complete inner product space with trivial orthogonal complement is dense. -/
````

Original comment 246, line 325:

````lean
/-- `V3` (von Neumann): `T†T` is self-adjoint.

Symmetry (`adjointComp_isFormalAdjoint`) together with density of `D(T†T)` (`V4`) gives
`T†T ≤ (T†T)†`.  For the reverse inclusion take `y ∈ D((T†T)†)`, solve `u + T†T u = y + (T†T)† y`
with `u ∈ D(T†T)` by surjectivity of `1 + T†T`, and test against an arbitrary `z = x + T†T x`:
both `⟪z, y⟫` and `⟪z, u⟫` collapse to `⟪x, y + (T†T)† y⟫`, so `y - u` is orthogonal to all of
`H₀` and therefore `y = u ∈ D(T†T)`, with `(T†T)† y = T†T u`.  The two inclusions have equal
domains, so `LinearPMap.eq_of_le_of_domain_eq` finishes. -/
````

Original comment 247, line 376:

````lean
/-- `V5`: the Yosida approximation on `D(T†T)`.

For `f ∈ D(T†T)`, `f - J_s f = s • J_s (T†T f)`; equivalently `L_s f = s⁻¹ (f - J_s f)` equals
`J_s (T†T f)`.  By `V1`, `f` itself solves the weak equation with datum `f + s • T†T f`, so
uniqueness (`eq_resolventDomain`) gives `J_s (f + s • T†T f) = f`, and linearity of `J_s`
separates the two terms. -/
````

### `formalization/FunctionalInequalities/Analysis/Semigroup/Yosida/Approximation.lean`

Original comment 248, line 3:

````lean
/-!
# The Yosida approximation `L_s = s⁻¹ (1 - J_s)`

Definitions only. Given a closed operator `T : H₀ →ₗ.[ℝ] H₁` between real Hilbert spaces and the
resolvent `J_s = resolventCLM T hT hs` of `Analysis/Semigroup/Resolvent/Basic.lean`, this module packages
the bounded operator `L_s = s⁻¹ • (1 - J_s)` on `H₀`. Formally `L_s = T†T J_s = T†T (1 + s T†T)⁻¹`,
the classical Yosida approximation of `T†T`; that identification is `V5` of
`Analysis/Semigroup/VonNeumann.lean`, not anything proved here.

Its properties (nonnegativity, symmetry, commutation, convergence to `T†T` on `D(T†T)`, and the
strong convergence of `exp (-t • L_s)` which is `S6`) are the `Y`-series obligations of
`research/audits/YosidaLimitRouteStatements.lean`. Everything here is definitional or `simp`-level
glue. No measure, no log-concavity and no KLS content.
-/
````

### `formalization/FunctionalInequalities/Analysis/Semigroup/Yosida/Laws.lean`

Original comment 252, line 42:

````lean
/-- `Y3`: the Yosida family commutes, `L_s L_r = L_r L_s`.  Both sides expand to
`s⁻¹ r⁻¹ (1 - J_s - J_r + J_s J_r)`, and `J_s J_r = J_r J_s` is `R3`
(`resolventCLM_comp_comm`). -/
````

Original comment 253, line 54:

````lean
/-- `Y4`: on `D(T†T)` the Yosida approximation is `L_s = J_s T†T`.  This is `V5`
(`sub_resolvent_eq_smul`) divided by `s`. -/
````

Original comment 254, line 62:

````lean
/-- `Y5`: on `D(T†T)` the Yosida approximation converges strongly to `T†T` as `s ↓ 0`.  By `Y4`
the difference is `J_s (T†T f) - T†T f`, which `R2`
(`exists_delta_norm_resolventCLM_sub_lt`) makes small. -/
````

### `formalization/FunctionalInequalities/Analysis/Semigroup/Yosida/Limit.lean`

Original comment 255, line 4:

````lean
/-!
# `S6`: the Yosida exponentials converge strongly

`Y8` of the Yosida-limit route (`research/decisions/2026-09-19-yosida-limit-route.md`), which is
`S6` of the semigroup-generation route for the actual Yosida approximation
`L_s = s⁻¹ (1 - J_s)` of `T†T`: for `T` closed and densely defined,
`exp (-t • L_s) f` converges as `s ↓ 0`, for every `f : H₀` and every `t ≥ 0`.

The proof is pure composition. The corrected abstract statement `Y7`
(`exists_limit_exp_neg_smul`, `Exponential/Limit.lean`) is applied to the family `s ↦ L_s` with the
dense set `D(T†T)`: nonnegativity is `Y1` (`yosida_nonneg`), commutation is `Y3`
(`yosida_comp_comm`), density is `V4` (`dense_adjointComp_domain`), and the Cauchy property on
`D(T†T)` follows from the convergence `L_s f → T†T f` of `Y5`
(`exists_delta_norm_yosida_sub_adjointComp_lt`) by the triangle inequality.

The limit `g` is not yet named as an operator: `S7` (the limit defines a strongly continuous
semigroup of self-adjoint contractions) and `S8` (its generator is `T†T`) are not proved here. Nothing
here is the Markov property, Bakry–Émery calculus, a heat estimate or any step of Buser's inequality.
-/
````

Original comment 257, line 55:

````lean
/-- **`S6` for the Yosida approximation** (`Y8`). For `T` closed and densely defined, every
`t ≥ 0` and every `f : H₀`, the vectors `exp (-t • L_s) f` converge as `s ↓ 0`, in the `ε`–`δ`
sense forced by the proof argument `0 < s` carried by `L_s`. -/
````

### `formalization/FunctionalInequalities/Analysis/TemperateGrowth.lean`

Original comment 258, line 4:

````lean
/-!
# Temperate growth from bounded high derivatives

Generic calculus support (for the polynomial growth of the derivatives of a smoothed log-density,
Bizeul–Klartag–Lehec arXiv:2610.05474v1, Section 2, p. 5): on arbitrary real normed spaces, a
polynomial bound on `D^{m+1} f` gives one on `D^m f` by the mean value inequality, and a smooth
function with uniformly bounded derivatives of all orders `≥ 3` has `Function.HasTemperateGrowth`.
Proof bodies: root Codex (bundle `Log-Composition-Bounds`, independently accepted); statements and
placement: Claude.
-/
````

### `formalization/FunctionalInequalities/Analysis/Tensor/Coordinate.lean`

Original comment 259, line 202:

````lean
/-- **Letwin (2.12), finite form** (arXiv:2607.24164v1, proof of Theorem 2.5, p. 10): for an array
`T` symmetric in its first two indices and weights `b`,
`Σ b_i² T_{ijk}² − Σ b_i b_j T_{ijk}² = ½ Σ (b_i − b_j)² T_{ijk}²`; in particular the left side is
nonnegative. Stated for arbitrary real weights (the source has nonnegative eigenvalues). Codex proof
(`build/reviews/2026-10-07-bkl-continuous/queue/letwin-prerequisite/Letwin-2-12-Codex-Proof.lean`,
independently accepted). -/
````

### `formalization/FunctionalInequalities/Analysis/Vector/Coarea/Local.lean`

Original comment 261, line 4:

````lean
/-! # The local codimension-`m` coarea equality on a level chart

Everything the codimension-`m` coarea formula needs on one chart is now available, and this module
puts it together.  The three inputs, each proved in its own round:

* the **ambient side**, `setLIntegral_coareaJacobian_levelGraphFamily`: on a Borel piece of a level
  family the ambient coarea density becomes the graph area density, by the fibrewise
  `m`-dimensional change of variables and the fibre Jacobian identity;
* the **fibre side**, `setLIntegral_image_vectorGraphMap`: the weighted codimension-`m` graph area
  formula;
* the **slice description**, `slice_eq_image_vectorGraphMap`: each level set of the family is a
  graph over the corresponding parameter slice.

Tonelli in the level variable joins them.  The result,
`setLIntegral_coarea_levelGraphFamily`, is the codimension-`m` analogue of the scalar
`setLIntegral_coarea_graph_family`: on the image of a Borel piece of the chart,

`∫ coareaJacobian (Du) · g dx = ∫_t ∫_{fibre} g dℋ^{n-m} dt`,

with an arbitrary measurable `ℝ≥0∞` weight and no finiteness hypothesis anywhere.

**This is a local statement on one chart, not the codimension-`m` regular coarea formula.**  Two
things are still missing for that: the countable cover of a regular open set by such charts with the
disjoint patching, and the codimension-`m` weighted slice measurability that makes the outer
integral well posed as an a.e. statement (the scalar analogues are the assembly in
`KLS/Geometry/Coarea/Regular.lean` and `KLS/Geometry/Slice/OpenMeasurable.lean`).
-/
````

### `formalization/FunctionalInequalities/Analysis/Vector/Coarea/Regular.lean`

Original comment 262, line 3:

````lean
/-! # Weighted slice measurability in codimension `m`, and the regular coarea formula

The assembly of the local coarea equality into a statement about a whole regular open set needs one
more ingredient: the level function `t ↦ ∫⁻ over S ∩ {u = t}` must be measurable, since the
patching exchanges a countable sum with the outer integral and `lintegral_tsum` needs measurability.

**The route taken here is not the scalar one.**  In codimension one the repository proves slice
measurability for an arbitrary Borel `S` inside an open `C¹` domain **with no regular-point
hypothesis**, through the Eilenberg slicing inequality of `Analysis/Hausdorff/SurfaceSlicing.lean`.  The
codimension-`m` Eilenberg inequality is **not** available here, so this module proves the statement
only where the differential is surjective, and proves it **directly from the chart**: on a chart the
slice integral is a Tonelli section of one measurable function on the parameter–level product, so
its measurability is immediate and no slicing inequality is used.

That is enough for the regular case, and `coarea_of_contDiffOn_of_coareaJacobian_ne_zero` assembles
it: the **codimension-`m` regular coarea formula**, the analogue of the scalar `L9`
`KLS.coarea_of_contDiffOn_of_fderiv_ne_zero`, with weighted slice measurability included.

**What is still open**: slice measurability **without** the regularity hypothesis, which in
codimension one is what lets the critical part be treated at all; the critical set, sharp
finite-regularity Sard, and everything beyond the regular case.
-/
````

Original comment 263, line 130:

````lean
/-- **The codimension-`m` regular coarea formula.**  On an open set where the differential of `u` is
everywhere surjective, for every Borel `S ⊆ O` and every measurable `ℝ≥0∞` weight, the level
function is measurable and the coarea equality holds, with the normalized Hausdorff measure of the
codimension as the fibre measure.

This is the analogue of the scalar `L9`, `KLS.coarea_of_contDiffOn_of_fderiv_ne_zero`; the level
function is even **measurable**, not merely almost everywhere measurable.

No finiteness, boundedness, integrability, regular-value or `SFinite` hypothesis is used, and no
regularity of `u` outside `O`.  **Nothing is claimed about the critical set**: surjectivity of the
differential is assumed at every point of `O`. -/
````

### `formalization/FunctionalInequalities/Analysis/Vector/Graph/Area.lean`

Original comment 268, line 3:

````lean
/-! # The codimension-`m` area formula for `C¹` graphs

Obligation `B1`, fifth and last phase.  The `k`-dimensional measure of the graph of a `C¹`
`K`-valued map over a measurable set is the integral of `√det (1 + Dγᵀ Dγ)`.

One step differs from codimension one and is the reason this phase needed its own partition.  The
codimension-one proof uses that the Jacobian `√(1 + ‖a‖²)` is **globally `1`-Lipschitz** in the
slope, so that closeness of the derivatives transfers to closeness of the Jacobians.  In
codimension `m` the Jacobian `√det (1 + AᵀA)` is **not** uniformly Lipschitz — already for
`A = t • id` on a two-dimensional parameter space it grows like `1 + t²` — so
`exists_approximating_partition_with_jacobian` below asks the partition to control the Jacobian
**directly**, which continuity supplies.  Everything after that mirrors the codimension-one file,
and the limit lemmas `tendsto_aux`, `tendsto_aux'` are graph-independent and reused unchanged.
-/
````

Original comment 269, line 280:

````lean
/-- **`B1`: the codimension-`m` area formula for `C¹` graphs.**  The `k`-dimensional Hausdorff
measure of the graph of a `C¹` `K`-valued map over a measurable set is the integral of the graph
volume factor `√det (1 + Dγᵀ Dγ)`.  No finiteness, boundedness or injectivity hypothesis: a graph
map is injective by construction. -/
````

### `formalization/FunctionalInequalities/Analysis/Vector/Graph/Basic.lean`

Original comment 271, line 4:

````lean
/-! # Graphs of vector-valued maps

Obligation `B1` of the area formula route, first part: the `C¹` infrastructure for the graph of a
**`K`-valued** map, `dim K = m`, which is what a codimension-`m` fibre looks like.  The
codimension-one case lives in `Analysis/Graph/Area.lean`; this module mirrors its second and third
phases — the graph map, its retraction, injectivity, derivative, image measurability and linear
approximation — with a vector-valued slope.

Two things are easier here than in codimension one.  The retraction `graphProj ι = ιᵀ` is already
available and is an **explicit** left inverse of the graph map, which is exactly what the general
area-formula route lacks.  And the linear area formula for the graph model is immediate from
Mathlib's `LinearMap.hausdorffMeasure_image` together with `normDet_graphMapLinear`, so the shear
argument the codimension-one file needed is not repeated.

**The area formula itself is not proved here**: the two-sided estimates and the limit, the fourth
and fifth phases of the codimension-one file, are the remaining part of `B1`.
-/
````

Original comment 272, line 170:

````lean
/-- **The linear case of `B1`.**  No shear argument is needed: this is Mathlib's linear area formula
combined with the volume factor computed in `Analysis/Graph/Jacobian.lean`. -/
````

### `formalization/FunctionalInequalities/Analysis/Vector/Graph/Integral.lean`

Original comment 275, line 3:

````lean
/-! # The weighted codimension-`m` graph area formula

Obligation `B2` of the area formula route computes the normalized `k`-dimensional measure of a `C¹`
graph.  That is an identity of **measures of sets**; the coarea formula integrates an arbitrary
weight over a fibre, so it needs the same identity as a **change of variables**.

`map_vectorGraphMap_withDensity` upgrades it in the standard way: the graph parametrization pushes
the Jacobian-weighted Lebesgue measure on the parameter space forward to the normalized surface
measure restricted to the graph.  Injectivity of the graph map — automatic, by construction — and
measurability of its image are what make the two restrictions match.  From it,
`setLIntegral_image_vectorGraphMap` is the change of variables for an arbitrary measurable
`ℝ≥0∞`-valued weight.

This is the codimension-`m` analogue of `setLIntegral_image_graphMap` in `OpenGraphIntegral.lean`,
proved through `GraphIntegral.lean`; the structure of the argument is the same, with the
codimension-one Jacobian `√(1 + ‖∇g‖²)` replaced by `normDet (graphMapLinear ι κ (Dγ y))`.

**No integrability, finiteness or boundedness hypothesis** is used: the weight may be unbounded or
identically `∞`, and the parameter set need only be measurable.  **No coarea formula is proved
here.**
-/
````

### `formalization/FunctionalInequalities/Analysis/Vector/Graph/Sandwich.lean`

Original comment 277, line 3:

````lean
/-! # Two-sided estimates for vector-valued graphs

Obligation `B1`, fourth phase: the sandwich estimates.  A graph map that is `ε`-close to its linear
model has `k`-dimensional image measure within a factor `(1 + ε)^k` of the linear one, on both
sides.

Both directions reduce to the same generic comparison
`Analysis.hausdorffMeasure_image_le_of_norm_le`, already proved for the codimension-one file, and
both need the **Pythagorean identity** `‖ι y + κ z‖² = ‖y‖² + ‖z‖²`, which holds because the two
embeddings have orthogonal ranges.  Its consequence `‖y - y'‖ ≤ ‖Ψ y - Ψ y'‖` is what makes a graph
map expansive, and that is exactly the lower bound the general area-formula route has to obtain
from an inverse it does not have.

**The area formula itself is still not proved**: the limit `ε → 0` and the countable patching are
the fifth and last phase.
-/
````

Original comment 278, line 187:

````lean
/-- A countable measurable partition of `H` on which the graph map is `ε`-approximated by linear
graph maps and the derivative stays `ε`-close to the corresponding slope.  This is the input of the
remaining, fifth phase of `B1`. -/
````

### `formalization/FunctionalInequalities/Analysis/Vector/Jacobian.lean`

Original comment 279, line 77:

````lean
/-- **Compatibility with the proved scalar theory**: the coarea Jacobian of the differential of a
real-valued function is exactly the norm of its gradient, the integrand of the weighted coarea
formula `L11`/`L12`/`L13`. -/
````

### `formalization/FunctionalInequalities/Analysis/Vector/JacobianContinuity.lean`

Original comment 280, line 4:

````lean
/-! # Continuity and measurability of the volume factors

Obligation `A1` of the area formula route.  Mathlib proves the algebraic theory of
`LinearMap.normDet` but **not** its continuity in the operator, so the right-hand side of the area
formula is not yet known to be an integral of a measurable function.  This module supplies that.

`normDet A` is the square root of the determinant of the Gram operator `Aᵀ A`, and each step of
that description is continuous: the adjoint is a linear isometry, composition is continuous, the
determinant of a continuous linear endomorphism is continuous, and so is the square root.  The
measurability of the integrand then follows from `measurable_fderiv`, which needs **no**
differentiability hypothesis on the function.

The same argument applies verbatim to `coareaJacobian`, whose integrand the codimension-`m` coarea
formula will need on the other side.

**No area formula and no coarea formula are proved here.**
-/
````

### `formalization/FunctionalInequalities/Analysis/Vector/RankDeficient/Coarea.lean`

Original comment 283, line 3:

````lean
/-! # The rank-deficient critical set, and the codimension-`m` coarea formula

The last three obligations of the rank-deficient route recorded in
`research/decisions/2026-09-17-rank-deficient-route.md`: `R8`, the localization; **`R0`**, the
target — the rank-deficient critical set is `ℋ^k`-null in almost every level; and **`R9`**, the
codimension-`m` coarea formula with **no hypothesis on the critical set**.

**What this closes.**  `Analysis/Vector/Coarea/Regular.lean` proved the coarea formula where the
differential is surjective, and `Analysis/Vector/Slice/Critical.lean` extended it under the hypothesis
that the derivative *vanishes* wherever it fails to be surjective — a genuine restriction for
`m ≥ 2`, exhibited there by a rank-one map of the plane.  `coarea_of_contDiff` below removes that
hypothesis entirely.

**What it is not.**  It is **not a Sard theorem**: nothing whatever is claimed about the measure of
the set of critical *values*, which for a merely `C¹` map may well be positive.  The map is assumed
`C¹`, not Lipschitz.  The fibre measure is the normalized Hausdorff measure of the complementary
dimension, in the repository's standing convention.

**The route, in one paragraph.**  `R1` stratifies the critical set by the exact rank of the
differential into finitely many measurable layers.  On a layer, `R2` says the differential dies
along the fibres of the regular component `P ∘ u`, `R3` makes that quantitative with a locally
uniform right-inverse bound, and `R4` turns the two into a small tangential Lipschitz constant.
`R7` then runs the approximating partition on `u` itself and applies the Eilenberg bound **inside a
fibre**, where `k + (m − r) = n − r` is the right exponent, integrating against the proved regular
coarea formula; that gives the layer's nullity near each of its points.  `R8` here patches those
neighbourhoods together by second countability, the finite union over `r < m` gives `R0`, and the
critical part of the coarea equality then vanishes on both sides, giving `R9`.
-/
````

Original comment 284, line 43:

````lean
/-- **`R8`: a local null-slicing statement patches to a global one.**  `V` is second countable, so
the neighbourhood family has a countable subcover and the almost-everywhere quantifier survives the
countable intersection.  No regularity of `u` and no measurability of `A` is used. -/
````

Original comment 285, line 99:

````lean
/-- **`R0`: the critical set of a `C¹` map is `ℋ^k`-null in almost every level.**  This is the
target of the rank-deficient route, and it covers the **whole** critical set
`{x | fderiv ℝ u x` is not surjective`}`, not merely the part where the derivative vanishes.

No positivity of the codimension is needed: with a zero-dimensional target every linear map is
surjective, the critical set is empty and the statement is vacuous rather than false.

**This is not a Sard theorem**: nothing is claimed about the measure of the set of critical
*values*. -/
````

Original comment 286, line 126:

````lean
/-- The normalized form of `R0`, which the coarea layer consumes. -/
````

Original comment 287, line 135:

````lean
/-- **`R9`: the codimension-`m` coarea formula for `C¹` maps, with no hypothesis on the critical
set.**  `Analysis/Vector/Slice/Critical.lean` proved this under the extra assumption that the
derivative vanishes wherever it fails to be surjective, which for `m ≥ 2` is a genuine restriction;
`R0` removes it.

No finiteness, boundedness, integrability or regular-value hypothesis is used, `S` is an arbitrary
Borel set, `g` an arbitrary measurable `ℝ≥0∞` weight, and no positivity of the codimension is
required.  **It is not a Sard theorem.** -/
````

### `formalization/FunctionalInequalities/Analysis/Vector/RankDeficient/ExponentObstruction.lean`

Original comment 288, line 4:

````lean
/-! # What the small-Lipschitz method actually yields: the exponent of the obstruction

Route obligation `N1` of `research/decisions/2026-09-17-rank-deficient-route.md`, the **diagnostic**
that records what the projected small-Lipschitz argument gives and why it is not `R0`.

Suppose the composite `Q ∘ u` — the part of `u` orthogonal to the range of its differential — can,
at every scale `ε`, be made `ε`-Lipschitz on the pieces of a countable measurable partition of `S`.
Running the codimension-`dim W₂` Eilenberg inequality on each piece and letting `ε → 0` gives

`μH[n − dim W₂] (S ∩ {Q ∘ u = τ}) = 0` for almost every `τ ∈ W₂`.

**That exponent is `k + r`, not `k`.**  In the route's notation `W₂` is the orthogonal complement of
the rank-`r` range, so `dim W₂ = m − r` and the exponent is `n − (m − r) = k + r`.  For `r ≥ 1` this
is strictly weaker than `R0` in the useless direction: a set can be `μH[k + r]`-null and still carry
infinite `μH[k]`.  That is exactly why the route has to slice **inside a fibre** instead, which is
what `Analysis/Vector/RankDeficient/StratumSlicing.lean` does, and why this file is a diagnostic with **no consumer**.

**Both side conditions of the route statement are used and both are real.**  `S` must be measurable
for the majorants of the disjoint pieces to add up to the majorant of `S`, and `0 < finrank ℝ W₂`
is what makes the Eilenberg constant `ε ^ (dim W₂)` tend to `0` — with `dim W₂ = 0` the constant is
`1`, nothing tends to zero, and the statement is false.

**The truncated exponent is harmless here.**  `finrank ℝ V - finrank ℝ W₂` is a natural subtraction,
so when the target is larger than the domain it collapses to `0` rather than going negative.  The
proof never needs `finrank ℝ W₂ ≤ finrank ℝ V`: all it uses is
`(n - m) + m ≥ n`, which holds in `ℕ` either way and keeps the Eilenberg right-hand side
`μH[(n − m) + m] S ≤ μH[n] S` finite.  This is the point on which the companion diagnostic `N2`
fails, and `N1` survives it.

**The companion diagnostic `N2` is false as written**, and `hausdorffMeasure_finrank_sub_eq_top`
below is its repair: below the top dimension a set of positive Lebesgue measure has infinite
Hausdorff measure, **provided the dimension is positive**.  That proviso is exactly what the route's
`N2` was missing, and it is necessary — the refutation and the route bookkeeping are in
`research/audits/ExponentObstructionAudit.lean`.  The repaired statement is also what makes `N1`
useless for `R0`: at the exponent `k` the measure is already infinite, so nullity at `k + r` says
nothing.
-/
````

Original comment 289, line 67:

````lean
/-! ### The companion diagnostic `N2`, repaired -/
````

Original comment 290, line 70:

````lean
/-- **`N2`, repaired.**  Below the top dimension the Hausdorff measure of a set of positive
Lebesgue measure is infinite.  The hypothesis `0 < finrank ℝ V` is **necessary**: the route's `N2`
omits it and is false, because the truncated subtraction `finrank ℝ V - r` collapses to `0` in a
zero-dimensional space, where a nonempty set has `μH[0] = 1` rather than `⊤`.  The refutation is
`route_N2_is_false` in `research/audits/ExponentObstructionAudit.lean`. -/
````

Original comment 291, line 146:

````lean
/-- **`N1`: the obstruction, stated.**  Projecting away the range of the differential and running
the proved Eilenberg bound gives a null slicing statement at the exponent `n − dim W₂`, which in
the route's notation is `k + r`, **not** `k`.  For `r ≥ 1` this is strictly weaker than `R0` in the
useless direction: a set can be `μH[k + r]`-null and have infinite `μH[k]`.

This is a **diagnostic**: it is not a step towards `R0`, which was proved independently in
`Analysis/Vector/RankDeficient/Coarea.lean` by slicing inside a fibre instead. -/
````

### `formalization/FunctionalInequalities/Analysis/Vector/RankDeficient/RegularFibreFinite.lean`

Original comment 292, line 3:

````lean
/-! # The fibres of the regular part have finite Hausdorff measure

Obligation `R5` of the rank-deficient route recorded in
`research/decisions/2026-09-17-rank-deficient-route.md` and stated in
`research/audits/RankDeficientRouteStatements.lean`.  **Only `R5` is proved here**; with `R1`, `R2`,
`R3`, `R4` and `R6` that is six of the route's obligations.  `R0`, `R7`–`R10`, `N1` and `N2` remain
open, and so does the rank-deficient part of the codimension-`m` coarea critical set.  Nothing here
is a coarea formula in a new case, a slicing statement about the critical set, or a Sard theorem.

**What `R5` is for.**  The route repairs the exponent by applying the Eilenberg bound not in `V` but
inside a fibre of the regular component `v = P ∘ u`, with `d = k` and a target of dimension
`m − r`, so that `d + (m − r) = n − r`.  For that bound to say anything the fibre must carry
**finite** `ℋ^{n−r}` measure — otherwise the right-hand side is `∞` and the estimate is vacuous,
exactly as `N2` records for the one-step method.

**It is a corollary of the proved regular coarea formula**, not new analysis:
`coarea_of_contDiffOn_of_coareaJacobian_ne_zero` with weight `1` says that the total fibre measure
integrates to `∫⁻ coareaJacobian` over the piece, which is finite on a relatively compact piece
because the integrand is continuous there.  A finite integral has almost everywhere finite
integrand.

**Relative compactness is a real hypothesis, not a convenience.**  The coarea Jacobian may be
unbounded near the boundary of the regular open set, and the fibres of a regular map need not have
finite measure globally — a linear projection of the plane has fibres of infinite length.
-/
````

Original comment 293, line 63:

````lean
/-- **`R5`: at almost every level the fibre of a regular `C¹` map meets a relatively compact piece
in a set of finite `ℋ^{n-r}` measure.**

This is what makes the Eilenberg right-hand side finite at the repaired exponent.  It follows from
the **proved** regular coarea formula with weight `1`; no new analysis is involved, and nothing is
claimed about the critical set of `v`. -/
````

### `formalization/FunctionalInequalities/Analysis/Vector/RankDeficient/RightInverseBound.lean`

Original comment 294, line 6:

````lean
/-! # Approximate right inverses of a surjection, pointwise and locally uniformly

Obligation `R3` of the rank-deficient route recorded in
`research/decisions/2026-09-17-rank-deficient-route.md` and stated in
`research/audits/RankDeficientRouteStatements.lean`.  **Only `R3` is proved here**; together with
the already proved `R1` and `R2` of `Analysis/Vector/RankDeficient/Stratification.lean` that is three of the route's
obligations.  `R0`, `R4`–`R10`, `N1` and `N2` remain open, and so does the rank-deficient part of
the codimension-`m` coarea critical set.  Nothing here is a coarea formula, a slicing statement or
a Sard theorem.

**What `R3` is for.**  In the route a fibre of the regular component `v = P ∘ u` is sliced, and the
chord `b - a` of a fibre is *not* a tangent vector: two points of one fibre only give
`‖Dv (b - a)‖ ≤ ε ‖b - a‖`, not `Dv (b - a) = 0`.  Turning that into smallness of `‖Du (b - a)‖`
needs a quantitative statement that a vector almost annihilated by a surjection is close to its
kernel, which is exactly a norm bound on a right inverse.

**Why the uniform version is a hard requirement rather than a convenience.**  The limit `ε → 0` in
the Eilenberg argument uses a *different* approximating partition at every scale, so a constant
depending on the piece is useless; the bound has to hold with one constant on a whole
neighbourhood.  `exists_nhds_uniform_rightInverse_bound` provides that, by perturbing a single
right inverse at the base point: if `A ∘ R₀` stays a unit then `R₀ ∘ (A ∘ R₀)⁻¹` is a right inverse
of `A`, and its norm is controlled because inversion is continuous at a unit.

Neither statement needs an inner product, a measure or completeness of the domain; only the target
is finite-dimensional, and the domain is an arbitrary real normed space.
-/
````

Original comment 295, line 58:

````lean
/-- **`R3`, pointwise.**  A surjection onto a finite-dimensional space admits a single constant `C`
such that every vector is within `C ‖L z‖` of the kernel.

The domain is an arbitrary real normed space: only the target has to be finite-dimensional, which
is what makes the linear right inverse of `L` automatically continuous. -/
````

Original comment 296, line 89:

````lean
/-- **`R3`, locally uniform.**  Around a point where the differential of a `C¹` map is surjective
there is a neighbourhood carrying **one** bound `M` on the differential and **one** constant `C`
for the kernel estimate.

This is the form the route needs: the `ε → 0` limit runs through a different approximating
partition at each scale, so a constant depending on the piece would be useless. -/
````

### `formalization/FunctionalInequalities/Analysis/Vector/RankDeficient/Stratification.lean`

Original comment 297, line 6:

````lean
/-! # The rank stratification of the differential, and the kernel lemma

The first two obligations of the rank-deficient route recorded in
`research/decisions/2026-09-17-rank-deficient-route.md` and stated in
`research/audits/RankDeficientRouteStatements.lean`.  **Only `R1` and `R2` are proved here**; `R0`
and `R3`–`R10` remain open, and so does the rank-deficient part of the codimension-`m` coarea
critical set that they are steps towards.  Nothing here is a coarea formula, a slicing statement or
a Sard theorem.

The coarea critical set of a map into an `m`-dimensional target is
`{x | fderiv ℝ u x` is not surjective`}`, where the rank of the differential drops below `m`.
`Analysis/Vector/Slice/Critical.lean` handles the layer where the derivative *vanishes*; the route
for the remaining layers stratifies the critical set by the exact rank.

**`R1`** makes the stratification usable: each stratum is measurable — Mathlib's
`isOpen_setOfPred_nat_le_rank` makes `{f | r ≤ rank f}` open, so a stratum is the difference of two
open sets, pulled back along the continuous derivative — and the critical set is the union of the
finitely many strata of rank `r < m`.

**`R2`** is the structural heart of the route, and is pure linear algebra.  If `P ∘ L` is already
surjective onto a space of the same dimension as the range of `L`, then `P` is injective on that
range, so `P ∘ L` and `L` have the *same* kernel.  In the route `L` is the differential at a point
of the stratum and `P` the orthogonal projection onto its range, so the conclusion is that the
differential vanishes along the fibre of the regular part `P ∘ u` — which is what lets the
Eilenberg bound be applied inside a fibre, at the exponent that finally matches.

No inner product, no measure and no completeness is used for `R2`; `R1` needs only continuity of
the derivative and the Borel structure of the domain.  The target is never assumed
positive-dimensional: with `finrank ℝ W = 0` every map is surjective, the critical set is empty and
the union over `r < 0` is empty too.
-/
````

Original comment 298, line 59:

````lean
/-- **`R2`, kernel form.**  If `P ∘ L` is surjective onto a space whose dimension equals the rank of
`L`, then `P` is injective on the range of `L` and the two kernels coincide.

The dimension hypothesis is exactly what rules out the degenerate reading: without it `P` may
collapse part of the range of `L` while `P ∘ L` stays surjective, and then `ker (P ∘ L)` is
strictly larger. -/
````

Original comment 299, line 83:

````lean
/-- **`R2`, the form the route consumes**: on the stratum the differential vanishes wherever the
regular component does, that is, along the fibre directions of `P ∘ u`. -/
````

Original comment 300, line 130:

````lean
/-- **`R1`, second half: the critical set is the union of the strata of rank below the dimension of
the target.**  A finite union, and no regularity of `u` is used: this is pointwise linear algebra.
With a zero-dimensional target both sides are empty. -/
````

Original comment 301, line 150:

````lean
/-- **`R1`, first half: the rank strata of the differential of a `C¹` map are measurable.**

Mathlib's `isOpen_setOfPred_nat_le_rank` gives the lower semicontinuity of the rank; a stratum is
the difference of two of those open sets, pulled back along the continuous derivative.  No
measurable structure on the space of operators is needed. -/
````

### `formalization/FunctionalInequalities/Analysis/Vector/RankDeficient/StratumSlicing.lean`

Original comment 302, line 8:

````lean
/-! # The per-stratum slicing

**Obligation `R7`** of the rank-deficient route recorded in
`research/decisions/2026-09-17-rank-deficient-route.md`, **proved** here as
`exists_nhds_ae_hausdorffMeasure_stratum_inter_levelSet_eq_zero`: around every point of the rank-`r`
stratum there is a neighbourhood in which almost every level meets the stratum in an `ℋ^k`-null set.
With `R1`–`R6` that is seven of the route's obligations.  **`R0` is still open**: it needs `R8`, the
localization of this statement to the whole stratum, and the finite union over `r < m`.  Nothing
here is a coarea formula in a new case, a slicing statement about the full critical set, or a Sard
theorem.

**The argument.**  Near a point of the stratum let `K` be the range of the differential there and
`P`, `Q` the orthogonal projections onto `K` and `Kᗮ`.

* `exists_stratum_local_data` — the **local package**.  There is an open neighbourhood with compact
  closure on which `P ∘ u` is a submersion, together with **one** constant `c` such that for
  **every** stratum point `y` in it, every `ε` and every set on which `u` is `ε`-approximated by
  `fderiv ℝ u y`, the projected map `Q ∘ u` is `c ε`-Lipschitz along every fibre of `P ∘ u`.  The
  uniformity of `c` over `y` is the difficulty, since `R4`'s constant depends on the piece's linear
  model; it comes from `R2`, the **locally uniform** half of `R3`, and a bound on `‖fderiv ℝ u‖`.
* `lintegral_split_target` — an integral over the target is the iterated integral over an orthogonal
  splitting of it, by `LinearIsometryEquiv.measurePreserving`, `WithLp.volume_preserving_toLp` and
  Tonelli.  This is the integral form of what `R6` does for null sets.
* `lintegral_hausdorffMeasure_stratum_le` — the **per-scale bound**.  Run Mathlib's approximating
  partition on `u` **itself**, so one partition serves both components; on each piece the local
  package makes `Q ∘ u` small-Lipschitz along fibres; the Eilenberg bound of
  `Analysis/Vector/Slice/Hausdorff.lean` applies **inside a fibre** at exponent `k` with a target of
  dimension `m − r`, where `k + (m − r) = n − r` is exactly right; integrating over the fibre
  parameter against the **proved** regular coarea formula for `P ∘ u` turns the fibre measures into
  an ordinary integral of the coarea Jacobian, and `lintegral_split_target` reads the result as an
  integral over the target.  The constant does **not** depend on `ε`.
* `exists_nhds_ae_hausdorffMeasure_stratum_inter_levelSet_eq_zero` — the limit `ε → 0`.  The
  right-hand factor is finite because the closure of the neighbourhood is compact, and the exponent
  `m − r` is positive exactly because `r < m`, so the integral over the target vanishes and the
  integrand vanishes almost everywhere.

**Where the wrong exponent of the one-step method is repaired** is the fibre: applying the Eilenberg
bound in the ambient space would force the exponent `k + r`, and forcing it back to `k` would make
the right-hand side `μH[n − r]` of a set of positive Lebesgue measure, which is `∞`.  Inside a fibre
the same bound is used at `k` and the right-hand side is the fibre's own finite `ℋ^{n−r}` measure.
-/
````

Original comment 303, line 187:

````lean
/-- **The integral form of the target splitting.**  An integral over the target is the iterated
integral over an orthogonal splitting of it.  This is what `R6` does for null sets, in the form the
per-scale estimate has to be integrated against: the inner integral is over the directions the
second slicing uses, the outer one over the fibre parameter of the regular component. -/
````

Original comment 304, line 405:

````lean
/-- **`R7`: the local per-stratum slicing.** -/
````

### `formalization/FunctionalInequalities/Analysis/Vector/RankDeficient/TangentialLipschitz.lean`

Original comment 305, line 5:

````lean
/-! # The tangential small-Lipschitz estimate on fibres

Obligation `R4` of the rank-deficient route recorded in
`research/decisions/2026-09-17-rank-deficient-route.md` and stated in
`research/audits/RankDeficientRouteStatements.lean`.  **Only `R4` is proved here**; with `R1`, `R2`
of `Analysis/Vector/RankDeficient/Stratification.lean` and `R3` of `Analysis/Vector/RankDeficient/RightInverseBound.lean` that is four of
the route's obligations.  `R0`, `R5`–`R10`, `N1` and `N2` remain open, and so does the
rank-deficient part of the codimension-`m` coarea critical set.  Nothing here is a coarea formula,
a slicing statement or a Sard theorem.

**This is the analytic content the route turns on, and the step that replaces the one that fails.**
The proved vanishing-derivative argument covers the rank-zero layer because there the approximating
partition makes `u` itself `ε`-Lipschitz on each piece.  On a stratum of rank `r ≥ 1` it does not,
in any direction inside the range of the differential.  What `R4` says is that the **projected** map
`Q ∘ f` is nevertheless Lipschitz with a constant proportional to `ε` **along each fibre of
`P ∘ f`** — which is exactly what the Eilenberg bound needs inside a fibre.

**The estimate in one line.**  For `a`, `b` in one fibre, `P (f b) = P (f a)`, so the approximation
gives `‖P (A (b - a))‖ ≤ ‖P‖ ε ‖b - a‖`: the chord is *almost* in the kernel of `P ∘ A`, though not
in it.  `R3` converts that into an actual kernel element `w` with `‖(b - a) - w‖ ≤ C ‖P (A (b-a))‖`,
`R2` says `A w = 0`, and therefore `‖A (b - a)‖ ≤ ‖A‖ C ‖P‖ ε ‖b - a‖`.  Feeding this back into the
approximation bounds `‖f b - f a‖`, and applying `Q` gives the constant
`‖Q‖ (1 + ‖A‖ C ‖P‖)`, which **does not depend on `ε`**.

That independence is the whole point: the `ε → 0` limit of the Eilenberg argument uses a different
approximating partition at every scale, so a constant that grew with the partition would be
useless.

No inner product, no measure, no completeness and no finite-dimensionality is used by `R4` itself;
the hypotheses are exactly the conclusions of `R2` and `R3` for the linear model, and
`exists_lipschitzOnWith_fibre` records what they combine to on a rank stratum.
-/
````

Original comment 306, line 65:

````lean
/-- **`R4`: the tangential small-Lipschitz estimate.**  If the linear model `A` dies on the kernel
of `P ∘ A` — the conclusion of `R2` — and vectors almost annihilated by `P ∘ A` are close to that
kernel with constant `C` — the conclusion of `R3` — then on every fibre of `P ∘ f` the projected map
`Q ∘ f` is Lipschitz with constant proportional to the approximation parameter `ε`.

The constant `c = ‖Q‖ (1 + ‖A‖ C ‖P‖)` depends only on the linear data, **never on `ε`, on `f`, on
`S` or on the fibre**, which is what makes it usable in the `ε → 0` limit.

`f` is an arbitrary function, `S` an arbitrary set, and no finite-dimensionality, inner product,
measurability or completeness is assumed.  This is the **explicit-constant** form; the route's
existential statement is `exists_lipschitzOnWith_of_ker_bound` just below. -/
````

Original comment 307, line 86:

````lean
-- `R3` replaces it by an honest kernel element, and `R2` kills the linear model there
````

Original comment 308, line 108:

````lean
/-- **`R4`: the tangential small-Lipschitz estimate, existential form.**  The route's statement;
the constant supplied by `lipschitzOnWith_of_ker_bound` is `‖Q‖ (1 + ‖A‖ C ‖P‖)`, which depends
only on the linear data and **never on `ε`, on `f`, on `S` or on the fibre**.  The explicit form is
what a per-stratum assembly needs, because the approximating partition produces a different linear
model on every piece and the constant has to be uniform over them. -/
````

Original comment 309, line 131:

````lean
/-- **What `R2`, `R3` and `R4` combine to on a rank stratum.**  If `P ∘ A` is surjective onto a
space of the same dimension as the range of `A` — the situation at a point of the rank stratum, with
`P` the projection onto the range of the differential — then the two hypotheses of `R4` are
available, and the projected map is `c ε`-Lipschitz along every fibre of `P ∘ f`.

This is a **corollary of the three proved obligations, not a new one**, and in particular it is
**not** `R7`: it says nothing about measures, slices or Hausdorff dimension, and the approximating
partition that would supply `f` and `S` is not constructed here. -/
````

### `formalization/FunctionalInequalities/Analysis/Vector/RankDeficient/TargetSplitFubini.lean`

Original comment 310, line 5:

````lean
/-! # Fubini across an orthogonal splitting of the target

Obligation `R6` of the rank-deficient route recorded in
`research/decisions/2026-09-17-rank-deficient-route.md` and stated in
`research/audits/RankDeficientRouteStatements.lean`.  **Only `R6` is proved here**; with `R1`, `R2`
of `Analysis/Vector/RankDeficient/Stratification.lean`, `R3` of `Analysis/Vector/RankDeficient/RightInverseBound.lean` and `R4` of
`Analysis/Vector/RankDeficient/TangentialLipschitz.lean` that is five of the route's obligations.  `R0`, `R5`,
`R7`–`R10`, `N1` and `N2` remain open, and so does the rank-deficient part of the codimension-`m`
coarea critical set.  Nothing here is a coarea formula, a slicing statement or a Sard theorem.

**What `R6` is for.**  The route slices twice: first in codimension `r` by the regular component
`P ∘ u`, then in codimension `m − r` by `Q ∘ u` inside each fibre.  What that produces is "for
almost every `s ∈ W₁`, for almost every `τ ∈ W₁ᗮ`", while the conclusion has to be about almost
every `t ∈ W`.  `R6` is the bookkeeping that joins the two levels.

**It is bookkeeping, but it was not available.**  Mathlib supplies every part —
`LinearIsometryEquiv.measurePreserving`, `WithLp.volume_preserving_toLp` and `Measure.prod_apply` —
and this module only assembles them.  The splitting is presented abstractly, as a linear isometry
onto `WithLp 2 (W₁ × W₂)`, so that the caller decides how to produce it; for an orthogonal
complement `Submodule.orthogonalDecomposition` is exactly such an isometry.

No differentiability, no Hausdorff measure and no regularity appears: this is a statement about one
measurable set.
-/
````

Original comment 311, line 56:

````lean
/-- **`R6`: Fubini across an orthogonal splitting of the target.**  If almost every first-coordinate
slice of `N` is null, then `N` is null.

This is what turns the route's "for almost every `s`, for almost every `τ`" into "for almost every
`t`".  The splitting is an arbitrary linear isometry onto `WithLp 2 (W₁ × W₂)`; for the route it is
the orthogonal decomposition along the range of the differential. -/
````

### `formalization/FunctionalInequalities/Analysis/Vector/Slice/Critical.lean`

Original comment 312, line 202:

````lean
/-- **Codimension-`m` coarea when the derivative vanishes wherever it fails to be surjective.**
Under that hypothesis the critical set is exactly the vanishing-derivative set, whose slices are
null by the theorem above, so the regular-case formula extends to the whole space.

For `m = 1` the hypothesis is **automatic** — a real differential is surjective exactly when it is
nonzero — so this is the codimension-one `L11` in that case.  For `m ≥ 2` it is a genuine
restriction: it excludes intermediate ranks, and the rank-deficient part is **not** covered by
anything proved here. -/
````

### `formalization/FunctionalInequalities/Analysis/Whitney/Cover.lean`

Original comment 338, line 6:

````lean
/-!
# A quantitative Whitney ball cover

For a nonempty closed set `S`, use radius `min 1 (infDist x S) / 20`. Vitali extraction gives
disjoint small balls whose fivefold enlargements cover the complement. Eightfold closed balls
stay in the complement, are locally finite there, and have uniformly bounded overlap.

This is the geometric input to the compact-jet extension construction. It does not construct
a partition of unity or prove L6. All constants are explicit; no sharpness is asserted.
-/
````

### `formalization/FunctionalInequalities/Analysis/Whitney/Extension.lean`

Original comment 339, line 3:

````lean
/-!
# Boundary gluing for the compact first-order Whitney extension problem

This module starts the sufficiency direction of obligation L6. It proves the boundary step:
a candidate defined and differentiable off the compact set, with controlled value and derivative
errors relative to nearest-point affine jets, extends the prescribed jet as a globally C¹ map.

It does **not** construct that candidate. The quantitative covering, partition and affine-jet
estimates are supplied by `WhitneyCover`, `WhitneyBump`, `WhitneyPartition` and
`WhitneyConstruction`. The last module proves the full compact-set L6 extension theorem;
this module provides its boundary step. `FirstOrderJet` supplies the necessity direction.
-/
````

Original comment 340, line 151:

````lean
/-- The boundary gluing criterion for L6. The hypotheses concern a candidate and a continuous
derivative field on the **complement** of the compact set, together with two quantitative
nearest-jet estimates. The conclusion includes the ambient derivative on `S`, even when `S`
has empty interior. `WhitneyConstruction` constructs such candidates in finite dimension. -/
````

Original comment 341, line 191:

````lean
/-- Reduction of L6 to a controlled C¹ function on the complement. The input `w` need not
agree with `f`, be continuous, or have the prescribed derivative on `S`. The extension is
constructed by replacing its values on `S` with `f`; boundary gluing proves it is globally C¹.
Existence of such a controlled `w` is proved separately in `WhitneyConstruction`; it is an
explicit hypothesis of this boundary-gluing theorem. -/
````

### `formalization/FunctionalInequalities/Analysis/Whitney/FirstOrderJet.lean`

Original comment 342, line 6:

````lean
/-! # The first-order jet condition of the Whitney extension problem

Obligation `L6` of the weighted coarea route asks for the converse of what is proved here: that a
compatible first-order jet `(f, F)` on a compact set extends to a globally `C¹` function with
exactly those values and derivatives.  **`L6` itself is not proved in this module**, and the pinned
Mathlib contains no Whitney extension theorem — only the unrelated `WhitneyEmbedding` for manifolds
and `Continuous.exists_contDiff_approx_and_eqOn`, which requires the function to be `C^n` on a
whole *neighbourhood* of the closed set and therefore cannot start from jet data on the set alone.

What is proved here is that `L6`'s hypothesis is **necessary**, so the jet condition it assumes is
exactly the right one: if some globally `C¹` function realizes the jet on a compact `S`, then the
uniform first-order remainder estimate

`∀ ε > 0, ∃ δ > 0, ∀ x y ∈ S, ‖y - x‖ < δ → ‖f y - f x - F x (y - x)‖ ≤ ε ‖y - x‖`

holds.  Together with `L6` this makes the estimate a characterization, and it is the exact
interface between `L6a` — which must *produce* this estimate on compact pieces of a Lipschitz
function — and `L6`, which *consumes* it.

The proof is the mean value inequality along segments.  Compactness enters twice: it makes the
closed unit thickening of `S` compact in a finite-dimensional space, so the continuous derivative
is *uniformly* continuous there, and it lets the segment between two nearby points of `S` stay
inside that thickening.  Neither `f` nor `F` is assumed continuous: their behaviour on `S` is
forced by the realizing function.
-/
````

Original comment 343, line 43:

````lean
/-- **The first-order jet condition of `L6` is necessary.**  If a globally `C¹` function realizes
the values `f` and the derivatives `F` on a compact set `S`, then the uniform first-order remainder
estimate of `L6` holds on `S`.

`L6` is the converse — that the estimate suffices to build such a function — and is **not** proved
here. -/
````

### `formalization/FunctionalInequalities/Energy/Cheeger/Identification.lean`

Original comment 344, line 101:

````lean
-- The type is the one fixed by the statement round; `CompleteSpace E` is part of the frozen
````

Original comment 645, line 102:

````lean
-- signature, so the linter is silenced instead of the signature changed.
````

### `formalization/FunctionalInequalities/Energy/DualNorm.lean`

Original comment 348, line 6:

````lean
/-!
# The `H^{-1}` dual energy norm

Letwin, arXiv:2607.24164v1, (2.19): for a probability law `μ` and `q ∈ L²(μ)`,
`‖q‖_{H^{-1}(μ)} = sup { ∫ q f dμ : f locally Lipschitz, ∫ ‖∇f‖² dμ ≤ 1 }`. The supremum is taken as
an extended real over the full test class (no centering, smoothness or compact support); it is
identified with the real signed supremum only once finiteness is proved. Constant inputs have
infinite dual norm (constants are zero-energy tests). Proof bodies: Codex route (bundle
`Letwin-A7`, independently accepted); statements and placement: Claude.
-/
````

### `formalization/FunctionalInequalities/Energy/Euclidean/LipschitzApproximation/Kernel.lean`

Original comment 353, line 4:

````lean
/-!
# LipschitzApproximation: Kernel

Responsibility split of the existing implementation. Public namespaces, mathematical scope
and proof bodies are preserved; later layers import their prerequisites.
-/
````

### `formalization/FunctionalInequalities/Energy/Euclidean/LipschitzApproximation/Measurable.lean`

Original comment 354, line 5:

````lean
/-!
# LipschitzApproximation: Measurable

Responsibility split of the existing implementation. Public namespaces, mathematical scope
and proof bodies are preserved; later layers import their prerequisites.
-/
````

### `formalization/FunctionalInequalities/Energy/Euclidean/Slope/Density.lean`

Original comment 360, line 3:

````lean
/-!
# Density of smooth tests in the local-slope energy

Source: the route recorded in `research/decisions/2026-09-19-energy-slope-route.md`, part `C`.
Read `SmoothGradient.relaxation_le_localSlope` (`C6`) for the main contract, then
`LocalSlope.measurable_apply` (`C1`), `LocalSlope.exists_patch` (`C2`, the McShane patch),
`SmoothGradient.relaxation_le_localSlope_of_lipschitzWith` (`C4`) and
`SmoothGradient.relaxation_le_localSlope_of_admissible` (`C5`).

## The argument

`C1`.  The local slope of a continuous function is the countable infimum, over the radii
`1 / (m + 1)`, of the secant suprema `LocalSlope.secant`, each of which is lower semicontinuous:
a witness `y` realizing a value above a threshold satisfies two strict inequalities, both of which
survive a small move of the base point, and the secant quotient is continuous there because the
witness is at positive distance.

`C2`, the McShane patch.  For a globally `L`-Lipschitz `f` the slope is stratified into bands of
width `α`; each band is cut by the balls of a dense sequence into pieces of diameter below the
radius witnessing the slope bound, and `disjointed` turns the countable family into a Borel
partition on which `f` is Lipschitz with a constant within `α` of its slope.  Inner regularity
replaces each piece by a compact core, finitely many of which already carry all but `δ` of the
mass.  The cores are pairwise disjoint compacts, so they have a common separation radius; `f` is
extended from each core by McShane with the core's own constant and the extensions are glued by
linear cutoffs at that scale.  At most one block is active at any point, which is what keeps the
global Lipschitz constant at `9 L + 8 α`, independently of `δ`.

`C4`.  Taking `α = δ = 1 / (n + 1)` the patches converge to `g` in `L²(ν)` — they differ from `g`
by at most `2 L + 2 α` and only outside a set of mass `δ` — and `B1` bounds the relaxation at each
patch by its asymptotic-Lipschitz energy, which a *measurable majorant* bounds by
`(1 + 4 α) · LocalSlope.energy ν g + 4 α + 4 α² + M² δ`.  No measurability of the asymptotic
Lipschitz constant is needed.  Lower semicontinuity of the relaxation finishes.

`C5`.  A general admissible test is cut off by the smooth bump `scaled (n + 1)`; `B2` and `B3`
make the cutoff globally Lipschitz, dominated convergence gives `L²` convergence, and `B5` with
Young's inequality bounds the energy of the cutoff.  `C6` feeds `C5` to
`LocalSlope.le_relaxation_of_lowerSemicontinuous`.

Closest literature: S. Eriksson-Bique, *Density of Lipschitz functions in energy*, Calc. Var. PDE
62 (2023), Art. 60, Thm 1.1, of which this Euclidean argument is an elementary special case.
-/
````

### `formalization/FunctionalInequalities/Energy/Euclidean/Slope/Recovery.lean`

Original comment 370, line 4:

````lean
/-!
# Smooth recovery of a globally Lipschitz test, and the reduction tools

Source: the route recorded in `research/decisions/2026-09-19-energy-slope-route.md`, part `B`.
Read `SmoothGradient.relaxation_le_asymptoticLipschitz_of_lipschitzWith` (`B1`) for the main
contract, then the four reduction tools `locallyLipschitz_mul` (`B2`),
`exists_lipschitzWith_of_eq_zero_outside_ball` (`B3`), `AsymptoticLipschitz.apply_mul_le` (`B4`)
and `LocalSlope.apply_mul_le` (`B5`).

## What is proved

`B1`.  For a globally `K`-Lipschitz `g` the mollifications `g ⋆ ρ_R` of
`Energy/Euclidean/LipschitzApproximation/Kernel.lean` are `C^∞`, uniformly `K`-Lipschitz, converge to
`g` uniformly (hence in `L²(ν)` for every probability law `ν`), and satisfy the pointwise bound
`limsup_{R → 0} ‖∇(g ⋆ ρ_R)(x)‖ ≤ Lip_a g (x)`: the mollification at `x` sees `g` only within
`2R`, so on the ball of radius `δ` it inherits the Lipschitz constant of `g` on the ball of
radius `δ + 2R`, and every constant strictly above `Lip_a g (x)` is such a constant for a small
enough radius.  The uniform bound `K²` makes reverse Fatou (`MeasureTheory.limsup_lintegral_le`)
applicable, so the mollifications form an approximating sequence of smooth tests whose limiting
energy is at most the asymptotic-Lipschitz energy of `g`.

`B2`–`B5` are the reduction tools that turn a general test into a globally Lipschitz one:
a locally Lipschitz function times a bounded globally Lipschitz one is locally Lipschitz; a
locally Lipschitz function vanishing outside a ball is globally Lipschitz; and the one-moving-
point Leibniz bounds for the asymptotic Lipschitz constant and for the local slope.

## What is not proved here

No density statement: the mollification radius is uniform in `x`, which is genuinely insufficient
for a general locally Lipschitz test (the diagnostic `D1` of the route file).  The density
argument is `Energy/Euclidean/Slope/Density.lean`.
-/
````

Original comment 371, line 192:

````lean
/-! ### `B2`, `B3` — the two Lipschitz reduction tools -/
````

Original comment 372, line 199:

````lean
/-- `B2`.  A locally Lipschitz function times a bounded globally Lipschitz one is locally
Lipschitz. -/
````

Original comment 373, line 250:

````lean
/-- `B3`.  A locally Lipschitz function vanishing outside a ball is globally Lipschitz. -/
````

Original comment 374, line 304:

````lean
/-! ### `B4`, `B5` — the one-moving-point Leibniz bounds -/
````

Original comment 375, line 313:

````lean
/-- `B4`.  Multiplying by a bounded `N`-Lipschitz factor costs at most `|g x| · N` in the
asymptotic Lipschitz constant. -/
````

Original comment 376, line 401:

````lean
/-- `B5`.  Multiplying by a bounded `N`-Lipschitz factor costs at most `|g x| · N` in the local
slope.  Here the moving point is only `y`, so no correction in the radius is needed. -/
````

Original comment 377, line 452:

````lean
/-! ### `B1` — smooth recovery of a globally Lipschitz test -/
````

Original comment 378, line 555:

````lean
/-- `B1`.  The smooth-gradient relaxation of a globally Lipschitz test is at most its
asymptotic-Lipschitz energy.  The recovery sequence is the mollification at radius `2 / (j + 1)`;
the global Lipschitz constant dominates the integrands uniformly, so reverse Fatou converts the
pointwise bound `limsup ‖∇(g ⋆ ρ_R)(x)‖ ≤ Lip_a g (x)` into the energy bound. -/
````

### `formalization/FunctionalInequalities/Energy/LocalSlope/Gradient.lean`

Original comment 648, line 4:

````lean
/-!
# Local metric slope and the canonical Hilbert gradient

Five proved interfaces for `thm:smooth-lipschitz-constant-equivalence`.
Source: the existing `Energy.LocalSlope.apply` definition and Blueprint shared analytic bridges.
Read the pointwise identity first, then its almost-everywhere consequence, extended energy
identity, finite-energy domain characterization, and the real-integral form of the energy
(`energy_eq_integral_gradient`, moved here from `Poincare/LipschitzGradient/Comparison.lean` by
LD-013, statement and proof unchanged). All five proofs are complete.
Proof acceptance: `research/decisions/2026-09-06-smooth-literature-proofs.md`.
The earlier statement handoff remains a historical scope record.

The pointwise result needs only differentiability at the point and includes the zero space.
For locally Lipschitz tests, absolute continuity transfers the proved Rademacher statement
from a Haar reference measure to the probability law. Energy equality allows infinity;
only the admissibility characterization adds L2 membership. No factor of one half is used.
These declarations do not redefine the target, slope, gradient or admissibility predicate.
-/
````

### `formalization/FunctionalInequalities/KLS/BKL/GaussianTaylor.lean`

Original comment 383, line 6:

````lean
/-!
# Nonvacuity of BKL Theorem 3.1: the standard Gaussian on `ℝ¹`

Bizeul–Klartag–Lehec (arXiv:2610.05474v1), Theorem 3.1, is formalized as
`KLS.RegularPotential.poincare_le_of_taylor` (`KLS/BKL/PoissonIterate/Criterion.lean`). This
module shows that its hypotheses are jointly satisfiable in positive dimension: for the standard
Gaussian `γ = volume.tilted (-‖·‖²/2)` on `ℝ¹ = EuclideanSpace ℝ (Fin 1)` every hypothesis is
discharged, with the explicit Taylor constant `R = 8`.

## What is proved

For every finite-dimensional real inner product space `E`:

* `regularPotential_half_norm_sq`: `‖x‖²/2` is a regular potential (BKL (12)) with `a = b = 1`
  (temperate growth, Hessian form exactly `‖v‖²`);
* `integral_exp_inner_tilted_half_norm_sq`: the moment generating function
  `∫ e^{⟪z, x⟫} dγ = e^{‖z‖²/2}`, from Mathlib's complex Gaussian integral;
* `integral_id_tilted_half_norm_sq` and `integral_inner_sq_tilted_half_norm_sq`: `γ` is centered
  and `∫ ⟪v, x⟫² dγ = ‖v‖²`, the first two derivatives of the moment generating function at `0`.

On `ℝ¹`:

* `norm_iteratedFDeriv_exp_neg_half_norm_sq_le`: `‖∇^j e^{-‖z‖²/2}(0)‖ ≤ j!`, through the Hermite
  polynomials (`d^j/dt^j e^{-t²/2} = (-1)^j He_j(t) e^{-t²/2}`, `|He_j(0)| ≤ (j-1)!!`);
* `norm_iteratedFDeriv_integral_exp_inner_smul_tilted_half_norm_sq_le`: the numerator
  `N(z) = ∫ e^{⟪z, x⟫} f(x) dγ` has `‖∇^k N(0)‖ ≤ 4 k! ‖f‖_{L²(γ)}`;
* `norm_taylorTensor_tilted_half_norm_sq_le`: `‖T_d f‖ ≤ 4 (d + 1) ‖f‖_{L²(γ)}` (operator norm);
* `norm_coordTensor_taylorTensor_tilted_half_norm_sq_le`: (29) with `R = 8` in the
  Hilbert–Schmidt norm of the standard basis;
* `gaussian_taylor_hypotheses` and `gaussian_poincare_le_of_taylor_witness`: all hypotheses of
  Theorem 3.1 for `n = 1`, `V = ‖·‖²/2`, `a = b = 1`, `R = 8`, and its conclusion
  `C_P(γ) ≤ K · 8²` obtained from the library theorem.

## The argument

By the moment generating function, `F_f(z) = e^{-‖z‖²/2} N(z)` (`tiltAverage_eq_mul`). The
derivatives of `N` at `0` are the moments `∫ f ∏ ⟪x, h_j⟫ dγ`
(`iteratedFDeriv_integral_exp_inner_smul`); with `‖x‖^k ≤ k! e^{‖x‖}` and Cauchy–Schwarz they are
at most `k! ‖e^{‖x‖}‖_{L²(γ)} ‖f‖₂`, and in dimension one `e^{2‖x‖} ≤ e^{2x₁} + e^{-2x₁}` gives
`∫ e^{2‖x‖} dγ ≤ 2e² ≤ 16`. The Leibniz rule with `binom(d, i) i! (d-i)! = d!` gives
`‖∇^d F_f(0)‖ ≤ 4 (d + 1) d! ‖f‖₂`, hence `‖T_d f‖ ≤ 4 (d + 1) ‖f‖₂ ≤ 8^d ‖f‖₂` for `d ≥ 1`; in
dimension one the coefficient array has one entry, so its norm is at most the operator norm.

## What this is not

The constant `R = 8` is not optimized (the sharp bound is `‖T_d f‖ ≤ ‖f‖₂ / √(d!)`, by Hermite
orthogonality). The Taylor bound is proved only on `ℝ¹`: the moment bound `∫ e^{2‖x‖} dγ ≤ 16`
is dimension-dependent, and no dimension-free instance of (29) is claimed. The witness is a
nonvacuity check of the hypotheses of Theorem 3.1; it gives no new information on the Gaussian
(whose Poincaré constant is `1` by Bakry–Émery) and is not a step towards the KLS bound.

Placement: `KLS/LogConcave/` next to `Regular.lean`, whose `RegularPotential` structure and law it
instantiates; it consumes `PoissonIterate/Criterion.lean` and is not imported by the route.
-/
````

### `formalization/FunctionalInequalities/KLS/BKL/LocalThirdCumulant.lean`

Original comment 384, line 6:

````lean
/-!
# BKL Lemma 4.2 in its source scope, conditional on the Letwin bound

Bizeul–Klartag–Lehec arXiv:2610.05474v1, Lemma 4.2 and the base of the Section 4 induction. For an
isotropic log-concave law, Borell gives some positive exponential radius (not every exponential moment);
with the Letwin quadratic-form bound
(Letwin Theorem 1.2, an explicit hypothesis) the third cumulants satisfy `∑_{jk} κ₃(u,e_j,e_k)² ≤ 8‖u‖²`.
If this holds for all isotropic log-concave laws in positive dimension, `CumulantBound 2 8` follows.
The older statement in `Analysis/BakryEmery/Cumulant/Basic.lean` assumes all exponential moments, which
general log-concave laws (e.g. Laplace) do not have; this module is the source-faithful version.
The full noncompact Letwin hypothesis remains open. The separately proved Theorem 4.1 uses the
compact Letwin theorem and cutoff induction; it does not discharge this module's full hypothesis
or construct the uncut Eldan process. Proof bodies: Codex route (bundle
`Local-Third-Cumulant`, independently accepted); statements and placement: Claude.
-/
````

### `formalization/FunctionalInequalities/KLS/BKL/Posterior/Covariance.lean`

Original comment 389, line 65:

````lean
/-- The canonical inverse `Ring.inverse (Cov μ_{c,Q})` is a two-sided, self-adjoint, strictly positive inverse
(Codex root reviewer of the Posterior-Covariance-Domain bundle). -/
````

### `formalization/FunctionalInequalities/KLS/BKL/Posterior/Response.lean`

Original comment 390, line 3:

````lean
/-!
# Initial parameter response of the BKL posterior for isotropic priors

Bizeul–Klartag–Lehec arXiv:2610.05474v1, p. 19: at the initial parameters `c = Q = 0` of the
localization (67), the response of a linear statistic of a compactly supported isotropic prior to the
linear parameter is the isotropic covariance pairing. This is the deterministic first variation only;
the stochastic equations (67)–(71) are not constructed. Proof bodies: Codex q_batch bundle
`Posterior-Parameter-Calculus` (independently accepted); statements and placement: Claude.
-/
````

### `formalization/FunctionalInequalities/KLS/BKL/Proposition71.lean`

Original comment 391, line 12:

````lean
/-!
# BKL Proposition 7.1: the Taylor-coefficient bound from cumulant bounds

Bizeul–Klartag–Lehec (arXiv:2610.05474v1), Proposition 7.1, pp. 28–30. Under the hypothesis
`CumulantBound d b` (`R^ν_{d+1} ≤ b Id` for every isotropic log-concave `ν` in every dimension),
every isotropic regular law `μ` satisfies (113), `|T_d f|² ≤ b/(d!)²`, for `f ∈ C² ∩ L²(μ)` with
bounded Hessian normalized by (108) — proved through the suspension `(S, X₁, …, X_N)` with `N`
chosen by (110) for each `β`, then `β → ∞`. Then (113) extends by density to every `f ∈ L²(μ)` orthogonal to the affine
functions (`norm_coordTensor_taylorTensor_sq_le_of_orthogonal`). Finally the assembly (107),
`norm_coordTensor_taylorTensor_sq_le_two_mul`, is Proposition 7.1 in the source form (conditional on
its hypothesis `CumulantBound`). Nothing here is Theorem 4.1 or Theorem 1.1.

Provenance: Codex proof (`build/reviews/2026-10-07-bkl-continuous/reviews/P71-R7-assembly/
R7-EXACT-PROPOSAL.lean`, exact frozen statement `P71-R7`, root-independent strict replay), over the
production steps in `SuspensionLaw`, `SuspensionDensity`, `SuspensionCumulant`, `SuspensionMoments`
and `SuspensionDerivatives`; the Luna R7 attempts failed and are recorded.
-/
````

Original comment 392, line 36:

````lean
/-! Codex scratch assembly for exact frozen P71-R7. The scalar lemma is the independently
proved Codex beta-limit argument, using the integrated sigma identity. Actual R1, R2/R3,
original chosen-N R5c (112), R6 and the Fin coordinate adapter are consumed below. -/
````

Original comment 393, line 108:

````lean
/-- **BKL (113) for `f ∈ C²` with bounded Hessian satisfying (108)**: under `CumulantBound d b`, for an
isotropic regular law, `|T_d f|² ≤ b/(d!)²`. For each `β > 0` a copy number `N` is chosen by (110); the
joint law is isotropic and log-concave, (112) and the Hilbert–Schmidt step give
`(d!)²/σ_β² |T_d f|² ≤ b`, and `β → ∞` (Codex assembly, `reviews/P71-R7-assembly/`). -/
````

Original comment 394, line 160:

````lean
/-! Codex scratch proof for BKL p.30: actual smooth-infinity affine-orthogonal approximants.
Production affine projection proofs retain their own Luna/Codex provenance. The approximation
is derived from actual Mathlib smooth compact-support density, not assumed as a field. -/
````

Original comment 398, line 379:

````lean
/-- Exact source R8 endpoint: the normalized smooth estimate extends to the full affine-
orthogonal L2 subspace by actual smooth bounded-Hessian density and actual Taylor continuity. -/
````

### `formalization/FunctionalInequalities/KLS/BKL/SecondCumulant.lean`

Original comment 399, line 6:

````lean
/-!
# BKL Theorem 4.1, the second-cumulant base case

Bizeul–Klartag–Lehec arXiv:2610.05474v1, p. 18: for an isotropic log-concave law the second cumulant
is `R₂ = Id`, so the universal cumulant bound `CumulantBound 1 1` (the `(d+1) = 2` cumulant bound with
constant `1`) holds unconditionally in every dimension. This is the `m = 2` base of Theorem 4.1 only;
the all-order source certificate is registered separately (`thm:bkl-cumulant-bound`). Proof bodies: Codex route bundle
`Local-Second-Cumulant` (independently accepted); statements and placement: Claude.
-/
````

### `formalization/FunctionalInequalities/KLS/BKL/Suspension/Derivatives.lean`

Original comment 400, line 5:

````lean
/-!
# Derivatives of the logarithmic Laplace transform of the suspension (BKL (111), (112))

Bizeul–Klartag–Lehec (arXiv:2610.05474v1), proof of Proposition 7.1, p. 29. For a regular law
`μ = e^{-V}dx/Z`, `f ∈ C²` with bounded Hessian and `N` chosen by (110), the joint law `ν` of
`(S, X₁, …, X_N)` has a logarithmic Laplace transform `Λ_ν` that is smooth near `0`
(`exists_integrable_exp_norm_contDiffOn_logLaplace_jointLaw`) and factorizes
(`logLaplace_jointLaw_factorization`); differentiating the factorization along `e₀` at a point
with vanishing `S`-coordinate gives (111):
`∂_{e₀} Λ_ν(0, z₁, …, z_N) = (σ√N)⁻¹ Σ_i F_f(z_i)`.

The noise factor has zero derivative (`η_β` is centered) and each copy factor is differentiated
through the graph law `(f(x), x)_* μ`. Differentiating `d` more times along copy directions gives
(112), `cumulant_jointLaw_none_entries`: the mixed cumulants `κ^ν_{d+1}(e₀, e_{(i_k, j_k)})` vanish
unless all `i_k` coincide, and then equal `d!/(σ√N) · T_d f(e_{j_1}, …, e_{j_d})`. The helpers
(block selection, local slot calculus, spatial slice) are private to this boundary.

Provenance: Codex proofs (`build/reviews/2026-10-07-bkl-continuous/reviews/R4-FirstDerivative/` for
(111), exact frozen statement `P71-R4d`; `reviews/P71-source112/S112-ORIGINAL-R5C-PROOF.lean` for
(112), exact frozen statement `P71-R5c`), not Luna. The same derivative steps are
also available as the public lemmas `hasDerivAt_log_integral_exp_laplaceMeasure_zero` (Luna, R4a3),
`tiltAverage_inner_eq_fderiv_logLaplace_of_lt` (Luna, R4b2) and `hasDerivAt_log_integral_exp_copy`
(Luna, R4d1).
-/
````

Original comment 401, line 36:

````lean
/-! Codex reviewer scratch helper assembly. The frozen target below is unchanged;
all additional declarations are private lemmas. Production/API ownership remains with Claude/Luna. -/
````

Original comment 402, line 475:

````lean
/-! Codex scratch proof proposal: local symmetry and the mixed-derivative bridge in BKL (112).
The function is smooth on an open neighborhood, not on the whole ambient space. -/
````

Original comment 403, line 575:

````lean
/-! Codex scratch consumer body. Compile with the exact two preceding scratch helper contexts.
This is a genuine deduction of higher mixed derivatives from a separately proved first-derivative
germ; no mixed derivative identity is assumed. -/
````

Original comment 404, line 695:

````lean
/-! Codex scratch source consumer. The actual (111) proof context is copied unaltered from
q_batch's Production111.lean; the new higher derivative and factorial assembly are Codex.
This statement is BKL (112) for the original regular-law setting; no separate L2 premise is needed.
It does not assert Proposition 7.1's final operator inequality. -/
````

### `formalization/FunctionalInequalities/KLS/BKL/Suspension/Moments.lean`

Original comment 405, line 5:

````lean
/-!
# Second moments of the BKL suspension

Bizeul–Klartag–Lehec (arXiv:2610.05474v1), proof of Proposition 7.1, p. 28: for `f` satisfying
(108) and an isotropic centered `μ`, the coordinates of the joint law of `(S, X_1, …, X_N)` are
centered and uncorrelated with unit variance. This module proves the scalar pieces: the copy
statistic `F_N`, the suspension coordinate `S = (F_N + η)/σ_β`, and their cross moments with the
copies, and assembles them into the second moments and the isotropy of the joint law
(`isotropic_jointLaw`). Codex proofs (`build/reviews/2026-10-07-bkl-continuous/reviews/R1-*`,
`R1-joint-assembly/`).
-/
````

Original comment 406, line 240:

````lean
/-- **Second moments of the joint law** (BKL p. 28, isotropy from (108)): under the explicit Laplace
moment data, the joint law of `(S, X₁, …, X_N)` has finite second moment, mean `0` and identity
covariance. Codex proof (`reviews/R1-joint-assembly/`, independently accepted). -/
````

### `formalization/FunctionalInequalities/KLS/CEK/BoundedPrimal.lean`

Original comment 407, line 7:

````lean
/-!
# A normalized Lipschitz primal for a bounded isotropic source law

For a bundled isotropic probability law `μ` on a finite-dimensional real inner-product space (dimension zero included) and
`L : ℝ≥0` with `‖y‖ ≤ L` `μ`-almost everywhere, the CEK variational maximiser (`exists_variational_maximum`, Proposition 12)
capped to `closedBall 0 L` is again a maximiser: convex, lower semicontinuous, `μ`-integrable, with effective domain in the
ball, conjugate mass `1` and every competitor's functional at most its own (`bounded_source_cap_lsc`; the original interface
`bounded_source_cap`). It attains a real minimum and has a globally finite conjugate (`bounded_source_finite_conjugate`),
whose real representative `ψ` is convex, `L`-Lipschitz and continuous, with `exp(−ψ)` Bochner integrable, `∫ exp(−ψ) = 1`
and `weightedMeasure volume ψ` a probability measure (`bounded_source_lipschitz_primal`); consequences for the density
`exp(−ψ)` (Fenchel contact at the origin, Lipschitz envelope, positivity, midpoint log-concavity):
`bounded_source_real_density_client`. The source inputs are only `μ`, its isotropy, `L` and the almost-everywhere bound.

This is a weak normalized convex Lipschitz primal linked to the source law, a support toward the moment map of
Cordero-Erausquin–Klartag Theorem 2 and Letwin, arXiv:2607.24164v1, Lemmas 2.1–2.2. Not provided: the Euler–Lagrange
identification, the gradient pushforward `(∇ψ)_# e^{−ψ} = μ`, smoothness, a positive definite Hessian, the gradient
diffeomorphism, the Monge–Ampère equation, Letwin Theorem 2.5. Proof bodies: strong-API candidate (gpt-6-astra,
`api-bounded-primal-geometry-v11`, d77ddfc1…), verbatim up to the name `cap ↦ closedBallCap`; placement: Claude.
-/
````

### `formalization/FunctionalInequalities/KLS/CEK/Competitors.lean`

Original comment 649, line 6:

````lean
/-!
# CEK Proposition 12: reduction of every admissible competitor

Cordero-Erausquin–Klartag, *Moment measures* (arXiv:1304.0630v1), proof of Proposition 12: every admissible competitor
is reduced, up to epsilon, to a normalized convex one; a finite real ceiling over all admissible competitors and a
finite norm baseline bound the variational range.

Declaration blocks are verbatim from the root-accepted CEK Proposition 12 bundle (`independent-p12-attainment`, ACCEPTANCE 848aa45b…) under the reviewed rev3 migration map.
-/
````

### `formalization/FunctionalInequalities/KLS/CEK/MomentRegularity/WeakDerivative.lean`

Original comment 413, line 28:

````lean
/-- Actual source-law tensor: both original hw and hF inputs are produced;
all original R0 data and the weak/local-L2 tensor are retained. -/
````

### `formalization/FunctionalInequalities/KLS/CEK/VariationalMaximum.lean`

Original comment 650, line 8:

````lean
/-!
# CEK Proposition 12: variational attainment

Cordero-Erausquin–Klartag (arXiv:1304.0630v1), Proposition 12 (38): for a probability measure with finite first
moment, barycenter zero and full-dimensional support, a convex lower semicontinuous admissible potential with
Legendre exponential mass one maximizes the functional over every admissible competitor
(`exists_variational_maximum`). Not provided: essential continuity, the Euler–Lagrange identification, Theorem 2.

Declaration blocks are verbatim from the root-accepted CEK Proposition 12 bundle (`independent-p12-attainment`, ACCEPTANCE 848aa45b…) under the reviewed rev3 migration map.
-/
````

### `formalization/FunctionalInequalities/KLS/Geometry/Cheeger/Equality.lean`

Original comment 420, line 469:

````lean
-- The type is the one fixed by the statement round; `CompleteSpace E` became unused only because
````

Original comment 646, line 470:

````lean
-- the body is now a proof rather than a hole, so the linter is silenced instead of the signature
````

Original comment 647, line 471:

````lean
-- changed.
````

### `formalization/FunctionalInequalities/KLS/Geometry/Coarea/Isoperimetry.lean`

Original comment 422, line 3:

````lean
/-! # Weighted coarea for a `C¹` Lipschitz function

`Isoperimetry.lintegral_enorm_gradient_mul_eq_lintegral_levelSet` migrated here from
`KLS/WIP/CheegerInfimum.lean`, where it was a direct hole, with a **byte-identical `pp.all`
signature**: the same universe, the same seven instance arguments in the same order
(`CompleteSpace V` and `SecondCountableTopology V` included, although the proof uses neither), the
same implicit binders `u`, `K`, `g`, the same hypothesis names `hu`, `hK`, `hg`, and the same
conclusion.  Only its proof is new, and it no longer depends on `sorryAx`.  The module is free of
`sorry` and of transitive `sorryAx`.

The proof is `KLS.coarea_of_contDiff` (obligation `L11`) at `S = Set.univ`.  The `LipschitzWith`
hypothesis `hK` is **not used**: the declaration already assumes `ContDiff ℝ 1 u`, and `L11` needs
no Lipschitz bound.  `L11` in turn is `L9` on the open regular set glued to `L10` on the closed
critical set, over the Mathlib-only analytic layer of `Analysis/`.

The declaration keeps the `FunctionalInequalities.KLS.Isoperimetry` namespace because its published
name must not change, while the file sits under `KLS/Geometry/` beside the coarea layer it consumes;
`KLS/Geometry/Slice/Measurable.lean` made the same choice.

The formula here retains its original `C¹` and Lipschitz hypotheses. The more general
`Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet`, assuming only global Lipschitz
continuity, is proved separately in `LipschitzCoarea` from L12 and the compact-set Whitney
construction L6/L6a/L7. `LocallyLipschitzCoarea` proves the locally Lipschitz extension L13.
The sharp `C^(finrank)` `Analysis.sard` is proved in `Analysis/Sard/Sharp.lean`; the former
`KLS/WIP/AnalyticPrerequisites.lean` is deleted. -/
````

### `formalization/FunctionalInequalities/KLS/Geometry/Coarea/Lipschitz.lean`

Original comment 423, line 4:

````lean
/-! # Weighted coarea for Lipschitz functions

L12: the exact C¹ pieces from L7 carry the C¹ formula L11. Countable additivity sums the
pieces; null slicing L2 removes their ambient-null complement from almost every level.
No boundedness, finite-volume, integrability, positive-dimension, or SFinite surface-measure
assumption is imposed. The ENNReal weight may be identically infinity.

The original entry point `Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet` (`T2`)
migrated here at the end of this file from `KLS/WIP/AnalyticPrerequisites.lean`, where it was a
direct hole, with a **byte-identical `pp.all` signature**: the same universe, the same six
instance arguments in the same order, the same implicit binders `u`, `K`, `g`, the same
hypothesis names `hu`, `hg`, and the same conclusion.  Only its proof is new, and it no longer
depends on `sorryAx`.  It is `L12` at `S = Set.univ`; the coarea theorem is not reproved and no
compatibility alias is introduced.  It keeps the `FunctionalInequalities.Analysis` namespace
because its published name must not change, exactly as `KLS/Geometry/Slice/Measurable.lean`
and `KLS/Geometry/Coarea/Isoperimetry.lean` did for their own migrations.

**This closes neither the sharp `C^(finrank)` `Analysis.sard` nor its consequence
`Analysis.ae_forall_fderiv_ne_zero`, which keep their statements, proofs and holes.**
-/
````

Original comment 424, line 34:

````lean
/-- **L12**: weighted Lipschitz coarea, including almost-everywhere slice measurability. -/
````

### `formalization/FunctionalInequalities/KLS/Geometry/Coarea/LocallyLipschitz.lean`

Original comment 425, line 3:

````lean
/-! # Weighted coarea for locally Lipschitz functions

`L13`: the weighted coarea formula and slice `AEMeasurable` with **no global Lipschitz bound and no
global modulus of any kind** — only `LocallyLipschitz u`.  This is a common generalization of the
two results it is built from: `LipschitzWith K u → LocallyLipschitz u` gives back `L12`
(`coarea_of_lipschitz`), and `ContDiff ℝ 1 u → LocallyLipschitz u` gives back the hypothesis of
`L11` (`coarea_of_contDiff`), so neither a Lipschitz constant nor `C¹` regularity is needed any
more.  Both original theorems keep their statements; nothing is restated through this one.

The reduction is by half-open annuli.  A finite-dimensional real normed space is proper, so `u` is
Lipschitz on each closed ball; McShane's extension replaces it there by a **globally** Lipschitz
`v k`, and `L12` applies to `v k` on the piece `S ∩ (ball 0 (k+1) \ ball 0 k)`.  Each piece is
contained in the **open** ball, where `u` and `v k` agree on a neighbourhood of every point, so the
gradients agree pointwise and the level sets of `u` and `v k` cut each piece identically.  Countable
additivity over the disjoint pieces then assembles both conclusions; the sum is exchanged with the
outer integral by `lintegral_tsum`, whose hypothesis is exactly the per-piece `AEMeasurable` that
`L12` supplies.

No boundedness, finite-volume, integrability, positive-dimension or `SFinite` surface-measure
assumption is imposed, the set `S` is an arbitrary measurable set, and the `ℝ≥0∞` weight may be
identically infinity.
-/
````

Original comment 426, line 35:

````lean
/-- **L13**: weighted coarea for a locally Lipschitz function, including almost-everywhere slice
measurability.  No global Lipschitz constant and no `C¹` regularity is assumed. -/
````

Original comment 427, line 94:

````lean
-- `L12` on each piece, transported back to `u`.
````

### `formalization/FunctionalInequalities/KLS/Geometry/Coarea/Regular.lean`

Original comment 428, line 6:

````lean
/-! # Weighted coarea on regular open C¹ domains (L9)

`KLS.coarea_of_contDiffOn_of_fderiv_ne_zero` proves both weighted slice measurability and
coarea for arbitrary Borel `S ⊆ O`, arbitrary measurable ENNReal weights, and every dimension.
The gradient and normalized Hausdorff surface measure are the existing repository definitions.

The local calculation uses the measure-preserving orthogonal splitting from
`SubgraphDivergence`, proved via `WithLp 2`, followed by the one-dimensional specialization of
Mathlib's Jacobian theorem on each vertical fiber. Tonelli gives the ambient integral. The identity
`abs_deriv_mul_norm_gradient` matches its density with the graph area density, entirely by
multiplication, including infinite weights. Only volume measures enter the Tonelli steps.

`LocalInverse` and `RegularChart` retain the level parameter in a joint C¹ inverse. An interior
bump gives a global representative of its height on a smaller parameter ball, where the global
graph-area theorem applies. Separately, a local representative of `u` on a ball allows this
calculation with no regularity outside `O`. Neither representative is a global extension of all
of `O`. Second countability and disjoint Borel pieces assemble the final equality; weighted
slice measurability is established independently in `OpenSliceMeasurable`.

This proves only the regular-domain result L9. It does not use critical slicing, Sard, WIP,
or Whitney extension, and does not migrate any existing coarea hole.
-/
````

Original comment 429, line 237:

````lean
/-- **L9: weighted coarea on a regular open C¹ domain**, including a.e. measurability
of the weighted slices. All weights in ENNReal and all dimensions are covered. -/
````

### `formalization/FunctionalInequalities/KLS/Geometry/Coarea/Smooth.lean`

Original comment 430, line 4:

````lean
/-! # Weighted coarea for an arbitrary `C¹` function

Obligation `L11` of the weighted coarea route: the regular-domain identity `L9` and the null
critical slices `L10` combine into the weighted coarea formula for **any** `C¹` real function on a
finite-dimensional inner-product space, over any measurable set and any measurable `ℝ≥0∞` weight.

No Lipschitz bound on `u`, no boundedness or finiteness of `S`, no integrability of `g`, and no
nondegeneracy assumption on the derivative: the critical set is allowed to be arbitrarily large.

The two halves meet exactly, and neither alone suffices.  The critical set
`C = {x | fderiv ℝ u x = 0}` is closed, so its complement `R` is open and `L9` applies to `R`,
which gives the identity for `S ∩ R`.  On the left the critical part contributes nothing because
`gradient u` vanishes there, so the ambient integral over `S` equals the one over `S ∩ R`.  On the
right `L10` makes the critical slice null at almost every level, so the slice integral over
`S ∩ {u = t}` agrees with the one over `(S ∩ R) ∩ {u = t}` for almost every `t`; that same almost
everywhere equality transports `L9`'s `AEMeasurable` component to the full slice function.

This module assumes `u` is `C¹`. `LipschitzCoarea` uses this theorem and the proved exact C¹
decomposition L7, built from the compact Whitney extension L6, to prove L12 for globally
Lipschitz functions and the original `Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet`
entry point. `LocallyLipschitzCoarea` further proves L13 for locally Lipschitz functions. -/
````

Original comment 431, line 48:

````lean
/-- **Weighted coarea for an arbitrary `C¹` function** (obligation `L11`), including almost
everywhere measurability of the weighted slices. -/
````

Original comment 432, line 59:

````lean
-- `L9` on the open regular part.
````

Original comment 433, line 64:

````lean
-- `L10`: the two slice integrands agree at almost every level.
````

### `formalization/FunctionalInequalities/KLS/Geometry/Slice/Critical.lean`

Original comment 449, line 4:

````lean
/-! # The critical part of a `C¹` function has null level slices

Obligation `L10` of the weighted coarea route: for a `C¹` real function on a finite-dimensional
inner-product space, almost every level meets the critical set `{x | fderiv ℝ u x = 0}` in a set of
zero `surfaceMeasure`.

This is **not** Sard's theorem and does not imply it.  Sard asserts that the *image* of the
critical set is Lebesgue-null in `ℝ`, which in high dimension needs regularity `C^(finrank)` and
remains an unproved obligation (`Analysis.sard`).  The statement here is about the codimension-one
measure of the critical *part of each slice*, and it holds for merely `C¹` functions in every
dimension.  A `C¹` function may well have a positive-measure set of critical values; the assertion
is only that the critical part of almost every slice is `ℋ^{n-1}`-null.

The proof is the first genuine consumer of the Eilenberg bound `L1`
(`KLS.exists_measurable_majorant`).  On the critical set the derivative vanishes, so Mathlib's
`exists_partition_approximatesLinearOn_of_hasFDerivWithinAt` — whose approximating linear maps are
values of the derivative — covers it by countably many **pairwise disjoint measurable** pieces on
which `u` is `ε`-Lipschitz, for any prescribed `ε > 0`.  Applying `L1` on each piece inside a ball
of radius `R` and summing gives a measurable majorant of the slice measure whose integral is at
most `eilenbergConstant V * ε * volume (closedBall 0 R)`.  Taking the pointwise infimum over
`ε = (k + 1)⁻¹` produces a measurable majorant of integral zero, so the slice measure vanishes
almost everywhere inside each ball, and a countable union over the radii removes the ball.

The critical set is closed because `fderiv ℝ u` is continuous, so no measurability hypothesis is
needed.  `u` is not assumed Lipschitz, bounded or proper, and `V` may be zero-dimensional. -/
````

Original comment 450, line 145:

````lean
/-- **The critical part of almost every level is null** (obligation `L10`).

Not Sard's theorem: nothing is claimed about the Lebesgue measure of the set of critical *values*,
which for a merely `C¹` function may well be positive. -/
````

### `formalization/FunctionalInequalities/KLS/Geometry/Slice/Measurable.lean`

Original comment 451, line 3:

````lean
/-! # Measurability of weighted level-set integrals

`Analysis.aemeasurable_lintegral_levelSet` migrated here from `KLS/WIP/AnalyticPrerequisites.lean`,
where it was a direct hole, with a **byte-identical `pp.all` signature**: the same universe, the
same six instance arguments in the same order (`CompleteSpace V` included, although the proof does
not use it), the same implicit binders `u`, `K`, `g`, the same hypothesis names `hu`, `hg`, and the
same conclusion.  Only its proof is new, and it no longer depends on `sorryAx`.  The module is free
of `sorry` and of transitive `sorryAx`.

The proof is `KLS.aemeasurable_setLIntegral_inter_levelSet` (obligation `L5` of the weighted coarea
route) at `S = Set.univ`, which is itself built from the measurable Eilenberg majorant (`L1`), null
slicing (`L2`), compact-slice measurability (`L3`) and the Borel version (`L4`) of
`Analysis/Hausdorff/SurfaceSlicing.lean` and `Analysis/Hausdorff/Content.lean`.  No parametric-integral
theorem is used, so the codimension-one surface measure is never assumed `SFinite`, which it is not
in positive dimension.

The declaration keeps the `FunctionalInequalities.Analysis` namespace because its published name
must not change, while the file sits under `KLS/Geometry/` because the statement names
`KLS.surfaceMeasure` and is therefore not part of the KLS-independent `Analysis/` layer; the
work-in-progress file it replaces made the same choice.

This module supplies measurability. The equality
`Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet` is proved separately in
`KLS/Geometry/Coarea/Lipschitz.lean`; `LocallyLipschitzCoarea` extends both conclusions to locally
Lipschitz functions. The sharp `C^(finrank)` `Analysis.sard` is proved in
`Analysis/Sard/Sharp.lean`; the former `KLS/WIP/AnalyticPrerequisites.lean` is deleted. -/
````

### `formalization/FunctionalInequalities/KLS/Geometry/Slice/OpenMeasurable.lean`

Original comment 452, line 4:

````lean
/-! # Measurability of weighted slices on an open C¹ domain

The measurability component of L9. No regular-point hypothesis is needed for this component.
Local C¹ representatives and disjoint Borel pieces reduce it to the Lipschitz-on-set result.
This module does not assert the coarea equality.
-/
````

### `formalization/FunctionalInequalities/KLS/IsotropicSupport.lean`

Original comment 453, line 4:

````lean
/-!
# Full affine support of isotropic laws

An isotropic law has identity covariance, hence an injective covariance operator and full affine
support. Light owner of this fact (the Section 2 reduction module restates it with heavier imports).
Proof body: Codex bkl bundle `Posterior-Covariance-Domain` (independently accepted); statement and
placement: Claude.
-/
````

### `formalization/FunctionalInequalities/KLS/LogConcave/BrascampLieb.lean`

Original comment 454, line 5:

````lean
/-!
# The scalar Brascamp–Lieb inequality for a given potential

Let `ν = m.tilted (−U)` be a log-concave probability law on a finite-dimensional real inner-product space (any dimension,
zero included), `m` an additive Haar measure, and let the Hessian of `U` be positive definite at every point (no uniform
lower bound). For a `C¹` test `f` in `L²(ν)`, not necessarily compactly supported:

* `scalar_brascamp_lieb_finite_energy` (`U ∈ C²`): if the energy `⟪∇f, H⁻¹∇f⟫` is integrable, then
  `Var_ν f ≤ ∫ ⟪∇f, H⁻¹∇f⟫ dν`;
* `scalar_brascamp_lieb_extended_energy` (`U ∈ C^∞`): with no energy premise,
  `ofReal (Var_ν f) ≤ ∫⁻ ofReal ⟪∇f, H⁻¹∇f⟫ dν`, the right side possibly infinite; `…_of_bounded` derives `L²` for bounded
  `f`.

Route: by Young, compact integration by parts and the ordinary-diffusion coercivity (`compact_variational_estimate`), the
centered class of `f` satisfies `2⟪f̄, w⟫ − ‖w‖² ≤ ∫ energy` on the compact smooth diffusion images `w`, which are dense in the
centered classes (`center_mem_closure_compactSmoothDiffusionImage`). This is the inequality of Letwin, arXiv:2607.24164v1,
Lemma A.6, for a GIVEN potential: the source moment map, its Euler–Lagrange identification, push-forward and regularity, and
therefore A.6 for the source law and Theorem 2.5, are not provided. Proof bodies: strong-API candidate (gpt-6-astra,
`api-scalar-bl-extended-gaussian-v5`, 394a24b1…; the finite-energy blocks from the accepted assembly-v2), verbatim with
their section variable contexts; the one-use Hilbert-closure and `L²`-pairing helpers are private here; placement: Claude.
-/
````

### `formalization/FunctionalInequalities/KLS/LogConcave/Density/BorellRepresentation/Basic.lean`

Original comment 457, line 9:

````lean
/-!
# BorellRepresentation: Basic

Responsibility split of the existing implementation. Public namespaces, mathematical scope
and proof bodies are preserved; later layers import their prerequisites.
-/
````

### `formalization/FunctionalInequalities/KLS/LogConcave/Density/BorellRepresentation/Construction.lean`

Original comment 458, line 5:

````lean
/-!
# BorellRepresentation: Construction

Responsibility split of the existing implementation. Public namespaces, mathematical scope
and proof bodies are preserved; later layers import their prerequisites.
-/
````

### `formalization/FunctionalInequalities/KLS/LogConcave/Density/BorellRepresentation/Moments.lean`

Original comment 459, line 5:

````lean
/-!
# BorellRepresentation: Moments

Responsibility split of the existing implementation. Public namespaces, mathematical scope
and proof bodies are preserved; later layers import their prerequisites.
-/
````

Original comment 460, line 248:

````lean
/-- **Quantitative Borell exponential moment**: if a ball of radius `R` carries mass `≥ 3/4`, then
`∫ e^{q‖v‖} dν ≤ 3^{3/4}/(1 − 3^{−1/4})` with the explicit rate `q = log 3/(4R)`; constants do not
depend on the law (BKL Section 2, p. 5, uniform moments of the regular approximation; Codex, bundle
`Borell-Uniform-Moments`). -/
````

### `formalization/FunctionalInequalities/KLS/LogConcave/Density/ConcaveTilt.lean`

Original comment 461, line 6:

````lean
/-!
# Concave tilts of log-concave laws

A continuous concave exponent `φ` with `∫ e^{φ} dμ < ∞` tilts a log-concave probability law to a
log-concave law: on the intrinsic affine support the Borell density is multiplied by the log-concave
weight `e^{φ}/Z`, and the result is pushed forward along the reconstruction isometry. Used for the BKL
posterior with `Q ≥ 0` (`KLS/BKL/PosteriorDomain.lean`). Proof bodies: Codex q_batch bundle
`Posterior-LogConcavity` (independently accepted); statements and placement: Claude.
-/
````

### `formalization/FunctionalInequalities/KLS/LogConcave/Density/GaussianSmoothing/Growth.lean`

Original comment 462, line 6:

````lean
/-!
# Polynomial growth of the derivatives of the Gaussian-smoothed potential

Bizeul–Klartag–Lehec arXiv:2610.05474v1, Section 2 (p. 5), regular approximation: every derivative
of `V_s = −log(ρ * γ_s)` has polynomial growth. Along an increment `u` at the base point `x`, the
smoothed density factors through the centered posterior `Q_x`:
`V_s(x+u) = V_s(x) + s‖u‖² − 2s⟪m_x − x, u⟫ − Λ_{Q_x}(2s·u)`, so `D^n V_s(x) = −(2s)^n D^n Λ_{Q_x}(0)`
for `n ≥ 3`. The centered posterior has all exponential moments (completing the square), its
Laplace derivatives at `0` are the moment tensors bounded by the uniform quantitative Borell moments
(`Posterior`), the local log-composition bound gives `‖D^n Λ_{Q_x}(0)‖ ≤ (n!)² D^n` with `D`
independent of `x`, and the temperate-growth constructor turns the uniform bounds of orders `≥ 3`
into `Function.HasTemperateGrowth`. Constants depend on `n`, the dimension and `s`; nothing here is
dimension-free. Quadratic regularization, whitening and the convergence of the approximation are
separate. Proof bodies: Codex q_batch (bundle `Gaussian-AllOrder-Growth`, independently accepted);
statements and placement: Claude.
-/
````

### `formalization/FunctionalInequalities/KLS/LogConcave/Density/GaussianSmoothing/Hessian.lean`

Original comment 463, line 6:

````lean
/-!
# Hessian of the Gaussian-smoothed potential

Bizeul–Klartag–Lehec arXiv:2610.05474v1, Section 2 (p. 5), regular approximation: the potential
`V_s = -log(ρ * γ_s)` of the Gaussian smoothing with kernel `e^{-s‖x-y‖²}` (variance `ε = 1/(2s)`)
satisfies `∇²V_s ≤ ε⁻¹ Id = 2s Id`. The proof goes through the Gaussian posterior
`P_x = μ.tilted (-s‖x-·‖²)`: along a line the smoothed density factors into a scalar Gaussian and
the moment generating function of the score `2s⟪y-x,v⟫`, whose cumulant generating function is
smooth on all of `ℝ` by completing the square, so

`∇²V_s(x)(v,v) = 2s‖v‖² − Var_{P_x}(2s⟪·-x,v⟫) = 2s‖v‖² − 4s² Var_{P_x}⟪·,v⟫`.

Nonnegativity of the variance gives the upper bound; convexity of `V_s` (Basic) gives the posterior
variance bound `Var_{P_x}⟪·,v⟫ ≤ ‖v‖²/(2s)` and finite second moments of `P_x`. Polynomial growth of
the higher derivatives and the covariance normalization of the regular approximation are not treated
here. Proof bodies: Codex (bundle `Gaussian-Hessian-Upper`, independently accepted); statements and
placement: Claude.
-/
````

### `formalization/FunctionalInequalities/KLS/LogConcave/Density/GaussianSmoothing/Moments.lean`

Original comment 464, line 12:

````lean
/-!
# Moments of the Gaussian noise and of the smoothed law

Bizeul–Klartag–Lehec arXiv:2610.05474v1, Section 2 (p. 5), regular approximation: the Gaussian
noise `γ_s` (kernel `e^{-s‖y‖²}`, variance `ε = 1/(2s)`) has mean zero and `∫⟪v,y⟫² = ‖v‖²/(2s)`;
the smoothed law `μ * γ_s` of a law with finite second moment keeps the mean and has covariance
`Cov μ + ε·Id`, with `∫‖y‖²` increased by `n ε`. As `s → ∞` the means, raw second moments and
covariance operators converge to those of `μ`. The weak convergence of the smoothed laws is in
`Approximation`. Proof bodies: Codex q_batch (bundle `Gaussian-Moments-Convergence`, independently
accepted); statements and placement: Claude.
-/
````

### `formalization/FunctionalInequalities/KLS/LogConcave/Density/GaussianSmoothing/Posterior.lean`

Original comment 466, line 5:

````lean
/-!
# Gaussian posterior of the smoothing and its uniform moments

Bizeul–Klartag–Lehec arXiv:2610.05474v1, Section 2 (p. 5), regular approximation. For a probability
law `μ` with a Borell density `ρ` and `s > 0`, the Gaussian posterior `P_x = μ.tilted (-s‖x-·‖²)` is
a log-concave probability law with density `ρ(y) e^{-s‖x-y‖²}/Z_x`; its centering `Q_x` has mean
zero, directional variances `≤ ‖v‖²/(2s)` (from the Hessian identity in `Hessian`) and trace
`≤ n/(2s)`. The quantitative Borell bounds (`BorellRepresentation.Moments`) then give exponential
and all-order moment bounds for `Q_x` with constants depending on `n`, `s` and the order only, not
on `x`. This is the moment input for the polynomial growth of the derivatives of the smoothed
potential, which is not treated here. Proof bodies: Codex (bundle `Gaussian-Posterior-Centered`,
quantitative Borell by root Codex, independently accepted); statements and placement: Claude.
-/
````

### `formalization/FunctionalInequalities/KLS/LogConcave/Density/GaussianSmoothing/Regular.lean`

Original comment 467, line 5:

````lean
/-!
# The regular approximation produces regular potentials

Bizeul–Klartag–Lehec arXiv:2610.05474v1, Section 2 (p. 5): smoothing a law with a Borell density by
the Gaussian of variance `ε = 1/(2s)` and then tilting by `e^{-δ‖x‖²/2}` yields the law of the
potential `V_s + δ/2‖·‖²`, which is regular in the sense of (12): smooth with polynomial growth of all
derivatives (`Growth`), convex, and `δ · Id ≤ ∇² ≤ (2s + δ) · Id` (`Hessian`). The two-step law is
identified exactly with `Probability.quadraticTiltLaw (smoothedProbabilityLaw μ s) δ` and is
log-concave. The approximation sequence, covariance normalization and the passage to the limit are
not treated here. Proof bodies: root Codex (bundle `Gaussian-Regular-Producer`, independently
accepted); statements and placement: Claude.
-/
````

### `formalization/FunctionalInequalities/KLS/LogConcave/Density/GaussianSmoothing/RegularApproximation.lean`

Original comment 468, line 8:

````lean
/-!
# The regular approximation: joint Gaussian-then-quadratic diagonal

Bizeul–Klartag–Lehec arXiv:2610.05474v1, Section 2 (p. 5): every probability law with a Borell
density and finite second moment is approximated by the laws of regular potentials
`V_{n+1} + δ_k/2‖·‖²` (Gaussian smoothing of variance `1/(2(n+1))`, then the quadratic tilt of rate
`δ_k = 1/(k+1)`), with curvature bounds `δ_k ≤ ∇² ≤ 2(n+1) + δ_k`. Along a diagonal `k n ≥ n`
selected in the metrizable product of the weak topology with the statistics, the laws converge
weakly and their means, raw second moments and covariance operators converge to those of the
law. Convergence of whitened laws and the limit of the Poincaré constants are separate (the
conditional transfer is in `KLS/LogConcave/Regular/Poincare.lean`). Proof bodies: Codex q (bundle
`Gaussian-Quadratic-Diagonal`, independently accepted); statements and placement: Claude.
-/
````

### `formalization/FunctionalInequalities/KLS/LogConcave/HeatSemigroup/Basic.lean`

Original comment 480, line 5:

````lean
/-!
# The heat semigroup of a log-concave law

This module specialises the abstract semigroup construction of `Analysis/Semigroup/` (route
`S1`–`S8`, all proved) to the repository's energy operator. For a full-dimensional compact-set
log-concave probability `ν` on a finite-dimensional Euclidean space `V`, a Haar measure `m` and a
weight `B : V →L[ℝ] V`, the closable weighted gradient
`T = hν.weightedOperator m B hi : L²(ν) →ₗ.[ℝ] L²(ν; V)` (`KLS/LogConcave/WeightedGradient/Basic.lean`,
`g ↦ B ∘ ∇g` on Lipschitz tests) has a closure `T̄`, closed and densely defined. Feeding `T̄` to
`FunctionalInequalities.Analysis.Semigroup.Generated.operator` gives

`P_t = HeatSemigroup.operator hν m B hi ht : L²(ν) →L[ℝ] L²(ν)`, formally `exp (-t T̄†T̄)`,

and every abstract law transfers by one `exact`: contraction, symmetry, `P_0 = 1`,
`P_{t+u} = P_t P_u`, strong continuity on `[0, ∞)`, and the generator identity
`(P_t f - f)/t → -T̄†T̄ f` on `D(T̄†T̄)`. The bridge to the energy is `inner_adjointComp_self_eq`:
`⟪T̄†T̄ f, f⟫ = ‖T̄ f‖²`, which by `weighted_relaxation_of_mem` is the sequential relaxation of
`‖B ∇g‖²`, the repository's closed energy. The intrinsic version for an arbitrary log-concave law
on any finite-dimensional Euclidean space is `HeatSemigroup.intrinsic`.

## What this is not

This closes **gap 1** of the Buser program recorded for
`thm:logconcave-cheeger-poincare-comparison` in `tasks.json` (generation of a symmetric contraction
semigroup from the closed energy form), for the concrete operator. It provides **no** Markov
property (positivity, `P_t 1 = 1`, `L^∞` contraction: gap 2), no Bakry–Émery `Γ`-calculus (gap 3),
no small-time heat estimate (gap 4), and no step of Buser's inequality; the node gains no progress
marker and the constant `π` is not approached. Nothing here uses log-concavity beyond the three
hypothesis lemmas that make the weighted gradient closable and densely defined.
-/
````

### `formalization/FunctionalInequalities/KLS/LogConcave/HeatSemigroup/Generator.lean`

Original comment 508, line 5:

````lean
/-!
# The generator on smooth compactly supported tests: `T̄†T̄ f = -ℒ f`

Route obligations `G0` and `G1` of `research/decisions/2026-09-20-bakry-emery-route.md`, for the
smooth-potential model with unit weight. Let `ν` be a full-dimensional log-concave probability law
on a finite-dimensional Euclidean space `V` whose measure is the tilted Haar measure
`m.tilted (-U)` for a `C¹` potential `U`, and let

`T̄ = hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi`

be the closed unit-weight gradient, so that the heat semigroup is `P_t = exp (-t T̄†T̄)`. For
`f ∈ C_c^∞(V)` and the weighted Laplacian `ℒ f = Δ f - ⟪∇U, ∇f⟫`
(`Analysis.BakryEmery.weightedLaplacian`):

* `G0`: `∫ ⟪∇f, ∇g⟫ dν = ∫ (-ℒf) g dν` for every `C¹` function `g`
  (`integral_inner_gradient_eq`);
* `G1`: `-ℒ f ∈ L²(ν)`, `[f] ∈ D(T̄†T̄)` and `T̄†T̄ [f] = [-ℒ f]`
  (`memLp_neg_weightedLaplacian`, `toLp_mem_adjointComp_domain`, `adjointComp_toLp_eq`).

The proof of `G1` goes through the adjoint, not through a pointwise computation. The weak identity
`⟪[-ℒf], [g]⟫ = ⟪[∇f], [∇g]⟫` is `G0` on smooth compactly supported `g`; by
`closure_domRestrict_eq_of_smoothCore_le` these classes are a graph-norm core of `T̄`, and
`Analysis.Semigroup.inner_eq_inner_closure_apply` extends the identity to every `x ∈ D(T̄)`. Then
`[∇f] = T̄ [f]` lies in `D(T̄†)` with `T̄† [∇f] = [-ℒf]` (`LinearPMap.adjoint_apply_eq`, using the
dense domain), which is exactly membership in `D(T̄†T̄)` and the value of `adjointComp`.

## What this is not

These are statements about individual test functions. They do **not** say that `C_c^∞(V)` is an
operator core of `T̄†T̄` (density in the graph norm of `T̄†T̄`), nor that the closure of `-ℒ` on
`C_c^∞` equals `T̄†T̄`; only the first of the four layers listed in the route record is proved. No
`Γ`, `Γ₂`, Bochner or gradient estimate, no statement about `P_t f` for `t > 0`, and no Buser
inequality is made. The hypothesis `(ν : Measure V) = m.tilted (-U)` is an explicit premise: it is
not derived here from log-concavity, and no convexity of `U` is used.
-/
````

Original comment 509, line 60:

````lean
/-- **`G0`, weighted integration by parts for the law `ν = m.tilted (-U)`**: for a `C²` compactly
supported `f` and a `C¹` function `g`, `∫ ⟪∇f, ∇g⟫ dν = ∫ (-ℒf) g dν`. -/
````

Original comment 510, line 71:

````lean
/-- The weighted Laplacian has zero mean: `∫ ℒf dν = 0` for `C²` compactly supported `f`. This is
`G0` against the constant test `g = 1`, and it is the infinitesimal form of the conservation of
integrals by the heat semigroup (`HeatSemigroup.integral`). -/
````

Original comment 511, line 97:

````lean
/-- `-ℒ f ∈ L²(ν)` for `f ∈ C_c^∞(V)` and a `C¹` potential: the integrability clause of `G1`. -/
````

Original comment 512, line 129:

````lean
/-- **The weak identity on the domain of `T̄`**: for `f ∈ C_c^∞(V)` and every `x ∈ D(T̄)`,
`⟪[-ℒf], x⟫ = ⟪[∇f], T̄ x⟫` in `L²(ν)`. On smooth compactly supported classes this is `G0`; it
extends to `D(T̄)` because those classes are a graph-norm core of `T̄`. -/
````

Original comment 513, line 188:

````lean
/-- **`G1`, domain clause**: for `f ∈ C_c^∞(V)`, the class `[f]` lies in `D(T̄†T̄)`. -/
````

Original comment 514, line 200:

````lean
/-- **`G1`, value clause**: for `f ∈ C_c^∞(V)`, `T̄†T̄ [f] = [-ℒ f]` with `ℒ f = Δ f - ⟪∇U, ∇f⟫`.
The generator of the heat semigroup `P_t = exp (-t T̄†T̄)` is therefore `ℒ` on smooth compactly
supported tests: `d/dt P_t f |_{t=0} = ℒ f`. -/
````

### `formalization/FunctionalInequalities/KLS/LogConcave/HeatSemigroup/Hessian.lean`

Original comment 515, line 5:

````lean
/-!
# The weak Hessian on the generator domain and the curvature form of (16)

Route obligation `O3` of `research/decisions/2026-10-07-bkl-operator-route.md`
(Bizeul–Klartag–Lehec, arXiv:2610.05474v1, eq. (16) and its use in Lemma 3.4), for the heat
model with unit weight. Let `ν = m.tilted (-U)` be a full-dimensional log-concave probability law
whose potential `U` has temperate growth and all exponential moments, let
`T̄ = hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi` be the closed gradient and
`A = T̄†T̄ = -ℒ`, and let `eᵢ = stdOrthonormalBasis ℝ V i`. For `F ∈ D(A)`:

* `compLp_innerSL_mem_closedWeightedOperator_domain`: every weak first derivative
  `∂ᵢ F = ⟪eᵢ, T̄ F⟫` lies in `D(T̄)`;
* `compLp_innerSL_closedWeightedOperator_comm`: the weak Hessian `⟪eⱼ, T̄ ∂ᵢ F⟫` is symmetric
  in `i, j`;
* `sum_norm_sq_closedWeightedOperator_add_le`: if `∇²U ≥ ρ` (any real `ρ`), then
  `Σᵢ ‖T̄ ∂ᵢ F‖² + ρ ‖T̄ F‖² ≤ ‖A F‖²`, the curvature form of (16) on `D(A)`.

## The argument

`C_c^∞(V)` is an operator core of `A` (`exists_seq_smooth_tendsto_adjointComp`): there are
`fₙ ∈ C_c^∞` with `[fₙ] → F` and `A [fₙ] → A F`. Since `‖T̄ u‖² = ⟪A u, u⟫` on `D(A)`, also
`T̄ [fₙ] → T̄ F`. For smooth compactly supported `f` the integrated Bochner inequality on the class
`𝒜` (`integral_hessianSq_add_le_of_hasTemperateGrowth`) reads, in `L²` norms,
`Σᵢ ‖T̄ [∂ᵢ f]‖² + ρ ‖T̄ [f]‖² ≤ ‖A [f]‖²`, because `Σᵢ ‖∇∂ᵢ f‖² = Σᵢ Σⱼ (∇²f(eᵢ, eⱼ))²`.
Applied to `fₙ - fₖ`, it shows that `T̄ [∂ᵢ fₙ]` is Cauchy, while
`[∂ᵢ fₙ] = ⟪eᵢ, T̄ [fₙ]⟫ → ⟪eᵢ, T̄ F⟫`; closedness of `T̄` gives `⟪eᵢ, T̄ F⟫ ∈ D(T̄)` with
`T̄ ⟪eᵢ, T̄ F⟫ = lim T̄ [∂ᵢ fₙ]`. Symmetry and the inequality pass to the limit from the
pointwise symmetry of second derivatives and the smooth inequality.

The membership statement assumes no curvature bound. The Cauchy step uses `∇²U ≥ 0`, which is
derived here from log-concavity: the continuous density `e^{-U} / Z` agrees `m`-a.e. with the
log-concave Borell representative of `ν`, which is continuous because `ν` has full support, so
the two agree everywhere and `U` is convex (`convexOn_of_eq_tilted`, `Density/Tilted.lean`).

## What this is not

No regularity of `F` beyond `D(A)` is claimed: the weak Hessian is the `L²` object
`T̄ ⟪eᵢ, T̄ F⟫`, not a classical second derivative, and nothing is said about the class `𝒜` or
Lemma 2.1 on `𝒜`. The Hessian square is taken in the fixed standard orthonormal basis; basis
independence is not proved. The identity form of (16) on `D(A)` is not stated.
-/
````

Original comment 516, line 261:

````lean
/-- **The approximation behind `O3`.** For `F ∈ D(A)` there are `fₙ ∈ C_c^∞` with
`T̄ [fₙ] → T̄ F`, `A [fₙ] → A F`, and, for every `i`, `⟪eᵢ, T̄ F⟫ ∈ D(T̄)` with
`T̄ [∂ᵢ fₙ] → T̄ ⟪eᵢ, T̄ F⟫`. -/
````

Original comment 517, line 344:

````lean
/-- **`O3`, weak first derivatives in the form domain.** For `ν = m.tilted (-U)` log-concave,
with `U` of temperate growth and all exponential moments, and `F ∈ D(A)`, every weak first
derivative `∂ᵢ F = ⟪eᵢ, T̄ F⟫` (standard orthonormal basis) lies in `D(T̄)`. No curvature bound
beyond the convexity of `U` implied by log-concavity is assumed. -/
````

Original comment 518, line 362:

````lean
/-- **`O3`, symmetry of the weak Hessian.** Under the hypotheses of
`compLp_innerSL_mem_closedWeightedOperator_domain`, `⟪eⱼ, T̄ ∂ᵢ F⟫ = ⟪eᵢ, T̄ ∂ⱼ F⟫` in `L²(ν)`. -/
````

Original comment 519, line 397:

````lean
/-- **`O3`, the curvature form of BKL (16) on `D(A)`.** Under the hypotheses of
`compLp_innerSL_mem_closedWeightedOperator_domain`, if `∇²U ≥ ρ` for a real `ρ`, then
`Σᵢ ‖T̄ ∂ᵢ F‖² + ρ ‖T̄ F‖² ≤ ‖A F‖²`. -/
````

### `formalization/FunctionalInequalities/KLS/LogConcave/HeatSemigroup/Range.lean`

Original comment 524, line 7:

````lean
/-!
# Density of compact smooth diffusion images in centered `L²`

For a log-concave probability law `ν = m.tilted (−U)` on a finite-dimensional real inner-product space, with `U` of class
`C¹` and `m` an additive Haar measure, the literal images `−L f` of compactly supported smooth `f` under the ordinary
weighted diffusion operator (`compactSmoothDiffusionImage`) are dense in the mean-zero real classes of `L²(ν)`: every
`g ∈ L²(ν)` with mean `0` lies in their closure (`centered_mem_closure_compactSmoothDiffusionImage`), and so does the
centering of every `g` (`center_mem_closure_compactSmoothDiffusionImage`). The class `g` is arbitrary (no operator-domain or
compact-test restriction). Route: the kernel of the closed weighted operator consists of constants, so the range of
`T†T` is dense in the centered classes, and every element of that range is approximated by the images of compactly
supported smooth functions. Supporting infrastructure for the finite-energy Brascamp–Lieb inequality of Letwin,
arXiv:2607.24164v1, Lemma A.6; not Brascamp–Lieb, A.6, the moment map or Theorem 2.5. Proof bodies: strong-API candidate
(gpt-6-astra, `api-centered-range-gaussian-compiler-v6`, 527e35ef…), verbatim.
-/
````

### `formalization/FunctionalInequalities/KLS/LogConcave/HessianStein.lean`

Original comment 527, line 11:

````lean
/-!
# The Hessian–Stein kernel of a normalized convex potential

Letwin, arXiv:2607.24164v1, Lemma 2.7, analytic part for a given potential. Let `φ` be smooth and
convex on `ℝⁿ` with `e^{-φ}` a probability density, `ν = e^{-φ}dx`, and `(∇φ)_* ν = μ` isotropic.
Then the entries of the Hessian matrix of `φ` are `ν`-integrable, and for a measurable left inverse `Ψ`
of `∇φ` the Hessian kernel `τ = ∇²φ ∘ Ψ` is a Stein kernel of `μ` (Definition 2.6) with integrable entries, a.e. symmetry,
positive semidefiniteness and mean `Id`; gradient injectivity (an explicit geometric prerequisite)
produces such a `Ψ`. The existence of the moment-map potential for an arbitrary law, strict positive
definiteness and the Hilbert–Schmidt `L²` bound (the rest of Lemma 2.7 and Theorem 2.5) remain
open. Proof bodies: Codex route (bundle `Hessian-Stein-Kernel`, independently accepted);
statements and placement: Claude.
-/
````

### `formalization/FunctionalInequalities/KLS/LogConcave/HessianTrace.lean`

Original comment 529, line 8:

````lean
/-!
# Hessian trace estimates for log-concave potentials

Letwin arXiv:2607.24164v1 Theorem 2.5 in weak form: for a normalized log-concave law with a C1 globally Lipschitz potential
with Lipschitz gradient, the weak Brascamp–Lieb inequality applied to the entries of `√B ∇²U √B`, the matrix variance
identity and the half energy bound give `∫ tr(B ∇²U B ∇²U) ≤ 2 tr(B B)` for PSD `B`. Regularity is explicit in each
statement. The entry Brascamp–Lieb client and the finite component-integrability step are private one-use supports.
Proof bodies: accepted Codex closed assemblies, verbatim up to the reviewed matrix-product name.
-/
````

### `formalization/FunctionalInequalities/KLS/LogConcave/IsotropicReduction.lean`

Original comment 531, line 8:

````lean
/-!
# Reduction of the isotropic log-concave Poincaré bound to regular laws

Bizeul–Klartag–Lehec arXiv:2610.05474v1, Section 2 (p. 5): the regular approximation reduces
Theorem 1.1 to isotropic regular laws. Formalized conditionally: if every isotropic regular law on
`ℝⁿ` (`n > 0`) has literature Poincaré constant at most `K`, then so does every isotropic log-concave
law on every finite-dimensional inner product space (`KLS.IsotropicBound K`). The proof derives the
Borell density of the law, approximates it by the laws of regular potentials with converging
covariances, transfers the bound through centering/whitening with the envelope coefficient, and
passes to the weak limit. The universal bound for regular laws is a hypothesis (it is what Theorems
3.1, 4.1 and Proposition 7.1 would supply); nothing unconditional is asserted. Proof bodies: Codex
q_batch (bundle `Full-Isotropic-Regular-Reduction`, independently accepted); statements and
placement: Claude.
-/
````

### `formalization/FunctionalInequalities/KLS/LogConcave/Line/Buser.lean`

Original comment 534, line 146:

````lean
/-- Blueprint Stage 1 `Q4`: the identity is a smooth test of unit gradient energy on the line, so
the variance is at most the smooth-test Poincaré constant. -/
````

Original comment 536, line 201:

````lean
/-- Blueprint Stage 1 `Q3`: a law on the line whose density is bounded by `M` has extended
variance at least `1 / (12 M²)`. -/
````

Original comment 538, line 286:

````lean
/-- Blueprint Stage 1 `Q0`: on the line the squared inverse Cheeger scale is at most twelve times
the smooth-test Poincaré constant. -/
````

Original comment 539, line 332:

````lean
/-- Blueprint Stage 1 `Q0'`: a log-concave law whose affine support has dimension at most one
satisfies the Buser comparison with constant twelve.  Dirac laws have both sides zero on the
left. -/
````

### `formalization/FunctionalInequalities/KLS/LogConcave/Line/Isoperimetry.lean`

Original comment 541, line 4:

````lean
/-!
# One-dimensional isoperimetry for log-concave laws: `h_M(ν) ≥ 2 ρ(m)`

Source: Blueprint Stage 1 of `research/decisions/2026-09-19-buser-route.md`, obligations `Q1`,
`Q1'` and `Q2` of `research/audits/BuserRouteStatements.lean`.  Read
`LineDensity.le_two_mul` (the density is at most twice its value at a median), then the
boundary-charge lemmas `LineDensity.mul_measure_Iio_diff_le`, `mul_measure_Ioi_diff_le`,
`mul_measure_compl_le`, then the smooth-domain bound
`LineDensity.mul_min_le_relativePerimeter` and its infimum form
`LineDensity.two_mul_le_minkowskiConstant`.

On the real line the surface measure of the relative-perimeter chain is the zero-dimensional
Hausdorff measure, so a boundary integral is bounded below by the density at any single boundary
point lying in the interior of the support (`LineDensity.ofReal_le_setLIntegral`).  For an open
set `W` containing a median `m`, the supremum `a` of the complement to the left of `m` and the
infimum `b` of the complement to the right are boundary points with `(a, b) ⊆ W`, so the
hazard-rate median bounds `2 ρ(m) F(a) ≤ ρ(a)` and `2 ρ(m) (1 - F(b)) ≤ ρ(b)` give
`2 ρ(m) · ν(Wᶜ) ≤ ρ(a) + ρ(b)`.  For a smooth domain `U` there are three cases: the median lies in
`U`, on its frontier, or outside its closure; in the first case the bound is applied to `U`, in
the third to the complement of the closure (whose frontier is contained in that of `U`), and in
the second the single boundary point `m` already carries `ρ(m) ≥ 2 ρ(m) · min {ν U, 1 - ν U}`.
The certified equality `h_M = h_S` then turns the smooth-domain bound into the bound on the
Minkowski Cheeger infimum.

For `Q2` the supporting exponential at the median with slope `k` has `|k| ≤ 2 ρ(m)`, because the
half mass on the side where it decays is `ρ(m) / |k|`; the supporting-line bound
`ρ ≤ ρ(m) + k (F - 1/2)` of the hazard module then gives `ρ ≤ 2 ρ(m)` on the interior of the
support, and log-concavity together with the vanishing of `ρ` off that interior extends the bound
to every point of the line.

No Poincaré inequality and no Buser-type comparison is asserted here.
-/
````

Original comment 542, line 127:

````lean
/-! ### `Q2`: the density is at most twice its value at a median -/
````

Original comment 543, line 190:

````lean
/-- Blueprint Stage 1 `Q2`: the density of a log-concave law on the line is at most twice its
value at a median, at every point of the line. -/
````

Original comment 544, line 247:

````lean
/-! ### `Q1'`: the smooth-domain isoperimetric bound -/
````

Original comment 545, line 386:

````lean
/-- Blueprint Stage 1 `Q1'`: every smooth domain of the line has relative perimeter at least
`2 ρ(m)` times the balance of its mass. -/
````

Original comment 546, line 433:

````lean
/-- Blueprint Stage 1 `Q1`: the Minkowski Cheeger infimum of a log-concave law on the line is at
least twice the density at a median. -/
````

### `formalization/FunctionalInequalities/KLS/LogConcave/Regular/Affine.lean`

Original comment 551, line 5:

````lean
/-!
# Regular potentials under affine changes of variables

Bizeul–Klartag–Lehec arXiv:2610.05474v1, Section 2 (p. 5): the regular class (12) is stable under
affine changes of variables, which is what centering and whitening a regular law use. For a regular
potential `V` and an invertible affine map `x ↦ L x + c`, the potential `V ∘ (L · + c)` is regular
(`Regular`), its normalizing constant is `|det L|⁻¹` times that of `V`, and its law is exactly the
image of the law of `V` under `y ↦ L⁻¹(y − c)`, i.e. a translation followed by the continuous linear
equivalence `L⁻¹`. No whitening operator is chosen here. Proof bodies: Codex bkl (bundle
`Affine-Regular-Transport`, independently accepted); statements and placement: Claude.
-/
````

### `formalization/FunctionalInequalities/KLS/LogConcave/Regular/Isometry.lean`

Original comment 553, line 8:

````lean
/-!
# Regular potentials under linear isometries

Bizeul–Klartag–Lehec arXiv:2610.05474v1, Section 2 (p. 5): regular potentials, their laws, isotropy
and the Poincaré constants transport through linear isometries between (possibly different)
finite-dimensional inner product spaces, with the same curvature constants `a, b`. In particular a
regular law on an abstract space has a regular law in standard coordinates on `ℝⁿ`, so a Poincaré
bound for isotropic regular laws on `ℝⁿ` transfers with the same constant. No non-isometric
invariance of the constant is asserted. Proof bodies: Codex bkl (bundle `Regular-Isometry-Transport`,
independently accepted); statements and placement: Claude.
-/
````

### `formalization/FunctionalInequalities/KLS/LogConcave/Regular/Isotropic.lean`

Original comment 554, line 6:

````lean
/-!
# Regular laws reduce to isotropic regular laws

Bizeul–Klartag–Lehec arXiv:2610.05474v1, Section 2 (p. 5): the reduction of Theorem 1.1 to
isotropic regular laws by centering and whitening. A regular law has finite second moment, full
support and positive definite covariance; a covariance whitening `W` exists, and the affine
potential `V (W⁻¹ · + mean)` is regular (`RegularAffine`) and isotropic, with its law the
translated and whitened law. No continuity or uniqueness of the whitening is asserted. Proof
bodies: Codex bkl (bundle `Regular-Isotropic-Producer`, independently accepted); statements and
placement: Claude.
-/
````

### `formalization/FunctionalInequalities/KLS/LogConcave/Regular/Poincare.lean`

Original comment 555, line 5:

````lean
/-!
# Conditional Poincaré transfer from isotropic regular laws to regular laws

Bizeul–Klartag–Lehec arXiv:2610.05474v1, Section 2 (p. 5): a universal Poincaré bound `K` for
isotropic regular laws (an explicit hypothesis here; the paper's Theorem 1.1 for the regular class)
gives `C_P(μ) ≤ K‖Cov μ‖` for every regular law `μ`, by centering and whitening to an isotropic
regular law (`RegularIsotropic`) and transporting the covariance energy; the envelope form
`K(1 + ‖Cov μ − Id‖)` tends to `K` along laws whose covariances tend to `Id`. No whitening-sequence
limit and no unconditional bound is asserted. Proof bodies: Codex route (bundle
`Regular-Poincare-Reduction`, independently accepted); statements and placement: Claude.
-/
````

### `formalization/FunctionalInequalities/KLS/LogConcave/Stein.lean`

Original comment 556, line 6:

````lean
/-!
# Stein kernels of log-concave laws: Letwin A.7 and Lemma 2.9

Letwin, arXiv:2607.24164v1, Appendix A.7 and Lemma 2.9, for a centered log-concave law `μ` on `ℝⁿ`
of full affine dimension (hence `μ ≪ volume` with finite second moment): the Stein identity extends
to all locally Lipschitz `f` with `f, ∇f ∈ L²(μ)`, and the `H^{-1}(μ)` norm of `⟪·, v⟫` is bounded by
`∫ ‖τ(x) v‖² dμ`. No isotropy, regularity or Stein-kernel construction is assumed or provided; the
moment-map kernel of the paper (Lemma 2.2, Proposition 2.8) and Theorems 1.1–1.2 remain open.
Proof bodies: Codex route (bundle `Letwin-A7`, independently accepted); statements and placement: Claude.
-/
````

### `formalization/FunctionalInequalities/KLS/LogConcave/WeakBrascampLieb.lean`

Original comment 557, line 8:

````lean
/-!
# Weak finite-energy scalar Brascamp–Lieb at C^{1,1}

Letwin arXiv:2607.24164v1 Lemma A.6 for a normalized C1 globally Lipschitz potential with Lipschitz gradient and
a.e. positive definite coordinate Hessian, for globally bounded weak tests with finite inverse-Hessian energy. Weak
sibling of `KLS/LogConcave/BrascampLieb.lean`, reusing its Hilbert-closure helpers; the finite-coordinate Hessian
identification uses `Probability/Stein/HessianKernel`. Proof bodies: accepted Codex closed assembly, verbatim.
-/
````

### `formalization/FunctionalInequalities/L2/Pairing.lean`

Original comment 574, line 3:

````lean
/-!
# `L²` pairings of vector fields

Generic facts about the pairing `∫ ⟪a, f⟫ dμ` of two square-integrable fields: identification with
the `L²` inner product, continuity along `L²` convergence, Cauchy–Schwarz, the energy identity
`∫ ‖a‖² = ‖a‖₂²`, and integrability of the pointwise pairing. Used for the Stein-kernel identities of
Letwin arXiv:2607.24164v1 (Appendix A.7). Proof bodies: Codex route (bundle `Letwin-A7`,
independently accepted); statements and placement: Claude.
-/
````

### `formalization/FunctionalInequalities/Poincare/LocalSlope/Gradient.lean`

Original comment 592, line 32:

````lean
/-- `Q1`: for an absolutely continuous law the local-slope and gradient descriptions of a valid
finite constant agree. Both directions rewrite the same two proved identifications, so no
inequality is weakened: the admissible class and the energy are transported simultaneously. -/
````

Original comment 593, line 58:

````lean
/-- `Q2`: the literature optimum of an absolutely continuous intrinsic law, in gradient form.
The two infima range over subtypes cut out by equivalent predicates, so each bounds the other. -/
````

### `formalization/FunctionalInequalities/Poincare/LocalSlope/SmoothTestComparison.lean`

Original comment 651, line 8:

````lean
/-!
# Smooth and literature Poincare constants

Proved continuation of the certified weighted approximation lemma.
Source: Blueprint `thm:smooth-lipschitz-constant-equivalence`; the final selected-constant
corollary retains explicit intrinsic absolute continuity, before the separate Borell theorem.
Read finite-constant equivalence, equality of the coordinate infima, the ambient/intrinsic
chain, then the selected/literature corollary. All four proofs are complete.
See `research/decisions/2026-09-06-smooth-literature-proofs.md` for scope and acceptance.

`Poincare.LocalSlope.Holds ν` tests functions directly on ν. In contrast, `Poincare.LocalSlope.Intrinsic.constant μ` is
already defined on `Probability.intrinsicMeasure μ`. The coordinate infimum below is printed
explicitly to avoid taking intrinsic coordinates a second time. No alternative constant is defined.
Finite constants include zero; optimal values remain in ENNReal, including infinity.
Only the intrinsic law must be absolutely continuous: the ambient law may be singular.
No log-concavity, second moment, Cheeger identification or raw/core agreement is assumed.
-/
````

### `formalization/FunctionalInequalities/Probability/ConvexSupport.lean`

Original comment 652, line 390:

````lean
/-! Cordero-Erausquin–Klartag (2015), Lemma 16, finiteness near the interior: an extended-real convex potential with finite
integral is finite on a neighbourhood of every interior point of the convex hull of the support. Body: root-accepted raw
candidate (CEK16-FiniteNear-Raw-Root ACCEPTANCE b389a6fc…, candidate a96fc727…), verbatim; statement = the exact
`ExtendedFiniteNearGoal` contract with its definitions unfolded. -/
````

Original comment 653, line 454:

````lean
/-! Cordero-Erausquin–Klartag (2015), Lemma 16, bound (54) for a FINITE Borel measure (the source's generality): the
probability specialization `exists_pos_le_measure_halfspace_of_mem_interior_convexHull_support` transported by
normalization `ν = μ(E)⁻¹ • μ` (same support; `μ ≠ 0` follows from the support-hull hypothesis, never from the zero-mass
fallback of `FiniteMeasure.normalize`). The bound `m ≤ μ(E)` keeps the positive total mass for the global-minimum
alternative; in dimension 0 the direction condition is vacuous. Statement and body: root direct existing-source
specialization (CEK16-FiniteMass-Raw-Root ACCEPTANCE 88b66a91…, CandidateV3 df51eb0b…, freeze 1a7f2143…), verbatim. -/
````

Original comment 605, line 508:

````lean
/-! Cordero-Erausquin–Klartag (2015), Lemma 16, the pointwise bound. Private geometry: root-accepted source specialization
(CEK16-EReal-Geometry-Raw-Root ACCEPTANCE 20790ce1…, candidate a5a8c47e…), verbatim, reusing the private
`effective_domain_convex` of section `EffectiveDomain`; `real_convexOn_effective_domain` is public (generic consumer).
Public statement frozen 670cf2e6…; proof: Codex source specialization from the finite-near theorem, the finite-measure (54)
bound and the geometry (CEK16-Point-Control-Raw-Root ACCEPTANCE 8e161b9d…). -/
````

### `formalization/FunctionalInequalities/Probability/Covariance/CauchySchwarz.lean`

Original comment 606, line 4:

````lean
/-!
# Covariance Cauchy–Schwarz

`cov[X, Y]² ≤ Var X · Var Y` for two square-integrable real statistics under a probability measure, on
an arbitrary measurable space. The pinned Mathlib has `covariance_eq_sub`, `covariance_self`, the
bilinearity lemmas and `variance_nonneg` but no such endpoint. It is a deterministic support of the BKL (68)
posterior noise estimate (Codex review `Root-Posterior-Noise-Bound-20261008`; proof body: Luna unit NB1,
independently accepted 2026-10-08): the nonnegative variance polynomial of `Y − tX` is expanded by
bilinearity, and both the zero-variance and positive-variance branches in `X` are treated.
-/
````

### `formalization/FunctionalInequalities/Probability/Covariance/Positivity.lean`

Original comment 607, line 4:

````lean
/-!
# Positivity of the ambient covariance

For a probability law with finite second moment on a finite-dimensional inner product space: full affine
support gives a strictly positive covariance operator, an injective covariance operator gives full affine
support, and the covariance operator is self-adjoint. Proof bodies: Codex bkl bundle
`Posterior-Covariance-Domain` (independently accepted); statements and placement: Claude.
-/
````

### `formalization/FunctionalInequalities/Probability/Covariance/Whitening.lean`

Original comment 608, line 6:

````lean
/-!
# Whitening of a positive definite operator and of the covariance

Source: Blueprint `thm:affine-isotropic-reduction`, the sentence "whiten the centered intrinsic law
by `Cov_{μ,V}^{-1/2}`, which exists by `lem:ambient-intrinsic-covariance`". Read
`exists_whitening_of_isSymmetric` and `Covariance.exists_whitening`.

On a finite-dimensional real inner product space every symmetric operator `T` with
`⟪T v, v⟫ > 0` for `v ≠ 0` has a self-adjoint continuous linear equivalence `W` with
`⟪T (W u), W v⟫ = ⟪u, v⟫` for all `u, v`: take the orthonormal eigenbasis of `T` and scale each
eigenvector by the inverse square root of its (positive) eigenvalue. The public conclusion is the
self-adjoint whitening identity `W ∘ T ∘ W = 1`. The covariance operator of a Borel law is such a `T` when it
is positive definite; the intrinsic covariance of a law with finite second moment is positive
definite by `lem:ambient-intrinsic-covariance`.

Only existence of a self-adjoint whitening is claimed; the statement does not assert positivity
or uniqueness of `W`, so its returned conditions do not characterize the positive inverse square
root `T^{-1/2}`. For example, `T = 1` and `W = -1` satisfy them. The isotropic reduction needs only
the whitening identity. The zero-dimensional space is included: the positivity premise is vacuous
and the unique linear equivalence satisfies the conclusion.

`Covariance.variance_inner_eq_of_sandwich` records the variance of a whitened linear statistic: for a
probability law with finite second moment and a self-adjoint `S` with the actual sandwich
`S ∘ Cov ∘ S = 1`, `Var⟪S h, ·⟫ = ‖h‖²`. It is a deterministic support of the BKL (68) posterior noise
estimate (Codex review `Root-Posterior-Noise-Bound-20261008`; proof body: Luna unit NB3, independently
accepted 2026-10-08, with `E` renamed to the section variable `V`); the sandwich is a hypothesis, not a
produced root.
-/
````

### `formalization/FunctionalInequalities/Probability/Diffusion/Existence.lean`

Original comment 609, line 10:

````lean
/-!
# Existence of diffusions with globally Lipschitz bounded coefficients

On any filtered space carrying a multidimensional Brownian motion with a usual filtration, autonomous globally
Lipschitz bounded coefficients on `Fin N → ℝ` have an everywhere continuous adapted solution with Itô
representation along itself (`exists_isDiffusion`): the vendored Picard global solution with zero jumps (a
zero-intensity Poisson random measure), its continuous Itô version, and their identification. Used for the cutoff
Eldan localization equations (BKL arXiv:2610.05474v1, (67)). Proof body: GPT (BKL Claude-controller goal, task
S5a); statement and placement: Claude.
-/
````

### `formalization/FunctionalInequalities/Probability/Diffusion/VectorGenerator.lean`

Original comment 610, line 5:

````lean
/-!
# The vector-valued generator

`vectorGenerator b σ G x = DG(x)[b x] + ½ Σ_k D²G(x)[σ_k x, σ_k x]` (the drift of `G(X_t)`), equal to `diffusionGenerator`
for scalar `G`, and its behaviour under continuous linear maps, products and finite families. Proof bodies: GPT (task
S-3bV); statements by the S-line sub-controller; placement: Claude.
-/
````

### `formalization/FunctionalInequalities/Probability/MomentMeasure/Affine.lean`

Original comment 612, line 8:

````lean
/-!
# Exponential mass, integrals and the CEK functional under affine subtraction

Exact formulas for the conjugate mass, the integral and the extended-logarithm functional after subtracting an affine
function: a finite-measure correction in general, and invariance for a centered probability measure with finite first
moment; the normalization producing a nonnegative potential vanishing at the origin.

Declaration blocks are verbatim from the root-accepted CEK Proposition 12 bundle (`independent-p12-attainment`, ACCEPTANCE 848aa45b…) under the reviewed rev3 migration map.
-/
````

### `formalization/FunctionalInequalities/Probability/MomentMeasure/Baseline.lean`

Original comment 613, line 5:

````lean
/-!
# The norm potential as a baseline

The Legendre transform of the norm (zero on the closed unit ball, `⊤` outside), its density and finite positive Haar
mass, and the finite functional value of the norm potential for finite first moment, including dimension zero.

Declaration blocks are verbatim from the root-accepted CEK Proposition 12 bundle (`independent-p12-attainment`, ACCEPTANCE 848aa45b…) under the reviewed rev3 migration map.
-/
````

### `formalization/FunctionalInequalities/Probability/MomentMeasure/Basic.lean`

Original comment 654, line 7:

````lean
/-!
# Exponential potential measures and the CEK functional

For an extended-real potential `φ`, `density φ = exp(-φ)` in `ℝ≥0∞` (zero where `φ = ⊤`), `weightedMeasure dx φ` is the
measure `exp(-φ) dx` and `mass dx φ = ∫⁻ exp(-φ) dx`; zero and infinite mass are retained and nothing is normalized.
`PotentialIntegrable φ μ` and `variationalFunctional dx μ φ = log ∫ exp(-φ*) dx - ∫ φ dμ` (extended logarithm) are the
objects of Cordero-Erausquin–Klartag, *Moment measures* (arXiv:1304.0630v1), Proposition 12. Elementary properties:
the monotonicity `mass_legendre_mono` used for the truncation (61), and Borel measurability of the conjugate density for
an arbitrary, possibly nonmeasurable primal (`measurable_density_legendre`).

The gradient push-forward (moment measure), the effective domain and essential continuity of CEK Definition 2 and
Theorem 2 are not defined in this module. Declaration blocks are verbatim from the root-accepted Lemma 17 bundle
(ACCEPTANCE ec6d356c…): lane A definitions (6433a0f6…) and prerequisites (5ec2f621…), ConjugateMass (90a65ba7…).
-/
````

### `formalization/FunctionalInequalities/Probability/MomentMeasure/Coercivity.lean`

Original comment 614, line 8:

````lean
/-!
# Coercivity of the CEK functional

Haar scaling of exponential mass, a polynomial bound on conjugate mass with the constant chosen before the potential,
and the resulting functional and integral bounds for centered probability measures with full-dimensional support.
This route does not establish the particular constant of CEK Lemma 15.

Declaration blocks are verbatim from the root-accepted CEK Proposition 12 bundle (`independent-p12-attainment`, ACCEPTANCE 848aa45b…) under the reviewed rev3 migration map.
-/
````

### `formalization/FunctionalInequalities/Probability/MomentMeasure/Compactness.lean`

Original comment 655, line 10:

````lean
/-!
# Compactness of convex potentials (CEK Lemma 17)

Cordero-Erausquin–Klartag, *Moment measures* (arXiv:1304.0630v1), Lemma 17, for a finite Borel measure `μ` (not
normalized) on a finite-dimensional real inner product space whose support hull has `0` in its interior, and nonnegative
extended-real potentials `φ ℓ` with convex real epigraphs, `φ ℓ 0 = 0`, a.e.-measurable `toENNReal` and uniformly bounded
integrals. Dimension zero is included.

* (56a), `Probability.exists_subseq_lintegral_le_liminf_of_convex_epigraph`: a subsequence and a nonnegative convex limit,
  finite and attained pointwise on the interior of the support hull, radially closed, `⊤` off its closure and Borel,
  whose integral is at most the liminf of the integrals. Pointwise bounds come from Lemma 16
  (`Probability/ConvexSupport.lean`), the subsequence from `Analysis/Convex/PointwiseCompactness.lean`, the limit from
  `Analysis/Convex/RadialExtension.lean`; Fatou is applied to the scaled potentials and then along the radial limit.
* Full (56), `MomentMeasure.exists_subseq_integral_bounds_of_convex_epigraph`: the same subsequence and limit also satisfy
  (56b) for every additive Haar `dx`, `limsup ∫ exp(-(φ (s j))*) dx ≤ ∫ exp(-ψ*) dx`, with `ψ` integrable against `μ` and
  finite conjugate mass derived (`MomentMeasure/ConjugateMass.lean`), not assumed. Zero conjugate mass is allowed.

Not provided: attainment in Proposition 12, essential continuity, the Euler–Lagrange identification, existence or
uniqueness of moment potentials (Theorem 2). Declaration blocks are verbatim from the root-accepted Lemma 17 bundle
(ACCEPTANCE ec6d356c…): the (56a) assembly (adcb1e09…) and Lemma17 (26b7c645…).
-/
````

### `formalization/FunctionalInequalities/Probability/MomentMeasure/ConjugateMass.lean`

Original comment 616, line 10:

````lean
/-!
# Upper semicontinuity of conjugate mass (CEK Lemma 17, (56b))

`limsup_mass_legendre_le`: let `K` be open and convex with `0 ∈ K`, let potentials `φ j` converge to `ψ` at every point of
`K`, where `ψ` is finite, and let `ψ` be radially closed and `⊤` off `closure K`. Then for every additive Haar measure `dx`
on a finite-dimensional space, dimension zero included, `∫ exp(-ψ*) dx` is finite and is at least
`limsup_j ∫ exp(-(φ j)*) dx` (Cordero-Erausquin–Klartag, *Moment measures*, arXiv:1304.0630v1, Lemma 17, (56b)).
No convergence of the conjugates, finiteness of initial dual masses or integrability is assumed: the pointwise step is
`limsup_density_legendre_le`, and the common integrable dominator `exists_integrable_exponential_domination` is built from
finitely many vertices (`Analysis/Convex/AffineMaximum.lean`) and `integrable_exp_sub_norm`, the Haar integrability of
`exp(M - c‖y‖)` for `c > 0`.

Declaration blocks are verbatim from ConjugateMass (90a65ba7…) of the root-accepted Lemma 17 bundle (ACCEPTANCE
ec6d356c…).

Real normalization (`real_legendre_normalization`): if the conjugate `φ*` has a real representative `ψ` and conjugate mass
`1`, then `exp(−ψ)` is Bochner integrable with integral `1` and `weightedMeasure dx ψ` is a probability measure; finiteness of
the lower integral is established before the real conversion. Proof body: strong-API candidate (gpt-6-astra,
`api-bounded-primal-geometry-v11`, d77ddfc1…), verbatim, in its own variable context; placement: Claude.
-/
````

### `formalization/FunctionalInequalities/Probability/MomentMeasure/Integrability.lean`

Original comment 618, line 8:

````lean
/-!
# Integrable potentials and their truncation

Finite-domain witnesses of `PotentialIntegrable`, integrability of the lower truncation for every real cutoff and of
its actual biconjugate, and the integral comparison used in the convexification step of CEK Proposition 12.

Declaration blocks are verbatim from the root-accepted CEK Proposition 12 bundle (`independent-p12-attainment`, ACCEPTANCE 848aa45b…) under the reviewed rev3 migration map.
-/
````

### `formalization/FunctionalInequalities/Probability/MomentMeasure/Normalization.lean`

Original comment 619, line 7:

````lean
/-!
# Effective-domain interior from a lower bound

`origin_mem_interior_domain_of_lower_bound`: the generic interior step used before supporting-plane normalization.

Declaration blocks are verbatim from the root-accepted CEK Proposition 12 bundle (`independent-p12-attainment`, ACCEPTANCE 848aa45b…) under the reviewed rev3 migration map.
-/
````

### `formalization/FunctionalInequalities/Probability/MomentMeasure/Truncation.lean`

Original comment 620, line 4:

````lean
/-!
# Truncation convergence and the convexified competitor

Dominated convergence for lower truncations, the lower-tail control of the truncation error, and the epsilon
reduction of every admissible competitor to a convex lower semicontinuous admissible one
(`exists_convexified_lowerTruncate_variational_le_add`), with zero and infinite exponential mass retained.

Declaration blocks are verbatim from the root-accepted CEK Proposition 12 bundle (`independent-p12-attainment`, ACCEPTANCE 848aa45b…) under the reviewed rev3 migration map.
-/
````

### `formalization/FunctionalInequalities/Probability/Moments.lean`

Original comment 621, line 12:

````lean
/-!
# Finite second moments of Borel laws and a third-moment contraction

`memLp_id_two_iff_lintegral_enorm_rpow_lt_top` characterises finite second moments. The section
`ThirdMomentContraction` proves `Σ_{ijk} (∫ x_i x_j x_k dν)² ≤ ∫ ‖x‖⁶ dν` for a probability law on `ℝⁿ` with
integrable sixth moment (no centering or log-concavity), a deterministic support of the proposed
log-determinant non-explosion route for the BKL localization equations (67) (Codex review
`Takeover-Logdet-Nonexplosion-20261008`; proof body: Luna unit TM1b round 6, independently accepted 2026-10-08).
The section `MomentTails` holds the eighth-moment tail bounds on a normed group with Borel structure: for a
probability law with integrable `‖x‖⁸` and `R > 0`, `ν(ball(0,R)ᶜ) ≤ M₈/R⁸` (Markov) and `‖x‖⁴` together with its
tail restriction are integrable with `∫ 1_{ball(0,R)ᶜ} ‖x‖⁴ ≤ M₈/R⁴`, `M₈` the actual eighth moment. They are the first
supports of the ball-conditioning stage of the moment-potential producer (Codex reviews
`Takeover-Moment-Potential-Producer-20261008`, `Conditioning-Draft-Review-20261008`; proof bodies: Luna units CB2 round 5
and CB3 round 2 under the checked-context driver, independently accepted 2026-10-08, kept verbatim).
-/
````

### `formalization/FunctionalInequalities/Probability/Posterior/Coercive.lean`

Original comment 623, line 7:

````lean
/-!
# The BKL posterior under a coercive quadratic parameter

Bizeul–Klartag–Lehec arXiv:2610.05474v1, p. 19, (67): when `⟪Q x, x⟫ ≥ a‖x‖²` with `a > 0`, the
quadratic damping of the exponent `⟪c, x⟫ − ½⟪Q x, x⟫` dominates every polynomially weighted exponential
on a parameter neighbourhood, so for an arbitrary probability prior (no moment assumption) the posterior
is a probability law, polynomially growing statistics are in `L²`, and the posterior expectation has the
covariance derivative along any signed parameter line `(c + t h, Q + t H)`. The source initial stage
`Q = 0` is not coercive in positive dimension (in dimension zero coercivity holds vacuously) and is
handled by the compact-prior modules. No stochastic process, Itô formula
or (68)–(71) is constructed. Proof bodies: Codex q_batch bundle `Posterior-Parameter-Calculus`
(independently accepted); statements and placement: Claude.
-/
````

### `formalization/FunctionalInequalities/Probability/Posterior/CompactDomain.lean`

Original comment 624, line 5:

````lean
/-!
# The BKL posterior of a compactly supported prior as a probability law

Bizeul–Klartag–Lehec arXiv:2610.05474v1, (67): the posterior `μ_{c,Q} = μ e^{⟪c,x⟫ − ½⟪Qx,x⟫}/Z` of a
compactly supported prior, for every finite parameter pair (including the initial pair and negative `Q`),
as a probability law with the null sets, a.e. filter, support and affine support of the prior, finite
second moment, and, when the prior has full affine support, strictly positive covariance. The isotropic
source adapter (unit covariance with a self-adjoint positive canonical inverse) is in
`KLS/BKL/PosteriorDomain.lean`. No square root, transported-law whitening, stochastic equation or coefficient
regularity is provided. Proof bodies: Codex bkl bundle `Posterior-Covariance-Domain` (independently
accepted); statements and placement: Claude.
-/
````

### `formalization/FunctionalInequalities/Probability/Posterior/CompactPrior.lean`

Original comment 625, line 9:

````lean
/-!
# Tilts of a compactly supported prior

Bizeul–Klartag–Lehec arXiv:2610.05474v1, p. 19, the compact-prior stage before (67): for a probability
law with compact support, every continuous exponent gives an integrable tilt (a probability law), bounded
measurable statistics are in `L²` of the tilt, tilted expectations are bounded by the support bound, and
the expectation `t ↦ ∫ f d(μ.tilted (φ + t g))` has derivative `Cov_{μ.tilted φ}(f, g)` at `t = 0`.
No coercivity is needed, so zero parameters are covered. Proof bodies: Codex q_batch bundle
`Posterior-Parameter-Calculus` (independently accepted); statements and placement: Claude.
-/
````

### `formalization/FunctionalInequalities/Probability/Posterior/CompactQuadratic.lean`

Original comment 626, line 4:

````lean
/-!
# The BKL posterior of a compactly supported prior

Bizeul–Klartag–Lehec arXiv:2610.05474v1, p. 19, (67) in the compact stage: for a compactly supported
prior every parameter pair `(c, Q)`, including the initial pair `c = Q = 0`, gives a probability
posterior, continuous statistics are in `L²`, the expectation has the covariance derivative along signed
parameter lines, and all norm moments are bounded uniformly in the parameters by a support radius.
Proof bodies: Codex q_batch bundle `Posterior-Parameter-Calculus` (independently accepted); statements
and placement: Claude.
-/
````

### `formalization/FunctionalInequalities/Probability/Posterior/Exponent.lean`

Original comment 627, line 8:

````lean
/-!
# The linear–quadratic exponent of the BKL posterior

Bizeul–Klartag–Lehec arXiv:2610.05474v1, p. 19, (67): the localization posterior of a prior `μ` with
parameters `(c, Q)` is the tilt of `μ` by the exponent `x ↦ ⟪c, x⟫ − ½⟪Q x, x⟫`. This module defines the
exponent, records that it is affine in the parameters, bounds it polynomially, and writes a tilted
expectation as a ratio of prior integrals. Analytic inputs for the parameter response are in
`Probability/Posterior/{CompactPrior, Coercive, CompactQuadratic}.lean`. Proof bodies: Codex q_batch
bundle `Posterior-Parameter-Calculus` (independently accepted); statements and placement: Claude.
-/
````

### `formalization/FunctionalInequalities/Probability/Posterior/Generator.lean`

Original comment 628, line 7:

````lean
/-!
# Generator of the BKL posterior expectation (deterministic core of (68))

Bizeul–Klartag–Lehec arXiv:2610.05474v1, p. 19, (67)–(68), compact-prior stage: the posterior
expectation `(c, Q) ↦ ∫ f dμ_{c,Q}` of a measurable `f` bounded on the support is `C^∞` in `c`, its
`c`-gradient is `Cov(f, ⟪h,x⟫)`, its `c`-Hessian is a covariance expression, its `Q`-derivative in a
direction `M` is `−½ Cov(f, ⟪Mx,x⟫)`, and for every symmetric `M` the generator combination
`D_c[M a] + ∂_Q[M] + ½ tr_M D²_c` vanishes. Instantiating `M = Cov(μ_{c,Q})⁻¹` is the deterministic
content of the zero drift in (68); no stochastic process, Itô formula or martingale is constructed.
Proof bodies: Codex q_batch bundle `Posterior-Generator-Cancellation` (independently accepted);
statements and placement: Claude.
-/
````

### `formalization/FunctionalInequalities/Probability/Posterior/JointRegularity.lean`

Original comment 629, line 12:

````lean
/-!
# Joint regularity of the compact posterior in `(c, Q)`

Bizeul–Klartag–Lehec arXiv:2610.05474v1, p. 19, (67), compact-prior stage. The posterior expectation
`(c, Q) ↦ ∫ f dμ_{c,Q}` of a measurable `f` bounded on the prior support is `C^∞` jointly in the parameter
pair `p = (c, Q) ∈ E × (E →L[ℝ] E)` (product norm, operator norm on the second factor), for every finite
pair including `Q = 0`, non-symmetric `Q` and dimension zero; hence so are the posterior mean and the
posterior covariance operator. The proof linearises the exponent: the score `p ↦ ⟪c,x⟫ − ½⟪Qx,x⟫` is
continuous linear in `p`, so after a finite-dimensional chart it is the pairing with a Riesz feature
`ψ(x)`, and the joint expectation is the `c`-only expectation (`Generator.lean`) of the pushed-forward
prior `ψ_*μ` at `Q' = 0`, composed with the chart; the chart is an implementation device and is private.
Prior isotropy is not used here; the inverse covariance and the drift of (67) are in
`KLS/BKL/PosteriorDomain.lean`. No stochastic process, SDE or Itô statement. Proof bodies: Codex q_batch
bundle `Posterior-Joint-Regularity` (independently accepted); statements and placement: Claude.
-/
````

### `formalization/FunctionalInequalities/Probability/QuadraticTilt.lean`

Original comment 630, line 10:

````lean
/-!
# Small quadratic tilts of a probability measure

For a probability measure `μ` on a normed space, the normalized tilts `e^{-δ‖x‖²/2} μ / Z_δ`
converge to `μ` as `δ → 0⁺`: integrals of integrable observables, the laws (weakly), means and
second moments. Only probability and integrability are assumed. This is the second step of the
regular approximation in Bizeul–Klartag–Lehec (arXiv:2610.05474v1, Section 2, p. 5); the
Gaussian smoothing step and the joint limit are separate. Codex proofs
(`build/reviews/2026-10-07-bkl-continuous/queue/regular-approximation/`).
-/
````

### `formalization/FunctionalInequalities/Probability/Stein/DualBound.lean`

Original comment 631, line 6:

````lean
/-!
# Stein kernels bound the `H^{-1}` norm of linear functions

Letwin, arXiv:2607.24164v1, Lemma 2.9 in generic form: if `τ` is an a.e. symmetric Stein kernel of
`μ ≪ volume` with `|τ|_HS ∈ L²(μ)` and finite second moment, then for every `v` the linear function
`⟪·, v⟫` has finite `H^{-1}(μ)` norm with `‖⟪·, v⟫‖²_{H^{-1}} ≤ ∫ ‖τ(x) v‖² dμ` (A.7 plus Cauchy–Schwarz
on every unit-energy test). Proof bodies: Codex route (bundle `Letwin-A7`, independently accepted);
statements and placement: Claude.
-/
````

### `formalization/FunctionalInequalities/Probability/Stein/IdentityExtension.lean`

Original comment 632, line 4:

````lean
/-!
# Stein identity extension to locally Lipschitz L2 tests

Existing statements, names and proof payloads are preserved.
-/
````

### `formalization/FunctionalInequalities/Probability/Stein/QuadraticAction.lean`

Original comment 633, line 8:

````lean
/-!
# Quadratic forms, noise shifts and energies of the matrix action

Identities for the Euclidean action `Stein.action` of a real matrix, used for spectral quadratic-form estimates:
- the coordinate form `Σᵢⱼ Aᵢⱼ xᵢ xⱼ = ⟪A x, x⟫`, the sandwich `⟪Q (S x), S x⟫ = ⟪(S Q S) x, x⟫` for symmetric `S`, the conjugated latent
  field `e (H (e† v)) + t v = (S H S + t) v`, and invariance of the variance of a quadratic form under the pushforward by `S`;
- `Analysis.sum_norm_action_spectral_sign_noise`: for symmetric invertible `M` with `B = √(M²)`, `S = √B` and `Q = sign M`, and any
  symmetric `H`, `Σᵢ ‖(S H S + t) Q eᵢ‖² = tr (B H B H) + 2 t tr (B H) + n t²`;
- `KLS.LogConcave.sum_integral_spectral_noise_energy_le`: for an arbitrary measurable, a.e. symmetric random matrix with integrable
  entries and mean `Id` whose `tr (B H B H)` satisfies the trace bound `∫ ≤ 2 tr (B²)` for every symmetric `B` (an input), the integrated
  energy of the shifted action is at most `2 tr (M²) + 2 t tr B + n t²`. No log-concavity or Hessian hypothesis is used.

Provenance: accepted closed assemblies for the exact compact Letwin constant 8 (Codex acceptances recorded in the integration packet).
All finite dimensions; nothing here asserts a Stein kernel.
-/
````

### `solutions/LemAmbientIntrinsicPoincareComparison.lean`

Original comment 638, line 3:

````lean
/-!
# Lean certificate: ambient and intrinsic-affine comparison

Ledger node: `lem:ambient-intrinsic-poincare-comparison`.
Status: proved / checked_by: lean. The named certificate packages the complete node.
The public comparison signatures are unchanged from the reviewed statement batch.
Typed applications include zero dimension, singular laws and infinite optimal constants.

Sources, assumptions and reading order: `Poincare/Euclidean/README.md` in the library.
-/
````

### `solutions/LemCovarianceTestCoreDensity.lean`

Original comment 656, line 3:

````lean
/-!
# Lean certificate: `lem:covariance-test-core-density`

Status: proved / checked_by: lean. The certificate packages all four approximation contracts.
Source: Blueprint Appendix A and `research/decisions/2026-09-06-weighted-approximation-acceptance.md`.
The reusable declarations retain their original hypotheses, including arbitrary singular B,
absolute continuity with respect to any Haar reference measure, and dimension zero.
-/
````

### `solutions/LemLegacyRelaxedPoincareComparison.lean`

Original comment 640, line 4:

````lean
/-!
# Lean certificate: legacy tests and relaxed Poincaré constants

Ledger node: `lem:legacy-relaxed-poincare-comparison`.
Status: proved / checked_by: lean. The named certificate packages the complete node.
The public comparison signatures are unchanged from the reviewed statement batch.
Typed applications include zero dimension, singular laws and infinite optimal constants.

Sources, assumptions and reading order: `Poincare/Euclidean/README.md` in the library.
-/
````

### `solutions/ThmSmoothLipschitzConstantEquivalence.lean`

Original comment 657, line 3:

````lean
/-!
# Lean certificate: `thm:smooth-lipschitz-constant-equivalence`

Status: proved / checked_by: lean. The sole certificate packages all eight public interfaces,
with their own quantifiers: pointwise slope, a.e. slope, energy, domain, finite bounds, coordinate
infima, ambient/intrinsic comparison, and the selected/literature corollary under intrinsic
absolute continuity. It does not supply the separate Borell input or a KLS proof.
Proof acceptance: `research/decisions/2026-09-06-smooth-literature-proofs.md`.
-/
````
