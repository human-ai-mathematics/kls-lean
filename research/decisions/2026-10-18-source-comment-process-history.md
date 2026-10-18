# Source-comment process history

Archived on 2026-10-18 from the already accepted, uncommitted downstream/API proposal.
The original comments below retain their exact text, source paths and original line numbers.
They are historical records, including old task/round/worker/controller descriptions; they do not assign current proof or paper-coverage status.

The live source keeps mathematics, hypotheses, constants, source locators and useful proof explanations.
Only comment prose is edited. Each batch compares every byte outside comments and synchronizes matching infrastructure source hashes without changing classifications, assumptions, gaps or certificates.
Per-batch documentation acceptance is under `build/file-management/2026-10-18-source-comment-cleanup/`.
The preceding full Lean receipt remains bound to its earlier snapshot; this maintenance is not a new full Lean run.

## 01-probability-l2-poincare

### formalization/FunctionalInequalities/L2/AffineDecomposition.lean

[Current source](../../formalization/FunctionalInequalities/L2/AffineDecomposition.lean)

Original comment 188, line 8:

````lean
/-!
# Affine decomposition bounds in `L²`

Bizeul–Klartag–Lehec (arXiv:2610.05474v1), end of the proof of Proposition 7.1, p. 30: an
`f ∈ L²(μ)` splits as `c + ℓ + h` with `c` constant, `ℓ` linear and `h` orthogonal to the affine
functions, and a linear operator that kills constants and is bounded by `A` on linear functions and
on the affine-orthogonal part is bounded by `√2 A`.

`norm_apply_le_sqrt_two_mul` is the abstract Hilbert-space form, for orthogonal
finite-dimensional subspaces `K` (constants) and `L` (linear functions).

`affineOrthPart μ g = g - ∫ g dμ - Σ_j (∫ ⟪e_j, y⟫ g(y) dμ) ⟪e_j, ·⟫` is the concrete
affine-orthogonal part of a function on `ℝⁿ` for a centered probability measure `μ` with identity
covariance; its properties are stated with those moment hypotheses only (Luna, tasks R8a).
-/
````

Original comment 189, line 114:

````lean
/-- `∫ u² ≤ ∫ v²` implies `‖u‖₂ ≤ ‖v‖₂` for `u, v ∈ L²` (Luna, task R8a3). -/
````

Original comment 190, line 479:

````lean
/-- For `f` centered and orthogonal to the linear functions, `f - g̃ = (f - g)~` (Luna, task R8a3). -/
````

Original comment 191, line 529:

````lean
/-- The affine-orthogonal part of a `C²` function is `C²` with the same second derivative (Luna,
task R8a4). -/
````

Original comment 192, line 595:

````lean
/-- **The affine-orthogonal part is orthogonal to the affine part**: `∫ g̃ (g - g̃) = 0` (Luna, task
R8a3-cross). -/
````

Original comment 193, line 699:

````lean
/-- **Bessel's inequality for the affine-orthogonal part**: `∫ g̃² ≤ ∫ g²` (Luna, task R8a3-sq2; one
dead tactic and four `<;>`→`;` linter fixes applied at integration). -/
````

Original comment 194, line 869:

````lean
/-- **Contraction towards the affine-orthogonal functions**: if `f ∈ L²` is centered and orthogonal
to the linear functions, then `‖f - g̃‖₂ ≤ ‖f - g‖₂` (Luna, task R8a5). -/
````

Original comment 195, line 883:

````lean
/-- **Square integral of an affine function** under a centered law with identity covariance (Luna, task R8a3-affsq). -/
````

Original comment 196, line 940:

````lean
/-- **Pythagoras for the affine decomposition** of `f ∈ L²(μ)` (Luna, task R8a3-pyth2). -/
````

### formalization/FunctionalInequalities/Poincare/SmoothTest/WeakLimit.lean

[Current source](../../formalization/FunctionalInequalities/Poincare/SmoothTest/WeakLimit.lean)

Original comment 197, line 29:

````lean
/-- **Weak passage of the Poincaré inequality on a compactly supported smooth test**: if `μ_j → μ`
weakly, `C_j → C` and `Var_{μ_j} f ≤ C_j ∫‖∇f‖² dμ_j`, then `Var_μ f ≤ C ∫‖∇f‖² dμ` (Luna, task S2-W1-2). -/
````

Original comment 198, line 158:

````lean
/-- A `C^∞` function with compact support is an admissible test for every finite measure (Luna, task
S2-W2a). -/
````

Original comment 199, line 200:

````lean
/-- The first and second integrals of the cutoffs `f χ_{n+1}` converge to those of `f`:
`∫ χ_{n+1} f → ∫ f` and `∫ (χ_{n+1} f)² → ∫ f²` (no `L²`-norm convergence is exported).
(Luna, task S2-W2b). -/
````

Original comment 200, line 329:

````lean
/-- Inside the ball the cutoff does not change the gradient (Luna, task S2-W2c1a). -/
````

Original comment 201, line 344:

````lean
/-- Everywhere the cutoff gradient is dominated by `2‖∇f‖² + 2 (M/R)² f²` (Luna, task S2-W2c1). -/
````

Original comment 202, line 423:

````lean
/-- The energies of the cutoffs `f χ_{n+1}` converge to the energy of `f` for an admissible `f`
(Luna, task S2-W2c2). -/
````

Original comment 203, line 533:

````lean
/-- **A Poincaré bound on compactly supported admissible tests extends to all admissible tests**
(BKL Section 2, cutoff extension; Luna, task S2-W2 assembly). -/
````

### formalization/FunctionalInequalities/Probability/Conditioning.lean

[Current source](../../formalization/FunctionalInequalities/Probability/Conditioning.lean)

Original comment 204, line 242:

````lean
/-! Conditioning weakly convergent laws on a ball containing the support of the limit: integrals of continuous functions converge (Letwin Lemma A.1 approximation; task L-T10a). -/
````

Original comment 205, line 246:

````lean
/-- **Conditioning on a large ball preserves weak convergence** (Letwin Lemma A.1 approximation, task T10a):
if `ν k → μ` weakly and `μ` is carried by `closedBall 0 r` with `r < R`, then for every continuous `f` the
integrals against the conditioned laws `ν k [| closedBall 0 R]` converge to `∫ f dμ`. -/
````

### formalization/FunctionalInequalities/Probability/Diffusion/Dynkin.lean

[Current source](../../formalization/FunctionalInequalities/Probability/Diffusion/Dynkin.lean)

Original comment 206, line 5:

````lean
/-!
# Dynkin's identity for diffusions with compactly supported coefficients

For continuous compactly supported coefficients and every `C²` function `F`, `F(Y_T)` is integrable and
`E F(Y_T) − F(x₀) = E ∫₀ᵀ 𝓛F(Y_s) ds` (vector Itô formula and the mean-zero Brownian integral); and linear
functionals annihilating the noise evolve pathwise by the drift. These are the only stochastic inputs of
the generator-form treatment of BKL arXiv:2610.05474v1, Lemmas 4.3, 5.1 and 5.2. Proof bodies: GPT (BKL Claude-controller goal, tasks S5b); statements and placement: Claude.
-/
````

### formalization/FunctionalInequalities/Probability/Diffusion/Generator.lean

[Current source](../../formalization/FunctionalInequalities/Probability/Diffusion/Generator.lean)

Original comment 207, line 10:

````lean
/-!
# The generator of a diffusion

`diffusionGenerator b σ F x = DF(x)[b x] + ½ Σ_k D²F(x)[σ_k x, σ_k x]` for drift `b` and noise columns
`σ_k`, coordinate-free on a normed space; it is invariant under continuous linear changes of coordinates
(`diffusionGenerator_transport`), which moves a diffusion on a finite-dimensional state space (for BKL
arXiv:2610.05474v1 (67), the parameter space `E × (E →L[ℝ] E)`) to coordinates `Fin N → ℝ`. Proof bodies: GPT (BKL Claude-controller goal, tasks S5cd); statements and placement: Claude.
-/
````

Original comment 208, line 84:

````lean
/-! Chain rule for the generator, the step (82) of BKL (task S3b1; proof body GPT, statement Claude). -/
````

Original comment 209, line 173:

````lean
/-! Pointwise chain rule under local `C²` hypotheses (task S-3b1L; proof body GPT, statement by the S-line sub-controller). -/
````

### formalization/FunctionalInequalities/Probability/Diffusion/InverseCalculus.lean

[Current source](../../formalization/FunctionalInequalities/Probability/Diffusion/InverseCalculus.lean)

Original comment 210, line 9:

````lean
/-!
# Generators of inverses and powers

The derivative of `Ring.inverse ∘ G`, the generator of an inverse operator `𝓛(A⁻¹) = −A⁻¹(𝓛A)A⁻¹ + Σ_k A⁻¹H_kA⁻¹H_kA⁻¹`, and
bounds for generators of powers. Proof bodies: GPT (task S-5e0); statements by the S-line sub-controller; placement: Claude.
-/
````

### formalization/FunctionalInequalities/Probability/Diffusion/Setup.lean

[Current source](../../formalization/FunctionalInequalities/Probability/Diffusion/Setup.lean)

Original comment 211, line 11:

````lean
/-!
# Brownian setup and diffusions with Itô representation

The usual augmentation of the right-continuous natural filtration of a multidimensional Brownian motion
(vendored LevyStochCalc API) and `IsDiffusion`: an everywhere continuous adapted version `Y` of
`x₀ + ∫₀ᵗ b(Y_s) ds + Σ_k ∫₀ᵗ σ_k(Y_s) dW^k_s` with coefficients evaluated along `Y`. This is the first
project module importing the vendored stochastic calculus (formalization/vendor/README.md); only vendored
declarations with standard logical axioms are used. Proof bodies: GPT (BKL Claude-controller goal, tasks S5b); statements and placement: Claude.
-/
````

### formalization/FunctionalInequalities/Probability/Diffusion/Transport.lean

[Current source](../../formalization/FunctionalInequalities/Probability/Diffusion/Transport.lean)

Original comment 212, line 5:

````lean
/-!
# Diffusions under a change of coordinates

Continuity of diffusion paths, Dynkin's identity and the noise-free linear identity for a diffusion transported by a
continuous linear equivalence of the state space (used for the Eldan process on `E × (E →L[ℝ] E)` in coordinates).
Proof bodies: GPT (S-line sub-controller task S-5d2a); statements by the S-line sub-controller; placement: Claude.
-/
````

### formalization/FunctionalInequalities/Probability/Line/Laplace.lean

[Current source](../../formalization/FunctionalInequalities/Probability/Line/Laplace.lean)

Original comment 213, line 94:

````lean
/-! ### Local moment generating function and moments

The density MGF is Luna's (task B2b, round 6); the law MGF, the moment identification through
`ProbabilityTheory.iteratedDeriv_mgf_zero` and the rational calculus are Codex proofs
(`build/reviews/2026-10-07-bkl-continuous/reviews/Q0b-mgf-closure/`). Only `|w| < β` is used. -/
````

Original comment 214, line 374:

````lean
/-- **The noise factor of BKL (111) has zero derivative at the origin**: `w ↦ log ∫ e^{(w/σ)s} dη_β(s)`
is differentiable at `0` with derivative `0`, since `η_β` is centered (Luna, task R4a3). -/
````

### formalization/FunctionalInequalities/Probability/Posterior/LogPartition.lean

[Current source](../../formalization/FunctionalInequalities/Probability/Posterior/LogPartition.lean)

Original comment 215, line 4:

````lean
/-!
# The log-partition function of the BKL posterior

`ψ(c, Q) = log ∫ e^{⟪c,x⟫ − ½⟪Qx,x⟫} dμ` for a compactly supported prior (Bizeul–Klartag–Lehec
arXiv:2610.05474v1, Section 4): `ψ` is jointly `C^∞`, the log-Laplace transform of the posterior is
`Λ_{μ_{c,Q}}(z) = ψ(c + z, Q) − ψ(c, Q)`, posterior cumulants are `c`-derivatives `κ_m = D_c^m ψ` (`m ≥ 1`),
and `D_c ψ[h] = ⟪h, a(c, Q)⟫`. This is the deterministic bridge that turns the Itô computations (71) and
(73) into generator identities. Proof bodies: GPT (BKL Claude-controller goal, task S1a; lint options
adjusted by Claude); statements and placement: Claude.
-/
````

### formalization/FunctionalInequalities/Probability/Product.lean

[Current source](../../formalization/FunctionalInequalities/Probability/Product.lean)

Original comment 216, line 5:

````lean
/-!
# Independent coordinates of product measures

Factorization of lower integrals of products over `μ^N`, and second-moment calculus on finite products `μ^N = Measure.pi (fun _ => μ)` and on binary products
`μ ⊗ ν`: normalized sums of independent copies, products of coordinates, and sums of independent
observables. Only `L²` hypotheses are used. These are the moment computations behind the isotropy
of the suspension in Bizeul–Klartag–Lehec (arXiv:2610.05474v1), proof of Proposition 7.1, p. 28.
`lintegral_pi_prod_fin` is Luna's (task LF2); the moment results are Codex proofs
(`build/reviews/2026-10-07-bkl-continuous/reviews/R1-*`).
-/
````

Original comment 217, line 22:

````lean
/-- `∫⁻ Π_i g_i(x_i) d(⊗_i μ) = Π_i ∫⁻ g_i dμ` over `Fin N` (Luna, task LF2). -/
````

## 02-analysis-convex-weak-sard

### formalization/FunctionalInequalities/Analysis/Convex/Alexandrov.lean

[Current source](../../formalization/FunctionalInequalities/Analysis/Convex/Alexandrov.lean)

Original comment 19, line 4:

````lean
/-!
# Alexandrov identity in push-forward form

If `(∇u)_# ν = μ` with `ν, μ ≪ volume` for a convex Lipschitz `u`, the subgradient image of a set has `μ`-measure
equal to the `ν`-measure of the set (route node N5 of the weak moment-map route to Letwin arXiv:2607.24164v1), and the
farthest-point exposure lemma for the Caffarelli block. Proof bodies: GPT (Letwin sub-controller tasks L-T14b, L-T11c1);
statements by the Letwin sub-controller; placement: Claude.
-/
````

Original comment 20, line 140:

````lean
/-! Farthest points are exposed (task L-T11c1). -/
````

Original comment 21, line 192:

````lean
/-! Local two-sided Alexandrov bounds (task L-T14c). -/
````

Original comment 22, line 438:

````lean
/-! Sliding supporting hyperplanes (Caffarelli block; task L-T11c2). -/
````

Original comment 23, line 608:

````lean
/-! Nearest boundary points and supporting half-spaces (task L-T11c3). -/
````

Original comment 24, line 734:

````lean
/-! Volumes of cones over convex sets (task L-T11c4). -/
````

Original comment 25, line 1057:

````lean
/-! The Alexandrov maximum principle (task L-T11c5). -/
````

Original comment 26, line 1395:

````lean
/-! Subgradient images of quadratic functions (task L-T12c1). -/
````

Original comment 27, line 1666:

````lean
/-! Distance to the frontier is bounded by the directional width (weak Letwin route, Caffarelli step G3, task L-T11e2). -/
````

Original comment 28, line 1737:

````lean
/-! Subgradient images under affine changes of variables and their volume (task L-T11e1). -/
````

Original comment 29, line 1929:

````lean
/-! Minimum estimate for a normalized convex function from a lower Alexandrov bound (task L-T11e4). -/
````

Original comment 30, line 2084:

````lean
/-! Subgradient images after subtracting an affine function, and their volume (task L-T11e6). -/
````

Original comment 31, line 2129:

````lean
/-! The Alexandrov identity on open sets: the volume of the subgradient image equals the integral of the Monge–Ampère density (task L-T14d). -/
````

Original comment 32, line 2159:

````lean
/-- **Alexandrov identity on open sets for the moment potential** (weak Letwin route, N5/N8, task T14d):
if `u` is convex, Lipschitz, `ν = e^{-u} dx` is normalised and `ν.map ∇u = μ = 1_K e^{-V} dx` for a closed convex
`K` and a measurable `V`, then the subgradient image of every open `G` has volume `∫_G e^{-u + V(∇u)}`. -/
````

Original comment 33, line 2309:

````lean
/-! Two-sided Alexandrov bounds for the inverse subgradient map (task L-T11f4). -/
````

Original comment 34, line 2411:

````lean
/-- **Reciprocal Alexandrov bounds** (weak Letwin route, N7, task T11f4; KLS500
`exists_local_relativeSubgradientImage_volume_bounds`): for the moment potential `u` (convex, Lipschitz,
`ν = e^{-u} dx` normalised, `ν.map ∇u = μ = ρ dx` with `c ≤ ρ ≤ C` on a closed convex `K`) and a radius `M`,
the set `(∂u)⁻¹(G) = {x | ∃ p ∈ G, p ∈ ∂u(x)}` of an open `G ⊆ K` that lies in `closedBall 0 M` has volume
comparable to `vol G`. -/
````

### formalization/FunctionalInequalities/Analysis/Convex/Caffarelli.lean

[Current source](../../formalization/FunctionalInequalities/Analysis/Convex/Caffarelli.lean)

Original comment 35, line 9:

````lean
/-!
# Caffarelli's strict convexity argument: geometric steps

Steps of Caffarelli's exposed-point argument for Alexandrov solutions with two-sided Monge–Ampère bounds
(weak Letwin route, block T11e), built on `Analysis/Convex/Alexandrov.lean` and `Analysis/Convex/Normalization.lean`.

* `infDist_frontier_image_le_of_width` (task L-T11e5).
-/
````

Original comment 36, line 146:

````lean
/-! Compact sections nested inside the domain that shrink to the contact set (task L-T11e3). -/
````

Original comment 37, line 352:

````lean
/-! Caffarelli's contact-set lemma: under local two-sided Alexandrov bounds a compact contact set is a single point, also in the localized form at exposed points (tasks L-T11e and L-T11e7). -/
````

Original comment 38, line 657:

````lean
/-- **Caffarelli's contact-set lemma, localised form** (weak Letwin route, N6, task T11e7): let `C` be the
compact contact set of a supporting affine function of the convex `u`, `z ∈ C` strictly exposed in the unit
direction `θ`, `h > 0`, and suppose the two-sided Alexandrov bounds hold only on compact subsets of an open `U`
containing the slab piece `C ∩ {⟪· − z, θ⟫ ≥ −h}`. Then `C = {z}`. -/
````

Original comment 39, line 1001:

````lean
/-- **Caffarelli's contact-set lemma** (global bounds, compact contact set; same statement as task L-T11e,
re-derived here from the localised form so that only this file needs integrating). -/
````

Original comment 40, line 1063:

````lean
/-! Elementary steps from singleton contact sets to strict convexity (task L-T11f1). -/
````

Original comment 41, line 1084:

````lean
/-- **Singleton contact sets give strict convexity** (weak Letwin route, N6, task T11f1): if every
supporting affine function of the convex `u` touches its graph at exactly one point, `u` is strictly
convex. -/
````

Original comment 42, line 1137:

````lean
/-- **Slopes of a strictly convex function lie in the interior of a convex slope range** (weak Letwin
route, N7, task T11f1): if all subgradients of the strictly convex `u` lie in a convex `K` with nonempty
interior, they lie in `interior K`. -/
````

Original comment 43, line 1181:

````lean
/-- **A strictly exposed contact point below a level** (weak Letwin route, N6, task T11f1; KLS500
`exists_strict_exposed_contact_in_sublevel`): if `{u ≤ R}` is compact and `u x < R`, the contact set of a
supporting affine function at `x` has a point `z` with `u z < R` that is strictly exposed in the direction
`θ` among the contact points with `u ≤ R`. -/
````

Original comment 44, line 1251:

````lean
/-! The truncated conjugate used to localize the contact-set argument (task L-T11f2). -/
````

Original comment 45, line 1255:

````lean
/-- The **ball-truncated conjugate** `p ↦ sup_{‖x‖ ≤ M} (⟪p, x⟫ − u x)` (weak Letwin route, N7, task T11f2;
KLS500 `truncatedLegendrePotential`): a globally finite convex function that agrees with the Legendre
transform of `u` wherever the supremum is attained inside the ball. -/
````

Original comment 46, line 1302:

````lean
/-- **Zeros of the centred truncated conjugate are the subgradients** (task T11f2): for convex `u` and
`‖xc‖ < M`, `f p := truncatedConjugate u M p − ⟪p, xc⟫ + u xc` is nonnegative, vanishes exactly at the
subgradients of `u` at `xc`, and has compact sublevel sets. -/
````

Original comment 47, line 1411:

````lean
/-! Subgradients and subgradient images of the truncated conjugate (task L-T11f3). -/
````

Original comment 48, line 1519:

````lean
/-- The set of slopes whose ball maximisers all lie in the open ball is open (weak Letwin route, N7,
task T11f3). -/
````

Original comment 49, line 1546:

````lean
/-- For strictly convex `u`, a subgradient `p` at a point `x` of the open ball has `x` as its only ball
maximiser (task T11f3). -/
````

Original comment 50, line 1623:

````lean
/-- **Danskin identification of subgradient images** (weak Letwin route, N7, task T11f3; KLS500
`convexSubgradientImage_truncatedLegendrePotential_eq_relative`): for strictly convex continuous `u`, on a set
`S` of slopes whose ball maximisers lie in the open ball, the subgradient image of the truncated conjugate is the
inverse subgradient image `{x | ∃ p ∈ S, p ∈ ∂u(x)}`. -/
````

Original comment 51, line 1665:

````lean
/-! The contact lemma on sublevel sets (task L-T11f5). -/
````

Original comment 52, line 1872:

````lean
/-- **Caffarelli's contact-set lemma below a level** (weak Letwin route, N6, task T11f5; KLS500
`supportContactSet_subsingleton_of_local_subgradient_bounds`): if `{u ≤ R}` is compact and the convex `u` has
two-sided Alexandrov bounds on compact subsets of `{u < R}`, then a supporting affine function at `x₀`
(`u x₀ < R`) touches the graph of `u` at no other point of `{u < R}`. No compactness of the full contact set
is assumed. -/
````

Original comment 53, line 1937:

````lean
/-! **Caffarelli's strict convexity** for moment-map potentials: a convex potential whose gradient pushes a measure with bounded density forward to one with density bounded above and below on a convex body is strictly convex (task L-T11f6). -/
````

Original comment 54, line 1941:

````lean
/-- **The moment potential is strictly convex** (weak Letwin route, N6, task T11f6; KLS500
`moment_strictConvexOn`): a convex Lipschitz `u` with `∫ e^{-u} = 1` whose gradient pushes `e^{-u} dx` forward
to `1_K e^{-V} dx` (`K` compact convex nonempty, `V` continuous) is strictly convex. -/
````

Original comment 55, line 2055:

````lean
/-! **The moment-map potential is C¹**: strict convexity of the conjugate gives differentiability of the potential (task L-T11f7). -/
````

Original comment 56, line 2105:

````lean
/-- **The moment potential is `C¹`** (weak Letwin route, N7, task T11f7; KLS500
`moment_contDiff_one_closedTarget`): a convex Lipschitz `u` with `∫ e^{-u} = 1` whose gradient pushes
`e^{-u} dx` forward to `1_K e^{-V} dx` (`K` compact convex with nonempty interior, `V` continuous) has exactly
one subgradient at every point, hence is continuously differentiable. -/
````

### formalization/FunctionalInequalities/Analysis/Convex/GradientLipschitz.lean

[Current source](../../formalization/FunctionalInequalities/Analysis/Convex/GradientLipschitz.lean)

Original comment 57, line 6:

````lean
/-!
# The C^{1,1} estimate for moment-map potentials

If the gradient of a convex Lipschitz potential `u` with `∫ e^{-u} = 1` pushes `e^{-u} dx` forward to a law with density
`e^{-V}` on a compact convex body, with `V` κ-strongly convex, then `∇u` is `16/κ`-Lipschitz (weak Letwin route, N9:
maximum principle for penalized second differences; task L-T17d). The earlier exact centered-difference
coefficient `4/κ` is exported for the actual weak Hessian regularity consumer. The existing `16/κ`
gradient interface and all source hypotheses are unchanged.
-/
````

Original comment 58, line 177:

````lean
/-- **`C^{1,1}` regularity of the moment potential** (weak Letwin route, N9, task T17d; KLS500
`weak_moment_mollify_hessian_upper`/`moment gradient Lipschitz`): if the `C¹` convex Lipschitz `u` with
`∫ e^{-u} = 1` pushes `e^{-u} dx` forward by `∇u` to `1_K e^{-V} dx` with `K` compact convex and `V ∈ C¹` such
that `V − (κ/2)‖·‖²` is convex, then `∇u` is `16/κ`-Lipschitz. -/
````

### formalization/FunctionalInequalities/Analysis/Convex/HessianIncrement.lean

[Current source](../../formalization/FunctionalInequalities/Analysis/Convex/HessianIncrement.lean)

Original comment 59, line 111:

````lean
/-- **Integrated energy of Hessian increments** (weak Letwin route, N11, task N11b; KLS500
`weak_moment_compact_hessian_increment_energy_bound`): for the `C^{1,1}` Monge–Ampère solution `u` with
`0 ≤ Δ²ₕu ≤ D‖h‖²`, every nonnegative `η ∈ C²_c` satisfies
`∫ η (‖H(x+h) − H(x)‖²_F + ‖H(x−h) − H(x)‖²_F) e^{−u} ≤ 2K² D ‖h‖² ∫ |η + Lη| e^{−u}`,
`Lη := tr(H⁻¹∇²η) − DV(∇u)(∇η)`. -/
````

### formalization/FunctionalInequalities/Analysis/Convex/HessianRegularity.lean

[Current source](../../formalization/FunctionalInequalities/Analysis/Convex/HessianRegularity.lean)

Original comment 60, line 14:

````lean
/-- **The Hessian of the `C^{1,1}` Monge–Ampère solution is in `H¹_loc`** (weak Letwin route, N11, task N11d; KLS500
`weak_moment_exists_third_tensor`): every entry of `∇²u` has a weak derivative along every coordinate direction, locally in
`L²`. -/
````

### formalization/FunctionalInequalities/Analysis/Convex/Normalization.lean

[Current source](../../formalization/FunctionalInequalities/Analysis/Convex/Normalization.lean)

Original comment 61, line 3:

````lean
/-!
# Affine normalisation of convex bodies

Maximal-volume simplices in a convex body and the elementary geometry of the standard simplex, used for the
affine normalisation step of Caffarelli's strict convexity argument (weak Letwin route, block T11d).

* `simplexEdgeMatrix`, `exists_max_simplexEdgeMatrix_det` (task L-T11d1);
* `abs_simplexCoord_le_one_of_max` (task L-T11d2);
* `closedBall_subset_stdSimplex_and_box_subset_closedBall` (task L-T11d3).
-/
````

Original comment 62, line 129:

````lean
/-! Coordinates relative to a maximal simplex are bounded (task L-T11d2). -/
````

Original comment 63, line 306:

````lean
/-! A ball inside the standard simplex and the box inside a ball (task L-T11d3). -/
````

Original comment 64, line 511:

````lean
/-! Affine normalisation of a convex body: an affine image sandwiched between two balls with dimensional radii (task L-T11d4). -/
````

### formalization/FunctionalInequalities/Analysis/Convex/Proximal.lean

[Current source](../../formalization/FunctionalInequalities/Analysis/Convex/Proximal.lean)

Original comment 65, line 18:

````lean
/-! The proximal point of a convex function and its Lipschitz dependence (task L-T12d2). -/
````

Original comment 66, line 126:

````lean
/-- The **proximal point** (resolvent of the subdifferential) of `f` at `z`: a point `x` such that
`z − x` is a subgradient of `f` at `x`, i.e. the minimiser of `x ↦ f x + ½‖x − z‖²` (weak Letwin route,
Alexandrov's theorem, task T12d2). For convex `f` on a finite-dimensional space it exists and is unique. -/
````

Original comment 67, line 189:

````lean
/-! Derivative of `½‖x‖² − (Moreau envelope)` and symmetry of the derivative of the resolvent (task L-T12d3). -/
````

Original comment 68, line 193:

````lean
/-- **The resolvent of a convex function is a gradient** (weak Letwin route, Alexandrov's theorem, task
T12d3): if `P z` is a point at which `z − P z` is a subgradient of the convex `f` (the proximal map), then
`w ↦ ½‖w‖² − (f (P w) + ½‖P w − w‖²)` (½‖·‖² minus the Moreau envelope) has derivative `⟪P z, ·⟫` at every `z`. -/
````

Original comment 69, line 233:

````lean
/-- **The derivative of the resolvent is symmetric and firmly nonexpansive** (task T12d3): at a point
where the proximal map `P` is differentiable with derivative `T`, `⟪T v, w⟫ = ⟪v, T w⟫` and
`‖T v‖² ≤ ⟪T v, v⟫`. -/
````

### formalization/FunctionalInequalities/Analysis/Convex/SecondDifference.lean

[Current source](../../formalization/FunctionalInequalities/Analysis/Convex/SecondDifference.lean)

Original comment 70, line 4:

````lean
/-!
# Second differences and Lipschitz gradients

A convex differentiable function with `u(x+h) + u(x−h) − 2u(x) ≤ C‖h‖²` has a quadratic upper bound, a co-coercive
gradient and a `4C`-Lipschitz gradient (final step of the `C^{1,1}` estimate of the weak moment-map route to Letwin
arXiv:2607.24164v1). Proof bodies: GPT (Letwin sub-controller tasks L-T4a, L-T4b, W0T4); statements by Claude and the
Letwin sub-controller; placement: Claude.
-/
````

Original comment 71, line 71:

````lean
/-! Co-coercivity of the gradient (task L-T4b). -/
````

Original comment 72, line 210:

````lean
/-! Lipschitz gradient from a second-difference bound (task W0T4). -/
````

Original comment 73, line 488:

````lean
/-! Second differences at maximisers of a penalized second difference (weak Letwin route, C^{1,1} estimate N9; task L-T17c). -/
````

Original comment 74, line 679:

````lean
/-- **Second-difference bound from penalised maxima** (weak Letwin route, N9, task T17c; KLS500
`weak_moment_symmetricSecondDifference_le_of_uniformlyConvex_target`, algebraic part): let `u` be convex and
differentiable, bounded below, and `V` differentiable with `V − (κ/2)‖·‖²` convex. Suppose that for every
`η > 0` the penalised second difference `Δ²ₕu − η u` has a maximiser `x₀` at which the log-density
`F := V ∘ ∇u − u` satisfies the comparison `F(x₀ + h) + F(x₀ − h) − 2 F(x₀) ≤ η n`. Then
`u(x + h) + u(x − h) − 2 u(x) ≤ 4 ‖h‖² / κ` everywhere. -/
````

### formalization/FunctionalInequalities/Analysis/Convex/SecondOrder.lean

[Current source](../../formalization/FunctionalInequalities/Analysis/Convex/SecondOrder.lean)

Original comment 75, line 10:

````lean
/-!
# Second-order differentiability of convex functions (Alexandrov's theorem)

First-order expansions of the subgradient through the resolvent of the subdifferential, integrated second
differences, and Alexandrov's theorem that a convex function has a second-order Taylor expansion almost everywhere
(weak Letwin route, block T12d).

* `subgradient_expansion_of_hasFDerivAt_resolvent` (task L-T12d4);
* `tendsto_integral_secondDifference_mul`, `integral_mul_le_integral_mul_sum_iteratedFDeriv` (task L-T12d7);
* `ae_exists_secondOrder_expansion` (task L-T12d6).
-/
````

Original comment 76, line 148:

````lean
/-- **Inverting the resolvent at a point of invertible differentiability** (weak Letwin route,
Alexandrov's theorem, task T12d4): let `P` be the resolvent of `f` (`z − P z` is a subgradient of `f` at
`P z` for every `z`). If `P` is differentiable at `z` with invertible derivative `T`, then `p₀ := z − P z` is
the only subgradient of `f` at `x := P z`, and every subgradient `q` of `f` at `y` near `x` satisfies
`‖q − p₀ − (T⁻¹ (y − x) − (y − x))‖ ≤ ε ‖y − x‖`. -/
````

Original comment 77, line 256:

````lean
/-! Second differences against smooth tests and their limit (task L-T12d7). -/
````

Original comment 78, line 378:

````lean
/-- **Second difference quotients converge to the distributional second derivative** (weak Letwin route,
task T12d7): for continuous `u` and `χ ∈ C²` with compact support,
`∫ (u(x + t v) + u(x − t v) − 2 u(x)) / t² · χ(x) dx → ∫ u(x) ∂²_v χ(x) dx` as `t → 0⁺`. -/
````

Original comment 79, line 450:

````lean
/-- **Fatou bound for the distributional second derivatives of a convex function** (weak Letwin route,
task T12d7, input of the distributional log-det inequality): if `g` is below the lower limit of a
nonnegative combination of second difference quotients of the convex `u` almost everywhere, then
`∫ g χ ≤ ∫ u ∑ᵢ cᵢ ∂²_{vᵢ} χ` for every nonnegative `χ ∈ C²` with compact support. -/
````

Original comment 80, line 581:

````lean
/-! **Alexandrov's theorem**: a convex function on a finite-dimensional space has a second-order Taylor expansion at almost every point (task L-T12d6). -/
````

Original comment 81, line 585:

````lean
/-- **Alexandrov's theorem** (A. D. Alexandrov 1939; Evans–Gariepy, *Measure theory and fine properties of
functions*, Thm 6.9; weak Letwin route, task T12d6): a convex function on a finite-dimensional real inner
product space has, at almost every point, a unique subgradient `p` and a second-order expansion
`f y = f x + ⟪p, y − x⟫ + ½ ⟪B (y − x), y − x⟫ + o(‖y − x‖²)` with a symmetric `B`. -/
````

### formalization/FunctionalInequalities/Analysis/Convex/Subgradient.lean

[Current source](../../formalization/FunctionalInequalities/Analysis/Convex/Subgradient.lean)

Original comment 82, line 11:

````lean
/-!
# Subgradients of convex functions

Pointwise subgradients are written inline, `∀ y, u x + ⟪p, y - x⟫ ≤ u y`. A differentiable convex function on a
finite-dimensional space is `C¹` (`contDiff_one_of_convexOn_of_differentiable`), and the subgradients of a convex
Lipschitz function lie in every closed convex set containing its a.e. gradient
(`subgradient_mem_of_ae_gradient_mem`). Weak moment-map route to Letwin arXiv:2607.24164v1, Theorem 1.2 (nodes N4,
N7 of build/reviews/2026-10-12-bkl-claude-goal/routes/letwin-weak-route.md). Proof bodies: GPT (BKL
Claude-controller goal, Letwin sub-controller tasks L-T5b, L-T11a); statements by the Letwin sub-controller;
placement: Claude.
-/
````

Original comment 83, line 197:

````lean
/-! Max formula and existence of subgradients (task L-T5a; proof body GPT, statement by the Letwin sub-controller). -/
````

Original comment 84, line 562:

````lean
/-! Convex functions on open sets are differentiable almost everywhere (task L-T14a0; proof body GPT, statement by the Letwin sub-controller). -/
````

Original comment 85, line 625:

````lean
/-! A unique subgradient gives differentiability (task L-T5c). -/
````

Original comment 86, line 849:

````lean
/-! Monotonicity of subgradient images (Gutiérrez Lemma 1.4.1; task L-T12a). -/
````

Original comment 87, line 1040:

````lean
/-! Almost-everywhere injectivity of the subgradient map (task L-T14a). -/
````

Original comment 88, line 1208:

````lean
/-! Subgradients along a segment where the function is affine form a null set (Caffarelli block; task L-T11b). -/
````

Original comment 89, line 1304:

````lean
/-! Unique subgradients everywhere give a `C¹` function (task L-T5d). -/
````

Original comment 90, line 1327:

````lean
/-! A first-order expansion of the subgradient gives a second-order Taylor expansion of the function (task L-T12d5). -/
````

Original comment 91, line 1405:

````lean
/-- **First-order expansion of the subdifferential gives a second-order Taylor expansion** (weak Letwin
route, Alexandrov's theorem, task T12d5): if every subgradient `q` of the convex `f` at points `y` near `x`
satisfies `‖q − p − B (y − x)‖ ≤ ε ‖y − x‖`, then
`|f y − f x − ⟪p, y − x⟫ − ½ ⟪B (y − x), y − x⟫| ≤ ε' ‖y − x‖²` near `x`. -/
````

### formalization/FunctionalInequalities/Analysis/Convex/Viscosity.lean

[Current source](../../formalization/FunctionalInequalities/Analysis/Convex/Viscosity.lean)

Original comment 92, line 8:

````lean
/-!
# Touching-test (viscosity) inequalities for convex functions

Pointwise consequences of touching a function from above or below by a `C²` test function, stated with the
coordinate Hessian `Probability.Stein.hessianMatrix` (weak Letwin route, steps N8/N12). Kept apart from
`Analysis/Convex/Alexandrov.lean`, which needs no Hessian machinery.

* `posSemidef_hessianMatrix_of_upper_touch` (task L-T12c3).
-/
````

Original comment 93, line 191:

````lean
/-! Second-order Taylor bound with the coordinate Hessian for `C²` test functions (task L-T12c2). -/
````

Original comment 94, line 410:

````lean
/-! Viscosity inequalities for Alexandrov solutions: the determinant of the Hessian of a `C²` test touching from above (below) is bounded below (above) by the Monge–Ampère density (task L-T12c4). -/
````

Original comment 95, line 774:

````lean
/-! At a point of second-order expansion the Monge–Ampère equation holds pointwise with a positive definite Hessian (task L-T12e1). -/
````

Original comment 96, line 778:

````lean
/-- `quadraticAt A x₀ b c` is smooth (weak Letwin route, task T12e1). -/
````

Original comment 97, line 832:

````lean
/-- The coordinate Hessian of `quadraticAt A x₀ b c` is `A` at every point when `A` is symmetric
(weak Letwin route, task T12e1). -/
````

Original comment 98, line 909:

````lean
/-- **The Monge–Ampère equation at points of second-order differentiability** (weak Letwin route, N8;
task T12e1): if the subgradient images of the convex `u` on open subsets of `Ω` carry the density `f`,
`f` is continuous and positive at `x₀ ∈ Ω`, and `u` has a second-order expansion at `x₀` with a symmetric
matrix `B` (`|u x − (u x₀ + ⟪g, x − x₀⟫ + ½ ⟪x − x₀, B (x − x₀)⟫)| ≤ ε ‖x − x₀‖²` near `x₀` for every
`ε > 0`), then `B` is positive definite and `det B = f x₀`. -/
````

Original comment 99, line 990:

````lean
/-! The log-determinant of the Hessian bounds the mollified Monge–Ampère density from above at points with positive definite Hessian (task L-T12d8). -/
````

Original comment 100, line 1324:

````lean
/-- **Mollified log-det lower bound** (weak Letwin route, N8/N9, task T12d8; KLS500
`weak_moment_mollified_average_det_lower`, via Fatou instead of the viscosity–distribution lemma): if the
convex `u` has at almost every point a second-order expansion with a positive definite symmetric matrix
`B` with `F x ≤ log det B`, `F` continuous, then every mollification `uφ := φ.normed ⋆ u` has a positive
definite Hessian with `(φ.normed ⋆ F)(x) ≤ log det ∇²uφ(x)`. -/
````

Original comment 101, line 1407:

````lean
/-! **The Monge–Ampère equation almost everywhere**: an Alexandrov solution has, at almost every point, a quadratic expansion with positive definite Hessian whose determinant equals the density (task L-T12d6b). -/
````

Original comment 102, line 1411:

````lean
/-- **Alexandrov's theorem in coordinates** (weak Letwin route, task T12d6b): a convex function on
`EuclideanSpace ℝ (Fin n)` has, at almost every point `x`, a second-order expansion
`|u y − quadraticAt B x g (u x) y| ≤ ε ‖y − x‖²` near `x` with a symmetric matrix `B`. -/
````

Original comment 103, line 1440:

````lean
/-- **The a.e. Monge–Ampère equation for an Alexandrov solution** (weak Letwin route, N8, task T12d6b):
if the subgradient images of the convex `u` on open sets carry a continuous positive density `f`, then at
almost every point `u` has a second-order expansion with a positive definite symmetric `B`, `det B = f x`. -/
````

Original comment 104, line 1471:

````lean
/-! Existence of a penalized maximum with a quadratic comparison function (C^{1,1} estimate N9; task L-T17b). -/
````

Original comment 105, line 1704:

````lean
/-- **A penalised maximum with the log-density comparison** (weak Letwin route, N9, task T17b; KLS500
`exists_weak_moment_maximum_with_target_comparison`): let the convex, Lipschitz, coercive `u` be an Alexandrov
solution `vol ∂u(G) = ∫_G e^F` with continuous `F`, and let `uₖ` be `C²` approximations, uniformly close to `u`,
with positive definite Hessians satisfying `Fₖ ≤ log det ∇²uₖ` for `Fₖ → F` locally uniformly. Then for
every `η > 0`, `Δ²ₕu − η u` has a maximiser `x₀` with `F(x₀ + h) + F(x₀ − h) − 2 F(x₀) ≤ η n`. -/
````

Original comment 106, line 1809:

````lean
/-! Coercivity of `tr(A) − log det` around the identity and the a.e. bound of Hessian increments by the generator (weak Letwin route N11; task L-N11a). -/
````

Original comment 107, line 1901:

````lean
/-- **Three-point log-det concavity** (weak Letwin route, N11, task N11a): for positive definite `A, B₊, B₋ ≤ K·Id`,
`(‖B₊ − A‖²_F + ‖B₋ − A‖²_F)/(2K²) ≤ tr(A⁻¹(B₊ + B₋ − 2A)) − log det B₊ − log det B₋ + 2 log det A`. -/
````

Original comment 108, line 1918:

````lean
/-- **Pointwise coercivity of Hessian increments for a `C^{1,1}` Monge–Ampère solution** (weak Letwin route, N11, task
N11a; KLS500 `weak_moment_centered_difference_coercivity_ae`): if a.e. `∇²u` is positive definite, `≤ K·Id`, and
`log det ∇²u = −u + V(∇u)` with `V` convex and differentiable, then for every `h`, at a.e. `x`, with
`w := u(· + h) + u(· − h) − 2u` and `H := ∇²u`,
`(‖H(x+h) − H(x)‖²_F + ‖H(x−h) − H(x)‖²_F)/(2K²) ≤ tr(H(x)⁻¹ ∇²w(x)) − DV(∇u(x))(∇w(x)) + w(x)`. -/
````

### formalization/FunctionalInequalities/Analysis/Sard/Equidimensional.lean

[Current source](../../formalization/FunctionalInequalities/Analysis/Sard/Equidimensional.lean)

Original comment 120, line 130:

````lean
/-! Lipschitz maps between spaces of equal dimension send null sets to null sets (task L-T12d1). -/
````

Original comment 121, line 134:

````lean
/-- **Lipschitz maps send null sets to null sets** (weak Letwin route, Alexandrov's second-order
differentiability theorem, task T12d1): for a map of a finite-dimensional real inner product space into
itself that is Lipschitz on `s`, a Lebesgue-null `s` has a Lebesgue-null image. No measurability of `s`
is assumed. -/
````

### formalization/FunctionalInequalities/Analysis/WeakDerivative/Approximation.lean

[Current source](../../formalization/FunctionalInequalities/Analysis/WeakDerivative/Approximation.lean)

Original comment 128, line 20:

````lean
/-! Gluing local weak derivatives along cutoffs into a global one (task L-N11c2). -/
````

Original comment 129, line 24:

````lean
/-- **Gluing local weak derivatives** (weak Letwin route, N11, task N11c2, generic): if for every `C¹` cutoff `χ` with
compact support the product `χ f` has a weak derivative along `v` that is locally `L²`, then `f` itself has a weak
derivative along `v` that is `L²` on every compact set. -/
````

### formalization/FunctionalInequalities/Analysis/WeakDerivative/Mollification.lean

[Current source](../../formalization/FunctionalInequalities/Analysis/WeakDerivative/Mollification.lean)

Original comment 130, line 19:

````lean
/-! Mollification commutes with weak directional derivatives (task L-W3b1). -/
````

Original comment 131, line 23:

````lean
/-- **Mollification commutes with weak derivatives** (weak Letwin route, task W3b1, generic): if `g` is the weak derivative
of `f` along `v`, then `φ.normed ⋆ f` is smooth with `∂ᵥ(φ.normed ⋆ f) = φ.normed ⋆ g`. -/
````

Original comment 132, line 94:

````lean
/-! Uniform `L²` bounds on difference quotients give a weak derivative in `L²` (task L-N11c1). -/
````

Original comment 133, line 177:

````lean
/-- **Difference-quotient criterion for a weak derivative in `L²`** (Nirenberg; Evans PDE §5.8.2 Thm 3(ii); weak Letwin
route, N11, task N11c1): if `f ∈ L²` and `∫ (f(x + t v) − f(x))² ≤ C t²` for all small `t ≠ 0`, then `f` has a weak
derivative along `v` that lies in `L²`. -/
````

## 03-analysis-tools

### formalization/FunctionalInequalities/Analysis/BakryEmery/Bochner/Lipschitz.lean

[Current source](../../formalization/FunctionalInequalities/Analysis/BakryEmery/Bochner/Lipschitz.lean)

Original comment 1, line 6:

````lean
/-!
# Bochner's identity at `C^{1,1}`

`∫ (ℒf)² dν = ∫ (‖∇²f‖² + ⟪D∇U ∇f, ∇f⟫) dν` for compactly supported smooth `f` and a Lipschitz `C¹` potential `U` with
Lipschitz gradient (route node N14). Proof body: GPT (task L-T8b); statement by the Letwin sub-controller; placement: Claude.
-/
````

### formalization/FunctionalInequalities/Analysis/BakryEmery/Calculus.lean

[Current source](../../formalization/FunctionalInequalities/Analysis/BakryEmery/Calculus.lean)

Original comment 2, line 402:

````lean
/-- **Product rule for the Hessian quadratic/bilinear form**: for `f, g ∈ C²`,
`D²(fg)(x)(u, v) = f(x) D²g(x)(u, v) + g(x) D²f(x)(u, v) + Df(x)u · Dg(x)v + Dg(x)u · Df(x)v`
(Letwin (2.3) prerequisite; `laplacian_mul` is the identity-metric trace of this; Luna, task LET23-H). -/
````

Original comment 3, line 709:

````lean
/-- **Letwin (2.3), the product rule for `L_{A,b}`** with symmetric `A(x)`:
`L(fg) = f Lg + g Lf + 2 ∑_{ij} A_{ij} ∂_i f ∂_j g` (Luna, task LET23-N round 7; the three private helpers
above are Luna proof implementation). -/
````

Original comment 4, line 798:

````lean
/-- A `C^∞` function with compact support has a bounded second derivative (Luna, task R8s-2; one
closing step replaced by `ContinuousLinearMap.opNorm_zero` at integration). -/
````

### formalization/FunctionalInequalities/Analysis/BakryEmery/Cumulant/Basic.lean

[Current source](../../formalization/FunctionalInequalities/Analysis/BakryEmery/Cumulant/Basic.lean)

Original comment 5, line 5:

````lean
/-!
# The logarithmic Laplace transform and cumulant tensors

Bizeul–Klartag–Lehec (arXiv:2610.05474v1), Section 4 and the linear step of Proposition 7.1. For a
nonzero finite measure `μ` with all exponential moments, `Λ_μ(z) = log ∫ e^{⟪z, x⟫} dμ(x)` is smooth,
the tilt average of a linear function is a directional derivative, `F_{⟪v,·⟫}(z) = DΛ_μ(z) v`, and
the Taylor tensors of linear functions are cumulant tensors,
`T_d ⟪v, ·⟫ = κ_{d+1}(v, ·, …, ·) / d!` with `κ_m = ∇^m Λ_μ(0)`.

The third cumulant of a centered law is its third moment. Conditionally on the quadratic-form
estimate of Letwin (2026, Theorem 1.2), stated as the explicit premise `LetwinQuadraticBound`, a
centered isotropic probability law with all exponential moments satisfies `R^μ_3 ≤ 8 Id`
(BKL Lemma 4.2 in that conditional, restricted form; the Letwin estimate is not proved here).

Cumulants of order `k ≥ 2` transform along affine maps `x ↦ T(x − a)` through the adjoint of `T`
(`cumulant_map_affine`, BKL (77)); proof body: GPT (BKL Claude-controller goal, task T1b), statement and
placement: Claude.

`LetwinQuadraticBound` is closed under convergence of mixed moments of degree at most four
(`letwinQuadraticBound_of_tendsto_moments`, Letwin arXiv:2607.24164v1, last sentence of Lemma A.1); proof body:
GPT (Letwin sub-controller task L-T10e), statement by the Letwin sub-controller, placement: Claude.
-/
````

Original comment 6, line 178:

````lean
/-- **Local tilt-average/derivative identity**: `F_{⟪v,·⟫}(z) = ∂_v Λ_μ(z)` for `‖z‖ < r`, assuming
only the single exponential moment `∫ e^{r‖x‖} dμ < ∞` (Luna, task R4b2). -/
````

Original comment 7, line 709:

````lean
/-- **Linear-function step in an arbitrary orthonormal basis** (BKL p. 30): the special case
`norm_coordTensor_taylorTensor_inner_sq_le` with `stdOrthonormalBasis ℝ E` replaced by any orthonormal
basis `bE` (Luna, task B3g). -/
````

Original comment 8, line 750:

````lean
/-- **Local smoothness of `Λ_μ`** (BKL p. 29, "finite and smooth in a neighborhood of the origin"):
one positive norm-exponential moment `∫ e^{r‖x‖} dμ < ∞` makes `Λ_μ` `C^∞` on the open ball of
radius `r`. Provenance: Codex wrapper over the Luna local bodies in `Tilt/Local.lean`. -/
````

Original comment 9, line 797:

````lean
/-- **Cumulants along a linear isometry**: `κ^{φ_*ν}_k(φ u₁, …, φ u_k) = κ^ν_k(u₁, …, u_k)` for
every measure `ν`, since `Λ_{φ_*ν} = Λ_ν ∘ φ⁻¹` pointwise (Luna, task T1b). -/
````

### formalization/FunctionalInequalities/Analysis/BakryEmery/Cumulant/Truncation.lean

[Current source](../../formalization/FunctionalInequalities/Analysis/BakryEmery/Cumulant/Truncation.lean)

Original comment 10, line 5:

````lean
/-!
# Cumulants of ball truncations converge

For a probability measure with one exponential moment `∫ e^{r‖x‖} < ∞`, the cumulants of the conditional laws on
the balls `B(0, R)` converge to its cumulants as `R → ∞` (`tendsto_cumulant_cond_closedBall`): cumulants are a fixed
continuous function (Faà di Bruno, `FormalMultilinearSeries.taylorComp`) of the moment jets at `0`, and the
truncated moment tensors converge. Used to reduce BKL arXiv:2610.05474v1, Theorem 4.1, to compactly supported laws
(p. 19, end of Section 6). Proof body: Fable worker (BKL Claude-controller goal, task S8b); statement and
placement: Claude.
-/
````

### formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts/InverseHessian/Weak.lean

[Current source](../../formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts/InverseHessian/Weak.lean)

Original comment 11, line 766:

````lean
/-- **The Hessian-metric generator at `C^{1,1}` is symmetric** (Letwin arXiv:2607.24164v1 (2.2), weak form; weak Letwin
route, N10, task N10b): for the `C^{1,1}` Monge–Ampère solution `u` (`det ∇²u = e^{−u + V(∇u)}` a.e., the right side
Lipschitz), with `L f := tr((∇²u)⁻¹ ∇²f) − DV(∇u)(∇f)`, every `w ∈ C¹` with Lipschitz gradient and every `η ∈ C²` with compact
support satisfy `∫ η (L w) e^{−u} = −∫ ⟨(∇²u)⁻¹ ∇η, ∇w⟩ e^{−u}`. -/
````

### formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts/LipschitzHessian.lean

[Current source](../../formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts/LipschitzHessian.lean)

Original comment 12, line 6:

````lean
/-!
# Mean of the Hessian at `C^{1,1}`

`∫⟪D(∇φ)u, v⟫ dν = ∫ ∂_uφ ∂_vφ dν` for `ν = e^{−φ}dx` with `φ` convex `C¹` with Lipschitz gradient (Letwin
arXiv:2607.24164v1, Lemma 2.3, analytic part, weak route). Proof body: GPT (task L-T15a); statement by the Letwin
sub-controller; placement: Claude.
-/
````

### formalization/FunctionalInequalities/Analysis/BakryEmery/IteratedDerivative.lean

[Current source](../../formalization/FunctionalInequalities/Analysis/BakryEmery/IteratedDerivative.lean)

Original comment 13, line 355:

````lean
/-- **Local symmetry of iterated derivatives**: for `f ∈ C^∞(U)`, `U` open, the iterated
derivatives at `x ∈ U` are symmetric in their arguments (localization of
`iteratedFDeriv_comp_perm_of_contDiff` by a smooth cutoff; Luna, task R5a3). -/
````

Original comment 14, line 413:

````lean
/-- **Chain rule for iterated derivatives along a continuous linear map, on an open set**:
`∇ⁿ(g ∘ L)(x) = ∇ⁿg(Lx) ∘ (L, …, L)` when `g ∈ Cⁿ(U)`, `U` open, `Lx ∈ U` (Luna, task R5a). -/
````

### formalization/FunctionalInequalities/Analysis/BakryEmery/Tilt/Local.lean

[Current source](../../formalization/FunctionalInequalities/Analysis/BakryEmery/Tilt/Local.lean)

Original comment 15, line 3:

````lean
/-!
# Exponential-weight integrals under local moments

The `Tilt/SquareIntegrable.lean` machinery assumes integrability against every exponential weight.
Here only `∀ t < r, ∫ e^{t‖x‖} ‖g x‖ < ∞` is assumed (one open radius `r`), as needed for laws with
local exponential moments such as the Laplace noise of Bizeul–Klartag–Lehec (arXiv:2610.05474v1),
Proposition 7.1. Then `z ↦ ∫ e^{⟪z, x⟫} g(x) dμ` is `C^∞` on the open ball of radius `r`.

* `weightedExpD_integrable_lt`: the invariant passes to the derivative amplitude (same radius).
* `weightedExp_integral_hasFDerivAt_of_lt`: differentiation under the integral inside the ball.
* `weighted_integral_contDiffOn`: `C^∞` on `ball 0 r`, by induction on the order.

Provenance: the first two bodies are unchanged Luna proofs (tasks Q6-1, Q6-2); the finite-order
induction and the universe adapter are Codex proofs, independently reviewed
(`build/reviews/2026-10-07-bkl-continuous/reviews/REVIEW-Q6-local-assembly-independent.md`).
-/
````

### formalization/FunctionalInequalities/Analysis/BakryEmery/Tilt/SquareIntegrable.lean

[Current source](../../formalization/FunctionalInequalities/Analysis/BakryEmery/Tilt/SquareIntegrable.lean)

Original comment 16, line 287:

````lean
/-- `F_f(z) · ∫ e^{⟪z,x⟫} dμ = ∫ e^{⟪z,x⟫} f(x) dμ` whenever `∫ e^{⟪z,x⟫} dμ ≠ 0`
(Luna, task RED-D1a). -/
````

### formalization/FunctionalInequalities/Analysis/BakryEmery/WeakHessian.lean

[Current source](../../formalization/FunctionalInequalities/Analysis/BakryEmery/WeakHessian.lean)

Original comment 17, line 14:

````lean
/-! Weak-route support for Letwin arXiv:2607.24164v1. Proof body: the independently
checked existing L-N11e-third-derivative-symmetry candidate; placement and acceptance: Codex closeout. -/
````

Original comment 18, line 148:

````lean
/-- **Symmetry of the weak third derivative** (weak Letwin route, N11, task N11e): for `u ∈ C¹` with Lipschitz gradient, if
`T · k i j` is the weak derivative of the Hessian entry `Hᵢⱼ` along `eₖ` for all indices, then a.e. `Tₖᵢⱼ = Tᵢₖⱼ` and
`Tₖᵢⱼ = Tₖⱼᵢ`. -/
````

### formalization/FunctionalInequalities/Analysis/Gronwall.lean

[Current source](../../formalization/FunctionalInequalities/Analysis/Gronwall.lean)

Original comment 109, line 5:

````lean
/-!
# Integral Grönwall inequality

`φ(t) ≤ a + K ∫₀ᵗ φ` on `[0, T]` for a measurable bounded `φ` and `K ≥ 0` gives `φ(t) ≤ a e^{Kt}`, any real
`a` (Mathlib has the differential and discrete forms). Proof bodies: GPT (BKL Claude-controller goal, tasks S5cd); statements and placement: Claude.
-/
````

### formalization/FunctionalInequalities/Analysis/Matrix/LogDet.lean

[Current source](../../formalization/FunctionalInequalities/Analysis/Matrix/LogDet.lean)

Original comment 110, line 10:

````lean
/-!
# Inequalities for the log-determinant

Two matrix facts used on the weak moment-map route to Letwin's quadratic-form bound
(arXiv:2607.24164v1, Theorem 1.2; BKL arXiv:2610.05474v1, Lemma 4.2):

- `forall_posDef_add_log_det_le_trace_iff`: `log det` as an infimum of linear functions,
  `(∀ J ≻ 0, b + log det J + n ≤ tr(J A)) ↔ (A ≻ 0 ∧ e^b ≤ det A)` for positive semidefinite `A`
  (the distributional form of the Monge–Ampère equation);
- `log_det_add_frobenius_sq_le`: quantitative concavity, for positive definite `A, B ≤ K·Id`,
  `log det B + ‖B − A‖²_F/(2K²) ≤ log det A + tr(A⁻¹(B − A))` (the difference-quotient estimate of the
  Hessian of the moment map).

Proof bodies: GPT (BKL Claude-controller goal, tasks W0T2 and W0T1); statements and placement: Claude.
-/
````

### formalization/FunctionalInequalities/Analysis/Matrix/Piola.lean

[Current source](../../formalization/FunctionalInequalities/Analysis/Matrix/Piola.lean)

Original comment 111, line 8:

````lean
/-!
# The Piola identity for Hessian adjugates

`Σⱼ ∂ⱼ adj(∇²u)ᵢⱼ = 0` for `C³` functions `u` (`sum_fderiv_adjugate_hessianMatrix_eq_zero`), in terms of
`Probability.Stein.hessianMatrix`; the smooth input of the weak Piola identity on the moment-map route to Letwin
arXiv:2607.24164v1. Proof body: GPT (Letwin sub-controller task L-T6a); statement by the Letwin sub-controller;
placement: Claude. The cofactor consumers also supply essential boundedness from a Lipschitz gradient and weak adjugate derivatives from a given local-L2 Hessian tensor; they do not assume smoothness of that tensor or prove the main bound.
-/
````

Original comment 112, line 281:

````lean
/-! The weak Piola identity for `C¹` functions with Lipschitz gradient (task L-T6b). -/
````

Original comment 113, line 500:

````lean
/-! The weak Piola identity for Lipschitz gradients and the divergence form of the inverse Hessian (weak Letwin route N10; task L-N10a). -/
````

Original comment 114, line 807:

````lean
/-- **Weak Piola identity with Lipschitz tests** (weak Letwin route, N10, task N10a): for `u ∈ C¹` with Lipschitz
gradient and a Lipschitz `ψ` with compact support (`fderiv ℝ ψ` its a.e. derivative),
`∑ⱼ ∫ (adj ∇²u)ᵢⱼ ∂ⱼψ = 0`. -/
````

Original comment 115, line 900:

````lean
/-- **Divergence of the inverse Hessian** (weak Letwin route, N10, task N10a): if moreover `det ∇²u = e^F` a.e. for a
Lipschitz `F`, then for Lipschitz `ψ` with compact support
`∑ⱼ ∫ (∇²u)⁻¹ᵢⱼ ∂ⱼψ = ∑ⱼ ∫ (∇²u)⁻¹ᵢⱼ ∂ⱼF ψ`, i.e. `div (∇²u)⁻¹ = −(∇²u)⁻¹ ∇F` weakly. -/
````

### formalization/FunctionalInequalities/Analysis/Mollification/Basic.lean

[Current source](../../formalization/FunctionalInequalities/Analysis/Mollification/Basic.lean)

Original comment 116, line 439:

````lean
/-! Derivative of a normalized-bump convolution with a Lipschitz function (proof body: GPT, Letwin sub-controller
task L-T8a1; statement by the Letwin sub-controller; placement: Claude). -/
````

Original comment 117, line 554:

````lean
/-! Weak-route support for Letwin arXiv:2607.24164v1. Proof body: the independently
checked existing L-W3b2a-mollified-values-convex candidate; placement and acceptance: Codex closeout. -/
````

Original comment 118, line 564:

````lean
/-- **Mollified values stay in a closed convex set** (weak Letwin route, task W3b2a, generic): if the vector of values
`(f k x)ₖ` lies in a closed convex `C` for almost every `x` in `cthickening r S`, then for every bump `φ` with
`φ.rOut ≤ r` and every `x ∈ S`, the mollified vector `((φ.normed ⋆ f k) x)ₖ` lies in `C`. -/
````

### formalization/FunctionalInequalities/Analysis/Operator/HilbertSchmidt.lean

[Current source](../../formalization/FunctionalInequalities/Analysis/Operator/HilbertSchmidt.lean)

Original comment 119, line 4:

````lean
/-!
# Standard trace and Hilbert–Schmidt norm

`stdTrace` and `hsNormSq` in the standard basis of a finite-dimensional inner-product space, with operator norm ≤
Hilbert–Schmidt ≤ trace for positive operators and the Cauchy–Schwarz and composition bounds (Lyapunov estimates of the
cutoff localization). Proof bodies: GPT (task S-O1); statements by the S-line sub-controller; placement: Claude.
-/
````

### formalization/FunctionalInequalities/Analysis/Tensor/EnergyForm.lean

[Current source](../../formalization/FunctionalInequalities/Analysis/Tensor/EnergyForm.lean)

Original comment 122, line 3:

````lean
/-!
# The energy form of a coordinate tensor

`energyForm A T = ⟨T, (A⁻¹)^{⊗r} T⟩` for an operator `A` and an order-`r` coordinate tensor `T` (BKL arXiv:2610.05474v1, p. 22,
`F(A, T)`), the standard matrix of an operator, `energyForm 1 T = |T|²`, and smoothness near invertible `A`. Proof bodies:
GPT (S-line sub-controller task S-3bF); statements by the S-line sub-controller; placement: Claude.
-/
````

Original comment 123, line 89:

````lean
/-! First derivative of the energy form at `A = Id` (BKL (88), first order; task S-3bF2). -/
````

Original comment 124, line 413:

````lean
/-! Helpers for the second-order expansion of the energy form: a double-erasure product sum and line derivatives of `⟪(1 + tB)⁻¹ ·, ·⟫` (task S-3bF3b1). -/
````

Original comment 125, line 646:

````lean
/-! Second derivative of the energy form along lines and at the identity (BKL (88), second order; task S-3bF3b2). -/
````

### formalization/FunctionalInequalities/Analysis/Tensor/SlotAction.lean

[Current source](../../formalization/FunctionalInequalities/Analysis/Tensor/SlotAction.lean)

Original comment 126, line 3:

````lean
/-!
# Matrices acting on one slot of a coordinate tensor

Order-`r` coordinate tensors on `ℝⁿ`, their Euclidean inner product, the action `H^{(s)}` of a matrix on the `s`-th input
and `Σ_H = Σ_s H^{(s)}` (BKL arXiv:2610.05474v1, p. 23), and the algebra (89)–(91) of the proof of Lemma 5.1 at `A = Id`:
the drift expression is at least `½ Σ|W_i|² − 17 m² |T|² − 2⟨T, L⟩` when `Σ_i H_i² ≤ 8 Id`. Proof body: GPT (BKL
Claude-controller goal, task S3a); statement and placement: Claude.
-/
````

Original comment 127, line 258:

````lean
/-! Commutation and inner-product algebra of slot actions (task S-3bF3a). -/
````

## 04-kls-bkl

### formalization/FunctionalInequalities/KLS/BKL/CompactReduction.lean

[Current source](../../formalization/FunctionalInequalities/KLS/BKL/CompactReduction.lean)

Original comment 134, line 8:

````lean
/-!
# Reduction of BKL Theorem 4.1 to compactly supported laws

Bizeul–Klartag–Lehec arXiv:2610.05474v1, p. 19: Theorem 4.1 is proved first for compactly supported
isotropic log-concave laws (`CumulantBoundCompact`), whose localization coefficients are smooth and
bounded. `LetwinCompactBound` is Letwin's quadratic-form bound (arXiv:2607.24164v1, Theorem 1.2) for
compactly supported laws: the interface between the Letwin stream and the Theorem 4.1 stream. It gives
the base case `CumulantBoundCompact 2 8` (BKL Lemma 4.2). Both names are hypotheses; neither Letwin's
theorem nor Theorem 4.1 is proved here. Proof bodies: GPT (BKL Claude-controller goal, task S8a);
statements and placement: Claude.
-/
````

Original comment 135, line 103:

````lean
/-! Reduction to compactly supported laws (BKL p. 19 and end of Section 6): `cumulantBound_of_compact`. Proof body: Fable worker (task S8c); statement: Claude. -/
````

### formalization/FunctionalInequalities/KLS/BKL/CumulantEnergy/Basic.lean

[Current source](../../formalization/FunctionalInequalities/KLS/BKL/CumulantEnergy/Basic.lean)

Original comment 136, line 3:

````lean
/-!
# Cumulant energies and the middle term `L_m` of the localization

Bizeul–Klartag–Lehec arXiv:2610.05474v1, (72) and (75)–(76), at a fixed law `ν` with covariance `A` and
`σ = A^{-1/2}`: the middle term `L_m(h) = Σ_{J ∋ i₀, 2 ≤ |J|, |Jᶜ| ≥ 2} ⟪κ_{|J|+1}(h_J, ·), A⁻¹ κ_{m−|J|+1}(h_{Jᶜ}, ·)⟫`
(`lowerDrift`, in the mask form of `Analysis/BakryEmery/Cumulant/Leibniz.lean`) and the cumulant energy
`E_{r+1} = |κ_{r+1}(u)|²_A = Σ_J κ_{r+1}(u, σ e_{J_1}, …, σ e_{J_r})²` (`cumulantEnergy`). Definitions only;
statements and placement: Claude (BKL Claude-controller goal).
-/
````

Original comment 137, line 46:

````lean
/-! Section 6 pointwise bound (BKL (99)–(102) and the pointwise triangle inequality behind (104)): `sqrt_lowerDrift_energy_le`. Proof body: Fable worker (task S4); statement: Claude. -/
````

### formalization/FunctionalInequalities/KLS/BKL/CumulantEnergy/Conjugation.lean

[Current source](../../formalization/FunctionalInequalities/KLS/BKL/CumulantEnergy/Conjugation.lean)

Original comment 138, line 3:

````lean
/-!
# Cumulant energies as energy forms

`E_{r+1}(u) = F(PAP, P^{⊗r} κ_{r+1}(u, ·))` for the standard-coordinate cumulant tensor (BKL (83), (85)): the reduction of
Lemma 5.1 to `A = Id`. Proof body: GPT (task S-3bJ); statement by the S-line sub-controller; placement: Claude.
-/
````

### formalization/FunctionalInequalities/KLS/BKL/LetwinApproximation.lean

[Current source](../../formalization/FunctionalInequalities/KLS/BKL/LetwinApproximation.lean)

Original comment 139, line 7:

````lean
/-!
# Reduction of the compact Letwin bound to the regular class

`letwinCompactBound_of_regularClass`: if Letwin's quadratic-form bound holds for every isotropic law with density
`1_K e^{-W}` (K a compact convex body, W smooth and κ-strongly convex), it holds for every compactly supported isotropic
log-concave law, i.e. `LetwinCompactBound` (Letwin arXiv:2607.24164v1, Lemma A.1 approximation by Gaussian smoothing,
ball conditioning and whitening; task L-T10f).
-/
````

Original comment 140, line 58:

````lean
/-- **Reduction of the compact Letwin bound to Letwin's regular class** (Letwin arXiv:2607.24164v1, Lemma A.1, task
T10f): if every isotropic law `1_K e^{−W} dx` with `K` compact convex with nonempty interior and `W` smooth and
uniformly convex satisfies Letwin's quadratic bound, then so does every compactly supported isotropic log-concave law
in positive dimension (`LetwinCompactBound`). -/
````

### formalization/FunctionalInequalities/KLS/BKL/Localization/Coefficients.lean

[Current source](../../formalization/FunctionalInequalities/KLS/BKL/Localization/Coefficients.lean)

Original comment 141, line 5:

````lean
/-!
# Coefficients and generator of the Eldan localization equations

Bizeul–Klartag–Lehec arXiv:2610.05474v1, (67), compact-prior stage: the parameter space `p = (c, Q)`, the posterior
covariance `A(p)`, the drift `(A⁻¹ a, A⁻¹)`, the noise columns `(A^{-1/2} e_k, 0)`, the generator
`𝓛F = DF[(A⁻¹a, A⁻¹)] + ½ Σ_k D²F[(A^{-1/2}e_k, 0), (A^{-1/2}e_k, 0)]`, and the cutoff coefficients
`γ² · drift`, `γ · noise` for an admissible cutoff `γ`, with `𝓛_γ F = γ² 𝓛F` and the admissibility of the cutoff
coefficients (globally Lipschitz, bounded, compactly supported) for an isotropic compact prior. Statements and placement:
Claude; proof bodies: Fable worker (BKL Claude-controller goal, task S5d1).
-/
````

### formalization/FunctionalInequalities/KLS/BKL/Localization/CovarianceGenerator.lean

[Current source](../../formalization/FunctionalInequalities/KLS/BKL/Localization/CovarianceGenerator.lean)

Original comment 142, line 7:

````lean
/-!
# The generator of the posterior covariance

The carré-du-champ product rule for the generator, `𝓛 ∫ f dμ_p = 0` for posterior expectations, and
`𝓛⟪A x, y⟫ = −⟪A x, y⟫` (BKL arXiv:2610.05474v1, (69)). Proof bodies: GPT (task S-3bA); statements by the S-line
sub-controller; placement: Claude.
-/
````

### formalization/FunctionalInequalities/KLS/BKL/Localization/CumulantDerivative.lean

[Current source](../../formalization/FunctionalInequalities/KLS/BKL/Localization/CumulantDerivative.lean)

Original comment 143, line 5:

````lean
/-!
# Parameter derivatives of posterior cumulants

Posterior cumulants are jointly smooth in the parameters and `D_c κ_m(μ_p)(h)[v] = κ_{m+1}(μ_p)(h, v)` (BKL (81)); covariance
entries are second cumulants. Proof bodies: GPT (task S-3bD); statements by the S-line sub-controller; placement: Claude.
-/
````

### formalization/FunctionalInequalities/KLS/BKL/Localization/CumulantGenerator.lean

[Current source](../../formalization/FunctionalInequalities/KLS/BKL/Localization/CumulantGenerator.lean)

Original comment 144, line 6:

````lean
/-!
# BKL Lemma 4.3 in generator form

For `m ≥ 3`, every slot `i₀` and directions `h`, `𝓛_p κ_m(μ_p)(h) = −(m κ_m(h) + L_m(h))` with `L_m` the middle term (72)
(`generator_cumulant_posterior`): the generator commutes with `D_z^m` (coefficients independent of `z`), (71) gives
`𝓛Λ_p(z) = −½⟪v, A⁻¹v⟫`, and the grouped Leibniz expansion (74) finishes. Proof body: Fable worker (BKL Claude-controller
goal, task S1c); statement and placement: Claude.
-/
````

### formalization/FunctionalInequalities/KLS/BKL/Localization/CutoffEnergy/Boundary.lean

[Current source](../../formalization/FunctionalInequalities/KLS/BKL/Localization/CutoffEnergy/Boundary.lean)

Original comment 145, line 26:

````lean
/-! Boundary-term split for the ball cutoff and a mean-value choice of the horizon in `[T₀, 2T₀]` (task S-7b2). -/
````

### formalization/FunctionalInequalities/KLS/BKL/Localization/CutoffEnergy/Induction.lean

[Current source](../../formalization/FunctionalInequalities/KLS/BKL/Localization/CutoffEnergy/Induction.lean)

Original comment 146, line 17:

````lean
/-! The strong induction over the order and Theorem 4.1 for compactly supported laws with `K = 153`, given the induction step and the claim-to-bound passage as hypotheses (task S-7d). -/
````

### formalization/FunctionalInequalities/KLS/BKL/Localization/CutoffEnergy/Step.lean

[Current source](../../formalization/FunctionalInequalities/KLS/BKL/Localization/CutoffEnergy/Step.lean)

Original comment 147, line 14:

````lean
/-!
# The induction step of BKL Theorem 4.1 in cutoff form

`cutoffEnergyClaim_succ`: the cutoff energy claim (95) at order `m` from the lower orders, combining Lemma 5.2 in
cutoff form (`EnergyIntegral.lean`), the Section 6 bound (104), the Lyapunov moment and tail bounds, the boundary
mean-value step and the envelope arithmetic (105)–(106) (BKL arXiv:2610.05474v1, pp. 24–27; task S-7b3).
Lemma 5.1 enters as the named hypothesis `Lemma51Bound`, the exact statement of `generator_cumulantEnergy_ge`.
-/
````

### formalization/FunctionalInequalities/KLS/BKL/Localization/CutoffEnergy/ToCumulant.lean

[Current source](../../formalization/FunctionalInequalities/KLS/BKL/Localization/CutoffEnergy/ToCumulant.lean)

Original comment 148, line 25:

````lean
/-! From the cutoff energy claim to the compact cumulant bound (task S-7c). -/
````

### formalization/FunctionalInequalities/KLS/BKL/Localization/Energy/Generator.lean

[Current source](../../formalization/FunctionalInequalities/KLS/BKL/Localization/Energy/Generator.lean)

Original comment 149, line 12:

````lean
/-!
# The generator of the cumulant energy

The energy tensor, lower tensor and noise tensors of the posterior along the localization (BKL arXiv:2610.05474v1, (81)), and the
chain-rule expression (82) for the generator of `E_m(p) = F(A(p), κ_m(p)(u))` in conjugated coordinates. Proof bodies: GPT
(S-line sub-controller task S-3b-chain); statements by the S-line sub-controller; placement: Claude.
-/
````

Original comment 150, line 420:

````lean
/-! **BKL Lemma 5.1** in generator form: the drift inequality (80) for the cumulant energy, from the chain rule (82), the first- and second-order expansions (88) of the energy form and the algebraic bound `drift_expression_ge` (task S-3b-lemma51-assembly). -/
````

### formalization/FunctionalInequalities/KLS/BKL/Localization/LogLaplaceGenerator.lean

[Current source](../../formalization/FunctionalInequalities/KLS/BKL/Localization/LogLaplaceGenerator.lean)

Original comment 151, line 5:

````lean
/-!
# BKL (71) in generator form

For every `z`, the generator of the localization equations (67) applied to the posterior log-Laplace transform
`Λ_p(z) = ψ(c + z, Q) − ψ(c, Q)` equals `−½ ⟪v, A⁻¹ v⟫` with `v = a(c + z, Q) − a(c, Q)`
(`generator_logLaplace_posterior`): `∫ e^{⟪z,x⟫} dμ_p = e^{Λ_p(z)}` has zero generator by the generator cancellation
of the posterior, and the chain rule for `exp` gives the formula. Includes partial-derivative helpers on the parameter
space. Proof body: Fable worker (BKL Claude-controller goal, task S1b); statement and placement: Claude.
-/
````

### formalization/FunctionalInequalities/KLS/BKL/Localization/Lyapunov/Bound.lean

[Current source](../../formalization/FunctionalInequalities/KLS/BKL/Localization/Lyapunov/Bound.lean)

Original comment 152, line 30:

````lean
/-! Generator bound `𝓛𝒱 ≤ K𝒱` on symmetric positive semidefinite `Q` under `CumulantBoundCompact 2 8` (task S-5e1b). -/
````

### formalization/FunctionalInequalities/KLS/BKL/Localization/Lyapunov/Moment.lean

[Current source](../../formalization/FunctionalInequalities/KLS/BKL/Localization/Lyapunov/Moment.lean)

Original comment 153, line 7:

````lean
/-!
# Lyapunov moment bound for the cutoff Eldan process

Gronwall bound `E 𝒱(p_t) ≤ 𝒱(p_0) e^{Kt}` along a ball-cutoff Eldan process, from a generator bound `L𝒱 ≤ K𝒱`
taken as a hypothesis, and the resulting Markov tail bound (BKL Section 5, task S-5e2).
-/
````

### formalization/FunctionalInequalities/KLS/BKL/Localization/NoiseBound.lean

[Current source](../../formalization/FunctionalInequalities/KLS/BKL/Localization/NoiseBound.lean)

Original comment 154, line 5:

````lean
/-!
# The conjugated noise matrices of the covariance

`cumulantEnergy_succ_eq` reindexes `E_{r+2}` (BKL arXiv:2610.05474v1, (90)); `conjugatedNoiseMatrix μ hc p i` has entries
`κ₃(μ_p)(σ e_a, σ e_b, σ e_i)`, `σ = A(p)^{-1/2}` (BKL (85), `H̃_i = P H_i P`), and the bound (79) in conjugated form,
`Σ_i |H̃_i v|² ≤ 8|v|²`, follows from `CumulantBoundCompact 2 8` for symmetric positive semidefinite `Q`. Proof bodies: GPT
(S-line sub-controller task S-3bI); statements by the S-line sub-controller; placement: Claude.
-/
````

### formalization/FunctionalInequalities/KLS/BKL/Localization/Process/Basic.lean

[Current source](../../formalization/FunctionalInequalities/KLS/BKL/Localization/Process/Basic.lean)

Original comment 155, line 9:

````lean
/-!
# The cutoff Eldan localization process

`IsEldanCutoff μ hc W ℱ hW γ p`: the parameter process `p_t = (c_t, Q_t)` solves the cutoff localization equations
(67) (drift `γ² (A⁻¹a, A⁻¹)`, noise `γ (A^{-1/2} e_k, 0)`, start `0`) in coordinates; existence for every admissible
cutoff, continuity of paths, initial value, and Dynkin's identity `E F(p_T) − F(0) = E ∫₀ᵀ γ(p_s)² 𝓛F(p_s) ds` for
every `C²` function (BKL arXiv:2610.05474v1, Section 4, cutoff stage). Proof bodies: GPT (S-line sub-controller
task S-5d2a); statements by the S-line sub-controller; placement: Claude.
-/
````

Original comment 156, line 231:

````lean
/-! `Q_t = ∫₀ᵗ γ² A⁻¹` pathwise, hence symmetric positive semidefinite (task S-5d2b). -/
````

### formalization/FunctionalInequalities/KLS/BKL/Localization/Standardization.lean

[Current source](../../formalization/FunctionalInequalities/KLS/BKL/Localization/Standardization.lean)

Original comment 157, line 4:

````lean
/-!
# Standardized posteriors inherit the compact cumulant bound

BKL arXiv:2610.05474v1, (77): for a compactly supported isotropic log-concave prior and symmetric positive
semidefinite `Q`, the standardized posterior `(A^{-1/2}(· − a))_* μ_{c,Q}` is compactly supported, isotropic and
log-concave, so a bound `CumulantBoundCompact d b` transfers to `‖κ_{d+1}(t)(v)‖²_t ≤ b ⟨A v, v⟩`.
Proof body: GPT (BKL Claude-controller goal, task S2); statement and placement: Claude.
-/
````

### formalization/FunctionalInequalities/KLS/BKL/Reduction.lean

[Current source](../../formalization/FunctionalInequalities/KLS/BKL/Reduction.lean)

Original comment 158, line 23:

````lean
/-- Entries of the coordinate array of `T_1 f` for a centered law: `(T_1 f)_j = ∫ ⟪e_j, x⟫ f(x) dμ` (Luna, task RED-D2a). -/
````

Original comment 159, line 47:

````lean
/-- **The `d = 1` Taylor bound from isotropy** (Bessel): `‖T_1 f‖_HS ≤ ‖f‖_{L²(μ)}`, given the entry
formula of the coordinate array (Luna, task RED-D2b). -/
````

Original comment 160, line 149:

````lean
/-- **BKL p. 30, the case `d = 1`**: for an isotropic law on `ℝⁿ` with all exponential moments and
`f ∈ L²(μ)`, `‖T_1 f‖_HS ≤ ‖f‖_{L²(μ)}` (Bessel; assembly of the two previous lemmas, Claude glue). -/
````

Original comment 161, line 166:

````lean
/-- `2 K^d ≤ (2K)^d` for `d ≥ 1` and `K ≥ 0` (numeric step of BKL p. 30; Luna, task RED-D3b). -/
````

Original comment 162, line 174:

````lean
/-- **BKL p. 30: Theorem 1.1 for regular isotropic laws, conditional on the cumulant bounds of
Theorem 4.1.** If `R^ν_{d+1} ≤ (d!)² K^d · Id` for every isotropic log-concave `ν` in every dimension
and every `d ≥ 2` (`CumulantBound d ((d!)² K^d)`, `K ≥ 1`), then every isotropic regular law on `ℝⁿ`
has literature Poincaré constant at most `2 C K`, where `C` is the constant of Theorem 3.1
(`poincare_le_of_taylor`): Proposition 7.1 gives `|T_d f|² ≤ 2K^d‖f‖² ≤ (2K)^d‖f‖²` for `d ≥ 2`,
isotropy gives `|T_1 f| ≤ ‖f‖`, and Theorem 3.1 applies with `R = √(2K)`. The hypothesis is the
source's Theorem 4.1, discharged in the closed producer `BKL.Localization.theorem11`. (Luna, task RED-D4.) -/
````

### formalization/FunctionalInequalities/KLS/BKL/Suspension/Cumulant.lean

[Current source](../../formalization/FunctionalInequalities/KLS/BKL/Suspension/Cumulant.lean)

Original comment 163, line 5:

````lean
/-!
# Cumulants of the suspension (BKL Proposition 7.1)

Bizeul–Klartag–Lehec (arXiv:2610.05474v1), proof of Proposition 7.1, p. 29: the mixed cumulants of
the joint law `ν` of `(S, X₁, …, X_N)` and the Hilbert–Schmidt lower bound that follows from (112),
`|κ(e₀)|² ≥ (d!)²/σ² |T_d f|²`.

* `sum_sq_cumulant_ge_of_entries`: if the entries satisfy (112), the lower bound holds; the copy
  blocks are selected by `card_mul_sq_mul_sum_sq_le_of_blocks`.

* `lintegral_exp_inner_jointLaw` (Luna), `joint_integrability_factorization` and
  `logLaplace_jointLaw_factorization` (Codex): the joint Laplace transform factorizes, in extended,
  real and logarithmic form, with every factor's integrability derived from the joint one.

(111) and (112) themselves are not proved here yet.
-/
````

Original comment 164, line 69:

````lean
/-- **Factorization of the joint Laplace transform** (BKL p. 28), in extended nonnegative form:
`∫⁻ e^{⟪z, p⟫} dν = (∫⁻ e^{(z₀/σ) s} dη_β) · Π_i ∫⁻ e^{(z₀/(σ√N)) f + ⟪z_i, x⟫} dμ` (Luna, task LF2). -/
````

Original comment 165, line 296:

````lean
/-! ### Exponential moments of `f` and of the graph law

Codex proofs (`build/reviews/2026-10-07-bkl-continuous/reviews/R4-GraphMoment/`) over the
factorization above; inputs for the local smoothness of `Λ` in (111). -/
````

Original comment 166, line 474:

````lean
/-- **The copy factor is the Laplace transform of the graph law** `(f(x), x)_* μ` at `(c, z)`
(Luna, task R4c). -/
````

Original comment 167, line 510:

````lean
/-- **The tilt average of the `none` coordinate of the graph law at `(0, z)` is `F_f(z)`** (Luna,
task R4c2). -/
````

Original comment 168, line 546:

````lean
/-- **Derivative of a copy term of (111) at `w = 0`**: `d/dw log ∫ e^{c w f + ⟪z, x⟫} dμ = c F_f(z)`,
through the graph law (Luna, task R4d1). -/
````

### formalization/FunctionalInequalities/KLS/BKL/Suspension/Density.lean

[Current source](../../formalization/FunctionalInequalities/KLS/BKL/Suspension/Density.lean)

Original comment 169, line 7:

````lean
/-!
# The density of the suspension law (BKL (109))

Bizeul–Klartag–Lehec (arXiv:2610.05474v1), proof of Proposition 7.1, p. 28: for
`μ = e^{-V} dx / Z`, the joint law of `(S, X₁, …, X_N)` is the normalized tilted Lebesgue law of
`W_N(s, x) = Σ V(x_i) + β |σ s - N^{-1/2} Σ f(x_i)|` (`Suspension.potential`), for every `N` and
`n` (including `0`), assuming only measurable `V`, `f`, `β > 0` and integrable `e^{-V}`.

The argument: the product of the Lebesgue densities of `μ^{⊗N}` and the Laplace law, a measurable
nonlinear fibrewise shear `η ↦ (F_N(x) + η)/σ` (density multiplier `σ`, from `dη = σ ds`), a
volume-preserving coordinate equivalence onto `EuclideanSpace ℝ (Option (Fin N × Fin n))`, and
normalization of a positive density. The helpers are private to this boundary.

Provenance: assembled by Codex (`build/reviews/2026-10-07-bkl-continuous/reviews/
R2-assembly-Codex-proposal.lean`, independently verified) from a Luna finite-product integral
helper (task LF2, now `Probability.lintegral_pi_prod_fin`) and Codex-proved density, shear, volume and normalization lemmas.
-/
````

### formalization/FunctionalInequalities/KLS/BKL/Suspension/Law.lean

[Current source](../../formalization/FunctionalInequalities/KLS/BKL/Suspension/Law.lean)

Original comment 170, line 40:

````lean
/-- `σ_β² = 1 + 2/β²` (Luna, task R7a). -/
````

Original comment 171, line 47:

````lean
/-- **The limit `β → ∞`** (BKL p. 30): `X ≤ C σ_β²` for all `β > 0` forces `X ≤ C` (Luna, task R7a3). -/
````

Original comment 172, line 237:

````lean
/-! ### The coordinate adapter `ℝ^{Option (Fin N × Fin n)} ≃ ℝ^{Nn+1}`

The hypothesis `CumulantBound` is stated for laws on `EuclideanSpace ℝ (Fin m)`; the joint law is
moved there by the linear isometry `coordinateEquiv`, which preserves isotropy
(`Isotropic.map_linearIsometryEquiv`), log-concavity and cumulants
(`cumulant_map_linearIsometryEquiv`). Codex clients (`reviews/A1-replan/`). -/
````

## 05-kls-other

### formalization/FunctionalInequalities/KLS/CEK/MomentMap.lean

[Current source](../../formalization/FunctionalInequalities/KLS/CEK/MomentMap.lean)

Original comment 173, line 3:

````lean
/-!
# The weak moment map of a bounded isotropic law

Euler–Lagrange identification for the Cordero-Erausquin–Klartag variational problem: the gradient of the bounded-source
primal pushes `e^{−ψ} dx` forward to the source law (weak moment map), the existence step of the weak moment-map route to
Letwin arXiv:2607.24164v1. Proof body: GPT / Letwin sub-controller (task L-T13b); statement by the Letwin
sub-controller; placement: Claude.
-/
````

### formalization/FunctionalInequalities/KLS/CEK/PartitionVariation.lean

[Current source](../../formalization/FunctionalInequalities/KLS/CEK/PartitionVariation.lean)

Original comment 174, line 7:

````lean
/-!
# First variation of the CEK partition function

The derivative at `0` of `t ↦ ∫ e^{−(q + t b)*}` (Cordero-Erausquin–Klartag (42), integral form), built on the pointwise
Legendre first variation; the Euler–Lagrange step towards the moment-map push-forward on the weak route to Letwin
arXiv:2607.24164v1. Proof body: GPT (Letwin sub-controller task L-T13a); statement by the Letwin sub-controller;
placement: Claude.
-/
````

### formalization/FunctionalInequalities/KLS/Isotropic.lean

[Current source](../../formalization/FunctionalInequalities/KLS/Isotropic.lean)

Original comment 175, line 53:

````lean
/-- For an isotropic law the raw second moments are `∫ ⟪u, x⟫ ⟪v, x⟫ = ⟪u, v⟫` (Luna, task A1). -/
````

Original comment 176, line 70:

````lean
/-- **Isotropy along a linear isometry** (Luna, task A1 round 10; `MemLp` step repaired by Codex via
`ContinuousLinearMap.comp_memLp'`). -/
````

Original comment 177, line 124:

````lean
/-- **Gradient second moments of an isotropic pushforward** (Letwin Lemma 2.3, step 2; Luna, task
LW-L23b; the worker failed on one `unnecessarySimpa` diagnostic and Claude rewrote three proof steps at
integration): if `(∇φ)_* ν` is isotropic then
`∫ (∂_u φ)(∂_v φ) dν = ⟪u, v⟫`. -/
````

Original comment 178, line 160:

````lean
/-- **Letwin Lemma 2.3 (mean Hessian of the moment-map potential is the identity)**, for any smooth
normalized `φ` with isotropic gradient law and the stated integrability (Luna, task LW-L23; the moment map
itself is not constructed). -/
````

Original comment 179, line 242:

````lean
/-! ### Covariance of the matrix absolute-value transform (Letwin, proof of Theorem 1.2, p. 14)

For an isotropic law and a real symmetric matrix `M` (singular, indefinite and `Fin 0` included), the push-forward by
`S = sqrt(sqrt(M * M))` has covariance `|M| = sqrt(M * M)`: the covariance step `Cov Z = |M|`, `Z = |M|^{1/2} X`,
of the proof of Letwin arXiv:2607.24164v1 Theorem 1.2 (p. 14, the unnumbered display preceding (2.21); the source
first reduces to invertible `M`). Covariance/algebra prerequisite only (consumer chain:
Letwin Theorem 1.2, then Bizeul–Klartag–Lehec Lemma 4.2); not the Stein-kernel trace identity (2.21), the `H⁻¹` or
the variance-eight estimates.
Proof body: root-accepted Astra v5 (`round1.lean` 030a859b…), verbatim. -/
````

### formalization/FunctionalInequalities/KLS/LogConcave/BallConditioning.lean

[Current source](../../formalization/FunctionalInequalities/KLS/LogConcave/BallConditioning.lean)

Original comment 180, line 7:

````lean
/-!
# Log-concave laws conditioned on balls

Conditioning a log-concave law on a closed ball and pushing it forward by an affine map stays in the regular
class used by the approximation step of Letwin's Lemma A.1 (weak Letwin route, block T10).

* `exists_regularClass_of_cond_closedBall_map` (task L-T10c).
-/
````

Original comment 181, line 92:

````lean
/-- **Ball-conditioned, affinely transported regular laws lie in Letwin's class** (Letwin Lemma A.1, task T10c):
conditioning the law of a regular potential `V` on `closedBall 0 R` (`R > 0`) and pushing forward by
`x ↦ L (x − c)` gives `1_K e^{−W} dx` with `K` compact convex with nonempty interior and `W` smooth and uniformly
convex. -/
````

Original comment 182, line 190:

````lean
/-! Whitening maps of laws with converging second moments converge to the identity and preserve moment convergence (Letwin Lemma A.1 approximation; task L-T10b). -/
````

Original comment 183, line 454:

````lean
/-- **Whitening preserves convergence of low moments** (Letwin Lemma A.1 approximation, task T10b): if the laws
`λ k`, all carried by a fixed ball, have mixed moments of degree `≤ 4` converging to those of an isotropic `μ`, then
there are affine maps `x ↦ L k (x − c k)` that make `λ k` isotropic for large `k` (mean zero, identity second
moments) and keep the convergence of the moments of degree `≤ 4`. -/
````

### formalization/FunctionalInequalities/KLS/LogConcave/HminusOne.lean

[Current source](../../formalization/FunctionalInequalities/KLS/LogConcave/HminusOne.lean)

Original comment 184, line 6:

````lean
/-!
# Dual gradient estimates and the H⁻¹ variance bound

Supports Letwin arXiv:2607.24164v1, Proposition 2.8, through three interfaces:
- nonnegativity of a compact-test dual constant for a positive-dimensional law
  with continuous tilted density;
- the integrated Bochner Hessian bound for a convex C² potential;
- `variance_le_sum_of_partial_dual_bounds`, retaining the C² convex potential,
  C¹/L² function and L² partial-derivative hypotheses stated below.

The variance assembly uses the heat-generator range density from `HeatSemigroup/Range.lean`.
Historical task and proof-route details are retained in `research/decisions/2026-10-18-source-interface-history.md`.
-/
````

Original comment 185, line 185:

````lean
/-! Bochner Hessian bound for a convex `C²` potential (task L-T9c; proof body GPT, statement by the Letwin sub-controller). -/
````

### formalization/FunctionalInequalities/KLS/LogConcave/Transport.lean

[Current source](../../formalization/FunctionalInequalities/KLS/LogConcave/Transport.lean)

Original comment 186, line 6:

````lean
/-!
# Geometry of the compact-set log-concavity convention

These lemmas use the existing `KLS.LogConcave` definition. Read affine-isometric pullback,
then the intrinsic-coordinate corollary. They provide the coordinate reduction for the
absolute-continuity step in the general log-concave literature comparison. No density is
included in the definition and no representation theorem is assumed here.

Conditioning on a closed convex set of positive mass preserves log-concavity (`cond`), used to
truncate laws to balls (BKL arXiv:2610.05474v1, p. 19); proof body: GPT (BKL Claude-controller goal,
task T1a), statement and placement: Claude.
-/
````

### formalization/FunctionalInequalities/KLS/LogConcave/WeakLimit.lean

[Current source](../../formalization/FunctionalInequalities/KLS/LogConcave/WeakLimit.lean)

Original comment 187, line 21:

````lean
/-- **Weak-limit transfer of the Poincaré bound** to the literature constant of a log-concave law**
(BKL arXiv:2610.05474v1, Section 2, p. 5): if `μ_j → μ` weakly, each `μ_j` satisfies the smooth-test
Poincaré bound with constant `C_j`, and `C_j → C`, then the log-concave limit `μ` has literature
constant at most `C`. The smooth-test bound passes to the limit on compactly supported smooth tests
(`Poincare.SmoothTest.variance_le_mul_energy_of_tendsto`), extends to all admissible tests by the
cutoff argument (`Poincare.SmoothTest.Holds.of_compactSupport`), and the smooth-test constant equals
the literature constant for log-concave laws. Luna, task S2-W3. -/
````

## 06-bare-route-identifiers

### formalization/FunctionalInequalities/Analysis/BakryEmery/Bochner/Lipschitz.lean

[Current source](../../formalization/FunctionalInequalities/Analysis/BakryEmery/Bochner/Lipschitz.lean)

Original comment 218, line 121:

````lean
/-- **Bochner identity for a Lipschitz potential with Lipschitz gradient** (weak Letwin route, N14,
Brascamp–Lieb at `C^{1,1}`): for `U ∈ C¹` Lipschitz with `G`-Lipschitz gradient and integrable
`e^{-U}`, and `f ∈ C_c^∞`, `∫ (ℒf)² dν = ∫ (‖∇²f‖² + ⟪D(∇U) ∇f, ∇f⟫) dν` with `ν = e^{-U} dx`
normalized, `ℒf = Δf − ⟪∇U, ∇f⟫`, and `D(∇U)` the a.e. derivative of the Lipschitz map `∇U`. -/
````

### formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts/InverseHessian/Weak.lean

[Current source](../../formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts/InverseHessian/Weak.lean)

Original comment 219, line 887:

````lean
/-- Genuine integrability for the weak inverse-Hessian generator, its exchanged
test density and the absolute RHS of the original N11b energy estimate. -/
````

### formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts/LipschitzHessian.lean

[Current source](../../formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts/LipschitzHessian.lean)

Original comment 220, line 26:

````lean
/-- **Mean Hessian identity for a `C¹` potential with Lipschitz gradient** (Letwin
arXiv:2607.24164v1, Lemma 2.3, analytic part, at `C^{1,1}`; weak Letwin route, N15):
`∫ ⟪D(∇φ)(x) u, v⟫ dν = ∫ ∂_uφ ∂_vφ dν` for convex `φ ∈ C¹` with `G`-Lipschitz gradient,
`e^{-φ}` a probability density and `∇φ ∈ L²(ν)`, where `D(∇φ)` is the a.e. (Rademacher)
derivative of the Lipschitz map `∇φ`. -/
````

### formalization/FunctionalInequalities/Analysis/Convex/Alexandrov.lean

[Current source](../../formalization/FunctionalInequalities/Analysis/Convex/Alexandrov.lean)

Original comment 221, line 72:

````lean
/-- **Alexandrov identity in push-forward form** (weak Letwin route, step N5): for a convex Lipschitz
`u` with `ν ≪ volume`, `ν.map (gradient u) = μ ≪ volume`, integrals of nonnegative functions over the subgradient
image `∂u(S)` of a compact `S` against `μ` equal integrals over `S` of the composition with `∇u`
against `ν`. -/
````

Original comment 222, line 250:

````lean
/-- **Local two-sided Alexandrov bounds** (weak Letwin route, step N5, input of the Caffarelli
argument N6): if `u` is convex and Lipschitz, `ν = e^{-u} dx` (normalized), `ν.map ∇u = μ` has a
density `ρ` bounded above and below on a closed convex `K` containing `∇u` a.e., then on every compact
`Q` the volume of the subgradient image is comparable to the volume of the set:
`a · vol S ≤ vol (∂u(S)) ≤ b · vol S` for all compact `S ⊆ Q`, with `0 < a`. -/
````

Original comment 223, line 1399:

````lean
/-- The quadratic function with constant `c`, slope `b` and Hessian matrix `A` centred at `x₀`:
`Q x = c + ⟪b, x − x₀⟫ + ½ ⟪x − x₀, A (x − x₀)⟫` (weak Letwin route, N8 viscosity tests). -/
````

Original comment 224, line 1647:

````lean
/-- **Subgradient images of a positive definite quadratic are exact affine images, with volume
`det A · vol G`** (weak Letwin route, N8). -/
````

### formalization/FunctionalInequalities/Analysis/Convex/HessianIncrement.lean

[Current source](../../formalization/FunctionalInequalities/Analysis/Convex/HessianIncrement.lean)

Original comment 225, line 34:

````lean
/-- The actual squared shifted Hessian-increment density in N11b is integrable
against the continuous compact weight. No C2 or given integrability is assumed. -/
````

### formalization/FunctionalInequalities/Analysis/Convex/SecondDifference.lean

[Current source](../../formalization/FunctionalInequalities/Analysis/Convex/SecondDifference.lean)

Original comment 226, line 43:

````lean
/-- **Quadratic upper bound from a second-difference bound** (weak Letwin route, C^{1,1} step N9,
support for T4): a differentiable convex `u` with `u(x+h) + u(x−h) − 2u(x) ≤ C‖h‖²` satisfies
`u y ≤ u x + ⟪∇u x, y − x⟫ + C ‖y − x‖²`. -/
````

Original comment 227, line 73:

````lean
/-- **Co-coercivity: a quadratic upper bound gives a Lipschitz gradient** (weak Letwin route, C^{1,1}
step N9, support for T4): if a differentiable convex `u` satisfies
`u y ≤ u x + ⟪∇u x, y − x⟫ + C ‖y − x‖²` for all `x, y` with `C > 0`, then
`‖∇u x − ∇u y‖ ≤ 2C ‖x − y‖`. -/
````

Original comment 228, line 826:

````lean
/-- The actual centered difference bounds required by the original N11b
increment-energy estimate, with no differentiability or sign assumption on D. -/
````

### formalization/FunctionalInequalities/Analysis/Convex/Subgradient.lean

[Current source](../../formalization/FunctionalInequalities/Analysis/Convex/Subgradient.lean)

Original comment 229, line 32:

````lean
/-- **A differentiable convex function on a finite-dimensional space is `C¹`** (weak Letwin
route, step N7): convexity makes the derivative map continuous. -/
````

Original comment 230, line 143:

````lean
/-- **Subgradients of a convex Lipschitz function lie in the closed convex range of its a.e.
gradient** (weak Letwin route, step N4: `∂u(x) ⊆ K̄` for the weak moment map, whose gradient lies
a.e. in the target `K`): if `u` is convex and Lipschitz on a finite-dimensional inner product space,
`K` is closed and convex and `∇u(x) ∈ K` for a.e. `x`, then every subgradient `p` of `u` at every
point `x` (`u(x) + ⟪p, y − x⟫ ≤ u(y)` for all `y`) lies in `K`. -/
````

Original comment 231, line 199:

````lean
/-- **Max formula for the one-sided directional derivative of a finite convex function** (weak
Letwin route, step N7 "singleton subdifferential ⇒ C¹"): for a convex `u : E → ℝ` on a
finite-dimensional inner product space, every point `x` and every direction `v`, there is a
subgradient `g` of `u` at `x` whose pairing with `v` is the right derivative
`inf_{t>0} (u(x + t v) - u(x))/t`: it is a subgradient and the difference quotients come
arbitrarily close to `⟪g, v⟫` (they are `≥ ⟪g, v⟫` by the subgradient inequality). -/
````

Original comment 232, line 564:

````lean
/-- **A convex function on an open set is differentiable almost everywhere on it** (Rademacher for
convex functions; weak Letwin route, support for the a.e. injectivity of the subgradient map, N5). -/
````

Original comment 233, line 826:

````lean
/-- **A convex function with a unique subgradient at every point is differentiable** (weak Letwin
route, step N7 "singleton subdifferential ⇒ C¹", differentiability half): on a finite-dimensional
inner product space, if the subgradient inequality `u x + ⟪g, y - x⟫ ≤ u y` (all `y`) is satisfied by
exactly one `g` at every `x`, then `u` is differentiable (with that `g` as gradient; `C¹` then follows
from `contDiff_one_of_convexOn_of_differentiable`). -/
````

Original comment 234, line 973:

````lean
/-- **Monotonicity of subgradient images under comparison** (Gutiérrez, *The Monge–Ampère
equation*, Lemma 1.4.1; weak Letwin route, step N8 comparison principle): if `u ≤ v` on a
bounded open `Ω` and `u = v` on its frontier, then `∂v(Ω) ⊆ ∂u(Ω)`. -/
````

Original comment 235, line 1088:

````lean
/-- **Almost every subgradient belongs to a single point** (weak Letwin route, step N5, the
Alexandrov identity): for a convex Lipschitz `u` on a finite-dimensional inner product space, the
set of `p` that are subgradients of `u` at two distinct points is Lebesgue-null (such `p` are
non-differentiability points of the conjugate `u*`, or frontier points of its domain). -/
````

Original comment 236, line 1308:

````lean
/-- **Singleton subdifferential ⇒ `C¹`** (weak Letwin route, step N7, assembly of L-T5b/L-T5c): a
convex function on a finite-dimensional inner product space with exactly one subgradient at every
point is continuously differentiable. -/
````

### formalization/FunctionalInequalities/Analysis/Convex/Viscosity.lean

[Current source](../../formalization/FunctionalInequalities/Analysis/Convex/Viscosity.lean)

Original comment 237, line 147:

````lean
/-- **A `C²` function touching a convex function from above has positive semidefinite Hessian at the
contact point** (weak Letwin route, N8 viscosity tests). -/
````

Original comment 238, line 385:

````lean
/-- **Second-order Taylor bound with the coordinate Hessian** (weak Letwin route, N8 viscosity tests):
for `ψ` twice differentiable at `x₀` (`ContDiffAt ℝ 2`), every `ε > 0` admits `r > 0` with
`|ψ x − ψ x₀ − Dψ(x₀)(x − x₀) − ½ ⟪x − x₀, ∇²ψ(x₀)(x − x₀)⟫| ≤ ε ‖x − x₀‖²` on `ball x₀ r`. -/
````

Original comment 239, line 547:

````lean
/-- **Upper touching test for an Alexandrov solution** (weak Letwin route, N8 viscosity inequality,
T12c): if the subgradient images of the convex `u` on open subsets of `Ω` carry the density `f`
(`vol (∂u(G)) = ∫_G f`), `f` is continuous at `x₀ ∈ Ω`, and a `C²` function `ψ` touches `u` from above
at `x₀` (`u ≤ ψ` near `x₀`, `u x₀ = ψ x₀`), then `f x₀ ≤ det ∇²ψ(x₀)` (standard coordinates of
`EuclideanSpace ℝ (Fin n)`, `hessianMatrix ψ x₀ i j = D²ψ(x₀)(eᵢ, eⱼ)`). -/
````

Original comment 240, line 653:

````lean
/-- **Lower touching test for an Alexandrov solution** (weak Letwin route, N8, T12c): with the
same Alexandrov hypothesis, if `ψ ∈ C²` touches `u` from below at `x₀` (`ψ ≤ u` near `x₀`,
`u x₀ = ψ x₀`) and `∇²ψ(x₀)` is positive semidefinite, then `det ∇²ψ(x₀) ≤ f x₀`. -/
````

### formalization/FunctionalInequalities/Analysis/Matrix/Piola.lean

[Current source](../../formalization/FunctionalInequalities/Analysis/Matrix/Piola.lean)

Original comment 241, line 132:

````lean
/-- **Piola identity for the adjugate of a smooth Hessian** (weak Letwin route, step N10, smooth
case): for a `C³` function `u` on `ℝⁿ`, the rows of the adjugate (cofactor) matrix of the Hessian
`H = ∇²u` are divergence-free: `∑ⱼ ∂ⱼ (adj H)ᵢⱼ = 0`. Here `hessianMatrix u y i j = D²u(y)(eᵢ, eⱼ)`
in the standard basis `eⱼ = EuclideanSpace.basisFun (Fin n) ℝ j`. -/
````

Original comment 242, line 418:

````lean
/-- **Weak Piola identity for a `C¹` function with Lipschitz gradient** (weak Letwin route, step N10):
the rows of the adjugate of the a.e. Hessian `H = D(∇u)` are weakly divergence-free,
`∑ⱼ ∫ (adj H)ᵢⱼ ∂ⱼψ = 0` for every `C¹` test `ψ` with compact support. Here
`hessianMatrix u x i j = D²u(x)(eᵢ, eⱼ)` is the true Hessian at every point where `∇u` is
differentiable (almost everywhere, Rademacher), and the identity is obtained by mollification from
the smooth case `sum_fderiv_adjugate_hessianMatrix_eq_zero`. -/
````

### formalization/FunctionalInequalities/Analysis/Mollification/Basic.lean

[Current source](../../formalization/FunctionalInequalities/Analysis/Mollification/Basic.lean)

Original comment 243, line 501:

````lean
/-- **Derivative of the mollification of a Lipschitz map** (weak Letwin route, support for the
mollification steps N10/N14): for a Lipschitz map `F : E → E` and a bump `φ`, the convolution
`φ.normed ⋆ F` is differentiable with derivative `φ.normed ⋆ DF`, where `DF = fderiv ℝ F` is the
almost-everywhere (Rademacher) derivative of `F` (a bounded measurable map). -/
````

### formalization/FunctionalInequalities/KLS/CEK/MomentMap.lean

[Current source](../../formalization/FunctionalInequalities/KLS/CEK/MomentMap.lean)

Original comment 244, line 27:

````lean
/-- **Weak moment map of a bounded isotropic law** (Cordero-Erausquin–Klartag arXiv:1304.0630v1,
Theorem 2, existence, via the bounded CEK primal `bounded_source_lipschitz_primal` and the first
variation; weak Letwin route, step N3): for an isotropic probability law `μ` supported in the
closed ball of radius `L`, there is a convex `L`-Lipschitz potential `ψ` with `∫ e^{-ψ} = 1`
whose a.e. gradient pushes the law `e^{-ψ} dx` forward to `μ`. No regularity beyond Lipschitz is
claimed. -/
````

Original comment 245, line 344:

````lean
/-- **Weak moment map of a bounded isotropic law** (Cordero-Erausquin–Klartag arXiv:1304.0630v1,
Theorem 2, existence, via the bounded CEK primal `bounded_source_lipschitz_primal` and the first
variation; weak Letwin route, step N3): for an isotropic probability law `μ` supported in the closed
ball of radius `L`, there is a convex `L`-Lipschitz potential `ψ` with `∫ e^{-ψ} = 1` whose a.e.
gradient pushes the law `e^{-ψ} dx` forward to `μ`. No regularity beyond Lipschitz is claimed. -/
````

### formalization/FunctionalInequalities/KLS/CEK/PartitionVariation.lean

[Current source](../../formalization/FunctionalInequalities/KLS/CEK/PartitionVariation.lean)

Original comment 246, line 27:

````lean
/-- **First variation of the partition function of the conjugate** (Cordero-Erausquin–Klartag
arXiv:1304.0630v1, proof of Theorem 2, first variation (42) integrated; weak Letwin route, step
N3): for a proper lower semicontinuous potential `q` whose conjugate `ψ = q*` is real, Lipschitz
and has integrable `e^{-ψ}`, and a bounded continuous perturbation `b`, the map
`t ↦ ∫ exp(−(q + t b)*(x)) dx` is differentiable at `0` with derivative
`∫ exp(−ψ(x)) b(∇ψ(x)) dx` (`∇ψ` is the a.e. gradient of the Lipschitz function `ψ`). -/
````

### formalization/FunctionalInequalities/KLS/LogConcave/HminusOne.lean

[Current source](../../formalization/FunctionalInequalities/KLS/LogConcave/HminusOne.lean)

Original comment 247, line 253:

````lean
/-- **Bochner bound for the coordinate Hessian under a convex `C²` potential** (Letwin
arXiv:2607.24164v1, Proposition 2.8 via Barthe–Klartag; weak Letwin route, N16 support): for
`ν = e^{-W} dm` with `W` convex and `C²`, and `g ∈ C_c^∞`,
`∑ᵢ ∫ ‖∇(∂ᵢ g)‖² dν ≤ ∫ (ℒg)² dν` with `ℒg = Δg − ⟪∇W, ∇g⟫` and `∂ᵢ g = Dg(eᵢ)` in the
standard coordinates of `EuclideanSpace ℝ (Fin n)`. -/
````

## Previous handoff (verbatim)

The complete current-state text before this comment-only pass is preserved below; its receipts apply to their recorded snapshots.

````text
# Current KLS handoff

Updated 2026-10-18 for the accepted layout baseline and the downstream reuse/API proposal.

## Accepted result and open boundaries

`FunctionalInequalities.KLS.kls : KLS.Conjecture` is proved through the selected BKL
cutoff-localization route. Its target is unchanged: one finite covariance-normalized
literature Poincaré bound for every dimension and every log-concave probability law with
finite second moment, including dimension zero and singular affine supports.

The accepted chain is compact Letwin Theorem 1.2 (constant 8) → finite-horizon cutoff BKL (95)
→ source-form BKL Theorem 4.1 → source-form BKL Theorem 1.1 → KLS.
The [paper register](research/progress/LITERATURE.md) owns exact scope and coverage; the
[proof path](research/progress/PROOF-PATH.md) maps the chain to Lean and its certificates.
BKL's main theorem is covered. Letwin's noncompact Theorems 1.1/1.2, the uncut Eldan
construction and literal identities (68)–(73), and the separate uncut intermediate statements
remain open. The four exploratory routes retain their own statuses.

## Current library and maintenance state

The article-standard review, BKL reorganization, documentation corrections and five subsequent
source-layout batches are complete and independently accepted. All 8,018 compared public
interfaces agree across the latter layout work. Proof statements, definitions, assumptions,
certificate states and existing historical records were preserved.

- [Lean design](LEAN_DESIGN.md) and [calling examples](examples/README.md): public interfaces and imports.
- [Module directory](formalization/MODULES.md) and [BKL guide](formalization/FunctionalInequalities/KLS/BKL/README.md): source owners.
- [Maintenance register](research/technical-debt/remaining-families.md): per-batch decisions, migration maps and acceptance requirements; MetricBV cross-family relocation remains deferred.
- [Final documentation decision](research/decisions/2026-10-18-final-documentation-review.md): corrected status prose and shortened navigation.

## Reuse proposal and evidence

The independent Git-pinned downstream acceptance, three narrow clients and two bounded-operator
interfaces are recorded in the [reuse decision](research/decisions/2026-10-18-downstream-reuse.md)
and [example guide](examples/README.md). Concise source headers and the scoped HminusOne openings
preserve all 42 original declaration interfaces and proof-expression comparisons. Existing
certificates, hypotheses and history are unchanged; the one empty migrated source directory was removed.

The published baseline `79fbe1a` passed a fresh full local verification at
`build/verification/20261018T011543.378047Z/report.json` (297 gates, 282 strict clients,
9,842 local declarations and 864 module replays). Every project-local declaration, `KLS.kls`
included, is audited; known [vendor holes](formalization/vendor/README.md#upstream-holes) remain isolated.

The current uncommitted proposal has per-batch receipts and its final frozen-tree verification
under `build/reusability/2026-10-18-downstream-and-examples/STATE.json` and `FINAL-ACCEPTANCE.json`.
Each receipt applies to its recorded snapshot; see [receipt scope](research/verification.md#receipts-and-trust-scope).

## Coordination and delivery

Proof API loops and the original Claude proof-integrator session are idle. The queued review
follow-up stays paused. All sealed failures, previous decisions and controller records remain
historical evidence. The earlier one-commit/one-push delivery is complete at `79fbe1a`;
this reuse/source-interface proposal is local and uncommitted. Superseded evidence/delivery
wording is preserved in the [reuse decision](research/decisions/2026-10-18-downstream-reuse.md).

````

## 07-wide-process-identifiers

### formalization/FunctionalInequalities/Analysis/BakryEmery/Calculus.lean

[Current source](../../formalization/FunctionalInequalities/Analysis/BakryEmery/Calculus.lean)

Original comment 248, line 139:

````lean
/-- Mixed directional derivatives of a `C²` function commute (route `B2` in directional form). -/
````

### formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts/InverseHessian/Weak.lean

[Current source](../../formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts/InverseHessian/Weak.lean)

Original comment 249, line 1150:

````lean
/-- C1 compact multiplier version of the existing closed weak generator proof.
Actual weak-source support for Letwin A4; no new regularity hypothesis on u. -/
````

### formalization/FunctionalInequalities/Analysis/Convex/Alexandrov.lean

[Current source](../../formalization/FunctionalInequalities/Analysis/Convex/Alexandrov.lean)

Original comment 250, line 144:

````lean
/-- **A farthest point of a compact set is exposed** (weak Letwin route, Caffarelli block T11c/T11e):
for a nonempty compact `C` in an inner product space and any `y`, there is `x_e ∈ C` with
`⟪x − x_e, x_e − y⟫ < 0` for every other `x ∈ C`; moreover `‖x_e − y‖ ≥ ‖x − y‖` for all `x ∈ C`. -/
````

Original comment 251, line 442:

````lean
/-- **Sliding lemma for the Alexandrov maximum principle** (weak Letwin route, Caffarelli block T11c):
if `u` is convex, `u ≥ 0` on the frontier of a bounded open `Ω`, `u x₀ < 0` at some `x₀ ∈ Ω`, and the
affine function `x ↦ u x₀ + ⟪p, x − x₀⟫` is `≤ 0` on `closure Ω`, then `p` is a subgradient of `u` at
some point of `Ω`. In particular, `closedBall 0 (-u x₀ / diam Ω) ⊆ ∂u(Ω)`, and the cone over the ball
with apex in the direction of a nearest boundary point is contained in `∂u(Ω)`. -/
````

Original comment 252, line 612:

````lean
/-- **Supporting half-space at a nearest boundary point of an open convex set** (weak Letwin route,
Caffarelli block T11c, the `dist(x₀, ∂Ω)` factor of the Alexandrov estimate): for a bounded open convex
`Ω` and `x₀ ∈ Ω`, with `d := infDist x₀ (frontier Ω)`, there is a unit vector `e` such that
`⟪x − x₀, e⟫ ≤ d` for every `x ∈ Ω`. -/
````

Original comment 253, line 738:

````lean
/-- **Volume of the cone over a ball** (weak Letwin route, Caffarelli block T11c, Alexandrov maximum
principle): there is `c > 0`, depending only on `E`, such that the convex hull of the closed ball of
radius `r` and a point `q` with `‖q‖ ≥ r` has volume at least `c · r^(n−1) · ‖q‖`, `n = dim E`. -/
````

Original comment 254, line 1202:

````lean
/-- **Alexandrov maximum principle** (Gutiérrez, *The Monge–Ampère equation*, Theorem 1.4.2; weak
Letwin route, Caffarelli block T11c): there is `c > 0` depending only on `E` such that for every
convex `u`, bounded open convex `Ω`, `u ≥ 0` on `∂Ω` and `x₀ ∈ Ω` with `u x₀ < 0`,
`c · (−u x₀)^n ≤ vol (∂u(Ω)) · diam(Ω)^(n−1) · dist(x₀, ∂Ω)`, `n = dim E`. -/
````

Original comment 255, line 1670:

````lean
/-- **Distance to the frontier is at most the width in any direction** (weak Letwin route, Caffarelli
block T11e, step G3): for a bounded open `S`, a point `x ∈ S` and a unit vector `θ`, if
`⟪y − x, θ⟫ ≤ t` for all `y ∈ S`, then `infDist x (frontier S) ≤ t`. -/
````

Original comment 256, line 1748:

````lean
/-- **Affine transport of subgradient images** (weak Letwin route, Caffarelli block T11e, step G5):
under an affine equivalence `e` with linear part `T`, the subgradient image of `u ∘ e.symm` over
`e '' G` is the image of `∂u(G)` under the adjoint of `T⁻¹`. -/
````

Original comment 257, line 1933:

````lean
/-- **Minimum estimate on a normalised section by quadratic comparison** (weak Letwin route, Caffarelli
block T11e, step (b); Gutiérrez Lemma via the comparison with `½κ(‖x‖² − 1)`): if `v` is convex, `≤ 0` on
the frontier of a bounded open `S ⊇ closedBall 0 1`, and `a · vol G ≤ vol ∂v(G)` for open `G ⊆ S`, then
`v 0 ≤ −½ (a/2)^{1/n}`. -/
````

Original comment 258, line 2088:

````lean
/-- **Subtracting an affine function translates subgradient images** (weak Letwin route, Caffarelli
block T11e, bookkeeping): `∂(u − ⟪p, ·⟫ − c)(G) = ∂u(G) − p`, hence the volumes agree. -/
````

### formalization/FunctionalInequalities/Analysis/Convex/Caffarelli.lean

[Current source](../../formalization/FunctionalInequalities/Analysis/Convex/Caffarelli.lean)

Original comment 259, line 25:

````lean
/-- **Width ratios control the distance to the frontier after an affine normalisation** (weak Letwin
route, Caffarelli block T11e, step (c)): if a bounded open `S ∋ x` has width at most `α` above `x` and
at least `β > 0` below `x` in the unit direction `θ`, and `e` is an affine equivalence with
`e '' S ⊆ closedBall 0 C₀`, then `infDist (e x) (frontier (e '' S)) ≤ 2 C₀ α / β`. -/
````

Original comment 260, line 171:

````lean
/-- **Sections at an exposed point of a compact contact set are bounded and shrink to the slab piece
of the contact set** (weak Letwin route, Caffarelli block T11e, steps G1–G2): with `w := u − ℓ ≥ 0`
(`ℓ` the supporting affine function at `x₀`), compact contact set `C = {w = 0}`, an exposed point
`xe ∈ C` in the unit direction `θ`, and `h > 0`, the sections
`S ε := {x | w x < ε (⟪x − xe, θ⟫ + h)}` lie in a fixed compact set for small `ε`, and for every `δ > 0`
they lie in the `δ`-thickening of `C ∩ {⟪· − xe, θ⟫ ≥ −h}` for `ε` small enough. -/
````

### formalization/FunctionalInequalities/Analysis/Convex/Normalization.lean

[Current source](../../formalization/FunctionalInequalities/Analysis/Convex/Normalization.lean)

Original comment 261, line 29:

````lean
/-- **A compact convex body contains a simplex of maximal volume with positive volume** (weak Letwin
route, Caffarelli block T11d, affine normalisation, step 1). -/
````

Original comment 262, line 172:

````lean
/-- **Maximality of the simplex confines the body to a box in simplex coordinates** (weak Letwin
route, Caffarelli block T11d, step 2): if `v` is a nondegenerate simplex of maximal volume in `K`,
then every `y ∈ K` has simplex coordinates `c = (M v)⁻¹ (y − v 0)` with `|cⱼ| ≤ 1` and
`|1 − ∑ cⱼ| ≤ 1`. -/
````

Original comment 263, line 346:

````lean
/-- **The standard simplex contains a ball around its barycentre, and the coordinate box lies in a
ball** (weak Letwin route, Caffarelli block T11d, step 3). -/
````

Original comment 264, line 516:

````lean
/-- **Affine normalisation of convex bodies** (John-type, via a maximal-volume simplex; weak Letwin
route, Caffarelli block T11d): there is a constant `C` depending only on the space such that every
compact convex set with nonempty interior is affinely equivalent to a set squeezed between the unit
ball and the ball of radius `C`. -/
````

### formalization/FunctionalInequalities/Analysis/Convex/Subgradient.lean

[Current source](../../formalization/FunctionalInequalities/Analysis/Convex/Subgradient.lean)

Original comment 265, line 1212:

````lean
/-- **A function affine along a full line pins every subgradient** (weak Letwin route, Caffarelli
block T11b): if `u (x₀ + t θ) = u x₀ + t c` for all real `t`, then every subgradient `p` of `u` at
any point satisfies `⟪p, θ⟫ = c`. -/
````

### formalization/FunctionalInequalities/Analysis/Gronwall.lean

[Current source](../../formalization/FunctionalInequalities/Analysis/Gronwall.lean)

Original comment 266, line 18:

````lean
/-- Integral Grönwall (real analysis, needed for S5e-2; not in Mathlib in this form). -/
````

### formalization/FunctionalInequalities/Analysis/Sard/Equidimensional.lean

[Current source](../../formalization/FunctionalInequalities/Analysis/Sard/Equidimensional.lean)

Original comment 267, line 5:

````lean
/-! # The equidimensional degenerate case: almost no level is a critical value

Route obligation `R10` of `research/decisions/2026-09-17-rank-deficient-route.md`, the last
non-diagnostic item on that list.  When `n = m` the fibre dimension is `k = 0`, and `μH[0]`-nullity
of a slice means the slice is **empty**, so the statement to prove is that for almost every `t` the
level `{u = t}` contains **no** critical point at all.

**What this is.**  It is Mathlib's equidimensional Sard lemma
`MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero` — if a map of a finite-dimensional
real space to *itself* is differentiable on a set and its differential is singular there, the image
of that set is Lebesgue-null — transported across the linear isometry
`isometryEquivOfFinrankEq` between two inner product spaces of the same dimension, plus the
linear algebra that in equal dimensions "not surjective" and "determinant zero" agree.

**What this is not.**  It is **not** a Sard theorem in any generality, and it is **not** a step
towards `R0`.  The sharp finite-regularity Sard theorem — the direct hole `Analysis.sard` — is
untouched by this module and its status is unchanged.  Sard's theorem is a statement about the
measure of the set of critical **values** of a map `ℝⁿ → ℝᵐ`; what is proved here is only the
`n = m` case, and only that case, where the critical set maps into a null set purely because a
singular linear map contracts volume.  For `n > m` the critical values of a `C¹` map can have
positive measure (Whitney), and nothing below says otherwise.  `R0`, the target of the
rank-deficient route, is a statement about `ℋ^k` **inside** a level and was proved independently in
`Analysis/Vector/RankDeficient/Coarea.lean`; `R10` is a consistency check on it, not an ingredient of it.

**Relation to `R0`.**  In the equidimensional case `R0` reads `μH[0] (C ∩ {u = t}) = 0` for almost
every `t`, and a nonempty set has `μH[0] ≥ 1`, so `R0` and `R10` are then *equivalent* statements.
Nothing of that equivalence is used here: this module imports neither `R0` nor any part of the
rank-deficient route, so the two proofs are independent and the agreement is a real cross-check.
It is recorded in `research/audits/EquidimensionalSardAudit.lean`, in both directions.
-/
````

Original comment 268, line 105:

````lean
/-- **`R10`: in equal dimensions, almost every level avoids the critical set entirely.**  The
fibre dimension is `k = 0`, so the `ℋ^0`-null conclusion of `R0` degenerates to emptiness of the
slice.  See the module docstring: this is the `n = m` case only, and is not a general Sard
theorem. -/
````

### formalization/FunctionalInequalities/Analysis/WeakDerivative/Approximation.lean

[Current source](../../formalization/FunctionalInequalities/Analysis/WeakDerivative/Approximation.lean)

Original comment 269, line 372:

````lean
/-! Bounded all-coordinate common-support approximation (accepted B1). -/
````

### formalization/FunctionalInequalities/Probability/Diffusion/Generator.lean

[Current source](../../formalization/FunctionalInequalities/Probability/Diffusion/Generator.lean)

Original comment 270, line 44:

````lean
/-- **S5c.** The coordinate-free generator is invariant under a continuous linear change of
coordinates (no differentiability hypothesis is needed for a linear equivalence). -/
````
