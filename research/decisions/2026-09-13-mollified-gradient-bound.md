# Pointwise Gradient Norm Bound of Smoothing Indicators and Hole-Free Module Stratification

Date: 2026-09-13. Taking over [global Gauss–Green record](2026-09-13-global-gauss-green.md).
At the start of this round, HEAD was `2965b32`, with multiple rounds of uncommitted modifications and untracked modules; starting
`build/verification/latest.json` was `passed`, and all 364 files covered matched the current content.
This round retains these results, without submission or push. Previous decision was to preserve the original text.

## Scope of completion

`KLS.SmoothDomain.enorm_gradient_mollified_le` has been proven to migrate from
`KLS/WIP/RelativePerimeter.lean` to `KLS/Geometry/MollifiedBoundary.lean`:

```lean
theorem enorm_gradient_mollified_le (U : SmoothDomain V)
    (φ : ContDiffBump (0 : V)) (x : V) :
    ‖gradient (U.mollifiedIndicator φ volume) x‖ₑ ≤
      ∫⁻ y in frontier U.carrier, ENNReal.ofReal (φ.normed volume (x - y))
        ∂(surfaceMeasure V)
```

Mathematical range and normalization invariance: finite-dimensional real inner product spaces, any smooth region, any normalized smooth bump, at each point.
No requirement for the region to be bounded, for the boundary to have finite measure, for non-zero dimension, or for the right-hand prior to be finite.
The new consequence module does not explicitly carry `SecondCountableTopology V`, which is instead derived automatically from finite-dimensionality;
the gradient formula after migration retains its original instance scope, and the point-wise norm bound does not require re-carriage of this derivable parameter.
No new axioms, compatible aliases, or redundant proofs are introduced. The formal certification remains **24**, with no new Blueprint certification anchor points.
`lem:relative-perimeter-smoothing` infrastructure remains `missing`.

Prove first transfer the continuity and compact support of the reflected translation kernel `y ↦ φ.normed volume (x-y)` to `integrableOn_smul_outwardNormal`, obtaining genuine Bochner integrability. Then use the already proven `gradient_mollifiedIndicator_eq` (negative outward normal integral) to eliminate the negative sign in the norm, and successively apply:

1. `norm_integral_le_integral_norm` and `ENNReal.ofReal_le_ofReal`;
2. `ofReal_integral_norm_eq_lintegral_enorm`, whose integrability assumption is satisfied by the above evidence;
3. On the measurable frontier, pointwise apply `norm_smul`, `norm_outwardNormal`, and
   `ContDiffBump.nonneg_normed`, to express the norm of the normal-weighted vector as the kernel itself.

Therefore, there is no borrowing of the full definition of zero-value Bochner integral to skip integrability, nor is there use of a finite total boundary measure.
The empty boundary and zero-dimensional cases follow the same proof; the outward unit normal is only invoked on the frontier.

## Module Migration and Consumers

The actual old dependency is `GaussGreen → LocalGaussGreen → BoundaryChart → WIP/RelativePerimeter`,
cannot reverse-import GaussGreen from the last layer. This round is split by consumer as:

```text
SurfaceMeasure + Analysis/LevelSet
  → Geometry/SmoothDomain
      → Geometry/BoundaryChart → LocalGaussGreen → GaussGreen
      → Geometry/Mollification
  GaussGreen + Mollification → Geometry/MollifiedBoundary
      → WIP/RelativePerimeter → WIP/CheegerInfimum
Analysis/LevelSet + SurfaceMeasure + Mathlib calculus → WIP/AnalyticPrerequisites
```

* `Geometry/SmoothDomain.lean`: Migration to normalization convention check, `SmoothDomain` structure, locally defined functions and
  frontier interface, empty/univ, homothety, local finiteness of the boundary, Haar nullity and existing Hausdorff scaling.
* `Geometry/Mollification.lean`: migration into `mollifiedIndicator`, convolution representation, indicator local integrability,
  Smoothness / global Lipschitz / `[0,1]` range. Two existing private auxiliary lemmas
  Set `locallyIntegrable_indicator`, `mollifiedIndicator_eq` to public, names and proofs remain.
* `Geometry/GaussGreen.lean`: scalar form
  `setIntegral_gradient_eq_integral_smul_outwardNormal` Imported verbatim from AnalyticPrerequisites.
* `Geometry/MollifiedBoundary.lean`: Move into `gradient_mollifiedIndicator_eq`, and prove the current round's goal.
  Originally, the two duplicate private auxiliary proofs in AnalyticPrerequisites were removed, and consumers now use the above unique public interface.
* `BoundaryChart` import `SmoothDomain`; `RelativePerimeter` import `MollifiedBoundary`;
  `AnalyticPrerequisites` No longer indirectly introducing perimeter applications, retain 4 public theorem, where coarea two and Sard
  Three direct proof holes, only Sard's a.e. the consequences have proofs and still depend transitively on `sorryAx`.
* The independent GaussGreen client is also modified to import `MollifiedBoundary`; no forwarding declaration is left behind.

The transitive local import closure of the new consequence module consists of **15 modules, zero WIP imports**; the base module has no direct holes and does not bring in the coarea/Sard environment. All remain outside the existing certification closure, with no registration of the entire perimeter chain.
WIP direct holes: RelativePerimeter **2**, AnalyticPrerequisites **3**, CheegerInfimum **8**, Energy/WIP/Cheeger **5**, total **18**.

## Next: Gradient Integral Estimation After Outer Expansion

The goal remains the original statement `RelativePerimeter.lintegral_enorm_gradient_mollified_homothety_le`,
no proof, no problem modification. Let `n = finrank ℝ V`, `H(y)=a+(y-a)/s`, `η=φ.normed volume`,
`C=(M/b₀)^((1-s)/s)`, `Ω=interior ν.support`. The precise route is

```text
∫ ‖∇(η⋆1_{H(U)})(x)‖ dν(x)
 ≤ ∫∂H(U) ∫ η(x-q) ρ(x) dx dσ(q)
 = s^(1-n) ∫∂U ∫ η(x-H(y)) ρ(x) dx dσ(y)
 ≤ s^(1-n) C ∫∂U∩Ω ρ(y) dσ(y).
```

Existing input: pointwise bound in this round; `hρ.withDensity_eq`, `hρ.measurable`, `hρ.nonneg`;
local finiteness of surface measure on boundary; `IsBorellDensity.le_rpow_mul_of_combination`;
bump kernel is non-negative, has compact support, and integrates to 1; smooth region homothety is defined.
The following interfaces still need to be implemented in practice, not just concatenating existing theorem names:

1. **Weighted boundary change of variables.** Currently `hausdorff_frontier_homothety` only compares the
   **unnormalized total measure** of the entire frontier. This is insufficient for changing variables in weighted integrals, especially when the total measures on both sides may be infinite.
   It requires Mathlib `hausdorffMeasure_homothety_image` to establish, for any measurable boundary piece, an equality of normalized measures via pushforward/restriction, and then derive `setLIntegral` change of variables; the normalization factors are equal on both sides.
   When `n≥1`, natural numbers `n-1` and real exponents `n-1` are aligned, with scaling factor `s^(1-n)`;
   When `n=0`, the frontier being empty prevents directly using the old lemma for real exponent `-1` as if it were for natural number exponent 0.
   The private `homothetyHomeomorph` is currently used only within the base module; if new consumers require it, migration or public interface exposure is provided, without copying it.

2. **Tonelli and density rewriting.** Rewrite `ν` as `volume.withDensity (ofReal ∘ ρ)`, proving the joint kernel
   `(x,q) ↦ ofReal(η(x-q)) * ofReal(ρ x)` is measurable, and invoking the exchange of integrals for non-negative functions.
   The surface measure restricted to the frontier is locally finite, and since the finite-dimensional space is second-countable, this restriction is σ-finite;
   combined with volume, Tonelli's theorem applies. Global boundary finiteness is not required, nor is prior proof of finite weighted double integral needed.

3. **Convex combinations within kernel support and zero contribution outside Ω.** When `η(x-H(y))≠0`, define
   `z=x-H(y)`, `b=a-s/(1-s) • z`. The kernel support is given by `‖z‖<φ.rOut`, with radius condition given by
   `b∈closedBall a r⊆Ω`, and `y=s•x+(1-s)•b`. A density comparison already gives `ρ x≤Cρ y`.
   It is still necessary to prove separately: if both `ρ x>0`, then `y∈Ω`, hence when `y∉Ω` the kernel multiplied by weight is zero.
   This cannot be inferred solely from numerical comparison, nor can `∂U\Ω` be simply deleted.
   One route that does not shrink the original IsBorellDensity range is: `convex_pos` and
   `interior_support_subset` place the combination point in the interior of the positivity set;
   `continuousOn_interior_pos` adds Haar measure to open sets with positive mass, proving that the interior of the positivity set is contained in
   `ν.support`. This reverse interior containment requires a supplementary interface; it cannot rely solely on the intrinsic log-concave law-specific `convex_support` while secretly strengthening the assumptions of the current goal.

4. **Kernel averaging and coefficient consolidation.** For fixed y, perform numerical comparison of integrals, using translation invariance and `φ.integral_normed` to obtain average weight ≤ `Cρ(y)`, zero outside Ω; then integrate over frontier ∩ Ω and combine the ENNReal coefficients.
   `M≥b₀>0` is provided by the center point's hball/hM, and all rpow/ofReal are preserved with non-negativity and non-vanishing evidence.

All four steps do not require coarea, Sard, Cheeger infima, or singular law comparisons.

## What remains to construct the recovery sequence

Even if the one-step integral bound is closed, `exists_smooth_recovery_sequence` still needs:

* In the general range of IsBorellDensity, select `a∈Ω` and the internal closed ball. The existing proof of `interior_support_subset` has constructed a non-empty positivity set internally, but this is not yet a complete public interface for this choice; combining the reverse internal containment yields a non-empty Ω. Take `exists_bounds_of_isCompact` to be `b₀>0`, and take `IsBorellDensity.exists_le` to be the global M.
* Fix s, construct a bump with external radius tending to zero and prove smooth approximation `1_{H(U)}` converges `L¹(ν)` to the boundary. This can be done using Mathlib `ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable` (requiring fixed inner/outer radius ratio and correct convolution order), or by using the local constancy of the boundary exterior indicator and `ContDiffBump.normed_convolution_eq_right`. The locally integrable property of the indicator announced in this round can be reused. The absolute continuity derived from `addHaar_frontier` plus `withDensity_eq` passes the boundary zero measure, then apply `[0,1]` with a probability measure to perform dominated convergence; it is not assumed that the entire indicator is integrable over infinite volume.
* Take `s_j↑1`, and use the existing `tendsto_indicator_homothety` to control the error from expansion; for each j, choose a sufficiently small ε_j satisfying both the radius condition and the smooth L¹ error tending to zero, and combine the two terms via triangle inequality.
* `mollifiedIndicator_contDiff_lipschitz_mem_Icc` provides regularity and range requirements for each term; prove `s_j^(1-n) (M/b₀)^((1-s_j)/s_j)→1`, combining the finite `relativePerimeter` original assumption and per-step bounds to obtain an upper bound for ENNReal limsup. Including the case of zero perimeter, division by perimeter is not allowed.

Thus, the next step can focus on proving the one-step outer expansion integral bound; the recovery sequence is the result of independent subsequent convergence and diagonalization work.
coarea/Sard is an open input for future Cheeger's application, not a necessary precondition for either of these two.

## Verification Records and Boundaries

* The seven geometry modules `SurfaceMeasure / SmoothDomain / Mollification / BoundaryChart /
  LocalGaussGreen / GaussGreen / MollifiedBoundary` each actually executes
  `lake env lean -DwarningAsError=true`, all exit codes are 0, with no diagnosis.
* The strict client in the ignored path `build/audit/GaussGreenAudit.lean` exits 0, with 22 axiom reports,
  Everything consists only of `propext / Classical.choice / Quot.sound`. The key foundation of coverage migration, smoothing regularity,
  Two Gauss–Green consequences, new objectives, and originally 11 clients (internal/external support, no support constraints)
  Hemispace, direction signs, endpoints of one-dimensional intervals, empty boundary, zero-dimensional). This round added a norm bound on unbounded hemispaces.
  Client where the gradient is zero when the kernel is zero on the boundary.
* Four WIP files are actually re-elaborated in normal mode, all exit 0, diagnosis strictly as expected
  2 / 3 / 8 / 5 entries `declaration uses sorry`, no other diagnoses. This is not a WIP strict mode pass.
* Default `lake build` passed (3393 jobs). Library build log: `build/audit/mollified-library-build.log`; root directory verification command:
  `python3 research/verify.py`. The final snapshot binding verification receipt is final as per `build/verification/latest.json`.
  The evidence hash of task infrastructure is updated according to the current round of code refresh, and the status remains missing.

These are local Lean compilations, axiom checks, and unified verification receipts; third-party dependencies use compiled artifacts of fixed versions, and do not claim to reconstruct Mathlib, remote CI, or new end-to-end certificates.
