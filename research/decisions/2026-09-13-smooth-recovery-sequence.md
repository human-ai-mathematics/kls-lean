# Smooth Recovery Sequence of Relative Perimeter

Date: 2026-09-13. Taking over [external expansion gradient integral record](2026-09-13-dilated-gradient-integral.md).
Starting HEAD is `2965b32`; the 372 files passed the verification receipt from the previous round all match the initial snapshot.
Retain previous unsubmitted and untracked results; no commit or push in this round; historical decision records are not rewritten.

## Goals and Scope

`KLS.RelativePerimeter.exists_smooth_recovery_sequence` has been proven and migrated into the new hole-free module
`formalization/FunctionalInequalities/KLS/Geometry/PerimeterRecovery.lean`.
The statement text matches the original target: any finite-dimensional real inner product space, a Borell probability density with respect to **Lebesgue volume** `ρ`,
any `SmoothDomain U`, under the assumption of `relativePerimeter ρ (interior ν.support) U ≠ ⊤`, yields
`u : ℕ → V → ℝ`, each term globally `C^∞`, globally Lipschitz, taking values in `[0,1]`, and

```
∫⁻ ‖u j - 1_U‖ₑ dν → 0,      limsup ∫⁻ ‖∇(u j)‖ₑ dν ≤ relativePerimeter ρ Ω U.
```

No additional assumptions on boundedness of regions, boundedness of boundaries, boundedness of carriers, finite total boundary measure, non-zero dimension, or extra density regularity are required;
the Lipschitz constant does not need to be uniformly bounded with respect to `j`. The assumption of finite relative perimeter is retained in the statement, though it is not actually used in the proof (lower bounds and limit arguments also hold for `⊤`), so the bound appears at `_hU`, with no change in mathematical scope.

This round reduces the direct proof hole from **17** to **16**: AnalyticPrerequisites **3**, CheegerInfimum **8**, Energy/WIP/Cheeger **5**. `KLS/WIP/RelativePerimeter.lean` has no remaining content and is being fully deleted.
The certification remains **24**, and the infrastructure relative to the perimeter chain remains `missing`.
The coarea, Sard, Cheeger infimum, and general singular law comparison are not addressed in this round and are not prerequisites of this construction.

## Actual proof

1. **Density ball and global upper bound.** `LogConcave/DensityBounds.lean` originally for `private` the
   `IsBorellDensity.exists_ball_le` changed to public (the unique proof location remains unchanged, no reproof is performed),
   Give a lower bound on `a`, `r₀>0`, `b₀>0`, and `ball a r₀`. Take `r = r₀/2`,
   `closedBall a r ⊆ ball a r₀` lower bound for closed balls; `ball a r₀ ⊆ {ρ>0}` plus `interior_maximal`
   With the existing `interior_pos_subset` given to `closedBall a r ⊆ interior ν.support`.
   `exists_le` gives `M`, `b₀ ≤ ρ a ≤ M` gives `M > 0`.
2. **Absolute continuity.** Added `IsBorellDensity.absolutelyContinuous` (`ν ≪ m`, directly by
   obtained from `withDensity_absolutelyContinuous`). Together with the proved `SmoothDomain.addHaar_frontier`
   Synthesis yields `ν (frontier U.carrier) = 0` and the same conclusion for each external extension region;
   No assumption is made that the indicator is integrable over the full space.
3. **Smoothing convergence under fixed scaling.** `SmoothDomain.mollifiedIndicator_eq_indicator_of_const`:
   If the indicator takes a constant value on the half-ball outside the bump, then the smoothed value is exactly equal to the indicator. Proof by
   `φ.support_normed_eq` Set the exterior kernel to zero, `φ.normed_neg` and `integral_sub_right_eq_self`
   Transform the kernel integral into `φ.integral_normed = 1`, using only normalization, without needing the Lebesgue differentiation theorem.
   `SmoothDomain.exists_bump_lintegral_enorm_mollifiedIndicator_sub_lt` Take explicit bump family
   `rOut = R/(k+2)`, `rIn = rOut/2`, locally constant radius taken from the openness of the region or the complement of the closure outside the frontier,
   Use `[0,1]` to control and dominate the probabilistic measure convergence, obtaining `L¹(ν)` error tending to zero, then select an item within the given tolerance.
   The conclusion also provides `rOut < R` for diagonal selection use.
4. **Diagonal selection.** Take `s j = 1 - 1/(j+2) ↑ 1`. For each `j` use the previous step in
   `R = r(1-s j)/s j`, tolerance `((j:ℝ≥0∞)+1)⁻¹` selects bump `φ j`, thus simultaneously satisfying
   `s j * (φ j).rOut / (1 - s j) < r` and polishing error tending to zero.
   `u j` Take the smoothed indicator of the outer expanded region `U.homothety a (s j)⁻¹`.
   `L¹` error is split into `enorm_add_le` and the measurable function's `lintegral_add_left`, consisting of a smoothed term and an outer expansion term,
   The external expansion term is reduced to a previously proven one via `SmoothDomain.indicator_homothety` and `inv_inv`.
   composition of `RelativePerimeter.tendsto_indicator_homothety` with `s j → 1`,
   Again use the squeezing of ENNReal to obtain joint convergence; do not treat the two convergences directly as joint convergence.
5. **Gradient budget.** Regularity directly takes `mollifiedIndicator_contDiff_lipschitz_mem_Icc`.
   The gradient integral of each term is dominated by the previous round `lintegral_enorm_gradient_mollified_homothety_le`, with coefficient
   `s j ^ (1 - finrank ℝ V) * (M/b₀)^((1-s j)/s j)`. Base `s j → 1 > 0`,
   Exponential `(1-s j)/s j → 0`, `M/b₀ > 0`, from `Real.continuousAt_rpow_const` and
   `Real.continuous_const_rpow` makes the coefficient tend to `1`; both side conditions of `ENNReal.Tendsto.mul` follow from
   The limit `1 ≠ 0, 1 ≠ ⊤` holds, so `ofReal (c j) * P → P` also holds for `P = 0` and `P = ⊤`.
   Finally add `limsup_le_limsup` to `Tendsto.limsup_eq` for `limsup ≤ P`, without dividing by the relative perimeter.

## Layering, Migration, and Deletion

* The new module `Geometry/PerimeterRecovery.lean` only imports `Geometry/RelativePerimeter`,
  local transitive import closure consists of **30 modules, zero WIP imports**.
* `LogConcave/DensityBounds.lean` only changes visibility and adds absolute continuity, without copying existing proofs.
* `KLS/WIP/RelativePerimeter.lean` is **deleted** due to no remaining content; `KLS/WIP/CheegerInfimum.lean`
  is now directly imported from `Geometry/PerimeterRecovery`. No alias compatibility, forward declarations, or empty shell modules are present.
* Names, namespaces, `surfaceMeasure` normalization, and `volume` baseline remain unchanged.

## Verification

* `exists_smooth_recovery_sequence`, two smoothing lemmas, `absolutelyContinuous` and `exists_ball_le`'s transitive axioms are all `propext / Classical.choice / Quot.sound`, without `sorryAx`.
* Eight related hole-free modules (DensityBounds, SmoothDomain, SurfaceMeasure, SurfaceHomothety, Mollification, MollifiedBoundary, RelativePerimeter, PerimeterRecovery) compile directly via `lake env lean -DwarningAsError=true`.
* The independent client `build/audit/RecoveryAudit.lean` compiles strictly as well, containing 9 clients and 14 axiom reports: unbounded regions, boundaries, and carriers; pointwise Lipschitz and `[0,1]`; any `L¹` tolerance achievable; zero relative perimeter gives `limsup = 0`; zero-dimensional; the whole space as an unbounded zero-perimeter region; mollification of the whole space is always `1` while mollification of empty regions is always `0` (direction of the core and normalization checks); any small bump radius.
  Both `DilationAudit` and `GaussGreenAudit` clients have been rerun, still relying only on the standard three axioms.
* Three WIP files are recompiled in normal mode, diagnosed with **3/8/5** direct proof holes, still not passing strict mode.
* After default `lake build` and root directory `python3 research/verify.py` completion, the final source code verification receipt is `build/verification/latest.json`; infrastructure evidence hash is synchronized and refreshed, WIP module entries removed, new module entries added.

Verification is local compilation, axiom auditing, and local kernel replay under a fixed third-party compiler dependency, not remote CI.

## Next step: what is missing from the h_M ≤ h_S branch?

The only consumer of the recovery sequence is `KLS/WIP/CheegerInfimum.lean`'s `minkowskiConstant_le_smoothConstant`. After this round, the dependencies of this theorem remain only two, both unrelated to Sard and weighted coarea:

1. `lintegral_minkowskiContent_superlevel_le` (Minkowski coarea inequality,
   (Ambrosio–Di Marino–Gigli 2017 lemma 3.2): for `C¹` Lipschitz `u`,
   `∫ ν⁺({u ≥ t}) dt ≤ ∫ ‖∇u‖ dν`. This is an independent analysis lemma, without requiring density.
   This is the next smallest goal.
2. `minkowskiConstant_mul_lintegral_min_superlevel_le`: By the 1th axiom plus
   The mass of open and closed superlevel sets of monotone functions is almost everywhere the same `t`.

With these two, `minkowskiConstant_le_smoothConstant` is purely assembled: for each smooth domain of intermediate mass, take the current recovery sequence, apply the 2th statement term by term, then use the already proven `tendsto_lintegral_min_superlevel` to transfer the convergence of `L¹` to the balanced quantity on the superlevel set, take `limsup` and close out with respect to `iInf`; the case of `P_ρ(U) = ⊤` is trivially handled.

The other direction `smoothConstant_le_minkowskiConstant` still requires `WIP/AnalyticPrerequisites`'s Sard and weighted coarea, as well as `lintegral_enorm_gradient_distanceCutoff_le`, and has made no progress this round. Therefore, the completion of the recovery sequence cannot be stated as coarea, Cheeger bridge, or the entire relative perimeter chain being completed.
