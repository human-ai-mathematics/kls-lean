module

public import FunctionalInequalities.Analysis.Vector.RankDeficient.StratumSlicing

/-!
# Route statements for the per-stratum local slicing

**This file contains only `#check`s.  A proposition that type-checks is not a proof.**  It declares
nothing, proves nothing, and introduces no placeholder axiom.  It preserves the two contracts `R7b`
and `R7c`, which `Analysis/Vector/RankDeficient/StratumSlicing.lean` proves — `R7b` as
`lintegral_hausdorffMeasure_stratum_le` and `R7c` as the limit step inside
`exists_nhds_ae_hausdorffMeasure_stratum_inter_levelSet_eq_zero`, the per-stratum local slicing
itself.

`R7b` and `R7c` split obligation `R7` of `RankDeficientRouteStatements.lean`, the per-stratum local
slicing.  `Analysis/Vector/RankDeficient/StratumSlicing.lean` proves two further parts of it: the
**local package** `exists_stratum_local_data`, which assembles the kernel lemma, the locally uniform
right-inverse bound and the tangential small-Lipschitz estimate into one neighbourhood carrying a
single tangential Lipschitz constant, and `lintegral_split_target`, the change-of-variables and
Tonelli identity for the orthogonal splitting of the target.  What is left is the estimate itself
and its limit, recorded here as `R7b` and `R7c`.

## Why these two and not more

With the local package in hand the argument is: run the approximating partition on `u` itself at
scale `ε`, so that one partition serves both components; on each piece the local package makes
`Q ∘ u` `c ε`-Lipschitz along every fibre of `P ∘ u`; apply the Eilenberg bound of
`Analysis/Vector/Slice/Hausdorff.lean` inside a fibre, at exponent `k` with a target of dimension
`m − r`, where `k + (m − r) = n − r` is exactly right; integrate over the fibre parameter against
the **proved** regular coarea formula for `P ∘ u`, which converts the fibre measures into an
ordinary integral of the coarea Jacobian over the piece; and use `lintegral_split_target` to read
the result as an integral over the target.  `R7b` is the outcome of that computation at a fixed
scale.  `R7c` is the limit `ε → 0`, which is the pattern already used twice in the repository, in
`Analysis/Vector/Slice/Hausdorff.lean` and `Analysis/Vector/Slice/Critical.lean`.

Together they give the per-stratum local slicing.  The null slicing on the whole critical set
further needs localization and the finite union over `r < m`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Module FunctionalInequalities FunctionalInequalities.Analysis
open scoped ENNReal NNReal

/-! ### `R7b` — the per-scale bound

At a fixed approximation scale, the total fibre measure of the stratum piece over the whole target
is controlled by `ε ^ (m − r)` times the integral of the coarea Jacobian of the regular component.
The constant depends on the ambient data but **not** on `ε`, which is what makes the limit possible.
-/

#check (∀ {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    [MeasurableSpace W] [BorelSpace W]
    {u : V → W} {k r : ℕ} {x₀ : V} {U : Set V} {c : ℝ≥0},
    ContDiff ℝ 1 u → k + finrank ℝ W = finrank ℝ V → r < finrank ℝ W →
    x₀ ∈ stratum u r → IsOpen U → x₀ ∈ U → IsCompact (closure U) →
    (∀ x ∈ closure U, coareaJacobian
      (fderiv ℝ (fun y => (tangentRange u x₀).orthogonalProjectionOnto (u y)) x) ≠ 0) →
    (∀ y ∈ stratum u r ∩ U, ∀ (ε : ℝ≥0) (S : Set V) (s : tangentRange u x₀),
      ApproximatesLinearOn u (fderiv ℝ u y) S ε →
        LipschitzOnWith (c * ε)
          (fun x => (tangentRange u x₀)ᗮ.orthogonalProjectionOnto (u x))
          (S ∩ {x : V | (tangentRange u x₀).orthogonalProjectionOnto (u x) = s})) →
    ∃ Cst : ℝ≥0∞, Cst ≠ ⊤ ∧ ∀ ε : ℝ≥0, ε ≠ 0 →
      (∫⁻ t, μH[(k : ℝ)] (stratum u r ∩ U ∩ {x : V | u x = t}) ∂(volume : Measure W))
        ≤ Cst * ((c * ε : ℝ≥0) : ℝ≥0∞) ^ (finrank ℝ W - r)
            * ∫⁻ x in stratum u r ∩ U,
                ENNReal.ofReal (coareaJacobian
                  (fderiv ℝ (fun y => (tangentRange u x₀).orthogonalProjectionOnto (u y)) x))
                ∂(volume : Measure V))

/-! ### `R7c` — the limit, and with it the per-stratum local slicing

A bound of that shape valid at every scale, with a finite right-hand factor and a positive exponent,
forces the integral to vanish, and a vanishing integral of a nonnegative almost everywhere
measurable function forces it to vanish almost everywhere.  The positivity of `m − r` is exactly
`r < m`, and the finiteness of the Jacobian integral is what the compact closure of the
neighbourhood provides.
-/

#check (∀ {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    [MeasurableSpace W] [BorelSpace W]
    {u : V → W} {k r : ℕ} {x₀ : V} {U : Set V},
    ContDiff ℝ 1 u → k + finrank ℝ W = finrank ℝ V → r < finrank ℝ W →
    x₀ ∈ stratum u r → IsOpen U → x₀ ∈ U →
    (∃ Cst D : ℝ≥0∞, Cst ≠ ⊤ ∧ D ≠ ⊤ ∧ ∃ c : ℝ≥0, ∀ ε : ℝ≥0, ε ≠ 0 →
      (∫⁻ t, μH[(k : ℝ)] (stratum u r ∩ U ∩ {x : V | u x = t}) ∂(volume : Measure W))
        ≤ Cst * ((c * ε : ℝ≥0) : ℝ≥0∞) ^ (finrank ℝ W - r) * D) →
    ∀ᵐ t ∂(volume : Measure W),
      μH[(k : ℝ)] (stratum u r ∩ U ∩ {x : V | u x = t}) = 0)
