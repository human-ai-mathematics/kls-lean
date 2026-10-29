import FunctionalInequalities.Analysis.Vector.RankDeficient.StratumSlicing

/-!
# Scope audit for the local package and the target split

This client restates obligation `R7` of `RankDeficientRouteStatements.lean`, the per-stratum local
slicing, **verbatim** as `route_R7` and discharges it, together with the two sub-obligations `R7b`
and `R7c` of `research/audits/Vector/StratumSlicingRouteStatements.lean`, and audits the pieces it
is built from.  The null slicing on the whole critical set further needs localization of the
per-stratum statement and the finite union over `r < m`; those are audited in
`RankDeficientCoareaAudit.lean`.

**What the local package delivers, and why the uniformity is the point.**  Around a point of the
rank-`r` stratum there is an open neighbourhood with compact closure on which the regular component
`P ∘ u` is a submersion, together with **one** constant `c` that works for **every** point `y` of the
stratum in that neighbourhood.  That uniformity is the whole difficulty: the approximating partition
produces a different linear model `fderiv ℝ u y` on every piece, and the constant of the tangential
small-Lipschitz estimate depends on that model through `‖fderiv ℝ u y‖` and the right-inverse
bound.  It is obtained from the kernel lemma, the **locally uniform** right-inverse bound, and a
bound on `‖fderiv ℝ u‖` near the point — which is exactly why the right-inverse bound needed its
uniform version.

**What this does not do.**  The per-stratum local slicing is a statement about **one stratum in one
neighbourhood**.  It says nothing about the whole critical set, which is the union of the strata of
every rank `r < m` and needs localization to be assembled; and it is not a coarea formula in a new
case, nor a Sard theorem — no claim whatever is made about the measure of the set of critical
*values*.
-/

noncomputable section

open MeasureTheory Set Module Filter Topology FunctionalInequalities
open FunctionalInequalities.Analysis
open scoped ENNReal NNReal

namespace StratumSlicingAudit

/-! ### The per-stratum local slicing, restated verbatim and discharged -/

/-- **Route obligation `R7`**, copied from
`research/audits/Vector/RankDeficientRouteStatements.lean` and discharged. -/
theorem route_R7 :
    (∀ {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
      [MeasurableSpace V] [BorelSpace V]
      [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
      [MeasurableSpace W] [BorelSpace W]
      {u : V → W} {k r : ℕ}, ContDiff ℝ 1 u → k + finrank ℝ W = finrank ℝ V →
      r < finrank ℝ W →
      ∀ x₀ ∈ {x : V | (fderiv ℝ u x).toLinearMap.rank = (r : Cardinal)}, ∃ U ∈ nhds x₀,
        ∀ᵐ t ∂(volume : Measure W),
          μH[(k : ℝ)] ({x : V | (fderiv ℝ u x).toLinearMap.rank = (r : Cardinal)} ∩ U
            ∩ {x : V | u x = t}) = 0) :=
  fun hu hk hr _ hx₀ =>
    exists_nhds_ae_hausdorffMeasure_stratum_inter_levelSet_eq_zero hu hk hr hx₀

section Package

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]

omit [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ W] [MeasurableSpace W]
  [BorelSpace W] in
/-- **The local package, restated independently.**  `u` is only `C¹`, the point is only required to
lie on the stratum, and the constant `c` does **not** depend on the point `y`, on `ε`, on the set `S`
or on the fibre `s`. -/
theorem local_package {u : V → W} (hu : ContDiff ℝ 1 u) {r : ℕ} {x₀ : V}
    (hx₀ : x₀ ∈ stratum u r) :
    ∃ (U : Set V) (c : ℝ≥0), IsOpen U ∧ x₀ ∈ U ∧ IsCompact (closure U) ∧
      (∀ x ∈ closure U, coareaJacobian
        (fderiv ℝ (fun y => (tangentRange u x₀).orthogonalProjectionOnto (u y)) x) ≠ 0) ∧
      (∀ y ∈ stratum u r ∩ U, ∀ (ε : ℝ≥0) (S : Set V) (s : tangentRange u x₀),
        ApproximatesLinearOn u (fderiv ℝ u y) S ε →
          LipschitzOnWith (c * ε)
            (fun x => (tangentRange u x₀)ᗮ.orthogonalProjectionOnto (u x))
            (S ∩ {x : V | (tangentRange u x₀).orthogonalProjectionOnto (u x) = s})) :=
  exists_stratum_local_data hu hx₀

omit [FiniteDimensional ℝ W] [MeasurableSpace W] [BorelSpace W] in
/-- **The stratum is measurable**, so the set the package is about is a legitimate target for a
measure-theoretic argument.  This is the measurability half of the rank stratification, recorded
here because the per-stratum local slicing consumes it. -/
theorem stratum_measurable {u : V → W} (hu : ContDiff ℝ 1 u) (r : ℕ) :
    MeasurableSet (stratum u r) :=
  measurableSet_rank_fderiv_eq hu r

omit [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ W] [MeasurableSpace W]
  [BorelSpace W] in
/-- **The regular component is `C¹` and its differential is the projected differential.** -/
theorem regular_component {u : V → W} (hu : ContDiff ℝ 1 u) (x₀ x : V) :
    fderiv ℝ (fun y => (tangentRange u x₀).orthogonalProjectionOnto (u y)) x
      = (tangentRange u x₀).orthogonalProjectionOnto.comp (fderiv ℝ u x) :=
  fderiv_clm_comp hu _ x

omit [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ W] [MeasurableSpace W]
  [BorelSpace W] in
/-- **At the base point the regular component really is a submersion**, which is what makes the
neighbourhood nonempty. -/
theorem base_point_regular (u : V → W) (x₀ : V) :
    Function.Surjective ((tangentRange u x₀).orthogonalProjectionOnto.comp (fderiv ℝ u x₀)) :=
  surjective_proj_comp u x₀

end Package

section Split

variable {W W₁ W₂ : Type*}
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]
  [NormedAddCommGroup W₁] [InnerProductSpace ℝ W₁] [FiniteDimensional ℝ W₁]
  [MeasurableSpace W₁] [BorelSpace W₁]
  [NormedAddCommGroup W₂] [InnerProductSpace ℝ W₂] [FiniteDimensional ℝ W₂]
  [MeasurableSpace W₂] [BorelSpace W₂]

/-- **The integral form of the target splitting, restated.**  Only almost everywhere measurability
of the integrand is assumed; the splitting is an arbitrary linear isometry. -/
theorem target_split (e : W ≃ₗᵢ[ℝ] WithLp 2 (W₁ × W₂)) {f : W → ℝ≥0∞}
    (hf : AEMeasurable f (volume : Measure W)) :
    ∫⁻ t, f t ∂(volume : Measure W)
      = ∫⁻ s, ∫⁻ τ, f (e.symm (WithLp.toLp 2 (s, τ))) ∂(volume : Measure W₂)
          ∂(volume : Measure W₁) :=
  lintegral_split_target e hf

/-- **The splitting along an orthogonal complement**, the one the route uses. -/
theorem target_split_orthogonal (K : Submodule ℝ W) {f : W → ℝ≥0∞}
    (hf : AEMeasurable f (volume : Measure W)) :
    ∫⁻ t, f t ∂(volume : Measure W)
      = ∫⁻ s, ∫⁻ τ, f (K.orthogonalDecomposition.symm (WithLp.toLp 2 (s, τ)))
          ∂(volume : Measure Kᗮ) ∂(volume : Measure K) :=
  lintegral_split_target K.orthogonalDecomposition hf

end Split

end StratumSlicingAudit

/-! ### Axiom audit: every report is standard-only -/

#print axioms FunctionalInequalities.Analysis.fderiv_clm_comp
#print axioms FunctionalInequalities.Analysis.surjective_proj_comp
#print axioms FunctionalInequalities.Analysis.finrank_tangentRange_eq
#print axioms FunctionalInequalities.Analysis.exists_stratum_local_data
#print axioms FunctionalInequalities.Analysis.lintegral_split_target
#print axioms FunctionalInequalities.Analysis.hausdorffMeasure_eq_inv_mul_normalized
#print axioms FunctionalInequalities.Analysis.finrank_tangentRange_eq_of_mem
#print axioms FunctionalInequalities.Analysis.lintegral_hausdorffMeasure_stratum_le
#print axioms FunctionalInequalities.Analysis.exists_nhds_ae_hausdorffMeasure_stratum_inter_levelSet_eq_zero
#print axioms StratumSlicingAudit.route_R7
#print axioms StratumSlicingAudit.local_package
#print axioms StratumSlicingAudit.stratum_measurable
#print axioms StratumSlicingAudit.regular_component
#print axioms StratumSlicingAudit.base_point_regular
#print axioms StratumSlicingAudit.target_split
#print axioms StratumSlicingAudit.target_split_orthogonal
