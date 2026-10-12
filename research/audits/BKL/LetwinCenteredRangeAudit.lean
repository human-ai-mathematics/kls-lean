import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Range
import FunctionalInequalities.KLS.BKL.GaussianTaylor
import FunctionalInequalities.KLS.LogConcave.RegularIsotropic

/-!
# Audit: centered range density for the standard Gaussian law

Source: Letwin, arXiv:2607.24164v1, Lemma A.6 (support only: density of compact smooth diffusion images in centered
`L²`). A real nonzero client: for the canonical Gaussian law `e^{−x²/2}` on `ℝ` (the regular potential `‖x‖²/2`), the class
`g = id` has `‖g‖² = 1`, `g ≠ 0`, mean `0`, and lies in the closure of the compact smooth diffusion images, by the
production theorem `centered_mem_closure_compactSmoothDiffusionImage`. Every premise is derived here. Not Brascamp–Lieb,
A.6 or a moment-map client. Client body: strong-API candidate (`api-centered-range-gaussian-compiler-v6`, 527e35ef…),
verbatim.
-/

noncomputable section

open MeasureTheory Filter Topology Set InnerProductSpace
open FunctionalInequalities
open FunctionalInequalities.L2
open FunctionalInequalities.KLS.LogConcave
open FunctionalInequalities.Analysis.Semigroup
open FunctionalInequalities.Analysis.Semigroup.Generated
open FunctionalInequalities.Analysis.BakryEmery
open scoped ContDiff RealInnerProductSpace LinearPMap

open FunctionalInequalities.KLS.LogConcave.HeatSemigroup

namespace LetwinCenteredRangeAudit

theorem gaussian_nonzero_client :
    let ν : ProbabilityMeasure ℝ :=
      (FunctionalInequalities.KLS.regularPotential_half_norm_sq (E := ℝ)).law
    let U : ℝ → ℝ := fun x => ‖x‖ ^ 2 / 2
    let hU : ContDiff ℝ 1 U :=
      (FunctionalInequalities.KLS.regularPotential_half_norm_sq (E := ℝ)).temperate.1.of_le
        (WithTop.coe_le_coe.mpr le_top)
    ∃ g : Lp ℝ 2 (ν : Measure ℝ),
      ‖g‖ ^ 2 = 1 ∧
      g ≠ 0 ∧
      L2.mean ν g = 0 ∧
      g ∈ closure (compactSmoothDiffusionImage hU) := by
  let ν : ProbabilityMeasure ℝ :=
    (FunctionalInequalities.KLS.regularPotential_half_norm_sq (E := ℝ)).law
  let U : ℝ → ℝ := fun x => ‖x‖ ^ 2 / 2
  let hU : ContDiff ℝ 1 U :=
    (FunctionalInequalities.KLS.regularPotential_half_norm_sq (E := ℝ)).temperate.1.of_le
      (WithTop.coe_le_coe.mpr le_top)
  have hν : FunctionalInequalities.KLS.LogConcave ν := by
    exact
      (FunctionalInequalities.KLS.regularPotential_half_norm_sq (E := ℝ)).logConcave_law
  have hνU : (ν : Measure ℝ) = (volume : Measure ℝ).tilted (-U) := by
    rfl
  have h2 : MemLp (id : ℝ → ℝ) 2 (ν : Measure ℝ) := by
    exact FunctionalInequalities.KLS.RegularPotential.memLp_id_two
      (FunctionalInequalities.KLS.regularPotential_half_norm_sq (E := ℝ))
  let g : Lp ℝ 2 (ν : Measure ℝ) := h2.toLp (id : ℝ → ℝ)
  have hmean : L2.mean ν g = 0 := by
    rw [L2.mean_eq_integral]
    calc
      (∫ x, g x ∂(ν : Measure ℝ)) = ∫ x, x ∂(ν : Measure ℝ) := by
        apply integral_congr_ae
        change (h2.toLp (id : ℝ → ℝ) : ℝ → ℝ) =ᵐ[(ν : Measure ℝ)] (id : ℝ → ℝ)
        exact h2.coeFn_toLp
      _ = 0 := by
        rw [hνU]
        simpa [U] using
          (FunctionalInequalities.KLS.integral_id_tilted_half_norm_sq (E := ℝ))
  have hnormsq : ‖g‖ ^ 2 = 1 := by
    calc
      ‖g‖ ^ 2 = ∫ x, ‖(id : ℝ → ℝ) x‖ ^ 2 ∂(ν : Measure ℝ) := by
        simpa [g] using (L2.norm_toLp_sq h2)
      _ = ∫ x, ⟪(1 : ℝ), x⟫ ^ 2 ∂(ν : Measure ℝ) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun x => by
          change ‖x‖ ^ 2 = ⟪(1 : ℝ), x⟫ ^ 2
          rw [← real_inner_self_eq_norm_sq]
          simp only [Real.inner_apply]
          ring)
      _ = ‖(1 : ℝ)‖ ^ 2 := by
        rw [hνU]
        simpa [U] using
          (FunctionalInequalities.KLS.integral_inner_sq_tilted_half_norm_sq (E := ℝ)
            (1 : ℝ))
      _ = 1 := by norm_num
  have hne : g ≠ 0 := by
    intro hg
    rw [hg] at hnormsq
    norm_num at hnormsq
  have hclosure : g ∈ closure (compactSmoothDiffusionImage hU) :=
    centered_mem_closure_compactSmoothDiffusionImage
      (ν := ν) (m := (volume : Measure ℝ)) hν hνU hU g hmean
  exact ⟨g, hnormsq, hne, hmean, hclosure⟩

end LetwinCenteredRangeAudit

#print axioms FunctionalInequalities.KLS.LogConcave.HeatSemigroup.centered_mem_closure_compactSmoothDiffusionImage
#print axioms FunctionalInequalities.KLS.LogConcave.HeatSemigroup.center_mem_closure_compactSmoothDiffusionImage
#print axioms LetwinCenteredRangeAudit.gaussian_nonzero_client
