import FunctionalInequalities.KLS.CEK.MomentRegularity.Smooth
import FunctionalInequalities.Analysis.BakryEmery.Hessian.Trace
import FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.InverseHessian.Cutoff
import Mathlib.LinearAlgebra.Determinant

/-!
# Smooth moment-map calculus and conservative height cutoffs

Letwin arXiv:2607.24164v1, Lemma 2.4 and Lemmas A.4/A.5, in the strong regular class.
One actual smooth moment potential supplies the pointwise Hessian generator identity,
smooth compact height cutoffs with an O(1/N) generator defect, and conservativity for every
bounded smooth test with Lf + cf >= 0, c > 0. Every positive dimension is included.
Only the strong regular class is treated here; smooth moment potentials for the literal merely
convex source class (Lemma 2.2 and Theorem 2.5) are produced in `KLS/Letwin/MomentMap.lean`
through `KLS/CEK/MomentRegularity/GivenGradient.lean`.
-/
noncomputable section
namespace FunctionalInequalities.Analysis
open Set Metric MeasureTheory Filter Topology
open FunctionalInequalities.Analysis.BakryEmery FunctionalInequalities.Probability.Stein
open scoped NNReal ContDiff ENNReal
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

section RegularClass
variable (hn : 0 < n) {K : Set (EuclideanSpace ℝ (Fin n))} {W : EuclideanSpace ℝ (Fin n) → ℝ}
  {κ : ℝ} (hκ : 0 < κ) (hK : IsCompact K) (hKc : Convex ℝ K) (hKint : (interior K).Nonempty)
  (hW : ContDiff ℝ ∞ W) (hstrong : ConvexOn ℝ univ (fun y => W y - (κ / 2) * ‖y‖ ^ 2))
  (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hμ : (μ : Measure (EuclideanSpace ℝ (Fin n))) =
    (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
      (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p))))
  (hiso : KLS.Isotropic μ)
include hn hκ hK hKc hKint hW hstrong hμ hiso

/-- Original strong-class inputs produce the smooth Hessian identity, A.4 cutoffs and A.5 conservativity
at one normalized transporting potential. No cutoff or generator-integrability premise is supplied. -/
theorem exists_regular_smooth_moment_calculus :
    ∃ (u : E → ℝ) (L : NNReal),
      ContDiff ℝ ∞ u ∧ ConvexOn ℝ univ u ∧ LipschitzWith L u ∧
      (∫ x, Real.exp (-u x) ∂(volume : Measure E)) = 1 ∧
      ((volume : Measure E).tilted (-u)).map (gradient u) = (μ : Measure E) ∧
      (∀ x, (hessianMatrix u x).PosDef) ∧
      (∀ x, logDetHessian u (stdOrthonormalBasis ℝ E) x = -u x + W (gradient u x)) ∧
      range (gradient u) ⊆ interior K ∧
      (∀ x, stdHessianMatrixGenerator u W x = -stdHessianMatrix u x +
        stdHessianMatrix u x * hessianMatrixIn W (stdOrthonormalBasis ℝ E) (gradient u x) *
          stdHessianMatrix u x + stdThirdGram u x) ∧
      ∃ (χ : ℕ → E → ℝ) (C : ℝ), 0 ≤ C ∧
        (∀ N, ContDiff ℝ ∞ (χ N)) ∧ (∀ N, HasCompactSupport (χ N)) ∧
        (∀ N x, 0 ≤ χ N x ∧ χ N x ≤ 1) ∧
        (∀ x, Monotone (fun N => χ N x)) ∧
        (∀ x, Tendsto (fun N => χ N x) atTop (𝓝 1)) ∧
        (∀ N, Integrable (hessianInverseOperator u W (χ N)) ((volume : Measure E).tilted (-u))) ∧
        (∀ N, (∫ x, |hessianInverseOperator u W (χ N) x|
          ∂((volume : Measure E).tilted (-u))) ≤ C / ((N : ℝ) + 1)) ∧
        Tendsto (fun N => ∫ x, |hessianInverseOperator u W (χ N) x|
          ∂((volume : Measure E).tilted (-u))) atTop (𝓝 0) ∧
        ∀ f : E → ℝ, ContDiff ℝ ∞ f → ∀ D : ℝ, (∀ x, |f x| ≤ D) →
          ∀ c : ℝ, 0 < c → (∀ x, 0 ≤ hessianInverseOperator u W f x + c * f x) →
            Integrable (hessianInverseOperator u W f) ((volume : Measure E).tilted (-u)) ∧
            (∫ x, hessianInverseOperator u W f x ∂((volume : Measure E).tilted (-u))) = 0 := by
  obtain ⟨u, L, _LF, _T, hconv, hl, hnorm, hmap, _hC1, _hG, _hF, _hd, _hT, hC2, _hHc,
      hEvery, _hLocal, he, _hΨ, hsm, _hall, _hΨsm⟩ :=
    exists_regular_moment_potential_smooth hn hκ hK hKc hKint hW hstrong μ hμ hiso
  have hPD : ∀ x v : E, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ u x v v :=
    fun x v hv => bilinearIteratedFDerivTwo_pos_of_hessianMatrix_posDef (hEvery x).1 v hv
  have hMA : ∀ x, logDetHessian u (stdOrthonormalBasis ℝ E) x = -u x + W (gradient u x) := by
    intro x
    rw [logDetHessian_std_eq_log_det_hessianMatrix hC2]
    exact (hEvery x).2.1
  obtain ⟨e, he⟩ := he
  have hRange : range (gradient u) ⊆ interior K := by
    rintro _ ⟨x, rfl⟩
    rw [← he x]
    exact (e x).property
  have hRangeK : range (gradient u) ⊆ K := hRange.trans interior_subset
  obtain ⟨χ, C, hC, hχ, hχS, hχB, hχM, hχL, hχI, hχD, hχDL⟩ :=
    exists_cutoffs_hessianInverseOperator (volume : Measure E) hsm hconv hK.isBounded hRangeK
      isOpen_univ (subset_univ _) hW.contDiffOn hMA hPD hnorm
  refine ⟨u, L, hsm, hconv, hl, hnorm, hmap, fun x => (hEvery x).1, hMA, hRange,
    ?_, χ, C, hC, hχ, hχS, hχB, hχM, hχL, hχI, hχD, hχDL, ?_⟩
  · exact stdHessianMatrixGenerator_eq_on_range hsm isOpen_univ (subset_univ _) hW.contDiffOn
      hRangeK hMA hPD
  · intro f hf D hfD c hc hLower
    exact integrable_and_integral_hessianInverseOperator_eq_zero_of_cutoffs (volume : Measure E)
      hsm hf isOpen_univ hW.contDiffOn (subset_univ _) hMA hPD hnorm D hfD c hc hLower
      χ hχ hχS hχB hχL hχI hχDL
end RegularClass
end FunctionalInequalities.Analysis
