module

public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.Convex.Function

/-!
# Mollification of convex Lipschitz functions

Let `V` be a finite-dimensional real inner product space with an additive Haar measure `m`,
`φ : ContDiffBump (0 : V)` and `ρ = φ.normed m` the normalized bump, of radius `φ.rOut`.
For a continuous `g : V → ℝ` the mollification `ρ ⋆ g` is `C^∞`
(`contDiff_normed_convolution`). If `g` is convex, so is `ρ ⋆ g`, as an average of translates of
`g` (`convexOn_normed_convolution`); if `g` is `L`-Lipschitz, then `|ρ ⋆ g - g| ≤ L φ.rOut`
(`abs_normed_convolution_sub_le`). Together these produce smooth convex approximations of a
convex Lipschitz function with an explicit uniform error.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Metric ContinuousLinearMap
open scoped Convolution ContDiff

namespace FunctionalInequalities.Analysis.Mollification

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] (m : Measure V) [m.IsAddHaarMeasure]
  (φ : ContDiffBump (0 : V)) {g : V → ℝ}

/-- The mollification of a continuous function is `C^∞`. -/
theorem contDiff_normed_convolution (hg : Continuous g) :
    ContDiff ℝ ∞ (φ.normed m ⋆[lsmul ℝ ℝ, m] g) :=
  φ.hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ) φ.contDiff_normed
    hg.locallyIntegrable

/-- **The mollification of a continuous convex function is convex.** -/
theorem convexOn_normed_convolution (hg : Continuous g) (hconv : ConvexOn ℝ univ g) :
    ConvexOn ℝ univ (φ.normed m ⋆[lsmul ℝ ℝ, m] g) := by
  have hex : ConvolutionExists (φ.normed m) g (lsmul ℝ ℝ) m :=
    φ.hasCompactSupport_normed.convolutionExists_left (lsmul ℝ ℝ) φ.continuous_normed
      hg.locallyIntegrable
  refine ⟨convex_univ, fun x₁ _ x₂ _ a b ha hb hab => ?_⟩
  simp only [convolution_def, lsmul_apply, smul_eq_mul]
  have hi (x : V) : Integrable (fun t => φ.normed m t * g (x - t)) m := by
    simpa only [ConvolutionExistsAt, lsmul_apply, smul_eq_mul] using hex x
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add ((hi x₁).const_mul a)
    ((hi x₂).const_mul b)]
  refine integral_mono (hi _) (((hi x₁).const_mul a).add ((hi x₂).const_mul b)) fun t => ?_
  have hpt : a • x₁ + b • x₂ - t = a • (x₁ - t) + b • (x₂ - t) := by
    have ht : t = a • t + b • t := by rw [← add_smul, hab, one_smul]
    conv_lhs => rw [ht]
    simp only [smul_sub]
    abel
  have hc := hconv.2 (mem_univ (x₁ - t)) (mem_univ (x₂ - t)) ha hb hab
  simp only [smul_eq_mul] at hc
  have hn := φ.nonneg_normed (μ := m) t
  simp only
  rw [hpt]
  nlinarith [mul_le_mul_of_nonneg_left hc hn]

/-- **Uniform error of the mollification of a Lipschitz function**:
if `|g x - g y| ≤ L ‖x - y‖`, then `|(ρ ⋆ g) x - g x| ≤ L φ.rOut`. -/
theorem abs_normed_convolution_sub_le (hg : Continuous g) {L : ℝ} (hL : 0 ≤ L)
    (hLip : ∀ x y, |g x - g y| ≤ L * ‖x - y‖) (x : V) :
    |(φ.normed m ⋆[lsmul ℝ ℝ, m] g) x - g x| ≤ L * φ.rOut := by
  have h := φ.dist_normed_convolution_le (μ := m) (x₀ := x) (ε := L * φ.rOut)
    hg.aestronglyMeasurable (fun y hy => by
      rw [Real.dist_eq]
      refine (hLip y x).trans ?_
      have : ‖y - x‖ < φ.rOut := by rw [← dist_eq_norm]; exact hy
      exact mul_le_mul_of_nonneg_left this.le hL)
  rwa [Real.dist_eq] at h

end FunctionalInequalities.Analysis.Mollification
