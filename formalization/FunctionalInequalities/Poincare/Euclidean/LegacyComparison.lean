import FunctionalInequalities.Poincare.Basic
import FunctionalInequalities.Poincare.Euclidean.AffineComparison
import FunctionalInequalities.Poincare.Relaxation

/-!
# Connecting legacy smooth tests to the selected relaxed constant

These five proved comparisons belong to `lem:legacy-relaxed-poincare-comparison`.
Read them in order: identify the raw test family, compare finite constants with ambient
relaxation, compare extended optima, then use the ambient/intrinsic-affine bridge.

The normalization is always variance at most `C` times the integral of the squared gradient;
there is no factor of two. Legacy `Holds` takes a real constant, so its argument is explicitly
`(C : ℝ)` for `C : NNReal`. Optimal constants stay in `ENNReal`, including infinity.

Source: Blueprint `thm:legacy-relaxed-holds-equivalence` and
`thm:legacy-canonical-constant-comparison`. The historical manuscript's Definition 2.1 supplies
the variance/gradient normalization, as documented in `Poincare.Basic`; the exact test domain,
relaxation and coordinate comparisons are local specifications. They apply to every Borel
probability in finite dimension, without second moments, density, log-concavity, or a positive
dimension assumption. They do not identify the locally Lipschitz literature constant.
-/

noncomputable section

open MeasureTheory

namespace FunctionalInequalities.Poincare.Euclidean

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
  (μ : ProbabilityMeasure E)

/-- The concrete smooth-gradient family has exactly the legacy fixed-constant inequality.
Source: identical smooth finite-energy tests and `L2.variance_toLp`; no closure theorem is used. -/
theorem holds_iff_preEnergy (C : NNReal) :
    Holds (μ : Measure E) (C : ℝ) ↔
      (TestFamily.ofPreEnergy μ (Energy.Euclidean.smoothGradientPreEnergy μ)).Holds C := by
  have hvariance (f : Energy.Euclidean.SmoothGradientTest μ) :
      (L2.variance μ f.toL2 : ℝ) = ProbabilityTheory.variance f.toFun (μ : Measure E) :=
    (L2.coe_variance_eq_pointwise μ f.toL2).trans
      (ProbabilityTheory.variance_congr f.toL2_coeFn)
  constructor
  · intro h
    change ∀ f : Energy.Euclidean.SmoothGradientTest μ,
      L2.variance μ f.toL2 ≤ C * f.gradientEnergy
    intro f
    apply NNReal.coe_le_coe.mp
    rw [hvariance, NNReal.coe_mul]
    exact h.variance_le ⟨f.contDiff, f.memLp_two, f.gradient_sq_integrable⟩
  · intro h
    refine ⟨inferInstance, C.2, ?_⟩
    intro f hf
    let t : Energy.Euclidean.SmoothGradientTest μ :=
      ⟨f, hf.smooth', hf.memLp_two, hf.energy_integrable⟩
    have ht := NNReal.coe_le_coe.mpr (h t)
    change (L2.variance μ t.toL2 : ℝ) ≤ (C * t.gradientEnergy : NNReal) at ht
    rw [hvariance, NNReal.coe_mul] at ht
    exact ht

/-- Legacy and ambient relaxed inequalities have the same valid finite constants.
Source: Blueprint `thm:legacy-relaxed-holds-equivalence` and the abstract pre-energy bridge. -/
theorem holds_iff_ambient (C : NNReal) :
    Holds (μ : Measure E) (C : ℝ) ↔ Ambient.Holds μ C := by
  exact (holds_iff_preEnergy μ C).trans
    (TestFamily.holds_ofPreEnergy_iff μ (Energy.Euclidean.smoothGradientPreEnergy μ) C)

/-- The legacy infimum equals the ambient relaxed Rayleigh supremum, also at infinity.
Source: equality of the sets of valid finite constants; no attainment assumption is needed. -/
theorem constant_eq_ambient :
    constant (μ : Measure E) = Ambient.constant μ := by
  apply le_antisymm
  · by_cases h : Ambient.constant μ = ⊤
    · simp [h]
    · have hcoe := ENNReal.coe_toNNReal h
      have hbound := (Ambient.holds_iff_constant_le μ _).mpr hcoe.ge
      exact (constant_le ((holds_iff_ambient μ _).mpr hbound)).trans hcoe.le
  · apply le_constant
    intro C hC
    exact (Ambient.holds_iff_constant_le μ C).mp
      ((holds_iff_ambient μ C).mp hC)

/-- A finite legacy bound gives exactly the selected intrinsic-affine inequality.
Source: the preceding fixed-constant equivalence and the ambient/intrinsic-affine comparison. -/
theorem holds_iff_canonical (C : NNReal) :
    Holds (μ : Measure E) (C : ℝ) ↔ Canonical.Holds μ C := by
  exact (holds_iff_ambient μ C).trans
    (Ambient.holds_iff_canonical μ C)

/-- The legacy and selected extended optima agree for every finite-dimensional law.
Source: Blueprint `thm:legacy-canonical-constant-comparison`; literature equivalence is separate. -/
theorem constant_eq_canonical :
    constant (μ : Measure E) = Canonical.constant μ := by
  exact (constant_eq_ambient μ).trans
    (Ambient.constant_eq_canonical μ)

end FunctionalInequalities.Poincare.Euclidean
