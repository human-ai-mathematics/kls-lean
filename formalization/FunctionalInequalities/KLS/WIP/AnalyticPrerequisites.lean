import FunctionalInequalities.Analysis.LevelSet
import FunctionalInequalities.KLS.Geometry.SurfaceMeasure
import Mathlib.Analysis.Calculus.Implicit
import Mathlib.Analysis.Calculus.Gradient.Basic

/-! # Open analytic prerequisites

Weighted coarea and Sard remain two direct holes.  Its measurability half
`Analysis.aemeasurable_lintegral_levelSet` moved to the hole-free
`KLS/Geometry/LevelSetMeasurable.lean` with a byte-identical `pp.all` signature, where it is
proved; only the **equality** below is still open here.
The Sard consequence inherits its hole. Gauss–Green and mollification consequences
now live in `KLS/Geometry`, without importing this module. -/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff Pointwise RealInnerProductSpace

namespace FunctionalInequalities

universe u

namespace Analysis

/-! ### D. Weighted coarea formula -/

section Coarea

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- **Weighted coarea formula** for a Lipschitz function on a finite-dimensional inner-product
space, with Lebesgue measure on `V` and the normalized surface measure `ℋ^{n-1}` on the level
sets: `∫ g ‖∇u‖ = ∫_ℝ (∫_{u = t} g dℋ^{n-1}) dt`.  The gradient is Mathlib's `gradient`, zero at
the points of non-differentiability (a null set by Rademacher's theorem). -/
theorem lintegral_enorm_gradient_mul_eq_lintegral_levelSet {u : V → ℝ} {K : ℝ≥0}
    (hu : LipschitzWith K u) {g : V → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x, ‖gradient u x‖ₑ * g x ∂(volume : Measure V) =
      ∫⁻ t, ∫⁻ y in {x | u x = t}, g y ∂(KLS.surfaceMeasure V) ∂(volume : Measure ℝ) := by
  sorry

end Coarea

/-! ### E. Sard's theorem for real-valued functions -/

section Sard

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- **Sard's theorem** for real-valued functions: the critical values of a `C^n` function on an
`n`-dimensional space form a Lebesgue-null set.  `C^n` is the sharp regularity for target
dimension one. -/
theorem sard {u : V → ℝ} (hu : ContDiff ℝ (Module.finrank ℝ V) u) :
    (volume : Measure ℝ) (u '' {x | fderiv ℝ u x = 0}) = 0 := by
  sorry

/-- Almost every level is a regular value of a `C^n` function on an `n`-dimensional space. -/
theorem ae_forall_fderiv_ne_zero {u : V → ℝ} (hu : ContDiff ℝ (Module.finrank ℝ V) u) :
    ∀ᵐ t ∂(volume : Measure ℝ), ∀ x, u x = t → fderiv ℝ u x ≠ 0 := by
  rw [ae_iff]
  refine measure_mono_null (fun t ht => ?_) (sard hu)
  by_contra hcon
  exact ht fun x hxt hx0 => hcon ⟨x, hx0, hxt⟩

end Sard

end Analysis

end FunctionalInequalities
