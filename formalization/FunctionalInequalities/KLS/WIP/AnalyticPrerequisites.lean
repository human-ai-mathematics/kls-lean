import FunctionalInequalities.Analysis.LevelSet
import FunctionalInequalities.KLS.Geometry.SurfaceMeasure
import Mathlib.Analysis.Calculus.Implicit
import Mathlib.Analysis.Calculus.Gradient.Basic

/-! # Open analytic prerequisites

The sharp `C^(finrank)` Sard theorem is the one remaining direct hole here, and
`Analysis.ae_forall_fderiv_ne_zero` inherits it.

Both halves of the weighted coarea formula have now left this file with byte-identical `pp.all`
signatures.  Its measurability half `Analysis.aemeasurable_lintegral_levelSet` moved to the
hole-free `KLS/Geometry/LevelSetMeasurable.lean`, and its equality half
`Analysis.lintegral_enorm_gradient_mul_eq_lintegral_levelSet` moved to the hole-free
`KLS/Geometry/LipschitzCoarea.lean`, where it is proved from `L12` at `S = Set.univ`.
Gauss–Green and mollification consequences now live in `KLS/Geometry`, without importing this
module. -/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff Pointwise RealInnerProductSpace

namespace FunctionalInequalities

universe u

namespace Analysis

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
