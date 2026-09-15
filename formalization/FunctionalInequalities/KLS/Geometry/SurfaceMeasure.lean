import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# Normalized Hausdorff measures and the surface measure of the relative-perimeter chain

Base definitions layer of the relative-perimeter chain.  Mathlib's `μH[d]` uses the gauge
`diam ^ d`; the classical `d`-dimensional Hausdorff measure uses `ω_d (diam / 2) ^ d`.  This
module fixes `ω_d` (`unitBallVolume`), the rescaled measure `hausdorffNormalized`, and the
codimension-one `surfaceMeasure` used throughout `lem:relative-perimeter-smoothing` and
`lem:relative-perimeter-cheeger-infimum`.

The module carries definitions only, so that the general Hausdorff and level-set geometry of
`Analysis/LevelSet.lean` can be stated in terms of `unitBallVolume` without depending on the
perimeter statements that consume it.  The convention check
`KLS.hausdorffNormalized_finrank_eq_volume` — that the normalized top-dimensional Hausdorff
measure is Lebesgue measure — is proved in `KLS/Geometry/SmoothDomain.lean`, where the
isodiametric input of `Analysis/LevelSet.lean` is available.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace FunctionalInequalities.KLS

universe u

section Normalization

variable (V : Type u) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
  [BorelSpace V] [FiniteDimensional ℝ V]

/-- The volume `ω_d = π^{d/2} / Γ(d/2 + 1)` of the unit ball of `ℝ^d`. -/
def unitBallVolume (d : ℕ) : ℝ := Real.sqrt Real.pi ^ d / Real.Gamma ((d : ℝ) / 2 + 1)

/-- The standard `d`-dimensional Hausdorff measure `(ω_d / 2^d) • μH[d]`: Mathlib's `μH[d]` uses the
gauge `diam ^ d`, the classical definition uses `ω_d (diam / 2)^d`. -/
def hausdorffNormalized (d : ℕ) : Measure V :=
  ENNReal.ofReal (unitBallVolume d / 2 ^ d) • (μH[(d : ℝ)] : Measure V)

/-- The surface measure `ℋ^{n-1}` of the Blueprint, `n = finrank ℝ V`, in the standard
normalization.  For `n = 0` the natural subtraction gives `ℋ^0`, which only meets the empty
frontier of a smooth domain in a one-point space. -/
def surfaceMeasure : Measure V := hausdorffNormalized V (Module.finrank ℝ V - 1)

end Normalization

end FunctionalInequalities.KLS

end
