import FunctionalInequalities.Analysis.Convex.Legendre
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-!
# Exponential potential measures and the CEK functional

For an extended-real potential `φ`, `density φ = exp(-φ)` in `ℝ≥0∞` (zero where `φ = ⊤`), `weightedMeasure dx φ` is the
measure `exp(-φ) dx` and `mass dx φ = ∫⁻ exp(-φ) dx`; zero and infinite mass are retained and nothing is normalized.
`PotentialIntegrable φ μ` and `variationalFunctional dx μ φ = log ∫ exp(-φ*) dx - ∫ φ dμ` (extended logarithm) are the
objects of Cordero-Erausquin–Klartag, *Moment measures* (arXiv:1304.0630v1), Proposition 12. Elementary properties:
the monotonicity `mass_legendre_mono` used for the truncation (61), and Borel measurability of the conjugate density for
an arbitrary, possibly nonmeasurable primal (`measurable_density_legendre`).

The gradient push-forward (moment measure), the effective domain and essential continuity of CEK Definition 2 and
Theorem 2 are not defined in this module.

Supporting definitions for Cordero-Erausquin–Klartag, Lemma 17.
-/

noncomputable section

namespace FunctionalInequalities.Probability.MomentMeasure

open MeasureTheory
open scoped ENNReal
open FunctionalInequalities.Analysis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The extended exponential handles `+∞` potentials correctly: density zero. -/
def density (φ : E → EReal) (x : E) : ℝ≥0∞ := EReal.exp (-φ x)

section Measurable

variable [MeasurableSpace E]

/-- Integrability in CEK Proposition 12, including a.e. finiteness before using `toReal`. -/
def PotentialIntegrable (φ : E → EReal) (μ : Measure E) : Prop :=
  (∀ x, φ x ≠ ⊥) ∧ (∀ᵐ x ∂μ, φ x ≠ ⊤) ∧
    Integrable (fun x => (φ x).toReal) μ

section Haar

variable [BorelSpace E] [FiniteDimensional ℝ E]

/-- The measure `exp(-φ(x)) dx`, without implicit probability normalization. -/
def weightedMeasure (dx : Measure E) (φ : E → EReal) : Measure E :=
  dx.withDensity (density φ)

/-- `Z(φ)`, retaining both zero and infinite mass rather than totalizing a real logarithm. -/
def mass (dx : Measure E) (φ : E → EReal) : ℝ≥0∞ := ∫⁻ x, density φ x ∂dx

/-- CEK's functional `I_μ(f) = log ∫ exp(-f*) - ∫ f dμ`, with extended logarithm. -/
def variationalFunctional (dx μ : Measure E) (φ : E → EReal) : EReal :=
  ENNReal.log (mass dx (legendre φ)) - (∫ x, (φ x).toReal ∂μ : ℝ)

end Haar

/-- The monotonicity used for the truncation in CEK (61): increasing the primal
potential increases the mass of the exponential of its negative Legendre transform. -/
theorem mass_legendre_mono (dx : Measure E) {φ ψ : E → EReal} (h : ∀ x, φ x ≤ ψ x) :
    mass dx (legendre φ) ≤ mass dx (legendre ψ) := by
  apply lintegral_mono
  intro x
  exact EReal.exp_monotone (EReal.neg_le_neg_iff.mpr (legendre_antitone h x))

end Measurable

/-- The density of the actual conjugate is Borel even for a nonmeasurable primal. -/
theorem measurable_density_legendre [MeasurableSpace E] [BorelSpace E] (φ : E → EReal) :
    Measurable (density (legendre φ)) :=
  EReal.measurable_exp.comp (lowerSemicontinuous_legendre φ).measurable.neg

end FunctionalInequalities.Probability.MomentMeasure
