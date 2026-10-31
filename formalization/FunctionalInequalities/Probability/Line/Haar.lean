module

public import Mathlib.MeasureTheory.Measure.Haar.Disintegration
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Analysis.InnerProductSpace.Orthogonal
public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Fubini splitting of a Haar measure along a line

Read `lineEquiv` and then `exists_lintegral_line`.

For a unit vector `θ` of a finite-dimensional inner product space `E`, the map
`(z, s) ↦ z + s • θ` is a linear equivalence from `θ^⊥ × ℝ` onto `E`. Pushing the product of the
canonical Haar measure of `θ^⊥` with Lebesgue measure through it gives a Haar measure on `E`,
hence a positive finite multiple of any prescribed Haar measure `m`. The resulting identity
`c * ∫ G dm = ∫∫ G (z + s θ)` is the Fubini splitting used by the conditional-fiber
disintegration; the constant `c` depends on `θ` and is never computed.

No ledger, certificate, or Blueprint claim is made by this module.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace FunctionalInequalities.Probability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

/-- The linear map `(z, s) ↦ z + s • θ` from `θ^⊥ × ℝ` to `E`. -/
def lineMap (θ : E) : ((ℝ ∙ θ)ᗮ × ℝ) →ₗ[ℝ] E :=
  ((ℝ ∙ θ)ᗮ).subtype.coprod (LinearMap.toSpanSingleton ℝ E θ)

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
@[simp]
theorem lineMap_apply (θ : E) (p : (ℝ ∙ θ)ᗮ × ℝ) : lineMap θ p = (p.1 : E) + p.2 • θ := rfl

/-- Orthogonal splitting of `E` along a unit vector: `(z, s) ↦ z + s • θ`. -/
def lineEquiv {θ : E} (hθ : ‖θ‖ = 1) : ((ℝ ∙ θ)ᗮ × ℝ) ≃ₗ[ℝ] E := by
  refine LinearEquiv.ofBijective (lineMap θ) ⟨?_, ?_⟩
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨z, s⟩ hp
    rw [lineMap_apply] at hp
    have hzθ : inner ℝ θ (z : E) = 0 := Submodule.mem_orthogonal_singleton_iff_inner_right.1 z.2
    have hθθ : inner ℝ θ θ = (1 : ℝ) := by
      rw [real_inner_self_eq_norm_sq, hθ]
      norm_num
    have hs : s = 0 := by
      have hcong := congrArg (fun x : E ↦ inner ℝ θ x) hp
      have hθ0 : θ ≠ 0 := by
        intro h
        rw [h, norm_zero] at hθ
        norm_num at hθ
      have : s = 0 ∨ θ = 0 := by
        simpa [inner_add_right, real_inner_smul_right, hzθ, hθθ] using hcong
      exact this.resolve_right hθ0
    subst hs
    have hz : (z : E) = 0 := by simpa using hp
    simp [Prod.ext_iff, Submodule.coe_eq_zero.1 hz]
  · intro x
    refine ⟨⟨⟨x - (inner ℝ θ x : ℝ) • θ, ?_⟩, (inner ℝ θ x : ℝ)⟩, ?_⟩
    · rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
      have hθθ : inner ℝ θ θ = (1 : ℝ) := by
        rw [real_inner_self_eq_norm_sq, hθ]
        norm_num
      simp [inner_sub_right, real_inner_smul_right, hθ]
    · simp

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
@[simp]
theorem lineEquiv_apply {θ : E} (hθ : ‖θ‖ = 1) (p : (ℝ ∙ θ)ᗮ × ℝ) :
    lineEquiv hθ p = (p.1 : E) + p.2 • θ := rfl

variable [SecondCountableTopology E]

/-- **Fubini splitting of a Haar measure along a line.** For a unit vector `θ` there is a positive
finite constant `c` such that integrating over `E` against a Haar measure `m` is, after
multiplication by `c`, the iterated integral over `θ^⊥` and the line `ℝ θ`. -/
theorem exists_lintegral_line (m : Measure E) [m.IsAddHaarMeasure] {θ : E} (hθ : ‖θ‖ = 1) :
    ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ G : E → ENNReal, Measurable G →
      c * ∫⁻ x, G x ∂m =
        ∫⁻ z : (ℝ ∙ θ)ᗮ, ∫⁻ s : ℝ, G ((z : E) + s • θ) ∂(volume : Measure ℝ)
          ∂(Measure.addHaar : Measure (ℝ ∙ θ)ᗮ) := by
  set L := (lineEquiv hθ).toContinuousLinearEquiv with hL
  set ν : Measure ((ℝ ∙ θ)ᗮ × ℝ) :=
    (Measure.addHaar : Measure (ℝ ∙ θ)ᗮ).prod (volume : Measure ℝ) with hν
  have hHaar : (ν.map L).IsAddHaarMeasure := L.isAddHaarMeasure_map ν
  refine ⟨(Measure.addHaarScalarFactor (ν.map L) m : ENNReal), ?_, ENNReal.coe_ne_top,
    fun G hG ↦ ?_⟩
  · simpa only [ne_eq, ENNReal.coe_eq_zero] using
      (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure (ν.map L) m).ne'
  have hmap : ν.map L = (Measure.addHaarScalarFactor (ν.map L) m : ENNReal) • m := by
    have h := Measure.isAddLeftInvariant_eq_smul (ν.map L) m
    rwa [ENNReal.smul_def] at h
  have h1 : ∫⁻ x, G x ∂(ν.map L) = ∫⁻ p, G (L p) ∂ν :=
    lintegral_map hG L.continuous.measurable
  rw [hmap, lintegral_smul_measure, smul_eq_mul] at h1
  rw [h1, hν]
  exact lintegral_prod (fun p ↦ G (L p)) (hG.comp L.continuous.measurable).aemeasurable

end FunctionalInequalities.Probability
