import FunctionalInequalities.KLS.ConditionalFiber.Basic
import FunctionalInequalities.Probability.Line.Haar
import Mathlib.Probability.Kernel.WithDensity

/-!
# The explicit slice kernel of a law with a Haar density

Read `sliceMass`, `sliceKernel`, then `compProd_baseLaw_sliceKernel` and `ae_sliceKernel_eq`.

For a density `p` of the law `μ` with respect to a Haar measure `m`, the conditional law of the
scalar coordinate given the base point `(θ, z)` is the normalized line density
`t ↦ p (z + t θ) / Z(θ, z)`, where `Z` is the slice mass. This module builds that Markov kernel,
proves that it disintegrates the joint law, and concludes from Mathlib's uniqueness of conditional
kernels that it agrees base-law almost everywhere with the chosen kernel of
`KLS/ConditionalFiber/Basic.lean`.

No ledger, certificate, or Blueprint claim is made by this module.
-/

noncomputable section

open MeasureTheory ProbabilityTheory

namespace FunctionalInequalities.KLS.ConditionalFiber

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- The unnormalized mass of the density `p` along the line through the base point. -/
def sliceMass (p : E → ℝ) (b : Direction E × E) : ENNReal :=
  ∫⁻ t : ℝ, ENNReal.ofReal (p (reconstruct b t))

/-- Base points with positive and finite slice mass. -/
def SliceGood (p : E → ℝ) : Set (Direction E × E) :=
  {b | 0 < sliceMass p b ∧ sliceMass p b < ⊤}

/-- The normalized line density, as a function of the base point and the scalar coordinate. -/
def sliceDensity (p : E → ℝ) (b : Direction E × E) (t : ℝ) : ENNReal :=
  ENNReal.ofReal (p (reconstruct b t)) / sliceMass p b

theorem measurable_sliceMass {p : E → ℝ} (hp : Measurable p) : Measurable (sliceMass p) :=
  Measurable.lintegral_prod_right' (ν := (volume : Measure ℝ))
    (f := fun q : (Direction E × E) × ℝ ↦ ENNReal.ofReal (p (reconstruct q.1 q.2)))
    (hp.comp measurable_reconstruct).ennreal_ofReal

theorem measurableSet_sliceGood {p : E → ℝ} (hp : Measurable p) : MeasurableSet (SliceGood p) :=
  (measurableSet_lt measurable_const (measurable_sliceMass hp)).inter
    (measurableSet_lt (measurable_sliceMass hp) measurable_const)

theorem measurable_sliceDensity {p : E → ℝ} (hp : Measurable p) :
    Measurable (Function.uncurry (sliceDensity p)) :=
  ((hp.comp measurable_reconstruct).ennreal_ofReal).div
    ((measurable_sliceMass hp).comp measurable_fst)

/-- The explicit conditional kernel along lines: on base points with positive finite slice mass it
is the normalized line density against Lebesgue measure, and elsewhere an arbitrary probability
measure. -/
def sliceKernel (p : E → ℝ) (hp : Measurable p) : Kernel (Direction E × E) ℝ := by
  classical
  exact Kernel.piecewise (measurableSet_sliceGood hp)
    (Kernel.withDensity (Kernel.const (Direction E × E) (volume : Measure ℝ)) (sliceDensity p))
    (Kernel.const (Direction E × E) (Measure.dirac 0))

theorem sliceKernel_apply_of_good {p : E → ℝ} (hp : Measurable p) {b : Direction E × E}
    (hb : b ∈ SliceGood p) (A : Set ℝ) :
    sliceKernel p hp b A = ∫⁻ t in A, sliceDensity p b t := by
  classical
  rw [sliceKernel, Kernel.piecewise_apply, if_pos hb,
    Kernel.withDensity_apply' _ (measurable_sliceDensity hp), Kernel.const_apply]

theorem sliceKernel_eq_withDensity_of_good {p : E → ℝ} (hp : Measurable p)
    {b : Direction E × E} (hb : b ∈ SliceGood p) :
    sliceKernel p hp b = (volume : Measure ℝ).withDensity (sliceDensity p b) := by
  classical
  rw [sliceKernel, Kernel.piecewise_apply, if_pos hb,
    Kernel.withDensity_apply _ (measurable_sliceDensity hp), Kernel.const_apply]

theorem sliceKernel_apply_of_not_good {p : E → ℝ} (hp : Measurable p) {b : Direction E × E}
    (hb : b ∉ SliceGood p) : sliceKernel p hp b = Measure.dirac 0 := by
  classical
  rw [sliceKernel, Kernel.piecewise_apply, if_neg hb, Kernel.const_apply]

instance instIsMarkovKernelSliceKernel (p : E → ℝ) (hp : Measurable p) :
    IsMarkovKernel (sliceKernel p hp) := by
  refine ⟨fun b ↦ ?_⟩
  by_cases hb : b ∈ SliceGood p
  · refine ⟨?_⟩
    rw [sliceKernel_apply_of_good hp hb, Measure.restrict_univ]
    simp only [sliceDensity, ENNReal.div_eq_inv_mul]
    rw [lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 hb.1.ne')]
    exact ENNReal.inv_mul_cancel hb.1.ne' hb.2.ne
  · rw [sliceKernel_apply_of_not_good hp hb]
    infer_instance

section Disintegration

variable [FiniteDimensional ℝ E]

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E] in
omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E] in
/-- Along a unit direction, the scalar coordinate of an orthogonal point plus a multiple of the
direction is that multiple. -/
theorem inner_add_smul_orthogonal {θ : Direction E} (z : (ℝ ∙ θ.1)ᗮ) (t : ℝ) :
    inner ℝ ((z : E) + t • θ.1) θ.1 = t := by
  have hzθ : inner ℝ θ.1 (z : E) = (0 : ℝ) :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.1 z.2
  have hθθ : inner ℝ θ.1 θ.1 = (1 : ℝ) := by
    rw [real_inner_self_eq_norm_sq, θ.2]
    norm_num
  rw [inner_add_left, real_inner_smul_left, real_inner_comm θ.1 (z : E), hzθ, hθθ]
  ring

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E] in
/-- Joint coordinates of a point written in the orthogonal splitting along `θ`. -/
theorem coordinates_add_smul_orthogonal {θ : Direction E} (z : (ℝ ∙ θ.1)ᗮ) (t : ℝ) :
    coordinates (θ, (z : E) + t • θ.1) = ((θ, (z : E)), t) := by
  have h := inner_add_smul_orthogonal z t
  simp only [coordinates, h]
  simp

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E] in
/-- The base projection of a point written in the orthogonal splitting along `θ`. -/
theorem baseMap_add_smul_orthogonal {θ : Direction E} (z : (ℝ ∙ θ.1)ᗮ) (t : ℝ) :
    (z : E) + t • θ.1 - inner ℝ ((z : E) + t • θ.1) θ.1 • θ.1 = (z : E) := by
  rw [inner_add_smul_orthogonal]
  abel

omit [FiniteDimensional ℝ E] in
/-- Multiplying the fiber law by the slice mass undoes the normalization; this also covers the
base points with vanishing slice mass. -/
theorem sliceKernel_mul_sliceMass {p : E → ℝ} (hp : Measurable p) {b : Direction E × E}
    (hb : sliceMass p b ≠ ⊤) (A : Set ℝ) :
    sliceKernel p hp b A * sliceMass p b = ∫⁻ t in A, ENNReal.ofReal (p (reconstruct b t)) := by
  by_cases hg : b ∈ SliceGood p
  · rw [sliceKernel_apply_of_good hp hg]
    simp only [sliceDensity, ENNReal.div_eq_inv_mul]
    rw [lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 hg.1.ne'), mul_comm, ← mul_assoc,
      ENNReal.mul_inv_cancel hg.1.ne' hg.2.ne, one_mul]
  · have hz : sliceMass p b = 0 := by
      rcases eq_or_lt_of_le (show (0 : ENNReal) ≤ sliceMass p b from zero_le) with h | h
      · exact h.symm
      · exact absurd ⟨h, lt_of_le_of_ne le_top hb⟩ hg
    have hle : ∫⁻ t in A, ENNReal.ofReal (p (reconstruct b t)) ≤ sliceMass p b :=
      setLIntegral_le_lintegral _ _
    rw [hz] at hle ⊢
    rw [mul_zero]
    exact (le_antisymm hle zero_le).symm

/-- The Fubini splitting of the law `μ` along a fixed unit direction, using a Haar density. -/
theorem exists_lintegral_line_density (μ : ProbabilityMeasure E) (m : Measure E)
    [m.IsAddHaarMeasure] {p : E → ℝ} (hp : Measurable p)
    (hpμ : m.withDensity (fun x ↦ ENNReal.ofReal (p x)) = (μ : Measure E)) (θ : Direction E) :
    ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ F : E → ENNReal, Measurable F →
      c * ∫⁻ x, F x ∂(μ : Measure E) =
        ∫⁻ z : (ℝ ∙ θ.1)ᗮ, ∫⁻ t : ℝ, F ((z : E) + t • θ.1) *
            ENNReal.ofReal (p ((z : E) + t • θ.1)) ∂(volume : Measure ℝ)
          ∂(Measure.addHaar : Measure (ℝ ∙ θ.1)ᗮ) := by
  obtain ⟨c, hc0, hctop, hfub⟩ := Probability.exists_lintegral_line m θ.2
  refine ⟨c, hc0, hctop, fun F hF ↦ ?_⟩
  have hkey := hfub (fun x ↦ F x * ENNReal.ofReal (p x)) (hF.mul hp.ennreal_ofReal)
  rw [← hkey, ← hpμ, lintegral_withDensity_eq_lintegral_mul m hp.ennreal_ofReal hF]
  exact congrArg _ (lintegral_congr fun x ↦ mul_comm _ _)

/-- The slice kernel reproduces the direction section of the joint law. -/
private theorem lintegral_section_eq (μ : ProbabilityMeasure E) (m : Measure E)
    [m.IsAddHaarMeasure] {p : E → ℝ} (hp : Measurable p)
    (hpμ : m.withDensity (fun x ↦ ENNReal.ofReal (p x)) = (μ : Measure E))
    {s : Set ((Direction E × E) × ℝ)} (hs : MeasurableSet s) (θ : Direction E) :
    ∫⁻ z, sliceKernel p hp (θ, z) (Prod.mk ((θ, z) : Direction E × E) ⁻¹' s)
        ∂((μ : Measure E).map (fun x ↦ x - inner ℝ x θ.1 • θ.1)) =
      (μ : Measure E) ((fun x ↦ coordinates (θ, x)) ⁻¹' s) := by
  obtain ⟨c, hc0, hctop, hline⟩ := exists_lintegral_line_density μ m hp hpμ θ
  set P : E → E := fun x ↦ x - inner ℝ x θ.1 • θ.1 with hPdef
  have hPmeas : Measurable P := by rw [hPdef]; fun_prop
  set H : E → ENNReal :=
    fun z ↦ sliceKernel p hp (θ, z) (Prod.mk ((θ, z) : Direction E × E) ⁻¹' s) with hHdef
  have hHmeas : Measurable H :=
    (Kernel.measurable_kernel_prodMk_left (κ := sliceKernel p hp) hs).comp (by fun_prop)
  have hHle : ∀ z, H z ≤ 1 := fun z ↦ prob_le_one
  have hAmeas : ∀ b : Direction E × E, MeasurableSet (Prod.mk b ⁻¹' s) :=
    fun b ↦ measurable_prodMk_left hs
  have hcoord : MeasurableSet ((fun x ↦ coordinates (θ, x)) ⁻¹' s) :=
    (measurable_coordinates.comp (by fun_prop)) hs
  -- almost every slice has finite mass
  have hmassfin : ∀ᵐ z : (ℝ ∙ θ.1)ᗮ ∂(Measure.addHaar : Measure (ℝ ∙ θ.1)ᗮ),
      sliceMass p (θ, (z : E)) ≠ ⊤ := by
    have h1 := hline (fun _ ↦ 1) measurable_const
    simp only [lintegral_const, measure_univ, mul_one, one_mul] at h1
    have h2 : ∫⁻ z : (ℝ ∙ θ.1)ᗮ, sliceMass p (θ, (z : E))
        ∂(Measure.addHaar : Measure (ℝ ∙ θ.1)ᗮ) = c := by
      rw [h1]
      rfl
    have hmeas : Measurable fun z : (ℝ ∙ θ.1)ᗮ ↦ sliceMass p (θ, (z : E)) :=
      (measurable_sliceMass hp).comp (by fun_prop)
    exact (ae_lt_top hmeas (by rw [h2]; exact hctop)).mono fun z hz ↦ hz.ne
  -- both sides, after multiplication by `c`, are the same iterated integral
  have hL : c * ∫⁻ z, H z ∂((μ : Measure E).map P) =
      ∫⁻ z : (ℝ ∙ θ.1)ᗮ, H (z : E) * sliceMass p (θ, (z : E))
        ∂(Measure.addHaar : Measure (ℝ ∙ θ.1)ᗮ) := by
    rw [lintegral_map hHmeas hPmeas, hline (fun x ↦ H (P x)) (hHmeas.comp hPmeas)]
    refine lintegral_congr fun z ↦ ?_
    have hPz : ∀ t : ℝ, P ((z : E) + t • θ.1) = (z : E) := fun t ↦
      baseMap_add_smul_orthogonal z t
    simp only [hPz]
    rw [lintegral_const_mul' _ _ (ne_top_of_le_ne_top ENNReal.one_ne_top (hHle _))]
    rfl
  have hR : c * (μ : Measure E) ((fun x ↦ coordinates (θ, x)) ⁻¹' s) =
      ∫⁻ z : (ℝ ∙ θ.1)ᗮ, (∫⁻ t in Prod.mk ((θ, (z : E)) : Direction E × E) ⁻¹' s,
          ENNReal.ofReal (p (reconstruct (θ, (z : E)) t)) ∂(volume : Measure ℝ))
        ∂(Measure.addHaar : Measure (ℝ ∙ θ.1)ᗮ) := by
    rw [← lintegral_indicator_one hcoord,
      hline _ ((measurable_one.indicator hcoord))]
    refine lintegral_congr fun z ↦ ?_
    rw [← lintegral_indicator (hAmeas (θ, (z : E)))]
    refine lintegral_congr fun t ↦ ?_
    have hmem : ((z : E) + t • θ.1 ∈ (fun x ↦ coordinates (θ, x)) ⁻¹' s) ↔
        (t ∈ Prod.mk ((θ, (z : E)) : Direction E × E) ⁻¹' s) := by
      simp only [Set.mem_preimage, coordinates_add_smul_orthogonal z t]
    by_cases ht : t ∈ Prod.mk ((θ, (z : E)) : Direction E × E) ⁻¹' s
    · rw [Set.indicator_of_mem (hmem.2 ht), Set.indicator_of_mem ht]
      simp [reconstruct]
    · rw [Set.indicator_of_notMem (fun hc ↦ ht (hmem.1 hc)), Set.indicator_of_notMem ht]
      simp
  have heq : c * ∫⁻ z, H z ∂((μ : Measure E).map P) =
      c * (μ : Measure E) ((fun x ↦ coordinates (θ, x)) ⁻¹' s) := by
    rw [hL, hR]
    refine lintegral_congr_ae (hmassfin.mono fun z hz ↦ ?_)
    exact sliceKernel_mul_sliceMass hp hz _
  exact (ENNReal.mul_right_inj hc0 hctop).1 heq

/-- **The slice kernel disintegrates the joint law.** -/
theorem compProd_baseLaw_sliceKernel (μ : ProbabilityMeasure E)
    (ρ : ProbabilityMeasure (Direction E)) (m : Measure E) [m.IsAddHaarMeasure] {p : E → ℝ}
    (hp : Measurable p) (hpμ : m.withDensity (fun x ↦ ENNReal.ofReal (p x)) = (μ : Measure E)) :
    baseLaw μ ρ ⊗ₘ sliceKernel p hp = jointLaw μ ρ := by
  refine Measure.ext fun s hs ↦ ?_
  rw [Measure.compProd_apply hs]
  rw [lintegral_baseLaw μ ρ _ (Kernel.measurable_kernel_prodMk_left (κ := sliceKernel p hp) hs)]
  rw [jointLaw, Measure.map_apply measurable_coordinates hs,
    Measure.prod_apply (measurable_coordinates hs)]
  exact lintegral_congr fun θ ↦ lintegral_section_eq μ m hp hpμ hs θ

/-- The slice kernel agrees with the chosen conditional kernel base-law almost everywhere. -/
theorem ae_sliceKernel_eq (μ : ProbabilityMeasure E) (ρ : ProbabilityMeasure (Direction E))
    (m : Measure E) [m.IsAddHaarMeasure] {p : E → ℝ} (hp : Measurable p)
    (hpμ : m.withDensity (fun x ↦ ENNReal.ofReal (p x)) = (μ : Measure E)) :
    ∀ᵐ b ∂baseLaw μ ρ, sliceKernel p hp b = kernel μ ρ b :=
  ProbabilityTheory.eq_condKernel_of_measure_eq_compProd (sliceKernel p hp)
    (compProd_baseLaw_sliceKernel μ ρ m hp hpμ).symm

end Disintegration

end FunctionalInequalities.KLS.ConditionalFiber
