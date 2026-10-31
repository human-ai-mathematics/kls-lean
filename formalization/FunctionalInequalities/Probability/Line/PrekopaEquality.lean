module

public import FunctionalInequalities.Probability.Line.Cdf
public import Mathlib.Analysis.Calculus.Deriv.Inverse
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.Topology.OpenPartialHomeomorph.Basic

/-!
# Equality in the midpoint Prekopa--Leindler inequality on the line

Let `f, g` be continuous, everywhere positive, integrable densities on `ℝ` with the same total
mass, and let `h` be integrable with `√(f x * g y) ≤ h ((x + y) / 2)` for all `x, y`. The
one-dimensional Prekopa--Leindler inequality gives `∫ h ≥ ∫ f`. If equality holds in the weak
form `∫ h ≤ ∫ f`, then `g` is a translate of `f` (`exists_eq_comp_sub_of_midpoint_le`); with equal
first moments the translate is trivial (`eq_of_midpoint_le_of_integral_mul_eq`).

This is the one-dimensional equality input of the uniqueness part of Cordero-Erausquin--Klartag,
*Moment measures*, arXiv:1304.0630, Theorem 2 (restated as Lemma 2.1 of Letwin,
arXiv:2607.24164v1), applied there to the one-dimensional marginals.

The proof is by monotone transport in quantile coordinates. After normalizing the mass to one,
let `Qf, Qg` be the inverse distribution functions on `(0, 1)`, so `Qf' = 1 / f ∘ Qf` and
`Qg' = 1 / g ∘ Qg`. The midpoint map `z = (Qf + Qg) / 2` is injective with
`z' = (Qf' + Qg') / 2`, and by the hypothesis and the arithmetic--geometric mean inequality
`z' * h ∘ z ≥ √(f ∘ Qf * g ∘ Qg) * (Qf' + Qg') / 2 ≥ 1` on `(0, 1)`. The one-dimensional change of
variables gives `∫ h ≥ ∫_{(0,1)} z' * h ∘ z ≥ 1`, so equality forces the arithmetic--geometric
mean inequality to be an equality everywhere on `(0, 1)` (both sides are continuous there), hence
`Qf' = Qg'`, `Qg - Qf` is constant, and `g` is a translate of `f`.

No ledger, certificate, or Blueprint claim is made by this module.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology

namespace FunctionalInequalities.Probability.Line

section Quantile

/-- The quantile function of a continuous everywhere positive probability density: a strictly
increasing map of `(0, 1)` onto `ℝ` with derivative `1 / ρ ∘ Q`. -/
private theorem exists_quantile {ρ : ℝ → ℝ} (hc : Continuous ρ) (hpos : ∀ x, 0 < ρ x)
    (hint : Integrable ρ) (hone : ∫ x, ρ x = 1) :
    ∃ Q : ℝ → ℝ, (∀ p ∈ Ioo (0 : ℝ) 1, HasDerivAt Q (ρ (Q p))⁻¹ p) ∧
      (∀ x, ∃ p ∈ Ioo (0 : ℝ) 1, Q p = x) ∧ StrictMonoOn Q (Ioo (0 : ℝ) 1) := by
  have hnn : ∀ x, 0 ≤ ρ x := fun x ↦ (hpos x).le
  have hprob : IsProbabilityMeasure
      ((volume : Measure ℝ).withDensity fun x ↦ ENNReal.ofReal (ρ x)) := by
    constructor
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ hnn), hone, ENNReal.ofReal_one]
  set μ : ProbabilityMeasure ℝ := ⟨_, hprob⟩ with hμdef
  have hμ : (μ : Measure ℝ) = volume.withDensity fun x ↦ ENNReal.ofReal (ρ x) := rfl
  set F := cdf μ with hF
  have hderiv : ∀ x, HasDerivAt F (ρ x) x :=
    fun x ↦ hasDerivAt_cdf μ hμ hc.measurable hnn hc.continuousAt
  have hmono : StrictMono F :=
    strictMono_of_deriv_pos fun x ↦ by
      rw [(hderiv x).deriv]
      exact hpos x
  have hmem : ∀ x, F x ∈ Ioo (0 : ℝ) 1 := fun x ↦
    ⟨lt_of_le_of_lt (cdf_nonneg _ (x - 1)) (hmono (by linarith : x - 1 < x)),
      lt_of_lt_of_le (hmono (by linarith : x < x + 1)) (cdf_le_one _ (x + 1))⟩
  have hrange : range F = Ioo (0 : ℝ) 1 := by
    ext p
    constructor
    · rintro ⟨x, rfl⟩
      exact hmem x
    · intro hp
      exact exists_cdf_eq μ hμ hc.measurable hnn hp.1 hp.2
  have hemb : IsOpenEmbedding F := by
    refine ⟨hmono.isEmbedding_of_ordConnected ?_, ?_⟩
    · rw [hrange]
      exact ordConnected_Ioo
    · rw [hrange]
      exact isOpen_Ioo
  set e := hemb.toOpenPartialHomeomorph F with he
  have hright : ∀ p ∈ Ioo (0 : ℝ) 1, F (e.symm p) = p := fun p hp ↦
    hemb.toOpenPartialHomeomorph_right_inv F (hrange.symm ▸ hp)
  refine ⟨e.symm, fun p hp ↦ ?_, fun x ↦ ⟨F x, hmem x, ?_⟩, fun p hp q hq hpq ↦ ?_⟩
  · apply e.hasDerivAt_symm
    · simpa only [he, IsOpenEmbedding.toOpenPartialHomeomorph_target, hrange] using hp
    · exact (hpos _).ne'
    · exact hderiv _
  · exact hemb.toOpenPartialHomeomorph_left_inv F
  · rw [← hmono.lt_iff_lt, hright p hp, hright q hq]
    exact hpq

end Quantile

section Equality

/-- The arithmetic--geometric mean defect in the form used below. -/
private theorem sqrt_mul_mul_inv_add_inv {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Real.sqrt (a * b) * ((a⁻¹ + b⁻¹) / 2) =
      1 + (Real.sqrt a - Real.sqrt b) ^ 2 / (2 * (Real.sqrt a * Real.sqrt b)) := by
  obtain ⟨p, hp, rfl⟩ : ∃ p, 0 < p ∧ a = p ^ 2 :=
    ⟨Real.sqrt a, Real.sqrt_pos.mpr ha, (Real.sq_sqrt ha.le).symm⟩
  obtain ⟨q, hq, rfl⟩ : ∃ q, 0 < q ∧ b = q ^ 2 :=
    ⟨Real.sqrt b, Real.sqrt_pos.mpr hb, (Real.sq_sqrt hb.le).symm⟩
  rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hp.le, Real.sqrt_sq hq.le]
  field_simp
  ring

/-- The normalized equality case: `f` and `g` have mass one and `∫ h ≤ 1`. -/
private theorem exists_eq_comp_sub_of_midpoint_le_of_normalized {f g h : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g) (hf0 : ∀ x, 0 < f x) (hg0 : ∀ y, 0 < g y)
    (hfi : Integrable f) (hgi : Integrable g) (hhi : Integrable h) (hf1 : ∫ x, f x = 1)
    (hg1 : ∫ y, g y = 1) (hh1 : ∫ z, h z ≤ 1)
    (hfgh : ∀ x y, Real.sqrt (f x * g y) ≤ h ((x + y) / 2)) : ∃ c : ℝ, ∀ y, g y = f (y - c) := by
  obtain ⟨Qf, hQf, hQfs, hQfm⟩ := exists_quantile hf hf0 hfi hf1
  obtain ⟨Qg, hQg, -, hQgm⟩ := exists_quantile hg hg0 hgi hg1
  set S : Set ℝ := Ioo (0 : ℝ) 1 with hS
  have hSo : IsOpen S := isOpen_Ioo
  set a : ℝ → ℝ := fun p ↦ f (Qf p) with ha
  set b : ℝ → ℝ := fun p ↦ g (Qg p) with hb
  set z : ℝ → ℝ := fun p ↦ (Qf p + Qg p) / 2 with hz
  set z' : ℝ → ℝ := fun p ↦ ((a p)⁻¹ + (b p)⁻¹) / 2 with hz'
  have hapos : ∀ p, 0 < a p := fun p ↦ hf0 _
  have hbpos : ∀ p, 0 < b p := fun p ↦ hg0 _
  have hz'pos : ∀ p, 0 < z' p := fun p ↦ by
    have := hapos p
    have := hbpos p
    positivity
  have hzderiv : ∀ p ∈ S, HasDerivAt z (z' p) p := fun p hp ↦
    ((hQf p hp).add (hQg p hp)).div_const 2
  have hzinj : InjOn z S := by
    refine StrictMonoOn.injOn fun p hp q hq hpq ↦ ?_
    have h1 := hQfm hp hq hpq
    have h2 := hQgm hp hq hpq
    simp only [hz]
    linarith
  have hh0 : ∀ r, 0 ≤ h r := fun r ↦ by
    have := hfgh r r
    rw [add_self_div_two] at this
    exact
      (Real.sqrt_nonneg _).trans
        this
  -- the transported midpoint density

  set φ : ℝ → ℝ := fun p ↦ |z' p| • h (z p) with hφ
  have hcov :=
    integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
      (fun p hp ↦ (hzderiv p hp).hasDerivWithinAt) hzinj h
  have hφi : IntegrableOn φ S :=
    (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioo
          (fun p hp ↦ (hzderiv p hp).hasDerivWithinAt) hzinj h).mp
      hhi.integrableOn
  -- the arithmetic--geometric mean lower bound

  set ψ : ℝ → ℝ := fun p ↦ Real.sqrt (a p * b p) * z' p with hψ
  have hψeq :
    ∀ p,
      ψ p =
        1 +
          (Real.sqrt (a p) - Real.sqrt (b p)) ^ 2 / (2 * (Real.sqrt (a p) * Real.sqrt (b p))) :=
    fun p ↦ sqrt_mul_mul_inv_add_inv (hapos p) (hbpos p)
  have hψ1 : ∀ p, 1 ≤ ψ p := fun p ↦ by
    rw [hψeq]
    have := Real.sqrt_pos.mpr (hapos p)
    have := Real.sqrt_pos.mpr (hbpos p)
    have :
      0 ≤ (Real.sqrt (a p) - Real.sqrt (b p)) ^ 2 / (2 * (Real.sqrt (a p) * Real.sqrt (b p))) := by
      positivity
    linarith
  have hψφ : ∀ p, ψ p ≤ φ p := fun p ↦ by
    simp only [hψ, hφ, smul_eq_mul, abs_of_pos (hz'pos p)]
    rw [mul_comm (z' p)]
    exact
      mul_le_mul_of_nonneg_right (hfgh _ _)
        (hz'pos p).le
  -- integrating: `∫_S (φ - 1) ≤ 0`

  have hvol : (volume : Measure ℝ).real S = 1 := by simp [hS, Real.volume_real_Ioo]
  have hφint : ∫ p in S, φ p ≤ 1 := by
    have : ∫ p in S, φ p = ∫ r in z '' S, h r := by rw [hcov]
    rw [this]
    exact (setIntegral_le_integral hhi (ae_of_all _ hh0)).trans hh1
  have hone_i : IntegrableOn (fun _ : ℝ ↦ (1 : ℝ)) S := by
    refine integrableOn_const ?_ ?_ <;> simp [hS]
  have hdi : IntegrableOn (fun p ↦ φ p - 1) S := hφi.sub hone_i
  have hdnn : 0 ≤ᵐ[volume.restrict S] fun p ↦ φ p - 1 :=
    ae_of_all _ fun p ↦ by
      have := hψ1 p
      have := hψφ p
      simp only [Pi.zero_apply]
      linarith
  have hd0 : ∫ p in S, (φ p - 1) = 0 := by
    refine le_antisymm ?_ (setIntegral_nonneg_of_ae_restrict hdnn)
    rw [integral_sub hφi hone_i, setIntegral_const, smul_eq_mul, hvol, mul_one]
    linarith
  have hdae := (setIntegral_eq_zero_iff_of_nonneg_ae hdnn hdi).mp hd0
  have hψae : ψ =ᵐ[volume.restrict S] fun _ ↦ (1 : ℝ) := by
    filter_upwards [hdae] with p hp
    have := hψ1 p
    have := hψφ p
    simp only [Pi.zero_apply] at hp
    linarith
  -- continuity of `ψ` on `S`

  have hQfc : ContinuousOn Qf S := fun p hp ↦ (hQf p hp).continuousAt.continuousWithinAt
  have hQgc : ContinuousOn Qg S := fun p hp ↦ (hQg p hp).continuousAt.continuousWithinAt
  have hac : ContinuousOn a S := hf.comp_continuousOn hQfc
  have hbc : ContinuousOn b S := hg.comp_continuousOn hQgc
  have hψc : ContinuousOn ψ S := by
    have hz'c : ContinuousOn z' S :=
      (((hac.inv₀ fun p _ ↦ (hapos p).ne').add (hbc.inv₀ fun p _ ↦ (hbpos p).ne')).div_const 2)
    exact ((hac.mul hbc).sqrt).mul hz'c
  have hψS : EqOn ψ (fun _ ↦ 1) S :=
    Measure.eqOn_open_of_ae_eq hψae hSo hψc
      continuousOn_const
  -- equality in the arithmetic--geometric mean inequality

  have hab : ∀ p ∈ S, a p = b p := fun p hp ↦ by
    have h1 := hψS hp
    rw [hψeq] at h1
    have hpa := Real.sqrt_pos.mpr (hapos p)
    have hpb := Real.sqrt_pos.mpr (hbpos p)
    have hfrac :
      (Real.sqrt (a p) - Real.sqrt (b p)) ^ 2 / (2 * (Real.sqrt (a p) * Real.sqrt (b p))) = 0 := by
      simp only at h1
      linarith
    rw [div_eq_zero_iff] at hfrac
    rcases hfrac with hfrac | hfrac
    · have hsq : Real.sqrt (a p) = Real.sqrt (b p) := by
        have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hfrac
        linarith
      rw [← Real.sq_sqrt (hapos p).le, ← Real.sq_sqrt (hbpos p).le, hsq]
    · exfalso
      have : 0 < 2 * (Real.sqrt (a p) * Real.sqrt (b p)) := by positivity
      linarith
  -- `Qg - Qf` is constant on `S`

  have hD : ∀ p ∈ S, HasDerivAt (fun p ↦ Qg p - Qf p) 0 p := fun p hp ↦ by
    have := (hQg p hp).sub (hQf p hp)
    have hb' : b p = a p := (hab p hp).symm
    simp only [hb] at hb'
    rwa [hb', sub_self] at this
  obtain ⟨c, hc⟩ :=
    hSo.exists_is_const_of_deriv_eq_zero isPreconnected_Ioo
      (fun p hp ↦ (hD p hp).differentiableAt.differentiableWithinAt)
      (fun p hp ↦ (hD p hp).deriv)
  refine ⟨c, fun y ↦ ?_⟩
  obtain ⟨p, hp, hpy⟩ := hQfs (y - c)
  have hQgp : Qg p = y := by
    have : Qg p - Qf p = c := hc p hp
    linarith
  have := hab p hp
  simp only [ha, hb, hpy, hQgp] at this
  exact this.symm

/-- **Equality in the midpoint Prekopa--Leindler inequality on the line.** Let `f, g` be
continuous, everywhere positive densities with `f` integrable and `∫ g = ∫ f`, and let `h` be
integrable with `√(f x * g y) ≤ h ((x + y) / 2)` for all `x, y`. If `∫ h ≤ ∫ f` (Prekopa--Leindler
gives the reverse inequality), then `g` is a translate of `f`.

This is the one-dimensional equality step in the uniqueness part of Cordero-Erausquin--Klartag,
*Moment measures*, arXiv:1304.0630, Theorem 2 (Letwin, arXiv:2607.24164v1, Lemma 2.1). -/
theorem exists_eq_comp_sub_of_midpoint_le {f g h : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g) (hf0 : ∀ x, 0 < f x) (hg0 : ∀ y, 0 < g y)
    (hfi : Integrable f) (hhi : Integrable h)
    (hgf : ∫ y, g y = ∫ x, f x) (hhf : ∫ z, h z ≤ ∫ x, f x)
    (hfgh : ∀ x y, Real.sqrt (f x * g y) ≤ h ((x + y) / 2)) :
    ∃ c : ℝ, ∀ y, g y = f (y - c) := by
  set M := ∫ x, f x with hM
  have hMpos : 0 < M := by
    rw [hM, integral_pos_iff_support_of_nonneg (fun x ↦ (hf0 x).le) hfi]
    have : Function.support f = univ := eq_univ_of_forall fun x ↦ (hf0 x).ne'
    rw [this, Real.volume_univ]
    exact ENNReal.zero_lt_top
  have hgi : Integrable g := Integrable.of_integral_ne_zero (by rw [hgf]; exact hMpos.ne')
  obtain ⟨c, hc⟩ := exists_eq_comp_sub_of_midpoint_le_of_normalized (f := fun x ↦ f x / M)
    (g := fun y ↦ g y / M) (h := fun z ↦ h z / M) (hf.div_const M) (hg.div_const M)
    (fun x ↦ div_pos (hf0 x) hMpos) (fun y ↦ div_pos (hg0 y) hMpos) (hfi.div_const M)
    (hgi.div_const M) (hhi.div_const M) (by rw [integral_div, div_self hMpos.ne'])
    (by rw [integral_div, hgf, div_self hMpos.ne'])
    (by rw [integral_div, div_le_one hMpos]; exact hhf)
    (fun x y ↦ by
      rw [div_mul_div_comm, Real.sqrt_div' _ (mul_self_nonneg M), Real.sqrt_mul_self hMpos.le]
      exact div_le_div_of_nonneg_right (hfgh x y) hMpos.le)
  exact ⟨c, fun y ↦ by
    have := hc y
    rwa [div_left_inj' hMpos.ne'] at this⟩

/-- **Equality in the midpoint Prekopa--Leindler inequality, centered form.** Under the
hypotheses of `exists_eq_comp_sub_of_midpoint_le`, if moreover `x ↦ x * f x` is integrable and
`f, g` have the same first moment, then `g = f`. -/
theorem eq_of_midpoint_le_of_integral_mul_eq {f g h : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g) (hf0 : ∀ x, 0 < f x) (hg0 : ∀ y, 0 < g y)
    (hfi : Integrable f) (hhi : Integrable h) (hf1 : Integrable fun x ↦ x * f x)
    (hgf : ∫ y, g y = ∫ x, f x) (hhf : ∫ z, h z ≤ ∫ x, f x)
    (hfgh : ∀ x y, Real.sqrt (f x * g y) ≤ h ((x + y) / 2))
    (hmean : ∫ y, y * g y = ∫ x, x * f x) :
    g = f := by
  obtain ⟨c, hc⟩ := exists_eq_comp_sub_of_midpoint_le hf hg hf0 hg0 hfi hhi hgf hhf hfgh
  have hMpos : 0 < ∫ x, f x := by
    rw [integral_pos_iff_support_of_nonneg (fun x ↦ (hf0 x).le) hfi]
    have : Function.support f = univ := eq_univ_of_forall fun x ↦ (hf0 x).ne'
    rw [this, Real.volume_univ]
    exact ENNReal.zero_lt_top
  have hshift : ∫ y, y * g y = (∫ x, x * f x) + c * ∫ x, f x := by
    have h1 : ∫ y, y * g y = ∫ x, (x + c) * f x := by
      simp_rw [hc]
      have := integral_add_right_eq_self (μ := volume) (fun y ↦ y * f (y - c)) c
      simp only [add_sub_cancel_right] at this
      exact this.symm
    have h2 : (fun x ↦ (x + c) * f x) = fun x ↦ x * f x + c * f x := by
      funext x
      ring
    rw [h1, h2, integral_add hf1 (hfi.const_mul c), integral_const_mul]
  have hc0 : c = 0 := by
    rw [hmean] at hshift
    have : c * ∫ x, f x = 0 := left_eq_add.mp hshift
    exact (mul_eq_zero.mp this).resolve_right hMpos.ne'
  funext y
  rw [hc y, hc0, sub_zero]

end Equality

end FunctionalInequalities.Probability.Line
