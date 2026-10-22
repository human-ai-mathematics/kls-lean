import FunctionalInequalities.Analysis.MeasureGrowth
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Radial potentials of measures with ball growth

For measures on a normed space with power ball growth: the radial potential `∫ ‖y - x‖^{-a} dν(y)` of a measure supported
within distance `D` is at most `K d/(d - a) D^{d - a}` (`0 < a < d`, mass derived from the support), and the critical
two-measure moment `∫ (∫ ‖y - x‖^{N(μ-1)} dν)^q dη ≤ A/(1-μ) [((1-μ)/μ) K q]^q D^N` for `0 < μ ≤ 1/2`, `q ≥ 2` and common
bounded support, by a layer-cake tail bound, Hölder interpolation of radial kernels and Tonelli. These are the potential
estimates of Gilbarg–Trudinger (2001), Lemmas 7.18 and 7.20 (proof), in the measure form; the real power kernel is `0` at
the diagonal. Lebesgue densities are treated in `RieszPotential/Critical`.
`lintegral_riesz_potential_le_diameter_mul_lintegral` bounds the `L¹` norm of the critical Riesz potential of an `L¹`
density on a set of diameter at most `D` by `ω_n n D ‖f‖₁` (`n ≥ 2`).
-/

noncomputable section

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology

namespace FunctionalInequalities.Analysis

/-- Layer-cake tail bound `∫ f ≤ B0 T + B1 T^{1-s}/(s-1)` from the mass and the tail `B1 t^{-s}`. -/
private theorem lintegral_le_of_mass_and_rpow_tail
    {X : Type*} [MeasurableSpace X] (μ : Measure X) {f : X → ℝ}
    (hf : AEMeasurable f μ) (hf0 : ∀ᵐ x ∂μ, 0 ≤ f x)
    {B0 B1 s T : ℝ} (hB0 : 0 ≤ B0) (hB1 : 0 ≤ B1) (hs : 1 < s) (hT : 0 < T)
    (hmass : μ univ ≤ ENNReal.ofReal B0)
    (htail : ∀ t : ℝ, 0 < t → μ {x | t < f x} ≤ ENNReal.ofReal (B1 * t ^ (-s))) :
    (∫⁻ x, ENNReal.ofReal (f x) ∂μ) ≤
      ENNReal.ofReal (B0 * T + B1 * T ^ (1 - s) / (s - 1)) := by
  have hsplit : Ioi (0 : ℝ) = Ioc (0 : ℝ) T ∪ Ioi T := by
    ext t
    change 0 < t ↔ (0 < t ∧ t ≤ T) ∨ T < t
    constructor
    · intro ht
      by_cases h : t ≤ T
      · exact Or.inl ⟨ht,h⟩
      · exact Or.inr (lt_of_not_ge h)
    · rintro (⟨ht,-⟩ | ht)
      · exact ht
      · exact hT.trans ht
  have hdisj : Disjoint (Ioc (0 : ℝ) T) (Ioi T) :=
    Set.disjoint_left.mpr fun _ hx hy => (not_lt_of_ge hx.2) hy
  have hconst : (∫⁻ t in Ioc (0 : ℝ) T, ENNReal.ofReal B0) = ENNReal.ofReal (B0 * T) := by
    rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero,
      ← ENNReal.ofReal_mul hB0]
  have hp : IntegrableOn (fun t : ℝ => B1 * t ^ (-s)) (Ioi T) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : -s < -1) hT).const_mul B1
  have hpn : ∀ᵐ t ∂(volume.restrict (Ioi T)), 0 ≤ B1 * t ^ (-s) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg hB1 (Real.rpow_nonneg (hT.trans ht).le _)
  have hpower : (∫⁻ t in Ioi T, ENNReal.ofReal (B1 * t ^ (-s))) =
      ENNReal.ofReal (B1 * T ^ (1 - s) / (s - 1)) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hp hpn, integral_const_mul,
      integral_Ioi_rpow_of_lt (by linarith : -s < -1) hT]
    congr 1
    have he : -s + 1 = -(s - 1) := by ring
    have he' : 1 - s = -(s - 1) := by ring
    rw [he, he', neg_div_neg_eq]
    ring
  calc
    _ = (∫⁻ t in Ioc (0 : ℝ) T, μ {x | t < f x}) +
        ∫⁻ t in Ioi T, μ {x | t < f x} := by
      rw [lintegral_eq_lintegral_meas_lt μ hf0 hf, hsplit,
        lintegral_union measurableSet_Ioi hdisj]
    _ ≤ (∫⁻ t in Ioc (0 : ℝ) T, ENNReal.ofReal B0) +
        ∫⁻ t in Ioi T, ENNReal.ofReal (B1 * t ^ (-s)) := by
      apply add_le_add
      · apply lintegral_mono_ae
        filter_upwards with t
        exact (measure_mono (Set.subset_univ _)).trans hmass
      · apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact htail t (hT.trans ht)
    _ = _ := by
      rw [hconst,hpower, ← ENNReal.ofReal_add (by positivity) (by positivity)]

section MeasurableSpace

variable {E : Type*}
variable [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]

/-- Radial potential bound from ball growth and a total-mass bound. -/
private theorem lintegral_norm_sub_rpow_neg_le_of_ball_growth
    (ν : Measure E) (x : E) {K D a d : ℝ} (hK : 0 ≤ K) (hD : 0 < D)
    (ha : 0 < a) (had : a < d)
    (hmass : ν univ ≤ ENNReal.ofReal (K * D ^ d))
    (hgrowth : ∀ r : ℝ, 0 < r → ν (ball x r) ≤ ENNReal.ofReal (K * r ^ d)) :
    (∫⁻ y, ENNReal.ofReal (‖y - x‖ ^ (-a)) ∂ν) ≤
      ENNReal.ofReal (K * d / (d - a) * D ^ (d - a)) := by
  have hs : 1 < d / a := (lt_div_iff₀ ha).mpr (by simpa only [one_mul] using had)
  have hf : AEMeasurable (fun y : E => ‖y - x‖ ^ (-a)) ν :=
    ((continuous_id.sub continuous_const).norm.measurable.pow_const (-a)).aemeasurable
  have hf0 : ∀ᵐ y ∂ν, 0 ≤ ‖y - x‖ ^ (-a) :=
    ae_of_all _ fun _ => Real.rpow_nonneg (norm_nonneg _) _
  have ht : ∀ t : ℝ, 0 < t →
      ν {y : E | t < ‖y - x‖ ^ (-a)} ≤ ENNReal.ofReal (K * t ^ (-(d / a))) := by
    intro t ht
    let r := t ^ ((-a)⁻¹)
    have hr : 0 < r := Real.rpow_pos_of_pos ht _
    have hset : {y : E | t < ‖y - x‖ ^ (-a)} ⊆ ball x r := by
      intro y hy
      change t < ‖y - x‖ ^ (-a) at hy
      have hn : 0 < ‖y - x‖ := by
        by_contra h
        have hz : ‖y - x‖ = 0 := le_antisymm (not_lt.mp h) (norm_nonneg _)
        rw [hz, Real.zero_rpow (by linarith : -a ≠ 0)] at hy
        linarith
      rw [mem_ball, dist_eq_norm]
      exact (Real.lt_rpow_inv_iff_of_neg hn ht (by linarith : -a < 0)).mpr hy
    have he : (-a)⁻¹ * d = -(d / a) := by rw [inv_neg, div_eq_mul_inv]; ring
    have hg := hgrowth r hr
    dsimp only [r] at hg
    rw [← Real.rpow_mul ht.le, he] at hg
    exact (measure_mono hset).trans hg
  have h := lintegral_le_of_mass_and_rpow_tail ν hf hf0
    (mul_nonneg hK (Real.rpow_nonneg hD.le _)) hK hs
    (Real.rpow_pos_of_pos hD (-a)) hmass ht
  have hp : (D ^ (-a)) ^ (1 - d / a) = D ^ (d - a) := by
    rw [← Real.rpow_mul hD.le]
    congr 1
    field_simp [ha.ne']
    ring
  have hprod : D ^ d * D ^ (-a) = D ^ (d - a) := by
    rw [← Real.rpow_add hD]
    congr 1
  have he : (K * D ^ d) * D ^ (-a) + K * (D ^ (-a)) ^ (1 - d / a) / (d / a - 1) =
      K * d / (d - a) * D ^ (d - a) := by
    rw [hp, mul_assoc, hprod]
    have hden : d / a - 1 = (d - a) / a := by field_simp [ha.ne']
    rw [hden]
    field_simp [(sub_pos.mpr had).ne', ha.ne']
    ring
  simpa only [he] using h

/-- **Subcritical radial potential.** For `ν` a.e. supported in `closedBall x D`, `D > 0`, with `ν(B(x,r)) ≤ K r^d`, and
`0 < a < d`: `∫ ‖y - x‖^{-a} dν(y) ≤ K d/(d - a) D^{d - a}`. -/
theorem lintegral_norm_sub_rpow_neg_le_of_ae_closedBall_ball_growth
    (ν : Measure E) (x : E) {K D a d : ℝ} (hK : 0 ≤ K) (hD : 0 < D)
    (ha : 0 < a) (had : a < d)
    (hsupport : ∀ᵐ y ∂ν, y ∈ closedBall x D)
    (hgrowth : ∀ r : ℝ, 0 < r → ν (ball x r) ≤ ENNReal.ofReal (K * r ^ d)) :
    (∫⁻ y, ENNReal.ofReal (‖y - x‖ ^ (-a)) ∂ν) ≤
      ENNReal.ofReal (K * d / (d - a) * D ^ (d - a)) :=
  lintegral_norm_sub_rpow_neg_le_of_ball_growth ν x hK hD ha had
    (measure_univ_le_of_ae_closedBall_ball_growth ν x hD hsupport hgrowth) hgrowth

/-- Hölder interpolation of radial kernels (the diagonal included). -/
private theorem lintegral_norm_sub_rpow_neg_interpolation
    (ν : Measure E) (x : E) {b c t : ℝ} (hb : 0 < b) (hc : 0 < c)
    (ht : 0 < t) (ht1 : t < 1) :
    (∫⁻ y, ENNReal.ofReal (‖y - x‖ ^ (-(b * t + c * (1 - t)))) ∂ν) ≤
      (∫⁻ y, ENNReal.ofReal (‖y - x‖ ^ (-b)) ∂ν) ^ t *
      (∫⁻ y, ENNReal.ofReal (‖y - x‖ ^ (-c)) ∂ν) ^ (1 - t) := by
  have hm (v : ℝ) : AEMeasurable (fun y : E => ENNReal.ofReal (‖y - x‖ ^ v)) ν :=
    ENNReal.continuous_ofReal.measurable.comp
      ((continuous_id.sub continuous_const).norm.measurable.pow_const v) |>.aemeasurable
  have he (y : E) : ENNReal.ofReal (‖y - x‖ ^ (-(b * t + c * (1 - t)))) =
      ENNReal.ofReal (‖y - x‖ ^ (-b)) ^ t *
        ENNReal.ofReal (‖y - x‖ ^ (-c)) ^ (1 - t) := by
    by_cases h : ‖y - x‖ = 0
    · have hv : 0 < b * t + c * (1 - t) := by positivity
      simp only [h, Real.zero_rpow (neg_ne_zero.mpr hv.ne'),
        Real.zero_rpow (neg_ne_zero.mpr hb.ne'), Real.zero_rpow (neg_ne_zero.mpr hc.ne'),
        ENNReal.ofReal_zero, ENNReal.zero_rpow_of_pos ht,
        ENNReal.zero_rpow_of_pos (sub_pos.mpr ht1), zero_mul]
    · have hp : 0 < ‖y - x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h)
      rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _) ht.le,
        ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (by linarith)]
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _)]
      congr 1
      rw [← Real.rpow_mul hp.le, ← Real.rpow_mul hp.le, ← Real.rpow_add hp]
      congr 1
      ring
  simp_rw [he]
  exact ENNReal.lintegral_mul_norm_pow_le (hm (-b)) (hm (-c)) ht.le (by linarith) (by ring)

/-- The powered Hölder interpolation, `q > 1`. -/
private theorem lintegral_norm_sub_rpow_neg_pow_le
    (ν : Measure E) (x : E) {b c q : ℝ} (hb : 0 < b) (hc : 0 < c)
    (hq : 1 < q) :
    (∫⁻ y, ENNReal.ofReal (‖y - x‖ ^ (-(b / q + c * (1 - 1 / q)))) ∂ν) ^ q ≤
      (∫⁻ y, ENNReal.ofReal (‖y - x‖ ^ (-b)) ∂ν) *
      (∫⁻ y, ENNReal.ofReal (‖y - x‖ ^ (-c)) ∂ν) ^ (q - 1) := by
  have hq0 : 0 < q := by linarith
  have h := lintegral_norm_sub_rpow_neg_interpolation ν x hb hc
    (one_div_pos.mpr hq0) ((div_lt_one hq0).mpr hq)
  rw [← div_eq_mul_one_div] at h
  have hp := ENNReal.rpow_le_rpow h hq0.le
  rw [ENNReal.mul_rpow_of_nonneg _ _ hq0.le, ← ENNReal.rpow_mul,
    ← ENNReal.rpow_mul] at hp
  have he : (1 / q) * q = 1 := by field_simp [hq0.ne']
  have he' : (1 - 1 / q) * q = q - 1 := by field_simp [hq0.ne']
  simpa only [he, he', ENNReal.rpow_one] using hp

section StructuredSpace

variable [SecondCountableTopology E]

/-- Two-measure radial moments from ball growth and common bounded support (finiteness derived). -/
private theorem lintegral_radial_potential_rpow_le_of_two_ball_growth
    (ν η : Measure E) {S : Set E} (hS : S.Nonempty)
    {D K A d N b c q : ℝ} (hD : 0 < D) (hK : 0 ≤ K) (hA : 0 ≤ A)
    (hb : 0 < b) (hbN : b < N) (hc : 0 < c) (hcd : c < d) (hq : 1 < q)
    (hdiam : ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ D)
    (hνS : ∀ᵐ y ∂ν, y ∈ S) (hηS : ∀ᵐ y ∂η, y ∈ S)
    (hνgrowth : ∀ x : E, ∀ r : ℝ, 0 < r →
      ν (ball x r) ≤ ENNReal.ofReal (K * r ^ d))
    (hηgrowth : ∀ x : E, ∀ r : ℝ, 0 < r →
      η (ball x r) ≤ ENNReal.ofReal (A * r ^ N)) :
    (∫⁻ x, (∫⁻ y, ENNReal.ofReal (‖y - x‖ ^ (-(b / q + c * (1 - 1 / q)))) ∂ν) ^ q ∂η) ≤
      ENNReal.ofReal ((A * N / (N - b) * D ^ (N - b)) * (K * D ^ d) *
        (K * d / (d - c) * D ^ (d - c)) ^ (q - 1)) := by
  have hνsupp (x : E) (hx : x ∈ S) : ∀ᵐ y ∂ν, y ∈ closedBall x D :=
    hνS.mono fun y hy => hdiam y hy x hx
  have hηsupp (x : E) (hx : x ∈ S) : ∀ᵐ y ∂η, y ∈ closedBall x D :=
    hηS.mono fun y hy => hdiam y hy x hx
  obtain ⟨x0, hx0⟩ := hS
  have hνmass := measure_univ_le_of_ae_closedBall_ball_growth ν x0 hD (hνsupp x0 hx0)
    (hνgrowth x0)
  have hηmass := measure_univ_le_of_ae_closedBall_ball_growth η x0 hD (hηsupp x0 hx0)
    (hηgrowth x0)
  let : IsFiniteMeasure ν := ⟨hνmass.trans_lt ENNReal.ofReal_lt_top⟩
  let : IsFiniteMeasure η := ⟨hηmass.trans_lt ENNReal.ofReal_lt_top⟩
  have hd : 0 < d := hc.trans hcd
  have hN : 0 < N := hb.trans hbN
  have hdc : 0 < d - c := sub_pos.mpr hcd
  have hNb : 0 < N - b := sub_pos.mpr hbN
  let C := K * d / (d - c) * D ^ (d - c)
  let B := A * N / (N - b) * D ^ (N - b)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hνpot (x : E) (hx : x ∈ S) :
      (∫⁻ y, ENNReal.ofReal (‖y - x‖ ^ (-c)) ∂ν) ≤ ENNReal.ofReal C :=
    lintegral_norm_sub_rpow_neg_le_of_ae_closedBall_ball_growth ν x hK hD hc hcd
      (hνsupp x hx) (hνgrowth x)
  have hηpot (y : E) (hy : y ∈ S) :
      (∫⁻ x, ENNReal.ofReal (‖x - y‖ ^ (-b)) ∂η) ≤ ENNReal.ofReal B :=
    lintegral_norm_sub_rpow_neg_le_of_ae_closedBall_ball_growth η y hA hD hb hbN
      (hηsupp y hy) (hηgrowth y)
  have hm : Measurable (fun z : E × E => ENNReal.ofReal (‖z.2 - z.1‖ ^ (-b))) :=
    ENNReal.continuous_ofReal.measurable.comp
      ((measurable_snd.sub measurable_fst).norm.pow_const (-b))
  have hL : (∫⁻ x, ∫⁻ y, ENNReal.ofReal (‖y - x‖ ^ (-b)) ∂ν ∂η) ≤
      ENNReal.ofReal B * ENNReal.ofReal (K * D ^ d) := by
    rw [lintegral_lintegral_swap hm.aemeasurable]
    calc
      _ ≤ ∫⁻ y, ENNReal.ofReal B ∂ν := by
        refine lintegral_mono_ae (hνS.mono fun y hy => ?_)
        simpa only [norm_sub_rev] using hηpot y hy
      _ = ENNReal.ofReal B * ν univ := by simp only [lintegral_const]
      _ ≤ _ := mul_le_mul le_rfl hνmass zero_le zero_le
  calc
    _ ≤ ∫⁻ x, (∫⁻ y, ENNReal.ofReal (‖y - x‖ ^ (-b)) ∂ν) *
        ENNReal.ofReal C ^ (q - 1) ∂η := by
      refine lintegral_mono_ae (hηS.mono fun x hx => ?_)
      exact (lintegral_norm_sub_rpow_neg_pow_le ν x hb hc hq).trans
        (mul_le_mul le_rfl (ENNReal.rpow_le_rpow (hνpot x hx) (by linarith : 0 ≤ q - 1))
          zero_le zero_le)
    _ = (∫⁻ x, ∫⁻ y, ENNReal.ofReal (‖y - x‖ ^ (-b)) ∂ν ∂η) *
        ENNReal.ofReal C ^ (q - 1) := by
      rw [lintegral_mul_const _ hm.lintegral_prod_right]
    _ ≤ (ENNReal.ofReal B * ENNReal.ofReal (K * D ^ d)) *
        ENNReal.ofReal C ^ (q - 1) := mul_le_mul hL le_rfl zero_le zero_le
    _ = _ := by
      rw [ENNReal.ofReal_rpow_of_nonneg hC (by linarith),
        ← ENNReal.ofReal_mul hB, ← ENNReal.ofReal_mul (mul_nonneg hB (by positivity))]

/-- **Critical radial moments.** For measures `ν, η` with all-center growth `ν(B(x,r)) ≤ K r^{N(1-μ)}`,
`η(B(x,r)) ≤ A r^N`, a.e. supported in a nonempty `S` of diameter at most `D > 0`, `0 < μ ≤ 1/2` and `q ≥ 2`:
`∫ (∫ ‖y - x‖^{N(μ-1)} dν(y))^q dη(x) ≤ A/(1-μ) [((1-μ)/μ) K q]^q D^N`. -/
theorem lintegral_critical_radial_potential_rpow_le
    (ν η : Measure E) {S : Set E} (hS : S.Nonempty)
    {D K A N μ q : ℝ} (hD : 0 < D) (hK : 0 ≤ K) (hA : 0 ≤ A)
    (hN : 0 < N) (hμ : 0 < μ) (hμ2 : μ ≤ 1 / 2) (hq : 2 ≤ q)
    (hdiam : ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ D)
    (hνS : ∀ᵐ y ∂ν, y ∈ S) (hηS : ∀ᵐ y ∂η, y ∈ S)
    (hνgrowth : ∀ x : E, ∀ r : ℝ, 0 < r →
      ν (ball x r) ≤ ENNReal.ofReal (K * r ^ (N * (1 - μ))))
    (hηgrowth : ∀ x : E, ∀ r : ℝ, 0 < r →
      η (ball x r) ≤ ENNReal.ofReal (A * r ^ N)) :
    (∫⁻ x, (∫⁻ y, ENNReal.ofReal (‖y - x‖ ^ (N * (μ - 1))) ∂ν) ^ q ∂η) ≤
      ENNReal.ofReal (A / (1 - μ) * ((1 - μ) / μ * K * q) ^ q * D ^ N) := by
  have hq0 : 0 < q := by linarith
  have hq1 : 1 < q := by linarith
  have hμ1 : 0 < 1 - μ := by linarith
  have hμq : 0 < μ / q := div_pos hμ hq0
  have hμq2 : μ / q ≤ μ / 2 :=
    div_le_div_of_nonneg_left hμ.le (by norm_num) hq
  let b := N * (1 - μ / q)
  let c := N * (1 - μ - μ / q)
  let d := N * (1 - μ)
  let e := N * μ / q
  have hb : 0 < b := by dsimp only [b]; apply mul_pos hN; linarith
  have hc : 0 < c := by dsimp only [c]; apply mul_pos hN; linarith
  have hbN : b < N := by dsimp only [b]; nlinarith
  have hcd : c < d := by dsimp only [c, d]; nlinarith
  have he : 0 < e := by dsimp only [e]; positivity
  have hbc : -(b / q + c * (1 - 1 / q)) = N * (μ - 1) := by
    dsimp only [b, c]
    field_simp [hq0.ne']
    ring
  have hdce : d - c = e := by dsimp only [d, c, e]; ring
  have hNbe : N - b = e := by dsimp only [b, e]; ring
  have h := lintegral_radial_potential_rpow_le_of_two_ball_growth ν η hS hD hK hA
    hb hbN hc hcd hq1 hdiam hνS hηS hνgrowth hηgrowth
  rw [hbc, hdce, hNbe] at h
  have hfactor : (A * N / e * D ^ e) * (K * D ^ d) *
      (K * d / e * D ^ e) ^ (q - 1) =
      A / (1 - μ) * ((1 - μ) / μ * K * q) ^ q * D ^ N := by
    let X := (1 - μ) / μ * K * q
    have hX : 0 ≤ X := by dsimp only [X]; positivity
    have hcX : K * d / e = X := by
      dsimp only [d, e, X]
      field_simp [hN.ne', hμ.ne', hq0.ne']
    have hAX : (A * N / e) * K = A / (1 - μ) * X := by
      dsimp only [e, X]
      field_simp [hN.ne', hμ.ne', hq0.ne', hμ1.ne']
    rw [hcX, Real.mul_rpow hX (Real.rpow_nonneg hD.le _), ← Real.rpow_mul hD.le]
    have hDpow : D ^ e * D ^ d * D ^ (e * (q - 1)) = D ^ N := by
      rw [← Real.rpow_add hD, ← Real.rpow_add hD]
      congr 1
      dsimp only [e, d]
      field_simp [hq0.ne']
      ring
    have hXpow : X * X ^ (q - 1) = X ^ q := by
      rcases eq_or_lt_of_le hX with hz | hp
      · rw [← hz, Real.zero_rpow hq0.ne', Real.zero_rpow (by linarith : q - 1 ≠ 0), zero_mul]
      · nth_rw 1 [← Real.rpow_one X]
        rw [← Real.rpow_add hp]
        congr 1
        ring
    calc
      _ = ((A * N / e) * K) * X ^ (q - 1) *
          (D ^ e * D ^ d * D ^ (e * (q - 1))) := by ring
      _ = (A / (1 - μ)) * (X * X ^ (q - 1)) * D ^ N := by rw [hAX, hDpow]; ring
      _ = _ := by rw [hXpow]
  simpa only [hfactor] using h

end StructuredSpace

end MeasurableSpace

/-- **`L¹` control of the Riesz potential** (`n ≥ 2`): on a set of diameter at most `D`, for `f ∈ L¹`, the potential
`P(x) = ∫ |y − x|^{1−n} |f y| dy` is a.e. measurable and finite a.e., and `∫ P ≤ ω_n n D ∫ |f|`. -/
theorem lintegral_riesz_potential_le_diameter_mul_lintegral
    {n : ℕ} (hn : 2 ≤ n) {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (hΩm : MeasurableSet Ω) (hΩne : Ω.Nonempty) {D : ℝ} (hD : 0 < D)
    (hdiam : ∀ y ∈ Ω, ∀ z ∈ Ω, dist y z ≤ D)
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : Integrable f ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict Ω)) :
    let P := fun x => ∫⁻ y in Ω,
      ENNReal.ofReal (‖y - x‖ ^ (1 - (n : ℝ)) * |f y|)
    AEMeasurable P ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict Ω) ∧
      (∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict Ω), P x < ∞) ∧
      (∫⁻ x in Ω, P x) ≤
        ENNReal.ofReal (((volume : Measure (EuclideanSpace ℝ (Fin n))).real (ball 0 1) *
          (n : ℝ) * D * (∫ y in Ω, |f y|))) := by
  intro P
  let μ := (volume : Measure (EuclideanSpace ℝ (Fin n))).restrict Ω
  let ω := (volume : Measure (EuclideanSpace ℝ (Fin n))).real (ball 0 1)
  have hω : 0 ≤ ω := measureReal_nonneg
  have hV : (volume : Measure (EuclideanSpace ℝ (Fin n))) (ball 0 1) ≠ ∞ := measure_ball_lt_top.ne
  have hgrowth (x : EuclideanSpace ℝ (Fin n)) (r : ℝ) (hr : 0 < r) :
      μ (ball x r) ≤ ENNReal.ofReal (ω * r ^ (n : ℝ)) := by
    calc
      _ ≤ (volume : Measure (EuclideanSpace ℝ (Fin n))) (ball x r) := Measure.restrict_le_self _
      _ = ENNReal.ofReal (r ^ n) * (volume : Measure (EuclideanSpace ℝ (Fin n))) (ball 0 1) := by
        simpa only [finrank_euclideanSpace_fin] using
          Measure.addHaar_ball_of_pos (volume : Measure (EuclideanSpace ℝ (Fin n))) x hr
      _ = _ := by
        rw [Real.rpow_natCast,ENNReal.ofReal_mul hω]
        dsimp only [ω,measureReal_def]
        rw [ENNReal.ofReal_toReal hV,mul_comm]
  obtain ⟨x0,hx0⟩ := hΩne
  have hsupp : ∀ᵐ y ∂μ, y ∈ closedBall x0 D :=
    (ae_restrict_mem hΩm).mono fun y hy => hdiam y hy x0 hx0
  have hmass := measure_univ_le_of_ae_closedBall_ball_growth μ x0 hD hsupp (hgrowth x0)
  let : IsFiniteMeasure μ := ⟨hmass.trans_lt ENNReal.ofReal_lt_top⟩
  have hn2 : 2 ≤ (n : ℝ) := by exact_mod_cast hn
  have hcol (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ Ω) :
      (∫⁻ x, ENNReal.ofReal (‖y - x‖ ^ (1 - (n : ℝ))) ∂μ) ≤
        ENNReal.ofReal (ω * (n : ℝ) * D) := by
    have hyS : ∀ᵐ z ∂μ, z ∈ closedBall y D :=
      (ae_restrict_mem hΩm).mono fun z hz => hdiam z hz y hy
    have H := lintegral_norm_sub_rpow_neg_le_of_ae_closedBall_ball_growth μ y hω hD
      (by linarith : (0 : ℝ) < (n : ℝ) - 1) (by linarith : (n : ℝ) - 1 < (n : ℝ)) hyS (hgrowth y)
    have he : -((n : ℝ) - 1) = 1 - (n : ℝ) := by ring
    have hd : (n : ℝ) - ((n : ℝ) - 1) = 1 := by ring
    have hs : (fun x => ENNReal.ofReal (‖y - x‖ ^ (1 - (n : ℝ)))) =
        fun x => ENNReal.ofReal (‖x - y‖ ^ (1 - (n : ℝ))) := funext fun x => by rw [norm_sub_rev]
    rw [hs]
    simpa only [he,hd,Real.rpow_one,div_one] using H
  have hfm : AEMeasurable (fun y => ENNReal.ofReal |f y|) μ := by
    simpa only [Real.norm_eq_abs] using hf.aestronglyMeasurable.norm.aemeasurable.ennreal_ofReal
  have hk : Measurable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      ENNReal.ofReal (‖p.2 - p.1‖ ^ (1 - (n : ℝ)))) :=
    ((measurable_snd.sub measurable_fst).norm.pow_const _).ennreal_ofReal
  have hj := (hk.aemeasurable (μ := μ.prod μ)).mul hfm.comp_snd
  have hP : AEMeasurable P μ := by
    dsimp only [P]
    simp_rw [ENNReal.ofReal_mul (Real.rpow_nonneg (norm_nonneg _) _)]
    exact hj.lintegral_prod_right
  have hle : (∫⁻ x, P x ∂μ) ≤ ENNReal.ofReal (ω * (n : ℝ) * D) *
      (∫⁻ y, ENNReal.ofReal |f y| ∂μ) := by
    calc
      _ = ∫⁻ y, (∫⁻ x, ENNReal.ofReal (‖y - x‖ ^ (1 - (n : ℝ))) ∂μ) *
          ENNReal.ofReal |f y| ∂μ := by
        dsimp only [P]
        simp_rw [ENNReal.ofReal_mul (Real.rpow_nonneg (norm_nonneg _) _)]
        rw [lintegral_lintegral_swap hj]
        apply lintegral_congr
        intro y
        rw [lintegral_mul_const _ (by fun_prop)]
      _ ≤ ∫⁻ y, ENNReal.ofReal (ω * (n : ℝ) * D) * ENNReal.ofReal |f y| ∂μ := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem hΩm] with y hy
        exact mul_le_mul_of_nonneg_right (hcol y hy) zero_le
      _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have hi : (∫⁻ y, ENNReal.ofReal |f y| ∂μ) = ENNReal.ofReal (∫ y, |f y| ∂μ) :=
    (ofReal_integral_eq_lintegral_ofReal hf.abs (ae_of_all _ fun y => abs_nonneg (f y))).symm
  have hfin : (∫⁻ x, P x ∂μ) < ∞ := hle.trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (by rw [hi]; exact ENNReal.ofReal_lt_top))
  refine ⟨hP,ae_lt_top' hP hfin.ne,?_⟩
  change (∫⁻ x, P x ∂μ) ≤ ENNReal.ofReal (ω * (n : ℝ) * D * (∫ y, |f y| ∂μ))
  rw [hi,← ENNReal.ofReal_mul (by positivity : 0 ≤ ω * (n : ℝ) * D)] at hle
  exact hle

end FunctionalInequalities.Analysis
