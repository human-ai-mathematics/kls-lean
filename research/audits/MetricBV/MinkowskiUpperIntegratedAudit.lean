import FunctionalInequalities.KLS.Geometry.Cheeger.UpperMinkowskiContent

/-! Independent full-signature clients for the integrated upper content of thickenings. Checks: the
integrated bound `∫⁻ s in (0, r), ν⁺⁺(B^s) ≤ ν(B^r) - ν(B)` for every law, set and radius, its
measurable-set and positive-radius form, the half-open interval form, the derivative integral bound
on its own, the empty set, zero increments, the handling of `ENNReal` values (the integral is finite
and the integrand is a.e. finite; no measurability of the integrand is assumed anywhere), and the
uniform law on `[0, 1]` with `B = {0}`, where for `0 < r ≤ 1` the integral equals
`ENNReal.ofReal r = ν(B^r) - ν(B)`, so the bound is attained. Not claimed: measurability or
integrability of the integrand or of the derivative, absolute continuity of the radius mass,
equality in general, the lower-to-upper recovery or relaxed-upper identity. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Metric Set
open scoped ENNReal Topology

namespace MinkowskiUpperIntegratedAudit

open FunctionalInequalities.KLS.Isoperimetry

variable {V : Type*} [NormedAddCommGroup V] [MeasurableSpace V]

theorem integratedBound (ν : ProbabilityMeasure V) (B : Set V) (r : ℝ) :
    ∫⁻ s in Ioo 0 r, upperMinkowskiContent (ν : Measure V) (thickening s B) ≤
      (ν : Measure V) (thickening r B) - (ν : Measure V) B :=
  setLIntegral_upperMinkowskiContent_thickening_le (ν : Measure V) B r

/-- The form with measurable `B` and `r > 0` (the hypotheses are not needed). -/
theorem assignmentForm [BorelSpace V] (ν : ProbabilityMeasure V) {B : Set V}
    (_hB : MeasurableSet B) {r : ℝ} (_hr : 0 < r) :
    ∫⁻ s in Ioo 0 r, upperMinkowskiContent (ν : Measure V) (thickening s B) ≤
      (ν : Measure V) (thickening r B) - (ν : Measure V) B :=
  setLIntegral_upperMinkowskiContent_thickening_le (ν : Measure V) B r

theorem halfOpenForm (ν : ProbabilityMeasure V) (B : Set V) (r : ℝ) :
    ∫⁻ s in Ioc 0 r, upperMinkowskiContent (ν : Measure V) (thickening s B) ≤
      (ν : Measure V) (thickening r B) - (ν : Measure V) B :=
  setLIntegral_Ioc_upperMinkowskiContent_thickening_le (ν : Measure V) B r

/-- The derivative integral bound and its ingredients: Stieltjes mass of `(0, r)` and the two
endpoint passages. -/
theorem derivativeIntegral (ν : ProbabilityMeasure V) (B : Set V) (r : ℝ) :
    (∫⁻ s in Ioo 0 r, ENNReal.ofReal (deriv (thickeningMass (ν : Measure V) B) s) ≤
        (ν : Measure V) (thickening r B) - (ν : Measure V) B) ∧
      (monotone_thickeningMass (ν : Measure V) B).stieltjesFunction.measure (Ioo 0 r) ≤
        (ν : Measure V) (thickening r B) - (ν : Measure V) B ∧
      ((ν : Measure V) B).toReal ≤ Function.rightLim (thickeningMass (ν : Measure V) B) 0 ∧
      Function.leftLim (Function.rightLim (thickeningMass (ν : Measure V) B)) r ≤ thickeningMass (ν : Measure V) B r :=
  ⟨setLIntegral_ofReal_deriv_thickeningMass_le (ν : Measure V) B r, stieltjesMeasure_thickeningMass_Ioo_le (ν : Measure V) B r,
    toReal_measure_le_rightLim_thickeningMass_zero (ν : Measure V) B, leftLim_rightLim_thickeningMass_le (ν : Measure V) B r⟩

theorem emptySet (ν : ProbabilityMeasure V) (r : ℝ) :
    ∫⁻ s in Ioo 0 r, upperMinkowskiContent (ν : Measure V) (thickening s (∅ : Set V)) = 0 :=
  setLIntegral_upperMinkowskiContent_thickening_empty (ν : Measure V) r

theorem zeroIncrements (ν : ProbabilityMeasure V) {B : Set V} {r : ℝ}
    (h : (ν : Measure V) (thickening r B) ≤ (ν : Measure V) B) :
    ∫⁻ s in Ioo 0 r, upperMinkowskiContent (ν : Measure V) (thickening s B) = 0 :=
  setLIntegral_upperMinkowskiContent_thickening_eq_zero_of_measure_thickening_le (ν : Measure V) B h

/-- `ENNReal` values: the integral is finite and the integrand is a.e. finite, without any
measurability of the integrand; the bound itself is at most one. -/
theorem ennrealValues (ν : ProbabilityMeasure V) (B : Set V) (r : ℝ) :
    ∫⁻ s in Ioo 0 r, upperMinkowskiContent (ν : Measure V) (thickening s B) < ⊤ ∧
      (∀ᵐ s ∂(volume : Measure ℝ), upperMinkowskiContent (ν : Measure V) (thickening s B) < ⊤) ∧
      ∫⁻ s in Ioo 0 r, upperMinkowskiContent (ν : Measure V) (thickening s B) ≤ 1 :=
  ⟨setLIntegral_upperMinkowskiContent_thickening_lt_top (ν : Measure V) B r,
    ae_upperMinkowskiContent_thickening_lt_top (ν : Measure V) B,
    (setLIntegral_upperMinkowskiContent_thickening_le (ν : Measure V) B r).trans
      (tsub_le_self.trans prob_le_one)⟩

/-- Nonpositive radii: the interval is empty and the left side is `0`. -/
theorem nonpositiveRadius (ν : ProbabilityMeasure V) (B : Set V) {r : ℝ} (hr : r ≤ 0) :
    ∫⁻ s in Ioo 0 r, upperMinkowskiContent (ν : Measure V) (thickening s B) = 0 := by
  rw [Ioo_eq_empty (not_lt.mpr hr), Measure.restrict_empty, lintegral_zero_measure]

/-! ### The uniform law on `[0, 1]` with `B = {0}`: the bound is attained -/

/-- The uniform law on `[0, 1]`. -/
def uniformInterval : ProbabilityMeasure ℝ :=
  ⟨(volume : Measure ℝ).restrict (Icc 0 1), ⟨by simp⟩⟩

theorem thickening_ball_real {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    thickening t (ball (0 : ℝ) s) = ball (0 : ℝ) (s + t) := by
  refine subset_antisymm ((thickening_ball 0 t s).trans (by rw [add_comm])) fun x hx => ?_
  rw [mem_ball, dist_zero_right, Real.norm_eq_abs] at hx
  have hst : 0 < s + t := by linarith
  set c : ℝ := s / (s + t) with hc
  have hc0 : 0 < c := div_pos hs hst
  have hc1 : c < 1 := (div_lt_one hst).mpr (by linarith)
  refine mem_thickening_iff.mpr ⟨c * x, ?_, ?_⟩
  · rw [mem_ball, dist_zero_right, Real.norm_eq_abs, abs_mul, abs_of_pos hc0]
    calc c * |x| < c * (s + t) := mul_lt_mul_of_pos_left hx hc0
      _ = s := by rw [hc]; field_simp
  · rw [Real.dist_eq, show x - c * x = (1 - c) * x by ring, abs_mul, abs_of_pos (by linarith)]
    calc (1 - c) * |x| < (1 - c) * (s + t) := mul_lt_mul_of_pos_left hx (by linarith)
      _ = t := by rw [hc]; field_simp; ring

theorem uniform_ball {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    (uniformInterval : Measure ℝ) (ball (0 : ℝ) r) = ENNReal.ofReal r := by
  have hset : ball (0 : ℝ) r ∩ Icc 0 1 = Ico 0 r := by
    ext x
    simp only [Real.ball_eq_Ioo, zero_sub, zero_add, mem_inter_iff, mem_Ioo, mem_Icc, mem_Ico]
    constructor
    · rintro ⟨⟨_, h2⟩, h3, _⟩
      exact ⟨h3, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨by linarith, h2⟩, h1, by linarith⟩
  simp only [uniformInterval, ProbabilityMeasure.coe_mk]
  rw [Measure.restrict_apply measurableSet_ball, hset, Real.volume_Ico, sub_zero]

theorem uniform_singleton : (uniformInterval : Measure ℝ) {0} = 0 := by
  simp only [uniformInterval, ProbabilityMeasure.coe_mk]
  rw [Measure.restrict_apply (measurableSet_singleton 0)]
  exact measure_mono_null inter_subset_left (Real.volume_singleton)

theorem uniform_thickeningMass {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) :
    thickeningMass (uniformInterval : Measure ℝ) {0} s = s := by
  rw [thickeningMass, thickening_singleton, uniform_ball hs0 hs1, ENNReal.toReal_ofReal hs0.le]

theorem uniform_hasDerivAt {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    HasDerivAt (thickeningMass (uniformInterval : Measure ℝ) {0}) 1 s := by
  refine (hasDerivAt_id s).congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds hs0 hs1] with t ht
  exact uniform_thickeningMass ht.1 ht.2.le

/-- The upper content of the `s`-thickening of `{0}` is exactly `1` for `s ∈ (0, 1)`. -/
theorem uniform_upperContent {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    upperMinkowskiContent (uniformInterval : Measure ℝ) (thickening s {0}) = 1 := by
  have hquot : ∀ t : ℝ, 0 < t → t < 1 - s →
      ((uniformInterval : Measure ℝ) (thickening t (thickening s {0})) -
          (uniformInterval : Measure ℝ) (thickening s {0})) / ENNReal.ofReal t = 1 := by
    intro t ht0 ht1
    rw [thickening_singleton, thickening_ball_real hs0 ht0, uniform_ball hs0 hs1.le,
      uniform_ball (by linarith) (by linarith), ← ENNReal.ofReal_sub _ hs0.le,
      show s + t - s = t by ring, ENNReal.div_self (by simpa using ht0) ENNReal.ofReal_ne_top]
  unfold upperMinkowskiContent
  rw [limsup_congr (Eventually.mono (Ioo_mem_nhdsGT (by linarith : (0 : ℝ) < 1 - s))
    fun t ht => hquot t ht.1 ht.2)]
  exact limsup_const 1

/-- Attained: for `0 < r ≤ 1` both sides equal `ENNReal.ofReal r`.  (The pointwise value `1` on
`(0, 1)` is not used at the endpoint `r = 1` itself, which is Lebesgue-null.) -/
theorem uniformAttained {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    ∫⁻ s in Ioo 0 r, upperMinkowskiContent (uniformInterval : Measure ℝ) (thickening s {0}) =
        ENNReal.ofReal r ∧
      (uniformInterval : Measure ℝ) (thickening r {0}) - (uniformInterval : Measure ℝ) {0} =
        ENNReal.ofReal r := by
  constructor
  · rw [setLIntegral_congr_fun measurableSet_Ioo
      (fun s hs => uniform_upperContent hs.1 (hs.2.trans_le hr1)), setLIntegral_const,
      Real.volume_Ioo, sub_zero, one_mul]
  · rw [thickening_singleton, uniform_ball hr0 hr1, uniform_singleton, tsub_zero]

theorem uniformBoundConsistent {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    ∫⁻ s in Ioo 0 r, upperMinkowskiContent (uniformInterval : Measure ℝ) (thickening s {0}) =
      (uniformInterval : Measure ℝ) (thickening r {0}) - (uniformInterval : Measure ℝ) {0} := by
  obtain ⟨h1, h2⟩ := uniformAttained hr0 hr1
  exact le_antisymm (integratedBound uniformInterval {0} r) (by rw [h1, h2])

#print axioms integratedBound
#print axioms assignmentForm
#print axioms halfOpenForm
#print axioms derivativeIntegral
#print axioms emptySet
#print axioms zeroIncrements
#print axioms ennrealValues
#print axioms nonpositiveRadius
#print axioms uniformAttained
#print axioms uniformBoundConsistent

end MinkowskiUpperIntegratedAudit
