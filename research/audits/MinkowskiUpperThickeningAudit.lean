import FunctionalInequalities.KLS.Geometry.Cheeger.UpperMinkowskiContent
import FunctionalInequalities.KLS.BKL.Localization.Process.Basic
/-! Independent full-signature clients for the upper Minkowski content of thickenings at
differentiability radii (phase 22).  Checks: the almost-everywhere monotone differentiation
theorem combined with the pointwise derivative bound, the pointwise bound with a nonnegative
derivative, lower ≤ upper content, the empty set and the radius-mass bookkeeping, zero mass
increments, and two explicit probability laws on `ℝ` with `B = {0}`: the uniform law on `[0, 1]`,
whose radius mass is the identity on `(0, 1)` (derivative `1`, and the upper content of the
thickening is exactly `1`, so the bound is attained), and the Dirac law at `0`, whose radius mass
jumps at `0` (so it is not continuous there, although it is differentiable with derivative `0` at
every positive radius, where the upper content of the thickening is `0`).  No integrated
upper-content bound, no recovery/relaxation identity between the lower and upper contents and no
absolute continuity of the radius mass is claimed. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Metric Set
open scoped ENNReal Topology

namespace MinkowskiUpperThickeningAudit

open FunctionalInequalities.KLS.Isoperimetry

variable {V : Type*} [NormedAddCommGroup V] [MeasurableSpace V]

/-- The a.e. theorem together with the pointwise derivative bound, for every law and set. -/
theorem aeDerivativeBound (ν : ProbabilityMeasure V) (B : Set V) :
    ∀ᵐ s ∂(volume : Measure ℝ), DifferentiableAt ℝ (thickeningMass (ν : Measure V) B) s ∧
      upperMinkowskiContent (ν : Measure V) (thickening s B) ≤ ENNReal.ofReal (deriv (thickeningMass (ν : Measure V) B) s) := by
  filter_upwards [ae_differentiableAt_thickeningMass (ν : Measure V) B] with s hs
  exact ⟨hs, upperMinkowskiContent_thickening_le_deriv_of_differentiableAt (ν : Measure V) B hs⟩

/-- The same at almost every positive radius. -/
theorem aePositiveRadii (ν : ProbabilityMeasure V) (B : Set V) :
    ∀ᵐ s ∂((volume : Measure ℝ).restrict (Ioi 0)),
      0 < s ∧ DifferentiableAt ℝ (thickeningMass (ν : Measure V) B) s ∧
        upperMinkowskiContent (ν : Measure V) (thickening s B) ≤
          ENNReal.ofReal (deriv (thickeningMass (ν : Measure V) B) s) :=
  ae_restrict_Ioi_upperMinkowskiContent_thickening_le_deriv (ν : Measure V) B

/-- Pointwise: a derivative `d` at any radius bounds the upper content and is nonnegative. -/
theorem pointwiseBound (ν : ProbabilityMeasure V) (B : Set V) {s d : ℝ}
    (hd : HasDerivAt (thickeningMass (ν : Measure V) B) d s) :
    upperMinkowskiContent (ν : Measure V) (thickening s B) ≤ ENNReal.ofReal d ∧ 0 ≤ d :=
  ⟨upperMinkowskiContent_thickening_le_of_hasDerivAt (ν : Measure V) B hd,
    nonneg_of_hasDerivAt_thickeningMass (ν : Measure V) B hd⟩

theorem lowerLeUpper (ν : ProbabilityMeasure V) (B : Set V) :
    minkowskiContent (ν : Measure V) B ≤ upperMinkowskiContent (ν : Measure V) B :=
  minkowskiContent_le_upperMinkowskiContent (ν : Measure V) B

theorem emptySet (ν : ProbabilityMeasure V) :
    upperMinkowskiContent (ν : Measure V) (∅ : Set V) = 0 ∧ minkowskiContent (ν : Measure V) (∅ : Set V) = 0 ∧
      ∀ s : ℝ, thickeningMass (ν : Measure V) (∅ : Set V) s = 0 :=
  ⟨upperMinkowskiContent_empty (ν : Measure V), minkowskiContent_empty (ν : Measure V), thickeningMass_empty (ν : Measure V)⟩

/-- Radius-mass bookkeeping: monotone, in `[0, 1]`, zero for nonpositive radii, lossless
conversion, and the increment-quotient conversion with a positive denominator. -/
theorem massBookkeeping (ν : ProbabilityMeasure V) (B : Set V) :
    Monotone (thickeningMass (ν : Measure V) B) ∧
      (∀ s : ℝ, 0 ≤ thickeningMass (ν : Measure V) B s ∧ thickeningMass (ν : Measure V) B s ≤ 1) ∧
      (∀ s : ℝ, s ≤ 0 → thickeningMass (ν : Measure V) B s = 0) ∧
      (∀ s : ℝ, ENNReal.ofReal (thickeningMass (ν : Measure V) B s) = (ν : Measure V) (thickening s B)) ∧
      ∀ s t : ℝ, 0 < t →
        ((ν : Measure V) (thickening (s + t) B) - (ν : Measure V) (thickening s B)) /
            ENNReal.ofReal t =
          ENNReal.ofReal ((thickeningMass (ν : Measure V) B (s + t) - thickeningMass (ν : Measure V) B s) / t) :=
  ⟨monotone_thickeningMass (ν : Measure V) B, fun s => ⟨thickeningMass_nonneg (ν : Measure V) B s, thickeningMass_le_one ν B s⟩,
    fun _ hs => thickeningMass_of_nonpos (ν : Measure V) B hs, ofReal_thickeningMass (ν : Measure V) B,
    fun _ _ ht => measure_thickening_sub_div_eq_ofReal (ν : Measure V) B ht⟩

/-- Zero increments give zero upper content (and zero lower content). -/
theorem zeroIncrements (ν : ProbabilityMeasure V) {B : Set V}
    (h : ∀ r : ℝ, 0 < r → (ν : Measure V) (thickening r B) ≤ (ν : Measure V) B) :
    upperMinkowskiContent (ν : Measure V) B = 0 ∧ minkowskiContent (ν : Measure V) B = 0 := by
  have hu := upperMinkowskiContent_eq_zero_of_forall_measure_thickening_le (ν : Measure V) h
  exact ⟨hu, le_antisymm ((minkowskiContent_le_upperMinkowskiContent (ν : Measure V) B).trans_eq hu) bot_le⟩

/-! ### The uniform law on `[0, 1]` with `B = {0}` -/

/-- The uniform law on `[0, 1]`. -/
def uniformInterval : ProbabilityMeasure ℝ :=
  ⟨(volume : Measure ℝ).restrict (Icc 0 1), ⟨by simp⟩⟩

/-- On `ℝ`, the `t`-thickening of the ball of radius `s` is the ball of radius `s + t`
(the reverse inclusion by scaling towards the centre). -/
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

/-- The radius mass of `{0}` under the uniform law is the radius itself on `(0, 1]`. -/
theorem uniform_thickeningMass {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) :
    thickeningMass (uniformInterval : Measure ℝ) {0} s = s := by
  rw [thickeningMass, thickening_singleton, uniform_ball hs0 hs1, ENNReal.toReal_ofReal hs0.le]

/-- The radius mass has derivative `1` at every radius in `(0, 1)`. -/
theorem uniform_hasDerivAt {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    HasDerivAt (thickeningMass (uniformInterval : Measure ℝ) {0}) 1 s := by
  refine (hasDerivAt_id s).congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds hs0 hs1] with t ht
  exact uniform_thickeningMass ht.1 ht.2.le

/-- The derivative bound at every radius in `(0, 1)`: upper content of the thickening `≤ 1`. -/
theorem uniformBound {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    upperMinkowskiContent (uniformInterval : Measure ℝ) (thickening s {0}) ≤ 1 := by
  simpa using
    upperMinkowskiContent_thickening_le_of_hasDerivAt (uniformInterval : Measure ℝ) {0} (uniform_hasDerivAt hs0 hs1)

/-- The bound is attained: the upper content of the thickening is exactly `1`, and equals
`ENNReal.ofReal` of the derivative. -/
theorem uniformAttained {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    upperMinkowskiContent (uniformInterval : Measure ℝ) (thickening s {0}) = 1 ∧
      upperMinkowskiContent (uniformInterval : Measure ℝ) (thickening s {0}) =
        ENNReal.ofReal (deriv (thickeningMass (uniformInterval : Measure ℝ) {0}) s) := by
  have hderiv : deriv (thickeningMass (uniformInterval : Measure ℝ) {0}) s = 1 := (uniform_hasDerivAt hs0 hs1).deriv
  have hquot : ∀ t : ℝ, 0 < t → t < 1 - s →
      ((uniformInterval : Measure ℝ) (thickening t (thickening s {0})) -
          (uniformInterval : Measure ℝ) (thickening s {0})) / ENNReal.ofReal t = 1 := by
    intro t ht0 ht1
    rw [thickening_singleton, thickening_ball_real hs0 ht0, uniform_ball hs0 hs1.le,
      uniform_ball (by linarith) (by linarith), ← ENNReal.ofReal_sub _ hs0.le,
      show s + t - s = t by ring, ENNReal.div_self (by simpa using ht0) ENNReal.ofReal_ne_top]
  have hconst : upperMinkowskiContent (uniformInterval : Measure ℝ) (thickening s {0}) = 1 := by
    unfold upperMinkowskiContent
    rw [limsup_congr (Eventually.mono (Ioo_mem_nhdsGT (by linarith : (0 : ℝ) < 1 - s))
      fun t ht => hquot t ht.1 ht.2)]
    exact limsup_const 1
  exact ⟨hconst, by rw [hconst, hderiv, ENNReal.ofReal_one]⟩

/-! ### The Dirac law at `0` with `B = {0}`: zero increments and a jump of the radius mass -/

/-- The Dirac law at `0`. -/
def diracLaw : ProbabilityMeasure ℝ := ⟨Measure.dirac 0, inferInstance⟩

theorem dirac_thickeningMass_pos {s : ℝ} (hs : 0 < s) : thickeningMass (diracLaw : Measure ℝ) {0} s = 1 := by
  simp [thickeningMass, diracLaw, thickening_singleton, Measure.dirac_apply_of_mem (mem_ball_self hs)]

theorem dirac_thickeningMass_nonpos {s : ℝ} (hs : s ≤ 0) : thickeningMass (diracLaw : Measure ℝ) {0} s = 0 :=
  thickeningMass_of_nonpos (diracLaw : Measure ℝ) {0} hs

/-- The radius mass jumps at `0`: it is not continuous there, so a.e. differentiability does not
mean absolute continuity. -/
theorem dirac_jump : ¬ ContinuousAt (thickeningMass (diracLaw : Measure ℝ) {0}) 0 := by
  intro h
  have h0 : Tendsto (thickeningMass (diracLaw : Measure ℝ) {0}) (𝓝[>] 0) (𝓝 0) := by
    have := h.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    rwa [dirac_thickeningMass_nonpos le_rfl] at this
  have h1 : Tendsto (thickeningMass (diracLaw : Measure ℝ) {0}) (𝓝[>] 0) (𝓝 1) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (dirac_thickeningMass_pos hs).symm
  exact zero_ne_one (tendsto_nhds_unique h0 h1)

/-- At every positive radius the radius mass is differentiable with derivative `0`, the upper
content of the thickening is `0`, and the thickening carries no extra mass. -/
theorem diracPositiveRadius {s : ℝ} (hs : 0 < s) :
    HasDerivAt (thickeningMass (diracLaw : Measure ℝ) {0}) 0 s ∧
      upperMinkowskiContent (diracLaw : Measure ℝ) (thickening s {0}) = 0 := by
  have hd : HasDerivAt (thickeningMass (diracLaw : Measure ℝ) {0}) 0 s := by
    refine (hasDerivAt_const s (1 : ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hs] with t ht
    exact dirac_thickeningMass_pos ht
  refine ⟨hd, le_antisymm ?_ bot_le⟩
  simpa using upperMinkowskiContent_thickening_le_of_hasDerivAt (diracLaw : Measure ℝ) {0} hd

#print axioms aeDerivativeBound
#print axioms aePositiveRadii
#print axioms pointwiseBound
#print axioms lowerLeUpper
#print axioms emptySet
#print axioms massBookkeeping
#print axioms zeroIncrements
#print axioms uniformBound
#print axioms uniformAttained
#print axioms dirac_jump
#print axioms diracPositiveRadius

end MinkowskiUpperThickeningAudit
