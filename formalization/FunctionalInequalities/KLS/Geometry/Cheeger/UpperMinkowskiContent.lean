import FunctionalInequalities.KLS.Geometry.Cheeger.MinkowskiContent
import Mathlib.Analysis.Calculus.Monotone

/-!
# Upper Minkowski content of thickenings at differentiability radii

Companion of `Cheeger/MinkowskiContent.lean`.  `upperMinkowskiContent ν B` is the `limsup`, along
`𝓝[>] 0`, of the same radius quotient `(ν (thickening r B) - ν B) / ENNReal.ofReal r` whose
`liminf` defines the lower `minkowskiContent ν B`; the lower content is at most the upper one.

`thickeningMass ν B s = (ν (thickening s B)).toReal` is the real mass of the open `s`-thickening
of `B`.  It is monotone in the radius, hence differentiable at Lebesgue-almost every radius by
the monotone differentiation theorem (`Monotone.ae_differentiableAt`), and at every radius `s`
where it has a derivative `d` the upper content of `thickening s B` is at most `ENNReal.ofReal d`
(`upperMinkowskiContent_thickening_le_of_hasDerivAt`): the `t`-thickening of the `s`-thickening
lies in the `(s + t)`-thickening, so every content quotient is at most the right difference
quotient of the radius mass, which converges to `d`.  No content comparison is assumed.

Conventions.  The quotient lives in the complete lattice `ℝ≥0∞`, so `limsup` needs no
boundedness and may be `⊤`; the filter `𝓝[>] 0` only sees positive radii, where
`ENNReal.ofReal r` is a positive finite denominator, and it is nontrivial, so `liminf ≤ limsup`.
Masses are converted between `ℝ≥0∞` and `ℝ` through `ENNReal.ofReal`/`ENNReal.toReal`, which is
lossless for a finite measure (`ofReal_thickeningMass`, `measure_thickening_sub_div_eq_ofReal`).

Scope: finite measures on a metric space with a measurable structure (2026-09-30: generic metric
scope and finite-measure scope, as for the lower content; only the bound `thickeningMass ≤ 1` is
probability-specific; scaling by nonnegative real scalars and the zero measure are explicit), and every set `B` (the empty set and sets whose thickenings carry no extra mass are
covered explicitly).  Nothing is assumed or claimed about absolute continuity of the radius mass:
jumps and singular variation remain possible, and almost-everywhere differentiability is exactly
what the monotone differentiation theorem gives.  The section `Integrated` integrates the bound over the
radii (`setLIntegral_upperMinkowskiContent_thickening_le`): for every set `B` and radius `r`,
`∫⁻ s in Ioo 0 r, upperMinkowskiContent ν (thickening s B) ≤ ν (thickening r B) - ν B`, by
inequalities only (Radon–Nikodym form of the monotone differentiation theorem and one-sided
limits at the endpoints; no measurability of the content, integrability of the derivative or
absolute continuity is assumed).  The sections `Selection` and `Recovery` then give the
quantitative small-radius selection (`exists_upperMinkowskiContent_thickening_le_div_add`) and the
lower-to-upper recovery of every measurable set of finite lower content (`exists_upperRecovery`).
The upper-content recovery of the metric BV perimeter and the relaxed upper content live above
this layer, in `Perimeter/UpperMinkowskiRecovery.lean` and `Perimeter/RelaxedMinkowski.lean`.
-/

noncomputable section

open MeasureTheory Filter Metric Set
open scoped ENNReal NNReal Topology

namespace FunctionalInequalities.KLS.Isoperimetry

variable {V : Type*} [MetricSpace V] [MeasurableSpace V]

/-! ### Upper Minkowski content -/

/-- Upper Minkowski content `limsup_{r ↓ 0} (ν(B^r) - ν(B)) / r`, with open thickenings and
`ENNReal` truncated subtraction: the `limsup` of the radius quotient whose `liminf` is
`minkowskiContent`. -/
def upperMinkowskiContent (ν : Measure V) (B : Set V) : ℝ≥0∞ :=
  limsup (fun r : ℝ ↦
    ((ν : Measure V) (Metric.thickening r B) - (ν : Measure V) B) / ENNReal.ofReal r) (𝓝[>] 0)

/-- A positive neighborhood inside a measurable restriction region preserves the upper
content by eventual equality of the genuine small-radius quotients. -/
theorem upperMinkowskiContent_restrict_of_thickening_subset (ν : Measure V) {B U : Set V} (hU : MeasurableSet U)
    {δ : ℝ} (hδ : 0 < δ) (hsub : Metric.thickening δ B ⊆ U) :
    upperMinkowskiContent (ν.restrict U) B = upperMinkowskiContent ν B := by
  have hB : B ⊆ U := (Metric.self_subset_thickening hδ B).trans hsub
  unfold upperMinkowskiContent
  apply limsup_congr
  filter_upwards [Ioo_mem_nhdsGT hδ] with r hr
  have ht : Metric.thickening r B ⊆ U := (Metric.thickening_mono hr.2.le B).trans hsub
  rw [Measure.restrict_apply' hU, Measure.restrict_apply' hU,
    Set.inter_eq_left.2 ht, Set.inter_eq_left.2 hB]
omit [MetricSpace V] in
private theorem lintegral_enorm_indicator_sub_restrict_eq (ν : Measure V) {A B U : Set V} (hA : A ⊆ U) (hB : B ⊆ U) :
    (∫⁻ x, ‖A.indicator (1 : V → ℝ) x - B.indicator 1 x‖ₑ ∂(ν.restrict U)) =
      ∫⁻ x, ‖A.indicator (1 : V → ℝ) x - B.indicator 1 x‖ₑ ∂ν := by
  apply setLIntegral_eq_of_support_subset
  intro x hx
  by_contra hnot
  have ha : x ∉ A := fun hxA => hnot (hA hxA)
  have hb : x ∉ B := fun hxB => hnot (hB hxB)
  exact hx (by simp [ha, hb])

/-- The lower content is at most the upper content: `liminf ≤ limsup` along the nontrivial
filter `𝓝[>] 0`. -/
theorem minkowskiContent_le_upperMinkowskiContent (ν : Measure V) [IsFiniteMeasure ν] (B : Set V) :
    minkowskiContent ν B ≤ upperMinkowskiContent ν B :=
  liminf_le_limsup

/-- Zero mass increments: if no positive thickening carries more mass than `B`, the upper content
vanishes (every quotient is `0 / ENNReal.ofReal r = 0`). -/
theorem upperMinkowskiContent_eq_zero_of_forall_measure_thickening_le (ν : Measure V) [IsFiniteMeasure ν]
    {B : Set V} (h : ∀ r : ℝ, 0 < r → (ν : Measure V) (Metric.thickening r B) ≤ (ν : Measure V) B) :
    upperMinkowskiContent ν B = 0 := by
  refine le_antisymm ?_ bot_le
  unfold upperMinkowskiContent
  refine limsup_le_of_le (by isBoundedDefault) ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  rw [tsub_eq_zero_of_le (h r hr), ENNReal.zero_div]

/-- The empty set has zero upper content. -/
theorem upperMinkowskiContent_empty (ν : Measure V) [IsFiniteMeasure ν] :
    upperMinkowskiContent ν (∅ : Set V) = 0 :=
  upperMinkowskiContent_eq_zero_of_forall_measure_thickening_le ν fun r _ => by
    simp [Metric.thickening_empty]

/-- The empty set has zero lower content as well. -/
theorem minkowskiContent_empty (ν : Measure V) [IsFiniteMeasure ν] :
    minkowskiContent ν (∅ : Set V) = 0 :=
  le_antisymm
    ((minkowskiContent_le_upperMinkowskiContent ν ∅).trans_eq (upperMinkowskiContent_empty ν))
    bot_le

/-- **Upper content scaling**: `upperMinkowskiContent (c • ν) B = c * upperMinkowskiContent ν B`
for every `c : ℝ≥0`. -/
theorem upperMinkowskiContent_smul (c : ℝ≥0) (ν : Measure V) (B : Set V) :
    upperMinkowskiContent (c • ν) B = c * upperMinkowskiContent ν B := by
  unfold upperMinkowskiContent
  rw [← limsup_coe_mul]
  refine limsup_congr (Eventually.of_forall fun r => ?_)
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  rw [← ENNReal.mul_sub (fun _ _ => ENNReal.coe_ne_top), mul_div_assoc]

/-- The zero measure has zero upper content. -/
theorem upperMinkowskiContent_zero_measure (B : Set V) :
    upperMinkowskiContent (0 : Measure V) B = 0 :=
  upperMinkowskiContent_eq_zero_of_forall_measure_thickening_le (0 : Measure V) fun _ _ => by simp

/-! ### Radius mass of thickenings -/

/-- Real mass `ν(B^s)` of the open `s`-thickening of `B`. -/
def thickeningMass (ν : Measure V) (B : Set V) (s : ℝ) : ℝ :=
  ((ν : Measure V) (Metric.thickening s B)).toReal

theorem thickeningMass_nonneg (ν : Measure V) [IsFiniteMeasure ν] (B : Set V) (s : ℝ) :
    0 ≤ thickeningMass ν B s :=
  ENNReal.toReal_nonneg

theorem thickeningMass_le_one (ν : Measure V) [IsProbabilityMeasure ν] (B : Set V) (s : ℝ) :
    thickeningMass ν B s ≤ 1 :=
  ENNReal.toReal_le_of_le_ofReal zero_le_one (by rw [ENNReal.ofReal_one]; exact prob_le_one)

/-- The real radius mass converts back to the `ℝ≥0∞` mass without loss. -/
theorem ofReal_thickeningMass (ν : Measure V) [IsFiniteMeasure ν] (B : Set V) (s : ℝ) :
    ENNReal.ofReal (thickeningMass ν B s) = (ν : Measure V) (Metric.thickening s B) :=
  ENNReal.ofReal_toReal (measure_ne_top _ _)

/-- The radius mass is monotone: thickenings grow with the radius. -/
theorem monotone_thickeningMass (ν : Measure V) [IsFiniteMeasure ν] (B : Set V) :
    Monotone (thickeningMass ν B) := fun _ _ hst =>
  ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Metric.thickening_mono hst B))

/-- Nonpositive radii give the empty thickening, hence zero mass. -/
theorem thickeningMass_of_nonpos (ν : Measure V) [IsFiniteMeasure ν] (B : Set V) {s : ℝ} (hs : s ≤ 0) :
    thickeningMass ν B s = 0 := by
  simp [thickeningMass, Metric.thickening_of_nonpos hs]

/-- The radius mass scales with the measure. -/
theorem thickeningMass_smul (c : ℝ≥0) (ν : Measure V) (B : Set V) (s : ℝ) :
    thickeningMass (c • ν) B s = c * thickeningMass ν B s := by
  rw [thickeningMass, thickeningMass, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul,
    ENNReal.toReal_mul, ENNReal.coe_toReal]

/-- The zero measure has zero radius mass. -/
theorem thickeningMass_zero_measure (B : Set V) (s : ℝ) :
    thickeningMass (0 : Measure V) B s = 0 := by
  simp [thickeningMass]

theorem thickeningMass_empty (ν : Measure V) [IsFiniteMeasure ν] (s : ℝ) :
    thickeningMass ν (∅ : Set V) s = 0 := by
  simp [thickeningMass]

/-- For a positive radius increment `t`, the `ℝ≥0∞` increment quotient of the thickening masses
equals `ENNReal.ofReal` of the real right difference quotient of the radius mass. -/
theorem measure_thickening_sub_div_eq_ofReal (ν : Measure V) [IsFiniteMeasure ν] (B : Set V) {s t : ℝ}
    (ht : 0 < t) :
    ((ν : Measure V) (Metric.thickening (s + t) B) - (ν : Measure V) (Metric.thickening s B)) /
        ENNReal.ofReal t =
      ENNReal.ofReal ((thickeningMass ν B (s + t) - thickeningMass ν B s) / t) := by
  rw [ENNReal.ofReal_div_of_pos ht, ENNReal.ofReal_sub _ (thickeningMass_nonneg ν B s),
    ofReal_thickeningMass, ofReal_thickeningMass]

/-! ### Derivative bound on the upper content of a thickening -/

/-- The right difference quotient of a real function converges to its derivative along
`𝓝[>] 0`. -/
private theorem tendsto_right_slope_of_hasDerivAt {F : ℝ → ℝ} {d s : ℝ}
    (hF : HasDerivAt F d s) :
    Tendsto (fun t : ℝ => (F (s + t) - F s) / t) (𝓝[>] 0) (𝓝 d) := by
  have h := (hasDerivAt_iff_tendsto_slope_zero.mp hF).mono_left
    (nhdsWithin_mono (0 : ℝ) fun t (ht : t ∈ Ioi 0) => (ne_of_gt ht : t ≠ 0))
  refine h.congr' (Eventually.of_forall fun t => ?_)
  simp [smul_eq_mul, inv_mul_eq_div]

/-- At a radius `s` where the radius mass has the derivative `d`, the upper Minkowski content of
`thickening s B` is at most `ENNReal.ofReal d`.  The `t`-thickening of `thickening s B` lies in
`thickening (s + t) B`, so each content quotient is at most the right difference quotient
`(F (s + t) - F s) / t` of the radius mass, whose limit is `d`.  Nothing is assumed about the
content of `B` itself; for `s ≤ 0` the thickening is empty and the bound is trivial. -/
theorem upperMinkowskiContent_thickening_le_of_hasDerivAt (ν : Measure V) [IsFiniteMeasure ν] (B : Set V)
    {s d : ℝ} (hd : HasDerivAt (thickeningMass ν B) d s) :
    upperMinkowskiContent ν (Metric.thickening s B) ≤ ENNReal.ofReal d := by
  have hlim : Tendsto
      (fun t : ℝ => ENNReal.ofReal ((thickeningMass ν B (s + t) - thickeningMass ν B s) / t))
      (𝓝[>] 0) (𝓝 (ENNReal.ofReal d)) :=
    ENNReal.tendsto_ofReal (tendsto_right_slope_of_hasDerivAt hd)
  rw [← hlim.limsup_eq]
  unfold upperMinkowskiContent
  refine limsup_le_limsup ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [← measure_thickening_sub_div_eq_ofReal ν B ht]
  refine ENNReal.div_le_div_right (tsub_le_tsub_right (measure_mono ?_) _) _
  exact (Metric.thickening_thickening_subset t s B).trans (by rw [add_comm])

/-- The `deriv` form of the bound at a differentiability radius. -/
theorem upperMinkowskiContent_thickening_le_deriv_of_differentiableAt (ν : Measure V) [IsFiniteMeasure ν]
    (B : Set V) {s : ℝ} (hs : DifferentiableAt ℝ (thickeningMass ν B) s) :
    upperMinkowskiContent ν (Metric.thickening s B) ≤
      ENNReal.ofReal (deriv (thickeningMass ν B) s) :=
  upperMinkowskiContent_thickening_le_of_hasDerivAt ν B hs.hasDerivAt

/-- The derivative of the monotone radius mass is nonnegative (`deriv` is `0` where the mass is
not differentiable). -/
theorem deriv_thickeningMass_nonneg (ν : Measure V) [IsFiniteMeasure ν] (B : Set V) (s : ℝ) :
    0 ≤ deriv (thickeningMass ν B) s :=
  (monotone_thickeningMass ν B).deriv_nonneg

theorem nonneg_of_hasDerivAt_thickeningMass (ν : Measure V) [IsFiniteMeasure ν] (B : Set V) {s d : ℝ}
    (hd : HasDerivAt (thickeningMass ν B) d s) : 0 ≤ d := by
  rw [← hd.deriv]
  exact deriv_thickeningMass_nonneg ν B s

/-! ### Almost-everywhere differentiability of the radius mass -/

/-- The radius mass is differentiable at Lebesgue-almost every radius, by the monotone
differentiation theorem.  Only differentiability is claimed: the radius mass may still jump or
have singular variation. -/
theorem ae_differentiableAt_thickeningMass (ν : Measure V) [IsFiniteMeasure ν] (B : Set V) :
    ∀ᵐ s ∂(volume : Measure ℝ), DifferentiableAt ℝ (thickeningMass ν B) s :=
  (monotone_thickeningMass ν B).ae_differentiableAt

/-- At Lebesgue-almost every radius the upper content of the thickening is at most the derivative
of the radius mass (for `s ≤ 0` the thickening is empty). -/
theorem ae_upperMinkowskiContent_thickening_le_deriv (ν : Measure V) [IsFiniteMeasure ν] (B : Set V) :
    ∀ᵐ s ∂(volume : Measure ℝ), upperMinkowskiContent ν (Metric.thickening s B) ≤
      ENNReal.ofReal (deriv (thickeningMass ν B) s) := by
  filter_upwards [ae_differentiableAt_thickeningMass ν B] with s hs
  exact upperMinkowskiContent_thickening_le_deriv_of_differentiableAt ν B hs

/-- The same at Lebesgue-almost every positive radius, with the positivity and the
differentiability witness recorded. -/
theorem ae_restrict_Ioi_upperMinkowskiContent_thickening_le_deriv (ν : Measure V) [IsFiniteMeasure ν]
    (B : Set V) :
    ∀ᵐ s ∂((volume : Measure ℝ).restrict (Ioi 0)),
      0 < s ∧ DifferentiableAt ℝ (thickeningMass ν B) s ∧
        upperMinkowskiContent ν (Metric.thickening s B) ≤
          ENNReal.ofReal (deriv (thickeningMass ν B) s) := by
  filter_upwards [ae_restrict_mem (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ))),
    ae_restrict_of_ae (ae_differentiableAt_thickeningMass ν B)] with s hs hd
  exact ⟨hs, hd, upperMinkowskiContent_thickening_le_deriv_of_differentiableAt ν B hd⟩

/-! ### Integrated upper content of thickenings

The upper content of `thickening s B` integrated over the radii `s ∈ (0, r)` is at most the mass
increment `ν (thickening r B) - ν B`.  The route is inequality only: the phase-22 a.e. bound by
`ENNReal.ofReal (deriv F s)`, then the Radon–Nikodym form of the monotone differentiation theorem
(`Monotone.ae_hasDerivAt`), which identifies the derivative a.e. with the density of the
Lebesgue–Stieltjes measure `μ_F` of the right-continuous modification `rightLim F` of the radius
mass `F = thickeningMass ν B`, then `∫⁻ rnDeriv ≤ μ_F` on `(0, r)` (`withDensity_rnDeriv_le`, no
absolute continuity), and finally the endpoint passages `μ_F (Ioo 0 r) = ofReal (leftLim g r - g 0)`
with `leftLim g r ≤ F r` and `(ν B).toReal ≤ g 0`, both by one-sided limits of monotone functions.
Nothing is assumed about measurability of the integrand, integrability of the derivative, or
continuity of the radius mass at `0` or `r`.
-/

section Integrated

variable (ν : Measure V) [IsFiniteMeasure ν] (B : Set V)

/-- The right limit of the radius mass at `0` dominates the mass of `B`: every positive
thickening contains `B`. -/
theorem toReal_measure_le_rightLim_thickeningMass_zero :
    ((ν : Measure V) B).toReal ≤ Function.rightLim (thickeningMass ν B) 0 := by
  refine ge_of_tendsto ((monotone_thickeningMass ν B).tendsto_rightLim 0) ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact ENNReal.toReal_mono (measure_ne_top _ _)
    (measure_mono (Metric.self_subset_thickening hs B))

/-- The left limit at `r` of the right-continuous modification of the radius mass is at most the
radius mass at `r` (for `s < r`, `rightLim F s ≤ F r`). -/
theorem leftLim_rightLim_thickeningMass_le (r : ℝ) :
    Function.leftLim (Function.rightLim (thickeningMass ν B)) r ≤ thickeningMass ν B r := by
  refine le_of_tendsto ((monotone_thickeningMass ν B).rightLim.tendsto_leftLim r) ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact (monotone_thickeningMass ν B).rightLim_le hs

/-- The Lebesgue–Stieltjes measure of the right-continuous modification of the radius mass gives
the open radius interval `(0, r)` at most the mass increment `ν (thickening r B) - ν B`. -/
theorem stieltjesMeasure_thickeningMass_Ioo_le (r : ℝ) :
    (monotone_thickeningMass ν B).stieltjesFunction.measure (Ioo 0 r) ≤
      (ν : Measure V) (Metric.thickening r B) - (ν : Measure V) B := by
  rw [StieltjesFunction.measure_Ioo]
  have h1 : Function.leftLim (⇑(monotone_thickeningMass ν B).stieltjesFunction) r ≤
      thickeningMass ν B r :=
    leftLim_rightLim_thickeningMass_le ν B r
  have h2 : ((ν : Measure V) B).toReal ≤ (monotone_thickeningMass ν B).stieltjesFunction 0 :=
    toReal_measure_le_rightLim_thickeningMass_zero ν B
  calc ENNReal.ofReal (Function.leftLim (⇑(monotone_thickeningMass ν B).stieltjesFunction) r -
        (monotone_thickeningMass ν B).stieltjesFunction 0)
      ≤ ENNReal.ofReal (thickeningMass ν B r - ((ν : Measure V) B).toReal) :=
        ENNReal.ofReal_le_ofReal (by linarith)
    _ = (ν : Measure V) (Metric.thickening r B) - (ν : Measure V) B := by
        rw [ENNReal.ofReal_sub _ ENNReal.toReal_nonneg, ofReal_thickeningMass,
          ENNReal.ofReal_toReal (measure_ne_top _ _)]

/-- The derivative integral bound: the integrated derivative of the radius mass over `(0, r)` is at
most the mass increment.  A.e. the derivative is the (truncated) Radon–Nikodym density of the
Stieltjes measure, whose integral is at most the Stieltjes mass of `(0, r)`; no absolute
continuity is used, and the density may be infinite on a null set. -/
theorem setLIntegral_ofReal_deriv_thickeningMass_le (r : ℝ) :
    ∫⁻ s in Ioo 0 r, ENNReal.ofReal (deriv (thickeningMass ν B) s) ≤
      (ν : Measure V) (Metric.thickening r B) - (ν : Measure V) B := by
  calc ∫⁻ s in Ioo 0 r, ENNReal.ofReal (deriv (thickeningMass ν B) s)
      ≤ ∫⁻ s in Ioo 0 r,
          (monotone_thickeningMass ν B).stieltjesFunction.measure.rnDeriv volume s := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_restrict_of_ae (monotone_thickeningMass ν B).ae_hasDerivAt] with s hs
        rw [hs.deriv]
        exact ENNReal.ofReal_toReal_le
    _ = (volume.withDensity
          ((monotone_thickeningMass ν B).stieltjesFunction.measure.rnDeriv volume)) (Ioo 0 r) :=
        (withDensity_apply _ measurableSet_Ioo).symm
    _ ≤ (monotone_thickeningMass ν B).stieltjesFunction.measure (Ioo 0 r) :=
        Measure.le_iff'.mp (Measure.withDensity_rnDeriv_le _ _) _
    _ ≤ (ν : Measure V) (Metric.thickening r B) - (ν : Measure V) B :=
        stieltjesMeasure_thickeningMass_Ioo_le ν B r

/-- **Integrated upper content of thickenings.**  For every set `B` and every radius `r`, the
upper Minkowski content of `thickening s B` integrated over `s ∈ (0, r)` is at most the mass
increment `ν (thickening r B) - ν B` (for `r ≤ 0` the left side is `0`).  The integrand need not
be measurable: the lower integral is monotone under a.e. inequalities. -/
theorem setLIntegral_upperMinkowskiContent_thickening_le (r : ℝ) :
    ∫⁻ s in Ioo 0 r, upperMinkowskiContent ν (Metric.thickening s B) ≤
      (ν : Measure V) (Metric.thickening r B) - (ν : Measure V) B :=
  (lintegral_mono_ae (ae_restrict_of_ae (ae_upperMinkowskiContent_thickening_le_deriv ν B))).trans
    (setLIntegral_ofReal_deriv_thickeningMass_le ν B r)

/-- The same over the half-open radius interval `(0, r]`: the endpoint is Lebesgue-null. -/
theorem setLIntegral_Ioc_upperMinkowskiContent_thickening_le (r : ℝ) :
    ∫⁻ s in Ioc 0 r, upperMinkowskiContent ν (Metric.thickening s B) ≤
      (ν : Measure V) (Metric.thickening r B) - (ν : Measure V) B := by
  rw [← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
  exact setLIntegral_upperMinkowskiContent_thickening_le ν B r

/-- The integrated upper content of thickenings is finite (at most the mass of the
`r`-thickening). -/
theorem setLIntegral_upperMinkowskiContent_thickening_lt_top (r : ℝ) :
    ∫⁻ s in Ioo 0 r, upperMinkowskiContent ν (Metric.thickening s B) < ⊤ :=
  (setLIntegral_upperMinkowskiContent_thickening_le ν B r).trans_lt
    (tsub_le_self.trans_lt (measure_lt_top _ _))

/-- The upper content of the thickening is finite at Lebesgue-almost every radius. -/
theorem ae_upperMinkowskiContent_thickening_lt_top :
    ∀ᵐ s ∂(volume : Measure ℝ), upperMinkowskiContent ν (Metric.thickening s B) < ⊤ := by
  filter_upwards [ae_upperMinkowskiContent_thickening_le_deriv ν B] with s hs
  exact hs.trans_lt ENNReal.ofReal_lt_top

/-- Zero mass increments give zero integrated upper content. -/
theorem setLIntegral_upperMinkowskiContent_thickening_eq_zero_of_measure_thickening_le {r : ℝ}
    (hr : (ν : Measure V) (Metric.thickening r B) ≤ (ν : Measure V) B) :
    ∫⁻ s in Ioo 0 r, upperMinkowskiContent ν (Metric.thickening s B) = 0 :=
  le_antisymm
    ((setLIntegral_upperMinkowskiContent_thickening_le ν B r).trans_eq (tsub_eq_zero_of_le hr))
    bot_le

/-- The empty set has zero integrated upper content. -/
theorem setLIntegral_upperMinkowskiContent_thickening_empty (r : ℝ) :
    ∫⁻ s in Ioo 0 r, upperMinkowskiContent ν (Metric.thickening s (∅ : Set V)) = 0 :=
  setLIntegral_upperMinkowskiContent_thickening_eq_zero_of_measure_thickening_le ν ∅
    (by simp [Metric.thickening_empty])

end Integrated

/-! ### Quantitative small-radius selection

From the integrated bound, some radius `s ∈ (0, r)` has upper content of `thickening s B` at most
the lower-content quotient at `r` plus any positive slack.  The radius-content function is never
assumed measurable: the argument compares the lower integral with the integral of a constant.
-/

section Selection

variable (ν : Measure V) [IsFiniteMeasure ν] (B : Set V)

/-- Selection with positive slack (the argument of
`MetricBV.exists_mem_Ioo_le_div_add_of_setLIntegral_le`, re-proved privately here because that
lemma lives in the BV–Minkowski bridge above this layer): if a not necessarily measurable `φ` has
lower integral at most a finite `C` over `(0, r)`, some `t ∈ (0, r)` has
`φ t ≤ C / ofReal r + ofReal ε`. -/
private theorem exists_mem_Ioo_le_div_add {φ : ℝ → ℝ≥0∞} {r : ℝ} (hr : 0 < r) {C : ℝ≥0∞}
    (hC : C ≠ ⊤) (hφ : ∫⁻ t in Ioo 0 r, φ t ≤ C) {ε : ℝ} (hε : 0 < ε) :
    ∃ t ∈ Ioo 0 r, φ t ≤ C / ENNReal.ofReal r + ENNReal.ofReal ε := by
  by_contra h
  push Not at h
  have hr0 : ENNReal.ofReal r ≠ 0 := (ENNReal.ofReal_pos.2 hr).ne'
  have hlow : (C / ENNReal.ofReal r + ENNReal.ofReal ε) * ENNReal.ofReal r ≤ C := by
    calc (C / ENNReal.ofReal r + ENNReal.ofReal ε) * ENNReal.ofReal r
        = ∫⁻ _ in Ioo 0 r, (C / ENNReal.ofReal r + ENNReal.ofReal ε) := by
          rw [setLIntegral_const, Real.volume_Ioo, sub_zero]
      _ ≤ ∫⁻ t in Ioo 0 r, φ t := setLIntegral_mono' measurableSet_Ioo fun t ht => (h t ht).le
      _ ≤ C := hφ
  rw [add_mul, ENNReal.div_mul_cancel hr0 ENNReal.ofReal_ne_top] at hlow
  have hpos : 0 < ENNReal.ofReal ε * ENNReal.ofReal r :=
    ENNReal.mul_pos (ENNReal.ofReal_pos.2 hε).ne' hr0
  exact absurd hlow (not_le.2 (ENNReal.lt_add_right hC hpos.ne'))

/-- **Quantitative small-radius selection.**  For every set `B`, `r > 0` and `ε > 0` there is a
radius `s ∈ (0, r)` with `upperMinkowskiContent ν (thickening s B) ≤
(ν (thickening r B) - ν B) / ENNReal.ofReal r + ENNReal.ofReal ε`; the first summand is the
lower-content quotient at `r`. -/
theorem exists_upperMinkowskiContent_thickening_le_div_add {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε) :
    ∃ s ∈ Ioo 0 r, upperMinkowskiContent ν (Metric.thickening s B) ≤
      ((ν : Measure V) (Metric.thickening r B) - (ν : Measure V) B) / ENNReal.ofReal r +
        ENNReal.ofReal ε :=
  exists_mem_Ioo_le_div_add hr (tsub_le_self.trans_lt (measure_lt_top _ _)).ne
    (setLIntegral_upperMinkowskiContent_thickening_le ν B r) hε

end Selection

/-! ### Lower-to-upper recovery of a measurable set of finite lower content

For a measurable `B` with `minkowskiContent ν B ≠ ⊤`, radii `r n ∈ (0, 1/(n+1))` at which the
lower-content quotient is below `minkowskiContent ν B + n⁻¹` exist (the quotient tends to the
lower content along them), and the selection gives `s n ∈ (0, r n)` whose thickenings converge
to `B` in indicator `L¹(ν)` with `limsup upperMinkowskiContent ν (thickening (s n) B) ≤
minkowskiContent ν B`.  The vanishing mass increment is derived from the finite lower content
(`ν (B^{r n}) - ν B = q (r n) · ofReal (r n)`); no `ν (closure B) = ν B` is assumed, equality with
the lower content is not claimed, and the infinite-content case is excluded by hypothesis rather
than handled through `toReal` (for `minkowskiContent ν B = ⊤` only the trivial bound `≤ ⊤` holds).
-/

section Recovery

variable (ν : Measure V) [IsFiniteMeasure ν] (B : Set V)

omit [IsFiniteMeasure ν] in
/-- The mass increment at a positive radius is the lower-content quotient times the radius. -/
theorem measure_thickening_sub_eq_div_mul {r : ℝ} (hr : 0 < r) :
    (ν : Measure V) (Metric.thickening r B) - (ν : Measure V) B =
      ((ν : Measure V) (Metric.thickening r B) - (ν : Measure V) B) / ENNReal.ofReal r *
        ENNReal.ofReal r :=
  (ENNReal.div_mul_cancel (ENNReal.ofReal_pos.2 hr).ne' ENNReal.ofReal_ne_top).symm

omit [IsFiniteMeasure ν] in
/-- Radii realizing the lower-content liminf: `r n ∈ (0, 1/(n+1))` with quotient at most
`minkowskiContent ν B + n⁻¹`, so `r n → 0⁺` and the quotients tend to the lower content. -/
theorem exists_radii_tendsto_minkowskiContent (hfin : minkowskiContent ν B ≠ ⊤) :
    ∃ r : ℕ → ℝ, (∀ n : ℕ, r n ∈ Ioo 0 (1 / ((n : ℝ) + 1))) ∧
      (∀ n : ℕ, ((ν : Measure V) (Metric.thickening (r n) B) - (ν : Measure V) B) /
          ENNReal.ofReal (r n) ≤ minkowskiContent ν B + (n : ℝ≥0∞)⁻¹) ∧
      Tendsto r atTop (𝓝[>] 0) ∧
      Tendsto (fun n => ((ν : Measure V) (Metric.thickening (r n) B) - (ν : Measure V) B) /
        ENNReal.ofReal (r n)) atTop (𝓝 (minkowskiContent ν B)) := by
  set q : ℝ → ℝ≥0∞ := fun t =>
    ((ν : Measure V) (Metric.thickening t B) - (ν : Measure V) B) / ENNReal.ofReal t with hq
  have hex : ∀ n : ℕ, ∃ t, t ∈ Ioo 0 (1 / ((n : ℝ) + 1)) ∧
      q t < minkowskiContent ν B + (n : ℝ≥0∞)⁻¹ := by
    intro n
    have hlt : liminf q (𝓝[>] 0) < minkowskiContent ν B + (n : ℝ≥0∞)⁻¹ :=
      ENNReal.lt_add_right hfin (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top n))
    have hfreq : ∃ᶠ t in 𝓝[>] (0 : ℝ), q t < minkowskiContent ν B + (n : ℝ≥0∞)⁻¹ :=
      frequently_lt_of_liminf_lt (by isBoundedDefault) hlt
    have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Ioo 0 (1 / ((n : ℝ) + 1)) :=
      Ioo_mem_nhdsGT (by positivity)
    exact (hev.and_frequently hfreq).exists
  choose r hr using hex
  have hrT : Tendsto r atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => (hr n).1.1⟩
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      tendsto_one_div_add_atTop_nhds_zero_nat (fun n => (hr n).1.1.le) (fun n => (hr n).1.2.le)
  refine ⟨r, fun n => (hr n).1, fun n => (hr n).2.le, hrT, ?_⟩
  refine tendsto_of_le_liminf_of_limsup_le ?_ ?_
  · exact hrT.liminf_le_liminf_comp
  · have hlim : Tendsto (fun n : ℕ => minkowskiContent ν B + (n : ℝ≥0∞)⁻¹) atTop
        (𝓝 (minkowskiContent ν B)) := by
      simpa using tendsto_const_nhds.add ENNReal.tendsto_inv_nat_nhds_zero
    rw [← hlim.limsup_eq]
    exact limsup_le_limsup (Eventually.of_forall fun n => (hr n).2.le)

variable [OpensMeasurableSpace V]

/-- The indicator `L¹(ν)` error of a positive thickening of a measurable set is the mass
increment. -/
theorem lintegral_enorm_indicator_thickening_sub (hB : MeasurableSet B) {s : ℝ} (hs : 0 < s) :
    ∫⁻ x, ‖(Metric.thickening s B).indicator (1 : V → ℝ) x - B.indicator 1 x‖ₑ ∂(ν : Measure V) =
      (ν : Measure V) (Metric.thickening s B) - (ν : Measure V) B := by
  have hsub : B ⊆ Metric.thickening s B := Metric.self_subset_thickening hs B
  have hpt : ∀ x, ‖(Metric.thickening s B).indicator (1 : V → ℝ) x - B.indicator 1 x‖ₑ =
      (Metric.thickening s B \ B).indicator (fun _ => (1 : ℝ≥0∞)) x := by
    intro x
    by_cases hxB : x ∈ B
    · simp [hxB, hsub hxB]
    · by_cases hxT : x ∈ Metric.thickening s B
      · simp [hxB, hxT]
      · simp [hxB, hxT]
  simp_rw [hpt]
  rw [lintegral_indicator (Metric.isOpen_thickening.measurableSet.diff hB), setLIntegral_const,
    one_mul, measure_sdiff hsub hB.nullMeasurableSet (measure_ne_top _ _)]

/-- **Lower-to-upper recovery.**  For a measurable `B` with finite lower content there are
positive radii `s n → 0` whose (measurable, open) thickenings converge to `B` in indicator
`L¹(ν)` and satisfy `limsup upperMinkowskiContent ν (thickening (s n) B) ≤ minkowskiContent ν B`.
The mass increments vanish because the lower content is finite; nothing is assumed about
`ν (closure B)`. -/
theorem exists_upperRecovery (hB : MeasurableSet B) (hfin : minkowskiContent ν B ≠ ⊤) :
    ∃ s : ℕ → ℝ, (∀ n, 0 < s n) ∧ Tendsto s atTop (𝓝 0) ∧
      (∀ n, MeasurableSet (Metric.thickening (s n) B)) ∧
      Tendsto (fun n => ∫⁻ x, ‖(Metric.thickening (s n) B).indicator (1 : V → ℝ) x -
        B.indicator 1 x‖ₑ ∂(ν : Measure V)) atTop (𝓝 0) ∧
      limsup (fun n => upperMinkowskiContent ν (Metric.thickening (s n) B)) atTop ≤
        minkowskiContent ν B := by
  obtain ⟨r, hr, hq, hrT, hqT⟩ := exists_radii_tendsto_minkowskiContent ν B hfin
  have hsel : ∀ n : ℕ, ∃ s ∈ Ioo 0 (r n), upperMinkowskiContent ν (Metric.thickening s B) ≤
      ((ν : Measure V) (Metric.thickening (r n) B) - (ν : Measure V) B) /
        ENNReal.ofReal (r n) + ENNReal.ofReal (1 / ((n : ℝ) + 1)) :=
    fun n => exists_upperMinkowskiContent_thickening_le_div_add ν B (hr n).1 (by positivity)
  choose s hs hsel using hsel
  have hr0 : Tendsto r atTop (𝓝 0) := hrT.mono_right nhdsWithin_le_nhds
  have hslack : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat
  refine ⟨s, fun n => (hs n).1, ?_, fun _ => Metric.isOpen_thickening.measurableSet, ?_, ?_⟩
  · exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hr0
      (fun n => (hs n).1.le) (fun n => (hs n).2.le)
  · have hbound : ∀ n : ℕ, ∫⁻ x, ‖(Metric.thickening (s n) B).indicator (1 : V → ℝ) x -
        B.indicator 1 x‖ₑ ∂(ν : Measure V) ≤
          (minkowskiContent ν B + (n : ℝ≥0∞)⁻¹) * ENNReal.ofReal (1 / ((n : ℝ) + 1)) := by
      intro n
      rw [lintegral_enorm_indicator_thickening_sub ν B hB (hs n).1]
      calc (ν : Measure V) (Metric.thickening (s n) B) - (ν : Measure V) B
          ≤ (ν : Measure V) (Metric.thickening (r n) B) - (ν : Measure V) B :=
            tsub_le_tsub_right (measure_mono (Metric.thickening_mono (hs n).2.le B)) _
        _ = ((ν : Measure V) (Metric.thickening (r n) B) - (ν : Measure V) B) /
              ENNReal.ofReal (r n) * ENNReal.ofReal (r n) :=
            measure_thickening_sub_eq_div_mul ν B (hr n).1
        _ ≤ (minkowskiContent ν B + (n : ℝ≥0∞)⁻¹) * ENNReal.ofReal (1 / ((n : ℝ) + 1)) :=
            mul_le_mul' (hq n) (ENNReal.ofReal_le_ofReal (hr n).2.le)
    have hlim : Tendsto (fun n : ℕ => (minkowskiContent ν B + (n : ℝ≥0∞)⁻¹) *
        ENNReal.ofReal (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n : ℕ => minkowskiContent ν B + (n : ℝ≥0∞)⁻¹) atTop
          (𝓝 (minkowskiContent ν B)) := by
        simpa using tendsto_const_nhds.add ENNReal.tendsto_inv_nat_nhds_zero
      simpa using ENNReal.Tendsto.mul h1 (Or.inr ENNReal.zero_ne_top) hslack (Or.inr hfin)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => zero_le)
      hbound
  · have hlim : Tendsto (fun n : ℕ =>
        ((ν : Measure V) (Metric.thickening (r n) B) - (ν : Measure V) B) /
          ENNReal.ofReal (r n) + ENNReal.ofReal (1 / ((n : ℝ) + 1))) atTop
        (𝓝 (minkowskiContent ν B)) := by
      simpa using hqT.add hslack
    rw [← hlim.limsup_eq]
    exact limsup_le_limsup (Eventually.of_forall fun n => hsel n)

end Recovery

section FiniteTargetRecovery

variable [OpensMeasurableSpace V]

/-- Actual lower-to-upper thickening recovery for a measurable finite-mass target of
finite lower content, under an arbitrary measure on a metric space. Finite neighborhood
mass is proved from the two finiteness premises; original global indicator L1 and upper
contents transfer only at radii whose positive neighborhoods lie in that region. Every
selected thickening has finite mass. No properness or finiteness on bounded sets is needed. -/
theorem exists_upperRecovery_of_measure_lt_top (ν : Measure V) {B : Set V} (hB : MeasurableSet B) (hνB : ν B < ⊤)
    (hcontent : minkowskiContent ν B < ⊤) :
    ∃ s : ℕ → ℝ, (∀ n, 0 < s n) ∧ Tendsto s atTop (𝓝 0) ∧
      (∀ n, MeasurableSet (Metric.thickening (s n) B)) ∧
      (∀ n, ν (Metric.thickening (s n) B) < ⊤) ∧
      Tendsto (fun n => ∫⁻ x, ‖(Metric.thickening (s n) B).indicator (1 : V → ℝ) x -
        B.indicator 1 x‖ₑ ∂ν) atTop (𝓝 0) ∧
      limsup (fun n => upperMinkowskiContent ν (Metric.thickening (s n) B)) atTop ≤
        minkowskiContent ν B := by
  obtain ⟨R, hR, hmass⟩ := exists_measure_thickening_lt_top ν hνB hcontent
  let U := Metric.thickening R B
  have hU : MeasurableSet U := Metric.isOpen_thickening.measurableSet
  have : IsFiniteMeasure (ν.restrict U) := ⟨by simpa [Measure.restrict_apply_univ] using hmass⟩
  have hBsub : B ⊆ U := Metric.self_subset_thickening hR B
  have hlower : minkowskiContent (ν.restrict U) B = minkowskiContent ν B :=
    minkowskiContent_restrict_of_thickening_subset ν hU hR Set.Subset.rfl
  obtain ⟨s, hs, hst, hsm, hL1, hc⟩ := exists_upperRecovery (ν.restrict U) B hB
    (hlower.trans_lt hcontent).ne
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hst.eventually_lt_const (half_pos hR))
  have hsmall : ∀ n : ℕ, s (n + N) < R/2 := fun n => hN _ (by omega)
  have hsub : ∀ n, Metric.thickening (s (n + N)) B ⊆ U := fun n =>
    Metric.thickening_mono (by linarith [hsmall n]) B
  have hupper : ∀ n, upperMinkowskiContent (ν.restrict U) (Metric.thickening (s (n + N)) B) =
      upperMinkowskiContent ν (Metric.thickening (s (n + N)) B) := by
    intro n
    apply upperMinkowskiContent_restrict_of_thickening_subset ν hU (half_pos hR)
    exact (Metric.thickening_thickening_subset (R/2) (s (n + N)) B).trans
      (Metric.thickening_mono (by linarith [hsmall n]) B)
  refine ⟨fun n => s (n + N), fun n => hs (n + N),
    hst.comp (tendsto_add_atTop_nat N), fun n => hsm (n + N),
    fun n => (measure_mono (hsub n)).trans_lt hmass, ?_, ?_⟩
  · have h := hL1.comp (tendsto_add_atTop_nat N)
    have he : (fun n : ℕ => ∫⁻ x, ‖(Metric.thickening (s (n + N)) B).indicator
        (1 : V → ℝ) x - B.indicator 1 x‖ₑ ∂(ν.restrict U)) =
        (fun n : ℕ => ∫⁻ x, ‖(Metric.thickening (s (n + N)) B).indicator
          (1 : V → ℝ) x - B.indicator 1 x‖ₑ ∂ν) :=
      funext fun n => lintegral_enorm_indicator_sub_restrict_eq ν (hsub n) hBsub
    change Tendsto (fun n : ℕ => ∫⁻ x, ‖(Metric.thickening (s (n + N)) B).indicator
      (1 : V → ℝ) x - B.indicator 1 x‖ₑ ∂(ν.restrict U)) atTop (𝓝 0) at h
    rw [he] at h
    exact h
  · calc limsup (fun n => upperMinkowskiContent ν (Metric.thickening (s (n + N)) B)) atTop
        = limsup (fun n => upperMinkowskiContent (ν.restrict U)
            (Metric.thickening (s (n + N)) B)) atTop :=
          congrArg (fun g : ℕ → ℝ≥0∞ => limsup g atTop) (funext fun n => (hupper n).symm)
      _ = limsup (fun n => upperMinkowskiContent (ν.restrict U) (Metric.thickening (s n) B))
          atTop := limsup_nat_add (fun n : ℕ => upperMinkowskiContent (ν.restrict U)
            (Metric.thickening (s n) B)) N
      _ ≤ minkowskiContent (ν.restrict U) B := hc
      _ = _ := hlower


end FiniteTargetRecovery

end FunctionalInequalities.KLS.Isoperimetry
