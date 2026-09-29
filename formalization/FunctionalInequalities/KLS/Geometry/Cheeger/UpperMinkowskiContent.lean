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
lossless for a probability law (`ofReal_thickeningMass`, `measure_thickening_sub_div_eq_ofReal`).

Scope: probability laws on a normed additive group with a measurable structure, as for the lower
content, and every set `B` (the empty set and sets whose thickenings carry no extra mass are
covered explicitly).  Nothing is assumed or claimed about absolute continuity of the radius mass:
jumps and singular variation remain possible, and almost-everywhere differentiability is exactly
what the monotone differentiation theorem gives.  This module stops before any integrated
upper-content bound and before the recovery/relaxation identities between the lower and upper
contents.
-/

noncomputable section

open MeasureTheory Filter Metric Set
open scoped ENNReal Topology

namespace FunctionalInequalities.KLS.Isoperimetry

variable {V : Type*} [NormedAddCommGroup V] [MeasurableSpace V]

/-! ### Upper Minkowski content -/

/-- Upper Minkowski content `limsup_{r ↓ 0} (ν(B^r) - ν(B)) / r`, with open thickenings and
`ENNReal` truncated subtraction: the `limsup` of the radius quotient whose `liminf` is
`minkowskiContent`. -/
def upperMinkowskiContent (ν : ProbabilityMeasure V) (B : Set V) : ℝ≥0∞ :=
  limsup (fun r : ℝ ↦
    ((ν : Measure V) (Metric.thickening r B) - (ν : Measure V) B) / ENNReal.ofReal r) (𝓝[>] 0)

/-- The lower content is at most the upper content: `liminf ≤ limsup` along the nontrivial
filter `𝓝[>] 0`. -/
theorem minkowskiContent_le_upperMinkowskiContent (ν : ProbabilityMeasure V) (B : Set V) :
    minkowskiContent ν B ≤ upperMinkowskiContent ν B :=
  liminf_le_limsup

/-- Zero mass increments: if no positive thickening carries more mass than `B`, the upper content
vanishes (every quotient is `0 / ENNReal.ofReal r = 0`). -/
theorem upperMinkowskiContent_eq_zero_of_forall_measure_thickening_le (ν : ProbabilityMeasure V)
    {B : Set V} (h : ∀ r : ℝ, 0 < r → (ν : Measure V) (Metric.thickening r B) ≤ (ν : Measure V) B) :
    upperMinkowskiContent ν B = 0 := by
  refine le_antisymm ?_ bot_le
  unfold upperMinkowskiContent
  refine limsup_le_of_le (by isBoundedDefault) ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  rw [tsub_eq_zero_of_le (h r hr), ENNReal.zero_div]

/-- The empty set has zero upper content. -/
theorem upperMinkowskiContent_empty (ν : ProbabilityMeasure V) :
    upperMinkowskiContent ν (∅ : Set V) = 0 :=
  upperMinkowskiContent_eq_zero_of_forall_measure_thickening_le ν fun r _ => by
    simp [Metric.thickening_empty]

/-- The empty set has zero lower content as well. -/
theorem minkowskiContent_empty (ν : ProbabilityMeasure V) :
    minkowskiContent ν (∅ : Set V) = 0 :=
  le_antisymm
    ((minkowskiContent_le_upperMinkowskiContent ν ∅).trans_eq (upperMinkowskiContent_empty ν))
    bot_le

/-! ### Radius mass of thickenings -/

/-- Real mass `ν(B^s)` of the open `s`-thickening of `B`. -/
def thickeningMass (ν : ProbabilityMeasure V) (B : Set V) (s : ℝ) : ℝ :=
  ((ν : Measure V) (Metric.thickening s B)).toReal

theorem thickeningMass_nonneg (ν : ProbabilityMeasure V) (B : Set V) (s : ℝ) :
    0 ≤ thickeningMass ν B s :=
  ENNReal.toReal_nonneg

theorem thickeningMass_le_one (ν : ProbabilityMeasure V) (B : Set V) (s : ℝ) :
    thickeningMass ν B s ≤ 1 :=
  ENNReal.toReal_le_of_le_ofReal zero_le_one (by rw [ENNReal.ofReal_one]; exact prob_le_one)

/-- The real radius mass converts back to the `ℝ≥0∞` mass without loss. -/
theorem ofReal_thickeningMass (ν : ProbabilityMeasure V) (B : Set V) (s : ℝ) :
    ENNReal.ofReal (thickeningMass ν B s) = (ν : Measure V) (Metric.thickening s B) :=
  ENNReal.ofReal_toReal (measure_ne_top _ _)

/-- The radius mass is monotone: thickenings grow with the radius. -/
theorem monotone_thickeningMass (ν : ProbabilityMeasure V) (B : Set V) :
    Monotone (thickeningMass ν B) := fun _ _ hst =>
  ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Metric.thickening_mono hst B))

/-- Nonpositive radii give the empty thickening, hence zero mass. -/
theorem thickeningMass_of_nonpos (ν : ProbabilityMeasure V) (B : Set V) {s : ℝ} (hs : s ≤ 0) :
    thickeningMass ν B s = 0 := by
  simp [thickeningMass, Metric.thickening_of_nonpos hs]

theorem thickeningMass_empty (ν : ProbabilityMeasure V) (s : ℝ) :
    thickeningMass ν (∅ : Set V) s = 0 := by
  simp [thickeningMass]

/-- For a positive radius increment `t`, the `ℝ≥0∞` increment quotient of the thickening masses
equals `ENNReal.ofReal` of the real right difference quotient of the radius mass. -/
theorem measure_thickening_sub_div_eq_ofReal (ν : ProbabilityMeasure V) (B : Set V) {s t : ℝ}
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
theorem upperMinkowskiContent_thickening_le_of_hasDerivAt (ν : ProbabilityMeasure V) (B : Set V)
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
theorem upperMinkowskiContent_thickening_le_deriv_of_differentiableAt (ν : ProbabilityMeasure V)
    (B : Set V) {s : ℝ} (hs : DifferentiableAt ℝ (thickeningMass ν B) s) :
    upperMinkowskiContent ν (Metric.thickening s B) ≤
      ENNReal.ofReal (deriv (thickeningMass ν B) s) :=
  upperMinkowskiContent_thickening_le_of_hasDerivAt ν B hs.hasDerivAt

/-- The derivative of the monotone radius mass is nonnegative (`deriv` is `0` where the mass is
not differentiable). -/
theorem deriv_thickeningMass_nonneg (ν : ProbabilityMeasure V) (B : Set V) (s : ℝ) :
    0 ≤ deriv (thickeningMass ν B) s :=
  (monotone_thickeningMass ν B).deriv_nonneg

theorem nonneg_of_hasDerivAt_thickeningMass (ν : ProbabilityMeasure V) (B : Set V) {s d : ℝ}
    (hd : HasDerivAt (thickeningMass ν B) d s) : 0 ≤ d := by
  rw [← hd.deriv]
  exact deriv_thickeningMass_nonneg ν B s

/-! ### Almost-everywhere differentiability of the radius mass -/

/-- The radius mass is differentiable at Lebesgue-almost every radius, by the monotone
differentiation theorem.  Only differentiability is claimed: the radius mass may still jump or
have singular variation. -/
theorem ae_differentiableAt_thickeningMass (ν : ProbabilityMeasure V) (B : Set V) :
    ∀ᵐ s ∂(volume : Measure ℝ), DifferentiableAt ℝ (thickeningMass ν B) s :=
  (monotone_thickeningMass ν B).ae_differentiableAt

/-- At Lebesgue-almost every radius the upper content of the thickening is at most the derivative
of the radius mass (for `s ≤ 0` the thickening is empty). -/
theorem ae_upperMinkowskiContent_thickening_le_deriv (ν : ProbabilityMeasure V) (B : Set V) :
    ∀ᵐ s ∂(volume : Measure ℝ), upperMinkowskiContent ν (Metric.thickening s B) ≤
      ENNReal.ofReal (deriv (thickeningMass ν B) s) := by
  filter_upwards [ae_differentiableAt_thickeningMass ν B] with s hs
  exact upperMinkowskiContent_thickening_le_deriv_of_differentiableAt ν B hs

/-- The same at Lebesgue-almost every positive radius, with the positivity and the
differentiability witness recorded. -/
theorem ae_restrict_Ioi_upperMinkowskiContent_thickening_le_deriv (ν : ProbabilityMeasure V)
    (B : Set V) :
    ∀ᵐ s ∂((volume : Measure ℝ).restrict (Ioi 0)),
      0 < s ∧ DifferentiableAt ℝ (thickeningMass ν B) s ∧
        upperMinkowskiContent ν (Metric.thickening s B) ≤
          ENNReal.ofReal (deriv (thickeningMass ν B) s) := by
  filter_upwards [ae_restrict_mem (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ))),
    ae_restrict_of_ae (ae_differentiableAt_thickeningMass ν B)] with s hs hd
  exact ⟨hs, hd, upperMinkowskiContent_thickening_le_deriv_of_differentiableAt ν B hd⟩

end FunctionalInequalities.KLS.Isoperimetry
