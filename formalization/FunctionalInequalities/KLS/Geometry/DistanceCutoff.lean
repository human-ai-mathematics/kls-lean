import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Distance cutoffs and their gradient integral

Hole-free coordinate-space module for the distance cutoff `w_r = (1 - d(·, B) / r)₊` used by the
reverse Cheeger comparison.  It owns `Isoperimetry.distanceCutoff` with its range, Lipschitz and
boundary-value lemmas, the `L¹(ν)` convergence `tendsto_distanceCutoff_indicator` to the indicator
of `B`, and the gradient integral estimate

`∫ ‖∇w_r‖ dν ≤ (ν(B^r) - ν(closure B)) / r`,

`lintegral_enorm_gradient_distanceCutoff_le`, with the **closure** of `B` on the right, which is
sharper than the Blueprint's `ν(B)`.

The estimate is pointwise, not almost-everywhere: `w_r` attains its global maximum `1` on
`closure B` and its global minimum `0` outside the open thickening, so
`IsLocalMax.fderiv_eq_zero` and `IsLocalMin.fderiv_eq_zero` make the gradient vanish **at every
point** of those two sets, the level sets `{d = 0}` and `{d = r}` included; on the open annulus
`B^r ∖ closure B` the Lipschitz constant `1/r` bounds the gradient through
`norm_fderiv_le_of_lipschitz`.  Neither of those Mathlib lemmas needs a differentiability
hypothesis, because `fderiv` and `gradient` are defined to be zero at points of
non-differentiability.  Consequently the proof uses no Rademacher theorem, no Lebesgue density
theorem, no general "the gradient vanishes almost everywhere on a level set" lemma, and no
absolute continuity: the Haar measure `m` and the hypothesis `hac` of
`lintegral_enorm_gradient_distanceCutoff_le` are kept because they are part of the published
interface, but the proof does not use them.  That convention about non-differentiability points is
local to this estimate and is not a comparison result for singular laws.

`B` is arbitrary: neither nonempty, nor measurable, nor closed, nor bounded, and no null boundary
is assumed.  The empty set is a separate branch: Mathlib's `Metric.infDist x ∅ = 0` makes
`distanceCutoff ∅ r` the constant `1`, not `0`, while `Metric.thickening r ∅ = ∅`, so both sides
vanish.  The module imports no local module at all, only Mathlib.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace FunctionalInequalities.KLS

universe u

namespace Isoperimetry

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]

/-! ### Distance cutoffs -/

/-- The distance cutoff `w_r = (1 - d(·, B) / r)₊`: equal to `1` on the closure of `B`, to `0`
outside the open `r`-thickening, and `1/r`-Lipschitz. -/
def distanceCutoff (B : Set V) (r : ℝ) (x : V) : ℝ :=
  max 0 (1 - Metric.infDist x B / r)

omit [InnerProductSpace ℝ V] [CompleteSpace V] [MeasurableSpace V] [BorelSpace V]
  [SecondCountableTopology V] [FiniteDimensional ℝ V] in
/-- The cutoff takes values in `[0, 1]`. -/
theorem distanceCutoff_mem_Icc (B : Set V) {r : ℝ} (hr : 0 < r) (x : V) :
    distanceCutoff B r x ∈ Set.Icc (0 : ℝ) 1 := by
  unfold distanceCutoff
  refine ⟨le_max_left _ _, max_le (by norm_num) ?_⟩
  have h0 : 0 ≤ Metric.infDist x B / r := div_nonneg Metric.infDist_nonneg hr.le
  linarith

omit [InnerProductSpace ℝ V] [CompleteSpace V] [MeasurableSpace V] [BorelSpace V]
  [SecondCountableTopology V] [FiniteDimensional ℝ V] in
/-- The cutoff is `1/r`-Lipschitz. -/
theorem lipschitzWith_distanceCutoff (B : Set V) {r : ℝ} (hr : 0 < r) :
    LipschitzWith (Real.toNNReal r⁻¹) (distanceCutoff B r) := by
  apply LipschitzWith.of_dist_le' (K := r⁻¹)
  intro x y
  unfold distanceCutoff
  have hinf : dist (Metric.infDist x B) (Metric.infDist y B) ≤ dist x y := by
    simpa using (Metric.lipschitz_infDist_pt (s := B)).dist_le_mul x y
  rw [Real.dist_eq] at hinf
  have hstep : |max 0 (1 - Metric.infDist x B / r) - max 0 (1 - Metric.infDist y B / r)|
      ≤ |(1 - Metric.infDist x B / r) - (1 - Metric.infDist y B / r)| := by
    rw [max_comm 0 (1 - Metric.infDist x B / r), max_comm 0 (1 - Metric.infDist y B / r)]
    exact abs_max_sub_max_le_abs _ _ 0
  have heq : (1 - Metric.infDist x B / r) - (1 - Metric.infDist y B / r)
      = -(Metric.infDist x B - Metric.infDist y B) / r := by ring
  rw [Real.dist_eq]
  refine hstep.trans ?_
  rw [heq, abs_div, abs_neg, abs_of_pos hr, div_le_iff₀ hr]
  calc |Metric.infDist x B - Metric.infDist y B| ≤ dist x y := hinf
    _ = r⁻¹ * dist x y * r := by field_simp

omit [InnerProductSpace ℝ V] [CompleteSpace V] [MeasurableSpace V] [BorelSpace V]
  [SecondCountableTopology V] [FiniteDimensional ℝ V] in
/-- The cutoff equals `1` on the closure of a nonempty `B`. -/
theorem distanceCutoff_eq_one_of_mem_closure {B : Set V} (hB : B.Nonempty) {r : ℝ} (_hr : 0 < r)
    {x : V} (hx : x ∈ closure B) :
    distanceCutoff B r x = 1 := by
  unfold distanceCutoff
  have h0 : Metric.infDist x B = 0 := (Metric.mem_closure_iff_infDist_zero hB).mp hx
  rw [h0]
  simp

omit [InnerProductSpace ℝ V] [CompleteSpace V] [MeasurableSpace V] [BorelSpace V]
  [SecondCountableTopology V] [FiniteDimensional ℝ V] in
/-- The cutoff vanishes outside the open `r`-thickening of a nonempty `B`.  Nonemptiness is
needed: `Metric.thickening r ∅ = ∅` makes the hypothesis vacuous for every `x`, while Mathlib's
convention `Metric.infDist x ∅ = 0` gives `distanceCutoff ∅ r x = 1`. -/
theorem distanceCutoff_eq_zero_of_notMem_thickening {B : Set V} (hB : B.Nonempty)
    {r : ℝ} (hr : 0 < r) {x : V} (hx : x ∉ Metric.thickening r B) :
    distanceCutoff B r x = 0 := by
  unfold distanceCutoff
  rw [Metric.mem_thickening_iff_infDist_lt hB, not_lt] at hx
  refine max_eq_left ?_
  rw [sub_nonpos, le_div_iff₀ hr, one_mul]
  exact hx

omit [InnerProductSpace ℝ V] [CompleteSpace V] [SecondCountableTopology V]
  [FiniteDimensional ℝ V] in
/-- When `B` is measurable and its closure carries no extra mass, the cutoffs converge to the
indicator in `L¹(ν)` as `r ↓ 0`.  Measurability is needed to identify the mass of the annulus
`B^r \ B` with `ν(B^r) − ν(B)`. -/
theorem tendsto_distanceCutoff_indicator (ν : ProbabilityMeasure V) {B : Set V}
    (hB : B.Nonempty) (hBm : MeasurableSet B)
    (hcl : (ν : Measure V) (closure B) = (ν : Measure V) B) :
    Tendsto (fun r : ℝ ↦ ∫⁻ x, ‖distanceCutoff B r x - B.indicator 1 x‖ₑ ∂(ν : Measure V))
      (𝓝[>] 0) (𝓝 0) := by
  -- pointwise bound by the indicator of the annulus
  have hbound : ∀ r : ℝ, 0 < r →
      ∫⁻ x, ‖distanceCutoff B r x - B.indicator 1 x‖ₑ ∂(ν : Measure V) ≤
        (ν : Measure V) (Metric.thickening r B) - (ν : Measure V) B := by
    intro r hr
    have hsub : B ⊆ Metric.thickening r B := Metric.self_subset_thickening hr B
    have hdiff : (ν : Measure V) (Metric.thickening r B \ B) =
        (ν : Measure V) (Metric.thickening r B) - (ν : Measure V) B :=
      measure_sdiff hsub hBm.nullMeasurableSet (measure_ne_top _ _)
    rw [← hdiff, ← lintegral_indicator_one (Metric.isOpen_thickening.measurableSet.diff hBm)]
    refine lintegral_mono fun x ↦ ?_
    by_cases hxB : x ∈ B
    · rw [distanceCutoff_eq_one_of_mem_closure hB hr (subset_closure hxB),
        Set.indicator_of_mem hxB]
      simp
    · by_cases hxt : x ∈ Metric.thickening r B
      · rw [Set.indicator_of_notMem hxB, Set.indicator_of_mem (Set.mem_sdiff_of_mem hxt hxB)]
        obtain ⟨h0, h1⟩ := distanceCutoff_mem_Icc B hr x
        rw [sub_zero, Real.enorm_eq_ofReal_abs, abs_of_nonneg h0]
        simpa using ENNReal.ofReal_le_one.2 h1
      · rw [distanceCutoff_eq_zero_of_notMem_thickening hB hr hxt,
          Set.indicator_of_notMem hxB]
        simp
  -- the annulus mass tends to zero
  have hthin : Tendsto
      (fun r : ℝ ↦ (ν : Measure V) (Metric.thickening r B) - (ν : Measure V) B) (𝓝[>] 0) (𝓝 0) := by
    rw [ENNReal.tendsto_nhds_zero]
    intro ε hε
    -- continuity from above along the radii `1 / (n + 1)`
    have hmono : Antitone fun n : ℕ ↦ Metric.thickening (1 / ((n : ℝ) + 1)) B := by
      intro a b hab
      refine Metric.thickening_mono ?_ B
      have ha : (0 : ℝ) < (a : ℝ) + 1 := by positivity
      have hb : (0 : ℝ) < (b : ℝ) + 1 := by positivity
      rw [div_le_div_iff₀ hb ha]
      have : (a : ℝ) ≤ (b : ℝ) := Nat.cast_le.2 hab
      linarith
    have hiInter : ⋂ n : ℕ, Metric.thickening (1 / ((n : ℝ) + 1)) B = closure B := by
      refine Set.Subset.antisymm ?_ ?_
      · rw [Metric.closure_eq_iInter_thickening B]
        refine Set.subset_iInter fun δ ↦ Set.subset_iInter fun hδ ↦ ?_
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
        exact (Set.iInter_subset _ n).trans (Metric.thickening_mono hn.le B)
      · refine Set.subset_iInter fun n ↦ ?_
        refine Metric.closure_subset_thickening ?_ B
        positivity
    have htend := tendsto_measure_iInter_atTop (μ := (ν : Measure V))
      (s := fun n : ℕ ↦ Metric.thickening (1 / ((n : ℝ) + 1)) B)
      (fun n ↦ Metric.isOpen_thickening.measurableSet.nullMeasurableSet) hmono
      ⟨0, measure_ne_top _ _⟩
    rw [hiInter, hcl] at htend
    have hεpos : (0 : ENNReal) < ε := hε
    obtain ⟨N, hN⟩ := (ENNReal.tendsto_atTop (measure_ne_top (ν : Measure V) B)).1 htend ε hεpos
    have hr0 : (0 : ℝ) < 1 / ((N : ℝ) + 1) := by positivity
    filter_upwards [Ioo_mem_nhdsGT hr0] with r hr
    have hrt : Metric.thickening r B ⊆ Metric.thickening (1 / ((N : ℝ) + 1)) B :=
      Metric.thickening_mono hr.2.le B
    have hle : (ν : Measure V) (Metric.thickening r B) ≤ ε + (ν : Measure V) B := by
      refine (measure_mono hrt).trans ?_
      have hNN := (hN N le_rfl).2
      simpa [Function.comp, add_comm] using hNN
    exact tsub_le_iff_right.2 hle
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hthin ?_ ?_
  · filter_upwards with r using zero_le
  · filter_upwards [self_mem_nhdsWithin] with r hr using hbound r hr

/-! ### The gradient integral of the cutoff -/

-- `m`, its Haar instance and `hac` are part of the published interface of this estimate and are
-- kept verbatim; the pointwise route below needs no absolute continuity, so `hac` is unused, and
-- `FiniteDimensional`/`SecondCountableTopology` are unused section variables.  Both linters are
-- silenced for this declaration only, rather than the statement being changed.
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
/-- The gradient of the cutoff vanishes at every point of its two constant-value sets and is
bounded by `1/r` on the open annulus `B^r ∖ closure B`, so
`∫ ‖∇w_r‖ dν ≤ (ν(B^r) - ν(closure B)) / r`.  This sharpens the Blueprint's
`(ν(B^r) - ν(B)) / r`. -/
theorem lintegral_enorm_gradient_distanceCutoff_le (ν : ProbabilityMeasure V) (m : Measure V)
    [m.IsAddHaarMeasure] (hac : (ν : Measure V) ≪ m) (B : Set V) {r : ℝ} (hr : 0 < r) :
    ∫⁻ x, ‖gradient (distanceCutoff B r) x‖ₑ ∂(ν : Measure V) ≤
      ((ν : Measure V) (Metric.thickening r B) - (ν : Measure V) (closure B)) /
        ENNReal.ofReal r := by
  rcases Set.eq_empty_or_nonempty B with rfl | hB
  · -- `Metric.infDist x ∅ = 0`, so the cutoff is the constant `1` and its gradient vanishes.
    have hconst : distanceCutoff (∅ : Set V) r = fun _ : V ↦ (1 : ℝ) := by
      funext x
      simp [distanceCutoff]
    rw [hconst]
    simp [gradient_fun_const]
  -- The open annulus on which the cutoff is not locally constant.
  set A : Set V := Metric.thickening r B \ closure B with hA
  have hAmeas : MeasurableSet A :=
    Metric.isOpen_thickening.measurableSet.diff isClosed_closure.measurableSet
  have hKcoe : ((Real.toNNReal r⁻¹ : ℝ≥0) : ℝ) = r⁻¹ :=
    Real.coe_toNNReal _ (inv_nonneg.mpr hr.le)
  have hpt : ∀ x : V, ‖gradient (distanceCutoff B r) x‖ₑ ≤
      A.indicator (fun _ : V ↦ ENNReal.ofReal r⁻¹) x := by
    intro x
    by_cases hxA : x ∈ A
    · rw [Set.indicator_of_mem hxA]
      have hnorm : ‖gradient (distanceCutoff B r) x‖ ≤ r⁻¹ := by
        have h := norm_fderiv_le_of_lipschitz ℝ (lipschitzWith_distanceCutoff B hr) (x₀ := x)
        rw [hKcoe] at h
        simpa only [gradient, LinearIsometryEquiv.norm_map] using h
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal hnorm
    · -- Outside the annulus the cutoff attains a global extremum, so its gradient is zero.
      have hzero : gradient (distanceCutoff B r) x = 0 := by
        by_cases hxt : x ∈ Metric.thickening r B
        · -- Then `x` lies in the closure, where the cutoff is `1`, its global maximum.
          have hxc : x ∈ closure B := by
            by_contra hc
            exact hxA (Set.mem_sdiff_of_mem hxt hc)
          have hmax : IsLocalMax (distanceCutoff B r) x := by
            refine Filter.Eventually.of_forall fun y ↦ ?_
            rw [distanceCutoff_eq_one_of_mem_closure hB hr hxc]
            exact (distanceCutoff_mem_Icc B hr y).2
          simp only [gradient, hmax.fderiv_eq_zero, map_zero]
        · -- Outside the open thickening the cutoff is `0`, its global minimum.
          have hmin : IsLocalMin (distanceCutoff B r) x := by
            refine Filter.Eventually.of_forall fun y ↦ ?_
            rw [distanceCutoff_eq_zero_of_notMem_thickening hB hr hxt]
            exact (distanceCutoff_mem_Icc B hr y).1
          simp only [gradient, hmin.fderiv_eq_zero, map_zero]
      rw [hzero]
      simp
  have hdiff : (ν : Measure V) A =
      (ν : Measure V) (Metric.thickening r B) - (ν : Measure V) (closure B) :=
    measure_sdiff (Metric.closure_subset_thickening hr B) isClosed_closure.nullMeasurableSet
      (measure_ne_top _ _)
  calc ∫⁻ x, ‖gradient (distanceCutoff B r) x‖ₑ ∂(ν : Measure V)
      ≤ ∫⁻ x, A.indicator (fun _ : V ↦ ENNReal.ofReal r⁻¹) x ∂(ν : Measure V) :=
        lintegral_mono hpt
    _ = ENNReal.ofReal r⁻¹ * (ν : Measure V) A := lintegral_indicator_const hAmeas _
    _ = ((ν : Measure V) (Metric.thickening r B) - (ν : Measure V) (closure B)) /
        ENNReal.ofReal r := by
        rw [hdiff, ENNReal.ofReal_inv_of_pos hr, ← ENNReal.div_eq_inv_mul]

end Isoperimetry

end FunctionalInequalities.KLS
