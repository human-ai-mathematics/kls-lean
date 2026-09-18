import FunctionalInequalities.KLS.Geometry.CheegerEquality
import FunctionalInequalities.KLS.LogConcave.Line.Hazard

/-!
# One-dimensional isoperimetry for log-concave laws: `h_M(ν) ≥ 2 ρ(m)`

Source: Blueprint Stage 1 of `research/decisions/2026-09-19-buser-route.md`, obligations `Q1`,
`Q1'` and `Q2` of `research/audits/BuserRouteStatements.lean`.  Read
`LineDensity.le_two_mul` (the density is at most twice its value at a median), then the
boundary-charge lemmas `LineDensity.mul_measure_Iio_diff_le`, `mul_measure_Ioi_diff_le`,
`mul_measure_compl_le`, then the smooth-domain bound
`LineDensity.mul_min_le_relativePerimeter` and its infimum form
`LineDensity.two_mul_le_minkowskiConstant`.

On the real line the surface measure of the relative-perimeter chain is the zero-dimensional
Hausdorff measure, so a boundary integral is bounded below by the density at any single boundary
point lying in the interior of the support (`LineDensity.ofReal_le_setLIntegral`).  For an open
set `W` containing a median `m`, the supremum `a` of the complement to the left of `m` and the
infimum `b` of the complement to the right are boundary points with `(a, b) ⊆ W`, so the
hazard-rate median bounds `2 ρ(m) F(a) ≤ ρ(a)` and `2 ρ(m) (1 - F(b)) ≤ ρ(b)` give
`2 ρ(m) · ν(Wᶜ) ≤ ρ(a) + ρ(b)`.  For a smooth domain `U` there are three cases: the median lies in
`U`, on its frontier, or outside its closure; in the first case the bound is applied to `U`, in
the third to the complement of the closure (whose frontier is contained in that of `U`), and in
the second the single boundary point `m` already carries `ρ(m) ≥ 2 ρ(m) · min {ν U, 1 - ν U}`.
The certified equality `h_M = h_S` then turns the smooth-domain bound into the bound on the
Minkowski Cheeger infimum.

For `Q2` the supporting exponential at the median with slope `k` has `|k| ≤ 2 ρ(m)`, because the
half mass on the side where it decays is `ρ(m) / |k|`; the supporting-line bound
`ρ ≤ ρ(m) + k (F - 1/2)` of the hazard module then gives `ρ ≤ 2 ρ(m)` on the interior of the
support, and log-concavity together with the vanishing of `ρ` off that interior extends the bound
to every point of the line.

No Poincaré inequality and no Buser-type comparison is asserted here.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open FunctionalInequalities.Probability.Line (cdf)
open scoped ENNReal NNReal

namespace FunctionalInequalities.KLS

/-! ### The surface measure of the line -/

/-- On the line the surface measure of the relative-perimeter chain is `ℋ^0`: the normalizing
factor `ω_0 / 2^0` equals `1 / Γ(1) = 1`. -/
theorem surfaceMeasure_real : surfaceMeasure ℝ = (μH[(0 : ℝ)] : Measure ℝ) := by
  unfold surfaceMeasure hausdorffNormalized unitBallVolume
  norm_num [Real.Gamma_one]

/-- The surface measure of the line counts points. -/
theorem surfaceMeasure_real_singleton (a : ℝ) : surfaceMeasure ℝ {a} = 1 := by
  rw [surfaceMeasure_real]
  exact MeasureTheory.Measure.hausdorffMeasure_zero_singleton a

/-- The distribution function in extended form. -/
theorem measure_Iic_eq_ofReal_cdf (μ : ProbabilityMeasure ℝ) (a : ℝ) :
    (μ : Measure ℝ) (Iic a) = ENNReal.ofReal (cdf μ a) := by
  rw [Probability.Line.cdf, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]

/-- A finite measure of a set in extended form. -/
theorem measure_eq_ofReal_measureReal (μ : ProbabilityMeasure ℝ) (S : Set ℝ) :
    (μ : Measure ℝ) S = ENNReal.ofReal ((μ : Measure ℝ).real S) := by
  rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]

namespace LineDensity

variable {μ : ProbabilityMeasure ℝ} (d : LineDensity μ)

/-! ### Boundary integrals on the line -/

/-- A single boundary point already charges a boundary integral: on the line the surface measure
gives every singleton unit mass. -/
theorem ofReal_le_setLIntegral {D : Set ℝ} {a : ℝ} (ha : a ∈ D) :
    ENNReal.ofReal (d.ρ a) ≤ ∫⁻ x in D, ENNReal.ofReal (d.ρ x) ∂(surfaceMeasure ℝ) := by
  have hbound : ∀ x, ({a} : Set ℝ).indicator (fun _ ↦ ENNReal.ofReal (d.ρ a)) x ≤
      ENNReal.ofReal (d.ρ x) := by
    intro x
    by_cases hx : x = a
    · simp [hx]
    · rw [Set.indicator_of_notMem (by simpa using hx)]
      exact zero_le
  calc ENNReal.ofReal (d.ρ a)
      = ∫⁻ x in D, ({a} : Set ℝ).indicator (fun _ ↦ ENNReal.ofReal (d.ρ a)) x
          ∂(surfaceMeasure ℝ) := by
        rw [lintegral_indicator_const (measurableSet_singleton a),
          Measure.restrict_apply (measurableSet_singleton a),
          Set.inter_eq_self_of_subset_left (Set.singleton_subset_iff.mpr ha),
          surfaceMeasure_real_singleton, mul_one]
    _ ≤ _ := lintegral_mono hbound

include d in
/-- A law with a Lebesgue density gives no mass to points. -/
theorem measure_singleton (b : ℝ) : (μ : Measure ℝ) {b} = 0 := by
  rw [d.withDensity_eq, withDensity_apply _ (measurableSet_singleton b)]
  exact setLIntegral_measure_zero _ _ (by simp)

/-! ### Interior of the positivity set -/

/-- Interior points of the positivity set of the density lie in the interior of the support: on a
neighbourhood contained in the positivity set the law has positive mass. -/
theorem interior_pos_subset : interior {y | 0 < d.ρ y} ⊆ interior (μ : Measure ℝ).support := by
  refine interior_maximal ?_ isOpen_interior
  intro x hx
  by_contra hxs
  obtain ⟨N, hN, hN0⟩ := Measure.notMem_support_iff_exists.mp hxs
  obtain ⟨O, hON, hO, hxO⟩ := mem_nhds_iff.mp hN
  set W := O ∩ interior {y | 0 < d.ρ y} with hW
  have hWopen : IsOpen W := hO.inter isOpen_interior
  have hxW : x ∈ W := ⟨hxO, hx⟩
  have hW0 : (μ : Measure ℝ) W = 0 := measure_mono_null (fun z hz ↦ hON hz.1) hN0
  rw [d.withDensity_eq, withDensity_apply _ hWopen.measurableSet,
    setLIntegral_eq_zero_iff' hWopen.measurableSet d.measurable.ennreal_ofReal.aemeasurable] at hW0
  have hvol : (volume : Measure ℝ) W = 0 := by
    have hsub : W ⊆ {z : ℝ | ¬ (z ∈ W → ENNReal.ofReal (d.ρ z) = 0)} := by
      intro z hz
      simp only [mem_ofPred_eq, not_forall]
      refine ⟨hz, ?_⟩
      have hz' : z ∈ {y : ℝ | 0 < d.ρ y} := interior_subset hz.2
      have hpos : 0 < d.ρ z := hz'
      simpa [ENNReal.ofReal_eq_zero] using not_le.mpr hpos
    exact measure_mono_null hsub (ae_iff.mp hW0)
  exact absurd hvol (hWopen.measure_pos volume ⟨x, hxW⟩).ne'

/-! ### `Q2`: the density is at most twice its value at a median -/

section Median

variable (hμ : LogConcave μ) (hi : (interior (μ : Measure ℝ).support).Nonempty)
  {m : ℝ} (hm : cdf μ m = 1 / 2)

section Supergradient

variable {k : ℝ}
  (hk : ∀ s ∈ interior (μ : Measure ℝ).support, d.ρ s ≤ d.ρ m * Real.exp (k * (s - m)))
include hμ hi hm hk

/-- A supporting slope of the logarithm of the density at a median is bounded by twice the
density there: the half mass on the side where the supporting exponential decays is at most
`ρ(m) / |k|`. -/
theorem abs_le_two_mul : |k| ≤ 2 * d.ρ m := by
  have hc : 0 < d.ρ m := d.pos (median_mem hμ hi hm)
  have hae : ∀ᵐ s ∂(volume : Measure ℝ), d.ρ s ≤ d.ρ m * Real.exp (k * (s - m)) := by
    filter_upwards [d.ae_eq_zero_of_not_mem_interior_support hμ hi] with s hs
    by_cases hsΩ : s ∈ interior (μ : Measure ℝ).support
    · exact hk s hsΩ
    · rw [hs hsΩ]
      positivity
  rcases lt_trichotomy k 0 with hk0 | hk0 | hk0
  · have hhalf : (1 : ℝ) / 2 = ∫ s in Ioi m, d.ρ s := by
      rw [← d.measureReal_eq_setIntegral measurableSet_Ioi, Probability.Line.measureReal_Ioi, hm]
      norm_num
    have hle : ∫ s in Ioi m, d.ρ s ≤ ∫ s in Ioi m, d.ρ m * Real.exp (k * (s - m)) :=
      integral_mono_ae d.integrable.integrableOn
        (Probability.Line.integrableOn_exp_affine_Ioi hc.le hk0 m m)
        (ae_restrict_of_ae hae)
    rw [Probability.Line.integral_exp_affine_Ioi hc.le hk0 m m] at hle
    simp only [sub_self, mul_zero, Real.exp_zero, mul_one] at hle
    have h2 : (1 : ℝ) / 2 ≤ -(d.ρ m / k) := by linarith [hhalf ▸ hle]
    have hmul := mul_le_mul_of_nonneg_right h2 (neg_nonneg.mpr hk0.le)
    have hcancel : -(d.ρ m / k) * -k = d.ρ m := by
      rw [neg_mul_neg, div_mul_cancel₀ _ hk0.ne]
    rw [hcancel] at hmul
    rw [abs_of_neg hk0]
    linarith
  · rw [hk0, abs_zero]
    linarith
  · have hhalf : (1 : ℝ) / 2 = ∫ s in Iic m, d.ρ s := by
      rw [← d.measureReal_eq_setIntegral measurableSet_Iic]
      exact hm.symm
    have hle : ∫ s in Iic m, d.ρ s ≤ ∫ s in Iic m, d.ρ m * Real.exp (k * (s - m)) :=
      integral_mono_ae d.integrable.integrableOn
        (Probability.Line.integrableOn_exp_affine_Iic hc.le hk0 m m)
        (ae_restrict_of_ae hae)
    rw [Probability.Line.integral_exp_affine_Iic hc.le hk0 m m] at hle
    simp only [sub_self, mul_zero, Real.exp_zero, mul_one] at hle
    have h2 : (1 : ℝ) / 2 ≤ d.ρ m / k := by linarith [hhalf ▸ hle]
    have hmul := mul_le_mul_of_nonneg_right h2 hk0.le
    have hcancel : d.ρ m / k * k = d.ρ m := div_mul_cancel₀ _ hk0.ne'
    rw [hcancel] at hmul
    rw [abs_of_pos hk0]
    linarith

end Supergradient

include hμ hi hm

/-- Blueprint Stage 1 `Q2`: the density of a log-concave law on the line is at most twice its
value at a median, at every point of the line. -/
theorem le_two_mul (x : ℝ) : d.ρ x ≤ 2 * d.ρ m := by
  have hmΩ := median_mem hμ hi hm
  have hc : 0 < d.ρ m := d.pos hmΩ
  obtain ⟨k, hk⟩ := d.exists_supergradient hμ hmΩ
  have habs := d.abs_le_two_mul hμ hi hm hk
  have hΩ : ∀ y ∈ interior (μ : Measure ℝ).support, d.ρ y ≤ 2 * d.ρ m := by
    intro y hy
    have h := d.le_add_mul_cdf_sub hμ hi hm hk hy
    have hF0 := Probability.Line.cdf_nonneg μ y
    have hF1 := Probability.Line.cdf_le_one μ y
    have hkb : k * (cdf μ y - 1 / 2) ≤ |k| * |cdf μ y - 1 / 2| := by
      calc k * (cdf μ y - 1 / 2) ≤ |k * (cdf μ y - 1 / 2)| := le_abs_self _
        _ = |k| * |cdf μ y - 1 / 2| := abs_mul _ _
    have habs2 : |cdf μ y - 1 / 2| ≤ 1 / 2 := by
      rw [abs_le]; constructor <;> linarith
    nlinarith [abs_nonneg k, abs_nonneg (cdf μ y - 1 / 2)]
  by_cases hx : x ∈ interior (μ : Measure ℝ).support
  · exact hΩ x hx
  rcases le_or_gt (d.ρ x) 0 with h0 | h0
  · linarith
  obtain ⟨y, hy⟩ := hi
  have hb : 0 < d.ρ y := d.pos hy
  have hint : interior {y | 0 < d.ρ y} = interior (μ : Measure ℝ).support :=
    subset_antisymm d.interior_pos_subset d.isBorell.interior_support_subset
  have hcl : x ∈ closure (interior (μ : Measure ℝ).support) := by
    have hne : (interior {y : ℝ | 0 < d.ρ y}).Nonempty := by rw [hint]; exact ⟨y, hy⟩
    have heq := d.isBorell.convex_pos.closure_interior_eq_closure_of_nonempty_interior hne
    rw [hint] at heq
    rw [heq]
    exact subset_closure (show x ∈ {y : ℝ | 0 < d.ρ y} from h0)
  have hseg : ∀ t : ℝ, t ∈ Ioo (0 : ℝ) 1 → d.ρ x ^ t * d.ρ y ^ (1 - t) ≤ 2 * d.ρ m := by
    intro t ht
    have hz : t • x + (1 - t) • y ∈ interior (μ : Measure ℝ).support := by
      have hyi : y ∈ interior (interior (μ : Measure ℝ).support) := by
        rwa [isOpen_interior.interior_eq]
      have := hμ.convex_interior_support.combo_closure_interior_mem_interior
        (a := t) (b := 1 - t) hcl hyi ht.1.le (by linarith [ht.2]) (by ring)
      rwa [isOpen_interior.interior_eq] at this
    exact (d.isBorell.logConcave x y t ht.1 ht.2).trans (hΩ _ hz)
  have hgeq : ∀ t : ℝ, d.ρ x ^ t * d.ρ y ^ (1 - t) =
      Real.exp (Real.log (d.ρ x) * t + Real.log (d.ρ y) * (1 - t)) := by
    intro t
    rw [Real.exp_add, Real.rpow_def_of_pos h0, Real.rpow_def_of_pos hb]
  have hgc : Continuous fun t : ℝ ↦ d.ρ x ^ t * d.ρ y ^ (1 - t) := by
    simp only [hgeq]
    fun_prop
  have htend : Tendsto (fun t : ℝ ↦ d.ρ x ^ t * d.ρ y ^ (1 - t)) (𝓝[<] (1 : ℝ))
      (𝓝 (d.ρ x ^ (1 : ℝ) * d.ρ y ^ (1 - (1 : ℝ)))) :=
    (hgc.tendsto 1).mono_left nhdsWithin_le_nhds
  have hlim : d.ρ x ^ (1 : ℝ) * d.ρ y ^ (1 - (1 : ℝ)) ≤ 2 * d.ρ m := by
    refine le_of_tendsto htend ?_
    filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with t ht
    exact hseg t ht
  simpa using hlim

/-! ### `Q1'`: the smooth-domain isoperimetric bound -/

/-- Left half: the mass strictly left of the median outside an open set containing the median is
charged by the boundary point closest to the median on that side. -/
theorem mul_measure_Iio_diff_le {W : Set ℝ} (hW : IsOpen W) (hmW : m ∈ W) :
    ENNReal.ofReal (2 * d.ρ m) * (μ : Measure ℝ) (Iio m \ W) ≤
      ∫⁻ x in frontier W ∩ interior (μ : Measure ℝ).support ∩ Iio m,
        ENNReal.ofReal (d.ρ x) ∂(surfaceMeasure ℝ) := by
  have hmΩ : m ∈ interior (μ : Measure ℝ).support := median_mem hμ hi hm
  rcases (Iio m \ W).eq_empty_or_nonempty with hA | hA
  · rw [hA]
    simp
  have hbdd : BddAbove (Iio m \ W) := ⟨m, fun y hy ↦ le_of_lt hy.1⟩
  set a := sSup (Iio m \ W) with ha
  have hacl : a ∉ W := by
    have hmem : a ∈ closure (Iio m \ W) := csSup_mem_closure hA hbdd
    exact closure_minimal (fun y hy ↦ hy.2) hW.isClosed_compl hmem
  have ham : a ≤ m := csSup_le hA (fun y hy ↦ hy.1.le)
  have haltm : a < m := lt_of_le_of_ne ham (fun h ↦ hacl (by rw [h]; exact hmW))
  have hAsub : Iio m \ W ⊆ Iic a := fun y hy ↦ le_csSup hbdd hy
  by_cases haΩ : a ∈ interior (μ : Measure ℝ).support
  · have hIoo : Ioo a m ⊆ W := by
      intro y hy
      by_contra hyW
      exact absurd (le_csSup hbdd ⟨hy.2, hyW⟩) (not_le.mpr hy.1)
    have hafr : a ∈ frontier W := by
      rw [hW.frontier_eq]
      refine ⟨?_, hacl⟩
      have hmem : a ∈ closure (Ioo a m) := by
        rw [closure_Ioo haltm.ne]
        exact ⟨le_rfl, ham⟩
      exact closure_mono hIoo hmem
    have hmem : a ∈ frontier W ∩ interior (μ : Measure ℝ).support ∩ Iio m := ⟨⟨hafr, haΩ⟩, haltm⟩
    refine le_trans ?_ (d.ofReal_le_setLIntegral hmem)
    calc ENNReal.ofReal (2 * d.ρ m) * (μ : Measure ℝ) (Iio m \ W)
        ≤ ENNReal.ofReal (2 * d.ρ m) * (μ : Measure ℝ) (Iic a) := by gcongr
      _ = ENNReal.ofReal (2 * d.ρ m) * ENNReal.ofReal (cdf μ a) := by
          rw [measure_Iic_eq_ofReal_cdf]
      _ = ENNReal.ofReal (2 * d.ρ m * cdf μ a) := by
          rw [← ENNReal.ofReal_mul (by linarith [d.nonneg m] : (0 : ℝ) ≤ 2 * d.ρ m)]
      _ ≤ ENNReal.ofReal (d.ρ a) := ENNReal.ofReal_le_ofReal (d.two_mul_cdf_le hμ hi hm ham)
  · have hnull : (μ : Measure ℝ) (Iic a) = 0 := by
      refine measure_mono_null ?_ (hμ.measure_compl_interior_support hi)
      intro z hz hzΩ
      exact haΩ (hμ.convex_interior_support.ordConnected.out hzΩ hmΩ ⟨hz, ham⟩)
    rw [measure_mono_null hAsub hnull, mul_zero]
    exact zero_le

/-- Right half: the mass strictly right of the median outside an open set containing the median is
charged by the boundary point closest to the median on that side. -/
theorem mul_measure_Ioi_diff_le {W : Set ℝ} (hW : IsOpen W) (hmW : m ∈ W) :
    ENNReal.ofReal (2 * d.ρ m) * (μ : Measure ℝ) (Ioi m \ W) ≤
      ∫⁻ x in frontier W ∩ interior (μ : Measure ℝ).support ∩ Ioi m,
        ENNReal.ofReal (d.ρ x) ∂(surfaceMeasure ℝ) := by
  have hmΩ : m ∈ interior (μ : Measure ℝ).support := median_mem hμ hi hm
  rcases (Ioi m \ W).eq_empty_or_nonempty with hA | hA
  · rw [hA]
    simp
  have hbdd : BddBelow (Ioi m \ W) := ⟨m, fun y hy ↦ le_of_lt hy.1⟩
  set b := sInf (Ioi m \ W) with hb
  have hbcl : b ∉ W := by
    have hmem : b ∈ closure (Ioi m \ W) := csInf_mem_closure hA hbdd
    exact closure_minimal (fun y hy ↦ hy.2) hW.isClosed_compl hmem
  have hmb : m ≤ b := le_csInf hA (fun y hy ↦ hy.1.le)
  have hmltb : m < b := lt_of_le_of_ne hmb (fun h ↦ hbcl (by rw [← h]; exact hmW))
  have hAsub : Ioi m \ W ⊆ Ici b := fun y hy ↦ csInf_le hbdd hy
  by_cases hbΩ : b ∈ interior (μ : Measure ℝ).support
  · have hIoo : Ioo m b ⊆ W := by
      intro y hy
      by_contra hyW
      exact absurd (csInf_le hbdd ⟨hy.1, hyW⟩) (not_le.mpr hy.2)
    have hbfr : b ∈ frontier W := by
      rw [hW.frontier_eq]
      refine ⟨?_, hbcl⟩
      have hmem : b ∈ closure (Ioo m b) := by
        rw [closure_Ioo hmltb.ne]
        exact ⟨hmb, le_rfl⟩
      exact closure_mono hIoo hmem
    have hmem : b ∈ frontier W ∩ interior (μ : Measure ℝ).support ∩ Ioi m := ⟨⟨hbfr, hbΩ⟩, hmltb⟩
    refine le_trans ?_ (d.ofReal_le_setLIntegral hmem)
    have hIci : (μ : Measure ℝ) (Ici b) = (μ : Measure ℝ) (Ioi b) := by
      rw [← Set.Ioi_union_left, measure_union (by simp) (measurableSet_singleton b),
        d.measure_singleton b, add_zero]
    calc ENNReal.ofReal (2 * d.ρ m) * (μ : Measure ℝ) (Ioi m \ W)
        ≤ ENNReal.ofReal (2 * d.ρ m) * (μ : Measure ℝ) (Ici b) := by gcongr
      _ = ENNReal.ofReal (2 * d.ρ m) * ENNReal.ofReal ((μ : Measure ℝ).real (Ioi b)) := by
          rw [hIci, measure_eq_ofReal_measureReal]
      _ = ENNReal.ofReal (2 * d.ρ m * (μ : Measure ℝ).real (Ioi b)) := by
          rw [← ENNReal.ofReal_mul (by linarith [d.nonneg m] : (0 : ℝ) ≤ 2 * d.ρ m)]
      _ ≤ ENNReal.ofReal (d.ρ b) :=
          ENNReal.ofReal_le_ofReal (d.two_mul_measureReal_Ioi_le hμ hi hm hmb)
  · have hnull : (μ : Measure ℝ) (Ici b) = 0 := by
      refine measure_mono_null ?_ (hμ.measure_compl_interior_support hi)
      intro z hz hzΩ
      exact hbΩ (hμ.convex_interior_support.ordConnected.out hmΩ hzΩ ⟨hmb, hz⟩)
    rw [measure_mono_null hAsub hnull, mul_zero]
    exact zero_le

/-- Boundary charge of an open set containing the median: the mass of its complement is
controlled by the boundary integral, with the factor `2 ρ(m)`. -/
theorem mul_measure_compl_le {W : Set ℝ} (hW : IsOpen W) (hmW : m ∈ W) :
    ENNReal.ofReal (2 * d.ρ m) * (μ : Measure ℝ) Wᶜ ≤
      ∫⁻ x in frontier W ∩ interior (μ : Measure ℝ).support,
        ENNReal.ofReal (d.ρ x) ∂(surfaceMeasure ℝ) := by
  set D := frontier W ∩ interior (μ : Measure ℝ).support with hD
  have hDmeas : MeasurableSet D :=
    isClosed_frontier.measurableSet.inter isOpen_interior.measurableSet
  have hsplit : Wᶜ ⊆ (Iio m \ W) ∪ (Ioi m \ W) := by
    intro z hz
    rcases lt_trichotomy z m with h | h | h
    · exact Or.inl ⟨h, hz⟩
    · exact absurd (h ▸ hmW) hz
    · exact Or.inr ⟨h, hz⟩
  have hdisj : Disjoint (D ∩ Iio m) (D ∩ Ioi m) := by
    refine Set.disjoint_left.mpr fun z hz hz' ↦ ?_
    have h1 : z < m := hz.2
    have h2 : m < z := hz'.2
    exact absurd h1 (not_lt.mpr h2.le)
  have hunion : ∫⁻ x in (D ∩ Iio m) ∪ (D ∩ Ioi m), ENNReal.ofReal (d.ρ x) ∂(surfaceMeasure ℝ) =
      (∫⁻ x in D ∩ Iio m, ENNReal.ofReal (d.ρ x) ∂(surfaceMeasure ℝ)) +
      ∫⁻ x in D ∩ Ioi m, ENNReal.ofReal (d.ρ x) ∂(surfaceMeasure ℝ) :=
    lintegral_union (hDmeas.inter measurableSet_Ioi) hdisj
  calc ENNReal.ofReal (2 * d.ρ m) * (μ : Measure ℝ) Wᶜ
      ≤ ENNReal.ofReal (2 * d.ρ m) *
          ((μ : Measure ℝ) (Iio m \ W) + (μ : Measure ℝ) (Ioi m \ W)) := by
        gcongr
        exact (measure_mono hsplit).trans (measure_union_le _ _)
    _ = ENNReal.ofReal (2 * d.ρ m) * (μ : Measure ℝ) (Iio m \ W) +
        ENNReal.ofReal (2 * d.ρ m) * (μ : Measure ℝ) (Ioi m \ W) := by rw [mul_add]
    _ ≤ (∫⁻ x in D ∩ Iio m, ENNReal.ofReal (d.ρ x) ∂(surfaceMeasure ℝ)) +
        ∫⁻ x in D ∩ Ioi m, ENNReal.ofReal (d.ρ x) ∂(surfaceMeasure ℝ) :=
        add_le_add (d.mul_measure_Iio_diff_le hμ hi hm hW hmW)
          (d.mul_measure_Ioi_diff_le hμ hi hm hW hmW)
    _ = ∫⁻ x in (D ∩ Iio m) ∪ (D ∩ Ioi m), ENNReal.ofReal (d.ρ x) ∂(surfaceMeasure ℝ) :=
        hunion.symm
    _ ≤ ∫⁻ x in D, ENNReal.ofReal (d.ρ x) ∂(surfaceMeasure ℝ) :=
        lintegral_mono' (Measure.restrict_mono (by
          rintro z (hz | hz) <;> exact hz.1) le_rfl) le_rfl

/-- Blueprint Stage 1 `Q1'`: every smooth domain of the line has relative perimeter at least
`2 ρ(m)` times the balance of its mass. -/
theorem mul_min_le_relativePerimeter (U : SmoothDomain ℝ) :
    ENNReal.ofReal (2 * d.ρ m) *
        min ((μ : Measure ℝ) U.carrier) (1 - (μ : Measure ℝ) U.carrier) ≤
      relativePerimeter d.ρ (interior (μ : Measure ℝ).support) U := by
  have hmΩ : m ∈ interior (μ : Measure ℝ).support := median_mem hμ hi hm
  rw [relativePerimeter]
  set p := (μ : Measure ℝ) U.carrier with hp
  have hp1 : p ≤ 1 := prob_le_one
  have hmin_le_left : min p (1 - p) ≤ p := min_le_left _ _
  have hmin_le_right : min p (1 - p) ≤ 1 - p := min_le_right _ _
  by_cases hmU : m ∈ U.carrier
  · have hcompl : (μ : Measure ℝ) (U.carrier)ᶜ = 1 - p := prob_compl_eq_one_sub U.measurableSet
    refine le_trans ?_ (d.mul_measure_compl_le hμ hi hm U.isOpen hmU)
    have hle : min p (1 - p) ≤ (μ : Measure ℝ) (U.carrier)ᶜ := by
      rw [hcompl]; exact hmin_le_right
    exact mul_le_mul_right hle _
  by_cases hmfr : m ∈ frontier U.carrier
  · have htwo : 2 * min p (1 - p) ≤ 1 := by
      calc 2 * min p (1 - p) = min p (1 - p) + min p (1 - p) := two_mul _
        _ ≤ p + (1 - p) := add_le_add hmin_le_left hmin_le_right
        _ = 1 := add_tsub_cancel_of_le hp1
    have hofReal : ENNReal.ofReal (2 * d.ρ m) = 2 * ENNReal.ofReal (d.ρ m) := by
      rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
    calc ENNReal.ofReal (2 * d.ρ m) * min p (1 - p)
        = ENNReal.ofReal (d.ρ m) * (2 * min p (1 - p)) := by rw [hofReal]; ring
      _ ≤ ENNReal.ofReal (d.ρ m) * 1 := mul_le_mul_right htwo _
      _ = ENNReal.ofReal (d.ρ m) := mul_one _
      _ ≤ _ := d.ofReal_le_setLIntegral (Set.mem_inter hmfr hmΩ)
  · have hmcl : m ∉ closure U.carrier := by
      intro hcl
      exact hmfr (by rw [U.isOpen.frontier_eq]; exact ⟨hcl, hmU⟩)
    have hWopen : IsOpen (closure U.carrier)ᶜ := isClosed_closure.isOpen_compl
    have hfrW : frontier (closure U.carrier)ᶜ ⊆ frontier U.carrier := by
      rw [frontier_compl]
      exact frontier_closure_subset
    have hWc : (μ : Measure ℝ) ((closure U.carrier)ᶜ)ᶜ = (μ : Measure ℝ) (closure U.carrier) := by
      rw [compl_compl]
    have hstep := d.mul_measure_compl_le hμ hi hm hWopen hmcl
    refine le_trans (le_trans ?_ hstep) ?_
    · refine mul_le_mul_right ?_ _
      rw [hWc]
      exact hmin_le_left.trans (measure_mono subset_closure)
    · exact lintegral_mono' (Measure.restrict_mono
        (Set.inter_subset_inter_left _ hfrW) le_rfl) le_rfl

/-- Blueprint Stage 1 `Q1`: the Minkowski Cheeger infimum of a log-concave law on the line is at
least twice the density at a median. -/
theorem two_mul_le_minkowskiConstant :
    ENNReal.ofReal (2 * d.ρ m) ≤ Isoperimetry.minkowskiConstant μ := by
  rw [Isoperimetry.minkowskiConstant_eq_smoothConstant d.isBorell, Isoperimetry.smoothConstant]
  refine le_iInf fun U ↦ le_iInf fun hpos ↦ le_iInf fun hlt ↦ ?_
  set p := (μ : Measure ℝ) U.carrier with hp
  have hmin0 : min p (1 - p) ≠ 0 := ne_of_gt (lt_min hpos (tsub_pos_of_lt hlt))
  have hmintop : min p (1 - p) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top ((min_le_left _ _).trans prob_le_one)
  exact (ENNReal.le_div_iff_mul_le (Or.inl hmin0) (Or.inl hmintop)).mpr
    (d.mul_min_le_relativePerimeter hμ hi hm U)

end Median

end LineDensity

end FunctionalInequalities.KLS
