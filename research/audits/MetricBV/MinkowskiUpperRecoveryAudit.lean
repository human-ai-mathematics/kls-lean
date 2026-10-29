import FunctionalInequalities.KLS.Geometry.Cheeger.UpperMinkowskiContent

/-! Independent full-signature clients for the quantitative small-radius selection of an
upper-content-controlled thickening radius, and the lower-to-upper recovery of a measurable set of
finite lower Minkowski content. Checks: the selection for every set, radius and slack (with the
selected radius strictly inside `(0, r)`); the recovery with all its components (positive radii
tending to `0`, measurable thickenings, indicator `L¹(ν)` convergence, `limsup` of upper contents at
most the lower content); the quotient-realizing radii; the indicator-error identity; the empty set
and the full set (lower content `0`); zero lower content; a boundary atom (Dirac law at `0` with
`B = [0, ∞)`); the separation of the infinite-content case (only the trivial bound, no `toReal`);
and the uniform law on `[0, 1]` with `B = {0}`, whose lower content is `1` and whose recovery
thickenings have upper content exactly `1`, so the `limsup` bound is attained. Not claimed: equality
of the `limsup` with the lower content in general, `ν (closure B) = ν B`, measurability of the
radius-content function, any BV or relaxation statement. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Metric Set
open scoped ENNReal Topology

namespace MinkowskiUpperRecoveryAudit

open FunctionalInequalities.KLS.Isoperimetry

variable {V : Type*} [NormedAddCommGroup V] [MeasurableSpace V]

/-- Selection for every set: a radius strictly inside `(0, r)` with the quantitative bound. -/
theorem selection (ν : ProbabilityMeasure V) (B : Set V) {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε) :
    ∃ s : ℝ, 0 < s ∧ s < r ∧ upperMinkowskiContent (ν : Measure V) (thickening s B) ≤
      ((ν : Measure V) (thickening r B) - (ν : Measure V) B) / ENNReal.ofReal r +
        ENNReal.ofReal ε := by
  obtain ⟨s, hs, h⟩ := exists_upperMinkowskiContent_thickening_le_div_add (ν : Measure V) B hr hε
  exact ⟨s, hs.1, hs.2, h⟩

/-- Radii realizing the lower-content liminf, with the quotient bound and both limits. -/
theorem realizingRadii (ν : ProbabilityMeasure V) (B : Set V) (hfin : minkowskiContent (ν : Measure V) B ≠ ⊤) :
    ∃ r : ℕ → ℝ, (∀ n : ℕ, 0 < r n ∧ r n < 1 / ((n : ℝ) + 1)) ∧
      (∀ n : ℕ, ((ν : Measure V) (thickening (r n) B) - (ν : Measure V) B) /
          ENNReal.ofReal (r n) ≤ minkowskiContent (ν : Measure V) B + (n : ℝ≥0∞)⁻¹) ∧
      Tendsto r atTop (𝓝[>] 0) ∧
      Tendsto (fun n => ((ν : Measure V) (thickening (r n) B) - (ν : Measure V) B) /
        ENNReal.ofReal (r n)) atTop (𝓝 (minkowskiContent (ν : Measure V) B)) := by
  obtain ⟨r, h1, h2, h3, h4⟩ := exists_radii_tendsto_minkowskiContent (ν : Measure V) B hfin
  exact ⟨r, fun n => ⟨(h1 n).1, (h1 n).2⟩, h2, h3, h4⟩

section Borel

variable [OpensMeasurableSpace V]

/-- The recovery with all five components, for every measurable set of finite lower content. -/
theorem recovery (ν : ProbabilityMeasure V) {B : Set V} (hB : MeasurableSet B)
    (hfin : minkowskiContent (ν : Measure V) B ≠ ⊤) :
    ∃ s : ℕ → ℝ, (∀ n, 0 < s n) ∧ Tendsto s atTop (𝓝 0) ∧
      (∀ n, MeasurableSet (thickening (s n) B)) ∧
      Tendsto (fun n => ∫⁻ x, ‖(thickening (s n) B).indicator (1 : V → ℝ) x -
        B.indicator 1 x‖ₑ ∂(ν : Measure V)) atTop (𝓝 0) ∧
      limsup (fun n => upperMinkowskiContent (ν : Measure V) (thickening (s n) B)) atTop ≤
        minkowskiContent (ν : Measure V) B :=
  exists_upperRecovery (ν : Measure V) B hB hfin

theorem indicatorError (ν : ProbabilityMeasure V) {B : Set V} (hB : MeasurableSet B) {s : ℝ}
    (hs : 0 < s) :
    ∫⁻ x, ‖(thickening s B).indicator (1 : V → ℝ) x - B.indicator 1 x‖ₑ ∂(ν : Measure V) =
      (ν : Measure V) (thickening s B) - (ν : Measure V) B :=
  lintegral_enorm_indicator_thickening_sub (ν : Measure V) B hB hs

/-- The empty set: lower content `0`, hence finite; the recovery applies and the `limsup` is
bounded by `0`. -/
theorem emptySet (ν : ProbabilityMeasure V) :
    minkowskiContent (ν : Measure V) (∅ : Set V) = 0 ∧
      ∃ s : ℕ → ℝ, (∀ n, 0 < s n) ∧ Tendsto s atTop (𝓝 0) ∧
        limsup (fun n => upperMinkowskiContent (ν : Measure V) (thickening (s n) (∅ : Set V))) atTop ≤ 0 := by
  have h0 := minkowskiContent_empty (ν : Measure V)
  obtain ⟨s, hs, hs0, -, -, hl⟩ :=
    exists_upperRecovery (ν : Measure V) (∅ : Set V) MeasurableSet.empty (h0 ▸ ENNReal.zero_ne_top)
  exact ⟨h0, s, hs, hs0, h0 ▸ hl⟩

/-- The full set: every positive thickening is the whole space, so the lower content is `0` and
the recovery applies with `limsup` at most `0`. -/
theorem fullSet (ν : ProbabilityMeasure V) :
    minkowskiContent (ν : Measure V) (univ : Set V) = 0 ∧
      ∃ s : ℕ → ℝ, (∀ n, 0 < s n) ∧
        Tendsto (fun n => ∫⁻ x, ‖(thickening (s n) (univ : Set V)).indicator (1 : V → ℝ) x -
          (univ : Set V).indicator 1 x‖ₑ ∂(ν : Measure V)) atTop (𝓝 0) ∧
        limsup (fun n => upperMinkowskiContent (ν : Measure V) (thickening (s n) (univ : Set V))) atTop ≤ 0 := by
  have hzero : upperMinkowskiContent (ν : Measure V) (univ : Set V) = 0 :=
    upperMinkowskiContent_eq_zero_of_forall_measure_thickening_le (ν : Measure V) fun r hr => by
      rw [eq_univ_of_univ_subset (self_subset_thickening hr univ)]
  have h0 : minkowskiContent (ν : Measure V) (univ : Set V) = 0 :=
    le_antisymm ((minkowskiContent_le_upperMinkowskiContent (ν : Measure V) _).trans_eq hzero) bot_le
  obtain ⟨s, hs, -, -, hL1, hl⟩ :=
    exists_upperRecovery (ν : Measure V) (univ : Set V) MeasurableSet.univ (h0 ▸ ENNReal.zero_ne_top)
  exact ⟨h0, s, hs, hL1, h0 ▸ hl⟩

/-- Zero lower content: the upper contents of the recovery thickenings tend to `0`. -/
theorem zeroContent (ν : ProbabilityMeasure V) {B : Set V} (hB : MeasurableSet B)
    (h0 : minkowskiContent (ν : Measure V) B = 0) :
    ∃ s : ℕ → ℝ, (∀ n, 0 < s n) ∧ Tendsto s atTop (𝓝 0) ∧
      Tendsto (fun n => ∫⁻ x, ‖(thickening (s n) B).indicator (1 : V → ℝ) x -
        B.indicator 1 x‖ₑ ∂(ν : Measure V)) atTop (𝓝 0) ∧
      Tendsto (fun n => upperMinkowskiContent (ν : Measure V) (thickening (s n) B)) atTop (𝓝 0) := by
  obtain ⟨s, hs, hs0, -, hL1, hl⟩ := exists_upperRecovery (ν : Measure V) B hB (h0 ▸ ENNReal.zero_ne_top)
  refine ⟨s, hs, hs0, hL1, ?_⟩
  rw [h0] at hl
  exact tendsto_of_le_liminf_of_limsup_le bot_le hl

omit [OpensMeasurableSpace V] in
/-- Infinite lower content is excluded from the recovery by hypothesis; only the trivial bound
holds, and no `toReal` is used. -/
theorem infiniteContentSeparation (ν : ProbabilityMeasure V) (B : Set V)
    (htop : minkowskiContent (ν : Measure V) B = ⊤) (s : ℕ → ℝ) :
    limsup (fun n => upperMinkowskiContent (ν : Measure V) (thickening (s n) B)) atTop ≤
      minkowskiContent (ν : Measure V) B := by
  rw [htop]
  exact le_top

end Borel

/-! ### A boundary atom: the Dirac law at `0` with `B = [0, ∞)` -/

def diracLaw : ProbabilityMeasure ℝ := ⟨Measure.dirac 0, inferInstance⟩

theorem dirac_Ici : (diracLaw : Measure ℝ) (Ici 0) = 1 := by
  simp [diracLaw, Measure.dirac_apply_of_mem (mem_Ici.2 le_rfl : (0 : ℝ) ∈ Ici 0)]

/-- The atom sits on the boundary of `[0, ∞)`: every positive thickening carries no extra mass,
so both contents vanish and the recovery applies. -/
theorem boundaryAtom :
    minkowskiContent (diracLaw : Measure ℝ) (Ici 0) = 0 ∧ upperMinkowskiContent (diracLaw : Measure ℝ) (Ici 0) = 0 ∧
      ∃ s : ℕ → ℝ, (∀ n, 0 < s n) ∧
        Tendsto (fun n => ∫⁻ x, ‖(thickening (s n) (Ici (0 : ℝ))).indicator (1 : ℝ → ℝ) x -
          (Ici (0 : ℝ)).indicator 1 x‖ₑ ∂(diracLaw : Measure ℝ)) atTop (𝓝 0) ∧
        limsup (fun n => upperMinkowskiContent (diracLaw : Measure ℝ) (thickening (s n) (Ici 0))) atTop ≤ 0 := by
  have hup : upperMinkowskiContent (diracLaw : Measure ℝ) (Ici 0) = 0 :=
    upperMinkowskiContent_eq_zero_of_forall_measure_thickening_le (diracLaw : Measure ℝ) fun r _ => by
      rw [dirac_Ici]; exact prob_le_one
  have hlow : minkowskiContent (diracLaw : Measure ℝ) (Ici 0) = 0 :=
    le_antisymm ((minkowskiContent_le_upperMinkowskiContent _ _).trans_eq hup) bot_le
  obtain ⟨s, hs, -, -, hL1, hl⟩ :=
    exists_upperRecovery (diracLaw : Measure ℝ) (Ici 0) measurableSet_Ici (hlow ▸ ENNReal.zero_ne_top)
  exact ⟨hlow, hup, s, hs, hL1, hlow ▸ hl⟩

/-! ### The uniform law on `[0, 1]` with `B = {0}`: the bound is attained -/

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

/-- The lower-content quotient of `{0}` equals `1` at every radius in `(0, 1]`. -/
theorem uniform_quotient {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    ((uniformInterval : Measure ℝ) (thickening t {0}) - (uniformInterval : Measure ℝ) {0}) /
      ENNReal.ofReal t = 1 := by
  rw [thickening_singleton, uniform_ball ht0 ht1, uniform_singleton, tsub_zero,
    ENNReal.div_self (by simpa using ht0) ENNReal.ofReal_ne_top]

/-- The lower content of `{0}` under the uniform law is `1`. -/
theorem uniform_minkowskiContent : minkowskiContent (uniformInterval : Measure ℝ) {0} = 1 := by
  unfold minkowskiContent
  rw [liminf_congr (Eventually.mono (Ioo_mem_nhdsGT (zero_lt_one' ℝ))
    fun t ht => uniform_quotient ht.1 ht.2.le)]
  exact liminf_const 1

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

/-- Selection is exact here: for `r ∈ (0, 1]` the bound reads `1 + ε`, and the selected
thickening has upper content exactly `1` (when `r < 1`). -/
theorem uniformSelection {r ε : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (hε : 0 < ε) :
    ∃ s ∈ Ioo 0 r, upperMinkowskiContent (uniformInterval : Measure ℝ) (thickening s {0}) = 1 ∧
      upperMinkowskiContent (uniformInterval : Measure ℝ) (thickening s {0}) ≤ 1 + ENNReal.ofReal ε := by
  obtain ⟨s, hs, h⟩ :=
    exists_upperMinkowskiContent_thickening_le_div_add (uniformInterval : Measure ℝ) {0} hr0 hε
  rw [uniform_quotient hr0 hr1.le] at h
  exact ⟨s, hs, uniform_upperContent hs.1 (hs.2.trans hr1), h⟩

/-- Attained: the recovery thickenings of `{0}` have upper content exactly `1` eventually, so the
`limsup` equals the lower content `1`; the indicator errors still vanish. -/
theorem uniformAttained :
    ∃ s : ℕ → ℝ, (∀ n, 0 < s n) ∧ Tendsto s atTop (𝓝 0) ∧
      Tendsto (fun n => ∫⁻ x, ‖(thickening (s n) ({0} : Set ℝ)).indicator (1 : ℝ → ℝ) x -
        ({0} : Set ℝ).indicator 1 x‖ₑ ∂(uniformInterval : Measure ℝ)) atTop (𝓝 0) ∧
      limsup (fun n => upperMinkowskiContent (uniformInterval : Measure ℝ) (thickening (s n) {0})) atTop =
        minkowskiContent (uniformInterval : Measure ℝ) {0} := by
  obtain ⟨s, hs, hs0, -, hL1, hl⟩ := exists_upperRecovery (uniformInterval : Measure ℝ) {0}
    (measurableSet_singleton 0) (uniform_minkowskiContent ▸ ENNReal.one_ne_top)
  refine ⟨s, hs, hs0, hL1, le_antisymm hl ?_⟩
  rw [uniform_minkowskiContent]
  have hev : ∀ᶠ n in atTop, upperMinkowskiContent (uniformInterval : Measure ℝ) (thickening (s n) {0}) = 1 := by
    filter_upwards [(tendsto_order.1 hs0).2 1 one_pos] with n hn
    exact uniform_upperContent (hs n) hn
  rw [limsup_congr hev]
  exact (limsup_const 1).ge

#print axioms selection
#print axioms realizingRadii
#print axioms recovery
#print axioms indicatorError
#print axioms emptySet
#print axioms fullSet
#print axioms zeroContent
#print axioms infiniteContentSeparation
#print axioms boundaryAtom
#print axioms uniformSelection
#print axioms uniformAttained

end MinkowskiUpperRecoveryAudit
