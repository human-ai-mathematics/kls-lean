import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Outer Minkowski content and the Minkowski coarea inequality

Hole-free companion of `KLS/Isoperimetry.lean`: `minkowskiContent` is `boundaryContent` written on
an arbitrary metric space with a Borel measure (finite Borel measures wherever a statement needs
finiteness; the probability statements are instances), with open thickenings, `ENNReal` truncated
subtraction and a right-neighbourhood `liminf` at `r ↓ 0` (2026-09-30: generic metric scope and
finite-measure scope, with scaling by nonnegative real scalars and the zero measure; on
the coordinate space it is the ambient form of `boundaryContent`).  The open-ball supremum
`openBallSup` is the lower semicontinuous majorant used by the metric coarea inequality in
`LocalSlopeCoarea.lean`; the closed-ball `ballSup` and the `C¹` coarea theorem keep their normed
scope.

The module proves `lintegral_minkowskiContent_superlevel_le`, the Minkowski coarea inequality of
Ambrosio--Di Marino--Gigli 2017, Lemma 3.2: for a `C¹` globally Lipschitz `u`,
`∫ ν⁺({u ≥ t}) dt ≤ ∫ ‖∇u‖ dν`.  The measure is an arbitrary finite measure; no density,
no absolute continuity, no positive dimension and no boundedness of `u` are assumed.

Read `minkowskiContent`, then the local supremum `ballSup` with its Lipschitz property and
the near-neighbour witness `thickening_superlevel_subset`, then the coarea inequality.
Nothing here depends on the weighted coarea formula, Sard, the relative perimeter or any
work-in-progress layer: the module imports no local module at all, only Mathlib.
-/

noncomputable section

open MeasureTheory Filter Metric Set
open scoped ENNReal NNReal Topology

namespace FunctionalInequalities.KLS.Isoperimetry

universe u

section Generic

variable {V : Type u} [MetricSpace V]

/-! ### Local suprema over open balls

The majorant of Ambrosio--Di Marino--Gigli (3.1): the supremum of `u` over the *open* ball.  On an
arbitrary metric space the closed-ball supremum `ballSup` below need not be continuous (two
components `[0, 1] ∪ [2, 3] ⊆ ℝ`, `u = 0` on the first and `1` on the second, radius `1`: the
supremum jumps at the centre `1`), while the open-ball supremum is lower semicontinuous, hence
Borel, and satisfies the same near-neighbour witness.  The two are different objects; the
closed-ball API keeps its normed-group scope.
-/

section OpenBallSup

variable {u : V → ℝ} {K : ℝ≥0} {r : ℝ}

/-- The supremum of `u` over the open ball of radius `r` around `x`. -/
def openBallSup (u : V → ℝ) (r : ℝ) (x : V) : ℝ := sSup (u '' Metric.ball x r)

/-- A Lipschitz function is bounded above on an open ball by its value at the centre. -/
theorem bddAbove_image_ball (hK : LipschitzWith K u) (r : ℝ) (x : V) :
    BddAbove (u '' Metric.ball x r) := by
  refine ⟨u x + K * r, ?_⟩
  rintro a ⟨y, hy, rfl⟩
  have hd : dist (u y) (u x) ≤ K * dist y x := hK.dist_le_mul y x
  rw [Real.dist_eq] at hd
  have hyx : dist y x ≤ r := (Metric.mem_ball.1 hy).le
  have h2 : |u y - u x| ≤ (K : ℝ) * r := hd.trans (by gcongr)
  linarith [(abs_le.mp h2).2]

/-- The centre value is below the open-ball supremum (positive radius). -/
theorem le_openBallSup (hK : LipschitzWith K u) (hr : 0 < r) (x : V) :
    u x ≤ openBallSup u r x :=
  le_csSup (bddAbove_image_ball hK r x) ⟨x, Metric.mem_ball_self hr, rfl⟩

/-- The open-ball supremum exceeds the centre value by at most `K r`. -/
theorem openBallSup_le_add (hK : LipschitzWith K u) (hr : 0 < r) (x : V) :
    openBallSup u r x ≤ u x + K * r := by
  refine csSup_le ⟨u x, x, Metric.mem_ball_self hr, rfl⟩ ?_
  rintro a ⟨y, hy, rfl⟩
  have hd : dist (u y) (u x) ≤ K * dist y x := hK.dist_le_mul y x
  rw [Real.dist_eq] at hd
  have hyx : dist y x ≤ r := (Metric.mem_ball.1 hy).le
  have h2 : |u y - u x| ≤ (K : ℝ) * r := hd.trans (by gcongr)
  linarith [(abs_le.mp h2).2]

/-- The open-ball supremum is lower semicontinuous on every metric space: a point of the open ball
above a level stays in the open balls of nearby centres. -/
theorem lowerSemicontinuous_openBallSup (hK : LipschitzWith K u) (hr : 0 < r) :
    LowerSemicontinuous (openBallSup u r) := by
  intro x t ht
  obtain ⟨a, ⟨z, hz, rfl⟩, hta⟩ := (lt_csSup_iff (bddAbove_image_ball hK r x)
    ⟨u x, x, Metric.mem_ball_self hr, rfl⟩).1 ht
  have hzx : dist z x < r := Metric.mem_ball.1 hz
  filter_upwards [Metric.ball_mem_nhds x (sub_pos.2 hzx)] with y hy
  have hzy : z ∈ Metric.ball y r := by
    rw [Metric.mem_ball] at hy ⊢
    calc dist z y ≤ dist z x + dist x y := dist_triangle _ _ _
      _ < r := by rw [dist_comm x y]; linarith
  exact hta.trans_le (le_csSup (bddAbove_image_ball hK r y) ⟨z, hzy, rfl⟩)

/-- The open-ball supremum of a Lipschitz function is Borel measurable. -/
theorem measurable_openBallSup [MeasurableSpace V] [OpensMeasurableSpace V] (hK : LipschitzWith K u) (hr : 0 < r) :
    Measurable (openBallSup u r) :=
  (lowerSemicontinuous_openBallSup hK hr).measurable

/-- Near-neighbour witness with open balls: a point of the open `r`-thickening of a closed
superlevel set either lies in the set or has an open-ball supremum reaching the level. -/
theorem thickening_superlevel_subset_openBallSup (hK : LipschitzWith K u) (r : ℝ) (t : ℝ) :
    Metric.thickening r {x : V | t ≤ u x} ⊆
      {x : V | u x < t ∧ t ≤ openBallSup u r x} ∪ {x : V | t ≤ u x} := by
  intro x hx
  by_cases hxt : t ≤ u x
  · exact Or.inr hxt
  refine Or.inl ⟨not_le.mp hxt, ?_⟩
  obtain ⟨z, hz, hdz⟩ := Metric.mem_thickening_iff.mp hx
  refine hz.trans (le_csSup (bddAbove_image_ball hK r x) ⟨z, ?_, rfl⟩)
  rw [Metric.mem_ball, dist_comm]
  exact hdz

end OpenBallSup

variable [MeasurableSpace V]

/-! ### Outer Minkowski content on a metric space -/

/-- Outer Minkowski content `ν⁺(B) = liminf_{r ↓ 0} (ν(B^r) - ν(B)) / r` of a probability law on a
metric space, with open thickenings; on the coordinate space this is the coordinate-space form of
`boundaryContent`. -/
def minkowskiContent (ν : Measure V) (B : Set V) : ℝ≥0∞ :=
  liminf (fun r : ℝ ↦
    ((ν : Measure V) (Metric.thickening r B) - (ν : Measure V) B) / ENNReal.ofReal r) (𝓝[>] 0)

/-- `liminf` commutes with multiplication by a finite constant on `ℝ≥0∞` (a local tool used for
the scaling of contents). -/
theorem liminf_coe_mul {ι : Type*} {l : Filter ι} [l.NeBot] (c : ℝ≥0) (u : ι → ℝ≥0∞) :
    liminf (fun i => (c : ℝ≥0∞) * u i) l = c * liminf u l := by
  have hmono : Monotone fun x : ℝ≥0∞ => (c : ℝ≥0∞) * x := fun _ _ h => mul_le_mul' le_rfl h
  have h := hmono.map_liminf_of_continuousAt (F := l) u
    (ENNReal.continuous_const_mul ENNReal.coe_ne_top).continuousAt
  simpa [Function.comp_def] using h.symm

/-- `limsup` commutes with multiplication by a finite constant on `ℝ≥0∞` (a local tool). -/
theorem limsup_coe_mul {ι : Type*} {l : Filter ι} [l.NeBot] (c : ℝ≥0) (u : ι → ℝ≥0∞) :
    limsup (fun i => (c : ℝ≥0∞) * u i) l = c * limsup u l := by
  have hmono : Monotone fun x : ℝ≥0∞ => (c : ℝ≥0∞) * x := fun _ _ h => mul_le_mul' le_rfl h
  have h := hmono.map_limsup_of_continuousAt (F := l) u
    (ENNReal.continuous_const_mul ENNReal.coe_ne_top).continuousAt
  simpa [Function.comp_def] using h.symm

/-- **Content scaling**: `minkowskiContent (c • ν) B = c * minkowskiContent ν B` for every
`c : ℝ≥0` (finite scalar; the increment is scaled before the truncated subtraction). -/
theorem minkowskiContent_smul (c : ℝ≥0) (ν : Measure V) (B : Set V) :
    minkowskiContent (c • ν) B = c * minkowskiContent ν B := by
  unfold minkowskiContent
  rw [← liminf_coe_mul]
  refine liminf_congr (Eventually.of_forall fun r => ?_)
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  rw [← ENNReal.mul_sub (fun _ _ => ENNReal.coe_ne_top), mul_div_assoc]

/-- The zero measure has zero lower content. -/
theorem minkowskiContent_zero_measure (B : Set V) : minkowskiContent (0 : Measure V) B = 0 := by
  simpa using minkowskiContent_smul (0 : ℝ≥0) (0 : Measure V) B

/-- Finite target mass and finite lower content imply some positive thickening has finite
mass, even if the target is unbounded and the measure has infinite total mass. -/
theorem exists_measure_thickening_lt_top (ν : Measure V) {B : Set V} (hνB : ν B < ⊤)
    (hcontent : minkowskiContent ν B < ⊤) :
    ∃ R : ℝ, 0 < R ∧ ν (Metric.thickening R B) < ⊤ := by
  have ha : minkowskiContent ν B < minkowskiContent ν B + 1 :=
    ENNReal.lt_add_right hcontent.ne one_ne_zero
  have hf : ∃ᶠ r in 𝓝[>] (0 : ℝ),
      (ν (Metric.thickening r B) - ν B) / ENNReal.ofReal r < minkowskiContent ν B + 1 :=
    frequently_lt_of_liminf_lt (by isBoundedDefault) ha
  obtain ⟨R, hq, hR⟩ := (hf.and_eventually self_mem_nhdsWithin).exists
  have hqfin : (ν (Metric.thickening R B) - ν B) / ENNReal.ofReal R < ⊤ :=
    hq.trans (ENNReal.add_lt_top.2 ⟨hcontent, by norm_num⟩)
  have hinc : ν (Metric.thickening R B) - ν B < ⊤ := by
    have he := ENNReal.div_mul_cancel (b := ν (Metric.thickening R B) - ν B)
      (ENNReal.ofReal_pos.2 hR).ne' ENNReal.ofReal_ne_top
    rw [← he]
    exact ENNReal.mul_lt_top hqfin ENNReal.ofReal_lt_top
  exact ⟨R, hR, le_tsub_add.trans_lt (ENNReal.add_lt_top.2 ⟨hinc, hνB⟩)⟩

/-- Restriction preserves the lower content when a positive thickening is contained in
the measurable restriction region. No mass-finiteness assumption is needed. -/
theorem minkowskiContent_restrict_of_thickening_subset (ν : Measure V) {B U : Set V} (hU : MeasurableSet U)
    {δ : ℝ} (hδ : 0 < δ) (hsub : Metric.thickening δ B ⊆ U) :
    minkowskiContent (ν.restrict U) B = minkowskiContent ν B := by
  have hB : B ⊆ U := (Metric.self_subset_thickening hδ B).trans hsub
  unfold minkowskiContent
  apply liminf_congr
  filter_upwards [Ioo_mem_nhdsGT hδ] with r hr
  have ht : Metric.thickening r B ⊆ U := (Metric.thickening_mono hr.2.le B).trans hsub
  rw [Measure.restrict_apply' hU, Measure.restrict_apply' hU,
    Set.inter_eq_left.2 ht, Set.inter_eq_left.2 hB]
/-- The whole carrier has zero lower content for every measure, including infinite total mass.
This fact about truncated content does not assert zero bounded-support perimeter. -/
theorem minkowskiContent_univ (ν : Measure V) : minkowskiContent ν (Set.univ : Set V) = 0 := by
  unfold minkowskiContent
  have he : (fun r : ℝ => (ν (Metric.thickening r (Set.univ : Set V)) - ν Set.univ) /
      ENNReal.ofReal r) =ᶠ[𝓝[>] (0 : ℝ)] fun _ => 0 := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    have ht : Metric.thickening r (Set.univ : Set V) = Set.univ :=
      Set.eq_univ_of_univ_subset (Metric.self_subset_thickening hr Set.univ)
    simp [ht]
  rw [liminf_congr he, liminf_const]

/-- Finite Minkowski content forces the closure to carry no extra mass. -/
theorem measure_closure_eq_of_minkowskiContent_ne_top (ν : Measure V) [IsFiniteMeasure ν] {B : Set V}
    (h : minkowskiContent ν B ≠ ⊤) :
    (ν : Measure V) (closure B) = (ν : Measure V) B := by
  by_contra hne
  have hle : (ν : Measure V) B ≤ (ν : Measure V) (closure B) := measure_mono subset_closure
  have hlt : (ν : Measure V) B < (ν : Measure V) (closure B) := lt_of_le_of_ne hle (Ne.symm hne)
  set δ : ℝ≥0∞ := (ν : Measure V) (closure B) - (ν : Measure V) B with hδ
  have hδpos : 0 < δ := tsub_pos_of_lt hlt
  have hle2 : ∀ r : ℝ, 0 < r →
      δ / ENNReal.ofReal r ≤
        ((ν : Measure V) (Metric.thickening r B) - (ν : Measure V) B) / ENNReal.ofReal r := by
    intro r hr
    apply ENNReal.div_le_div_right
    have hsub : closure B ⊆ Metric.thickening r B := Metric.closure_subset_thickening hr B
    have hmono : (ν : Measure V) (closure B) ≤ (ν : Measure V) (Metric.thickening r B) :=
      measure_mono hsub
    exact tsub_le_tsub_right hmono _
  have htendsto : Tendsto (fun r : ℝ ↦ δ / ENNReal.ofReal r) (𝓝[>] 0) (𝓝 ⊤) := by
    have hinv : Tendsto (fun r : ℝ ↦ r⁻¹) (𝓝[>] (0 : ℝ)) atTop := tendsto_inv_nhdsGT_zero
    have h1 : Tendsto (fun r : ℝ ↦ ENNReal.ofReal r⁻¹) (𝓝[>] (0 : ℝ)) (𝓝 ⊤) :=
      ENNReal.tendsto_ofReal_nhds_top.mpr hinv
    have h2 : Tendsto (fun r : ℝ ↦ δ * ENNReal.ofReal r⁻¹) (𝓝[>] (0 : ℝ)) (𝓝 (δ * ⊤)) :=
      ENNReal.Tendsto.const_mul h1 (Or.inl ENNReal.top_ne_zero)
    rw [ENNReal.mul_top hδpos.ne'] at h2
    refine h2.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    rw [ENNReal.ofReal_inv_of_pos hr, div_eq_mul_inv]
  have hliminf_top : liminf (fun r : ℝ ↦ δ / ENNReal.ofReal r) (𝓝[>] 0) = ⊤ := htendsto.liminf_eq
  have hmono2 : liminf (fun r : ℝ ↦ δ / ENNReal.ofReal r) (𝓝[>] 0) ≤
      liminf (fun r : ℝ ↦
        ((ν : Measure V) (Metric.thickening r B) - (ν : Measure V) B) / ENNReal.ofReal r)
        (𝓝[>] 0) :=
    liminf_le_liminf (by filter_upwards [self_mem_nhdsWithin] with r hr; exact hle2 r hr)
  rw [hliminf_top] at hmono2
  exact h (top_le_iff.mp hmono2)

section BorelMajorants
variable {V : Type*} [MetricSpace V] [MeasurableSpace V] [BorelSpace V]

/-- Measurable-strip layer cake and Fatou bound the content integral by the liminf
of integrated majorant growth at any positive radii tending to zero. This is the
sequence-growth step before dominated reverse Fatou, on arbitrary metric Borel spaces. -/
theorem lintegral_minkowskiContent_superlevel_le_liminf_of_majorant (ν : Measure V) [IsFiniteMeasure ν]
    {u : V → ℝ} {K : ℝ≥0} (hK : LipschitzWith K u) {r : ℕ → ℝ} (hrpos : ∀ n, 0 < r n)
    (hr0 : Tendsto r atTop (𝓝 0)) {w : ℕ → V → ℝ} (hwmeas : ∀ n, Measurable (w n))
    (hwit : ∀ n t, Metric.thickening (r n) {x | t ≤ u x} ⊆
      {x | u x < t ∧ t ≤ w n x} ∪ {x | t ≤ u x}) :
    ∫⁻ t, minkowskiContent ν {x | t ≤ u x} ∂(volume : Measure ℝ) ≤
      liminf (fun n : ℕ => ∫⁻ x, ENNReal.ofReal ((w n x - u x) / r n) ∂ν) atTop := by
  classical
  have hrW : Tendsto r atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hr0
      (Eventually.of_forall hrpos)
  have humeas : Measurable u := hK.continuous.measurable
  set T : ℕ → Set (ℝ × V) := fun n => {p | u p.2 < p.1 ∧ p.1 ≤ w n p.2} with hTdef
  have hTmeas : ∀ n, MeasurableSet (T n) := fun n =>
    (measurableSet_lt (humeas.comp measurable_snd) measurable_fst).inter
      (measurableSet_le measurable_fst ((hwmeas n).comp measurable_snd))
  set S : ℕ → ℝ → Set V := fun n t => {x | u x < t ∧ t ≤ w n x} with hSdef
  set G : ℕ → ℝ → ℝ≥0∞ := fun n t => (ν : Measure V) (S n t) / ENNReal.ofReal (r n) with hGdef
  have hmeasfun : ∀ n, Measurable fun t : ℝ => (ν : Measure V) (S n t) := fun n =>
    measurable_measure_prodMk_left (ν := (ν : Measure V)) (hTmeas n)
  have hGmeas : ∀ n, Measurable (G n) := by
    intro n
    simpa [hGdef, div_eq_mul_inv] using
      (hmeasfun n).mul_const ((ENNReal.ofReal (r n))⁻¹)
  -- Step 1: the near-neighbour witness bounds the content by a measurable strip quotient.
  have step1 : ∀ t : ℝ, minkowskiContent ν {x | t ≤ u x} ≤ liminf (fun n => G n t) atTop := by
    intro t
    have h1 : minkowskiContent ν {x | t ≤ u x} ≤
        liminf (fun n => ((ν : Measure V) (Metric.thickening (r n) {x | t ≤ u x}) -
          (ν : Measure V) {x | t ≤ u x}) / ENNReal.ofReal (r n)) atTop := by
      have hcomp := hrW.liminf_le_liminf_comp (u := fun s : ℝ =>
        ((ν : Measure V) (Metric.thickening s {x | t ≤ u x}) -
          (ν : Measure V) {x | t ≤ u x}) / ENNReal.ofReal s)
      simpa [minkowskiContent, Function.comp_def] using hcomp
    refine h1.trans (liminf_le_liminf (Eventually.of_forall fun n => ?_))
    refine ENNReal.div_le_div_right (tsub_le_iff_right.mpr ?_) _
    calc (ν : Measure V) (Metric.thickening (r n) {x | t ≤ u x})
        ≤ (ν : Measure V) (S n t ∪ {x | t ≤ u x}) := measure_mono (hwit n t)
      _ ≤ (ν : Measure V) (S n t) + (ν : Measure V) {x | t ≤ u x} := measure_union_le _ _
  -- Step 2: Tonelli turns the strip integral into the growth quotient.
  have step2 : ∀ n, ∫⁻ t, G n t ∂(volume : Measure ℝ) =
      ∫⁻ x, ENNReal.ofReal ((w n x - u x) / r n) ∂(ν : Measure V) := by
    intro n
    have hrne : ENNReal.ofReal (r n) ≠ 0 := by
      simp [ENNReal.ofReal_eq_zero, not_le, hrpos n]
    have hinvne : (ENNReal.ofReal (r n))⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hrne
    have hsec : ∀ x : V, (fun t : ℝ => (t, x)) ⁻¹' T n = Set.Ioc (u x) (w n x) := by
      intro x
      ext t
      simp [hTdef, Set.mem_Ioc]
    calc ∫⁻ t, G n t ∂(volume : Measure ℝ)
        = ∫⁻ t, (ν : Measure V) (Prod.mk t ⁻¹' T n) * (ENNReal.ofReal (r n))⁻¹
            ∂(volume : Measure ℝ) := by
          simp [hGdef, hTdef, hSdef, div_eq_mul_inv]
      _ = (∫⁻ t, (ν : Measure V) (Prod.mk t ⁻¹' T n) ∂(volume : Measure ℝ)) *
            (ENNReal.ofReal (r n))⁻¹ := lintegral_mul_const' _ _ hinvne
      _ = ((volume : Measure ℝ).prod (ν : Measure V)) (T n) * (ENNReal.ofReal (r n))⁻¹ := by
          rw [Measure.prod_apply (hTmeas n)]
      _ = (∫⁻ x, (volume : Measure ℝ) ((fun t : ℝ => (t, x)) ⁻¹' T n) ∂(ν : Measure V)) *
            (ENNReal.ofReal (r n))⁻¹ := by rw [Measure.prod_apply_symm (hTmeas n)]
      _ = (∫⁻ x, ENNReal.ofReal (w n x - u x) ∂(ν : Measure V)) *
            (ENNReal.ofReal (r n))⁻¹ := by
          congr 1
          refine lintegral_congr fun x => ?_
          rw [hsec x, Real.volume_Ioc]
      _ = ∫⁻ x, ENNReal.ofReal (w n x - u x) * (ENNReal.ofReal (r n))⁻¹
            ∂(ν : Measure V) := (lintegral_mul_const' _ _ hinvne).symm
      _ = ∫⁻ x, ENNReal.ofReal ((w n x - u x) / r n) ∂(ν : Measure V) := by
          refine lintegral_congr fun x => ?_
          rw [ENNReal.ofReal_div_of_pos (hrpos n), div_eq_mul_inv]
  calc ∫⁻ t, minkowskiContent ν {x | t ≤ u x} ∂(volume : Measure ℝ)
      ≤ ∫⁻ t, liminf (fun n => G n t) atTop ∂(volume : Measure ℝ) := lintegral_mono step1
    _ ≤ liminf (fun n => ∫⁻ t, G n t ∂(volume : Measure ℝ)) atTop := lintegral_liminf_le hGmeas
    _ = liminf (fun n => ∫⁻ x, ENNReal.ofReal ((w n x - u x) / r n)
          ∂(ν : Measure V)) atTop := by simp only [step2]


/-- Layer cake for a globally Lipschitz function with an abstract measurable majorant family
`w n`: if each `w n` carries the near-neighbour witness for the radius `r n` and exceeds `u` by
at most `K · r n`, the superlevel-content integral is at most the integrated limsup of the growth
quotients `(w n x - u x) / r n`.  The proof is the near-neighbour witness, measurable strips,
Tonelli, Fatou and reverse Fatou under the uniform Lipschitz bound; it holds on every metric
space with a Borel probability law. -/
theorem lintegral_minkowskiContent_superlevel_le_limsup_of_majorant (ν : Measure V) [IsFiniteMeasure ν]
    {u : V → ℝ} {K : ℝ≥0} (hK : LipschitzWith K u) {r : ℕ → ℝ} (hrpos : ∀ n, 0 < r n)
    (hr0 : Tendsto r atTop (𝓝 0)) {w : ℕ → V → ℝ} (hwmeas : ∀ n, Measurable (w n))
    (hwit : ∀ n t, Metric.thickening (r n) {x | t ≤ u x} ⊆
      {x | u x < t ∧ t ≤ w n x} ∪ {x | t ≤ u x})
    (hwle : ∀ n x, w n x ≤ u x + K * r n) :
    ∫⁻ t, minkowskiContent ν {x | t ≤ u x} ∂(volume : Measure ℝ) ≤
      ∫⁻ x, limsup (fun n : ℕ => ENNReal.ofReal ((w n x - u x) / r n)) atTop ∂(ν : Measure V) := by
  have hlower := lintegral_minkowskiContent_superlevel_le_liminf_of_majorant ν hK hrpos hr0 hwmeas hwit
  have humeas : Measurable u := hK.continuous.measurable
  -- Step 3: the growth quotients are uniformly bounded by the Lipschitz constant.
  have hqmeas : ∀ n, Measurable fun x : V => ENNReal.ofReal ((w n x - u x) / r n) :=
    fun n => (((hwmeas n).sub humeas).div_const _).ennreal_ofReal
  have hqbound : ∀ n, ∀ x : V,
      ENNReal.ofReal ((w n x - u x) / r n) ≤ ENNReal.ofReal (K : ℝ) := by
    intro n x
    refine ENNReal.ofReal_le_ofReal ?_
    rw [div_le_iff₀ (hrpos n)]
    linarith [hwle n x]
  have hgfin : ∫⁻ _ : V, ENNReal.ofReal (K : ℝ) ∂(ν : Measure V) ≠ ⊤ := by
    rw [lintegral_const]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  calc ∫⁻ t, minkowskiContent ν {x | t ≤ u x} ∂(volume : Measure ℝ)
      ≤ liminf (fun n => ∫⁻ x, ENNReal.ofReal ((w n x - u x) / r n) ∂ν) atTop := hlower
    _ ≤ limsup (fun n => ∫⁻ x, ENNReal.ofReal ((w n x - u x) / r n) ∂ν) atTop := liminf_le_limsup
    _ ≤ ∫⁻ x, limsup (fun n => ENNReal.ofReal ((w n x - u x) / r n)) atTop ∂ν :=
      limsup_lintegral_le _ hqmeas (fun n => Eventually.of_forall (hqbound n)) hgfin


end BorelMajorants

end Generic

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]

/-! ### Local suprema of a Lipschitz function over closed balls (normed scope) -/

section BallSup

omit [InnerProductSpace ℝ V] [CompleteSpace V] [MeasurableSpace V] [BorelSpace V]
  [SecondCountableTopology V] [FiniteDimensional ℝ V]

/-- The supremum of `u` over the closed ball of radius `r` around `x`.  For a globally Lipschitz
`u` and `0 ≤ r` the defining family is nonempty and bounded above. -/
def ballSup (u : V → ℝ) (r : ℝ) (x : V) : ℝ := sSup (u '' Metric.closedBall x r)

variable {u : V → ℝ} {K : ℝ≥0} {r : ℝ}

/-- A Lipschitz function is bounded above on a closed ball by its value at the centre. -/
theorem bddAbove_image_closedBall (hK : LipschitzWith K u) (r : ℝ) (x : V) :
    BddAbove (u '' Metric.closedBall x r) := by
  refine ⟨u x + K * r, ?_⟩
  rintro a ⟨y, hy, rfl⟩
  have hd : dist (u y) (u x) ≤ K * dist y x := hK.dist_le_mul y x
  rw [Real.dist_eq] at hd
  have hyx : dist y x ≤ r := by simpa [Metric.mem_closedBall] using hy
  have h2 : |u y - u x| ≤ (K : ℝ) * r := hd.trans (by gcongr)
  linarith [(abs_le.mp h2).2]

/-- The centre value is below the local supremum. -/
theorem le_ballSup (hK : LipschitzWith K u) (hr : 0 ≤ r) (x : V) : u x ≤ ballSup u r x :=
  le_csSup (bddAbove_image_closedBall hK r x) ⟨x, Metric.mem_closedBall_self hr, rfl⟩

/-- The local supremum exceeds the centre value by at most `K r`. -/
theorem ballSup_le_add (hK : LipschitzWith K u) (hr : 0 ≤ r) (x : V) :
    ballSup u r x ≤ u x + K * r := by
  refine csSup_le ⟨u x, x, Metric.mem_closedBall_self hr, rfl⟩ ?_
  rintro a ⟨y, hy, rfl⟩
  have hd : dist (u y) (u x) ≤ K * dist y x := hK.dist_le_mul y x
  rw [Real.dist_eq] at hd
  have hyx : dist y x ≤ r := by simpa [Metric.mem_closedBall] using hy
  have h2 : |u y - u x| ≤ (K : ℝ) * r := hd.trans (by gcongr)
  linarith [(abs_le.mp h2).2]

/-- Translating the ball shows that the local supremum inherits the Lipschitz constant. -/
theorem lipschitzWith_ballSup (hK : LipschitzWith K u) (hr : 0 ≤ r) :
    LipschitzWith K (ballSup u r) := by
  have key : ∀ x y : V, ballSup u r x ≤ ballSup u r y + K * dist x y := by
    intro x y
    refine csSup_le ⟨u x, x, Metric.mem_closedBall_self hr, rfl⟩ ?_
    rintro a ⟨z, hz, rfl⟩
    have hzx : dist z x ≤ r := by simpa [Metric.mem_closedBall] using hz
    have hmem : z + (y - x) ∈ Metric.closedBall y r := by
      have hshift : dist (z + (y - x)) y = dist z x := by
        rw [dist_eq_norm, dist_eq_norm]
        congr 1
        abel
      simpa [Metric.mem_closedBall, hshift] using hzx
    have hle : u (z + (y - x)) ≤ ballSup u r y :=
      le_csSup (bddAbove_image_closedBall hK r y) ⟨z + (y - x), hmem, rfl⟩
    have hd : dist (u z) (u (z + (y - x))) ≤ K * dist z (z + (y - x)) := hK.dist_le_mul _ _
    rw [Real.dist_eq] at hd
    have hdist : dist z (z + (y - x)) = dist x y := by
      rw [dist_eq_norm, dist_eq_norm]
      congr 1
      abel
    rw [hdist] at hd
    linarith [(abs_le.mp hd).2]
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.dist_eq, abs_sub_le_iff]
  have h1 := key x y
  have h2 := key y x
  rw [dist_comm y x] at h2
  exact ⟨by linarith, by linarith⟩

/-- Near-neighbour witness: a point of the open `r`-thickening of a closed superlevel set either
lies in the set or has a local supremum reaching the level. -/
theorem thickening_superlevel_subset (hK : LipschitzWith K u) (r : ℝ) (t : ℝ) :
    Metric.thickening r {x : V | t ≤ u x} ⊆
      {x : V | u x < t ∧ t ≤ ballSup u r x} ∪ {x : V | t ≤ u x} := by
  intro x hx
  by_cases hxt : t ≤ u x
  · exact Or.inr hxt
  refine Or.inl ⟨not_le.mp hxt, ?_⟩
  obtain ⟨z, hz, hdz⟩ := Metric.mem_thickening_iff.mp hx
  refine hz.trans (le_csSup (bddAbove_image_closedBall hK r x) ⟨z, ?_, rfl⟩)
  simpa [Metric.mem_closedBall, dist_comm] using hdz.le

end BallSup

omit [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V] in
/-- Fréchet differentiability controls the normalized local growth of `u`: along positive radii
tending to zero the growth quotient `(ballSup u r x - u x) / r` is asymptotically at most the
gradient norm.  Only the upper bound is proved; it is what the coarea estimate needs. -/
theorem limsup_ofReal_ballSup_le {u : V → ℝ} {x : V} (hx : DifferentiableAt ℝ u x)
    {r : ℕ → ℝ} (hrpos : ∀ n, 0 < r n) (hr0 : Tendsto r atTop (𝓝 0)) :
    limsup (fun n => ENNReal.ofReal ((ballSup u (r n) x - u x) / r n)) atTop
      ≤ ‖gradient u x‖ₑ := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hεR : (0 : ℝ) < (ε : ℝ) := hε
  have hlo : (fun h => u (x + h) - u x - inner ℝ (gradient u x) h) =o[𝓝 0] fun h : V => h :=
    hasGradientAt_iff_isLittleO_nhds_zero.mp hx.hasGradientAt
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp (hlo.def hεR)
  have hsmall : ∀ᶠ n in atTop, r n < δ := hr0.eventually_lt_const hδ
  refine limsup_le_of_le ?_ ?_
  · exact isCobounded_le_of_bot
  filter_upwards [hsmall] with n hn
  have hle : ballSup u (r n) x ≤ u x + (‖gradient u x‖ + (ε : ℝ)) * r n := by
    refine csSup_le ⟨u x, x, Metric.mem_closedBall_self (hrpos n).le, rfl⟩ ?_
    rintro a ⟨y, hy, rfl⟩
    have hyx : dist y x ≤ r n := by simpa [Metric.mem_closedBall] using hy
    have hnorm : ‖y - x‖ ≤ r n := by simpa [dist_eq_norm] using hyx
    have hdlt : dist (y - x) 0 < δ := by
      simpa [dist_zero_right] using lt_of_le_of_lt hnorm hn
    have hkey := hball hdlt
    have hrw : x + (y - x) = y := by abel
    rw [hrw] at hkey
    have habs : |u y - u x - inner ℝ (gradient u x) (y - x)| ≤ (ε : ℝ) * ‖y - x‖ := by
      simpa [Real.norm_eq_abs] using hkey
    have hεmul : (ε : ℝ) * ‖y - x‖ ≤ (ε : ℝ) * r n :=
      mul_le_mul_of_nonneg_left hnorm hεR.le
    have hinner : inner ℝ (gradient u x) (y - x) ≤ ‖gradient u x‖ * ‖y - x‖ :=
      real_inner_le_norm _ _
    have hgmul : ‖gradient u x‖ * ‖y - x‖ ≤ ‖gradient u x‖ * r n :=
      mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)
    have h1 := (abs_le.mp habs).2
    nlinarith [h1, hεmul, hinner, hgmul]
  have hquot : (ballSup u (r n) x - u x) / r n ≤ ‖gradient u x‖ + (ε : ℝ) := by
    rw [div_le_iff₀ (hrpos n)]
    linarith
  calc ENNReal.ofReal ((ballSup u (r n) x - u x) / r n)
      ≤ ENNReal.ofReal (‖gradient u x‖ + (ε : ℝ)) := ENNReal.ofReal_le_ofReal hquot
    _ = ‖gradient u x‖ₑ + (ε : ℝ≥0∞) := by
        rw [ENNReal.ofReal_add (norm_nonneg _) ε.coe_nonneg, ofReal_norm,
          ENNReal.ofReal_coe_nnreal]

/-! ### The Minkowski coarea inequality -/

-- Finite dimensionality is retained explicitly in this Minkowski coarea interface.
omit [FiniteDimensional ℝ V] in
-- The ambient SecondCountableTopology parameter is part of this theorem's public scope.
set_option linter.unusedSectionVars false in
/-- Minkowski coarea inequality (Ambrosio–Di Marino–Gigli 2017, Lemma 3.2) for a `C¹` Lipschitz
function, with closed superlevel sets and the Euclidean gradient: `∫ ν⁺({u ≥ t}) dt ≤ ∫ ‖∇u‖ dν`.
No density is assumed. -/
theorem lintegral_minkowskiContent_superlevel_le
    [FiniteDimensional ℝ V]
    (ν : Measure V) [IsFiniteMeasure ν] {u : V → ℝ}
    (hu : ContDiff ℝ 1 u) {K : ℝ≥0} (hK : LipschitzWith K u) :
    ∫⁻ t, minkowskiContent ν {x | t ≤ u x} ∂(volume : Measure ℝ) ≤
      ∫⁻ x, ‖gradient u x‖ₑ ∂(ν : Measure V) := by
  classical
  set r : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hrdef
  have hrpos : ∀ n, 0 < r n := fun n => by
    have : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    simpa [hrdef] using one_div_pos.mpr this
  have hr0 : Tendsto r atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hbmeas : ∀ n, Measurable (ballSup u (r n)) := fun n =>
    (lipschitzWith_ballSup hK (hrpos n).le).continuous.measurable
  exact (lintegral_minkowskiContent_superlevel_le_limsup_of_majorant ν hK hrpos hr0 hbmeas
    (fun n t => thickening_superlevel_subset hK (r n) t)
    (fun n x => ballSup_le_add hK (hrpos n).le x)).trans
      (lintegral_mono fun x =>
        limsup_ofReal_ballSup_le (hu.differentiable one_ne_zero x) hrpos hr0)
end FunctionalInequalities.KLS.Isoperimetry
