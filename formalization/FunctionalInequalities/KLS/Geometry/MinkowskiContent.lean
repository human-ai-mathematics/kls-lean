import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Outer Minkowski content and the Minkowski coarea inequality

Hole-free coordinate-space companion of `KLS/Isoperimetry.lean`: `minkowskiContent` is
`boundaryContent` written on the ambient space itself, with open thickenings, `ENNReal`
truncated subtraction and a right-neighbourhood `liminf` at `r ↓ 0`.

The module proves `lintegral_minkowskiContent_superlevel_le`, the Minkowski coarea inequality of
Ambrosio--Di Marino--Gigli 2017, Lemma 3.2: for a `C¹` globally Lipschitz `u`,
`∫ ν⁺({u ≥ t}) dt ≤ ∫ ‖∇u‖ dν`.  The law is an arbitrary probability measure; no density,
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

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]

/-! ### Outer Minkowski content on the coordinate space -/

/-- Outer Minkowski content `ν⁺(B) = liminf_{r ↓ 0} (ν(B^r) - ν(B)) / r` on the coordinate space,
with open thickenings; the coordinate-space form of `boundaryContent`. -/
def minkowskiContent (ν : ProbabilityMeasure V) (B : Set V) : ℝ≥0∞ :=
  liminf (fun r : ℝ ↦
    ((ν : Measure V) (Metric.thickening r B) - (ν : Measure V) B) / ENNReal.ofReal r) (𝓝[>] 0)

omit [InnerProductSpace ℝ V] [CompleteSpace V] [BorelSpace V] [SecondCountableTopology V]
  [FiniteDimensional ℝ V] in
/-- Finite Minkowski content forces the closure to carry no extra mass. -/
theorem measure_closure_eq_of_minkowskiContent_ne_top (ν : ProbabilityMeasure V) {B : Set V}
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

/-! ### Local suprema of a Lipschitz function -/

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

-- The type class assumptions are the ones fixed by the original statement; `FiniteDimensional ℝ V`
-- became unused only because the body is now a proof rather than `sorry`, so the linter is
-- silenced instead of the mathematical scope of the statement changed.
set_option linter.unusedSectionVars false in
/-- Minkowski coarea inequality (Ambrosio–Di Marino–Gigli 2017, Lemma 3.2) for a `C¹` Lipschitz
function, with closed superlevel sets and the Euclidean gradient: `∫ ν⁺({u ≥ t}) dt ≤ ∫ ‖∇u‖ dν`.
No density is assumed. -/
theorem lintegral_minkowskiContent_superlevel_le (ν : ProbabilityMeasure V) {u : V → ℝ}
    (hu : ContDiff ℝ 1 u) {K : ℝ≥0} (hK : LipschitzWith K u) :
    ∫⁻ t, minkowskiContent ν {x | t ≤ u x} ∂(volume : Measure ℝ) ≤
      ∫⁻ x, ‖gradient u x‖ₑ ∂(ν : Measure V) := by
  classical
  set r : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hrdef
  have hrpos : ∀ n, 0 < r n := fun n => by
    have : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    simpa [hrdef] using one_div_pos.mpr this
  have hr0 : Tendsto r atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hrW : Tendsto r atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hr0
      (Eventually.of_forall hrpos)
  have humeas : Measurable u := hu.continuous.measurable
  have hbmeas : ∀ n, Measurable (ballSup u (r n)) := fun n =>
    (lipschitzWith_ballSup hK (hrpos n).le).continuous.measurable
  set T : ℕ → Set (ℝ × V) := fun n => {p | u p.2 < p.1 ∧ p.1 ≤ ballSup u (r n) p.2} with hTdef
  have hTmeas : ∀ n, MeasurableSet (T n) := fun n =>
    (measurableSet_lt (humeas.comp measurable_snd) measurable_fst).inter
      (measurableSet_le measurable_fst ((hbmeas n).comp measurable_snd))
  set S : ℕ → ℝ → Set V := fun n t => {x | u x < t ∧ t ≤ ballSup u (r n) x} with hSdef
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
        ≤ (ν : Measure V) (S n t ∪ {x | t ≤ u x}) :=
          measure_mono (thickening_superlevel_subset hK (r n) t)
      _ ≤ (ν : Measure V) (S n t) + (ν : Measure V) {x | t ≤ u x} := measure_union_le _ _
  -- Step 2: Tonelli turns the strip integral into the growth quotient.
  have step2 : ∀ n, ∫⁻ t, G n t ∂(volume : Measure ℝ) =
      ∫⁻ x, ENNReal.ofReal ((ballSup u (r n) x - u x) / r n) ∂(ν : Measure V) := by
    intro n
    have hrne : ENNReal.ofReal (r n) ≠ 0 := by
      simp [ENNReal.ofReal_eq_zero, not_le, hrpos n]
    have hinvne : (ENNReal.ofReal (r n))⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hrne
    have hsec : ∀ x : V, (fun t : ℝ => (t, x)) ⁻¹' T n = Set.Ioc (u x) (ballSup u (r n) x) := by
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
      _ = (∫⁻ x, ENNReal.ofReal (ballSup u (r n) x - u x) ∂(ν : Measure V)) *
            (ENNReal.ofReal (r n))⁻¹ := by
          congr 1
          refine lintegral_congr fun x => ?_
          rw [hsec x, Real.volume_Ioc]
      _ = ∫⁻ x, ENNReal.ofReal (ballSup u (r n) x - u x) * (ENNReal.ofReal (r n))⁻¹
            ∂(ν : Measure V) := (lintegral_mul_const' _ _ hinvne).symm
      _ = ∫⁻ x, ENNReal.ofReal ((ballSup u (r n) x - u x) / r n) ∂(ν : Measure V) := by
          refine lintegral_congr fun x => ?_
          rw [ENNReal.ofReal_div_of_pos (hrpos n), div_eq_mul_inv]
  -- Step 3: the growth quotients are uniformly bounded and dominated by the gradient norm.
  have hqmeas : ∀ n, Measurable fun x : V => ENNReal.ofReal ((ballSup u (r n) x - u x) / r n) :=
    fun n => (((hbmeas n).sub humeas).div_const _).ennreal_ofReal
  have hqbound : ∀ n, ∀ x : V,
      ENNReal.ofReal ((ballSup u (r n) x - u x) / r n) ≤ ENNReal.ofReal (K : ℝ) := by
    intro n x
    refine ENNReal.ofReal_le_ofReal ?_
    rw [div_le_iff₀ (hrpos n)]
    linarith [ballSup_le_add hK (hrpos n).le x]
  have hgfin : ∫⁻ _ : V, ENNReal.ofReal (K : ℝ) ∂(ν : Measure V) ≠ ⊤ := by
    simp [lintegral_const, measure_univ]
  calc ∫⁻ t, minkowskiContent ν {x | t ≤ u x} ∂(volume : Measure ℝ)
      ≤ ∫⁻ t, liminf (fun n => G n t) atTop ∂(volume : Measure ℝ) := lintegral_mono step1
    _ ≤ liminf (fun n => ∫⁻ t, G n t ∂(volume : Measure ℝ)) atTop := lintegral_liminf_le hGmeas
    _ = liminf (fun n => ∫⁻ x, ENNReal.ofReal ((ballSup u (r n) x - u x) / r n)
          ∂(ν : Measure V)) atTop := by simp only [step2]
    _ ≤ limsup (fun n => ∫⁻ x, ENNReal.ofReal ((ballSup u (r n) x - u x) / r n)
          ∂(ν : Measure V)) atTop := liminf_le_limsup
    _ ≤ ∫⁻ x, limsup (fun n => ENNReal.ofReal ((ballSup u (r n) x - u x) / r n)) atTop
          ∂(ν : Measure V) :=
        limsup_lintegral_le _ hqmeas (fun n => Eventually.of_forall (hqbound n)) hgfin
    _ ≤ ∫⁻ x, ‖gradient u x‖ₑ ∂(ν : Measure V) :=
        lintegral_mono fun x =>
          limsup_ofReal_ballSup_le (hu.differentiable one_ne_zero x) hrpos hr0

end FunctionalInequalities.KLS.Isoperimetry
