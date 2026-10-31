module

public import FunctionalInequalities.Analysis.Hausdorff.Volume
public import FunctionalInequalities.Analysis.Vector.Slice.Hausdorff

/-! # What the small-Lipschitz method actually yields: the exponent of the obstruction

The projected small-Lipschitz argument gives nullity at an exponent larger than the one needed for
critical-fibre nullity. The distinction is quantified below.

Suppose the composite `Q ∘ u` — the part of `u` orthogonal to the range of its differential — can,
at every scale `ε`, be made `ε`-Lipschitz on the pieces of a countable measurable partition of `S`.
Running the codimension-`dim W₂` Eilenberg inequality on each piece and letting `ε → 0` gives

`μH[n − dim W₂] (S ∩ {Q ∘ u = τ}) = 0` for almost every `τ ∈ W₂`.

**That exponent is `k + r`, not `k`.**  On the rank-`r` stratum `W₂` is the orthogonal complement of
the rank-`r` range, so `dim W₂ = m − r` and the exponent is `n − (m − r) = k + r`.  For `r ≥ 1` this
is strictly weaker than critical-fibre nullity in the useless direction: a set can be `μH[k +
r]`-null and still carry
infinite `μH[k]`.  Hence critical-fibre nullity is proved by slicing **inside a fibre**, which is
what `Analysis/Vector/RankDeficient/StratumSlicing.lean` does, and why this file is a diagnostic
with **no consumer**.

**Both side conditions are used and both are real.**  `S` must be measurable
for the majorants of the disjoint pieces to add up to the majorant of `S`, and `0 < finrank ℝ W₂`
is what makes the Eilenberg constant `ε ^ (dim W₂)` tend to `0` — with `dim W₂ = 0` the constant is
`1`, nothing tends to zero, and the statement is false.

**The truncated exponent is harmless here.**  `finrank ℝ V - finrank ℝ W₂` is a natural subtraction,
so when the target is larger than the domain it collapses to `0` rather than going negative.  The
proof never needs `finrank ℝ W₂ ≤ finrank ℝ V`: all it uses is
`(n - m) + m ≥ n`, which holds in `ℕ` either way and keeps the Eilenberg right-hand side
`μH[(n − m) + m] S ≤ μH[n] S` finite.  This is the point on which the companion exponent comparison
fails, and the weaker-exponent statement survives it.

**The companion exponent comparison is false without a positive dimension**, and
`hausdorffMeasure_finrank_sub_eq_top`
below is its repair: below the top dimension a set of positive Lebesgue measure has infinite
Hausdorff measure, **provided the dimension is positive**.  That proviso is necessary: in
dimension zero a nonempty set has `μH[0] = 1`.  The repaired statement is also what makes the
weaker-exponent statement
useless for critical-fibre nullity: at the exponent `k` the measure is already infinite, so nullity
at `k + r` says
nothing.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set Module
open scoped ENNReal NNReal

namespace FunctionalInequalities.Analysis

section ExponentObstruction

variable {V W W₂ : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [NormedAddCommGroup W₂] [InnerProductSpace ℝ W₂] [FiniteDimensional ℝ W₂]
  [MeasurableSpace W₂] [BorelSpace W₂]

omit [FiniteDimensional ℝ V] in
/-- The Eilenberg right-hand side at the truncated exponent is bounded by the top-dimensional one.
In `ℕ` one has `(n - m) + m ≥ n` whether or not `m ≤ n`, and the Hausdorff measure decreases in the
exponent. -/
theorem hausdorffMeasure_truncated_add_le (S : Set V) (m : ℕ) :
    μH[((finrank ℝ V - m : ℕ) : ℝ) + (m : ℝ)] S ≤ μH[((finrank ℝ V : ℕ) : ℝ)] S := by
  refine Measure.hausdorffMeasure_mono ?_ S
  have h : (finrank ℝ V : ℕ) ≤ (finrank ℝ V - m : ℕ) + m := by omega
  exact_mod_cast h

/-! ### The exponent comparison, repaired -/

omit [FiniteDimensional ℝ W] [MeasurableSpace W₂] [BorelSpace W₂] in
/--
**The exponent comparison, repaired.**  Below the top dimension the Hausdorff measure of a set of
positive
Lebesgue measure is infinite.  The hypothesis `0 < finrank ℝ V` is **necessary**: without
it the statement is false, because the truncated subtraction `finrank ℝ V - r` collapses to `0` in a
zero-dimensional space, where a nonempty set has `μH[0] = 1` rather than `⊤`. -/
theorem hausdorffMeasure_finrank_sub_eq_top {S : Set V} {r : ℕ} (hn : 0 < finrank ℝ V)
    (hS : (volume : Measure V) S ≠ 0) (hr : 0 < r) : μH[((finrank ℝ V - r : ℕ) : ℝ)] S = ⊤ := by
  have hωpos : 0 < KLS.unitBallVolume (finrank ℝ V) := by unfold KLS.unitBallVolume; positivity
  have hcpos : (0 : ℝ) < 2 ^ finrank ℝ V / KLS.unitBallVolume (finrank ℝ V) := by positivity
  have htop : μH[((finrank ℝ V : ℕ) : ℝ)] S ≠ 0 := by
    rw [show ((finrank ℝ V : ℕ) : ℝ) = (finrank ℝ V : ℝ) from rfl,
      hausdorffMeasure_finrank_eq_smul_volume V, Measure.smul_apply, smul_eq_mul]
    exact mul_ne_zero (ENNReal.ofReal_pos.mpr hcpos).ne' hS
  have hlt : ((finrank ℝ V - r : ℕ) : ℝ) < ((finrank ℝ V : ℕ) : ℝ) := by
    have : (finrank ℝ V - r : ℕ) < finrank ℝ V := by omega
    exact_mod_cast this
  rcases Measure.hausdorffMeasure_zero_or_top hlt S with h | h
  · exact absurd h htop
  · exact h

/-! ### One scale of the small-Lipschitz method -/

section LipschitzSliceMajorants

omit [FiniteDimensional ℝ V] [FiniteDimensional ℝ W]
/-- **One scale of the small-Lipschitz method.**  Given a countable measurable partition of `S` on
whose pieces `Q ∘ u` is `ε`-Lipschitz, the slice function at the exponent
`n − dim W₂` is dominated by a **measurable** majorant whose integral is at most
`C · ε ^ (dim W₂) · μH[n] S`.  The slice function itself is not known to be measurable — no
regularity whatever is assumed of `u` — which is why the bound is carried by a majorant. -/
theorem exists_measurable_majorant_of_lipschitz_pieces {u : V → W} {S : Set V} (Q : W →L[ℝ] W₂)
    (hS : MeasurableSet S) (ε : ℝ≥0) {T : ℕ → Set V}
    (hdisj : Pairwise (Function.onFun Disjoint T)) (hTmeas : ∀ n, MeasurableSet (T n))
    (hcover : S ⊆ ⋃ n, T n)
    (hlip : ∀ n, LipschitzOnWith ε (fun x => Q (u x)) (S ∩ T n)) :
    ∃ G : W₂ → ℝ≥0∞, Measurable G ∧
      (∀ τ, μH[((finrank ℝ V - finrank ℝ W₂ : ℕ) : ℝ)] (S ∩ {x : V | Q (u x) = τ}) ≤ G τ) ∧
      (∫⁻ τ, G τ ∂(volume : Measure W₂))
        ≤ (volume : Measure W₂) (Metric.closedBall (0 : W₂) 1) * (ε : ℝ≥0∞) ^ (finrank ℝ W₂)
            * μH[((finrank ℝ V : ℕ) : ℝ)] S := by
  classical
  set d : ℝ := ((finrank ℝ V - finrank ℝ W₂ : ℕ) : ℝ) with hddef
  have hd : 0 ≤ d := by positivity
  set C : ℝ≥0∞ := (volume : Measure W₂) (Metric.closedBall (0 : W₂) 1) with hCdef
  choose F hFmeas hFdom hFint using fun n =>
    exists_measurable_majorant_vector (W := W₂) (S := S ∩ T n) hd (hlip n)
  -- the pieces are disjoint, measurable, and exhaust `S`
  have hpmeas : ∀ n, MeasurableSet (S ∩ T n) := fun n => hS.inter (hTmeas n)
  have hpdisj : Pairwise (Function.onFun Disjoint fun n => S ∩ T n) := fun i j hij =>
    (hdisj hij).mono Set.inter_subset_right Set.inter_subset_right
  have hunion : ⋃ n, S ∩ T n = S := by
    rw [← Set.inter_iUnion]
    exact Set.inter_eq_self_of_subset_left hcover
  refine ⟨fun τ => ∑' n, F n τ, Measurable.tsum hFmeas, fun τ => ?_, ?_⟩
  · calc μH[d] (S ∩ {x : V | Q (u x) = τ})
        ≤ μH[d] (⋃ n, (S ∩ T n) ∩ {x : V | Q (u x) = τ}) := by
          refine measure_mono fun x hx => ?_
          obtain ⟨n, hn⟩ := Set.mem_iUnion.1 (hcover hx.1)
          exact Set.mem_iUnion.2 ⟨n, ⟨⟨hx.1, hn⟩, hx.2⟩⟩
      _ ≤ ∑' n, μH[d] ((S ∩ T n) ∩ {x : V | Q (u x) = τ}) := measure_iUnion_le _
      _ ≤ ∑' n, F n τ := ENNReal.tsum_le_tsum fun n => hFdom n τ
  · calc (∫⁻ τ, ∑' n, F n τ ∂(volume : Measure W₂))
        = ∑' n, ∫⁻ τ, F n τ ∂(volume : Measure W₂) :=
          lintegral_tsum fun n => (hFmeas n).aemeasurable
      _ ≤ ∑' n, C * (ε : ℝ≥0∞) ^ (finrank ℝ W₂) * μH[d + (finrank ℝ W₂ : ℝ)] (S ∩ T n) :=
          ENNReal.tsum_le_tsum hFint
      _ = C * (ε : ℝ≥0∞) ^ (finrank ℝ W₂)
            * ∑' n, μH[d + (finrank ℝ W₂ : ℝ)] (S ∩ T n) := ENNReal.tsum_mul_left
      _ = C * (ε : ℝ≥0∞) ^ (finrank ℝ W₂) * μH[d + (finrank ℝ W₂ : ℝ)] S := by
          rw [← measure_iUnion hpdisj hpmeas, hunion]
      _ ≤ C * (ε : ℝ≥0∞) ^ (finrank ℝ W₂) * μH[((finrank ℝ V : ℕ) : ℝ)] S := by
          gcongr C * (ε : ℝ≥0∞) ^ (finrank ℝ W₂) * ?_
          rw [hddef]
          exact hausdorffMeasure_truncated_add_le S _

/--
**The weaker-exponent statement: the obstruction, stated.**  Projecting away the range of the
differential and running
the proved Eilenberg bound gives a null slicing statement at the exponent `n − dim W₂`, which in
the notation above is `k + r`, **not** `k`.  For `r ≥ 1` this is strictly weaker than critical-fibre
nullity in the
useless direction: a set can be `μH[k + r]`-null and have infinite `μH[k]`.

This is a **diagnostic**: it is not a step towards critical-fibre nullity, which was proved
independently in
`Analysis/Vector/RankDeficient/Coarea.lean` by slicing inside a fibre instead. -/
theorem ae_hausdorffMeasure_inter_levelSet_eq_zero_of_lipschitz_pieces {u : V → W} {S : Set V}
    (Q : W →L[ℝ] W₂) (hS : MeasurableSet S) (hW₂ : 0 < finrank ℝ W₂)
    (hSfin : μH[((finrank ℝ V : ℕ) : ℝ)] S ≠ ⊤)
    (hpieces :
      ∀ ε : ℝ≥0,
        ε ≠ 0 →
          ∃ T : ℕ → Set V,
            Pairwise (Function.onFun Disjoint T) ∧
              (∀ n, MeasurableSet (T n)) ∧
                S ⊆ ⋃ n, T n ∧ ∀ n, LipschitzOnWith ε (fun x => Q (u x)) (S ∩ T n)) :
    ∀ᵐ τ ∂(volume : Measure W₂),
      μH[((finrank ℝ V - finrank ℝ W₂ : ℕ) : ℝ)] (S ∩ {x : V | Q (u x) = τ}) = 0 := by
  classical
  set d : ℝ := ((finrank ℝ V - finrank ℝ W₂ : ℕ) : ℝ) with hddef
  set C : ℝ≥0∞ := (volume : Measure W₂) (Metric.closedBall (0 : W₂) 1) with hCdef
  have hCtop : C ≠ ⊤ := measure_closedBall_lt_top.ne
  set M : ℝ≥0∞ := μH[((finrank ℝ V : ℕ) : ℝ)] S with hMdef
  set e : ℕ → ℝ≥0 := fun j => ((j : ℝ≥0) + 1)⁻¹ with hedef
  have hepos : ∀ j, e j ≠ 0 := fun j => by
    simp [hedef, inv_eq_zero]
  -- a measurable majorant at every scale

  have hscale :
    ∀ j : ℕ,
      ∃ G : W₂ → ℝ≥0∞,
        Measurable G ∧
          (∀ τ, μH[d] (S ∩ {x : V | Q (u x) = τ}) ≤ G τ) ∧
            (∫⁻ τ, G τ ∂(volume : Measure W₂)) ≤ C * (e j : ℝ≥0∞) ^ (finrank ℝ W₂) * M := by
    intro j
    obtain ⟨T, hdisj, hTmeas, hcover, hlip⟩ := hpieces (e j) (hepos j)
    exact exists_measurable_majorant_of_lipschitz_pieces Q hS (e j) hdisj hTmeas hcover hlip
  choose G hGmeas hGdom hGint using
    hscale
  -- their pointwise infimum still dominates, and its integral beats every scale

  set H : W₂ → ℝ≥0∞ := fun τ => ⨅ j, G j τ with hHdef
  have hHmeas : Measurable H := Measurable.iInf hGmeas
  have hHdom : ∀ τ, μH[d] (S ∩ {x : V | Q (u x) = τ}) ≤ H τ := fun τ =>
    le_iInf fun j => hGdom j τ
  have hHint :
    ∀ j, (∫⁻ τ, H τ ∂(volume : Measure W₂)) ≤ C * (e j : ℝ≥0∞) ^ (finrank ℝ W₂) * M := fun j =>
    (lintegral_mono fun τ => iInf_le _ j).trans
      (hGint j)
  -- the bound tends to zero, because the codimension is positive and `μH[n] S` is finite

  have htend : Tendsto (fun j : ℕ => C * (e j : ℝ≥0∞) ^ (finrank ℝ W₂) * M) atTop (nhds 0) := by
    have hbase : Tendsto (fun j : ℕ => ((j : ℝ≥0∞) + 1)⁻¹) atTop (nhds 0) := by
      have he : (fun j : ℕ => ((j : ℝ≥0∞) + 1)⁻¹) = fun j : ℕ => ((j + 1 : ℕ) : ℝ≥0∞)⁻¹ := by
        funext j; norm_cast
      rw [he]
      exact ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
    have hcoe : ∀ j : ℕ, ((e j : ℝ≥0) : ℝ≥0∞) = ((j : ℝ≥0∞) + 1)⁻¹ := by
      intro j
      rw [hedef, ENNReal.coe_inv (by positivity)]
      push_cast
      ring_nf
    have hinv : Tendsto (fun j : ℕ => ((e j : ℝ≥0) : ℝ≥0∞)) atTop (nhds 0) := by
      simpa only [hcoe] using hbase
    have hpow : Tendsto (fun j : ℕ => ((e j : ℝ≥0) : ℝ≥0∞) ^ (finrank ℝ W₂)) atTop (nhds 0) := by
      have h0 : (0 : ℝ≥0∞) ^ (finrank ℝ W₂) = 0 := zero_pow hW₂.ne'
      have h := (ENNReal.continuous_pow (finrank ℝ W₂)).continuousAt.tendsto.comp hinv
      rw [h0] at h
      simpa [Function.comp_def] using h
    have h1 := ENNReal.Tendsto.const_mul hpow (Or.inr hCtop)
    simp only [mul_zero] at h1
    have h2 := ENNReal.Tendsto.mul_const h1 (Or.inr hSfin)
    simpa using h2
  have hzero : (∫⁻ τ, H τ ∂(volume : Measure W₂)) = 0 :=
    le_antisymm (ge_of_tendsto' htend hHint) (by simp)
  filter_upwards [(lintegral_eq_zero_iff hHmeas).1 hzero] with τ hτ
  exact le_antisymm (le_of_le_of_eq (hHdom τ) hτ) (by simp)

end LipschitzSliceMajorants

end ExponentObstruction

end FunctionalInequalities.Analysis
