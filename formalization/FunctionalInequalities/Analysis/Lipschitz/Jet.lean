import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-! # Compact jets of a Lipschitz function
Uniformize the ambient remainder on compact sets covering almost every point.
The ambient estimate also gives continuity of the derivative on each piece. -/

noncomputable section
open Set Metric MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal

namespace FunctionalInequalities.Analysis.LipschitzJet

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- Countable measurable encoding of a uniform-radius remainder at a base point. -/
def goodSet (u : V → ℝ) (ε δ : ℝ) : Set V :=
  {x | ∀ i : ℕ, ‖denseSeq V i‖ < δ →
    ‖u (x + denseSeq V i) - u x - fderiv ℝ u x (denseSeq V i)‖ ≤ ε * ‖denseSeq V i‖}

theorem measurableSet_goodSet {u : V → ℝ} (hu : Continuous u) (ε δ : ℝ) :
    MeasurableSet (goodSet u ε δ) := by
  simp only [goodSet, ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro _hi
  exact measurableSet_le
    (((hu.measurable.comp (measurable_id.add_const (denseSeq V i))).sub hu.measurable).sub
      (measurable_fderiv_apply_const ℝ u (denseSeq V i))).norm measurable_const

omit [MeasurableSpace V] [BorelSpace V] in
theorem goodSet_iff {u : V → ℝ} (hu : Continuous u) {ε δ : ℝ} {x : V} :
    x ∈ goodSet u ε δ ↔ ∀ h : V, ‖h‖ < δ →
      ‖u (x + h) - u x - fderiv ℝ u x h‖ ≤ ε * ‖h‖ := by
  refine ⟨fun hx => ?_, fun hx i => hx _⟩
  have hc : IsClosed {h : V | ‖h‖ < δ →
      ‖u (x + h) - u x - fderiv ℝ u x h‖ ≤ ε * ‖h‖} := by
    simp only [imp_iff_not_or, not_lt]
    exact (isClosed_le continuous_const continuous_norm).union
      (isClosed_le (((hu.comp (continuous_const.add continuous_id)).sub continuous_const).sub
        (fderiv ℝ u x).continuous).norm (continuous_const.mul continuous_norm))
  intro h
  exact (denseRange_denseSeq V).induction_on h hc hx

omit [MeasurableSpace V] [BorelSpace V] in
theorem exists_goodSet {u : V → ℝ} {x : V} (hx : DifferentiableAt ℝ u x)
    {ε : ℝ} (hε : 0 < ε) : ∃ m : ℕ, x ∈ goodSet u ε ((m : ℝ) + 1)⁻¹ := by
  obtain ⟨δ, hδ, hd⟩ := Metric.mem_nhds_iff.1 (hx.hasFDerivAt.isLittleO.def hε)
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
  refine ⟨m, fun i hi => ?_⟩
  have hq : x + denseSeq V i ∈ ball x δ := by
    simpa only [mem_ball, dist_eq_norm, add_sub_cancel_left] using hi.trans (by simpa using hm)
  simpa only [mem_ofPred_eq, add_sub_cancel_left] using hd hq

omit [MeasurableSpace V] [BorelSpace V] in
theorem goodSet_mono {u : V → ℝ} {ε δ δ' : ℝ} (h : δ' ≤ δ) :
    goodSet u ε δ ⊆ goodSet u ε δ' :=
  fun _ hx i hi => hx i (hi.trans_le h)

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- Uniform ambient remainders and a Lipschitz bound force continuity of the derivative
on the set, without an interior or positive-dimensionality assumption. -/
theorem continuousOn_fderiv {u : V → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u) {S : Set V}
    (hR : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ x ∈ S, ∀ h : V, ‖h‖ < δ →
        ‖u (x + h) - u x - fderiv ℝ u x h‖ ≤ ε * ‖h‖) :
    ContinuousOn (fderiv ℝ u) S := by
  apply (Metric.uniformContinuousOn_iff.2 ?_).continuousOn
  intro ε hε
  obtain ⟨δ, hδ, hRδ⟩ := hR (ε / 8) (by positivity)
  refine ⟨ε * δ / (16 * (K + 1)), by positivity, ?_⟩
  intro x hx y hy hxy
  have hbound : ‖fderiv ℝ u x - fderiv ℝ u y‖ ≤ ε / 2 := by
    apply ContinuousLinearMap.opNorm_le_of_shell (c := (2 : ℝ)) hδ (by positivity) (by norm_num)
    intro h hlo hhi
    norm_num at hlo
    have h1 := hRδ x hx h hhi
    have h2 := hRδ y hy h hhi
    have h3 := hu.norm_sub_le (x + h) (y + h)
    have h4 := hu.norm_sub_le x y
    simp only [add_sub_add_right_eq_sub] at h3
    have heq : (fderiv ℝ u x - fderiv ℝ u y) h =
        -(u (x + h) - u x - fderiv ℝ u x h) +
        (u (y + h) - u y - fderiv ℝ u y h) +
        (u (x + h) - u (y + h)) - (u x - u y) := by
      simp only [sub_apply]; ring
    have hnorm : ‖(fderiv ℝ u x - fderiv ℝ u y) h‖ ≤
        ε / 8 * ‖h‖ + ε / 8 * ‖h‖ + K * ‖x - y‖ + K * ‖x - y‖ := by
      rw [heq]
      exact (norm_sub_le _ _).trans (add_le_add
        ((norm_add_le _ _).trans (add_le_add
          ((norm_add_le _ _).trans (add_le_add (by simpa only [norm_neg] using h1) h2)) h3)) h4)
    have hsmall : 16 * (K + 1) * ‖x - y‖ < ε * δ := by
      rw [dist_eq_norm] at hxy
      have := (lt_div_iff₀ (by positivity : 0 < 16 * ((K : ℝ) + 1))).1 hxy
      nlinarith
    have hK : (0 : ℝ) ≤ K := K.coe_nonneg
    have hn : 0 ≤ ‖x - y‖ := norm_nonneg _
    nlinarith
  rw [dist_eq_norm]
  exact hbound.trans_lt (by linarith)

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- Uniformize countably many increasing measurable covers on a large compact subset.
The summable exceptional budgets are chosen before compact inner regularity is applied. -/
theorem exists_compact_uniform_cover (μ : Measure V) [Measure.InnerRegularCompactLTTop μ]
    {A : Set V} (hA : MeasurableSet A) (hfin : μ A ≠ ∞)
    (B : ℕ → ℕ → Set V) (hB : ∀ n m, MeasurableSet (B n m))
    (hmono : ∀ n, Monotone (B n)) (hcover : ∀ n, A ⊆ ⋃ m, B n m)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ C, C ⊆ A ∧ IsCompact C ∧ μ (A \ C) < ε ∧ ∀ n, ∃ m, C ⊆ B n m := by
  classical
  obtain ⟨d, hd, hsum⟩ := ENNReal.exists_pos_sum_of_countable' (ENNReal.half_pos hε).ne' ℕ
  have hchoice : ∀ n, ∃ m, μ (A \ B n m) < d n := by
    intro n
    obtain ⟨m, hm⟩ := exists_measure_iInter_lt
      (fun m => (hA.diff (hB n m)).nullMeasurableSet) (hd n)
      ⟨0, ne_top_of_le_ne_top hfin (measure_mono sdiff_subset)⟩ (by
        ext x
        simp only [mem_iInter, Set.mem_sdiff, mem_empty_iff_false, iff_false]
        intro hx
        obtain ⟨m, hxm⟩ := mem_iUnion.1 (hcover n (hx 0).1)
        exact (hx m).2 hxm)
    refine ⟨m, (measure_mono ?_).trans_lt hm⟩
    intro x hx
    simp only [mem_iInter]
    exact fun j hj => ⟨hx.1, fun h => hx.2 (hmono n hj h)⟩
  choose m hm using hchoice
  let T := A ∩ ⋂ n, B n (m n)
  have hT : MeasurableSet T := hA.inter (MeasurableSet.iInter fun n => hB n (m n))
  have hTA : T ⊆ A := inter_subset_left
  have hloss : μ (A \ T) < ε / 2 := by
    calc
      _ ≤ μ (⋃ n, A \ B n (m n)) := measure_mono (by
        intro x hx
        have : ¬ ∀ n, x ∈ B n (m n) := by
          intro hall; exact hx.2 ⟨hx.1, mem_iInter.2 hall⟩
        obtain ⟨n, hn⟩ := not_forall.1 this
        exact mem_iUnion.2 ⟨n, hx.1, hn⟩)
      _ ≤ ∑' n, μ (A \ B n (m n)) := measure_iUnion_le _
      _ ≤ ∑' n, d n := ENNReal.tsum_le_tsum (fun n => (hm n).le)
      _ < ε / 2 := hsum
  obtain ⟨C, hCT, hC, hCloss⟩ := hT.exists_isCompact_sdiff_lt
    (ne_top_of_le_ne_top hfin (measure_mono hTA)) (ENNReal.half_pos hε).ne'
  refine ⟨C, hCT.trans hTA, hC, ?_, fun n => ⟨m n, fun x hx => mem_iInter.1 (hCT hx).2 n⟩⟩
  calc
    _ ≤ μ ((A \ T) ∪ (T \ C)) := measure_mono (by intro x hx; by_cases h : x ∈ T <;> simp_all)
    _ ≤ μ (A \ T) + μ (T \ C) := measure_union_le _ _
    _ < ε / 2 + ε / 2 := ENNReal.add_lt_add hloss hCloss
    _ = ε := ENNReal.add_halves ε

/-- **compact Whitney jets**: compact jets covering almost every point of a Lipschitz function.
The statement holds for every additive Haar measure on a finite-dimensional real normed space. -/
theorem exists_compact_jets (μ : Measure V) [Measure.IsAddHaarMeasure μ]
    {u : V → ℝ} {K : ℝ≥0} (hu : LipschitzWith K u) :
    ∃ S : ℕ → Set V, μ (⋃ j, S j)ᶜ = 0 ∧
      ∀ j, IsCompact (S j) ∧ (∀ x ∈ S j, DifferentiableAt ℝ u x) ∧
        ContinuousOn (fderiv ℝ u) (S j) ∧
        ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
          ∀ x ∈ S j, ∀ y ∈ S j, ‖y - x‖ < δ →
            ‖u y - u x - fderiv ℝ u x (y - x)‖ ≤ ε * ‖y - x‖ := by
  classical
  let D := {x | DifferentiableAt ℝ u x}
  let A : ℕ → Set V := fun m => D ∩ compactCovering V m
  let B : ℕ → ℕ → Set V := fun n m => goodSet u ((n : ℝ) + 1)⁻¹ ((m : ℝ) + 1)⁻¹
  have hA : ∀ m, MeasurableSet (A m) := fun m =>
    (measurableSet_of_differentiableAt ℝ u).inter (isCompact_compactCovering V m).measurableSet
  have hfin : ∀ m, μ (A m) ≠ ∞ := fun m =>
    ne_top_of_le_ne_top (isCompact_compactCovering V m).measure_lt_top.ne
      (measure_mono inter_subset_right)
  have hB : ∀ n m, MeasurableSet (B n m) := fun n m => measurableSet_goodSet hu.continuous _ _
  have hmono : ∀ n, Monotone (B n) := by
    intro n i j hij
    apply goodSet_mono
    exact inv_anti₀ (by positivity) (by exact_mod_cast Nat.add_le_add_right hij 1)
  have hcover : ∀ m n, A m ⊆ ⋃ k, B n k := by
    intro m n x hx
    exact mem_iUnion.2 (exists_goodSet hx.1 (by positivity))
  choose C hCA hC hCloss hCB using fun m k : ℕ =>
    exists_compact_uniform_cover μ (hA m) (hfin m) B hB hmono (hcover m)
      (ε := ((k : ℝ≥0∞) + 1)⁻¹) (by simp)
  have hR : ∀ m k, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ x ∈ C m k, ∀ h : V, ‖h‖ < δ →
        ‖u (x + h) - u x - fderiv ℝ u x h‖ ≤ ε * ‖h‖ := by
    intro m k ε hε
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    obtain ⟨q, hq⟩ := hCB m k n
    refine ⟨((q : ℝ) + 1)⁻¹, by positivity, ?_⟩
    intro x hx h hh
    have hle := (goodSet_iff hu.continuous).1 (hq hx) h hh
    exact hle.trans (mul_le_mul_of_nonneg_right (by simpa using hn.le) (norm_nonneg h))
  let S : ℕ → Set V := fun j => C j.unpair.1 j.unpair.2
  have hnull : ∀ m, μ (A m \ ⋃ j, S j) = 0 := by
    intro m
    have hle : ∀ k : ℕ, μ (A m \ ⋃ j, S j) ≤ ((k : ℝ≥0∞) + 1)⁻¹ := by
      intro k
      refine (measure_mono (sdiff_subset_sdiff_right ?_)).trans (hCloss m k).le
      exact subset_iUnion_of_subset (Nat.pair m k) (by simp [S])
    by_contra hne
    obtain ⟨k, hk⟩ := ENNReal.exists_inv_nat_lt hne
    exact (not_le.2 hk) ((hle k).trans (ENNReal.inv_le_inv.2 (by simp)))
  refine ⟨S, ?_, fun j => ⟨hC _ _, fun x hx => (hCA _ _ hx).1,
    continuousOn_fderiv hu (hR _ _), ?_⟩⟩
  · have hD : μ Dᶜ = 0 := ae_iff.1 (hu.ae_differentiableAt (μ := μ))
    refine measure_mono_null (fun x hx => ?_) (measure_union_null hD (measure_iUnion_null hnull))
    by_cases hd : x ∈ D
    · obtain ⟨m, hm⟩ := mem_iUnion.1 (iUnion_compactCovering V ▸ mem_univ x)
      exact Or.inr (mem_iUnion.2 ⟨m, ⟨hd, hm⟩, hx⟩)
    · exact Or.inl hd
  · intro ε hε
    obtain ⟨δ, hδ, hr⟩ := hR j.unpair.1 j.unpair.2 ε hε
    refine ⟨δ, hδ, fun x hx y _hy hxy => ?_⟩
    simpa only [add_sub_cancel] using hr x hx (y - x) hxy

end FunctionalInequalities.Analysis.LipschitzJet
