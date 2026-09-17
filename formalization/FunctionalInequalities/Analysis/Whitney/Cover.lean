import Mathlib.MeasureTheory.Covering.Vitali
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.Topology.LocallyFinite
import Mathlib.Algebra.Order.Group.MinMax

/-!
# A quantitative Whitney ball cover

For a nonempty closed set `S`, use radius `min 1 (infDist x S) / 20`. Vitali extraction gives
disjoint small balls whose fivefold enlargements cover the complement. Eightfold closed balls
stay in the complement, are locally finite there, and have uniformly bounded overlap.

This is the geometric input to the compact-jet extension construction. It does not construct
a partition of unity or prove L6. All constants are explicit; no sharpness is asserted.
-/

noncomputable section

open Set Metric MeasureTheory Module Measure
open scoped Topology ENNReal

namespace FunctionalInequalities.Analysis.WhitneyCover

section Metric

variable {V : Type*} [MetricSpace V] (S : Set V)

/-- Capping the distance permits one global Vitali extraction, including on an unbounded
complement. Near the closed set, the radius is exactly distance divided by twenty. -/
def radius (x : V) : ℝ := min 1 (infDist x S) / 20

theorem radius_nonneg (x : V) : 0 ≤ radius S x := by
  exact div_nonneg (le_min zero_le_one infDist_nonneg) (by norm_num)

theorem radius_le (x : V) : radius S x ≤ 1 / 20 := by
  exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)

theorem twenty_mul_radius_le (x : V) : 20 * radius S x ≤ infDist x S := by
  dsimp [radius]
  linarith [min_le_right (1 : ℝ) (infDist x S)]

theorem radius_pos (hS : IsClosed S) (hne : S.Nonempty) {x : V} (hx : x ∉ S) :
    0 < radius S x := by
  exact div_pos (lt_min zero_lt_one ((hS.notMem_iff_infDist_pos hne).1 hx)) (by norm_num)

theorem twenty_mul_radius_le_add (x y : V) :
    20 * radius S x ≤ 20 * radius S y + dist x y := by
  have h := abs_min_sub_min_le_max (1 : ℝ) (infDist x S) 1 (infDist y S)
  simp only [sub_self, abs_zero] at h
  rw [max_eq_right (abs_nonneg (infDist x S - infDist y S))] at h
  have hdist : |infDist x S - infDist y S| ≤ dist x y := by
    simpa only [Real.dist_eq, one_mul, NNReal.coe_one] using (lipschitz_infDist_pt S).dist_le_mul x y
  have hsub := (le_abs_self (min 1 (infDist x S) - min 1 (infDist y S))).trans (h.trans hdist)
  dsimp [radius]
  linarith

/-- An eightfold enlarged ball lies wholly outside the closed set. -/
theorem closedBall_subset_compl {x : V} (hx : 0 < radius S x) :
    closedBall x (8 * radius S x) ⊆ Sᶜ := by
  intro y hy hys
  have h1 := infDist_le_dist_of_mem (x := x) hys
  have h2 := twenty_mul_radius_le S x
  have h3 : dist x y ≤ 8 * radius S x := by simpa only [mem_closedBall, dist_comm] using hy
  linarith

/-- Any enlarged ball meeting `ball y (radius S y)` has comparable radius and nearby center.
This neighborhood version will prove local finiteness, not just pointwise finite overlap. -/
theorem radius_comparable_of_inter {y z : V}
    (h : (closedBall z (8 * radius S z) ∩ ball y (radius S y)).Nonempty) :
    radius S y / 2 ≤ radius S z ∧ radius S z ≤ 2 * radius S y ∧
      dist z y ≤ 20 * radius S y := by
  obtain ⟨w, hwz, hwy⟩ := h
  have hzy : dist z y ≤ 8 * radius S z + radius S y := by
    have hz : dist z w ≤ 8 * radius S z := by simpa only [mem_closedBall, dist_comm] using hwz
    have hy : dist w y < radius S y := hwy
    linarith [dist_triangle z w y]
  have h1 := twenty_mul_radius_le_add S z y
  have h2 := twenty_mul_radius_le_add S y z
  rw [dist_comm y z] at h2
  have h0 := radius_nonneg S y
  constructor
  · linarith
  constructor <;> linarith

end Metric

section FiniteDimension

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- A packing bound at arbitrary scale. No nonzero-dimension assumption is used. -/
theorem card_le_of_separated (s : Finset V) {y : V} {r : ℝ} (hr : 0 < r)
    (hs : ∀ z ∈ s, dist z y ≤ 20 * r)
    (hsep : ∀ z ∈ s, ∀ w ∈ s, z ≠ w → r / 2 ≤ dist z w) :
    s.card ≤ 81 ^ finrank ℝ V := by
  classical
  borelize V
  let μ : Measure V := Measure.addHaar
  let δ : ℝ := r / 4
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let ρ : ℝ := 81 * δ
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  let A := ⋃ z ∈ s, ball z δ
  have hdisj : (s : Set V).PairwiseDisjoint (fun z => ball z δ) := by
    intro z hz w hw hzw
    apply ball_disjoint_ball
    have := hsep z hz w hw hzw
    dsimp [δ]
    linarith
  have hsub : A ⊆ ball y ρ := by
    apply iUnion₂_subset
    intro z hz
    apply ball_subset_ball'
    have := hs z hz
    dsimp [δ, ρ]
    linarith
  have hvol : (s.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ finrank ℝ V) * μ (ball 0 1) ≤
      ENNReal.ofReal (ρ ^ finrank ℝ V) * μ (ball 0 1) := by
    calc
      _ = μ A := by
        rw [show A = ⋃ z ∈ s, ball z δ from rfl, measure_biUnion_finset hdisj
          (fun _ _ => measurableSet_ball)]
        simp only [μ.addHaar_ball_of_pos _ hδ, Finset.sum_const, nsmul_eq_mul, mul_assoc]
      _ ≤ μ (ball y ρ) := measure_mono hsub
      _ = _ := μ.addHaar_ball_of_pos y hρ
  have hvol' : (s.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ finrank ℝ V) ≤
      ENNReal.ofReal (ρ ^ finrank ℝ V) :=
    (ENNReal.mul_le_mul_iff_left (measure_ball_pos _ _ zero_lt_one).ne'
      measure_ball_lt_top.ne).1 hvol
  have hreal := ENNReal.toReal_le_of_le_ofReal (pow_nonneg hρ.le _) hvol'
  simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal (pow_nonneg hδ.le _)] at hreal
  have hpow : 0 < δ ^ finrank ℝ V := pow_pos hδ _
  dsimp [ρ] at hreal
  rw [mul_pow] at hreal
  have hcard : (s.card : ℝ) ≤ (81 : ℝ) ^ finrank ℝ V := by nlinarith
  exact_mod_cast hcard

/-- Disjoint small balls imply a uniform bound even on enlarged balls meeting a neighborhood.
The finite-subset formulation is also useful before choosing a `Fintype` of active indices. -/
theorem card_inter_le {S C : Set V}
    (hpos : ∀ z ∈ C, 0 < radius S z)
    (hdisj : C.PairwiseDisjoint (fun z => ball z (radius S z)))
    {y : V} (hy : 0 < radius S y) (s : Finset V)
    (hs : ∀ z ∈ s, z ∈ C ∧
      (closedBall z (8 * radius S z) ∩ ball y (radius S y)).Nonempty) :
    s.card ≤ 81 ^ finrank ℝ V := by
  apply card_le_of_separated s hy
  · intro z hz
    exact (radius_comparable_of_inter S (hs z hz).2).2.2
  · intro z hz w hw hzw
    have hrad := (radius_comparable_of_inter S (hs z hz).2).1
    have hnot : w ∉ ball z (radius S z) := by
      intro hmem
      exact Set.disjoint_left.1 (hdisj (hs z hz).1 (hs w hw).1 hzw)
        hmem (mem_ball_self (hpos w (hs w hw).1))
    have hdist : radius S z ≤ dist z w := by
      simpa only [mem_ball, not_lt, dist_comm] using hnot
    exact hrad.trans hdist

/-- There are finitely many enlarged balls meeting a fixed small neighborhood off the set. -/
theorem finite_inter {S C : Set V}
    (hpos : ∀ z ∈ C, 0 < radius S z)
    (hdisj : C.PairwiseDisjoint (fun z => ball z (radius S z)))
    {y : V} (hy : 0 < radius S y) :
    {z ∈ C | (closedBall z (8 * radius S z) ∩ ball y (radius S y)).Nonempty}.Finite := by
  by_contra h
  obtain ⟨s, hs, hcard⟩ := Set.Infinite.exists_subset_card_eq h (81 ^ finrank ℝ V + 1)
  have := card_inter_le hpos hdisj hy s (fun z hz => hs hz)
  omega

/-- A countable Whitney cover of the complement, with eightfold supports locally finite in
the complement and a dimension-dependent overlap bound. Nonemptiness is needed only because
`infDist` to the empty set is zero; the empty-set jet extension is a separate constant case. -/
theorem exists_cover {S : Set V} (hS : IsClosed S) (hne : S.Nonempty) :
    ∃ C : Set V, C ⊆ Sᶜ ∧ C.Countable ∧
      C.PairwiseDisjoint (fun z => ball z (radius S z)) ∧
      Sᶜ = ⋃ z ∈ C, ball z (5 * radius S z) ∧
      (∀ z ∈ C, closedBall z (8 * radius S z) ⊆ Sᶜ) ∧
      (LocallyFinite fun z : C =>
        {y : ↥(Sᶜ) | (y : V) ∈ closedBall (z : V) (8 * radius S z)}) ∧
      ∀ y ∉ S, ∀ s : Finset V,
        (∀ z ∈ s, z ∈ C ∧ y ∈ closedBall z (8 * radius S z)) →
          s.card ≤ 81 ^ finrank ℝ V := by
  obtain ⟨C, hC, hdisj, hcover⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement_ball
    Sᶜ (fun x : V => x) (radius S) (1 / 20) (fun x _ => radius_le S x) 5 (by norm_num)
  have hpos : ∀ z ∈ C, 0 < radius S z := fun z hz => radius_pos S hS hne (hC hz)
  have hcount := hdisj.countable_of_isOpen (fun _ _ => isOpen_ball)
    (fun z hz => ⟨z, mem_ball_self (hpos z hz)⟩)
  refine ⟨C, hC, hcount, hdisj, ?_, ?_, ?_, ?_⟩
  · apply Subset.antisymm
    · intro y hy
      obtain ⟨z, hz, hball⟩ := hcover y hy
      exact mem_iUnion₂.2 ⟨z, hz, hball (mem_ball_self (radius_pos S hS hne hy))⟩
    · apply iUnion₂_subset
      intro z hz y hy
      apply closedBall_subset_compl S (hpos z hz)
      have hy' : dist y z < 5 * radius S z := hy
      show dist y z ≤ 8 * radius S z
      linarith [hpos z hz]
  · exact fun z hz => closedBall_subset_compl S (hpos z hz)
  · intro y
    refine ⟨{w : ↥(Sᶜ) | (w : V) ∈ ball (y : V) (radius S y)}, ?_, ?_⟩
    · exact continuous_subtype_val.continuousAt.preimage_mem_nhds
        (ball_mem_nhds _ (radius_pos S hS hne y.property))
    · have hfin := finite_inter hpos hdisj (radius_pos S hS hne y.property)
      apply (hfin.preimage Subtype.val_injective.injOn).subset
      intro z hz
      obtain ⟨w, hwz, hwy⟩ := hz
      exact ⟨z.property, ⟨w, hwz, hwy⟩⟩
  · intro y hy s hs
    apply card_inter_le hpos hdisj (radius_pos S hS hne hy) s
    intro z hz
    exact ⟨(hs z hz).1, ⟨y, (hs z hz).2, mem_ball_self (radius_pos S hS hne hy)⟩⟩

end FiniteDimension

end FunctionalInequalities.Analysis.WhitneyCover
