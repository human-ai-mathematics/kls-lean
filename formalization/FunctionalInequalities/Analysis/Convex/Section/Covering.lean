module

public import FunctionalInequalities.Analysis.Convex.Section.Engulfing
public import Mathlib.MeasureTheory.Covering.Vitali

/-!
# Disjoint covering by convex sections

Supporting Letwin arXiv:2607.24164v1 Lemma 2.2 through Berman–Berndtsson
arXiv:1207.6128v1 Theorem 2.24(ii). The section engulfing geometry follows
Forzani–Maldonado, Nonlinear Analysis 57 (2004), 815–829, Theorem 1.

Intersecting sections of comparable heights are contained in a fixed height
enlargement. The abstract Vitali selection theorem then gives countably many
disjoint original sections whose height enlargements cover every original.
For a strictly convex C¹ Alexandrov solution with continuous positive density,
compact-uniform localization supplies all geometric inputs, with no engulfing
estimate as a premise. No bounded-overlap, contact-density or W²,p conclusion
is asserted.
-/

@[expose] public section

noncomputable section
open Set MeasureTheory Metric
open scoped RealInnerProductSpace ENNReal
namespace FunctionalInequalities.Analysis.SoftEngulfing
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- Intersecting sections of comparable heights are contained in a fixed height
enlargement. Only the original smaller section must lie in the set of admissible
centres; no closure property for all enlarged sections is assumed. -/
theorem section_subset_of_intersection {u : E → ℝ} {Q : Set E} {C H : ℝ}
    (hC : 1 < C) (hH : 0 < H)
    (heng : ∀ x ∈ Q, ∀ t : ℝ, 0 < t → t ≤ H → ∀ y z : E,
      defect u x y < t → defect u x z < t → defect u y z < C * t)
    {x y : E} (hx : x ∈ Q) (hy : y ∈ Q) {h k : ℝ}
    (hk : 0 < k) (hhk : h ≤ 2 * k) (hkH : k ≤ H / (4 * C))
    (hsub : {z | defect u x z < h} ⊆ Q)
    (hinter : ({z | defect u x z < h} ∩ {z | defect u y z < k}).Nonempty) :
    {z | defect u x z < h} ⊆ {z | defect u y z < 2 * C ^ 2 * k} := by
  have hCp : 0 < C := lt_trans zero_lt_one hC
  have hscale : 4 * C * k ≤ H := by
    have hh := (le_div_iff₀ (by positivity : 0 < 4 * C)).mp hkH
    nlinarith
  have hkH' : k ≤ H := by nlinarith
  have h2kH : 2 * k ≤ H := by nlinarith
  have h2CkH : 2 * C * k ≤ H := by nlinarith
  obtain ⟨w, hwx, hwy⟩ := hinter
  have hwQ := hsub hwx
  intro z hz
  have hwz := heng x hx (2 * k) (by positivity) h2kH w z
    (lt_of_lt_of_le hwx hhk) (lt_of_lt_of_le hz hhk)
  have hwy' := heng y hy k hk hkH' w y hwy (by simpa [defect] using hk)
  have hwy2 : defect u w y < 2 * C * k := by nlinarith
  have hwz2 : defect u w z < 2 * C * k := by nlinarith
  have hh := heng w hwQ (2 * C * k) (by positivity) h2CkH y z hwy2 hwz2
  change defect u y z < 2 * C ^ 2 * k
  nlinarith

/-- A family of small sections admits a countable disjoint subfamily whose
fixed height enlargements cover every original section. This is a geometric
selection theorem, without a bounded-overlap or differentiation assertion. -/
theorem exists_disjoint_section_cover {u : E → ℝ} (hu : Continuous u)
    {Q : Set E} {C H : ℝ} (hC : 1 < C) (hH : 0 < H)
    (heng : ∀ x ∈ Q, ∀ t : ℝ, 0 < t → t ≤ H → ∀ y z : E,
      defect u x y < t → defect u x z < t → defect u y z < C * t)
    {ι : Type*} (I : Set ι) (x : ι → E) (h : ι → ℝ)
    (hx : ∀ i ∈ I, x i ∈ Q) (hh : ∀ i ∈ I, 0 < h i ∧ h i ≤ H / (4 * C))
    (hsub : ∀ i ∈ I, {z | defect u (x i) z < h i} ⊆ Q) :
    ∃ J ⊆ I, J.Countable ∧ J.PairwiseDisjoint (fun i => {z | defect u (x i) z < h i}) ∧
      ∀ i ∈ I, {z | defect u (x i) z < h i} ⊆
        ⋃ j ∈ J, {z | defect u (x j) z < 2 * C ^ 2 * h j} := by
  let B : ι → Set E := fun i => {z | defect u (x i) z < h i}
  have hne : ∀ i ∈ I, (B i).Nonempty := by
    intro i hi
    refine ⟨x i, ?_⟩
    simpa [B, defect] using (hh i hi).1
  obtain ⟨J, hJI, hdisj, hselect⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement
    B I h 2 (by norm_num) (fun i hi => (hh i hi).1.le) (H / (4 * C))
    (fun i hi => (hh i hi).2) hne
  have hcount : J.Countable := hdisj.countable_of_isOpen (fun i _ => by
    change IsOpen {z | u z - u (x i) - ⟪gradient u (x i), z - x i⟫ < h i}
    apply isOpen_lt _ continuous_const
    fun_prop) (fun i hi => hne i (hJI hi))
  refine ⟨J, hJI, hcount, hdisj, ?_⟩
  intro i hi z hz
  obtain ⟨j, hj, hinter, hij⟩ := hselect i hi
  have hhsub := section_subset_of_intersection hC hH heng (hx i hi) (hx j (hJI hj))
    (hh j (hJI hj)).1 hij (hh j (hJI hj)).2 (hsub i hi) hinter
  exact mem_iUnion.mpr ⟨j, mem_iUnion.mpr ⟨hj, hhsub hz⟩⟩
end FunctionalInequalities.Analysis.SoftEngulfing

namespace FunctionalInequalities.Analysis
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- Countable disjoint selection for the actual small sections of a strictly
convex C¹ Alexandrov solution. All constants precede the indexed family. The
cover uses height enlargements of the selected sections; it does not assert
bounded overlap of a shrunken family or a contact-set density improvement. -/
theorem exists_disjoint_section_cover_of_alexandrov_density (hn : 0 < n)
    {u f : E → ℝ} (hs : StrictConvexOn ℝ univ u) (hC1 : ContDiff ℝ 1 u)
    (hf : Continuous f) (hfpos : ∀ x, 0 < f x)
    (hMA : ∀ G : Set E, IsOpen G → volume (subgradientImage u G) =
      ∫⁻ y in G, ENNReal.ofReal (f y)) {K : Set E} (hK : IsCompact K) :
    ∃ A h₀ : ℝ, 1 < A ∧ 0 < h₀ ∧ ∀ {ι : Type*} (I : Set ι) (x : ι → E) (h : ι → ℝ),
      (∀ i ∈ I, x i ∈ K) → (∀ i ∈ I, 0 < h i ∧ h i ≤ h₀) →
      ∃ J ⊆ I, J.Countable ∧
        J.PairwiseDisjoint (fun i => {z | SoftEngulfing.defect u (x i) z < h i}) ∧
        ∀ i ∈ I, {z | SoftEngulfing.defect u (x i) z < h i} ⊆
          ⋃ j ∈ J, {z | SoftEngulfing.defect u (x j) z < A * h j} := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨R, hR, hKR⟩ := hK.isBounded.exists_pos_norm_le
  obtain ⟨C, H, hC, hH, heng⟩ := exists_section_engulfing_of_alexandrov_density
    hn hs hC1 hf hfpos hMA (isCompact_closedBall (0 : E) (R + 1))
  obtain ⟨h₁, hh₁, hloc⟩ := exists_uniform_section_subset_ball hs hC1 hK (R := 1) zero_lt_one
  have hCp : 0 < C := lt_trans zero_lt_one hC
  refine ⟨2 * C ^ 2, min h₁ (H / (4 * C)), by nlinarith, by positivity, ?_⟩
  intro ι I x h hx hh
  apply SoftEngulfing.exists_disjoint_section_cover hC1.continuous hC hH heng I x h
  · intro i hi
    change dist (x i) 0 ≤ R + 1
    rw [dist_zero_right]
    linarith [hKR (x i) (hx i hi)]
  · intro i hi
    exact ⟨(hh i hi).1, ((hh i hi).2).trans (min_le_right _ _)⟩
  · intro i hi z hz
    have hz' : u z < u (x i) + ⟪gradient u (x i), z - x i⟫ + h i := by
      change u z - u (x i) - ⟪gradient u (x i), z - x i⟫ < h i at hz
      linarith
    have hdist := hloc (x i) (hx i hi) (h i)
      (((hh i hi).2).trans (min_le_left _ _)) hz'
    have hdist' : dist z (x i) < 1 := hdist
    change dist z 0 ≤ R + 1
    calc dist z 0 ≤ dist z (x i) + dist (x i) 0 := dist_triangle _ _ _
      _ ≤ R + 1 := by
        rw [dist_zero_right]
        linarith [hKR (x i) (hx i hi), hdist']
/-- A countable disjoint summation lemma for weak-type estimates.

The sets `C j` need not be measurable: only the measurable disjoint sets
`B j` are used in the summation identity. No finiteness or cancellation
assumption is made on any of the measures or on the constants. -/
private theorem weak_type_of_countable_disjoint
    {α ι : Type*} [MeasurableSpace α] (μ : Measure α)
    {J : Set ι} (hJ : J.Countable)
    {B C : ι → Set α} {U s : Set α}
    {η M : ℝ≥0∞}
    (hB : ∀ j ∈ J, MeasurableSet (B j))
    (hdisj : J.PairwiseDisjoint B)
    (hs : MeasurableSet s)
    (hU : U ⊆ ⋃ j ∈ J, C j)
    (hC : ∀ j ∈ J, μ (C j) ≤ M * μ (B j))
    (hdensity : ∀ j ∈ J, η * μ (B j) ≤ μ (s ∩ B j)) :
    η * μ U ≤ M * μ s := by
  let := hJ.toEncodable
  have hCsum :
      (∑' j : J, μ (C j)) ≤ M * (∑' j : J, μ (B j)) := by
    calc
      (∑' j : J, μ (C j)) ≤ ∑' j : J, M * μ (B j) :=
        ENNReal.tsum_le_tsum (fun j => hC j j.property)
      _ = M * (∑' j : J, μ (B j)) := by
        rw [ENNReal.tsum_mul_left]

  have hI_disj : J.PairwiseDisjoint (fun j => s ∩ B j) := by
    intro i hi j hj hij
    exact (hdisj hi hj hij).mono inter_subset_right inter_subset_right

  have hI_meas : ∀ j ∈ J, MeasurableSet (s ∩ B j) := by
    intro j hj
    exact hs.inter (hB j hj)

  have hI_union :
      μ (⋃ j ∈ J, s ∩ B j) = ∑' p : J, μ (s ∩ B p) :=
    measure_biUnion hJ hI_disj hI_meas

  have hsubset : (⋃ j ∈ J, s ∩ B j) ⊆ s := by
    exact iUnion_subset fun _ => iUnion_subset fun _ => inter_subset_left

  have hdensity_sum :
      η * (∑' j : J, μ (B j)) ≤ μ s := by
    calc
      η * (∑' j : J, μ (B j)) =
          ∑' j : J, η * μ (B j) := by
            rw [ENNReal.tsum_mul_left]
      _ ≤ ∑' j : J, μ (s ∩ B j) :=
        ENNReal.tsum_le_tsum (fun j => hdensity j j.property)
      _ = μ (⋃ j ∈ J, s ∩ B j) := hI_union.symm
      _ ≤ μ s := measure_mono hsubset

  have hC_union :
      μ (⋃ j ∈ J, C j) ≤ ∑' j : J, μ (C j) := by
    rw [biUnion_eq_iUnion]
    exact measure_iUnion_le _

  calc
    η * μ U ≤ η * μ (⋃ j ∈ J, C j) :=
      mul_le_mul_right (measure_mono hU) η
    _ ≤ η * (∑' j : J, μ (C j)) :=
      mul_le_mul_right hC_union η
    _ ≤ η * (M * (∑' j : J, μ (B j))) :=
      mul_le_mul_right hCsum η
    _ = M * (η * (∑' j : J, μ (B j))) := by
      ac_rfl
    _ ≤ M * μ s :=
      mul_le_mul_right hdensity_sum M

/-- Quantitative maximal weak-type covering estimate for actual small sections.

This is a maximal weak-type support statement. It does not assert a nonlinear
contact-set gain, bounded overlap, an ink-spots estimate, or any Hessian or
`W²,p` conclusion. -/
theorem exists_quantitative_weak_type_section_cover (hn : 0 < n) {u f : E → ℝ}
    (hstrict : StrictConvexOn ℝ univ u) (hC1 : ContDiff ℝ 1 u) (hf : Continuous f)
    (hfpos : ∀ x, 0 < f x)
    (hMA :
      ∀ G : Set E, IsOpen G → volume (subgradientImage u G) = ∫⁻ y in G, ENNReal.ofReal (f y))
    {K : Set E} (hK : IsCompact K) :
    ∃ M h₀ : ℝ,
      0 < M ∧
        0 < h₀ ∧
          ∀ {ι : Type*} (δ : ℝ),
            0 < δ →
              ∀ s : Set E,
                MeasurableSet s →
                  ∀ (I : Set ι) (x : ι → E) (h : ι → ℝ),
                    (∀ i ∈ I, x i ∈ K) →
                      (∀ i ∈ I, 0 < h i ∧ h i ≤ h₀) →
                        (∀ i ∈ I,
                            ENNReal.ofReal δ *
                                volume {z | SoftEngulfing.defect u (x i) z < h i} ≤
                              volume (s ∩ {z | SoftEngulfing.defect u (x i) z < h i})) →
                          ENNReal.ofReal δ *
                              volume (⋃ i ∈ I, {z | SoftEngulfing.defect u (x i) z < h i}) ≤
                            ENNReal.ofReal M * volume s := by
  obtain ⟨A, h₀, hA, h₀pos, hselection⟩ :=
    exists_disjoint_section_cover_of_alexandrov_density hn hstrict hC1 hf hfpos hMA hK
  have hMpos : 0 < A ^ n := pow_pos (lt_trans zero_lt_one hA) n
  refine ⟨A ^ n, h₀, hMpos, h₀pos, ?_⟩
  intro ι δ _hδ s hs I x h hx hh hdensity
  obtain ⟨J, hJI, hJcount, hJdisj, hJcover⟩ := hselection I x h hx hh
  let B : ι → Set E := fun i => {z | SoftEngulfing.defect u (x i) z < h i}
  let C : ι → Set E := fun i => {z | SoftEngulfing.defect u (x i) z < A * h i}
  have hsection_eq :
    ∀ (i : ι) (q : ℝ),
      {z : E | u z < u (x i) + ⟪gradient u (x i), z - x i⟫ + q} =
        {z : E | SoftEngulfing.defect u (x i) z < q} := by
    intro i q
    ext z
    change
      (u z < u (x i) + ⟪gradient u (x i), z - x i⟫ + q) ↔
        u z - u (x i) - ⟪gradient u (x i), z - x i⟫ < q
    constructor <;> intro hz <;> linarith
  have hucont : Continuous u := hC1.continuous
  have hBmeas : ∀ i ∈ J, MeasurableSet (B i) := by
    intro i hi
    have hopen : IsOpen {z : E | SoftEngulfing.defect u (x i) z < h i} := by
      change IsOpen {z : E | u z - u (x i) - ⟪gradient u (x i), z - x i⟫ < h i}
      apply isOpen_lt _ continuous_const
      fun_prop
    exact hopen.measurableSet
  have hCvol :
    ∀ i ∈ J, (volume : Measure E) (C i) ≤ ENNReal.ofReal (A ^ n) * (volume : Measure E) (B i) := by
    intro i hi
    have hvol :=
      section_volume_mul_le (u := u) hstrict.convexOn (x i) (gradient u (x i)) (h := h i) (A :=
        A) hA.le
    rw [hsection_eq i (A * h i), hsection_eq i (h i)] at hvol
    simpa [B, C] using hvol
  have hU : (⋃ i ∈ I, B i) ⊆ ⋃ j ∈ J, C j := by
    intro z hz
    rcases mem_iUnion.mp hz with ⟨i, hz⟩
    rcases mem_iUnion.mp hz with ⟨hi, hzi⟩
    have hzi' : z ∈ {z : E | SoftEngulfing.defect u (x i) z < h i} := by simpa [B] using hzi
    have hzcover := hJcover i hi hzi'
    simpa [C] using hzcover
  have hdensityJ :
    ∀ i ∈ J, ENNReal.ofReal δ * (volume : Measure E) (B i) ≤ (volume : Measure E) (s ∩ B i) := by
    intro i hi
    simpa [B] using hdensity i (hJI hi)
  have hweak :
    ENNReal.ofReal δ * (volume : Measure E) (⋃ i ∈ I, B i) ≤
      ENNReal.ofReal (A ^ n) * (volume : Measure E) s :=
    weak_type_of_countable_disjoint (volume : Measure E) hJcount hBmeas hJdisj hs hU hCvol
      hdensityJ
  simpa [B] using hweak


end FunctionalInequalities.Analysis
