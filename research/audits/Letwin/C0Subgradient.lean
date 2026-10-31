module

public import FunctionalInequalities.Analysis.Convex.Alexandrov.Measure
public import FunctionalInequalities.Analysis.Convex.Alexandrov.Stability
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

@[expose] public section

noncomputable section
open Set Metric
open scoped RealInnerProductSpace
namespace LetwinC0SubgradientAudit
open FunctionalInequalities.Analysis

private lemma abs_convex : ConvexOn ℝ (Ioo (-2 : ℝ) 2) (fun y : ℝ => |y|) := by
  refine ⟨convex_Ioo _ _, ?_⟩
  intro a _ha b _hb t u ht hu _htu
  have h := abs_add_le (t * a) (u * b)
  rw [abs_mul, abs_mul, abs_of_nonneg ht, abs_of_nonneg hu] at h
  exact h

/-- Concrete one-dimensional client for `v x = |x|` on `(-2,2)`. -/
theorem real_abs_client :
    ∃ R : ℝ,
      0 ≤ R ∧
        (∀ x ∈ Set.Icc (-1 : ℝ) 1, ∃ p : ℝ, ∀ y ∈ Set.Ioo (-2 : ℝ) 2, |x| + ⟪p, y - x⟫ ≤ |y|) ∧
          (∀ x ∈ Set.Icc (-1 : ℝ) 1,
            ∀ p : ℝ, (∀ y ∈ Set.Ioo (-2 : ℝ) 2, |x| + ⟪p, y - x⟫ ≤ |y|) → ‖p‖ ≤ R) := by
  have hΩ : IsOpen (Set.Ioo (-2 : ℝ) 2) := isOpen_Ioo
  have hv : ConvexOn ℝ (Set.Ioo (-2 : ℝ) 2) (fun x : ℝ => |x|) := abs_convex
  have hvc : ContinuousOn (fun x : ℝ => |x|) (Set.Ioo (-2 : ℝ) 2) := continuous_abs.continuousOn
  have hK : IsCompact (Set.Icc (-1 : ℝ) 1) := isCompact_Icc
  have hKΩ : Set.Icc (-1 : ℝ) 1 ⊆ Set.Ioo (-2 : ℝ) 2 := by
    intro x hx
    constructor <;> linarith [hx.1, hx.2]
  exact exists_uniform_subgradient_bound_on_compact hΩ hv hvc hK hKΩ

/-- Concrete zero-dimensional client on the singleton open domain. -/
theorem zero_dimensional_client :
    ∃ R : ℝ,
      0 ≤ R ∧
        (∀ x ∈ ({0} : Set (EuclideanSpace ℝ (Fin 0))),
            ∃ p : EuclideanSpace ℝ (Fin 0),
              ∀ y ∈ (Set.univ : Set (EuclideanSpace ℝ (Fin 0))), (0 : ℝ) + ⟪p, y - x⟫ ≤ 0) ∧
          (∀ x ∈ ({0} : Set (EuclideanSpace ℝ (Fin 0))),
            ∀ p : EuclideanSpace ℝ (Fin 0),
              (∀ y ∈ (Set.univ : Set (EuclideanSpace ℝ (Fin 0))), (0 : ℝ) + ⟪p, y - x⟫ ≤ 0) →
                ‖p‖ ≤ R) := by
  have hΩ : IsOpen (Set.univ : Set (EuclideanSpace ℝ (Fin 0))) := isOpen_univ
  have hv :
    ConvexOn ℝ (Set.univ : Set (EuclideanSpace ℝ (Fin 0)))
      (fun _ : EuclideanSpace ℝ (Fin 0) => (0 : ℝ)) :=
    convexOn_const 0 convex_univ
  have hvc :
    ContinuousOn (fun _ : EuclideanSpace ℝ (Fin 0) => (0 : ℝ))
      (Set.univ : Set (EuclideanSpace ℝ (Fin 0))) :=
    continuous_const.continuousOn
  have hK : IsCompact ({0} : Set (EuclideanSpace ℝ (Fin 0))) := isCompact_singleton
  have hKΩ :
    ({0} : Set (EuclideanSpace ℝ (Fin 0))) ⊆ (Set.univ : Set (EuclideanSpace ℝ (Fin 0))) := by
    exact singleton_subset_iff.mpr (mem_univ 0)
  exact exists_uniform_subgradient_bound_on_compact hΩ hv hvc hK hKΩ

end LetwinC0SubgradientAudit
set_option pp.fullNames true in
#print axioms FunctionalInequalities.Analysis.exists_uniform_subgradient_bound_on_compact
set_option pp.fullNames true in
#print axioms LetwinC0SubgradientAudit.real_abs_client
set_option pp.fullNames true in
#print axioms LetwinC0SubgradientAudit.zero_dimensional_client

namespace LetwinLocalUniformSubgradientAudit
open FunctionalInequalities.Analysis Set Metric Filter
open scoped Topology

private lemma scalar_shift_tendsto :
    Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

private lemma vertical_shift_tendsto :
    TendstoUniformly (fun (n : ℕ) (x : ℝ) => |x| + 1 / ((n : ℝ) + 1)) (fun x : ℝ => |x|)
      atTop := by
  have hc : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) := scalar_shift_tendsto
  intro V hV
  obtain ⟨ε, hε, hεV⟩ := mem_uniformity_dist.mp hV
  filter_upwards [(Metric.tendsto_nhds.mp hc) ε hε] with n hn
  intro x
  apply hεV
  rw [dist_comm, Real.dist_eq, add_sub_cancel_left]
  simpa only [Real.dist_eq, sub_zero] using hn

private lemma abs_reference_image {G : Set ℝ} (hG : G ⊆ Icc (-1 : ℝ) 1) (h0 : (0 : ℝ) ∈ G) :
    subgradientImageOn (fun y : ℝ => |y|) (Ioo (-2) 2) G = Icc (-1 : ℝ) 1 := by
  ext p
  constructor
  · rintro ⟨x, hxG, hp⟩
    have hx := hG hxG
    have hplus := hp (3 / 2) (by norm_num)
    have hminus := hp (-3 / 2) (by norm_num)
    change |x| + (3 / 2 - x) * p ≤ |3 / 2| at hplus
    change |x| + (-3 / 2 - x) * p ≤ |-3 / 2| at hminus
    norm_num at hplus hminus
    constructor
    · by_contra hn
      have hh :=
        mul_pos (show 0 < -1 - p by linarith) (show 0 < (3 / 2 : ℝ) + x by linarith [hx.1])
      nlinarith [neg_le_abs x]
    · by_contra hn
      have hh :=
        mul_pos (show 0 < p - 1 by linarith) (show 0 < (3 / 2 : ℝ) - x by linarith [hx.2])
      nlinarith [le_abs_self x]
  · intro hp
    refine ⟨0, h0, ?_⟩
    intro y _hy
    have hpabs : |p| ≤ 1 := abs_le.mpr hp
    have hh : |y * p| ≤ |y| := by rw [abs_mul]; nlinarith [abs_nonneg y]
    change |(0 : ℝ)| + (y - 0) * p ≤ |y|
    norm_num
    exact (le_abs_self _).trans hh

private lemma fin0_reference_image {G : Set (EuclideanSpace ℝ (Fin 0))}
    (h0 : (0 : EuclideanSpace ℝ (Fin 0)) ∈ G) :
    subgradientImageOn (fun _ : EuclideanSpace ℝ (Fin 0) => (0 : ℝ)) univ G = univ := by
  ext p
  constructor
  · intro _hp
    exact mem_univ _
  · intro _hp
    refine ⟨0, h0, ?_⟩
    intro y _hy
    have hy : y = 0 := Subsingleton.elim _ _
    have hp : p = 0 := Subsingleton.elim _ _
    simp [hp, hy]

private lemma fin0_reference_volume {G : Set (EuclideanSpace ℝ (Fin 0))}
    (h0 : (0 : EuclideanSpace ℝ (Fin 0)) ∈ G) :
    (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 0)))
        (subgradientImageOn (fun _ : EuclideanSpace ℝ (Fin 0) => (0 : ℝ)) univ G) =
      1 := by
  rw [fin0_reference_image h0, volume_euclideanSpace_eq_dirac]
  simp

theorem actual_vertical_shift_support_bound :
    ∃ R : ℝ,
      0 ≤ R ∧
        ∀ᶠ n : ℕ in atTop,
          ∀ x ∈ Icc (-1 : ℝ) 1,
            ∀ p : ℝ,
              (∀ y ∈ Ioo (-2 : ℝ) 2,
                  (|x| + 1 / ((n : ℝ) + 1)) + ⟪p, y - x⟫ ≤ |y| + 1 / ((n : ℝ) + 1)) →
                ‖p‖ ≤ R := by
  apply
    exists_eventual_support_slope_bound_of_locally_uniform isOpen_Ioo
      continuous_abs.continuousOn
      vertical_shift_tendsto.tendstoUniformlyOn.tendstoLocallyUniformlyOn isCompact_Icc
  intro x hx
  constructor <;> linarith [hx.1, hx.2]

theorem actual_fin0_varying_support_bound :
    ∃ R : ℝ,
      0 ≤ R ∧
        ∀ᶠ n : ℕ in atTop,
          ∀ x ∈ ({0} : Set (EuclideanSpace ℝ (Fin 0))),
            ∀ p : EuclideanSpace ℝ (Fin 0),
              (∀ y ∈ univ, (1 : ℝ) / ((n : ℝ) + 1) + ⟪p, y - x⟫ ≤ (1 : ℝ) / ((n : ℝ) + 1)) →
                ‖p‖ ≤ R := by
  have hc : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) := scalar_shift_tendsto
  exact
    exists_eventual_support_slope_bound_of_locally_uniform isOpen_univ
      continuous_const.continuousOn
      hc.tendstoUniformly_const.tendstoUniformlyOn.tendstoLocallyUniformlyOn isCompact_singleton
      (subset_univ _)


/-- A varying nonsmooth source family uses the actual upper-image theorem and
an explicit genuine reference-image bound, for every open epsilon neighborhood. -/
theorem actual_abs_upper_image {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      subgradientImageOn (fun x : ℝ => |x| + 1 / ((n : ℝ) + 1)) (Ioo (-2) 2) (Icc (-1) 1) ⊆
        Ioo (-1 - ε) (1 + ε) := by
  have hKΩ : Icc (-1 : ℝ) 1 ⊆ Ioo (-2) 2 := by
    intro x hx
    constructor <;> linarith [hx.1, hx.2]
  apply
    eventually_subgradientImageOn_subset_of_tendstoLocallyUniformlyOn isOpen_Ioo
      continuous_abs.continuousOn
      vertical_shift_tendsto.tendstoUniformlyOn.tendstoLocallyUniformlyOn isCompact_Icc hKΩ
      isOpen_Ioo
  rw [abs_reference_image (subset_refl _) (by norm_num)]
  intro p hp
  constructor <;> linarith [hp.1, hp.2]

/-- Actual zero-dimensional Haar carrier: only topological support stability is
claimed, with a genuinely varying family of constants. -/
theorem actual_fin0_upper_image :
    ∀ᶠ n : ℕ in atTop,
      subgradientImageOn (fun _ : EuclideanSpace ℝ (Fin 0) => (1 : ℝ) / ((n : ℝ) + 1)) univ
          ({0} : Set (EuclideanSpace ℝ (Fin 0))) ⊆
        ball 0 1 := by
  have hc : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) := scalar_shift_tendsto
  apply
    eventually_subgradientImageOn_subset_of_tendstoLocallyUniformlyOn isOpen_univ
      continuous_const.continuousOn
      hc.tendstoUniformly_const.tendstoUniformlyOn.tendstoLocallyUniformlyOn isCompact_singleton
      (subset_univ _) isOpen_ball
  intro p _hp
  have hp : p = 0 := Subsingleton.elim _ _
  simp [hp]


open MeasureTheory
theorem actual_varying_abs_contact :
    ∀ᶠ n : ℕ in atTop,
      (0 : ℝ) ∈
        subgradientImageOn (fun y : ℝ => |y| + 1 / ((n : ℝ) + 1)) (Ioo (-2) 2) (Ioo (-1) 1) := by
  apply
    eventually_mem_subgradientImageOn_of_unique_contact (x := (0 : ℝ)) isOpen_Ioo
      (fun n => LetwinC0SubgradientAudit.abs_convex.add (convexOn_const _ (convex_Ioo _ _)))
      (fun _ => (continuous_abs.add continuous_const).continuousOn) continuous_abs.continuousOn
      vertical_shift_tendsto.tendstoUniformlyOn.tendstoLocallyUniformlyOn isOpen_Ioo
      (by intro y hy; constructor <;> linarith [hy.1, hy.2]) (by norm_num)
  · intro y _hy
    simp
  · intro y _hy heq
    exact abs_eq_zero.mp (by simpa using heq)

theorem actual_fin0_varying_contact :
    ∀ᶠ n : ℕ in atTop,
      (0 : EuclideanSpace ℝ (Fin 0)) ∈
        subgradientImageOn (fun _ : EuclideanSpace ℝ (Fin 0) => (1 : ℝ) / ((n : ℝ) + 1)) univ
          univ := by
  have hc : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) := scalar_shift_tendsto
  exact
    eventually_mem_subgradientImageOn_of_unique_contact (v :=
      fun _ : EuclideanSpace ℝ (Fin 0) => (0 : ℝ)) (x := 0) isOpen_univ
      (fun _ => convexOn_const _ convex_univ) (fun _ => continuous_const.continuousOn)
      continuous_const.continuousOn
      hc.tendstoUniformly_const.tendstoUniformlyOn.tendstoLocallyUniformlyOn isOpen_univ
      (subset_refl _) (mem_univ _) (by intro y _hy; simp)
      (fun y _hy _heq => Subsingleton.elim y 0)

theorem actual_varying_abs_volume_upper :
    limsup
        (fun n : ℕ =>
          (volume : Measure ℝ)
            (subgradientImageOn (fun x : ℝ => |x| + 1 / ((n : ℝ) + 1)) (Ioo (-2) 2)
              (Icc (-1) 1)))
        atTop ≤
      ENNReal.ofReal 2 := by
  have hKΩ : Icc (-1 : ℝ) 1 ⊆ Ioo (-2) 2 := by
    intro x hx
    constructor <;> linarith [hx.1, hx.2]
  have h :=
    limsup_volume_subgradientImageOn_le_of_locally_uniform isOpen_Ioo
      LetwinC0SubgradientAudit.abs_convex continuous_abs.continuousOn
      vertical_shift_tendsto.tendstoUniformlyOn.tendstoLocallyUniformlyOn isCompact_Icc hKΩ
  rw [abs_reference_image (subset_refl _) (by norm_num), Real.volume_Icc] at h
  norm_num at h ⊢
  exact h

theorem actual_fin0_volume_upper :
    limsup
        (fun n : ℕ =>
          (volume : Measure (EuclideanSpace ℝ (Fin 0)))
            (subgradientImageOn (fun _ => (1 : ℝ) / ((n : ℝ) + 1)) univ {0}))
        atTop ≤
      1 := by
  have hc : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) := scalar_shift_tendsto
  have hv : ConvexOn ℝ (univ : Set (EuclideanSpace ℝ (Fin 0))) (fun _ => (0 : ℝ)) :=
    convexOn_const 0 convex_univ
  have h :=
    limsup_volume_subgradientImageOn_le_of_locally_uniform (K :=
      ({0} : Set (EuclideanSpace ℝ (Fin 0)))) isOpen_univ hv continuous_const.continuousOn
      hc.tendstoUniformly_const.tendstoUniformlyOn.tendstoLocallyUniformlyOn isCompact_singleton
      (subset_univ _)
  have hvol :=
    fin0_reference_volume (G := ({0} : Set (EuclideanSpace ℝ (Fin 0)))) (mem_singleton _)
  exact h.trans hvol.le

theorem actual_varying_abs_lower :
    ENNReal.ofReal 2 ≤
      liminf
        (fun n : ℕ =>
          (volume : Measure ℝ)
            (subgradientImageOn (fun y : ℝ => |y| + 1 / ((n : ℝ) + 1)) (Ioo (-2) 2)
              (Ioo (-1) 1)))
        atTop := by
  have h :=
    volume_subgradientImageOn_le_liminf_of_locally_uniform (G := Ioo (-1 : ℝ) 1) isOpen_Ioo
      (fun n => LetwinC0SubgradientAudit.abs_convex.add (convexOn_const _ (convex_Ioo _ _)))
      (fun _ => (continuous_abs.add continuous_const).continuousOn)
      LetwinC0SubgradientAudit.abs_convex continuous_abs.continuousOn
      vertical_shift_tendsto.tendstoUniformlyOn.tendstoLocallyUniformlyOn isOpen_Ioo
      (by intro y hy; constructor <;> linarith [hy.1, hy.2])
  rw [abs_reference_image (fun _ hy => ⟨hy.1.le, hy.2.le⟩) (by norm_num), Real.volume_Icc] at h
  norm_num at h ⊢
  exact h

theorem actual_fin0_lower :
    1 ≤
      liminf
        (fun n : ℕ =>
          (volume : Measure (EuclideanSpace ℝ (Fin 0)))
            (subgradientImageOn (fun _ => (1 : ℝ) / ((n : ℝ) + 1)) univ univ))
        atTop := by
  have hc : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) := scalar_shift_tendsto
  have hv : ConvexOn ℝ (univ : Set (EuclideanSpace ℝ (Fin 0))) (fun _ => (0 : ℝ)) :=
    convexOn_const 0 convex_univ
  have h :=
    volume_subgradientImageOn_le_liminf_of_locally_uniform (G :=
      (univ : Set (EuclideanSpace ℝ (Fin 0)))) isOpen_univ
      (fun _ => convexOn_const _ convex_univ) (fun _ => continuous_const.continuousOn) hv
      continuous_const.continuousOn
      hc.tendstoUniformly_const.tendstoUniformlyOn.tendstoLocallyUniformlyOn isOpen_univ
      (subset_refl _)
  have hvol := fin0_reference_volume (G := (univ : Set (EuclideanSpace ℝ (Fin 0)))) (mem_univ _)
  rw [hvol] at h
  exact h

theorem actual_varying_abs_continuity_set :
    ∃ (μs : ℕ → Measure ℝ) (μ : Measure ℝ),
      (∀ n,
          ∀ G : Set ℝ,
            MeasurableSet G →
              μs n G =
                volume
                  (subgradientImageOn (fun y : ℝ => |y| + 1 / ((n : ℝ) + 1)) (Ioo (-2) 2)
                    (G ∩ Ioo (-2) 2))) ∧
        (∀ G : Set ℝ,
            MeasurableSet G →
              μ G =
                volume (subgradientImageOn (fun y : ℝ => |y|) (Ioo (-2) 2) (G ∩ Ioo (-2) 2))) ∧
          μ (Icc (-1) 1) = ENNReal.ofReal 2 ∧
            Tendsto (fun n => μs n (Icc (-1) 1)) atTop (𝓝 (ENNReal.ofReal 2)) := by
  obtain ⟨μs, μ, hμs, hμ, _hfin, _hμfin, _hupper, _hlower, hcont⟩ :=
    exists_domain_mongeAmpere_measures_local_limits isOpen_Ioo
      (fun n => LetwinC0SubgradientAudit.abs_convex.add (convexOn_const _ (convex_Ioo _ _)))
      (fun _ => (continuous_abs.add continuous_const).continuousOn)
      LetwinC0SubgradientAudit.abs_convex continuous_abs.continuousOn
      vertical_shift_tendsto.tendstoUniformlyOn.tendstoLocallyUniformlyOn
  have hKΩ : Icc (-1 : ℝ) 1 ⊆ Ioo (-2) 2 := by
    intro x hx
    constructor <;> linarith [hx.1, hx.2]
  have hmass : μ (Icc (-1 : ℝ) 1) = ENNReal.ofReal 2 := by
    rw [hμ _ measurableSet_Icc, inter_eq_left.mpr hKΩ,
      abs_reference_image (subset_refl _) (by norm_num), Real.volume_Icc]
    norm_num
  have hboundary : μ (frontier (Icc (-1 : ℝ) 1)) = 0 := by
    rw [hμ _ isClosed_frontier.measurableSet]
    have hnull : (volume : Measure ℝ) ({-1, 1} : Set ℝ) = 0 :=
      ((Set.finite_singleton (1 : ℝ)).insert (-1)).measure_zero volume
    apply measure_mono_null (t := ({-1, 1} : Set ℝ)) ?_ hnull
    rintro p ⟨x, hx, hp⟩
    rw [frontier_Icc (by norm_num : (-1 : ℝ) ≤ 1)] at hx
    have hx' : x = -1 ∨ x = 1 := by simpa using hx.1
    rcases hx' with rfl | rfl
    · have h0 := hp 0 (by norm_num)
      have hm := hp (-3 / 2) (by norm_num)
      change |(-1 : ℝ)| + (0 - (-1)) * p ≤ |0| at h0
      change |(-1 : ℝ)| + (-3 / 2 - (-1)) * p ≤ |-3 / 2| at hm
      norm_num at h0 hm
      have heq : p = -1 := by linarith
      simp [heq]
    · have h0 := hp 0 (by norm_num)
      have hm := hp (3 / 2) (by norm_num)
      change |(1 : ℝ)| + (0 - 1) * p ≤ |0| at h0
      change |(1 : ℝ)| + (3 / 2 - 1) * p ≤ |3 / 2| at hm
      norm_num at h0 hm
      have heq : p = 1 := by linarith
      simp [heq]
  have hlim :=
    hcont (Icc (-1 : ℝ) 1)
      (by simpa only [closure_Icc] using (isCompact_Icc : IsCompact (Icc (-1 : ℝ) 1)))
      (by simpa only [closure_Icc] using hKΩ) hboundary
  rw [hmass] at hlim
  exact ⟨μs, μ, hμs, hμ, hmass, hlim⟩

theorem actual_fin0_continuity_set :
    ∃ (μs : ℕ → Measure (EuclideanSpace ℝ (Fin 0))) (μ : Measure (EuclideanSpace ℝ (Fin 0))),
      (∀ n,
          ∀ G : Set (EuclideanSpace ℝ (Fin 0)),
            MeasurableSet G →
              μs n G =
                volume
                  (subgradientImageOn (fun _ => (1 : ℝ) / ((n : ℝ) + 1)) univ (G ∩ univ))) ∧
        (∀ G : Set (EuclideanSpace ℝ (Fin 0)),
            MeasurableSet G →
              μ G = volume (subgradientImageOn (fun _ => (0 : ℝ)) univ (G ∩ univ))) ∧
          μ univ = 1 ∧ Tendsto (fun n => μs n univ) atTop (𝓝 1) := by
  have hc : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) := scalar_shift_tendsto
  obtain ⟨μs, μ, hμs, hμ, _hfin, _hμfin, _hupper, _hlower, hcont⟩ :=
    exists_domain_mongeAmpere_measures_local_limits (v := fun _ : EuclideanSpace ℝ (Fin 0) =>
      (0 : ℝ)) isOpen_univ (fun _ => convexOn_const _ convex_univ)
      (fun _ => continuous_const.continuousOn) (convexOn_const _ convex_univ)
      continuous_const.continuousOn
      hc.tendstoUniformly_const.tendstoUniformlyOn.tendstoLocallyUniformlyOn
  have hmass : μ univ = 1 := by
    rw [hμ _ MeasurableSet.univ, inter_univ]
    exact fin0_reference_volume (mem_univ _)
  have hcl : IsCompact (closure (univ : Set (EuclideanSpace ℝ (Fin 0)))) := by
    rw [closure_univ]
    have heq : (univ : Set (EuclideanSpace ℝ (Fin 0))) = {0} := by
      ext x
      simp [Subsingleton.elim x (0 : EuclideanSpace ℝ (Fin 0))]
    rw [heq]
    exact isCompact_singleton
  have hlim := hcont univ hcl (subset_univ _) (by simp)
  rw [hmass] at hlim
  exact ⟨μs, μ, hμs, hμ, hmass, hlim⟩

end LetwinLocalUniformSubgradientAudit
set_option pp.fullNames true in
#print axioms LetwinLocalUniformSubgradientAudit.actual_vertical_shift_support_bound
set_option pp.fullNames true in
#print axioms LetwinLocalUniformSubgradientAudit.actual_fin0_varying_support_bound
set_option pp.fullNames true in
#print axioms LetwinLocalUniformSubgradientAudit.actual_abs_upper_image
set_option pp.fullNames true in
#print axioms LetwinLocalUniformSubgradientAudit.actual_fin0_upper_image

set_option pp.fullNames true in
#print axioms LetwinLocalUniformSubgradientAudit.actual_varying_abs_contact

set_option pp.fullNames true in
#print axioms LetwinLocalUniformSubgradientAudit.actual_fin0_varying_contact

set_option pp.fullNames true in
#print axioms LetwinLocalUniformSubgradientAudit.actual_varying_abs_volume_upper

set_option pp.fullNames true in
#print axioms LetwinLocalUniformSubgradientAudit.actual_fin0_volume_upper

set_option pp.fullNames true in
#print axioms LetwinLocalUniformSubgradientAudit.actual_varying_abs_lower

set_option pp.fullNames true in
#print axioms LetwinLocalUniformSubgradientAudit.actual_fin0_lower

set_option pp.fullNames true in
#print axioms LetwinLocalUniformSubgradientAudit.actual_varying_abs_continuity_set

set_option pp.fullNames true in
#print axioms LetwinLocalUniformSubgradientAudit.actual_fin0_continuity_set

namespace LetwinC0SubgradientAudit
open FunctionalInequalities.Analysis
/-- Actual nonsmooth absolute-value localization at zero uses its real convex
fixture, with no differentiability or extension assumption. -/
theorem actual_abs_nondiff_localization :
    subgradientImageOn (fun x : ℝ => |x|) (Ioo (-1) 1) {0} =
      subgradientImageOn (fun x : ℝ => |x|) (Ioo (-2) 2) {0} := by
  apply subgradientImageOn_eq_of_isOpen_subset abs_convex isOpen_Ioo
  · intro x hx
    constructor <;> linarith [hx.1, hx.2]
  · exact singleton_subset_iff.mpr (by constructor <;> norm_num)
end LetwinC0SubgradientAudit
#print axioms LetwinC0SubgradientAudit.actual_abs_nondiff_localization
