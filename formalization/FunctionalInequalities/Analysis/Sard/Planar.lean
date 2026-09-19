import FunctionalInequalities.Analysis.Sard.QuadraticCover
import Mathlib.Topology.Bases

/-! # Sard's theorem in the plane

The critical values of a `C²` function on `Fin 2 → ℝ` are Lebesgue null. The critical set is
split at the second derivative. The flat layer is handled by the planar covering lemma of
`Analysis/Sard/QuadraticCover.lean`. On the nonflat layer the critical set is locally a Lipschitz
graph over one coordinate — proved here by an elementary mean-value estimate with linear
principal part, **not** by the implicit function theorem — so the quadratic bound at critical
points collapses onto the one-dimensional covering lemma.

This is dimension two only. It does not prove `Analysis.sard`, which is stated in arbitrary
finite dimension and needs the higher-order flatness stratification.
-/

noncomputable section

open Set MeasureTheory Metric

namespace FunctionalInequalities.Analysis

/-- The two coordinates of `Fin 2 → ℝ` split every vector; `1 - i` is the other index. -/
private lemma decomp_fin_two (i : Fin 2) (v : Fin 2 → ℝ) :
    v = v i • Pi.single i (1 : ℝ) + v (1 - i) • Pi.single (1 - i) (1 : ℝ) := by
  funext k
  fin_cases i <;> fin_cases k <;> simp

private lemma apply_decomp_fin_two (α : (Fin 2 → ℝ) →L[ℝ] ℝ) (i : Fin 2) (v : Fin 2 → ℝ) :
    α v = v i * α (Pi.single i (1 : ℝ)) + v (1 - i) * α (Pi.single (1 - i) (1 : ℝ)) := by
  have h := congrArg α (decomp_fin_two i v)
  simpa [smul_eq_mul] using h

private lemma norm_le_abs_add_abs (i : Fin 2) (v : Fin 2 → ℝ) :
    ‖v‖ ≤ |v i| + |v (1 - i)| := by
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro k
  fin_cases i <;> fin_cases k <;> simp only [Real.norm_eq_abs] <;> simp

private lemma exists_apply_single_ne_zero {α : (Fin 2 → ℝ) →L[ℝ] ℝ} (hα : α ≠ 0) :
    ∃ i : Fin 2, α (Pi.single i (1 : ℝ)) ≠ 0 := by
  by_contra h
  push Not at h
  refine hα (ContinuousLinearMap.ext fun v => ?_)
  rw [apply_decomp_fin_two α 0 v, h 0, h (1 - 0)]
  simp

/-- A nonzero functional on the plane makes the region where it is small a Lipschitz graph
over one of the two coordinates. Elementary linear algebra; no implicit function theorem. -/
private lemma exists_graph_direction {α : (Fin 2 → ℝ) →L[ℝ] ℝ} (hα : α ≠ 0) :
    ∃ (j : Fin 2) (ε L : ℝ), 0 < ε ∧ 0 < L ∧
      ∀ v : Fin 2 → ℝ, |α v| ≤ ε * ‖v‖ → ‖v‖ ≤ L * |v j| := by
  obtain ⟨i, hi⟩ := exists_apply_single_ne_zero hα
  set A : ℝ := α (Pi.single i (1 : ℝ)) with hAdef
  set B : ℝ := α (Pi.single (1 - i) (1 : ℝ)) with hBdef
  have ha : 0 < |A| := abs_pos.mpr hi
  have hb : 0 ≤ |B| := abs_nonneg _
  refine ⟨1 - i, |A| / 4, 4 * (|A| / 4 + |B|) / (3 * |A|) + 1, by positivity, by positivity, ?_⟩
  intro v hv
  have hdec := apply_decomp_fin_two α i v
  have hsum := norm_le_abs_add_abs i v
  have hiA : v i * A = α v - v (1 - i) * B := by rw [hdec]; ring
  have h1 : |A| * |v i| ≤ |α v| + |B| * |v (1 - i)| := by
    calc |A| * |v i| = |v i * A| := by rw [abs_mul]; ring
      _ = |α v - v (1 - i) * B| := by rw [hiA]
      _ ≤ |α v| + |v (1 - i) * B| := abs_sub _ _
      _ = |α v| + |B| * |v (1 - i)| := by rw [abs_mul]; ring
  have h2 : |α v| ≤ |A| / 4 * (|v i| + |v (1 - i)|) :=
    hv.trans (mul_le_mul_of_nonneg_left hsum (by positivity))
  have h3 : 3 * |A| / 4 * |v i| ≤ (|A| / 4 + |B|) * |v (1 - i)| := by nlinarith
  have h4 : |v i| ≤ 4 * (|A| / 4 + |B|) / (3 * |A|) * |v (1 - i)| := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity : (0 : ℝ) < 3 * |A|)]
    linarith
  have hexp : (4 * (|A| / 4 + |B|) / (3 * |A|) + 1) * |v (1 - i)|
      = 4 * (|A| / 4 + |B|) / (3 * |A|) * |v (1 - i)| + |v (1 - i)| := by ring
  rw [hexp]
  linarith

/-- Mean-value quadratic bound at a critical point, with a fixed second-derivative bound on a
ball. Unlike the flat-point remainder this keeps a genuine constant. -/
private lemma abs_sub_le_of_fderiv_eq_zero {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {u : V → ℝ} {x₀ : V} {δ M : ℝ} (hu : ContDiff ℝ 2 u) (hδ : 0 < δ)
    (hM : ∀ z ∈ ball x₀ δ, ‖fderiv ℝ (fderiv ℝ u) z‖ ≤ M)
    {x : V} (hx : x ∈ ball x₀ δ) (hx1 : fderiv ℝ u x = 0) {y : V} (hy : y ∈ ball x₀ δ) :
    |u y - u x| ≤ M * ‖y - x‖ ^ 2 := by
  have hM0 : 0 ≤ M :=
    le_trans (ContinuousLinearMap.opNorm_nonneg _) (hM x₀ (mem_ball_self hδ))
  have hdu : Differentiable ℝ u := hu.differentiable (by norm_num)
  have hdf : Differentiable ℝ (fderiv ℝ u) :=
    (hu.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiable (by norm_num)
  have hfirst : ∀ z ∈ ball x₀ δ, ‖fderiv ℝ u z‖ ≤ M * ‖z - x‖ := by
    intro z hz
    simpa [hx1] using (convex_ball x₀ δ).norm_image_sub_le_of_norm_fderiv_le
      (fun z _ ↦ hdf z) hM hx hz
  have hseg : segment ℝ x y ⊆ ball x₀ δ := (convex_ball x₀ δ).segment_subset hx hy
  have hbound : ∀ z ∈ segment ℝ x y, ‖fderiv ℝ u z‖ ≤ M * ‖y - x‖ := fun z hz =>
    (hfirst z (hseg hz)).trans
      (mul_le_mul_of_nonneg_left (norm_sub_le_of_mem_segment hz) hM0)
  have h := (convex_segment x y).norm_image_sub_le_of_norm_fderiv_le
    (fun z _ ↦ hdu z) hbound (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  simpa [Real.norm_eq_abs, pow_two, mul_assoc] using h

/-- Near a point with nonvanishing second derivative, the critical set of `u` is a Lipschitz
graph over one coordinate, so the quadratic bound at critical points collapses to the
one-dimensional covering lemma. Criticality at the base point is not needed. -/
private lemma exists_ball_image_critical_null {u : (Fin 2 → ℝ) → ℝ} (hu : ContDiff ℝ 2 u)
    {x₀ : Fin 2 → ℝ} (h2 : iteratedFDeriv ℝ 2 u x₀ ≠ 0) :
    ∃ δ > 0, (volume : Measure ℝ) (u '' ({x | fderiv ℝ u x = 0} ∩ ball x₀ δ)) = 0 := by
  classical
  have hdf : Differentiable ℝ (fderiv ℝ u) :=
    (hu.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiable (by norm_num)
  set T : (Fin 2 → ℝ) →L[ℝ] ((Fin 2 → ℝ) →L[ℝ] ℝ) := fderiv ℝ (fderiv ℝ u) x₀ with hTdef
  have hT : T ≠ 0 := by
    intro h
    refine h2 (norm_eq_zero.mp ?_)
    have hn : ‖T‖ = 0 := by rw [h]; exact ContinuousLinearMap.opNorm_zero
    rw [hTdef] at hn
    simpa [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv] using hn
  obtain ⟨v₀, hv₀⟩ : ∃ v, T v ≠ 0 := by
    by_contra h
    push Not at h
    exact hT (ContinuousLinearMap.ext h)
  obtain ⟨w, hw⟩ : ∃ w, (T v₀) w ≠ 0 := by
    by_contra h
    push Not at h
    exact hv₀ (ContinuousLinearMap.ext h)
  set α : (Fin 2 → ℝ) →L[ℝ] ℝ := T.flip w with hαdef
  have hα : α ≠ 0 := by
    intro h
    exact hw (by simpa [hαdef] using congrArg (fun L : (Fin 2 → ℝ) →L[ℝ] ℝ => L v₀) h)
  obtain ⟨j, ε, L, hε, hL, hlip⟩ := exists_graph_direction hα
  have hZc : Continuous fun z => fderiv ℝ (fderiv ℝ u) z :=
    (hu.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).continuous_fderiv (by norm_num)
  set η : ℝ := min (ε / (‖w‖ + 1)) 1 with hηdef
  have hη : 0 < η := lt_min (div_pos hε (by positivity)) one_pos
  obtain ⟨δ, hδ, hδZ⟩ :
      ∃ δ > 0, ∀ z ∈ ball x₀ δ, ‖fderiv ℝ (fderiv ℝ u) z - T‖ ≤ η := by
    have hnc : Continuous fun z => dist (fderiv ℝ (fderiv ℝ u) z) T :=
      hZc.dist continuous_const
    have hx₀ : x₀ ∈ {z : Fin 2 → ℝ | dist (fderiv ℝ (fderiv ℝ u) z) T < η} := by
      have hd : dist (fderiv ℝ (fderiv ℝ u) x₀) T = 0 := by rw [← hTdef]; exact dist_self T
      simpa [hd] using hη
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp (isOpen_lt hnc continuous_const) x₀ hx₀
    refine ⟨δ, hδ, fun z hz => ?_⟩
    have h : dist (fderiv ℝ (fderiv ℝ u) z) T < η := hball hz
    have hconv : ‖fderiv ℝ (fderiv ℝ u) z - T‖ = dist (fderiv ℝ (fderiv ℝ u) z) T :=
      (dist_eq_norm (fderiv ℝ (fderiv ℝ u) z) T).symm
    rw [hconv]
    exact h.le
  set M : ℝ := ‖T‖ + 1 with hMdef
  have hTnn : (0 : ℝ) ≤ ‖T‖ := ContinuousLinearMap.opNorm_nonneg T
  have hM0 : (0 : ℝ) ≤ M := by rw [hMdef]; linarith
  have hMb : ∀ z ∈ ball x₀ δ, ‖fderiv ℝ (fderiv ℝ u) z‖ ≤ M := by
    intro z hz
    have hη1 : η ≤ 1 := min_le_right _ _
    have h := hδZ z hz
    have heq : fderiv ℝ (fderiv ℝ u) z = (fderiv ℝ (fderiv ℝ u) z - T) + T := by abel
    calc ‖fderiv ℝ (fderiv ℝ u) z‖ = ‖(fderiv ℝ (fderiv ℝ u) z - T) + T‖ := by rw [← heq]
      _ ≤ ‖fderiv ℝ (fderiv ℝ u) z - T‖ + ‖T‖ := ContinuousLinearMap.opNorm_add_le _ _
      _ ≤ M := by rw [hMdef]; linarith
  set S₀ : Set (Fin 2 → ℝ) := {x | fderiv ℝ u x = 0} ∩ ball x₀ δ with hS₀def
  have hgraph : ∀ x ∈ S₀, ∀ y ∈ S₀, ‖y - x‖ ≤ L * |y j - x j| := by
    intro x hx y hy
    have hmv : ‖fderiv ℝ u y - fderiv ℝ u x - T (y - x)‖ ≤ η * ‖y - x‖ :=
      (convex_ball x₀ δ).norm_image_sub_le_of_norm_fderiv_le'
        (fun z _ => hdf z) (fun z hz => hδZ z hz) hx.2 hy.2
    have hx1 : fderiv ℝ u x = 0 := hx.1
    have hy1 : fderiv ℝ u y = 0 := hy.1
    have hzero : ‖T (y - x)‖ ≤ η * ‖y - x‖ := by
      simpa only [hx1, hy1, sub_zero, zero_sub, norm_neg] using hmv
    have hw1 : η * ‖w‖ ≤ ε := by
      have hηe : η ≤ ε / (‖w‖ + 1) := min_le_left _ _
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < ‖w‖ + 1)] at hηe
      nlinarith [hη.le, norm_nonneg w]
    have hαv : |α (y - x)| ≤ ε * ‖y - x‖ := by
      calc |α (y - x)| ≤ ‖T (y - x)‖ * ‖w‖ := by
            simpa [hαdef, Real.norm_eq_abs] using (T (y - x)).le_opNorm w
        _ ≤ (η * ‖y - x‖) * ‖w‖ := mul_le_mul_of_nonneg_right hzero (norm_nonneg w)
        _ = (η * ‖w‖) * ‖y - x‖ := by ring
        _ ≤ ε * ‖y - x‖ := mul_le_mul_of_nonneg_right hw1 (norm_nonneg _)
    simpa using hlip (y - x) hαv
  have hquad : ∀ x ∈ S₀, ∀ y ∈ S₀, |u y - u x| ≤ M * ‖y - x‖ ^ 2 := fun x hx y hy =>
    abs_sub_le_of_fderiv_eq_zero hu hδ hMb hx.2 hx.1 hy.2
  have hkey : ∀ x ∈ S₀, ∀ y ∈ S₀, |u y - u x| ≤ (M * L ^ 2) * |y j - x j| ^ 2 := by
    intro x hx y hy
    have h3 : ‖y - x‖ ^ 2 ≤ (L * |y j - x j|) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hgraph x hx y hy) 2
    calc |u y - u x| ≤ M * ‖y - x‖ ^ 2 := hquad x hx y hy
      _ ≤ M * (L * |y j - x j|) ^ 2 := mul_le_mul_of_nonneg_left h3 hM0
      _ = (M * L ^ 2) * |y j - x j| ^ 2 := by ring
  have hchoice : ∀ t : ℝ, ∃ x : Fin 2 → ℝ, (∃ z, z ∈ S₀ ∧ z j = t) → x ∈ S₀ ∧ x j = t := by
    intro t
    by_cases h : ∃ z, z ∈ S₀ ∧ z j = t
    · obtain ⟨z, hz⟩ := h
      exact ⟨z, fun _ => hz⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose G hG using hchoice
  set A : Set ℝ := (fun x : Fin 2 → ℝ => x j) '' S₀ with hAdef
  have hAbdd : Bornology.IsBounded A := by
    rw [isBounded_iff_forall_norm_le]
    refine ⟨‖x₀‖ + δ, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    have h1 : |x j| ≤ ‖x‖ := by simpa [Real.norm_eq_abs] using norm_le_pi_norm x j
    have h2' : ‖x - x₀‖ < δ := by simpa [dist_eq_norm] using hx.2
    have h3 : ‖x‖ ≤ ‖x₀‖ + ‖x - x₀‖ := by
      calc ‖x‖ = ‖x₀ + (x - x₀)‖ := by rw [add_sub_cancel]
        _ ≤ ‖x₀‖ + ‖x - x₀‖ := norm_add_le _ _
    simp only [Real.norm_eq_abs]
    linarith
  have hsub : u '' S₀ ⊆ (fun t => u (G t)) '' A := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨hGA, hGj⟩ := hG (x j) ⟨x, hx, rfl⟩
    have hle : ‖x - G (x j)‖ ≤ L * |x j - (G (x j)) j| := hgraph (G (x j)) hGA x hx
    rw [hGj, sub_self, abs_zero, mul_zero] at hle
    have hxe : x = G (x j) := sub_eq_zero.mp (norm_le_zero_iff.mp hle)
    exact ⟨x j, ⟨x, hx, rfl⟩, by show u (G (x j)) = u x; rw [← hxe]⟩
  have hquad1 : ∀ s ∈ A, ∀ t ∈ A, |u (G t) - u (G s)| ≤ (M * L ^ 2) * |t - s| ^ 2 := by
    intro s hs t ht
    obtain ⟨z, hz, hzs⟩ := hs
    obtain ⟨z', hz', hz't⟩ := ht
    obtain ⟨hGs, hGsj⟩ := hG s ⟨z, hz, hzs⟩
    obtain ⟨hGt, hGtj⟩ := hG t ⟨z', hz', hz't⟩
    have h := hkey (G s) hGs (G t) hGt
    rwa [hGsj, hGtj] at h
  exact ⟨δ, hδ, measure_mono_null hsub
    (volume_image_eq_zero_of_quadratic_bound hAbdd hquad1)⟩

/-- The critical points of a `C²` function on the plane at which the second derivative does
not vanish have Lebesgue null image. The set is not assumed measurable. -/
theorem volume_image_nonflat_eq_zero {u : (Fin 2 → ℝ) → ℝ} (hu : ContDiff ℝ 2 u) :
    (volume : Measure ℝ)
      (u '' {x | fderiv ℝ u x = 0 ∧ iteratedFDeriv ℝ 2 u x ≠ 0}) = 0 := by
  classical
  set N : Set (Fin 2 → ℝ) := {x | fderiv ℝ u x = 0 ∧ iteratedFDeriv ℝ 2 u x ≠ 0} with hNdef
  choose δ hδ hnull using fun p : N => exists_ball_image_critical_null hu p.2.2
  obtain ⟨I, hIc, hIeq⟩ :=
    TopologicalSpace.isOpen_iUnion_countable (fun p : N => ball (p : Fin 2 → ℝ) (δ p))
      (fun _ => isOpen_ball)
  have hcov : N ⊆ ⋃ p ∈ I, ball (p : Fin 2 → ℝ) (δ p) := by
    intro x hx
    rw [hIeq]
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, mem_ball_self (hδ _)⟩
  have hsub : u '' N ⊆
      ⋃ p ∈ I, u '' ({x | fderiv ℝ u x = 0} ∩ ball (p : Fin 2 → ℝ) (δ p)) := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.mp (hcov hx)
    exact mem_iUnion₂.mpr ⟨p, hp, ⟨x, ⟨hx.1, hxp⟩, rfl⟩⟩
  exact measure_mono_null hsub ((measure_biUnion_null_iff hIc).mpr fun p _ => hnull p)

/-- Sard's theorem in the plane: the critical values of a `C²` function on `Fin 2 → ℝ` are
Lebesgue null. The critical set is not assumed measurable. This is the two-dimensional case
only; the general statement in arbitrary finite dimension is not proved here. -/
theorem sard_plane {u : (Fin 2 → ℝ) → ℝ} (hu : ContDiff ℝ 2 u) :
    (volume : Measure ℝ) (u '' {x | fderiv ℝ u x = 0}) = 0 := by
  have hsplit : {x : Fin 2 → ℝ | fderiv ℝ u x = 0} =
      {x | fderiv ℝ u x = 0 ∧ iteratedFDeriv ℝ 2 u x = 0} ∪
        {x | fderiv ℝ u x = 0 ∧ iteratedFDeriv ℝ 2 u x ≠ 0} := by
    ext x
    by_cases h : iteratedFDeriv ℝ 2 u x = 0 <;> simp [h]
  rw [hsplit, image_union]
  exact measure_union_null (volume_image_flat_univ_eq_zero hu)
    (volume_image_nonflat_eq_zero hu)

end FunctionalInequalities.Analysis
