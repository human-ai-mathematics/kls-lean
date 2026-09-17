import FunctionalInequalities.Analysis.Whitney.Extension
import FunctionalInequalities.Analysis.Whitney.Partition

/-! # Construction from a compact first-order Whitney jet -/

noncomputable section

open Set Metric Function Filter
open scoped ContDiff Topology

namespace FunctionalInequalities.Analysis.WhitneyJet

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem hasFDerivAt_affine (f : V → ℝ) (F : V → V →L[ℝ] ℝ) (a y : V) :
    HasFDerivAt (affine f F a) (F a) y := by
  change HasFDerivAt (fun w => f a + F a (w - a)) (F a) y
  simp_rw [map_sub]
  exact ((F a).hasFDerivAt.sub_const (F a a)).const_add (f a)

theorem contDiff_affine (f : V → ℝ) (F : V → V →L[ℝ] ℝ) (a : V) :
    ContDiff ℝ ∞ (affine f F a) := by
  exact contDiff_const.add ((F a).contDiff.comp (contDiff_id.sub contDiff_const))

/-- The actual off-set candidate: a locally finite weighted sum of nearest-point affine jets. -/
def candidate (S C : Set V) (p : V → V) (f : V → ℝ) (F : V → V →L[ℝ] ℝ) (y : V) : ℝ :=
  ∑ᶠ z, WhitneyCover.weight S C z y * affine f F (p z) y

open WhitneyCover

theorem candidate_eq_sum {S C : Set V} (p : V → V) (f : V → ℝ) (F : V → V →L[ℝ] ℝ)
    {t : Finset V} {y : V} (ht : ∀ z ∉ t, bumpFamily S C z y = 0) :
    candidate S C p f F y = ∑ z ∈ t, weight S C z y * affine f F (p z) y := by
  apply finsum_eq_finsetSum_of_support_subset
  intro z hz
  by_contra hzt
  exact hz (by simp [weight, ht z hzt])

section FiniteDimension

variable [FiniteDimensional ℝ V] {S C : Set V}

theorem contDiffOn_candidate (hS : IsClosed S) (hne : S.Nonempty) (hC : C ⊆ Sᶜ)
    (hdisj : C.PairwiseDisjoint (fun z => ball z (radius S z)))
    (hcover : Sᶜ = ⋃ z ∈ C, ball z (5 * radius S z))
    (p : V → V) (f : V → ℝ) (F : V → V →L[ℝ] ℝ) :
    ContDiffOn ℝ ∞ (candidate S C p f F) Sᶜ := by
  intro y hy
  obtain ⟨t, -, -, -, ht⟩ := exists_local_finset hS hne hC hdisj hy
  have hsum : ContDiffAt ℝ ∞ (fun w => ∑ z ∈ t, weight S C z w * affine f F (p z) w) y := by
    apply ContDiffAt.sum
    intro z _
    exact ((contDiffOn_weight hS hne hC hdisj hcover z).contDiffAt
      (hS.isOpen_compl.mem_nhds hy)).mul (contDiff_affine f F (p z)).contDiffAt
  apply (hsum.congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [ball_mem_nhds y (radius_pos S hS hne hy)] with w hw
  exact candidate_eq_sum p f F (ht w hw)

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] in
/-- A nearest anchor belonging to a locally active center remains uniformly near the
evaluation point when the latter is near the closed set. -/
theorem dist_anchor_le {y z a : V} (hdy : infDist y S < 1 / 2)
    (hz : radius S z ≤ 2 * radius S y ∧ dist z y ≤ 20 * radius S y)
    (ha : infDist z S = dist z a) : dist a y ≤ 3 * infDist y S := by
  have hry : 20 * radius S y = infDist y S := by
    dsimp [radius]
    rw [min_eq_right (by linarith : infDist y S ≤ 1)]
    ring
  have hmin : min 1 (infDist z S) < 1 := by
    have hrz := hz.1
    dsimp [radius] at hrz
    have hm : min 1 (infDist y S) ≤ infDist y S := min_le_right _ _
    linarith
  have hdz : infDist z S ≤ 1 := by
    by_contra h
    rw [min_eq_left (le_of_lt (not_le.1 h))] at hmin
    exact (lt_irrefl 1) hmin
  have hrz : 20 * radius S z = infDist z S := by
    dsimp [radius]; rw [min_eq_right hdz]; ring
  have hdist := dist_triangle a z y
  rw [dist_comm a z, ← ha] at hdist
  linarith [hz.1, hz.2]

omit [FiniteDimensional ℝ V] in
/-- The finite-sum cancellation used in the derivative estimate. -/
theorem derivative_sum_sub (t : Finset V) (φ : V → ℝ) (D : V → V →L[ℝ] ℝ)
    (A : V → ℝ) (G : V → V →L[ℝ] ℝ) (a : ℝ) (L : V →L[ℝ] ℝ)
    (hφ : ∑ i ∈ t, φ i = 1) (hD : ∑ i ∈ t, D i = 0) :
    (∑ i ∈ t, (φ i • G i + A i • D i)) - L =
      (∑ i ∈ t, φ i • (G i - L)) + (∑ i ∈ t, (A i - a) • D i) := by
  have h1 : (∑ i ∈ t, φ i • (G i - L)) = (∑ i ∈ t, φ i • G i) - L := by
    simp_rw [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hφ, one_smul]
  have h2 : (∑ i ∈ t, (A i - a) • D i) = ∑ i ∈ t, A i • D i := by
    calc
      _ = ∑ i ∈ t, (A i • D i - a • D i) :=
        Finset.sum_congr rfl (fun i _ => sub_smul (A i) a (D i))
      _ = (∑ i ∈ t, A i • D i) - a • (∑ i ∈ t, D i) := by
        rw [Finset.sum_sub_distrib, Finset.smul_sum]
      _ = _ := by rw [hD, smul_zero, sub_zero]
  rw [h1, h2, Finset.sum_add_distrib]
  module

/-- Construct a smooth candidate on the complement with the two uniform jet estimates
required by the previously proved boundary gluing theorem. -/
theorem exists_compl_approx (hS : IsCompact S) (hne : S.Nonempty)
    {f : V → ℝ} {F : V → V →L[ℝ] ℝ} (hF : ContinuousOn F S)
    (hR : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ x ∈ S, ∀ y ∈ S, ‖y - x‖ < δ →
        ‖f y - f x - F x (y - x)‖ ≤ ε * ‖y - x‖) :
    ∃ w : V → ℝ, ContDiffOn ℝ 1 w Sᶜ ∧
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ y ∉ S, ∀ a ∈ S, infDist y S = dist y a → infDist y S < δ →
          ‖w y - affine f F a y‖ ≤ ε * infDist y S ∧ ‖fderiv ℝ w y - F a‖ ≤ ε := by
  classical
  obtain ⟨C, hC, -, hdisj, hcover, -, -, -⟩ := exists_cover hS.isClosed hne
  choose p hpS hpdist using fun z : V => hS.exists_infDist_eq_dist hne z
  obtain ⟨K, hK, hKder⟩ := exists_weight_derivative_bound hS.isClosed hne hC hdisj hcover
  let N : ℝ := (81 ^ Module.finrank ℝ V : ℕ)
  have hN : 0 ≤ N := by dsimp [N]; positivity
  let w := candidate S C p f F
  have hw := contDiffOn_candidate hS.isClosed hne hC hdisj hcover p f F
  refine ⟨w, hw.of_le (by simp), fun ε hε => ?_⟩
  let η := ε / (8 + 140 * N * K)
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨δR, hδR, hrem⟩ := hR η hη
  obtain ⟨δF, hδF, hder⟩ := Metric.uniformContinuousOn_iff.1
    (hS.uniformContinuousOn_of_continuous hF) η hη
  refine ⟨min (1 / 2) (min (δR / 4) (δF / 4)),
    lt_min (by norm_num) (lt_min (by positivity) (by positivity)), ?_⟩
  intro y hy a ha hnear hyd
  have hry := radius_pos S hS.isClosed hne hy
  have hdy := (hS.isClosed.notMem_iff_infDist_pos hne).1 hy
  have hyd1 : infDist y S < 1 / 2 := hyd.trans_le (min_le_left _ _)
  have hydR : 4 * infDist y S < δR := by
    have := hyd.trans_le ((min_le_right _ _).trans (min_le_left _ _)); linarith
  have hydF : 4 * infDist y S < δF := by
    have := hyd.trans_le ((min_le_right _ _).trans (min_le_right _ _)); linarith
  have hscale : 20 * radius S y = infDist y S := by
    dsimp [radius]; rw [min_eq_right (by linarith : infDist y S ≤ 1)]; ring
  obtain ⟨t, htC, htN, htrad, ht⟩ := exists_local_finset hS.isClosed hne hC hdisj hy
  have htN' : (t.card : ℝ) ≤ N := by dsimp [N]; exact_mod_cast htN
  have hym : y ∈ ball y (radius S y) := mem_ball_self hry
  have hφzero : ∀ q ∈ ball y (radius S y), ∀ z ∉ t, weight S C z q = 0 := by
    intro q hq z hz; simp [weight, ht q hq z hz]
  have hsum1 : ∀ q ∈ ball y (radius S y), ∑ z ∈ t, weight S C z q = 1 := by
    intro q hq
    have hqS : q ∉ S := closedBall_subset_compl S hry (show dist q y ≤ 8 * radius S y by
      have : dist q y < radius S y := hq; linarith)
    rw [← sum_weight_eq_one hS.isClosed hne hC hdisj hcover hqS]
    symm
    apply finsum_eq_finsetSum_of_support_subset
    intro z hz
    by_contra hzt
    exact hz (hφzero q hq z hzt)
  have hφder : ∀ z, HasFDerivAt (weight S C z) (fderiv ℝ (weight S C z) y) y := by
    intro z
    exact ((contDiffOn_weight hS.isClosed hne hC hdisj hcover z).differentiableOn
      (by simp) y hy).differentiableAt (hS.isClosed.isOpen_compl.mem_nhds hy) |>.hasFDerivAt
  have hsumD : ∑ z ∈ t, fderiv ℝ (weight S C z) y = 0 := by
    have h := (HasFDerivAt.fun_sum (fun z (_ : z ∈ t) => hφder z)).congr_of_eventuallyEq
      (show (fun _ : V => (1 : ℝ)) =ᶠ[𝓝 y] (fun q => ∑ z ∈ t, weight S C z q) by
        filter_upwards [ball_mem_nhds y hry] with q hq
        exact (hsum1 q hq).symm)
    simpa using h.fderiv.symm
  have hlocal : w =ᶠ[𝓝 y] fun q => ∑ z ∈ t, weight S C z q * affine f F (p z) q := by
    filter_upwards [ball_mem_nhds y hry] with q hq
    exact candidate_eq_sum p f F (ht q hq)
  have hDw := (HasFDerivAt.fun_sum (fun z (_ : z ∈ t) =>
    (hφder z).fun_mul (hasFDerivAt_affine f F (p z) y))).congr_of_eventuallyEq hlocal
  have hpnear : ∀ z ∈ t, dist (p z) y ≤ 3 * infDist y S ∧ dist (p z) a ≤ 4 * infDist y S := by
    intro z hz
    have h1 := dist_anchor_le hyd1 (htrad z hz).2 (hpdist z)
    refine ⟨h1, ?_⟩
    have := dist_triangle (p z) y a
    rw [← hnear] at this
    linarith
  have hG : ∀ z ∈ t, ‖F (p z) - F a‖ ≤ η := by
    intro z hz
    have := hder (p z) (hpS z) a ha ((hpnear z hz).2.trans_lt hydF)
    simpa only [dist_eq_norm] using this.le
  have hA : ∀ z ∈ t, ‖affine f F (p z) y - affine f F a y‖ ≤ 7 * η * infDist y S := by
    intro z hz
    have h1 := hrem a ha (p z) (hpS z) (by
      rw [← dist_eq_norm]; exact (hpnear z hz).2.trans_lt hydR)
    have h2 := norm_affine_sub_le f F (p z) a y
    have h3 := mul_le_mul_of_nonneg_right (hG z hz) (norm_nonneg (y - p z))
    have h4 := mul_le_mul_of_nonneg_left (hpnear z hz).2 hη.le
    have h5 := mul_le_mul_of_nonneg_left (hpnear z hz).1 hη.le
    simp only [dist_eq_norm] at h4 h5
    rw [norm_sub_rev y (p z)] at h2 h3
    linarith
  have hvalue : ‖w y - affine f F a y‖ ≤ 7 * η * infDist y S := by
    have heq : w y - affine f F a y =
        ∑ z ∈ t, weight S C z y * (affine f F (p z) y - affine f F a y) := by
      rw [hlocal.self_of_nhds]
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum1 y hym, one_mul]
    rw [heq]
    calc
      _ ≤ ∑ z ∈ t, ‖weight S C z y * (affine f F (p z) y - affine f F a y)‖ := norm_sum_le _ _
      _ ≤ ∑ z ∈ t, weight S C z y * (7 * η * infDist y S) := by
        apply Finset.sum_le_sum
        intro z hz
        rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (weight_nonneg hS.isClosed hne hC hdisj hcover z hy)]
        exact mul_le_mul_of_nonneg_left (hA z hz) (weight_nonneg hS.isClosed hne hC hdisj hcover z hy)
      _ = _ := by rw [← Finset.sum_mul, hsum1 y hym, one_mul]
  have hgradient : ‖fderiv ℝ w y - F a‖ ≤ η + 140 * N * K * η := by
    rw [hDw.fderiv, derivative_sum_sub t (fun z => weight S C z y)
      (fun z => fderiv ℝ (weight S C z) y) (fun z => affine f F (p z) y)
      (fun z => F (p z)) (affine f F a y) (F a) (hsum1 y hym) hsumD]
    have hfirst : ‖∑ z ∈ t, weight S C z y • (F (p z) - F a)‖ ≤ η := by
      calc
        _ ≤ ∑ z ∈ t, ‖weight S C z y • (F (p z) - F a)‖ := norm_sum_le _ _
        _ ≤ ∑ z ∈ t, weight S C z y * η := by
          apply Finset.sum_le_sum
          intro z hz
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (weight_nonneg hS.isClosed hne hC hdisj hcover z hy)]
          exact mul_le_mul_of_nonneg_left (hG z hz) (weight_nonneg hS.isClosed hne hC hdisj hcover z hy)
        _ = _ := by rw [← Finset.sum_mul, hsum1 y hym, one_mul]
    have hsecond : ‖∑ z ∈ t, (affine f F (p z) y - affine f F a y) •
        fderiv ℝ (weight S C z) y‖ ≤ 140 * N * K * η := by
      calc
        _ ≤ ∑ z ∈ t, ‖(affine f F (p z) y - affine f F a y) • fderiv ℝ (weight S C z) y‖ := norm_sum_le _ _
        _ ≤ ∑ _z ∈ t, (7 * η * infDist y S) * (K / radius S y) := by
          apply Finset.sum_le_sum
          intro z hz
          rw [norm_smul]
          exact mul_le_mul (hA z hz) (hKder y hy z) (norm_nonneg _) (by positivity)
        _ = (t.card : ℝ) * (140 * K * η) := by
          simp only [Finset.sum_const, nsmul_eq_mul]
          rw [← hscale]
          field_simp
          ring
        _ ≤ N * (140 * K * η) := mul_le_mul_of_nonneg_right htN' (by positivity)
        _ = _ := by ring
    exact (norm_add_le _ _).trans (add_le_add hfirst hsecond)
  have hηε : (8 + 140 * N * K) * η = ε := by
    dsimp [η]
    field_simp
  have hvalueε : 7 * η ≤ ε := by
    have : 0 ≤ 140 * N * K * η := by positivity
    nlinarith
  have hgradε : η + 140 * N * K * η ≤ ε := by nlinarith
  exact ⟨hvalue.trans (mul_le_mul_of_nonneg_right hvalueε hdy.le), hgradient.trans hgradε⟩


/-- Whitney's C¹ extension theorem for a compact first-order real-valued jet.
The uniform remainder condition and continuity of the prescribed derivative suffice;
no interior, positive dimension, or nonemptiness assumption is needed. -/
theorem exists_contDiff_extension (hS : IsCompact S)
    {f : V → ℝ} {F : V → V →L[ℝ] ℝ} (hF : ContinuousOn F S)
    (hR : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ x ∈ S, ∀ y ∈ S, ‖y - x‖ < δ →
        ‖f y - f x - F x (y - x)‖ ≤ ε * ‖y - x‖) :
    ∃ v : V → ℝ, ContDiff ℝ 1 v ∧ EqOn v f S ∧
      ∀ x ∈ S, fderiv ℝ v x = F x := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · exact ⟨fun _ => 0, contDiff_const, by simp, by simp⟩
  · obtain ⟨w, hw, happ⟩ := exists_compl_approx hS hne hF hR
    exact exists_contDiff_of_compl_approx hS hF hR hw happ

end FiniteDimension

end FunctionalInequalities.Analysis.WhitneyJet
