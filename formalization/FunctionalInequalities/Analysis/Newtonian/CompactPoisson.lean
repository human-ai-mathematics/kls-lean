import FunctionalInequalities.Analysis.Newtonian.Representation
import FunctionalInequalities.Analysis.Newtonian.Schauder
import FunctionalInequalities.Analysis.Newtonian.GradientBound
import FunctionalInequalities.Analysis.Holder.Closure
import FunctionalInequalities.Analysis.Holder.ZeroExtension
import FunctionalInequalities.Analysis.Divergence

/-!
# Compactly supported solutions of Poisson's equation (GT Theorem 4.5)

Theorem 4.5 of Gilbarg–Trudinger, *Elliptic Partial Differential Equations of Second Order*, Classics
2001 (ISBN 3-540-41160-7), p. 60, for compactly supported solutions. For `u ∈ C²₀(ℝⁿ)`, `n ≥ 2`
(including `n = 2`), with `Δu = f` and `f` locally `α`-Hölder (`0 < α < 1`; uniformly on every compact
set, as in the definition on pp. 51–53):

* `f` vanishes off `supp u`, and the representation (4.15) `u(x) = ∫ Γ(x - y) f(y) dy` holds, with `u`
  equal to the Newtonian potential of `f` over any set containing `supp u`
  (`compactPoisson_eq_newtonianPotential`);
* `u ∈ C^{2,α}(ℝⁿ)`: the actual Hessian has a global Hölder cap;
* for every ball `B = B_R(c) ⊇ supp u`, both estimates (4.14) in the diameter normalisation
  `d = diam B = 2R` (p. 53): `sup ‖D²u‖ + (2R)^α [D²u]_α ≤ C₂(n, α) (M + (2R)^α H)` and
  `|u| + 2R ‖Du‖ ≤ C₁(n) R² M`, where `M`, `H` are any bound and Hölder cap of `f` on `B`
  (`compactPoisson_first_estimate`, `compactPoisson_hessian_estimates`, `compactPoisson_estimates`).

`C₁ = 8n` is chosen before `α`; `C₂ = 3 C(n, α)`, with `C(n, α)` the constant of Lemma 4.4
(`newtonianPotential_schauder`), is chosen before `c, R, u, f`. `compactPoisson_GT4_5` states the theorem
in the source class. Norms are the actual operator norms of `fderiv ℝ u` and `fderiv ℝ (fderiv ℝ u)`.
The general (not compactly supported) case and the harmonic half of Theorem 4.6 are not treated here.
The support lemma `fderiv_of_notMem_tsupport` comes from Mathlib calculus.
-/

noncomputable section

open Set Metric MeasureTheory
open scoped NNReal
open FunctionalInequalities.Analysis.BakryEmery

namespace FunctionalInequalities.Analysis

section CompactPoisson

variable {n : ℕ}

/-- The actual second derivative vanishes off the topological support. -/
theorem fderiv_fderiv_eq_zero_of_notMem_tsupport {u : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∉ tsupport u) : fderiv ℝ (fderiv ℝ u) x = 0 :=
  Function.notMem_support.mp fun h => hx (tsupport_fderiv_subset ℝ (support_fderiv_subset ℝ h))

/-- The actual Laplacian vanishes off the topological support. -/
theorem laplacian_eq_zero_of_notMem_tsupport {u : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∉ tsupport u) : Laplacian.laplacian u x = 0 := by
  have h0 : iteratedFDeriv ℝ 2 u x = 0 := Function.notMem_support.mp fun h => hx (support_iteratedFDeriv_subset 2 h)
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis u (EuclideanSpace.basisFun (Fin n) ℝ)]
  simp [h0]

/-- A source equal to `Δu` is continuous and vanishes off every set containing `tsupport u`. -/
theorem source_continuous_and_zero {u f : EuclideanSpace ℝ (Fin n) → ℝ} (hu : ContDiff ℝ 2 u)
    (hΔ : ∀ x, Laplacian.laplacian u x = f x) {s : Set (EuclideanSpace ℝ (Fin n))} (hs : tsupport u ⊆ s) :
    Continuous f ∧ ∀ y, y ∉ s → f y = 0 := by
  refine ⟨?_, fun y hy => ?_⟩
  · have h := continuous_laplacian hu
    rwa [show Laplacian.laplacian u = f from funext hΔ] at h
  · rw [← hΔ y]; exact laplacian_eq_zero_of_notMem_tsupport fun h => hy (hs h)

/-- A bound and a Hölder cap of a continuous source on the OPEN ball, with the source zero off the ball, give the same bound
everywhere and the same cap GLOBALLY (closure extension, then zero extension). -/
theorem global_source_of_ball {c : EuclideanSpace ℝ (Fin n)} {R M : ℝ} (hR : 0 < R) {α H : ℝ≥0}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hfc : Continuous f) (hz : ∀ y, y ∉ ball c R → f y = 0)
    (hM : ∀ y ∈ ball c R, |f y| ≤ M) (hH : HolderOnWith H α f (ball c R)) :
    0 ≤ M ∧ (∀ y, |f y| ≤ M) ∧ HolderWith H α f := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM c (mem_ball_self hR))
  refine ⟨hM0, fun y => ?_, ?_⟩
  · by_cases hy : y ∈ ball c R
    · exact hM y hy
    · rw [hz y hy, abs_zero]; exact hM0
  · have hcl := holderOnWith_closure_of_continuous hH hfc
    rw [closure_ball c hR.ne'] at hcl
    exact holderWith_of_holderOnWith_closedBall_zero_off_ball hcl hz

/-- The original source condition (uniformly `α`-Hölder on every compact set) and continuity give a bound and a cap on any ball. -/
theorem exists_source_bounds_ball {α : ℝ≥0} {f : EuclideanSpace ℝ (Fin n) → ℝ} (hfc : Continuous f)
    (hloc : ∀ K, IsCompact K → ∃ H : ℝ≥0, HolderOnWith H α f K) (c : EuclideanSpace ℝ (Fin n)) (R : ℝ) :
    ∃ M : ℝ, ∃ H : ℝ≥0, (∀ y ∈ ball c R, |f y| ≤ M) ∧ HolderOnWith H α f (ball c R) := by
  obtain ⟨H, hH⟩ := hloc (closedBall c R) (isCompact_closedBall c R)
  obtain ⟨M, hM⟩ := (isCompact_closedBall c R).exists_bound_of_continuousOn hfc.continuousOn
  exact ⟨M, H, fun y hy => by simpa only [Real.norm_eq_abs] using hM y (ball_subset_closedBall hy),
    hH.mono ball_subset_closedBall⟩

/-- **(4.15)** For `u ∈ C²₀` with `Δu = f`, `Γ(x − ·) f` is integrable, `u(x) = ∫ Γ(x − y) f(y) dy`, and `u` equals the
Newtonian potential of `f` over ANY set `s ⊇ tsupport u`, as functions (via `compact_C2_newtonian_representation`). -/
theorem compactPoisson_eq_newtonianPotential (hn : 2 ≤ n) {u f : EuclideanSpace ℝ (Fin n) → ℝ} (hu : ContDiff ℝ 2 u)
    (hc : HasCompactSupport u) (hΔ : ∀ x, Laplacian.laplacian u x = f x) {s : Set (EuclideanSpace ℝ (Fin n))}
    (hs : tsupport u ⊆ s) :
    (∀ x, Integrable (fun y => newtonianKernel n (x - y) * f y) volume ∧ u x = ∫ y, newtonianKernel n (x - y) * f y) ∧
      u = newtonianPotential n s f := by
  have hfz := (source_continuous_and_zero hu hΔ hs).2
  have hrep : ∀ x, Integrable (fun y => newtonianKernel n (x - y) * f y) volume ∧
      u x = ∫ y, newtonianKernel n (x - y) * f y := by
    intro x
    have h := compact_C2_newtonian_representation hn hu hc x
    simp only [hΔ] at h
    exact h
  refine ⟨hrep, funext fun x => ?_⟩
  rw [(hrep x).2, newtonianPotential, setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => by rw [hfz y hy, mul_zero]]

/-- **(4.14), first estimate.** For `u ∈ C²` with `tsupport u ⊆ B_R(c)`, `Δu = f` and `|f| ≤ M` on `B_R(c)`: `‖Du‖ ≤ n(2R)M`
everywhere and `|u(x)| + 2R ‖Du(z)‖ ≤ 8n R² M` for all `x, z`. The constant depends only on `n` (no Hölder exponent). -/
theorem compactPoisson_first_estimate (hn : 2 ≤ n) {c : EuclideanSpace ℝ (Fin n)} {R : ℝ} (hR : 0 < R)
    {u f : EuclideanSpace ℝ (Fin n) → ℝ} {M : ℝ} (hu : ContDiff ℝ 2 u) (hs : tsupport u ⊆ ball c R)
    (hΔ : ∀ x, Laplacian.laplacian u x = f x) (hM : ∀ y ∈ ball c R, |f y| ≤ M) :
    (∀ x, ‖fderiv ℝ u x‖ ≤ n * (2 * R) * M) ∧ ∀ x z, |u x| + 2 * R * ‖fderiv ℝ u z‖ ≤ 8 * n * R ^ 2 * M := by
  have hc : HasCompactSupport u :=
    (isCompact_closedBall c R).of_isClosed_subset (isClosed_tsupport u) (hs.trans ball_subset_closedBall)
  have hfc := (source_continuous_and_zero hu hΔ hs).1
  have hueq := (compactPoisson_eq_newtonianPotential hn hu hc hΔ hs).2
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM c (mem_ball_self hR))
  have hG : ∀ x, ‖fderiv ℝ u x‖ ≤ n * (2 * R) * M := by
    intro x
    by_cases hx : x ∈ closedBall c R
    · rw [hueq]; exact norm_fderiv_newtonianPotential_ball_le hn hR hfc.aemeasurable hM hx
    · rw [fderiv_of_notMem_tsupport ℝ fun h => hx (ball_subset_closedBall (hs h)), norm_zero]; positivity
  have hdiff : Differentiable ℝ u := hu.differentiable (by norm_num)
  have hux : ∀ x, |u x| ≤ 2 * R * (n * (2 * R) * M) := by
    intro x
    by_cases hx : x ∈ closedBall c R
    · set e := EuclideanSpace.basisFun (Fin n) ℝ ⟨0, by omega⟩
      have he : ‖e‖ = 1 := (EuclideanSpace.basisFun (Fin n) ℝ).orthonormal.norm_eq_one _
      set p := x + (2 * R) • e
      have hpx : ‖p - x‖ = 2 * R := by
        rw [show p - x = (2 * R) • e by simp only [p, add_sub_cancel_left], norm_smul, he, Real.norm_eq_abs,
          abs_of_pos (by positivity), mul_one]
      have hp : p ∉ ball c R := by
        rw [mem_ball, not_lt, dist_eq_norm]
        rw [mem_closedBall, dist_eq_norm] at hx
        have h1 : ‖p - x‖ ≤ ‖p - c‖ + ‖x - c‖ := by
          rw [show p - x = (p - c) - (x - c) by abel]; exact norm_sub_le _ _
        linarith
      have hup : u p = 0 := image_eq_zero_of_notMem_tsupport fun h => hp (hs h)
      have hmv := Convex.norm_image_sub_le_of_norm_fderiv_le (fun y _ => hdiff y) (fun y _ => hG y) convex_univ
        (mem_univ x) (mem_univ p)
      rw [hup, zero_sub, norm_neg, Real.norm_eq_abs, hpx] at hmv
      linarith
    · rw [image_eq_zero_of_notMem_tsupport fun h => hx (ball_subset_closedBall (hs h)), abs_zero]; positivity
  refine ⟨hG, fun x z => ?_⟩
  have h2 := mul_le_mul_of_nonneg_left (hG z) (by positivity : (0:ℝ) ≤ 2 * R)
  nlinarith [hux x]

/-- **(4.14), Hessian estimate, quantitative form.** For `n ≥ 2`, `0 < α < 1` there is `C₂ > 0` (chosen before `c, R, u, f, M, H`)
such that for `u ∈ C²` with `tsupport u ⊆ B_R(c)`, `Δu = f`, `|f| ≤ M` and `HolderOnWith H α f` on the OPEN ball `B_R(c)`:
the actual Hessian has a GLOBAL Hölder cap `C₂ ((2R)^{−α} M + H)`, `‖D²u‖ ≤ C₂ (M + (2R)^α H)` everywhere, and the combined
diameter-normalised inequality `‖D²u(x)‖ + (2R)^α ‖D²u(y) − D²u(z)‖/‖y − z‖^α ≤ C₂ (M + (2R)^α H)` holds with the SAME `C₂`. -/
theorem compactPoisson_hessian_estimates (hn : 2 ≤ n) {α : ℝ≥0} (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ C2 : ℝ, 0 < C2 ∧ ∀ (c : EuclideanSpace ℝ (Fin n)) (R : ℝ), 0 < R →
      ∀ (u f : EuclideanSpace ℝ (Fin n) → ℝ) (M : ℝ) (H : ℝ≥0),
      ContDiff ℝ 2 u → tsupport u ⊆ ball c R → (∀ x, Laplacian.laplacian u x = f x) →
      (∀ y ∈ ball c R, |f y| ≤ M) → HolderOnWith H α f (ball c R) →
      HolderWith (Real.toNNReal (C2 * ((2 * R) ^ (-(α:ℝ)) * M + H))) α (fderiv ℝ (fderiv ℝ u)) ∧
      (∀ x, ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ C2 * (M + (2 * R) ^ (α:ℝ) * H)) ∧
      (∀ x z, ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) z‖ ≤
        C2 * ((2 * R) ^ (-(α:ℝ)) * M + H) * ‖x - z‖ ^ (α:ℝ)) ∧
      (∀ x y z, y ≠ z → ‖fderiv ℝ (fderiv ℝ u) x‖ +
        (2 * R) ^ (α:ℝ) * (‖fderiv ℝ (fderiv ℝ u) y - fderiv ℝ (fderiv ℝ u) z‖ / ‖y - z‖ ^ (α:ℝ)) ≤
        C2 * (M + (2 * R) ^ (α:ℝ) * H)) := by
  obtain ⟨C, hC, hS⟩ := newtonianPotential_schauder hn hα0 hα1
  refine ⟨3 * C, by positivity, fun c R hR u f M H hu hs hΔ hM hH => ?_⟩
  have hc : HasCompactSupport u :=
    (isCompact_closedBall c R).of_isClosed_subset (isClosed_tsupport u) (hs.trans ball_subset_closedBall)
  obtain ⟨hfc, hfz⟩ := source_continuous_and_zero hu hΔ hs
  obtain ⟨hM0, hMg, hHg⟩ := global_source_of_ball hR hfc hfz hM hH
  have hueq := (compactPoisson_eq_newtonianPotential hn hu hc hΔ
    (hs.trans (ball_subset_ball (by linarith) : ball c R ⊆ ball c (2 * R)))).2
  obtain ⟨-, hsup, hdiff, -, -⟩ := hS c R hR f M H (fun y _ => hMg y) (hHg.holderOnWith _)
  rw [← hueq] at hsup hdiff
  have hα' : (0:ℝ) ≤ α := α.coe_nonneg
  have hα1' : (α:ℝ) < 1 := by exact_mod_cast hα1
  have h2R : 0 < 2 * R := by positivity
  set P := (2 * R) ^ (α:ℝ) with hPdef
  have hP : 0 < P := Real.rpow_pos_of_pos h2R _
  have hPneg : (2 * R) ^ (-(α:ℝ)) = P⁻¹ := Real.rpow_neg h2R.le _
  have hRα : R ^ (α:ℝ) ≤ P := Real.rpow_le_rpow hR.le (by linarith) hα'
  have hRneg : R ^ (-(α:ℝ)) ≤ 2 * P⁻¹ := by
    have h2 : 1 ≤ 2 * (2:ℝ) ^ (-(α:ℝ)) := by
      have h := Real.one_le_rpow (by norm_num : (1:ℝ) ≤ 2) (by linarith : (0:ℝ) ≤ 1 + -(α:ℝ))
      rwa [Real.rpow_add (by norm_num : (0:ℝ) < 2), Real.rpow_one] at h
    rw [← hPneg, Real.mul_rpow (by norm_num) hR.le]
    calc R ^ (-(α:ℝ)) = 1 * R ^ (-(α:ℝ)) := (one_mul _).symm
      _ ≤ 2 * (2:ℝ) ^ (-(α:ℝ)) * R ^ (-(α:ℝ)) := mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hR.le _)
      _ = 2 * ((2:ℝ) ^ (-(α:ℝ)) * R ^ (-(α:ℝ))) := by ring
  set D2 := fderiv ℝ (fderiv ℝ u) with hD2
  have hzero : ∀ y, y ∉ ball c R → D2 y = 0 := fun y hy => fderiv_fderiv_eq_zero_of_notMem_tsupport fun h => hy (hs h)
  have hsupC : ∀ x, ‖D2 x‖ ≤ C * (M + P * H) := by
    intro x
    by_cases hx : x ∈ closedBall c R
    · exact (hsup x hx).trans (mul_le_mul_of_nonneg_left
        (add_le_add le_rfl (mul_le_mul_of_nonneg_right hRα H.coe_nonneg)) hC.le)
    · rw [hzero x fun h => hx (ball_subset_closedBall h), ContinuousLinearMap.opNorm_zero]; positivity
  have hloc2 : ∀ x ∈ closedBall c R, ∀ z ∈ closedBall c R,
      ‖D2 x - D2 z‖ ≤ 2 * C * (P⁻¹ * M + H) * ‖x - z‖ ^ (α:ℝ) := by
    intro x hx z hz
    have hcap : C * (M * R ^ (-(α:ℝ)) + H) ≤ 2 * C * (P⁻¹ * M + H) := by
      have h1 : M * R ^ (-(α:ℝ)) ≤ M * (2 * P⁻¹) := mul_le_mul_of_nonneg_left hRneg hM0
      nlinarith [mul_nonneg hC.le H.coe_nonneg]
    exact (hdiff x hx z hz).trans (mul_le_mul_of_nonneg_right hcap (Real.rpow_nonneg (norm_nonneg _) _))
  have hK2 : 0 ≤ 2 * C * (P⁻¹ * M + H) := by positivity
  have hW2 : HolderWith (Real.toNNReal (2 * C * (P⁻¹ * M + H))) α D2 :=
    holderWith_of_holderOnWith_closedBall_zero_off_ball (holderOnWith_of_dist_le hK2 fun x hx z hz => by
      rw [dist_eq_norm, dist_eq_norm]; exact hloc2 x hx z hz) hzero
  have hglob2 : ∀ x z, ‖D2 x - D2 z‖ ≤ 2 * C * (P⁻¹ * M + H) * ‖x - z‖ ^ (α:ℝ) := by
    intro x z
    have h := hW2.dist_le x z
    rwa [Real.coe_toNNReal _ hK2, dist_eq_norm, dist_eq_norm] at h
  have hglob3 : ∀ x z, ‖D2 x - D2 z‖ ≤ 3 * C * (P⁻¹ * M + H) * ‖x - z‖ ^ (α:ℝ) := fun x z =>
    (hglob2 x z).trans (mul_le_mul_of_nonneg_right (by nlinarith [mul_nonneg hC.le (by positivity : (0:ℝ) ≤ P⁻¹ * M + H)])
      (Real.rpow_nonneg (norm_nonneg _) _))
  rw [hPneg]
  refine ⟨holderOnWith_univ.mp (holderOnWith_of_dist_le (by positivity) fun x _ z _ => by
      rw [dist_eq_norm, dist_eq_norm]; exact hglob3 x z),
    fun x => (hsupC x).trans (by nlinarith [mul_nonneg hC.le (by positivity : (0:ℝ) ≤ M + P * H)]),
    hglob3, fun x y z hyz => ?_⟩
  have hyz' : 0 < ‖y - z‖ ^ (α:ℝ) := Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hyz)) _
  have hq : ‖D2 y - D2 z‖ / ‖y - z‖ ^ (α:ℝ) ≤ 2 * C * (P⁻¹ * M + H) := (div_le_iff₀ hyz').mpr (hglob2 y z)
  calc ‖D2 x‖ + P * (‖D2 y - D2 z‖ / ‖y - z‖ ^ (α:ℝ)) ≤ C * (M + P * H) + P * (2 * C * (P⁻¹ * M + H)) :=
        add_le_add (hsupC x) (mul_le_mul_of_nonneg_left hq hP.le)
    _ = 3 * C * (M + P * H) := by
        rw [show P * (2 * C * (P⁻¹ * M + H)) = 2 * C * (P * P⁻¹ * M + P * H) by ring, mul_inv_cancel₀ hP.ne', one_mul]
        ring

/-- **GT2001 Theorem 4.5, quantitative interface.** `C₁ = 8n` (independent of `α`) is chosen first; then for every `0 < α < 1`
a `C₂(n,α)`; then for all `c, R > 0, u, f, M, H` with `u ∈ C²`, `tsupport u ⊆ B_R(c)`, `Δu = f`, `|f| ≤ M` and
`HolderOnWith H α f` on `B_R(c)`: the representation (4.15), the derived global source bound/cap, the global Hessian Hölder cap and
both estimates (4.14) in the diameter normalisation `2R`. -/
theorem compactPoisson_estimates (hn : 2 ≤ n) :
    ∃ C1 : ℝ, 0 < C1 ∧ ∀ α : ℝ≥0, 0 < α → α < 1 → ∃ C2 : ℝ, 0 < C2 ∧
      ∀ (c : EuclideanSpace ℝ (Fin n)) (R : ℝ), 0 < R → ∀ (u f : EuclideanSpace ℝ (Fin n) → ℝ) (M : ℝ) (H : ℝ≥0),
      ContDiff ℝ 2 u → tsupport u ⊆ ball c R → (∀ x, Laplacian.laplacian u x = f x) →
      (∀ y ∈ ball c R, |f y| ≤ M) → HolderOnWith H α f (ball c R) →
      (∀ x, Integrable (fun y => newtonianKernel n (x - y) * f y) volume ∧
        u x = ∫ y, newtonianKernel n (x - y) * f y) ∧
      (∀ y, |f y| ≤ M) ∧ HolderWith H α f ∧
      HolderWith (Real.toNNReal (C2 * ((2 * R) ^ (-(α:ℝ)) * M + H))) α (fderiv ℝ (fderiv ℝ u)) ∧
      (∀ x, ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ C2 * (M + (2 * R) ^ (α:ℝ) * H)) ∧
      (∀ x z, ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) z‖ ≤
        C2 * ((2 * R) ^ (-(α:ℝ)) * M + H) * ‖x - z‖ ^ (α:ℝ)) ∧
      (∀ x y z, y ≠ z → ‖fderiv ℝ (fderiv ℝ u) x‖ +
        (2 * R) ^ (α:ℝ) * (‖fderiv ℝ (fderiv ℝ u) y - fderiv ℝ (fderiv ℝ u) z‖ / ‖y - z‖ ^ (α:ℝ)) ≤
        C2 * (M + (2 * R) ^ (α:ℝ) * H)) ∧
      (∀ x z, |u x| + 2 * R * ‖fderiv ℝ u z‖ ≤ C1 * R ^ 2 * M) := by
  refine ⟨8 * n, by have : (2:ℝ) ≤ n := by exact_mod_cast hn
                    positivity, fun α hα0 hα1 => ?_⟩
  obtain ⟨C2, hC2, hE⟩ := compactPoisson_hessian_estimates hn hα0 hα1
  refine ⟨C2, hC2, fun c R hR u f M H hu hs hΔ hM hH => ?_⟩
  have hc : HasCompactSupport u :=
    (isCompact_closedBall c R).of_isClosed_subset (isClosed_tsupport u) (hs.trans ball_subset_closedBall)
  obtain ⟨hfc, hfz⟩ := source_continuous_and_zero hu hΔ hs
  obtain ⟨-, hMg, hHg⟩ := global_source_of_ball hR hfc hfz hM hH
  obtain ⟨h1, h2, h3, h4⟩ := hE c R hR u f M H hu hs hΔ hM hH
  exact ⟨(compactPoisson_eq_newtonianPotential hn hu hc hΔ hs).1, hMg, hHg, h1, h2, h3, h4,
    (compactPoisson_first_estimate hn hR hu hs hΔ hM).2⟩

/-- **GT2001 Theorem 4.5 in the original source class.** `C₁ = C(n) > 0` is chosen first (independent of `α`); for every
`0 < α < 1` a `C₂ = C(n,α) > 0` is chosen; then for every `u ∈ C²` with compact support and every `f` uniformly `α`-Hölder on each
compact set (the local class `C^α(ℝⁿ)`, pp. 51–53) with `Δu = f`: `f` has compact support inside `supp u`; the representation (4.15);
`u ∈ C^{2,α}(ℝⁿ)` (a global Hölder cap and a global bound for the actual Hessian); and for EVERY ball `B_R(c) ⊇ supp u` finite source
bounds exist (derived) and, for any bound `M` and cap `H` of `f` on `B_R(c)`, both estimates (4.14) hold with `d = 2R`. No global or
uniform Hölder premise and no regularity of `u` beyond `C²` is assumed. -/
theorem compactPoisson_GT4_5 (hn : 2 ≤ n) :
    ∃ C1 : ℝ, 0 < C1 ∧ ∀ α : ℝ≥0, 0 < α → α < 1 → ∃ C2 : ℝ, 0 < C2 ∧
      ∀ u f : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ 2 u → HasCompactSupport u →
      (∀ K, IsCompact K → ∃ H : ℝ≥0, HolderOnWith H α f K) → (∀ x, Laplacian.laplacian u x = f x) →
      (HasCompactSupport f ∧ tsupport f ⊆ tsupport u) ∧
      (∀ x, Integrable (fun y => newtonianKernel n (x - y) * f y) volume ∧
        u x = ∫ y, newtonianKernel n (x - y) * f y) ∧
      (∃ K : ℝ≥0, HolderWith K α (fderiv ℝ (fderiv ℝ u))) ∧ (∃ B : ℝ, ∀ x, ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ B) ∧
      ∀ (c : EuclideanSpace ℝ (Fin n)) (R : ℝ), 0 < R → tsupport u ⊆ ball c R →
        (∃ M : ℝ, ∃ H : ℝ≥0, (∀ y ∈ ball c R, |f y| ≤ M) ∧ HolderOnWith H α f (ball c R)) ∧
        ∀ (M : ℝ) (H : ℝ≥0), (∀ y ∈ ball c R, |f y| ≤ M) → HolderOnWith H α f (ball c R) →
          HolderWith (Real.toNNReal (C2 * ((2 * R) ^ (-(α:ℝ)) * M + H))) α (fderiv ℝ (fderiv ℝ u)) ∧
          (∀ x, ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ C2 * (M + (2 * R) ^ (α:ℝ) * H)) ∧
          (∀ x z, ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) z‖ ≤
            C2 * ((2 * R) ^ (-(α:ℝ)) * M + H) * ‖x - z‖ ^ (α:ℝ)) ∧
          (∀ x y z, y ≠ z → ‖fderiv ℝ (fderiv ℝ u) x‖ +
            (2 * R) ^ (α:ℝ) * (‖fderiv ℝ (fderiv ℝ u) y - fderiv ℝ (fderiv ℝ u) z‖ / ‖y - z‖ ^ (α:ℝ)) ≤
            C2 * (M + (2 * R) ^ (α:ℝ) * H)) ∧
          (∀ x z, |u x| + 2 * R * ‖fderiv ℝ u z‖ ≤ C1 * R ^ 2 * M) := by
  obtain ⟨C1, hC1, hQ⟩ := compactPoisson_estimates hn
  refine ⟨C1, hC1, fun α hα0 hα1 => ?_⟩
  obtain ⟨C2, hC2, hE⟩ := hQ α hα0 hα1
  refine ⟨C2, hC2, fun u f hu hc hloc hΔ => ?_⟩
  obtain ⟨hfc, -⟩ := source_continuous_and_zero hu hΔ (subset_refl (tsupport u))
  have hsub : tsupport f ⊆ tsupport u := closure_minimal (fun y hy => by
    by_contra h
    exact hy (by rw [← hΔ y]; exact laplacian_eq_zero_of_notMem_tsupport h)) (isClosed_tsupport u)
  obtain ⟨r, hr⟩ := hc.isCompact.isBounded.subset_ball (0 : EuclideanSpace ℝ (Fin n))
  have hR0 : 0 < max r 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hs0 : tsupport u ⊆ ball 0 (max r 1) := hr.trans (ball_subset_ball (le_max_left _ _))
  obtain ⟨M0, H0, hM0, hH0⟩ := exists_source_bounds_ball hfc hloc 0 (max r 1)
  obtain ⟨-, -, -, hW, hB, -⟩ := hE 0 (max r 1) hR0 u f M0 H0 hu hs0 hΔ hM0 hH0
  refine ⟨⟨hc.isCompact.of_isClosed_subset (isClosed_tsupport f) hsub, hsub⟩,
    (compactPoisson_eq_newtonianPotential hn hu hc hΔ (subset_refl _)).1, ⟨_, hW⟩, ⟨_, hB⟩,
    fun c R hR hs => ⟨exists_source_bounds_ball hfc hloc c R, fun M H hM hH => ?_⟩⟩
  obtain ⟨-, -, -, h1, h2, h3, h4, h5⟩ := hE c R hR u f M H hu hs hΔ hM hH
  exact ⟨h1, h2, h3, h4, h5⟩

end CompactPoisson

end FunctionalInequalities.Analysis
