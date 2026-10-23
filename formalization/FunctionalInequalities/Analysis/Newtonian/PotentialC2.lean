import FunctionalInequalities.Analysis.Newtonian.GradientApprox
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Topology.MetricSpace.Holder

/-!
# The Newtonian potential is C² and solves Poisson's equation (GT Lemma 4.2)

Lemma 4.2 of Gilbarg–Trudinger, *Elliptic Partial Differential Equations of Second Order*, Classics 2001
(ISBN 3-540-41160-7), pp. 55–56. For `n ≥ 2` (including `n = 2`), a bounded open `Ω` and `f` bounded and
locally `α`-Hölder in `Ω` (`0 < α ≤ 1`), `newtonianPotential_contDiffOn_two` proves that the Newtonian
potential `w` is `C²` in `Ω`, that `Δw = f` in `Ω` for Mathlib's actual Laplacian, and that its Hessian has
the compact-test representation
`D_jD_i w(x) = ∫ D_jD_iΓ(x - y)(F(y) - f(x)θ(y)) dy + f(x) ∫ D_iΓ(x - y) D_jθ(y) dy`, `F = 1_Ω f`,
for every `θ ∈ C¹_c` equal to `1` on an open set containing `Ω` (such `θ` exist,
`exists_newtonian_test`). This test form replaces the boundary integral over `∂Ω₀` in GT's (4.9); the
boundary form is derived in `Analysis/Newtonian/BoundaryFormula.lean`.

The proof follows the book: the cut-off first derivatives `v_{ε,i}`, locally uniform convergence of
`Dv_{ε,i}` along `ε_k = 1/(k+1)` (`newtonianPotential_hessian_local`), and the unit radial mass of the
trace density for `Δw = f`. `newtonianPotential_contDiffOn_two_of_test` is the same statement for one
fixed admissible test with real-valued Hölder data.
-/

noncomputable section

open Set Metric MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal

namespace FunctionalInequalities.Analysis

/-- The compact-test Hessian entry `u_{ij}(x) = ∫ D_jD_iΓ(x−y)(F(y) − f(x)θ(y))dy + f(x)∫ D_iΓ(x−y)D_jθ(y)dy`. -/
def newtonianHessianTestRep (n : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin n))) (f θ : EuclideanSpace ℝ (Fin n) → ℝ)
    (i j : Fin n) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (∫ y, bilinearIteratedFDerivTwo ℝ (newtonianKernel n) (x - y)
      (EuclideanSpace.basisFun (Fin n) ℝ j) (EuclideanSpace.basisFun (Fin n) ℝ i) * (Ω.indicator f y - f x * θ y)) +
    f x * ∫ y, fderiv ℝ (newtonianKernel n) (x - y) (EuclideanSpace.basisFun (Fin n) ℝ i) *
      fderiv ℝ θ y (EuclideanSpace.basisFun (Fin n) ℝ j)

/-- The `i`-th row `v ↦ Σ_j u_{ij}(x) v_j` as a continuous linear functional. -/
def newtonianHessianTestRow (n : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin n))) (f θ : EuclideanSpace ℝ (Fin n) → ℝ)
    (i : Fin n) (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
  ∑ j : Fin n, newtonianHessianTestRep n Ω f θ i j x • EuclideanSpace.proj j

theorem newtonianHessianTestRow_apply {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n))) (f θ : EuclideanSpace ℝ (Fin n) → ℝ)
    (i l : Fin n) (x : EuclideanSpace ℝ (Fin n)) :
    newtonianHessianTestRow n Ω f θ i x (EuclideanSpace.basisFun (Fin n) ℝ l) = newtonianHessianTestRep n Ω f θ i l x := by
  simp [newtonianHessianTestRow, EuclideanSpace.basisFun_apply]

/-- Every functional on `ℝⁿ` is `Σ_i L(e_i) e_i^*`. -/
theorem eq_sum_apply_basisFun_smul_proj {n : ℕ} (L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :
    L = ∑ i : Fin n, L (EuclideanSpace.basisFun (Fin n) ℝ i) • EuclideanSpace.proj i := by
  ext v
  conv_lhs => rw [← (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr v]
  simp [map_sum, map_smul, EuclideanSpace.basisFun_repr, mul_comm]

section Core

variable {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))} {f θ : EuclideanSpace ℝ (Fin n) → ℝ} {M α : ℝ}
  {U : Set (EuclideanSpace ℝ (Fin n))}

/-- One-point error: if `B(x,2ε) ⊆ Ω` and `f` is `α`-Hölder at `x` on that ball, then
`|D_j v_{ε,i}(x) − u_{ij}(x)| ≤ (n/α + 2B) H (2ε)^α`, and the Hessian integrand of `u_{ij}` is integrable. -/
theorem abs_newtonianGradientApprox_deriv_sub_rep_le (hn : 2 ≤ n) (hΩo : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hfi : IntegrableOn f Ω volume) (hθ : ContDiff ℝ 1 θ) (hθc : HasCompactSupport θ) (hU : IsOpen U) (hΩU : Ω ⊆ U)
    (hθ1 : ∀ y ∈ U, θ y = 1) (hα : 0 < α) (hαn : α < n) {eps H : ℝ} (heps : 0 < eps) (hH : 0 ≤ H)
    {x : EuclideanSpace ℝ (Fin n)} (hx : ball x (2 * eps) ⊆ Ω)
    (hHx : ∀ y ∈ ball x (2 * eps), |f y - f x| ≤ H * ‖y - x‖ ^ α) (i j : Fin n) :
    Integrable (fun y => bilinearIteratedFDerivTwo ℝ (newtonianKernel n) (x - y)
      (EuclideanSpace.basisFun (Fin n) ℝ j) (EuclideanSpace.basisFun (Fin n) ℝ i) * (Ω.indicator f y - f x * θ y)) volume ∧
    Integrable (fun y => fderiv ℝ (newtonianKernel n) (x - y) (EuclideanSpace.basisFun (Fin n) ℝ i) *
      fderiv ℝ θ y (EuclideanSpace.basisFun (Fin n) ℝ j)) volume ∧
    |(∫ y in Ω, fderiv ℝ (newtonianTruncatedGradientComponent n eps i) (x - y) (EuclideanSpace.basisFun (Fin n) ℝ j) * f y) -
        newtonianHessianTestRep n Ω f θ i j x| ≤ ((n:ℝ) / α + 2 * newtonianCutoffCap) * H * (2 * eps) ^ α := by
  have hΩm : MeasurableSet Ω := hΩo.measurableSet
  have hθi : Integrable θ volume := hθ.continuous.integrable_of_hasCompactSupport hθc
  have hφi : Integrable (fun y => Ω.indicator f y - f x * θ y) volume :=
    ((integrable_indicator_iff hΩm).mpr hfi).sub (hθi.const_mul (f x))
  have hφH : ∀ y ∈ ball x (2 * eps), |Ω.indicator f y - f x * θ y| ≤ H * ‖y - x‖ ^ α := by
    intro y hy
    rw [Set.indicator_of_mem (hx hy), hθ1 y (hΩU (hx hy)), mul_one]
    exact hHx y hy
  obtain ⟨hk0, -, hnear⟩ := newtonianTruncatedGradient_near_error hn heps hα hαn hH x hφi hφH i j
  obtain ⟨-, hT, hrep⟩ := newtonianGradientApprox_deriv_eq_test hn hΩo hΩb hfi heps hθ hθc hU hΩU hθ1 hx i j
  refine ⟨hk0, hT, ?_⟩
  rw [hrep, newtonianHessianTestRep]
  convert hnear using 2
  ring

/-- The trace of the approximants is an approximate identity at `x`: if `B(x,2ε) ⊆ Ω` and `f` is `α`-Hölder at `x`
there, `|Σ_i D_i v_{ε,i}(x) − f(x)| ≤ H (2ε)^α`. Uses the imported radial mass one and the trace positivity/support. -/
theorem abs_sum_newtonianGradientApprox_deriv_sub_le (hn : 2 ≤ n) (hΩo : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hfi : IntegrableOn f Ω volume) {eps H : ℝ} (heps : 0 < eps) (hH : 0 ≤ H) (hα : 0 < α)
    {x : EuclideanSpace ℝ (Fin n)} (hx : ball x (2 * eps) ⊆ Ω)
    (hHx : ∀ y ∈ ball x (2 * eps), |f y - f x| ≤ H * ‖y - x‖ ^ α) :
    |(∑ i : Fin n, ∫ y in Ω, fderiv ℝ (newtonianTruncatedGradientComponent n eps i) (x - y)
        (EuclideanSpace.basisFun (Fin n) ℝ i) * f y) - f x| ≤ H * (2 * eps) ^ α := by
  set b := EuclideanSpace.basisFun (Fin n) ℝ
  set k : EuclideanSpace ℝ (Fin n) → ℝ := fun z =>
    ∑ i : Fin n, fderiv ℝ (newtonianTruncatedGradientComponent n eps i) z (b i)
  set R := 2 * eps
  have hR : 0 < R := by positivity
  have hΩm : MeasurableSet Ω := hΩo.measurableSet
  have hsub : Continuous (fun y : EuclideanSpace ℝ (Fin n) => x - y) := continuous_const.sub continuous_id
  have hkc (i : Fin n) : Continuous (fun y => fderiv ℝ (newtonianTruncatedGradientComponent n eps i) (x - y) (b i)) :=
    (((contDiff_newtonianTruncatedGradientComponent hn heps i).continuous_fderiv (by simp)).comp hsub).clm_apply
      continuous_const
  have hkx : Continuous (fun y => k (x - y)) := continuous_finsetSum _ fun i _ => hkc i
  obtain ⟨hki, hk1⟩ := integral_sum_fderiv_newtonianTruncatedGradientComponent hn heps
  have hk0 : ∀ y ∉ ball x R, k (x - y) = 0 := by
    intro y hy
    have hy' : 2 * eps ≤ ‖x - y‖ := by simpa only [R, mem_ball, dist_eq_norm, norm_sub_rev, not_lt] using hy
    exact sum_fderiv_newtonianTruncatedGradientComponent_eq_zero hn heps hy'
  have hkpos : ∀ y, 0 ≤ k (x - y) := fun y => sum_fderiv_newtonianTruncatedGradientComponent_nonneg hn heps (x - y)
  -- each trace component is integrable on `Ω`, so the sum of integrals is the integral of `k(x − ·) f`
  have hcomp (i : Fin n) : Integrable
      (fun y => fderiv ℝ (newtonianTruncatedGradientComponent n eps i) (x - y) (b i) * f y) (volume.restrict Ω) := by
    obtain ⟨Ci, hCi⟩ := hΩb.isCompact_closure.exists_bound_of_continuousOn (hkc i).continuousOn
    refine hfi.bdd_mul (c := Ci) (hkc i).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem hΩm] with y hy using hCi y (subset_closure hy)
  have hsum : (∑ i : Fin n, ∫ y in Ω, fderiv ℝ (newtonianTruncatedGradientComponent n eps i) (x - y) (b i) * f y) =
      ∫ y in Ω, k (x - y) * f y := by
    rw [← integral_finsetSum _ fun i _ => hcomp i]
    congr 1; funext y; simp only [k, Finset.sum_mul]
  -- localize to `B(x,2ε)`
  obtain ⟨C, hC⟩ := (isCompact_closedBall x R).exists_bound_of_continuousOn hkx.continuousOn
  have hkf : IntegrableOn (fun y => k (x - y) * f y) (ball x R) volume := by
    refine (hfi.mono_set hx).bdd_mul (c := C) hkx.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_ball] with y hy using hC y (ball_subset_closedBall hy)
  have hkb : IntegrableOn (fun y => k (x - y)) (ball x R) volume := (hki.comp_sub_left x).integrableOn
  have hloc1 : (∫ y in Ω, k (x - y) * f y) = ∫ y in ball x R, k (x - y) * f y := by
    rw [← integral_indicator hΩm, ← integral_indicator measurableSet_ball]
    congr 1; funext y
    by_cases hy : y ∈ ball x R
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem (hx hy)]
    · rw [Set.indicator_of_notMem hy]
      by_cases hyΩ : y ∈ Ω
      · rw [Set.indicator_of_mem hyΩ, hk0 y hy, zero_mul]
      · rw [Set.indicator_of_notMem hyΩ]
  have hloc2 : (∫ y in ball x R, k (x - y)) = 1 := by
    rw [← integral_indicator measurableSet_ball]
    have h : (ball x R).indicator (fun y => k (x - y)) = fun y => k (x - y) := by
      funext y; by_cases hy : y ∈ ball x R
      · rw [Set.indicator_of_mem hy]
      · rw [Set.indicator_of_notMem hy, hk0 y hy]
    rw [h, integral_sub_left_eq_self k volume x, hk1]
  have hdiff : (∫ y in ball x R, k (x - y) * f y) - f x = ∫ y in ball x R, k (x - y) * (f y - f x) := by
    have h : (∫ y in ball x R, k (x - y) * (f y - f x)) = (∫ y in ball x R, k (x - y) * f y) - f x := by
      rw [show (fun y => k (x - y) * (f y - f x)) = fun y => k (x - y) * f y - k (x - y) * f x by funext y; ring,
        integral_sub hkf (hkb.mul_const _), integral_mul_const, hloc2, one_mul]
    exact h.symm
  rw [hsum, hloc1, hdiff, ← Real.norm_eq_abs]
  calc ‖∫ y in ball x R, k (x - y) * (f y - f x)‖ ≤ ∫ y in ball x R, k (x - y) * (H * R ^ α) := by
        refine norm_integral_le_of_norm_le (hkb.mul_const _) ?_
        filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
        have hyx : ‖y - x‖ < R := by rwa [mem_ball, dist_eq_norm] at hy
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hkpos y)]
        exact mul_le_mul_of_nonneg_left ((hHx y hy).trans
          (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) hyx.le hα.le) hH)) (hkpos y)
    _ = H * R ^ α := by rw [integral_mul_const, hloc2, one_mul]

end Core

section Main

variable {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))} {f θ : EuclideanSpace ℝ (Fin n) → ℝ} {M α : ℝ}
  {U : Set (EuclideanSpace ℝ (Fin n))}

theorem tendsto_two_mul_inv_succ_rpow (hα : 0 < α) :
    Tendsto (fun k : ℕ => (2 * (1 / ((k:ℝ) + 1))) ^ α) atTop (𝓝 0) := by
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul 2).rpow_const (p := α) (Or.inr hα.le)
  simpa [Real.zero_rpow hα.ne'] using h

theorem eventually_two_mul_inv_succ_le {r : ℝ} (hr : 0 < r) :
    ∀ᶠ k : ℕ in atTop, 2 * (1 / ((k:ℝ) + 1)) ≤ r := by
  have h := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (2:ℝ)
  rw [mul_zero] at h
  exact h.eventually (ge_mem_nhds hr)

/-- Local step at `x₀ ∈ Ω` (GT2001 p. 56): along `ε_k = 1/(k+1)`, `D v_{ε_k,i}` converges uniformly on `B(x₀,r/2)` to the
explicit test row; hence `D_i w` has derivative `row_i(x₀)` at `x₀`, the row is continuous at `x₀`, and every component of
`D v_{ε_k,i}(x₀)` converges to `u_{ij}(x₀)`. -/
theorem newtonianPotential_hessian_local (hn : 2 ≤ n) (hΩo : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hfi : IntegrableOn f Ω volume) (hfb : ∀ y ∈ Ω, |f y| ≤ M) (hθ : ContDiff ℝ 1 θ) (hθc : HasCompactSupport θ)
    (hU : IsOpen U) (hΩU : Ω ⊆ U) (hθ1 : ∀ y ∈ U, θ y = 1) (hα : 0 < α) (hαn : α < n)
    (hloc : ∀ x ∈ Ω, ∃ r > 0, ∃ H, 0 ≤ H ∧ ball x r ⊆ Ω ∧
      ∀ y ∈ ball x r, ∀ z ∈ ball x r, |f y - f z| ≤ H * ‖y - z‖ ^ α)
    {x0 : EuclideanSpace ℝ (Fin n)} (hx0 : x0 ∈ Ω) (i : Fin n) :
    HasFDerivAt (fun x => fderiv ℝ (newtonianPotential n Ω f) x (EuclideanSpace.basisFun (Fin n) ℝ i))
      (newtonianHessianTestRow n Ω f θ i x0) x0 ∧
    ContinuousAt (newtonianHessianTestRow n Ω f θ i) x0 ∧
    ∀ j, Tendsto (fun k : ℕ => ∫ y in Ω, fderiv ℝ (newtonianTruncatedGradientComponent n (1 / ((k:ℝ) + 1)) i) (x0 - y)
      (EuclideanSpace.basisFun (Fin n) ℝ j) * f y) atTop (𝓝 (newtonianHessianTestRep n Ω f θ i j x0)) := by
  set b := EuclideanSpace.basisFun (Fin n) ℝ
  have hΩm : MeasurableSet Ω := hΩo.measurableSet
  have hf : AEMeasurable f (volume.restrict Ω) := hfi.aemeasurable
  have hM : ∀ᵐ y ∂(volume.restrict Ω), |f y| ≤ M := ae_restrict_of_forall_mem hΩm hfb
  obtain ⟨-, -, -, hw⟩ := newtonianPotential_contDiff_one hn hΩo hΩb hfi ⟨M, hfb⟩
  obtain ⟨r, hr, H, hH, hball, hHol⟩ := hloc x0 hx0
  set ε : ℕ → ℝ := fun k => 1 / ((k:ℝ) + 1)
  have hε : ∀ k, 0 < ε k := fun k => by positivity
  set s := ball x0 (r / 2)
  have hcen : x0 ∈ s := mem_ball_self (half_pos hr)
  set F' : ℕ → EuclideanSpace ℝ (Fin n) → (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) := fun k x =>
    ∫ y in Ω, f y • fderiv ℝ (newtonianTruncatedGradientComponent n (ε k) i) (x - y)
  have happ := fun k => hasFDerivAt_newtonianGradientApprox hn hΩm hΩb hf hM (hε k) i
  have hcompk : ∀ k x v, F' k x v = ∫ y in Ω, fderiv ℝ (newtonianTruncatedGradientComponent n (ε k) i) (x - y) v * f y :=
    fun k => (happ k).2.2
  set C := (n:ℝ) / α + 2 * newtonianCutoffCap
  have hsub : ∀ k, 2 * ε k ≤ r / 2 → ∀ x ∈ s, ball x (2 * ε k) ⊆ ball x0 r := by
    intro k hk x hx y hy
    rw [mem_ball] at hx hy ⊢
    calc dist y x0 ≤ dist y x + dist x x0 := dist_triangle _ _ _
      _ < 2 * ε k + r / 2 := add_lt_add hy hx
      _ ≤ r := by linarith
  have hxr : ∀ x ∈ s, x ∈ ball x0 r := fun x hx => ball_subset_ball (half_le_self hr.le) hx
  have hbound : ∀ k, 2 * ε k ≤ r / 2 → ∀ x ∈ s,
      ‖newtonianHessianTestRow n Ω f θ i x - F' k x‖ ≤ n * (C * H * (2 * ε k) ^ α) := by
    intro k hk x hx
    have hsk := hsub k hk x hx
    have he (l : Fin n) : |(newtonianHessianTestRow n Ω f θ i x - F' k x) (b l)| ≤ C * H * (2 * ε k) ^ α := by
      rw [sub_apply, newtonianHessianTestRow_apply, hcompk, abs_sub_comm]
      exact (abs_newtonianGradientApprox_deriv_sub_rep_le hn hΩo hΩb hfi hθ hθc hU hΩU hθ1 hα hαn (hε k) hH
        (hsk.trans hball) (fun y hy => hHol y (hsk hy) x (hxr x hx)) i l).2.2
    refine (opNorm_le_sum_abs_basisFun _).trans ?_
    calc (∑ l : Fin n, |(newtonianHessianTestRow n Ω f θ i x - F' k x) (b l)|) ≤
        ∑ _l : Fin n, C * H * (2 * ε k) ^ α := Finset.sum_le_sum fun l _ => he l
      _ = n * (C * H * (2 * ε k) ^ α) := by simp
  have hunif : TendstoUniformlyOn F' (newtonianHessianTestRow n Ω f θ i) atTop s := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro δ hδ
    have ht : Tendsto (fun k : ℕ => (n:ℝ) * (C * H * (2 * ε k) ^ α)) atTop (𝓝 0) := by
      have h := ((tendsto_two_mul_inv_succ_rpow hα).const_mul (C * H)).const_mul (n:ℝ)
      simpa only [mul_zero] using h
    filter_upwards [ht.eventually (gt_mem_nhds hδ), eventually_two_mul_inv_succ_le (half_pos hr)] with k hk1 hk2 x hx
    rw [dist_eq_norm]
    exact (hbound k hk2 x hx).trans_lt hk1
  have hfg : ∀ x ∈ s, Tendsto (fun k => newtonianGradientApprox n Ω f (ε k) i x) atTop
      (𝓝 (fderiv ℝ (newtonianPotential n Ω f) x (b i))) := by
    intro x _
    rw [hw x i]
    refine tendsto_iff_norm_sub_tendsto_zero.mpr
      (squeeze_zero (g := fun k => max M 0 * (2 * ε k)) (fun _ => norm_nonneg _) (fun k => ?_) ?_)
    · rw [Real.norm_eq_abs]; exact abs_newtonianGradientApprox_sub_le hn hΩb hf hM (hε k) i x
    · have h := (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (2:ℝ)).const_mul (max M 0)
      simpa only [mul_zero] using h
  refine ⟨hasFDerivAt_of_tendstoUniformlyOn isOpen_ball hunif (fun k x _ => (happ k).1 x) hfg hcen,
    (hunif.continuousOn (Frequently.of_forall fun k => (happ k).2.1.continuousOn)).continuousAt
      (isOpen_ball.mem_nhds hcen), fun j => ?_⟩
  have h := ((ContinuousLinearMap.apply ℝ ℝ (b j)).continuous.tendsto _).comp (hunif.tendsto_at hcen)
  rw [← newtonianHessianTestRow_apply]
  simp only [Function.comp_def, ContinuousLinearMap.apply_apply, hcompk] at h
  exact h

/-- GT2001 Lemma 4.2 in real-Hölder form, for a fixed admissible test `θ`: `w ∈ C²(Ω)`, `Δw = f` in `Ω`, and the
compact-test Hessian representation with both integrands integrable. -/
theorem newtonianPotential_contDiffOn_two_of_test (hn : 2 ≤ n) (hΩo : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hfi : IntegrableOn f Ω volume) (hfb : ∀ y ∈ Ω, |f y| ≤ M) (hθ : ContDiff ℝ 1 θ) (hθc : HasCompactSupport θ)
    (hU : IsOpen U) (hΩU : Ω ⊆ U) (hθ1 : ∀ y ∈ U, θ y = 1) (hα : 0 < α) (hαn : α < n)
    (hloc : ∀ x ∈ Ω, ∃ r > 0, ∃ H, 0 ≤ H ∧ ball x r ⊆ Ω ∧
      ∀ y ∈ ball x r, ∀ z ∈ ball x r, |f y - f z| ≤ H * ‖y - z‖ ^ α) :
    ContDiffOn ℝ 2 (newtonianPotential n Ω f) Ω ∧
    (∀ x ∈ Ω, Laplacian.laplacian (newtonianPotential n Ω f) x = f x) ∧
    ∀ x ∈ Ω, ∀ i j : Fin n,
      Integrable (fun y => bilinearIteratedFDerivTwo ℝ (newtonianKernel n) (x - y)
        (EuclideanSpace.basisFun (Fin n) ℝ j) (EuclideanSpace.basisFun (Fin n) ℝ i) * (Ω.indicator f y - f x * θ y)) volume ∧
      Integrable (fun y => fderiv ℝ (newtonianKernel n) (x - y) (EuclideanSpace.basisFun (Fin n) ℝ i) *
        fderiv ℝ θ y (EuclideanSpace.basisFun (Fin n) ℝ j)) volume ∧
      iteratedFDeriv ℝ 2 (newtonianPotential n Ω f) x
          ![EuclideanSpace.basisFun (Fin n) ℝ j, EuclideanSpace.basisFun (Fin n) ℝ i] =
        newtonianHessianTestRep n Ω f θ i j x := by
  set b := EuclideanSpace.basisFun (Fin n) ℝ
  set w := newtonianPotential n Ω f
  have hl := fun {x} (hx : x ∈ Ω) (i : Fin n) =>
    newtonianPotential_hessian_local hn hΩo hΩb hfi hfb hθ hθc hU hΩU hθ1 hα hαn hloc hx i
  obtain ⟨-, -, hw1, -⟩ := newtonianPotential_contDiff_one hn hΩo hΩb hfi ⟨M, hfb⟩
  have hDc (i : Fin n) : ContDiffOn ℝ 1 (fun x => fderiv ℝ w x (b i)) Ω := by
    rw [show (1 : WithTop ℕ∞) = 0 + 1 from (zero_add 1).symm, contDiffOn_succ_iff_fderiv_of_isOpen hΩo]
    refine ⟨fun x hx => (hl hx i).1.differentiableAt.differentiableWithinAt, fun h => by simp at h, ?_⟩
    rw [contDiffOn_zero]
    exact ContinuousOn.congr (fun x hx => (hl hx i).2.1.continuousWithinAt) fun x hx => (hl hx i).1.fderiv
  have hDw : ContDiffOn ℝ 1 (fderiv ℝ w) Ω := by
    have heq : fderiv ℝ w = fun x => ∑ i : Fin n, fderiv ℝ w x (b i) • EuclideanSpace.proj i :=
      funext fun x => eq_sum_apply_basisFun_smul_proj _
    rw [heq]
    exact ContDiffOn.sum fun i _ => (hDc i).smul contDiffOn_const
  have hC2 : ContDiffOn ℝ 2 w Ω := by
    rw [show (2 : WithTop ℕ∞) = 1 + 1 by norm_num, contDiffOn_succ_iff_fderiv_of_isOpen hΩo]
    exact ⟨(hw1.differentiable one_ne_zero).differentiableOn, fun h => by simp at h, hDw⟩
  have hsecond : ∀ x ∈ Ω, ∀ i j : Fin n, iteratedFDeriv ℝ 2 w x ![b j, b i] = newtonianHessianTestRep n Ω f θ i j x := by
    intro x hx i j
    have hd : DifferentiableAt ℝ (fderiv ℝ w) x := (hDw.contDiffAt (hΩo.mem_nhds hx)).differentiableAt one_ne_zero
    have h1 : fderiv ℝ (fun z => fderiv ℝ w z (b i)) x (b j) = bilinearIteratedFDerivTwo ℝ w x (b j) (b i) := by
      rw [fderiv_clm_apply hd (differentiableAt_const (b i))]
      simp [bilinearIteratedFDerivTwo]
    rw [← bilinearIteratedFDerivTwo_eq_iteratedFDeriv, ← h1, (hl hx i).1.fderiv, newtonianHessianTestRow_apply]
  refine ⟨hC2, fun x hx => ?_, fun x hx i j => ?_⟩
  · -- Δw(x) = Σ_i u_ii(x), and Σ_i D_i v_{ε,i}(x) → f(x) (approximate identity)
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis w b]
    simp only [fun i => hsecond x hx i i]
    obtain ⟨r, hr, H, hH, hball, hHol⟩ := hloc x hx
    have hT1 : Tendsto (fun k : ℕ => ∑ i : Fin n, ∫ y in Ω,
        fderiv ℝ (newtonianTruncatedGradientComponent n (1 / ((k:ℝ) + 1)) i) (x - y) (b i) * f y) atTop
        (𝓝 (∑ i : Fin n, newtonianHessianTestRep n Ω f θ i i x)) :=
      tendsto_finsetSum _ fun i _ => (hl hx i).2.2 i
    have hT2 : Tendsto (fun k : ℕ => ∑ i : Fin n, ∫ y in Ω,
        fderiv ℝ (newtonianTruncatedGradientComponent n (1 / ((k:ℝ) + 1)) i) (x - y) (b i) * f y) atTop (𝓝 (f x)) := by
      refine tendsto_iff_norm_sub_tendsto_zero.mpr (squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
        (by simpa only [mul_zero] using (tendsto_two_mul_inv_succ_rpow hα).const_mul H))
      filter_upwards [eventually_two_mul_inv_succ_le hr] with k hk
      have hsub : ball x (2 * (1 / ((k:ℝ) + 1))) ⊆ ball x r := ball_subset_ball hk
      rw [Real.norm_eq_abs]
      exact abs_sum_newtonianGradientApprox_deriv_sub_le hn hΩo hΩb hfi (by positivity) hH hα (hsub.trans hball)
        (fun y hy => hHol y (hsub hy) x (mem_ball_self hr))
    exact tendsto_nhds_unique hT1 hT2
  · obtain ⟨r, hr, H, hH, hball, hHol⟩ := hloc x hx
    have hsub : ball x (2 * (r / 4)) ⊆ ball x r := ball_subset_ball (by linarith)
    obtain ⟨h1, h2, -⟩ := abs_newtonianGradientApprox_deriv_sub_rep_le hn hΩo hΩb hfi hθ hθc hU hΩU hθ1 hα hαn
      (by positivity : 0 < r / 4) hH (hsub.trans hball) (fun y hy => hHol y (hsub hy) x (mem_ball_self hr)) i j
    exact ⟨h1, h2, hsecond x hx i j⟩

end Main

section Producer

variable {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))} {f : EuclideanSpace ℝ (Fin n) → ℝ}

/-- From the source inputs (bounded open `Ω`, `f` bounded on `Ω`, locally `α`-Hölder in `Ω` with `0 < α`): continuity,
measurability and integrability on `Ω`, and the real-valued local Hölder bound. Nothing global across `∂Ω` is assumed. -/
theorem localHolder_regularity_of_holderOnWith (hΩo : IsOpen Ω) (hΩb : Bornology.IsBounded Ω) (hfb : ∃ M, ∀ y ∈ Ω, |f y| ≤ M)
    {α : ℝ≥0} (hα0 : 0 < α)
    (hloc : ∀ x ∈ Ω, ∃ r > 0, ∃ H : ℝ≥0, ball x r ⊆ Ω ∧ HolderOnWith H α f (ball x r)) :
    ContinuousOn f Ω ∧ AEMeasurable f (volume.restrict Ω) ∧ IntegrableOn f Ω volume ∧
    ∀ x ∈ Ω, ∃ r > 0, ∃ H : ℝ, 0 ≤ H ∧ ball x r ⊆ Ω ∧
      ∀ y ∈ ball x r, ∀ z ∈ ball x r, |f y - f z| ≤ H * ‖y - z‖ ^ (α:ℝ) := by
  have hc : ContinuousOn f Ω := by
    intro x hx
    obtain ⟨r, hr, H, -, hH⟩ := hloc x hx
    exact ((hH.continuousOn hα0).continuousAt (ball_mem_nhds x hr)).continuousWithinAt
  have hm : AEMeasurable f (volume.restrict Ω) := hc.aemeasurable hΩo.measurableSet
  obtain ⟨M, hM⟩ := hfb
  have hi : IntegrableOn f Ω volume :=
    (integrableOn_const (C := M) hΩb.measure_lt_top.ne).mono' hm.aestronglyMeasurable
      ((ae_restrict_mem hΩo.measurableSet).mono fun y hy => by rw [Real.norm_eq_abs]; exact hM y hy)
  refine ⟨hc, hm, hi, fun x hx => ?_⟩
  obtain ⟨r, hr, H, hsub, hH⟩ := hloc x hx
  refine ⟨r, hr, H, H.coe_nonneg, hsub, fun y hy z hz => ?_⟩
  have h := hH.dist_le hy hz
  rwa [Real.dist_eq, dist_eq_norm] at h

/-- Admissible compact tests exist for every bounded `Ω`: a smooth bump equal to `1` on an open ball containing `Ω`. -/
theorem exists_newtonian_test (hΩb : Bornology.IsBounded Ω) :
    ∃ θ : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ ∞ θ ∧ HasCompactSupport θ ∧
      ∃ U, IsOpen U ∧ Ω ⊆ U ∧ ∀ y ∈ U, θ y = 1 := by
  obtain ⟨R, hR⟩ := hΩb.subset_ball (0:EuclideanSpace ℝ (Fin n))
  set R' := max R 1
  have hR' : 0 < R' := lt_of_lt_of_le one_pos (le_max_right _ _)
  let β : ContDiffBump (0:EuclideanSpace ℝ (Fin n)) := ⟨R', R' + 1, hR', by linarith⟩
  refine ⟨β, β.contDiff, β.hasCompactSupport, ball 0 R', isOpen_ball,
    hR.trans (ball_subset_ball (le_max_left _ _)), fun y hy => β.one_of_mem_closedBall (ball_subset_closedBall hy)⟩

/-- **GT2001 Lemma 4.2 (C², Poisson equation, Hessian representation) from the source inputs.**
`n ≥ 2` (including `n = 2`), `Ω` bounded open, `f` real (signed), bounded on `Ω` and locally `α`-Hölder in `Ω` with
`0 < α ≤ 1` (including `α = 1`). Then `w = newtonianPotential n Ω f` is `C²` in `Ω`, `Δw = f` in `Ω` for the actual Mathlib
Laplacian, and for every `θ ∈ C¹_c` equal to `1` on an open `U ⊇ Ω` the Hessian is the integrable representation
`D_jD_iw(x) = ∫ D_jD_iΓ(x−y)(F(y) − f(x)θ(y))dy + f(x)∫ D_iΓ(x−y)D_jθ(y)dy`, `F = 1_Ω f`; such `θ` exist. -/
theorem newtonianPotential_contDiffOn_two (hn : 2 ≤ n) (hΩo : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hfb : ∃ M, ∀ y ∈ Ω, |f y| ≤ M) {α : ℝ≥0} (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hloc : ∀ x ∈ Ω, ∃ r > 0, ∃ H : ℝ≥0, ball x r ⊆ Ω ∧ HolderOnWith H α f (ball x r)) :
    ContDiffOn ℝ 2 (newtonianPotential n Ω f) Ω ∧
    (∀ x ∈ Ω, Laplacian.laplacian (newtonianPotential n Ω f) x = f x) ∧
    (∀ θ : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ 1 θ → HasCompactSupport θ →
      ∀ U, IsOpen U → Ω ⊆ U → (∀ y ∈ U, θ y = 1) → ∀ x ∈ Ω, ∀ i j : Fin n,
        Integrable (fun y => bilinearIteratedFDerivTwo ℝ (newtonianKernel n) (x - y)
          (EuclideanSpace.basisFun (Fin n) ℝ j) (EuclideanSpace.basisFun (Fin n) ℝ i) *
            (Ω.indicator f y - f x * θ y)) volume ∧
        Integrable (fun y => fderiv ℝ (newtonianKernel n) (x - y) (EuclideanSpace.basisFun (Fin n) ℝ i) *
          fderiv ℝ θ y (EuclideanSpace.basisFun (Fin n) ℝ j)) volume ∧
        iteratedFDeriv ℝ 2 (newtonianPotential n Ω f) x
            ![EuclideanSpace.basisFun (Fin n) ℝ j, EuclideanSpace.basisFun (Fin n) ℝ i] =
          (∫ y, bilinearIteratedFDerivTwo ℝ (newtonianKernel n) (x - y)
              (EuclideanSpace.basisFun (Fin n) ℝ j) (EuclideanSpace.basisFun (Fin n) ℝ i) *
                (Ω.indicator f y - f x * θ y)) +
            f x * ∫ y, fderiv ℝ (newtonianKernel n) (x - y) (EuclideanSpace.basisFun (Fin n) ℝ i) *
              fderiv ℝ θ y (EuclideanSpace.basisFun (Fin n) ℝ j)) ∧
    (∃ θ : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ ∞ θ ∧ HasCompactSupport θ ∧
      ∃ U, IsOpen U ∧ Ω ⊆ U ∧ ∀ y ∈ U, θ y = 1) := by
  obtain ⟨-, -, hfi, hloc'⟩ := localHolder_regularity_of_holderOnWith hΩo hΩb hfb hα0 hloc
  obtain ⟨M, hM⟩ := hfb
  have hα : (0:ℝ) < α := hα0
  have hαn : (α:ℝ) < n := by
    have h1 : (α:ℝ) ≤ 1 := hα1
    have h2 : (2:ℝ) ≤ n := by exact_mod_cast hn
    linarith
  obtain ⟨θ0, hθ0, hθ0c, U0, hU0, hΩU0, hθ01⟩ := exists_newtonian_test (n := n) hΩb
  have hθ0' : ContDiff ℝ 1 θ0 := hθ0.of_le (WithTop.coe_le_coe.mpr le_top)
  obtain ⟨hC2, hΔ, -⟩ := newtonianPotential_contDiffOn_two_of_test hn hΩo hΩb hfi hM hθ0' hθ0c hU0 hΩU0 hθ01 hα hαn hloc'
  refine ⟨hC2, hΔ, fun θ hθ hθc U hU hΩU hθ1 x hx i j => ?_, θ0, hθ0, hθ0c, U0, hU0, hΩU0, hθ01⟩
  exact (newtonianPotential_contDiffOn_two_of_test hn hΩo hΩb hfi hM hθ hθc hU hΩU hθ1 hα hαn hloc').2.2 x hx i j

end Producer

end FunctionalInequalities.Analysis
