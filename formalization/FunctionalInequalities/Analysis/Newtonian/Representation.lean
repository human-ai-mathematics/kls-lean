import FunctionalInequalities.Analysis.Laplacian.Convolution
import FunctionalInequalities.Analysis.Newtonian.PotentialC2

/-!
# Newtonian representation of compactly supported C² functions

The representation (4.15) of Gilbarg–Trudinger, *Elliptic Partial Differential Equations of Second
Order*, Classics 2001 (ISBN 3-540-41160-7), used for Theorem 4.5 (p. 60):

* `locallyIntegrable_newtonianKernel`: `Γ` is locally integrable on `ℝⁿ` for `n ≥ 2`;
* `compact_C2_newtonian_representation`: for `n ≥ 2` and a compactly supported `u ∈ C²(ℝⁿ)`, at every
  `x` the integrand `Γ(x - ·) Δu` is integrable and `u(x) = ∫ Γ(x - y) Δu(y) dy`.

The proof applies Lemma 4.2 (`newtonianPotential_contDiffOn_two`) to `u` itself on a ball containing
its support, giving `Δ(Γ ⋆ u) = u`, and commutes the Laplacian with the convolution
(`laplacian_convolution_compact_C2`).
-/

noncomputable section

open Set Metric MeasureTheory Filter
open scoped Convolution ContDiff Topology NNReal
open FunctionalInequalities.Analysis.BakryEmery
namespace FunctionalInequalities.Analysis

/-- Local integrability of the actual source-normalized kernel, including n=2. -/
theorem locallyIntegrable_newtonianKernel {n : ℕ} (hn : 2 ≤ n) :
    LocallyIntegrable (newtonianKernel n) volume := by
  intro x
  refine ⟨ball 0 (‖x‖+1),isOpen_ball.mem_nhds ?_,
    (integrableOn_newtonianKernel_ball hn (by positivity : 0 < ‖x‖+1)).1⟩
  rw [mem_ball,dist_zero_right]
  linarith

/-- GT2001 (4.15), the compact C² Newtonian representation used in Theorem 4.5.
All integrability and kernel normalization are derived. -/
theorem compact_C2_newtonian_representation {n : ℕ} (hn : 2 ≤ n)
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : ContDiff ℝ 2 u) (hc : HasCompactSupport u)
    (x : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun y => newtonianKernel n (x-y) * Laplacian.laplacian u y) volume ∧
    u x = ∫ y, newtonianKernel n (x-y) * Laplacian.laplacian u y := by
  have hk := locallyIntegrable_newtonianKernel hn
  obtain ⟨r,hr⟩ := hc.isCompact.isBounded.subset_ball (0:EuclideanSpace ℝ (Fin n))
  let R := max r (‖x‖+1)
  let Ω := ball (0:EuclideanSpace ℝ (Fin n)) R
  have hR : 0 < R := lt_of_lt_of_le (by positivity : 0 < ‖x‖+1) (le_max_right _ _)
  have hsupport : tsupport u ⊆ Ω := hr.trans (ball_subset_ball (le_max_left _ _))
  have hx : x ∈ Ω := by
    rw [mem_ball,dist_zero_right]
    exact lt_of_lt_of_le (by linarith : ‖x‖ < ‖x‖+1) (le_max_right _ _)
  have hzero (y : EuclideanSpace ℝ (Fin n)) (hy : y ∉ Ω) : u y = 0 := by
    by_contra h
    exact hy (hsupport (subset_closure h))
  have hbridge : newtonianPotential n Ω u =
      newtonianKernel n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u := by
    funext a
    rw [newtonianPotential,setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun y hy => by rw [hzero y hy,mul_zero])]
    have ht := integral_sub_left_eq_self (fun t => newtonianKernel n t * u (a-t)) volume a
    simpa only [sub_sub_cancel,convolution_def,ContinuousLinearMap.lsmul_apply,smul_eq_mul] using ht
  have hu1 : ContDiff ℝ 1 u := hu.of_le (by norm_num)
  obtain ⟨M,hM⟩ := hu.continuous.bounded_above_of_compact_support hc
  have hbounded : ∃ M, ∀ y ∈ Ω, |u y| ≤ M := ⟨M,fun y _ => by simpa only [Real.norm_eq_abs] using hM y⟩
  have hloc : ∀ a ∈ Ω, ∃ s > 0, ∃ H : ℝ≥0, ball a s ⊆ Ω ∧ HolderOnWith H 1 u (ball a s) := by
    intro a ha
    obtain ⟨H,t,ht,hLip⟩ := (hu1.contDiffAt (x := a)).exists_lipschitzOnWith
    obtain ⟨s,hs,hsub⟩ := Metric.mem_nhds_iff.mp (inter_mem ht (isOpen_ball.mem_nhds ha))
    exact ⟨s,hs,H,fun y hy => (hsub hy).2,(hLip.mono (fun y hy => (hsub hy).1)).holderOnWith⟩
  have hP := (newtonianPotential_contDiffOn_two hn isOpen_ball isBounded_ball hbounded
    (by norm_num : (0:ℝ≥0)<1) (by norm_num : (1:ℝ≥0)≤1) hloc).2.1 x hx
  rw [hbridge] at hP
  have hcLap := hasCompactSupport_laplacian hc
  have hIL := hcLap.convolutionExists_right (ContinuousLinearMap.lsmul ℝ ℝ) hk (continuous_laplacian hu) x
  have hreflect : (fun y => newtonianKernel n (x-y) * Laplacian.laplacian u y) =
      (fun t => (ContinuousLinearMap.lsmul ℝ ℝ (newtonianKernel n t))
        (Laplacian.laplacian u (x-t))) ∘ (fun y => x-y) := by
    funext y
    simp only [Function.comp_def,sub_sub_cancel,ContinuousLinearMap.lsmul_apply,smul_eq_mul]
  have hi : Integrable (fun y => newtonianKernel n (x-y) * Laplacian.laplacian u y) volume := by
    rw [hreflect]
    exact hIL.comp_sub_left x
  refine ⟨hi, ?_⟩
  calc
    u x = Laplacian.laplacian (newtonianKernel n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] u) x := hP.symm
    _ = (newtonianKernel n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] Laplacian.laplacian u) x :=
      laplacian_convolution_compact_C2 hk hu hc x
    _ = ∫ y, newtonianKernel n (x-y) * Laplacian.laplacian u y := by
      have ht := integral_sub_left_eq_self (fun t => newtonianKernel n t * Laplacian.laplacian u (x-t)) volume x
      simpa only [sub_sub_cancel,convolution_def,ContinuousLinearMap.lsmul_apply,smul_eq_mul] using ht.symm
end FunctionalInequalities.Analysis
