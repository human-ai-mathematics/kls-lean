module

public import FunctionalInequalities.Analysis.Newtonian.Truncation.Error
public import Mathlib.Analysis.Calculus.UniformLimitsDeriv
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# The Newtonian potential and its first derivatives (GT Lemma 4.1)

`newtonianPotential n Ω f x = ∫_Ω Γ(x - y) f(y) dy`, the Newtonian potential (4.1) of
Gilbarg–Trudinger,
*Elliptic Partial Differential Equations of Second Order*, Classics 2001 (ISBN 3-540-41160-7), with
the
source-normalized kernel `newtonianKernel n`, and Lemma 4.1 (p. 54):

* `newtonianPotential_contDiff_one`: for `n ≥ 2`, a bounded open `Ω` and `f` integrable and bounded
  on
  `Ω`, the scalar and first-derivative integrands are integrable for every `x`, `w ∈ C¹(ℝⁿ)` and
  `D_i w(x) = ∫_Ω D_iΓ(x - y) f(y) dy` for every `x ∈ ℝⁿ` (the source states it for `x ∈ Ω`);
* `newtonianPotential_contDiff_one_of_aebounded`: the same for a bounded measurable `Ω` and an
  a.e.-measurable, essentially bounded `f`.

The proof passes to the limit in smooth truncations of the kernel, uniformly in the derivative.
Connectedness of `Ω` is not needed.
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory Filter
open scoped ContDiff Topology

namespace FunctionalInequalities.Analysis

/-- The Newtonian potential of `f` over `Ω` with the source-normalized kernel (GT2001 (4.1)):
`w(x) = ∫_Ω Γ(x − y) f(y) dy`. -/
def newtonianPotential (n : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∫ y in Ω, newtonianKernel n (x - y) * f y

section Potential

variable {n : ℕ}

/-- Local L¹ on `B(0,R)` translates and reflects to local L¹ of `y ↦ h(x − y)` on `B(x,R)`. -/
theorem integrableOn_ball_comp_sub {h : EuclideanSpace ℝ (Fin n) → ℝ} {R : ℝ}
    (hh : IntegrableOn h (ball 0 R) volume) (x : EuclideanSpace ℝ (Fin n)) :
    IntegrableOn (fun y => h (x - y)) (ball x R) volume := by
  have hI : Integrable ((ball (0:EuclideanSpace ℝ (Fin n)) R).indicator h) volume :=
    (integrable_indicator_iff measurableSet_ball).mpr hh
  have hT := hI.comp_sub_left x
  have heq : (fun y => (ball (0:EuclideanSpace ℝ (Fin n)) R).indicator h (x - y)) =
      (ball x R).indicator (fun y => h (x - y)) := by
    funext y
    by_cases hy : y ∈ ball x R
    · have hy' : x - y ∈ ball (0:EuclideanSpace ℝ (Fin n)) R := by
        rw [mem_ball, dist_zero_right, norm_sub_rev]; rwa [mem_ball, dist_eq_norm] at hy
      rw [Set.indicator_of_mem hy', Set.indicator_of_mem hy]
    · have hy' : x - y ∉ ball (0:EuclideanSpace ℝ (Fin n)) R := by
        rw [mem_ball, dist_zero_right, norm_sub_rev]; rwa [mem_ball, dist_eq_norm] at hy
      rw [Set.indicator_of_notMem hy', Set.indicator_of_notMem hy]
  rw [heq] at hT
  exact (integrable_indicator_iff measurableSet_ball).mp hT

/-- A bounded set lies in a ball of positive radius around any centre. -/
private theorem exists_pos_ball_superset {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (hΩb : Bornology.IsBounded Ω) (x : EuclideanSpace ℝ (Fin n)) : ∃ R, 0 < R ∧ Ω ⊆ ball x R := by
  obtain ⟨r, hr⟩ := hΩb.subset_ball x
  exact ⟨max r 1, by positivity, hr.trans (ball_subset_ball (le_max_left _ _))⟩

variable {Ω : Set (EuclideanSpace ℝ (Fin n))} {f : EuclideanSpace ℝ (Fin n) → ℝ} {M : ℝ}

/-- The scalar Newtonian integrand is integrable on a bounded set for every `x`. -/
theorem integrableOn_newtonianKernel_sub_mul (hn : 2 ≤ n) (hΩb : Bornology.IsBounded Ω)
    (hf : AEMeasurable f (volume.restrict Ω)) (hM : ∀ᵐ y ∂(volume.restrict Ω), |f y| ≤ M)
    (x : EuclideanSpace ℝ (Fin n)) :
    IntegrableOn (fun y => newtonianKernel n (x - y) * f y) Ω volume := by
  obtain ⟨R, hR, hsub⟩ := exists_pos_ball_superset hΩb x
  have hk :=
    ((integrableOn_ball_comp_sub (integrableOn_newtonianKernel_ball hn hR).1 x).mono_set hsub)
  exact hk.mul_bdd hf.aestronglyMeasurable (by simpa only [Real.norm_eq_abs] using hM)

/-- Every first-derivative component integrand is integrable on a bounded set for every `x`. -/
theorem integrableOn_fderiv_newtonianKernel_sub_mul (hn : 2 ≤ n) (hΩb : Bornology.IsBounded Ω)
    (hf : AEMeasurable f (volume.restrict Ω)) (hM : ∀ᵐ y ∂(volume.restrict Ω), |f y| ≤ M)
    (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    IntegrableOn
      (fun y =>
        fderiv ℝ (newtonianKernel n) (x - y) (EuclideanSpace.basisFun (Fin n) ℝ i) * f y)
      Ω volume := by
  obtain ⟨R, hR, hsub⟩ := exists_pos_ball_superset hΩb x
  have hk :=
    (integrableOn_ball_comp_sub (integrableOn_fderiv_newtonianKernel_ball hn hR i).1 x).mono_set
      hsub
  exact hk.mul_bdd hf.aestronglyMeasurable (by simpa only [Real.norm_eq_abs] using hM)

/-- The operator-valued derivative integrand is integrable on a bounded set for every `x`. -/
private theorem integrable_smul_fderiv_newtonianKernel (hn : 2 ≤ n)
    (hΩb : Bornology.IsBounded Ω) (hf : AEMeasurable f (volume.restrict Ω))
    (hM : ∀ᵐ y ∂(volume.restrict Ω), |f y| ≤ M) (x : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun y => f y • fderiv ℝ (newtonianKernel n) (x - y)) (volume.restrict Ω) := by
  obtain ⟨R, hR, hsub⟩ := exists_pos_ball_superset hΩb x
  have hcomp (i : Fin n) :
    Integrable
      (fun y => |fderiv ℝ (newtonianKernel n) (x - y) (EuclideanSpace.basisFun (Fin n) ℝ i)|)
      (volume.restrict Ω) :=
    ((integrableOn_ball_comp_sub (integrableOn_fderiv_newtonianKernel_ball hn hR i).1
            x).mono_set
        hsub).abs
  have hsum := (integrable_finsetSum Finset.univ fun i _ => hcomp i).const_mul (max M 0)
  have hmeas :
    AEStronglyMeasurable (fun y => f y • fderiv ℝ (newtonianKernel n) (x - y))
      (volume.restrict Ω) :=
    hf.aestronglyMeasurable.smul
      ((measurable_fderiv ℝ (newtonianKernel n)).comp
          (measurable_const.sub measurable_id)).aestronglyMeasurable
  refine hsum.mono' hmeas ?_
  filter_upwards [hM] with y hy
  rw [norm_smul, Real.norm_eq_abs]
  have hL := opNorm_le_sum_abs_basisFun (fderiv ℝ (newtonianKernel n) (x - y))
  exact mul_le_mul (hy.trans (le_max_left _ _)) hL (norm_nonneg _) (le_max_right _ _)

/-- Differentiation under a bounded-domain integral for a C1 translated kernel. -/
theorem hasFDerivAt_setIntegral_comp_sub_mul {T : EuclideanSpace ℝ (Fin n) → ℝ}
    (hT : ContDiff ℝ 1 T) (hΩm : MeasurableSet Ω) (hΩb : Bornology.IsBounded Ω)
    (hf : AEMeasurable f (volume.restrict Ω)) (hM : ∀ᵐ y ∂(volume.restrict Ω), |f y| ≤ M) :
    (∀ x,
        HasFDerivAt (fun x => ∫ y in Ω, T (x - y) * f y) (∫ y in Ω, f y • fderiv ℝ T (x - y))
          x) ∧
      (∀ x, Integrable (fun y => f y • fderiv ℝ T (x - y)) (volume.restrict Ω)) ∧
        Continuous (fun x => ∫ y in Ω, f y • fderiv ℝ T (x - y)) := by
  have : IsFiniteMeasure (volume.restrict Ω) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hΩb.measure_lt_top⟩
  have hTc : Continuous T := hT.continuous
  have hT1 : Continuous (fderiv ℝ T) := hT.continuous_fderiv one_ne_zero
  have hTd : Differentiable ℝ T := hT.differentiable one_ne_zero
  set M' := max M 0
  have hM' : ∀ᵐ y ∂(volume.restrict Ω), |f y| ≤ M' :=
    hM.mono fun _ h => h.trans (le_max_left _ _)
  have hfi : Integrable f (volume.restrict Ω) :=
    (integrable_const M').mono' hf.aestronglyMeasurable
      (by simpa only [Real.norm_eq_abs] using hM')
  obtain ⟨R0, hR0⟩ := hΩb.subset_closedBall (0 : EuclideanSpace ℝ (Fin n))
  have hmem (x0 x y : EuclideanSpace ℝ (Fin n)) (hx : x ∈ ball x0 1) (hy : y ∈ Ω) :
    x - y ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) (‖x0‖ + 1 + R0) := by
    have h1 : ‖x‖ ≤ ‖x0‖ + 1 := by
      have := norm_le_norm_add_norm_sub' x x0
      rw [mem_ball, dist_eq_norm] at hx; linarith
    have h2 : ‖y‖ ≤ R0 := by simpa only [mem_closedBall, dist_zero_right] using hR0 hy
    rw [mem_closedBall, dist_zero_right]
    exact (norm_sub_le x y).trans (by linarith)
  have hbounds (x0 : EuclideanSpace ℝ (Fin n)) :
    ∃ K1 K2 : ℝ,
      (∀ z ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) (‖x0‖ + 1 + R0), ‖T z‖ ≤ K1) ∧
        ∀ z ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) (‖x0‖ + 1 + R0), ‖fderiv ℝ T z‖ ≤ K2 := by
    obtain ⟨K1, h1⟩ :=
      (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n))
            (‖x0‖ + 1 + R0)).exists_bound_of_continuousOn
        hTc.continuousOn
    obtain ⟨K2, h2⟩ :=
      (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n))
            (‖x0‖ + 1 + R0)).exists_bound_of_continuousOn
        hT1.continuousOn
    exact ⟨K1, K2, h1, h2⟩
  have hmeasF (x : EuclideanSpace ℝ (Fin n)) :
    AEStronglyMeasurable (fun y => T (x - y) * f y) (volume.restrict Ω) :=
    (hTc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable.mul
      hf.aestronglyMeasurable
  have hmeasF' (x : EuclideanSpace ℝ (Fin n)) :
    AEStronglyMeasurable (fun y => f y • fderiv ℝ T (x - y)) (volume.restrict Ω) :=
    hf.aestronglyMeasurable.smul
      (hT1.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  have hboundF' (x0 : EuclideanSpace ℝ (Fin n)) (K2 : ℝ)
    (h2 :
      ∀ z ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) (‖x0‖ + 1 + R0), ‖fderiv ℝ T z‖ ≤ K2) :
    ∀ᵐ y ∂(volume.restrict Ω), ∀ x ∈ ball x0 1, ‖f y • fderiv ℝ T (x - y)‖ ≤ M' * K2 := by
    filter_upwards [ae_restrict_mem hΩm, hM'] with y hy hfy
    intro x hx
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul hfy (h2 _ (hmem x0 x y hx hy)) (norm_nonneg _) (le_max_right _ _)
  refine ⟨fun x0 => ?_, fun x0 => ?_, ?_⟩
  · obtain ⟨K1, K2, h1, h2⟩ := hbounds x0
    have hint : Integrable (fun y => T (x0 - y) * f y) (volume.restrict Ω) := by
      refine
        hfi.bdd_mul (c := K1)
          (hTc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable ?_
      filter_upwards [ae_restrict_mem hΩm] with y hy
      exact h1 _ (hmem x0 x0 y (mem_ball_self one_pos) hy)
    refine
      hasFDerivAt_integral_of_dominated_of_fderiv_le (ball_mem_nhds x0 one_pos)
        (Eventually.of_forall hmeasF) hint (hmeasF' x0) (hboundF' x0 K2 h2) (integrable_const _)
        ?_
    refine ae_of_all _ fun y x _ => ?_
    have hc : HasFDerivAt (fun x => T (x - y)) (fderiv ℝ T (x - y)) x := by
      have hs :
        HasFDerivAt (fun x : EuclideanSpace ℝ (Fin n) => x - y)
          (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))) x :=
        (hasFDerivAt_id x).sub_const y
      have h := (hTd (x - y)).hasFDerivAt.comp x hs
      rw [ContinuousLinearMap.comp_id] at h
      exact h
    exact hc.mul_const (f y)
  · obtain ⟨_, K2, -, h2⟩ := hbounds x0
    refine (integrable_const (M' * K2)).mono' (hmeasF' x0) ?_
    filter_upwards [hboundF' x0 K2 h2] with y hy
    exact hy x0 (mem_ball_self one_pos)
  · refine continuous_iff_continuousAt.mpr fun x0 => ?_
    obtain ⟨_, K2, -, h2⟩ := hbounds x0
    refine
      continuousAt_of_dominated (bound := fun _ => M' * K2) (Eventually.of_forall hmeasF') ?_
        (integrable_const _) (ae_of_all _ fun y => ?_)
    · filter_upwards [ball_mem_nhds x0 one_pos] with x hx
      filter_upwards [hboundF' x0 K2 h2] with y hy
      exact hy x hx
    · exact
        ((hT1.comp (continuous_id.sub (continuous_const (y := y)))).const_smul
            (f y)).continuousAt


/--
The smooth truncated potentials are differentiable everywhere, with the derivative under the
integral, and the
derivative field is continuous. Uses only the finite measure of `Ω` and the essential bound of `f`.
-/
private theorem approx_hasFDerivAt_continuous (hn : 2 ≤ n) (hΩm : MeasurableSet Ω)
    (hΩb : Bornology.IsBounded Ω) (hf : AEMeasurable f (volume.restrict Ω))
    (hM : ∀ᵐ y ∂(volume.restrict Ω), |f y| ≤ M) {eps : ℝ} (heps : 0 < eps) :
    (∀ x,
        HasFDerivAt (fun x => ∫ y in Ω, truncatedNewtonianKernel n eps (x - y) * f y)
          (∫ y in Ω, f y • fderiv ℝ (truncatedNewtonianKernel n eps) (x - y)) x) ∧
      Continuous (fun x => ∫ y in Ω, f y • fderiv ℝ (truncatedNewtonianKernel n eps) (x - y)) := by
  obtain ⟨hd, -, hc⟩ :=
    hasFDerivAt_setIntegral_comp_sub_mul
      ((contDiff_truncatedNewtonianKernel hn heps).of_le (WithTop.coe_le_coe.mpr le_top)) hΩm
      hΩb hf hM
  exact ⟨hd, hc⟩
/--
Scalar approximation error at every point: `|w_ε(x) − w(x)| ≤ max M 0 · newtonianScalarErrorBound n
ε`. -/
private theorem approx_potential_error (hn : 2 ≤ n) (hΩb : Bornology.IsBounded Ω)
    (hf : AEMeasurable f (volume.restrict Ω)) (hM : ∀ᵐ y ∂(volume.restrict Ω), |f y| ≤ M)
    {eps : ℝ} (heps : 0 < eps) (x : EuclideanSpace ℝ (Fin n)) :
    |(∫ y in Ω, truncatedNewtonianKernel n eps (x - y) * f y) - newtonianPotential n Ω f x| ≤
      max M 0 * newtonianScalarErrorBound n eps := by
  set M' := max M 0
  have hM' : ∀ᵐ y ∂(volume.restrict Ω), |f y| ≤ M' :=
    hM.mono fun _ h => h.trans (le_max_left _ _)
  obtain ⟨hE, hEb⟩ := integrable_truncatedNewtonianKernel_sub hn heps
  set E : EuclideanSpace ℝ (Fin n) → ℝ := fun y =>
    truncatedNewtonianKernel n eps y - newtonianKernel n y
  have hEx : Integrable (fun y => E (x - y)) volume := hE.comp_sub_left x
  have hW := integrableOn_newtonianKernel_sub_mul hn hΩb hf hM x
  have hEf : Integrable (fun y => E (x - y) * f y) (volume.restrict Ω) :=
    hEx.integrableOn.mul_bdd hf.aestronglyMeasurable (by simpa only [Real.norm_eq_abs] using hM)
  have hA :
    Integrable (fun y => truncatedNewtonianKernel n eps (x - y) * f y) (volume.restrict Ω) :=
    (hW.add hEf).congr (ae_of_all _ fun y => by simp only [E, Pi.add_apply]; ring)
  have hdiff :
    (∫ y in Ω, truncatedNewtonianKernel n eps (x - y) * f y) - newtonianPotential n Ω f x =
      ∫ y in Ω, E (x - y) * f y := by
    unfold newtonianPotential
    rw [← integral_sub hA hW]
    congr 1; funext y; simp only [E]; ring
  have hg : Integrable (fun y => M' * |E (x - y)|) volume := hEx.abs.const_mul M'
  rw [hdiff, ← Real.norm_eq_abs]
  calc
    _ ≤ ∫ y in Ω, M' * |E (x - y)| := by
      refine norm_integral_le_of_norm_le hg.integrableOn ?_
      filter_upwards [hM'] with y hy
      rw [Real.norm_eq_abs, abs_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right hy (abs_nonneg _)
    _ ≤ ∫ y, M' * |E (x - y)| := setIntegral_le_integral hg (ae_of_all _ fun y => by positivity)
    _ = M' * ∫ y, |E y| := by
      rw [integral_const_mul, integral_sub_left_eq_self (fun z => |E z|) volume x]
    _ ≤ M' * newtonianScalarErrorBound n eps := mul_le_mul_of_nonneg_left hEb (le_max_right _ _)

/--
Operator-valued derivative approximation error at every point, from the component L¹ error bounds.
-/
private theorem approx_deriv_error (hn : 2 ≤ n) (hΩb : Bornology.IsBounded Ω)
    (hf : AEMeasurable f (volume.restrict Ω)) (hM : ∀ᵐ y ∂(volume.restrict Ω), |f y| ≤ M)
    {eps C : ℝ}
    (hcap :
      ∀ i : Fin n,
        Integrable
            (fun y =>
              fderiv ℝ (truncatedNewtonianKernel n eps) y
                  (EuclideanSpace.basisFun (Fin n) ℝ i) -
                fderiv ℝ (newtonianKernel n) y (EuclideanSpace.basisFun (Fin n) ℝ i))
            volume ∧
          (∫ y,
              |fderiv ℝ (truncatedNewtonianKernel n eps) y
                    (EuclideanSpace.basisFun (Fin n) ℝ i) -
                  fderiv ℝ (newtonianKernel n) y (EuclideanSpace.basisFun (Fin n) ℝ i)|) ≤
            C)
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖(∫ y in Ω, f y • fderiv ℝ (truncatedNewtonianKernel n eps) (x - y)) -
          ∫ y in Ω, f y • fderiv ℝ (newtonianKernel n) (x - y)‖ ≤
      max M 0 * ((n : ℝ) * C) := by
  set M' := max M 0
  have hM' : ∀ᵐ y ∂(volume.restrict Ω), |f y| ≤ M' :=
    hM.mono fun _ h => h.trans (le_max_left _ _)
  set T := truncatedNewtonianKernel n eps
  set D : Fin n → EuclideanSpace ℝ (Fin n) → ℝ := fun i y =>
    fderiv ℝ T y (EuclideanSpace.basisFun (Fin n) ℝ i) -
      fderiv ℝ (newtonianKernel n) y (EuclideanSpace.basisFun (Fin n) ℝ i)
  have hDx (i : Fin n) : Integrable (fun y => |D i (x - y)|) volume :=
    ((hcap i).1.comp_sub_left x).abs
  have hg : Integrable (fun y => M' * ∑ i, |D i (x - y)|) volume :=
    (integrable_finsetSum Finset.univ fun i _ => hDx i).const_mul M'
  have hΔ :
    Integrable (fun y => f y • (fderiv ℝ T (x - y) - fderiv ℝ (newtonianKernel n) (x - y)))
      (volume.restrict Ω) := by
    refine
      hg.integrableOn.mono'
        (hf.aestronglyMeasurable.smul
          (((measurable_fderiv ℝ T).sub (measurable_fderiv ℝ (newtonianKernel n))).comp
              (measurable_const.sub measurable_id)).aestronglyMeasurable)
        ?_
    filter_upwards [hM'] with y hy
    rw [norm_smul, Real.norm_eq_abs]
    refine
      mul_le_mul hy ((opNorm_le_sum_abs_basisFun _).trans_eq ?_) (norm_nonneg _)
        (le_max_right _ _)
    simp only [D, sub_apply]
  have hWi := integrable_smul_fderiv_newtonianKernel hn hΩb hf hM x
  have hsplit :
    (fun y => f y • fderiv ℝ T (x - y)) = fun y =>
      f y • fderiv ℝ (newtonianKernel n) (x - y) +
        f y • (fderiv ℝ T (x - y) - fderiv ℝ (newtonianKernel n) (x - y)) := by
    funext y; rw [← smul_add, add_sub_cancel]
  rw [hsplit, integral_add hWi hΔ, add_sub_cancel_left]
  calc
    _ ≤ ∫ y in Ω, M' * ∑ i, |D i (x - y)| := by
      refine norm_integral_le_of_norm_le hg.integrableOn ?_
      filter_upwards [hM'] with y hy
      rw [norm_smul, Real.norm_eq_abs]
      refine
        mul_le_mul hy ((opNorm_le_sum_abs_basisFun _).trans_eq ?_) (norm_nonneg _)
          (le_max_right _ _)
      simp only [D, sub_apply]
    _ ≤ ∫ y, M' * ∑ i, |D i (x - y)| :=
      setIntegral_le_integral hg (ae_of_all _ fun y => by positivity)
    _ = M' * ∑ i, ∫ y, |D i y| := by
      rw [integral_const_mul, integral_finsetSum Finset.univ fun i _ => hDx i]
      congr 1
      exact
        Finset.sum_congr rfl fun i _ => integral_sub_left_eq_self (fun z => |D i z|) volume x
    _ ≤ M' * ∑ _i : Fin n, C :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => (hcap i).2) (le_max_right _ _)
    _ = M' * ((n : ℝ) * C) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/--
**GT2001 Lemma 4.1, stronger support form.** For `n ≥ 2`, a bounded measurable `Ω` and a signed real
`f` that is
a.e.-measurable and essentially bounded on `Ω`: for every `x` the scalar and first-derivative
Newtonian integrands are
integrable on `Ω`, the Newtonian potential is globally `C¹`, and for every `x` and every coordinate
`i`,
`D_i w(x) = ∫_Ω D_iΓ(x − y) f(y) dy`. The source normalization of `Γ`, including the planar
logarithm and its finite
value at `0`, is that of `newtonianKernel`. -/
theorem newtonianPotential_contDiff_one_of_aebounded (hn : 2 ≤ n) (hΩm : MeasurableSet Ω)
    (hΩb : Bornology.IsBounded Ω) (hf : AEMeasurable f (volume.restrict Ω))
    (hM : ∀ᵐ y ∂(volume.restrict Ω), |f y| ≤ M) :
    (∀ x, IntegrableOn (fun y => newtonianKernel n (x - y) * f y) Ω volume) ∧
      (∀ x (i : Fin n),
          IntegrableOn
            (fun y =>
              fderiv ℝ (newtonianKernel n) (x - y) (EuclideanSpace.basisFun (Fin n) ℝ i) * f y)
            Ω volume) ∧
        ContDiff ℝ 1 (newtonianPotential n Ω f) ∧
          ∀ x (i : Fin n),
            fderiv ℝ (newtonianPotential n Ω f) x (EuclideanSpace.basisFun (Fin n) ℝ i) =
              ∫ y in Ω,
                fderiv ℝ (newtonianKernel n) (x - y) (EuclideanSpace.basisFun (Fin n) ℝ i) *
                  f y := by
  obtain ⟨B, -, hcap⟩ := exists_newtonian_truncation_derivative_l1_cap
  set M' := max M 0
  set ε : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hε (k : ℕ) : 0 < ε k := by positivity
  set W : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ := fun x =>
    ∫ y in Ω, f y • fderiv ℝ (newtonianKernel n) (x - y)
  have hA (k : ℕ) := approx_hasFDerivAt_continuous hn hΩm hΩb hf hM (hε k)
  obtain ⟨hS, hC⟩ := tendsto_newtonian_error_bounds n
  have hfg :
    ∀ x,
      Tendsto (fun k => ∫ y in Ω, truncatedNewtonianKernel n (ε k) (x - y) * f y) atTop
        (𝓝 (newtonianPotential n Ω f x)) := by
    intro x
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have h0 : Tendsto (fun k => M' * newtonianScalarErrorBound n (ε k)) atTop (𝓝 0) := by
      simpa only [mul_zero] using hS.const_mul M'
    refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_) h0
    rw [Real.norm_eq_abs]
    exact approx_potential_error hn hΩb hf hM (hε k) x
  have hunif :
    TendstoUniformly
      (fun k x => ∫ y in Ω, f y • fderiv ℝ (truncatedNewtonianKernel n (ε k)) (x - y)) W
      atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro δ hδ
    have h0 :
      Tendsto (fun k => M' * ((n : ℝ) * ((1 + B / 2) * newtonianDerivErrorBound n (ε k)))) atTop
        (𝓝 0) := by
      simpa only [mul_zero] using ((hC.const_mul (1 + B / 2)).const_mul (n : ℝ)).const_mul M'
    filter_upwards [h0.eventually (gt_mem_nhds hδ)] with k hk x
    rw [dist_comm, dist_eq_norm]
    exact (approx_deriv_error hn hΩb hf hM (fun i => hcap n hn (ε k) (hε k) i) x).trans_lt hk
  have hW (x : EuclideanSpace ℝ (Fin n)) : HasFDerivAt (newtonianPotential n Ω f) (W x) x :=
    hasFDerivAt_of_tendstoUniformly hunif (fun k x => (hA k).1 x) hfg x
  have hWc : Continuous W := hunif.continuous (Frequently.of_forall fun k => (hA k).2)
  have hfd : fderiv ℝ (newtonianPotential n Ω f) = W := funext fun x => (hW x).fderiv
  refine
    ⟨integrableOn_newtonianKernel_sub_mul hn hΩb hf hM,
      integrableOn_fderiv_newtonianKernel_sub_mul hn hΩb hf hM,
      contDiff_one_iff_fderiv.mpr ⟨fun x => (hW x).differentiableAt, hfd ▸ hWc⟩, fun x i => ?_⟩
  rw [hfd]
  change
    (∫ y in Ω, f y • fderiv ℝ (newtonianKernel n) (x - y))
        (EuclideanSpace.basisFun (Fin n) ℝ i) =
      _
  rw [ContinuousLinearMap.integral_apply
      (integrable_smul_fderiv_newtonianKernel hn hΩb hf hM x)]
  congr 1; funext y
  rw [smul_apply, smul_eq_mul, mul_comm]

/--
**GT2001 Lemma 4.1 (Gilbarg–Trudinger, 2001 Classics, p. 54), from the original inputs.** Let `n ≥
2`, `Ω` a bounded
open set in `ℝⁿ`, and `f` a real (signed) function that is integrable and bounded on `Ω`. Then for
every `x` the
Newtonian integrand `y ↦ Γ(x − y) f(y)` and every first-derivative integrand `y ↦ D_iΓ(x − y) f(y)`
are integrable on
`Ω`, the Newtonian potential `w = ∫_Ω Γ(· − y) f(y) dy` is `C¹` on all of `ℝⁿ`, and `D_i w(x) = ∫_Ω
D_iΓ(x − y) f(y) dy`
for every `x ∈ ℝⁿ` and every `i` (the source states the formula for `x ∈ Ω`). Connectedness of `Ω`
is not needed. -/
theorem newtonianPotential_contDiff_one (hn : 2 ≤ n) (hΩo : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω) (hf : IntegrableOn f Ω volume)
    (hfb : ∃ M, ∀ y ∈ Ω, |f y| ≤ M) :
    (∀ x, IntegrableOn (fun y => newtonianKernel n (x - y) * f y) Ω volume) ∧
      (∀ x (i : Fin n),
          IntegrableOn
            (fun y =>
              fderiv ℝ (newtonianKernel n) (x - y) (EuclideanSpace.basisFun (Fin n) ℝ i) * f y)
            Ω volume) ∧
        ContDiff ℝ 1 (newtonianPotential n Ω f) ∧
          ∀ x (i : Fin n),
            fderiv ℝ (newtonianPotential n Ω f) x (EuclideanSpace.basisFun (Fin n) ℝ i) =
              ∫ y in Ω,
                fderiv ℝ (newtonianKernel n) (x - y) (EuclideanSpace.basisFun (Fin n) ℝ i) *
                  f y := by
  obtain ⟨M, hM⟩ := hfb
  exact
    newtonianPotential_contDiff_one_of_aebounded hn hΩo.measurableSet hΩb hf.aemeasurable
      (ae_restrict_of_forall_mem hΩo.measurableSet hM)

end Potential

end FunctionalInequalities.Analysis
