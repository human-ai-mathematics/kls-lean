import FunctionalInequalities.Analysis.Cutoff.Translation
import FunctionalInequalities.Analysis.Convex.SecondDifference
import FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.WeakInverseHessian
import FunctionalInequalities.Analysis.Convex.Viscosity
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Integrated energy of Hessian increments

For a weak `C^{1,1}` Monge–Ampère potential `u` (Letwin arXiv:2607.24164v1, weak route toward Theorem 2.5):

* `integrable_hessian_increment_energy`: for continuous `u` with Lipschitz gradient and a continuous compactly supported
  `η`, the density `η (‖H(x+h) − H(x)‖²_F + ‖H(x−h) − H(x)‖²_F) e^{−u}` of the total coordinate Hessian `H` is integrable,
  for every shift `h` and every finite dimension;
* `integral_mul_hessian_increment_le`: under the original hypotheses (C¹ convex `u` with Lipschitz gradient, C¹ convex `V`,
  Lipschitz exponent `−u + V(∇u)`, almost-everywhere positive definite Hessian with the Monge–Ampère log-determinant identity
  and the upper cap `H ≤ K`, nonnegative compactly supported `C²` test `η` and the centered-difference bound
  `u(x+h) + u(x−h) − 2u(x) ≤ D‖h‖²`), the integrated Hessian-increment energy is at most
  `2K²(D‖h‖²) ∫ |η + Lη| e^{−u}`, with `L` the inverse-Hessian generator.

The pointwise coercivity is `ae_hessian_increment_le_generator` (`Analysis/Convex/Viscosity.lean`); the generator identities
and integrability are in `Analysis/BakryEmery/IntegrationByParts/WeakInverseHessian.lean`; the centered-difference facts are in
`Analysis/Convex/SecondDifference.lean`. These are supports: the weak third derivative, Theorem 2.5 and Theorem 1.2 are not
proved here.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace
open FunctionalInequalities.Probability.Stein

namespace FunctionalInequalities.Analysis

/-- The actual squared shifted Hessian-increment density in N11b is integrable
against the continuous compact weight. No C2 or given integrability is assumed. -/
theorem integrable_hessian_increment_energy {n : ℕ}
    {u η : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : Continuous u) {G : NNReal} (hG : LipschitzWith G (gradient u))
    (hη : Continuous η) (hηc : HasCompactSupport η)
    (h : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun x => η x *
      ((∑ i, ∑ j, (hessianMatrix u (x + h) - hessianMatrix u x) i j ^ 2) +
       ∑ i, ∑ j, (hessianMatrix u (x - h) - hessianMatrix u x) i j ^ 2) *
      Real.exp (-u x)) (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  let w : EuclideanSpace ℝ (Fin n) → ℝ := fun x => η x * Real.exp (-u x)
  have hwc : Continuous w :=
    hη.mul (Real.continuous_exp.comp hu.neg)
  have hws : HasCompactSupport w := hηc.mul_right
  have hw : Integrable w (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    hwc.integrable_of_hasCompactSupport hws
  have hentry
      (T : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
      (hT : Continuous T) (i j : Fin n) :
      Integrable
        (fun x => (hessianMatrix u (T x) i j - hessianMatrix u x i j) ^ 2 * w x)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    have hm := measurable_hessianMatrix_entry u i j
    have hmd :
        Measurable (fun x => hessianMatrix u (T x) i j - hessianMatrix u x i j) :=
      (hm.comp hT.measurable).sub hm
    have hms :
        Measurable
          (fun x => (hessianMatrix u (T x) i j - hessianMatrix u x i j) ^ 2) := by
      simp only [pow_two]
      exact hmd.mul hmd
    apply hw.bdd_mul hms.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro x
    have hb :
        ‖hessianMatrix u (T x) i j - hessianMatrix u x i j‖ ≤
          (G : ℝ) + (G : ℝ) :=
      calc
        ‖hessianMatrix u (T x) i j - hessianMatrix u x i j‖ ≤
            ‖hessianMatrix u (T x) i j‖ + ‖hessianMatrix u x i j‖ :=
          norm_sub_le _ _
        _ ≤ (G : ℝ) + (G : ℝ) :=
          add_le_add
            (norm_hessianMatrix_entry_le_of_lipschitz_gradient hG (T x) i j)
            (norm_hessianMatrix_entry_le_of_lipschitz_gradient hG x i j)
    exact
      (norm_pow _ 2).le.trans
        (pow_le_pow_left₀ (norm_nonneg _) hb 2)
  have hsum
      (T : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
      (hT : Continuous T) :
      Integrable
        (fun x => ∑ i, ∑ j,
          (hessianMatrix u (T x) i j - hessianMatrix u x i j) ^ 2 * w x)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    integrable_finsetSum Finset.univ fun i _ =>
      integrable_finsetSum Finset.univ fun j _ => hentry T hT i j
  have hp := hsum (fun x => x + h) (continuous_id.add continuous_const)
  have hm := hsum (fun x => x - h) (continuous_id.sub continuous_const)
  apply (hp.add hm).congr
  apply Filter.Eventually.of_forall
  intro x
  change
    (∑ i, ∑ j,
      (hessianMatrix u (x + h) i j - hessianMatrix u x i j) ^ 2 * w x) +
    (∑ i, ∑ j,
      (hessianMatrix u (x - h) i j - hessianMatrix u x i j) ^ 2 * w x) =
    η x *
      ((∑ i, ∑ j, (hessianMatrix u (x + h) - hessianMatrix u x) i j ^ 2) +
       ∑ i, ∑ j, (hessianMatrix u (x - h) - hessianMatrix u x) i j ^ 2) *
      Real.exp (-u x)
  simp only [← Finset.sum_mul, Matrix.sub_apply]
  dsimp only [w]
  ring


/-- **Integrated energy of Hessian increments** (weak Letwin route, N11, task N11b; KLS500
`weak_moment_compact_hessian_increment_energy_bound`): for the `C^{1,1}` Monge–Ampère solution `u` with
`0 ≤ Δ²ₕu ≤ D‖h‖²`, every nonnegative `η ∈ C²_c` satisfies
`∫ η (‖H(x+h) − H(x)‖²_F + ‖H(x−h) − H(x)‖²_F) e^{−u} ≤ 2K² D ‖h‖² ∫ |η + Lη| e^{−u}`,
`Lη := tr(H⁻¹∇²η) − DV(∇u)(∇η)`. -/
theorem integral_mul_hessian_increment_le {n : ℕ} {u V η : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ 1 u) (hconv : ConvexOn ℝ univ u) {G : NNReal}
    (hG : LipschitzWith G (gradient u)) (hV : ContDiff ℝ 1 V) (hVc : ConvexOn ℝ univ V)
    {LF : NNReal} (hF : LipschitzWith LF (fun x => -u x + V (gradient u x))) {K : ℝ} (hK : 0 < K)
    (hdata : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (hessianMatrix u x).PosDef ∧
      Real.log (hessianMatrix u x).det = -u x + V (gradient u x) ∧
      (K • (1 : Matrix (Fin n) (Fin n) ℝ) - hessianMatrix u x).PosSemidef)
    (hη : ContDiff ℝ 2 η) (hηc : HasCompactSupport η) (hη0 : ∀ x, 0 ≤ η x) {D : ℝ}
    (h : EuclideanSpace ℝ (Fin n)) (hw : ∀ x, u (x + h) + u (x - h) - 2 * u x ≤ D * ‖h‖ ^ 2) :
    ∫ x, η x * ((∑ i, ∑ j, (hessianMatrix u (x + h) - hessianMatrix u x) i j ^ 2) +
        ∑ i, ∑ j, (hessianMatrix u (x - h) - hessianMatrix u x) i j ^ 2) * Real.exp (-u x)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) ≤
      2 * K ^ 2 * (D * ‖h‖ ^ 2) *
        ∫ x, |η x + (((hessianMatrix u x)⁻¹ * hessianMatrix η x).trace -
          fderiv ℝ V (gradient u x) (gradient η x))| * Real.exp (-u x)
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  classical
  let w : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun x => u (x + h) + u (x - h) - 2 * u x
  let C : ℝ := D * ‖h‖ ^ 2
  let q : ℝ := 2 * K ^ 2
  let ρ : EuclideanSpace ℝ (Fin n) → ℝ := fun x => Real.exp (-u x)
  let L : (EuclideanSpace ℝ (Fin n) → ℝ) → EuclideanSpace ℝ (Fin n) → ℝ :=
    fun f x => ((hessianMatrix u x)⁻¹ * hessianMatrix f x).trace -
      fderiv ℝ V (gradient u x) (gradient f x)
  let E : EuclideanSpace ℝ (Fin n) → ℝ := fun x =>
    (∑ i, ∑ j, (hessianMatrix u (x + h) - hessianMatrix u x) i j ^ 2) +
      ∑ i, ∑ j, (hessianMatrix u (x - h) - hessianMatrix u x) i j ^ 2
  let e : EuclideanSpace ℝ (Fin n) → ℝ := fun x => η x * E x * ρ x
  let p : EuclideanSpace ℝ (Fin n) → ℝ := fun x => η x * L w x * ρ x
  let t : EuclideanSpace ℝ (Fin n) → ℝ := fun x => η x * w x * ρ x
  let s : EuclideanSpace ℝ (Fin n) → ℝ := fun x => w x * L η x * ρ x
  let b : EuclideanSpace ℝ (Fin n) → ℝ := fun x => |η x + L η x| * ρ x

  have hq : 0 < q := mul_pos (by norm_num) (pow_pos hK 2)
  have hρ : Continuous ρ := Real.continuous_exp.comp hu.continuous.neg
  have hρ0 (x : EuclideanSpace ℝ (Fin n)) : 0 ≤ ρ x :=
    (Real.exp_pos (-u x)).le
  have hwreg : ContDiff ℝ 1 w ∧ LipschitzWith (4 * G) (gradient w) :=
    centeredDifference_contDiff_lipschitz_gradient hu hG h
  obtain ⟨hw1, hwG⟩ := hwreg
  have hbounds : (∀ x, 0 ≤ w x ∧ w x ≤ C) ∧ 0 ≤ C :=
    centeredDifference_nonneg_le hconv h hw

  have hdet : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (hessianMatrix u x).det = Real.exp (-u x + V (gradient u x)) := by
    filter_upwards [hdata] with x hx
    rw [← hx.2.1, Real.exp_log hx.1.det_pos]

  have hie : Integrable e (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    integrable_hessian_increment_energy hu.continuous hG hη.continuous hηc h
  have higen :
      Integrable p (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      Integrable s (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      Integrable b (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    integrable_weak_generator_densities hu.continuous hG hV hF.continuous
      hdet hw1.continuous hwG hη hηc
  obtain ⟨hip, his, hib⟩ := higen
  have hit : Integrable t (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    ((hη.continuous.mul hw1.continuous).mul hρ).integrable_of_hasCompactSupport
      (hηc.mul_right.mul_right)

  have hswap : (∫ x, p x) = ∫ x, s x :=
    (integral_mul_generator_eq_neg_energy hu hG hV hF hdet hw1 hwG hη hηc).trans
      (integral_mul_generator_eq_neg_energy' hu hG hV hF hdet hw1 hwG hη hηc).symm
  have hsum : (∫ x, p x + t x) = ∫ x, t x + s x := by
    rw [integral_add hip hit, integral_add hit his, hswap]
    exact add_comm _ _

  have hcoerc := ae_hessian_increment_le_generator
    hu hG (hV.differentiable one_ne_zero) hVc hdata h
  have hpoint :
      ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        e x ≤ q * (p x + t x) := by
    filter_upwards [hcoerc] with x hx
    have hxdiv : E x / q ≤ L w x + w x := hx
    have hxmul : E x ≤ (L w x + w x) * q :=
      (div_le_iff₀ hq).mp hxdiv
    calc
      e x = (η x * ρ x) * E x := by
        dsimp only [e]
        ring
      _ ≤ (η x * ρ x) * ((L w x + w x) * q) :=
        mul_le_mul_of_nonneg_left hxmul (mul_nonneg (hη0 x) (hρ0 x))
      _ = q * (p x + t x) := by
        dsimp only [p, t]
        ring

  have hbound : (∫ x, t x + s x) ≤ C * ∫ x, b x := by
    calc
      (∫ x, t x + s x) ≤ ∫ x, C * b x := by
        apply integral_mono_ae (hit.add his) (hib.const_mul C)
        apply Filter.Eventually.of_forall
        intro x
        have hscalar : w x * (η x + L η x) ≤ C * |η x + L η x| :=
          (mul_le_mul_of_nonneg_left (le_abs_self (η x + L η x))
            (hbounds.1 x).1).trans
            (mul_le_mul_of_nonneg_right (hbounds.1 x).2
              (abs_nonneg (η x + L η x)))
        calc
          t x + s x = (w x * (η x + L η x)) * ρ x := by
            dsimp only [t, s]
            ring
          _ ≤ (C * |η x + L η x|) * ρ x :=
            mul_le_mul_of_nonneg_right hscalar (hρ0 x)
          _ = C * b x := by
            dsimp only [b]
            ring
      _ = C * ∫ x, b x := integral_const_mul C b

  change (∫ x, e x) ≤ q * C * ∫ x, b x
  calc
    (∫ x, e x) ≤ ∫ x, q * (p x + t x) :=
      integral_mono_ae hie ((hip.add hit).const_mul q) hpoint
    _ = q * ∫ x, p x + t x :=
      integral_const_mul q (fun x => p x + t x)
    _ = q * ∫ x, t x + s x := congrArg (fun z : ℝ => q * z) hsum
    _ ≤ q * (C * ∫ x, b x) :=
      mul_le_mul_of_nonneg_left hbound hq.le
    _ = q * C * ∫ x, b x := by ring

end FunctionalInequalities.Analysis


noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff RealInnerProductSpace
open FunctionalInequalities.Probability.Stein
namespace FunctionalInequalities.Analysis

private lemma n11d3_entry_sq_le_total {n : ℕ}
    (P Q : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    P i j ^ 2 ≤
      (∑ k, ∑ l, P k l ^ 2) + ∑ k, ∑ l, Q k l ^ 2 := by
  classical
  have hj : P i j ^ 2 ≤ ∑ l, P i l ^ 2 :=
    Finset.single_le_sum (fun l _ => sq_nonneg (P i l)) (Finset.mem_univ j)
  have hi : (∑ l, P i l ^ 2) ≤ ∑ k, ∑ l, P k l ^ 2 :=
    Finset.single_le_sum
      (fun k _ => Finset.sum_nonneg (fun l _ => sq_nonneg (P k l)))
      (Finset.mem_univ i)
  exact (hj.trans hi).trans
    (le_add_of_nonneg_right
      (Finset.sum_nonneg
        (fun k _ => Finset.sum_nonneg (fun l _ => sq_nonneg (Q k l)))))

set_option maxHeartbeats 800000 in
/-- Produce the actual global L2 difference-quotient bound for a compact cutoff
times a Hessian entry from the original Monge-Ampere/increment hypotheses.
The bound is a conclusion, never a supplied regularity or energy premise. -/
theorem exists_hessian_cutoff_sq_difference_bound {n : ℕ}
    {u V χ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ 1 u) (hconv : ConvexOn ℝ univ u) {G : NNReal}
    (hG : LipschitzWith G (gradient u)) (hV : ContDiff ℝ 1 V) (hVc : ConvexOn ℝ univ V)
    {LF : NNReal} (hF : LipschitzWith LF (fun x => -u x + V (gradient u x)))
    {K : ℝ} (hK : 0 < K)
    (hdata : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (hessianMatrix u x).PosDef ∧
      Real.log (hessianMatrix u x).det = -u x + V (gradient u x) ∧
      (K • (1 : Matrix (Fin n) (Fin n) ℝ) - hessianMatrix u x).PosSemidef)
    {D : ℝ} (hw : ∀ x h, u (x + h) + u (x - h) - 2 * u x ≤ D * ‖h‖ ^ 2)
    (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ)
    (i j : Fin n) (v : EuclideanSpace ℝ (Fin n)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, t ≠ 0 → |t| ≤ 1 →
      (∫ x, (χ (x + t • v) * hessianMatrix u (x + t • v) i j -
        χ x * hessianMatrix u x i j) ^ 2) ≤ C * t ^ 2 := by
  classical
  obtain ⟨η, hη, hηc, hη0, hmajor⟩ :=
    exists_smooth_compact_translate_majorant hu.continuous hχ.continuous hχc v
  have hη2 : ContDiff ℝ 2 η :=
    hη.of_le (WithTop.coe_le_coe.mpr le_top)
  obtain ⟨L, hL⟩ :=
    ContDiff.lipschitzWith_of_hasCompactSupport hχc hχ one_ne_zero
  let H : EuclideanSpace ℝ (Fin n) → ℝ := fun x => hessianMatrix u x i j
  let q : EuclideanSpace ℝ (Fin n) → ℝ :=
    (tsupport η).indicator (fun _ => (1 : ℝ))
  have hqint : Integrable q (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    (integrable_indicator_iff (isClosed_tsupport η).measurableSet).mpr
      (integrableOn_const hηc.isCompact.measure_lt_top.ne)
  have hq0 (x : EuclideanSpace ℝ (Fin n)) : 0 ≤ q x :=
    Set.indicator_nonneg (fun _ _ => zero_le_one) x
  let J : ℝ := ∫ x, q x
  have hJ : 0 ≤ J := integral_nonneg hq0
  let I : ℝ :=
    ∫ x, |η x + (((hessianMatrix u x)⁻¹ * hessianMatrix η x).trace -
      fderiv ℝ V (gradient u x) (gradient η x))| * Real.exp (-u x)
  let A : ℝ := |2 * K ^ 2 * D * I| * ‖v‖ ^ 2
  let B : ℝ := ((G : ℝ) * (L : ℝ) * ‖v‖) ^ 2
  have hA : 0 ≤ A := mul_nonneg (abs_nonneg _) (sq_nonneg _)
  have hB : 0 ≤ B := sq_nonneg _
  let e : ℝ → EuclideanSpace ℝ (Fin n) → ℝ := fun t x =>
    η x *
      ((∑ k, ∑ l,
          (hessianMatrix u (x + t • v) - hessianMatrix u x) k l ^ 2) +
        ∑ k, ∑ l,
          (hessianMatrix u (x - t • v) - hessianMatrix u x) k l ^ 2) *
      Real.exp (-u x)
  have heint (t : ℝ) :
      Integrable (e t) (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    integrable_hessian_increment_energy hu.continuous hG hη.continuous hηc (t • v)
  have hebound (t : ℝ) : (∫ x, e t x) ≤ A * t ^ 2 := by
    have hh :=
      integral_mul_hessian_increment_le hu hconv hG hV hVc hF hK hdata
        hη2 hηc hη0 (t • v) (fun x => hw x (t • v))
    calc
      (∫ x, e t x) ≤ 2 * K ^ 2 * (D * ‖t • v‖ ^ 2) * I := hh
      _ = (2 * K ^ 2 * D * I) * ‖v‖ ^ 2 * t ^ 2 := by
        rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
        ring
      _ ≤ |2 * K ^ 2 * D * I| * ‖v‖ ^ 2 * t ^ 2 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg _))
          (sq_nonneg _)
      _ = A * t ^ 2 := rfl
  have henvelope (t : ℝ) (ht : |t| ≤ 1) (x : EuclideanSpace ℝ (Fin n)) :
      χ (x + t • v) ^ 2 ≤ η x * Real.exp (-u x) := by
    calc
      χ (x + t • v) ^ 2 =
          (χ (x + t • v) ^ 2 * Real.exp (u x)) * Real.exp (-u x) := by
        rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
      _ ≤ η x * Real.exp (-u x) :=
        mul_le_mul_of_nonneg_right (hmajor t ht x) (Real.exp_pos _).le
  have hvanish (t : ℝ) (ht : |t| ≤ 1)
      (x : EuclideanSpace ℝ (Fin n)) (hx : x ∉ tsupport η) :
      χ (x + t • v) = 0 := by
    have hh := henvelope t ht x
    rw [image_eq_zero_of_notMem_tsupport hx, zero_mul] at hh
    exact sq_eq_zero_iff.mp (le_antisymm hh (sq_nonneg _))
  have hf : MemLp (fun x => χ x * H x) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    memLp_cutoff_mul_hessianMatrix_entry hG i j hχ.continuous hχc
  refine ⟨2 * A + 2 * B * J, ?_, ?_⟩
  · positivity
  · intro t _ht0 ht
    have htranslated : MemLp (fun x => χ (x + t • v) * H (x + t • v)) 2
        (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
      hf.comp_measurePreserving (measurePreserving_add_right volume (t • v))
    have hdiff : MemLp
        (fun x => χ (x + t • v) * H (x + t • v) - χ x * H x) 2
        (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
      htranslated.sub hf
    have hdiffint : Integrable
        (fun x => (χ (x + t • v) * H (x + t • v) - χ x * H x) ^ 2)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
      simpa only [pow_two, Pi.mul_def] using hdiff.integrable_mul hdiff
    have hpoint (x : EuclideanSpace ℝ (Fin n)) :
        (χ (x + t • v) * H (x + t • v) - χ x * H x) ^ 2 ≤
          2 * e t x + (2 * B * t ^ 2) * q x := by
      let a : ℝ := χ (x + t • v) * (H (x + t • v) - H x)
      let b : ℝ := H x * (χ (x + t • v) - χ x)
      have ha : a ^ 2 ≤ e t x := by
        have hentry :=
          n11d3_entry_sq_le_total
            (hessianMatrix u (x + t • v) - hessianMatrix u x)
            (hessianMatrix u (x - t • v) - hessianMatrix u x) i j
        change (H (x + t • v) - H x) ^ 2 ≤ _ at hentry
        calc
          a ^ 2 =
              χ (x + t • v) ^ 2 * (H (x + t • v) - H x) ^ 2 := by
            dsimp only [a]
            ring
          _ ≤ (η x * Real.exp (-u x)) *
              ((∑ k, ∑ l,
                  (hessianMatrix u (x + t • v) - hessianMatrix u x) k l ^ 2) +
                ∑ k, ∑ l,
                  (hessianMatrix u (x - t • v) - hessianMatrix u x) k l ^ 2) :=
            mul_le_mul (henvelope t ht x) hentry (sq_nonneg _)
              (mul_nonneg (hη0 x) (Real.exp_pos _).le)
          _ = e t x := by
            dsimp only [e]
            ring
      have hb : b ^ 2 ≤ (B * t ^ 2) * q x := by
        by_cases hx : x ∈ tsupport η
        · have hqx : q x = 1 := Set.indicator_of_mem hx _
          rw [hqx, mul_one]
          have hH : H x ^ 2 ≤ (G : ℝ) ^ 2 := by
            have hh := pow_le_pow_left₀ (norm_nonneg (H x))
              (norm_hessianMatrix_entry_le_of_lipschitz_gradient hG x i j) 2
            simpa only [Real.norm_eq_abs, sq_abs] using hh
          have hcut :
              (χ (x + t • v) - χ x) ^ 2 ≤
                (L : ℝ) ^ 2 * t ^ 2 * ‖v‖ ^ 2 := by
            have hh := hL.norm_sub_le (x + t • v) x
            rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs] at hh
            have hs := pow_le_pow_left₀
              (norm_nonneg (χ (x + t • v) - χ x)) hh 2
            calc
              (χ (x + t • v) - χ x) ^ 2 =
                  ‖χ (x + t • v) - χ x‖ ^ 2 := by
                rw [Real.norm_eq_abs, sq_abs]
              _ ≤ ((L : ℝ) * (|t| * ‖v‖)) ^ 2 := hs
              _ = (L : ℝ) ^ 2 * t ^ 2 * ‖v‖ ^ 2 := by
                simp only [mul_pow, sq_abs]
                ring
          calc
            b ^ 2 = H x ^ 2 * (χ (x + t • v) - χ x) ^ 2 := by
              dsimp only [b]
              ring
            _ ≤ (G : ℝ) ^ 2 * ((L : ℝ) ^ 2 * t ^ 2 * ‖v‖ ^ 2) :=
              mul_le_mul hH hcut (sq_nonneg _) (sq_nonneg _)
            _ = B * t ^ 2 := by
              dsimp only [B]
              ring
        · have hqx : q x = 0 := Set.indicator_of_notMem hx _
          have hχt : χ (x + t • v) = 0 := hvanish t ht x hx
          have hχ0 : χ x = 0 := by
            simpa only [zero_smul, add_zero] using
              hvanish 0 (by norm_num) x hx
          have hb0 : b = 0 := by
            dsimp only [b]
            rw [hχt, hχ0]
            ring
          rw [hb0, hqx]
          norm_num
      have hsplit :
          χ (x + t • v) * H (x + t • v) - χ x * H x = a + b := by
        dsimp only [a, b]
        ring
      calc
        (χ (x + t • v) * H (x + t • v) - χ x * H x) ^ 2 =
            (a + b) ^ 2 := congrArg (fun z : ℝ => z ^ 2) hsplit
        _ ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
          nlinarith [sq_nonneg (a - b)]
        _ ≤ 2 * e t x + (2 * B * t ^ 2) * q x := by
          nlinarith [ha, hb]
    calc
      (∫ x, (χ (x + t • v) * hessianMatrix u (x + t • v) i j -
          χ x * hessianMatrix u x i j) ^ 2) ≤
          ∫ x, 2 * e t x + (2 * B * t ^ 2) * q x :=
        integral_mono hdiffint
          (((heint t).const_mul 2).add (hqint.const_mul (2 * B * t ^ 2)))
          hpoint
      _ = 2 * (∫ x, e t x) + (2 * B * t ^ 2) * J := by
        rw [integral_add ((heint t).const_mul 2)
          (hqint.const_mul (2 * B * t ^ 2)),
          integral_const_mul, integral_const_mul]
      _ ≤ 2 * (A * t ^ 2) + (2 * B * t ^ 2) * J := by
        have hscaled : 2 * (∫ x, e t x) ≤ 2 * (A * t ^ 2) :=
          mul_le_mul_of_nonneg_left (hebound t) (by norm_num : (0 : ℝ) ≤ 2)
        exact add_le_add hscaled (le_refl ((2 * B * t ^ 2) * J))
      _ = (2 * A + 2 * B * J) * t ^ 2 := by ring

end FunctionalInequalities.Analysis
