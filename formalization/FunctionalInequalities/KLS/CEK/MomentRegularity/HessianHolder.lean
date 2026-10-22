import FunctionalInequalities.KLS.CEK.MomentRegularity.WeakHessian
import FunctionalInequalities.Analysis.WeakDerivative.Harnack
import FunctionalInequalities.Analysis.Matrix.LogDetOscillation
import FunctionalInequalities.Analysis.Matrix.RankOneFrame
import FunctionalInequalities.Analysis.Matrix.Holder
import FunctionalInequalities.Analysis.EssentialOscillation
import FunctionalInequalities.Analysis.HolderRepresentative
import FunctionalInequalities.Analysis.HessianRegularity

/-!
# Regular moment potentials with Hölder Hessian

At the regular moment potential `u` of `exists_regular_moment_directional_hessian_subsolution` (smooth `κ`-uniformly convex `W`,
compact convex `K` with nonempty interior, normalized isotropic `1_K e^{−W}` law; Letwin, arXiv:2607.24164v1, Lemma 2.2 support):
the essential weak Harnack law for the directional Hessian deficits, their essential oscillation decay in a fixed frame,
power decay, Hölder representatives of every Hessian entry, one continuous representative, `C²`, and the everywhere
log-determinant equation. The method is the rough-divergence form of Gilbarg–Trudinger (2001), Lemmas 17.13/17.14 and 8.23.
All steps use the same `u`. The public result is `exists_regular_moment_potential_holder_hessian`. Not full Schauder/`C^∞` regularity
and not the merely convex Lemma 2.2.
-/

/-! ## The same regular moment potential -/

noncomputable section RegularMomentHolderHessian

open MeasureTheory Set Metric Matrix
open scoped ContDiff ENNReal NNReal

namespace FunctionalInequalities.Analysis

open FunctionalInequalities FunctionalInequalities.Probability.Stein

section SameWitness
variable {n : ℕ} (hn : 0 < n) {K : Set (EuclideanSpace ℝ (Fin n))} {W : EuclideanSpace ℝ (Fin n) → ℝ} {κ : ℝ}
  (hκ : 0 < κ) (hK : IsCompact K) (hKc : Convex ℝ K) (hKint : (interior K).Nonempty) (hW : ContDiff ℝ ∞ W)
  (hstrong : ConvexOn ℝ univ (fun y => W y - (κ / 2) * ‖y‖ ^ 2))
  (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hμ : (μ : Measure (EuclideanSpace ℝ (Fin n))) =
    (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
      (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p))))
  (hiso : KLS.Isotropic μ)
include hn hκ hK hKc hKint hW hstrong hμ hiso

/-- One regular moment potential `u` with all its regular-class data, and the essential weak Harnack law of
Gilbarg–Trudinger (2001), Theorem 8.18 (bounded symmetric case), for every directional Hessian deficit at that `u`. For
every compact `S` the coefficients `α, β, B` and constants `C(p)` are chosen before every center, radius, direction and cap.
This is the given-data application of `bounded_weak_harnack_of_given_data` to the CEK weak Hessian producer. -/
private theorem given_data_harnack_regular_moment_potential :
    ∃ (u : EuclideanSpace ℝ (Fin n) → ℝ) (L LF : NNReal)
        (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ),
      ConvexOn ℝ univ u ∧ LipschitzWith L u ∧
      (∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 1 ∧
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
        (μ : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ContDiff ℝ 1 u ∧ LipschitzWith (Real.toNNReal (16 / κ)) (gradient u) ∧
      LipschitzWith LF (fun x => -u x + W (gradient u x)) ∧
      (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        (hessianMatrix u x).PosDef ∧
        Real.log (hessianMatrix u x).det = -u x + W (gradient u x) ∧
        ((16 / κ) • (1 : Matrix (Fin n) (Fin n) ℝ) - hessianMatrix u x).PosSemidef) ∧
      (∀ k i j,
        HasWeakDerivAlong (fun x => hessianMatrix u x i j) (fun x => T x k i j)
            (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
          ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
            MemLp (fun x => T x k i j) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
      ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        ∃ α β B : ℝ, 0 < α ∧ 0 < β ∧ 0 ≤ B ∧
        (∀ x ∈ S, Real.exp (-u x) ≤ B) ∧
        (∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S),
          (Real.exp (-u x) • (hessianMatrix u x)⁻¹ - α • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef ∧
          (β • (1 : Matrix (Fin n) (Fin n) ℝ) - Real.exp (-u x) • (hessianMatrix u x)⁻¹).PosSemidef) ∧
        ∃ C : ℝ → ℝ,
          (∀ p : ℝ, 0 < p → (n ≤ 2 ∨ p < (n:ℝ)/((n:ℝ)-2)) → 0 < C p) ∧
          ∀ (x0 : EuclideanSpace ℝ (Fin n)) (R : ℝ), 0 < R → closedBall x0 (4*R) ⊆ S →
          ∀ (v : Fin n → ℝ) (M : ℝ), 0 ≤ M →
            (∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (closedBall x0 (4*R))),
              ∑ i : Fin n, ∑ j : Fin n, v i * v j * hessianMatrix u x i j ≤ M) →
          let w := fun x => M - ∑ i : Fin n, ∑ j : Fin n, v i * v j * hessianMatrix u x i j
          ∀ p : ℝ, 0 < p → (n ≤ 2 ∨ p < (n:ℝ)/((n:ℝ)-2)) →
            (ENNReal.ofReal R)^(-(n:ℝ)/p) * eLpNorm w (ENNReal.ofReal p)
              ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (ball x0 (2*R))) ≤
            ENNReal.ofReal (C p) *
              (essInf (fun x => ENNReal.ofReal (w x))
                ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (ball x0 R)) +
              ENNReal.ofReal (M*B*R^2/α)) := by
  obtain ⟨u, L, LF, T, hold, -, hcoef⟩ :=
    exists_regular_moment_directional_hessian_subsolution hn hκ hK hKc hKint hW hstrong μ hμ hiso
  obtain ⟨hconv, hl, hnorm, hmap, hC1, hG, hF, -, hd, hT, -, hfirst, hInv, -⟩ := hold
  have hdet : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (hessianMatrix u x).det = Real.exp (-u x + W (gradient u x)) := by
    filter_upwards [hd] with x hx
    rw [← hx.2.1, Real.exp_log hx.1.det_pos]
  have hVc : ConvexOn ℝ univ W := by
    have hn' : ConvexOn ℝ univ (fun y : EuclideanSpace ℝ (Fin n) => ‖y‖ ^ 2) :=
      convexOn_univ_norm.pow (fun _ _ => norm_nonneg _) 2
    have hq := hn'.smul (show 0 ≤ κ / 2 by positivity)
    have he : (fun y => W y - κ / 2 * ‖y‖ ^ 2) + (fun y => (κ / 2) • ‖y‖ ^ 2) = W := by
      funext y
      simp only [Pi.add_apply, smul_eq_mul, sub_add_cancel]
    rw [← he]
    exact hstrong.add hq
  have hρc : Continuous fun x => Real.exp (-u x) := Real.continuous_exp.comp hC1.continuous.neg
  have hAm (i j : Fin n) : AEStronglyMeasurable (fun x => (Real.exp (-u x) • (hessianMatrix u x)⁻¹) i j)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    have hLoc : LocallyIntegrable (fun x => (hessianMatrix u x)⁻¹ i j)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
      apply locallyIntegrable_iff.mpr
      intro S hS
      let : IsFiniteMeasure ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) :=
        isFiniteMeasure_restrict.mpr hS.measure_lt_top.ne
      exact ((hInv i i j).2.2 S hS).integrable (by simp)
    change AEStronglyMeasurable (fun x => Real.exp (-u x) * (hessianMatrix u x)⁻¹ i j) volume
    exact hρc.aestronglyMeasurable.mul hLoc.aestronglyMeasurable
  refine ⟨u,L,LF,T,hconv,hl,hnorm,hmap,hC1,hG,hF,hd,hT,fun S hSc => ?_⟩
  -- one choice of `α, β` and of the density bound `B` on `B_4R`
  obtain ⟨c0, c1, hc0, hc1, hcb⟩ := hcoef S hSc
  obtain ⟨Cρ, hCρ⟩ := hSc.exists_bound_of_continuousOn hρc.continuousOn
  have hρB (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ S) :
      Real.exp (-u x) ≤ max Cρ 0 := by
    have h := hCρ x hx
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at h
    exact h.trans (le_max_left _ _)
  obtain ⟨C,hC,hH⟩ := bounded_weak_harnack_of_given_data hn hc0 hc1
  refine ⟨c0,c1,max Cρ 0,hc0,hc1,le_max_right _ _,hρB,hcb,C,hC,?_⟩
  intro x0 R hR hBallS v M hM0 hcap w p hp hcl
  let a := fun (k : Fin n) x => -(∑ i : Fin n, ∑ j : Fin n, v i * v j * T x k i j)
  let F := M * max Cρ 0
  have hSm : MeasurableSet (Metric.closedBall x0 (4 * R)) := Metric.isClosed_closedBall.measurableSet
  classical
  set hv := fun x => ∑ i : Fin n, ∑ j : Fin n, v i * v j * hessianMatrix u x i j with hhvdef
  -- `0 ≤ h_v` everywhere a.e. (positive Hessian); `h_v ≤ M` only on `B_4R`
  have hv0 : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), 0 ≤ hv x := by
    filter_upwards [hd] with x hx
    have h0 := hx.1.posSemidef.dotProduct_mulVec_nonneg v
    simp only [star_trivial] at h0
    have hquad : dotProduct v ((hessianMatrix u x).mulVec v) =
        ∑ i : Fin n, ∑ j : Fin n, v i * v j * hessianMatrix u x i j := by
      simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [hquad] at h0
    exact h0
  have hcap' : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      x ∈ Metric.closedBall x0 (4 * R) → hv x ≤ M :=
    (ae_restrict_iff' hSm).1 hcap
  have hw0S : ∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (Metric.closedBall x0 (4 * R))),
      0 ≤ w x := hcap.mono fun x hx => by simp only [w]; linarith
  -- weak data of `w` from the weak Hessian tensor
  have hsum (k : Fin n) := hasWeakDerivAlong_finsetSum_mul (Finset.univ : Finset (Fin n × Fin n))
    (fun p => v p.1 * v p.2) (f := fun p x => hessianMatrix u x p.1 p.2) (df := fun p x => T x k p.1 p.2)
    (v := EuclideanSpace.basisFun (Fin n) ℝ k) (fun p _ => (hT k p.1 p.2).1) (fun p _ => (hT k p.1 p.2).2)
  have hhv (k : Fin n) : HasWeakDerivAlong hv (fun x => ∑ i : Fin n, ∑ j : Fin n, v i * v j * T x k i j)
      (EuclideanSpace.basisFun (Fin n) ℝ k) :=
    (hsum k).1.congr_ae (ae_of_all _ fun x => by simp only [hv, Fintype.sum_prod_type])
      (ae_of_all _ fun x => by simp only [Fintype.sum_prod_type])
  have htv2 (k : Fin n) : ∀ S' : Set (EuclideanSpace ℝ (Fin n)), IsCompact S' →
      MemLp (fun x => ∑ i : Fin n, ∑ j : Fin n, v i * v j * T x k i j) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S') := by
    intro S' hS'
    have h := (hsum k).2 S' hS'
    simpa only [Fintype.sum_prod_type] using h
  have hwweak (k : Fin n) : HasWeakDerivAlong w (a k) (EuclideanSpace.basisFun (Fin n) ℝ k) :=
    ((hhv k).const_add_mul M (-1)).congr_ae
      (ae_of_all _ fun x => by simp only [w, hv]; ring) (ae_of_all _ fun x => by simp only [a]; ring)
  have ha2 (k : Fin n) : ∀ S' : Set (EuclideanSpace ℝ (Fin n)), IsCompact S' →
      MemLp (a k) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S') :=
    fun S' hS' => (htv2 k S' hS').neg
  -- the global Hessian cap bounds `w` everywhere, also where it is negative
  set Hb : ℝ := ∑ i : Fin n, ∑ j : Fin n, ‖v i * v j‖ * ((Real.toNNReal (16 / κ) : NNReal) : ℝ)
  have hvb (x : EuclideanSpace ℝ (Fin n)) : ‖hv x‖ ≤ Hb := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => (norm_sum_le _ _).trans
      (Finset.sum_le_sum fun j _ => ?_))
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_hessianMatrix_entry_le_of_lipschitz_gradient hG x i j) (norm_nonneg _)
  have hwb (x : EuclideanSpace ℝ (Fin n)) : ‖w x‖ ≤ ‖M‖ + Hb :=
    (norm_sub_le _ _).trans (by linarith [hvb x])
  have hwl : LocallyIntegrable w (volume : Measure (EuclideanSpace ℝ (Fin n))) := (hwweak ⟨0, hn⟩).1
  have hF0 : 0 ≤ F := mul_nonneg hM0 (le_max_right _ _)
  -- the weak supersolution inequality with the LOCAL forcing `F = M B`, for every cutoff in `B_4R`
  have hsub
      (η : EuclideanSpace ℝ (Fin n) → ℝ) (dη : Fin n → EuclideanSpace ℝ (Fin n) → ℝ)
      (hηl : LocallyIntegrable η (volume : Measure (EuclideanSpace ℝ (Fin n))))
      (hηb : ∃ Bη : ℝ, 0 ≤ Bη ∧ ∀ x, ‖η x‖ ≤ Bη) (hηc : HasCompactSupport η)
      (hηs : Function.support η ⊆ Metric.closedBall x0 (4 * R)) (hη0 : ∀ x, 0 ≤ η x)
      (hηd : ∀ k : Fin n, HasWeakDerivAlong η (dη k) (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        HasCompactSupport (dη k) ∧ Function.support (dη k) ⊆ Metric.closedBall x0 (4 * R) ∧
        MemLp (dη k) 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
      -F * (∫ x, η x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) ≤
        ∫ x, dotProduct (fun k => a k x) (((fun x => Real.exp (-u x) • (hessianMatrix u x)⁻¹) x).mulVec
          (fun k => dη k x)) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    obtain ⟨Bη, -, hBη⟩ := hηb
    obtain ⟨h1, h2, h3⟩ := integral_directional_hessian_flux_le_of_bounded_weak_test hC1 hl hG
      (hW.of_le (WithTop.coe_le_coe.mpr le_top)) hF hdet T hT hInv (fun i => (hfirst i).2.2.2.2) hVc
      (hd.mono fun x hx => hx.1) v hηl hBη hηc (fun k => (hηd k).1) (fun k => (hηd k).2.1) (fun k => (hηd k).2.2.2)
      (ae_of_all _ hη0)
    have hηint : Integrable η (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
      (integrableOn_iff_integrable_of_support_subset (subset_tsupport η)).1 (hηl.integrableOn_isCompact hηc)
    have hL : (fun x => dotProduct (fun k => a k x)
        (((fun x => Real.exp (-u x) • (hessianMatrix u x)⁻¹) x).mulVec (fun k => dη k x))) =
        fun x => -(Real.exp (-u x) * (∑ k : Fin n,
          (∑ b : Fin n, (hessianMatrix u x)⁻¹ b k *
            (∑ i : Fin n, ∑ j : Fin n, v i * v j * T x b i j)) * dη k x)) := by
      funext x
      simp only [dotProduct, Matrix.mulVec, a, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul,
        neg_mul, Finset.sum_neg_distrib, neg_inj]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun b _ =>
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [hL, integral_neg]
    have hR' : (∫ x, Real.exp (-u x) * (∑ i : Fin n, ∑ j : Fin n, v i * v j * hessianMatrix u x i j) * η x
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) ≤ ∫ x, (M * max Cρ 0) * η x ∂volume := by
      refine integral_mono_ae h2 (hηint.const_mul _) ?_
      filter_upwards [hv0, hcap'] with x hx0 hxc
      by_cases hxs : x ∈ Metric.closedBall x0 (4 * R)
      · have hh : Real.exp (-u x) * hv x ≤ M * max Cρ 0 := by
          calc Real.exp (-u x) * hv x ≤ max Cρ 0 * M :=
                mul_le_mul (hρB x (hBallS hxs)) (hxc hxs) hx0 (le_max_right _ _)
            _ = M * max Cρ 0 := mul_comm _ _
        exact mul_le_mul_of_nonneg_right hh (hη0 x)
      · have h0 : η x = 0 := by
          by_contra h; exact hxs (hηs h)
        simp only [h0, mul_zero, le_refl]
    rw [integral_const_mul] at hR'
    change -(M * max Cρ 0) * _ ≤ _
    linarith
  have hCb : 0 ≤ ‖M‖ + Hb := (norm_nonneg (w 0)).trans (hwb 0)
  exact hH x0 R hR (fun x => Real.exp (-u x) • (hessianMatrix u x)⁻¹) w a F
    hwl ⟨_,hCb,hwb⟩ hwweak ha2 hAm hw0S
    (ae_restrict_of_ae_restrict_of_subset hBallS hcb) hF0 hsub p hp hcl

/-- At the same regular moment potential: for every compact `S`, a fixed frame (coordinates and normalized pairs) and
`0 < θ < 1`, `C > 0` with the essential oscillation decay of its Hessian directions on balls `B̄(x0,4R) ⊆ S`. -/
private theorem regular_moment_hessian_essential_oscillation :
    ∃ (u : EuclideanSpace ℝ (Fin n) → ℝ) (L LF : NNReal)
        (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ),
      ConvexOn ℝ univ u ∧ LipschitzWith L u ∧
      (∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 1 ∧
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
        (μ : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ContDiff ℝ 1 u ∧ LipschitzWith (Real.toNNReal (16 / κ)) (gradient u) ∧
      LipschitzWith LF (fun x => -u x + W (gradient u x)) ∧
      (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        (hessianMatrix u x).PosDef ∧
        Real.log (hessianMatrix u x).det = -u x + W (gradient u x) ∧
        ((16 / κ) • (1 : Matrix (Fin n) (Fin n) ℝ) - hessianMatrix u x).PosSemidef) ∧
      (∀ k i j,
        HasWeakDerivAlong (fun x => hessianMatrix u x i j) (fun x => T x k i j)
            (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
          ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
            MemLp (fun x => T x k i j) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
      ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        ∃ α β B : ℝ, 0 < α ∧ 0 < β ∧ 0 ≤ B ∧
        (∀ x ∈ S, Real.exp (-u x) ≤ B) ∧
        (∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S),
          (Real.exp (-u x) • (hessianMatrix u x)⁻¹ - α • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef ∧
          (β • (1 : Matrix (Fin n) (Fin n) ℝ) - Real.exp (-u x) • (hessianMatrix u x)⁻¹).PosSemidef) ∧
        ∃ (N : ℕ) (γ : Fin N → Fin n → ℝ) (θ C : ℝ),
          (∀ k, ∑ i : Fin n, (γ k i)^2 = 1) ∧
          (∀ i : Fin n, ∃ k : Fin N, γ k = Pi.single i 1) ∧
          (∀ i j : Fin n, i ≠ j → ∃ k : Fin N,
            γ k = fun a => ((Pi.single i (1:ℝ) : Fin n → ℝ) a + (Pi.single j (1:ℝ) : Fin n → ℝ) a)/Real.sqrt 2) ∧
          0 < θ ∧ θ < 1 ∧ 0 < C ∧
          ∀ (x0 : EuclideanSpace ℝ (Fin n)) (R : ℝ), 0 < R → closedBall x0 (4*R) ⊆ S →
            let q := fun k x => ∑ i : Fin n, ∑ j : Fin n, γ k i*γ k j*hessianMatrix u x i j
            (∑ k, (essSup (q k) ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (ball x0 R))-
              essInf (q k) ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (ball x0 R)))) ≤
            θ*(∑ k, (essSup (q k) ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (ball x0 (4*R)))-
              essInf (q k) ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (ball x0 (4*R)))))+C*(R+R^2) := by
  obtain ⟨u,L,LF,T,hconv,hl,hnorm,hmap,hC1,hG,hF,hd,hT,hS⟩ :=
    given_data_harnack_regular_moment_potential hn hκ hK hKc hKint hW hstrong μ hμ hiso
  refine ⟨u,L,LF,T,hconv,hl,hnorm,hmap,hC1,hG,hF,hd,hT,fun S hSc => ?_⟩
  obtain ⟨α,β,B,hα,hβ,hB,hρB,hA,Ch,hCh,hH⟩ := hS S hSc
  let hi : ℝ := α+β+1
  have hαhi : α < hi := by dsimp only [hi]; linarith
  have hhi : 0 < hi := hα.trans hαhi
  obtain ⟨N,γ,lc,hlc,-,hγ,hcoord,hpair,hframe⟩ :=
    exists_uniform_positive_rank_one_frame hn hα hαhi
  have hA' : ∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S),
      (Real.exp (-u x) • (hessianMatrix u x)⁻¹-α • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef ∧
      (hi • (1 : Matrix (Fin n) (Fin n) ℝ)-Real.exp (-u x) • (hessianMatrix u x)⁻¹).PosSemidef := by
    filter_upwards [hA] with x hx
    refine ⟨hx.1,?_⟩
    have hgap : 0 ≤ hi-β := by dsimp only [hi]; linarith
    have he : hi • (1 : Matrix (Fin n) (Fin n) ℝ)-Real.exp (-u x) • (hessianMatrix u x)⁻¹ =
        (hi-β) • (1 : Matrix (Fin n) (Fin n) ℝ)+
          (β • (1 : Matrix (Fin n) (Fin n) ℝ)-Real.exp (-u x) • (hessianMatrix u x)⁻¹) := by
      rw [sub_smul]
      abel
    rw [he]
    exact (Matrix.PosSemidef.one.smul hgap).add hx.2
  have hcrit : n ≤ 2 ∨ (1:ℝ) < (n:ℝ)/((n:ℝ)-2) := by
    by_cases h2 : n ≤ 2
    · exact Or.inl h2
    · right
      have hn2 : (2:ℝ) < n := by exact_mod_cast (by omega : 2 < n)
      exact (lt_div_iff₀ (by linarith : 0 < (n:ℝ)-2)).2 (by linarith)
  have hCh1 : 0 ≤ Ch 1 := (hCh 1 one_pos hcrit).le
  have hPl (i j : Fin n) : LocallyIntegrable (fun x => hessianMatrix u x i j)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := (hT ⟨0,hn⟩ i j).1.1
  have hPD : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (hessianMatrix u x).PosDef ∧
      ((16/κ) • (1 : Matrix (Fin n) (Fin n) ℝ)-hessianMatrix u x).PosSemidef ∧
      Real.log (hessianMatrix u x).det = -u x+W (gradient u x) :=
    hd.mono fun _ hx => ⟨hx.1,hx.2.2,hx.2.1⟩
  obtain ⟨θ,C,hθ,hθ1,hC,hOsc⟩ := oscillation_of_fixed_frame_and_essential_harnack
    (fun x => hessianMatrix u x) (fun x => -u x+W (gradient u x)) (fun x => Real.exp (-u x)) LF S
    (by positivity : 0 ≤ 16/κ) hα hB hlc hhi.le hCh1 hPl (fun x => (Real.exp_pos _).le)
    hρB hF hPD hA' γ hγ hframe (fun x0 R hR hBS k M hM hcap => by
      have HH := hH x0 R hR hBS (γ k) M hM hcap 1 one_pos hcrit
      simpa only [div_one,ENNReal.ofReal_one] using HH)
  exact ⟨α,β,B,hα,hβ,hB,hρB,hA,N,γ,θ,C,hγ,hcoord,hpair,hθ,hθ1,hC,hOsc⟩

/-- At the same regular moment potential: for every `s > 0`, a fixed frame and `η, Q`, chosen before every center in
`B̄(0,s)` and every radius in `(0,1]`, bounding the summed essential widths of the Hessian directions by `Q r^η`. -/
private theorem regular_moment_hessian_power_oscillation :
    ∃ (u : EuclideanSpace ℝ (Fin n) → ℝ) (L LF : NNReal)
        (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ),
      ConvexOn ℝ univ u ∧ LipschitzWith L u ∧
      (∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 1 ∧
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
        (μ : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ContDiff ℝ 1 u ∧ LipschitzWith (Real.toNNReal (16 / κ)) (gradient u) ∧
      LipschitzWith LF (fun x => -u x + W (gradient u x)) ∧
      (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        (hessianMatrix u x).PosDef ∧
        Real.log (hessianMatrix u x).det = -u x + W (gradient u x) ∧
        ((16 / κ) • (1 : Matrix (Fin n) (Fin n) ℝ) - hessianMatrix u x).PosSemidef) ∧
      (∀ k i j,
        HasWeakDerivAlong (fun x => hessianMatrix u x i j) (fun x => T x k i j)
            (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
          ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
            MemLp (fun x => T x k i j) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
      ∀ s : ℝ, 0 < s →
        ∃ (N : ℕ) (γ : Fin N → Fin n → ℝ) (η Q : ℝ),
          (∀ k, ∑ i : Fin n, (γ k i)^2 = 1) ∧
          (∀ i : Fin n, ∃ k : Fin N, γ k = Pi.single i 1) ∧
          (∀ i j : Fin n, i ≠ j → ∃ k : Fin N,
            γ k = fun a => ((Pi.single i (1:ℝ) : Fin n → ℝ) a + (Pi.single j (1:ℝ) : Fin n → ℝ) a)/Real.sqrt 2) ∧
          0 < η ∧ η < 1 ∧ 0 < Q ∧
          let q := fun k x => ∑ i : Fin n, ∑ j : Fin n, γ k i*γ k j*hessianMatrix u x i j
          ∀ x0 ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) s, ∀ r ∈ Ioc (0:ℝ) 1,
            (∑ k, (essSup (q k) ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (ball x0 r))-
              essInf (q k) ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (ball x0 r)))) ≤ Q*r^η := by
  obtain ⟨u,L,LF,T,hconv,hl,hnorm,hmap,hC1,hG,hF,hd,hT,hS⟩ :=
    regular_moment_hessian_essential_oscillation hn hκ hK hKc hKint hW hstrong μ hμ hiso
  refine ⟨u,L,LF,T,hconv,hl,hnorm,hmap,hC1,hG,hF,hd,hT,fun s _hs => ?_⟩
  obtain ⟨_α,_β,_B,_hα,_hβ,_hB,_hρB,_hA,N,γ,θ,C,hγ,hcoord,hpair,hθ,hθ1,hC,hOsc⟩ :=
    hS (closedBall (0 : EuclideanSpace ℝ (Fin n)) (s+4)) (isCompact_closedBall _ _)
  let q := fun k x => ∑ i : Fin n, ∑ j : Fin n, γ k i*γ k j*hessianMatrix u x i j
  have hqb (k : Fin N) : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), 0 ≤ q k x ∧ q k x ≤ 16/κ := by
    filter_upwards [hd] with x hx
    exact unit_quadratic_bounds (hessianMatrix u x) (γ k) hx.1.posSemidef hx.2.2 (hγ k)
  obtain ⟨η,Q,hη,hη1,hQ,hPow⟩ := essential_width_power_of_quarter_contraction q
    (closedBall (0 : EuclideanSpace ℝ (Fin n)) s) (by positivity : 0 ≤ 16/κ) hθ hθ1 hC
    (fun k => (hqb k).mono fun _ hx => hx.1) (fun k => (hqb k).mono fun _ hx => hx.2) (fun x0 hx0 r hr => by
      have hn0 : ‖x0‖ ≤ s := by simpa only [Metric.mem_closedBall,dist_zero_right] using hx0
      have hBall : closedBall x0 (4*(r/4)) ⊆ closedBall (0 : EuclideanSpace ℝ (Fin n)) (s+4) := by
        intro y hy
        have hyx := Metric.mem_closedBall.mp hy
        have ht := dist_triangle y x0 0
        rw [dist_zero_right x0,dist_zero_right y] at ht
        apply Metric.mem_closedBall.mpr
        rw [dist_zero_right]
        linarith [hr.2]
      let omega := fun t : ℝ => ∑ k, (essSup (q k)
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (ball x0 t))-
        essInf (q k) ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (ball x0 t)))
      change omega ((1/4)*r) ≤ θ*omega r+C*(r+r^2)
      have hh := hOsc x0 (r/4) (div_pos hr.1 (by norm_num : (0:ℝ) < 4)) hBall
      change omega (r/4) ≤ θ*omega (4*(r/4))+C*((r/4)+(r/4)^2) at hh
      rw [show 4*(r/4)=r by ring] at hh
      have herr : C*((r/4)+(r/4)^2) ≤ C*(r+r^2) :=
        mul_le_mul_of_nonneg_left (by nlinarith [hr.1,sq_nonneg r]) hC.le
      rw [show (1/4:ℝ)*r=r/4 by ring]
      exact hh.trans (add_le_add le_rfl herr))
  exact ⟨N,γ,η,Q,hγ,hcoord,hpair,hη,hη1,hQ,hPow⟩

/-- At the same regular moment potential: on every ball `B(0,s)`, continuous Hölder representatives (common `η, C`) of every
frame quadratic form of the Hessian. -/
private theorem regular_moment_hessian_directional_holder :
    ∃ (u : EuclideanSpace ℝ (Fin n) → ℝ) (L LF : NNReal)
        (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ),
      ConvexOn ℝ univ u ∧ LipschitzWith L u ∧
      (∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 1 ∧
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
        (μ : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ContDiff ℝ 1 u ∧ LipschitzWith (Real.toNNReal (16 / κ)) (gradient u) ∧
      LipschitzWith LF (fun x => -u x + W (gradient u x)) ∧
      (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        (hessianMatrix u x).PosDef ∧
        Real.log (hessianMatrix u x).det = -u x + W (gradient u x) ∧
        ((16 / κ) • (1 : Matrix (Fin n) (Fin n) ℝ) - hessianMatrix u x).PosSemidef) ∧
      (∀ k i j,
        HasWeakDerivAlong (fun x => hessianMatrix u x i j) (fun x => T x k i j)
            (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
          ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
            MemLp (fun x => T x k i j) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
      ∀ s : ℝ, 0 < s →
        ∃ (N : ℕ) (γ : Fin N → Fin n → ℝ) (η C : ℝ≥0),
          (∀ k, ∑ i : Fin n, (γ k i)^2 = 1) ∧
          (∀ i : Fin n, ∃ k : Fin N, γ k = Pi.single i 1) ∧
          (∀ i j : Fin n, i ≠ j → ∃ k : Fin N,
            γ k = fun a => ((Pi.single i (1:ℝ) : Fin n → ℝ) a + (Pi.single j (1:ℝ) : Fin n → ℝ) a)/Real.sqrt 2) ∧
          0 < η ∧ η < 1 ∧ 0 < C ∧
          ∀ k : Fin N, ∃ g : (ball (0 : EuclideanSpace ℝ (Fin n)) s) → ℝ,
            HolderWith C η g ∧ Continuous g ∧
            ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (ball 0 s),
              ∀ hx : x ∈ ball (0 : EuclideanSpace ℝ (Fin n)) s,
                g ⟨x,hx⟩ = ∑ i : Fin n, ∑ j : Fin n, γ k i*γ k j*hessianMatrix u x i j := by
  obtain ⟨u,L,LF,T,hconv,hl,hnorm,hmap,hC1,hG,hF,hd,hT,hS⟩ :=
    regular_moment_hessian_power_oscillation hn hκ hK hKc hKint hW hstrong μ hμ hiso
  refine ⟨u,L,LF,T,hconv,hl,hnorm,hmap,hC1,hG,hF,hd,hT,fun s hs => ?_⟩
  obtain ⟨N,γ,η,Q,hγ,hcoord,hpair,hη,hη1,hQ,hPow⟩ := hS s hs
  let q := fun k x => ∑ i : Fin n, ∑ j : Fin n, γ k i*γ k j*hessianMatrix u x i j
  let ηn : ℝ≥0 := ⟨η,hη.le⟩
  have hηn : 0 < ηn := by exact_mod_cast hη
  have hηn1 : ηn < 1 := by exact_mod_cast hη1
  let C : ℝ≥0 := ⟨(Q+16/κ)*2^η,by positivity⟩
  have hC : 0 < C := by change 0 < (Q+16/κ)*2^η; positivity
  have hqb (k : Fin N) : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), 0 ≤ q k x ∧ q k x ≤ 16/κ := by
    filter_upwards [hd] with x hx
    exact unit_quadratic_bounds (hessianMatrix u x) (γ k) hx.1.posSemidef hx.2.2 (hγ k)
  refine ⟨N,γ,ηn,C,hγ,hcoord,hpair,hηn,hηn1,hC,fun k => ?_⟩
  have hOne : ∀ x0 ∈ ball (0 : EuclideanSpace ℝ (Fin n)) s, ∀ r ∈ Ioc (0:ℝ) 1,
      essSup (q k) ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (ball x0 r))-
        essInf (q k) ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (ball x0 r)) ≤ Q*r^(ηn:ℝ) := by
    intro x0 hx0 r hr
    let ν := (volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (ball x0 r)
    let : NeZero ν := ⟨restricted_ball_ne_zero x0 hr.1⟩
    have hnonneg (j : Fin N) : 0 ≤ essSup (q j) ν-essInf (q j) ν := by
      apply sub_nonneg.mpr
      exact (real_essential_bounds ν (q j)
        (ae_restrict_of_ae ((hqb j).mono fun _ hx => hx.1))
        (ae_restrict_of_ae ((hqb j).mono fun _ hx => hx.2))).2.1
    have hsingle := Finset.single_le_sum (f := fun j : Fin N => essSup (q j) ν-essInf (q j) ν)
      (fun j _ => hnonneg j) (Finset.mem_univ k)
    exact hsingle.trans (hPow x0 (ball_subset_closedBall hx0) r hr)
  obtain ⟨Ck,g,hCk,hHg,hgCont,hgAE⟩ := exists_local_holder_representative_of_essential_power
    (volume : Measure (EuclideanSpace ℝ (Fin n))) (q k) (ball 0 s) isOpen_ball hηn hQ.le
    (by positivity : 0 ≤ 16/κ) ((hqb k).mono fun _ hx => hx.1) ((hqb k).mono fun _ hx => hx.2) hOne
  have hCeq : Ck = C := by
    apply Subtype.ext
    exact hCk
  rw [hCeq] at hHg
  exact ⟨g,hHg,hgCont,hgAE⟩

/-- At the same regular moment potential: on every ball `B(0,s)`, continuous Hölder representatives (common `η, C`) of every
Hessian entry. -/
private theorem regular_moment_hessian_entry_holder :
    ∃ (u : EuclideanSpace ℝ (Fin n) → ℝ) (L LF : NNReal)
        (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ),
      ConvexOn ℝ univ u ∧ LipschitzWith L u ∧
      (∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 1 ∧
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
        (μ : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ContDiff ℝ 1 u ∧ LipschitzWith (Real.toNNReal (16 / κ)) (gradient u) ∧
      LipschitzWith LF (fun x => -u x + W (gradient u x)) ∧
      (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        (hessianMatrix u x).PosDef ∧
        Real.log (hessianMatrix u x).det = -u x + W (gradient u x) ∧
        ((16 / κ) • (1 : Matrix (Fin n) (Fin n) ℝ) - hessianMatrix u x).PosSemidef) ∧
      (∀ k i j,
        HasWeakDerivAlong (fun x => hessianMatrix u x i j) (fun x => T x k i j)
            (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
          ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
            MemLp (fun x => T x k i j) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
      ∀ s : ℝ, 0 < s →
        ∃ η C : ℝ≥0, 0 < η ∧ η < 1 ∧ 0 < C ∧
          ∀ i j : Fin n, ∃ g : (ball (0 : EuclideanSpace ℝ (Fin n)) s) → ℝ,
            HolderWith C η g ∧ Continuous g ∧
            ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (ball 0 s),
              ∀ hx : x ∈ ball (0 : EuclideanSpace ℝ (Fin n)) s,
                g ⟨x,hx⟩ = hessianMatrix u x i j := by
  obtain ⟨u,L,LF,T,hconv,hl,hnorm,hmap,hC1,hG,hF,hd,hT,hS⟩ :=
    regular_moment_hessian_directional_holder hn hκ hK hKc hKint hW hstrong μ hμ hiso
  refine ⟨u,L,LF,T,hconv,hl,hnorm,hmap,hC1,hG,hF,hd,hT,fun s hs => ?_⟩
  obtain ⟨N,γ,η,C,_hγ,hcoord,hpair,hη,hη1,hC,hRep⟩ := hS s hs
  have hSym : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (ball 0 s),
      (hessianMatrix u x).IsSymm := ae_restrict_of_ae (hd.mono fun _ hx =>
        Matrix.isHermitian_iff_isSymm.mp hx.1.isHermitian)
  have hEntry := exists_matrix_entry_holder_representatives
    (volume : Measure (EuclideanSpace ℝ (Fin n))) (ball 0 s) (hessianMatrix u) γ hcoord hpair hSym hη
    (fun k => by
      obtain ⟨g,hg,_hgc,hgAE⟩ := hRep k
      exact ⟨g,hg,hgAE⟩)
  exact ⟨η,2*C,hη,hη1,mul_pos (by norm_num) hC,hEntry⟩

/-- At the same regular moment potential: one continuous matrix field equal to the Hessian almost everywhere and locally
Hölder in every entry. -/
private theorem regular_moment_continuous_hessian_representative :
    ∃ (u : EuclideanSpace ℝ (Fin n) → ℝ) (L LF : NNReal)
        (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ),
      ConvexOn ℝ univ u ∧ LipschitzWith L u ∧
      (∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 1 ∧
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
        (μ : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ContDiff ℝ 1 u ∧ LipschitzWith (Real.toNNReal (16 / κ)) (gradient u) ∧
      LipschitzWith LF (fun x => -u x + W (gradient u x)) ∧
      (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        (hessianMatrix u x).PosDef ∧
        Real.log (hessianMatrix u x).det = -u x + W (gradient u x) ∧
        ((16 / κ) • (1 : Matrix (Fin n) (Fin n) ℝ) - hessianMatrix u x).PosSemidef) ∧
      (∀ k i j,
        HasWeakDerivAlong (fun x => hessianMatrix u x i j) (fun x => T x k i j)
            (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
          ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
            MemLp (fun x => T x k i j) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
      ∃ B : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ,
        Continuous B ∧ B =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin n)))] hessianMatrix u ∧
        ∀ s : ℝ, 0 < s → ∃ η C : ℝ≥0, 0 < η ∧ η < 1 ∧ 0 < C ∧
          ∀ i j : Fin n, HolderWith C η
            (fun x : ball (0 : EuclideanSpace ℝ (Fin n)) s => B x.val i j) := by
  classical
  obtain ⟨u,L,LF,T,hconv,hl,hnorm,hmap,hC1,hG,hF,hd,hT,hS⟩ :=
    regular_moment_hessian_entry_holder hn hκ hK hKc hKint hW hstrong μ hμ hiso
  have hNat (m : ℕ) := hS ((m:ℝ)+1) (by positivity)
  choose ηm Cm hηm hηm1 hCm hLoc using hNat
  choose g hgHolder hgCont hgAE using hLoc
  have hGlue (i j : Fin n) := glue_continuous_ae_representatives_on_balls
    (volume : Measure (EuclideanSpace ℝ (Fin n))) (fun x => hessianMatrix u x i j)
    (fun m => g m i j) (fun m => hgCont m i j) (fun m => hgAE m i j)
  choose b hbCont hbAE hbEq using hGlue
  let B := fun x i j => b i j x
  have hBcont : Continuous B := continuous_pi fun i => continuous_pi fun j => hbCont i j
  have hBAE : B =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin n)))] hessianMatrix u := by
    filter_upwards [ae_all_iff.mpr (fun i => ae_all_iff.mpr (fun j => hbAE i j))] with x hx
    ext i j
    exact hx i j
  refine ⟨u,L,LF,T,hconv,hl,hnorm,hmap,hC1,hG,hF,hd,hT,B,hBcont,hBAE,fun s _hs => ?_⟩
  obtain ⟨m,hm⟩ := exists_nat_gt s
  have hms : s < (m:ℝ)+1 := by linarith
  refine ⟨ηm m,Cm m,hηm m,hηm1 m,hCm m,fun i j => ?_⟩
  apply holderWith_of_real_dist_bound
  intro x y
  have hxm : x.val ∈ ball (0 : EuclideanSpace ℝ (Fin n)) ((m:ℝ)+1) :=
    (Metric.mem_ball.mp x.property).trans hms
  have hym : y.val ∈ ball (0 : EuclideanSpace ℝ (Fin n)) ((m:ℝ)+1) :=
    (Metric.mem_ball.mp y.property).trans hms
  change dist (b i j x.val) (b i j y.val) ≤ (Cm m:ℝ)*dist x.val y.val^(ηm m:ℝ)
  rw [hbEq i j m ⟨x.val,hxm⟩,hbEq i j m ⟨y.val,hym⟩]
  exact (hgHolder m i j).dist_le ⟨x.val,hxm⟩ ⟨y.val,hym⟩

/-- At the same regular moment potential: `u` is `C²` and its classical Hessian entries are locally Hölder. -/
private theorem regular_moment_contDiff_two_holder_hessian :
    ∃ (u : EuclideanSpace ℝ (Fin n) → ℝ) (L LF : NNReal)
        (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ),
      ConvexOn ℝ univ u ∧ LipschitzWith L u ∧
      (∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 1 ∧
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
        (μ : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ContDiff ℝ 1 u ∧ LipschitzWith (Real.toNNReal (16 / κ)) (gradient u) ∧
      LipschitzWith LF (fun x => -u x + W (gradient u x)) ∧
      (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        (hessianMatrix u x).PosDef ∧
        Real.log (hessianMatrix u x).det = -u x + W (gradient u x) ∧
        ((16 / κ) • (1 : Matrix (Fin n) (Fin n) ℝ) - hessianMatrix u x).PosSemidef) ∧
      (∀ k i j,
        HasWeakDerivAlong (fun x => hessianMatrix u x i j) (fun x => T x k i j)
            (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
          ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
            MemLp (fun x => T x k i j) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
      ContDiff ℝ 2 u ∧
      ∀ s : ℝ, 0 < s → ∃ η C : ℝ≥0, 0 < η ∧ η < 1 ∧ 0 < C ∧
        ∀ i j : Fin n, HolderWith C η
          (fun x : ball (0 : EuclideanSpace ℝ (Fin n)) s => hessianMatrix u x.val i j) := by
  obtain ⟨u,L,LF,T,hconv,hl,hnorm,hmap,hC1,hG,hF,hd,hT,B,hBcont,hBAE,hLocal⟩ :=
    regular_moment_continuous_hessian_representative hn hκ hK hKc hKint hW hstrong μ hμ hiso
  obtain ⟨hC2,hHess⟩ := contDiff_two_of_continuous_ae_hessian hC1 hG B hBcont hBAE
  refine ⟨u,L,LF,T,hconv,hl,hnorm,hmap,hC1,hG,hF,hd,hT,hC2,?_⟩
  simpa only [hHess] using hLocal

/-- Regular moment potential with Hölder Hessian (support for Letwin, arXiv:2607.24164v1, Lemma 2.2, strong class). Setting:
`n > 0`, smooth `κ`-uniformly convex `W` (`κ > 0`), compact convex `K` with nonempty interior, and the normalized isotropic
law `1_K e^{−W}`. ONE convex potential `u` keeps its original data: Lipschitz bound, `∫ e^{−u} = 1`, `(∇u)_* e^{−u} = μ`,
`C¹` with `16/κ`-Lipschitz gradient, Lipschitz right side, the a.e. positive definite Hessian with `log det = −u + W∘∇u` and
cap `16/κ`, and the weak third derivative `T`. The same `u` is moreover `C²`, its Hessian is continuous, the Hessian is
positive definite with the log-determinant equation and cap at EVERY point, and on every ball `B(0,s)` all Hessian entries
are Hölder with one exponent and constant chosen before the entries. The proof is the rough-divergence form of
Gilbarg–Trudinger (2001), Lemmas 17.13/17.14 and 8.23. It is not full Schauder/`C^∞` regularity nor the merely convex Lemma
2.2. -/
theorem exists_regular_moment_potential_holder_hessian :
    ∃ (u : EuclideanSpace ℝ (Fin n) → ℝ) (L LF : NNReal)
        (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ),
      ConvexOn ℝ univ u ∧ LipschitzWith L u ∧
      (∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 1 ∧
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
        (μ : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ContDiff ℝ 1 u ∧ LipschitzWith (Real.toNNReal (16 / κ)) (gradient u) ∧
      LipschitzWith LF (fun x => -u x + W (gradient u x)) ∧
      (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        (hessianMatrix u x).PosDef ∧
        Real.log (hessianMatrix u x).det = -u x + W (gradient u x) ∧
        ((16 / κ) • (1 : Matrix (Fin n) (Fin n) ℝ) - hessianMatrix u x).PosSemidef) ∧
      (∀ k i j,
        HasWeakDerivAlong (fun x => hessianMatrix u x i j) (fun x => T x k i j)
            (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
          ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
            MemLp (fun x => T x k i j) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
      ContDiff ℝ 2 u ∧ Continuous (hessianMatrix u) ∧
      (∀ x, (hessianMatrix u x).PosDef ∧
        Real.log (hessianMatrix u x).det = -u x + W (gradient u x) ∧
        ((16/κ) • (1 : Matrix (Fin n) (Fin n) ℝ)-hessianMatrix u x).PosSemidef) ∧
      ∀ s : ℝ, 0 < s → ∃ η C : ℝ≥0, 0 < η ∧ η < 1 ∧ 0 < C ∧
        ∀ i j : Fin n, HolderWith C η
          (fun x : ball (0 : EuclideanSpace ℝ (Fin n)) s => hessianMatrix u x.val i j) := by
  obtain ⟨u,L,LF,T,hconv,hl,hnorm,hmap,hC1,hG,hF,hd,hT,B,hBcont,hBAE,hLocal⟩ :=
    regular_moment_continuous_hessian_representative hn hκ hK hKc hKint hW hstrong μ hμ hiso
  obtain ⟨hC2,hHess⟩ := contDiff_two_of_continuous_ae_hessian hC1 hG B hBcont hBAE
  have hHcont : Continuous (hessianMatrix u) := by rw [hHess]; exact hBcont
  have hEvery := everywhere_posDef_logdet_of_continuous_hessian_ae hn
    (by positivity : 0 < 16/κ) hHcont hF.continuous hd
  refine ⟨u,L,LF,T,hconv,hl,hnorm,hmap,hC1,hG,hF,hd,hT,hC2,hHcont,hEvery,?_⟩
  simpa only [hHess] using hLocal

end SameWitness

end FunctionalInequalities.Analysis

end RegularMomentHolderHessian
