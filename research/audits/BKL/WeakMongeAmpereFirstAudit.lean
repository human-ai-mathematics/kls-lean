import FunctionalInequalities.KLS.CEK.MomentRegularity.WeakDerivative

/-!
# Actual-source first weak Monge–Ampère identity

Letwin arXiv:2607.24164v1 (2.4), first derivative only. This client
retains every field of the source-law tensor producer, verifies the new
determinant/logarithmic weak identities, and recovers the original interface.
No C2 regularity or given tensor is supplied. The second evolution identity,
trace-square bound, Brascamp–Lieb and constant-8 conclusions remain open.
-/

noncomputable section
open MeasureTheory Set Matrix Metric
open scoped ContDiff Topology Matrix.Norms.Elementwise
open FunctionalInequalities FunctionalInequalities.Analysis
open FunctionalInequalities.Probability.Stein
namespace WeakMongeAmpereFirstAudit

theorem consumes_all_original_fields_and_first_identity {n : ℕ} (hn : 0 < n)
    {K : Set (EuclideanSpace ℝ (Fin n))} {W : EuclideanSpace ℝ (Fin n) → ℝ}
    {κ : ℝ} (hκ : 0 < κ) (hK : IsCompact K) (hKc : Convex ℝ K)
    (hKint : (interior K).Nonempty) (hW : ContDiff ℝ ∞ W)
    (hstrong : ConvexOn ℝ univ (fun y => W y - (κ / 2) * ‖y‖ ^ 2))
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hμ : (μ : Measure (EuclideanSpace ℝ (Fin n))) =
      (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
        (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p))))
    (hiso : KLS.Isotropic μ) :
    ∃ (u : EuclideanSpace ℝ (Fin n) → ℝ) (L LF : NNReal)
        (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ),
      ConvexOn ℝ univ u ∧ LipschitzWith L u ∧
      (∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 1 ∧
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
        (μ : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ContDiff ℝ 1 u ∧ LipschitzWith (Real.toNNReal (16 / κ)) (gradient u) ∧
      LipschitzWith LF (fun x => -u x + W (gradient u x)) ∧
      (∀ x h, u (x + h) + u (x - h) - 2 * u x ≤ (4 / κ) * ‖h‖ ^ 2) ∧
      (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        (hessianMatrix u x).PosDef ∧
        Real.log (hessianMatrix u x).det = -u x + W (gradient u x) ∧
        ((16 / κ) • (1 : Matrix (Fin n) (Fin n) ℝ) - hessianMatrix u x).PosSemidef) ∧
      (∀ k i j,
        HasWeakDerivAlong (fun x => hessianMatrix u x i j) (fun x => T x k i j)
            (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
          ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
            MemLp (fun x => T x k i j) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
      (∃ LE : NNReal,
        LipschitzWith LE (fun x => Real.exp (-u x + W (gradient u x)))) ∧
      ∀ k : Fin n,
        HasWeakDerivAlong (fun x => (hessianMatrix u x).det)
          (fun x => (hessianMatrix u x).det *
            ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace)
          (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        (∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
          MemLp (fun x => (hessianMatrix u x).det *
            ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace)
            2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
        HasWeakDerivAlong (fun x => Real.log (hessianMatrix u x).det)
          (fun x => ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace)
          (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
          ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace =
            fderiv ℝ (fun y => -u y + W (gradient u y)) x
              (EuclideanSpace.basisFun (Fin n) ℝ k)) ∧
        (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
          ((hessianMatrix u x)⁻¹ * (Matrix.of fun i j => T x k i j)).trace =
            -fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ k) +
              ∑ a : Fin n, hessianMatrix u x k a *
                fderiv ℝ W (gradient u x) (EuclideanSpace.basisFun (Fin n) ℝ a)) := by
  exact exists_regular_moment_weak_first_derivative hn hκ hK hKc hKint hW hstrong μ hμ hiso

theorem forgets_only_new_fields {n : ℕ} (hn : 0 < n)
    {K : Set (EuclideanSpace ℝ (Fin n))} {W : EuclideanSpace ℝ (Fin n) → ℝ}
    {κ : ℝ} (hκ : 0 < κ) (hK : IsCompact K) (hKc : Convex ℝ K)
    (hKint : (interior K).Nonempty) (hW : ContDiff ℝ ∞ W)
    (hstrong : ConvexOn ℝ univ (fun y => W y - (κ / 2) * ‖y‖ ^ 2))
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hμ : (μ : Measure (EuclideanSpace ℝ (Fin n))) =
      (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
        (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p))))
    (hiso : KLS.Isotropic μ) :
    ∃ (u : EuclideanSpace ℝ (Fin n) → ℝ) (L LF : NNReal)
        (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ),
      ConvexOn ℝ univ u ∧ LipschitzWith L u ∧
      (∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 1 ∧
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
        (μ : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ContDiff ℝ 1 u ∧ LipschitzWith (Real.toNNReal (16 / κ)) (gradient u) ∧
      LipschitzWith LF (fun x => -u x + W (gradient u x)) ∧
      (∀ x h, u (x + h) + u (x - h) - 2 * u x ≤ (4 / κ) * ‖h‖ ^ 2) ∧
      (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        (hessianMatrix u x).PosDef ∧
        Real.log (hessianMatrix u x).det = -u x + W (gradient u x) ∧
        ((16 / κ) • (1 : Matrix (Fin n) (Fin n) ℝ) - hessianMatrix u x).PosSemidef) ∧
      ∀ k i j,
        HasWeakDerivAlong (fun x => hessianMatrix u x i j) (fun x => T x k i j)
            (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
          ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
            MemLp (fun x => T x k i j) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
  obtain ⟨u, L, LF, T, hc, hl, hnrm, hm, hC1, hG, hF, hw, hd, hT, _hexp, _hfirst⟩ :=
    exists_regular_moment_weak_first_derivative hn hκ hK hKc hKint hW hstrong μ hμ hiso
  exact ⟨u, L, LF, T, hc, hl, hnrm, hm, hC1, hG, hF, hw, hd, hT⟩

/-- A singular singleton matrix still has a nonzero determinant differential
in a nonzero direction; invertibility cannot be used for the generic identity. -/
theorem singular_singleton_direction (N : Matrix (Fin 1) (Fin 1) ℝ) :
    fderiv ℝ Matrix.det (0 : Matrix (Fin 1) (Fin 1) ℝ) N = N 0 0 := by
  simpa using fderiv_det_eq_sum_permutation (0 : Matrix (Fin 1) (Fin 1) ℝ) N

/-- The empty matrix case is retained. -/
theorem empty_matrix_direction :
    fderiv ℝ Matrix.det (0 : Matrix (Fin 0) (Fin 0) ℝ) 0 = 0 := by
  exact (fderiv_det_eq_sum_permutation (0 : Matrix (Fin 0) (Fin 0) ℝ) 0).trans (by simp)


/-- Negative upper threshold and a genuinely unbounded-below affine-norm exponent. -/
theorem negative_unbounded_exponent :
    LipschitzWith (Real.toNNReal (Real.exp (-2)))
      (fun x : ℝ => Real.exp (-2 - ‖x‖)) := by
  have hn : LipschitzWith 1 (fun x : ℝ => -‖x‖) :=
    (lipschitzWith_one_norm : LipschitzWith 1 (norm : ℝ → ℝ)).neg
  have hf : LipschitzWith 1 (fun x : ℝ => -2 - ‖x‖) := by
    simpa only [sub_eq_add_neg, zero_add] using
      (LipschitzWith.const (-2 : ℝ)).add hn
  have hm : MapsTo (fun x : ℝ => -2 - ‖x‖) univ (Iic (-2)) := by
    intro x _
    change -2 - ‖x‖ ≤ -2
    linarith [norm_nonneg x]
  simpa only [Function.comp_def, mul_one] using!
    lipschitzOnWith_univ.mp ((lipschitzOnWith_exp_Iic (-2)).comp hf.lipschitzOnWith hm)


end WeakMongeAmpereFirstAudit
