import FunctionalInequalities.Analysis.WeakDerivative.Basic
import FunctionalInequalities.Analysis.WeakDerivative.Products
import FunctionalInequalities.KLS.CEK.MomentRegularity.WeakDerivative
import FunctionalInequalities.KLS.BKL.Localization.Process.Basic
noncomputable section
open MeasureTheory Set
open scoped ContDiff Topology
open FunctionalInequalities FunctionalInequalities.Analysis
open FunctionalInequalities.Probability.Stein

namespace WeakHessianProductAudit.Global

/-- Genuine application: the actual normalized regular source law produces
both cut-off Hessian factors and their derivative densities. -/
theorem produced_normalized_cutoff_hessian_product {n : ℕ} (hn : 0 < n)
    {K : Set (EuclideanSpace ℝ (Fin n))} {W : EuclideanSpace ℝ (Fin n) → ℝ}
    {κ : ℝ} (hκ : 0 < κ) (hK : IsCompact K) (hKc : Convex ℝ K)
    (hKint : (interior K).Nonempty) (hW : ContDiff ℝ ∞ W)
    (hstrong : ConvexOn ℝ univ (fun y => W y - (κ / 2) * ‖y‖ ^ 2))
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hμ : (μ : Measure (EuclideanSpace ℝ (Fin n))) =
      (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
        (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p))))
    (hiso : KLS.Isotropic μ)
    {χ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ) :
    ∃ (u : EuclideanSpace ℝ (Fin n) → ℝ)
        (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ),
      (∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 1 ∧
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
        (μ : Measure (EuclideanSpace ℝ (Fin n))) ∧
      LipschitzWith (Real.toNNReal (16 / κ)) (gradient u) ∧
      ∀ k i j a b : Fin n,
        HasWeakDerivAlong
          (fun x => (χ x * hessianMatrix u x i j) * (χ x * hessianMatrix u x a b))
          (fun x =>
            (χ x * T x k i j + fderiv ℝ χ x
              (EuclideanSpace.basisFun (Fin n) ℝ k) * hessianMatrix u x i j) *
                (χ x * hessianMatrix u x a b) +
            (χ x * hessianMatrix u x i j) *
              (χ x * T x k a b + fderiv ℝ χ x
                (EuclideanSpace.basisFun (Fin n) ℝ k) * hessianMatrix u x a b))
          (EuclideanSpace.basisFun (Fin n) ℝ k) := by
  obtain ⟨u, _L, _LF, T, _hconv, _hLip, hnorm, hmap, _hC1, hG,
      _hF, _hw, _hdata, hT⟩ :=
    exists_regular_moment_weak_tensor hn hκ hK hKc hKint hW hstrong μ hμ hiso
  refine ⟨u, T, hnorm, hmap, hG, ?_⟩
  intro k i j a b
  have hχd : Continuous (fun x => fderiv ℝ χ x
      (EuclideanSpace.basisFun (Fin n) ℝ k)) :=
    (hχ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hχdc : HasCompactSupport (fun x => fderiv ℝ χ x
      (EuclideanSpace.basisFun (Fin n) ℝ k)) := by
    change HasCompactSupport ((fun A : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ =>
      A (EuclideanSpace.basisFun (Fin n) ℝ k)) ∘ fderiv ℝ χ)
    exact (hχc.fderiv ℝ).comp_left (by simp)
  have hfactor (r s : Fin n) :=
    Probability.Stein.memLp_cutoff_mul_hessianMatrix_entry hG r s hχ.continuous hχc
  have hdensity (r s : Fin n) : MemLp
      (fun x => χ x * T x k r s + fderiv ℝ χ x
        (EuclideanSpace.basisFun (Fin n) ℝ k) * hessianMatrix u x r s) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    (memLp_mul_of_hasCompactSupport hχ.continuous hχc (hT k r s).2).add
      (Probability.Stein.memLp_cutoff_mul_hessianMatrix_entry hG r s hχd hχdc)
  exact ((hT k i j).1.mul_contDiff hχ hχc).mul_of_memLp_two
    ((hT k a b).1.mul_contDiff hχ hχc)
    (hfactor i j) (hdensity i j) (hfactor a b) (hdensity a b)

/-- The global consumer retains actual L1 densities and the exact weak
testing identity; the derivative is not claimed L2. -/
theorem global_product_testing {n : ℕ}
    {f df g dg : EuclideanSpace ℝ (Fin n) → ℝ} {v : EuclideanSpace ℝ (Fin n)}
    (hf : HasWeakDerivAlong f df v) (hg : HasWeakDerivAlong g dg v)
    (hf2 : MemLp f 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hdf2 : MemLp df 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hg2 : MemLp g 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hdg2 : MemLp dg 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    Integrable (fun x => f x * g x) (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
    Integrable (fun x => df x * g x + f x * dg x)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
    ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ 1 ψ → HasCompactSupport ψ →
      (∫ x, (f x * g x) * fderiv ℝ ψ x v) =
        -∫ x, (df x * g x + f x * dg x) * ψ x := by
  refine ⟨hf2.integrable_mul hg2, (hdf2.integrable_mul hg2).add
    (hf2.integrable_mul hdg2), ?_⟩
  exact (hf.mul_of_memLp_two hg hf2 hdf2 hg2 hdg2).2.2


end WeakHessianProductAudit.Global

namespace WeakHessianProductAudit.Local

/-- Produce uncut bounded-Hessian weak products and local L2 densities from
actual normalized R0 source-law inputs, not assumed global-L2 raw fields. -/
theorem produced_normalized_hessian_product {n : ℕ} (hn : 0 < n)
    {K : Set (EuclideanSpace ℝ (Fin n))} {W : EuclideanSpace ℝ (Fin n) → ℝ}
    {κ : ℝ} (hκ : 0 < κ) (hK : IsCompact K) (hKc : Convex ℝ K)
    (hKint : (interior K).Nonempty) (hW : ContDiff ℝ ∞ W)
    (hstrong : ConvexOn ℝ univ (fun y => W y - (κ / 2) * ‖y‖ ^ 2))
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hμ : (μ : Measure (EuclideanSpace ℝ (Fin n))) =
      (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
        (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p))))
    (hiso : KLS.Isotropic μ)
 :
    ∃ (u : EuclideanSpace ℝ (Fin n) → ℝ)
        (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ),
      (∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 1 ∧
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
        (μ : Measure (EuclideanSpace ℝ (Fin n))) ∧
      LipschitzWith (Real.toNNReal (16 / κ)) (gradient u) ∧
      ∀ k i j a b : Fin n,
        HasWeakDerivAlong
          (fun x => hessianMatrix u x i j * hessianMatrix u x a b)
          (fun x => T x k i j * hessianMatrix u x a b +
            hessianMatrix u x i j * T x k a b)
          (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
          MemLp (fun x => T x k i j * hessianMatrix u x a b +
            hessianMatrix u x i j * T x k a b) 2
            ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
  obtain ⟨u, _L, _LF, T, _hconv, _hLip, hnorm, hmap, _hC1, hG,
      _hF, _hw, _hdata, hT⟩ :=
    exists_regular_moment_weak_tensor hn hκ hK hKc hKint hW hstrong μ hμ hiso
  refine ⟨u, T, hnorm, hmap, hG, ?_⟩
  intro k i j a b
  have hbound (r s : Fin n) : MemLp (fun x => hessianMatrix u x r s)
      (⊤ : ENNReal) (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    memLp_top_of_bound (measurable_hessianMatrix_entry u r s).aestronglyMeasurable
      (Real.toNNReal (16 / κ) : ℝ)
      (Filter.Eventually.of_forall fun x =>
        norm_hessianMatrix_entry_le_of_lipschitz_gradient hG x r s)
  exact (hT k i j).1.mul_of_locally_memLp_two (hT k a b).1
    (hbound i j) (hbound a b) (hT k i j).2 (hT k a b).2

/-- The real source-law square consumer retains normalization and the actual
pushforward, and identifies the derivative 2*H_ij*T_kij with compact-local L2. -/
theorem produced_normalized_hessian_square {n : ℕ} (hn : 0 < n)
    {K : Set (EuclideanSpace ℝ (Fin n))} {W : EuclideanSpace ℝ (Fin n) → ℝ}
    {κ : ℝ} (hκ : 0 < κ) (hK : IsCompact K) (hKc : Convex ℝ K)
    (hKint : (interior K).Nonempty) (hW : ContDiff ℝ ∞ W)
    (hstrong : ConvexOn ℝ univ (fun y => W y - (κ / 2) * ‖y‖ ^ 2))
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hμ : (μ : Measure (EuclideanSpace ℝ (Fin n))) =
      (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
        (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p))))
    (hiso : KLS.Isotropic μ)
 :
    ∃ (u : EuclideanSpace ℝ (Fin n) → ℝ)
        (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ),
      (∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 1 ∧
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
        (μ : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ∀ k i j : Fin n,
        HasWeakDerivAlong (fun x => (hessianMatrix u x i j) ^ 2)
          (fun x => 2 * hessianMatrix u x i j * T x k i j)
          (EuclideanSpace.basisFun (Fin n) ℝ k) ∧
        ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
          MemLp (fun x => 2 * hessianMatrix u x i j * T x k i j) 2
            ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) := by
  obtain ⟨u, T, hnorm, hmap, _hG, hprod⟩ :=
    produced_normalized_hessian_product hn hκ hK hKc hKint hW hstrong μ hμ hiso
  refine ⟨u, T, hnorm, hmap, ?_⟩
  intro k i j
  refine ⟨?_, ?_⟩
  · convert (hprod k i j i j).1 using 1 <;> funext x <;> ring
  · intro S hS
    convert (hprod k i j i j).2 S hS using 1
    funext x
    ring


end WeakHessianProductAudit.Local

#print axioms FunctionalInequalities.Analysis.HasWeakDerivAlong.mul_of_memLp_two
#print axioms FunctionalInequalities.Analysis.HasWeakDerivAlong.mul_of_locally_memLp_two
#print axioms WeakHessianProductAudit.Global.produced_normalized_cutoff_hessian_product
#print axioms WeakHessianProductAudit.Global.global_product_testing
#print axioms WeakHessianProductAudit.Local.produced_normalized_hessian_product
#print axioms WeakHessianProductAudit.Local.produced_normalized_hessian_square
