import FunctionalInequalities.KLS.CEK.MomentRegularity.TraceStein

/-!
# Audit client of the weak Hessian–Stein kernel of the strong regular class

* The statements of the determinant floor, strict-convex gradient injectivity and the two Hessian-kernel
  transport lemmas are restated verbatim and discharged by the canonical declarations.
* Edge cases: the floor in dimension one (`K ^ 0 = 1`) and gradient injectivity in dimension zero.
* Same witness: the old flat conjunctions of `exists_regular_moment_potential` and
  `exists_regular_moment_hessian_trace_bound` are prefixes, at the same `u` and `L`, of the inverse, local-ellipticity and
  target-kernel producers, and the kernel is `∇²u ∘ Ψ` for a left inverse `Ψ` of that `∇u`.

This does not prove the smooth moment map of Letwin arXiv:2607.24164v1, Lemma 2.2, nor everywhere positive definiteness.
-/

noncomputable section
open MeasureTheory Set
open scoped ContDiff RealInnerProductSpace Matrix.Norms.Frobenius

namespace LetwinWeakHessianKernelAudit

open FunctionalInequalities FunctionalInequalities.Analysis FunctionalInequalities.Probability.Stein
open FunctionalInequalities.Analysis.BakryEmery

/-- Statement: determinant floor. -/
theorem det_floor {n : ℕ} (hn : 0 < n)
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef)
    {K δ : ℝ} (hK : 0 < K) (hδ : 0 < δ)
    (hupper : (K • (1 : Matrix (Fin n) (Fin n) ℝ) - A).PosSemidef)
    (hdet : δ ≤ A.det) :
    (A - (δ / K ^ (n - 1)) • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef :=
  posSemidef_sub_scalar_of_det_lower hn hA hK hδ hupper hdet

/-- The determinant floor in dimension one is `δ` itself. -/
theorem det_floor_one {A : Matrix (Fin 1) (Fin 1) ℝ} (hA : A.PosSemidef) {K δ : ℝ} (hK : 0 < K) (hδ : 0 < δ)
    (hupper : (K • (1 : Matrix (Fin 1) (Fin 1) ℝ) - A).PosSemidef) (hdet : δ ≤ A.det) :
    (A - δ • (1 : Matrix (Fin 1) (Fin 1) ℝ)).PosSemidef := by
  simpa using posSemidef_sub_scalar_of_det_lower one_pos hA hK hδ hupper hdet

/-- Statement: strict-convex gradient injectivity. -/
theorem strict_gradient {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {u : E → ℝ} (hu : Differentiable ℝ u) (hstrict : StrictConvexOn ℝ univ u) :
    Function.Injective (gradient u) :=
  injective_gradient_of_strictConvexOn hu hstrict

/-- Gradient injectivity in dimension zero. -/
theorem strict_gradient_zero {u : EuclideanSpace ℝ (Fin 0) → ℝ} (hu : Differentiable ℝ u)
    (hs : StrictConvexOn ℝ univ u) : Function.Injective (gradient u) :=
  injective_gradient_of_strictConvexOn hu hs

/-- Statement: transport of a.e. positive definiteness. -/
theorem posDef_transport {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : ContDiff ℝ 1 u)
    (ν μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hmap : (ν : Measure (EuclideanSpace ℝ (Fin n))).map (gradient u) =
      (μ : Measure (EuclideanSpace ℝ (Fin n))))
    {Ψ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)} (hΨ : Measurable Ψ)
    (hInv : ∀ᵐ y ∂(ν : Measure (EuclideanSpace ℝ (Fin n))), Ψ (gradient u y) = y)
    (hPD : ∀ᵐ y ∂(ν : Measure (EuclideanSpace ℝ (Fin n))), (hessianMatrix u y).PosDef) :
    ∀ᵐ x ∂(μ : Measure (EuclideanSpace ℝ (Fin n))), (hessianKernel u Ψ x).PosDef :=
  hessianKernel_posDefAE_of_map hu ν μ hmap hΨ hInv hPD

/-- Statement: transport of the Hilbert–Schmidt `L²` bound. -/
theorem hs_transport {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : ContDiff ℝ 1 u)
    (ν μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hmap : (ν : Measure (EuclideanSpace ℝ (Fin n))).map (gradient u) =
      (μ : Measure (EuclideanSpace ℝ (Fin n))))
    {Ψ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)} (hΨ : Measurable Ψ)
    (hInv : ∀ᵐ y ∂(ν : Measure (EuclideanSpace ℝ (Fin n))), Ψ (gradient u y) = y)
    (hHS : MemLp (fun y => hsNorm (hessianMatrix u y)) 2
      (ν : Measure (EuclideanSpace ℝ (Fin n)))) :
    MemLp (fun x => hsNorm (hessianKernel u Ψ x)) 2
      (μ : Measure (EuclideanSpace ℝ (Fin n))) :=
  memLp_hsNorm_hessianKernel_of_map hu ν μ hmap hΨ hInv hHS

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

/-- The inverse producer keeps every field of `exists_regular_moment_potential` at the same `u` and `L`, and the inverse is a
left inverse of that `∇u`. -/
theorem inverse_same_witness :
    ∃ (u : EuclideanSpace ℝ (Fin n) → ℝ) (L : NNReal),
      ConvexOn ℝ univ u ∧ LipschitzWith L u ∧
      (∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 1 ∧
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
        (μ : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ContDiff ℝ 1 u ∧ LipschitzWith (Real.toNNReal (16 / κ)) (gradient u) ∧
      (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        (hessianMatrix u x).PosDef ∧
        Real.log (hessianMatrix u x).det = -u x + W (gradient u x) ∧
        ((16 / κ) • (1 : Matrix (Fin n) (Fin n) ℝ) - hessianMatrix u x).PosSemidef) ∧
      ∃ Ψ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n), Measurable Ψ ∧
        Function.LeftInverse Ψ (gradient u) := by
  obtain ⟨u, L, h1, h2, h3, h4, h5, h6, h7, -, hΨ⟩ :=
    exists_regular_moment_potential_with_inverse hn hκ hK hKc hKint hW hstrong μ hμ hiso
  exact ⟨u, L, h1, h2, h3, h4, h5, h6, h7, hΨ⟩

/-- The local-ellipticity producer keeps every field of `exists_regular_moment_potential` at the same `u` and `L`. -/
theorem ellipticity_same_witness :
    ∃ (u : EuclideanSpace ℝ (Fin n) → ℝ) (L : NNReal),
      ConvexOn ℝ univ u ∧ LipschitzWith L u ∧
      (∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 1 ∧
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
        (μ : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ContDiff ℝ 1 u ∧ LipschitzWith (Real.toNNReal (16 / κ)) (gradient u) ∧
      (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        (hessianMatrix u x).PosDef ∧
        Real.log (hessianMatrix u x).det = -u x + W (gradient u x) ∧
        ((16 / κ) • (1 : Matrix (Fin n) (Fin n) ℝ) - hessianMatrix u x).PosSemidef) ∧
      ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        ∃ δ : ℝ, 0 < δ ∧ ∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S),
          (hessianMatrix u x - δ • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef :=
  exists_regular_moment_potential_locally_elliptic hn hκ hK hKc hKint hW hstrong μ hμ hiso

/-- The target-kernel producer keeps every field of `exists_regular_moment_hessian_trace_bound` at the same `u` and `L`, and
its kernel is `∇²u ∘ Ψ` for a left inverse `Ψ` of that `∇u`. -/
theorem kernel_same_witness :
    ∃ (u : EuclideanSpace ℝ (Fin n) → ℝ) (L : NNReal) (Ψ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
      ConvexOn ℝ univ u ∧ LipschitzWith L u ∧
      (∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 1 ∧
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
        (μ : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ContDiff ℝ 1 u ∧ LipschitzWith (Real.toNNReal (16 / κ)) (gradient u) ∧
      (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        (hessianMatrix u x).PosDef ∧
        Real.log (hessianMatrix u x).det = -u x + W (gradient u x) ∧
        ((16 / κ) • (1 : Matrix (Fin n) (Fin n) ℝ) - hessianMatrix u x).PosSemidef) ∧
      (∀ i j : Fin n,
        Integrable (fun x => hessianMatrix u x i j)
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) ∧
        (∫ x, hessianMatrix u x i j
          ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) =
          (1 : Matrix (Fin n) (Fin n) ℝ) i j) ∧
      (∀ B : Matrix (Fin n) (Fin n) ℝ, B.IsSymm →
        Integrable (fun x => (B * hessianMatrix u x * B * hessianMatrix u x).trace)
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)) ∧
        (∫ x, (B * hessianMatrix u x * B * hessianMatrix u x).trace
          ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u))) ≤ 2 * (B * B).trace) ∧
      Function.LeftInverse Ψ (gradient u) ∧ IsSteinKernel μ (hessianKernel u Ψ) ∧
      (∀ᵐ x ∂(μ : Measure (EuclideanSpace ℝ (Fin n))), (hessianKernel u Ψ x).PosDef) ∧
      (∫ x, hsNorm (hessianKernel u Ψ x) ^ 2 ∂(μ : Measure (EuclideanSpace ℝ (Fin n)))) ≤ 2 * n := by
  obtain ⟨u, L, Ψ, ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩, -, hl, hS, hPD, -, -, hHS2, -⟩ :=
    exists_regular_moment_target_stein_kernel hn hκ hK hKc hKint hW hstrong μ hμ hiso
  exact ⟨u, L, Ψ, h1, h2, h3, h4, h5, h6, h7, h8, h9, hl, hS, hPD, hHS2⟩

/-- The kernel producer's first component elaborates as the flat trace-bound statement itself at its own `u` and `L`. -/
example : True := by
  obtain ⟨u, L, Ψ, hsrc, -⟩ :=
    exists_regular_moment_target_stein_kernel hn hκ hK hKc hKint hW hstrong μ hμ hiso
  have _ : type_of% (exists_regular_moment_hessian_trace_bound hn hκ hK hKc hKint hW hstrong μ hμ hiso) :=
    ⟨u, L, hsrc⟩
  trivial

end SameWitness

end LetwinWeakHessianKernelAudit

#print axioms LetwinWeakHessianKernelAudit.det_floor
#print axioms LetwinWeakHessianKernelAudit.det_floor_one
#print axioms LetwinWeakHessianKernelAudit.strict_gradient
#print axioms LetwinWeakHessianKernelAudit.strict_gradient_zero
#print axioms LetwinWeakHessianKernelAudit.posDef_transport
#print axioms LetwinWeakHessianKernelAudit.hs_transport
#print axioms LetwinWeakHessianKernelAudit.inverse_same_witness
#print axioms LetwinWeakHessianKernelAudit.ellipticity_same_witness
#print axioms LetwinWeakHessianKernelAudit.kernel_same_witness
#print axioms FunctionalInequalities.Analysis.posSemidef_sub_scalar_of_det_lower
#print axioms FunctionalInequalities.Analysis.injective_gradient_of_strictConvexOn
#print axioms FunctionalInequalities.Analysis.ae_posSemidef_hessianMatrix_sub_of_log_det
#print axioms FunctionalInequalities.Analysis.measurable_inverse_gradient_of_map_gradient
#print axioms FunctionalInequalities.Analysis.exists_regular_moment_potential_with_inverse
#print axioms FunctionalInequalities.Analysis.exists_regular_moment_potential_locally_elliptic
#print axioms FunctionalInequalities.Probability.Stein.hsNorm_sq_eq_trace_mul_self
#print axioms FunctionalInequalities.Probability.Stein.hessianKernel_posDefAE_of_map
#print axioms FunctionalInequalities.Probability.Stein.memLp_hsNorm_hessianKernel_of_map
#print axioms FunctionalInequalities.KLS.LogConcave.weak_hessianKernel_isSteinKernel
#print axioms FunctionalInequalities.Analysis.exists_regular_moment_target_stein_kernel
