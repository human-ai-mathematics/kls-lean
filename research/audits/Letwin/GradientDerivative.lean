module

public import FunctionalInequalities.Analysis.Convex.Quadratic
public import FunctionalInequalities.Analysis.Convex.Viscosity.Equation
public import FunctionalInequalities.KLS.CEK.MomentRegularity.GradientHolder

@[expose] public section

noncomputable section
open Set Filter MeasureTheory Metric
open scoped RealInnerProductSpace Topology
namespace LetwinGradientDerivativeAudit
open FunctionalInequalities.Analysis
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- Actual quadratic C1, convexity and unit MA equation are constructed. The
operator differentiates the gradient and gives the value expansion at the same point. -/
theorem unit_quadratic :
    ∀ᵐ x ∂(volume : Measure E), ∃ A : Matrix (Fin n) (Fin n) ℝ,
      A.IsHermitian ∧ A.PosDef ∧ A.det = 1 ∧
        HasFDerivAt (gradient (quadraticAt (1 : Matrix (Fin n) (Fin n) ℝ) 0 0 0))
          (Matrix.toEuclideanLin A).toContinuousLinearMap x ∧
        ∀ ε > 0, ∀ᶠ y in 𝓝 x,
          |quadraticAt (1 : Matrix (Fin n) (Fin n) ℝ) 0 0 0 y -
            quadraticAt A x (gradient (quadraticAt (1 : Matrix (Fin n) (Fin n) ℝ) 0 0 0) x)
              (quadraticAt (1 : Matrix (Fin n) (Fin n) ℝ) 0 0 0 x) y| ≤ ε * ‖y - x‖ ^ 2 := by
  have hd : Differentiable ℝ (quadraticAt (1 : Matrix (Fin n) (Fin n) ℝ) (0 : E) 0 0) :=
    (contDiff_quadraticAt _ _ _ _).differentiable (by norm_num)
  have hMA : ∀ G : Set E, IsOpen G → G ⊆ univ →
      volume (subgradientImage (quadraticAt (1 : Matrix (Fin n) (Fin n) ℝ) 0 0 0) G) =
        ∫⁻ _y in G, ENNReal.ofReal (1 : ℝ) := by
    intro G hG _
    rw [volume_subgradientImage_quadraticAt Matrix.PosDef.one (0 : E) 0 0 hG.measurableSet,
      Matrix.det_one, ENNReal.ofReal_one, one_mul]
    simp
  simpa only [Measure.restrict_univ] using
    ae_exists_gradient_posDef_det_eq (convexOn_quadraticAt Matrix.PosSemidef.one _ _ _) hd
      isOpen_univ continuousOn_const (fun _ _ => zero_lt_one) hMA

/-- Actual literal-source input; the same normalized transporting Holder witness
now has a genuine gradient derivative with determinant equal to its actual MA density.
No derivative, Hessian, MA equation, C11 or W2p estimate of that witness is supplied. -/
theorem source_gradient_derivative (hn : 0 < n)
    {K : Set E} (hKb : Bornology.IsBounded K) (hKo : IsOpen K) (hKc : Convex ℝ K)
    (hKne : K.Nonempty) {W : E → ℝ} (hW : ContinuousOn W (closure K))
    (μ : ProbabilityMeasure E)
    (hμ : (μ : Measure E) = volume.withDensity
      (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p))))
    (hiso : FunctionalInequalities.KLS.Isotropic μ) :
    ∃ (u : E → ℝ) (L : NNReal), StrictConvexOn ℝ univ u ∧ LipschitzWith L u ∧
      (∫ x, Real.exp (-u x) ∂(volume : Measure E)) = 1 ∧
      ((volume : Measure E).tilted (-u)).map (gradient u) = (μ : Measure E) ∧
      ContDiff ℝ 1 u ∧ (∃ e : E ≃ₜ K, ∀ x, (e x : E) = gradient u x) ∧
      (∀ Q : Set E, IsCompact Q → ∃ α C : ℝ, 0 < α ∧ α ≤ 1 ∧ 0 ≤ C ∧
        ∀ x ∈ Q, ∀ y ∈ Q, ‖gradient u y - gradient u x‖ ≤ C * ‖y - x‖ ^ α) ∧
      ∀ᵐ x ∂(volume : Measure E), ∃ A : Matrix (Fin n) (Fin n) ℝ,
        A.IsHermitian ∧ A.PosDef ∧ A.det = Real.exp (-u x + W (gradient u x)) ∧
          HasFDerivAt (gradient u) (Matrix.toEuclideanLin A).toContinuousLinearMap x ∧
          ∀ ε > 0, ∀ᶠ y in 𝓝 x,
            |u y - quadraticAt A x (gradient u x) (u x) y| ≤ ε * ‖y - x‖ ^ 2 := by
  obtain ⟨u, L, hs, hl, hn', hm, hC1, he, hf, hMA, _hae, _hu, _hd, hholder, _hpower⟩ :=
    exists_moment_potential_holder_gradient_of_bounded_open_convex hn hKb hKo hKc hKne hW μ hμ hiso
  refine ⟨u, L, hs, hl, hn', hm, hC1, he, hholder, ?_⟩
  simpa only [Measure.restrict_univ] using
    ae_exists_gradient_posDef_det_eq hs.convexOn (hC1.differentiable one_ne_zero)
      isOpen_univ hf.continuousOn (fun x _ => Real.exp_pos _)
        (fun G hG _ => hMA G hG)

end LetwinGradientDerivativeAudit
#print axioms FunctionalInequalities.Analysis.ae_exists_subgradient_secondOrder_expansion
#print axioms FunctionalInequalities.Analysis.ae_exists_gradient_secondOrder_expansion
#print axioms FunctionalInequalities.Analysis.ae_exists_gradient_quadraticAt_expansion
#print axioms FunctionalInequalities.Analysis.ae_exists_gradient_posDef_det_eq
#print axioms LetwinGradientDerivativeAudit.unit_quadratic
#print axioms LetwinGradientDerivativeAudit.source_gradient_derivative
#check LetwinGradientDerivativeAudit.unit_quadratic (n := 0)
