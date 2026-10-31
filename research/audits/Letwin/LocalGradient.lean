module

public import FunctionalInequalities.Analysis.Convex.Quadratic
public import FunctionalInequalities.Analysis.Convex.Viscosity.Equation
public import FunctionalInequalities.KLS.CEK.MomentRegularity.GradientHolder
public import Mathlib.Analysis.Calculus.Deriv.Abs

@[expose] public section

noncomputable section
open Set Filter MeasureTheory Metric
open scoped RealInnerProductSpace Topology
namespace LetwinLocalGradientAudit

open Set Filter MeasureTheory
open FunctionalInequalities.Analysis
open scoped RealInnerProductSpace Topology

theorem abs_on_Ioi0 :
    ∀ᵐ x ∂(volume : Measure ℝ).restrict (Ioi (0 : ℝ)),
      ∃ B : ℝ →L[ℝ] ℝ,
        (∀ v w, ⟪B v, w⟫ = ⟪v, B w⟫) ∧
        HasFDerivAt (gradient (fun x : ℝ => |x|)) B x ∧
        ∀ ε > 0, ∀ᶠ y in 𝓝 x,
          |(|y| : ℝ) - |x| - ⟪gradient (fun x : ℝ => |x|) x, y - x⟫ -
              (1 / 2) * ⟪B (y - x), y - x⟫| ≤ ε * ‖y - x‖ ^ 2 := by
  have hconv : ConvexOn ℝ Set.univ (fun x : ℝ => |x|) := by
    refine ⟨convex_univ, ?_⟩
    intro x hx y hy a b ha hb hab
    calc
      |a • x + b • y| ≤ |a • x| + |b • y| := abs_add_le _ _
      _ = a • |x| + b • |y| := by
        simp [smul_eq_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]

  have hdiff : DifferentiableOn ℝ (fun x : ℝ => |x|) (Ioi (0 : ℝ)) := by
    intro x hx
    have hEq :
        (fun y : ℝ => |y|) =ᶠ[𝓝 x] (fun y : ℝ => y) := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      exact abs_of_pos hy
    have hId : DifferentiableAt ℝ (fun y : ℝ => y) x :=
      differentiableAt_id
    have hAbs : DifferentiableAt ℝ (fun y : ℝ => |y|) x :=
      hId.congr_of_eventuallyEq hEq
    exact hAbs.differentiableWithinAt

  exact
    ae_exists_gradient_secondOrder_expansion_on_open
      (u := fun x : ℝ => |x|) hconv (Omega := Ioi (0 : ℝ))
      isOpen_Ioi hdiff

end LetwinLocalGradientAudit

namespace LetwinLocalGradientAudit
open FunctionalInequalities.Analysis

/-- The actual local abs client cannot meet the old global differentiability input. -/
theorem abs_not_globally_differentiable :
    ¬ Differentiable ℝ (fun x : ℝ => |x|) := by
  intro h
  exact not_differentiableAt_abs_zero (h 0)

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- Actual unit-MA quadratic on a proper open ball, with the SAME derivative and
expansion matrix, including dimension zero. Convexity/differentiability/MA constructed. -/
theorem unit_quadratic_local :
    ∀ᵐ x ∂((volume : Measure E).restrict (ball 0 1)),
      ∃ A : Matrix (Fin n) (Fin n) ℝ, A.IsHermitian ∧ A.PosDef ∧ A.det = 1 ∧
        HasFDerivAt (gradient (quadraticAt (1 : Matrix (Fin n) (Fin n) ℝ) 0 0 0))
          (Matrix.toEuclideanLin A).toContinuousLinearMap x ∧
        ∀ ε > 0, ∀ᶠ y in 𝓝 x,
          |quadraticAt (1 : Matrix (Fin n) (Fin n) ℝ) 0 0 0 y -
            quadraticAt A x (gradient (quadraticAt (1 : Matrix (Fin n) (Fin n) ℝ) 0 0 0) x)
              (quadraticAt (1 : Matrix (Fin n) (Fin n) ℝ) 0 0 0 x) y| ≤ ε * ‖y - x‖ ^ 2 := by
  have hd : DifferentiableOn ℝ
      (quadraticAt (1 : Matrix (Fin n) (Fin n) ℝ) (0 : E) 0 0) (ball 0 1) :=
    ((contDiff_quadraticAt _ _ _ _).differentiable (by norm_num)).differentiableOn
  have hMA : ∀ G : Set E, IsOpen G → G ⊆ ball 0 1 →
      volume (subgradientImage (quadraticAt (1 : Matrix (Fin n) (Fin n) ℝ) 0 0 0) G) =
        ∫⁻ _y in G, ENNReal.ofReal (1 : ℝ) := by
    intro G hG _
    rw [volume_subgradientImage_quadraticAt Matrix.PosDef.one (0 : E) 0 0 hG.measurableSet,
      Matrix.det_one, ENNReal.ofReal_one, one_mul]
    simp
  exact ae_exists_gradient_posDef_det_eq_on_open
    (convexOn_quadraticAt Matrix.PosSemidef.one _ _ _) isOpen_ball hd
    continuousOn_const (fun _ _ => zero_lt_one) hMA

/-- Actual literal-source input; the same normalized transporting Holder witness
now has a genuine gradient derivative with determinant equal to its actual MA density.
No derivative, Hessian, MA equation, C11 or W2p estimate of that witness is supplied. -/
theorem source_local_gradient_derivative (hn : 0 < n)
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
      ∀ R : ℝ, 0 < R → ∀ᵐ x ∂((volume : Measure E).restrict (ball 0 R)),
        ∃ A : Matrix (Fin n) (Fin n) ℝ,
        A.IsHermitian ∧ A.PosDef ∧ A.det = Real.exp (-u x + W (gradient u x)) ∧
          HasFDerivAt (gradient u) (Matrix.toEuclideanLin A).toContinuousLinearMap x ∧
          ∀ ε > 0, ∀ᶠ y in 𝓝 x,
            |u y - quadraticAt A x (gradient u x) (u x) y| ≤ ε * ‖y - x‖ ^ 2 := by
  obtain ⟨u, L, hs, hl, hn', hm, hC1, he, hf, hMA, _hae, _hu, _hd, hholder, _hpower⟩ :=
    exists_moment_potential_holder_gradient_of_bounded_open_convex hn hKb hKo hKc hKne hW μ hμ hiso
  refine ⟨u, L, hs, hl, hn', hm, hC1, he, hholder, ?_⟩
  intro R _hR
  exact ae_exists_gradient_posDef_det_eq_on_open hs.convexOn isOpen_ball
    (hC1.differentiable one_ne_zero).differentiableOn hf.continuousOn
    (fun x _ => Real.exp_pos _) (fun G hG _ => hMA G hG)

end LetwinLocalGradientAudit
#print axioms FunctionalInequalities.Analysis.ae_exists_gradient_secondOrder_expansion_on_open
#print axioms FunctionalInequalities.Analysis.ae_exists_gradient_quadraticAt_expansion_on_open
#print axioms FunctionalInequalities.Analysis.ae_exists_gradient_posDef_det_eq_on_open
#print axioms LetwinLocalGradientAudit.abs_on_Ioi0
#print axioms LetwinLocalGradientAudit.abs_not_globally_differentiable
#print axioms LetwinLocalGradientAudit.unit_quadratic_local
#print axioms LetwinLocalGradientAudit.source_local_gradient_derivative
#check LetwinLocalGradientAudit.unit_quadratic_local (n := 0)
