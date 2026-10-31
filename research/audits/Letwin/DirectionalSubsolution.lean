module

public import FunctionalInequalities.KLS.CEK.MomentRegularity.WeakHessian

/-!
# Audit client of the directional weak subsolution at the regular-class witness

* Empty index type: the finite flux contraction and the reciprocal matrix bounds apply.
* Same witness: the first component of `exists_regular_moment_directional_hessian_subsolution`
  elaborates as
  `exists_regular_moment_weak_hessian_evolution` at the same `u, L, LF, T`; the directional
  inequality is applied to an
  actual smooth compactly supported bump test, and the coefficient bounds to the closed unit ball.

This does not prove Harnack, oscillation decay, Schauder regularity or the smooth moment map of
Letwin arXiv:2607.24164v1,
Lemma 2.2.
-/

@[expose] public section

noncomputable section
open MeasureTheory Set
open scoped ContDiff

namespace LetwinDirectionalSubsolutionAudit

open FunctionalInequalities FunctionalInequalities.Analysis FunctionalInequalities.Probability.Stein

/-- Finite flux contraction over the empty index type. -/
theorem flux_empty {X : Type*} [MeasurableSpace X] (ν : Measure X)
    (F E H : X → Matrix Empty Empty ℝ) (v : Empty → ℝ)
    (hF : ∀ i j, Integrable (fun x => F x i j) ν) (hE : ∀ i j, Integrable (fun x => E x i j) ν)
    (hH : ∀ i j, Integrable (fun x => H x i j) ν)
    (hflux : ∀ i j, (∫ x, F x i j ∂ν) = -(∫ x, E x i j ∂ν))
    (hpos : ∀ᵐ x ∂ν, (E x + H x).PosSemidef) :
    (∫ x, dotProduct v ((F x).mulVec v) ∂ν) ≤ ∫ x, dotProduct v ((H x).mulVec v) ∂ν :=
  integral_quadratic_flux_le_of_posSemidef ν F E H v hF hE hH hflux hpos

/-- Reciprocal matrix bounds in dimension zero. -/
theorem inverse_bounds_zero {A : Matrix (Fin 0) (Fin 0) ℝ} (hA : A.PosDef) {α β : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hl : (A - α • (1 : Matrix (Fin 0) (Fin 0) ℝ)).PosSemidef)
    (hu : (β • (1 : Matrix (Fin 0) (Fin 0) ℝ) - A).PosSemidef) :
    (A⁻¹ - β⁻¹ • (1 : Matrix (Fin 0) (Fin 0) ℝ)).PosSemidef ∧
      (α⁻¹ • (1 : Matrix (Fin 0) (Fin 0) ℝ) - A⁻¹).PosSemidef :=
  inverse_posSemidef_bounds hA hα hβ hl hu

section SameWitness

variable {n : ℕ} (hn : 0 < n) {K : Set (EuclideanSpace ℝ (Fin n))}
  {W : EuclideanSpace ℝ (Fin n) → ℝ} {κ : ℝ} (hκ : 0 < κ) (hK : IsCompact K) (hKc : Convex ℝ K)
  (hKint : (interior K).Nonempty) (hW : ContDiff ℝ ∞ W)
  (hstrong : ConvexOn ℝ univ (fun y => W y - (κ / 2) * ‖y‖ ^ 2))
  (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hμ :
    (μ : Measure (EuclideanSpace ℝ (Fin n))) =
      (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
        (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p))))
  (hiso : KLS.Isotropic μ)
include hn hκ hK hKc hKint hW hstrong hμ hiso

/--
At one actual witness `u`: the directional inequality for an actual smooth bump test and the
coefficient bounds on the
closed unit ball. -/
theorem bump_and_ball (v : Fin n → ℝ) (f : ContDiffBump (0 : EuclideanSpace ℝ (Fin n))) :
    ∃ u : EuclideanSpace ℝ (Fin n) → ℝ,
      ∃ T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ,
        (∫ x,
              Real.exp (-u x) *
                (∑ a : Fin n,
                  (∑ b : Fin n,
                      (hessianMatrix u x)⁻¹ b a *
                        (∑ i : Fin n, ∑ j : Fin n, v i * v j * T x b i j)) *
                    fderiv ℝ (fun y => f y) x
                      (EuclideanSpace.basisFun (Fin n) ℝ
                        a)) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) ≤
            (∫ x,
              Real.exp (-u x) * (∑ i : Fin n, ∑ j : Fin n, v i * v j * hessianMatrix u x i j) *
                f x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) ∧
          ∃ c₀ c₁ : ℝ,
            0 < c₀ ∧
              0 < c₁ ∧
                ∀ᵐ
                  x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict
                    (Metric.closedBall 0 1)),
                  (Real.exp (-u x) • (hessianMatrix u x)⁻¹ -
                        c₀ • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef ∧
                    (c₁ • (1 : Matrix (Fin n) (Fin n) ℝ) -
                        Real.exp (-u x) • (hessianMatrix u x)⁻¹).PosSemidef := by
  obtain ⟨u, L, LF, T, -, hdir, hcoef⟩ :=
    exists_regular_moment_directional_hessian_subsolution hn hκ hK hKc hKint hW hstrong μ hμ
      hiso
  exact
    ⟨u, T,
      hdir v (fun x => f x) (f.contDiff.of_le (WithTop.coe_le_coe.mpr le_top))
        f.hasCompactSupport (fun _ => f.nonneg),
      hcoef (Metric.closedBall 0 1) (isCompact_closedBall 0 1)⟩

/--
The first component elaborates as `exists_regular_moment_weak_hessian_evolution` at the same `u, L,
LF, T`. -/
example : True := by
  obtain ⟨u, L, LF, T, hold, -⟩ :=
    exists_regular_moment_directional_hessian_subsolution hn hκ hK hKc hKint hW hstrong μ hμ
      hiso
  have _ :
    type_of%
      (exists_regular_moment_weak_hessian_evolution hn hκ hK hKc hKint hW hstrong μ hμ hiso) :=
    ⟨u, L, LF, T, hold⟩
  trivial

end SameWitness

end LetwinDirectionalSubsolutionAudit

#print axioms LetwinDirectionalSubsolutionAudit.flux_empty
#print axioms LetwinDirectionalSubsolutionAudit.inverse_bounds_zero
#print axioms LetwinDirectionalSubsolutionAudit.bump_and_ball
#print axioms FunctionalInequalities.Analysis.integral_quadratic_flux_le_of_posSemidef
#print axioms FunctionalInequalities.Analysis.inverse_posSemidef_bounds
#print axioms FunctionalInequalities.Analysis.exists_compact_inverse_hessian_coefficient_bounds
#print axioms FunctionalInequalities.Analysis.integral_directional_hessian_flux_le
#print axioms FunctionalInequalities.Analysis.exists_regular_moment_directional_hessian_subsolution
