module

public import FunctionalInequalities.KLS.CEK.GeneralExistence

@[expose] public section

noncomputable section
namespace LetwinMomentMeasureExistenceAudit
open Set MeasureTheory FunctionalInequalities.Analysis
open FunctionalInequalities.Probability.MomentMeasure
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/--
Letwin arXiv:2607.24164v1 Lemma 2.1 = Cordero-Erausquin–Klartag arXiv:1304.0630v1 Theorem 2,
existence part,
on `ℝⁿ` with Lebesgue measure, without essential continuity: a finite Borel `μ ≠ 0` with finite
first moment,
barycenter `0` and not supported in a proper linear subspace is the push-forward of `exp(-ψ(x)) dx`
under the gradient
of a convex lower semicontinuous `ψ : ℝⁿ → ℝ ∪ {+∞}` with `∫ exp(-ψ) = μ(ℝⁿ)` and full-dimensional
effective domain.
The push-forward is written out literally. Essential continuity and uniqueness are not asserted. -/
theorem source_existence (μ : Measure E) [IsFiniteMeasure μ] (hμ : μ ≠ 0)
    (hsub : ∀ V : Submodule ℝ E, μ (V : Set E)ᶜ = 0 → V = ⊤)
    (hfirst : Integrable (fun x : E => x) μ) (hbar : ∫ x, x ∂μ = 0) :
    ∃ ψ : E → EReal,
      (∀ x, ψ x ≠ ⊥) ∧
        Convex ℝ {p : E × ℝ | ψ p.1 ≤ (p.2 : EReal)} ∧
          LowerSemicontinuous ψ ∧
            (interior {x | ψ x ≠ ⊤}).Nonempty ∧
              (∫⁻ x, EReal.exp (-ψ x) ∂(volume : Measure E)) = μ univ ∧
                ((volume : Measure E).withDensity (fun x => EReal.exp (-ψ x))).map
                    (gradient fun x => (ψ x).toReal) =
                  μ := by
  obtain ⟨ψ, hc, hlsc, hint, hmass, hmom⟩ :=
    FunctionalInequalities.KLS.CEK.exists_ofPotential_eq (volume : Measure E) μ hμ hsub hfirst
      hbar
  exact ⟨ψ, hc.1, hc.2, hlsc, hint, hmass, hmom⟩

end LetwinMomentMeasureExistenceAudit

#print axioms FunctionalInequalities.Probability.MomentMeasure.ofPotential
#print axioms FunctionalInequalities.Probability.MomentMeasure.measurable_gradient_toReal
#print axioms FunctionalInequalities.Probability.MomentMeasure.ofPotential_apply
#print axioms FunctionalInequalities.Probability.MomentMeasure.ofPotential_univ
#print axioms FunctionalInequalities.Probability.MomentMeasure.isFiniteMeasure_ofPotential
#print axioms FunctionalInequalities.Probability.MomentMeasure.integral_ofPotential
#print axioms
  FunctionalInequalities.Probability.MomentMeasure.interior_domain_nonempty_of_mass_ne_zero
#print axioms FunctionalInequalities.Probability.MomentMeasure.density_sub_const
#print axioms FunctionalInequalities.Probability.MomentMeasure.mass_sub_const
#print axioms FunctionalInequalities.Probability.MomentMeasure.ofPotential_sub_const
#print axioms FunctionalInequalities.Probability.MomentMeasure.hasDerivAt_mass_legendre_add_smul
#print axioms FunctionalInequalities.Probability.MomentMeasure.ofPotential_legendre_eq_of_maximizer
#print axioms FunctionalInequalities.KLS.CEK.exists_ofPotential_eq_of_probability
#print axioms FunctionalInequalities.KLS.CEK.exists_ofPotential_eq
#print axioms LetwinMomentMeasureExistenceAudit.source_existence
