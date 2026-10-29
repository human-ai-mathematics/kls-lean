import FunctionalInequalities.KLS.CEK.GeneralExistence

noncomputable section
namespace LetwinMomentMeasureEssentialExistenceAudit
open Set MeasureTheory Filter FunctionalInequalities.Analysis
open FunctionalInequalities.Probability.MomentMeasure
open scoped Topology
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- Letwin arXiv:2607.24164v1 Lemma 2.1 = Cordero-Erausquin–Klartag arXiv:1304.0630v1 Theorem 2, existence part,
on `ℝⁿ` with Lebesgue measure: a finite Borel `μ ≠ 0` with finite first moment, barycenter `0` and not supported in a
proper linear subspace is the push-forward of `exp(-ψ(x)) dx` under the gradient of a convex `ψ : ℝⁿ → ℝ ∪ {+∞}`
that is essentially continuous (CEK Definition 2, written out: lower semicontinuous, and the set of discontinuity
points has zero `(n − 1)`-dimensional Hausdorff measure), with `∫ exp(-ψ) = μ(ℝⁿ)` and full-dimensional effective
domain. The push-forward is written out literally. Uniqueness is not asserted. -/
theorem source_existence (μ : Measure E) [IsFiniteMeasure μ] (hμ : μ ≠ 0)
    (hsub : ∀ V : Submodule ℝ E, μ (V : Set E)ᶜ = 0 → V = ⊤)
    (hfirst : Integrable (fun x : E => x) μ) (hbar : ∫ x, x ∂μ = 0) :
    ∃ ψ : E → EReal, (∀ x, ψ x ≠ ⊥) ∧ Convex ℝ {p : E × ℝ | ψ p.1 ≤ (p.2 : EReal)} ∧
      LowerSemicontinuous ψ ∧ μH[(n : ℝ) - 1] {x | ¬ContinuousAt ψ x} = 0 ∧
      (interior {x | ψ x ≠ ⊤}).Nonempty ∧
      (∫⁻ x, EReal.exp (-ψ x) ∂(volume : Measure E)) = μ univ ∧
      ((volume : Measure E).withDensity (fun x => EReal.exp (-ψ x))).map
        (gradient fun x => (ψ x).toReal) = μ := by
  obtain ⟨ψ, hc, hess, hint, hmass, hmom⟩ :=
    FunctionalInequalities.KLS.CEK.exists_ofPotential_eq_essentiallyContinuous (volume : Measure E) μ hμ hsub
      hfirst hbar
  have h2 := hess.2
  rw [finrank_euclideanSpace_fin] at h2
  exact ⟨ψ, hc.1, hc.2, hess.1, h2, hint, hmass, hmom⟩

/-- CEK arXiv:1304.0630v1, (23), on the half-line `[0, ∞)`: near its boundary point `0` there is a unit direction
in which every non-interior point leaves the set. -/
theorem halfLine_chart :
    ∃ θ : ℝ, ‖θ‖ = 1 ∧ ∃ U ∈ 𝓝 (0 : ℝ), ∀ x ∈ U, x ∉ interior (Ici (0 : ℝ)) →
      ∀ t : ℝ, 0 < t → x + t • θ ∉ Ici (0 : ℝ) := by
  have h0 : (0 : ℝ) ∉ interior (Ici (0 : ℝ)) := by
    rw [interior_Ici, mem_Ioi]
    exact lt_irrefl 0
  obtain ⟨θ, hθ, U, hU, _M, _hM, hout, _hvol⟩ :=
    exists_convex_frontier_chart (volume : Measure ℝ) (convex_Ici 0)
      (by rw [interior_Ici]; exact ⟨1, mem_Ioi.mpr one_pos⟩) h0
  exact ⟨θ, hθ, U, hU, hout⟩

end LetwinMomentMeasureEssentialExistenceAudit

#print axioms FunctionalInequalities.Analysis.add_smul_notMem_of_sub_smul_mem_interior
#print axioms FunctionalInequalities.Analysis.norm_sub_le_mul_transversal
#print axioms FunctionalInequalities.Analysis.hausdorffMeasure_mul_le_of_graph
#print axioms FunctionalInequalities.Analysis.exists_convex_frontier_chart
#print axioms FunctionalInequalities.KLS.CEK.essentiallyContinuous_legendre_of_maximizer
#print axioms FunctionalInequalities.KLS.CEK.exists_ofPotential_eq_essentiallyContinuous_of_probability
#print axioms FunctionalInequalities.KLS.CEK.exists_ofPotential_eq_essentiallyContinuous
#print axioms FunctionalInequalities.KLS.CEK.exists_ofPotential_eq
#print axioms LetwinMomentMeasureEssentialExistenceAudit.source_existence
#print axioms LetwinMomentMeasureEssentialExistenceAudit.halfLine_chart
