module

public import FunctionalInequalities.KLS.CEK.MomentRegularity.Potential
public import FunctionalInequalities.Analysis.Convex.Section.Growth

@[expose] public section

noncomputable section
namespace LetwinConvexMomentAudit
open Set MeasureTheory Filter Topology FunctionalInequalities.Analysis
open FunctionalInequalities.Probability.Stein
open scoped ContDiff RealInnerProductSpace
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- Literal A.1 source class, without uniform convexity: a finite C1 moment potential, exact
transport, gradient homeomorphism and both viscosity inequalities at the same actual u.
This client does not assert the missing C1,alpha/W2,p/C-infinity stages of Lemma 2.2. -/
theorem source_moment_equation (hn : 0 < n) {K U : Set E}
    (hKb : Bornology.IsBounded K) (hKo : IsOpen K) (hKc : Convex ℝ K) (hKne : K.Nonempty)
    (_hU : IsOpen U) (hKU : closure K ⊆ U) {W : E → ℝ}
    (hW : ContDiffOn ℝ ∞ W U) (_hWconvex : ConvexOn ℝ U W)
    (μ : ProbabilityMeasure E)
    (hμ : (μ : Measure E) = (volume : Measure E).withDensity
      (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p))))
    (hiso : FunctionalInequalities.KLS.Isotropic μ) :
    ∃ (u : E → ℝ) (L : NNReal), StrictConvexOn ℝ univ u ∧ LipschitzWith L u ∧
      (∫ x, Real.exp (-u x) ∂(volume : Measure E)) = 1 ∧
      ((volume : Measure E).tilted (-u)).map (gradient u) = (μ : Measure E) ∧
      ContDiff ℝ 1 u ∧ (∃ e : E ≃ₜ K, ∀ x, (e x : E) = gradient u x) ∧
      (∀ (x : E) (ψ : E → ℝ), ContDiffAt ℝ 2 ψ x → u x = ψ x →
        (∀ᶠ y in 𝓝 x, u y ≤ ψ y) →
        Real.exp (-u x + W (gradient u x)) ≤ (hessianMatrix ψ x).det) ∧
      ∀ (x : E) (ψ : E → ℝ), ContDiffAt ℝ 2 ψ x → (hessianMatrix ψ x).PosSemidef →
        u x = ψ x → (∀ᶠ y in 𝓝 x, ψ y ≤ u y) →
        (hessianMatrix ψ x).det ≤ Real.exp (-u x + W (gradient u x)) := by
  obtain ⟨u, L, hstrict, hl, hnorm, hm, hC1, he, _hf, _hMA, _hae, hUpper, hLower⟩ :=
    exists_moment_potential_of_bounded_open_convex hn hKb hKo hKc hKne
      (hW.continuousOn.mono hKU) μ hμ hiso
  exact ⟨u, L, hstrict, hl, hnorm, hm, hC1, he, hUpper, hLower⟩
/-- At the actual literal-source moment potential, compact sets have a quantitative Alexandrov
section estimate with constants chosen before the centre, slope and height. This is a
necessary section-geometry support, without asserting the normalized power-rate iteration. -/
theorem source_section_estimate (hn : 0 < n) {K : Set E}
    (hKb : Bornology.IsBounded K) (hKo : IsOpen K) (hKc : Convex ℝ K) (hKne : K.Nonempty)
    {W : E → ℝ} (hW : ContinuousOn W (closure K)) (μ : ProbabilityMeasure E)
    (hμ : (μ : Measure E) = (volume : Measure E).withDensity
      (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p))))
    (hiso : FunctionalInequalities.KLS.Isotropic μ) :
    ∃ (u : E → ℝ) (L : NNReal) (c : ℝ), StrictConvexOn ℝ univ u ∧ LipschitzWith L u ∧
      (∫ x, Real.exp (-u x) ∂(volume : Measure E)) = 1 ∧
      ((volume : Measure E).tilted (-u)).map (gradient u) = (μ : Measure E) ∧
      ContDiff ℝ 1 u ∧ 0 < c ∧ ∀ Q : Set E, IsCompact Q → ∃ b : ℝ, 0 < b ∧
        ∀ (x p : E) (h : ℝ), 0 < h →
          {y | u y < u x + ⟪p, y - x⟫ + h} ⊆ Q →
          c * h ^ Module.finrank ℝ E ≤
            b * ((volume : Measure E) {y | u y < u x + ⟪p, y - x⟫ + h}).toReal *
              (Metric.diam {y | u y < u x + ⟪p, y - x⟫ + h} ^ (Module.finrank ℝ E - 1) *
                Metric.infDist x (frontier {y | u y < u x + ⟪p, y - x⟫ + h})) := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have : Nontrivial E := inferInstance
  obtain ⟨u, L, hstrict, hl, hnorm, hm, hC1, _he, hf, hMA, _hae, _hUpper, _hLower⟩ :=
    exists_moment_potential_of_bounded_open_convex hn hKb hKo hKc hKne hW μ hμ hiso
  obtain ⟨c, hc, hest⟩ := exists_section_estimate_of_continuous_density («E» := E)
  exact ⟨u, L, c, hstrict, hl, hnorm, hm, hC1, hc,
    hest u _ hstrict.convexOn hC1.continuous hf hMA⟩

end LetwinConvexMomentAudit
#print axioms LetwinConvexMomentAudit.source_moment_equation
#print axioms FunctionalInequalities.Analysis.exists_moment_potential_of_bounded_open_convex
#print axioms FunctionalInequalities.Analysis.exists_moment_potential_of_continuousOn

#print axioms LetwinConvexMomentAudit.source_section_estimate
#print axioms FunctionalInequalities.Analysis.exists_section_estimate_of_continuous_density
