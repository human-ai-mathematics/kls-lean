module

public import FunctionalInequalities.KLS.CEK.MomentRegularity.Potential
public import FunctionalInequalities.Analysis.Convex.Section.Engulfing

/-!
# Hölder gradients of moment potentials for continuous convex-body targets

Letwin arXiv:2607.24164v1 Lemma 2.2, through Berman–Berndtsson
arXiv:1207.6128v1 Theorem 2.24(i). For every n > 0, bounded open convex K,
continuous W on closure K and the normalized isotropic density 1_K exp(-W),
the actual normalized transporting C¹ potential has a Hölder gradient on every
compact set. The exponent and constant precede all pairs of points there.

All Alexandrov, a.e. quadratic-expansion and viscosity fields of the C¹ producer
are retained at the same u. No uniform convexity, gradient Lipschitz bound,
section estimate or Hölder conclusion is an input. W²,p and full smoothness
remain separate gains.
-/

@[expose] public section

noncomputable section
open MeasureTheory Set Filter
open scoped RealInnerProductSpace ContDiff Topology
open FunctionalInequalities.Probability.Stein
namespace FunctionalInequalities.Analysis
section ContinuousTarget
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- The literal convex-body source produces a C¹,α moment potential, retaining
normalization, transport, gradient homeomorphism and all Alexandrov/viscosity fields. -/
theorem exists_moment_potential_holder_gradient_of_bounded_open_convex (hn : 0 < n)
    {K : Set E} (hKb : Bornology.IsBounded K) (hKo : IsOpen K) (hKc : Convex ℝ K)
    (hKne : K.Nonempty) {W : E → ℝ} (hW : ContinuousOn W (closure K))
    (μ : ProbabilityMeasure E)
    (hμ : (μ : Measure E) = (volume : Measure E).withDensity
      (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p))))
    (hiso : KLS.Isotropic μ) :
    ∃ (u : E → ℝ) (L : NNReal), StrictConvexOn ℝ univ u ∧ LipschitzWith L u ∧
      (∫ x, Real.exp (-u x) ∂(volume : Measure E)) = 1 ∧
      ((volume : Measure E).tilted (-u)).map (gradient u) = (μ : Measure E) ∧
      ContDiff ℝ 1 u ∧
      (∃ e : E ≃ₜ K, ∀ x, (e x : E) = gradient u x) ∧
      Continuous (fun x => Real.exp (-u x + W (gradient u x))) ∧
      (∀ G : Set E, IsOpen G → volume (subgradientImage u G) =
        ∫⁻ x in G, ENNReal.ofReal (Real.exp (-u x + W (gradient u x)))) ∧
      (∀ᵐ x ∂(volume : Measure E), ∃ B : Matrix (Fin n) (Fin n) ℝ,
        B.IsHermitian ∧ B.PosDef ∧ B.det = Real.exp (-u x + W (gradient u x)) ∧
        ∃ g : E, ∀ ε > 0, ∀ᶠ y in 𝓝 x,
          |u y - quadraticAt B x g (u x) y| ≤ ε * ‖y - x‖ ^ 2) ∧
      (∀ (x : E) (ψ : E → ℝ), ContDiffAt ℝ 2 ψ x → u x = ψ x →
        (∀ᶠ y in 𝓝 x, u y ≤ ψ y) →
        Real.exp (-u x + W (gradient u x)) ≤ (hessianMatrix ψ x).det) ∧
      (∀ (x : E) (ψ : E → ℝ), ContDiffAt ℝ 2 ψ x → (hessianMatrix ψ x).PosSemidef →
        u x = ψ x → (∀ᶠ y in 𝓝 x, ψ y ≤ u y) →
        (hessianMatrix ψ x).det ≤ Real.exp (-u x + W (gradient u x))) ∧
      (∀ Q : Set E, IsCompact Q → ∃ α C : ℝ, 0 < α ∧ α ≤ 1 ∧ 0 ≤ C ∧
        ∀ x ∈ Q, ∀ y ∈ Q, ‖gradient u y - gradient u x‖ ≤ C * ‖y - x‖ ^ α) ∧
      ∀ Q : Set E, IsCompact Q → ∃ α c : ℝ, 0 < α ∧ α ≤ 1 ∧ 0 < c ∧
        ∀ x ∈ Q, ∀ h : ℝ, 0 < h → h ≤ 1 →
          Metric.closedBall x (c * h ^ (1 + α)⁻¹) ⊆
            {z | u z ≤ u x + ⟪gradient u x, z - x⟫ + h} := by
  obtain ⟨u, L, hstrict, hl, hnorm, hm, hC1, he, hf, hMA, hae, hUpper, hLower⟩ :=
    exists_moment_potential_of_bounded_open_convex hn hKb hKo hKc hKne hW μ hμ hiso
  refine ⟨u, L, hstrict, hl, hnorm, hm, hC1, he, hf, hMA, hae, hUpper, hLower, ?_, ?_⟩
  · intro Q hQ
    exact exists_holder_gradient_of_alexandrov_density hn hl hstrict hC1 hf
      (fun x => Real.exp_pos _) hMA hQ
  · intro Q hQ
    exact exists_section_power_inclusion_of_alexandrov_density hn hl hstrict hC1 hf
      (fun x => Real.exp_pos _) hMA hQ

end ContinuousTarget
end FunctionalInequalities.Analysis
