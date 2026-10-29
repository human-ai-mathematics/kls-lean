import FunctionalInequalities.KLS.Letwin.SteinKernel

/-! Client of the "every moment potential" forms of Letwin arXiv:2607.24164v1, Lemma 2.2,
Theorem 2.5, Lemmas 2.3, 2.4, A.4–A.6, 2.7 and 2.9, through the uniqueness part of Lemma 2.1
(Cordero-Erausquin–Klartag arXiv:1304.0630v1, Theorem 2) for essentially continuous potentials of
bounded-support laws. -/
noncomputable section
namespace LetwinEveryMomentPotentialAudit
open Set MeasureTheory FunctionalInequalities.Analysis FunctionalInequalities.Probability.Stein
open FunctionalInequalities.Probability.MomentMeasure
open scoped ContDiff
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- For the literal Lemma 2.2 class, an arbitrary convex essentially continuous moment map
`ψ : ℝⁿ → ℝ ∪ {+∞}` of `μ` is finite and smooth, its Hessian satisfies the Theorem 2.5 bound
`E_ν tr((∇²ψ)²) ≤ 2n`, and any second such moment map is a translate of it. -/
theorem every_moment_map_client (hn : 0 < n)
    {K U : Set E} (hKb : Bornology.IsBounded K) (hKo : IsOpen K)
    (hKc : Convex ℝ K) (hKne : K.Nonempty) (hU : IsOpen U) (hKU : closure K ⊆ U)
    {V : E → ℝ} (hV : ContDiffOn ℝ ∞ V U) (hVc : ConvexOn ℝ K V)
    (μ : ProbabilityMeasure E)
    (hμ : (μ : Measure E) =
      (volume : Measure E).withDensity (K.indicator fun p => ENNReal.ofReal (Real.exp (-V p))))
    (hiso : FunctionalInequalities.KLS.Isotropic μ)
    {ψ ψ' : E → EReal} (hψ : ConvexPotential ψ) (hess : EssentiallyContinuous ψ)
    (hψμ : ofPotential volume ψ = (μ : Measure E))
    (hψ' : ConvexPotential ψ') (hess' : EssentiallyContinuous ψ')
    (hψμ' : ofPotential volume ψ' = (μ : Measure E)) :
    (∀ x, ψ x ≠ ⊤) ∧ (∃ y₀ : E, ∀ y, ψ' y = ψ (y - y₀)) ∧
      ∃ φ : E → ℝ, (∀ x, ψ x = φ x) ∧ ContDiff ℝ ∞ φ ∧
        (∫ x, (hessianMatrix φ x * hessianMatrix φ x).trace
          ∂((volume : Measure E).tilted (-φ))) ≤ 2 * n := by
  obtain ⟨φ, hcoe, -, -, -, hφ, -, -, -, -, -, htr⟩ :=
    integral_trace_le_of_ofPotential_of_bounded_open_convex hn hKb hKo hKc hKne hU hKU hV hVc
      μ hμ hiso hψ hess hψμ
  obtain ⟨R, hR⟩ := hKb.exists_norm_le
  have hzero : (μ : Measure E) Kᶜ = 0 := by
    rw [hμ, withDensity_apply _ hKo.measurableSet.compl]
    calc
      _ = ∫⁻ x in Kᶜ, (0 : ENNReal) ∂(volume : Measure E) := by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem hKo.measurableSet.compl] with x hx
        exact indicator_of_notMem hx _
      _ = 0 := by simp
  have hK : ∀ᵐ y ∂(μ : Measure E), y ∈ K := mem_ae_iff.mpr hzero
  obtain ⟨y₀, hy₀⟩ := exists_eq_translate_of_ofPotential_eq hψ hess hψ' hess' hψμ hψμ'
    (hK.mono fun y hy => hR y hy)
  refine ⟨fun x => by rw [hcoe x]; exact EReal.coe_ne_top _, ⟨y₀, hy₀⟩, φ, hcoe, hφ, ?_⟩
  simpa only [one_mul, mul_one, Matrix.trace_one, Fintype.card_fin] using
    (htr 1 Matrix.isSymm_one).2

end LetwinEveryMomentPotentialAudit
#print axioms FunctionalInequalities.Probability.MomentMeasure.ofPotential_coe_eq_map_gradient
#print axioms FunctionalInequalities.Probability.MomentMeasure.exists_eq_coe_of_ofPotential_eq
#print axioms FunctionalInequalities.Probability.MomentMeasure.exists_eq_translate_of_ofPotential_eq
#print axioms FunctionalInequalities.Probability.MomentMeasure.exists_eq_translate_of_ofPotential_eq_of_map_gradient_eq
#print axioms FunctionalInequalities.Probability.MomentMeasure.ofPotential_eq_iff_exists_eq_translate
#print axioms FunctionalInequalities.Probability.MomentMeasure.exists_centered_regular_potential
#print axioms FunctionalInequalities.Probability.MomentMeasure.exists_smooth_moment_calculus_of_bounded_open_convex
#print axioms FunctionalInequalities.Probability.MomentMeasure.smooth_of_moment_potential_of_bounded_open_convex
#print axioms FunctionalInequalities.Probability.MomentMeasure.integral_trace_le_of_moment_potential_of_bounded_open_convex
#print axioms FunctionalInequalities.Probability.MomentMeasure.smooth_moment_calculus_of_moment_potential_of_bounded_open_convex
#print axioms FunctionalInequalities.Probability.MomentMeasure.smooth_of_ofPotential_of_bounded_open_convex
#print axioms FunctionalInequalities.Probability.MomentMeasure.integral_trace_le_of_ofPotential_of_bounded_open_convex
#print axioms FunctionalInequalities.Probability.MomentMeasure.smooth_moment_calculus_of_ofPotential_of_bounded_open_convex
#print axioms FunctionalInequalities.Probability.MomentMeasure.exists_smooth_moment_stein_kernel_of_bounded_open_convex
#print axioms FunctionalInequalities.Probability.MomentMeasure.exists_stein_kernel_of_moment_potential_of_bounded_open_convex
#print axioms FunctionalInequalities.Probability.MomentMeasure.exists_stein_kernel_of_ofPotential_of_bounded_open_convex
#print axioms LetwinEveryMomentPotentialAudit.every_moment_map_client
