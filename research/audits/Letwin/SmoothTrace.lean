module

public import FunctionalInequalities.KLS.Letwin.SteinKernel

@[expose] public section

noncomputable section
namespace LetwinSharpSmoothSteinAudit
open Set MeasureTheory FunctionalInequalities.Analysis FunctionalInequalities.Probability.Stein
open scoped NNReal ContDiff Matrix.Norms.Frobenius
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)
section RegularClass
variable (hn : 0 < n) {K : Set (EuclideanSpace ℝ (Fin n))} {W : EuclideanSpace ℝ (Fin n) → ℝ}
  {κ : ℝ} (hκ : 0 < κ) (hK : IsCompact K) (hKc : Convex ℝ K) (hKint : (interior K).Nonempty)
  (hW : ContDiff ℝ ∞ W) (hstrong : ConvexOn ℝ univ (fun y => W y - (κ / 2) * ‖y‖ ^ 2))
  (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hμ : (μ : Measure (EuclideanSpace ℝ (Fin n))) =
    (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
      (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p))))
  (hiso : FunctionalInequalities.KLS.Isotropic μ)
include hn hκ hK hKc hKint hW hstrong hμ hiso

/-- Original source inputs, one smooth u and one coupled Stein kernel: all symmetric source
trace bounds and the sharp HS-L2 estimate hold simultaneously, without supplied estimates. -/
theorem sharp_smooth_coupling :
    ∃ (u : E → ℝ) (Ψ : E → E), ContDiff ℝ ∞ u ∧
      (∫ x, Real.exp (-u x) ∂(volume : Measure E)) = 1 ∧
      ((volume : Measure E).tilted (-u)).map (gradient u) = (μ : Measure E) ∧
      IsSteinKernel μ (hessianKernel u Ψ) ∧
      (∀ B : Matrix (Fin n) (Fin n) ℝ, B.IsSymm →
        Integrable (fun x => (B * hessianMatrix u x * B * hessianMatrix u x).trace)
          ((volume : Measure E).tilted (-u)) ∧
        (∫ x, (B * hessianMatrix u x * B * hessianMatrix u x).trace
          ∂((volume : Measure E).tilted (-u))) ≤ 2 * (B * B).trace) ∧
      MemLp (fun x => hsNorm (hessianKernel u Ψ x)) 2 (μ : Measure E) ∧
      (∫ x, hsNorm (hessianKernel u Ψ x) ^ 2 ∂(μ : Measure E)) ≤ 2 * n ∧
      ∀ y, hessianKernel u Ψ (gradient u y) = hessianMatrix u y := by
  obtain ⟨u, Ψ, hsm, _hc, _hG, hnorm, hm, _hEvery, _he, _hΨ, _hleft, _hright, _hΨsm,
      hstein, _hsym, _hPD, _hentries, hcoupling, htrace, hHS, hHSbound, _hmean⟩ :=
    exists_regular_smooth_moment_stein_kernel_L2 hn hκ hK hKc hKint hW hstrong μ hμ hiso
  exact ⟨u, Ψ, hsm, hnorm, hm, hstein, htrace, hHS, hHSbound, hcoupling⟩
end RegularClass

/--
Letwin Lemmas 2.7 and 2.9 for the literal source class at one produced potential: the moment-map
Stein kernel `τ` of `μ` has `∫ ‖τ‖²_HS dμ ≤ 2n` and bounds the `H^{-1}(μ)` norm of every linear
function `⟪·, v⟫` by `(∫ ‖τ v‖² dμ)^{1/2}`, with no moment-map property supplied. -/
theorem literal_stein_dual_client (hn : 0 < n) {K U : Set E} (hKb : Bornology.IsBounded K)
    (hKo : IsOpen K) (hKc : Convex ℝ K) (hKne : K.Nonempty) (hU : IsOpen U)
    (hKU : closure K ⊆ U) {V : E → ℝ} (hV : ContDiffOn ℝ ∞ V U) (hVc : ConvexOn ℝ K V)
    (μ : ProbabilityMeasure E)
    (hμ :
      (μ : Measure E) =
        (volume : Measure E).withDensity
          (K.indicator fun p => ENNReal.ofReal (Real.exp (-V p))))
    (hiso : FunctionalInequalities.KLS.Isotropic μ) :
    ∃ (φ : E → ℝ) (Ψ : E → E),
      ((volume : Measure E).tilted (-φ)).map (gradient φ) = (μ : Measure E) ∧
        IsSteinKernel μ (hessianKernel φ Ψ) ∧
          (∫ x, hsNorm (hessianKernel φ Ψ x) ^ 2 ∂(μ : Measure E)) ≤ 2 * n ∧
            ∀ v : E,
              (FunctionalInequalities.Energy.Dual.dualNorm μ
                      (linearLp μ hiso.memLp_two v)).toReal ^
                  2 ≤
                ∫ x, ‖action (hessianKernel φ Ψ x) v‖ ^ 2 ∂(μ : Measure E) := by
  obtain ⟨φ, Ψ, -, -, -, hm, -, -, -, -, -, -, hstein, -, -, -, -, -, -, hHS, -, hdual⟩ :=
    FunctionalInequalities.Probability.MomentMeasure.exists_smooth_moment_stein_kernel_of_bounded_open_convex
      hn hKb hKo hKc hKne hU hKU hV hVc μ hμ hiso
  exact ⟨φ, Ψ, hm, hstein, hHS, fun v => (hdual v).2.2⟩
end LetwinSharpSmoothSteinAudit
#print axioms LetwinSharpSmoothSteinAudit.sharp_smooth_coupling
#print axioms FunctionalInequalities.Analysis.exists_regular_smooth_moment_stein_kernel_L2
#print axioms FunctionalInequalities.Analysis.exists_regular_moment_potential_smooth_trace
#print axioms FunctionalInequalities.Analysis.holder_hessian_of_weak_evolution_fields
#print axioms FunctionalInequalities.Analysis.contDiff_three_of_regular_fields
#print axioms FunctionalInequalities.Analysis.smooth_of_regular_moment_fields
#print axioms
  FunctionalInequalities.Probability.MomentMeasure.exists_smooth_moment_stein_kernel_of_bounded_open_convex
#print axioms LetwinSharpSmoothSteinAudit.literal_stein_dual_client
