import FunctionalInequalities.KLS.Letwin.MomentCalculus

/-! Actual original-input client of the smooth A.4/A.5 producer. -/
noncomputable section
namespace LetwinSmoothCalculusAudit
open Set MeasureTheory FunctionalInequalities.Analysis FunctionalInequalities.Analysis.BakryEmery
open scoped ContDiff
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

/-- At one smooth normalized transporting potential, every bounded smooth test with
Lf + cf >= 0 has an integrable generator with zero mean; no cutoff premise is supplied. -/
theorem source_conservativity_client :
    ∃ u : E → ℝ, ContDiff ℝ ∞ u ∧
      (∫ x, Real.exp (-u x) ∂(volume : Measure E)) = 1 ∧
      ((volume : Measure E).tilted (-u)).map (gradient u) = (μ : Measure E) ∧
      ∀ f : E → ℝ, ContDiff ℝ ∞ f → ∀ D : ℝ, (∀ x, |f x| ≤ D) →
        ∀ c : ℝ, 0 < c → (∀ x, 0 ≤ hessianInverseOperator u W f x + c * f x) →
          Integrable (hessianInverseOperator u W f) ((volume : Measure E).tilted (-u)) ∧
          (∫ x, hessianInverseOperator u W f x ∂((volume : Measure E).tilted (-u))) = 0 := by
  obtain ⟨u, _L, hsm, _hc, _hl, hnorm, hmap, _hPD, _hMA, _hRange, _hId,
    _χ, _C, _hC, _hχ, _hχS, _hχB, _hχM, _hχL, _hχI, _hχD, _hχDL, hA5⟩ :=
    exists_regular_smooth_moment_calculus hn hκ hK hKc hKint hW hstrong μ hμ hiso
  exact ⟨u, hsm, hnorm, hmap, hA5⟩
end RegularClass
end LetwinSmoothCalculusAudit
#print axioms FunctionalInequalities.Analysis.exists_regular_smooth_moment_calculus
#print axioms LetwinSmoothCalculusAudit.source_conservativity_client
