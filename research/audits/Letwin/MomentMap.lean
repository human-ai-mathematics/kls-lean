import FunctionalInequalities.KLS.Letwin.MomentMap

noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace LetwinMomentMapAudit
open FunctionalInequalities FunctionalInequalities.Probability.Stein

/-- Letwin Lemma 2.2 and Theorem 2.5 with `B = Id`: for `K` bounded open convex
nonempty, `V` smooth near `closure K` and convex on `K`, and isotropic `μ = 1_K e^{-V} dx`, some
smooth convex moment potential `φ` with `∇φ : ℝⁿ ≃ₜ K` satisfies `E_ν ‖∇²φ‖²_HS ≤ 2n`; no
moment-map property is assumed. -/
theorem identity_client {n : ℕ} (hn : 0 < n)
    {K U : Set (EuclideanSpace ℝ (Fin n))} (hKb : Bornology.IsBounded K) (hKo : IsOpen K)
    (hKc : Convex ℝ K) (hKne : K.Nonempty) (hU : IsOpen U) (hKU : closure K ⊆ U)
    {V : EuclideanSpace ℝ (Fin n) → ℝ} (hV : ContDiffOn ℝ ∞ V U) (hVc : ConvexOn ℝ K V)
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hμ : (μ : Measure (EuclideanSpace ℝ (Fin n))) =
      (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
        (K.indicator fun p => ENNReal.ofReal (Real.exp (-V p))))
    (hiso : KLS.Isotropic μ) :
    ∃ φ : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ ∞ φ ∧
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-φ)).map (gradient φ) =
        (μ : Measure (EuclideanSpace ℝ (Fin n))) ∧
      (∃ e : EuclideanSpace ℝ (Fin n) ≃ₜ K, ∀ x, (e x : EuclideanSpace ℝ (Fin n)) = gradient φ x) ∧
      (∫ x, (hessianMatrix φ x * hessianMatrix φ x).trace
        ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-φ))) ≤ 2 * n := by
  obtain ⟨φ, -, -, hφ, -, hmap, -, -, he, -, -, htr⟩ :=
    Probability.MomentMeasure.exists_smooth_moment_potential_trace_le_of_bounded_open_convex hn hKb
      hKo hKc hKne hU hKU hV hVc μ hμ hiso
  refine ⟨φ, hφ, hmap, he, ?_⟩
  have h := (htr 1 Matrix.isSymm_one).2
  simpa only [Matrix.one_mul, Matrix.mul_one, Matrix.trace_one, Fintype.card_fin] using h

/-- Letwin Lemmas 2.3 and A.6 at one produced potential: for the literal source class, some
smooth convex moment potential `φ` of `μ` has `E_ν ∇²φ = Id` (as a bilinear form) and satisfies
the scalar Brascamp–Lieb inequality for `ν = e^{-φ} dx` on every bounded `C¹` test. -/
theorem calculus_client {n : ℕ} (hn : 0 < n)
    {K U : Set (EuclideanSpace ℝ (Fin n))} (hKb : Bornology.IsBounded K) (hKo : IsOpen K)
    (hKc : Convex ℝ K) (hKne : K.Nonempty) (hU : IsOpen U) (hKU : closure K ⊆ U)
    {V : EuclideanSpace ℝ (Fin n) → ℝ} (hV : ContDiffOn ℝ ∞ V U) (hVc : ConvexOn ℝ K V)
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hμ : (μ : Measure (EuclideanSpace ℝ (Fin n))) =
      (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
        (K.indicator fun p => ENNReal.ofReal (Real.exp (-V p))))
    (hiso : KLS.Isotropic μ) :
    ∃ φ : EuclideanSpace ℝ (Fin n) → ℝ,
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-φ)).map (gradient φ) =
        (μ : Measure (EuclideanSpace ℝ (Fin n))) ∧
      (∀ u v, (∫ x, bilinearIteratedFDerivTwo ℝ φ x u v
        ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-φ))) = inner ℝ u v) ∧
      ∀ f : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ 1 f → (∃ D : ℝ, ∀ x, |f x| ≤ D) →
        ENNReal.ofReal (ProbabilityTheory.variance f
            ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-φ))) ≤
          ∫⁻ x, ENNReal.ofReal (inner ℝ (gradient f x)
            (Ring.inverse (Analysis.BakryEmery.hessianOperator φ x) (gradient f x)))
            ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-φ)) := by
  obtain ⟨φ, -, -, -, hφ, -, -, -, hnorm, hmap, -, -, -, -, -, h23, -, -, -, hBL⟩ :=
    Probability.MomentMeasure.exists_smooth_moment_calculus_of_bounded_open_convex hn hKb hKo hKc
      hKne hU hKU hV hVc μ hμ hiso
  refine ⟨φ, hmap, fun u v => (h23 u v).2, fun f hf ⟨D, hD⟩ => hBL f hf ?_⟩
  have : IsProbabilityMeasure ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-φ)) :=
    Analysis.BakryEmery.isProbabilityMeasure_tilted_neg_of_integral_eq_one _ φ hnorm
  exact MemLp.of_bound hf.continuous.aestronglyMeasurable D
    (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hD x)

end LetwinMomentMapAudit
#print axioms FunctionalInequalities.Analysis.exists_contDiff_eqOn_closure
#print axioms FunctionalInequalities.Analysis.smooth_moment_potential_of_lipschitzWith_gradient
#print axioms FunctionalInequalities.Analysis.exists_regular_moment_potential_smooth_on_range
#print axioms FunctionalInequalities.Probability.MomentMeasure.exists_centered_regular_potential
#print axioms FunctionalInequalities.Probability.MomentMeasure.exists_smooth_moment_potential_of_bounded_open_convex
#print axioms FunctionalInequalities.Probability.MomentMeasure.exists_smooth_moment_potential_trace_le_of_bounded_open_convex
#print axioms LetwinMomentMapAudit.identity_client
#print axioms FunctionalInequalities.Probability.MomentMeasure.exists_smooth_moment_calculus_of_bounded_open_convex
#print axioms LetwinMomentMapAudit.calculus_client
