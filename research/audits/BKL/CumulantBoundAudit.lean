import solutions.ThmBklCumulantBound

/-!
Independent source specification and clients of the BKL Theorem 4.1 certificate.
`Expected` is handwritten in the source index m ≥ 2 (order m, with m − 1 free slots), with the single
universal K outside every order, dimension, law and direction, the coordinate sum (65), the factor
K^{m−1}((m−1)!)² and the norm square. No compactness hypothesis appears anywhere.
-/

noncomputable section
open MeasureTheory
namespace CumulantBoundAudit

/-- BKL Theorem 4.1, (65)–(66), handwritten in the source order m ≥ 2. -/
def Expected : Prop :=
  ∃ K : ℝ, 1 ≤ K ∧ ∀ m : ℕ, 2 ≤ m →
    ∀ (n : ℕ) (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))),
      FunctionalInequalities.KLS.Isotropic μ →
      FunctionalInequalities.KLS.LogConcave μ →
      ∀ u : EuclideanSpace ℝ (Fin n),
        ∑ J : Fin (m - 1) → Fin n,
            FunctionalInequalities.Analysis.BakryEmery.cumulant
                (μ : Measure (EuclideanSpace ℝ (Fin n))) (m - 1 + 1)
                (Fin.cons u fun k => EuclideanSpace.basisFun (Fin n) ℝ (J k)) ^ 2 ≤
          K ^ (m - 1) * ((m - 1).factorial : ℝ) ^ 2 * ‖u‖ ^ 2

/-- The certificate gives the source-indexed statement. -/
theorem expected : Expected := by
  obtain ⟨K, hK, h⟩ := Solutions.ThmBklCumulantBound.certificate
  exact ⟨K, hK, fun m hm => h (m - 1) (by omega)⟩

/-- The base order m = 2 with the same universal K: Σ_j κ₂(μ)(u, e_j)² ≤ K ‖u‖². -/
theorem base_order : ∃ K : ℝ, 1 ≤ K ∧
    ∀ (n : ℕ) (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))),
      FunctionalInequalities.KLS.Isotropic μ → FunctionalInequalities.KLS.LogConcave μ →
      ∀ u : EuclideanSpace ℝ (Fin n),
        ∑ J : Fin 1 → Fin n,
            FunctionalInequalities.Analysis.BakryEmery.cumulant
                (μ : Measure (EuclideanSpace ℝ (Fin n))) 2
                (Fin.cons u fun k => EuclideanSpace.basisFun (Fin n) ℝ (J k)) ^ 2 ≤ K * ‖u‖ ^ 2 := by
  obtain ⟨K, hK, h⟩ := Solutions.ThmBklCumulantBound.certificate
  refine ⟨K, hK, fun n μ hiso hLC u => ?_⟩
  have hb := h 1 le_rfl n μ hiso hLC u
  simpa using hb

/-- Noncompact consumption of the closed certificate: one K ≥ 1 taken from
`Solutions.ThmBklCumulantBound.certificate` bounds the third order (the Lemma 4.2 order) for an arbitrary
isotropic log-concave law in every dimension, with no support, Letwin or bound hypothesis. -/
theorem third_order_arbitrary_law : ∃ K : ℝ, 1 ≤ K ∧
    ∀ (n : ℕ) (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))),
      FunctionalInequalities.KLS.Isotropic μ → FunctionalInequalities.KLS.LogConcave μ →
      ∀ u : EuclideanSpace ℝ (Fin n),
        ∑ J : Fin 2 → Fin n,
            FunctionalInequalities.Analysis.BakryEmery.cumulant
                (μ : Measure (EuclideanSpace ℝ (Fin n))) 3
                (Fin.cons u fun k => EuclideanSpace.basisFun (Fin n) ℝ (J k)) ^ 2 ≤
          K ^ 2 * 4 * ‖u‖ ^ 2 := by
  obtain ⟨K, hK, h⟩ := Solutions.ThmBklCumulantBound.certificate
  refine ⟨K, hK, fun n μ hiso hLC u => ?_⟩
  have hb := h 2 (by norm_num) n μ hiso hLC u
  have hf : ((Nat.factorial 2 : ℕ) : ℝ) ^ 2 = 4 := by norm_num [Nat.factorial]
  calc _ ≤ K ^ 2 * ((Nat.factorial 2 : ℕ) : ℝ) ^ 2 * ‖u‖ ^ 2 := hb
    _ = K ^ 2 * 4 * ‖u‖ ^ 2 := by rw [hf]

/-- The base and third orders hold with the same certificate constant. -/
theorem base_and_third_same_constant : ∃ K : ℝ, 1 ≤ K ∧
    ∀ (n : ℕ) (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))),
      FunctionalInequalities.KLS.Isotropic μ → FunctionalInequalities.KLS.LogConcave μ →
      ∀ u : EuclideanSpace ℝ (Fin n),
        (∑ J : Fin 1 → Fin n,
            FunctionalInequalities.Analysis.BakryEmery.cumulant
                (μ : Measure (EuclideanSpace ℝ (Fin n))) 2
                (Fin.cons u fun k => EuclideanSpace.basisFun (Fin n) ℝ (J k)) ^ 2 ≤ K * ‖u‖ ^ 2) ∧
        (∑ J : Fin 2 → Fin n,
            FunctionalInequalities.Analysis.BakryEmery.cumulant
                (μ : Measure (EuclideanSpace ℝ (Fin n))) 3
                (Fin.cons u fun k => EuclideanSpace.basisFun (Fin n) ℝ (J k)) ^ 2 ≤ K ^ 2 * 4 * ‖u‖ ^ 2) := by
  obtain ⟨K, hK, h⟩ := Solutions.ThmBklCumulantBound.certificate
  refine ⟨K, hK, fun n μ hiso hLC u => ⟨?_, ?_⟩⟩
  · simpa using h 1 le_rfl n μ hiso hLC u
  · have hb := h 2 (by norm_num) n μ hiso hLC u
    have hf : ((Nat.factorial 2 : ℕ) : ℝ) ^ 2 = 4 := by norm_num [Nat.factorial]
    calc _ ≤ K ^ 2 * ((Nat.factorial 2 : ℕ) : ℝ) ^ 2 * ‖u‖ ^ 2 := hb
      _ = K ^ 2 * 4 * ‖u‖ ^ 2 := by rw [hf]

#print axioms expected
#print axioms base_order
#print axioms third_order_arbitrary_law
#print axioms base_and_third_same_constant

end CumulantBoundAudit
