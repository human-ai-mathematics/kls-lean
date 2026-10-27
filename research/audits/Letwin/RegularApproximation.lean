import FunctionalInequalities.KLS.Letwin.Approximation
import FunctionalInequalities.KLS.Letwin.RegularClass
import FunctionalInequalities.KLS.Letwin.QuadraticBound
import Mathlib.Analysis.Convex.Measure

/-!
# Audit clients of Letwin's regular approximation (Lemma A.1)

* `letwinQuadraticBound_of_regular_approximation`: Letwin Theorem 1.2 for every isotropic log-concave law, re-derived
  through `exists_regular_approximation` and the compact regular-class bound on `closure (K j)` (null frontier). This is
  an alternate derivation for audit only; the public endpoint remains `KLS.LogConcave.letwinQuadraticBound`.
* `finite_polynomial_sum`: every finite sum of mixed linear monomials of degree at most four has convergent expectations
  along the approximants (independently checked client, adapted to the canonical names). No `MvPolynomial` interface.
-/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped RealInnerProductSpace ENNReal

namespace LetwinRegularApproximationAudit

open FunctionalInequalities FunctionalInequalities.KLS.LogConcave
open FunctionalInequalities.Analysis.BakryEmery

/-- A convex set and its closure carry the same `withDensity` measure for an additive Haar measure. -/
private theorem withDensity_indicator_closure {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
    {K : Set E} (hK : Convex ℝ K) (g : E → ℝ≥0∞) :
    μ.withDensity ((closure K).indicator g) = μ.withDensity (K.indicator g) := by
  refine withDensity_congr_ae ?_
  have hnull : ∀ᵐ x ∂μ, x ∉ frontier K := measure_eq_zero_iff_ae_notMem.1 (hK.addHaar_frontier μ)
  filter_upwards [hnull] with x hx
  by_cases hk : x ∈ K
  · simp [hk, subset_closure hk]
  · have hc : x ∉ closure K := fun hc => hx ⟨hc, fun hi => hk (interior_subset hi)⟩
    simp [hk, hc]

private theorem memLp_four {n : ℕ} (ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hν : KLS.LogConcave ν) : MemLp id 4 (ν : Measure (EuclideanSpace ℝ (Fin n))) :=
  (integrable_norm_rpow_iff (p := 4) continuous_id.aestronglyMeasurable (by norm_num)
    (by norm_num)).mp (by simpa using hν.integrable_norm_pow 4)

/-- Letwin Theorem 1.2 for an arbitrary isotropic log-concave law through Lemma A.1 and the compact regular-class
bound `regularClass_letwinQuadraticBound`. -/
theorem letwinQuadraticBound_of_regular_approximation {n : ℕ} (hn : 0 < n)
    {μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))} (hLC : KLS.LogConcave μ) (hiso : KLS.Isotropic μ) :
    LetwinQuadraticBound (μ : Measure (EuclideanSpace ℝ (Fin n))) := by
  obtain ⟨η, K, V, hη, hmom⟩ := exists_regular_approximation μ hLC hiso
  refine letwinQuadraticBound_of_tendsto_moments (fun j => (η j : Measure (EuclideanSpace ℝ (Fin n))))
    (μ : Measure (EuclideanSpace ℝ (Fin n))) (fun j => memLp_four _ (hη j).1) (memLp_four _ hLC) hmom
    fun j => ?_
  obtain ⟨_hLCj, hisoj, hopen, hbdd, hconv, hne, -, ⟨κ, hκ, hV, hVc⟩, heq⟩ := hη j
  have hKc : IsCompact (closure (K j)) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure hbdd.closure
  have hint : (interior (closure (K j))).Nonempty :=
    hne.mono (hopen.subset_interior_iff.2 subset_closure)
  refine regularClass_letwinQuadraticBound hn hκ hKc hconv.closure hint hV hVc (η j) ?_ hisoj
  rw [withDensity_indicator_closure volume hconv]
  exact heq

/-- Every finite sum of mixed linear monomials of degree at most four has convergent expectations along the
isotropic approximants of Lemma A.1. -/
theorem finite_polynomial_sum {n m : ℕ}
    (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hLC : KLS.LogConcave μ) (hiso : KLS.Isotropic μ)
    (d : Fin m → ℕ) (hd : ∀ i, d i ≤ 4)
    (a : Fin m → ℝ) (v : (i : Fin m) → Fin (d i) → EuclideanSpace ℝ (Fin n)) :
    ∃ η : ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin n)),
      (∀ k, KLS.Isotropic (η k)) ∧
      Tendsto
        (fun k => ∫ x, ∑ i, a i * ∏ j, ⟪v i j, x⟫
          ∂(η k : Measure (EuclideanSpace ℝ (Fin n)))) atTop
        (𝓝 (∫ x, ∑ i, a i * ∏ j, ⟪v i j, x⟫
          ∂(μ : Measure (EuclideanSpace ℝ (Fin n))))) := by
  obtain ⟨η, K, V, hη, hmom⟩ := exists_regular_approximation μ hLC hiso
  have hint (ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
      (hν : KLS.LogConcave ν) (i : Fin m) :
      Integrable (fun x => ∏ j, ⟪v i j, x⟫)
        (ν : Measure (EuclideanSpace ℝ (Fin n))) := by
    obtain ⟨r, hr, hexp⟩ := ((KLS.LogConcave.borel_iff ν).1 hν).exists_integrable_exp_norm
    simpa only [real_inner_comm] using
      FunctionalInequalities.Probability.integrable_prod_inner_of_exp (ν : Measure (EuclideanSpace ℝ (Fin n))) hr hexp (d i) (v i)
  have integral_eq (ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
      (hν : KLS.LogConcave ν) :
      (∫ x, ∑ i, a i * ∏ j, ⟪v i j, x⟫
        ∂(ν : Measure (EuclideanSpace ℝ (Fin n)))) =
      ∑ i, a i * ∫ x, ∏ j, ⟪v i j, x⟫
        ∂(ν : Measure (EuclideanSpace ℝ (Fin n))) := by
    rw [integral_finsetSum _ (fun i _ => (hint ν hν i).const_mul (a i))]
    simp_rw [integral_const_mul]
  refine ⟨η, fun k => (hη k).2.1, ?_⟩
  simp_rw [integral_eq (η _) (hη _).1, integral_eq μ hLC]
  exact tendsto_finsetSum _ fun i _ => (hmom (d i) (hd i) (v i)).const_mul (a i)

end LetwinRegularApproximationAudit

#print axioms FunctionalInequalities.Probability.tendsto_integral_prod_inner_of_coord
#print axioms FunctionalInequalities.Probability.prod_coord_eq_prod_inner_single
#print axioms FunctionalInequalities.KLS.LogConcave.integrable_norm_pow
#print axioms FunctionalInequalities.KLS.LogConcave.Suspension.exists_compact_moment_approximation
#print axioms FunctionalInequalities.KLS.LogConcave.exists_regularClass_seq_of_compact
#print axioms FunctionalInequalities.KLS.LogConcave.exists_regular_approximation
#print axioms FunctionalInequalities.KLS.LogConcave.exists_regular_approximation_eps
#print axioms FunctionalInequalities.KLS.LogConcave.Suspension.letwinCompactBound_of_regularClass
#print axioms FunctionalInequalities.KLS.LogConcave.Suspension.letwinCompactBound
#print axioms FunctionalInequalities.KLS.LogConcave.letwinQuadraticBound
#print axioms FunctionalInequalities.KLS.LogConcave.matrix_variance_le_eight
#print axioms LetwinRegularApproximationAudit.letwinQuadraticBound_of_regular_approximation
#print axioms LetwinRegularApproximationAudit.finite_polynomial_sum
