import FunctionalInequalities.KLS.CEK.Uniqueness

/-! Client of CEK Theorem 2 for essentially continuous potentials (Cordero-Erausquin–Klartag
arXiv:1304.0630v1, Theorem 2, existence and uniqueness; Letwin arXiv:2607.24164v1, Lemma 2.1),
of CEK Theorem 8 (18) for essentially continuous potentials, of CEK Proposition 7 and of the
supporting results: the Fenchel–Moreau theorem, linear growth, the ball truncations of the
conjugate, the line-by-line variation estimates (CEK Lemmas 3, 4, 9) and the integration by parts
bound (CEK Lemma 5). -/
noncomputable section
namespace LetwinEssentialUniquenessAudit
open MeasureTheory Set FunctionalInequalities.Analysis
open FunctionalInequalities.Probability.MomentMeasure

/-- On `ℝⁿ`, with the moment measure and essential continuity written out: two convex essentially
continuous potentials with the same finite nonzero moment measure are translates of each other. -/
theorem translate_client {n : ℕ} {μ : Measure (EuclideanSpace ℝ (Fin n))} [IsFiniteMeasure μ]
    (hμ : μ ≠ 0) {ψ₀ ψ₁ : EuclideanSpace ℝ (Fin n) → EReal}
    (hψ₀ : ConvexPotential ψ₀) (hψ₁ : ConvexPotential ψ₁)
    (hl₀ : LowerSemicontinuous ψ₀) (hl₁ : LowerSemicontinuous ψ₁)
    (hd₀ : μH[(n : ℝ) - 1] {x | ¬ContinuousAt ψ₀ x} = 0)
    (hd₁ : μH[(n : ℝ) - 1] {x | ¬ContinuousAt ψ₁ x} = 0)
    (hm₀ : ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
      (fun x => EReal.exp (-ψ₀ x))).map (gradient fun x => (ψ₀ x).toReal) = μ)
    (hm₁ : ((volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
      (fun x => EReal.exp (-ψ₁ x))).map (gradient fun x => (ψ₁ x).toReal) = μ) :
    ∃ y₀ : EuclideanSpace ℝ (Fin n), ∀ y, ψ₁ y = ψ₀ (y - y₀) := by
  have hdim : (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) : ℝ) = n := by simp
  exact FunctionalInequalities.KLS.CEK.exists_eq_translate_of_ofPotential_eq_of_essentiallyContinuous
    hμ hψ₀ hψ₁ ⟨hl₀, by rw [hdim]; exact hd₀⟩ ⟨hl₁, by rw [hdim]; exact hd₁⟩ hm₀ hm₁

/-- CEK (18) on `ℝⁿ`: for a normalized convex essentially continuous `ψ₀` with moment measure `μ`
and a convex lower semicontinuous `ψ₁` whose conjugate is `μ`-integrable,
`log ∫ e^{-ψ₁} ≤ ∫ (ψ₁* − ψ₀*) dμ`. -/
theorem prekopa_client {n : ℕ} {ψ₀ ψ₁ : EuclideanSpace ℝ (Fin n) → EReal}
    (hψ₀ : ConvexPotential ψ₀) (hess : EssentiallyContinuous ψ₀)
    (hmass : ∫⁻ x, EReal.exp (-ψ₀ x) = 1)
    (hψ₁ : ConvexPotential ψ₁) (hl₁ : LowerSemicontinuous ψ₁) (hne₁ : ∃ x, ψ₁ x ≠ ⊤)
    (hint₁ : PotentialIntegrable (legendre ψ₁) (ofPotential volume ψ₀)) :
    ENNReal.log (∫⁻ x, EReal.exp (-ψ₁ x)) ≤
      (((∫ p, (legendre ψ₁ p).toReal ∂ofPotential volume ψ₀) -
        ∫ p, (legendre ψ₀ p).toReal ∂ofPotential volume ψ₀ : ℝ) : EReal) := by
  have hm : mass volume ψ₀ = 1 := hmass
  have h := variationalFunctional_le_legendre hψ₀ hess hm hint₁
  have hne₀ : ∃ x, ψ₀ x ≠ ⊤ := by
    obtain ⟨x, hx⟩ := interior_domain_nonempty_of_mass_ne_zero volume hψ₀
      (by rw [hm]; exact one_ne_zero)
    exact ⟨x, interior_subset hx⟩
  simp only [variationalFunctional, legendre_legendre_eq hψ₁ hl₁ hne₁,
    legendre_legendre_eq hψ₀ hess.1 hne₀, hm, ENNReal.log_one, zero_sub] at h
  have h2 := (EReal.sub_le_iff_le_add (.inr (EReal.coe_ne_top _))
    (.inr (EReal.coe_ne_bot _))).mp h
  change ENNReal.log (mass volume ψ₁) ≤ _
  refine h2.trans (le_of_eq ?_)
  rw [← EReal.coe_add]
  congr 1
  ring

end LetwinEssentialUniquenessAudit
#print axioms FunctionalInequalities.Analysis.le_legendre_legendre_of_affine_le
#print axioms FunctionalInequalities.Analysis.legendre_legendre_eq
#print axioms FunctionalInequalities.Analysis.integral_rightDeriv_mul_exp_neg
#print axioms FunctionalInequalities.Analysis.integral_abs_rightDeriv_mul_exp_neg_le
#print axioms FunctionalInequalities.Analysis.two_mul_exp_neg_sub_le_integral_abs
#print axioms FunctionalInequalities.Probability.MomentMeasure.exists_affine_minorant
#print axioms FunctionalInequalities.Probability.MomentMeasure.exists_linear_lower_bound_of_mass
#print axioms FunctionalInequalities.Probability.MomentMeasure.ballTruncate
#print axioms FunctionalInequalities.Probability.MomentMeasure.ballTruncate_of_norm_le
#print axioms FunctionalInequalities.Probability.MomentMeasure.le_ballTruncate
#print axioms FunctionalInequalities.Probability.MomentMeasure.ballTruncate_anti
#print axioms FunctionalInequalities.Probability.MomentMeasure.lowerSemicontinuous_ballTruncate
#print axioms FunctionalInequalities.Probability.MomentMeasure.legendre_le_of_linear_lower_bound
#print axioms FunctionalInequalities.Probability.MomentMeasure.legendre_ballTruncate_mono
#print axioms FunctionalInequalities.Probability.MomentMeasure.legendre_ballTruncate_le
#print axioms FunctionalInequalities.Probability.MomentMeasure.iSup_legendre_ballTruncate
#print axioms FunctionalInequalities.Probability.MomentMeasure.linear_lower_bound_legendre_ballTruncate
#print axioms FunctionalInequalities.Probability.MomentMeasure.legendre_ballTruncate_le_add
#print axioms FunctionalInequalities.Probability.MomentMeasure.legendre_ballTruncate_le_add_norm
#print axioms FunctionalInequalities.Probability.MomentMeasure.ballTruncate_legendre_zero_ne_top
#print axioms FunctionalInequalities.Probability.MomentMeasure.legendre_ballTruncate_ne_top_ne_bot
#print axioms FunctionalInequalities.Probability.MomentMeasure.convexOn_toReal_legendre_ballTruncate
#print axioms FunctionalInequalities.Probability.MomentMeasure.norm_gradient_toReal_legendre_ballTruncate_le
#print axioms FunctionalInequalities.Probability.MomentMeasure.legendre_gradient_toReal_legendre_ballTruncate
#print axioms FunctionalInequalities.Probability.MomentMeasure.legendre_gradient_le
#print axioms FunctionalInequalities.Probability.MomentMeasure.legendre_ballTruncate_eq_of_norm_gradient_le
#print axioms FunctionalInequalities.Probability.MomentMeasure.gradient_toReal_legendre_ballTruncate_eq
#print axioms FunctionalInequalities.Probability.MomentMeasure.addHaar_eq_zero_of_hausdorffMeasure_eq_zero
#print axioms FunctionalInequalities.Probability.MomentMeasure.addHaar_setOf_exists_line_mem_eq_zero
#print axioms FunctionalInequalities.Probability.MomentMeasure.ae_ae_line_notMem
#print axioms FunctionalInequalities.Probability.MomentMeasure.iSup_legendre_ballTruncate_add
#print axioms FunctionalInequalities.Probability.MomentMeasure.lintegral_directional_truncate_le_const
#print axioms FunctionalInequalities.Probability.MomentMeasure.eventually_lintegral_directional_truncate_le
#print axioms FunctionalInequalities.Probability.MomentMeasure.legendre_gradient_eq_of_mem_interior
#print axioms FunctionalInequalities.Probability.MomentMeasure.ae_mem_interior_differentiableAt
#print axioms FunctionalInequalities.Probability.MomentMeasure.lintegral_ofPotential
#print axioms FunctionalInequalities.Probability.MomentMeasure.norm_le_sum_abs_inner
#print axioms FunctionalInequalities.Probability.MomentMeasure.toReal_legendre_ballTruncate_eq
#print axioms FunctionalInequalities.Probability.MomentMeasure.density_eq_ofReal'
#print axioms FunctionalInequalities.Probability.MomentMeasure.lintegral_indicator_abs_inner_gradient_lt_top
#print axioms FunctionalInequalities.Probability.MomentMeasure.integrable_norm_ofPotential
#print axioms FunctionalInequalities.Probability.MomentMeasure.lintegral_indicator_inner_gradient_sub_le
#print axioms FunctionalInequalities.Probability.MomentMeasure.potentialIntegrable_legendre
#print axioms FunctionalInequalities.Probability.MomentMeasure.lintegral_le_exp_of_convexOn
#print axioms FunctionalInequalities.Probability.MomentMeasure.variationalFunctional_le_legendre
#print axioms FunctionalInequalities.KLS.CEK.exists_eq_translate_of_ofPotential_eq_of_essentiallyContinuous
#print axioms FunctionalInequalities.KLS.CEK.exists_essentiallyContinuous_ofPotential_eq_unique
#print axioms LetwinEssentialUniquenessAudit.translate_client
#print axioms LetwinEssentialUniquenessAudit.prekopa_client
