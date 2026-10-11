import FunctionalInequalities.KLS.LogConcave.Stein

/-!
# Audit: Letwin Stein kernels, A.7 and Lemma 2.9 with source-style consumers

Source: Letwin, arXiv:2607.24164v1, Definition 2.6, (2.19), Lemma 2.9 and Appendix A.7. Clients:
the Hilbert–Schmidt normalization of the identity on `ℝ²` is `√2` (not the operator norm `1`); the
norm test `x ↦ ‖x‖` (locally Lipschitz, not compactly supported) satisfies A.7 for every
full-dimensional log-concave law with a Stein kernel and is a unit-energy test; constant inputs
have infinite `H^{-1}` norm (constants are zero-energy tests), so the extended-valued definition is
needed. No Stein kernel is constructed; Letwin Theorems 1.1–1.2 and the moment-map kernel are not
asserted. Clients adapted from the Codex bundle `Letwin-A7` (author `SourceClients.lean`, reviewer
`UnboundedClient.lean`).
-/

open MeasureTheory FunctionalInequalities
open FunctionalInequalities.Energy.Euclidean.LipschitzApproximation
open scoped RealInnerProductSpace Matrix.Norms.Frobenius

namespace LetwinSteinAudit

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E]

/-- The HS normalization of the two-dimensional identity is sqrt2, not operator norm1. -/
theorem identity_two_hs_sq : Probability.Stein.hsNorm (1 : Probability.Stein.KernelMatrix 2) ^ 2 = 2 := by
  rw [Probability.Stein.hsNorm_eq_sqrt]
  norm_num [Matrix.one_apply, Fin.sum_univ_two]

/-- The actual Lipschitz norm test is generally nonsmooth and not compactly supported.
LC derives its value-L2 data; the actual global Lipschitz gradient bound derives gradient-L2. -/
theorem norm_test_source_A7 {n : ℕ} (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (τ : EuclideanSpace ℝ (Fin n) → Probability.Stein.KernelMatrix n) (hK : Probability.Stein.IsSteinKernel μ τ)
    (hLC : KLS.LogConcave μ) (hfull : Probability.affineSupport μ = ⊤)
    (hSym : Probability.Stein.SymmetricAE μ τ) (hHS : MemLp (fun x => Probability.Stein.hsNorm (τ x)) 2 (μ : Measure (EuclideanSpace ℝ (Fin n))))
    (v : EuclideanSpace ℝ (Fin n)) :
    (∫ x, ⟪x, v⟫ * ‖x‖ ∂(μ : Measure (EuclideanSpace ℝ (Fin n)))) =
        (∫ x, ⟪Probability.Stein.action (τ x) v, gradient (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖) x⟫ ∂(μ : Measure (EuclideanSpace ℝ (Fin n)))) ∧
      |∫ x, ⟪x, v⟫ * ‖x‖ ∂(μ : Measure (EuclideanSpace ℝ (Fin n)))| ≤
        Real.sqrt (∫ x, ‖Probability.Stein.action (τ x) v‖ ^ 2 ∂(μ : Measure (EuclideanSpace ℝ (Fin n)))) *
          Real.sqrt (∫ x, ‖gradient (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖) x‖ ^ 2 ∂(μ : Measure (EuclideanSpace ℝ (Fin n)))) := by
  have hμ2 := (KLS.LogConcave.absolutelyContinuous_and_memLp_two_of_affineSupport_eq_top μ hLC hfull).2
  have hnorm2 : MemLp (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖) 2 (μ : Measure (EuclideanSpace ℝ (Fin n))) := by
    simpa only [id_eq] using hμ2.norm
  have hlip : LipschitzWith 1 (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖) := lipschitzWith_one_norm
  have hgrad2 : MemLp (gradient (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖)) 2 (μ : Measure (EuclideanSpace ℝ (Fin n))) :=
    MemLp.of_bound (aestronglyMeasurable_gradient _ _) 1
      (Filter.Eventually.of_forall fun x => norm_gradient_le_of_lipschitz hlip x)
  exact KLS.LogConcave.stein_identity_of_affineSupport_eq_top μ τ hK hLC hfull hSym hHS (fun x => ‖x‖) hlip.locallyLipschitz hnorm2 hgrad2 v

/-- Energy-normalized norm test really lies in the full source H^-1 test class. -/
noncomputable def normUnitTest {n : ℕ} (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))) (hLC : KLS.LogConcave μ)
    (hfull : Probability.affineSupport μ = ⊤) : Energy.Dual.UnitEnergyTest μ where
  fn := fun x => ‖x‖
  locallyLipschitz := (lipschitzWith_one_norm : LipschitzWith 1 (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖)).locallyLipschitz
  memLp := by simpa only [id_eq] using (KLS.LogConcave.absolutelyContinuous_and_memLp_two_of_affineSupport_eq_top μ hLC hfull).2.norm
  gradLp := MemLp.of_bound (aestronglyMeasurable_gradient _ _) 1
    (Filter.Eventually.of_forall fun x => norm_gradient_le_of_lipschitz ((lipschitzWith_one_norm : LipschitzWith 1 (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖))) x)
  energy := by
    apply (Energy.Dual.unit_gradient_norm_iff μ _).mpr
    have hpoint : ∀ x : EuclideanSpace ℝ (Fin n), ‖gradient (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖) x‖ ^ 2 ≤ 1 := by
      intro x
      have h := norm_gradient_le_of_lipschitz ((lipschitzWith_one_norm : LipschitzWith 1 (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖))) x
      change ‖gradient (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖) x‖ ≤ (1 : ℝ) at h
      nlinarith [norm_nonneg (gradient (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖) x)]
    have hg := (aestronglyMeasurable_gradient (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖) (μ : Measure (EuclideanSpace ℝ (Fin n))))
    have hgrad2 : MemLp (gradient (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖)) 2 (μ : Measure (EuclideanSpace ℝ (Fin n))) :=
      MemLp.of_bound hg 1 (Filter.Eventually.of_forall fun x => norm_gradient_le_of_lipschitz
        ((lipschitzWith_one_norm : LipschitzWith 1 (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖))) x)
    have hi := (memLp_two_iff_integrable_sq_norm hgrad2.aestronglyMeasurable).mp hgrad2
    have hle := integral_mono hi (integrable_const (1 : ℝ)) hpoint
    simpa only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] using hle


noncomputable def constantTest (μ : ProbabilityMeasure E) (c : ℝ) : Energy.Dual.UnitEnergyTest μ where
  fn := fun _ => c
  locallyLipschitz := LocallyLipschitz.const c
  memLp := memLp_const c
  gradLp := by rw [gradient_fun_const']; exact memLp_const (0 : E)
  energy := by
    rw [Lp.norm_toLp, gradient_fun_const']
    change (eLpNorm (0 : E → E) 2 (μ : Measure E)).toReal ≤ 1
    simp

noncomputable def oneInput (μ : ProbabilityMeasure E) : Lp ℝ 2 (μ : Measure E) :=
  (memLp_const (μ := (μ : Measure E)) (p := 2) (1 : ℝ)).toLp (fun _ => 1)

theorem pairing_one_constant (μ : ProbabilityMeasure E) (c : ℝ) :
    Energy.Dual.pairing μ (oneInput μ) (constantTest μ c) = c := by
  change ⟪(memLp_const (μ := (μ : Measure E)) (p := 2) (1 : ℝ)).toLp (fun _ => 1),
    (memLp_const (μ := (μ : Measure E)) (p := 2) c).toLp (fun _ => c)⟫ = c
  rw [← L2.integral_inner_toLp]
  simp

theorem actual_unbounded_dual (μ : ProbabilityMeasure E) :
    Energy.Dual.dualNorm μ (oneInput μ) = ⊤ := by
  by_contra h
  obtain ⟨n, hn⟩ := exists_nat_gt (Energy.Dual.dualNorm μ (oneInput μ)).toReal
  have hb := Energy.Dual.pairing_le_toReal_of_ne_top μ (oneInput μ) h (constantTest μ (n : ℝ))
  rw [pairing_one_constant] at hb
  exact (not_le_of_gt hn) hb

end LetwinSteinAudit

#print axioms FunctionalInequalities.Probability.Stein.norm_action_le_hsNorm
#print axioms FunctionalInequalities.Probability.Stein.compact_directional_identity
#print axioms FunctionalInequalities.Probability.Stein.extended_identity_of_ac
#print axioms FunctionalInequalities.Probability.Stein.extended_abs_bound_of_ac
#print axioms FunctionalInequalities.Probability.Stein.linear_dual_bound_of_ac
#print axioms FunctionalInequalities.Energy.Dual.toReal_dualNorm_eq_signed_sSup
#print axioms FunctionalInequalities.Energy.Dual.dualNorm_eq_iSup_abs
#print axioms FunctionalInequalities.KLS.LogConcave.stein_identity_of_affineSupport_eq_top
#print axioms FunctionalInequalities.KLS.LogConcave.dualNorm_linear_sq_le_of_affineSupport_eq_top
#print axioms FunctionalInequalities.KLS.LogConcave.dualNorm_linear_sq_le_of_affineSupport_eq_top'
#print axioms LetwinSteinAudit.identity_two_hs_sq
#print axioms LetwinSteinAudit.norm_test_source_A7
#print axioms LetwinSteinAudit.normUnitTest
#print axioms LetwinSteinAudit.pairing_one_constant
#print axioms LetwinSteinAudit.actual_unbounded_dual
