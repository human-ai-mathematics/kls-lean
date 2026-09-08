import FunctionalInequalities.Energy.Euclidean.CovarianceGradient.Core
import FunctionalInequalities.Poincare.Euclidean.LiteratureComparison
import FunctionalInequalities.Poincare.Relaxation
import FunctionalInequalities.Probability.CovarianceSqrt

/-!
# The identity-weighted Lipschitz gradient relaxation and the literature constant

Source: Blueprint `thm:affine-isotropic-reduction`, the passages "pullback of the isotropic inequality
gives the covariance-form inequality, first on the raw tests and then on their relaxation" and
"item (3) implies item (2) from `⟪Cov v, v⟫ ≤ ‖Cov‖ ‖v‖²`, together with cutoff and truncation from
locally to globally Lipschitz tests". Read `lipschitzGradientRelaxation`,
`L2Energy.holds_lipschitzGradientRelaxation_iff_literatureHolds`,
`Poincare.constant_eq_lipschitzGradientRelaxation`, `covarianceRelaxation_eq_lipschitzGradientRelaxation`
and `covarianceRelaxation_le_opNorm_mul_lipschitzGradientRelaxation`.

For a probability law `ν` on a finite-dimensional Euclidean space `V` that is absolutely continuous
with respect to Haar measure and has a null support frontier, the sequential relaxation of the
squared-norm energy `f ↦ ‖∇f‖²` of the gradient operator on globally Lipschitz tests (the weighted
gradient operator of `lem:covariance-core-closure` with `B = 1`) has the same finite Poincaré
constants as the locally Lipschitz literature class and the same optimal constant as the legacy
smooth-test constant `Poincare.constant ν`: one direction relaxes the raw inequality on Lipschitz
tests, the other approximates a locally Lipschitz literature test by smooth compactly supported
functions in the weighted graph norm (the certified approximation lemma with `B = 1`). When the
covariance operator is the identity the covariance relaxation of `def:affine-poincare-constant` is
this relaxation; in general the covariance relaxation is at most `‖Σ‖` times it.

Nothing here asserts a Poincaré inequality, finiteness of any constant, or log-concavity; the
log-concave discharge of the two hypotheses is in `KLS/LogConcave/CovarianceClosure.lean`. The
zero-dimensional space is included.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ContDiff

namespace FunctionalInequalities.Energy.Euclidean

universe u

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]

/- The common ambient assumptions are intentionally kept uniform across the public API. -/
set_option linter.unusedSectionVars false

variable (ν : ProbabilityMeasure V) (m : Measure V) [m.IsAddHaarMeasure]

/-- The identity-weighted gradient is the gradient. -/
theorem weightedGradient_id (g : V → ℝ) :
    weightedGradient (ContinuousLinearMap.id ℝ V) g = gradient g := by
  funext x
  rfl

/-- The sequential relaxation of `f ↦ ‖∇f‖²` on the classes of globally Lipschitz `L²(ν)` functions
with square-integrable gradient: the weighted gradient operator with `B = 1`. -/
def lipschitzGradientRelaxation (hac : (ν : Measure V) ≪ m) :
    Functional (Lp ℝ 2 (ν : Measure V)) :=
  (PreEnergy.ofLinearPMap (gradientOperator ν (ContinuousLinearMap.id ℝ V) hac)).sequentialRelaxation

/-- The literature energy of a locally Lipschitz function with square-integrable gradient is the
real integral of the squared gradient norm, under absolute continuity. -/
theorem _root_.FunctionalInequalities.KLS.literatureEnergy_eq_ofReal_integral_sq_norm_gradient
    (hac : (ν : Measure V) ≪ m) (f : V → ℝ) (hf : LocallyLipschitz f)
    (hg : MemLp (gradient f) 2 (ν : Measure V)) :
    KLS.literatureEnergy ν f = ENNReal.ofReal (∫ x, ‖gradient f x‖ ^ 2 ∂(ν : Measure V)) := by
  rw [KLS.literatureEnergy_eq_lintegral_gradient ν m hac f hf,
    ofReal_integral_eq_lintegral_ofReal ((memLp_two_iff_integrable_sq_norm hg.1).mp hg)
      (ae_of_all _ fun x ↦ sq_nonneg ‖gradient f x‖)]
  congr 1
  funext x
  rw [ENNReal.ofReal_pow (norm_nonneg _) 2]

section Bridge

/-- A literature constant is valid on the raw globally Lipschitz gradient tests. -/
theorem holds_ofPreEnergy_gradientOperator_of_literatureHolds (hac : (ν : Measure V) ≪ m)
    (hfr : (ν : Measure V) (frontier (ν : Measure V).support) = 0) {C : NNReal}
    (h : KLS.LiteratureHolds ν C) :
    (Poincare.TestFamily.ofPreEnergy ν
      (PreEnergy.ofLinearPMap (gradientOperator ν (ContinuousLinearMap.id ℝ V) hac))).Holds C := by
  rintro ⟨x, hx⟩
  obtain ⟨g, hg, rfl⟩ := (mem_domain_gradientOperator_iff ν _ hac x).mp hx
  have hT := gradientOperator_apply ν (ContinuousLinearMap.id ℝ V) hac hfr hg hx rfl
  have hgrad : MemLp (gradient g) 2 (ν : Measure V) := by
    simpa only [weightedGradient_id] using hg.memLp_weightedGradient
  obtain ⟨K, hK⟩ := hg.1
  have hlit := h g ((KLS.literatureAdmissible_iff_memLp_gradient ν m hac g).mpr
    ⟨hK.locallyLipschitz, hg.memLp_two, hgrad⟩)
  rw [← ProbabilityTheory.ofReal_variance hg.memLp_two,
    KLS.literatureEnergy_eq_ofReal_integral_sq_norm_gradient ν m hac g hK.locallyLipschitz hgrad,
    ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul C.coe_nonneg] at hlit
  have hreal : ProbabilityTheory.variance g (ν : Measure V) ≤
      (C : ℝ) * ∫ x, ‖gradient g x‖ ^ 2 ∂(ν : Measure V) :=
    (ENNReal.ofReal_le_ofReal_iff (mul_nonneg C.2 (integral_nonneg fun x ↦ sq_nonneg _))).mp hlit
  change L2.variance ν (hg.memLp_two.toLp g) ≤
    C * ‖gradientOperator ν (ContinuousLinearMap.id ℝ V) hac ⟨_, hx⟩‖₊ ^ 2
  rw [hT, L2.variance_toLp, ← NNReal.coe_le_coe]
  push_cast
  rw [Real.coe_toNNReal _ (ProbabilityTheory.variance_nonneg _ _), norm_toLp_sq,
    weightedGradient_id]
  exact hreal

/-- A valid constant of the Lipschitz gradient relaxation is a literature constant: approximate a
locally Lipschitz literature test by smooth compactly supported functions in the graph norm. -/
theorem literatureHolds_of_holds_lipschitzGradientRelaxation (hac : (ν : Measure V) ≪ m)
    (hfr : (ν : Measure V) (frontier (ν : Measure V).support) = 0) {C : NNReal}
    (h : Poincare.L2Energy.Holds ν (lipschitzGradientRelaxation ν m hac) C) :
    KLS.LiteratureHolds ν C := by
  intro f hf
  obtain ⟨hlip, hL2, hgL2⟩ := (KLS.literatureAdmissible_iff_memLp_gradient ν m hac f).mp hf
  obtain ⟨fs, hfs, hconv, hgconv⟩ :=
    LipschitzApproximation.exists_smooth_weighted_L2_approximation
      ν m hac (ContinuousLinearMap.id ℝ V) f hlip hL2 (by simpa using hgL2)
  have hsL2 (j : ℕ) : MemLp (fs j) 2 (ν : Measure V) := (hfs j).2.2.1
  have hgsL2 (j : ℕ) : MemLp (gradient (fs j)) 2 (ν : Measure V) := by
    simpa using (hfs j).2.2.2
  have hval := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' fs hsL2 f hL2).mpr hconv
  have hgrad := (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
    (fun j ↦ gradient (fs j)) hgsL2 (gradient f) hgL2).mpr (by
      convert! hgconv using 1)
  have hvar : Tendsto (fun j ↦ (L2.variance ν ((hsL2 j).toLp (fs j)) : ℝ)) atTop
      (𝓝 (L2.variance ν (hL2.toLp f) : ℝ)) :=
    ((NNReal.continuous_coe.comp (L2.continuous_variance ν)).tendsto _).comp hval
  have henergy : Tendsto (fun j ↦ ‖(hgsL2 j).toLp (gradient (fs j))‖ ^ 2) atTop
      (𝓝 (‖hgL2.toLp (gradient f)‖ ^ 2)) :=
    hgrad.norm.pow 2
  have hbound : ∀ j, (L2.variance ν ((hsL2 j).toLp (fs j)) : ℝ) ≤
      (C : ℝ) * ‖(hgsL2 j).toLp (gradient (fs j))‖ ^ 2 := by
    intro j
    have htest : IsGradientTest ν (ContinuousLinearMap.id ℝ V) (fs j) :=
      IsGradientTest.of_contDiff_hasCompactSupport ν _ (hfs j).1 (hfs j).2.1
    have hmem : (hsL2 j).toLp (fs j) ∈ (gradientOperator ν (ContinuousLinearMap.id ℝ V) hac).domain :=
      toLp_mem_domain_gradientOperator ν _ hac htest
    have hfin : (lipschitzGradientRelaxation ν m hac).FiniteAt ((hsL2 j).toLp (fs j)) :=
      PreEnergy.sequentialRelaxation_finiteAt_toAmbient
        (PreEnergy.ofLinearPMap (gradientOperator ν (ContinuousLinearMap.id ℝ V) hac) :
          PreEnergy (Lp ℝ 2 (ν : Measure V))) ⟨_, hmem⟩
    have h1 := h ⟨_, hfin⟩
    have h2 : (lipschitzGradientRelaxation ν m hac).finiteValue ⟨_, hfin⟩ ≤
        ‖(hgsL2 j).toLp (gradient (fs j))‖₊ ^ 2 := by
      apply ENNReal.coe_le_coe.mp
      rw [Energy.Functional.coe_finiteValue]
      have h3 := PreEnergy.sequentialRelaxation_toAmbient_le
        (PreEnergy.ofLinearPMap (gradientOperator ν (ContinuousLinearMap.id ℝ V) hac) :
          PreEnergy (Lp ℝ 2 (ν : Measure V))) ⟨_, hmem⟩
      change (lipschitzGradientRelaxation ν m hac) ((hsL2 j).toLp (fs j)) ≤
        ((‖gradientOperator ν (ContinuousLinearMap.id ℝ V) hac ⟨_, hmem⟩‖₊ ^ 2 : NNReal) : ENNReal)
        at h3
      rw [gradientOperator_apply ν _ hac hfr htest hmem rfl] at h3
      exact h3
    have h4 : L2.variance ν ((hsL2 j).toLp (fs j)) ≤ C * ‖(hgsL2 j).toLp (gradient (fs j))‖₊ ^ 2 :=
      h1.trans (mul_le_mul_of_nonneg_left h2 zero_le)
    have h5 := NNReal.coe_le_coe.mpr h4
    push_cast at h5
    exact h5
  have hreal : (L2.variance ν (hL2.toLp f) : ℝ) ≤ (C : ℝ) * ‖hgL2.toLp (gradient f)‖ ^ 2 :=
    le_of_tendsto_of_tendsto' hvar (tendsto_const_nhds.mul henergy) hbound
  rw [L2.variance_toLp, Real.coe_toNNReal _ (ProbabilityTheory.variance_nonneg _ _),
    norm_toLp_sq] at hreal
  rw [← ProbabilityTheory.ofReal_variance hL2,
    KLS.literatureEnergy_eq_ofReal_integral_sq_norm_gradient ν m hac f hlip hgL2,
    ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul C.coe_nonneg]
  exact ENNReal.ofReal_le_ofReal hreal

/-- A finite constant is valid for the Lipschitz gradient relaxation exactly when it is a literature
constant. -/
theorem _root_.FunctionalInequalities.Poincare.L2Energy.holds_lipschitzGradientRelaxation_iff_literatureHolds
    (hac : (ν : Measure V) ≪ m) (hfr : (ν : Measure V) (frontier (ν : Measure V).support) = 0)
    (C : NNReal) :
    Poincare.L2Energy.Holds ν (lipschitzGradientRelaxation ν m hac) C ↔ KLS.LiteratureHolds ν C :=
  ⟨literatureHolds_of_holds_lipschitzGradientRelaxation ν m hac hfr, fun h ↦
    (Poincare.TestFamily.holds_ofPreEnergy_iff ν _ C).mp
      (holds_ofPreEnergy_gradientOperator_of_literatureHolds ν m hac hfr h)⟩

/-- The legacy smooth-test constant equals the optimal constant of the Lipschitz gradient
relaxation. -/
theorem _root_.FunctionalInequalities.Poincare.constant_eq_lipschitzGradientRelaxation
    (hac : (ν : Measure V) ≪ m) (hfr : (ν : Measure V) (frontier (ν : Measure V).support) = 0) :
    Poincare.constant (ν : Measure V) =
      Poincare.L2Energy.constant ν (lipschitzGradientRelaxation ν m hac) := by
  apply le_antisymm
  · by_cases htop : Poincare.L2Energy.constant ν (lipschitzGradientRelaxation ν m hac) = ⊤
    · rw [htop]
      exact le_top
    · set C := (Poincare.L2Energy.constant ν (lipschitzGradientRelaxation ν m hac)).toNNReal
      have hC : Poincare.L2Energy.Holds ν (lipschitzGradientRelaxation ν m hac) C :=
        (Poincare.L2Energy.holds_iff_constant_le _ _ _).mpr (by rw [ENNReal.coe_toNNReal htop])
      have hlit := (Poincare.L2Energy.holds_lipschitzGradientRelaxation_iff_literatureHolds
        ν m hac hfr C).mp hC
      have hlegacy := (Poincare.Euclidean.holds_iff_literatureHolds ν m hac C).mpr hlit
      rw [← ENNReal.coe_toNNReal htop]
      exact Poincare.constant_le hlegacy
  · apply Poincare.le_constant
    intro C hC
    have hlit := (Poincare.Euclidean.holds_iff_literatureHolds ν m hac C).mp hC
    exact (Poincare.L2Energy.holds_iff_constant_le _ _ _).mp
      ((Poincare.L2Energy.holds_lipschitzGradientRelaxation_iff_literatureHolds ν m hac hfr C).mpr hlit)

/-- With identity covariance, the covariance relaxation of `def:affine-poincare-constant` is the
Lipschitz gradient relaxation. -/
theorem covarianceRelaxation_eq_lipschitzGradientRelaxation (hac : (ν : Measure V) ≪ m)
    (hfr : (ν : Measure V) (frontier (ν : Measure V).support) = 0)
    (hcov : Covariance.operator (ν : Measure V) = ContinuousLinearMap.id ℝ V) :
    covarianceRelaxation ν = lipschitzGradientRelaxation ν m hac :=
  covarianceRelaxation_eq_sequentialRelaxation_ofLinearPMap ν (ContinuousLinearMap.id ℝ V) hac hfr
    (fun v ↦ by rw [hcov, ContinuousLinearMap.id_apply, real_inner_self_eq_norm_sq])

/-- The covariance relaxation is at most the operator norm of the covariance times the Lipschitz
gradient relaxation, at every point of finite Lipschitz relaxation. -/
theorem covarianceRelaxation_le_opNorm_mul_lipschitzGradientRelaxation (hac : (ν : Measure V) ≪ m)
    (hfr : (ν : Measure V) (frontier (ν : Measure V).support) = 0) (f : Lp ℝ 2 (ν : Measure V))
    (hf : lipschitzGradientRelaxation ν m hac f ≠ ⊤) :
    covarianceRelaxation ν f ≤
      (‖Covariance.operator (ν : Measure V)‖₊ : ENNReal) * lipschitzGradientRelaxation ν m hac f := by
  obtain ⟨B, hB⟩ := Covariance.exists_sqrt (ν : Measure V)
  rw [covarianceRelaxation_eq_sequentialRelaxation_ofLinearPMap ν B hac hfr hB]
  refine PreEnergy.sequentialRelaxation_comp_le_mul
    (PreEnergy.ofLinearPMap (gradientOperator ν (ContinuousLinearMap.id ℝ V) hac) :
      PreEnergy (Lp ℝ 2 (ν : Measure V)))
    (PreEnergy.ofLinearPMap (gradientOperator ν B hac) : PreEnergy (Lp ℝ 2 (ν : Measure V))) id
    continuous_id ‖Covariance.operator (ν : Measure V)‖₊ ?_ f hf
  rintro ⟨x, hx⟩
  obtain ⟨g, hg, rfl⟩ := (mem_domain_gradientOperator_iff ν _ hac x).mp hx
  have hgrad : MemLp (gradient g) 2 (ν : Measure V) := by
    simpa only [weightedGradient_id] using hg.memLp_weightedGradient
  have hgB : IsGradientTest ν B g := ⟨hg.1, hg.memLp_two, B.comp_memLp' hgrad⟩
  refine ⟨⟨_, toLp_mem_domain_gradientOperator ν B hac hgB⟩, rfl, ?_⟩
  rw [PreEnergy.ofLinearPMap_energy, PreEnergy.ofLinearPMap_energy,
    gradientOperator_apply ν B hac hfr hgB _ rfl,
    gradientOperator_apply ν (ContinuousLinearMap.id ℝ V) hac hfr hg hx rfl, ← ENNReal.coe_mul]
  apply ENNReal.coe_le_coe.mpr
  rw [← NNReal.coe_le_coe]
  push_cast
  rw [norm_toLp_sq, norm_toLp_sq, weightedGradient_id, ← integral_const_mul]
  refine integral_mono_of_nonneg (ae_of_all _ fun x ↦ sq_nonneg _)
    (((memLp_two_iff_integrable_sq_norm hgrad.1).mp hgrad).const_mul _) (ae_of_all _ fun x ↦ ?_)
  change ‖B (gradient g x)‖ ^ 2 ≤ ‖Covariance.operator (ν : Measure V)‖ * ‖gradient g x‖ ^ 2
  rw [← hB]
  calc inner ℝ (Covariance.operator (ν : Measure V) (gradient g x)) (gradient g x)
      ≤ ‖Covariance.operator (ν : Measure V) (gradient g x)‖ * ‖gradient g x‖ :=
        real_inner_le_norm _ _
    _ ≤ ‖Covariance.operator (ν : Measure V)‖ * ‖gradient g x‖ * ‖gradient g x‖ := by
        gcongr
        exact ContinuousLinearMap.le_opNorm _ _
    _ = ‖Covariance.operator (ν : Measure V)‖ * ‖gradient g x‖ ^ 2 := by ring

end Bridge

end FunctionalInequalities.Energy.Euclidean
