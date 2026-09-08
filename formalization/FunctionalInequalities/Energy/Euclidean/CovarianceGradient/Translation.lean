import FunctionalInequalities.Energy.Euclidean.CovarianceGradient.Basic
import FunctionalInequalities.Poincare.L2Energy

/-!
# Translation invariance of the covariance relaxation

Source: Blueprint `thm:affine-covariance-relaxation-closed`, the sentence "changing the affine
origin translates `ν`; pullback by this translation is an `L²` isometry preserving variance and
covariance energy". Read `translateLaw`, `translateL2`, `L2.variance_translateL2`,
`Covariance.operator_translateLaw`, `CovarianceGradientTest.translate`,
`covarianceRelaxation_translateLaw` and `L2Energy.constant_covarianceRelaxation_translateLaw`.

For a probability law `ν` on a finite-dimensional Euclidean space and a vector `c`, the translated
law is the image of `ν` under `x ↦ c + x`. Composition with the translation is a linear isometric
equivalence `L²(translated) ≃ L²(ν)` which preserves the intrinsic `L²` variance; the covariance
operator is unchanged; globally Lipschitz tests correspond by composition with the translation,
with equal covariance energies; hence the covariance relaxations correspond under the isometry
and the optimal `L²` Poincaré constants of the two relaxations coincide.

These statements hold for every Borel probability law; no log-concavity, density or closability
is used, and no Poincaré inequality is asserted.
-/

noncomputable section

open MeasureTheory Filter Topology InnerProductSpace

namespace FunctionalInequalities.Energy.Euclidean

universe u

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]

/- The common ambient assumptions are intentionally kept uniform across the public API. -/
set_option linter.unusedSectionVars false

section Law

variable (ν : ProbabilityMeasure V) (c : V)

/-- The image of `ν` under the translation `x ↦ c + x`. -/
def translateLaw : ProbabilityMeasure V :=
  ν.map (measurable_const_add c).aemeasurable

theorem coe_translateLaw :
    (translateLaw ν c : Measure V) = (ν : Measure V).map (fun x ↦ c + x) := rfl

/-- The translation is measure preserving from `ν` to the translated law. -/
theorem measurePreserving_translate :
    MeasurePreserving (fun x ↦ c + x) (ν : Measure V) (translateLaw ν c : Measure V) :=
  ⟨measurable_const_add c, rfl⟩

/-- The inverse translation is measure preserving from the translated law back to `ν`. -/
theorem measurePreserving_translate_symm :
    MeasurePreserving (fun x ↦ -c + x) (translateLaw ν c : Measure V) (ν : Measure V) := by
  refine ⟨measurable_const_add _, ?_⟩
  rw [coe_translateLaw, Measure.map_map (measurable_const_add _) (measurable_const_add _)]
  have : ((fun x ↦ -c + x) ∘ fun x ↦ c + x) = id := by
    funext x
    simp
  rw [this, Measure.map_id]

/-- Translation does not change the covariance operator. -/
theorem _root_.FunctionalInequalities.Covariance.operator_translateLaw :
    Covariance.operator (translateLaw ν c : Measure V) = Covariance.operator (ν : Measure V) := by
  unfold Covariance.operator
  rw [coe_translateLaw, ProbabilityTheory.covarianceBilin_map_const_add]

/-- Pullback of `L²` classes along the translation. -/
def translateForward : Lp ℝ 2 (translateLaw ν c : Measure V) →ₗᵢ[ℝ] Lp ℝ 2 (ν : Measure V) :=
  Lp.compMeasurePreservingₗᵢ ℝ (fun x ↦ c + x) (measurePreserving_translate ν c)

/-- Pullback of `L²` classes along the inverse translation. -/
def translateBackward : Lp ℝ 2 (ν : Measure V) →ₗᵢ[ℝ] Lp ℝ 2 (translateLaw ν c : Measure V) :=
  Lp.compMeasurePreservingₗᵢ ℝ (fun x ↦ -c + x) (measurePreserving_translate_symm ν c)

theorem translateForward_coeFn (f : Lp ℝ 2 (translateLaw ν c : Measure V)) :
    translateForward ν c f =ᵐ[(ν : Measure V)] fun x ↦ f (c + x) :=
  Lp.coeFn_compMeasurePreserving f (measurePreserving_translate ν c)

theorem translateBackward_translateForward (f : Lp ℝ 2 (translateLaw ν c : Measure V)) :
    translateBackward ν c (translateForward ν c f) = f := by
  change Lp.compMeasurePreserving (fun x ↦ -c + x) (measurePreserving_translate_symm ν c)
    (Lp.compMeasurePreserving (fun x ↦ c + x) (measurePreserving_translate ν c) f) = f
  rw [← Lp.compMeasurePreserving_comp_apply f (measurePreserving_translate ν c)
    (measurePreserving_translate_symm ν c)]
  apply Subtype.ext
  change f.1.compMeasurePreserving ((fun x ↦ c + x) ∘ fun x ↦ -c + x)
    ((measurePreserving_translate ν c).comp (measurePreserving_translate_symm ν c)) = f.1
  have hae : ((fun x ↦ c + x) ∘ fun x ↦ -c + x) =ᵐ[(translateLaw ν c : Measure V)] id :=
    Eventually.of_forall fun x ↦ by simp
  rw [AEEqFun.compMeasurePreserving_congr f.1 _ measurable_id hae]
  exact AEEqFun.compMeasurePreserving_id f.1

theorem translateForward_translateBackward (f : Lp ℝ 2 (ν : Measure V)) :
    translateForward ν c (translateBackward ν c f) = f := by
  change Lp.compMeasurePreserving (fun x ↦ c + x) (measurePreserving_translate ν c)
    (Lp.compMeasurePreserving (fun x ↦ -c + x) (measurePreserving_translate_symm ν c) f) = f
  rw [← Lp.compMeasurePreserving_comp_apply f (measurePreserving_translate_symm ν c)
    (measurePreserving_translate ν c)]
  apply Subtype.ext
  change f.1.compMeasurePreserving ((fun x ↦ -c + x) ∘ fun x ↦ c + x)
    ((measurePreserving_translate_symm ν c).comp (measurePreserving_translate ν c)) = f.1
  have hae : ((fun x ↦ -c + x) ∘ fun x ↦ c + x) =ᵐ[(ν : Measure V)] id :=
    Eventually.of_forall fun x ↦ by simp
  rw [AEEqFun.compMeasurePreserving_congr f.1 _ measurable_id hae]
  exact AEEqFun.compMeasurePreserving_id f.1

/-- Pullback along the translation as a linear isometric equivalence of real `L²` spaces. -/
def translateL2 : Lp ℝ 2 (translateLaw ν c : Measure V) ≃ₗᵢ[ℝ] Lp ℝ 2 (ν : Measure V) where
  toFun := translateForward ν c
  invFun := translateBackward ν c
  left_inv := translateBackward_translateForward ν c
  right_inv := translateForward_translateBackward ν c
  map_add' := map_add (translateForward ν c)
  map_smul' := map_smul (translateForward ν c)
  norm_map' := norm_map (translateForward ν c)

@[simp]
theorem translateL2_apply (f : Lp ℝ 2 (translateLaw ν c : Measure V)) :
    translateL2 ν c f = translateForward ν c f := rfl

@[simp]
theorem translateL2_symm_apply (f : Lp ℝ 2 (ν : Measure V)) :
    (translateL2 ν c).symm f = translateBackward ν c f := rfl

/-- Pullback along the translation preserves the intrinsic `L²` variance. -/
theorem _root_.FunctionalInequalities.L2.variance_translateL2
    (f : Lp ℝ 2 (translateLaw ν c : Measure V)) :
    L2.variance ν (translateL2 ν c f) = L2.variance (translateLaw ν c) f := by
  apply NNReal.eq
  rw [L2.coe_variance_eq_pointwise, L2.coe_variance_eq_pointwise, translateL2_apply,
    ProbabilityTheory.variance_congr (translateForward_coeFn ν c f)]
  exact (measurePreserving_translate ν c).variance_fun_comp
    (Lp.aestronglyMeasurable f).aemeasurable

end Law

section Tests

variable {ν₁ ν₂ : ProbabilityMeasure V} {c : V}

/-- The gradient of a translated function is the translated gradient. -/
theorem gradient_comp_const_add (g : V → ℝ) (c x : V) :
    gradient (fun y ↦ g (c + y)) x = gradient g (c + x) := by
  apply (toDual ℝ V).injective
  simp only [toDual_gradient]
  exact fderiv_comp_add_left c

/-- Translations are `1`-Lipschitz. -/
theorem lipschitzWith_const_add (c : V) : LipschitzWith 1 (fun x : V ↦ c + x) :=
  LipschitzWith.of_dist_le_mul fun x y ↦ by simp [dist_eq_norm]

/-- Composition of a covariance test with a measure-preserving translation between two laws with
the same covariance operator. -/
def CovarianceGradientTest.translate
    (hmp : MeasurePreserving (fun x ↦ c + x) (ν₁ : Measure V) (ν₂ : Measure V))
    (hcov : Covariance.operator (ν₂ : Measure V) = Covariance.operator (ν₁ : Measure V))
    (g : CovarianceGradientTest ν₂) : CovarianceGradientTest ν₁ where
  toFun := fun x ↦ g (c + x)
  lipschitz := by
    obtain ⟨K, hK⟩ := g.lipschitz
    exact ⟨K * 1, hK.comp (lipschitzWith_const_add c)⟩
  memLp_two := by
    have := g.memLp_two
    rw [← hmp.map_eq] at this
    exact (memLp_map_measure_iff (hmp.map_eq ▸ g.memLp_two.1) hmp.aemeasurable).mp this
  integrable := by
    have hdens : covarianceGradientDensity ν₁ (fun x ↦ g (c + x)) =
        covarianceGradientDensity ν₂ g.toFun ∘ fun x ↦ c + x := by
      funext x
      simp only [covarianceGradientDensity, Function.comp_apply, gradient_comp_const_add, hcov]
    rw [hdens]
    have := g.integrable
    rw [← hmp.map_eq] at this
    exact (integrable_map_measure (hmp.map_eq ▸ g.integrable.1) hmp.aemeasurable).mp this

/-- The translated test has the same covariance energy. -/
theorem CovarianceGradientTest.covarianceEnergy_translate
    (hmp : MeasurePreserving (fun x ↦ c + x) (ν₁ : Measure V) (ν₂ : Measure V))
    (hcov : Covariance.operator (ν₂ : Measure V) = Covariance.operator (ν₁ : Measure V))
    (g : CovarianceGradientTest ν₂) :
    (g.translate hmp hcov).covarianceEnergy = g.covarianceEnergy := by
  apply NNReal.eq
  simp only [CovarianceGradientTest.coe_covarianceEnergy]
  have hdens : covarianceGradientDensity ν₁ (g.translate hmp hcov).toFun =
      covarianceGradientDensity ν₂ g.toFun ∘ fun x ↦ c + x := by
    funext x
    simp only [CovarianceGradientTest.translate, covarianceGradientDensity, Function.comp_apply,
      gradient_comp_const_add, hcov]
  rw [hdens, ← hmp.map_eq, integral_map hmp.aemeasurable (hmp.map_eq ▸ g.integrable.1)]
  rfl

/-- The translated test realizes the pullback of the original class. -/
theorem CovarianceGradientTest.toL2_translate
    (hmp : MeasurePreserving (fun x ↦ c + x) (ν₁ : Measure V) (ν₂ : Measure V))
    (hcov : Covariance.operator (ν₂ : Measure V) = Covariance.operator (ν₁ : Measure V))
    (g : CovarianceGradientTest ν₂) :
    (g.translate hmp hcov).toL2 = Lp.compMeasurePreserving (fun x ↦ c + x) hmp g.toL2 := by
  apply Lp.ext
  refine (g.translate hmp hcov).toL2_coeFn.trans ?_
  refine Filter.EventuallyEq.trans ?_ (Lp.coeFn_compMeasurePreserving g.toL2 hmp).symm
  exact hmp.quasiMeasurePreserving.ae_eq_comp g.toL2_coeFn.symm

end Tests

section Relaxation

variable (ν : ProbabilityMeasure V) (c : V)

/-- The covariance relaxation of the translated law is the covariance relaxation of `ν` pulled
back along the translation isometry. -/
theorem covarianceRelaxation_translateLaw (f : Lp ℝ 2 (translateLaw ν c : Measure V)) :
    covarianceRelaxation (translateLaw ν c) f = covarianceRelaxation ν (translateL2 ν c f) := by
  have hcov : Covariance.operator (translateLaw ν c : Measure V) =
      Covariance.operator (ν : Measure V) := Covariance.operator_translateLaw ν c
  apply le_antisymm
  · -- pull tests of `ν` back to the translated law along the inverse translation
    have h := (covariancePreEnergy ν).sequentialRelaxation_comp_le
      (covariancePreEnergy (translateLaw ν c)) (translateBackward ν c)
      (translateBackward ν c).continuous ?_ (translateL2 ν c f)
    · rw [translateL2_apply, translateBackward_translateForward] at h
      exact h
    · intro g
      refine ⟨g.translate (measurePreserving_translate_symm ν c) hcov.symm, ?_, le_of_eq ?_⟩
      · exact g.toL2_translate _ _
      · exact g.covarianceEnergy_translate _ _
  · have h := (covariancePreEnergy (translateLaw ν c)).sequentialRelaxation_comp_le
      (covariancePreEnergy ν) (translateForward ν c) (translateForward ν c).continuous ?_ f
    · exact h
    · intro g
      refine ⟨g.translate (measurePreserving_translate ν c) hcov, ?_, le_of_eq ?_⟩
      · exact g.toL2_translate _ _
      · exact g.covarianceEnergy_translate _ _

/-- The optimal `L²` Poincaré constant of the covariance relaxation is translation invariant. -/
theorem _root_.FunctionalInequalities.Poincare.L2Energy.constant_covarianceRelaxation_translateLaw :
    Poincare.L2Energy.constant (translateLaw ν c) (covarianceRelaxation (translateLaw ν c)) =
      Poincare.L2Energy.constant ν (covarianceRelaxation ν) :=
  Poincare.L2Energy.constant_eq_of_linearIsometryEquiv ν (translateLaw ν c)
    (covarianceRelaxation ν) (covarianceRelaxation (translateLaw ν c)) (translateL2 ν c)
    (L2.variance_translateL2 ν c) (covarianceRelaxation_translateLaw ν c)

end Relaxation

end FunctionalInequalities.Energy.Euclidean
