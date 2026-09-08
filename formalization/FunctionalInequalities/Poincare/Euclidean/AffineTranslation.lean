import FunctionalInequalities.Energy.Euclidean.CovarianceGradient.Isometry
import FunctionalInequalities.Poincare.Euclidean.AffineCovariance

/-!
# Ambient translation invariance of the affine covariance Poincaré constant

Source: Blueprint `lem:affine-poincare-translation-invariance`, the identity
`C_P^aff((τ_b)_# μ) = C_P^aff(μ)` for `τ_b(x) = x + b`. Read `Probability.affineSupport_translateLaw`,
`Probability.direction_affineSupport_translateLaw`, `Probability.intrinsicMeasure_translateLaw`,
`Energy.Affine.exists_translateLaw_isometry` and `Poincare.Affine.constant_translateLaw_ambient`.

For a probability law `μ` on a finite-dimensional Euclidean space `E` and `b ∈ E`, the translated
law `Energy.Euclidean.translateLaw μ b` is the image of `μ` under `x ↦ b + x`. Its affine support
is the translate of the affine support of `μ`, so both have the same direction submodule `V`; the
two intrinsic coordinate presentations differ by the linear isometric identification of the two
(equal) direction submodules followed by a translation inside the direction space. Hence the
intrinsic law of the translated law is a translate of the isometric image of the intrinsic law of
`μ`; the covariance relaxations correspond under the resulting `L²` isometry, which preserves
variance, and the affine covariance Poincaré constants coincide. The ambient covariance operator is
also unchanged. Finally, translating by the negative barycenter gives a law with zero mean whenever
the identity is integrable.

What this module claims: the statements above, for every Borel probability law on `E` and every
`b`, including the zero-dimensional direction space. What it does not claim: log-concavity of the
translated law (proved in `KLS/LogConcave/AffineTranslation.lean` from the compact-set
definition), any Poincaré inequality, finiteness of the constant, the isotropic reduction, or
invariance under any non-translation affine map of `E`.
-/

noncomputable section

open MeasureTheory Filter Topology

namespace FunctionalInequalities.Probability

open Energy.Euclidean

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]

/- The common ambient assumptions are intentionally kept uniform across the public API. -/
set_option linter.unusedSectionVars false

variable (μ : ProbabilityMeasure E) (b : E)

/-- On the affine support, the intrinsic coordinate of a point is its displacement from the chosen
support point. -/
theorem coe_intrinsicMap_of_mem {x : E} (hx : x ∈ affineSupport μ) :
    (intrinsicMap μ x : E) = x - supportPoint μ := by
  have hret : retraction μ x = ⟨x, hx⟩ := Subtype.ext (coe_retraction_of_mem μ hx)
  rw [intrinsicMap, hret, coordinateEquiv, AffineIsometryEquiv.coe_vaddConst_symm]
  rfl

/-- The affine support of the translated law is the translate of the affine support. -/
theorem affineSupport_translateLaw :
    affineSupport (translateLaw μ b) =
      (affineSupport μ).map (AffineEquiv.constVAdd ℝ E b).toAffineMap := by
  apply le_antisymm
  · apply affineSupport_le_of_ae_mem
    · exact ((affineSupport μ).map (AffineEquiv.constVAdd ℝ E b).toAffineMap).closed_of_finiteDimensional
    · rw [coe_translateLaw]
      refine (ae_map_iff (measurable_const_add b).aemeasurable
        ((affineSupport μ).map
          (AffineEquiv.constVAdd ℝ E b).toAffineMap).closed_of_finiteDimensional.measurableSet).2 ?_
      filter_upwards [ae_mem_affineSupport μ] with x hx
      exact ⟨x, hx, rfl⟩
  · rw [AffineSubspace.map_le_iff_le_comap]
    apply affineSupport_le_of_ae_mem
    · change IsClosed ((fun x : E ↦ b + x) ⁻¹' (affineSupport (translateLaw μ b) : Set E))
      exact (isClosed_affineSupport _).preimage (continuous_const.add continuous_id)
    · have h := ae_mem_affineSupport (translateLaw μ b)
      rw [coe_translateLaw] at h
      filter_upwards [ae_of_ae_map (measurable_const_add b).aemeasurable h] with x hx
      exact hx

/-- Translation does not change the direction of the affine support. -/
theorem direction_affineSupport_translateLaw :
    (affineSupport (translateLaw μ b)).direction = (affineSupport μ).direction := by
  rw [affineSupport_translateLaw, AffineSubspace.map_direction]
  simp [Submodule.map_id]

/-- The linear isometric identification of the two (equal) direction submodules. -/
def translateDirectionEquiv :
    (affineSupport μ).direction ≃ₗᵢ[ℝ] (affineSupport (translateLaw μ b)).direction :=
  LinearIsometryEquiv.ofEq _ _ (direction_affineSupport_translateLaw μ b).symm

@[simp]
theorem coe_translateDirectionEquiv (v : (affineSupport μ).direction) :
    (translateDirectionEquiv μ b v : E) = v :=
  LinearIsometryEquiv.coe_ofEq_apply _ _

/-- The translate of the chosen support point lies in the translated affine support. -/
theorem add_supportPoint_mem_affineSupport_translateLaw :
    b + supportPoint μ ∈ affineSupport (translateLaw μ b) := by
  rw [affineSupport_translateLaw]
  exact ⟨supportPoint μ, (origin μ).property, rfl⟩

/-- The shift between the two intrinsic coordinate presentations: the translated support point of
`μ` minus the support point chosen for the translated law, as a direction vector. -/
def translateShift : (affineSupport (translateLaw μ b)).direction :=
  ⟨b + supportPoint μ - supportPoint (translateLaw μ b),
    AffineSubspace.vsub_mem_direction (add_supportPoint_mem_affineSupport_translateLaw μ b)
      (origin (translateLaw μ b)).property⟩

@[simp]
theorem coe_translateShift :
    (translateShift μ b : E) = b + supportPoint μ - supportPoint (translateLaw μ b) := rfl

/-- On the affine support, intrinsic coordinates of the translated law are the shifted isometric
image of the intrinsic coordinates of `μ`. -/
theorem intrinsicMap_translateLaw {x : E} (hx : x ∈ affineSupport μ) :
    intrinsicMap (translateLaw μ b) (b + x) =
      translateShift μ b + translateDirectionEquiv μ b (intrinsicMap μ x) := by
  apply Subtype.ext
  have hx' : b + x ∈ affineSupport (translateLaw μ b) := by
    rw [affineSupport_translateLaw]
    exact ⟨x, hx, rfl⟩
  rw [coe_intrinsicMap_of_mem _ hx', Submodule.coe_add, coe_translateDirectionEquiv,
    coe_intrinsicMap_of_mem μ hx, coe_translateShift]
  abel

/-- The intrinsic law of the translated law is the translate, inside the direction space, of the
isometric image of the intrinsic law of `μ`. -/
theorem intrinsicMeasure_translateLaw :
    intrinsicMeasure (translateLaw μ b) =
      translateLaw (mapLaw (intrinsicMeasure μ) (translateDirectionEquiv μ b)) (translateShift μ b) := by
  apply ProbabilityMeasure.toMeasure_injective
  simp only [intrinsicMeasure, ProbabilityMeasure.toMeasure_map, coe_translateLaw, coe_mapLaw]
  rw [Measure.map_map (measurable_intrinsicMap _) (measurable_const_add b),
    Measure.map_map (measurable_const_add _) (translateDirectionEquiv μ b).continuous.measurable,
    Measure.map_map ((measurable_const_add _).comp (translateDirectionEquiv μ b).continuous.measurable)
      (measurable_intrinsicMap μ)]
  refine Measure.map_congr ?_
  filter_upwards [ae_mem_affineSupport μ] with x hx
  simp only [Function.comp_apply]
  exact intrinsicMap_translateLaw μ b hx

end FunctionalInequalities.Probability

namespace FunctionalInequalities.Energy.Euclidean

universe u

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]

/- The common ambient assumptions are intentionally kept uniform across the public API. -/
set_option linter.unusedSectionVars false

/-- The barycenter of a translated law is the translated barycenter. -/
theorem integral_id_translateLaw (ν : ProbabilityMeasure V) (hint : Integrable id (ν : Measure V))
    (c : V) : ∫ x, x ∂(translateLaw ν c : Measure V) = c + ∫ x, x ∂(ν : Measure V) := by
  rw [coe_translateLaw, integral_map (measurable_const_add c).aemeasurable
    continuous_id'.aestronglyMeasurable]
  have hint' : Integrable (fun x : V ↦ x) (ν : Measure V) := hint
  rw [integral_add (integrable_const c) hint', integral_const, probReal_univ, one_smul]

/-- Translating by the negative barycenter centers the law. -/
theorem integral_id_translateLaw_neg_integral (ν : ProbabilityMeasure V)
    (hint : Integrable id (ν : Measure V)) :
    ∫ x, x ∂(translateLaw ν (-∫ x, x ∂(ν : Measure V)) : Measure V) = 0 := by
  rw [integral_id_translateLaw ν hint]
  simp

end FunctionalInequalities.Energy.Euclidean

namespace FunctionalInequalities.Energy.Affine

open Energy.Euclidean Probability

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]

/- The common ambient assumptions are intentionally kept uniform across the public API. -/
set_option linter.unusedSectionVars false

variable (μ : ProbabilityMeasure E) (b : E)

/-- Translating `μ` in the ambient space: there is a linear isometric equivalence between the two
intrinsic `L²` spaces preserving variance and intertwining the affine covariance relaxations. -/
theorem exists_translateLaw_isometry :
    ∃ e : Lp ℝ 2 (Probability.intrinsicMeasure (translateLaw μ b) :
        Measure (affineSupport (translateLaw μ b)).direction) ≃ₗᵢ[ℝ]
        Lp ℝ 2 (Probability.intrinsicMeasure μ : Measure (affineSupport μ).direction),
      (∀ f, L2.variance (Probability.intrinsicMeasure μ) (e f) =
        L2.variance (Probability.intrinsicMeasure (translateLaw μ b)) f) ∧
      ∀ f, energy (translateLaw μ b) f = energy μ (e f) := by
  rw [energy_eq (translateLaw μ b), Probability.intrinsicMeasure_translateLaw]
  refine ⟨(translateL2 _ _).trans (mapL2 _ _), fun f ↦ ?_, fun f ↦ ?_⟩
  · rw [LinearIsometryEquiv.trans_apply, L2.variance_mapL2, L2.variance_translateL2]
  · rw [LinearIsometryEquiv.trans_apply, covarianceRelaxation_translateLaw, covarianceRelaxation_mapLaw]
    rfl

/-- The affine covariance Poincaré constant is invariant under ambient translations of the law. -/
theorem _root_.FunctionalInequalities.Poincare.Affine.constant_translateLaw_ambient :
    Poincare.Affine.constant (translateLaw μ b) = Poincare.Affine.constant μ := by
  unfold Poincare.Affine.constant
  rw [energy_eq (translateLaw μ b), energy_eq μ, Probability.intrinsicMeasure_translateLaw,
    Poincare.L2Energy.constant_covarianceRelaxation_translateLaw,
    Poincare.L2Energy.constant_covarianceRelaxation_mapLaw]

end FunctionalInequalities.Energy.Affine
