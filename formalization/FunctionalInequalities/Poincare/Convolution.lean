module

public import FunctionalInequalities.Poincare.Product.Tensorization
public import FunctionalInequalities.Energy.CovarianceGradient.Translation
public import Mathlib.MeasureTheory.Group.Convolution

/-!
# Poincaré bounds under addition of independent probability laws

The sum map from the Hilbert product sends the product law to convolution.
The separate coordinate terms in product tensorization give an additive
fixed-constant bound for the convolution law.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ContDiff

namespace FunctionalInequalities.Poincare.SmoothTest

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]

private def sumMap : WithLp 2 (V × V) → V := fun p => p.fst + p.snd

omit [CompleteSpace V] [MeasurableSpace V] [BorelSpace V]
  [SecondCountableTopology V] in
private theorem sumMap_contDiff : ContDiff ℝ ∞ (sumMap (V := V)) := by
  unfold sumMap
  exact (contDiff_fst.add contDiff_snd).comp
    (WithLp.prodContinuousLinearEquiv 2 ℝ V V).contDiff

section SumLaws

omit [CompleteSpace V]
private theorem sumMap_measurable : Measurable (sumMap (V := V)) :=
  sumMap_contDiff.continuous.measurable

private theorem map_prodMeasure_sumMap (μ ν : Measure V) :
    (prodMeasure μ ν).map (sumMap (V := V)) = μ.conv ν := by
  rw [prodMeasure, Measure.map_map sumMap_measurable
    (WithLp.measurable_toLp 2 (V × V))]
  rfl

private theorem sumMap_measurePreserving (μ ν : Measure V) :
    MeasurePreserving (sumMap (V := V)) (prodMeasure μ ν) (μ.conv ν) :=
  ⟨sumMap_measurable, map_prodMeasure_sumMap μ ν⟩

end SumLaws

section LiftedGradients

omit [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
private theorem gradient_lift_fst (f : V → ℝ) (hf : Differentiable ℝ f)
    (x y : V) :
    (gradient (fun p : WithLp 2 (V × V) => f (sumMap p))
      (WithLp.toLp 2 (x, y))).fst = gradient f (x + y) := by
  have hdiff : Differentiable ℝ (fun p : WithLp 2 (V × V) => f (sumMap p)) :=
    hf.comp (sumMap_contDiff.differentiable (by simp))
  rw [← gradient_section_left (hdiff _)]
  change gradient (fun z : V => f (z + y)) x = gradient f (x + y)
  simpa only [add_comm] using Energy.Euclidean.gradient_comp_const_add f y x

private theorem gradient_lift_snd (f : V → ℝ) (hf : Differentiable ℝ f)
    (x y : V) :
    (gradient (fun p : WithLp 2 (V × V) => f (sumMap p))
      (WithLp.toLp 2 (x, y))).snd = gradient f (x + y) := by
  have hdiff : Differentiable ℝ (fun p : WithLp 2 (V × V) => f (sumMap p)) :=
    hf.comp (sumMap_contDiff.differentiable (by simp))
  rw [← gradient_section_right (hdiff _)]
  change gradient (fun z : V => f (x + z)) y = gradient f (x + y)
  exact Energy.Euclidean.gradient_comp_const_add f x y

private theorem gradient_lift_norm_sq (f : V → ℝ) (hf : Differentiable ℝ f)
    (p : WithLp 2 (V × V)) :
    ‖gradient (fun q : WithLp 2 (V × V) => f (sumMap q)) p‖ ^ 2 =
      2 * ‖gradient f (sumMap p)‖ ^ 2 := by
  have hp : p = WithLp.toLp 2 (p.fst, p.snd) := rfl
  rw [hp, WithLp.prod_norm_sq_eq_of_L2,
    gradient_lift_fst f hf, gradient_lift_snd f hf]
  simp only [sumMap, WithLp.toLp_fst, WithLp.toLp_snd]
  ring

end LiftedGradients

private theorem admissible_lift {μ ν : Measure V} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {f : V → ℝ} (hf : Admissible (μ.conv ν) f) :
    Admissible (prodMeasure μ ν) (fun p => f (sumMap p)) := by
  let hmap := sumMap_measurePreserving μ ν
  have hdiff : Differentiable ℝ f := hf.smooth'.differentiable (by simp)
  have hbase : Integrable (fun p : WithLp 2 (V × V) =>
      ‖gradient f (sumMap p)‖ ^ 2) (prodMeasure μ ν) :=
    hmap.integrable_comp_of_integrable hf.energy_integrable
  refine ⟨hf.smooth'.comp sumMap_contDiff,
    hf.memLp_two.comp_measurePreserving hmap, ?_⟩
  refine (hbase.const_mul 2).congr (Filter.Eventually.of_forall fun p => ?_)
  exact (gradient_lift_norm_sq f hdiff p).symm

/-- Fixed-constant smooth-test Poincaré bound under convolution. -/
theorem Holds.conv {μ ν : Measure V} {C C' : ℝ}
    (hμ : Holds μ C) (hν : Holds ν C') : Holds (μ.conv ν) (C + C') := by
  have := hμ.probability
  have := hν.probability
  let hmap := sumMap_measurePreserving μ ν
  have hprob : IsProbabilityMeasure (μ.conv ν) := by
    rw [← map_prodMeasure_sumMap μ ν]
    exact (Measure.isProbabilityMeasure_map_iff sumMap_measurable.aemeasurable).2 inferInstance
  refine ⟨hprob, add_nonneg hμ.constant_nonneg hν.constant_nonneg, ?_⟩
  intro f hf
  let g : WithLp 2 (V × V) → ℝ := fun p => f (sumMap p)
  have hg : Admissible (prodMeasure μ ν) g := admissible_lift hf
  have hdiff : Differentiable ℝ f := hf.smooth'.differentiable (by simp)
  have hvar : variance g (prodMeasure μ ν) = variance f (μ.conv ν) := by
    exact hmap.variance_fun_comp hf.smooth'.continuous.aemeasurable
  have hA : (∫ p : V × V, ‖(gradient g (WithLp.toLp 2 p)).fst‖ ^ 2 ∂μ.prod ν)
      = energy (μ.conv ν) f := by
    calc
      _ = ∫ p : WithLp 2 (V × V), ‖(gradient g p).fst‖ ^ 2 ∂prodMeasure μ ν := by
        rw [prodMeasure]
        exact (integral_map_equiv (MeasurableEquiv.toLp 2 (V × V))
          (fun p => ‖(gradient g p).fst‖ ^ 2)).symm
      _ = ∫ p : WithLp 2 (V × V), ‖gradient f (sumMap p)‖ ^ 2 ∂prodMeasure μ ν := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun p => by
          have hp : p = WithLp.toLp 2 (p.fst, p.snd) := rfl
          rw [hp]
          change ‖(gradient (fun q : WithLp 2 (V × V) => f (sumMap q))
            (WithLp.toLp 2 (p.fst, p.snd))).fst‖ ^ 2 =
            ‖gradient f (sumMap (WithLp.toLp 2 (p.fst, p.snd)))‖ ^ 2
          rw [gradient_lift_fst f hdiff]
          rfl
      _ = energy (μ.conv ν) f := by
        rw [energy, ← hmap.map_eq]
        exact (integral_map (μ := prodMeasure μ ν) sumMap_measurable.aemeasurable
          (by rw [hmap.map_eq]; exact hf.energy_integrable.aestronglyMeasurable)).symm
  have hB : (∫ p : V × V, ‖(gradient g (WithLp.toLp 2 p)).snd‖ ^ 2 ∂μ.prod ν)
      = energy (μ.conv ν) f := by
    calc
      _ = ∫ p : WithLp 2 (V × V), ‖(gradient g p).snd‖ ^ 2 ∂prodMeasure μ ν := by
        rw [prodMeasure]
        exact (integral_map_equiv (MeasurableEquiv.toLp 2 (V × V))
          (fun p => ‖(gradient g p).snd‖ ^ 2)).symm
      _ = ∫ p : WithLp 2 (V × V), ‖gradient f (sumMap p)‖ ^ 2 ∂prodMeasure μ ν := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun p => by
          have hp : p = WithLp.toLp 2 (p.fst, p.snd) := rfl
          rw [hp]
          change ‖(gradient (fun q : WithLp 2 (V × V) => f (sumMap q))
            (WithLp.toLp 2 (p.fst, p.snd))).snd‖ ^ 2 =
            ‖gradient f (sumMap (WithLp.toLp 2 (p.fst, p.snd)))‖ ^ 2
          rw [gradient_lift_snd f hdiff]
          rfl
      _ = energy (μ.conv ν) f := by
        rw [energy, ← hmap.map_eq]
        exact (integral_map (μ := prodMeasure μ ν) sumMap_measurable.aemeasurable
          (by rw [hmap.map_eq]; exact hf.energy_integrable.aestronglyMeasurable)).symm
  have h := hμ.prod_components hν hg
  rw [hvar, hA, hB] at h
  convert h using 1
  ring

/-- The extended optimal smooth-test constant is subadditive under convolution,
including the cases where either constant is infinite. -/
theorem constant_conv_le_add {μ ν : Measure V}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    constant (μ.conv ν) ≤ constant μ + constant ν := by
  calc
    constant (μ.conv ν) ≤
        ⨅ A : {A : NNReal // Holds μ (A : ℝ)},
          ⨅ B : {B : NNReal // Holds ν (B : ℝ)},
            (A.1 : ENNReal) + (B.1 : ENNReal) := by
      refine le_iInf fun A => le_iInf fun B => ?_
      have hH : Holds (μ.conv ν) ((A.1 + B.1 : NNReal) : ℝ) := by
        simpa only [NNReal.coe_add] using A.2.conv B.2
      simpa only [ENNReal.coe_add] using constant_le hH
    _ = constant μ + constant ν := by
      rw [constant, constant, ENNReal.iInf_add]
      simp only [ENNReal.add_iInf]

end FunctionalInequalities.Poincare.SmoothTest
