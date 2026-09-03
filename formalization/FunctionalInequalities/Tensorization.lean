import FunctionalInequalities.ProductAdmissible

/-!
# Poincaré tensorization on Hilbert products

Node: `lem:poincare-tensorization`. The product law lives on `WithLp 2 (E × F)` and uses the
manuscript normalization `Var(f) ≤ C ∫ ‖gradient f‖²` for `Poincare.Admissible` tests. The fixed
and extended optimal-constant bounds below are packaged by the node-specific certificate.
-/

noncomputable section

open MeasureTheory ProbabilityTheory

namespace FunctionalInequalities.Poincare

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]

/-- Fixed-constant tensorization inequality on the Hilbert product.
The assumptions `Holds μ C` and `Holds ν C'` include probability and nonnegativity. -/
theorem Holds.prod
    {μ : Measure E} {ν : Measure F} {C C' : ℝ}
    (hμ : Holds μ C) (hν : Holds ν C') :
    Holds (prodMeasure μ ν) (max C C') := by
  have := hμ.probability
  have := hν.probability
  refine ⟨inferInstance, le_max_of_le_left hμ.constant_nonneg, ?_⟩
  intro g hg
  have hun : MemLp (fun p : E × F ↦ g (WithLp.toLp 2 p)) 2 (μ.prod ν) := hg.memLp_uncurry
  have hdiff : Differentiable ℝ g := hg.smooth'.differentiable (by simp)
  have hvar : variance g (prodMeasure μ ν)
      = variance (fun p : E × F ↦ g (WithLp.toLp 2 p)) (μ.prod ν) := by
    rw [prodMeasure, ← MeasurableEquiv.coe_toLp, variance_map_equiv]
    rfl
  have hIntG1 := hg.integrable_gradient_fst
  have hIntG2 := hg.integrable_gradient_snd
  have hIntVL := ProductVariance.integrable_variance_left hun
  have hIntVR := ProductVariance.integrable_variance_right hun
  have hVle := ProductVariance.variance_le hun
  set A : ℝ := ∫ p : E × F, ‖(gradient g (WithLp.toLp 2 p)).fst‖ ^ 2 ∂μ.prod ν with hA_def
  set B : ℝ := ∫ p : E × F, ‖(gradient g (WithLp.toLp 2 p)).snd‖ ^ 2 ∂μ.prod ν with hB_def
  have hA : 0 ≤ A := integral_nonneg fun _ ↦ sq_nonneg _
  have hB : 0 ≤ B := integral_nonneg fun _ ↦ sq_nonneg _
  -- the left-factor inequality, applied to almost every section and integrated
  have hterm1 : (∫ y, variance (fun x ↦ g (WithLp.toLp 2 (x, y))) μ ∂ν) ≤ C * A := by
    have hswap : A = ∫ y, ∫ x, ‖(gradient g (WithLp.toLp 2 (x, y))).fst‖ ^ 2 ∂μ ∂ν :=
      integral_prod_symm _ hIntG1
    have hmono : (∫ y, variance (fun x ↦ g (WithLp.toLp 2 (x, y))) μ ∂ν)
        ≤ ∫ y, C * ∫ x, ‖(gradient g (WithLp.toLp 2 (x, y))).fst‖ ^ 2 ∂μ ∂ν := by
      refine integral_mono_ae hIntVL ((hIntG1.integral_prod_right).const_mul C) ?_
      filter_upwards [hg.section_left_ae] with y hy
      show variance (fun x ↦ g (WithLp.toLp 2 (x, y))) μ
          ≤ C * ∫ x, ‖(gradient g (WithLp.toLp 2 (x, y))).fst‖ ^ 2 ∂μ
      have hv := hμ.variance_le hy
      have hen : energy μ (fun x ↦ g (WithLp.toLp 2 (x, y)))
          = ∫ x, ‖(gradient g (WithLp.toLp 2 (x, y))).fst‖ ^ 2 ∂μ := by
        rw [energy]
        refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
        show ‖gradient (fun x ↦ g (WithLp.toLp 2 (x, y))) x‖ ^ 2
            = ‖(gradient g (WithLp.toLp 2 (x, y))).fst‖ ^ 2
        rw [gradient_section_left (hdiff _)]
      rw [hen] at hv
      exact hv
    calc (∫ y, variance (fun x ↦ g (WithLp.toLp 2 (x, y))) μ ∂ν)
        ≤ ∫ y, C * ∫ x, ‖(gradient g (WithLp.toLp 2 (x, y))).fst‖ ^ 2 ∂μ ∂ν := hmono
      _ = C * ∫ y, ∫ x, ‖(gradient g (WithLp.toLp 2 (x, y))).fst‖ ^ 2 ∂μ ∂ν :=
          integral_const_mul C _
      _ = C * A := by rw [← hswap]
  -- the right-factor inequality, applied to almost every section and integrated
  have hterm2 : (∫ x, variance (fun y ↦ g (WithLp.toLp 2 (x, y))) ν ∂μ) ≤ C' * B := by
    have hswap : B = ∫ x, ∫ y, ‖(gradient g (WithLp.toLp 2 (x, y))).snd‖ ^ 2 ∂ν ∂μ :=
      integral_prod _ hIntG2
    have hmono : (∫ x, variance (fun y ↦ g (WithLp.toLp 2 (x, y))) ν ∂μ)
        ≤ ∫ x, C' * ∫ y, ‖(gradient g (WithLp.toLp 2 (x, y))).snd‖ ^ 2 ∂ν ∂μ := by
      refine integral_mono_ae hIntVR ((hIntG2.integral_prod_left).const_mul C') ?_
      filter_upwards [hg.section_right_ae] with x hx
      show variance (fun y ↦ g (WithLp.toLp 2 (x, y))) ν
          ≤ C' * ∫ y, ‖(gradient g (WithLp.toLp 2 (x, y))).snd‖ ^ 2 ∂ν
      have hv := hν.variance_le hx
      have hen : energy ν (fun y ↦ g (WithLp.toLp 2 (x, y)))
          = ∫ y, ‖(gradient g (WithLp.toLp 2 (x, y))).snd‖ ^ 2 ∂ν := by
        rw [energy]
        refine integral_congr_ae (Filter.Eventually.of_forall fun y ↦ ?_)
        show ‖gradient (fun y ↦ g (WithLp.toLp 2 (x, y))) y‖ ^ 2
            = ‖(gradient g (WithLp.toLp 2 (x, y))).snd‖ ^ 2
        rw [gradient_section_right (hdiff _)]
      rw [hen] at hv
      exact hv
    calc (∫ x, variance (fun y ↦ g (WithLp.toLp 2 (x, y))) ν ∂μ)
        ≤ ∫ x, C' * ∫ y, ‖(gradient g (WithLp.toLp 2 (x, y))).snd‖ ^ 2 ∂ν ∂μ := hmono
      _ = C' * ∫ x, ∫ y, ‖(gradient g (WithLp.toLp 2 (x, y))).snd‖ ^ 2 ∂ν ∂μ :=
          integral_const_mul C' _
      _ = C' * B := by rw [← hswap]
  calc variance g (prodMeasure μ ν)
      = variance (fun p : E × F ↦ g (WithLp.toLp 2 p)) (μ.prod ν) := hvar
    _ ≤ (∫ y, variance (fun x ↦ g (WithLp.toLp 2 (x, y))) μ ∂ν) +
        (∫ x, variance (fun y ↦ g (WithLp.toLp 2 (x, y))) ν ∂μ) := hVle
    _ ≤ C * A + C' * B := add_le_add hterm1 hterm2
    _ ≤ max C C' * A + max C C' * B :=
          add_le_add (mul_le_mul_of_nonneg_right (le_max_left _ _) hA)
            (mul_le_mul_of_nonneg_right (le_max_right _ _) hB)
    _ = max C C' * (A + B) := (mul_add _ _ _).symm
    _ = max C C' * energy (prodMeasure μ ν) g := by rw [energy_prod_eq hg]

/-- Bound for the extended optimal constants, including infinite constants. -/
theorem constant_prod_le
    {μ : Measure E} {ν : Measure F}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    constant (prodMeasure μ ν) ≤ max (constant μ) (constant ν) := by
  rw [← not_lt]
  intro hlt
  obtain ⟨C, hC⟩ : ∃ C : {C : NNReal // Holds μ (C : ℝ)},
      (C.1 : ENNReal) < constant (prodMeasure μ ν) := by
    have h1 : constant μ < constant (prodMeasure μ ν) :=
      lt_of_le_of_lt (le_max_left _ _) hlt
    rw [constant] at h1
    exact iInf_lt_iff.mp h1
  obtain ⟨C', hC'⟩ : ∃ C' : {C' : NNReal // Holds ν (C' : ℝ)},
      (C'.1 : ENNReal) < constant (prodMeasure μ ν) := by
    have h2 : constant ν < constant (prodMeasure μ ν) :=
      lt_of_le_of_lt (le_max_right _ _) hlt
    rw [constant] at h2
    exact iInf_lt_iff.mp h2
  have hH : Holds (prodMeasure μ ν) ((max C.1 C'.1 : NNReal) : ℝ) := by
    have h := C.2.prod C'.2
    rwa [← NNReal.coe_max] at h
  have hle : constant (prodMeasure μ ν) ≤ ((max C.1 C'.1 : NNReal) : ENNReal) :=
    constant_le hH
  have hmax : ((max C.1 C'.1 : NNReal) : ENNReal) < constant (prodMeasure μ ν) := by
    rw [ENNReal.coe_max]
    exact max_lt hC hC'
  exact absurd (hle.trans_lt hmax) (lt_irrefl _)

end FunctionalInequalities.Poincare
