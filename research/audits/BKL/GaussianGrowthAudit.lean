module

public import FunctionalInequalities.KLS.LogConcave.Density.GaussianSmoothing.Growth
public import FunctionalInequalities.KLS.LogConcave.Density.Tilted

/-!
# Audit: polynomial growth of the derivatives of the Gaussian-smoothed potential (BKL Section 2)

Source: Bizeul–Klartag–Lehec, arXiv:2610.05474v1, Section 2, p. 5. Clients: the standard Gaussian
source on `ℝ` at `s = 3` and the zero-dimensional Dirac law have temperate smoothed potentials; the
local weighted derivative formula on a Dirac mass gives the raw value `−16` (no Taylor factorial);
the third-derivative transfer at `s = 3` carries the factor `−216`; the lower polynomial degrees
`1, 2, 3` are derived from the order-three bound; second Laplace moment tensor of a Dirac mass,
dimension-zero vanishing and order zero. Neither the regular approximation nor Theorem 1.1 is
asserted.
-/

open MeasureTheory Set FunctionalInequalities
open FunctionalInequalities.KLS.LogConcave.GaussianSmoothing
  FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace ContDiff

namespace GaussianGrowthAudit

private noncomputable def W (y : ℝ) : ℝ := (1 / 2 : ℝ) * ‖y‖ ^ 2

private theorem W_integrable : Integrable (fun y : ℝ => Real.exp (-W y)) volume := by
  have h :=
    FunctionalInequalities.Probability.Gaussian.integrable_kernel (V := ℝ)
      (by norm_num : (0 : ℝ) < 1 / 2)
  change Integrable (fun y : ℝ => Real.exp (-(1 / 2 : ℝ) * ‖y‖ ^ 2)) volume at h
  convert h using 1
  funext y
  congr 1
  change -((1 / 2 : ℝ) * ‖y‖ ^ 2) = -(1 / 2 : ℝ) * ‖y‖ ^ 2
  ring

noncomputable def gaussianSource : ProbabilityMeasure ℝ :=
  ⟨volume.tilted (-W), isProbabilityMeasure_tilted W_integrable⟩

private theorem gaussian_source_density :
    KLS.IsBorellDensity (gaussianSource : Measure ℝ) volume
      (fun y => Real.exp (-W y) / ∫ z, Real.exp (-W z) ∂volume) := by
  apply KLS.LogConcave.isBorellDensity_of_eq_tilted (W := W) rfl (by
    change Continuous (fun y : ℝ => (1 / 2 : ℝ) * ‖y‖ ^ 2)
    fun_prop)
  change ConvexOn ℝ univ (fun y : ℝ => (1 / 2 : ℝ) * ‖y‖ ^ 2)
  have hcv : ConvexOn ℝ univ (fun y : ℝ => ‖y‖ ^ 2) :=
    convexOn_univ_norm.pow (fun _ _ => norm_nonneg _) 2
  exact hcv.smul (by norm_num : (0 : ℝ) ≤ 1 / 2)

/-- All original source assumptions are derived for a concrete positive-dimensional law. -/
theorem concrete_gaussian_temperate :
    Function.HasTemperateGrowth
      (potential (fun y : ℝ => Real.exp (-W y) / ∫ z, Real.exp (-W z) ∂volume) 3) :=
  potential_hasTemperateGrowth gaussian_source_density (by norm_num : (0 : ℝ) < 3)

private theorem zero_dim_source_density :
    KLS.IsBorellDensity (Measure.dirac (0 : EuclideanSpace ℝ (Fin 0))) volume
      (fun _ => (1 : ℝ)) := by
  refine ⟨measurable_const, fun _ => zero_le_one, upperSemicontinuous_const, ?_, ?_⟩
  · intro x y t ht0 ht1
    simp
  · simpa using (volume_euclideanSpace_eq_dirac (ι := Fin 0))

/-- Actual zero-dimensional Dirac probability law with its genuine density relative to Haar. -/
theorem zero_dimension_dirac_temperate {s : ℝ} (hs : 0 < s) :
    Function.HasTemperateGrowth (potential (fun _ : EuclideanSpace ℝ (Fin 0) => (1 : ℝ)) s) :=
  potential_hasTemperateGrowth zero_dim_source_density hs



/-- Actual weighted third derivative with repeated and mixed-sign directions. The raw answer
is -16, so no accidental Taylor factorial is allowed. -/
theorem weighted_mixed_third :
    iteratedFDeriv ℝ 3 (fun z : ℝ => ∫ y, Real.exp ⟪z, y⟫ • y ∂(Measure.dirac (2 : ℝ))) 0
        ![1, 1, -1] =
      -16 := by
  have hg : AEStronglyMeasurable (id : ℝ → ℝ) (Measure.dirac (2 : ℝ)) := by fun_prop
  have hi :
    ∀ t < (1 : ℝ), Integrable (fun y : ℝ => Real.exp (t * ‖y‖) * ‖y‖) (Measure.dirac (2 : ℝ)) := by
    intro t ht
    exact integrable_dirac enorm_lt_top
  rw [iteratedFDeriv_weightedExp_integral_of_lt (g := fun y : ℝ => y) (Measure.dirac (2 : ℝ)) hg
      hi 3 0 (by norm_num : ‖(0 : ℝ)‖ < 1)]
  norm_num [Fin.prod_univ_succ, Fin.prod_univ_two]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [CompleteSpace E] in
/-- The exact higher transfer at s=3 has the genuine raw third-derivative factor -216. -/
theorem source_third_scale {μ : Measure E} [IsProbabilityMeasure μ]
    {ρ : E → ℝ} (hρ : KLS.IsBorellDensity μ volume ρ) (x : E) (h : Fin 3 → E) :
    iteratedFDeriv ℝ 3 (potential ρ 3) x h =
      (-216 : ℝ) * iteratedFDeriv ℝ 3
        (logLaplace (centeredPosteriorLaw μ (by norm_num : (0 : ℝ) < 3) x : Measure E)) 0 h := by
  rw [potential_iteratedFDeriv_ge_three hρ (by norm_num : (0 : ℝ) < 3) x (by norm_num)]
  norm_num

/-- The original source law supplies the third bound before the real descent to lower degrees.
There is no assumed high-order or temperate-growth premise. -/
theorem source_low_polynomial_degrees {μ : Measure E} [IsProbabilityMeasure μ] {ρ : E → ℝ}
    (hρ : KLS.IsBorellDensity μ volume ρ) {s : ℝ} (hs : 0 < s) :
    (∃ B2 : ℝ, 0 ≤ B2 ∧ ∀ x : E, ‖iteratedFDeriv ℝ 2 (potential ρ s) x‖ ≤ B2 * (1 + ‖x‖) ^ 1) ∧
      (∃ B1 : ℝ,
          0 ≤ B1 ∧ ∀ x : E, ‖iteratedFDeriv ℝ 1 (potential ρ s) x‖ ≤ B1 * (1 + ‖x‖) ^ 2) ∧
        (∃ B0 : ℝ, 0 ≤ B0 ∧ ∀ x : E, ‖potential ρ s x‖ ≤ B0 * (1 + ‖x‖) ^ 3) := by
  obtain ⟨C3, hC3, h3⟩ := exists_uniform_potential_derivative_bound hρ hs (n := 3) le_rfl
  have hf := potential_contDiff_infty hρ hs
  obtain ⟨B2, hB2, h2⟩ :=
    FunctionalInequalities.Analysis.polynomial_growth_of_next_iteratedFDeriv hf 2 0 hC3
      (by intro x; simpa only [pow_zero, mul_one] using h3 x)
  obtain ⟨B1, hB1, h1⟩ :=
    FunctionalInequalities.Analysis.polynomial_growth_of_next_iteratedFDeriv hf 1 1 hB2 h2
  obtain ⟨B0, hB0, h0⟩ :=
    FunctionalInequalities.Analysis.polynomial_growth_of_next_iteratedFDeriv hf 0 2 hB1 h1
  refine ⟨⟨B2, hB2, h2⟩, ⟨B1, hB1, h1⟩, B0, hB0, ?_⟩
  intro x
  simpa only [norm_iteratedFDeriv_zero] using h0 x


private theorem dirac_exp :
    Integrable (fun y : ℝ => Real.exp ((1 : ℝ) * ‖y‖)) (Measure.dirac (1 : ℝ)) :=
  integrable_dirac (by simp)

/-- The true second Laplace moment tensor is nonzero and evaluates to one in unit directions. -/
theorem nonzero_second_moment_tensor :
    iteratedFDeriv ℝ 2 (fun z : ℝ => ∫ y, Real.exp ⟪z, y⟫ ∂(Measure.dirac (1 : ℝ)))
      0 ![1, 1] = 1 := by
  rw [iteratedFDeriv_laplace_zero (Measure.dirac (1 : ℝ)) (by norm_num : (0 : ℝ) < 1) dirac_exp]
  simp [Fin.prod_univ_two]

/-- The operator norm bound is attained by the actual nonzero second tensor. -/
theorem second_moment_norm_attained :
    ‖iteratedFDeriv ℝ 2 (fun z : ℝ => ∫ y, Real.exp ⟪z, y⟫ ∂(Measure.dirac (1 : ℝ))) 0‖ = 1 := by
  have hu := norm_iteratedFDeriv_laplace_zero_le (Measure.dirac (1 : ℝ))
    (by norm_num : (0 : ℝ) < 1) dirac_exp 2
  norm_num at hu
  have hl := (iteratedFDeriv ℝ 2
    (fun z : ℝ => ∫ y, Real.exp ⟪z, y⟫ ∂(Measure.dirac (1 : ℝ))) 0).le_opNorm ![1, 1]
  rw [nonzero_second_moment_tensor] at hl
  norm_num [Fin.prod_univ_two] at hl ⊢
  exact le_antisymm hu hl

/-- Original real Gaussian source inputs, with all intermediate desired bounds discharged. -/
theorem source_order_three {μ : Measure ℝ} [IsProbabilityMeasure μ] {ρ : ℝ → ℝ}
    (hρ : KLS.IsBorellDensity μ volume ρ) {s : ℝ} (hs : 0 < s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, ‖iteratedFDeriv ℝ 3 (potential ρ s) x‖ ≤ C :=
  exists_uniform_potential_derivative_bound hρ hs (by norm_num : 3 ≤ (3 : ℕ))

/-- Dimension-zero higher derivatives vanish for the actual Laplace integral. -/
theorem zero_dim_positive_derivative {μ : Measure (EuclideanSpace ℝ (Fin 0))}
    [IsProbabilityMeasure μ] (r : ℝ) (hr : 0 < r)
    (hexp : Integrable (fun y => Real.exp (r * ‖y‖)) μ) :
    ‖iteratedFDeriv ℝ 3 (fun z => ∫ y, Real.exp ⟪z, y⟫ ∂μ) 0‖ = 0 := by
  have h := norm_iteratedFDeriv_laplace_zero_le μ hr hexp 3
  have hf : (fun y : EuclideanSpace ℝ (Fin 0) => ‖y‖ ^ 3) = fun _ => (0 : ℝ) := by
    funext y
    rw [Subsingleton.elim y 0]
    simp
  rw [hf, integral_zero] at h
  exact le_antisymm h (norm_nonneg _)

/-- Order zero stays one for every genuine probability law, including dimension zero. -/
theorem laplace_order_zero (μ : Measure (EuclideanSpace ℝ (Fin 0))) [IsProbabilityMeasure μ] :
    ‖iteratedFDeriv ℝ 0 (fun z => ∫ y, Real.exp ⟪z, y⟫ ∂μ) 0‖ = 1 := by
  simp only [norm_iteratedFDeriv_zero, inner_zero_left, Real.exp_zero, integral_const,
    probReal_univ, one_smul, norm_one]

end GaussianGrowthAudit

#print axioms FunctionalInequalities.Analysis.BakryEmery.iteratedFDeriv_weightedExp_integral_of_lt
#print axioms FunctionalInequalities.Analysis.BakryEmery.iteratedFDeriv_laplace_zero
#print axioms FunctionalInequalities.Analysis.BakryEmery.norm_iteratedFDeriv_laplace_zero_le
#print axioms FunctionalInequalities.Analysis.norm_iteratedFDeriv_log_comp_le_factorial_sq
#print axioms FunctionalInequalities.Analysis.hasTemperateGrowth_of_bounded_high_derivatives
#print axioms
  FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.integrable_exp_norm_centeredPosteriorLaw
#print axioms
  FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.potential_centered_factorization
#print axioms
  FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.potential_iteratedFDeriv_ge_three
#print axioms
  FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.exists_uniform_potential_derivative_bound
#print axioms FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.potential_hasTemperateGrowth
#print axioms GaussianGrowthAudit.concrete_gaussian_temperate
#print axioms GaussianGrowthAudit.zero_dimension_dirac_temperate
#print axioms GaussianGrowthAudit.weighted_mixed_third
#print axioms GaussianGrowthAudit.source_third_scale
#print axioms GaussianGrowthAudit.source_low_polynomial_degrees
#print axioms GaussianGrowthAudit.nonzero_second_moment_tensor
#print axioms GaussianGrowthAudit.second_moment_norm_attained
#print axioms GaussianGrowthAudit.source_order_three
#print axioms GaussianGrowthAudit.zero_dim_positive_derivative
#print axioms GaussianGrowthAudit.laplace_order_zero
