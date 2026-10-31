module

public import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Generator.FormRange

/-! Independent clients of the class-level form-range density. The law is `ν = m.tilted (-U)`
for a smooth potential, the closed gradient `T̄` has unit weight, `A = T̄†T̄`, `J = I + A`, and
the form domain `D(T̄)` carries the graph norm. The clients instantiate an arbitrary target
`z ∈ D(T̄)`, extract an approximating sequence, check the norm and operator bridges
separately, and check zero dimension, where `J = I`. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.KLS.LogConcave
  FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
  FunctionalInequalities.Analysis.WaveSplitting FunctionalInequalities.Energy.WeightedGradient
open scoped ContDiff RealInnerProductSpace
namespace WaveSplittingFormRangeAudit
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] (hν : LogConcave ν)
  (hi : (interior (ν : Measure V).support).Nonempty) {U : V → ℝ}

/-- **Arbitrary target.** For every `z ∈ D(T̄)` there are `qₙ ∈ C_c^∞` with `J[qₙ] ∈ D(T̄)`
and `‖J[qₙ] - z‖_E < 1/(n+1)` in the graph norm. -/
theorem arbitrary_target (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ ∞ U)
    (z : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain) (n : ℕ) :
    ∃ (q : V → ℝ) (hq : ContDiff ℝ ∞ q) (hqc : HasCompactSupport q)
      (hA : (memLp_of_contDiff_hasCompactSupport ν hq hqc).toLp q ∈
        (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain)
      (hJ : (memLp_of_contDiff_hasCompactSupport ν hq hqc).toLp q +
          adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) ⟨_, hA⟩ ∈
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain),
      ‖(memLp_of_contDiff_hasCompactSupport ν hq hqc).toLp q +
            adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) ⟨_, hA⟩ -
            (z : Lp ℝ 2 (ν : Measure V))‖ ^ 2 +
          ‖hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi ⟨_, hJ⟩ -
            hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi z‖ ^ 2 <
        (1 / ((n : ℝ) + 1)) ^ 2 := by
  obtain ⟨q, hq, hqc, hA, hJ, hlt⟩ :=
    exists_toLp_add_adjointComp_graph_lt hνU hU z (ε := 1 / ((n : ℝ) + 1)) (by positivity)
  refine ⟨q, hq, hqc, hA, hJ, ?_⟩
  have h0 : 0 ≤ ‖(memLp_of_contDiff_hasCompactSupport ν hq hqc).toLp q +
      adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) ⟨_, hA⟩ -
      (z : Lp ℝ 2 (ν : Measure V))‖ ^ 2 +
      ‖hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi ⟨_, hJ⟩ -
        hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi z‖ ^ 2 := by positivity
  rwa [Real.sqrt_lt' (by positivity)] at hlt

/-- **Norm bridge client.** For `f ∈ C_c^∞`, the graph norm of `[f]` in the standard
orthonormal basis is `(1/Z) ∫ exp (-U) (f² + ‖∇f‖²) dm`, with `Z > 0`. -/
theorem norm_bridge (hνU : (ν : Measure V) = m.tilted (-U)) {f : V → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f) :
    0 < ∫ y, Real.exp (-U y) ∂m ∧
    ‖(memLp_of_contDiff_hasCompactSupport ν hf hfc).toLp f‖ ^ 2 +
        ‖hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
          ⟨_, hν.toLp_mem_closedWeightedOperator_domain m hi hf hfc⟩‖ ^ 2 =
      (∫ y, Real.exp (-U y) * (f y ^ 2 + ‖gradient f y‖ ^ 2) ∂m) /
        ∫ y, Real.exp (-U y) ∂m := by
  refine ⟨integral_exp_neg_pos_of_tilted m hνU, ?_⟩
  have h := norm_sq_add_norm_closedWeightedOperator_sq_eq m hν hi hνU (stdOrthonormalBasis ℝ V)
    ⟨_, hν.toLp_mem_closedWeightedOperator_domain m hi hf hfc⟩ hf hfc rfl
  rwa [weightedFormEnergy_eq_integral_norm_gradient] at h

omit [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] in
/-- The pointwise identities behind the bridges, in an arbitrary orthonormal basis. -/
theorem pointwise_identities {ι : Type*} [Fintype ι] (e : OrthonormalBasis ι ℝ V) {f : V → ℝ}
    (hf : ContDiff ℝ 2 f) (x : V) :
    ∑ j, fderiv ℝ f x (e j) ^ 2 = ‖gradient f x‖ ^ 2 ∧
      ∑ j, fderiv ℝ (fun y => fderiv ℝ f y (e j)) x (e j) = Laplacian.laplacian f x ∧
      ∑ j, fderiv ℝ U x (e j) * fderiv ℝ f x (e j) = ⟪gradient U x, gradient f x⟫ ∧
      formOperator e (fun j x => fderiv ℝ U x (e j)) f x = f x - weightedLaplacian U f x :=
  ⟨sum_fderiv_sq_eq_norm_gradient_sq e f x,
    sum_fderiv_fderiv_eq_laplacian e
      ((hf.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero x),
    sum_fderiv_mul_fderiv_eq_inner_gradient e U f x,
    congrFun (formOperator_eq_sub_weightedLaplacian e U hf) x⟩

/-- **Operator bridge client.** For `q ∈ C_c^∞`, `J[q] = [q - ℒq]` in `L²(ν)` and
`J[q] ∈ D(T̄)`. -/
theorem operator_bridge (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ ∞ U)
    {q : V → ℝ} (hq : ContDiff ℝ ∞ q) (hqc : HasCompactSupport q) :
    ∃ hL : MemLp (fun x => q x - weightedLaplacian U q x) 2 (ν : Measure V),
      (memLp_of_contDiff_hasCompactSupport ν hq hqc).toLp q +
          adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)
            ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU (hU.of_le (by decide)) hq hqc⟩ =
        hL.toLp _ ∧
      hL.toLp _ ∈ (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain := by
  have hq2 : ContDiff ℝ 2 q := hq.of_le (WithTop.coe_le_coe.mpr le_top)
  have hfo := formOperator_eq_sub_weightedLaplacian (stdOrthonormalBasis ℝ V) U hq2
  have hL : MemLp (fun x => q x - weightedLaplacian U q x) 2 (ν : Measure V) := by
    rw [← hfo]
    exact memLp_of_contDiff_hasCompactSupport ν (contDiff_formOperator _ hU hq)
      (hasCompactSupport_formOperator _ U hq2 hqc)
  have heq := toLp_add_adjointComp_eq_formOperator (hν := hν) (hi := hi) hνU hU
    (stdOrthonormalBasis ℝ V) hq hqc
  have hJ := toLp_add_adjointComp_mem_closedWeightedOperator_domain (hν := hν) (hi := hi) hνU hU
    hq hqc
  have hc : (memLp_of_contDiff_hasCompactSupport ν (contDiff_formOperator _ hU hq)
      (hasCompactSupport_formOperator _ U hq2 hqc)).toLp
        (formOperator (stdOrthonormalBasis ℝ V) (fun j x => fderiv ℝ U x
          (stdOrthonormalBasis ℝ V j)) q) = hL.toLp _ :=
    MemLp.toLp_congr _ _ (Eventually.of_forall fun x => congrFun hfo x)
  refine ⟨hL, heq.trans hc, ?_⟩
  rw [← hc, ← heq]
  exact hJ

/-- **Zero dimension.** If `finrank ℝ V = 0`, then `J = I` on `C_c^∞`: `T̄†T̄[q] = 0`. The
density theorem applies unchanged (`arbitrary_target` has no dimension hypothesis). -/
theorem zero_dimension (h0 : Module.finrank ℝ V = 0) (hνU : (ν : Measure V) = m.tilted (-U))
    (hU : ContDiff ℝ ∞ U) {q : V → ℝ} (hq : ContDiff ℝ ∞ q) (hqc : HasCompactSupport q) :
    adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)
        ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU (hU.of_le (by decide)) hq hqc⟩ = 0 := by
  have : IsEmpty (Fin (Module.finrank ℝ V)) := by rw [h0]; infer_instance
  have heq := toLp_add_adjointComp_eq_formOperator (hν := hν) (hi := hi) hνU hU
    (stdOrthonormalBasis ℝ V) hq hqc
  have hid : formOperator (stdOrthonormalBasis ℝ V)
      (fun j x => fderiv ℝ U x (stdOrthonormalBasis ℝ V j)) q = q := by
    funext x; simp [formOperator]
  have hc : (memLp_of_contDiff_hasCompactSupport ν (contDiff_formOperator _ hU hq)
      (hasCompactSupport_formOperator _ U (hq.of_le (WithTop.coe_le_coe.mpr le_top)) hqc)).toLp
        (formOperator (stdOrthonormalBasis ℝ V) (fun j x => fderiv ℝ U x
          (stdOrthonormalBasis ℝ V j)) q) =
      (memLp_of_contDiff_hasCompactSupport ν hq hqc).toLp q :=
    MemLp.toLp_congr _ _ (Eventually.of_forall fun x => congrFun hid x)
  rw [hc] at heq
  exact add_eq_left.mp heq

omit [CompleteSpace V] [BorelSpace V] [SecondCountableTopology V] [m.IsAddHaarMeasure] in
/-- In zero dimension the weighted coordinate form energy has no derivative terms. -/
theorem zero_dimension_energy (h0 : Module.finrank ℝ V = 0) (w f : V → ℝ) :
    weightedFormEnergy m w (stdOrthonormalBasis ℝ V) f = ∫ y, w y * f y ^ 2 ∂m := by
  have : IsEmpty (Fin (Module.finrank ℝ V)) := by rw [h0]; infer_instance
  simp [weightedFormEnergy_eq]

#print axioms arbitrary_target
#print axioms norm_bridge
#print axioms pointwise_identities
#print axioms operator_bridge
#print axioms zero_dimension
#print axioms zero_dimension_energy
#print axioms FunctionalInequalities.Analysis.WaveSplitting.fderiv_exp_neg_apply
#print axioms FunctionalInequalities.Analysis.WaveSplitting.exists_timeAverage_error_lt
#print axioms FunctionalInequalities.Analysis.WaveSplitting.sum_fderiv_sq_eq_norm_gradient_sq
#print axioms FunctionalInequalities.Analysis.WaveSplitting.sum_fderiv_mul_fderiv_eq_inner_gradient
#print axioms FunctionalInequalities.Analysis.WaveSplitting.sum_fderiv_fderiv_eq_laplacian
#print axioms FunctionalInequalities.Analysis.WaveSplitting.formOperator_eq_sub_weightedLaplacian
#print axioms FunctionalInequalities.Analysis.WaveSplitting.contDiff_formOperator
#print axioms FunctionalInequalities.Analysis.WaveSplitting.hasCompactSupport_formOperator
#print axioms
  FunctionalInequalities.Analysis.WaveSplitting.weightedFormEnergy_eq_integral_norm_gradient
#print axioms FunctionalInequalities.Analysis.WaveSplitting.integrable_exp_neg_of_tilted
#print axioms FunctionalInequalities.Analysis.WaveSplitting.integral_exp_neg_pos_of_tilted
#print axioms FunctionalInequalities.Analysis.WaveSplitting.integral_exp_neg_mul_eq_of_tilted
#print axioms FunctionalInequalities.Analysis.WaveSplitting.weightedFormEnergy_eq_mul_integral
#print axioms FunctionalInequalities.KLS.LogConcave.norm_sq_add_norm_closedWeightedOperator_sq_eq
#print axioms FunctionalInequalities.KLS.LogConcave.toLp_add_adjointComp_eq_formOperator
#print axioms
  FunctionalInequalities.KLS.LogConcave.toLp_add_adjointComp_mem_closedWeightedOperator_domain
#print axioms FunctionalInequalities.KLS.LogConcave.exists_toLp_add_adjointComp_graph_lt
#print axioms FunctionalInequalities.KLS.LogConcave.dense_formRange_graphL2
end WaveSplittingFormRangeAudit
