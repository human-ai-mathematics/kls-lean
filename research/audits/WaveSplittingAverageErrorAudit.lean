import FunctionalInequalities.Analysis.WaveSplitting.AverageError

/-! Independent clients of the quantitative error of the finite time average. The weight is
`exp (-U)` for an arbitrary smooth potential with `b_j = D_(a_j) U`; no convexity or global
derivative bound is assumed. The density client chooses the horizon first and then the mesh. -/
noncomputable section
set_option autoImplicit false
open MeasureTheory FunctionalInequalities.Analysis.WaveSplitting
open scoped ContDiff
namespace WaveSplittingAverageErrorAudit
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  (m : Measure E) [m.IsAddHaarMeasure]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem potential_weight (d : ℕ) (a : Fin d → E) {U : E → ℝ} (hU : ContDiff ℝ ∞ U) :
    ContDiff ℝ 1 (fun x => Real.exp (-U x)) ∧ (∀ x, 0 ≤ Real.exp (-U x)) ∧
      ∀ j x, fderiv ℝ (fun x => Real.exp (-U x)) x (a j) =
        -(fderiv ℝ U x (a j) * Real.exp (-U x)) := by
  refine ⟨Real.contDiff_exp.comp ((hU.of_le (by simp)).neg), fun x => (Real.exp_pos _).le,
    fun j x => ?_⟩
  have h : HasFDerivAt (fun x => Real.exp (-U x)) (Real.exp (-U x) • -fderiv ℝ U x) x :=
    (((hU.differentiable (by simp)) x).hasFDerivAt.neg).exp
  rw [h.fderiv]
  simp only [FunLike.coe_smul, FunLike.coe_neg, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
  ring

/-- The mesh-uniform error bound for the potential weight. -/
theorem potential_error (d : ℕ) (a : Fin d → E) (U h : E → ℝ) (hU : ContDiff ℝ ∞ U)
    (hh : ContDiff ℝ ∞ h) (hc : HasCompactSupport h) {L : ℝ} (hL : 0 < L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (δ : ℝ), 0 < δ → δ ≤ 1 → (N : ℝ) * δ = L →
      √(weightedFormEnergy m (fun x => Real.exp (-U x)) a (fun x =>
          formOperator a (fun j x => fderiv ℝ U x (a j))
            (timeAverage a (fun j x => fderiv ℝ U x (a j)) (List.finRange d) δ (initial h) N) x -
            h x)) ≤
        √(∫ x, Real.exp (-U x) * h x ^ 2 ∂m) / L + C * δ := by
  have hb (j : Fin d) : ContDiff ℝ ∞ (fun x => fderiv ℝ U x (a j)) :=
    (hU.fderiv_right (by simp)).clm_apply contDiff_const
  obtain ⟨hw, hw0, hwb⟩ := potential_weight d a hU
  exact exists_timeAverage_error_bound m a hb hw hw0 hwb hh hc hL

/-- **Classical form-range approximation.** For every compactly supported smooth `h` and every
`ε > 0` there is an actual cellwise time average `q ∈ C_c^∞` with
`sqrt FE_w(J_cl q - h) < ε`. The horizon is chosen first, then the mesh. -/
theorem potential_density (d : ℕ) (a : Fin d → E) (U h : E → ℝ) (hU : ContDiff ℝ ∞ U)
    (hh : ContDiff ℝ ∞ h) (hc : HasCompactSupport h) {ε : ℝ} (hε : 0 < ε) :
    ∃ (N : ℕ) (δ : ℝ), 0 < δ ∧
      ContDiff ℝ ∞ (timeAverage a (fun j x => fderiv ℝ U x (a j)) (List.finRange d) δ
        (initial h) N) ∧
      HasCompactSupport (timeAverage a (fun j x => fderiv ℝ U x (a j)) (List.finRange d) δ
        (initial h) N) ∧
      √(weightedFormEnergy m (fun x => Real.exp (-U x)) a (fun x =>
          formOperator a (fun j x => fderiv ℝ U x (a j))
            (timeAverage a (fun j x => fderiv ℝ U x (a j)) (List.finRange d) δ (initial h) N) x -
            h x)) < ε := by
  have hb (j : Fin d) : ContDiff ℝ ∞ (fun x => fderiv ℝ U x (a j)) :=
    (hU.fderiv_right (by simp)).clm_apply contDiff_const
  set W := √(∫ x, Real.exp (-U x) * h x ^ 2 ∂m)
  have hW : 0 ≤ W := Real.sqrt_nonneg _
  set L := 2 * (W + 1) / ε
  have hL : 0 < L := by positivity
  obtain ⟨C, hC, hbound⟩ := potential_error m d a U h hU hh hc hL
  obtain ⟨N, hN⟩ := exists_nat_gt (max L (2 * C * L / ε))
  have hNpos : (0 : ℝ) < N := lt_of_le_of_lt (le_max_left _ _ |>.trans' hL.le) hN
  set δ := L / N
  have hδ : 0 < δ := div_pos hL hNpos
  have hδ1 : δ ≤ 1 := by
    rw [div_le_one hNpos]; exact (le_max_left _ _).trans hN.le
  have hNδ : (N : ℝ) * δ = L := by simp only [δ]; field_simp
  obtain ⟨R, _, hR⟩ := supported_initial (ι := Fin d) hc
  refine ⟨N, δ, hδ, contDiff_timeAverage a hb _ (smooth_initial hh) δ N,
    hasCompactSupport_timeAverage a _ _ hR hδ.le N, ?_⟩
  have h₁ := hbound N δ hδ hδ1 hNδ
  have h₂ : W / L < ε / 2 := by
    rw [div_lt_iff₀ hL]; simp only [L]; field_simp; nlinarith
  have h₃ : C * δ < ε / 2 := by
    have hlt : 2 * C * L / ε < N := (le_max_right _ _).trans_lt hN
    rw [div_lt_iff₀ hε] at hlt
    simp only [δ]
    rw [mul_div_assoc', div_lt_iff₀ hNpos]
    nlinarith
  linarith

/-- The general estimate admits dimension zero, with any `C^1` weight. -/
theorem zero_dimension {w : E → ℝ} (hw : ContDiff ℝ 1 w) (hw0 : ∀ x, 0 ≤ w x) (h : E → ℝ)
    (hh : ContDiff ℝ ∞ h) (hc : HasCompactSupport h) {L : ℝ} (hL : 0 < L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (δ : ℝ), 0 < δ → δ ≤ 1 → (N : ℝ) * δ = L →
      √(weightedFormEnergy m w Fin.elim0 (fun x =>
          formOperator Fin.elim0 Fin.elim0
            (timeAverage Fin.elim0 Fin.elim0 (List.finRange 0) δ (initial h) N) x - h x)) ≤
        √(∫ x, w x * h x ^ 2 ∂m) / L + C * δ :=
  exists_timeAverage_error_bound m Fin.elim0 (b := Fin.elim0) (fun j => Fin.elim0 j) hw hw0
    (fun j => Fin.elim0 j) hh hc hL

#print axioms potential_error
#print axioms potential_density
#print axioms zero_dimension
#print axioms FunctionalInequalities.Analysis.WaveSplitting.contDiff_primitive_slice
#print axioms FunctionalInequalities.Analysis.WaveSplitting.scalarEnergy_intervalIntegral_le
#print axioms FunctionalInequalities.Analysis.WaveSplitting.sqrt_scalarEnergy_sum_le
#print axioms FunctionalInequalities.Analysis.WaveSplitting.weightedFormEnergy_add_le
#print axioms FunctionalInequalities.Analysis.WaveSplitting.weightedFormEnergy_le
#print axioms FunctionalInequalities.Analysis.WaveSplitting.scalarEnergy_weightedDivergence_le
#print axioms FunctionalInequalities.Analysis.WaveSplitting.exists_timeAverage_error_bound
end WaveSplittingAverageErrorAudit
