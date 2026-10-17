import FunctionalInequalities.Analysis.Cutoff.Conservativity
import FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.InverseHessian.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecificLimits.Basic

/-! Core client, re-pointed to the canonical module/name (`Analysis/Cutoff/Conservativity.lean`): the actual uniform
two-atom probability law on `Bool` (atoms `true`, `false`, mass `1/2` each), signed bounded `f` (values `2`, `-1`),
`g` (values `-1`, `1`), `c = 1`, cutoffs `χ_n` (values `1`, `1 - 1/(n+2)`), defects (values `-1/(2(n+2))`, `0`).
Every premise of `integrable_and_integral_eq_zero_of_cutoff_defect` is proved here from the actual values: `g + c f`
takes the values `1`, `0`; both sides of the weak symmetry equal `-1/(2(n+2))` (nonzero, so the symmetry does not encode
the conclusion); `∫ |defect_n| = 1/(4(n+2)) → 0`. The conclusion `Integrable g ∧ ∫ g = 0` is obtained only from the
core; `integral_g_direct` is an independent arithmetic cross-check, not a premise. -/

open MeasureTheory Filter
open scoped Topology ENNReal
open FunctionalInequalities.Analysis

namespace A5TwoAtomClient

/-- The uniform two-atom law. -/
noncomputable def law : ProbabilityMeasure Bool :=
  ⟨(2⁻¹ : ℝ≥0∞) • (Measure.dirac true + Measure.dirac false), by
    constructor
    simp only [Measure.smul_apply, Measure.add_apply, measure_univ, smul_eq_mul]
    rw [one_add_one_eq_two]
    exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)⟩

theorem integral_law (h : Bool → ℝ) : ∫ x, h x ∂(law : Measure Bool) = (h true + h false) / 2 := by
  change ∫ x, h x ∂((2⁻¹ : ℝ≥0∞) • (Measure.dirac true + Measure.dirac false)) = _
  rw [integral_smul_measure, integral_add_measure (Integrable.of_finite) (Integrable.of_finite),
    integral_dirac, integral_dirac]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_ofNat, smul_eq_mul]
  ring

theorem integrable_law (h : Bool → ℝ) : Integrable h (law : Measure Bool) := Integrable.of_finite

theorem aesm_law (h : Bool → ℝ) : AEStronglyMeasurable h (law : Measure Bool) :=
  (integrable_law h).aestronglyMeasurable

/-- Signed bounded `f`. -/
def f : Bool → ℝ := fun b => if b then 2 else -1
/-- The function whose integrability and zero mean are concluded. -/
def g : Bool → ℝ := fun b => if b then -1 else 1
/-- Cutoffs. -/
noncomputable def chi (n : ℕ) : Bool → ℝ := fun b => if b then 1 else 1 - 1 / ((n : ℝ) + 2)
/-- Defects. -/
noncomputable def defect (n : ℕ) : Bool → ℝ := fun b => if b then -1 / (2 * ((n : ℝ) + 2)) else 0

theorem f_bound : ∀ᵐ x ∂(law : Measure Bool), |f x| ≤ 2 :=
  ae_of_all _ fun b => by cases b <;> norm_num [f]

theorem lower : ∀ᵐ x ∂(law : Measure Bool), 0 ≤ g x + 1 * f x :=
  ae_of_all _ fun b => by cases b <;> norm_num [f, g]

theorem chi_bounds (n : ℕ) : ∀ᵐ x ∂(law : Measure Bool), 0 ≤ chi n x ∧ chi n x ≤ 1 := by
  refine ae_of_all _ fun b => ?_
  have h2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  cases b
  · simp only [chi, Bool.false_eq_true, ↓reduceIte]
    refine ⟨?_, ?_⟩
    · rw [sub_nonneg, div_le_one h2]; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
    · have : 0 ≤ 1 / ((n : ℝ) + 2) := by positivity
      linarith
  · simp [chi]

theorem chi_lim : ∀ᵐ x ∂(law : Measure Bool), Tendsto (fun n => chi n x) atTop (𝓝 1) := by
  refine ae_of_all _ fun b => ?_
  cases b
  · have h := ((tendsto_one_div_add_atTop_nhds_zero_nat :
      Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0)).comp (tendsto_add_atTop_nat 1))
    have h' : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 0) := by
      refine h.congr fun n => ?_
      simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
      ring_nf
    simpa [chi] using (tendsto_const_nhds (x := (1 : ℝ))).sub h'
  · simp [chi]

theorem defect_lim :
    Tendsto (fun n => ∫ x, |defect n x| ∂(law : Measure Bool)) atTop (𝓝 0) := by
  have h := ((tendsto_one_div_add_atTop_nhds_zero_nat :
      Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0)).comp (tendsto_add_atTop_nat 1))
  have hv (n : ℕ) : ∫ x, |defect n x| ∂(law : Measure Bool) = (1 / 4) * (1 / (((n + 1 : ℕ) : ℝ) + 1)) := by
    rw [integral_law]
    have h2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
    simp only [defect, ↓reduceIte, Bool.false_eq_true, abs_zero, add_zero, Nat.cast_add, Nat.cast_one]
    rw [abs_of_neg (by apply div_neg_of_neg_of_pos <;> [norm_num; positivity])]
    field_simp
    ring
  simpa [hv] using h.const_mul (1 / 4 : ℝ)

theorem symmetry (n : ℕ) :
    (∫ x, chi n x * g x ∂(law : Measure Bool)) = ∫ x, f x * defect n x ∂(law : Measure Bool) := by
  rw [integral_law, integral_law]
  have h2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  simp only [chi, g, f, defect, ↓reduceIte, Bool.false_eq_true]
  field_simp
  ring

/-- Both sides of the symmetry are the nonzero value `-1/(2(n+2))`. -/
theorem symmetry_value (n : ℕ) :
    (∫ x, chi n x * g x ∂(law : Measure Bool)) = -1 / (2 * ((n : ℝ) + 2)) := by
  rw [integral_law]
  have h2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  simp only [chi, g, ↓reduceIte, Bool.false_eq_true]
  field_simp
  ring

/-- **Client:** the core concludes integrability and zero mean of `g` from the actual premises. -/
theorem conservativity : Integrable g (law : Measure Bool) ∧ (∫ x, g x ∂(law : Measure Bool)) = 0 :=
  integrable_and_integral_eq_zero_of_cutoff_defect law f g (aesm_law f) (aesm_law g) 2 (by norm_num) f_bound
    1 one_pos lower chi defect (fun n => aesm_law (chi n)) chi_bounds chi_lim (fun n => integrable_law (defect n))
    defect_lim (fun n => integrable_law _) symmetry

/-- Independent arithmetic cross-check (not used above). -/
theorem integral_g_direct : (∫ x, g x ∂(law : Measure Bool)) = 0 := by
  rw [integral_law]; norm_num [g]

end A5TwoAtomClient

#print axioms A5TwoAtomClient.lower
#print axioms A5TwoAtomClient.chi_bounds
#print axioms A5TwoAtomClient.chi_lim
#print axioms A5TwoAtomClient.defect_lim
#print axioms A5TwoAtomClient.symmetry
#print axioms A5TwoAtomClient.symmetry_value
#print axioms A5TwoAtomClient.integral_g_direct
#print axioms A5TwoAtomClient.conservativity

/-! ### Necessity of the defect decay: an actual Dirac counterexample

On the Dirac law, `f = g = χ_n = d_n = 1`, `C = c = 1`: every premise of `integrable_and_integral_eq_zero_of_cutoff_defect`
except `∫ |d_n| → 0` holds, and `∫ g = 1 ≠ 0`. -/

namespace A5DiracCounterexample

/-- The Dirac law on `Unit`. -/
noncomputable def law : ProbabilityMeasure Unit := ⟨Measure.dirac (), inferInstance⟩

theorem integral_law (h : Unit → ℝ) : ∫ x, h x ∂(law : Measure Unit) = h () := by
  change ∫ x, h x ∂(Measure.dirac ()) = h ()
  rw [integral_dirac]

/-- All premises other than the defect decay, for the constant data `1`. -/
theorem premises_except_decay :
    AEStronglyMeasurable (fun _ : Unit => (1 : ℝ)) (law : Measure Unit) ∧ (0 : ℝ) ≤ 1 ∧
      (∀ᵐ x ∂(law : Measure Unit), |(fun _ : Unit => (1 : ℝ)) x| ≤ 1) ∧ (0 : ℝ) < 1 ∧
      (∀ᵐ x ∂(law : Measure Unit), 0 ≤ (fun _ : Unit => (1 : ℝ)) x + 1 * (fun _ : Unit => (1 : ℝ)) x) ∧
      (∀ n : ℕ, ∀ᵐ x ∂(law : Measure Unit), 0 ≤ (fun (_ : ℕ) (_ : Unit) => (1 : ℝ)) n x ∧
        (fun (_ : ℕ) (_ : Unit) => (1 : ℝ)) n x ≤ 1) ∧
      (∀ᵐ x ∂(law : Measure Unit), Tendsto (fun n : ℕ => (fun (_ : ℕ) (_ : Unit) => (1 : ℝ)) n x) atTop (𝓝 1)) ∧
      (∀ n : ℕ, Integrable ((fun (_ : ℕ) (_ : Unit) => (1 : ℝ)) n) (law : Measure Unit)) ∧
      (∀ n : ℕ, (∫ x, (fun (_ : ℕ) (_ : Unit) => (1 : ℝ)) n x * (fun _ : Unit => (1 : ℝ)) x ∂(law : Measure Unit)) =
        ∫ x, (fun _ : Unit => (1 : ℝ)) x * (fun (_ : ℕ) (_ : Unit) => (1 : ℝ)) n x ∂(law : Measure Unit)) := by
  refine ⟨aestronglyMeasurable_const, zero_le_one, ae_of_all _ fun _ => by norm_num, one_pos,
    ae_of_all _ fun _ => by norm_num, fun _ => ae_of_all _ fun _ => ⟨zero_le_one, le_rfl⟩,
    ae_of_all _ fun _ => tendsto_const_nhds, fun _ => integrable_const _, fun _ => rfl⟩

/-- The defect does not decay: `∫ |d_n| = 1` for every `n`. -/
theorem not_decay :
    ¬ Tendsto (fun n : ℕ => ∫ x, |(fun (_ : ℕ) (_ : Unit) => (1 : ℝ)) n x| ∂(law : Measure Unit)) atTop (𝓝 0) := by
  intro h
  have hv : (fun n : ℕ => ∫ x, |(fun (_ : ℕ) (_ : Unit) => (1 : ℝ)) n x| ∂(law : Measure Unit)) = fun _ => 1 := by
    funext n; rw [integral_law]; norm_num
  rw [hv] at h
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds h)

/-- The conclusion fails: `∫ g = 1`. -/
theorem integral_g : (∫ x, (fun _ : Unit => (1 : ℝ)) x ∂(law : Measure Unit)) = 1 := by
  rw [integral_law]

end A5DiracCounterexample

#print axioms A5DiracCounterexample.premises_except_decay
#print axioms A5DiracCounterexample.not_decay
#print axioms A5DiracCounterexample.integral_g
#print axioms FunctionalInequalities.Analysis.integrable_and_integral_eq_zero_of_cutoff_defect
#print axioms FunctionalInequalities.Analysis.BakryEmery.integrable_and_integral_hessianInverseOperator_eq_zero_of_cutoffs
