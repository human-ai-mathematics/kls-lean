import FunctionalInequalities.Probability.Conditioning
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Probability.Moments.Variance

/-! Independent audit clients for CB5 half mass and CB1/CB4 ball conditioning (Probability/Moments.lean section MomentTails, Probability/Conditioning.lean). Merged verbatim from the reviewer receipt `CB5-CB4-Independent-20261008 (raw d81354de…)` (modules
Models, ConditionModels, ConditionClients, BoundaryClients, ZeroClients), re-pointed from the raw `Candidate*` modules to the production owners; contracts/axiom-enumeration
tooling stays in the receipt. -/

-- ===== reviewer module Models (CB5-CB4-Independent-20261008 (raw d81354de…)) =====
noncomputable section
set_option autoImplicit false
open MeasureTheory
namespace CBTailModels
variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]

def atom (a : E) : ProbabilityMeasure E := ⟨Measure.dirac a, inferInstance⟩
lemma atom_integrable (a : E) (f : E → ℝ) : Integrable f (atom a : Measure E) :=
  integrable_dirac (by simp)
lemma atom_integral (a : E) (f : E → ℝ) :
    (∫ x, f x ∂(atom a : Measure E)) = f a := integral_dirac f a

def halfAtoms : ProbabilityMeasure ℝ :=
  ⟨(1 / 2 : ENNReal) • Measure.dirac 0 + (1 / 2 : ENNReal) • Measure.dirac 1, by
    constructor
    norm_num
    exact ENNReal.inv_two_add_inv_two⟩
lemma half_integrable (f : ℝ → ℝ) : Integrable f (halfAtoms : Measure ℝ) := by
  change Integrable f ((1 / 2 : ENNReal) • Measure.dirac 0 + (1 / 2 : ENNReal) • Measure.dirac 1)
  exact ((integrable_dirac (by simp)).smul_measure (by norm_num)).add_measure
    ((integrable_dirac (by simp)).smul_measure (by norm_num))
lemma half_integral (f : ℝ → ℝ) :
    (∫ x, f x ∂(halfAtoms : Measure ℝ)) = (f 0 + f 1) / 2 := by
  have h0 : Integrable f ((1 / 2 : ENNReal) • Measure.dirac (0 : ℝ)) :=
    (integrable_dirac (by simp)).smul_measure (by norm_num)
  have h1 : Integrable f ((1 / 2 : ENNReal) • Measure.dirac (1 : ℝ)) :=
    (integrable_dirac (by simp)).smul_measure (by norm_num)
  change (∫ x, f x ∂((1 / 2 : ENNReal) • Measure.dirac (0 : ℝ) +
    (1 / 2 : ENNReal) • Measure.dirac (1 : ℝ))) = _
  rw [integral_add_measure h0 h1, integral_smul_measure, integral_smul_measure]
  norm_num
  ring

def outside (R : ℝ) : Set ℝ := (Metric.ball (0 : ℝ) R)ᶜ
def fourthTail (R : ℝ) : ℝ → ℝ := (outside R).indicator (fun x => ‖x‖ ^ 4)
lemma atom_complement_zero : ((atom (0 : ℝ) : Measure ℝ) (outside 1)).toReal = 0 := by
  norm_num [atom, outside, mem_ball_zero_iff]
lemma atom_complement_boundary : ((atom (1 : ℝ) : Measure ℝ) (outside 1)).toReal = 1 := by
  norm_num [atom, outside, mem_ball_zero_iff]
lemma atom_complement_signed : ((atom (-2 : ℝ) : Measure ℝ) (outside 2)).toReal = 1 := by
  norm_num [atom, outside, mem_ball_zero_iff]
lemma half_complement : ((halfAtoms : Measure ℝ) (outside 1)).toReal = (1 / 2 : ℝ) := by
  norm_num [halfAtoms, outside, mem_ball_zero_iff, Measure.add_apply, Measure.smul_apply]
lemma atom_zero_eighth : (∫ x, ‖x‖ ^ 8 ∂(atom (0 : ℝ) : Measure ℝ)) = 0 := by
  rw [atom_integral]; norm_num
lemma atom_one_eighth : (∫ x, ‖x‖ ^ 8 ∂(atom (1 : ℝ) : Measure ℝ)) = 1 := by
  rw [atom_integral]; norm_num
lemma atom_signed_eighth : (∫ x, ‖x‖ ^ 8 ∂(atom (-2 : ℝ) : Measure ℝ)) = 256 := by
  rw [atom_integral]; norm_num
lemma half_eighth : (∫ x, ‖x‖ ^ 8 ∂(halfAtoms : Measure ℝ)) = (1 / 2 : ℝ) := by
  rw [half_integral]; norm_num
lemma atom_zero_fourth_tail : (∫ x, fourthTail 1 x ∂(atom (0 : ℝ) : Measure ℝ)) = 0 := by
  rw [atom_integral]; norm_num [fourthTail, outside, mem_ball_zero_iff]
lemma atom_one_fourth_tail : (∫ x, fourthTail 1 x ∂(atom (1 : ℝ) : Measure ℝ)) = 1 := by
  rw [atom_integral]; norm_num [fourthTail, outside, mem_ball_zero_iff]
lemma atom_signed_fourth_tail : (∫ x, fourthTail 2 x ∂(atom (-2 : ℝ) : Measure ℝ)) = 16 := by
  rw [atom_integral]; norm_num [fourthTail, outside, mem_ball_zero_iff]
lemma half_fourth_tail : (∫ x, fourthTail 1 x ∂(halfAtoms : Measure ℝ)) = (1 / 2 : ℝ) := by
  rw [half_integral]; norm_num [fourthTail, outside, mem_ball_zero_iff]
lemma signed_mean : (∫ x, x ∂(atom (-2 : ℝ) : Measure ℝ)) = -2 := by
  rw [atom_integral]

abbrev E0 := EuclideanSpace ℝ (Fin 0)
lemma rank_zero_eighth (ν : ProbabilityMeasure E0) :
    Integrable (fun x : E0 => ‖x‖ ^ 8) (ν : Measure E0) := by
  have hx : ∀ x : E0, x = 0 := fun x => Subsingleton.elim _ _
  simp [hx]
lemma rank_zero_ball (R : ℝ) (hR : 0 < R) : Metric.ball (0 : E0) R = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  have hx : x = 0 := Subsingleton.elim _ _
  simpa [hx, mem_ball_zero_iff] using hR
end CBTailModels

-- ===== reviewer module ConditionModels (CB5-CB4-Independent-20261008 (raw d81354de…)) =====
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set CBTailModels
open scoped ENNReal
open FunctionalInequalities.Probability
namespace CBConditionModels
lemma id_growth (x : ℝ) : |x| ≤ (1:ℝ) * (1 + ‖x‖ ^ 4) := by
  simp only [one_mul, Real.norm_eq_abs]
  nlinarith [sq_nonneg (|x|-1), sq_nonneg (|x|^2-1)]
lemma half_ball : (halfAtoms : Measure ℝ) (Metric.ball (0:ℝ) 1) = (1/2:ENNReal) := by
  norm_num [halfAtoms,mem_ball_zero_iff,Measure.add_apply,Measure.smul_apply]
lemma half_pos : 0 < (halfAtoms : Measure ℝ) (Metric.ball (0:ℝ) 1) := by
  rw [half_ball]
  norm_num
lemma half_condition : (conditionOnBall halfAtoms 1 half_pos : Measure ℝ) = Measure.dirac 0 := by
  classical
  rw [coe_conditionOnBall,ProbabilityTheory.cond,half_ball]
  norm_num [halfAtoms,Measure.restrict_add,Measure.restrict_smul,restrict_dirac,
    mem_ball_zero_iff,smul_smul,ENNReal.mul_inv_cancel,ENNReal.inv_mul_cancel]

def signedLaw : ProbabilityMeasure ℝ :=
  ⟨(2/3:ENNReal) • Measure.dirac 1 + (1/3:ENNReal) • Measure.dirac (-2), by
    constructor
    simp only [Measure.add_apply,Measure.smul_apply,measure_univ,smul_eq_mul,mul_one]
    rw [ENNReal.div_add_div_same]
    norm_num
    exact ENNReal.div_self (by norm_num) (by norm_num)⟩
lemma signed_integrable (f : ℝ → ℝ) : Integrable f (signedLaw : Measure ℝ) := by
  exact ((integrable_dirac (by simp)).smul_measure (ENNReal.div_ne_top (by norm_num) (by norm_num))).add_measure
    ((integrable_dirac (by simp)).smul_measure (ENNReal.div_ne_top (by norm_num) (by norm_num)))
lemma signed_integral (f : ℝ → ℝ) :
    (∫ x, f x ∂(signedLaw : Measure ℝ)) = (2/3:ℝ) * f 1 + (1/3:ℝ) * f (-2) := by
  have h1 : Integrable f ((2/3:ENNReal) • Measure.dirac (1:ℝ)) :=
    (integrable_dirac (by simp)).smul_measure (ENNReal.div_ne_top (by norm_num) (by norm_num))
  have h2 : Integrable f ((1/3:ENNReal) • Measure.dirac (-2:ℝ)) :=
    (integrable_dirac (by simp)).smul_measure (ENNReal.div_ne_top (by norm_num) (by norm_num))
  change (∫ x, f x ∂((2/3:ENNReal) • Measure.dirac 1 + (1/3:ENNReal) • Measure.dirac (-2))) = _
  rw [integral_add_measure h1 h2,integral_smul_measure,integral_smul_measure,integral_dirac,integral_dirac]
  norm_num
lemma signed_ball : (signedLaw : Measure ℝ) (Metric.ball (0:ℝ) (3/2)) = (2/3:ENNReal) := by
  norm_num [signedLaw,mem_ball_zero_iff,Measure.add_apply,Measure.smul_apply]
lemma signed_pos : 0 < (signedLaw : Measure ℝ) (Metric.ball (0:ℝ) (3/2)) := by
  rw [signed_ball]
  norm_num
lemma signed_condition : (conditionOnBall signedLaw (3/2) signed_pos : Measure ℝ) = Measure.dirac 1 := by
  classical
  have hmul : (2/3:ENNReal)⁻¹ * (2/3) = 1 :=
    ENNReal.inv_mul_cancel (by norm_num) (ENNReal.div_ne_top (by norm_num) (by norm_num))
  rw [coe_conditionOnBall,ProbabilityTheory.cond,signed_ball]
  norm_num [signedLaw,Measure.restrict_add,Measure.restrict_smul,restrict_dirac,
    mem_ball_zero_iff,smul_smul,ENNReal.mul_inv_cancel,ENNReal.inv_mul_cancel]
  rw [hmul,one_smul]

lemma signed_mean : (∫ x, x ∂(signedLaw : Measure ℝ)) = 0 := by
  rw [signed_integral]
  norm_num
lemma signed_condition_mean : (∫ x, x ∂(conditionOnBall signedLaw (3/2) signed_pos : Measure ℝ)) = 1 := by
  rw [signed_condition,integral_dirac]
lemma signed_condition_variance : variance id (conditionOnBall signedLaw (3/2) signed_pos : Measure ℝ) = 0 := by
  rw [signed_condition]
  exact variance_dirac _
lemma signed_id_error :
    |(∫ x, x ∂(conditionOnBall signedLaw (3/2) signed_pos : Measure ℝ)) - ∫ x, x ∂(signedLaw : Measure ℝ)| = 1 := by
  rw [signed_condition_mean,signed_mean]
  norm_num
lemma signed_eighth : (∫ x, ‖x‖^8 ∂(signedLaw : Measure ℝ)) = 86 := by
  rw [signed_integral]
  norm_num
lemma signed_fourth : (∫ x, ‖x‖^4 ∂(signedLaw : Measure ℝ)) = 6 := by
  rw [signed_integral]
  norm_num
lemma signed_abs_tail :
    (∫ x, (Metric.ball (0:ℝ) (3/2))ᶜ.indicator (fun y : ℝ => |y|) x ∂(signedLaw : Measure ℝ)) = 2/3 := by
  rw [signed_integral]
  norm_num [mem_ball_zero_iff]
lemma signed_threshold_false :
    ¬ (2 * (∫ x, ‖x‖^8 ∂(signedLaw : Measure ℝ)) ≤ (3/2:ℝ)^8) := by
  rw [signed_eighth]
  norm_num
end CBConditionModels

-- ===== reviewer module ConditionClients (CB5-CB4-Independent-20261008 (raw d81354de…)) =====
set_option autoImplicit false
noncomputable section
open MeasureTheory Set CBTailModels CBConditionModels
open FunctionalInequalities.Probability
open scoped ENNReal
namespace CBConditionClients

def errorClaim {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    (ν : ProbabilityMeasure E) (R C : ℝ) (hp : 0 < (ν : Measure E) (Metric.ball (0:E) R))
    (f : E → ℝ) : Prop :=
    Integrable f (ν : Measure E) ∧
    Integrable f (conditionOnBall ν R hp : Measure E) ∧
    Integrable (fun x : E => ‖x‖ ^ 4) (ν : Measure E) ∧
    |(∫ x, f x ∂(conditionOnBall ν R hp : Measure E)) - ∫ x, f x ∂(ν : Measure E)| ≤
      ((1 - ((ν : Measure E) (Metric.ball (0 : E) R)).toReal) * |∫ x, f x ∂(ν : Measure E)| +
        ∫ x, (Metric.ball (0 : E) R)ᶜ.indicator (fun y => |f y|) x ∂(ν : Measure E)) /
        ((ν : Measure E) (Metric.ball (0 : E) R)).toReal ∧
    |(∫ x, f x ∂(conditionOnBall ν R hp : Measure E)) - ∫ x, f x ∂(ν : Measure E)| ≤
      (C / ((ν : Measure E) (Metric.ball (0 : E) R)).toReal) *
        ((1 - ((ν : Measure E) (Metric.ball (0 : E) R)).toReal) * (2 + ∫ x, ‖x‖ ^ 4 ∂(ν : Measure E)) +
          (∫ x, ‖x‖ ^ 8 ∂(ν : Measure E)) / R ^ 4)

lemma half_from_threshold :
    (1/2:ℝ) ≤ ((halfAtoms : Measure ℝ) (Metric.ball (0:ℝ) 1)).toReal ∧
    0 < (halfAtoms : Measure ℝ) (Metric.ball (0:ℝ) 1) := by
  apply one_half_le_measure_ball_toReal_of_integral_norm_pow_eight halfAtoms (by norm_num) (half_integrable _)
  rw [half_eighth]
  norm_num
lemma half_threshold_sharp : 2 * (∫ x, ‖x‖^8 ∂(halfAtoms : Measure ℝ)) = (1:ℝ)^8 := by
  rw [half_eighth]
  norm_num
lemma half_actual_error_outputs : errorClaim halfAtoms 1 1 half_pos id := by
  exact abs_integral_conditionOnBall_sub_le halfAtoms (by norm_num) (by norm_num)
    (half_integrable _) half_pos measurable_id id_growth
lemma signed_actual_error_outputs : errorClaim signedLaw (3/2) 1 signed_pos id := by
  exact abs_integral_conditionOnBall_sub_le signedLaw (by norm_num) (by norm_num)
    (signed_integrable _) signed_pos measurable_id id_growth
lemma signed_both_numeric_bounds :
    |(∫ x, x ∂(conditionOnBall signedLaw (3/2) signed_pos : Measure ℝ)) - ∫ x, x ∂(signedLaw : Measure ℝ)| ≤ 1 ∧
    |(∫ x, x ∂(conditionOnBall signedLaw (3/2) signed_pos : Measure ℝ)) - ∫ x, x ∂(signedLaw : Measure ℝ)| ≤ 796/27 := by
  rcases signed_actual_error_outputs with ⟨hν,hcond,h4,hexact,hquant⟩
  constructor
  · simp only [id_eq] at hexact
    rw [signed_ball, CBConditionModels.signed_mean, signed_abs_tail] at hexact
    norm_num at hexact
    simpa only [CBConditionModels.signed_mean, sub_zero] using hexact
  · simp only [id_eq] at hquant
    rw [signed_ball, signed_fourth, signed_eighth] at hquant
    norm_num at hquant
    exact hquant
lemma half_mean : (∫ x, x ∂(halfAtoms : Measure ℝ)) = 1/2 := by
  rw [half_integral]
  norm_num
lemma half_error :
    |(∫ x, x ∂(conditionOnBall halfAtoms 1 half_pos : Measure ℝ)) - ∫ x, x ∂(halfAtoms : Measure ℝ)| = 1/2 := by
  rw [half_condition, integral_dirac, half_mean]
  norm_num
lemma half_both_numeric_bounds :
    |(∫ x, x ∂(conditionOnBall halfAtoms 1 half_pos : Measure ℝ)) - ∫ x, x ∂(halfAtoms : Measure ℝ)| ≤ 3/2 ∧
    |(∫ x, x ∂(conditionOnBall halfAtoms 1 half_pos : Measure ℝ)) - ∫ x, x ∂(halfAtoms : Measure ℝ)| ≤ 7/2 := by
  rcases half_actual_error_outputs with ⟨hν,hcond,h4,hexact,hquant⟩
  have htail :
      (∫ x, (Metric.ball (0:ℝ) 1)ᶜ.indicator (fun y : ℝ => |y|) x ∂(halfAtoms : Measure ℝ)) = 1/2 := by
    rw [half_integral]
    norm_num [mem_ball_zero_iff]
  have hfour : (∫ x, ‖x‖^4 ∂(halfAtoms : Measure ℝ)) = 1/2 := by
    rw [half_integral]
    norm_num
  constructor
  · norm_num [half_ball,half_mean,htail,id_eq] at hexact
    simpa only [half_mean] using hexact
  · simp only [id_eq] at hquant
    rw [half_ball,hfour,half_eighth] at hquant
    norm_num at hquant
    exact hquant

lemma atom_zero_mass : (atom (0:ℝ) : Measure ℝ) (Metric.ball (0:ℝ) 1) = 1 := by
  norm_num [atom,mem_ball_zero_iff]
lemma atom_zero_pos : 0 < (atom (0:ℝ) : Measure ℝ) (Metric.ball (0:ℝ) 1) := by
  rw [atom_zero_mass]
  norm_num
lemma atom_zero_half :
    (1/2:ℝ) ≤ ((atom (0:ℝ) : Measure ℝ) (Metric.ball (0:ℝ) 1)).toReal ∧
    0 < (atom (0:ℝ) : Measure ℝ) (Metric.ball (0:ℝ) 1) := by
  apply one_half_le_measure_ball_toReal_of_integral_norm_pow_eight (atom 0) (by norm_num) (atom_integrable 0 _)
  rw [atom_zero_eighth]
  norm_num
lemma atom_zero_error_outputs : errorClaim (atom (0:ℝ)) 1 0 atom_zero_pos (fun _ => 0) := by
  exact abs_integral_conditionOnBall_sub_le (atom 0) (by norm_num) (by norm_num)
    (atom_integrable 0 _) atom_zero_pos measurable_const (by intro x; simp)
lemma atom_zero_exact_error_zero :
    |(∫ _, (0:ℝ) ∂(conditionOnBall (atom (0:ℝ)) 1 atom_zero_pos : Measure ℝ)) - ∫ _, (0:ℝ) ∂(atom (0:ℝ) : Measure ℝ)| = 0 := by
  simp
end CBConditionClients

-- ===== reviewer module BoundaryClients (CB5-CB4-Independent-20261008 (raw d81354de…)) =====
set_option autoImplicit false
noncomputable section
open MeasureTheory Set CBTailModels
open FunctionalInequalities.Probability
namespace CBConditionBoundary
lemma zero_radius_threshold :
    2 * (∫ x, ‖x‖^8 ∂(atom (0:ℝ) : Measure ℝ)) ≤ (0:ℝ)^8 := by
  rw [atom_zero_eighth]
  norm_num
lemma zero_radius_half_mass_false :
    ¬ ((1/2:ℝ) ≤ ((atom (0:ℝ) : Measure ℝ) (Metric.ball (0:ℝ) 0)).toReal) := by
  norm_num [Metric.ball_eq_empty.mpr (le_refl (0:ℝ))]
lemma zero_radius_ctor_unavailable :
    ¬ (0 < (atom (0:ℝ) : Measure ℝ) (Metric.ball (0:ℝ) 0)) := by
  norm_num [Metric.ball_eq_empty.mpr (le_refl (0:ℝ))]
lemma boundary_null_ball : (atom (1:ℝ) : Measure ℝ) (Metric.ball (0:ℝ) 1) = 0 := by
  norm_num [atom,mem_ball_zero_iff]
lemma boundary_ctor_unavailable : ¬ (0 < (atom (1:ℝ) : Measure ℝ) (Metric.ball (0:ℝ) 1)) := by
  rw [boundary_null_ball]
  simp
lemma boundary_raw_cond_zero : ProbabilityTheory.cond (atom (1:ℝ) : Measure ℝ) (Metric.ball (0:ℝ) 1) = 0 :=
  ProbabilityTheory.cond_eq_zero_of_meas_eq_zero boundary_null_ball
lemma boundary_cond_not_probability :
    ¬ IsProbabilityMeasure (ProbabilityTheory.cond (atom (1:ℝ) : Measure ℝ) (Metric.ball (0:ℝ) 1)) := by
  rw [boundary_raw_cond_zero]
  intro hp
  have hu : (0 : Measure ℝ) Set.univ = 1 := measure_univ
  change (0:ENNReal) = 1 at hu
  exact zero_ne_one hu
end CBConditionBoundary

-- ===== reviewer module ZeroClients (CB5-CB4-Independent-20261008 (raw d81354de…)) =====
set_option autoImplicit false
noncomputable section
open MeasureTheory Set CBTailModels
open FunctionalInequalities.Probability
namespace CBConditionZero
lemma rank_positive (ν : ProbabilityMeasure E0) (R : ℝ) (hR : 0 < R) :
    0 < (ν : Measure E0) (Metric.ball (0:E0) R) := by
  rw [rank_zero_ball R hR]
  simp
lemma rank_half_mass (ν : ProbabilityMeasure E0) (R : ℝ) (hR : 0 < R) :
    (1/2:ℝ) ≤ ((ν : Measure E0) (Metric.ball (0:E0) R)).toReal ∧
      0 < (ν : Measure E0) (Metric.ball (0:E0) R) := by
  apply one_half_le_measure_ball_toReal_of_integral_norm_pow_eight ν hR (rank_zero_eighth ν)
  have hx : ∀ x:E0,x=0 := fun _ => Subsingleton.elim _ _
  simp [hx]
  positivity
lemma rank_condition (ν : ProbabilityMeasure E0) (R : ℝ) (hR : 0 < R) :
    (conditionOnBall ν R (rank_positive ν R hR) : Measure E0) = (ν : Measure E0) := by
  rw [coe_conditionOnBall,ProbabilityTheory.cond,rank_zero_ball R hR]
  simp
lemma rank_error_outputs (ν : ProbabilityMeasure E0) (R : ℝ) (hR : 0 < R) :
    Integrable (fun _ : E0 => (5:ℝ)) (ν : Measure E0) ∧
    Integrable (fun _ : E0 => (5:ℝ)) (conditionOnBall ν R (rank_positive ν R hR) : Measure E0) ∧
    Integrable (fun x:E0 => ‖x‖^4) (ν : Measure E0) := by
  have hg : ∀ x:E0, |(5:ℝ)| ≤ 5*(1+‖x‖^4) := by
    intro x
    have hx:x=0 := Subsingleton.elim _ _
    norm_num [hx]
  have h := abs_integral_conditionOnBall_sub_le ν hR (by norm_num : (0:ℝ)≤5) (rank_zero_eighth ν)
    (rank_positive ν R hR) measurable_const hg
  exact ⟨h.1,h.2.1,h.2.2.1⟩
lemma rank_actual_error_zero (ν : ProbabilityMeasure E0) (R : ℝ) (hR : 0 < R) :
    |(∫ _, (5:ℝ) ∂(conditionOnBall ν R (rank_positive ν R hR) : Measure E0)) - ∫ _, (5:ℝ) ∂(ν : Measure E0)| = 0 := by
  rw [rank_condition ν R hR]
  simp
end CBConditionZero

#print axioms CBTailModels.atom_integrable
#print axioms CBTailModels.atom_integral
#print axioms CBTailModels.half_integrable
#print axioms CBTailModels.half_integral
#print axioms CBTailModels.atom_complement_zero
#print axioms CBTailModels.atom_complement_boundary
#print axioms CBTailModels.atom_complement_signed
#print axioms CBTailModels.half_complement
#print axioms CBTailModels.atom_zero_eighth
#print axioms CBTailModels.atom_one_eighth
#print axioms CBTailModels.atom_signed_eighth
#print axioms CBTailModels.half_eighth
#print axioms CBTailModels.atom_zero_fourth_tail
#print axioms CBTailModels.atom_one_fourth_tail
#print axioms CBTailModels.atom_signed_fourth_tail
#print axioms CBTailModels.half_fourth_tail
#print axioms CBTailModels.signed_mean
#print axioms CBTailModels.rank_zero_eighth
#print axioms CBTailModels.rank_zero_ball
#print axioms CBConditionModels.id_growth
#print axioms CBConditionModels.half_ball
#print axioms CBConditionModels.half_pos
#print axioms CBConditionModels.half_condition
#print axioms CBConditionModels.signed_integrable
#print axioms CBConditionModels.signed_integral
#print axioms CBConditionModels.signed_ball
#print axioms CBConditionModels.signed_pos
#print axioms CBConditionModels.signed_condition
#print axioms CBConditionModels.signed_mean
#print axioms CBConditionModels.signed_condition_mean
#print axioms CBConditionModels.signed_condition_variance
#print axioms CBConditionModels.signed_id_error
#print axioms CBConditionModels.signed_eighth
#print axioms CBConditionModels.signed_fourth
#print axioms CBConditionModels.signed_abs_tail
#print axioms CBConditionModels.signed_threshold_false
#print axioms CBConditionClients.half_from_threshold
#print axioms CBConditionClients.half_threshold_sharp
#print axioms CBConditionClients.half_actual_error_outputs
#print axioms CBConditionClients.signed_actual_error_outputs
#print axioms CBConditionClients.signed_both_numeric_bounds
#print axioms CBConditionClients.half_mean
#print axioms CBConditionClients.half_error
#print axioms CBConditionClients.half_both_numeric_bounds
#print axioms CBConditionClients.atom_zero_mass
#print axioms CBConditionClients.atom_zero_pos
#print axioms CBConditionClients.atom_zero_half
#print axioms CBConditionClients.atom_zero_error_outputs
#print axioms CBConditionClients.atom_zero_exact_error_zero
#print axioms CBConditionBoundary.zero_radius_threshold
#print axioms CBConditionBoundary.zero_radius_half_mass_false
#print axioms CBConditionBoundary.zero_radius_ctor_unavailable
#print axioms CBConditionBoundary.boundary_null_ball
#print axioms CBConditionBoundary.boundary_ctor_unavailable
#print axioms CBConditionBoundary.boundary_raw_cond_zero
#print axioms CBConditionBoundary.boundary_cond_not_probability
#print axioms CBConditionZero.rank_positive
#print axioms CBConditionZero.rank_half_mass
#print axioms CBConditionZero.rank_condition
#print axioms CBConditionZero.rank_error_outputs
#print axioms CBConditionZero.rank_actual_error_zero
#print axioms FunctionalInequalities.Probability.one_half_le_measure_ball_toReal_of_integral_norm_pow_eight
#print axioms FunctionalInequalities.Probability.conditionOnBall
#print axioms FunctionalInequalities.Probability.coe_conditionOnBall
#print axioms FunctionalInequalities.Probability.abs_integral_conditionOnBall_sub_le
