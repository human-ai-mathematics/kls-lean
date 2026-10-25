import FunctionalInequalities.Probability.Moments
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-!
# Audit: eighth-moment tail bounds (ball-conditioning stage of the moment-potential producer)

Clients compiled against `Probability/Moments.lean` section `MomentTails`
(`Probability.measure_ball_compl_toReal_le_integral_norm_pow_eight_div`, Luna unit CB2 round 5;
`Probability.integrable_norm_pow_four_and_tail_le_of_integrable_pow_eight`, Luna unit CB3 round 2; both under the
checked-context driver rev3, independently accepted 2026-10-08, receipt `CB2-CB3-Independent-20261008/VERIFICATION.json`
1a08d848…). The consumers are the independent Codex reviewer's: the exact original generic contracts, real atoms at `0`
(zero tails), at the boundary `1` of the open unit ball (both bounds sharp: complement mass `1 = M₈/R⁸`, fourth tail
`1 = M₈/R⁴`), the signed atom `−2` with `R = 2` (sharp), the half law `(δ₀ + δ₁)/2` (sharp, mass `1/2`), rank zero with all
values `0` and both integrability outputs consumed, and the radius-zero guard (the bound is false at `R = 0`, so `R > 0`
is substantive). No conditional law, optimizer or potential is involved.
-/

noncomputable section
open MeasureTheory
open FunctionalInequalities.Probability

namespace IndependentMomentTailModels
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
end IndependentMomentTailModels

namespace IndependentMomentTailClients
open IndependentMomentTailModels

section MeasurableSpace

variable {E : Type*}
  [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]

/-- The original universal context has no LC/IP/FD/centering/isotropy/ball-mass premise. -/
theorem exact_cb2
    (ν : ProbabilityMeasure E) {R : ℝ} (hR : 0 < R)
    (h8 : Integrable (fun x : E => ‖x‖ ^ 8) (ν : Measure E)) :
    ((ν : Measure E) (Metric.ball (0 : E) R)ᶜ).toReal ≤
      (∫ x, ‖x‖ ^ 8 ∂(ν : Measure E)) / R ^ 8 := by
  exact measure_ball_compl_toReal_le_integral_norm_pow_eight_div ν hR h8

theorem exact_cb3
    (ν : ProbabilityMeasure E) {R : ℝ} (hR : 0 < R)
    (h8 : Integrable (fun x : E => ‖x‖ ^ 8) (ν : Measure E)) :
    Integrable (fun x : E => ‖x‖ ^ 4) (ν : Measure E) ∧
    Integrable ((Metric.ball (0 : E) R)ᶜ.indicator (fun x : E => ‖x‖ ^ 4)) (ν : Measure E) ∧
    (∫ x, (Metric.ball (0 : E) R)ᶜ.indicator (fun y : E => ‖y‖ ^ 4) x ∂(ν : Measure E)) ≤
      (∫ x, ‖x‖ ^ 8 ∂(ν : Measure E)) / R ^ 4 := by
  exact integrable_norm_pow_four_and_tail_le_of_integrable_pow_eight ν hR h8

end MeasurableSpace

/-- Each result consumes actual derived eighth integrability. -/
theorem real_atoms (a : ℝ) (R : ℝ) (hR : 0 < R) :
    ((atom a : Measure ℝ) (Metric.ball (0 : ℝ) R)ᶜ).toReal ≤
      (∫ x, ‖x‖ ^ 8 ∂(atom a : Measure ℝ)) / R ^ 8 ∧
    Integrable (fun x : ℝ => ‖x‖ ^ 4) (atom a : Measure ℝ) ∧
    Integrable ((Metric.ball (0 : ℝ) R)ᶜ.indicator (fun x : ℝ => ‖x‖ ^ 4)) (atom a : Measure ℝ) ∧
    (∫ x, (Metric.ball (0 : ℝ) R)ᶜ.indicator (fun y : ℝ => ‖y‖ ^ 4) x ∂(atom a : Measure ℝ)) ≤
      (∫ x, ‖x‖ ^ 8 ∂(atom a : Measure ℝ)) / R ^ 4 := by
  exact ⟨exact_cb2 (atom a) hR (atom_integrable a _),
    exact_cb3 (atom a) hR (atom_integrable a _)⟩

theorem half_law :
    ((halfAtoms : Measure ℝ) (Metric.ball (0 : ℝ) 1)ᶜ).toReal ≤
      (∫ x, ‖x‖ ^ 8 ∂(halfAtoms : Measure ℝ)) / (1 : ℝ) ^ 8 ∧
    Integrable (fun x : ℝ => ‖x‖ ^ 4) (halfAtoms : Measure ℝ) ∧
    Integrable ((Metric.ball (0 : ℝ) 1)ᶜ.indicator (fun x : ℝ => ‖x‖ ^ 4)) (halfAtoms : Measure ℝ) ∧
    (∫ x, (Metric.ball (0 : ℝ) 1)ᶜ.indicator (fun y : ℝ => ‖y‖ ^ 4) x ∂(halfAtoms : Measure ℝ)) ≤
      (∫ x, ‖x‖ ^ 8 ∂(halfAtoms : Measure ℝ)) / (1 : ℝ) ^ 4 := by
  exact ⟨exact_cb2 halfAtoms (by norm_num) (half_integrable _),
    exact_cb3 halfAtoms (by norm_num) (half_integrable _)⟩

theorem zero_model :
    ((atom (0 : ℝ) : Measure ℝ) (Metric.ball (0 : ℝ) 1)ᶜ).toReal ≤
      (∫ x, ‖x‖ ^ 8 ∂(atom (0 : ℝ) : Measure ℝ)) / (1 : ℝ) ^ 8 ∧
    Integrable (fun x : ℝ => ‖x‖ ^ 4) (atom (0 : ℝ) : Measure ℝ) ∧
    Integrable ((Metric.ball (0 : ℝ) 1)ᶜ.indicator (fun x : ℝ => ‖x‖ ^ 4)) (atom (0 : ℝ) : Measure ℝ) ∧
    (∫ x, (Metric.ball (0 : ℝ) 1)ᶜ.indicator (fun y : ℝ => ‖y‖ ^ 4) x ∂(atom (0 : ℝ) : Measure ℝ)) ≤
      (∫ x, ‖x‖ ^ 8 ∂(atom (0 : ℝ) : Measure ℝ)) / (1 : ℝ) ^ 4 := by
  exact real_atoms 0 1 (by norm_num)
theorem boundary_model :
    ((atom (1 : ℝ) : Measure ℝ) (Metric.ball (0 : ℝ) 1)ᶜ).toReal ≤
      (∫ x, ‖x‖ ^ 8 ∂(atom (1 : ℝ) : Measure ℝ)) / (1 : ℝ) ^ 8 ∧
    Integrable (fun x : ℝ => ‖x‖ ^ 4) (atom (1 : ℝ) : Measure ℝ) ∧
    Integrable ((Metric.ball (0 : ℝ) 1)ᶜ.indicator (fun x : ℝ => ‖x‖ ^ 4)) (atom (1 : ℝ) : Measure ℝ) ∧
    (∫ x, (Metric.ball (0 : ℝ) 1)ᶜ.indicator (fun y : ℝ => ‖y‖ ^ 4) x ∂(atom (1 : ℝ) : Measure ℝ)) ≤
      (∫ x, ‖x‖ ^ 8 ∂(atom (1 : ℝ) : Measure ℝ)) / (1 : ℝ) ^ 4 := by
  exact real_atoms 1 1 (by norm_num)
theorem signed_model :
    ((atom ((-2) : ℝ) : Measure ℝ) (Metric.ball (0 : ℝ) 2)ᶜ).toReal ≤
      (∫ x, ‖x‖ ^ 8 ∂(atom ((-2) : ℝ) : Measure ℝ)) / (2 : ℝ) ^ 8 ∧
    Integrable (fun x : ℝ => ‖x‖ ^ 4) (atom ((-2) : ℝ) : Measure ℝ) ∧
    Integrable ((Metric.ball (0 : ℝ) 2)ᶜ.indicator (fun x : ℝ => ‖x‖ ^ 4)) (atom ((-2) : ℝ) : Measure ℝ) ∧
    (∫ x, (Metric.ball (0 : ℝ) 2)ᶜ.indicator (fun y : ℝ => ‖y‖ ^ 4) x ∂(atom ((-2) : ℝ) : Measure ℝ)) ≤
      (∫ x, ‖x‖ ^ 8 ∂(atom ((-2) : ℝ) : Measure ℝ)) / (2 : ℝ) ^ 4 := by
  exact real_atoms (-2) 2 (by norm_num)

/-- Sharp values are derived from the actual fixture laws, not supplied as theorem premises. -/
theorem boundary_cb2_sharp :
    ((atom (1 : ℝ) : Measure ℝ) (outside 1)).toReal =
      (∫ x, ‖x‖ ^ 8 ∂(atom (1 : ℝ) : Measure ℝ)) / (1 : ℝ) ^ 8 := by
  rw [atom_complement_boundary, atom_one_eighth]
  norm_num
theorem boundary_cb3_sharp :
    (∫ x, fourthTail 1 x ∂(atom (1 : ℝ) : Measure ℝ)) =
      (∫ x, ‖x‖ ^ 8 ∂(atom (1 : ℝ) : Measure ℝ)) / (1 : ℝ) ^ 4 := by
  rw [atom_one_fourth_tail, atom_one_eighth]
  norm_num
theorem half_cb2_sharp :
    ((halfAtoms : Measure ℝ) (outside 1)).toReal =
      (∫ x, ‖x‖ ^ 8 ∂(halfAtoms : Measure ℝ)) / (1 : ℝ) ^ 8 := by
  rw [half_complement, half_eighth]
  norm_num
theorem half_cb3_sharp :
    (∫ x, fourthTail 1 x ∂(halfAtoms : Measure ℝ)) =
      (∫ x, ‖x‖ ^ 8 ∂(halfAtoms : Measure ℝ)) / (1 : ℝ) ^ 4 := by
  rw [half_fourth_tail, half_eighth]
  norm_num
theorem signed_cb2_sharp :
    ((atom (-2 : ℝ) : Measure ℝ) (outside 2)).toReal =
      (∫ x, ‖x‖ ^ 8 ∂(atom (-2 : ℝ) : Measure ℝ)) / (2 : ℝ) ^ 8 := by
  rw [atom_complement_signed, atom_signed_eighth]
  norm_num
theorem signed_cb3_sharp :
    (∫ x, fourthTail 2 x ∂(atom (-2 : ℝ) : Measure ℝ)) =
      (∫ x, ‖x‖ ^ 8 ∂(atom (-2 : ℝ) : Measure ℝ)) / (2 : ℝ) ^ 4 := by
  rw [atom_signed_fourth_tail, atom_signed_eighth]
  norm_num

theorem rank_zero (ν : ProbabilityMeasure E0) (R : ℝ) (hR : 0 < R) :
    ((ν : Measure E0) (Metric.ball (0 : E0) R)ᶜ).toReal ≤
      (∫ x, ‖x‖ ^ 8 ∂(ν : Measure E0)) / R ^ 8 ∧
    Integrable (fun x : E0 => ‖x‖ ^ 4) (ν : Measure E0) ∧
    Integrable ((Metric.ball (0 : E0) R)ᶜ.indicator (fun x : E0 => ‖x‖ ^ 4)) (ν : Measure E0) ∧
    (∫ x, (Metric.ball (0 : E0) R)ᶜ.indicator (fun y : E0 => ‖y‖ ^ 4) x ∂(ν : Measure E0)) ≤
      (∫ x, ‖x‖ ^ 8 ∂(ν : Measure E0)) / R ^ 4 := by
  exact ⟨exact_cb2 ν hR (rank_zero_eighth ν), exact_cb3 ν hR (rank_zero_eighth ν)⟩
end IndependentMomentTailClients

namespace IndependentMomentTailEdge
open IndependentMomentTailModels

theorem rank_zero_actual_values (ν : ProbabilityMeasure E0) (R : ℝ) (hR : 0 < R) :
    ((ν : Measure E0) (Metric.ball (0 : E0) R)ᶜ).toReal = 0 ∧
    (∫ x, ‖x‖ ^ 8 ∂(ν : Measure E0)) = 0 ∧
    (∫ x, (Metric.ball (0 : E0) R)ᶜ.indicator (fun y : E0 => ‖y‖ ^ 4) x ∂(ν : Measure E0)) = 0 := by
  have hx : ∀ x : E0, x = 0 := fun x => Subsingleton.elim _ _
  rw [rank_zero_ball R hR]
  simp [hx]

/-- Both fourth-integrability conclusions are consumed from the actual raw theorem. -/
theorem rank_zero_integrability_outputs (ν : ProbabilityMeasure E0) (R : ℝ) (hR : 0 < R) :
    Integrable (fun x : E0 => ‖x‖ ^ 4) (ν : Measure E0) ∧
    Integrable ((Metric.ball (0 : E0) R)ᶜ.indicator (fun x : E0 => ‖x‖ ^ 4)) (ν : Measure E0) := by
  have h := IndependentMomentTailClients.rank_zero ν R hR
  exact ⟨h.2.1, h.2.2.1⟩

/-- Positive-radius exclusion is substantive even in rank zero. -/
theorem zero_radius_guard :
    ¬ (((atom (0 : ℝ) : Measure ℝ) (Metric.ball (0 : ℝ) 0)ᶜ).toReal ≤
      (∫ x, ‖x‖ ^ 8 ∂(atom (0 : ℝ) : Measure ℝ)) / (0 : ℝ) ^ 8) := by
  norm_num [atom, Metric.ball_eq_empty.mpr (le_refl (0 : ℝ)), atom_zero_eighth]
end IndependentMomentTailEdge

#print axioms IndependentMomentTailClients.exact_cb2
#print axioms IndependentMomentTailClients.exact_cb3
#print axioms IndependentMomentTailClients.real_atoms
#print axioms IndependentMomentTailClients.half_law
#print axioms IndependentMomentTailClients.boundary_cb2_sharp
#print axioms IndependentMomentTailClients.half_cb3_sharp
#print axioms IndependentMomentTailClients.signed_cb2_sharp
#print axioms IndependentMomentTailClients.rank_zero
#print axioms IndependentMomentTailEdge.rank_zero_actual_values
#print axioms IndependentMomentTailEdge.zero_radius_guard
#print axioms FunctionalInequalities.Probability.measure_ball_compl_toReal_le_integral_norm_pow_eight_div
#print axioms FunctionalInequalities.Probability.integrable_norm_pow_four_and_tail_le_of_integrable_pow_eight
