module

public import FunctionalInequalities.Probability.Moments

/-!
# Audit: third-moment contraction (support of the BKL (67) log-determinant non-explosion route)

Clients of `Probability/Moments.lean` section `ThirdMomentContraction`
(`Probability.sum_sq_integral_mul_mul_le_integral_norm_pow_six`). Consumers: every Dirac atom in
every dimension, the noncentred atom `(2, −1)` where the full mixed tensor equals the sixth moment
`125` (sharp), the normalised two-atom law at `1, 3` with `196 ≤ 365` and gap `169`, and rank zero.
Deterministic support only: no covariance dynamics, Itô, strong solution or non-explosion theorem.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace IndependentThirdMomentContraction
abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

def atom {n : ℕ} (v : E n) : ProbabilityMeasure (E n) :=
  ⟨Measure.dirac v, inferInstance⟩

lemma atom_integrable {n : ℕ} (v : E n) (f : E n → ℝ) :
    Integrable f (atom v : Measure (E n)) := by
  exact integrable_dirac (by simp)

lemma atom_integral {n : ℕ} (v : E n) (f : E n → ℝ) :
    (∫ x, f x ∂(atom v : Measure (E n))) = f v := by
  exact integral_dirac f v

lemma all_dimension_atom {n : ℕ} (v : E n) :
    (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
      (∫ x, x i * x j * x k ∂(atom v : Measure (E n))) ^ 2) ≤
      ∫ x, ‖x‖ ^ 6 ∂(atom v : Measure (E n)) := by
  exact FunctionalInequalities.Probability.sum_sq_integral_mul_mul_le_integral_norm_pow_six
    (atom v) (atom_integrable v _)

def half : ℝ≥0∞ := 1 / 2

def twoLaw {n : ℕ} (v w : E n) : ProbabilityMeasure (E n) :=
  ⟨half • Measure.dirac v + half • Measure.dirac w, by
    constructor
    norm_num [half, Measure.add_apply, Measure.smul_apply, ENNReal.inv_two_add_inv_two]⟩

lemma two_integrable {n : ℕ} (v w : E n) (f : E n → ℝ) :
    Integrable f (twoLaw v w : Measure (E n)) := by
  apply (integrable_add_measure).2
  constructor
  · exact (integrable_smul_measure (by norm_num [half]) (by norm_num [half])).2
      (integrable_dirac (by simp))
  · exact (integrable_smul_measure (by norm_num [half]) (by norm_num [half])).2
      (integrable_dirac (by simp))

lemma two_integral {n : ℕ} (v w : E n) (f : E n → ℝ) :
    (∫ x, f x ∂(twoLaw v w : Measure (E n))) = (f v + f w) / 2 := by
  change (∫ x, f x ∂(half • Measure.dirac v + half • Measure.dirac w)) = _
  rw [integral_add_measure
    ((integrable_smul_measure (by norm_num [half]) (by norm_num [half])).2
      (integrable_dirac (by simp)))
    ((integrable_smul_measure (by norm_num [half]) (by norm_num [half])).2
      (integrable_dirac (by simp)))]
  simp [integral_smul_measure, integral_dirac, half]
  ring

def v2 : E 2 := WithLp.toLp 2 ![(2 : ℝ), (-1 : ℝ)]
def a1 : E 1 := WithLp.toLp 2 (fun _ => (1 : ℝ))
def b1 : E 1 := WithLp.toLp 2 (fun _ => (3 : ℝ))

lemma dirac_noncentered :
    (∫ x, x 0 ∂(atom v2 : Measure (E 2))) = 2 := by
  rw [atom_integral]; rfl

lemma dirac_mixed_signed :
    (∫ x, x 0 * x 0 * x 1 ∂(atom v2 : Measure (E 2))) = -4 := by
  rw [atom_integral]; norm_num [v2]

lemma dirac_all_tensor :
    (∑ i : Fin 2, ∑ j : Fin 2, ∑ k : Fin 2,
      (∫ x, x i * x j * x k ∂(atom v2 : Measure (E 2))) ^ 2) = 125 := by
  simp only [atom_integral, Fin.sum_univ_two]
  norm_num [v2]

lemma dirac_sixth :
    (∫ x, ‖x‖ ^ 6 ∂(atom v2 : Measure (E 2))) = 125 := by
  rw [atom_integral]
  rw [show ‖v2‖ ^ 6 = (‖v2‖ ^ 2) ^ 3 by ring, EuclideanSpace.real_norm_sq_eq]
  norm_num [v2, Fin.sum_univ_two]

lemma dirac_sharp :
    (∑ i : Fin 2, ∑ j : Fin 2, ∑ k : Fin 2,
      (∫ x, x i * x j * x k ∂(atom v2 : Measure (E 2))) ^ 2) =
      ∫ x, ‖x‖ ^ 6 ∂(atom v2 : Measure (E 2)) := by
  rw [dirac_all_tensor, dirac_sixth]

lemma two_noncentered :
    (∫ x, x 0 ∂(twoLaw a1 b1 : Measure (E 1))) = 2 := by
  rw [two_integral]; norm_num [a1, b1]

lemma two_third :
    (∫ x, x 0 * x 0 * x 0 ∂(twoLaw a1 b1 : Measure (E 1))) = 14 := by
  rw [two_integral]; norm_num [a1, b1]

lemma two_all_tensor :
    (∑ i : Fin 1, ∑ j : Fin 1, ∑ k : Fin 1,
      (∫ x, x i * x j * x k ∂(twoLaw a1 b1 : Measure (E 1))) ^ 2) = 196 := by
  simp only [Fin.sum_univ_one, two_third]; norm_num

lemma two_sixth :
    (∫ x, ‖x‖ ^ 6 ∂(twoLaw a1 b1 : Measure (E 1))) = 365 := by
  rw [two_integral]
  rw [show ‖a1‖ ^ 6 = (‖a1‖ ^ 2) ^ 3 by ring, EuclideanSpace.real_norm_sq_eq,
      show ‖b1‖ ^ 6 = (‖b1‖ ^ 2) ^ 3 by ring, EuclideanSpace.real_norm_sq_eq]
  norm_num [a1, b1, Fin.sum_univ_one]

lemma two_actual_contraction :
    (∑ i : Fin 1, ∑ j : Fin 1, ∑ k : Fin 1,
      (∫ x, x i * x j * x k ∂(twoLaw a1 b1 : Measure (E 1))) ^ 2) ≤
      ∫ x, ‖x‖ ^ 6 ∂(twoLaw a1 b1 : Measure (E 1)) := by
  exact FunctionalInequalities.Probability.sum_sq_integral_mul_mul_le_integral_norm_pow_six
    (twoLaw a1 b1) (two_integrable _ _ _)

lemma two_strict_gap :
    (∫ x, ‖x‖ ^ 6 ∂(twoLaw a1 b1 : Measure (E 1))) -
    (∑ i : Fin 1, ∑ j : Fin 1, ∑ k : Fin 1,
      (∫ x, x i * x j * x k ∂(twoLaw a1 b1 : Measure (E 1))) ^ 2) = 169 := by
  rw [two_sixth, two_all_tensor]; norm_num

lemma rank_zero (ν : ProbabilityMeasure (E 0)) :
    (∑ i : Fin 0, ∑ j : Fin 0, ∑ k : Fin 0,
      (∫ x, x i * x j * x k ∂(ν : Measure (E 0))) ^ 2) =
      ∫ x, ‖x‖ ^ 6 ∂(ν : Measure (E 0)) := by
  have hx : ∀ x : E 0, x = 0 := fun x => Subsingleton.elim _ _
  simp [hx]

lemma rank_zero_actual (ν : ProbabilityMeasure (E 0)) :
    (∑ i : Fin 0, ∑ j : Fin 0, ∑ k : Fin 0,
      (∫ x, x i * x j * x k ∂(ν : Measure (E 0))) ^ 2) ≤
      ∫ x, ‖x‖ ^ 6 ∂(ν : Measure (E 0)) := by
  have h6 : Integrable (fun x : E 0 => ‖x‖ ^ 6) (ν : Measure (E 0)) := by
    have hx : ∀ x : E 0, x = 0 := fun x => Subsingleton.elim _ _
    simp [hx]
  exact FunctionalInequalities.Probability.sum_sq_integral_mul_mul_le_integral_norm_pow_six ν h6

#print axioms all_dimension_atom
#print axioms dirac_sharp
#print axioms two_actual_contraction
#print axioms two_strict_gap
#print axioms rank_zero_actual
#print axioms FunctionalInequalities.Probability.sum_sq_integral_mul_mul_le_integral_norm_pow_six

end IndependentThirdMomentContraction
