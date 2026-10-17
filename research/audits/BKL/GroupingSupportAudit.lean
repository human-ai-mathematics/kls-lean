import FunctionalInequalities.Analysis.BakryEmery.Cumulant.Local
import FunctionalInequalities.Analysis.IteratedDerivative.Bilinear
import Mathlib.Analysis.InnerProductSpace.PiL2
import FunctionalInequalities.KLS.BKL.CumulantEnergy.Basic
/-! Independent audit clients for the cumulant permutation symmetry (LocalCumulant section CumulantSymmetry) and the Boolean-mask complement pairing (IteratedDerivative/Bilinear). Merged verbatim from the reviewer receipt `D74-Grouping-Supports-Independent-20261009 (receipt 0175abed…)` (modules SkewLaw, PlaneLaw, PermutationClients, PairClients), each in its own named section, re-pointed from the raw `Candidate*` modules to the production owners; contracts/axiom-enumeration tooling stays in the receipt. -/

-- ===== reviewer module SkewLaw (D74-Grouping-Supports-Independent-20261009 (receipt 0175abed…)) =====
section SkewLaw
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace ENNReal
open FunctionalInequalities.Analysis.BakryEmery
namespace D74rSkewLaw
/-- The two-point law `(1/5) δ₂ + (4/5) δ_{-1/2}`: centered, isotropic and skewed. -/
def twoPt : Measure ℝ := (1 / 5 : ℝ≥0∞) • Measure.dirac 2 + (4 / 5 : ℝ≥0∞) • Measure.dirac (-1 / 2)

theorem integrable_twoPt (f : ℝ → ℝ) : Integrable f twoPt := by
  refine Integrable.add_measure ?_ ?_
  · exact (integrable_dirac (by simp)).smul_measure (ENNReal.div_ne_top (by norm_num) (by norm_num))
  · exact (integrable_dirac (by simp)).smul_measure (ENNReal.div_ne_top (by norm_num) (by norm_num))

theorem integral_twoPt (f : ℝ → ℝ) : ∫ x, f x ∂twoPt = (1 / 5) * f 2 + (4 / 5) * f (-1 / 2) := by
  rw [twoPt, integral_add_measure, integral_smul_measure, integral_smul_measure, integral_dirac,
    integral_dirac]
  · simp [smul_eq_mul]
  · exact (integrable_dirac (by simp)).smul_measure (ENNReal.div_ne_top (by norm_num) (by norm_num))
  · exact (integrable_dirac (by simp)).smul_measure (ENNReal.div_ne_top (by norm_num) (by norm_num))

theorem isProbabilityMeasure_twoPt : IsProbabilityMeasure twoPt := by
  constructor
  rw [twoPt]
  simp only [Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [ENNReal.div_add_div_same]
  norm_num
  exact ENNReal.div_self (by norm_num) (by norm_num)

theorem centered_twoPt (v : ℝ) : ∫ x, ⟪v, x⟫ ∂twoPt = 0 := by
  rw [integral_twoPt]
  simp only [RCLike.inner_apply, conj_trivial]
  ring

theorem isotropic_twoPt (v w : ℝ) : ∫ x, ⟪v, x⟫ * ⟪w, x⟫ ∂twoPt = ⟪v, w⟫ := by
  rw [integral_twoPt]
  simp only [RCLike.inner_apply, conj_trivial]
  ring

theorem integrable_exp_mul_norm_twoPt (r : ℝ) :
    Integrable (fun x => Real.exp (r * ‖x‖)) twoPt := integrable_twoPt _

theorem cumulant_three_twoPt : cumulant twoPt 3 ![1, 1, 1] = 3 / 2 := by
  have := isProbabilityMeasure_twoPt
  rw [cumulant_three_eq_integral twoPt integrable_exp_mul_norm_twoPt centered_twoPt, integral_twoPt]
  simp only [RCLike.inner_apply, conj_trivial]
  norm_num

end D74rSkewLaw

end
end SkewLaw

-- ===== reviewer module PlaneLaw (D74-Grouping-Supports-Independent-20261009 (receipt 0175abed…)) =====
section PlaneLaw
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open FunctionalInequalities FunctionalInequalities.Analysis FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace ContDiff
namespace D74RawPlane
abbrev E := EuclideanSpace ℝ (Fin 2)
def point (a b : ℝ) : E := WithLp.toLp 2 ![a, b]
def μ : ProbabilityMeasure E :=
  ⟨ENNReal.ofReal (1 / 4) • Measure.dirac (point 1 1) +
    ENNReal.ofReal (1 / 4) • Measure.dirac (point 1 (-1)) +
    ENNReal.ofReal (1 / 4) • Measure.dirac (point (-1) 1) +
    ENNReal.ofReal (1 / 4) • Measure.dirac (point (-1) (-1)), by
      constructor
      simp only [Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
      rw [← ENNReal.ofReal_add (by norm_num) (by norm_num),
        ← ENNReal.ofReal_add (by norm_num) (by norm_num),
        ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
      norm_num⟩

theorem integral_μ {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (g : E → F) :
    (∫ x, g x ∂(μ : Measure E)) =
      (1 / 4 : ℝ) • g (point 1 1) + (1 / 4 : ℝ) • g (point 1 (-1)) +
      (1 / 4 : ℝ) • g (point (-1) 1) + (1 / 4 : ℝ) • g (point (-1) (-1)) := by
  have hi (x : E) : Integrable g (ENNReal.ofReal (1 / 4) • Measure.dirac x) :=
    (integrable_dirac (by simp)).smul_measure (by norm_num)
  change (∫ x, g x ∂(ENNReal.ofReal (1 / 4) • Measure.dirac (point 1 1) +
    ENNReal.ofReal (1 / 4) • Measure.dirac (point 1 (-1)) +
    ENNReal.ofReal (1 / 4) • Measure.dirac (point (-1) 1) +
    ENNReal.ofReal (1 / 4) • Measure.dirac (point (-1) (-1)))) = _
  rw [integral_add_measure ((hi _).add_measure (hi _) |>.add_measure (hi _)) (hi _),
    integral_add_measure ((hi _).add_measure (hi _)) (hi _),
    integral_add_measure (hi _) (hi _)]
  simp only [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 4)]

def K : Set E := {point 1 1, point 1 (-1), point (-1) 1, point (-1) (-1)}

theorem support_subset : (μ : Measure E).support ⊆ K := by
  apply Measure.support_subset_of_isClosed
    (isClosed_singleton.union (isClosed_singleton.union (isClosed_singleton.union isClosed_singleton)))
  rw [mem_ae_iff]
  change ((ENNReal.ofReal (1 / 4) • Measure.dirac (point 1 1) +
    ENNReal.ofReal (1 / 4) • Measure.dirac (point 1 (-1)) +
    ENNReal.ofReal (1 / 4) • Measure.dirac (point (-1) 1) +
    ENNReal.ofReal (1 / 4) • Measure.dirac (point (-1) (-1))) Kᶜ) = 0
  simp [K]

theorem compact_μ : IsCompact (μ : Measure E).support := by
  have hK : K.Finite := by simp [K]
  exact hK.isCompact.of_isClosed_subset (μ : Measure E).isClosed_support support_subset

theorem inner_point (u : E) (a b : ℝ) : ⟪u, point a b⟫ = u 0 * a + u 1 * b := by
  simp [point, PiLp.inner_apply, Fin.sum_univ_two, mul_comm]

end D74RawPlane

end
end PlaneLaw

-- ===== reviewer module PermutationClients (D74-Grouping-Supports-Independent-20261009 (receipt 0175abed…)) =====
section PermutationClients
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace
namespace D74GroupingPermutation
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem generic_all_orders (μ : ProbabilityMeasure E) (hc : IsCompact (μ : Measure E).support)
    {m : ℕ} (σ : Equiv.Perm (Fin m)) (h : Fin m → E) :
    cumulant (μ : Measure E) m (h ∘ σ) = cumulant (μ : Measure E) m h :=
  cumulant_comp_perm_of_compact (E := E) (μ := μ) (hc := hc) (m := m) (σ := σ) (h := h)

theorem generic_m0 (μ : ProbabilityMeasure E) (hc : IsCompact (μ : Measure E).support)
    (σ : Equiv.Perm (Fin 0)) (h : Fin 0 → E) :
    cumulant (μ : Measure E) 0 (h ∘ σ) = cumulant (μ : Measure E) 0 h :=
  cumulant_comp_perm_of_compact μ hc σ h

namespace Skew
open D74rSkewLaw
def law : ProbabilityMeasure ℝ := ⟨twoPt,isProbabilityMeasure_twoPt⟩
lemma compact_law : IsCompact (law : Measure ℝ).support := by
  have hs : (law : Measure ℝ).support ⊆ ({(2:ℝ),-1/2}:Set ℝ) := by
    apply Measure.support_subset_of_isClosed (isClosed_singleton.union isClosed_singleton)
    rw [mem_ae_iff]
    simp [law,twoPt]
  exact (Set.toFinite ({(2:ℝ),-1/2}:Set ℝ)).isCompact.of_isClosed_subset
    (law : Measure ℝ).isClosed_support hs

theorem actual_nonzero_third : cumulant (law : Measure ℝ) 3 ![1,1,1] = 3/2 :=
  cumulant_three_twoPt

theorem signed_third : cumulant (law : Measure ℝ) 3 ![-2,3,1] = -9 := by
  have : IsProbabilityMeasure twoPt := isProbabilityMeasure_twoPt
  change cumulant twoPt 3 ![-2,3,1] = -9
  rw [cumulant_three_eq_integral twoPt integrable_exp_mul_norm_twoPt centered_twoPt,integral_twoPt]
  norm_num [Real.inner_apply]

theorem actual_signed_swap : cumulant (law : Measure ℝ) 3 ![3,-2,1] = -9 := by
  have hp := cumulant_comp_perm_of_compact law compact_law (Equiv.swap (0:Fin 3) 1)
    ![(-2:ℝ),3,1]
  have he : (![-2,3,1] : Fin 3 → ℝ) ∘ Equiv.swap 0 1 = ![3,-2,1] := by
    funext i
    fin_cases i <;> norm_num [Function.comp_def,Equiv.swap_apply_def]
  rw [he] at hp
  exact hp.trans signed_third

theorem actual_all_orders {m : ℕ} (σ : Equiv.Perm (Fin m)) (h : Fin m → ℝ) :
    cumulant (law : Measure ℝ) m (h ∘ σ) = cumulant (law : Measure ℝ) m h :=
  cumulant_comp_perm_of_compact law compact_law σ h
end Skew

namespace Plane
open D74RawPlane

theorem all_orders {m : ℕ} (σ : Equiv.Perm (Fin m)) (h : Fin m → D74RawPlane.E) :
    cumulant (μ : Measure D74RawPlane.E) m (h ∘ σ) = cumulant (μ : Measure D74RawPlane.E) m h :=
  cumulant_comp_perm_of_compact μ compact_μ σ h

theorem actual_signed_second : cumulant (μ : Measure D74RawPlane.E) 2 ![point 1 2,point (-2) 3] = 4 := by
  rw [cumulant_two_eq_centered_moment_of_integrable_exp (μ : Measure D74RawPlane.E) one_pos
    (compact_support_integrable_exp _ compact_μ 1),integral_μ,integral_μ,integral_μ]
  norm_num [PiLp.inner_apply,Fin.sum_univ_two,Real.inner_apply,point,smul_eq_mul]

theorem actual_second_swap : cumulant (μ : Measure D74RawPlane.E) 2 ![point (-2) 3,point 1 2] = 4 := by
  have hp := cumulant_comp_perm_of_compact μ compact_μ (Equiv.swap (0:Fin 2) 1)
    ![point 1 2,point (-2) 3]
  have he : (![point 1 2,point (-2) 3] : Fin 2 → D74RawPlane.E) ∘ Equiv.swap 0 1 = ![point (-2) 3,point 1 2] := by
    funext i
    fin_cases i <;> norm_num [Function.comp_def,Equiv.swap_apply_def]
  rw [he] at hp
  exact hp.trans actual_signed_second

/-- Literal mixed coordinates, opposite signs and a repeated direction. -/
theorem fourth_repeat_signed_swap :
    cumulant (μ : Measure D74RawPlane.E) 4
      ((![point 1 2,point (-2) 3,point 1 2,point 3 (-1)] : Fin 4 → D74RawPlane.E) ∘ Equiv.swap 0 3) =
    cumulant (μ : Measure D74RawPlane.E) 4 ![point 1 2,point (-2) 3,point 1 2,point 3 (-1)] :=
  cumulant_comp_perm_of_compact μ compact_μ _ _
end Plane

namespace Zero
abbrev E0 := EuclideanSpace ℝ (Fin 0)
def law : ProbabilityMeasure E0 := ⟨Measure.dirac 0,inferInstance⟩
lemma compact_law : IsCompact (law : Measure E0).support :=
  isCompact_univ.of_isClosed_subset (law : Measure E0).isClosed_support (subset_univ _)

theorem positive_arity_all (m : ℕ) (σ : Equiv.Perm (Fin (m+1))) (h : Fin (m+1) → E0) :
    cumulant (law : Measure E0) (m+1) (h ∘ σ) = cumulant (law : Measure E0) (m+1) h :=
  cumulant_comp_perm_of_compact law compact_law σ h

/-- The compact zero-dimensional law is a real m0 consumer as well. -/
theorem m0 (σ : Equiv.Perm (Fin 0)) (h : Fin 0 → E0) :
    cumulant (law : Measure E0) 0 (h ∘ σ) = cumulant (law : Measure E0) 0 h :=
  cumulant_comp_perm_of_compact law compact_law σ h
end Zero
end D74GroupingPermutation

end
end PermutationClients

-- ===== reviewer module PairClients (D74-Grouping-Supports-Independent-20261009 (receipt 0175abed…)) =====
section PairClients
set_option autoImplicit false
open FunctionalInequalities.Analysis
namespace D74GroupingPairs

def compl {m : ℕ} (q : Fin m → Bool) : Fin m → Bool := fun i => !(q i)
lemma compl_compl {m : ℕ} (q : Fin m → Bool) : compl (compl q) = q := by
  funext i
  simp [compl]

/-- Actual source middle allocations: both inherited sides contain at least2 slots. -/
def middle (m : ℕ) (q : Fin m → Bool) : Prop :=
  2 ≤ (selected (fun _ : Fin m => ()) q).length ∧
    2 ≤ (selected (fun _ : Fin m => ()) (compl q)).length

instance middleDecidable (m : ℕ) : DecidablePred (middle m) := fun q =>
  inferInstanceAs (Decidable (2 ≤ (selected (fun _ : Fin m => ()) q).length ∧
    2 ≤ (selected (fun _ : Fin m => ()) (compl q)).length))

lemma middle_compl {m : ℕ} (q : Fin m → Bool) : middle m (compl q) ↔ middle m q := by
  unfold middle
  rw [compl_compl]
  exact and_comm

def middleMasks (m : ℕ) : Finset (Fin m → Bool) := Finset.univ.filter (middle m)
def representatives {m : ℕ} (i₀ : Fin m) : Finset (Fin m → Bool) :=
  Finset.univ.filter fun q => q i₀=true ∧ middle m q

lemma generic_signed_middle {m : ℕ} (f : (Fin m → Bool) → ℝ)
    (hf : ∀ q,f (compl q)=f q) (i₀ : Fin m) :
    (∑ q ∈ middleMasks m,f q) = 2*∑ q ∈ representatives i₀,f q :=
  sum_filter_eq_two_mul_sum_filter_of_compl_invariant (middle m) middle_compl f hf i₀

lemma actual_middle_m1 : (middleMasks 1).card=0 := by decide
lemma actual_middle_m2 : (middleMasks 2).card=0 := by decide
lemma actual_middle_m3 : (middleMasks 3).card=0 := by decide
lemma actual_middle_m4 : (middleMasks 4).card=6 := by decide
lemma actual_representatives_m1 : (representatives (0:Fin 1)).card=0 := by decide
lemma actual_representatives_m2 : (representatives (0:Fin 2)).card=0 := by decide
lemma actual_representatives_m3 : (representatives (0:Fin 3)).card=0 := by decide
lemma actual_representatives_m4 : (representatives (0:Fin 4)).card=3 := by decide

/-- Counted sum of actual middle masks, not an assumed pairing conclusion. -/
theorem constant_middle_pair (m : ℕ) (i₀ : Fin m) :
    (∑ _q ∈ middleMasks m,(1:ℝ)) = 2*∑ _q ∈ representatives i₀,(1:ℝ) :=
  generic_signed_middle (fun _ => 1) (fun _ => rfl) i₀

theorem actual_four_constant : (∑ _q ∈ middleMasks 4,(1:ℝ)) = 6 := by
  simp [actual_middle_m4]

theorem actual_four_representatives : (∑ _q ∈ representatives (0:Fin 4),(1:ℝ)) = 3 := by
  simp [actual_representatives_m4]

/-- Pair invariance permits signs: two contributions-2 cancel four contributions+1. -/
def signedFour (q : Fin 4 → Bool) : ℝ := if q 0=q 1 then -2 else 1
lemma signedFour_compl (q : Fin 4 → Bool) : signedFour (compl q)=signedFour q := by
  unfold signedFour compl
  cases q 0 <;> cases q 1 <;> rfl

theorem actual_signed_pair : (∑ q ∈ middleMasks 4,signedFour q) =
    2*∑ q ∈ representatives (0:Fin 4),signedFour q :=
  generic_signed_middle signedFour signedFour_compl 0

lemma concrete_representatives_four : representatives (0:Fin 4) =
    {![true,true,false,false],![true,false,true,false],![true,false,false,true]} := by decide

theorem signed_representatives_cancel : (∑ q ∈ representatives (0:Fin 4),signedFour q)=0 := by
  rw [concrete_representatives_four]
  norm_num [signedFour]

theorem signed_all_cancel : (∑ q ∈ middleMasks 4,signedFour q)=0 := by
  rw [actual_signed_pair,signed_representatives_cancel]
  ring

/-- Empty arity does not supply the fixed slot required by the public pair theorem. -/
theorem no_fixed_slot_Fin0 : ¬Nonempty (Fin 0) := by
  rintro ⟨i⟩
  exact Fin.elim0 i

theorem empty_arity_full_sum_one : (∑ _q : Fin 0 → Bool,(1:ℝ))=1 := by simp

theorem empty_arity_naive_doubling_false :
    (∑ _q : Fin 0 → Bool,(1:ℝ)) ≠ 2*(∑ _q : Fin 0 → Bool,(1:ℝ)) := by
  rw [empty_arity_full_sum_one]
  norm_num
end D74GroupingPairs

end PairClients

#print axioms D74rSkewLaw.integrable_twoPt
#print axioms D74rSkewLaw.integral_twoPt
#print axioms D74rSkewLaw.isProbabilityMeasure_twoPt
#print axioms D74rSkewLaw.centered_twoPt
#print axioms D74rSkewLaw.isotropic_twoPt
#print axioms D74rSkewLaw.integrable_exp_mul_norm_twoPt
#print axioms D74rSkewLaw.cumulant_three_twoPt
#print axioms D74RawPlane.integral_μ
#print axioms D74RawPlane.support_subset
#print axioms D74RawPlane.compact_μ
#print axioms D74RawPlane.inner_point
#print axioms D74GroupingPermutation.generic_all_orders
#print axioms D74GroupingPermutation.generic_m0
#print axioms D74GroupingPermutation.Skew.compact_law
#print axioms D74GroupingPermutation.Skew.actual_nonzero_third
#print axioms D74GroupingPermutation.Skew.signed_third
#print axioms D74GroupingPermutation.Skew.actual_signed_swap
#print axioms D74GroupingPermutation.Skew.actual_all_orders
#print axioms D74GroupingPermutation.Plane.all_orders
#print axioms D74GroupingPermutation.Plane.actual_signed_second
#print axioms D74GroupingPermutation.Plane.actual_second_swap
#print axioms D74GroupingPermutation.Plane.fourth_repeat_signed_swap
#print axioms D74GroupingPermutation.Zero.compact_law
#print axioms D74GroupingPermutation.Zero.positive_arity_all
#print axioms D74GroupingPermutation.Zero.m0
#print axioms D74GroupingPairs.compl_compl
#print axioms D74GroupingPairs.middle_compl
#print axioms D74GroupingPairs.generic_signed_middle
#print axioms D74GroupingPairs.actual_middle_m1
#print axioms D74GroupingPairs.actual_middle_m2
#print axioms D74GroupingPairs.actual_middle_m3
#print axioms D74GroupingPairs.actual_middle_m4
#print axioms D74GroupingPairs.actual_representatives_m1
#print axioms D74GroupingPairs.actual_representatives_m2
#print axioms D74GroupingPairs.actual_representatives_m3
#print axioms D74GroupingPairs.actual_representatives_m4
#print axioms D74GroupingPairs.constant_middle_pair
#print axioms D74GroupingPairs.actual_four_constant
#print axioms D74GroupingPairs.actual_four_representatives
#print axioms D74GroupingPairs.signedFour_compl
#print axioms D74GroupingPairs.actual_signed_pair
#print axioms D74GroupingPairs.concrete_representatives_four
#print axioms D74GroupingPairs.signed_representatives_cancel
#print axioms D74GroupingPairs.signed_all_cancel
#print axioms D74GroupingPairs.no_fixed_slot_Fin0
#print axioms D74GroupingPairs.empty_arity_full_sum_one
#print axioms D74GroupingPairs.empty_arity_naive_doubling_false
#print axioms FunctionalInequalities.Analysis.BakryEmery.cumulant_comp_perm_of_compact
#print axioms FunctionalInequalities.Analysis.sum_filter_eq_two_mul_sum_filter_of_compl_invariant
