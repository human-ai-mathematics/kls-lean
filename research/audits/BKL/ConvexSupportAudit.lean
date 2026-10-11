import FunctionalInequalities.Probability.ConvexSupport
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Independent audit clients for the uniform open-halfspace mass bound (CEK arXiv:1304.0630v1 (54), probability
specialization; Probability/ConvexSupport.lean). Merged verbatim from the reviewer receipts CEK54-UniformHalfspace-Independent
(6ddf2368…: ScalarClients, PlaneClients, ZeroClients, UniformScalarClients, UniformPlaneClients, UniformZeroClients) and
CEK54-PositiveNeighborhood-Independent (6926f5b0…: Clients), each in its own named section, re-pointed from the raw `Candidate`
module to the production owner; contracts/axiom-enumeration tooling stays in the receipts. -/

-- ===== reviewer module ScalarClients (CEK54-UniformHalfspace-Independent-20261009) =====
section ScalarClients
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace
open FunctionalInequalities.Probability
namespace CEK54Scalar

/-- Arbitrary real IP + MS only, without FD/Complete/Borel or any supplied support point. -/
theorem full_generic {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] (μ : ProbabilityMeasure E) {x₀ : E}
    (hx₀ : x₀ ∈ interior (convexHull ℝ (μ : Measure E).support)) {u : E} (hu : u ≠ 0) :
    ∃ y ∈ (μ : Measure E).support,0 < ⟪u,y-x₀⟫ :=
  exists_mem_support_inner_sub_pos_of_mem_interior_convexHull (E := E) (μ := μ)
    (x₀ := x₀) (hx₀ := hx₀) (u := u) (hu := hu)

def law (a b : ℝ) : ProbabilityMeasure ℝ :=
  ⟨(1/2:ENNReal) • Measure.dirac a + (1/2:ENNReal) • Measure.dirac b,by
    constructor
    simp only [Measure.add_apply,Measure.smul_apply,measure_univ,smul_eq_mul,mul_one]
    simpa only [one_div] using ENNReal.inv_two_add_inv_two⟩

lemma support_subset_pair (a b : ℝ) : (law a b : Measure ℝ).support ⊆ {a,b} := by
  apply Measure.support_subset_of_isClosed (isClosed_singleton.union isClosed_singleton)
  rw [mem_ae_iff]
  simp [law]

lemma atom_left_support (a b : ℝ) : a ∈ (law a b : Measure ℝ).support := by
  classical
  rw [Measure.mem_support_iff_forall]
  intro U hU
  have ha : a ∈ U := mem_of_mem_nhds hU
  change 0 < ((1/2:ENNReal) • Measure.dirac a + (1/2:ENNReal) • Measure.dirac b) U
  simp only [Measure.add_apply,Measure.smul_apply,smul_eq_mul,Measure.dirac_apply_of_mem ha,mul_one]
  exact lt_of_lt_of_le (by norm_num : (0:ENNReal) < 1/2) (le_add_right le_rfl)

lemma atom_right_support (a b : ℝ) : b ∈ (law a b : Measure ℝ).support := by
  classical
  rw [Measure.mem_support_iff_forall]
  intro U hU
  have hb : b ∈ U := mem_of_mem_nhds hU
  change 0 < ((1/2:ENNReal) • Measure.dirac a + (1/2:ENNReal) • Measure.dirac b) U
  simp only [Measure.add_apply,Measure.smul_apply,smul_eq_mul,Measure.dirac_apply_of_mem hb,mul_one]
  exact lt_of_lt_of_le (by norm_num : (0:ENNReal) < 1/2) (le_add_left le_rfl)

lemma actual_support (a b : ℝ) : (law a b : Measure ℝ).support = {a,b} := by
  apply Set.Subset.antisymm (support_subset_pair a b)
  intro x hx
  rcases hx with rfl | rfl
  · exact atom_left_support _ _
  · exact atom_right_support _ _

lemma actual_hull (a b : ℝ) (hab : a ≤ b) : convexHull ℝ (law a b : Measure ℝ).support = Icc a b := by
  rw [actual_support,convexHull_pair,segment_eq_Icc hab]

lemma actual_interior (a b x : ℝ) (hax : a < x) (hxb : x < b) :
    x ∈ interior (convexHull ℝ (law a b : Measure ℝ).support) := by
  rw [actual_hull a b (le_of_lt (lt_trans hax hxb)),interior_Icc]
  exact ⟨hax,hxb⟩

lemma integral_law (a b : ℝ) : (∫ x,x ∂(law a b : Measure ℝ)) = (a+b)/2 := by
  have ha : Integrable (fun x : ℝ => x) ((1/2:ENNReal) • Measure.dirac a) :=
    (integrable_dirac (by simp)).smul_measure (by norm_num)
  have hb : Integrable (fun x : ℝ => x) ((1/2:ENNReal) • Measure.dirac b) :=
    (integrable_dirac (by simp)).smul_measure (by norm_num)
  change (∫ x,x ∂((1/2:ENNReal) • Measure.dirac a + (1/2:ENNReal) • Measure.dirac b)) = _
  rw [integral_add_measure ha hb,integral_smul_measure,integral_smul_measure]
  norm_num
  ring

/-- A noncentered actual law and an interior point different from its mean. -/
theorem noncentered_mean : (∫ x,x ∂(law 1 3 : Measure ℝ)) = 2 := by
  rw [integral_law]
  norm_num

theorem center_not_mean : (3/2:ℝ) ≠ (∫ x,x ∂(law 1 3 : Measure ℝ)) := by
  rw [noncentered_mean]
  norm_num

theorem noncentered_nonmean_small_direction :
    ∃ y ∈ (law 1 3 : Measure ℝ).support,0 < ⟪(1/100:ℝ),y-(3/2:ℝ)⟫ :=
  exists_mem_support_inner_sub_pos_of_mem_interior_convexHull (law 1 3)
    (actual_interior 1 3 (3/2) (by norm_num) (by norm_num)) (by norm_num)

theorem balanced_positive : ∃ y ∈ (law (-1) 1 : Measure ℝ).support,0 < ⟪(2:ℝ),y⟫ := by
  have h := exists_mem_support_inner_sub_pos_of_mem_interior_convexHull (law (-1) 1)
    (actual_interior (-1) 1 0 (by norm_num) (by norm_num)) (by norm_num : (2:ℝ) ≠ 0)
  simpa only [sub_zero] using h

theorem balanced_negative : ∃ y ∈ (law (-1) 1 : Measure ℝ).support,0 < ⟪(-3:ℝ),y⟫ := by
  have h := exists_mem_support_inner_sub_pos_of_mem_interior_convexHull (law (-1) 1)
    (actual_interior (-1) 1 0 (by norm_num) (by norm_num)) (by norm_num : (-3:ℝ) ≠ 0)
  simpa only [sub_zero] using h

theorem boundary_no_positive_support :
    ¬∃ y ∈ (law (-1) 1 : Measure ℝ).support,0 < ⟪(1:ℝ),y-1⟫ := by
  rintro ⟨y,hy,hpos⟩
  have hp := support_subset_pair (-1) 1 hy
  rcases hp with rfl | rfl <;> norm_num [Real.inner_apply] at hpos

theorem boundary_not_interior :
    (1:ℝ) ∉ interior (convexHull ℝ (law (-1) 1 : Measure ℝ).support) := by
  rw [actual_hull (-1) 1 (by norm_num),interior_Icc]
  norm_num

theorem zero_direction_no_point :
    ¬∃ y ∈ (law (-1) 1 : Measure ℝ).support,0 < ⟪(0:ℝ),y⟫ := by simp
end CEK54Scalar

end
end ScalarClients

-- ===== reviewer module PlaneClients (CEK54-UniformHalfspace-Independent-20261009) =====
section PlaneClients
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open FunctionalInequalities.Probability
open scoped RealInnerProductSpace
namespace CEK54Plane
abbrev E := EuclideanSpace ℝ (Fin 2)
instance : MeasurableSpace E := borel E
instance : BorelSpace E := ⟨rfl⟩
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


lemma corner_support (a b : ℝ) (ha : a=1 ∨ a=-1) (hb : b=1 ∨ b=-1) :
    point a b ∈ (μ : Measure E).support := by
  classical
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  all_goals
    rw [Measure.mem_support_iff_forall]
    intro U hU
    have hmem := mem_of_mem_nhds hU
    change 0 < (ENNReal.ofReal (1/4) • Measure.dirac (point 1 1) +
      ENNReal.ofReal (1/4) • Measure.dirac (point 1 (-1)) +
      ENNReal.ofReal (1/4) • Measure.dirac (point (-1) 1) +
      ENNReal.ofReal (1/4) • Measure.dirac (point (-1) (-1))) U
    simp only [Measure.add_apply,Measure.smul_apply,smul_eq_mul,
      Measure.dirac_apply_of_mem hmem,mul_one]
    positivity

def box : Set E := {x | -1 < x 0 ∧ x 0 < 1 ∧ -1 < x 1 ∧ x 1 < 1}
lemma box_open : IsOpen box := by
  have h0 : Continuous (fun x : E => x 0) := by fun_prop
  have h1 : Continuous (fun x : E => x 1) := by fun_prop
  exact (isOpen_lt continuous_const h0).inter
    ((isOpen_lt h0 continuous_const).inter
      ((isOpen_lt continuous_const h1).inter (isOpen_lt h1 continuous_const)))

lemma point_interpolation (a b : ℝ) :
    point (-1) b + ((a+1)/2) • (point 1 b-point (-1) b) = point a b := by
  ext i
  fin_cases i
  · norm_num [point]
  · simp [point]

lemma vertical_interpolation (a b : ℝ) :
    point a (-1) + ((b+1)/2) • (point a 1-point a (-1)) = point a b := by
  ext i
  fin_cases i
  · simp [point]
  · norm_num [point]

lemma box_subset_hull : box ⊆ convexHull ℝ (μ : Measure E).support := by
  intro x hx
  rcases hx with ⟨h0l,h0r,h1l,h1r⟩
  have hc := convex_convexHull ℝ (μ : Measure E).support
  have ht0 : (x 0+1)/2 ∈ Icc (0:ℝ) 1 := by constructor <;> linarith
  have ht1 : (x 1+1)/2 ∈ Icc (0:ℝ) 1 := by constructor <;> linarith
  have lo : point (x 0) (-1) ∈ convexHull ℝ (μ : Measure E).support := by
    have h := hc.add_smul_sub_mem
      (subset_convexHull ℝ _ (corner_support (-1) (-1) (Or.inr rfl) (Or.inr rfl)))
      (subset_convexHull ℝ _ (corner_support 1 (-1) (Or.inl rfl) (Or.inr rfl))) ht0
    rwa [point_interpolation] at h
  have hi : point (x 0) 1 ∈ convexHull ℝ (μ : Measure E).support := by
    have h := hc.add_smul_sub_mem
      (subset_convexHull ℝ _ (corner_support (-1) 1 (Or.inr rfl) (Or.inl rfl)))
      (subset_convexHull ℝ _ (corner_support 1 1 (Or.inl rfl) (Or.inl rfl))) ht0
    rwa [point_interpolation] at h
  have h := hc.add_smul_sub_mem lo hi ht1
  rw [vertical_interpolation] at h
  have he : point (x 0) (x 1)=x := by
    ext i
    fin_cases i <;> simp [point]
  rwa [he] at h

lemma origin_interior : (0:E) ∈ interior (convexHull ℝ (μ : Measure E).support) := by
  apply mem_interior_iff_mem_nhds.mpr
  have hz : (0:E) ∈ box := by norm_num [box]
  exact Filter.mem_of_superset (box_open.mem_nhds hz) box_subset_hull

/-- Actual four-point measure has full-dimensional support hull; oblique direction is nonunit. -/
theorem oblique_direction : ∃ y ∈ (μ : Measure E).support,0 < ⟪point (1/100) (-2),y⟫ := by
  have hu : point (1/100) (-2) ≠ (0:E) := by
    intro he
    have h := congrArg (fun x : E => x 1) he
    norm_num [point] at h
  have h := exists_mem_support_inner_sub_pos_of_mem_interior_convexHull μ origin_interior hu
  simpa only [sub_zero] using h
end CEK54Plane

end
end PlaneClients

-- ===== reviewer module ZeroClients (CEK54-UniformHalfspace-Independent-20261009) =====
section ZeroClients
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace
open FunctionalInequalities.Probability
namespace CEK54Zero
abbrev E0 := EuclideanSpace ℝ (Fin 0)
instance : MeasurableSpace E0 := borel E0
instance : BorelSpace E0 := ⟨rfl⟩
def law : ProbabilityMeasure E0 := ⟨Measure.dirac 0,inferInstance⟩

lemma actual_support_univ : (law : Measure E0).support=univ := by
  apply Set.eq_univ_iff_forall.mpr
  intro x
  rw [Measure.mem_support_iff_forall]
  intro U hU
  have hx : x ∈ U := mem_of_mem_nhds hU
  have he : x=(0:E0) := Subsingleton.elim _ _
  rw [he] at hx
  change 0 < Measure.dirac (0:E0) U
  rw [Measure.dirac_apply_of_mem hx]
  exact zero_lt_one

lemma actual_origin_interior : (0:E0) ∈ interior (convexHull ℝ (law : Measure E0).support) := by
  rw [actual_support_univ,convexHull_univ,interior_univ]
  trivial

theorem no_nonzero_direction : ¬∃ u : E0,u ≠ 0 := by
  rintro ⟨u,hu⟩
  exact hu (Subsingleton.elim _ _)

/-- The public theorem remains callable at ambientFin0, but its nonzero-direction premise is empty. -/
theorem actual_Fin0_vacuity (u : E0) (hu : u ≠ 0) :
    ∃ y ∈ (law : Measure E0).support,0 < ⟪u,y⟫ := by
  have h := exists_mem_support_inner_sub_pos_of_mem_interior_convexHull law actual_origin_interior hu
  simpa only [sub_zero] using h
end CEK54Zero

end
end ZeroClients

-- ===== reviewer module Clients (CEK54-PositiveNeighborhood-Independent-20261009) =====
section NeighborhoodClients
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace
open FunctionalInequalities.Probability
namespace CEK54Neighborhood
/-- The same positive-mass ball works for every direction in an actual neighborhood. -/
theorem nearby_halfspace_mass {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] (μ : ProbabilityMeasure E) {x₀ u y : E}
    (hy : y ∈ (μ : Measure E).support) (hpos : 0 < ⟪u,y-x₀⟫) :
    ∃ δ > 0, ∀ v : E, ‖v-u‖ < δ → 0 < (μ : Measure E) {x | 0 < ⟪v,x-x₀⟫} := by
  obtain ⟨δ,hδ,r,_,hm,hnear⟩ := exists_pos_ball_inner_sub_pos_of_mem_support μ hy hpos
  refine ⟨δ,hδ,?_⟩
  intro v hv
  exact lt_of_lt_of_le hm (measure_mono (fun x hx => hnear v hv x hx))
def atom (y : ℝ) : ProbabilityMeasure ℝ := ⟨Measure.dirac y, inferInstance⟩
lemma atom_support (y : ℝ) : y ∈ (atom y : Measure ℝ).support := by
  rw [Measure.mem_support_iff_forall]
  intro U hU
  change 0 < Measure.dirac y U
  rw [Measure.dirac_apply_of_mem (mem_of_mem_nhds hU)]
  norm_num
/-- Noncentered law, shifted base point, and nonunit direction; no hull-interior premise. -/
theorem shifted_nonunit : ∃ δ > 0, ∀ v : ℝ, |v-2| < δ →
    0 < (atom 3 : Measure ℝ) {x | 0 < v*(x-1)} := by
  simpa only [Real.norm_eq_abs, RCLike.inner_apply, conj_trivial, mul_comm] using
    nearby_halfspace_mass (atom 3) (x₀:=1) (u:=2) (atom_support 3) (by norm_num)
theorem negative_nonunit : ∃ δ > 0, ∀ v : ℝ, |v-(-2)| < δ →
    0 < (atom (-3) : Measure ℝ) {x | 0 < v*(x-2)} := by
  simpa only [Real.norm_eq_abs, RCLike.inner_apply, conj_trivial, mul_comm] using
    nearby_halfspace_mass (atom (-3)) (x₀:=2) (u:=(-2)) (atom_support (-3)) (by norm_num)
theorem tiny_direction : ∃ δ > 0, ∀ v : ℝ, |v-(1/100)| < δ →
    0 < (atom 100 : Measure ℝ) {x | 0 < v*(x-(-2))} := by
  simpa only [Real.norm_eq_abs, RCLike.inner_apply, conj_trivial, mul_comm] using
    nearby_halfspace_mass (atom 100) (x₀:=(-2)) (u:=(1/100)) (atom_support 100) (by norm_num)
/-- Strict positivity is necessary, even at a genuine support point. -/
theorem boundary_point_failure : (atom 0 : Measure ℝ) {x | 0 < (1:ℝ)*(x-0)} = 0 := by
  change Measure.dirac 0 {x : ℝ | 0 < (1:ℝ)*(x-0)} = 0
  simp
lemma zero_direction_failure (μ : ProbabilityMeasure ℝ) (x₀ : ℝ) :
    (μ : Measure ℝ) {x | 0 < (0:ℝ)*(x-x₀)} = 0 := by simp
abbrev E := EuclideanSpace ℝ (Fin 2)
instance : MeasurableSpace E := borel E
def point (a b : ℝ) : E := WithLp.toLp 2 ![a,b]
def planeAtom : ProbabilityMeasure E := ⟨Measure.dirac (point 2 (-3)), inferInstance⟩
lemma plane_support : point 2 (-3) ∈ (planeAtom : Measure E).support := by
  rw [Measure.mem_support_iff_forall]
  intro U hU
  change 0 < Measure.dirac (point 2 (-3)) U
  rw [Measure.dirac_apply_of_mem (mem_of_mem_nhds hU)]
  norm_num
/-- Actual oblique 2D direction, nonzero base point, and nonsymmetric support. -/
theorem plane_oblique : ∃ δ > 0, ∀ v : E, ‖v-point 1 (-2)‖ < δ →
    0 < (planeAtom : Measure E) {x | 0 < ⟪v,x-point 0 1⟫} := by
  apply nearby_halfspace_mass planeAtom plane_support
  norm_num [point,PiLp.inner_apply,Fin.sum_univ_two]
/-- Fin0 provides no positive pairing, so no hidden unit-vector existence is used. -/
theorem fin0_no_positive_pairing (u x₀ y : EuclideanSpace ℝ (Fin 0)) : ¬ 0 < ⟪u,y-x₀⟫ := by
  have hu : u = 0 := Subsingleton.elim _ _
  simp [hu]
end CEK54Neighborhood

end
end NeighborhoodClients

-- ===== reviewer module UniformScalarClients (CEK54-UniformHalfspace-Independent-20261009) =====
section UniformScalarClients
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace
open FunctionalInequalities.Probability
namespace UniformScalar

def H (x₀ u : ℝ) : Set ℝ := {x | 0 < ⟪u,x-x₀⟫}
def HC (x₀ u : ℝ) : Set ℝ := {x | 0 ≤ ⟪u,x-x₀⟫}
lemma measurable_H (x₀ u : ℝ) : MeasurableSet (H x₀ u) := by
  simp only [H,Real.inner_apply]
  exact measurableSet_lt measurable_const (measurable_const.mul (measurable_id.sub measurable_const))
lemma measurable_HC (x₀ u : ℝ) : MeasurableSet (HC x₀ u) := by
  simp only [HC,Real.inner_apply]
  exact measurableSet_le measurable_const (measurable_const.mul (measurable_id.sub measurable_const))
lemma unit_cases {u : ℝ} (hu : ‖u‖=1) : u=1 ∨ u=-1 := by
  by_cases h : 0 ≤ u
  · left
    simpa only [Real.norm_eq_abs,abs_of_nonneg h] using hu
  · right
    have hn : u ≤ 0 := (lt_of_not_ge h).le
    rw [Real.norm_eq_abs,abs_of_nonpos hn] at hu
    linarith

lemma balanced_mass_one : ((CEK54Scalar.law (-1) 1 : Measure ℝ) (H 0 1)).toReal=1/2 := by
  norm_num [CEK54Scalar.law,Measure.dirac_apply,H,Real.inner_apply]
lemma balanced_mass_neg_one : ((CEK54Scalar.law (-1) 1 : Measure ℝ) (H 0 (-1))).toReal=1/2 := by
  norm_num [CEK54Scalar.law,Measure.dirac_apply,H,Real.inner_apply]
theorem balanced_uniform_actual_mass (u : ℝ) (hu : ‖u‖=1) :
    ((CEK54Scalar.law (-1) 1 : Measure ℝ) (H 0 u)).toReal=1/2 := by
  rcases unit_cases hu with rfl | rfl
  · exact balanced_mass_one
  · exact balanced_mass_neg_one
theorem balanced_uniform_target : ∃ m : ℝ,0<m ∧ m≤1 ∧
    ∀ u : ℝ,‖u‖=1 → m≤((CEK54Scalar.law (-1) 1 : Measure ℝ) (H 0 u)).toReal :=
  exists_pos_le_measure_halfspace_of_mem_interior_convexHull_support (CEK54Scalar.law (-1) 1)
    (CEK54Scalar.actual_interior (-1) 1 0 (by norm_num) (by norm_num))

theorem noncentered_shifted_uniform_target : ∃ m : ℝ,0<m ∧ m≤1 ∧
    ∀ u : ℝ,‖u‖=1 → m≤((CEK54Scalar.law 1 3 : Measure ℝ) (H (3/2) u)).toReal :=
  exists_pos_le_measure_halfspace_of_mem_interior_convexHull_support (CEK54Scalar.law 1 3)
    (CEK54Scalar.actual_interior 1 3 (3/2) (by norm_num) (by norm_num))
theorem noncentered_shifted_actual_mass (u : ℝ) (hu : ‖u‖=1) :
    ((CEK54Scalar.law 1 3 : Measure ℝ) (H (3/2) u)).toReal=1/2 := by
  rcases unit_cases hu with rfl | rfl <;>
    norm_num [CEK54Scalar.law,Measure.dirac_apply,
      Measure.dirac_apply,H,Real.inner_apply]

def asymmetric : ProbabilityMeasure ℝ :=
  ⟨ENNReal.ofReal (2/3:ℝ) • Measure.dirac 1 + ENNReal.ofReal (1/3:ℝ) • Measure.dirac 3,by
    constructor
    simp only [Measure.add_apply,Measure.smul_apply,measure_univ,smul_eq_mul,mul_one]
    rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    norm_num⟩
lemma asymmetric_support_subset : (asymmetric : Measure ℝ).support ⊆ {1,3} := by
  apply Measure.support_subset_of_isClosed (isClosed_singleton.union isClosed_singleton)
  rw [mem_ae_iff]
  simp [asymmetric]
lemma asymmetric_left_support : (1:ℝ) ∈ (asymmetric : Measure ℝ).support := by
  rw [Measure.mem_support_iff_forall]
  intro U hU
  have h1 : (1:ℝ) ∈ U := mem_of_mem_nhds hU
  change 0 < (ENNReal.ofReal (2/3:ℝ) • Measure.dirac (1:ℝ) + ENNReal.ofReal (1/3:ℝ) • Measure.dirac (3:ℝ)) U
  simp only [Measure.add_apply,Measure.smul_apply,smul_eq_mul,Measure.dirac_apply_of_mem h1,mul_one]
  exact lt_of_lt_of_le (by positivity : (0:ENNReal)<ENNReal.ofReal (2/3:ℝ)) (le_add_right le_rfl)
lemma asymmetric_right_support : (3:ℝ) ∈ (asymmetric : Measure ℝ).support := by
  rw [Measure.mem_support_iff_forall]
  intro U hU
  have h3 : (3:ℝ) ∈ U := mem_of_mem_nhds hU
  change 0 < (ENNReal.ofReal (2/3:ℝ) • Measure.dirac (1:ℝ) + ENNReal.ofReal (1/3:ℝ) • Measure.dirac (3:ℝ)) U
  simp only [Measure.add_apply,Measure.smul_apply,smul_eq_mul,Measure.dirac_apply_of_mem h3,mul_one]
  exact lt_of_lt_of_le (by positivity : (0:ENNReal)<ENNReal.ofReal (1/3:ℝ)) (le_add_left le_rfl)
lemma asymmetric_support : (asymmetric : Measure ℝ).support={1,3} := by
  apply Set.Subset.antisymm asymmetric_support_subset
  intro x hx
  rcases hx with rfl | rfl
  · exact asymmetric_left_support
  · exact asymmetric_right_support
lemma asymmetric_interior : (2:ℝ) ∈ interior (convexHull ℝ (asymmetric : Measure ℝ).support) := by
  rw [asymmetric_support,convexHull_pair,segment_eq_Icc (by norm_num : (1:ℝ)≤3),interior_Icc]
  norm_num
lemma asymmetric_mean : (∫ x,x ∂(asymmetric : Measure ℝ))=5/3 := by
  have h1 : Integrable (fun x : ℝ => x) (ENNReal.ofReal (2/3:ℝ) • Measure.dirac 1) :=
    (integrable_dirac (by simp)).smul_measure (by norm_num)
  have h3 : Integrable (fun x : ℝ => x) (ENNReal.ofReal (1/3:ℝ) • Measure.dirac 3) :=
    (integrable_dirac (by simp)).smul_measure (by norm_num)
  change (∫ x,x ∂(ENNReal.ofReal (2/3:ℝ) • Measure.dirac (1:ℝ)+ENNReal.ofReal (1/3:ℝ) • Measure.dirac (3:ℝ)))=5/3
  rw [integral_add_measure h1 h3,integral_smul_measure,integral_smul_measure]
  norm_num
lemma asymmetric_point_not_mean : (2:ℝ)≠(∫ x,x ∂(asymmetric : Measure ℝ)) := by
  rw [asymmetric_mean]
  norm_num
lemma asymmetric_mass_one : ((asymmetric : Measure ℝ) (H 2 1)).toReal=1/3 := by
  norm_num [asymmetric,Measure.dirac_apply,H,Real.inner_apply]
lemma asymmetric_mass_neg_one : ((asymmetric : Measure ℝ) (H 2 (-1))).toReal=2/3 := by
  norm_num [asymmetric,Measure.dirac_apply,H,Real.inner_apply]
theorem asymmetric_uniform_actual_mass (u : ℝ) (hu : ‖u‖=1) :
    (1/3:ℝ)≤((asymmetric : Measure ℝ) (H 2 u)).toReal := by
  rcases unit_cases hu with rfl | rfl
  · rw [asymmetric_mass_one]
  · rw [asymmetric_mass_neg_one]
    norm_num
theorem asymmetric_uniform_target : ∃ m : ℝ,0<m ∧ m≤1 ∧
    ∀ u : ℝ,‖u‖=1 → m≤((asymmetric : Measure ℝ) (H 2 u)).toReal :=
  exists_pos_le_measure_halfspace_of_mem_interior_convexHull_support asymmetric asymmetric_interior

theorem boundary_strict_mass_zero : ((CEK54Scalar.law (-1) 1 : Measure ℝ) (H 1 1)).toReal=0 := by
  norm_num [CEK54Scalar.law,Measure.dirac_apply,H,Real.inner_apply]
theorem boundary_closed_mass_half : ((CEK54Scalar.law (-1) 1 : Measure ℝ) (HC 1 1)).toReal=1/2 := by
  norm_num [CEK54Scalar.law,Measure.dirac_apply,HC,Real.inner_apply]
theorem zero_direction_strict_mass_zero : ((CEK54Scalar.law (-1) 1 : Measure ℝ) (H 0 0)).toReal=0 := by
  norm_num [CEK54Scalar.law,Measure.dirac_apply,H,Real.inner_apply]
theorem boundary_no_uniform_bound : ¬∃ m : ℝ,0<m ∧
    ∀ u : ℝ,‖u‖=1 → m≤((CEK54Scalar.law (-1) 1 : Measure ℝ) (H 1 u)).toReal := by
  rintro ⟨m,hm,h⟩
  have hz := h 1 (by norm_num)
  rw [boundary_strict_mass_zero] at hz
  exact (not_lt_of_ge hz) hm
end UniformScalar

end
end UniformScalarClients

-- ===== reviewer module UniformPlaneClients (CEK54-UniformHalfspace-Independent-20261009) =====
section UniformPlaneClients
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace
open FunctionalInequalities.Probability
namespace UniformPlane
open CEK54Plane

def H (u : E) : Set E := {x | 0 < ⟪u,x⟫}
lemma corner_mass_lower (A : Set E) (a b : ℝ) (ha : a=1 ∨ a=-1) (hb : b=1 ∨ b=-1)
    (hx : point a b ∈ A) : (1/4:ENNReal)≤(μ : Measure E) A := by
  have hc : ENNReal.ofReal (1/4:ℝ)=(1/4:ENNReal) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<4)]
    norm_num
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  all_goals
    change (1/4:ENNReal) ≤
      ((ENNReal.ofReal (1/4) • Measure.dirac (point 1 1) +
        ENNReal.ofReal (1/4) • Measure.dirac (point 1 (-1)) +
        ENNReal.ofReal (1/4) • Measure.dirac (point (-1) 1) +
        ENNReal.ofReal (1/4) • Measure.dirac (point (-1) (-1))) A)
    simp only [Measure.add_apply,Measure.smul_apply,smul_eq_mul,hc,
      Measure.dirac_apply_of_mem hx,mul_one]
  · exact le_add_right (le_add_right (le_add_right le_rfl))
  · exact le_add_right (le_add_right (le_add_left le_rfl))
  · exact le_add_right (le_add_left le_rfl)
  · exact le_add_left le_rfl

/-- Direct law calculation, independent of the final uniform-mass target. -/
theorem all_unit_directions_quarter (u : E) (hu : ‖u‖=1) :
    (1/4:ℝ)≤((μ : Measure E) (H u)).toReal := by
  have hn : u≠0 := by
    intro he
    rw [he,norm_zero] at hu
    norm_num at hu
  obtain ⟨y,hy,hpos⟩ :=
    exists_mem_support_inner_sub_pos_of_mem_interior_convexHull μ origin_interior hn
  have hk := support_subset hy
  have hH : y ∈ H u := by simpa only [H,mem_ofPred_eq,sub_zero] using hpos
  have hENN : (1/4:ENNReal)≤(μ : Measure E) (H u) := by
    rcases hk with rfl | rfl | rfl | rfl
    · exact corner_mass_lower (H u) 1 1 (Or.inl rfl) (Or.inl rfl) hH
    · exact corner_mass_lower (H u) 1 (-1) (Or.inl rfl) (Or.inr rfl) hH
    · exact corner_mass_lower (H u) (-1) 1 (Or.inr rfl) (Or.inl rfl) hH
    · exact corner_mass_lower (H u) (-1) (-1) (Or.inr rfl) (Or.inr rfl) hH
  have h := ENNReal.toReal_mono (measure_ne_top (μ : Measure E) (H u)) hENN
  norm_num at h
  exact h

theorem uniform_target : ∃ m : ℝ,0<m ∧ m≤1 ∧
    ∀ u : E,‖u‖=1 → m≤((μ : Measure E) (H u)).toReal := by
  simpa only [H,sub_zero] using
    exists_pos_le_measure_halfspace_of_mem_interior_convexHull_support μ origin_interior

def w : E := point (1/100) (-2)
def unitOblique : E := ‖w‖⁻¹ • w
lemma w_ne_zero : w≠0 := by
  intro he
  have h := congrArg (fun x : E => x 1) he
  norm_num [w,point] at h
lemma unitOblique_norm : ‖unitOblique‖=1 := by
  have hn : 0<‖w‖ := norm_pos_iff.mpr w_ne_zero
  rw [unitOblique,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hn),inv_mul_cancel₀ hn.ne']
theorem actual_oblique_mass : (1/4:ℝ)≤((μ : Measure E) (H unitOblique)).toReal :=
  all_unit_directions_quarter unitOblique unitOblique_norm
end UniformPlane

end
end UniformPlaneClients

-- ===== reviewer module UniformZeroClients (CEK54-UniformHalfspace-Independent-20261009) =====
section UniformZeroClients
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace
open FunctionalInequalities.Probability
namespace UniformZero
open CEK54Zero

theorem no_unit_direction (u : E0) : ‖u‖≠1 := by
  have he : u=0 := Subsingleton.elim _ _
  rw [he,norm_zero]
  norm_num
theorem uniform_target : ∃ m : ℝ,0<m ∧ m≤1 ∧
    ∀ u : E0,‖u‖=1 → m≤((law : Measure E0) {x | 0<⟪u,x⟫}).toReal := by
  simpa only [sub_zero] using
    exists_pos_le_measure_halfspace_of_mem_interior_convexHull_support law actual_origin_interior
/-- m=1 is valid because the actual Fin0 unit sphere is empty. -/
theorem actual_m_one : ∃ m : ℝ,m=1 ∧ 0<m ∧ m≤1 ∧
    ∀ u : E0,‖u‖=1 → m≤((law : Measure E0) {x | 0<⟪u,x⟫}).toReal := by
  refine ⟨1,rfl,by norm_num,le_rfl,?_⟩
  intro u hu
  exact (no_unit_direction u hu).elim
end UniformZero

end
end UniformZeroClients

#print axioms CEK54Scalar.full_generic
#print axioms CEK54Scalar.support_subset_pair
#print axioms CEK54Scalar.atom_left_support
#print axioms CEK54Scalar.atom_right_support
#print axioms CEK54Scalar.actual_support
#print axioms CEK54Scalar.actual_hull
#print axioms CEK54Scalar.actual_interior
#print axioms CEK54Scalar.integral_law
#print axioms CEK54Scalar.noncentered_mean
#print axioms CEK54Scalar.center_not_mean
#print axioms CEK54Scalar.noncentered_nonmean_small_direction
#print axioms CEK54Scalar.balanced_positive
#print axioms CEK54Scalar.balanced_negative
#print axioms CEK54Scalar.boundary_no_positive_support
#print axioms CEK54Scalar.boundary_not_interior
#print axioms CEK54Scalar.zero_direction_no_point
#print axioms CEK54Plane.integral_μ
#print axioms CEK54Plane.support_subset
#print axioms CEK54Plane.compact_μ
#print axioms CEK54Plane.inner_point
#print axioms CEK54Plane.corner_support
#print axioms CEK54Plane.box_open
#print axioms CEK54Plane.point_interpolation
#print axioms CEK54Plane.vertical_interpolation
#print axioms CEK54Plane.box_subset_hull
#print axioms CEK54Plane.origin_interior
#print axioms CEK54Plane.oblique_direction
#print axioms CEK54Zero.actual_support_univ
#print axioms CEK54Zero.actual_origin_interior
#print axioms CEK54Zero.no_nonzero_direction
#print axioms CEK54Zero.actual_Fin0_vacuity
#print axioms CEK54Neighborhood.nearby_halfspace_mass
#print axioms CEK54Neighborhood.atom_support
#print axioms CEK54Neighborhood.shifted_nonunit
#print axioms CEK54Neighborhood.negative_nonunit
#print axioms CEK54Neighborhood.tiny_direction
#print axioms CEK54Neighborhood.boundary_point_failure
#print axioms CEK54Neighborhood.zero_direction_failure
#print axioms CEK54Neighborhood.plane_support
#print axioms CEK54Neighborhood.plane_oblique
#print axioms CEK54Neighborhood.fin0_no_positive_pairing
#print axioms UniformScalar.measurable_H
#print axioms UniformScalar.measurable_HC
#print axioms UniformScalar.unit_cases
#print axioms UniformScalar.balanced_mass_one
#print axioms UniformScalar.balanced_mass_neg_one
#print axioms UniformScalar.balanced_uniform_actual_mass
#print axioms UniformScalar.balanced_uniform_target
#print axioms UniformScalar.noncentered_shifted_uniform_target
#print axioms UniformScalar.noncentered_shifted_actual_mass
#print axioms UniformScalar.asymmetric_support_subset
#print axioms UniformScalar.asymmetric_left_support
#print axioms UniformScalar.asymmetric_right_support
#print axioms UniformScalar.asymmetric_support
#print axioms UniformScalar.asymmetric_interior
#print axioms UniformScalar.asymmetric_mean
#print axioms UniformScalar.asymmetric_point_not_mean
#print axioms UniformScalar.asymmetric_mass_one
#print axioms UniformScalar.asymmetric_mass_neg_one
#print axioms UniformScalar.asymmetric_uniform_actual_mass
#print axioms UniformScalar.asymmetric_uniform_target
#print axioms UniformScalar.boundary_strict_mass_zero
#print axioms UniformScalar.boundary_closed_mass_half
#print axioms UniformScalar.zero_direction_strict_mass_zero
#print axioms UniformScalar.boundary_no_uniform_bound
#print axioms UniformPlane.corner_mass_lower
#print axioms UniformPlane.all_unit_directions_quarter
#print axioms UniformPlane.uniform_target
#print axioms UniformPlane.w_ne_zero
#print axioms UniformPlane.unitOblique_norm
#print axioms UniformPlane.actual_oblique_mass
#print axioms UniformZero.no_unit_direction
#print axioms UniformZero.uniform_target
#print axioms UniformZero.actual_m_one
#print axioms FunctionalInequalities.Probability.exists_mem_support_inner_sub_pos_of_mem_interior_convexHull
#print axioms FunctionalInequalities.Probability.exists_pos_ball_inner_sub_pos_of_mem_support
#print axioms FunctionalInequalities.Probability.exists_pos_le_measure_halfspace_of_mem_interior_convexHull_support
