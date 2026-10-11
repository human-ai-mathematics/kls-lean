import FunctionalInequalities.Analysis.BakryEmery.Cumulant.Leibniz
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Adjoint
import FunctionalInequalities.KLS.Isotropic

/-! Independent audit clients for the raw (74) expansion and its supports (Analysis/IteratedDerivative/{Bilinear,InnerProduct}.lean, Analysis/BakryEmery/Cumulant/Leibniz.lean). Merged verbatim from the reviewer receipt `D74-Raw-Assembly-Independent-20261009 (receipt f17f3495…)` (modules
UniformLaw, SkewLaw, MaskClients, InnerClients, GradientClients, RawModels, PlaneModels), re-pointed from the raw `Candidate*` modules to the production owners; contracts/axiom-enumeration tooling stays in the receipt. -/

-- ===== reviewer module UniformLaw (D74-Raw-Assembly-Independent-20261009 (receipt f17f3495…)) =====
section UniformLaw
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set intervalIntegral
open FunctionalInequalities FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace
namespace D74rUniformLaw
/-- Exact underlying measure of the library unitUniform law. -/
def law : ProbabilityMeasure ℝ := ⟨volume.restrict (Icc (0:ℝ) 1), by constructor; simp⟩
lemma law_compact : IsCompact (law : Measure ℝ).support := by
  apply isCompact_Icc.of_isClosed_subset (law : Measure ℝ).isClosed_support
  intro x hx
  have hs := Measure.support_restrict_subset (μ := (volume:Measure ℝ)) (s := Icc (0:ℝ) 1) hx
  simpa only [IsClosed.closure_eq isClosed_Icc] using hs.1
lemma law_memLp : MemLp (id : ℝ → ℝ) 2 (law : Measure ℝ) :=
  MemLp.of_bound continuous_id.aestronglyMeasurable 1 (by
    change ∀ᵐ x ∂(volume.restrict (Icc (0:ℝ) 1)), ‖id x‖ ≤ 1
    rw [ae_restrict_iff' measurableSet_Icc]
    exact ae_of_all _ fun u hu => by
      change ‖u‖ ≤ 1
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith [hu.1,hu.2])
lemma law_mean : (∫ x, x ∂(law : Measure ℝ)) = 1/2 := by
  change (∫ x in Icc (0:ℝ) 1, x) = 1/2
  rw [integral_Icc_eq_integral_Ioc, ← integral_of_le zero_le_one, integral_id]
  norm_num
/-- The existing AffineProfile variance proof, specialized to its actual uniform measure. -/
lemma law_variance : variance (id : ℝ → ℝ) (law : Measure ℝ) = 1/12 := by
  rw [variance_eq_sub law_memLp]
  change (∫ x in Icc (0:ℝ) 1, x^2) - (∫ x in Icc (0:ℝ) 1, x)^2 = 1/12
  rw [integral_Icc_eq_integral_Ioc, ← integral_of_le zero_le_one, integral_pow,
    integral_Icc_eq_integral_Ioc, ← integral_of_le zero_le_one, integral_id]
  norm_num
lemma law_covariance : Covariance.operator (law : Measure ℝ) = (1/12:ℝ) • ContinuousLinearMap.id ℝ ℝ := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℝ
  intro y
  rw [Covariance.operator_inner, covarianceBilin_real, law_variance]
  simp
  ring
end D74rUniformLaw

end
end UniformLaw

-- ===== reviewer module SkewLaw (D74-Raw-Assembly-Independent-20261009 (receipt f17f3495…)) =====
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

-- ===== reviewer module MaskClients (D74-Raw-Assembly-Independent-20261009 (receipt f17f3495…)) =====
section MaskClients
set_option autoImplicit false
namespace D74RawMasks

def proper (m : ℕ) : Finset (Fin m → Bool) :=
  Finset.univ.filter fun q => (∃ i,q i=true) ∧ (∃ i,q i=false)

theorem zero : proper 0 = ∅ := by decide

theorem one : proper 1 = ∅ := by
  ext q
  cases hq : q 0 <;> simp [proper,Fin.exists_fin_succ]

theorem two : proper 2 = {![true,false],![false,true]} := by
  ext q
  cases h0 : q 0 <;> cases h1 : q 1 <;>
    simp [proper,Fin.exists_fin_succ,funext_iff,Fin.forall_fin_succ,h0,h1]

theorem three : proper 3 =
    {![true,false,false],![false,true,false],![false,false,true],
      ![true,true,false],![true,false,true],![false,true,true]} := by
  ext q
  cases h0 : q 0 <;> cases h1 : q 1 <;> cases h2 : q 2 <;>
    simp [proper,Fin.exists_fin_succ,funext_iff,Fin.forall_fin_succ,h0,h1,h2]

theorem four_card : (proper 4).card = 14 := by decide

theorem four_single_count : ((proper 4).filter (fun q =>
    (FunctionalInequalities.Analysis.selected (fun _ : Fin 4 => ()) q).length = 1)).card = 4 := by decide

theorem four_double_count : ((proper 4).filter (fun q =>
    (FunctionalInequalities.Analysis.selected (fun _ : Fin 4 => ()) q).length = 2)).card = 6 := by decide

theorem four_triple_count : ((proper 4).filter (fun q =>
    (FunctionalInequalities.Analysis.selected (fun _ : Fin 4 => ()) q).length = 3)).card = 4 := by decide
end D74RawMasks

end MaskClients

-- ===== reviewer module InnerClients (D74-Raw-Assembly-Independent-20261009 (receipt f17f3495…)) =====
section InnerClients
set_option autoImplicit false
noncomputable section
open FunctionalInequalities.Analysis
open scoped RealInnerProductSpace ContDiff
namespace D74rInnerClients
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]

/-- No FD/Complete on E, no inner-product structure on D, and no symmetry of M. -/
theorem full_generic {f g : D → E} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (M : E →L[ℝ] E) (m : ℕ) (h : Fin m → D) (x : D) :
    iteratedFDeriv ℝ m (fun y => ⟪f y,M (g y)⟫) x h =
      ∑ q : Fin m → Bool,
        ⟪directional (selected h q) f x,M (directional (selected h (fun i => !(q i))) g x)⟫ :=
  iteratedFDeriv_inner_clm (E := E) (D := D) (f := f) (g := g) hf hg M m h x

theorem zero_order {f g : D → E} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (M : E →L[ℝ] E) (x : D) :
    iteratedFDeriv ℝ 0 (fun y => ⟪f y,M (g y)⟫) x (fun i : Fin 0 => Fin.elim0 i) = ⟪f x,M (g x)⟫ := by
  rw [iteratedFDeriv_inner_clm hf hg M]
  simp [selected,directional]

/-- D is the actual product with its max norm. E carries the Euclidean norm. -/
abbrev MaxDomain := ℝ × ℝ
abbrev Plane := EuclideanSpace ℝ (Fin 2)
def e0 : Plane := PiLp.single 2 0 1
def e1 : Plane := PiLp.single 2 1 1

def M : Plane →L[ℝ] Plane :=
  (innerSL ℝ e1).smulRight ((2:ℝ) • e0) + (innerSL ℝ e0).smulRight ((-3:ℝ) • e1)

lemma inner_coordinate_formula (a b : Plane) : ⟪a,b⟫ = a 0*b 0 + a 1*b 1 := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  change (∑ i : Fin 2, b i * star (a i)) = _
  rw [Fin.sum_univ_two]
  simp only [star_trivial]
  ring

lemma inner_e0 (x : Plane) : ⟪e0,x⟫ = x 0 := by
  rw [inner_coordinate_formula]
  simp [e0]
lemma inner_e1 (x : Plane) : ⟪e1,x⟫ = x 1 := by
  rw [inner_coordinate_formula]
  simp [e1]

lemma M_apply (x : Plane) : M x = (2*x 1) • e0 + (-3*x 0) • e1 := by
  change ⟪e1,x⟫ • ((2:ℝ) • e0) + ⟪e0,x⟫ • ((-3:ℝ) • e1) = _
  rw [inner_e1,inner_e0,smul_smul,smul_smul]
  congr 1 <;> congr 1 <;> ring

lemma M_coord0 (x : Plane) : M x 0 = 2*x 1 := by
  rw [M_apply]
  simp [e0,e1]
lemma M_coord1 (x : Plane) : M x 1 = -3*x 0 := by
  rw [M_apply]
  simp [e0,e1]

lemma offdiag_forward : ⟪e0,M e1⟫ = 2 := by
  rw [inner_e0,M_coord0]
  simp [e1]
lemma offdiag_reverse : ⟪e1,M e0⟫ = -3 := by
  rw [inner_e1,M_coord1]
  simp [e0]

lemma M_not_selfadjoint : ¬ IsSelfAdjoint M := by
  intro hs
  have h := hs.isSymmetric e1 e0
  change ⟪M e1,e0⟫ = ⟪e1,M e0⟫ at h
  rw [real_inner_comm,offdiag_forward,offdiag_reverse] at h
  norm_num at h

/-- Two maps into the plane have cross terms and unequal polynomial degrees. -/
def f (x : MaxDomain) : Plane := x.1^2 • e0 + x.2 • e1
def g (x : MaxDomain) : Plane := x.1 • e0 + (x.1*x.2) • e1
lemma f_smooth : ContDiff ℝ ∞ f :=
  ((contDiff_fst.pow 2).smul contDiff_const).add (contDiff_snd.smul contDiff_const)
lemma g_smooth : ContDiff ℝ ∞ g :=
  (contDiff_fst.smul contDiff_const).add ((contDiff_fst.mul contDiff_snd).smul contDiff_const)

lemma scalar_polynomial (x : MaxDomain) : ⟪f x,M (g x)⟫ = 2*x.1^3*x.2 - 3*x.1*x.2 := by
  rw [inner_coordinate_formula,M_coord0,M_coord1]
  simp [f,g,e0,e1]
  ring

theorem max_norm_domain_witness : ‖((2:ℝ),(-3:ℝ))‖ = 3 := by
  norm_num [Prod.norm_def]

theorem actual_polynomial_all_orders (m : ℕ) (h : Fin m → MaxDomain) (x : MaxDomain) :
    iteratedFDeriv ℝ m (fun y => ⟪f y,M (g y)⟫) x h =
      ∑ q : Fin m → Bool,
        ⟪directional (selected h q) f x,M (directional (selected h (fun i => !(q i))) g x)⟫ :=
  iteratedFDeriv_inner_clm f_smooth g_smooth M m h x

theorem actual_polynomial_zero_order :
    iteratedFDeriv ℝ 0 (fun y => ⟪f y,M (g y)⟫) ((1:ℝ),(-1:ℝ))
      (fun i : Fin 0 => Fin.elim0 i) = 1 := by
  rw [zero_order f_smooth g_smooth M,scalar_polynomial]
  norm_num

abbrev E0 := EuclideanSpace ℝ (Fin 0)
theorem zero_dimensional_all_orders (m : ℕ) (h : Fin m → MaxDomain) (x : MaxDomain)
    {a b : MaxDomain → E0} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (N : E0 →L[ℝ] E0) :
    iteratedFDeriv ℝ m (fun y => ⟪a y,N (b y)⟫) x h = 0 := by
  rw [iteratedFDeriv_inner_clm ha hb N]
  have hz : ∀ z : E0,z=0 := fun _ => Subsingleton.elim _ _
  simp [hz]
end D74rInnerClients

end
end InnerClients

-- ===== reviewer module GradientClients (D74-Raw-Assembly-Independent-20261009 (receipt f17f3495…)) =====
section GradientClients
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open FunctionalInequalities FunctionalInequalities.Analysis FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace ContDiff
namespace D74rGradientClients
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem full_generic (μ : ProbabilityMeasure E) (hc : IsCompact (μ : Measure E).support)
    (l : List E) :
    directional l (fun z : E => gradient (logLaplace (μ : Measure E)) z -
      gradient (logLaplace (μ : Measure E)) 0) 0 =
      if l = [] then 0 else cumulantVector (μ : Measure E) l :=
  directional_centeredGradient_logLaplace_zero_of_compact (E := E) (μ := μ) (hc := hc) (l := l)

namespace Uniform
open D74rUniformLaw

def v (z : ℝ) : ℝ := gradient (logLaplace (law : Measure ℝ)) z -
  gradient (logLaplace (law : Measure ℝ)) 0

theorem actual_all_lists (l : List ℝ) : directional l v 0 =
    if l = [] then 0 else cumulantVector (law : Measure ℝ) l :=
  directional_centeredGradient_logLaplace_zero_of_compact law law_compact l

theorem actual_gradient_mean : gradient (logLaplace (law : Measure ℝ)) 0 = 1/2 := by
  rw [gradient_logLaplace_zero_of_compact law law_compact, law_mean]

theorem actual_empty_vector : cumulantVector (law : Measure ℝ) [] = 1/2 := by
  have h := cumulantVector_inner (law : Measure ℝ) [] 1
  rw [Real.inner_apply] at h
  change cumulantVector (law : Measure ℝ) [] * 1 =
    iteratedFDeriv ℝ 1 (logLaplace (law : Measure ℝ)) 0 (Fin.snoc (fun i => [].get i) 1) at h
  rw [iteratedFDeriv_one_apply] at h
  change cumulantVector (law : Measure ℝ) [] * 1 =
    fderiv ℝ (logLaplace (law : Measure ℝ)) 0 1 at h
  rw [fderiv_logLaplace_zero_apply (hexp := compact_support_integrable_exp _ law_compact)] at h
  simpa only [Real.inner_apply, one_mul, mul_one, law_mean] using h

theorem actual_empty_directional : directional [] v 0 = 0 := by
  rw [actual_all_lists]
  simp

theorem empty_is_not_cumulant_vector : directional [] v 0 ≠ cumulantVector (law : Measure ℝ) [] := by
  rw [actual_empty_directional,actual_empty_vector]
  norm_num

theorem actual_singleton_vector (h : ℝ) : cumulantVector (law : Measure ℝ) [h] = h/12 := by
  have hc := cumulantVector_inner (law : Measure ℝ) [h] 1
  have he : Fin.snoc (fun i => ([h]:List ℝ).get i) (1:ℝ) = ![h,1] := by
    funext i
    fin_cases i <;> rfl
  rw [he] at hc
  rw [Real.inner_apply] at hc
  change cumulantVector (law : Measure ℝ) [h] * 1 = cumulant (law : Measure ℝ) 2 ![h,1] at hc
  rw [cumulant_two_eq_covariance_of_integrable_exp (μ := (law : Measure ℝ)) one_pos
    (compact_support_integrable_exp _ law_compact 1),law_covariance] at hc
  simpa [Real.inner_apply,div_eq_mul_inv,mul_comm] using hc

theorem actual_singleton (h : ℝ) : directional [h] v 0 = h/12 := by
  rw [actual_all_lists]
  simp only [List.cons_ne_nil,↓reduceIte]
  exact actual_singleton_vector h

theorem actual_signed_singleton : directional [(-6:ℝ)] v 0 = -1/2 := by
  rw [actual_singleton]
  norm_num

theorem actual_higher_signed : ⟪directional ([1,-2,3]:List ℝ) v 0,(4:ℝ)⟫ =
    cumulant (law : Measure ℝ) 4 ![1,-2,3,4] := by
  rw [actual_all_lists]
  simp only [List.cons_ne_nil,↓reduceIte,cumulantVector_inner]
  congr 1
  funext i
  fin_cases i <;> rfl
end Uniform

namespace Skew
open D74rSkewLaw
def law : ProbabilityMeasure ℝ := ⟨twoPt,isProbabilityMeasure_twoPt⟩
lemma law_compact : IsCompact (law : Measure ℝ).support := by
  have hsub : (law : Measure ℝ).support ⊆ ({(2:ℝ),-1/2}:Set ℝ) := by
    apply Measure.support_subset_of_isClosed (isClosed_singleton.union isClosed_singleton)
    rw [mem_ae_iff]
    simp [law,twoPt]
  exact (Set.toFinite ({(2:ℝ),-1/2}:Set ℝ)).isCompact.of_isClosed_subset
    (law : Measure ℝ).isClosed_support hsub

def v (z : ℝ) : ℝ := gradient (logLaplace (law : Measure ℝ)) z -
  gradient (logLaplace (law : Measure ℝ)) 0

theorem actual_all_lists (l : List ℝ) : directional l v 0 =
    if l = [] then 0 else cumulantVector (law : Measure ℝ) l :=
  directional_centeredGradient_logLaplace_zero_of_compact law law_compact l

theorem actual_third_vector : cumulantVector (law : Measure ℝ) [1,1] = 3/2 := by
  have h := cumulantVector_inner (law : Measure ℝ) [1,1] 1
  have he : Fin.snoc (fun i => ([1,1]:List ℝ).get i) (1:ℝ) = ![1,1,1] := by
    funext i
    fin_cases i <;> rfl
  rw [he] at h
  rw [Real.inner_apply] at h
  change cumulantVector (law : Measure ℝ) [1,1] * 1 = cumulant twoPt 3 ![1,1,1] at h
  simpa only [mul_one,cumulant_three_twoPt] using h

theorem actual_nonzero_third : directional ([1,1]:List ℝ) v 0 = 3/2 := by
  rw [actual_all_lists]
  simp only [List.cons_ne_nil,↓reduceIte]
  exact actual_third_vector

theorem actual_nonzero : directional ([1,1]:List ℝ) v 0 ≠ 0 := by
  rw [actual_nonzero_third]
  norm_num

theorem actual_signed_third : directional ([-2,3]:List ℝ) v 0 = -9 := by
  rw [actual_all_lists]
  simp only [List.cons_ne_nil,↓reduceIte]
  have h := cumulantVector_inner (law : Measure ℝ) [-2,3] 1
  have he : Fin.snoc (fun i => ([-2,3]:List ℝ).get i) (1:ℝ) = ![-2,3,1] := by
    funext i
    fin_cases i <;> rfl
  rw [he] at h
  rw [Real.inner_apply] at h
  change cumulantVector (law : Measure ℝ) [-2,3] * 1 = cumulant twoPt 3 ![-2,3,1] at h
  have : IsProbabilityMeasure twoPt := isProbabilityMeasure_twoPt
  rw [cumulant_three_eq_integral twoPt integrable_exp_mul_norm_twoPt centered_twoPt,integral_twoPt] at h
  norm_num [Real.inner_apply] at h
  exact h
end Skew

namespace Dirac

def law : ProbabilityMeasure ℝ := ⟨Measure.dirac 2,inferInstance⟩
lemma law_compact : IsCompact (law : Measure ℝ).support := by
  have hsub : (law : Measure ℝ).support ⊆ ({(2:ℝ)}:Set ℝ) := by
    apply Measure.support_subset_of_isClosed isClosed_singleton
    rw [mem_ae_iff]
    simp [law]
  exact isCompact_singleton.of_isClosed_subset (law : Measure ℝ).isClosed_support hsub

theorem actual_logLaplace : logLaplace (law : Measure ℝ) = fun z : ℝ => 2*z := by
  funext z
  simp [logLaplace,law,mul_comm]

theorem actual_gradient (z : ℝ) : gradient (logLaplace (law : Measure ℝ)) z = 2 := by
  rw [actual_logLaplace,gradient_eq_deriv']
  simp

def v (z : ℝ) : ℝ := gradient (logLaplace (law : Measure ℝ)) z -
  gradient (logLaplace (law : Measure ℝ)) 0

theorem actual_v_zero : v = fun _ => 0 := by
  funext z
  simp only [v,actual_gradient,sub_self]

lemma directional_zero (l : List ℝ) (x : ℝ) : directional l (fun _ : ℝ => (0:ℝ)) x = 0 := by
  induction l generalizing x with
  | nil => rfl
  | cons h l ih =>
    change fderiv ℝ (directional l (fun _ : ℝ => (0:ℝ))) x h = 0
    have he : directional l (fun _ : ℝ => (0:ℝ)) = fun _ => 0 := funext ih
    rw [he,fderiv_fun_const]
    rfl

theorem actual_all_lists_zero (l : List ℝ) : directional l v 0 = 0 := by
  rw [actual_v_zero]
  exact directional_zero l 0

theorem actual_positive_vectors_zero (l : List ℝ) (hl : l ≠ []) :
    cumulantVector (law : Measure ℝ) l = 0 := by
  have h := directional_centeredGradient_logLaplace_zero_of_compact law law_compact l
  change directional l v 0 = _ at h
  rw [actual_all_lists_zero] at h
  simpa only [hl,↓reduceIte] using h.symm

theorem actual_empty_vector : cumulantVector (law : Measure ℝ) [] = 2 := by
  have h := cumulantVector_inner (law : Measure ℝ) [] 1
  rw [Real.inner_apply] at h
  change cumulantVector (law : Measure ℝ) [] * 1 =
    iteratedFDeriv ℝ 1 (logLaplace (law : Measure ℝ)) 0 (Fin.snoc (fun i => [].get i) 1) at h
  rw [iteratedFDeriv_one_apply] at h
  change cumulantVector (law : Measure ℝ) [] * 1 =
    fderiv ℝ (logLaplace (law : Measure ℝ)) 0 1 at h
  rw [fderiv_logLaplace_zero_apply (hexp := compact_support_integrable_exp _ law_compact)] at h
  simpa [law] using h

theorem actual_covariance_zero : Covariance.operator (law : Measure ℝ) = 0 := by
  have h := fderiv_centeredGradient_logLaplace_zero_of_compact law law_compact
  change fderiv ℝ v 0 = Covariance.operator (law : Measure ℝ) at h
  rw [actual_v_zero,fderiv_fun_const] at h
  exact h.symm
end Dirac

namespace Zero
abbrev E0 := EuclideanSpace ℝ (Fin 0)
def law : ProbabilityMeasure E0 := ⟨Measure.dirac 0,inferInstance⟩
lemma law_compact : IsCompact (law : Measure E0).support :=
  isCompact_univ.of_isClosed_subset (law : Measure E0).isClosed_support (subset_univ _)

theorem actual_all_lists (l : List E0) :
    directional l (fun z : E0 => gradient (logLaplace (law : Measure E0)) z -
      gradient (logLaplace (law : Measure E0)) 0) 0 = 0 :=
  (directional_centeredGradient_logLaplace_zero_of_compact law law_compact l).trans (Subsingleton.elim _ _)

theorem actual_all_vectors_zero (l : List E0) : cumulantVector (law : Measure E0) l = 0 :=
  Subsingleton.elim _ _
end Zero
end D74rGradientClients

end
end GradientClients

-- ===== reviewer module RawModels (D74-Raw-Assembly-Independent-20261009 (receipt f17f3495…)) =====
section RawModels
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open FunctionalInequalities FunctionalInequalities.Analysis FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace ContDiff
namespace D74RawModels
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def Gamma (μ : ProbabilityMeasure E) (M : E →L[ℝ] E) (z : E) : ℝ :=
  ⟪gradient (logLaplace (μ : Measure E)) z - gradient (logLaplace (μ : Measure E)) 0,
    M (gradient (logLaplace (μ : Measure E)) z - gradient (logLaplace (μ : Measure E)) 0)⟫

theorem raw (μ : ProbabilityMeasure E) (hc : IsCompact (μ : Measure E).support)
    (M : E →L[ℝ] E) (m : ℕ) (h : Fin m → E) :
    iteratedFDeriv ℝ m (Gamma μ M) 0 h =
      ∑ q ∈ D74RawMasks.proper m,
        ⟪cumulantVector (μ : Measure E) (selected h q),
          M (cumulantVector (μ : Measure E) (selected h (fun i => !(q i))))⟫ :=
  iteratedFDeriv_inner_centeredGradient_zero_of_compact μ hc M m h

theorem zero_order (μ : ProbabilityMeasure E) (hc : IsCompact (μ : Measure E).support)
    (M : E →L[ℝ] E) (h : Fin 0 → E) : iteratedFDeriv ℝ 0 (Gamma μ M) 0 h = 0 := by
  rw [raw μ hc M,D74RawMasks.zero]
  simp

theorem one_order (μ : ProbabilityMeasure E) (hc : IsCompact (μ : Measure E).support)
    (M : E →L[ℝ] E) (h : Fin 1 → E) : iteratedFDeriv ℝ 1 (Gamma μ M) 0 h = 0 := by
  rw [raw μ hc M,D74RawMasks.one]
  simp

/-- At order2 only the two distinct inherited singleton allocations survive. -/
theorem second_order (μ : ProbabilityMeasure E) (hc : IsCompact (μ : Measure E).support)
    (M : E →L[ℝ] E) (a b : E) : iteratedFDeriv ℝ 2 (Gamma μ M) 0 ![a,b] =
    ⟪cumulantVector (μ : Measure E) [a],M (cumulantVector (μ : Measure E) [b])⟫ +
    ⟪cumulantVector (μ : Measure E) [b],M (cumulantVector (μ : Measure E) [a])⟫ := by
  rw [raw μ hc M,D74RawMasks.two]
  have hne : (![true,false] : Fin 2 → Bool) ≠ ![false,true] := by
    intro he
    have hh := congrFun he 0
    cases hh
  simp [selected,hne,Fin.tail]

namespace Uniform
open D74rUniformLaw

theorem mean_nonzero : gradient (logLaplace (law : Measure ℝ)) 0 = 1/2 :=
  D74rGradientClients.Uniform.actual_gradient_mean

theorem m0 (M : ℝ →L[ℝ] ℝ) (h : Fin 0 → ℝ) :
    iteratedFDeriv ℝ 0 (Gamma law M) 0 h = 0 := zero_order law law_compact M h

theorem m1 (M : ℝ →L[ℝ] ℝ) (h : Fin 1 → ℝ) :
    iteratedFDeriv ℝ 1 (Gamma law M) 0 h = 0 := one_order law law_compact M h

lemma cov_inverse : Ring.inverse (Covariance.operator (law : Measure ℝ)) =
    (12:ℝ) • ContinuousLinearMap.id ℝ ℝ := by
  let u : (ℝ →L[ℝ] ℝ)ˣ :=
    ⟨(1/12:ℝ) • ContinuousLinearMap.id ℝ ℝ,
      (12:ℝ) • ContinuousLinearMap.id ℝ ℝ,by
        apply ContinuousLinearMap.ext
        intro x
        change (1/12:ℝ)*(12*x)=x
        ring,by
        apply ContinuousLinearMap.ext
        intro x
        change (12:ℝ)*((1/12)*x)=x
        ring⟩
  rw [law_covariance]
  change Ring.inverse (u : ℝ →L[ℝ] ℝ) = _
  rw [Ring.inverse_unit]
  rfl

theorem inverse_cov_m2 (a b : ℝ) :
    iteratedFDeriv ℝ 2 (Gamma law (Ring.inverse (Covariance.operator (law : Measure ℝ)))) 0 ![a,b] =
      2*cumulant (law : Measure ℝ) 2 ![a,b] := by
  rw [second_order law law_compact,cov_inverse,
    D74rGradientClients.Uniform.actual_singleton_vector,
    D74rGradientClients.Uniform.actual_singleton_vector,
    cumulant_two_eq_covariance_of_integrable_exp (μ := (law : Measure ℝ)) one_pos
      (compact_support_integrable_exp _ law_compact 1),law_covariance]
  simp only [Real.inner_apply,smul_apply,smul_eq_mul,ContinuousLinearMap.id_apply]
  ring

theorem m4_literal (h : Fin 4 → ℝ) :
    iteratedFDeriv ℝ 4 (Gamma law (Ring.inverse (Covariance.operator (law : Measure ℝ)))) 0 h =
      ∑ q ∈ D74RawMasks.proper 4,
        ⟪cumulantVector (law : Measure ℝ) (selected h q),
          (Ring.inverse (Covariance.operator (law : Measure ℝ)))
            (cumulantVector (law : Measure ℝ) (selected h (fun i => !(q i))))⟫ :=
  raw law law_compact _ 4 h
end Uniform

namespace Skew
open D74rSkewLaw D74rGradientClients.Skew

lemma law_isotropic : KLS.Isotropic law := by
  have h2 : MemLp id 2 (law : Measure ℝ) :=
    (memLp_two_iff_integrable_sq continuous_id.aestronglyMeasurable).2 (integrable_twoPt _)
  apply KLS.isotropic_of_moments law h2
  · change (∫ x,x ∂twoPt)=0
    simpa using centered_twoPt 1
  · intro u v
    exact isotropic_twoPt u v

lemma singleton_vector : cumulantVector (law : Measure ℝ) [1] = 1 := by
  have h := cumulantVector_inner (law : Measure ℝ) [1] 1
  have he : Fin.snoc (fun i => ([1]:List ℝ).get i) (1:ℝ) = ![1,1] := by
    funext i
    fin_cases i <;> rfl
  rw [he] at h
  change ⟪cumulantVector (law : Measure ℝ) [1],1⟫ = cumulant (law : Measure ℝ) 2 ![1,1] at h
  rw [cumulant_two_eq_covariance_of_integrable_exp (μ := (law : Measure ℝ)) one_pos
    (compact_support_integrable_exp _ law_compact 1),law_isotropic.covariance_identity] at h
  simpa only [Real.inner_apply,mul_one,ContinuousLinearMap.id_apply,one_mul] using h

theorem inverse_cov_m3 :
    iteratedFDeriv ℝ 3 (Gamma law (Ring.inverse (Covariance.operator (law : Measure ℝ)))) 0
      (fun _ : Fin 3 => (1:ℝ)) = 6*cumulant (law : Measure ℝ) 3 ![1,1,1] := by
  have hi : Ring.inverse (ContinuousLinearMap.id ℝ ℝ) = ContinuousLinearMap.id ℝ ℝ := by
    change Ring.inverse (1 : ℝ →L[ℝ] ℝ) = 1
    exact Ring.inverse_one (ℝ →L[ℝ] ℝ)
  rw [raw law law_compact,D74RawMasks.three,law_isotropic.covariance_identity,hi]
  change _ = 6*cumulant twoPt 3 ![1,1,1]
  rw [cumulant_three_twoPt]
  norm_num [selected,Fin.tail,Matrix.cons_val_two,singleton_vector,D74rGradientClients.Skew.actual_third_vector,
    Real.inner_apply]

theorem m3_nonzero :
    iteratedFDeriv ℝ 3 (Gamma law (Ring.inverse (Covariance.operator (law : Measure ℝ)))) 0
      (fun _ : Fin 3 => (1:ℝ)) = 9 := by
  rw [inverse_cov_m3]
  change 6*cumulant twoPt 3 ![1,1,1]=9
  rw [cumulant_three_twoPt]
  norm_num
end Skew

namespace Zero
open D74rGradientClients.Zero

theorem all_orders (m : ℕ) (h : Fin m → E0) (M : E0 →L[ℝ] E0) :
    iteratedFDeriv ℝ m (Gamma law M) 0 h = 0 := by
  rw [raw law law_compact M]
  have hz : ∀ z : E0,z=0 := fun _ => Subsingleton.elim _ _
  simp [hz]

theorem positive_arity_nonempty_zero_selection :
    selected (fun _ : Fin 4 => (0:E0)) ![true,false,true,false] = [0,0] := rfl

theorem positive_arity_selection_not_nil :
    selected (fun _ : Fin 4 => (0:E0)) ![true,false,true,false] ≠ [] := by
  intro he
  have hall := (selected_eq_nil_iff _ _).1 he 0
  cases hall

theorem four_order_actual :
    iteratedFDeriv ℝ 4 (Gamma law (Ring.inverse (Covariance.operator (law : Measure E0)))) 0
      (fun _ => (0:E0)) = 0 := all_orders 4 _ _
end Zero
end D74RawModels

end
end RawModels

-- ===== reviewer module PlaneModels (D74-Raw-Assembly-Independent-20261009 (receipt f17f3495…)) =====
section PlaneModels
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

lemma law_memLp : MemLp id 2 (μ : Measure E) := by
  apply (memLp_two_iff_integrable_sq_norm continuous_id.aestronglyMeasurable).2
  have hi (x : E) : Integrable (fun z : E => ‖id z‖^2) (ENNReal.ofReal (1/4) • Measure.dirac x) :=
    (integrable_dirac (by simp)).smul_measure (by norm_num)
  exact ((hi _).add_measure (hi _) |>.add_measure (hi _)).add_measure (hi _)

lemma law_isotropic : KLS.Isotropic μ := by
  apply KLS.isotropic_of_moments μ law_memLp
  · rw [integral_μ]
    ext i
    fin_cases i <;> norm_num [point]
  · intro u v
    rw [integral_μ]
    simp only [smul_eq_mul,PiLp.inner_apply,Fin.sum_univ_two,Real.inner_apply]
    norm_num [point]
    ring

lemma singleton_vector (h : E) : cumulantVector (μ : Measure E) [h] = h := by
  apply ext_inner_right ℝ
  intro w
  rw [cumulantVector_inner]
  have he : Fin.snoc (fun i => ([h]:List E).get i) w = ![h,w] := by
    funext i
    fin_cases i <;> rfl
  rw [he]
  change cumulant (μ : Measure E) 2 ![h,w] = _
  rw [cumulant_two_eq_covariance_of_integrable_exp (μ := (μ : Measure E)) one_pos
    (compact_support_integrable_exp _ compact_μ 1),law_isotropic.covariance_identity]
  rfl

abbrev M := D74rInnerClients.M
lemma actual_M_nonsymmetric : ¬ IsSelfAdjoint M := D74rInnerClients.M_not_selfadjoint

def a : E := point 2 3
def c : E := point (-1) 4

lemma first_allocation : ⟪a,M c⟫ = 25 := by
  rw [D74rInnerClients.inner_coordinate_formula,
    D74rInnerClients.M_coord0,D74rInnerClients.M_coord1]
  norm_num [a,c,point]
lemma second_allocation : ⟪c,M a⟫ = -30 := by
  rw [D74rInnerClients.inner_coordinate_formula,
    D74rInnerClients.M_coord0,D74rInnerClients.M_coord1]
  norm_num [a,c,point]

theorem actual_signed_mixed_second :
    iteratedFDeriv ℝ 2 (D74RawModels.Gamma μ M) 0 ![a,c] = -5 := by
  rw [D74RawModels.second_order μ compact_μ M,singleton_vector,singleton_vector,
    first_allocation,second_allocation]
  norm_num

theorem actual_all_orders (m : ℕ) (h : Fin m → E) :
    iteratedFDeriv ℝ m (D74RawModels.Gamma μ M) 0 h =
      ∑ q ∈ D74RawMasks.proper m,
        ⟪cumulantVector (μ : Measure E) (selected h q),
          M (cumulantVector (μ : Measure E) (selected h (fun i => !(q i))))⟫ :=
  D74RawModels.raw μ compact_μ M m h
end D74RawPlane

end
end PlaneModels

#print axioms D74rUniformLaw.law_compact
#print axioms D74rUniformLaw.law_memLp
#print axioms D74rUniformLaw.law_mean
#print axioms D74rUniformLaw.law_variance
#print axioms D74rUniformLaw.law_covariance
#print axioms D74rSkewLaw.integrable_twoPt
#print axioms D74rSkewLaw.integral_twoPt
#print axioms D74rSkewLaw.isProbabilityMeasure_twoPt
#print axioms D74rSkewLaw.centered_twoPt
#print axioms D74rSkewLaw.isotropic_twoPt
#print axioms D74rSkewLaw.integrable_exp_mul_norm_twoPt
#print axioms D74rSkewLaw.cumulant_three_twoPt
#print axioms D74RawMasks.zero
#print axioms D74RawMasks.one
#print axioms D74RawMasks.two
#print axioms D74RawMasks.three
#print axioms D74RawMasks.four_card
#print axioms D74RawMasks.four_single_count
#print axioms D74RawMasks.four_double_count
#print axioms D74RawMasks.four_triple_count
#print axioms D74rInnerClients.full_generic
#print axioms D74rInnerClients.zero_order
#print axioms D74rInnerClients.inner_coordinate_formula
#print axioms D74rInnerClients.inner_e0
#print axioms D74rInnerClients.inner_e1
#print axioms D74rInnerClients.M_apply
#print axioms D74rInnerClients.M_coord0
#print axioms D74rInnerClients.M_coord1
#print axioms D74rInnerClients.offdiag_forward
#print axioms D74rInnerClients.offdiag_reverse
#print axioms D74rInnerClients.M_not_selfadjoint
#print axioms D74rInnerClients.f_smooth
#print axioms D74rInnerClients.g_smooth
#print axioms D74rInnerClients.scalar_polynomial
#print axioms D74rInnerClients.max_norm_domain_witness
#print axioms D74rInnerClients.actual_polynomial_all_orders
#print axioms D74rInnerClients.actual_polynomial_zero_order
#print axioms D74rInnerClients.zero_dimensional_all_orders
#print axioms D74rGradientClients.full_generic
#print axioms D74rGradientClients.Uniform.actual_all_lists
#print axioms D74rGradientClients.Uniform.actual_gradient_mean
#print axioms D74rGradientClients.Uniform.actual_empty_vector
#print axioms D74rGradientClients.Uniform.actual_empty_directional
#print axioms D74rGradientClients.Uniform.empty_is_not_cumulant_vector
#print axioms D74rGradientClients.Uniform.actual_singleton_vector
#print axioms D74rGradientClients.Uniform.actual_singleton
#print axioms D74rGradientClients.Uniform.actual_signed_singleton
#print axioms D74rGradientClients.Uniform.actual_higher_signed
#print axioms D74rGradientClients.Skew.law_compact
#print axioms D74rGradientClients.Skew.actual_all_lists
#print axioms D74rGradientClients.Skew.actual_third_vector
#print axioms D74rGradientClients.Skew.actual_nonzero_third
#print axioms D74rGradientClients.Skew.actual_nonzero
#print axioms D74rGradientClients.Skew.actual_signed_third
#print axioms D74rGradientClients.Dirac.law_compact
#print axioms D74rGradientClients.Dirac.actual_logLaplace
#print axioms D74rGradientClients.Dirac.actual_gradient
#print axioms D74rGradientClients.Dirac.actual_v_zero
#print axioms D74rGradientClients.Dirac.directional_zero
#print axioms D74rGradientClients.Dirac.actual_all_lists_zero
#print axioms D74rGradientClients.Dirac.actual_positive_vectors_zero
#print axioms D74rGradientClients.Dirac.actual_empty_vector
#print axioms D74rGradientClients.Dirac.actual_covariance_zero
#print axioms D74rGradientClients.Zero.law_compact
#print axioms D74rGradientClients.Zero.actual_all_lists
#print axioms D74rGradientClients.Zero.actual_all_vectors_zero
#print axioms D74RawModels.raw
#print axioms D74RawModels.zero_order
#print axioms D74RawModels.one_order
#print axioms D74RawModels.second_order
#print axioms D74RawModels.Uniform.mean_nonzero
#print axioms D74RawModels.Uniform.m0
#print axioms D74RawModels.Uniform.m1
#print axioms D74RawModels.Uniform.cov_inverse
#print axioms D74RawModels.Uniform.inverse_cov_m2
#print axioms D74RawModels.Uniform.m4_literal
#print axioms D74RawModels.Skew.law_isotropic
#print axioms D74RawModels.Skew.singleton_vector
#print axioms D74RawModels.Skew.inverse_cov_m3
#print axioms D74RawModels.Skew.m3_nonzero
#print axioms D74RawModels.Zero.all_orders
#print axioms D74RawModels.Zero.positive_arity_nonempty_zero_selection
#print axioms D74RawModels.Zero.positive_arity_selection_not_nil
#print axioms D74RawModels.Zero.four_order_actual
#print axioms D74RawPlane.integral_μ
#print axioms D74RawPlane.support_subset
#print axioms D74RawPlane.compact_μ
#print axioms D74RawPlane.inner_point
#print axioms D74RawPlane.law_memLp
#print axioms D74RawPlane.law_isotropic
#print axioms D74RawPlane.singleton_vector
#print axioms D74RawPlane.actual_M_nonsymmetric
#print axioms D74RawPlane.first_allocation
#print axioms D74RawPlane.second_allocation
#print axioms D74RawPlane.actual_signed_mixed_second
#print axioms D74RawPlane.actual_all_orders
#print axioms FunctionalInequalities.Analysis.selected_eq_nil_iff
#print axioms FunctionalInequalities.Analysis.iteratedFDeriv_inner_clm
#print axioms FunctionalInequalities.Analysis.BakryEmery.directional_centeredGradient_logLaplace_zero_of_compact
#print axioms FunctionalInequalities.Analysis.BakryEmery.iteratedFDeriv_inner_centeredGradient_zero_of_compact
