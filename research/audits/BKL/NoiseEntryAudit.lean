import FunctionalInequalities.KLS.BKL.Posterior.Covariance
import FunctionalInequalities.Probability.CoordinateThirdMoment
import FunctionalInequalities.KLS.BKL.Posterior.Noise
/-! Independent audit clients for the (69) entry chain (Analysis/OperatorCoordinates.lean section EuclideanCoordinates, Probability/Moments.lean section CoordinateMonomials, Probability/CoordinateThirdMoment.lean, Probability/Posterior/CompactDomain.lean, KLS/BKL/PosteriorDomain.lean section NoiseEntries). Merged verbatim from the reviewer receipt `B69-Full-Chain-Independent-20261009 (receipt b467cf7a…)` (modules
ABCClients, ChainClients, PosteriorClients), re-pointed from the raw `Candidate*` modules to the production owners; the namespace map Analysis → Probability of the moved B69 lemmas is applied by one added `open FunctionalInequalities.Probability` after each `open … FunctionalInequalities.Analysis` line; contracts/axiom-enumeration tooling stays in the receipt. -/

-- ===== reviewer module ABCClients (B69-Full-Chain-Independent-20261009 (receipt b467cf7a…)) =====
set_option autoImplicit false
noncomputable section
open MeasureTheory FunctionalInequalities.Analysis
open FunctionalInequalities.Probability
open scoped RealInnerProductSpace
namespace B69Clients
abbrev E2 := EuclideanSpace ℝ (Fin 2)
abbrev E0 := EuclideanSpace ℝ (Fin 0)
def e0 : E2 := WithLp.toLp 2 ![(1 : ℝ), (0 : ℝ)]
def e1 : E2 := WithLp.toLp 2 ![(0 : ℝ), (1 : ℝ)]
def v : E2 := WithLp.toLp 2 ![(2 : ℝ), (-1 : ℝ)]
def rankOne (u w : E2) : E2 →L[ℝ] E2 := (InnerProductSpace.toDual ℝ E2 w).smulRight u
def nonsym : E2 →L[ℝ] E2 := -rankOne e0 e0 + rankOne (2 • e0 + 3 • e1) e1
def coupled : E2 →L[ℝ] E2 := -rankOne (e0 - e1) (e0 - e1)

theorem coordinate_generic {n : ℕ} (T : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) (j : Fin n) :
    (T x) j = ∑ r : Fin n, operatorMatrix (EuclideanSpace.basisFun (Fin n) ℝ) T j r * x r :=
  euclidean_clm_apply_eq_sum_operatorMatrix T x j

theorem pairing_generic {n : ℕ} (T : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hT : IsSelfAdjoint T) (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    ⟪T (EuclideanSpace.basisFun (Fin n) ℝ i), x⟫ = (T x) i :=
  euclidean_inner_selfAdjoint_basisFun T hT x i

theorem cubic_generic {n : ℕ} {ν : Measure (EuclideanSpace ℝ (Fin n))} [IsFiniteMeasure ν]
    (a : EuclideanSpace ℝ (Fin n)) (R : ℝ) (hR : ∀ᵐ x ∂ν, ‖x - a‖ ≤ R) (p q r : Fin n) :
    Integrable (fun x => (x - a) p * (x - a) q * (x - a) r) ν :=
  integrable_coord_mul_coord_mul_coord_of_ae_norm_sub_le a R hR p q r

theorem nonsym_values : (nonsym v) 0 = -4 ∧ (nonsym v) 1 = -3 := by
  norm_num [nonsym, rankOne, ContinuousLinearMap.smulRight_apply, InnerProductSpace.toDual_apply_apply,
    PiLp.inner_apply, Fin.sum_univ_two, Real.inner_apply, e0, e1, v]

theorem nonsym_witness : ⟪nonsym e1, e0⟫ = 2 ∧ ⟪e1, nonsym e0⟫ = 0 := by
  simp only [nonsym, rankOne, add_apply, neg_apply,
    ContinuousLinearMap.smulRight_apply, InnerProductSpace.toDual_apply_apply, PiLp.inner_apply,
    Fin.sum_univ_two, Real.inner_apply]
  norm_num [e0, e1]

theorem nonsym_not_selfAdjoint : ¬ IsSelfAdjoint nonsym := by
  intro h
  have hs := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp h) e1 e0
  change ⟪nonsym e1, e0⟫ = ⟪e1, nonsym e0⟫ at hs
  rw [nonsym_witness.1, nonsym_witness.2] at hs
  norm_num at hs

theorem nonsym_actual_rows :
    (∑ r : Fin 2, operatorMatrix (EuclideanSpace.basisFun (Fin 2) ℝ) nonsym 0 r * v r) = -4 ∧
    (∑ r : Fin 2, operatorMatrix (EuclideanSpace.basisFun (Fin 2) ℝ) nonsym 1 r * v r) = -3 := by
  rw [← coordinate_generic, ← coordinate_generic]
  exact nonsym_values

theorem coupled_selfAdjoint : IsSelfAdjoint coupled := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  change ⟪coupled x, y⟫ = ⟪x, coupled y⟫
  simp [coupled, rankOne, ContinuousLinearMap.smulRight_apply, InnerProductSpace.toDual_apply_apply,
    inner_smul_left, inner_smul_right, real_inner_comm, inner_sub_right, inner_sub_left]
  all_goals ring

theorem coupled_values : (coupled v) 0 = -3 ∧ (coupled v) 1 = 3 := by
  norm_num [coupled, rankOne, ContinuousLinearMap.smulRight_apply, InnerProductSpace.toDual_apply_apply,
    PiLp.inner_apply, Fin.sum_univ_two, Real.inner_apply, e0, e1, v]

theorem coupled_signed_offdiagonal : ⟪coupled e0, e0⟫ = -1 ∧ ⟪coupled e0, e1⟫ = 1 := by
  simp only [coupled, rankOne, neg_apply, ContinuousLinearMap.smulRight_apply,
    InnerProductSpace.toDual_apply_apply, PiLp.inner_apply, Fin.sum_univ_two, Real.inner_apply]
  norm_num [e0, e1]

theorem coupled_nontrivial_kernel : coupled (e0 + e1) = 0 ∧ (e0 + e1 : E2) ≠ 0 := by
  constructor
  · ext i
    fin_cases i <;> norm_num [coupled, rankOne, ContinuousLinearMap.smulRight_apply,
      InnerProductSpace.toDual_apply_apply, PiLp.inner_apply, Fin.sum_univ_two, Real.inner_apply, e0, e1]
  · intro h
    have hh := congrArg (fun x : E2 => x (0 : Fin 2)) h
    norm_num [e0, e1] at hh

theorem coupled_actual_pairings :
    ⟪coupled (EuclideanSpace.basisFun (Fin 2) ℝ 0), v⟫ = -3 ∧
    ⟪coupled (EuclideanSpace.basisFun (Fin 2) ℝ 1), v⟫ = 3 := by
  rw [pairing_generic coupled coupled_selfAdjoint, pairing_generic coupled coupled_selfAdjoint]
  exact coupled_values

def center : E2 := WithLp.toLp 2 ![(1 : ℝ), (-2 : ℝ)]
def point : E2 := WithLp.toLp 2 ![(3 : ℝ), (-1 : ℝ)]
def finiteLaw : Measure E2 := (2 : ENNReal) • Measure.dirac point + (3 : ENNReal) • Measure.dirac 0
instance finiteLaw_isFinite : IsFiniteMeasure finiteLaw := by
  constructor
  simp [finiteLaw]

theorem finiteLaw_mass : finiteLaw.real Set.univ = 5 := by
  norm_num [finiteLaw, measureReal_def, ENNReal.toReal_add]

private theorem point_bound : ‖point - center‖ ≤ 3 := by
  have hs : ‖point - center‖ ^ 2 ≤ (3 : ℝ) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    norm_num [point, center, Fin.sum_univ_two]
  nlinarith [norm_nonneg (point - center)]
private theorem zero_bound : ‖(0 : E2) - center‖ ≤ 3 := by
  have hs : ‖(0 : E2) - center‖ ^ 2 ≤ (3 : ℝ) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    norm_num [center, Fin.sum_univ_two]
  nlinarith [norm_nonneg ((0 : E2) - center)]

theorem actual_ae_ball : ∀ᵐ x ∂finiteLaw, ‖x - center‖ ≤ 3 := by
  have hz : ‖center‖ ≤ 3 := by simpa using zero_bound
  rw [ae_iff]
  simp [finiteLaw, point_bound, hz]

theorem bound_is_not_global : ¬ ∀ x : E2, ‖x - center‖ ≤ 3 := by
  intro h
  have hh := h (center + 4 • e0)
  have hs : ‖(center + 4 • e0) - center‖ ^ 2 = (16 : ℝ) := by
    rw [EuclideanSpace.real_norm_sq_eq]
    norm_num [e0, Fin.sum_univ_two]
  nlinarith [norm_nonneg ((center + 4 • e0) - center)]

theorem actual_finite_nonprob_cubics (p q r : Fin 2) :
    Integrable (fun x => (x - center) p * (x - center) q * (x - center) r) finiteLaw :=
  integrable_coord_mul_coord_mul_coord_of_ae_norm_sub_le center 3 actual_ae_ball p q r

theorem actual_center_nonzero : center ≠ 0 := by
  intro h
  have hh := congrArg (fun x : E2 => x (0 : Fin 2)) h
  norm_num [center] at hh

theorem cubic_integral_fourteen :
    (∫ x, (x - center) 0 * (x - center) 0 * (x - center) 1 ∂finiteLaw) = 14 := by
  have hpoint : Integrable (fun x : E2 => (x - center) 0 * (x - center) 0 * (x - center) 1) (Measure.dirac point) :=
    integrable_dirac (by finiteness)
  have hzero : Integrable (fun x : E2 => (x - center) 0 * (x - center) 0 * (x - center) 1) (Measure.dirac 0) :=
    integrable_dirac (by finiteness)
  change (∫ x, _ ∂((2 : ENNReal) • Measure.dirac point + (3 : ENNReal) • Measure.dirac 0)) = _
  rw [integral_add_measure (hpoint.smul_measure (by norm_num)) (hzero.smul_measure (by norm_num)),
    integral_smul_measure, integral_smul_measure, integral_dirac, integral_dirac]
  norm_num [point, center]

theorem zero_measure_negative_radius (a : E2) (p q r : Fin 2) :
    Integrable (fun x => (x - a) p * (x - a) q * (x - a) r) (0 : Measure E2) := by
  exact integrable_coord_mul_coord_mul_coord_of_ae_norm_sub_le a (-1) (by simp) p q r

theorem radius_zero_dirac_center (a : E2) (p q r : Fin 2) :
    Integrable (fun x => (x - a) p * (x - a) q * (x - a) r) (Measure.dirac a) := by
  exact integrable_coord_mul_coord_mul_coord_of_ae_norm_sub_le a 0 (by simp) p q r

/-- No coordinate index is fabricated at rank0; these are the exact empty-index contracts. -/
theorem Fin0_coordinate (T : E0 →L[ℝ] E0) (x : E0) :
    ∀ j : Fin 0, (T x) j = ∑ r : Fin 0, operatorMatrix (EuclideanSpace.basisFun (Fin 0) ℝ) T j r * x r := by
  intro j
  exact coordinate_generic T x j

theorem Fin0_pairing (T : E0 →L[ℝ] E0) (hT : IsSelfAdjoint T) (x : E0) :
    ∀ i : Fin 0, ⟪T (EuclideanSpace.basisFun (Fin 0) ℝ i), x⟫ = (T x) i := by
  intro i
  exact pairing_generic T hT x i

theorem Fin0_cubic {ν : Measure E0} [IsFiniteMeasure ν] (a : E0) (R : ℝ)
    (hR : ∀ᵐ x ∂ν, ‖x - a‖ ≤ R) :
    ∀ p q r : Fin 0, Integrable (fun x => (x - a) p * (x - a) q * (x - a) r) ν := by
  intro p q r
  exact integrable_coord_mul_coord_mul_coord_of_ae_norm_sub_le a R hR p q r
end B69Clients

-- ===== reviewer module ChainClients (B69-Full-Chain-Independent-20261009 (receipt b467cf7a…)) =====
set_option autoImplicit false
noncomputable section
open MeasureTheory FunctionalInequalities.Analysis B69Clients
open FunctionalInequalities.Probability
open scoped RealInnerProductSpace
namespace B69ChainClients

/-- The three transformed coordinates are integrable from the actual AE bound and unit f,
without adding an integrability input. Symmetry of T is not needed for this fact. -/
theorem transformed_integrable {n : ℕ} {ν : Measure (EuclideanSpace ℝ (Fin n))}
    [IsFiniteMeasure ν] (a : EuclideanSpace ℝ (Fin n)) (R : ℝ)
    (hR : ∀ᵐ x ∂ν, ‖x-a‖ ≤ R)
    (T : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (i j k : Fin n) :
    Integrable (fun x => (T (x-a)) j * (T (x-a)) k * (T (x-a)) i) ν := by
  have hf : (fun x => (T (x-a)) j * (T (x-a)) k * (T (x-a)) i) =
      fun x => ∑ s : Fin n, ∑ t : Fin n,
        (operatorMatrix (EuclideanSpace.basisFun (Fin n) ℝ) T j s *
          operatorMatrix (EuclideanSpace.basisFun (Fin n) ℝ) T k t) *
        ((x-a) s * (x-a) t * (T (x-a)) i) := by
    funext x
    rw [euclidean_clm_apply_eq_sum_operatorMatrix T (x-a) j,
      euclidean_clm_apply_eq_sum_operatorMatrix T (x-a) k,
      Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro s hs
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro t ht
    ring
  rw [hf]
  exact integrable_finsetSum _ fun s _ => integrable_finsetSum _ fun t _ =>
    (integrable_coord_mul_coord_mul_clm_coord_of_ae_norm_sub_le a R hR T s t i).const_mul _

theorem actual_finite_nonprob_f (s t i : Fin 2) :
    Integrable (fun x => (x-center) s * (x-center) t * (nonsym (x-center)) i) finiteLaw :=
  integrable_coord_mul_coord_mul_clm_coord_of_ae_norm_sub_le center 3 actual_ae_ball nonsym s t i

theorem actual_nonprobability : ¬ IsProbabilityMeasure finiteLaw := by
  intro h
  have hm : finiteLaw.real Set.univ = 1 := by simp
  rw [finiteLaw_mass] at hm
  norm_num at hm

theorem actual_center_not_mean : (∫ x, x ∂finiteLaw) ≠ center := by
  intro h
  have hp : Integrable (fun x : E2 => x) (Measure.dirac point) := integrable_dirac (by finiteness)
  have hz : Integrable (fun x : E2 => x) (Measure.dirac (0:E2)) := integrable_dirac (by finiteness)
  have he : (∫ x, x ∂finiteLaw) = (2:ℝ) • point := by
    change (∫ x, x ∂((2:ENNReal) • Measure.dirac point + (3:ENNReal) • Measure.dirac 0)) = _
    rw [integral_add_measure (hp.smul_measure (by norm_num)) (hz.smul_measure (by norm_num)),
      integral_smul_measure, integral_smul_measure, integral_dirac, integral_dirac]
    norm_num
  rw [he] at h
  have hc := congrArg (fun x:E2 => x (0:Fin 2)) h
  norm_num [point,center] at hc

theorem coupled_transformed_integrable (i j k : Fin 2) :
    Integrable (fun x => (coupled (x-center)) j * (coupled (x-center)) k * (coupled (x-center)) i) finiteLaw :=
  transformed_integrable center 3 actual_ae_ball coupled i j k

theorem coupled_transformed_integral :
    (∫ x, (coupled (x-center)) 0 * (coupled (x-center)) 1 * (coupled (x-center)) 0 ∂finiteLaw) = -79 := by
  let f : E2 → ℝ := fun x => (coupled (x-center)) 0 * (coupled (x-center)) 1 * (coupled (x-center)) 0
  have hp : Integrable f (Measure.dirac point) := integrable_dirac (by finiteness)
  have hz : Integrable f (Measure.dirac (0:E2)) := integrable_dirac (by finiteness)
  change (∫ x, f x ∂((2:ENNReal) • Measure.dirac point + (3:ENNReal) • Measure.dirac 0)) = _
  rw [integral_add_measure (hp.smul_measure (by norm_num)) (hz.smul_measure (by norm_num)),
    integral_smul_measure, integral_smul_measure, integral_dirac, integral_dirac]
  norm_num [f,coupled,rankOne,ContinuousLinearMap.smulRight_apply,InnerProductSpace.toDual_apply_apply,
    PiLp.inner_apply,Fin.sum_univ_two,Real.inner_apply,e0,e1,point,center]

theorem actual_d2_offdiagonal :
    (operatorMatrix (EuclideanSpace.basisFun (Fin 2) ℝ) coupled *
      (Matrix.of fun j k : Fin 2 => ∫ x, (x-center) j * (x-center) k *
        ⟪coupled (EuclideanSpace.basisFun (Fin 2) ℝ 0),x-center⟫ ∂finiteLaw) *
      operatorMatrix (EuclideanSpace.basisFun (Fin 2) ℝ) coupled) 0 1 = -79 := by
  rw [operatorMatrix_mul_coordinateThirdMoment_mul_apply_of_ae_norm_sub_le
    center 3 actual_ae_ball coupled coupled_selfAdjoint]
  exact coupled_transformed_integral

theorem zero_measure_negative_radius (i j k : Fin 2) :
    (operatorMatrix (EuclideanSpace.basisFun (Fin 2) ℝ) coupled *
      (Matrix.of fun p q : Fin 2 => ∫ x, (x-center) p * (x-center) q *
        ⟪coupled (EuclideanSpace.basisFun (Fin 2) ℝ i),x-center⟫ ∂(0:Measure E2)) *
      operatorMatrix (EuclideanSpace.basisFun (Fin 2) ℝ) coupled) j k =
      ∫ x, (coupled (x-center)) j * (coupled (x-center)) k * (coupled (x-center)) i ∂(0:Measure E2) :=
  operatorMatrix_mul_coordinateThirdMoment_mul_apply_of_ae_norm_sub_le center (-1) (by simp)
    coupled coupled_selfAdjoint i j k

theorem dirac_zero_radius_f (a:E2) (s t i : Fin 2) :
    Integrable (fun x => (x-a) s * (x-a) t * (nonsym (x-a)) i) (Measure.dirac a) :=
  integrable_coord_mul_coord_mul_clm_coord_of_ae_norm_sub_le a 0 (by simp) nonsym s t i

theorem dirac_zero_radius_d2 (a:E2) (i j k:Fin 2) :
    (operatorMatrix (EuclideanSpace.basisFun (Fin 2) ℝ) coupled *
      (Matrix.of fun p q : Fin 2 => ∫ x, (x-a) p * (x-a) q *
        ⟪coupled (EuclideanSpace.basisFun (Fin 2) ℝ i),x-a⟫ ∂Measure.dirac a) *
      operatorMatrix (EuclideanSpace.basisFun (Fin 2) ℝ) coupled) j k = 0 := by
  rw [operatorMatrix_mul_coordinateThirdMoment_mul_apply_of_ae_norm_sub_le
    a 0 (by simp) coupled coupled_selfAdjoint]
  simp

theorem actual_symmetric_scalar_double_sum :
    (∑ s:Fin 2,∑ t:Fin 2,
      (if (0:Fin 2)=s then (-1:ℝ) else 1) * (v s * v t * (-5)) *
      (if t=(1:Fin 2) then (-1:ℝ) else 1)) = 45 := by
  let P:Fin 2→Fin 2→ℝ := fun r s => if r=s then -1 else 1
  have hs:∀ r s,P r s=P s r := by intro r s; simp [P,eq_comm]
  change (∑ s:Fin 2,∑ t:Fin 2,P 0 s * (v s * v t * (-5)) * P t 1)=45
  rw [sum_sum_mul_mul_mul_mul_eq_of_symm P hs (fun r=>v r) (-5) 0 1]
  norm_num [P,v,Fin.sum_univ_two]

theorem Fin0_d2 (ν:Measure E0) [IsFiniteMeasure ν] (a:E0) (R:ℝ)
    (hR:∀ᵐ x ∂ν,‖x-a‖≤R) (T:E0→L[ℝ]E0) (hT:IsSelfAdjoint T) :
    ∀ i j k : Fin 0,
      (operatorMatrix (EuclideanSpace.basisFun (Fin 0) ℝ) T *
        (Matrix.of fun p q : Fin 0 => ∫ x, (x-a) p * (x-a) q *
          ⟪T (EuclideanSpace.basisFun (Fin 0) ℝ i),x-a⟫ ∂ν) *
        operatorMatrix (EuclideanSpace.basisFun (Fin 0) ℝ) T) j k =
        ∫ x, (T (x-a)) j * (T (x-a)) k * (T (x-a)) i ∂ν := by
  intro i j k
  exact operatorMatrix_mul_coordinateThirdMoment_mul_apply_of_ae_norm_sub_le a R hR T hT i j k
end B69ChainClients

-- ===== reviewer module PosteriorClients (B69-Full-Chain-Independent-20261009 (receipt b467cf7a…)) =====
set_option autoImplicit false
noncomputable section
open MeasureTheory Set FunctionalInequalities
open FunctionalInequalities.Analysis FunctionalInequalities.Probability.Posterior
open FunctionalInequalities.Probability
open B69Clients B69ChainClients
open scoped RealInnerProductSpace ENNReal
namespace B69PosteriorClients

def corner (a b : ℝ) : E2 := WithLp.toLp 2 ![a,b]
def squareLaw : ProbabilityMeasure E2 :=
  ⟨(1/4:ENNReal) • Measure.dirac (corner 1 1) +
    (1/4:ENNReal) • Measure.dirac (corner 1 (-1)) +
    (1/4:ENNReal) • Measure.dirac (corner (-1) 1) +
    (1/4:ENNReal) • Measure.dirac (corner (-1) (-1)), by
    constructor
    simp only [Measure.add_apply,Measure.smul_apply,measure_univ,smul_eq_mul,mul_one]
    rw [ENNReal.div_add_div_same,ENNReal.div_add_div_same,ENNReal.div_add_div_same]
    norm_num
    exact ENNReal.div_self (by norm_num) (by norm_num)⟩

def corners : Set E2 := {corner 1 1,corner 1 (-1),corner (-1) 1,corner (-1) (-1)}
theorem corners_finite : corners.Finite := by simp [corners]

theorem support_subset : (squareLaw : Measure E2).support ⊆ corners := by
  apply Measure.support_subset_of_isClosed corners_finite.isClosed
  rw [mem_ae_iff]
  simp [squareLaw,corners]
theorem compact_support : IsCompact (squareLaw : Measure E2).support :=
  corners_finite.isCompact.of_isClosed_subset (squareLaw : Measure E2).isClosed_support support_subset

theorem integrable_law {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E2 → F) :
    Integrable f (squareLaw : Measure E2) := by
  have ha : Integrable f ((1/4:ENNReal) • Measure.dirac (corner 1 1)) :=
    (integrable_dirac (by finiteness)).smul_measure (by norm_num)
  have hb : Integrable f ((1/4:ENNReal) • Measure.dirac (corner 1 (-1))) :=
    (integrable_dirac (by finiteness)).smul_measure (by norm_num)
  have hc : Integrable f ((1/4:ENNReal) • Measure.dirac (corner (-1) 1)) :=
    (integrable_dirac (by finiteness)).smul_measure (by norm_num)
  have hd : Integrable f ((1/4:ENNReal) • Measure.dirac (corner (-1) (-1))) :=
    (integrable_dirac (by finiteness)).smul_measure (by norm_num)
  exact ((ha.add_measure hb).add_measure hc).add_measure hd

theorem integral_law {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (f : E2 → F) :
    (∫ x, f x ∂(squareLaw : Measure E2)) =
      (1/4:ℝ) • f (corner 1 1) + (1/4:ℝ) • f (corner 1 (-1)) +
      (1/4:ℝ) • f (corner (-1) 1) + (1/4:ℝ) • f (corner (-1) (-1)) := by
  have ha : Integrable f ((1/4:ENNReal) • Measure.dirac (corner 1 1)) :=
    (integrable_dirac (by finiteness)).smul_measure (by norm_num)
  have hb : Integrable f ((1/4:ENNReal) • Measure.dirac (corner 1 (-1))) :=
    (integrable_dirac (by finiteness)).smul_measure (by norm_num)
  have hc : Integrable f ((1/4:ENNReal) • Measure.dirac (corner (-1) 1)) :=
    (integrable_dirac (by finiteness)).smul_measure (by norm_num)
  have hd : Integrable f ((1/4:ENNReal) • Measure.dirac (corner (-1) (-1))) :=
    (integrable_dirac (by finiteness)).smul_measure (by norm_num)
  change (∫ x, f x ∂(_ + _ + _ + _)) = _
  rw [integral_add_measure ((ha.add_measure hb).add_measure hc) hd,
    integral_add_measure (ha.add_measure hb) hc,integral_add_measure ha hb]
  simp [integral_smul_measure,integral_dirac]

theorem actual_mean_zero : (∫ x, x ∂(squareLaw : Measure E2)) = 0 := by
  rw [integral_law]
  ext i
  fin_cases i <;> norm_num [corner]

theorem actual_isotropic : KLS.Isotropic squareLaw := by
  apply KLS.isotropic_of_moments squareLaw ?_ actual_mean_zero ?_
  · apply (memLp_two_iff_integrable_sq_norm continuous_id.aestronglyMeasurable).2
    exact integrable_law _
  · intro u v
    rw [integral_law]
    simp only [smul_eq_mul,PiLp.inner_apply,Fin.sum_univ_two,Real.inner_apply]
    norm_num [corner]
    ring

theorem corner_mem_support (a b : ℝ) (hab : a = 1 ∧ b = 1 ∨ a = -1 ∧ b = -1) :
    corner a b ∈ (squareLaw : Measure E2).support := by
  apply (Measure.mem_support_iff_forall (corner a b)).2
  intro U hU
  have hx : corner a b ∈ U := mem_of_mem_nhds hU
  have hp : 0 < (squareLaw : Measure E2) {corner a b} := by
    rcases hab with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> norm_num [squareLaw]
  exact hp.trans_le (measure_mono (singleton_subset_iff.mpr hx))

theorem zero_not_support : (0:E2) ∉ (squareLaw : Measure E2).support := by
  intro h
  have hc := support_subset h
  simp only [corners,mem_insert_iff,mem_singleton_iff] at hc
  rcases hc with h | h | h | h
  all_goals
    have hh := congrArg (fun x:E2 => x (0:Fin 2)) h
    norm_num [corner] at hh

theorem actual_not_logConcave : ¬ KLS.LogConcave squareLaw := by
  intro h
  have hc := h.convex_support (corner_mem_support 1 1 (Or.inl ⟨rfl,rfl⟩))
    (corner_mem_support (-1) (-1) (Or.inr ⟨rfl,rfl⟩))
    (by norm_num : (0:ℝ)≤1/2) (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)+(1/2)=1)
  have he : (1/2:ℝ) • corner 1 1 + (1/2:ℝ) • corner (-1) (-1) = 0 := by
    ext i
    fin_cases i <;> norm_num [corner]
  rw [he] at hc
  exact zero_not_support hc

def signedC : E2 := corner (-2) 1
def signedNonsymQ : E2 →L[ℝ] E2 := nonsym
theorem actual_signedC_nonzero : signedC ≠ 0 := by
  intro h
  have hh := congrArg (fun x:E2 => x (0:Fin 2)) h
  norm_num [signedC,corner] at hh
theorem actual_Q_not_selfAdjoint : ¬ IsSelfAdjoint signedNonsymQ := nonsym_not_selfAdjoint
theorem actual_Q_negative_direction : ⟪signedNonsymQ e0,e0⟫ = -1 := by
  change ⟪nonsym e0,e0⟫ = -1
  simp only [nonsym,rankOne,add_apply,neg_apply,ContinuousLinearMap.smulRight_apply,
    InnerProductSpace.toDual_apply_apply,PiLp.inner_apply,Fin.sum_univ_two,Real.inner_apply]
  norm_num [e0,e1]

def posterior : ProbabilityMeasure E2 := compactPosterior squareLaw compact_support signedC signedNonsymQ
def mean : E2 := posteriorMean squareLaw signedC signedNonsymQ
def sigma : E2 →L[ℝ] E2 := inverseSqrt (Covariance.operator (posterior : Measure E2))
theorem actual_sigma_selfAdjoint : IsSelfAdjoint sigma :=
  (KLS.Isotropic.compactPosterior_inverseSqrt_spec squareLaw compact_support actual_isotropic signedC signedNonsymQ).1
theorem actual_sigma_covariance_unit : IsUnit (Covariance.operator (posterior : Measure E2)) :=
  KLS.Isotropic.compactPosterior_covariance_isUnit squareLaw compact_support actual_isotropic signedC signedNonsymQ

theorem actual_bounded_support : ∃ R:ℝ,∀ᵐ x ∂(posterior : Measure E2),‖x-mean‖≤R :=
  compactPosterior_exists_ae_norm_sub_le squareLaw compact_support signedC signedNonsymQ mean

/-- Real input-domain data derive every H and transformed-coordinate integrability. -/
theorem actual_all_integrabilities (i j k:Fin 2) :
    Integrable (fun x => (x-mean) j * (x-mean) k *
      ⟪sigma (EuclideanSpace.basisFun (Fin 2) ℝ i),x-mean⟫) (posterior : Measure E2) ∧
    Integrable (fun x => (sigma (x-mean)) j * (sigma (x-mean)) k * (sigma (x-mean)) i)
      (posterior : Measure E2) := by
  obtain ⟨R,hR⟩ := actual_bounded_support
  constructor
  · have he : (fun x => (x-mean) j * (x-mean) k *
        ⟪sigma (EuclideanSpace.basisFun (Fin 2) ℝ i),x-mean⟫) =
        fun x => (x-mean) j * (x-mean) k * (sigma (x-mean)) i := by
      funext x
      rw [euclidean_inner_selfAdjoint_basisFun sigma actual_sigma_selfAdjoint]
    rw [he]
    exact integrable_coord_mul_coord_mul_clm_coord_of_ae_norm_sub_le mean R hR sigma j k i
  · exact transformed_integrable mean R hR sigma i j k

theorem actual_original_posterior_identity (i j k:Fin 2) :
    (operatorMatrix (EuclideanSpace.basisFun (Fin 2) ℝ) sigma *
      (Matrix.of fun p q : Fin 2 => ∫ x, (x-mean) p * (x-mean) q *
        ⟪sigma (EuclideanSpace.basisFun (Fin 2) ℝ i),x-mean⟫ ∂(posterior : Measure E2)) *
      operatorMatrix (EuclideanSpace.basisFun (Fin 2) ℝ) sigma) j k =
      ∫ x, (sigma (x-mean)) j * (sigma (x-mean)) k * (sigma (x-mean)) i ∂(posterior : Measure E2) :=
  KLS.Isotropic.operatorMatrix_inverseSqrt_mul_thirdMomentMatrix_mul_apply
    squareLaw compact_support actual_isotropic signedC signedNonsymQ i j k

theorem initial_sigma : inverseSqrt (Covariance.operator (compactPosterior squareLaw compact_support 0 0 : Measure E2)) =
    ContinuousLinearMap.id ℝ E2 :=
  KLS.Isotropic.inverseSqrt_covariance_compactPosterior_zero squareLaw compact_support actual_isotropic

theorem rank0_isotropic (ν:ProbabilityMeasure E0) : KLS.Isotropic ν where
  memLp_two := by
    have hi:(id:E0→E0)=0 := Subsingleton.elim _ _
    rw [hi]
    exact memLp_const (0:E0)
  mean_zero := by
    have hi:(fun x:E0=>x)=(fun _ =>(0:E0)) := Subsingleton.elim _ _
    rw [hi]
    simp
  covariance_identity := Subsingleton.elim _ _
theorem rank0_compact (ν:ProbabilityMeasure E0) : IsCompact (ν:Measure E0).support :=
  isCompact_univ.of_isClosed_subset (ν:Measure E0).isClosed_support (subset_univ _)
theorem rank0_sigma (ν:ProbabilityMeasure E0) (c:E0) (Q:E0→L[ℝ]E0) :
    inverseSqrt (Covariance.operator (compactPosterior ν (rank0_compact ν) c Q : Measure E0)) = 0 :=
  Subsingleton.elim _ _
theorem rank0_bounded (ν:ProbabilityMeasure E0) (c:E0) (Q:E0→L[ℝ]E0) (a:E0) :
    ∃ R:ℝ,∀ᵐ x ∂(compactPosterior ν (rank0_compact ν) c Q : Measure E0),‖x-a‖≤R :=
  compactPosterior_exists_ae_norm_sub_le ν (rank0_compact ν) c Q a

def sigma0 (ν:ProbabilityMeasure E0) (c:E0) (Q:E0→L[ℝ]E0) : E0→L[ℝ]E0 :=
  inverseSqrt (Covariance.operator (compactPosterior ν (rank0_compact ν) c Q : Measure E0))
theorem rank0_original (ν:ProbabilityMeasure E0) (c:E0) (Q:E0→L[ℝ]E0) :
    ∀ i j k : Fin 0,
      (operatorMatrix (EuclideanSpace.basisFun (Fin 0) ℝ) (sigma0 ν c Q) *
        (Matrix.of fun p q : Fin 0 => ∫ x,
          (x-posteriorMean ν c Q) p * (x-posteriorMean ν c Q) q *
          ⟪sigma0 ν c Q (EuclideanSpace.basisFun (Fin 0) ℝ i),x-posteriorMean ν c Q⟫
          ∂(compactPosterior ν (rank0_compact ν) c Q : Measure E0)) *
        operatorMatrix (EuclideanSpace.basisFun (Fin 0) ℝ) (sigma0 ν c Q)) j k =
      ∫ x, (sigma0 ν c Q (x-posteriorMean ν c Q)) j *
        (sigma0 ν c Q (x-posteriorMean ν c Q)) k *
        (sigma0 ν c Q (x-posteriorMean ν c Q)) i
        ∂(compactPosterior ν (rank0_compact ν) c Q : Measure E0) := by
  intro i j k
  exact KLS.Isotropic.operatorMatrix_inverseSqrt_mul_thirdMomentMatrix_mul_apply ν (rank0_compact ν)
    (rank0_isotropic ν) c Q i j k
end B69PosteriorClients

#print axioms B69Clients.coordinate_generic
#print axioms B69Clients.pairing_generic
#print axioms B69Clients.cubic_generic
#print axioms B69Clients.nonsym_values
#print axioms B69Clients.nonsym_witness
#print axioms B69Clients.nonsym_not_selfAdjoint
#print axioms B69Clients.nonsym_actual_rows
#print axioms B69Clients.coupled_selfAdjoint
#print axioms B69Clients.coupled_values
#print axioms B69Clients.coupled_signed_offdiagonal
#print axioms B69Clients.coupled_nontrivial_kernel
#print axioms B69Clients.coupled_actual_pairings
#print axioms B69Clients.finiteLaw_mass
#print axioms B69Clients.actual_ae_ball
#print axioms B69Clients.bound_is_not_global
#print axioms B69Clients.actual_finite_nonprob_cubics
#print axioms B69Clients.actual_center_nonzero
#print axioms B69Clients.cubic_integral_fourteen
#print axioms B69Clients.zero_measure_negative_radius
#print axioms B69Clients.radius_zero_dirac_center
#print axioms B69Clients.Fin0_coordinate
#print axioms B69Clients.Fin0_pairing
#print axioms B69Clients.Fin0_cubic
#print axioms B69ChainClients.transformed_integrable
#print axioms B69ChainClients.actual_finite_nonprob_f
#print axioms B69ChainClients.actual_nonprobability
#print axioms B69ChainClients.actual_center_not_mean
#print axioms B69ChainClients.coupled_transformed_integrable
#print axioms B69ChainClients.coupled_transformed_integral
#print axioms B69ChainClients.actual_d2_offdiagonal
#print axioms B69ChainClients.zero_measure_negative_radius
#print axioms B69ChainClients.dirac_zero_radius_f
#print axioms B69ChainClients.dirac_zero_radius_d2
#print axioms B69ChainClients.actual_symmetric_scalar_double_sum
#print axioms B69ChainClients.Fin0_d2
#print axioms B69PosteriorClients.corners_finite
#print axioms B69PosteriorClients.support_subset
#print axioms B69PosteriorClients.compact_support
#print axioms B69PosteriorClients.integrable_law
#print axioms B69PosteriorClients.integral_law
#print axioms B69PosteriorClients.actual_mean_zero
#print axioms B69PosteriorClients.actual_isotropic
#print axioms B69PosteriorClients.corner_mem_support
#print axioms B69PosteriorClients.zero_not_support
#print axioms B69PosteriorClients.actual_not_logConcave
#print axioms B69PosteriorClients.actual_signedC_nonzero
#print axioms B69PosteriorClients.actual_Q_not_selfAdjoint
#print axioms B69PosteriorClients.actual_Q_negative_direction
#print axioms B69PosteriorClients.actual_sigma_selfAdjoint
#print axioms B69PosteriorClients.actual_sigma_covariance_unit
#print axioms B69PosteriorClients.actual_bounded_support
#print axioms B69PosteriorClients.actual_all_integrabilities
#print axioms B69PosteriorClients.actual_original_posterior_identity
#print axioms B69PosteriorClients.initial_sigma
#print axioms B69PosteriorClients.rank0_isotropic
#print axioms B69PosteriorClients.rank0_compact
#print axioms B69PosteriorClients.rank0_sigma
#print axioms B69PosteriorClients.rank0_bounded
#print axioms B69PosteriorClients.rank0_original
#print axioms FunctionalInequalities.Analysis.euclidean_clm_apply_eq_sum_operatorMatrix
#print axioms FunctionalInequalities.Analysis.euclidean_inner_selfAdjoint_basisFun
#print axioms FunctionalInequalities.Analysis.sum_sum_mul_mul_mul_mul_eq_of_symm
#print axioms FunctionalInequalities.Probability.integrable_coord_mul_coord_mul_coord_of_ae_norm_sub_le
#print axioms FunctionalInequalities.Probability.integral_sum_sum_const_mul
#print axioms FunctionalInequalities.Probability.integrable_coord_mul_coord_mul_clm_coord_of_ae_norm_sub_le
#print axioms FunctionalInequalities.Probability.operatorMatrix_mul_coordinateThirdMoment_mul_apply_of_ae_norm_sub_le
#print axioms FunctionalInequalities.Probability.Posterior.compactPosterior_exists_ae_norm_sub_le
#print axioms FunctionalInequalities.KLS.Isotropic.operatorMatrix_inverseSqrt_mul_thirdMomentMatrix_mul_apply
