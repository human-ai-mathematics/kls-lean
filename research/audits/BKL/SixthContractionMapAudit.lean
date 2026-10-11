import FunctionalInequalities.Probability.Moments

/-! Independent audit clients for the third-moment contraction for an a.e.-measurable random vector (Probability/Moments section ThirdMomentContraction). Merged verbatim from the reviewer receipt `C69-Sixth-Contraction-Map-Independent-20261009 (receipt e16f27af…)` (modules Models, AEOnlyClient), each in its own named section, re-pointed from the raw `Candidate*` modules to the production owners; contracts/axiom-enumeration tooling stays in the receipt. -/

-- ===== reviewer module Models (C69-Sixth-Contraction-Map-Independent-20261009 (receipt e16f27af…)) =====
section Models
set_option autoImplicit false
noncomputable section
open MeasureTheory FunctionalInequalities.Probability
namespace C69Models
abbrev E1 := EuclideanSpace ℝ (Fin 1)
abbrev E2 := EuclideanSpace ℝ (Fin 2)
abbrev E0 := EuclideanSpace ℝ (Fin 0)
def scalar (r:ℝ) : E1 := EuclideanSpace.single 0 r
lemma scalar_zero_coord (r:ℝ) : scalar r (0:Fin 1)=r := by simp [scalar]
lemma scalar_six (r:ℝ) : ‖scalar r‖^6=r^6 := by
  simp only [scalar,PiLp.norm_single,Real.norm_eq_abs]
  calc
    |r|^6=(|r|^2)^3 := by ring
    _=(r^2)^3 := by rw [sq_abs]
    _=r^6 := by ring

def atom {X:Type*} [MeasurableSpace X] (x:X) : ProbabilityMeasure X := ⟨Measure.dirac x,inferInstance⟩
lemma negative_atom_sharp :
    (∑ i:Fin 1,∑ j:Fin 1,∑ k:Fin 1,
      (∫ _x:Unit, scalar (-2) i * scalar (-2) j * scalar (-2) k ∂(atom () : Measure Unit))^2)=64 ∧
    (∫ _x:Unit,‖scalar (-2)‖^6 ∂(atom () : Measure Unit))=64 := by
  constructor
  · norm_num [Fin.sum_univ_one,scalar]
  · norm_num [scalar_six]
lemma negative_atom_contract :
    (∑ i:Fin 1,∑ j:Fin 1,∑ k:Fin 1,
      (∫ _x:Unit, scalar (-2) i * scalar (-2) j * scalar (-2) k ∂(atom () : Measure Unit))^2)≤
      ∫ _x:Unit,‖scalar (-2)‖^6 ∂(atom () : Measure Unit) :=
  sum_sq_integral_comp_mul_mul_le_integral_norm_pow_six (atom ()) (fun _=>scalar (-2))
    measurable_const.aemeasurable (integrable_const _)

local instance : MeasurableSpace (Fin 2) := ⊤
local instance : MeasurableSingletonClass (Fin 2) := ⟨fun _ => trivial⟩
def uneven : ProbabilityMeasure (Fin 2) :=
  ⟨(1/3:ENNReal) • Measure.dirac 0 + (2/3:ENNReal) • Measure.dirac 1, by
    constructor
    simp only [Measure.add_apply,Measure.smul_apply,measure_univ,smul_eq_mul,mul_one]
    rw [ENNReal.div_add_div_same]
    norm_num
    exact ENNReal.div_self (by norm_num) (by norm_num)⟩
lemma uneven_integrable (f:Fin 2→ℝ) : Integrable f (uneven : Measure (Fin 2)) := by
  exact ((integrable_dirac (by simp)).smul_measure (ENNReal.div_ne_top (by norm_num) (by norm_num))).add_measure
    ((integrable_dirac (by simp)).smul_measure (ENNReal.div_ne_top (by norm_num) (by norm_num)))
lemma uneven_integral (f:Fin 2→ℝ) :
    (∫ x,f x ∂(uneven : Measure (Fin 2)))=(1/3:ℝ)*f 0+(2/3:ℝ)*f 1 := by
  have ha:Integrable f ((1/3:ENNReal) • Measure.dirac (0:Fin 2)) :=
    (integrable_dirac (by simp)).smul_measure (ENNReal.div_ne_top (by norm_num) (by norm_num))
  have hb:Integrable f ((2/3:ENNReal) • Measure.dirac (1:Fin 2)) :=
    (integrable_dirac (by simp)).smul_measure (ENNReal.div_ne_top (by norm_num) (by norm_num))
  change (∫ x,f x ∂((1/3:ENNReal) • Measure.dirac 0+(2/3:ENNReal) • Measure.dirac 1))=_
  rw [integral_add_measure ha hb,integral_smul_measure,integral_smul_measure,integral_dirac,integral_dirac]
  norm_num
def vector (a b:ℝ) : E2 := WithLp.toLp 2 ![a,b]
def Y2 (x:Fin 2) : E2 := if x=0 then vector 1 2 else vector (-2) 1
lemma Y2_measurable : Measurable Y2 := by intro s hs; trivial
lemma Y2_norm_six (x:Fin 2) : ‖Y2 x‖^6=125 := by
  rw [show (‖Y2 x‖:ℝ)^6=(‖Y2 x‖^2)^3 by ring,EuclideanSpace.real_norm_sq_eq]
  fin_cases x <;> norm_num [Y2,vector,Fin.sum_univ_two]
lemma actual_unequal_masses :
    (uneven:Measure (Fin 2)) {0}=(1/3:ENNReal) ∧ (uneven:Measure (Fin 2)) {1}=(2/3:ENNReal) := by
  norm_num [uneven,Measure.add_apply,Measure.smul_apply]
lemma actual_noncentered_means :
    (∫ x,Y2 x 0 ∂(uneven:Measure (Fin 2)))=-1 ∧
    (∫ x,Y2 x 1 ∂(uneven:Measure (Fin 2)))=(4/3:ℝ) := by
  rw [uneven_integral,uneven_integral]
  norm_num [Y2,vector]
lemma actual_cross_moment :
    (∫ x,Y2 x 0 * Y2 x 0 * Y2 x 1 ∂(uneven:Measure (Fin 2)))=(10/3:ℝ) := by
  rw [uneven_integral]
  norm_num [Y2,vector]
lemma actual_tensor_energy :
    (∑ i:Fin 2,∑ j:Fin 2,∑ k:Fin 2,
      (∫ x,Y2 x i * Y2 x j * Y2 x k ∂(uneven:Measure (Fin 2)))^2)=(625/9:ℝ) := by
  simp_rw [uneven_integral]
  norm_num [Y2,vector,Fin.sum_univ_two]
lemma actual_sixth_moment : (∫ x,‖Y2 x‖^6 ∂(uneven:Measure (Fin 2)))=125 := by
  simp_rw [Y2_norm_six]
  simp
lemma actual_2D_contraction :
    (∑ i:Fin 2,∑ j:Fin 2,∑ k:Fin 2,
      (∫ x,Y2 x i * Y2 x j * Y2 x k ∂(uneven:Measure (Fin 2)))^2)≤
      ∫ x,‖Y2 x‖^6 ∂(uneven:Measure (Fin 2)) :=
  sum_sq_integral_comp_mul_mul_le_integral_norm_pow_six uneven Y2 Y2_measurable.aemeasurable
    (uneven_integrable _)

lemma zero_radius_centered_dirac (a:E2) :
    (∑ i:Fin 2,∑ j:Fin 2,∑ k:Fin 2,
      (∫ x,(x-a) i * (x-a) j * (x-a) k ∂(atom a : Measure E2))^2)≤
      ∫ x,‖x-a‖^6 ∂(atom a : Measure E2) := by
  apply sum_sq_integral_comp_mul_mul_le_integral_norm_pow_six (atom a) (fun x=>x-a)
    (measurable_id.sub measurable_const).aemeasurable
  exact integrable_dirac (by simp)
lemma zero_radius_values (a:E2) :
    (∑ i:Fin 2,∑ j:Fin 2,∑ k:Fin 2,
      (∫ x,(x-a) i * (x-a) j * (x-a) k ∂(atom a : Measure E2))^2)=0 ∧
      (∫ x,‖x-a‖^6 ∂(atom a : Measure E2))=0 := by
  simp [atom,integral_dirac]

lemma rank0_actual {X:Type*} [MeasurableSpace X] (ν:ProbabilityMeasure X) (Y:X→E0) :
    AEMeasurable Y (ν:Measure X) ∧ Integrable (fun x=>‖Y x‖^6) (ν:Measure X) ∧
    (∑ i:Fin 0,∑ j:Fin 0,∑ k:Fin 0,(∫ x,Y x i*Y x j*Y x k ∂(ν:Measure X))^2)≤
      ∫ x,‖Y x‖^6 ∂(ν:Measure X) := by
  have hz:Y=(fun _=>0) := Subsingleton.elim _ _
  have hY:AEMeasurable Y (ν:Measure X) := by rw [hz]; exact measurable_const.aemeasurable
  have hi:Integrable (fun x=>‖Y x‖^6) (ν:Measure X) := by simp [hz]
  exact ⟨hY,hi,sum_sq_integral_comp_mul_mul_le_integral_norm_pow_six ν Y hY hi⟩
lemma rank0_values {X:Type*} [MeasurableSpace X] (ν:ProbabilityMeasure X) (Y:X→E0) :
    (∑ i:Fin 0,∑ j:Fin 0,∑ k:Fin 0,(∫ x,Y x i*Y x j*Y x k ∂(ν:Measure X))^2)=0 ∧
      (∫ x,‖Y x‖^6 ∂(ν:Measure X))=0 := by
  have hz:Y=(fun _=>0) := Subsingleton.elim _ _
  simp [hz]
end C69Models

end
end Models

-- ===== reviewer module AEOnlyClient (C69-Sixth-Contraction-Map-Independent-20261009 (receipt e16f27af…)) =====
section AEOnlyClient
set_option autoImplicit false
noncomputable section
open MeasureTheory Set C69Models FunctionalInequalities.Probability
namespace C69AEOnly
def partition (i:Fin 3) : Bool := decide (i=0)
@[instance_reducible] def partitionMS : MeasurableSpace (Fin 3) := (⊤:MeasurableSpace Bool).comap partition
local instance : MeasurableSpace (Fin 3) := partitionMS
def law : ProbabilityMeasure (Fin 3) := ⟨Measure.dirac 0,inferInstance⟩
def Y (i:Fin 3) : E1 := if i=0 then scalar 2 else if i=1 then scalar (-5) else scalar 9

lemma zero_singleton_measurable : MeasurableSet ({(0:Fin 3)}:Set (Fin 3)) := by
  change MeasurableSet[(⊤:MeasurableSpace Bool).comap partition] ({(0:Fin 3)}:Set (Fin 3))
  apply MeasurableSpace.measurableSet_comap.mpr
  refine ⟨{true},by trivial,?_⟩
  ext i
  simp [partition]

lemma actual_ae_zero : ∀ᵐ i ∂(law:Measure (Fin 3)),i=0 := by
  change ∀ᵐ i ∂Measure.dirac (0:Fin 3),i=0
  apply (MeasureTheory.ae_dirac_iff zero_singleton_measurable).2
  rfl
lemma actual_ae_const : Y=ᵐ[(law:Measure (Fin 3))] (fun _=>scalar 2) := by
  filter_upwards [actual_ae_zero] with i hi
  simp [Y,hi]
lemma actual_AEMeasurable : AEMeasurable Y (law:Measure (Fin 3)) :=
  measurable_const.aemeasurable.congr actual_ae_const.symm

lemma actual_not_Measurable : ¬ Measurable Y := by
  intro hY
  have hp:MeasurableSet (Y ⁻¹' {scalar (-5)}) := hY (measurableSet_singleton _)
  change MeasurableSet[(⊤:MeasurableSpace Bool).comap partition] (Y ⁻¹' {scalar (-5)}) at hp
  obtain ⟨s,_hs,heq⟩ := MeasurableSpace.measurableSet_comap.mp hp
  have h1:(1:Fin 3)∈partition ⁻¹' s := by
    rw [heq]
    norm_num [Y]
  have h2:(2:Fin 3)∈partition ⁻¹' s := by simpa [partition] using h1
  rw [heq] at h2
  have hv:scalar 9=scalar (-5) := by simpa [Y] using h2
  have hc:=congrArg (fun v:E1=>v (0:Fin 1)) hv
  norm_num [scalar] at hc

lemma actual_six_integrable : Integrable (fun i=>‖Y i‖^6) (law:Measure (Fin 3)) := by
  apply (integrable_const (‖scalar 2‖^6)).congr
  filter_upwards [actual_ae_const] with i hi
  rw [hi]
lemma actual_six_integral : (∫ i,‖Y i‖^6 ∂(law:Measure (Fin 3)))=64 := by
  calc
    _=∫ _i:Fin 3,‖scalar 2‖^6 ∂(law:Measure (Fin 3)) := by
      apply integral_congr_ae
      filter_upwards [actual_ae_const] with i hi
      rw [hi]
    _=64 := by norm_num [scalar_six]
lemma actual_cubic_integral : (∫ i,Y i 0*Y i 0*Y i 0 ∂(law:Measure (Fin 3)))=8 := by
  calc
    _=∫ _i:Fin 3,(2:ℝ)*2*2 ∂(law:Measure (Fin 3)) := by
      apply integral_congr_ae
      filter_upwards [actual_ae_const] with i hi
      rw [hi]
      simp [scalar]
    _=8 := by norm_num
lemma actual_energy :
    (∑ i:Fin 1,∑ j:Fin 1,∑ k:Fin 1,(∫ x,Y x i*Y x j*Y x k ∂(law:Measure (Fin 3)))^2)=64 := by
  rw [Fin.sum_univ_one,Fin.sum_univ_one,Fin.sum_univ_one,actual_cubic_integral]
  norm_num
lemma actual_AE_only_contraction :
    (∑ i:Fin 1,∑ j:Fin 1,∑ k:Fin 1,(∫ x,Y x i*Y x j*Y x k ∂(law:Measure (Fin 3)))^2)≤
      ∫ x,‖Y x‖^6 ∂(law:Measure (Fin 3)) :=
  sum_sq_integral_comp_mul_mul_le_integral_norm_pow_six law Y actual_AEMeasurable actual_six_integrable
end C69AEOnly

end
end AEOnlyClient

#print axioms C69Models.scalar_zero_coord
#print axioms C69Models.scalar_six
#print axioms C69Models.negative_atom_sharp
#print axioms C69Models.negative_atom_contract
#print axioms C69Models.uneven_integrable
#print axioms C69Models.uneven_integral
#print axioms C69Models.Y2_measurable
#print axioms C69Models.Y2_norm_six
#print axioms C69Models.actual_unequal_masses
#print axioms C69Models.actual_noncentered_means
#print axioms C69Models.actual_cross_moment
#print axioms C69Models.actual_tensor_energy
#print axioms C69Models.actual_sixth_moment
#print axioms C69Models.actual_2D_contraction
#print axioms C69Models.zero_radius_centered_dirac
#print axioms C69Models.zero_radius_values
#print axioms C69Models.rank0_actual
#print axioms C69Models.rank0_values
#print axioms C69AEOnly.zero_singleton_measurable
#print axioms C69AEOnly.actual_ae_zero
#print axioms C69AEOnly.actual_ae_const
#print axioms C69AEOnly.actual_AEMeasurable
#print axioms C69AEOnly.actual_not_Measurable
#print axioms C69AEOnly.actual_six_integrable
#print axioms C69AEOnly.actual_six_integral
#print axioms C69AEOnly.actual_cubic_integral
#print axioms C69AEOnly.actual_energy
#print axioms C69AEOnly.actual_AE_only_contraction
#print axioms FunctionalInequalities.Probability.sum_sq_integral_comp_mul_mul_le_integral_norm_pow_six
