import FunctionalInequalities.KLS.CEK.VariationalMaximum
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Convex.Mul
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! Audit clients for Cordero-Erausquin–Klartag (arXiv:1304.0630v1), Proposition 12 and its coercivity,
normalization and competitor reduction (`Probability/MomentMeasure/`, `KLS/CEK/`). Bodies are verbatim from the
accepted clients of `independent-p12-attainment` (CoercivityClients, NormalizedClients, AttainmentClients):
a centered two-atom probability law at the endpoints of `[-1, 1]` (boundary support), norm and quadratic scales,
zero mass and functional, a signed nonconvex input infinite at the origin, the variational range, dimension zero,
and the final all-competitor maximum. -/

noncomputable section

section
-- Accepted client `CoercivityClients.lean`.


open MeasureTheory Filter Set
open scoped ENNReal Topology
open FunctionalInequalities.Analysis FunctionalInequalities.Probability FunctionalInequalities.Probability.MomentMeasure FunctionalInequalities.KLS.CEK

namespace CEKCoercivityClients

/-- An actual centered probability concentrated at two boundary points. -/
def boundaryLaw : Measure ℝ := (1 / 2 : ℝ≥0∞) • (Measure.dirac (-1) + Measure.dirac 1)

instance boundaryLaw_probability : IsProbabilityMeasure boundaryLaw := ⟨by
  norm_num [boundaryLaw]
  rw [← two_mul, ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]⟩

theorem boundaryLaw_firstMoment : Integrable (fun x : ℝ => x) boundaryLaw := by
  apply (integrable_smul_measure (by norm_num : (1 / 2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (1 / 2 : ℝ≥0∞) ≠ ⊤)).mpr
  exact (integrable_dirac (by finiteness)).add_measure (integrable_dirac (by finiteness))

theorem boundaryLaw_centered : (∫ x : ℝ, x ∂boundaryLaw) = 0 := by
  rw [boundaryLaw, integral_smul_measure,
    integral_add_measure (integrable_dirac (by finiteness)) (integrable_dirac (by finiteness))]
  norm_num

theorem boundaryLaw_fullDimension :
    ∀ V : Submodule ℝ ℝ, boundaryLaw (V : Set ℝ)ᶜ = 0 → V = ⊤ := by
  intro V hV
  have h1 : (1 : ℝ) ∈ V := by
    by_contra hnot
    have hsubset : ({(1 : ℝ)} : Set ℝ) ⊆ (V : Set ℝ)ᶜ := by
      intro x hx
      rw [mem_singleton_iff.mp hx]
      exact hnot
    have hpoint : boundaryLaw {(1 : ℝ)} = 1 / 2 := by norm_num [boundaryLaw]
    have h := measure_mono (μ := boundaryLaw) hsubset
    rw [hpoint, hV] at h
    norm_num at h
  apply top_unique
  intro x _
  simpa only [smul_eq_mul, mul_one] using V.smul_mem x h1

/-- A is selected once for the measure, and applies to every scale t, including
arbitrarily small positive t and t=0. This tests the max(M,1) regime. -/
theorem boundary_all_norm_scales :
    ∃ A : ℝ, 0 < A ∧ ∀ t : ℝ, 0 ≤ t →
      mass volume (legendre (fun x : ℝ => ((t * ‖x‖ : ℝ) : EReal))) ≤
        ENNReal.ofReal (A * max t 1) := by
  obtain ⟨A, hA, hc⟩ := exists_coercivity_of_centered_probability (volume : Measure ℝ)
    boundaryLaw boundaryLaw_fullDimension boundaryLaw_firstMoment boundaryLaw_centered
  refine ⟨A, hA, ?_⟩
  intro t ht
  have hnn : ∀ x : ℝ, (0 : EReal) ≤ ((t * ‖x‖ : ℝ) : EReal) :=
    fun x => EReal.coe_nonneg.mpr (mul_nonneg ht (norm_nonneg x))
  have hconv : ConvexPotential (fun x : ℝ => ((t * ‖x‖ : ℝ) : EReal)) := by
    refine ⟨fun x => EReal.coe_ne_bot _, ?_⟩
    simpa only [smul_eq_mul, mem_univ, true_and, EReal.coe_le_coe_iff] using
      ((convexOn_norm (E := ℝ) convex_univ).smul ht).convex_epigraph
  have hi : Integrable (fun x : ℝ => t * ‖x‖) boundaryLaw := boundaryLaw_firstMoment.norm.const_mul t
  have hp : PotentialIntegrable (fun x : ℝ => ((t * ‖x‖ : ℝ) : EReal)) boundaryLaw :=
    ⟨fun _ => EReal.coe_ne_bot _, Eventually.of_forall fun _ => EReal.coe_ne_top _, by
      simpa only [EReal.toReal_coe] using hi⟩
  have hM : (∫ x : ℝ, t * ‖x‖ ∂boundaryLaw) = t := by
    rw [boundaryLaw, integral_smul_measure,
      integral_add_measure (integrable_dirac (by finiteness)) (integrable_dirac (by finiteness))]
    norm_num
    ring
  have h := (hc _ hnn (by simp) hconv hp).1
  simpa only [EReal.toReal_coe, hM, Module.finrank_self, pow_one] using h

/-- The source conditions and polynomial degree zero are accepted literally. -/
theorem zeroDim_probability :
    let E := EuclideanSpace ℝ (Fin 0)
    ∃ A : ℝ, 0 < A ∧ mass volume (legendre (fun _ : E => (0 : EReal))) ≤ ENNReal.ofReal A := by
  dsimp only
  let E := EuclideanSpace ℝ (Fin 0)
  let μ : Measure E := Measure.dirac 0
  have hsub : ∀ V : Submodule ℝ E, μ (V : Set E)ᶜ = 0 → V = ⊤ := by
    intro V _
    apply top_unique
    intro x _
    rw [Subsingleton.elim x 0]
    exact V.zero_mem
  have hint : Integrable (fun x : E => x) μ := integrable_dirac (by finiteness)
  have hbar : (∫ x, x ∂μ) = 0 := by simp [μ]
  obtain ⟨A, hA, hc⟩ := exists_coercivity_of_centered_probability (volume : Measure E) μ hsub hint hbar
  have hconv : ConvexPotential (fun _ : E => (0 : EReal)) := by
    refine ⟨fun _ => by simp, ?_⟩
    intro x hx y hy a b ha hb hab
    change (0 : EReal) ≤ ((a * x.2 + b * y.2 : ℝ) : EReal)
    exact EReal.coe_nonneg.mpr (add_nonneg
      (mul_nonneg ha (EReal.coe_nonneg.mp hx)) (mul_nonneg hb (EReal.coe_nonneg.mp hy)))
  have hp : PotentialIntegrable (fun _ : E => (0 : EReal)) μ := by
    exact ⟨fun _ => by simp, Eventually.of_forall fun _ => by simp, by simp⟩
  refine ⟨A, hA, ?_⟩
  simpa only [EReal.toReal_zero, integral_zero, max_eq_right zero_le_one, one_pow, mul_one] using
    (hc _ (fun _ => le_rfl) rfl hconv hp).1

/-- A real family with no supplied bound on its scale parameters. The actual
extended functional lower bound produces their uniform bound and the lintegral
bound needed by Lemma17. A finite exceptional prefix is permitted. -/
theorem norm_scale_sequence_bounded (t : ℕ → ℝ) (ht : ∀ j, 0 ≤ t j) (b : ℝ)
    (hfloor : ∀ᶠ j in atTop, (b : EReal) ≤ variationalFunctional volume boundaryLaw
      (fun x : ℝ => ((t j * ‖x‖ : ℝ) : EReal))) :
    ∃ B : ℝ, 0 ≤ B ∧ (∀ j, t j ≤ B) ∧
      (⨆ j, ∫⁻ x : ℝ, (((t j * ‖x‖ : ℝ) : EReal)).toENNReal ∂boundaryLaw) ≠ ⊤ := by
  have hnn : ∀ j (x : ℝ), (0 : EReal) ≤ ((t j * ‖x‖ : ℝ) : EReal) :=
    fun j x => EReal.coe_nonneg.mpr (mul_nonneg (ht j) (norm_nonneg x))
  have hconv : ∀ j, ConvexPotential (fun x : ℝ => ((t j * ‖x‖ : ℝ) : EReal)) := by
    intro j
    refine ⟨fun _ => EReal.coe_ne_bot _, ?_⟩
    simpa only [smul_eq_mul, mem_univ, true_and, EReal.coe_le_coe_iff] using
      ((convexOn_norm (E := ℝ) convex_univ).smul (ht j)).convex_epigraph
  have hp : ∀ j, PotentialIntegrable (fun x : ℝ => ((t j * ‖x‖ : ℝ) : EReal)) boundaryLaw := by
    intro j
    refine ⟨fun _ => EReal.coe_ne_bot _, Eventually.of_forall fun _ => EReal.coe_ne_top _, ?_⟩
    simpa only [EReal.toReal_coe] using boundaryLaw_firstMoment.norm.const_mul (t j)
  have hM : ∀ j, (∫ x : ℝ, t j * ‖x‖ ∂boundaryLaw) = t j := by
    intro j
    rw [boundaryLaw, integral_smul_measure,
      integral_add_measure (integrable_dirac (by finiteness)) (integrable_dirac (by finiteness))]
    norm_num
    ring
  obtain ⟨B, hB, hbound, hlin⟩ := exists_integral_bound_of_eventual_functional_lower
    (volume : Measure ℝ) boundaryLaw boundaryLaw_fullDimension boundaryLaw_firstMoment boundaryLaw_centered
    (fun j x => ((t j * ‖x‖ : ℝ) : EReal)) hnn (fun _ => by simp) hconv hp b hfloor
  exact ⟨B, hB, fun j => by simpa only [EReal.toReal_coe, hM j] using hbound j, hlin⟩

/-- The same source measure gives one A for every quadratic scale. The
arbitrarily small t regime retains max(t,1). -/
theorem boundary_all_quadratic_scales :
    ∃ A : ℝ, 0 < A ∧ ∀ t : ℝ, 0 ≤ t →
      mass volume (legendre (fun x : ℝ => ((t * x ^ 2 : ℝ) : EReal))) ≤
        ENNReal.ofReal (A * max t 1) := by
  obtain ⟨A, hA, hc⟩ := exists_coercivity_of_centered_probability (volume : Measure ℝ)
    boundaryLaw boundaryLaw_fullDimension boundaryLaw_firstMoment boundaryLaw_centered
  refine ⟨A, hA, ?_⟩
  intro t ht
  have hnn : ∀ x : ℝ, (0 : EReal) ≤ ((t * x ^ 2 : ℝ) : EReal) :=
    fun x => EReal.coe_nonneg.mpr (mul_nonneg ht (sq_nonneg x))
  have hconv : ConvexPotential (fun x : ℝ => ((t * x ^ 2 : ℝ) : EReal)) := by
    refine ⟨fun _ => EReal.coe_ne_bot _, ?_⟩
    simpa only [smul_eq_mul, mem_univ, true_and, EReal.coe_le_coe_iff] using
      ((Even.convexOn_pow (𝕜 := ℝ) (by norm_num : Even 2)).smul ht).convex_epigraph
  have hi : Integrable (fun x : ℝ => t * x ^ 2) boundaryLaw := by
    apply (integrable_smul_measure (by norm_num : (1 / 2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (1 / 2 : ℝ≥0∞) ≠ ⊤)).mpr
    exact (integrable_dirac (by finiteness)).add_measure (integrable_dirac (by finiteness))
  have hp : PotentialIntegrable (fun x : ℝ => ((t * x ^ 2 : ℝ) : EReal)) boundaryLaw :=
    ⟨fun _ => EReal.coe_ne_bot _, Eventually.of_forall fun _ => EReal.coe_ne_top _, by
      simpa only [EReal.toReal_coe] using hi⟩
  have hM : (∫ x : ℝ, t * x ^ 2 ∂boundaryLaw) = t := by
    rw [boundaryLaw, integral_smul_measure,
      integral_add_measure (integrable_dirac (by finiteness)) (integrable_dirac (by finiteness))]
    norm_num
    ring
  have h := (hc _ hnn (by simp) hconv hp).1
  simpa only [EReal.toReal_coe, hM, Module.finrank_self, pow_one] using h

/-- Actual zero mass on the line, and therefore the actual extended log(0),
are retained in the new functional estimate. -/
theorem zero_mass_and_functional :
    mass volume (legendre (fun _ : ℝ => (0 : EReal))) = 0 ∧
      variationalFunctional volume boundaryLaw (fun _ : ℝ => (0 : EReal)) = ⊥ := by
  have htop : ∀ y : ℝ, y ≠ 0 → legendre (fun _ : ℝ => (0 : EReal)) y = ⊤ := by
    intro y hy
    by_contra ht
    have hb := (legendre_ne_bot_iff (fun _ : ℝ => (0 : EReal)) y).mpr ⟨0, by simp⟩
    lift legendre (fun _ : ℝ => (0 : EReal)) y to ℝ using ⟨ht, hb⟩ with r hr
    have hh := le_iSup (fun x : ℝ => (inner ℝ x y : EReal) - (0 : EReal)) ((r + 1) / y)
    change (inner ℝ ((r + 1) / y) y : EReal) - 0 ≤ legendre (fun _ : ℝ => (0 : EReal)) y at hh
    rw [← hr, sub_zero, Real.inner_apply, div_mul_cancel₀ _ hy] at hh
    have hreal := EReal.coe_le_coe_iff.mp hh
    linarith
  have hmass : mass volume (legendre (fun _ : ℝ => (0 : EReal))) = 0 := by
    apply lintegral_eq_zero_of_ae_eq_zero
    filter_upwards [(volume : Measure ℝ).ae_ne 0] with y hy
    simp only [density, htop y hy, EReal.neg_top, EReal.exp_bot, Pi.zero_apply]
  refine ⟨hmass, ?_⟩
  simp only [variationalFunctional, hmass, ENNReal.log_zero, EReal.toReal_zero, integral_zero,
    EReal.coe_zero, sub_zero]

end CEKCoercivityClients

end

section
-- Accepted client `NormalizedClients.lean`.


/-! Genuine unrestricted signed/nonconvex and finite-mass scope consumers. -/
open MeasureTheory Filter Set
open scoped ENNReal Topology
open FunctionalInequalities.Analysis FunctionalInequalities.Probability FunctionalInequalities.Probability.MomentMeasure FunctionalInequalities.KLS.CEK

namespace CEKNormalizedClients
open CEKCoercivityClients

/-- Signed and genuinely nonconvex, with infinite values off the two atoms. -/
def signedInput (x : ℝ) : EReal :=
  if x = -1 then ((-3 : ℝ) : EReal) else if x = 1 then ((2 : ℝ) : EReal) else ⊤

theorem signedInput_admissible : PotentialIntegrable signedInput boundaryLaw := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    unfold signedInput
    split_ifs <;> simp
  · norm_num [boundaryLaw, signedInput]
  · apply (integrable_smul_measure (by norm_num : (1 / 2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (1 / 2 : ℝ≥0∞) ≠ ⊤)).mpr
    exact (integrable_dirac (by finiteness)).add_measure (integrable_dirac (by finiteness))

theorem signedInput_properties : signedInput (-1) < 0 ∧ signedInput 0 = ⊤ ∧ ¬ ConvexPotential signedInput := by
  refine ⟨by norm_num [signedInput], by norm_num [signedInput], ?_⟩
  intro hc
  have hp : ((-1 : ℝ), (-3 : ℝ)) ∈ {p : ℝ × ℝ | signedInput p.1 ≤ (p.2 : EReal)} := by
    norm_num [signedInput]
  have hq : ((1 : ℝ), (2 : ℝ)) ∈ {p : ℝ × ℝ | signedInput p.1 ≤ (p.2 : EReal)} := by
    norm_num [signedInput]
  have h := hc.2 hp hq (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  norm_num [signedInput] at h

/-- The input origin is actually outside its finite domain. The producer must
use actual convexification and derive domain interior before the touching plane. -/
theorem signed_nonconvex_reduction (ε : ℝ) (hε : 0 < ε) :
    ∃ ψ : ℝ → EReal, ConvexPotential ψ ∧ PotentialIntegrable ψ boundaryLaw ∧
      (∀ x, 0 ≤ ψ x) ∧ ψ 0 = 0 ∧
      variationalFunctional volume boundaryLaw signedInput ≤ variationalFunctional volume boundaryLaw ψ + (ε : EReal) :=
  exists_normalized_competitor volume boundaryLaw boundaryLaw_fullDimension boundaryLaw_firstMoment
    boundaryLaw_centered signedInput signedInput_admissible ε hε

/-- One finite upper bound covers all admissible inputs, including signedInput;
the actual finite norm baseline lies below it. No convex input assumption. -/
theorem boundary_variational_range :
    ∃ L U : ℝ, variationalFunctional volume boundaryLaw (fun x : ℝ => (‖x‖ : EReal)) = (L : EReal) ∧
      L ≤ U ∧ variationalFunctional volume boundaryLaw signedInput ≤ (U : EReal) ∧
      ∀ f : ℝ → EReal, PotentialIntegrable f boundaryLaw → variationalFunctional volume boundaryLaw f ≤ (U : EReal) := by
  obtain ⟨L, U, _hp, hL, hLU, hU⟩ := exists_finite_baseline_and_upper volume boundaryLaw
    boundaryLaw_fullDimension boundaryLaw_firstMoment boundaryLaw_centered
  exact ⟨L, U, hL, hLU, hU signedInput signedInput_admissible, hU⟩

/-- Baseline finiteness has its actual broader scope: a mass-two measure is
accepted here, without extending the probability-only normalization invariance. -/
theorem mass_two_zeroDim_baseline :
    let E := EuclideanSpace ℝ (Fin 0)
    let μ : Measure E := (2 : ℝ≥0∞) • Measure.dirac 0
    μ univ = 2 ∧ PotentialIntegrable (fun x : E => (‖x‖ : EReal)) μ ∧
      ∃ L : ℝ, variationalFunctional volume μ (fun x : E => (‖x‖ : EReal)) = (L : EReal) := by
  dsimp only
  let E := EuclideanSpace ℝ (Fin 0)
  let μ : Measure E := (2 : ℝ≥0∞) • Measure.dirac 0
  have hint : Integrable (fun x : E => x) μ := by
    apply (integrable_smul_measure (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)).mpr
    exact integrable_dirac (by finiteness)
  obtain ⟨_hc, hp, L, hL⟩ := norm_baseline_finite (volume : Measure E) μ hint
  exact ⟨by norm_num [μ], hp, L, hL⟩

end CEKNormalizedClients

end

section
-- Accepted client `AttainmentClients.lean`.


/-! Actual CEK Proposition12 clients: a full-span centered atomic probability,
a genuinely signed nonconvex competitor, and the literal zero-dimensional case. -/
open MeasureTheory Set Filter
open scoped ENNReal Topology
open FunctionalInequalities.Analysis FunctionalInequalities.Probability FunctionalInequalities.Probability.MomentMeasure FunctionalInequalities.KLS.CEK

namespace CEKAttainmentClients
open CEKCoercivityClients CEKNormalizedClients

/-- Actual mass1 lsc optimizer dominates the signed, nonconvex, infinite-at-origin
input and every other admissible input on the same genuine probability law. -/
theorem boundary_all_competitors :
    ∃ φ : ℝ → EReal, ConvexPotential φ ∧ LowerSemicontinuous φ ∧ PotentialIntegrable φ boundaryLaw ∧
      mass volume (legendre φ) = 1 ∧
      (∃ V : ℝ, variationalFunctional volume boundaryLaw φ = (V : EReal)) ∧
      variationalFunctional volume boundaryLaw signedInput ≤ variationalFunctional volume boundaryLaw φ ∧
      ∀ f : ℝ → EReal, PotentialIntegrable f boundaryLaw →
        variationalFunctional volume boundaryLaw f ≤ variationalFunctional volume boundaryLaw φ := by
  obtain ⟨φ, hc, hls, hp, hmass, hmax⟩ := exists_variational_maximum (volume : Measure ℝ)
    boundaryLaw boundaryLaw_fullDimension boundaryLaw_firstMoment boundaryLaw_centered
  refine ⟨φ, hc, hls, hp, hmass, ?_, hmax signedInput signedInput_admissible, hmax⟩
  refine ⟨-(∫ x, (φ x).toReal ∂boundaryLaw), ?_⟩
  simp only [variationalFunctional, hmass, ENNReal.log_one, zero_sub, EReal.coe_neg]

/-- No positive-dimensionality exception: the actual producer gives mass1 and
value0, dominating ALL admissible competitors in dimension0. -/
theorem zeroDim_actual_maximum :
    let E := EuclideanSpace ℝ (Fin 0)
    let μ : Measure E := Measure.dirac 0
    ∃ φ : E → EReal, ConvexPotential φ ∧ LowerSemicontinuous φ ∧ PotentialIntegrable φ μ ∧
      mass volume (legendre φ) = 1 ∧ variationalFunctional volume μ φ = 0 ∧
      ∀ f : E → EReal, PotentialIntegrable f μ → variationalFunctional volume μ f ≤ 0 := by
  dsimp only
  let E := EuclideanSpace ℝ (Fin 0)
  let μ : Measure E := Measure.dirac 0
  have hsub : ∀ V : Submodule ℝ E, μ (V : Set E)ᶜ = 0 → V = ⊤ := by
    intro V _
    apply top_unique
    intro x _
    rw [Subsingleton.elim x 0]
    exact V.zero_mem
  have hfirst : Integrable (fun x : E => x) μ := integrable_dirac (by finiteness)
  have hbar : (∫ x, x ∂μ) = 0 := by simp [μ]
  obtain ⟨φ, hc, hls, hp, hmass, hmax⟩ :=
    exists_variational_maximum (volume : Measure E) μ hsub hfirst hbar
  have hpoint (x : E) : φ x = φ 0 := by rw [Subsingleton.elim x 0]
  have hmass0 : mass volume (legendre φ) = EReal.exp (φ 0) := by
    rw [volume_euclideanSpace_eq_dirac]
    simp only [mass, density, legendre, lintegral_dirac, inner_zero_right,
      EReal.coe_zero, zero_sub, hpoint, iSup_const, neg_neg]
  have hφ0 : φ 0 = 0 := by
    apply EReal.exp_strictMono.injective
    rw [← hmass0, hmass, EReal.exp_zero]
  have hI : variationalFunctional volume μ φ = 0 := by
    simp [variationalFunctional, hmass, μ, hφ0]
  refine ⟨φ, hc, hls, hp, hmass, hI, ?_⟩
  intro f hf
  simpa only [hI] using hmax f hf

end CEKAttainmentClients

end

section NewInstantiations
-- New in this candidate (not from the accepted clients): small instantiations of the migrated API.

open MeasureTheory
open scoped ENNReal
open FunctionalInequalities.Analysis FunctionalInequalities.Probability.MomentMeasure

namespace CEKProposition12Instances

private theorem zero_potentialIntegrable (μ : Measure ℝ) [IsFiniteMeasure μ] :
    PotentialIntegrable (fun _ : ℝ => (0 : EReal)) μ :=
  ⟨fun _ => by simp, Filter.Eventually.of_forall fun _ => by simp, by simp⟩

/-- Total mass two: subtracting the constant `1` lowers the integral by the total mass `2`. -/
theorem affine_correction_mass_two :
    (∫ x, (affineSubtract (fun _ : ℝ => (0 : EReal)) 0 1 x).toReal
      ∂((2 : ℝ≥0∞) • Measure.dirac (0 : ℝ))) = -2 := by
  have : IsFiniteMeasure ((2 : ℝ≥0∞) • Measure.dirac (0 : ℝ)) := (Measure.dirac (0 : ℝ)).smul_finite (by simp)
  rw [integral_affineSubtract _ _ _ (zero_potentialIntegrable _)
    ((integrable_dirac (by simp)).smul_measure (by simp))]
  simp

/-- For the centered Dirac probability the same subtraction lowers the integral by exactly `1`. -/
theorem affine_correction_probability :
    (∫ x, (affineSubtract (fun _ : ℝ => (0 : EReal)) 0 1 x).toReal ∂(Measure.dirac (0 : ℝ))) = -1 := by
  rw [integral_affineSubtract_of_probability _ _ _ (zero_potentialIntegrable _)
    (integrable_dirac (by simp)) (by simp)]
  simp

/-- The potential `0` on `[-1, 1]` and `⊤` outside: a bounded effective domain. -/
noncomputable def intervalPotential (x : ℝ) : EReal := if |x| ≤ 1 then 0 else ⊤

theorem intervalPotential_admissible :
    PotentialIntegrable intervalPotential (Measure.dirac (0 : ℝ)) := by
  refine ⟨fun x => ?_, ?_, ?_⟩
  · unfold intervalPotential
    split_ifs <;> simp
  · rw [ae_dirac_eq]
    simp [intervalPotential]
  · have h : (fun x => (intervalPotential x).toReal) = fun _ => (0 : ℝ) := by
      funext x
      unfold intervalPotential
      split_ifs <;> simp
    rw [h]
    exact integrable_zero _ _ _

/-- Its lower truncations and their biconjugates stay admissible for every cutoff. -/
theorem intervalPotential_truncations (M : ℝ) :
    PotentialIntegrable (lowerTruncate intervalPotential M) (Measure.dirac (0 : ℝ)) ∧
      PotentialIntegrable (legendre (legendre (lowerTruncate intervalPotential M)))
        (Measure.dirac (0 : ℝ)) :=
  ⟨lowerTruncate_potentialIntegrable _ M intervalPotential_admissible,
    biconjugate_lowerTruncate_potentialIntegrable _ M (by simp) intervalPotential_admissible⟩

end CEKProposition12Instances

end NewInstantiations

#print axioms CEKCoercivityClients.boundaryLaw_firstMoment
#print axioms CEKCoercivityClients.boundaryLaw_centered
#print axioms CEKCoercivityClients.boundaryLaw_fullDimension
#print axioms CEKCoercivityClients.boundary_all_norm_scales
#print axioms CEKCoercivityClients.zeroDim_probability
#print axioms CEKCoercivityClients.norm_scale_sequence_bounded
#print axioms CEKCoercivityClients.boundary_all_quadratic_scales
#print axioms CEKCoercivityClients.zero_mass_and_functional
#print axioms CEKNormalizedClients.signedInput_admissible
#print axioms CEKNormalizedClients.signedInput_properties
#print axioms CEKNormalizedClients.signed_nonconvex_reduction
#print axioms CEKNormalizedClients.boundary_variational_range
#print axioms CEKNormalizedClients.mass_two_zeroDim_baseline
#print axioms CEKAttainmentClients.boundary_all_competitors
#print axioms CEKAttainmentClients.zeroDim_actual_maximum
#print axioms CEKProposition12Instances.affine_correction_mass_two
#print axioms CEKProposition12Instances.affine_correction_probability
#print axioms CEKProposition12Instances.intervalPotential_admissible
#print axioms CEKProposition12Instances.intervalPotential_truncations
#print axioms FunctionalInequalities.Probability.zero_mem_interior_convexHull_support_of_integral_eq_zero
#print axioms FunctionalInequalities.Analysis.exists_supporting_affine_at_zero
#print axioms FunctionalInequalities.Analysis.iSup_add_coe
#print axioms FunctionalInequalities.Analysis.legendre_affineSubtract
#print axioms FunctionalInequalities.Analysis.affineSubtract_toReal_of_finite
#print axioms FunctionalInequalities.Probability.MomentMeasure.mass_legendre_affineSubtract
#print axioms FunctionalInequalities.Probability.MomentMeasure.mass_legendre_affineSubtract_volume
#print axioms FunctionalInequalities.Probability.MomentMeasure.affineSubtract_potentialIntegrable
#print axioms FunctionalInequalities.Probability.MomentMeasure.integral_affineSubtract
#print axioms FunctionalInequalities.Probability.MomentMeasure.integral_affineSubtract_of_probability
#print axioms FunctionalInequalities.Probability.MomentMeasure.log_mass_legendre_affineSubtract
#print axioms FunctionalInequalities.Analysis.sub_coe_cancel_shift
#print axioms FunctionalInequalities.Probability.MomentMeasure.variationalFunctional_affineSubtract
#print axioms FunctionalInequalities.Probability.MomentMeasure.variationalFunctional_affineSubtract_volume
#print axioms FunctionalInequalities.Analysis.convex_epigraph_affineSubtract
#print axioms FunctionalInequalities.Analysis.exists_nonnegative_origin_zero_affine
#print axioms FunctionalInequalities.Probability.MomentMeasure.exists_origin_zero_affine_of_probability
#print axioms FunctionalInequalities.Probability.MomentMeasure.potentialIntegrable_exists_finite
#print axioms FunctionalInequalities.Probability.MomentMeasure.lowerTruncate_toReal_of_finite
#print axioms FunctionalInequalities.Probability.MomentMeasure.lowerTruncate_potentialIntegrable
#print axioms FunctionalInequalities.Probability.MomentMeasure.biconjugate_lowerTruncate_potentialIntegrable
#print axioms FunctionalInequalities.Probability.MomentMeasure.integral_biconjugate_lowerTruncate_le
#print axioms FunctionalInequalities.Probability.MomentMeasure.norm_max_neg_le
#print axioms FunctionalInequalities.Probability.MomentMeasure.tendsto_lowerTruncate_toReal
#print axioms FunctionalInequalities.Probability.MomentMeasure.tendsto_integral_lowerTruncate
#print axioms FunctionalInequalities.Probability.MomentMeasure.tendsto_integral_lowerTruncate_error
#print axioms FunctionalInequalities.Probability.MomentMeasure.integral_le_integral_lowerTruncate
#print axioms FunctionalInequalities.Probability.MomentMeasure.tendsto_integral_pointwise_lowerTruncate_error
#print axioms FunctionalInequalities.Probability.MomentMeasure.max_neg_error_le_tail
#print axioms FunctionalInequalities.Probability.MomentMeasure.lowerTailNorm_integrable
#print axioms FunctionalInequalities.Probability.MomentMeasure.tendsto_integral_lowerTailNorm
#print axioms FunctionalInequalities.Probability.MomentMeasure.integral_lowerTruncate_error_le_tail
#print axioms FunctionalInequalities.Probability.MomentMeasure.sub_coe_le_sub_coe_add
#print axioms FunctionalInequalities.Probability.MomentMeasure.exists_convexified_lowerTruncate_variational_le_add
#print axioms FunctionalInequalities.Probability.MomentMeasure.lintegral_nonneg_potential
#print axioms FunctionalInequalities.Probability.MomentMeasure.exists_uniform_legendre_lower
#print axioms FunctionalInequalities.Probability.MomentMeasure.density_scaled_le_exp
#print axioms FunctionalInequalities.Probability.MomentMeasure.lintegral_eq_pow_mul_smul
#print axioms FunctionalInequalities.Probability.MomentMeasure.exists_uniform_mass_bound
#print axioms FunctionalInequalities.Probability.MomentMeasure.functional_le_of_mass_bound
#print axioms FunctionalInequalities.Probability.MomentMeasure.exists_coercivity_of_centered_probability
#print axioms FunctionalInequalities.Probability.MomentMeasure.exists_bound_of_log_lower
#print axioms FunctionalInequalities.Probability.MomentMeasure.exists_integral_bound_of_eventual_functional_lower
#print axioms FunctionalInequalities.Probability.MomentMeasure.exists_integral_bound_of_tendsto_functional_above
#print axioms FunctionalInequalities.Probability.MomentMeasure.origin_mem_interior_domain_of_lower_bound
#print axioms FunctionalInequalities.KLS.CEK.exists_normalized_competitor
#print axioms FunctionalInequalities.Probability.MomentMeasure.real_coercivity_le_uniform
#print axioms FunctionalInequalities.KLS.CEK.exists_uniform_functional_upper
#print axioms FunctionalInequalities.Analysis.legendre_norm
#print axioms FunctionalInequalities.Probability.MomentMeasure.density_legendre_norm
#print axioms FunctionalInequalities.Probability.MomentMeasure.mass_legendre_norm
#print axioms FunctionalInequalities.Probability.MomentMeasure.norm_baseline_finite
#print axioms FunctionalInequalities.KLS.CEK.exists_finite_baseline_and_upper
#print axioms FunctionalInequalities.KLS.CEK.exists_normalized_maximizing_sequence
#print axioms FunctionalInequalities.KLS.CEK.exists_limit_ge_normalized_supremum
#print axioms FunctionalInequalities.KLS.CEK.exists_variational_maximum
