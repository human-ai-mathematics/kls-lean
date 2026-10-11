import FunctionalInequalities.KLS.BKL.LocalThirdCumulant
import FunctionalInequalities.KLS.BKL.SecondCumulant
import FunctionalInequalities.KLS.BKL.PosteriorCovariance
import FunctionalInequalities.KLS.BKL.Suspension.Density
import FunctionalInequalities.KLS.LogConcave.Regular
import FunctionalInequalities.Probability.Line.Laplace
import FunctionalInequalities.KLS.BKL.GaussianTaylor
import FunctionalInequalities.KLS.LogConcave.Translation
import FunctionalInequalities.KLS.LogConcave.Line.Poincare
import FunctionalInequalities.KLS.LogConcave.Density.Tilted

/-!
# Audit: BKL Lemma 4.2, the Theorem 4.1 base case and the posterior covariance domain

Source: Bizeul–Klartag–Lehec arXiv:2610.05474v1, Lemma 4.2. Clients compiled against the accepted
`Analysis/BakryEmery/Cumulant/Local.lean` and `KLS/BKL/LocalThirdCumulant.lean` owners:
the Laplace law (log-concave, isotropic for `β² = 2`, with only a small exponential radius and no
exponential moment at the rate itself, so excluded from the all-radii `Cumulant` statement),
a symmetric two-point law (isotropic, Letwin bound checked directly, unconditional contraction),
a skew two-point law with `κ₃ = 2`, the one-dimensional Gaussian and the rank-zero law; for the second
cumulant (`KLS/BKL/SecondCumulant.lean`): a noncentered two-point law where the mean correction matters
(`κ₂ = 1`, raw second moment `2`), the Laplace and Gaussian sources, Parseval and the rank-zero
`CumulantBound 1 1` instance; for the posterior covariance domain (`KLS/BKL/PosteriorDomain.lean`): the
atomic isotropic non-log-concave prior at all signed `(c, Q)` (unit covariance with a self-adjoint positive
inverse), the noncentered full-support prior, a positive-dimensional Dirac prior whose posterior
covariance is `0` and not a unit, and the rank-zero prior whose zero covariance is a unit; for the generator at the source rate
(`Isotropic.compactPosterior_generator_cancellation`): the atomic prior at signed `(1, −Id)` with a strictly
positive linear response, and the rank-zero initial pair; for the diffusion coefficient
(`Isotropic.compactPosterior_inverseSqrt_spec`, bundle `Principal-Inverse-SquareRoot`): the atomic prior at
`(1, −Id)`, its initial root `Id`, rank zero, and the excluded positive-dimensional Dirac law. Client bodies:
Codex route bundles `Local-Third-Cumulant`, `Local-Second-Cumulant` and the Codex bkl bundle
`Posterior-Covariance-Domain` and the Codex q_batch bundle `Posterior-Generator-Inverse` (independently accepted); the one-use normalization
helper in the Laplace client copies the reviewed helper of `KLS/BKL/SuspensionDensity.lean`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory FunctionalInequalities FunctionalInequalities.Analysis.BakryEmery
  FunctionalInequalities.Probability
open scoped RealInnerProductSpace ContDiff
open FunctionalInequalities.Probability.Line

/-! Actual Laplace local-radius, finite-support nonzero isotropic, and rank0 consumers.
The symmetric two-point law is not asserted log-concave; it consumes the stronger generic
local-radius calculus/contraction after its true quadratic bound is discharged. -/
namespace ActualLocalThird

theorem laplace_third_moment {β : ℝ} (hβ : 0 < β) (u v w : ℝ) :
    cumulant (laplaceMeasure β) 3 ![u, v, w] =
      ∫ x : ℝ, ⟪u, x⟫ * ⟪v, x⟫ * ⟪w, x⟫ ∂laplaceMeasure β := by
  have hp := isProbabilityMeasure_laplaceMeasure hβ
  apply cumulant_three_eq_integral_of_integrable_exp (laplaceMeasure β)
    (by positivity : 0 < β / 2) ?_ ?_ u v w
  · simpa only [Real.norm_eq_abs] using integrable_exp_abs_laplaceMeasure hβ
  · intro a
    simp only [Real.inner_apply]
    rw [integral_const_mul, integral_id_laplaceMeasure hβ, mul_zero]

def atomic : ProbabilityMeasure ℝ :=
  ⟨(1 / 2 : ENNReal) • Measure.dirac (-1) + (1 / 2 : ENNReal) • Measure.dirac 1, by
    constructor
    norm_num
    exact ENNReal.inv_two_add_inv_two⟩

private theorem atomic_integral (f : ℝ → ℝ) :
    (∫ x, f x ∂(atomic : Measure ℝ)) = (1 / 2 : ℝ) * f (-1) + (1 / 2 : ℝ) * f 1 := by
  have h0 : Integrable f ((1 / 2 : ENNReal) • Measure.dirac (-1 : ℝ)) :=
    (integrable_dirac (by simp)).smul_measure (by norm_num)
  have h1 : Integrable f ((1 / 2 : ENNReal) • Measure.dirac (1 : ℝ)) :=
    (integrable_dirac (by simp)).smul_measure (by norm_num)
  change (∫ x, f x ∂((1 / 2 : ENNReal) • Measure.dirac (-1) + (1 / 2 : ENNReal) • Measure.dirac 1)) = _
  rw [integral_add_measure h0 h1, integral_smul_measure, integral_smul_measure]
  simp

theorem atomic_compact_support : IsCompact (atomic : Measure ℝ).support := by
  have hae : ({(-1 : ℝ), 1} : Set ℝ) ∈ ae (atomic : Measure ℝ) := by
    rw [mem_ae_iff]
    change (((1 / 2 : ENNReal) • Measure.dirac (-1 : ℝ) + (1 / 2 : ENNReal) • Measure.dirac (1 : ℝ) : Measure ℝ)
      ({(-1 : ℝ), 1} : Set ℝ)ᶜ) = 0
    simp
  have hsub := Measure.support_subset_of_isClosed (isClosed_singleton.union isClosed_singleton) hae
  exact (Set.toFinite ({(-1 : ℝ), 1} : Set ℝ)).isCompact.of_isClosed_subset
    (atomic : Measure ℝ).isClosed_support hsub

theorem atomic_true_exponential (r : ℝ) :
    Integrable (fun x : ℝ => Real.exp (r * ‖x‖)) (atomic : Measure ℝ) :=
  compact_support_integrable_exp (atomic : Measure ℝ) atomic_compact_support r

theorem atomic_true_all_moments (k : ℕ) :
    Integrable (fun x : ℝ => ‖x‖ ^ k) (atomic : Measure ℝ) :=
  compact_support_integrable_norm_pow (atomic : Measure ℝ) atomic_compact_support k

theorem atomic_isotropic : KLS.Isotropic atomic := by
  apply KLS.isotropic_of_moments atomic ?_ ?_ ?_
  · apply (memLp_two_iff_integrable_sq_norm continuous_id.aestronglyMeasurable).2
    exact atomic_true_all_moments 2
  · rw [atomic_integral]
    norm_num
  · intro u v
    rw [atomic_integral]
    simp only [Real.inner_apply]
    ring

theorem atomic_letwin : LetwinQuadraticBound (atomic : Measure ℝ) := by
  intro M _hM
  have hneg : M (-1) = -M 1 := by simp
  have hmean : (∫ x, ⟪M x, x⟫ ∂(atomic : Measure ℝ)) = M 1 := by
    rw [atomic_integral]
    simp only [Real.inner_apply, hneg]
    ring
  rw [hmean, atomic_integral]
  simp only [Real.inner_apply, hneg]
  have hz : (1 / 2 : ℝ) * (-M 1 * -1 - M 1) ^ 2 +
      (1 / 2 : ℝ) * (M 1 * 1 - M 1) ^ 2 = 0 := by ring
  rw [hz]
  positivity

theorem atomic_actual_contraction (u : ℝ) :
    ∑ j, ∑ k, cumulant (atomic : Measure ℝ) 3
      ![u, stdOrthonormalBasis ℝ ℝ j, stdOrthonormalBasis ℝ ℝ k] ^ 2 ≤ 8 * ‖u‖ ^ 2 := by
  apply sum_sq_cumulant_three_le_of_letwin_of_integrable_exp (atomic : Measure ℝ) (by norm_num : (0 : ℝ) < 1)
    (atomic_true_exponential 1) ?_ atomic_isotropic.integral_inner_mul_inner atomic_letwin u
  intro v
  rw [atomic_integral]
  simp only [Real.inner_apply]
  ring

theorem atomic_variance_nonzero : (∫ x : ℝ, x ^ 2 ∂(atomic : Measure ℝ)) = 1 := by
  rw [atomic_integral]
  norm_num

abbrev ZeroSpace := EuclideanSpace ℝ (Fin 0)
def zeroLaw : ProbabilityMeasure ZeroSpace := ⟨Measure.dirac 0, inferInstance⟩

theorem rank0_third_moment (u v w : ZeroSpace) :
    cumulant (zeroLaw : Measure ZeroSpace) 3 ![u, v, w] = 0 := by
  have hc : IsCompact (zeroLaw : Measure ZeroSpace).support :=
    isCompact_univ.of_isClosed_subset (zeroLaw : Measure ZeroSpace).isClosed_support (Set.subset_univ _)
  have h := cumulant_three_eq_integral_of_integrable_exp (zeroLaw : Measure ZeroSpace)
    (by norm_num : (0 : ℝ) < 1) (compact_support_integrable_exp _ hc 1)
    (by intro v; simp [zeroLaw]) u v w
  simpa [zeroLaw] using h

end ActualLocalThird

open ActualLocalThird

namespace ActualLocalThirdScope

/-- A genuine scope obstruction: the Laplace law has a small exponential radius, but its
norm-exponential moment at the rate itself is infinite. -/
theorem laplace_rate_not_integrable {β : ℝ} (hβ : 0 < β) :
    ¬ Integrable (fun x : ℝ => Real.exp (β * ‖x‖)) (laplaceMeasure β) := by
  intro hi
  have hm : Measurable (fun s : ℝ => ENNReal.ofReal (laplaceDensity β s)) := by
    unfold laplaceDensity
    fun_prop
  have hfin : ∀ᵐ s : ℝ ∂volume, ENNReal.ofReal (laplaceDensity β s) < ⊤ :=
    Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have hnn (s : ℝ) : 0 ≤ laplaceDensity β s := by unfold laplaceDensity; positivity
  change Integrable _ (volume.withDensity fun s => ENNReal.ofReal (laplaceDensity β s)) at hi
  rw [integrable_withDensity_iff hm hfin] at hi
  have heq : (fun x : ℝ => Real.exp (β * ‖x‖) *
      (ENNReal.ofReal (laplaceDensity β x)).toReal) = fun _ => β / 2 := by
    ext x
    rw [ENNReal.toReal_ofReal (hnn x)]
    simp only [laplaceDensity, Real.norm_eq_abs]
    rw [mul_left_comm, ← Real.exp_add]
    simp
  rw [heq] at hi
  have hfinite : IsFiniteMeasure (volume : Measure ℝ) :=
    (integrable_const_iff_isFiniteMeasure (by positivity : β / 2 ≠ 0)).1 hi
  have hf := measure_lt_top (volume : Measure ℝ) Set.univ
  rw [Real.volume_univ] at hf
  exact lt_irrefl _ hf

abbrev E := EuclideanSpace ℝ (Fin 1)
def gaussian : ProbabilityMeasure E := (KLS.regularPotential_half_norm_sq (E := E)).law

theorem gaussian_isotropic : KLS.Isotropic gaussian := by
  apply KLS.isotropic_of_moments gaussian
    (KLS.regularPotential_half_norm_sq (E := E)).logConcave_law.memLp_id_two
    KLS.integral_id_tilted_half_norm_sq
  intro u v
  have hs : (∫ x : E, x 0 ^ 2 ∂(gaussian : Measure E)) = 1 := by
    have h := KLS.integral_inner_sq_tilted_half_norm_sq (EuclideanSpace.basisFun (Fin 1) ℝ 0)
    have hm : (volume : Measure E).tilted (-fun x : E => ‖x‖ ^ 2 / 2) = (gaussian : Measure E) := rfl
    rw [hm] at h
    simpa only [EuclideanSpace.basisFun_inner, OrthonormalBasis.norm_eq_one, one_pow] using h
  simp only [PiLp.inner_apply, Fin.sum_univ_one, Real.inner_apply]
  have he : (fun x : E => u 0 * x 0 * (v 0 * x 0)) = fun x => (u 0 * v 0) * x 0 ^ 2 := by
    ext x
    ring
  rw [he, integral_const_mul, hs, mul_one]

/-- This actual LC/isotropic law consumes the exact source endpoint. Its only remaining
input is the named upstream Letwin inequality, explicitly retained. -/
theorem gaussian_source_conditional (hL : LetwinQuadraticBound (gaussian : Measure E)) (u : E) :
    ∑ j, ∑ k, cumulant (gaussian : Measure E) 3
      ![u, stdOrthonormalBasis ℝ E j, stdOrthonormalBasis ℝ E k] ^ 2 ≤ 8 * ‖u‖ ^ 2 :=
  KLS.LogConcave.sum_sq_cumulant_three_le_of_letwin gaussian (KLS.regularPotential_half_norm_sq (E := E)).logConcave_law
    gaussian_isotropic hL (stdOrthonormalBasis ℝ E) u


theorem rank0_isotropic : KLS.Isotropic zeroLaw := by
  refine ⟨?_, ?_, Subsingleton.elim _ _⟩
  · apply (memLp_two_iff_integrable_sq_norm continuous_id.aestronglyMeasurable).2
    exact integrable_dirac (by simp)
  · simp [zeroLaw]

theorem rank0_source_contraction (u : ZeroSpace) :
    ∑ j, ∑ k, cumulant (zeroLaw : Measure ZeroSpace) 3
      ![u, stdOrthonormalBasis ℝ ZeroSpace j, stdOrthonormalBasis ℝ ZeroSpace k] ^ 2 ≤ 8 * ‖u‖ ^ 2 := by
  have hLC : KLS.LogConcave zeroLaw := by
    simpa only [zeroLaw, Probability.ofMeasure] using KLS.logConcave_dirac (0 : ZeroSpace)
  have hL : LetwinQuadraticBound (zeroLaw : Measure ZeroSpace) := by
    intro M _hM
    simp [zeroLaw]
    positivity
  exact KLS.LogConcave.sum_sq_cumulant_three_le_of_letwin zeroLaw hLC rank0_isotropic hL
    (stdOrthonormalBasis ℝ ZeroSpace) u

end ActualLocalThirdScope

/-! A genuinely nonzero third cumulant on a compact centered law. This two-point law is
not log-concave and is not asserted isotropic (its variance is2); it consumes the generic
one-radius third-moment identity with every hypothesis derived from its actual measure. -/
namespace ActualSkewLocalThird

def μ : ProbabilityMeasure ℝ :=
  ⟨(2 / 3 : ENNReal) • Measure.dirac (-1) + (1 / 3 : ENNReal) • Measure.dirac 2, by
    constructor
    simp only [Measure.add_apply, Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _),
      smul_eq_mul, mul_one]
    rw [← ENNReal.add_div]
    norm_num
    exact ENNReal.div_self (by norm_num) (by norm_num)⟩

private theorem integral_μ (f : ℝ → ℝ) :
    (∫ x, f x ∂(μ : Measure ℝ)) = (2 / 3 : ℝ) * f (-1) + (1 / 3 : ℝ) * f 2 := by
  have hm : Integrable f ((2 / 3 : ENNReal) • Measure.dirac (-1 : ℝ)) :=
    (integrable_dirac (by simp)).smul_measure (ENNReal.div_ne_top (by norm_num) (by norm_num))
  have hp : Integrable f ((1 / 3 : ENNReal) • Measure.dirac (2 : ℝ)) :=
    (integrable_dirac (by simp)).smul_measure (by norm_num)
  change (∫ x, f x ∂((2 / 3 : ENNReal) • Measure.dirac (-1) + (1 / 3 : ENNReal) • Measure.dirac 2)) = _
  rw [integral_add_measure hm hp, integral_smul_measure, integral_smul_measure]
  simp

theorem compact_support : IsCompact (μ : Measure ℝ).support := by
  have hae : ({(-1 : ℝ), 2} : Set ℝ) ∈ ae (μ : Measure ℝ) := by
    rw [mem_ae_iff]
    change (((2 / 3 : ENNReal) • Measure.dirac (-1 : ℝ) +
      (1 / 3 : ENNReal) • Measure.dirac (2 : ℝ) : Measure ℝ) ({(-1 : ℝ), 2} : Set ℝ)ᶜ) = 0
    simp
  have hsub := Measure.support_subset_of_isClosed (isClosed_singleton.union isClosed_singleton) hae
  exact (Set.toFinite ({(-1 : ℝ), 2} : Set ℝ)).isCompact.of_isClosed_subset
    (μ : Measure ℝ).isClosed_support hsub

theorem centered : ∀ v : ℝ, ∫ x, ⟪v, x⟫ ∂(μ : Measure ℝ) = 0 := by
  intro v
  rw [integral_μ]
  simp only [Real.inner_apply]
  ring

theorem third_cumulant_nonzero : cumulant (μ : Measure ℝ) 3 ![1, 1, 1] = 2 := by
  rw [cumulant_three_eq_integral_of_integrable_exp (μ : Measure ℝ)
    (by norm_num : (0 : ℝ) < 1) (compact_support_integrable_exp _ compact_support 1) centered]
  rw [integral_μ]
  norm_num [Real.inner_apply]

theorem variance_two : (∫ x : ℝ, x ^ 2 ∂(μ : Measure ℝ)) = 2 := by
  rw [integral_μ]
  norm_num

end ActualSkewLocalThird

/-! Actual log-concave Laplace scope client. The one-use normalization body below is copied
exactly from the already reviewed root-Codex helper in actual SuspensionDensity; client-only
reuse is explicit, not new distribution work or an API-output claim. -/
namespace ActualLaplaceLocalThird

private theorem normalized_of_probability_density {A : Type*} [MeasurableSpace A]
    (μ : Measure A) (W : A → ℝ) (hW : Measurable W) {C : ℝ} (hC : 0 < C)
    (hprob : IsProbabilityMeasure (μ.withDensity (fun x => ENNReal.ofReal (C * Real.exp (W x))))) :
    Integrable (fun x => Real.exp (W x)) μ ∧
      μ.withDensity (fun x => ENNReal.ofReal (C * Real.exp (W x))) = μ.tilted W := by
  let := hprob
  have hmass : ∫⁻ x, ENNReal.ofReal (C * Real.exp (W x)) ∂μ = 1 := by
    have hm := measure_univ (μ := μ.withDensity (fun x => ENNReal.ofReal (C * Real.exp (W x))))
    simpa only [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ] using hm
  have hmeas : Measurable (fun x => C * Real.exp (W x)) := measurable_const.mul hW.exp
  have hnonneg : ∀ x, 0 ≤ C * Real.exp (W x) := fun x => mul_nonneg hC.le (Real.exp_pos _).le
  have hInt : Integrable (fun x => C * Real.exp (W x)) μ := by
    refine ⟨hmeas.aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    simp_rw [Real.enorm_eq_ofReal (hnonneg _)]
    rw [hmass]
    exact ENNReal.one_lt_top
  have hexp : Integrable (fun x => Real.exp (W x)) μ := by
    have ht := hInt.const_mul C⁻¹
    simpa only [← mul_assoc, inv_mul_cancel₀ hC.ne', one_mul] using ht
  have ho : ENNReal.ofReal (∫ x, C * Real.exp (W x) ∂μ) = 1 :=
    (ofReal_integral_eq_lintegral_ofReal hInt (Filter.Eventually.of_forall hnonneg)).trans hmass
  have hval : (∫ x, C * Real.exp (W x) ∂μ) = 1 := by
    exact (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg hnonneg) zero_le_one).1
      (by simpa only [ENNReal.ofReal_one] using ho)
  have hnorm : C * (∫ x, Real.exp (W x) ∂μ) = 1 := by
    rw [← integral_const_mul C]
    exact hval
  have hz : (∫ x, Real.exp (W x) ∂μ) = C⁻¹ := by
    rw [← one_div]
    exact (eq_div_iff hC.ne').2 (by simpa only [mul_comm] using hnorm)
  refine ⟨hexp, ?_⟩
  unfold Measure.tilted
  congr 1
  funext x
  rw [hz, div_eq_mul_inv, inv_inv, mul_comm]


def μ (β : ℝ) (hβ : 0 < β) : ProbabilityMeasure ℝ :=
  ⟨laplaceMeasure β, isProbabilityMeasure_laplaceMeasure hβ⟩

theorem actual_tilted {β : ℝ} (hβ : 0 < β) :
    (μ β hβ : Measure ℝ) = volume.tilted (-fun x : ℝ => β * |x|) := by
  change volume.withDensity (fun x => ENNReal.ofReal (laplaceDensity β x)) = _
  exact (normalized_of_probability_density volume (fun x : ℝ => -(β * |x|))
    (by fun_prop) (by positivity : 0 < β / 2) (isProbabilityMeasure_laplaceMeasure hβ)).2

theorem actual_logConcave {β : ℝ} (hβ : 0 < β) : KLS.LogConcave (μ β hβ) := by
  apply KLS.LogConcave.logConcave_of_eq_tilted (actual_tilted hβ) (by fun_prop)
  simpa only [Real.norm_eq_abs, smul_eq_mul] using
    (convexOn_norm convex_univ (E := ℝ)).smul hβ.le

theorem actual_isotropic {β : ℝ} (hβ : 0 < β) (hβ2 : β ^ 2 = 2) : KLS.Isotropic (μ β hβ) := by
  apply KLS.isotropic_of_moments (μ β hβ) ?_ (integral_id_laplaceMeasure hβ) ?_
  · apply (memLp_two_iff_integrable_sq_norm continuous_id.aestronglyMeasurable).2
    change Integrable (fun x : ℝ => ‖x‖ ^ 2) (laplaceMeasure β)
    simpa only [Real.norm_eq_abs, sq_abs] using integrable_pow_laplaceMeasure hβ 2
  · intro u v
    simp only [Real.inner_apply]
    have heq : (fun x : ℝ => u * x * (v * x)) = fun x => (u * v) * x ^ 2 := by
      ext x
      ring
    rw [heq, integral_const_mul]
    change (u * v) * (∫ x : ℝ, x ^ 2 ∂laplaceMeasure β) = u * v
    rw [integral_sq_laplaceMeasure hβ, hβ2]
    norm_num

theorem source_conditional {β : ℝ} (hβ : 0 < β) (hβ2 : β ^ 2 = 2)
    (hL : LetwinQuadraticBound (μ β hβ : Measure ℝ)) (u : ℝ) :
    ∑ j, ∑ k, cumulant (μ β hβ : Measure ℝ) 3
      ![u, stdOrthonormalBasis ℝ ℝ j, stdOrthonormalBasis ℝ ℝ k] ^ 2 ≤ 8 * ‖u‖ ^ 2 :=
  KLS.LogConcave.sum_sq_cumulant_three_le_of_letwin (μ β hβ) (actual_logConcave hβ) (actual_isotropic hβ hβ2)
    hL (stdOrthonormalBasis ℝ ℝ) u

theorem source_conditional_sqrt_two
    (hL : LetwinQuadraticBound (μ (Real.sqrt 2) (Real.sqrt_pos.mpr (by norm_num)) : Measure ℝ))
    (u : ℝ) :
    ∑ j, ∑ k, cumulant
      (μ (Real.sqrt 2) (Real.sqrt_pos.mpr (by norm_num)) : Measure ℝ) 3
      ![u, stdOrthonormalBasis ℝ ℝ j, stdOrthonormalBasis ℝ ℝ k] ^ 2 ≤ 8 * ‖u‖ ^ 2 :=
  source_conditional (Real.sqrt_pos.mpr (by norm_num)) (Real.sq_sqrt (by norm_num)) hL u

end ActualLaplaceLocalThird

open ActualLaplaceLocalThird

namespace ActualLocalThirdScope

/-- A true isotropic log-concave law excluded by the old all-radius hypothesis.
This witnesses a material analytic restriction, rather than merely a missing proof of it. -/
theorem isotropic_logConcave_without_all_exponential_moments :
    ∃ ν : ProbabilityMeasure ℝ, KLS.LogConcave ν ∧ KLS.Isotropic ν ∧
      ¬ (∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (ν : Measure ℝ)) := by
  have hs : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  refine ⟨μ (Real.sqrt 2) hs, actual_logConcave hs,
    actual_isotropic hs (Real.sq_sqrt (by norm_num)), ?_⟩
  intro hall
  exact laplace_rate_not_integrable hs (hall (Real.sqrt 2))

end ActualLocalThirdScope

namespace ActualLocalSecond
open FunctionalInequalities FunctionalInequalities.Analysis.BakryEmery

def μ : ProbabilityMeasure ℝ :=
  ⟨(1 / 2 : ENNReal) • Measure.dirac 0 + (1 / 2 : ENNReal) • Measure.dirac 2, by
    constructor
    norm_num
    exact ENNReal.inv_two_add_inv_two⟩

private theorem integral_μ (f : ℝ → ℝ) :
    (∫ x, f x ∂(μ : Measure ℝ)) = (1 / 2 : ℝ) * f 0 + (1 / 2 : ℝ) * f 2 := by
  have h0 : Integrable f ((1 / 2 : ENNReal) • Measure.dirac (0 : ℝ)) :=
    (integrable_dirac (by simp)).smul_measure (by norm_num)
  have h2 : Integrable f ((1 / 2 : ENNReal) • Measure.dirac (2 : ℝ)) :=
    (integrable_dirac (by simp)).smul_measure (by norm_num)
  change (∫ x, f x ∂((1 / 2 : ENNReal) • Measure.dirac 0 + (1 / 2 : ENNReal) • Measure.dirac 2)) = _
  rw [integral_add_measure h0 h2, integral_smul_measure, integral_smul_measure]
  simp

theorem compact_support : IsCompact (μ : Measure ℝ).support := by
  have hae : ({(0 : ℝ), 2} : Set ℝ) ∈ ae (μ : Measure ℝ) := by
    rw [mem_ae_iff]
    change (((1 / 2 : ENNReal) • Measure.dirac (0 : ℝ) +
      (1 / 2 : ENNReal) • Measure.dirac (2 : ℝ) : Measure ℝ) ({(0 : ℝ), 2} : Set ℝ)ᶜ) = 0
    simp
  have hsub := Measure.support_subset_of_isClosed (isClosed_singleton.union isClosed_singleton) hae
  exact (Set.toFinite ({(0 : ℝ), 2} : Set ℝ)).isCompact.of_isClosed_subset
    (μ : Measure ℝ).isClosed_support hsub

theorem noncentered_mean : (∫ x : ℝ, x ∂(μ : Measure ℝ)) = 1 := by
  rw [integral_μ]
  norm_num

theorem raw_second_two : (∫ x : ℝ, x ^ 2 ∂(μ : Measure ℝ)) = 2 := by
  rw [integral_μ]
  norm_num

/-- The mean correction is genuinely used: second cumulant1 differs from raw second2. -/
theorem noncentered_second_cumulant : cumulant (μ : Measure ℝ) 2 ![1, 1] = 1 := by
  rw [cumulant_two_eq_centered_moment_of_integrable_exp (μ : Measure ℝ) (by norm_num : (0 : ℝ) < 1)
    (compact_support_integrable_exp _ compact_support 1)]
  rw [integral_μ, integral_μ]
  norm_num [Real.inner_apply]

theorem noncentered_second_cumulant_coordinates (u v : ℝ) :
    cumulant (μ : Measure ℝ) 2 ![u, v] = u * v := by
  rw [cumulant_two_eq_centered_moment_of_integrable_exp (μ : Measure ℝ) (by norm_num : (0 : ℝ) < 1)
    (compact_support_integrable_exp _ compact_support 1)]
  rw [integral_μ, integral_μ, integral_μ]
  simp only [Real.inner_apply]
  ring

theorem true_covariance_pairing : ⟪Covariance.operator (μ : Measure ℝ) 1, 1⟫ = 1 := by
  rw [← cumulant_two_eq_covariance_of_integrable_exp (μ : Measure ℝ) (by norm_num : (0 : ℝ) < 1)
    (compact_support_integrable_exp _ compact_support 1)]
  exact noncentered_second_cumulant

theorem laplace_source_second_cumulant :
    cumulant (ActualLaplaceLocalThird.μ (Real.sqrt 2) (Real.sqrt_pos.mpr (by norm_num)) : Measure ℝ)
      2 ![1, 1] = 1 := by
  have hs : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have h := KLS.LogConcave.cumulant_two_eq_inner_of_isotropic (ActualLaplaceLocalThird.μ (Real.sqrt 2) hs)
    (ActualLaplaceLocalThird.actual_logConcave hs)
    (ActualLaplaceLocalThird.actual_isotropic hs (Real.sq_sqrt (by norm_num))) (1 : ℝ) 1
  simpa only [Real.inner_apply, mul_one] using h

open ActualLocalThirdScope (E gaussian gaussian_isotropic)

theorem gaussian_source_second_cumulant :
    cumulant (gaussian : Measure E) 2
      ![EuclideanSpace.basisFun (Fin 1) ℝ 0, EuclideanSpace.basisFun (Fin 1) ℝ 0] = 1 := by
  have h := KLS.LogConcave.cumulant_two_eq_inner_of_isotropic gaussian
    (KLS.regularPotential_half_norm_sq (E := E)).logConcave_law gaussian_isotropic
    (EuclideanSpace.basisFun (Fin 1) ℝ 0) (EuclideanSpace.basisFun (Fin 1) ℝ 0)
  simpa only [OrthonormalBasis.inner_eq_ite, ite_true] using h

theorem gaussian_source_parseval (u : E) :
    (∑ j, cumulant (gaussian : Measure E) 2 ![u, EuclideanSpace.basisFun (Fin 1) ℝ j] ^ 2) = ‖u‖ ^ 2 :=
  KLS.LogConcave.sum_sq_cumulant_two_eq_norm_sq_of_isotropic gaussian
    (KLS.regularPotential_half_norm_sq (E := E)).logConcave_law gaussian_isotropic
    (EuclideanSpace.basisFun (Fin 1) ℝ) u

open ActualLocalThird (ZeroSpace zeroLaw)

theorem rank0_second_cumulant (u v : ZeroSpace) : cumulant (zeroLaw : Measure ZeroSpace) 2 ![u, v] = 0 := by
  have hLC : KLS.LogConcave zeroLaw := by
    simpa only [zeroLaw, Probability.ofMeasure] using KLS.logConcave_dirac (0 : ZeroSpace)
  rw [KLS.LogConcave.cumulant_two_eq_inner_of_isotropic zeroLaw hLC ActualLocalThirdScope.rank0_isotropic]
  have hu : u = 0 := Subsingleton.elim _ _
  rw [hu, inner_zero_left]

theorem rank0_original_global_base (u : ZeroSpace) :
    (∑ J : Fin 1 → Fin 0, cumulant (zeroLaw : Measure ZeroSpace) 2
      (Fin.cons u fun k => EuclideanSpace.basisFun (Fin 0) ℝ (J k)) ^ 2) ≤ 1 * ‖u‖ ^ 2 := by
  have hLC : KLS.LogConcave zeroLaw := by
    simpa only [zeroLaw, Probability.ofMeasure] using KLS.logConcave_dirac (0 : ZeroSpace)
  exact KLS.LogConcave.Suspension.cumulantBound_one_one 0 zeroLaw ActualLocalThirdScope.rank0_isotropic hLC u
end ActualLocalSecond

namespace ActualPosteriorDomainClients
open FunctionalInequalities FunctionalInequalities.Probability.Posterior

/-- A genuine compact isotropic non-Gaussian prior, at ALL signed finite c,Q. -/
theorem atomic_covariance_pos (c : ℝ) (Q : ℝ →L[ℝ] ℝ) :
    0 < ⟪Covariance.operator (compactPosterior ActualLocalThird.atomic
      ActualLocalThird.atomic_compact_support c Q : Measure ℝ) 1, 1⟫ :=
  KLS.Isotropic.compactPosterior_covariance_pos _ _ ActualLocalThird.atomic_isotropic c Q (by norm_num)

theorem atomic_covariance_unit_and_inverse (c : ℝ) (Q : ℝ →L[ℝ] ℝ) :
    IsUnit (Covariance.operator (compactPosterior ActualLocalThird.atomic
      ActualLocalThird.atomic_compact_support c Q : Measure ℝ)) ∧
    ∃ B : ℝ →L[ℝ] ℝ,
      (Covariance.operator (compactPosterior ActualLocalThird.atomic
        ActualLocalThird.atomic_compact_support c Q : Measure ℝ)).comp B = ContinuousLinearMap.id ℝ ℝ ∧
      B.comp (Covariance.operator (compactPosterior ActualLocalThird.atomic
        ActualLocalThird.atomic_compact_support c Q : Measure ℝ)) = ContinuousLinearMap.id ℝ ℝ :=
  ⟨KLS.Isotropic.compactPosterior_covariance_isUnit _ _ ActualLocalThird.atomic_isotropic c Q,
    KLS.Isotropic.compactPosterior_exists_covariance_inverse _ _ ActualLocalThird.atomic_isotropic c Q⟩

/-- Actual nonzero c and negative Q, without any posterior isotropy assumption. -/
theorem signed_parameters_positive :
    0 < ⟪Covariance.operator (compactPosterior ActualLocalThird.atomic
      ActualLocalThird.atomic_compact_support 1 (-ContinuousLinearMap.id ℝ ℝ) : Measure ℝ) 1, 1⟫ :=
  atomic_covariance_pos 1 (-ContinuousLinearMap.id ℝ ℝ)

/-- The original signed-parameter covariance rate has an ACTUAL self-adjoint positive inverse. -/
theorem signed_positive_symmetric_inverse :
    ∃ B : ℝ →L[ℝ] ℝ, IsSelfAdjoint B ∧ 0 < ⟪B 1, 1⟫ ∧
      (Covariance.operator (compactPosterior ActualLocalThird.atomic
        ActualLocalThird.atomic_compact_support 1 (-ContinuousLinearMap.id ℝ ℝ) : Measure ℝ)).comp B =
          ContinuousLinearMap.id ℝ ℝ ∧
      B.comp (Covariance.operator (compactPosterior ActualLocalThird.atomic
        ActualLocalThird.atomic_compact_support 1 (-ContinuousLinearMap.id ℝ ℝ) : Measure ℝ)) =
          ContinuousLinearMap.id ℝ ℝ := by
  obtain ⟨B, hB, hp, hAB, hBA⟩ := KLS.Isotropic.compactPosterior_exists_positive_symmetric_inverse
    ActualLocalThird.atomic ActualLocalThird.atomic_compact_support ActualLocalThird.atomic_isotropic
    (1 : ℝ) (-ContinuousLinearMap.id ℝ ℝ)
  exact ⟨B, hB, hp 1 (by norm_num), hAB, hBA⟩

private theorem noncentered_covariance_identity :
    Covariance.operator (ActualLocalSecond.μ : Measure ℝ) = ContinuousLinearMap.id ℝ ℝ := by
  apply ContinuousLinearMap.ext
  intro u
  apply ext_inner_right ℝ
  intro v
  rw [← cumulant_two_eq_covariance_of_integrable_exp (ActualLocalSecond.μ : Measure ℝ)
    (by norm_num : (0 : ℝ) < 1)
    (compact_support_integrable_exp _ ActualLocalSecond.compact_support 1)]
  simpa only [ContinuousLinearMap.id_apply, Real.inner_apply] using
    ActualLocalSecond.noncentered_second_cumulant_coordinates u v

private theorem noncentered_full : Probability.affineSupport ActualLocalSecond.μ = ⊤ := by
  have h2 := compactPosterior_memLp_id_two ActualLocalSecond.μ ActualLocalSecond.compact_support 0 0
  rw [compactPosterior_zero] at h2
  apply Probability.affineSupport_eq_top_of_covariance_injective ActualLocalSecond.μ h2
  rw [noncentered_covariance_identity]
  exact fun _ _ h => h

/-- Mean1 is genuinely permitted in the generic full-affine-support result. -/
theorem noncentered_all_parameter_pos (c : ℝ) (Q : ℝ →L[ℝ] ℝ) :
    (∫ x : ℝ, x ∂(ActualLocalSecond.μ : Measure ℝ)) = 1 ∧
    0 < ⟪Covariance.operator (compactPosterior ActualLocalSecond.μ
      ActualLocalSecond.compact_support c Q : Measure ℝ) 1, 1⟫ :=
  ⟨ActualLocalSecond.noncentered_mean,
    compactPosterior_covariance_pos_of_affineSupport_eq_top _ _ noncentered_full c Q (by norm_num)⟩

private def pointLaw : ProbabilityMeasure ℝ := ⟨Measure.dirac 0, inferInstance⟩
private theorem point_compact : IsCompact (pointLaw : Measure ℝ).support := by
  have hsub : (pointLaw : Measure ℝ).support ⊆ ({(0 : ℝ)} : Set ℝ) :=
    Measure.support_subset_of_isClosed isClosed_singleton (by simp [pointLaw])
  exact isCompact_singleton.of_isClosed_subset (pointLaw : Measure ℝ).isClosed_support hsub

private theorem point_posterior (c : ℝ) (Q : ℝ →L[ℝ] ℝ) :
    compactPosterior pointLaw point_compact c Q = pointLaw := by
  apply ProbabilityMeasure.toMeasure_injective
  change (Measure.dirac (0 : ℝ)).tilted (quadraticExponent c Q) = Measure.dirac 0
  have he : quadraticExponent c Q =ᵐ[Measure.dirac (0 : ℝ)] (0 : ℝ → ℝ) := by
    simp [Filter.EventuallyEq, quadraticExponent]
  rw [tilted_congr he, tilted_zero]

private theorem point_covariance_zero : Covariance.operator (pointLaw : Measure ℝ) = 0 := by
  apply ContinuousLinearMap.ext
  intro u
  apply ext_inner_right ℝ
  intro v
  rw [Covariance.operator_inner, zero_apply, inner_zero_left]
  change covarianceBilin (Measure.dirac (0 : ℝ)) u v = 0
  rw [covarianceBilin_real, variance_dirac]
  simp

/-- In positive dimension, compact support without fullness gives a genuine zero covariance
and a nonunit at every parameter, so the source isotropy/full-affine condition is necessary. -/
theorem positive_dim_zero_domain (c : ℝ) (Q : ℝ →L[ℝ] ℝ) :
    Covariance.operator (compactPosterior pointLaw point_compact c Q : Measure ℝ) = 0 ∧
    ¬ IsUnit (Covariance.operator (compactPosterior pointLaw point_compact c Q : Measure ℝ)) := by
  rw [point_posterior, point_covariance_zero]
  exact ⟨rfl, not_isUnit_zero⟩

open ActualLocalThird (ZeroSpace zeroLaw)
private theorem zero_compact : IsCompact (zeroLaw : Measure ZeroSpace).support :=
  isCompact_univ.of_isClosed_subset (zeroLaw : Measure ZeroSpace).isClosed_support (Set.subset_univ _)

/-- The actual rank0 source has covariance0 AND an actual unit: id=0 in this operator ring. -/
theorem rank0_zero_covariance_isUnit (c : ZeroSpace) (Q : ZeroSpace →L[ℝ] ZeroSpace) :
    Covariance.operator (compactPosterior zeroLaw zero_compact c Q : Measure ZeroSpace) = 0 ∧
    IsUnit (Covariance.operator (compactPosterior zeroLaw zero_compact c Q : Measure ZeroSpace)) := by
  refine ⟨?_, KLS.Isotropic.compactPosterior_covariance_isUnit _ _ ActualLocalThirdScope.rank0_isotropic c Q⟩
  apply ContinuousLinearMap.ext
  intro v
  exact Subsingleton.elim _ _

theorem rank0_actual_inverse (c : ZeroSpace) (Q : ZeroSpace →L[ℝ] ZeroSpace) :
    ∃ B : ZeroSpace →L[ℝ] ZeroSpace,
      (Covariance.operator (compactPosterior zeroLaw zero_compact c Q : Measure ZeroSpace)).comp B =
        ContinuousLinearMap.id ℝ ZeroSpace ∧
      B.comp (Covariance.operator (compactPosterior zeroLaw zero_compact c Q : Measure ZeroSpace)) =
        ContinuousLinearMap.id ℝ ZeroSpace :=
  KLS.Isotropic.compactPosterior_exists_covariance_inverse _ _ ActualLocalThirdScope.rank0_isotropic c Q
end ActualPosteriorDomainClients

namespace ActualPosteriorGeneratorSource
open FunctionalInequalities.Probability.Posterior
open ActualLocalThird (atomic atomic_compact_support atomic_isotropic ZeroSpace zeroLaw)

private theorem atomic_bound : ∀ x ∈ (atomic : Measure ℝ).support, ‖id x‖ ≤ (1 : ℝ) := by
  intro x hx
  have hae : ({(-1 : ℝ), 1} : Set ℝ) ∈ ae (atomic : Measure ℝ) := by
    rw [mem_ae_iff]
    change (((1 / 2 : ENNReal) • Measure.dirac (-1 : ℝ) +
      (1 / 2 : ENNReal) • Measure.dirac (1 : ℝ) : Measure ℝ)
      ({(-1 : ℝ), 1} : Set ℝ)ᶜ) = 0
    simp
  have hs : (atomic : Measure ℝ).support ⊆ ({(-1 : ℝ), 1} : Set ℝ) := by
    exact Measure.support_subset_of_isClosed (isClosed_singleton.union isClosed_singleton) hae
  rcases hs hx with h | h
  · subst x
    norm_num
  · simp only [Set.mem_singleton_iff] at h
    subst x
    norm_num

/-- Signed parameters `(1, −Id)` for the atomic isotropic prior: generator cancellation at the literal inverse
posterior covariance. -/
theorem signed_actual_generator :
    let Q : ℝ →L[ℝ] ℝ := -ContinuousLinearMap.id ℝ ℝ
    let A := Covariance.operator (compactPosterior atomic atomic_compact_support 1 Q : Measure ℝ)
    let M := Ring.inverse A
    fderiv ℝ (fun y => posteriorExpectation atomic y Q id) 1 (M (posteriorMean atomic 1 Q)) +
      deriv (fun t : ℝ => posteriorExpectation atomic 1 (Q + t • M) id) 0 +
      (1 / 2 : ℝ) * (∑ i : Fin 1, bilinearIteratedFDerivTwo ℝ
        (fun y => posteriorExpectation atomic y Q id) 1
        (M ((OrthonormalBasis.singleton (Fin 1) ℝ) i))
        ((OrthonormalBasis.singleton (Fin 1) ℝ) i)) = 0 := by
  exact KLS.Isotropic.compactPosterior_generator_cancellation atomic atomic_compact_support atomic_isotropic
    measurable_id (by norm_num : (0 : ℝ) ≤ 1) atomic_bound 1
    (-ContinuousLinearMap.id ℝ ℝ) (OrthonormalBasis.singleton (Fin 1) ℝ)

/-- The linear response of that signed posterior is strictly positive (not a zero witness). -/
theorem signed_response_positive :
    0 < fderiv ℝ (fun y => posteriorExpectation atomic y (-ContinuousLinearMap.id ℝ ℝ) id) 1 1 := by
  rw [fderiv_posteriorExpectation_c_apply atomic atomic_compact_support measurable_id
    (by norm_num : (0 : ℝ) ≤ 1) atomic_bound]
  have hp := KLS.Isotropic.compactPosterior_covariance_pos atomic atomic_compact_support atomic_isotropic
    (1 : ℝ) (-ContinuousLinearMap.id ℝ ℝ) (by norm_num : (1 : ℝ) ≠ 0)
  rw [Covariance.operator_inner, covarianceBilin_real] at hp
  have he : (fun x : ℝ => ⟪(1 : ℝ), x⟫) = id := by funext x; simp
  rw [he]
  change 0 < covariance (fun x : ℝ => x) (fun x : ℝ => x) _
  rw [covariance_self aemeasurable_id']
  simp only [mul_one, one_mul, compactPosterior] at hp
  convert! hp using 1

private theorem rank0_compact : IsCompact (zeroLaw : Measure ZeroSpace).support :=
  isCompact_univ.of_isClosed_subset (zeroLaw : Measure ZeroSpace).isClosed_support (Set.subset_univ _)

/-- Rank-zero initial pair with the literal inverse rate. -/
theorem rank0_actual_generator :
    let A := Covariance.operator (compactPosterior zeroLaw rank0_compact 0 0 : Measure ZeroSpace)
    let M := Ring.inverse A
    fderiv ℝ (fun y => posteriorExpectation zeroLaw y 0 (fun _ => (1 : ℝ))) 0
      (M (posteriorMean zeroLaw 0 0)) +
      deriv (fun t : ℝ => posteriorExpectation zeroLaw 0 (t • M) (fun _ => (1 : ℝ))) 0 +
      (1 / 2 : ℝ) * (∑ i, bilinearIteratedFDerivTwo ℝ
        (fun y => posteriorExpectation zeroLaw y 0 (fun _ => (1 : ℝ))) 0
        (M (stdOrthonormalBasis ℝ ZeroSpace i)) (stdOrthonormalBasis ℝ ZeroSpace i)) = 0 := by
  simpa only [zero_add] using KLS.Isotropic.compactPosterior_generator_cancellation zeroLaw rank0_compact
    ActualLocalThirdScope.rank0_isotropic measurable_const
    (by norm_num : (0 : ℝ) ≤ 1) (by intro x hx; norm_num) 0 0
    (stdOrthonormalBasis ℝ ZeroSpace)
end ActualPosteriorGeneratorSource

namespace ActualPrincipalSource
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
open ActualLocalThird (atomic atomic_compact_support atomic_isotropic ZeroSpace zeroLaw)

/-- The atomic isotropic prior at signed `(1, −Id)`: positive principal root with the Gram relations. -/
theorem signed_atomic_principal :
    let A := Covariance.operator (compactPosterior atomic atomic_compact_support
      1 (-ContinuousLinearMap.id ℝ ℝ) : Measure ℝ)
    let σ := inverseSqrt A
    0 < σ 1 ∧ σ * σ.adjoint = Ring.inverse A ∧
      A * (σ * σ.adjoint) = 1 ∧ (σ * σ.adjoint) * A = 1 := by
  obtain ⟨_, _, hp, _, hg, hl, hr⟩ := KLS.Isotropic.compactPosterior_inverseSqrt_spec atomic
    atomic_compact_support atomic_isotropic 1 (-ContinuousLinearMap.id ℝ ℝ)
  exact ⟨by simpa using hp 1 (by norm_num), hg, hl, hr⟩

/-- Initial coefficient `Id` for the atomic prior. -/
theorem atomic_initial_root :
    inverseSqrt (Covariance.operator (compactPosterior atomic atomic_compact_support
      0 0 : Measure ℝ)) = ContinuousLinearMap.id ℝ ℝ :=
  KLS.Isotropic.inverseSqrt_covariance_compactPosterior_zero atomic atomic_compact_support atomic_isotropic

private theorem zero_compact : IsCompact (zeroLaw : Measure ZeroSpace).support :=
  isCompact_univ.of_isClosed_subset (zeroLaw : Measure ZeroSpace).isClosed_support (Set.subset_univ _)

/-- Rank zero: the root is `0 = Id` and all relations hold. -/
theorem rank0_source_principal (c : ZeroSpace) (Q : ZeroSpace →L[ℝ] ZeroSpace) :
    let A := Covariance.operator (compactPosterior zeroLaw zero_compact c Q : Measure ZeroSpace)
    let σ := inverseSqrt A
    σ = 0 ∧ IsSelfAdjoint σ ∧ σ.IsPositive ∧
      σ * σ.adjoint = Ring.inverse A ∧ A * (σ * σ.adjoint) = 1 ∧
      (σ * σ.adjoint) * A = 1 := by
  obtain ⟨hsa, hp, _, _, hg, hl, hr⟩ := KLS.Isotropic.compactPosterior_inverseSqrt_spec zeroLaw zero_compact
    ActualLocalThirdScope.rank0_isotropic c Q
  exact ⟨Subsingleton.elim _ _, hsa, hp, hg, hl, hr⟩

/-- A positive-dimensional Dirac law has covariance `0`, not a unit: outside the domain. -/
theorem positive_dim_dirac_excluded :
    Covariance.operator (Measure.dirac (0 : ℝ)) = 0 ∧
      ¬ IsUnit (Covariance.operator (Measure.dirac (0 : ℝ))) := by
  have hz : Covariance.operator (Measure.dirac (0 : ℝ)) = 0 := by
    apply ContinuousLinearMap.ext
    intro u
    apply ext_inner_right ℝ
    intro v
    rw [Covariance.operator_inner, zero_apply, inner_zero_left]
    rw [covarianceBilin_real, variance_dirac]
    simp
  rw [hz]
  exact ⟨rfl, not_isUnit_zero⟩
end ActualPrincipalSource

#print axioms FunctionalInequalities.Analysis.BakryEmery.cumulant_three_eq_integral_of_integrable_exp
#print axioms FunctionalInequalities.Analysis.BakryEmery.memLp_of_polynomial_bound_of_integrable_exp
#print axioms FunctionalInequalities.Analysis.BakryEmery.sum_sq_cumulant_three_le_of_letwin_of_integrable_exp
#print axioms FunctionalInequalities.Analysis.BakryEmery.sum_sq_cumulant_three_le_of_letwin_of_integrable_exp_basis
#print axioms FunctionalInequalities.Analysis.BakryEmery.compact_support_integrable_exp
#print axioms FunctionalInequalities.Analysis.BakryEmery.compact_support_memLp_poly
#print axioms FunctionalInequalities.Analysis.BakryEmery.compact_support_integrable_norm_pow
#print axioms FunctionalInequalities.KLS.LogConcave.sum_sq_cumulant_three_le_of_letwin
#print axioms FunctionalInequalities.KLS.LogConcave.Suspension.cumulantBound_two_of_letwin
#print axioms ActualLocalThird.laplace_third_moment
#print axioms ActualLocalThird.atomic_actual_contraction
#print axioms ActualLocalThird.rank0_third_moment
#print axioms ActualLocalThirdScope.laplace_rate_not_integrable
#print axioms ActualLocalThirdScope.gaussian_source_conditional
#print axioms ActualLocalThirdScope.rank0_source_contraction
#print axioms ActualSkewLocalThird.third_cumulant_nonzero
#print axioms ActualLaplaceLocalThird.source_conditional_sqrt_two
#print axioms ActualLocalThirdScope.isotropic_logConcave_without_all_exponential_moments
#print axioms FunctionalInequalities.Analysis.BakryEmery.cumulant_two_eq_centered_moment_of_integrable_exp
#print axioms FunctionalInequalities.Analysis.BakryEmery.cumulant_two_eq_covariance_of_integrable_exp
#print axioms FunctionalInequalities.KLS.LogConcave.cumulant_two_eq_inner_of_isotropic
#print axioms FunctionalInequalities.KLS.LogConcave.sum_sq_cumulant_two_eq_norm_sq_of_isotropic
#print axioms FunctionalInequalities.KLS.LogConcave.Suspension.cumulantBound_one_one
#print axioms ActualLocalSecond.noncentered_second_cumulant
#print axioms ActualLocalSecond.laplace_source_second_cumulant
#print axioms ActualLocalSecond.gaussian_source_parseval
#print axioms ActualLocalSecond.rank0_original_global_base
#print axioms FunctionalInequalities.Probability.tilted_null_iff
#print axioms FunctionalInequalities.Probability.support_tilted_eq
#print axioms FunctionalInequalities.Analysis.isUnit_of_inner_self_pos
#print axioms FunctionalInequalities.Analysis.eq_ringInverse_of_comp_eq_id
#print axioms FunctionalInequalities.Covariance.inner_operator_self_pos_of_affineSupport_eq_top
#print axioms FunctionalInequalities.Probability.affineSupport_eq_top_of_covariance_injective
#print axioms FunctionalInequalities.Covariance.operator_isSelfAdjoint
#print axioms FunctionalInequalities.Probability.Posterior.compactPosterior_affineSupport
#print axioms FunctionalInequalities.Probability.Posterior.compactPosterior_covariance_pos_of_affineSupport_eq_top
#print axioms FunctionalInequalities.KLS.Isotropic.affineSupport_eq_top
#print axioms FunctionalInequalities.KLS.Isotropic.compactPosterior_exists_positive_symmetric_inverse
#print axioms FunctionalInequalities.KLS.Isotropic.compactPosterior_ringInverse_covariance
#print axioms ActualPosteriorDomainClients.signed_positive_symmetric_inverse
#print axioms ActualPosteriorDomainClients.noncentered_all_parameter_pos
#print axioms ActualPosteriorDomainClients.positive_dim_zero_domain
#print axioms ActualPosteriorDomainClients.rank0_zero_covariance_isUnit
#print axioms FunctionalInequalities.KLS.Isotropic.compactPosterior_generator_cancellation
#print axioms FunctionalInequalities.KLS.Isotropic.ringInverse_covariance_compactPosterior_zero
#print axioms ActualPosteriorGeneratorSource.signed_actual_generator
#print axioms ActualPosteriorGeneratorSource.signed_response_positive
#print axioms ActualPosteriorGeneratorSource.rank0_actual_generator
#print axioms FunctionalInequalities.KLS.Isotropic.compactPosterior_covariance_isPositive
#print axioms FunctionalInequalities.KLS.Isotropic.compactPosterior_inverseSqrt_spec
#print axioms FunctionalInequalities.KLS.Isotropic.inverseSqrt_covariance_compactPosterior_zero
#print axioms ActualPrincipalSource.signed_atomic_principal
#print axioms ActualPrincipalSource.rank0_source_principal
#print axioms ActualPrincipalSource.positive_dim_dirac_excluded

namespace IndependentCGFJets
/-! CGF gradient jets (`Analysis/BakryEmery/Cumulant/Local.lean` section `GradientJets`; units CGF1-M, CGF1-C,
independently accepted, receipt 279f7bea…): the Codex reviewer's consumers — the noncentred atom at `3` has
`∇Λ(0) = 3`, the scalar covariance identity, and dimension zero for both statements. -/
open FunctionalInequalities.Analysis

theorem mean_contract {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) :
    gradient (logLaplace (μ : Measure E)) 0 = ∫ x, x ∂(μ : Measure E) :=
  gradient_logLaplace_zero_of_compact μ hc

def atom (a : ℝ) : ProbabilityMeasure ℝ := ⟨Measure.dirac a, inferInstance⟩
lemma atom_compact (a : ℝ) : IsCompact (atom a : Measure ℝ).support := by
  have hs : (Measure.dirac a).support ⊆ {a} :=
    Measure.support_subset_of_isClosed isClosed_singleton (by simp)
  exact isCompact_singleton.of_isClosed_subset Measure.isClosed_support hs

theorem noncentered_atom : gradient (logLaplace (atom 3 : Measure ℝ)) 0 = 3 := by
  rw [gradient_logLaplace_zero_of_compact (atom 3) (atom_compact 3)]
  simp [atom]

theorem mean_empty (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin 0)))
    (hc : IsCompact (μ : Measure (EuclideanSpace ℝ (Fin 0))).support) :
    gradient (logLaplace (μ : Measure (EuclideanSpace ℝ (Fin 0)))) 0 = 0 := by
  rw [gradient_logLaplace_zero_of_compact μ hc]
  exact Subsingleton.elim _ _

theorem actual_scalar_covariance (μ : ProbabilityMeasure ℝ)
    (hc : IsCompact (μ : Measure ℝ).support) (u w : ℝ) :
    ⟪fderiv ℝ (fun z : ℝ => gradient (logLaplace (μ : Measure ℝ)) z -
      gradient (logLaplace (μ : Measure ℝ)) 0) 0 u, w⟫ =
    ⟪Covariance.operator (μ : Measure ℝ) u, w⟫ := by
  rw [fderiv_centeredGradient_logLaplace_zero_of_compact μ hc]

theorem covariance_empty (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin 0)))
    (hc : IsCompact (μ : Measure (EuclideanSpace ℝ (Fin 0))).support) :
    fderiv ℝ (fun z : EuclideanSpace ℝ (Fin 0) =>
      gradient (logLaplace (μ : Measure (EuclideanSpace ℝ (Fin 0)))) z -
      gradient (logLaplace (μ : Measure (EuclideanSpace ℝ (Fin 0)))) 0) 0 =
    Covariance.operator (μ : Measure (EuclideanSpace ℝ (Fin 0))) :=
  fderiv_centeredGradient_logLaplace_zero_of_compact μ hc
end IndependentCGFJets

#print axioms FunctionalInequalities.Analysis.BakryEmery.cumulantVector_inner
#print axioms FunctionalInequalities.Analysis.BakryEmery.gradient_logLaplace_zero_of_compact
#print axioms FunctionalInequalities.Analysis.BakryEmery.fderiv_centeredGradient_logLaplace_zero_of_compact
#print axioms IndependentCGFJets.noncentered_atom
#print axioms IndependentCGFJets.mean_empty
#print axioms IndependentCGFJets.actual_scalar_covariance
#print axioms IndependentCGFJets.covariance_empty

/-! Higher jets of the centred CGF gradient (`Analysis/BakryEmery/Cumulant/Local.lean` section `GradientJets`,
`iteratedFDeriv_centeredGradient_logLaplace_zero_of_compact`, with the generic supports of
`Analysis/IteratedDerivative/GradientJet.lean`; Luna units CGF1-J2a/J2b and the J2c v2 assembly, independently accepted
2026-10-08, receipt `CGF-J2a-J2c-Independent-20261008/VERIFICATION.json` 2adda06e…): the independent Codex reviewer's
consumers — the noncentred two-atom law `(δ₀ + δ₂)/2` (gradient `1` at `0`, centred value `0`, first jet `1`, the
order-three jet paired with the literal fourth cumulant in slots `1, 2, 3; 4`), rank zero at all positive orders, and
the generic shift contract with a quartic on the max-norm product `ℝ × ℝ` (no inner product supplied). -/
namespace IndependentCGFHigherJets
def μ : ProbabilityMeasure ℝ :=
  ⟨(1 / 2 : ENNReal) • Measure.dirac 0 + (1 / 2 : ENNReal) • Measure.dirac 2, by
    constructor
    norm_num
    exact ENNReal.inv_two_add_inv_two⟩

private theorem integral_μ (g : ℝ → ℝ) :
    (∫ x, g x ∂(μ : Measure ℝ)) = (1 / 2 : ℝ) * g 0 + (1 / 2 : ℝ) * g 2 := by
  have h0 : Integrable g ((1 / 2 : ENNReal) • Measure.dirac (0 : ℝ)) :=
    (integrable_dirac (by simp)).smul_measure (by norm_num)
  have h2 : Integrable g ((1 / 2 : ENNReal) • Measure.dirac (2 : ℝ)) :=
    (integrable_dirac (by simp)).smul_measure (by norm_num)
  change (∫ x, g x ∂((1 / 2 : ENNReal) • Measure.dirac 0 +
    (1 / 2 : ENNReal) • Measure.dirac 2)) = _
  rw [integral_add_measure h0 h2, integral_smul_measure, integral_smul_measure]
  norm_num

theorem compact_μ : IsCompact (μ : Measure ℝ).support := by
  have hsub : (μ : Measure ℝ).support ⊆ ({(0 : ℝ), 2} : Set ℝ) := by
    apply Measure.support_subset_of_isClosed (isClosed_singleton.union isClosed_singleton)
    rw [mem_ae_iff]
    change (((1 / 2 : ENNReal) • Measure.dirac (0 : ℝ) +
      (1 / 2 : ENNReal) • Measure.dirac 2) : Measure ℝ) ({(0 : ℝ), 2} : Set ℝ)ᶜ = 0
    simp
  exact (Set.toFinite ({(0 : ℝ), 2} : Set ℝ)).isCompact.of_isClosed_subset
    (μ : Measure ℝ).isClosed_support hsub

def v (z : ℝ) : ℝ := gradient (logLaplace (μ : Measure ℝ)) z -
  gradient (logLaplace (μ : Measure ℝ)) 0

/-- The source law is really noncentered: its actual CGF gradient at zero is one. -/
theorem noncentered_gradient : gradient (logLaplace (μ : Measure ℝ)) 0 = 1 := by
  rw [gradient_logLaplace_zero_of_compact μ compact_μ, integral_μ]
  norm_num

theorem centered_initial : v 0 = 0 := by simp [v]

private theorem actual_second_cumulant : cumulant (μ : Measure ℝ) 2 ![1,1] = 1 := by
  have h := cumulant_two_eq_centered_moment_of_integrable_exp (μ : Measure ℝ)
    (by norm_num : (0 : ℝ) < 1) (compact_support_integrable_exp _ compact_μ 1) 1 1
  simp only [integral_μ, Real.inner_apply] at h
  norm_num at h
  exact h

private theorem actual_second_vector : cumulantVector (μ : Measure ℝ) [1] = 1 := by
  have h := cumulantVector_inner (μ : Measure ℝ) [1] 1
  have hd : Fin.snoc (fun i : Fin [((1 : ℝ))].length => [((1 : ℝ))].get i) 1 = ![1,1] := by
    ext i
    fin_cases i <;> rfl
  rw [hd] at h
  simpa only [Real.inner_apply, mul_one, List.length_cons, List.length_nil, Nat.reduceAdd,
    actual_second_cumulant] using h

/-- Nonzero real first jet: no supplied mean/covariance/jet hypothesis. -/
theorem actual_first_jet : fderiv ℝ v 0 1 = 1 := by
  have h := iteratedFDeriv_centeredGradient_logLaplace_zero_of_compact μ compact_μ 1
    (by norm_num) (fun _ => 1)
  have hl : List.ofFn (fun _ : Fin 1 => (1 : ℝ)) = [1] := by simp
  rw [hl, actual_second_vector] at h
  change fderiv ℝ (fun z : ℝ => gradient (logLaplace (μ : Measure ℝ)) z -
    gradient (logLaplace (μ : Measure ℝ)) 0) 0 1 = 1
  simpa only [iteratedFDeriv_one_apply] using h

/-- Actual order-three centered jet pairs with the fourth cumulant in the exact last
slot. The nonconstant directions and fourth slot are literal, not diagonal aliases. -/
theorem actual_higher_jet :
    ⟪iteratedFDeriv ℝ 3 v 0 ![1,2,3], (4 : ℝ)⟫ =
      cumulant (μ : Measure ℝ) 4 ![1,2,3,4] := by
  have h := iteratedFDeriv_centeredGradient_logLaplace_zero_of_compact μ compact_μ 3
    (by norm_num) ![(1 : ℝ),2,3]
  have hl : List.ofFn ![(1 : ℝ),2,3] = [1,2,3] := by simp [List.ofFn_succ]
  rw [hl] at h
  change ⟪iteratedFDeriv ℝ 3 (fun z : ℝ => gradient (logLaplace (μ : Measure ℝ)) z -
      gradient (logLaplace (μ : Measure ℝ)) 0) 0 ![1,2,3], (4 : ℝ)⟫ = _
  rw [h, cumulantVector_inner]
  congr 1
  ext i
  fin_cases i <;> rfl

abbrev E0 := EuclideanSpace ℝ (Fin 0)
def μ0 : ProbabilityMeasure E0 := ⟨Measure.dirac 0, inferInstance⟩
private theorem compact_μ0 : IsCompact (μ0 : Measure E0).support :=
  isCompact_univ.of_isClosed_subset (μ0 : Measure E0).isClosed_support (Set.subset_univ _)

theorem actual_rank0_all_orders (r : ℕ) (hr : 1 ≤ r) (h : Fin r → E0) :
    iteratedFDeriv ℝ r (fun z : E0 => gradient (logLaplace (μ0 : Measure E0)) z -
      gradient (logLaplace (μ0 : Measure E0)) 0) 0 h = 0 :=
  (iteratedFDeriv_centeredGradient_logLaplace_zero_of_compact μ0 compact_μ0 r hr h).trans
    (Subsingleton.elim _ _)

#print axioms noncentered_gradient
#print axioms centered_initial
#print axioms actual_first_jet
#print axioms actual_higher_jet
#print axioms actual_rank0_all_orders
end IndependentCGFHigherJets

namespace IndependentGenericShift
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem full_original_contract {f : E → F} (hf : ContDiff ℝ ∞ f) (c : F)
    {r : ℕ} (hr : 1 ≤ r) (x : E) :
    iteratedFDeriv ℝ r (fun z => f z - c) x = iteratedFDeriv ℝ r f x :=
  FunctionalInequalities.Analysis.iteratedFDeriv_sub_const_of_pos hf c hr x

/-- The ordinary product has its max norm; no inner-product structure is supplied. -/
theorem product_quartic :
    iteratedFDeriv ℝ 4 (fun x : ℝ × ℝ => x.1 ^ 4 - 7) (0,0) =
      iteratedFDeriv ℝ 4 (fun x : ℝ × ℝ => x.1 ^ 4) (0,0) :=
  full_original_contract (by fun_prop) 7 (by norm_num) (0,0)

#print axioms full_original_contract
#print axioms product_quartic
end IndependentGenericShift
