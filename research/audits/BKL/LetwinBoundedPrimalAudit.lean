module

public import FunctionalInequalities.Analysis.BakryEmery.Cumulant.Local
public import FunctionalInequalities.Analysis.BakryEmery.Cumulant.Basic
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import FunctionalInequalities.KLS.Isotropic
public import FunctionalInequalities.KLS.CEK.BoundedPrimal

/-!
# Audit: the bounded-source normalized primal for the uniform law on `[-√3, √3]`

Source: Cordero-Erausquin–Klartag Proposition 12 / Theorem 2 and Letwin, arXiv:2607.24164v1,
Lemmas 2.1–2.2 (support only). The fixed law is the uniform law on `[-√3, √3]`; its boundedness
(`‖y‖ ≤ √3` almost everywhere), finite second moment, zero mean, isotropy and second moment `1` are
derived here with no premise, and the library producer `bounded_source_lipschitz_primal` is
invoked, retaining every conclusion; the density `ofReal (exp (−ψ))` is a probability. A weak
normalized primal: no Euler–Lagrange identification, gradient pushforward, smoothness, positive
Hessian, diffeomorphism, Monge–Ampère equation or Theorem 2.5.

Witness blocks: `unifSym`, `isProbabilityMeasure_unifSym`, `integral_unifSym`, `centered_unifSym`
and `isotropic_unifSym` repeat those of `SingletonAllocationAudit.lean` (namespace
`BKLThirdCumulantWitness` there, `LetwinBoundedPrimalWitness` here); no other block of that audit is
copied.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace LetwinBoundedPrimalWitness

open FunctionalInequalities.Analysis.BakryEmery

/-- The uniform law on `[-√3, √3]`. -/
def unifSym : Measure ℝ := (volume : Measure ℝ)[|Set.Icc (-Real.sqrt 3) (Real.sqrt 3)]

theorem isProbabilityMeasure_unifSym : IsProbabilityMeasure unifSym := by
    have hs : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.2 (by norm_num)
    have hdiff : 0 < Real.sqrt (3 : ℝ) - -Real.sqrt 3 := by
      linarith
    refine ⟨?_⟩
    simp only [unifSym, ProbabilityTheory.cond, Real.volume_Icc]
    simp
    exact ENNReal.inv_mul_cancel (by positivity) (by simp)

theorem integral_unifSym (f : ℝ → ℝ) :
    ∫ x, f x ∂unifSym = (2 * Real.sqrt 3)⁻¹ * ∫ x in (-Real.sqrt 3)..(Real.sqrt 3), f x := by
    have hs : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg _
    have hle : -Real.sqrt 3 ≤ Real.sqrt 3 := by
      linarith
    have hpos : 0 < 2 * Real.sqrt 3 := by
      positivity
    have hvol :
        volume (Set.Icc (-Real.sqrt 3) (Real.sqrt 3)) =
          ENNReal.ofReal (2 * Real.sqrt 3) := by
      rw [Real.volume_Icc]
      congr 1
      ring
    have hcoeff :
        ENNReal.toReal
            ((volume (Set.Icc (-Real.sqrt 3) (Real.sqrt 3)))⁻¹) =
          (2 * Real.sqrt 3)⁻¹ := by
      rw [hvol, ENNReal.toReal_inv, ENNReal.toReal_ofReal hpos.le]
    rw [unifSym, ProbabilityTheory.cond, integral_smul_measure, hcoeff]
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
    rw [← intervalIntegral.integral_of_le hle]
    simp [smul_eq_mul]

theorem centered_unifSym (v : ℝ) : ∫ x, ⟪v, x⟫ ∂unifSym = 0 := by
  rw [integral_unifSym]
  have h : (fun x : ℝ => ⟪v, x⟫) = fun x => v * x := by
    funext x
    simp [RCLike.inner_apply, conj_trivial, mul_comm]
  rw [h, intervalIntegral.integral_const_mul, integral_id]
  ring

theorem isotropic_unifSym (v w : ℝ) : ∫ x, ⟪v, x⟫ * ⟪w, x⟫ ∂unifSym = ⟪v, w⟫ := by
  rw [integral_unifSym]
  have h : (fun x : ℝ => ⟪v, x⟫ * ⟪w, x⟫) = fun x => (v * w) * x ^ 2 := by
    funext x
    simp [RCLike.inner_apply, conj_trivial]
    ring
  rw [h, intervalIntegral.integral_const_mul, integral_pow]
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hvw : ⟪v, w⟫ = v * w := by simp [RCLike.inner_apply, conj_trivial, mul_comm]
  rw [hvw]
  field_simp
  have h33 : Real.sqrt 3 ^ 3 = 3 * Real.sqrt 3 := by rw [pow_succ, h3]
  linear_combination 2 * (v * w) * h33

end LetwinBoundedPrimalWitness

namespace LetwinBoundedPrimalAudit

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal Topology RealInnerProductSpace

open FunctionalInequalities
open FunctionalInequalities.Analysis
open FunctionalInequalities.KLS
open FunctionalInequalities.Probability
open FunctionalInequalities.Probability.MomentMeasure

/-- The actual bundled uniform probability law on `[-√3, √3]`. -/
def mu : ProbabilityMeasure ℝ :=
  ⟨LetwinBoundedPrimalWitness.unifSym,
    LetwinBoundedPrimalWitness.isProbabilityMeasure_unifSym⟩

/-- The fixed nonnegative bound, not a client parameter. -/
def L : NNReal := ⟨Real.sqrt 3, Real.sqrt_nonneg _⟩

/-- The bundled measure is definitionally the uniform witness. -/
theorem mu_measure :
    (mu : Measure ℝ) = LetwinBoundedPrimalWitness.unifSym := rfl

/-- Interval support follows directly from the conditional restricted measure. -/
theorem mu_ae_mem_Icc :
    ∀ᵐ x ∂(mu : Measure ℝ),
      x ∈ Icc (-Real.sqrt 3) (Real.sqrt 3) := by
  rw [ae_iff]
  change
    (((volume : Measure ℝ) (Icc (-Real.sqrt 3) (Real.sqrt 3)))⁻¹ •
      (volume : Measure ℝ).restrict (Icc (-Real.sqrt 3) (Real.sqrt 3)))
        (Icc (-Real.sqrt 3) (Real.sqrt 3))ᶜ = 0
  rw [Measure.smul_apply,
    Measure.restrict_apply (isClosed_Icc.measurableSet.compl)]
  simp

/-- The actual source satisfies the fixed `√3` norm bound almost everywhere. -/
theorem mu_ae_norm_le :
    ∀ᵐ x ∂(mu : Measure ℝ), ‖x‖ ≤ (L : ℝ) := by
  filter_upwards [mu_ae_mem_Icc] with x hx
  change ‖x‖ ≤ Real.sqrt 3
  rw [Real.norm_eq_abs]
  exact abs_le.mpr hx

/-- Finite second moment is proved from the actual almost-everywhere bound. -/
theorem mu_memLp_two : MemLp id 2 (mu : Measure ℝ) := by
  exact MemLp.of_bound continuous_id.aestronglyMeasurable
    (L : ℝ) mu_ae_norm_le

/-- The scalar centering identity gives the actual barycenter. -/
theorem mu_mean_zero :
    (∫ x : ℝ, x ∂(mu : Measure ℝ)) = 0 := by
  change (∫ x : ℝ, x ∂LetwinBoundedPrimalWitness.unifSym) = 0
  simpa [RCLike.inner_apply, conj_trivial] using
    LetwinBoundedPrimalWitness.centered_unifSym (1 : ℝ)

/-- Isotropy is constructed from proved integrability and the actual moments. -/
theorem mu_isotropic : KLS.Isotropic mu := by
  exact KLS.isotropic_of_moments mu mu_memLp_two mu_mean_zero
    (fun u v => LetwinBoundedPrimalWitness.isotropic_unifSym u v)

/-- A nonzero second moment: this is not a zero-dimensional or zero-source test. -/
theorem mu_second_moment :
    (∫ x : ℝ, x ^ 2 ∂(mu : Measure ℝ)) = 1 := by
  change (∫ x : ℝ, x ^ 2 ∂LetwinBoundedPrimalWitness.unifSym) = 1
  simpa [RCLike.inner_apply, conj_trivial, pow_two] using
    LetwinBoundedPrimalWitness.isotropic_unifSym (1 : ℝ) (1 : ℝ)

/--
Premise-free fixed-law client of the actual strong bounded-source producer.
All of its finite-conjugate, optimizer, convexity, Lipschitz and normalization
data are retained for this exact uniform source. The probability conclusion
is also exposed for the explicit Lebesgue density `ofReal (exp (-ψ))`.
-/
theorem fixed_uniform_normalized_primal :
    (mu : Measure ℝ) = LetwinBoundedPrimalWitness.unifSym ∧
    KLS.Isotropic mu ∧
    (∀ᵐ y ∂(mu : Measure ℝ), ‖y‖ ≤ (L : ℝ)) ∧
    (∫ x : ℝ, x ^ 2 ∂(mu : Measure ℝ)) = 1 ∧
    ∃ (q : ℝ → EReal) (a m : ℝ) (ψ : ℝ → ℝ),
      ConvexPotential q ∧
      LowerSemicontinuous q ∧
      PotentialIntegrable q (mu : Measure ℝ) ∧
      (∀ y, q y ≠ ⊤ → y ∈ closedBall (0 : ℝ) (L : ℝ)) ∧
      a ∈ closedBall (0 : ℝ) (L : ℝ) ∧
      q a = (m : EReal) ∧
      (∀ y, (m : EReal) ≤ q y) ∧
      (∀ x, legendre q x ≠ ⊤ ∧ legendre q x ≠ ⊥) ∧
      (∀ x, legendre q x ≤ (((L : ℝ) * ‖x‖ - m : ℝ) : EReal)) ∧
      ψ = (fun x => (legendre q x).toReal) ∧
      (∀ x, legendre q x = (ψ x : EReal)) ∧
      mass (volume : Measure ℝ) (legendre q) = 1 ∧
      ConvexOn ℝ (univ : Set ℝ) ψ ∧
      LipschitzWith L ψ ∧
      Continuous ψ ∧
      Integrable (fun x => Real.exp (-ψ x)) (volume : Measure ℝ) ∧
      (∫ x, Real.exp (-ψ x) ∂(volume : Measure ℝ)) = 1 ∧
      IsProbabilityMeasure
        (weightedMeasure (volume : Measure ℝ) (fun x => (ψ x : EReal))) ∧
      IsProbabilityMeasure
        ((volume : Measure ℝ).withDensity
          (fun x => ENNReal.ofReal (Real.exp (-ψ x)))) ∧
      ∀ f : ℝ → EReal, PotentialIntegrable f (mu : Measure ℝ) →
        variationalFunctional (volume : Measure ℝ) (mu : Measure ℝ) f ≤
          variationalFunctional (volume : Measure ℝ) (mu : Measure ℝ) q := by
  refine ⟨mu_measure, mu_isotropic, mu_ae_norm_le, mu_second_moment, ?_⟩
  obtain ⟨q, a, m, ψ, hqconv, hqlsc, hqpot, hqdom, haB, ham, hfloor,
    hfinite, hupper, hdef, hψ, hmass, hconv, hlip, hcont,
    hexp, hint, hprob, hmax⟩ :=
    FunctionalInequalities.KLS.CEK.bounded_source_lipschitz_primal
      mu mu_isotropic L mu_ae_norm_le
  have hdensity :
      density (fun x : ℝ => (ψ x : EReal)) =
        (fun x : ℝ => ENNReal.ofReal (Real.exp (-ψ x))) := by
    funext x
    simp only [density, ← EReal.coe_neg, EReal.exp_coe]
  have hprobDensity : IsProbabilityMeasure
      ((volume : Measure ℝ).withDensity
        (fun x => ENNReal.ofReal (Real.exp (-ψ x)))) := by
    rw [← hdensity]
    exact hprob
  exact ⟨q, a, m, ψ, hqconv, hqlsc, hqpot, hqdom, haB, ham, hfloor,
    hfinite, hupper, hdef, hψ, hmass, hconv, hlip, hcont,
    hexp, hint, hprob, hprobDensity, hmax⟩

end

end LetwinBoundedPrimalAudit

#print axioms FunctionalInequalities.Analysis.closedBallCap_lowerSemicontinuous
#print axioms FunctionalInequalities.Analysis.exists_real_global_minimum_of_bounded_domain
#print axioms FunctionalInequalities.Analysis.legendre_le_of_real_lower_bound
#print axioms FunctionalInequalities.Analysis.legendre_finite_of_bounded_domain
#print axioms FunctionalInequalities.Analysis.real_convexOn_legendre
#print axioms FunctionalInequalities.Analysis.lipschitzWith_real_legendre
#print axioms FunctionalInequalities.Analysis.real_legendre_fenchel
#print axioms FunctionalInequalities.Probability.MomentMeasure.real_legendre_normalization
#print axioms FunctionalInequalities.KLS.CEK.bounded_source_cap_lsc
#print axioms FunctionalInequalities.KLS.CEK.bounded_source_cap
#print axioms FunctionalInequalities.KLS.CEK.bounded_source_finite_conjugate
#print axioms FunctionalInequalities.KLS.CEK.bounded_source_lipschitz_primal
#print axioms FunctionalInequalities.KLS.CEK.bounded_source_real_density_client
#print axioms LetwinBoundedPrimalAudit.mu_isotropic
#print axioms LetwinBoundedPrimalAudit.mu_second_moment
#print axioms LetwinBoundedPrimalAudit.fixed_uniform_normalized_primal
