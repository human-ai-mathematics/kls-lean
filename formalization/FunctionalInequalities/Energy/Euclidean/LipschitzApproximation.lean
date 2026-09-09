import FunctionalInequalities.Energy.SmoothGradient.Basic
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Weighted smooth approximation of locally Lipschitz tests

Source: Blueprint Appendix A, `lem:covariance-test-core-density`, first statement and proof.
Read `exists_smooth_weighted_L2` for the main contract, then the two preceding
intermediate statements for the cutoff / mollification / diagonal proof order. The final theorem
is the bounded L1 variant, preserving an arbitrary closed interval and the Lipschitz constant.
All four statements are proved; no proof placeholder remains in this module.

The space is finite-dimensional real Hilbert, including dimension zero. `m` is an additive Haar
measure: in finite dimension it is a Lebesgue reference measure, with arbitrary positive
normalization. The probability law `ν` is absolutely continuous with respect to `m`.
No log-concavity, density lower bound, translated-density estimate or second moment is required.
`B` is any continuous linear endomorphism, including zero or singular maps. Only `B ∘ gradient g`
must be square-integrable; integrability of the full gradient is not imposed in the main result.

`gradient` is Mathlib's canonical Hilbert gradient, zero at nondifferentiability points.
Rademacher's theorem (`LipschitzWith.ae_differentiableAt`, extended here to locally Lipschitz
functions through compact exhaustion and McShane extension) makes it meaningful `m`-almost
everywhere, hence `ν`-almost everywhere. Convergence is expressed by extended `eLpNorm` of
differences, with membership conditions explicit.

## Proof architecture

* A fixed smooth bump `bump`, rescaled to `scaled R`, provides both the cutoffs `scaled R` (one on
  the ball of radius `R`, zero outside radius `2 * R`) and the normalized mollifiers `kernel m R`
  (supported in radius `2 * R`, total mass one for the actual reference measure `m`).
* `mollify m R g = g ⋆ kernel m R` is smooth, preserves the global Lipschitz constant, preserves
  bounds and compact support, and is uniformly `2 K R`-close to `g`.
* At every differentiability point `x` of `g`, `fderiv (mollify m R g) x → fderiv g x` as `R → 0`.
  The argument compares the convolution derivative with the affine model `g x + L (· - x)`, using
  `integral_affine_smul_fderiv_kernel` and the scale-free derivative mass `kernelDerivativeMass m` of the kernel.
  No weak derivative or Lebesgue differentiation argument is needed.
* Dominated convergence in `L^p(ν)` (`tendsto_eLpNorm_zero_of_dominated`) transfers pointwise
  convergence to the weighted norms; the cutoff step uses the `L²` data `g` and `B ∘ gradient g`
  as dominating functions, and the diagonal selection in the main theorem combines both steps.

These statements do not identify local slope with gradient, compare Poincaré constants,
establish a closed gradient operator, or prove KLS.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ContDiff Convolution ENNReal

namespace FunctionalInequalities.Energy.Euclidean.LipschitzApproximation

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

section Gradient

variable [CompleteSpace E]

theorem norm_gradient_eq_norm_fderiv (f : E → ℝ) (x : E) :
    ‖gradient f x‖ = ‖fderiv ℝ f x‖ :=
  LinearIsometryEquiv.norm_map _ _

theorem norm_gradient_le_of_lipschitz {K : NNReal} {f : E → ℝ} (hf : LipschitzWith K f) (x : E) :
    ‖gradient f x‖ ≤ K := by
  rw [norm_gradient_eq_norm_fderiv]; exact norm_fderiv_le_of_lipschitz ℝ hf

theorem gradient_eq_of_hasFDerivAt {f : E → ℝ} {L : E →L[ℝ] ℝ} {x : E} (h : HasFDerivAt f L x) :
    gradient f x = (InnerProductSpace.toDual ℝ E).symm L :=
  (hasFDerivAt_iff_hasGradientAt.mp h).gradient

end Gradient

section Basic

/-- A fixed smooth bump: one on the closed unit ball, zero outside radius two. -/
def bump : ContDiffBump (0 : E) := ⟨1, 2, one_pos, one_lt_two⟩

/-- The bump rescaled to be one on radius `R` and zero outside radius `2 * R`. -/
def scaled (R : ℝ) (x : E) : ℝ := (bump (E := E)) (R⁻¹ • x)

theorem scaled_nonneg (R : ℝ) (x : E) : 0 ≤ scaled R x := by
  unfold scaled; exact (bump (E := E)).nonneg

theorem scaled_le_one (R : ℝ) (x : E) : scaled R x ≤ 1 := by
  unfold scaled; exact (bump (E := E)).le_one

theorem scaled_eq_one {R : ℝ} (hR : 0 < R) {x : E} (hx : ‖x‖ ≤ R) : scaled R x = 1 := by
  unfold scaled
  apply (bump (E := E)).one_of_mem_closedBall
  show R⁻¹ • x ∈ Metric.closedBall (0 : E) 1
  rw [Metric.mem_closedBall, dist_zero_right, norm_smul, norm_inv, Real.norm_eq_abs,
    abs_of_pos hR, inv_mul_le_iff₀ hR, mul_one]
  exact hx

theorem scaled_eq_zero {R : ℝ} (hR : 0 < R) {x : E} (hx : 2 * R ≤ ‖x‖) : scaled R x = 0 := by
  unfold scaled
  apply (bump (E := E)).zero_of_le_dist
  show (2 : ℝ) ≤ dist (R⁻¹ • x) 0
  rw [dist_zero_right, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hR, le_inv_mul_iff₀ hR]
  linarith

theorem contDiff_scaled (R : ℝ) : ContDiff ℝ ∞ (scaled (E := E) R) := by
  unfold scaled
  exact ((bump (E := E)).contDiff (n := ⊤)).comp (contDiff_const_smul R⁻¹)

theorem continuous_scaled (R : ℝ) : Continuous (scaled (E := E) R) :=
  (contDiff_scaled R).continuous

theorem hasFDerivAt_scaled (R : ℝ) (x : E) :
    HasFDerivAt (scaled R) (R⁻¹ • fderiv ℝ (⇑(bump (E := E))) (R⁻¹ • x)) x := by
  have h1 : HasFDerivAt (fun y : E => R⁻¹ • y) (R⁻¹ • ContinuousLinearMap.id ℝ E) x :=
    (hasFDerivAt_id x).const_smul R⁻¹
  have h2 : HasFDerivAt (⇑(bump (E := E))) (fderiv ℝ (⇑(bump (E := E))) (R⁻¹ • x)) (R⁻¹ • x) :=
    (((bump (E := E)).contDiff (n := 1)).differentiable (by simp) (R⁻¹ • x)).hasFDerivAt
  have h3 : (fderiv ℝ (⇑(bump (E := E))) (R⁻¹ • x)).comp (R⁻¹ • ContinuousLinearMap.id ℝ E) =
      R⁻¹ • fderiv ℝ (⇑(bump (E := E))) (R⁻¹ • x) := by
    ext v
    simp
  unfold scaled
  exact (h2.comp x h1).congr_fderiv h3

theorem fderiv_scaled_eq_zero {R : ℝ} (hR : 0 < R) {x : E} (hx : ‖x‖ < R) :
    fderiv ℝ (scaled R) x = 0 := by
  have h : scaled (E := E) R =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (show x ∈ Metric.ball (0 : E) R by
      simpa [Metric.mem_ball, dist_zero_right] using hx)] with y hy
    exact scaled_eq_one hR (le_of_lt (by simpa [Metric.mem_ball, dist_zero_right] using hy))
  rw [h.fderiv_eq]
  simp

theorem norm_fderiv_scaled_le {R : ℝ} (hR : 0 < R) {M : ℝ}
    (hM : ∀ x : E, ‖fderiv ℝ (⇑(bump (E := E))) x‖ ≤ M) (x : E) :
    ‖fderiv ℝ (scaled R) x‖ ≤ R⁻¹ * M := by
  rw [(hasFDerivAt_scaled R x).fderiv, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hR]
  gcongr
  exact hM _

theorem lipschitzWith_scaled {R : ℝ} (hR : 0 < R) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ x : E, ‖fderiv ℝ (⇑(bump (E := E))) x‖ ≤ M) :
    LipschitzWith (R⁻¹ * M).toNNReal (scaled (E := E) R) := by
  apply lipschitzWith_of_nnnorm_fderiv_le ((contDiff_scaled R).differentiable (by simp))
  intro x
  rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ (by positivity)]
  exact norm_fderiv_scaled_le hR hM x

theorem gradient_scaled_mul [CompleteSpace E] {R : ℝ} {g : E → ℝ} {x : E} (hx : DifferentiableAt ℝ g x) :
    gradient (fun y => scaled R y * g y) x =
      scaled R x • gradient g x + g x • gradient (scaled R) x := by
  have h1 : HasFDerivAt (scaled R) (fderiv ℝ (scaled R) x) x :=
    (hasFDerivAt_scaled R x).differentiableAt.hasFDerivAt
  have h : HasFDerivAt (fun y => scaled R y * g y)
      (scaled R x • fderiv ℝ g x + g x • fderiv ℝ (scaled R) x) x := h1.mul hx.hasFDerivAt
  rw [gradient_eq_of_hasFDerivAt h]
  simp only [map_add, map_smulₛₗ, starRingEnd_apply, star_trivial]
  rfl

end Basic

section FiniteDimensional

variable [FiniteDimensional ℝ E]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- A locally Lipschitz real function is Lipschitz on every compact set. -/
theorem lipschitzOnWith_of_locallyLipschitz_of_isCompact {f : E → ℝ} (hf : LocallyLipschitz f)
    {s : Set E} (hs : IsCompact s) : ∃ K : NNReal, LipschitzOnWith K f s := by
  have key : ∀ x : E, ∃ r : ℝ, 0 < r ∧ ∃ K : NNReal, LipschitzOnWith K f (Metric.ball x r) := by
    intro x
    obtain ⟨K, t, ht, hK⟩ := hf x
    obtain ⟨r, hr, hrt⟩ := Metric.mem_nhds_iff.mp ht
    exact ⟨r, hr, K, hK.mono hrt⟩
  choose r hr K hK using key
  obtain ⟨T, -, hT⟩ := hs.elim_nhds_subcover (fun x => Metric.ball x (r x))
    (fun x _ => Metric.ball_mem_nhds x (hr x))
  obtain ⟨δ, hδ, hcover⟩ := lebesgue_number_lemma_of_metric (ι := T)
    (c := fun i => Metric.ball (i : E) (r i)) hs (fun _ => Metric.isOpen_ball)
    (fun x hx => by
      obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (hT hx)
      exact Set.mem_iUnion.mpr ⟨⟨i, hi⟩, hxi⟩)
  obtain ⟨C, hC⟩ := hs.exists_bound_of_continuousOn hf.continuous.continuousOn
  set K' : NNReal := T.sup K with hK'
  set C' : ℝ := max C 0 with hC'
  refine ⟨(max (K' : ℝ) (2 * C' / δ)).toNNReal, LipschitzOnWith.of_dist_le' ?_⟩
  intro x hx y hy
  by_cases hxy : dist x y < δ
  · obtain ⟨i, hi⟩ := hcover x hx
    have hxi : x ∈ Metric.ball (i : E) (r i) := hi (Metric.mem_ball_self hδ)
    have hyi : y ∈ Metric.ball (i : E) (r i) := hi (by simpa [dist_comm] using hxy)
    have hKi : LipschitzOnWith (K i) f (Metric.ball (i : E) (r i)) := hK i
    calc dist (f x) (f y) ≤ K i * dist x y := hKi.dist_le_mul x hxi y hyi
      _ ≤ K' * dist x y := by
          gcongr
          exact_mod_cast Finset.le_sup (f := K) i.2
      _ ≤ max (K' : ℝ) (2 * C' / δ) * dist x y := by gcongr; exact le_max_left _ _
  · push Not at hxy
    have hCx : ‖f x‖ ≤ C' := (hC x hx).trans (le_max_left _ _)
    have hCy : ‖f y‖ ≤ C' := (hC y hy).trans (le_max_left _ _)
    have hC0 : 0 ≤ C' := le_max_right _ _
    calc dist (f x) (f y) ≤ ‖f x‖ + ‖f y‖ := dist_le_norm_add_norm _ _
      _ ≤ 2 * C' := by linarith
      _ = (2 * C' / δ) * δ := by field_simp
      _ ≤ (2 * C' / δ) * dist x y := by gcongr
      _ ≤ max (K' : ℝ) (2 * C' / δ) * dist x y := by gcongr; exact le_max_right _ _

theorem hasCompactSupport_scaled {R : ℝ} (hR : 0 < R) :
    HasCompactSupport (scaled (E := E) R) :=
  HasCompactSupport.intro (isCompact_closedBall (0 : E) (2 * R)) fun x hx =>
    scaled_eq_zero hR (by
      rw [Metric.mem_closedBall, dist_zero_right] at hx
      exact le_of_lt (not_le.mp hx))

theorem exists_bound_fderiv_bump :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x : E, ‖fderiv ℝ (⇑(bump (E := E))) x‖ ≤ M := by
  have hc : Continuous (fderiv ℝ (⇑(bump (E := E)))) :=
    ((bump (E := E)).contDiff (n := 1)).continuous_fderiv (by simp)
  have hs : HasCompactSupport (fderiv ℝ (⇑(bump (E := E)))) :=
    (bump (E := E)).hasCompactSupport.fderiv (𝕜 := ℝ)
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hs
  exact ⟨max C 0, le_max_right _ _, fun x => (hC x).trans (le_max_left _ _)⟩

end FiniteDimensional

section Measurable

variable [MeasurableSpace E]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
/-- Dominated convergence for the `L^p` seminorm, `0 < p < ∞`. -/
theorem tendsto_eLpNorm_zero_of_dominated {V : Type*} [NormedAddCommGroup V]
    (μ : Measure E) {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ⊤)
    {F : ℕ → E → V} (hF : ∀ n, AEStronglyMeasurable (F n) μ)
    {bound : E → ℝ} (hbound : MemLp bound p μ)
    (hle : ∀ n, ∀ᵐ x ∂μ, ‖F n x‖ ≤ bound x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (F n) p μ) atTop (𝓝 0) := by
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  simp_rw [eLpNorm_eq_eLpNorm' hp0 hp, eLpNorm']
  have h : Tendsto (fun n => ∫⁻ x, ‖F n x‖ₑ ^ p.toReal ∂μ) atTop (𝓝 (∫⁻ x, (0 : ℝ≥0∞) ∂μ)) := by
    refine tendsto_lintegral_of_dominated_convergence' (fun x => ‖bound x‖ₑ ^ p.toReal)
      (fun n => ((hF n).enorm.pow_const _)) (fun n => ?_) ?_ ?_
    · filter_upwards [hle n] with x hx
      have : ‖F n x‖ₑ ≤ ‖bound x‖ₑ := by
        rw [enorm_eq_nnnorm, enorm_eq_nnnorm, ENNReal.coe_le_coe, ← NNReal.coe_le_coe,
          coe_nnnorm, coe_nnnorm]
        exact hx.trans (le_abs_self _)
      exact ENNReal.rpow_le_rpow this hq.le
    · exact (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp0 hp hbound.eLpNorm_lt_top).ne
    · filter_upwards [hlim] with x hx
      have h0 : Tendsto (fun n => ‖F n x‖ₑ) atTop (𝓝 0) := by
        have := (continuous_enorm.tendsto (0 : V)).comp hx
        simp only [Function.comp_def, enorm_zero] at this
        exact this
      have := (ENNReal.continuous_rpow_const (y := p.toReal)).tendsto 0 |>.comp h0
      simpa [Function.comp_def, ENNReal.zero_rpow_of_pos hq] using this
  simp only [lintegral_zero] at h
  have := (ENNReal.continuous_rpow_const (y := 1 / p.toReal)).tendsto 0 |>.comp h
  simpa [Function.comp_def, ENNReal.zero_rpow_of_pos (inv_pos.mpr hq),
    ENNReal.zero_rpow_of_pos (by positivity : 0 < 1 / p.toReal)] using this

section GradientMeasurability

variable [BorelSpace E] [CompleteSpace E]

theorem measurable_gradient (f : E → ℝ) : Measurable (gradient f) :=
  (InnerProductSpace.toDual ℝ E).symm.continuous.measurable.comp (measurable_fderiv ℝ f)

variable [SecondCountableTopology E]

theorem aestronglyMeasurable_gradient (f : E → ℝ) (μ : Measure E) :
    AEStronglyMeasurable (gradient f) μ :=
  (measurable_gradient f).aestronglyMeasurable

end GradientMeasurability

variable [BorelSpace E] [FiniteDimensional ℝ E]
/-- Rademacher's theorem for locally Lipschitz real functions. -/
theorem ae_differentiableAt_of_locallyLipschitz {f : E → ℝ} (hf : LocallyLipschitz f)
    (m : Measure E) [m.IsAddHaarMeasure] : ∀ᵐ x ∂m, DifferentiableAt ℝ f x := by
  have h : ∀ n : ℕ, ∀ᵐ x ∂m, x ∈ Metric.ball (0 : E) n → DifferentiableAt ℝ f x := by
    intro n
    obtain ⟨K, hK⟩ := lipschitzOnWith_of_locallyLipschitz_of_isCompact hf (isCompact_closedBall (0 : E) n)
    obtain ⟨g, hg, hfg⟩ := hK.extend_real
    filter_upwards [hg.ae_differentiableAt (μ := m)] with x hx hxn
    have : f =ᶠ[𝓝 x] g := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hxn] with y hy
      exact hfg (Metric.ball_subset_closedBall hy)
    exact hx.congr_of_eventuallyEq this
  filter_upwards [ae_all_iff.mpr h] with x hx
  obtain ⟨n, hn⟩ := exists_nat_gt ‖x‖
  exact hx n (by simpa using hn)

/-- The radii `1 / (j + 1)` used for the approximating sequences. -/
def radius (j : ℕ) : ℝ := 1 / ((j : ℝ) + 1)

theorem radius_pos (j : ℕ) : 0 < radius j := by unfold radius; positivity

theorem tendsto_radius : Tendsto radius atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat

end Measurable

section Kernel

variable [MeasurableSpace E] (m : Measure E)

/-- The normalized mollifier of radius `2 * R`. -/
def kernel (R : ℝ) (x : E) : ℝ := (∫ y, scaled R y ∂m)⁻¹ • scaled R x

theorem kernel_nonneg (R : ℝ) (x : E) : 0 ≤ kernel m R x :=
  smul_nonneg (inv_nonneg.mpr (integral_nonneg fun y => scaled_nonneg R y)) (scaled_nonneg R x)

theorem kernel_eq_zero {R : ℝ} (hR : 0 < R) {x : E} (hx : 2 * R ≤ ‖x‖) : kernel m R x = 0 := by
  simp [kernel, scaled_eq_zero hR hx]

theorem norm_le_of_kernel_ne_zero {R : ℝ} (hR : 0 < R) {x : E} (hx : kernel m R x ≠ 0) :
    ‖x‖ < 2 * R := by
  by_contra h
  push Not at h
  exact hx (kernel_eq_zero m hR h)

theorem hasCompactSupport_kernel [FiniteDimensional ℝ E] {R : ℝ} (hR : 0 < R) : HasCompactSupport (kernel m R) :=
  HasCompactSupport.intro (isCompact_closedBall (0 : E) (2 * R)) fun x hx =>
    kernel_eq_zero m hR (by
      rw [Metric.mem_closedBall, dist_zero_right] at hx
      exact le_of_lt (not_le.mp hx))

theorem tsupport_kernel_subset {R : ℝ} (hR : 0 < R) :
    tsupport (kernel m R) ⊆ Metric.closedBall (0 : E) (2 * R) :=
  closure_minimal (fun x hx => by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact le_of_lt (norm_le_of_kernel_ne_zero m hR hx)) Metric.isClosed_closedBall

theorem contDiff_kernel (R : ℝ) : ContDiff ℝ ∞ (kernel m R) :=
  (contDiff_scaled R).const_smul _

theorem continuous_kernel (R : ℝ) : Continuous (kernel m R) := (contDiff_kernel m R).continuous

theorem hasFDerivAt_kernel (R : ℝ) (x : E) :
    HasFDerivAt (kernel m R)
      ((∫ y, scaled R y ∂m)⁻¹ • (R⁻¹ • fderiv ℝ (⇑(bump (E := E))) (R⁻¹ • x))) x := by
  exact HasFDerivAt.const_smul (hasFDerivAt_scaled (E := E) R x) (∫ y, scaled R y ∂m)⁻¹

theorem norm_fderiv_kernel {R : ℝ} (hR : 0 < R) (x : E) :
    ‖fderiv ℝ (kernel m R) x‖ =
      (∫ y, scaled R y ∂m)⁻¹ * (R⁻¹ * ‖fderiv ℝ (⇑(bump (E := E))) (R⁻¹ • x)‖) := by
  rw [(hasFDerivAt_kernel m R x).fderiv, norm_smul, norm_smul, norm_inv, norm_inv,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun y => scaled_nonneg R y),
    abs_of_pos hR]

/-- The scale-free constant controlling the mass of the kernel derivative. -/
def kernelDerivativeMass : ℝ := (∫ x, ‖fderiv ℝ (⇑(bump (E := E))) x‖ ∂m) / ∫ x, bump (E := E) x ∂m

theorem kernelDerivativeMass_nonneg : 0 ≤ kernelDerivativeMass (E := E) m :=
  div_nonneg (integral_nonneg fun _ => norm_nonneg _) (integral_nonneg fun _ => (bump (E := E)).nonneg)

theorem continuous_fderiv_kernel (R : ℝ) : Continuous (fderiv ℝ (kernel m R)) :=
  (contDiff_kernel m R).continuous_fderiv (by simp)

theorem hasCompactSupport_fderiv_kernel [FiniteDimensional ℝ E] {R : ℝ} (hR : 0 < R) :
    HasCompactSupport (fderiv ℝ (kernel m R)) :=
  (hasCompactSupport_kernel m hR).fderiv (𝕜 := ℝ)

theorem norm_le_of_fderiv_kernel_ne_zero {R : ℝ} (hR : 0 < R) {x : E}
    (hx : fderiv ℝ (kernel m R) x ≠ 0) : ‖x‖ ≤ 2 * R := by
  have := tsupport_kernel_subset m hR (support_fderiv_subset ℝ hx)
  simpa [Metric.mem_closedBall, dist_zero_right] using this

/-- Mollification of `g` by the normalized kernel of radius `2 * R`. -/
def mollify (R : ℝ) (g : E → ℝ) : E → ℝ :=
  g ⋆[ContinuousLinearMap.lsmul ℝ ℝ, m] kernel m R

theorem hasCompactSupport_mollify [FiniteDimensional ℝ E] {R : ℝ} (hR : 0 < R) {g : E → ℝ} (hg : HasCompactSupport g) :
    HasCompactSupport (mollify m R g) :=
  hg.convolution (ContinuousLinearMap.lsmul ℝ ℝ) (hasCompactSupport_kernel m hR)

section HaarNormalization

variable [BorelSpace E] [FiniteDimensional ℝ E] [m.IsAddHaarMeasure]

theorem integral_bump_pos : 0 < ∫ x, bump (E := E) x ∂m := (bump (E := E)).integral_pos

theorem integral_scaled {R : ℝ} (hR : 0 < R) :
    ∫ x, scaled R x ∂m = R ^ Module.finrank ℝ E * ∫ x, bump (E := E) x ∂m := by
  have := Measure.integral_comp_inv_smul m (fun y : E => bump (E := E) y) R
  simpa [scaled, abs_of_pos (pow_pos hR _)] using this

theorem integral_scaled_pos {R : ℝ} (hR : 0 < R) : 0 < ∫ x, scaled R x ∂m := by
  rw [integral_scaled m hR]
  have := integral_bump_pos (E := E) m
  positivity

theorem integrable_scaled {R : ℝ} (hR : 0 < R) : Integrable (scaled (E := E) R) m :=
  (continuous_scaled R).integrable_of_hasCompactSupport (hasCompactSupport_scaled hR)

theorem integrable_kernel {R : ℝ} (hR : 0 < R) : Integrable (kernel m R) m :=
  (continuous_kernel m R).integrable_of_hasCompactSupport (hasCompactSupport_kernel m hR)

theorem integral_kernel {R : ℝ} (hR : 0 < R) : ∫ x, kernel m R x ∂m = 1 := by
  simp only [kernel]
  rw [integral_smul, smul_eq_mul, inv_mul_cancel₀ (integral_scaled_pos m hR).ne']

theorem integrable_norm_fderiv_kernel {R : ℝ} (hR : 0 < R) :
    Integrable (fun x => ‖fderiv ℝ (kernel m R) x‖) m :=
  ((continuous_fderiv_kernel m R).integrable_of_hasCompactSupport
    (hasCompactSupport_fderiv_kernel m hR)).norm

theorem integral_norm_fderiv_kernel {R : ℝ} (hR : 0 < R) :
    ∫ x, ‖fderiv ℝ (kernel m R) x‖ ∂m = R⁻¹ * kernelDerivativeMass m := by
  simp_rw [norm_fderiv_kernel m hR]
  rw [integral_const_mul, integral_const_mul,
    Measure.integral_comp_inv_smul m (fun y : E => ‖fderiv ℝ (⇑(bump (E := E))) y‖) R,
    integral_scaled m hR, abs_of_pos (pow_pos hR _), kernelDerivativeMass, smul_eq_mul]
  have h1 := integral_bump_pos (E := E) m
  have h2 : (0 : ℝ) < R ^ Module.finrank ℝ E := pow_pos hR _
  field_simp

theorem mollify_apply (R : ℝ) (g : E → ℝ) (x : E) :
    mollify m R g x = ∫ t, g (x - t) * kernel m R t ∂m := by
  rw [mollify, convolution_eq_swap]
  simp [ContinuousLinearMap.lsmul_apply, smul_eq_mul]

theorem integrable_shift_mul_kernel {R : ℝ} (hR : 0 < R) {g : E → ℝ} (hg : Continuous g) (x : E) :
    Integrable (fun t => g (x - t) * kernel m R t) m := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact (hg.comp (continuous_const.sub continuous_id)).mul (continuous_kernel m R)
  · exact (hasCompactSupport_kernel m hR).mul_left

theorem contDiff_mollify {R : ℝ} (hR : 0 < R) {g : E → ℝ} (hg : Continuous g) :
    ContDiff ℝ ∞ (mollify m R g) :=
  (hasCompactSupport_kernel m hR).contDiff_convolution_right _ hg.locallyIntegrable
    (contDiff_kernel m R)

theorem continuous_mollify {R : ℝ} (hR : 0 < R) {g : E → ℝ} (hg : Continuous g) :
    Continuous (mollify m R g) :=
  (contDiff_mollify m hR hg).continuous

theorem lipschitzWith_mollify {R : ℝ} (hR : 0 < R) {K : NNReal} {g : E → ℝ}
    (hg : LipschitzWith K g) : LipschitzWith K (mollify m R g) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [mollify_apply, mollify_apply, Real.dist_eq,
    ← integral_sub (integrable_shift_mul_kernel m hR hg.continuous x)
      (integrable_shift_mul_kernel m hR hg.continuous y)]
  have hK : Integrable (fun t => K * dist x y * kernel m R t) m :=
    (integrable_kernel m hR).const_mul _
  calc |∫ t, (g (x - t) * kernel m R t - g (y - t) * kernel m R t) ∂m|
      ≤ ∫ t, K * dist x y * kernel m R t ∂m := by
        rw [← Real.norm_eq_abs]
        refine norm_integral_le_of_norm_le hK (ae_of_all _ fun t => ?_)
        rw [← sub_mul, Real.norm_eq_abs, abs_mul, abs_of_nonneg (kernel_nonneg m R t)]
        refine mul_le_mul_of_nonneg_right ?_ (kernel_nonneg m R t)
        rw [← Real.dist_eq]
        calc dist (g (x - t)) (g (y - t)) ≤ K * dist (x - t) (y - t) := hg.dist_le_mul _ _
          _ = K * dist x y := by rw [dist_sub_right]
    _ = K * dist x y := by rw [integral_const_mul, integral_kernel m hR, mul_one]

theorem mollify_le {R : ℝ} (hR : 0 < R) {g : E → ℝ} (hg : Continuous g) {b : ℝ}
    (hb : ∀ x, g x ≤ b) (x : E) : mollify m R g x ≤ b := by
  rw [mollify_apply]
  calc ∫ t, g (x - t) * kernel m R t ∂m ≤ ∫ t, b * kernel m R t ∂m := by
        refine integral_mono (integrable_shift_mul_kernel m hR hg x)
          ((integrable_kernel m hR).const_mul _) fun t => ?_
        exact mul_le_mul_of_nonneg_right (hb _) (kernel_nonneg m R t)
    _ = b := by rw [integral_const_mul, integral_kernel m hR, mul_one]

theorem le_mollify {R : ℝ} (hR : 0 < R) {g : E → ℝ} (hg : Continuous g) {a : ℝ}
    (ha : ∀ x, a ≤ g x) (x : E) : a ≤ mollify m R g x := by
  rw [mollify_apply]
  calc a = ∫ t, a * kernel m R t ∂m := by rw [integral_const_mul, integral_kernel m hR, mul_one]
    _ ≤ ∫ t, g (x - t) * kernel m R t ∂m := by
        refine integral_mono ((integrable_kernel m hR).const_mul _)
          (integrable_shift_mul_kernel m hR hg x) fun t => ?_
        exact mul_le_mul_of_nonneg_right (ha _) (kernel_nonneg m R t)

theorem abs_mollify_le {R : ℝ} (hR : 0 < R) {g : E → ℝ} (hg : Continuous g) {C : ℝ}
    (hC : ∀ x, |g x| ≤ C) (x : E) : |mollify m R g x| ≤ C :=
  abs_le.mpr ⟨le_mollify m hR hg (fun x => (abs_le.mp (hC x)).1) x,
    mollify_le m hR hg (fun x => (abs_le.mp (hC x)).2) x⟩

theorem norm_mollify_sub_le {R : ℝ} (hR : 0 < R) {K : NNReal} {g : E → ℝ}
    (hg : LipschitzWith K g) (x : E) : ‖mollify m R g x - g x‖ ≤ K * (2 * R) := by
  have h : mollify m R g x - g x = ∫ t, (g (x - t) - g x) * kernel m R t ∂m := by
    rw [mollify_apply]
    simp_rw [sub_mul]
    rw [integral_sub (integrable_shift_mul_kernel m hR hg.continuous x)
      ((integrable_kernel m hR).const_mul _), integral_const_mul, integral_kernel m hR, mul_one]
  rw [h]
  refine (norm_integral_le_of_norm_le ((integrable_kernel m hR).const_mul (K * (2 * R)))
    (ae_of_all _ fun t => ?_)).trans ?_
  · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (kernel_nonneg m R t)]
    by_cases ht : kernel m R t = 0
    · simp [ht]
    · have htR := norm_le_of_kernel_ne_zero m hR ht
      refine mul_le_mul_of_nonneg_right ?_ (kernel_nonneg m R t)
      calc |g (x - t) - g x| = dist (g (x - t)) (g x) := (Real.dist_eq _ _).symm
        _ ≤ K * dist (x - t) x := hg.dist_le_mul _ _
        _ = K * ‖t‖ := by rw [dist_eq_norm, sub_sub_cancel_left, norm_neg]
        _ ≤ K * (2 * R) := by gcongr
  · rw [integral_const_mul, integral_kernel m hR, mul_one]

theorem hasFDerivAt_mollify {R : ℝ} (hR : 0 < R) {g : E → ℝ} (hg : Continuous g) (x : E) :
    HasFDerivAt (mollify m R g)
      ((g ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).precompR E, m] fderiv ℝ (kernel m R)) x) x :=
  (hasCompactSupport_kernel m hR).hasFDerivAt_convolution_right _ hg.locallyIntegrable
    ((contDiff_kernel m R).of_le (mod_cast le_top)) x

theorem fderiv_mollify_apply {R : ℝ} (hR : 0 < R) {g : E → ℝ} (hg : Continuous g) (x : E) :
    fderiv ℝ (mollify m R g) x = ∫ t, g (x - t) • fderiv ℝ (kernel m R) t ∂m := by
  have h := (hasFDerivAt_mollify m hR hg x).fderiv
  rw [convolution_eq_swap] at h
  refine h.trans ?_
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  ext v
  simp [ContinuousLinearMap.precompR_apply, ContinuousLinearMap.compL_apply, smul_eq_mul]

theorem mollify_affine {R : ℝ} (hR : 0 < R) (c : ℝ) (L : E →L[ℝ] ℝ) (x : E) :
    mollify m R (fun z => c + L z) x = c + L x - ∫ t, L t * kernel m R t ∂m := by
  rw [mollify_apply]
  have h1 : Integrable (fun t => c * kernel m R t) m := (integrable_kernel m hR).const_mul _
  have h2 : Integrable (fun t => L x * kernel m R t) m := (integrable_kernel m hR).const_mul _
  have h3 : Integrable (fun t => L t * kernel m R t) m :=
    (L.continuous.mul (continuous_kernel m R)).integrable_of_hasCompactSupport
      (hasCompactSupport_kernel m hR).mul_left
  have h : (fun t => (c + L (x - t)) * kernel m R t) =
      fun t => c * kernel m R t + L x * kernel m R t - L t * kernel m R t := by
    funext t
    rw [map_sub, add_sub, sub_mul, add_mul]
  have h12 : Integrable (fun t => c * kernel m R t + L x * kernel m R t) m := h1.add h2
  rw [h, integral_sub h12 h3, integral_add h1 h2, integral_const_mul, integral_const_mul,
    integral_kernel m hR, mul_one, mul_one]

theorem hasFDerivAt_mollify_affine {R : ℝ} (hR : 0 < R) (c : ℝ) (L : E →L[ℝ] ℝ) (x : E) :
    HasFDerivAt (mollify m R (fun z => c + L z)) L x := by
  have h : mollify m R (fun z => c + L z) = fun x => c + L x - ∫ t, L t * kernel m R t ∂m :=
    funext (mollify_affine m hR c L)
  rw [h]
  exact (((hasFDerivAt_const c x).add L.hasFDerivAt).sub_const _).congr_fderiv (zero_add L)

theorem integral_affine_smul_fderiv_kernel {R : ℝ} (hR : 0 < R) (c : ℝ) (L : E →L[ℝ] ℝ)
    (x : E) : ∫ t, (c + L (x - t)) • fderiv ℝ (kernel m R) t ∂m = L := by
  have h1 := fderiv_mollify_apply m hR (g := fun z => c + L z)
    (continuous_const.add L.continuous) x
  rw [(hasFDerivAt_mollify_affine m hR c L x).fderiv] at h1
  exact h1.symm

theorem integrable_mul_smul_fderiv_kernel {R : ℝ} (hR : 0 < R) {g : E → ℝ} (hg : Continuous g)
    (x : E) : Integrable (fun t => g (x - t) • fderiv ℝ (kernel m R) t) m := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact (hg.comp (continuous_const.sub continuous_id)).smul (continuous_fderiv_kernel m R)
  · refine (hasCompactSupport_fderiv_kernel m hR).mono fun t ht => ?_
    rw [Function.mem_support] at ht ⊢
    intro h
    exact ht (by simp [h])

theorem norm_fderiv_mollify_sub_le {R : ℝ} (hR : 0 < R) {g : E → ℝ} (hg : Continuous g) {x : E}
    {L : E →L[ℝ] ℝ} {δ r : ℝ} (hδ : 0 ≤ δ)
    (hr : ∀ y, dist y x < r → ‖g y - g x - L (y - x)‖ ≤ δ * ‖y - x‖) (hRr : 2 * R < r) :
    ‖fderiv ℝ (mollify m R g) x - L‖ ≤ δ * (2 * kernelDerivativeMass m) := by
  have hL : L = ∫ t, (g x - L x + L (x - t)) • fderiv ℝ (kernel m R) t ∂m :=
    (integral_affine_smul_fderiv_kernel m hR (g x - L x) L x).symm
  have hint := integrable_mul_smul_fderiv_kernel m hR (g := fun z => g x - L x + L z)
    (continuous_const.add L.continuous) x
  rw [fderiv_mollify_apply m hR hg x, hL,
    ← integral_sub (integrable_mul_smul_fderiv_kernel m hR hg x) hint]
  calc ‖∫ t, (g (x - t) • fderiv ℝ (kernel m R) t -
        (g x - L x + L (x - t)) • fderiv ℝ (kernel m R) t) ∂m‖
      ≤ ∫ t, δ * (2 * R) * ‖fderiv ℝ (kernel m R) t‖ ∂m := by
        refine norm_integral_le_of_norm_le ((integrable_norm_fderiv_kernel m hR).const_mul _)
          (ae_of_all _ fun t => ?_)
        rw [← sub_smul, norm_smul]
        by_cases ht : fderiv ℝ (kernel m R) t = 0
        · simp [ht]
        · have htR : ‖t‖ ≤ 2 * R := norm_le_of_fderiv_kernel_ne_zero m hR ht
          have h1 : ‖g (x - t) - (g x - L x + L (x - t))‖ ≤ δ * ‖t‖ := by
            have h2 := hr (x - t) (by
              rw [dist_eq_norm, sub_sub_cancel_left, norm_neg]
              exact lt_of_le_of_lt htR hRr)
            have e : g (x - t) - (g x - L x + L (x - t)) = g (x - t) - g x - L ((x - t) - x) := by
              simp only [map_sub]
              abel
            rw [e]
            simpa [sub_sub_cancel_left, norm_neg] using h2
          calc ‖g (x - t) - (g x - L x + L (x - t))‖ * ‖fderiv ℝ (kernel m R) t‖
              ≤ δ * ‖t‖ * ‖fderiv ℝ (kernel m R) t‖ := by gcongr
            _ ≤ δ * (2 * R) * ‖fderiv ℝ (kernel m R) t‖ := by gcongr
    _ = δ * (2 * R) * (R⁻¹ * kernelDerivativeMass m) := by
        rw [integral_const_mul, integral_norm_fderiv_kernel m hR]
    _ = δ * (2 * kernelDerivativeMass m) := by field_simp

theorem tendsto_fderiv_mollify {g : E → ℝ} (hg : Continuous g) {x : E}
    (hx : DifferentiableAt ℝ g x) {Rs : ℕ → ℝ} (hRs : ∀ j, 0 < Rs j)
    (hlim : Tendsto Rs atTop (𝓝 0)) :
    Tendsto (fun j => fderiv ℝ (mollify m (Rs j) g) x) atTop (𝓝 (fderiv ℝ g x)) := by
  rw [Metric.tendsto_atTop]
  intro η hη
  have hC := kernelDerivativeMass_nonneg (E := E) m
  set δ := η / (2 * kernelDerivativeMass m + 1) with hδ_def
  have hδ : 0 < δ := by positivity
  obtain ⟨r, hr, hrδ⟩ := Metric.eventually_nhds_iff.mp (hx.hasFDerivAt.isLittleO.def hδ)
  have hev : ∀ᶠ j in atTop, 2 * Rs j < r := by
    have h2 : Tendsto (fun j => 2 * Rs j) atTop (𝓝 0) := by simpa using hlim.const_mul 2
    exact (tendsto_order.1 h2).2 r hr
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  refine ⟨N, fun j hj => ?_⟩
  rw [dist_eq_norm]
  calc ‖fderiv ℝ (mollify m (Rs j) g) x - fderiv ℝ g x‖ ≤ δ * (2 * kernelDerivativeMass m) :=
        norm_fderiv_mollify_sub_le m (hRs j) hg hδ.le (fun y hy => hrδ hy) (hN j hj)
    _ < η := by
        rw [hδ_def, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        have := mul_lt_mul_of_pos_left (lt_add_one (2 * kernelDerivativeMass m)) hη
        linarith

theorem tendsto_gradient_mollify {g : E → ℝ} (hg : Continuous g) {x : E}
    (hx : DifferentiableAt ℝ g x) {Rs : ℕ → ℝ} (hRs : ∀ j, 0 < Rs j)
    (hlim : Tendsto Rs atTop (𝓝 0)) :
    Tendsto (fun j => gradient (mollify m (Rs j) g) x) atTop (𝓝 (gradient g x)) :=
  ((InnerProductSpace.toDual ℝ E).symm.continuous.tendsto _).comp
    (tendsto_fderiv_mollify m hg hx hRs hlim)

end HaarNormalization

end Kernel

section Main

variable [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

variable (ν : ProbabilityMeasure E) (m : Measure E) [Measure.IsAddHaarMeasure m]

/-- Step 1 (cutoff): approximate in the weighted graph norm by globally Lipschitz tests
with compact support. Suggested witnesses are smooth cutoffs times g; their Lipschitz constants
may grow with j. This conclusion does not assert smoothness of the approximants. -/

theorem exists_compactSupport_weighted_L2
    (hν : (ν : Measure E) ≪ m) (B : E →L[ℝ] E) (g : E → ℝ)
    (hg : LocallyLipschitz g) (hg_L2 : MemLp g 2 (ν : Measure E))
    (hBg_L2 : MemLp (fun x ↦ B (gradient g x)) 2 (ν : Measure E)) :
    ∃ gSeq : ℕ → E → ℝ,
      (∀ j, HasCompactSupport (gSeq j) ∧
        (∃ K : NNReal, LipschitzWith K (gSeq j)) ∧
        MemLp (gSeq j) 2 (ν : Measure E) ∧
        MemLp (fun x ↦ B (gradient (gSeq j) x)) 2 (ν : Measure E)) ∧
      Tendsto (fun j ↦ eLpNorm (fun x ↦ gSeq j x - g x) 2 (ν : Measure E))
        atTop (𝓝 0) ∧
      Tendsto (fun j ↦ eLpNorm
        (fun x ↦ B (gradient (gSeq j) x) - B (gradient g x)) 2 (ν : Measure E))
        atTop (𝓝 0) := by
  obtain ⟨M, hM0, hM⟩ := exists_bound_fderiv_bump (E := E)
  obtain ⟨Rs, hRs⟩ : ∃ Rs : ℕ → ℝ, ∀ j, Rs j = (j : ℝ) + 1 := ⟨_, fun j => rfl⟩
  have hRpos : ∀ j, 0 < Rs j := fun j => by rw [hRs]; positivity
  have hR1 : ∀ j, 1 ≤ Rs j := fun j => by
    rw [hRs]
    linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  have hout : ∀ j (x : E), x ∉ Metric.closedBall (0 : E) (2 * Rs j) → scaled (Rs j) x = 0 := by
    intro j x hx
    rw [Metric.mem_closedBall, dist_zero_right] at hx
    exact scaled_eq_zero (hRpos j) (le_of_lt (not_le.mp hx))
  choose K hK using fun j =>
    lipschitzOnWith_of_locallyLipschitz_of_isCompact hg (isCompact_closedBall (0 : E) (2 * Rs j))
  choose C hC using fun j =>
    (isCompact_closedBall (0 : E) (2 * Rs j)).exists_bound_of_continuousOn
      hg.continuous.continuousOn
  have hC' : ∀ j (x : E), x ∈ Metric.closedBall (0 : E) (2 * Rs j) → |g x| ≤ max (C j) 0 := by
    intro j x hx
    have := hC j x hx
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)
  have hχlip : ∀ j, LipschitzWith ((Rs j)⁻¹ * M).toNNReal (scaled (E := E) (Rs j)) :=
    fun j => lipschitzWith_scaled (hRpos j) hM0 hM
  have hgrad_bound : ∀ j (x : E), ‖gradient (scaled (E := E) (Rs j)) x‖ ≤ M := fun j x => by
    rw [norm_gradient_eq_norm_fderiv]
    calc ‖fderiv ℝ (scaled (Rs j)) x‖ ≤ (Rs j)⁻¹ * M := norm_fderiv_scaled_le (hRpos j) hM x
      _ ≤ 1 * M := by gcongr; exact inv_le_one_of_one_le₀ (hR1 j)
      _ = M := one_mul M
  have hgrad_zero : ∀ j (x : E), ‖x‖ < Rs j → gradient (scaled (E := E) (Rs j)) x = 0 :=
    fun j x hx => by
    show (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ (scaled (Rs j)) x) = 0
    rw [fderiv_scaled_eq_zero (hRpos j) hx, map_zero]
  have hprod : ∀ j, LipschitzWith (((Rs j)⁻¹ * M) * max (C j) 0 + K j).toNNReal
      (fun x => scaled (Rs j) x * g x) := by
    intro j
    have hRj := hRpos j
    have key : ∀ x y, x ∈ Metric.closedBall (0 : E) (2 * Rs j) →
        dist (scaled (Rs j) x * g x) (scaled (Rs j) y * g y) ≤
          (((Rs j)⁻¹ * M) * max (C j) 0 + K j) * dist x y := by
      intro x y hx
      have e : scaled (Rs j) x * g x - scaled (Rs j) y * g y =
          (scaled (Rs j) x - scaled (Rs j) y) * g x + scaled (Rs j) y * (g x - g y) := by ring
      rw [Real.dist_eq, e]
      have h1 : |(scaled (Rs j) x - scaled (Rs j) y) * g x| ≤
          ((Rs j)⁻¹ * M) * max (C j) 0 * dist x y := by
        rw [abs_mul]
        calc |scaled (Rs j) x - scaled (Rs j) y| * |g x|
            ≤ ((Rs j)⁻¹ * M * dist x y) * max (C j) 0 := by
              gcongr
              · rw [← Real.dist_eq]
                have := (hχlip j).dist_le_mul x y
                rwa [Real.coe_toNNReal _ (by positivity)] at this
              · exact hC' j x hx
          _ = ((Rs j)⁻¹ * M) * max (C j) 0 * dist x y := by ring
      have h2 : |scaled (Rs j) y * (g x - g y)| ≤ K j * dist x y := by
        by_cases hy : y ∈ Metric.closedBall (0 : E) (2 * Rs j)
        · rw [abs_mul, abs_of_nonneg (scaled_nonneg _ _)]
          calc scaled (Rs j) y * |g x - g y| ≤ 1 * |g x - g y| := by
                gcongr
                exact scaled_le_one _ _
            _ = dist (g x) (g y) := by rw [one_mul, Real.dist_eq]
            _ ≤ K j * dist x y := (hK j).dist_le_mul x hx y hy
        · rw [hout j y hy, zero_mul, abs_zero]
          positivity
      calc |(scaled (Rs j) x - scaled (Rs j) y) * g x + scaled (Rs j) y * (g x - g y)|
          ≤ |(scaled (Rs j) x - scaled (Rs j) y) * g x| + |scaled (Rs j) y * (g x - g y)| :=
            abs_add_le _ _
        _ ≤ ((Rs j)⁻¹ * M) * max (C j) 0 * dist x y + K j * dist x y := add_le_add h1 h2
        _ = (((Rs j)⁻¹ * M) * max (C j) 0 + K j) * dist x y := by ring
    refine LipschitzWith.of_dist_le' fun x y => ?_
    by_cases hx : x ∈ Metric.closedBall (0 : E) (2 * Rs j)
    · exact key x y hx
    by_cases hy : y ∈ Metric.closedBall (0 : E) (2 * Rs j)
    · rw [dist_comm, dist_comm x y]
      exact key y x hy
    · rw [hout j x hx, hout j y hy, zero_mul, zero_mul, dist_self]
      positivity
  refine ⟨fun j x => scaled (Rs j) x * g x, fun j => ⟨?_, ⟨_, hprod j⟩, ?_, ?_⟩, ?_, ?_⟩
  · exact HasCompactSupport.intro (isCompact_closedBall (0 : E) (2 * Rs j)) fun x hx => by
      beta_reduce
      rw [hout j x hx, zero_mul]
  · refine MemLp.of_bound ((continuous_scaled _).mul hg.continuous).aestronglyMeasurable
      (max (C j) 0) (ae_of_all _ fun x => ?_)
    beta_reduce
    by_cases hx : x ∈ Metric.closedBall (0 : E) (2 * Rs j)
    · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (scaled_nonneg _ _)]
      calc scaled (Rs j) x * |g x| ≤ 1 * max (C j) 0 := by
            gcongr
            · exact scaled_le_one _ _
            · exact hC' j x hx
        _ = max (C j) 0 := one_mul _
    · rw [hout j x hx, zero_mul, norm_zero]
      exact le_max_right _ _
  · have hRj := hRpos j
    refine MemLp.of_bound
      (B.continuous.measurable.comp (measurable_gradient _)).aestronglyMeasurable
      (‖B‖ * (((Rs j)⁻¹ * M) * max (C j) 0 + K j)) (ae_of_all _ fun x => ?_)
    beta_reduce
    calc ‖B (gradient (fun x => scaled (Rs j) x * g x) x)‖
        ≤ ‖B‖ * ‖gradient (fun x => scaled (Rs j) x * g x) x‖ := B.le_opNorm _
      _ ≤ ‖B‖ * (((Rs j)⁻¹ * M) * max (C j) 0 + K j) := by
          gcongr
          have := norm_gradient_le_of_lipschitz (hprod j) x
          rwa [Real.coe_toNNReal _ (by positivity)] at this
  · refine tendsto_eLpNorm_zero_of_dominated (ν : Measure E) (by norm_num) (by norm_num)
      (fun j => (((continuous_scaled _).mul hg.continuous).sub hg.continuous).aestronglyMeasurable)
      (bound := fun x => ‖g x‖) hg_L2.norm (fun j => ae_of_all _ fun x => ?_)
      (ae_of_all _ fun x => ?_)
    · beta_reduce
      have e : scaled (Rs j) x * g x - g x = (scaled (Rs j) x - 1) * g x := by ring
      rw [e, norm_mul]
      calc ‖scaled (Rs j) x - 1‖ * ‖g x‖ ≤ 1 * ‖g x‖ := by
            gcongr
            rw [Real.norm_eq_abs, abs_le]
            constructor <;> linarith [scaled_nonneg (Rs j) x, scaled_le_one (Rs j) x]
        _ = ‖g x‖ := one_mul _
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop ⌈‖x‖⌉₊] with j hj
      have hxR : ‖x‖ ≤ Rs j := by
        rw [hRs j]
        calc ‖x‖ ≤ ⌈‖x‖⌉₊ := Nat.le_ceil _
          _ ≤ (j : ℝ) := by exact_mod_cast hj
          _ ≤ j + 1 := by linarith
      rw [scaled_eq_one (hRpos j) hxR, one_mul, sub_self]
  · have hdiff := hν.ae_le (ae_differentiableAt_of_locallyLipschitz hg m)
    refine tendsto_eLpNorm_zero_of_dominated (ν : Measure E) (by norm_num) (by norm_num)
      (fun j => ((B.continuous.measurable.comp (measurable_gradient _)).aestronglyMeasurable).sub
        (B.continuous.measurable.comp (measurable_gradient _)).aestronglyMeasurable)
      (bound := fun x => ‖B (gradient g x)‖ + ‖B‖ * M * ‖g x‖)
      (hBg_L2.norm.add (hg_L2.norm.const_mul _)) (fun j => ?_) ?_
    · filter_upwards [hdiff] with x hx
      rw [gradient_scaled_mul hx, map_add, map_smul, map_smul]
      have e : scaled (Rs j) x • B (gradient g x) + g x • B (gradient (scaled (Rs j)) x) -
          B (gradient g x) =
          (scaled (Rs j) x - 1) • B (gradient g x) + g x • B (gradient (scaled (Rs j)) x) := by
        rw [sub_smul, one_smul]
        abel
      rw [e]
      calc ‖(scaled (Rs j) x - 1) • B (gradient g x) + g x • B (gradient (scaled (Rs j)) x)‖
          ≤ ‖(scaled (Rs j) x - 1) • B (gradient g x)‖ +
            ‖g x • B (gradient (scaled (Rs j)) x)‖ := norm_add_le _ _
        _ ≤ 1 * ‖B (gradient g x)‖ + ‖g x‖ * (‖B‖ * M) := by
            rw [norm_smul, norm_smul]
            gcongr
            · rw [Real.norm_eq_abs, abs_le]
              constructor <;> linarith [scaled_nonneg (Rs j) x, scaled_le_one (Rs j) x]
            · calc ‖B (gradient (scaled (Rs j)) x)‖ ≤ ‖B‖ * ‖gradient (scaled (Rs j)) x‖ :=
                  B.le_opNorm _
                _ ≤ ‖B‖ * M := by gcongr; exact hgrad_bound j x
        _ = ‖B (gradient g x)‖ + ‖B‖ * M * ‖g x‖ := by ring
    · filter_upwards [hdiff] with x hx
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop ⌈‖x‖⌉₊] with j hj
      have hxR : ‖x‖ < Rs j := by
        rw [hRs j]
        calc ‖x‖ ≤ ⌈‖x‖⌉₊ := Nat.le_ceil _
          _ ≤ (j : ℝ) := by exact_mod_cast hj
          _ < j + 1 := by linarith
      rw [gradient_scaled_mul hx, scaled_eq_one (hRpos j) hxR.le, hgrad_zero j x hxR, one_smul,
        smul_zero, add_zero, sub_self]

/-- Step 2 (mollification): smooth a compactly supported globally Lipschitz test.
The original global Lipschitz constant is retained, and the *full* gradient converges in L2.
Its source and approximant membership is part of the conclusion, not an extra hypothesis. -/
theorem exists_smooth_compactSupport_L2
    (hν : (ν : Measure E) ≪ m) (g : E → ℝ) (K : NNReal)
    (hg : LipschitzWith K g) (hcompact : HasCompactSupport g) :
    MemLp g 2 (ν : Measure E) ∧ MemLp (gradient g) 2 (ν : Measure E) ∧
      ∃ gSeq : ℕ → E → ℝ,
        (∀ j, ContDiff ℝ ∞ (gSeq j) ∧ HasCompactSupport (gSeq j) ∧
          LipschitzWith K (gSeq j) ∧ MemLp (gSeq j) 2 (ν : Measure E) ∧
          MemLp (gradient (gSeq j)) 2 (ν : Measure E)) ∧
        Tendsto (fun j ↦ eLpNorm (fun x ↦ gSeq j x - g x) 2 (ν : Measure E))
          atTop (𝓝 0) ∧
        Tendsto (fun j ↦ eLpNorm (fun x ↦ gradient (gSeq j) x - gradient g x)
          2 (ν : Measure E)) atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := hg.continuous.bounded_above_of_compact_support hcompact
  have hgL2 : MemLp g 2 (ν : Measure E) :=
    MemLp.of_bound hg.continuous.aestronglyMeasurable C (ae_of_all _ hC)
  have hgradL2 : MemLp (gradient g) 2 (ν : Measure E) :=
    MemLp.of_bound (aestronglyMeasurable_gradient g _) K
      (ae_of_all _ (norm_gradient_le_of_lipschitz hg))
  refine ⟨hgL2, hgradL2, fun j => mollify m (radius j) g, fun j => ?_, ?_, ?_⟩
  · have hR := radius_pos j
    refine ⟨contDiff_mollify m hR hg.continuous, hasCompactSupport_mollify m hR hcompact,
      lipschitzWith_mollify m hR hg, ?_, ?_⟩
    · refine MemLp.of_bound (continuous_mollify m hR hg.continuous).aestronglyMeasurable C
        (ae_of_all _ fun x => ?_)
      rw [Real.norm_eq_abs]
      exact abs_mollify_le m hR hg.continuous (fun x => by rw [← Real.norm_eq_abs]; exact hC x) x
    · exact MemLp.of_bound (aestronglyMeasurable_gradient _ _) K
        (ae_of_all _ (norm_gradient_le_of_lipschitz (lipschitzWith_mollify m hR hg)))
  · have hbound : ∀ j, eLpNorm (fun x => mollify m (radius j) g x - g x) 2 (ν : Measure E) ≤
        ENNReal.ofReal (K * (2 * radius j)) := by
      intro j
      have := eLpNorm_le_of_ae_bound (μ := (ν : Measure E)) (p := 2)
        (ae_of_all _ (norm_mollify_sub_le m (radius_pos j) hg))
      simpa [measure_univ] using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
      (fun _ => zero_le) hbound
    have h : Tendsto (fun j => (K : ℝ) * (2 * radius j)) atTop (𝓝 0) := by
      simpa using (tendsto_radius.const_mul 2).const_mul (K : ℝ)
    simpa using ENNReal.tendsto_ofReal h
  · refine tendsto_eLpNorm_zero_of_dominated (ν : Measure E) (by norm_num) (by norm_num)
      (fun j => (aestronglyMeasurable_gradient _ _).sub (aestronglyMeasurable_gradient _ _))
      (bound := fun _ => (K : ℝ) + K) (memLp_const _) (fun j => ae_of_all _ fun x => ?_) ?_
    · calc ‖gradient (mollify m (radius j) g) x - gradient g x‖
          ≤ ‖gradient (mollify m (radius j) g) x‖ + ‖gradient g x‖ := norm_sub_le _ _
        _ ≤ K + K := add_le_add
          (norm_gradient_le_of_lipschitz (lipschitzWith_mollify m (radius_pos j) hg) x)
          (norm_gradient_le_of_lipschitz hg x)
    · filter_upwards [hν.ae_le (hg.ae_differentiableAt (μ := m))] with x hx
      have := (tendsto_gradient_mollify m hg.continuous hx radius_pos tendsto_radius).sub_const
        (gradient g x)
      simpa using this

/-- Main L2 statement of `lem:covariance-test-core-density`.
Choose compactly supported smooth approximants with simultaneous value and B-gradient convergence.
For fixed B, continuity transports step 2 to the weighted norm; a diagonal choice combines steps
1 and 2. This statement has no hypothesis asserting either intermediate approximation theorem. -/
theorem exists_smooth_weighted_L2
    (hν : (ν : Measure E) ≪ m) (B : E →L[ℝ] E) (g : E → ℝ)
    (hg : LocallyLipschitz g) (hg_L2 : MemLp g 2 (ν : Measure E))
    (hBg_L2 : MemLp (fun x ↦ B (gradient g x)) 2 (ν : Measure E)) :
    ∃ gSeq : ℕ → E → ℝ,
      (∀ j, ContDiff ℝ ∞ (gSeq j) ∧ HasCompactSupport (gSeq j) ∧
        MemLp (gSeq j) 2 (ν : Measure E) ∧
        MemLp (fun x ↦ B (gradient (gSeq j) x)) 2 (ν : Measure E)) ∧
      Tendsto (fun j ↦ eLpNorm (fun x ↦ gSeq j x - g x) 2 (ν : Measure E))
        atTop (𝓝 0) ∧
      Tendsto (fun j ↦ eLpNorm
        (fun x ↦ B (gradient (gSeq j) x) - B (gradient g x)) 2 (ν : Measure E))
        atTop (𝓝 0) := by
  obtain ⟨u, hu, hu1, hu2⟩ :=
    exists_compactSupport_weighted_L2 ν m hν B g hg hg_L2 hBg_L2
  choose K hK using fun j => (hu j).2.1
  choose v hv hv1 hv2 using fun j =>
    (exists_smooth_compactSupport_L2 ν m hν (u j) (K j) (hK j) (hu j).1).2.2
  have hpick : ∀ j, ∃ k,
      eLpNorm (fun x => v j k x - u j x) 2 (ν : Measure E) ≤ ENNReal.ofReal (radius j) ∧
      eLpNorm (fun x => gradient (v j k) x - gradient (u j) x) 2 (ν : Measure E) ≤
        ENNReal.ofReal (radius j) := by
    intro j
    have hε : (0 : ℝ≥0∞) < ENNReal.ofReal (radius j) := ENNReal.ofReal_pos.mpr (radius_pos j)
    exact ((ENNReal.tendsto_nhds_zero.mp (hv1 j) _ hε).and
      (ENNReal.tendsto_nhds_zero.mp (hv2 j) _ hε)).exists
  choose k hk1 hk2 using hpick
  have hmB : ∀ f : E → ℝ, AEStronglyMeasurable (fun x => B (gradient f x)) (ν : Measure E) :=
    fun f => (B.continuous.measurable.comp (measurable_gradient _)).aestronglyMeasurable
  refine ⟨fun j => v j (k j), fun j => ⟨(hv j (k j)).1, (hv j (k j)).2.1, (hv j (k j)).2.2.2.1, ?_⟩,
    ?_, ?_⟩
  · refine MemLp.of_le ((hv j (k j)).2.2.2.2.norm.const_mul ‖B‖) (hmB _) (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact B.le_opNorm _
  · have hmeas_v : ∀ j, AEStronglyMeasurable (v j (k j)) (ν : Measure E) :=
      fun j => (hv j (k j)).1.continuous.aestronglyMeasurable
    have hmeas_u : ∀ j, AEStronglyMeasurable (u j) (ν : Measure E) := fun j => (hu j).2.2.1.1
    have hmeas_g : AEStronglyMeasurable g (ν : Measure E) := hg.continuous.aestronglyMeasurable
    have hle : ∀ j, eLpNorm (fun x => v j (k j) x - g x) 2 (ν : Measure E) ≤
        ENNReal.ofReal (radius j) + eLpNorm (fun x => u j x - g x) 2 (ν : Measure E) := by
      intro j
      calc eLpNorm (fun x => v j (k j) x - g x) 2 (ν : Measure E)
          = eLpNorm ((fun x => v j (k j) x - u j x) + fun x => u j x - g x) 2 (ν : Measure E) := by
            congr 1
            funext x
            simp
        _ ≤ eLpNorm (fun x => v j (k j) x - u j x) 2 (ν : Measure E) +
            eLpNorm (fun x => u j x - g x) 2 (ν : Measure E) :=
            eLpNorm_add_le ((hmeas_v j).sub (hmeas_u j)) ((hmeas_u j).sub hmeas_g) one_le_two
        _ ≤ ENNReal.ofReal (radius j) + eLpNorm (fun x => u j x - g x) 2 (ν : Measure E) := by
            gcongr
            exact hk1 j
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun _ => zero_le) hle
    have h1 : Tendsto (fun j => ENNReal.ofReal (radius j)) atTop (𝓝 0) := by
      simpa using ENNReal.tendsto_ofReal tendsto_radius
    simpa using h1.add hu1
  · have hle : ∀ j, eLpNorm (fun x => B (gradient (v j (k j)) x) - B (gradient g x)) 2
        (ν : Measure E) ≤
        ‖B‖ₑ * ENNReal.ofReal (radius j) +
          eLpNorm (fun x => B (gradient (u j) x) - B (gradient g x)) 2 (ν : Measure E) := by
      intro j
      calc eLpNorm (fun x => B (gradient (v j (k j)) x) - B (gradient g x)) 2 (ν : Measure E)
          = eLpNorm ((fun x => B (gradient (v j (k j)) x) - B (gradient (u j) x)) +
              fun x => B (gradient (u j) x) - B (gradient g x)) 2 (ν : Measure E) := by
            congr 1
            funext x
            simp
        _ ≤ eLpNorm (fun x => B (gradient (v j (k j)) x) - B (gradient (u j) x)) 2 (ν : Measure E)
            + eLpNorm (fun x => B (gradient (u j) x) - B (gradient g x)) 2 (ν : Measure E) :=
            eLpNorm_add_le ((hmB _).sub (hmB _)) ((hmB _).sub (hmB _)) one_le_two
        _ ≤ ‖B‖ₑ * ENNReal.ofReal (radius j) +
            eLpNorm (fun x => B (gradient (u j) x) - B (gradient g x)) 2 (ν : Measure E) := by
            gcongr
            calc eLpNorm (fun x => B (gradient (v j (k j)) x) - B (gradient (u j) x)) 2
                  (ν : Measure E)
                ≤ eLpNorm (‖B‖ • fun x => ‖gradient (v j (k j)) x - gradient (u j) x‖) 2
                  (ν : Measure E) := by
                  refine eLpNorm_mono_ae_real (ae_of_all _ fun x => ?_)
                  rw [← map_sub]
                  exact B.le_opNorm _
              _ = ‖B‖ₑ * eLpNorm (fun x => gradient (v j (k j)) x - gradient (u j) x) 2
                  (ν : Measure E) := by
                  rw [eLpNorm_const_smul, enorm_norm, eLpNorm_norm]
              _ ≤ ‖B‖ₑ * ENNReal.ofReal (radius j) := by
                  gcongr
                  exact hk2 j
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun _ => zero_le) hle
    have h1 : Tendsto (fun j => ‖B‖ₑ * ENNReal.ofReal (radius j)) atTop (𝓝 0) := by
      have := ENNReal.Tendsto.const_mul (ENNReal.tendsto_ofReal tendsto_radius) (a := ‖B‖ₑ)
        (Or.inr enorm_ne_top)
      simpa using this
    simpa using h1.add hu2

/-- Bounded L1 variant of the same Blueprint lemma. A closed interval [a,b] is preserved;
setting a=0 and b=1 gives the stated range-preserving case. No compact support is required here.
The smoothing also preserves the supplied global Lipschitz bound. -/
theorem exists_smooth_bounded_L1
    (hν : (ν : Measure E) ≪ m) (g : E → ℝ) (K : NNReal)
    (hg : LipschitzWith K g) (a b : ℝ) (hbounds : ∀ x, a ≤ g x ∧ g x ≤ b) :
    MemLp g 1 (ν : Measure E) ∧ MemLp (gradient g) 1 (ν : Measure E) ∧
      ∃ gSeq : ℕ → E → ℝ,
        (∀ j, ContDiff ℝ ∞ (gSeq j) ∧ LipschitzWith K (gSeq j) ∧
          (∀ x, a ≤ gSeq j x ∧ gSeq j x ≤ b) ∧
          MemLp (gSeq j) 1 (ν : Measure E) ∧
          MemLp (gradient (gSeq j)) 1 (ν : Measure E)) ∧
        Tendsto (fun j ↦ eLpNorm (fun x ↦ gSeq j x - g x) 1 (ν : Measure E))
          atTop (𝓝 0) ∧
        Tendsto (fun j ↦ eLpNorm (fun x ↦ gradient (gSeq j) x - gradient g x)
          1 (ν : Measure E)) atTop (𝓝 0) := by
  have hC : ∀ x, ‖g x‖ ≤ max |a| |b| := fun x => by
    rw [Real.norm_eq_abs]
    exact abs_le_max_abs_abs (hbounds x).1 (hbounds x).2
  have hgL1 : MemLp g 1 (ν : Measure E) :=
    MemLp.of_bound hg.continuous.aestronglyMeasurable _ (ae_of_all _ hC)
  have hgradL1 : MemLp (gradient g) 1 (ν : Measure E) :=
    MemLp.of_bound (aestronglyMeasurable_gradient g _) K
      (ae_of_all _ (norm_gradient_le_of_lipschitz hg))
  refine ⟨hgL1, hgradL1, fun j => mollify m (radius j) g, fun j => ?_, ?_, ?_⟩
  · have hR := radius_pos j
    refine ⟨contDiff_mollify m hR hg.continuous, lipschitzWith_mollify m hR hg,
      fun x => ⟨le_mollify m hR hg.continuous (fun x => (hbounds x).1) x,
        mollify_le m hR hg.continuous (fun x => (hbounds x).2) x⟩, ?_, ?_⟩
    · refine MemLp.of_bound (continuous_mollify m hR hg.continuous).aestronglyMeasurable
        (max |a| |b|) (ae_of_all _ fun x => ?_)
      rw [Real.norm_eq_abs]
      exact abs_mollify_le m hR hg.continuous (fun x => by rw [← Real.norm_eq_abs]; exact hC x) x
    · exact MemLp.of_bound (aestronglyMeasurable_gradient _ _) K
        (ae_of_all _ (norm_gradient_le_of_lipschitz (lipschitzWith_mollify m hR hg)))
  · have hbound : ∀ j, eLpNorm (fun x => mollify m (radius j) g x - g x) 1 (ν : Measure E) ≤
        ENNReal.ofReal (K * (2 * radius j)) := by
      intro j
      have := eLpNorm_le_of_ae_bound (μ := (ν : Measure E)) (p := 1)
        (ae_of_all _ (norm_mollify_sub_le m (radius_pos j) hg))
      simpa [measure_univ] using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
      (fun _ => zero_le) hbound
    have h : Tendsto (fun j => (K : ℝ) * (2 * radius j)) atTop (𝓝 0) := by
      simpa using (tendsto_radius.const_mul 2).const_mul (K : ℝ)
    simpa using ENNReal.tendsto_ofReal h
  · refine tendsto_eLpNorm_zero_of_dominated (ν : Measure E) (by norm_num) (by norm_num)
      (fun j => (aestronglyMeasurable_gradient _ _).sub (aestronglyMeasurable_gradient _ _))
      (bound := fun _ => (K : ℝ) + K) (memLp_const _) (fun j => ae_of_all _ fun x => ?_) ?_
    · calc ‖gradient (mollify m (radius j) g) x - gradient g x‖
          ≤ ‖gradient (mollify m (radius j) g) x‖ + ‖gradient g x‖ := norm_sub_le _ _
        _ ≤ K + K := add_le_add
          (norm_gradient_le_of_lipschitz (lipschitzWith_mollify m (radius_pos j) hg) x)
          (norm_gradient_le_of_lipschitz hg x)
    · filter_upwards [hν.ae_le (hg.ae_differentiableAt (μ := m))] with x hx
      have := (tendsto_gradient_mollify m hg.continuous hx radius_pos tendsto_radius).sub_const
        (gradient g x)
      simpa using this

end Main

end FunctionalInequalities.Energy.Euclidean.LipschitzApproximation
