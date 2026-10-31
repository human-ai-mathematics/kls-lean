module

public import FunctionalInequalities.KLS.LogConcave.HminusOne
public import FunctionalInequalities.KLS.LogConcave.Density.LowerApproximation
public import FunctionalInequalities.KLS.LogConcave.Density.Tilted
public import FunctionalInequalities.KLS.LogConcave.Poincare
public import FunctionalInequalities.KLS.LogConcave.Stein
public import FunctionalInequalities.KLS.LogConcave.Transport
public import FunctionalInequalities.KLS.Statement
public import FunctionalInequalities.Energy.DualNorm
public import FunctionalInequalities.Probability.Covariance.CauchySchwarz

/-!
# The `H⁻¹` variance inequality for general log-concave laws

Letwin, arXiv:2607.24164v1, Proposition 2.8 (quoting Barthe–Klartag, Proposition 10), display
(2.20): for a log-concave probability law `μ` on `ℝⁿ` and a locally Lipschitz `f` with
`f, ∂ᵢf ∈ L²(μ)`,
`Var_μ f ≤ Σᵢ ‖∂ᵢ f‖²_{H⁻¹(μ)}`,
where `‖q‖_{H⁻¹(μ)} = sup { ∫ q h dμ : h locally Lipschitz, h ∈ L²(μ), ∫ ‖∇h‖² dμ ≤ 1 }` is
`Energy.Dual.dualNorm` (display (2.19)). Here `μ` is full-dimensional
(`Probability.affineSupport μ = ⊤`, equivalently `μ` has a density), `∂ᵢf = Df(eᵢ)` is the
Fréchet partial derivative, which for locally Lipschitz `f` is the a.e. gradient by Rademacher's
theorem, and the conclusion is stated in `ENNReal` so that an infinite right side is allowed.
The source premise `E ∂ᵢf = 0` is not needed: a finite `‖∂ᵢ f‖_{H⁻¹}` forces it
(`Energy.Dual.integral_eq_zero_of_dualNorm_ne_top`), and otherwise the right side is `⊤`.

The ambient-gradient encoding is ill-posed for laws of lower affine dimension, which is why
`affineSupport μ = ⊤` is assumed: for the standard Gaussian `λ` on the hyperplane `{xₙ = 0}` of
`ℝⁿ` (`n ≥ 2`) and `f = x₁ + |xₙ|`, `f` is not Fréchet differentiable at any point of the support,
so every ambient partial derivative is `0` on it and the right side vanishes, while
`Var_λ f = Var_λ x₁ = 1`.

The family theorem `variance_le_sum_dualNorm_sq_of_conjecture` takes the KLS conjecture
`KLS.Conjecture` as a hypothesis; it is used only to bound Poincaré constants uniformly along the
approximation (any finite uniform bound would do). The unconditional form is in
`KLS/Letwin/HminusOne.lean`.

Proof (Barthe–Klartag's approximation argument):
1. `IsBorellDensity.exists_smooth_convex_lower_approximation` gives smooth convex `W_k` with
   `Z_k λ_k = μ + σ_k`, `λ_k = e^{-W_k} dx / Z_k`, `σ_k ≥ 0`, `Z_k → 1`, and uniformly bounded
   second moments; KLS bounds the Poincaré constants `P` of all `λ_k` and of `μ`.
2. For `h ∈ C_c^∞` and a bounded continuous `g` with `N = ‖g‖_{H⁻¹(μ)} < ∞`,
   `|∫ (g - E_{λ_k} g) h dλ_k| ≤ (N √Z_k + ‖g‖_∞ √(Z_k - 1) √(Z_k P)) / Z_k · ‖∇h‖_{L²(λ_k)}`,
   since `Z_k ∫ g (h - E_{λ_k} h) dλ_k` splits into a `μ`-pairing, controlled by `N` and
   `∫ ‖∇h‖² dμ ≤ Z_k ∫ ‖∇h‖² dλ_k`, and a `σ_k`-pairing, controlled by Cauchy–Schwarz,
   `σ_k(ℝⁿ) = Z_k - 1` and Poincaré for `λ_k`.
3. For `F ∈ C¹` with bounded gradient, the `C²` theorem `variance_le_sum_of_partial_dual_bounds`
   on `λ_k`, applied to `F - ⟪c_k, ·⟫` with `c_k = E_{λ_k} ∇F → E_μ ∇F = 0`, and
   `Var_μ ≤ Z_k Var_{λ_k}` give the inequality for `F` in the limit.
4. A general `f` is approximated by `φ_j ∈ C_c^∞` in the weighted `H¹(μ)` sense
   (`LipschitzApproximation.exists_smooth_weighted_L2`), corrected by a linear term to keep
   centered partial derivatives; the dual norm is subadditive and bounded by `√C_P ‖·‖_{L²(μ)}`
   on centered functions.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

namespace FunctionalInequalities.KLS.LogConcave

section Measure

variable {α : Type*} [MeasurableSpace α]

/-- If `Z η = μ + σ`, then integrating against `μ` and `σ` adds up to `Z` times the `η`-integral. -/
private theorem integral_add_eq_mul_of_smul_eq_add {μ η σ : Measure α} {Z : ℝ} (hZ : 0 ≤ Z)
    (hdec : ENNReal.ofReal Z • η = μ + σ) {G : α → ℝ} (hG : Integrable G η) :
    Integrable G μ ∧ Integrable G σ ∧ (∫ x, G x ∂μ) + ∫ x, G x ∂σ = Z * ∫ x, G x ∂η := by
  have hGs : Integrable G (μ + σ) := by
    rw [← hdec]; exact hG.smul_measure ENNReal.ofReal_ne_top
  refine ⟨hGs.left_of_add_measure, hGs.right_of_add_measure, ?_⟩
  rw [← integral_add_measure hGs.left_of_add_measure hGs.right_of_add_measure, ← hdec,
    integral_smul_measure, ENNReal.toReal_ofReal hZ, smul_eq_mul]

/-- `|∫ a f dσ| ≤ (∫ a²)^{1/2} (∫ f²)^{1/2}`. -/
private theorem abs_integral_mul_le_sqrt {σ : Measure α} {a f : α → ℝ} (ha : MemLp a 2 σ)
    (hf : MemLp f 2 σ) :
    |∫ x, a x * f x ∂σ| ≤ Real.sqrt (∫ x, a x ^ 2 ∂σ) * Real.sqrt (∫ x, f x ^ 2 ∂σ) := by
  have h := L2.abs_integral_inner_le ha hf
  have hsa := L2.sqrt_integral_norm_sq_eq ha
  have hsf := L2.sqrt_integral_norm_sq_eq hf
  simp only [Real.norm_eq_abs, sq_abs] at hsa hsf
  rw [hsa, hsf, show (fun x => a x * f x) = fun x => f x * a x from funext fun x => mul_comm _ _]
  simpa only [RCLike.inner_apply, conj_trivial] using h

end Measure

section Euclidean

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Dual transfer under domination from below in density** (the approximation step of
Barthe–Klartag, Proposition 10). Let `Z η = μ + σ` with `Z ≥ 1`, `μ, η` probability laws, `σ ≥ 0`,
and let `η` satisfy the smooth-test Poincaré inequality with constant `P`. For a continuous `g`
with `|g| ≤ G` and finite `N = ‖g‖_{H⁻¹(μ)}`, every `h ∈ C_c^∞` satisfies
`(∫ (g - E_η g) h dη)² ≤ ((N √Z + G √(Z - 1) √(Z P)) / Z)² ∫ ‖Dh‖² dη`. -/
private theorem sq_integral_sub_mul_le {μ η : ProbabilityMeasure E} {σ : Measure E} {Z P G : ℝ}
    (hZ : 1 ≤ Z) (hdec : ENNReal.ofReal Z • (η : Measure E) = (μ : Measure E) + σ)
    (hP : Poincare.SmoothTest.Holds (η : Measure E) P) {g : E → ℝ} (hgc : Continuous g)
    (hgb : ∀ x, |g x| ≤ G) (hg2 : MemLp g 2 (μ : Measure E))
    (hfin : Energy.Dual.dualNorm μ (hg2.toLp g) ≠ ⊤) {h : E → ℝ} (hh : ContDiff ℝ ∞ h)
    (hhc : HasCompactSupport h) :
    (∫ x, (g x - ∫ y, g y ∂(η : Measure E)) * h x ∂(η : Measure E)) ^ 2 ≤
      (((Energy.Dual.dualNorm μ (hg2.toLp g)).toReal * Real.sqrt Z +
              G * Real.sqrt (Z - 1) * Real.sqrt (Z * P)) /
            Z) ^
          2 *
        ∫ x, ‖fderiv ℝ h x‖ ^ 2 ∂(η : Measure E) := by
  set N : ℝ := (Energy.Dual.dualNorm μ (hg2.toLp g)).toReal with hN
  set c : ℝ := ∫ y, g y ∂(η : Measure E) with hc
  set mh : ℝ := ∫ y, h y ∂(η : Measure E) with hmh
  set hb : E → ℝ := fun x => h x - mh with hhb
  set En : ℝ := ∫ x, ‖fderiv ℝ h x‖ ^ 2 ∂(η : Measure E) with hEn
  have hZ0 : 0 ≤ Z := zero_le_one.trans hZ
  have hZpos : 0 < Z := lt_of_lt_of_le one_pos hZ
  have hP0 : 0 ≤ P := hP.constant_nonneg
  have hG0 : 0 ≤ G := (abs_nonneg _).trans (hgb 0)
  have hN0 : 0 ≤ N := ENNReal.toReal_nonneg
  have hEn0 : 0 ≤ En := integral_nonneg fun x => sq_nonneg _
  have hσfin : IsFiniteMeasure σ := by
    constructor
    have h1 : (μ : Measure E) univ + σ univ = ENNReal.ofReal Z := by
      rw [← Measure.add_apply, ← hdec, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    calc
      σ univ ≤ (μ : Measure E) univ + σ univ := le_add_self
      _ = ENNReal.ofReal Z := h1
      _ < ⊤ := ENNReal.ofReal_lt_top
  obtain ⟨Hb, hHb⟩ := hhc.exists_bound_of_continuous hh.continuous
  have hcont1 : ContDiff ℝ 1 h := hh.of_le (by simp)
  have hhcont : Continuous h := hh.continuous
  have hbcont : Continuous hb := hhcont.sub continuous_const
  have hbbound : ∀ x, |hb x| ≤ Hb + |mh| := fun x => by
    have := hHb x
    rw [Real.norm_eq_abs] at this
    exact
      (abs_sub _ _).trans
        (by linarith)
  -- bounded continuous functions are integrable and square integrable on finite measures

  have hint :
    ∀ (ν : Measure E) [IsFiniteMeasure ν] (f : E → ℝ),
      Continuous f → (∃ C, ∀ x, |f x| ≤ C) → Integrable f ν ∧ MemLp f 2 ν := by
    intro ν _ f hf ⟨C, hC⟩
    exact
      ⟨Integrable.of_bound hf.aestronglyMeasurable C (Eventually.of_forall hC),
        MemLp.of_bound hf.aestronglyMeasurable C (Eventually.of_forall hC)⟩
  have hgB : ∃ C, ∀ x, |g x| ≤ C := ⟨G, hgb⟩
  have hhB : ∃ C, ∀ x, |h x| ≤ C := ⟨Hb, fun x => by simpa [Real.norm_eq_abs] using hHb x⟩
  have hbB : ∃ C, ∀ x, |hb x| ≤ C := ⟨_, hbbound⟩
  have hghB : ∃ C, ∀ x, |g x * h x| ≤ C :=
    ⟨G * Hb, fun x => by
      rw [abs_mul]
      exact mul_le_mul (hgb x) (by simpa [Real.norm_eq_abs] using hHb x) (abs_nonneg _) hG0⟩
  have hgbB : ∃ C, ∀ x, |g x * hb x| ≤ C :=
    ⟨G * (Hb + |mh|), fun x => by
      rw [abs_mul];
      exact mul_le_mul (hgb x) (hbbound x) (abs_nonneg _) hG0⟩
  -- Step 1: center the test function

  have hstep1 : ∫ x, (g x - c) * h x ∂(η : Measure E) = ∫ x, g x * hb x ∂(η : Measure E) := by
    have hgi := (hint η g hgc hgB).1
    have hhi := (hint η h hhcont hhB).1
    have hghi := (hint η (fun x => g x * h x) (hgc.mul hhcont) hghB).1
    have e1 : (fun x => (g x - c) * h x) = fun x => g x * h x - c * h x := by funext x; ring
    have e2 : (fun x => g x * hb x) = fun x => g x * h x - mh * g x := by
      funext x;
      simp only [hhb]; ring
    rw [e1, e2, integral_sub hghi (hhi.const_mul c), integral_sub hghi (hgi.const_mul mh),
      integral_const_mul, integral_const_mul, ← hc, ← hmh]
    ring
  -- Step 2: split the pairing along `Z η = μ + σ`

  obtain ⟨hgbμ, hgbσ, hsplit⟩ :=
    integral_add_eq_mul_of_smul_eq_add hZ0 hdec
      (hint η (fun x => g x * hb x) (hgc.mul hbcont) hgbB).1
  -- gradient facts

  have hgradb : gradient hb = gradient h := by
    funext x
    simp only [hhb, gradient, fderiv_sub_const]
  have hgradcont : Continuous (gradient h) := by
    have : gradient h = fun x => (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ h x) := rfl
    rw [this]
    exact (InnerProductSpace.toDual ℝ E).symm.continuous.comp (hh.continuous_fderiv (by simp))
  have hgradcs : HasCompactSupport (gradient h) := by
    have : gradient h = fun x => (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ h x) := rfl
    rw [this]
    exact (hhc.fderiv ℝ).comp_left (map_zero _)
  have hnormgrad : ∀ x, ‖gradient h x‖ = ‖fderiv ℝ h x‖ := fun x =>
    (Poincare.SmoothTest.norm_fderiv_eq_norm_gradient h x).symm
  have hEcs : HasCompactSupport (fun x => ‖gradient h x‖ ^ 2) := by
    have h0 : HasCompactSupport (fun x => ‖gradient h x‖) := hgradcs.norm
    exact h0.comp_left (g := fun r : ℝ => r ^ 2) (by norm_num)
  have hEcont : Continuous (fun x => ‖gradient h x‖ ^ 2) := (hgradcont.norm).pow 2
  have hEint : Integrable (fun x => ‖gradient h x‖ ^ 2) (η : Measure E) :=
    hEcont.integrable_of_hasCompactSupport
      hEcs
  -- Step 3: the `μ`-pairing

  have hbμ2 : MemLp hb 2 (μ : Measure E) := (hint μ hb hbcont hbB).2
  have hgradμ : MemLp (gradient hb) 2 (μ : Measure E) := by
    rw [hgradb];
    exact hgradcont.memLp_of_hasCompactSupport hgradcs
  have hμpair :
    |∫ x, g x * hb x ∂(μ : Measure E)| ≤
      N * Real.sqrt (∫ x, ‖gradient h x‖ ^ 2 ∂(μ : Measure E)) := by
    have h3 :=
      Energy.Dual.abs_inner_toLp_le_mul_sqrt_energy μ (hg2.toLp g) hfin
        ((hcont1.sub contDiff_const).locallyLipschitz) hbμ2 hgradμ
    rw [← L2.integral_inner_toLp hg2 hbμ2, hgradb] at h3
    rw [show (fun x => g x * hb x) = fun x => hb x * g x from funext fun x => mul_comm _ _]
    simpa only [RCLike.inner_apply, conj_trivial] using
      h3
  -- Step 4: energy comparison

  obtain ⟨hEμ, hEσ, hEsplit⟩ := integral_add_eq_mul_of_smul_eq_add hZ0 hdec hEint
  have hEcomp : ∫ x, ‖gradient h x‖ ^ 2 ∂(μ : Measure E) ≤ Z * En := by
    have hσ0 : 0 ≤ ∫ x, ‖gradient h x‖ ^ 2 ∂σ := integral_nonneg fun x => sq_nonneg _
    have : ∫ x, ‖gradient h x‖ ^ 2 ∂(η : Measure E) = En := by simp only [hEn, hnormgrad]
    rw [this] at hEsplit
    linarith
  -- Step 5: the `σ`-pairing

  obtain ⟨-, -, hmass⟩ :=
    integral_add_eq_mul_of_smul_eq_add (G := fun _ => (1 : ℝ)) hZ0 hdec (integrable_const 1)
  simp only [integral_const, probReal_univ, smul_eq_mul, mul_one] at hmass
  have hσmass : σ.real univ = Z - 1 := by linarith
  have hgσ2 : MemLp g 2 σ := (hint σ g hgc hgB).2
  have hbσ2 : MemLp hb 2 σ := (hint σ hb hbcont hbB).2
  have hgsq : ∫ x, g x ^ 2 ∂σ ≤ G ^ 2 * (Z - 1) := by
    calc
      ∫ x, g x ^ 2 ∂σ ≤ ∫ _x, G ^ 2 ∂σ :=
        integral_mono hgσ2.integrable_sq (integrable_const _) fun x => by
          rw [← sq_abs];
          exact pow_le_pow_left₀ (abs_nonneg _) (hgb x) 2
      _ = G ^ 2 * (Z - 1) := by rw [integral_const, smul_eq_mul, hσmass, mul_comm]
  have hbη2 : MemLp hb 2 (η : Measure E) := (hint η hb hbcont hbB).2
  obtain ⟨-, hbσi, hbsplit⟩ := integral_add_eq_mul_of_smul_eq_add hZ0 hdec hbη2.integrable_sq
  have hvar : ∫ x, hb x ^ 2 ∂(η : Measure E) ≤ P * En := by
    have hadm : Poincare.SmoothTest.Admissible (η : Measure E) h :=
      ⟨hh, (hint η h hhcont hhB).2, hEint⟩
    have hv := hP.variance_le hadm
    rw [variance_eq_integral hhcont.aemeasurable] at hv
    rw [Poincare.SmoothTest.energy_eq_fderiv] at hv
    exact hv
  have hbsq : ∫ x, hb x ^ 2 ∂σ ≤ Z * (P * En) := by
    have hμ0 : 0 ≤ ∫ x, hb x ^ 2 ∂(μ : Measure E) := integral_nonneg fun x => sq_nonneg _
    have := mul_le_mul_of_nonneg_left hvar hZ0
    linarith
  have hσpair :
    |∫ x, g x * hb x ∂σ| ≤ G * Real.sqrt (Z - 1) * Real.sqrt (Z * P) * Real.sqrt En := by
    refine (abs_integral_mul_le_sqrt hgσ2 hbσ2).trans ?_
    have h1 : Real.sqrt (∫ x, g x ^ 2 ∂σ) ≤ G * Real.sqrt (Z - 1) :=
      calc
        Real.sqrt (∫ x, g x ^ 2 ∂σ) ≤ Real.sqrt (G ^ 2 * (Z - 1)) := Real.sqrt_le_sqrt hgsq
        _ = G * Real.sqrt (Z - 1) := by rw [Real.sqrt_mul (sq_nonneg G), Real.sqrt_sq hG0]
    have h2 : Real.sqrt (∫ x, hb x ^ 2 ∂σ) ≤ Real.sqrt (Z * P) * Real.sqrt En :=
      calc
        Real.sqrt (∫ x, hb x ^ 2 ∂σ) ≤ Real.sqrt (Z * (P * En)) := Real.sqrt_le_sqrt hbsq
        _ = Real.sqrt (Z * P) * Real.sqrt En := by
          rw [← mul_assoc, Real.sqrt_mul (mul_nonneg hZ0 hP0)]
    calc
      Real.sqrt (∫ x, g x ^ 2 ∂σ) * Real.sqrt (∫ x, hb x ^ 2 ∂σ) ≤
          (G * Real.sqrt (Z - 1)) * (Real.sqrt (Z * P) * Real.sqrt En) :=
        mul_le_mul h1 h2 (Real.sqrt_nonneg _) (mul_nonneg hG0 (Real.sqrt_nonneg _))
      _ = _ := by
        ring
  -- Step 6: assemble

  have hμpair' : |∫ x, g x * hb x ∂(μ : Measure E)| ≤ N * Real.sqrt Z * Real.sqrt En := by
    refine hμpair.trans ?_
    rw [mul_assoc, ← Real.sqrt_mul hZ0]
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hEcomp) hN0
  set A : ℝ := (N * Real.sqrt Z + G * Real.sqrt (Z - 1) * Real.sqrt (Z * P)) / Z with hA
  have hbound : |∫ x, (g x - c) * h x ∂(η : Measure E)| ≤ A * Real.sqrt En := by
    rw [hstep1]
    have hZI :
      Z * |∫ x, g x * hb x ∂(η : Measure E)| ≤
        (N * Real.sqrt Z + G * Real.sqrt (Z - 1) * Real.sqrt (Z * P)) * Real.sqrt En := by
      rw [← abs_of_pos hZpos, ← abs_mul, ← hsplit, abs_of_pos hZpos]
      refine (abs_add_le _ _).trans ?_
      rw [add_mul]
      exact add_le_add hμpair' hσpair
    rw [hA, div_mul_eq_mul_div, le_div_iff₀ hZpos]
    linarith
  have hA0 : 0 ≤ A :=
    div_nonneg
      (add_nonneg (mul_nonneg hN0 (Real.sqrt_nonneg _))
        (mul_nonneg (mul_nonneg hG0 (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)))
      hZ0
  calc
    (∫ x, (g x - c) * h x ∂(η : Measure E)) ^ 2 = |∫ x, (g x - c) * h x ∂(η : Measure E)| ^ 2 :=
      (sq_abs _).symm
    _ ≤ (A * Real.sqrt En) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hbound 2
    _ = A ^ 2 * En := by rw [mul_pow, Real.sq_sqrt hEn0]

end Euclidean

section Variance

variable {α : Type*} [MeasurableSpace α]

/-- `Var X = ‖X - E X‖²_{L²}`. -/
private theorem variance_eq_norm_center_sq (μ : ProbabilityMeasure α) {X : α → ℝ}
    (hX : MemLp X 2 (μ : Measure α)) :
    variance X (μ : Measure α) = ‖L2.center μ (hX.toLp X)‖ ^ 2 := by
  rw [← L2.coe_variance, L2.variance_toLp, Real.coe_toNNReal _ (variance_nonneg _ _)]

/-- `√Var (X + Y) ≤ √Var X + √Var Y`. -/
private theorem variance_add_le (μ : ProbabilityMeasure α) {X Y : α → ℝ}
    (hX : MemLp X 2 (μ : Measure α)) (hY : MemLp Y 2 (μ : Measure α)) :
    variance (fun x => X x + Y x) (μ : Measure α) ≤
      (Real.sqrt (variance X (μ : Measure α)) + Real.sqrt (variance Y (μ : Measure α))) ^ 2 := by
  have hXY : MemLp (fun x => X x + Y x) 2 (μ : Measure α) := hX.add hY
  rw [variance_eq_norm_center_sq μ hXY, variance_eq_norm_center_sq μ hX,
    variance_eq_norm_center_sq μ hY, Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]
  have ht : hXY.toLp (fun x => X x + Y x) = hX.toLp X + hY.toLp Y := MemLp.toLp_add hX hY
  rw [ht, L2.center_add]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) 2

/-- **Variance under domination from below in density**: if `Z η = μ + σ` with `0 ≤ Z`, every
measurable `F ∈ L²(η)` lies in `L²(μ)` and `Var_μ F ≤ Z Var_η F`. -/
private theorem variance_le_mul_of_smul_eq_add {μ η : ProbabilityMeasure α} {σ : Measure α}
    {Z : ℝ} (hZ : 0 ≤ Z) (hdec : ENNReal.ofReal Z • (η : Measure α) = (μ : Measure α) + σ)
    {F : α → ℝ} (hFm : Measurable F) (hF : MemLp F 2 (η : Measure α)) :
    MemLp F 2 (μ : Measure α) ∧ variance F (μ : Measure α) ≤ Z * variance F (η : Measure α) := by
  set c : ℝ := ∫ x, F x ∂(η : Measure α)
  have hG : Integrable (fun x => (F x - c) ^ 2) (η : Measure α) :=
    (hF.sub (memLp_const c)).integrable_sq
  obtain ⟨hGμ, hGσ, hsplit⟩ := integral_add_eq_mul_of_smul_eq_add hZ hdec hG
  have hFμ : MemLp (fun x => F x - c) 2 (μ : Measure α) :=
    (memLp_two_iff_integrable_sq (hFm.sub measurable_const).aestronglyMeasurable).mpr hGμ
  have hFμ' : MemLp F 2 (μ : Measure α) := by
    have := hFμ.add (memLp_const c)
    convert this using 1
    funext x
    simp
  refine ⟨hFμ', ?_⟩
  have h1 : variance F (μ : Measure α) = variance (fun x => F x - c) (μ : Measure α) :=
    (variance_sub_const hFm.aestronglyMeasurable c).symm
  have h2 := variance_le_expectation_sq (μ := (μ : Measure α))
    (hFm.sub measurable_const).aestronglyMeasurable (X := fun x => F x - c)
  have h3 : variance F (η : Measure α) = ∫ x, (F x - c) ^ 2 ∂(η : Measure α) :=
    variance_eq_integral hFm.aemeasurable
  have hσ0 : 0 ≤ ∫ x, (F x - c) ^ 2 ∂σ := integral_nonneg fun x => sq_nonneg _
  rw [h1, h3]
  simp only [Pi.pow_apply] at h2
  linarith

end Variance

section Covariance

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- `‖Cov(η)‖ ≤ ∫ ‖x‖² dη` for a probability law with finite second moment. -/
private theorem opNorm_covariance_le {η : Measure E} [IsProbabilityMeasure η]
    (h2 : MemLp id 2 η) : ‖Covariance.operator η‖ ≤ ∫ x, ‖x‖ ^ 2 ∂η := by
  set S : ℝ := ∫ x, ‖x‖ ^ 2 ∂η with hS
  have hS0 : 0 ≤ S := integral_nonneg fun x => sq_nonneg _
  have hSint : Integrable (fun x : E => ‖x‖ ^ 2) η :=
    (memLp_two_iff_integrable_sq_norm h2.aestronglyMeasurable).mp h2
  have hmem (v : E) : MemLp (fun x : E => ⟪v, x⟫) 2 η := by
    have hh : MemLp (fun x : E => ⟪id x, v⟫) 2 η := h2.inner_const v
    simpa [real_inner_comm] using hh
  have hvar (v : E) : variance (fun x : E => ⟪v, x⟫) η ≤ ‖v‖ ^ 2 * S := by
    have hv := variance_le_expectation_sq (μ := η) (X := fun x : E => ⟪v, x⟫)
      (hmem v).aestronglyMeasurable
    simp only [Pi.pow_apply] at hv
    refine hv.trans ?_
    rw [hS, ← integral_const_mul]
    refine integral_mono (hmem v).integrable_sq (hSint.const_mul _) fun x => ?_
    have := abs_real_inner_le_norm v x
    have h0 : 0 ≤ ‖v‖ * ‖x‖ := by positivity
    calc ⟪v, x⟫ ^ 2 = |⟪v, x⟫| ^ 2 := (sq_abs _).symm
      _ ≤ (‖v‖ * ‖x‖) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
      _ = ‖v‖ ^ 2 * ‖x‖ ^ 2 := by ring
  have hcov (v w : E) : |⟪Covariance.operator η v, w⟫| ≤ S * ‖v‖ * ‖w‖ := by
    have hcs := Probability.covariance_sq_le_variance_mul_variance (hmem v) (hmem w)
    rw [Covariance.operator_inner, covarianceBilin_apply_eq_cov h2]
    have hsq : (covariance (fun x : E => ⟪v, x⟫) (fun x : E => ⟪w, x⟫) η) ^ 2 ≤
        (S * ‖v‖ * ‖w‖) ^ 2 := by
      refine hcs.trans ?_
      calc variance (fun x : E => ⟪v, x⟫) η * variance (fun x : E => ⟪w, x⟫) η
          ≤ (‖v‖ ^ 2 * S) * (‖w‖ ^ 2 * S) :=
            mul_le_mul (hvar v) (hvar w) (variance_nonneg _ _) (by positivity)
        _ = (S * ‖v‖ * ‖w‖) ^ 2 := by ring
    rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_sq (show 0 ≤ S * ‖v‖ * ‖w‖ by positivity)]
    exact Real.sqrt_le_sqrt hsq
  refine ContinuousLinearMap.opNorm_le_bound _ hS0 fun v => ?_
  set T := Covariance.operator η
  have h1 := hcov v (T v)
  rw [real_inner_self_eq_norm_sq, abs_of_nonneg (sq_nonneg _)] at h1
  rcases (norm_nonneg (T v)).eq_or_lt with h0 | hpos
  · rw [← h0]; positivity
  · have : ‖T v‖ * ‖T v‖ ≤ S * ‖v‖ * ‖T v‖ := by nlinarith
    exact le_of_mul_le_mul_right this hpos

end Covariance

section Poincare

/-- **Uniform smooth-test Poincaré constants from the KLS conjecture**: there is `K ≥ 0` such
that every log-concave law `η` on `ℝⁿ` with `∫ ‖x‖² dη ≤ C₂` satisfies the smooth-test Poincaré
inequality with constant `K C₂ + 1`. -/
private theorem exists_smoothTest_holds_of_conjecture (hKLS : KLS.Conjecture) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {n : ℕ} (η : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))),
      LogConcave η → MemLp id 2 (η : Measure (EuclideanSpace ℝ (Fin n))) → ∀ C₂ : ℝ,
        ∫ x, ‖x‖ ^ 2 ∂(η : Measure (EuclideanSpace ℝ (Fin n))) ≤ C₂ →
        Poincare.SmoothTest.Holds (η : Measure (EuclideanSpace ℝ (Fin n))) (K * C₂ + 1) := by
  obtain ⟨K, hK⟩ := hKLS
  refine ⟨K, K.2, fun {n} η hη h2 C₂ hC₂ => ?_⟩
  have h1 := hK n η hη h2
  have hcov := opNorm_covariance_le h2
  have hC0 : 0 ≤ C₂ := (integral_nonneg fun x => sq_nonneg _).trans hC₂
  have hlt : Poincare.SmoothTest.constant (η : Measure (EuclideanSpace ℝ (Fin n))) <
      ENNReal.ofReal (K * C₂ + 1) := by
    rw [smoothTest_constant_eq_localSlope hη]
    calc Poincare.LocalSlope.Intrinsic.constant η
        ≤ (K : ENNReal) * ENNReal.ofReal ‖Covariance.operator
            (η : Measure (EuclideanSpace ℝ (Fin n)))‖ := h1
      _ ≤ (K : ENNReal) * ENNReal.ofReal C₂ := by
          gcongr; exact hcov.trans hC₂
      _ = ENNReal.ofReal (K * C₂) := by
          rw [ENNReal.ofReal_mul (NNReal.coe_nonneg K), ENNReal.ofReal_coe_nnreal]
      _ < ENNReal.ofReal (K * C₂ + 1) :=
          (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (by linarith)
  obtain ⟨⟨C, hC⟩, hClt⟩ := iInf_lt_iff.mp hlt
  refine hC.mono ?_
  have : ((C : ℝ≥0∞)).toReal < K * C₂ + 1 := by
    have := (ENNReal.toReal_lt_toReal ENNReal.coe_ne_top ENNReal.ofReal_ne_top).mpr hClt
    rwa [ENNReal.toReal_ofReal (by positivity)] at this
  exact this.le

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- A smooth-test Poincaré inequality of an absolutely continuous law extends to every locally
Lipschitz `g ∈ L²` with `∇g ∈ L²` (`SmoothTest.holds_iff_localSlope`,
`LocalSlope.holds_iff_memLp_gradient`). -/
private theorem variance_le_of_smoothTest_holds {μ : ProbabilityMeasure E} (m : Measure E)
    [m.IsAddHaarMeasure] (hac : (μ : Measure E) ≪ m) {C : ℝ}
    (hC : Poincare.SmoothTest.Holds (μ : Measure E) C) {g : E → ℝ} (hl : LocallyLipschitz g)
    (h2 : MemLp g 2 (μ : Measure E)) (hg : MemLp (gradient g) 2 (μ : Measure E)) :
    variance g (μ : Measure E) ≤ C * ∫ x, ‖gradient g x‖ ^ 2 ∂(μ : Measure E) := by
  have hC0 := hC.constant_nonneg
  have hH : Poincare.LocalSlope.Holds μ C.toNNReal :=
    (Poincare.SmoothTest.holds_iff_localSlope μ m hac C.toNNReal).mp
      (by rw [Real.coe_toNNReal _ hC0]; exact hC)
  have h := (Poincare.LocalSlope.holds_iff_memLp_gradient μ m hac _).mp hH g hl h2 hg
  have hint : Integrable (fun x => ‖gradient g x‖ ^ 2) (μ : Measure E) :=
    (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mp hg
  have hlin : ∫⁻ x, ENNReal.ofReal ‖gradient g x‖ ^ 2 ∂(μ : Measure E) =
      ENNReal.ofReal (∫ x, ‖gradient g x‖ ^ 2 ∂(μ : Measure E)) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun x => sq_nonneg _)]
    congr 1
    funext x
    rw [ENNReal.ofReal_pow (norm_nonneg _)]
  rw [← ofReal_variance h2, hlin, ← ENNReal.ofReal_coe_nnreal, Real.coe_toNNReal _ hC0,
    ← ENNReal.ofReal_mul hC0] at h
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC0 (integral_nonneg fun x => sq_nonneg _))).mp h

end Poincare

section SmoothClass

variable {n : ℕ}

/-- The measure identity `Z η = μ + σ` makes `σ` finite with mass `Z - 1`. -/
private theorem isFiniteMeasure_and_real_univ {α : Type*} [MeasurableSpace α]
    {μ η : ProbabilityMeasure α} {σ : Measure α} {Z : ℝ} (hZ : 0 ≤ Z)
    (hdec : ENNReal.ofReal Z • (η : Measure α) = (μ : Measure α) + σ) :
    IsFiniteMeasure σ ∧ σ.real univ = Z - 1 := by
  have hfin : IsFiniteMeasure σ := by
    constructor
    have h1 : (μ : Measure α) univ + σ univ = ENNReal.ofReal Z := by
      rw [← Measure.add_apply, ← hdec, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    calc σ univ ≤ (μ : Measure α) univ + σ univ := le_add_self
      _ = ENNReal.ofReal Z := h1
      _ < ⊤ := ENNReal.ofReal_lt_top
  refine ⟨hfin, ?_⟩
  obtain ⟨-, -, hmass⟩ := integral_add_eq_mul_of_smul_eq_add (G := fun _ => (1 : ℝ)) hZ hdec
    (integrable_const 1)
  simp only [integral_const, probReal_univ, smul_eq_mul, mul_one] at hmass
  linarith

/-- **One approximation step** (Barthe–Klartag, Proposition 10). Let `η = e^{-W} dx / ∫ e^{-W}`
with `W` convex and `C²`, `Z η = μ + σ` with `Z ≥ 1`, `η` satisfying the smooth-test Poincaré
inequality with constant `P`, and `μ, η` with finite second moments. For `F ∈ C¹` with
`‖DF‖ ≤ L_F` and finite `N_i = ‖∂ᵢF‖_{H⁻¹(μ)}`,
`Var_μ F ≤ (√(Z Σᵢ A_i²) + n L_F (Z - 1) (∫ ‖x‖² dμ)^{1/2})²`,
`A_i = (N_i √Z + L_F √(Z - 1) √(Z P)) / Z`. -/
private theorem variance_le_of_lower_density
    {μ η : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))}
    {σ : Measure (EuclideanSpace ℝ (Fin n))} {W : EuclideanSpace ℝ (Fin n) → ℝ}
    (hη : LogConcave η) (hηW : (η : Measure (EuclideanSpace ℝ (Fin n))) = volume.tilted (-W))
    (hW : ContDiff ℝ 2 W) (hWc : ConvexOn ℝ univ W) {Z P : ℝ} (hZ : 1 ≤ Z)
    (hdec :
      ENNReal.ofReal Z • (η : Measure (EuclideanSpace ℝ (Fin n))) =
        (μ : Measure (EuclideanSpace ℝ (Fin n))) + σ)
    (hP : Poincare.SmoothTest.Holds (η : Measure (EuclideanSpace ℝ (Fin n))) P)
    (hη2 : MemLp id 2 (η : Measure (EuclideanSpace ℝ (Fin n))))
    (hμ2 : MemLp id 2 (μ : Measure (EuclideanSpace ℝ (Fin n))))
    {F : EuclideanSpace ℝ (Fin n) → ℝ} (hF : ContDiff ℝ 1 F) {Lf : ℝ}
    (hLf : ∀ x, ‖fderiv ℝ F x‖ ≤ Lf)
    (hdF :
      ∀ i,
        MemLp (fun x => fderiv ℝ F x (EuclideanSpace.single i 1)) 2
          (μ : Measure (EuclideanSpace ℝ (Fin n))))
    (hfin : ∀ i, Energy.Dual.dualNorm μ ((hdF i).toLp _) ≠ ⊤) :
    variance F (μ : Measure (EuclideanSpace ℝ (Fin n))) ≤
      (Real.sqrt
            (Z *
              ∑ i,
                (((Energy.Dual.dualNorm μ ((hdF i).toLp _)).toReal * Real.sqrt Z +
                      Lf * Real.sqrt (Z - 1) * Real.sqrt (Z * P)) /
                    Z) ^
                  2) +
          n * (Lf * (Z - 1)) *
            Real.sqrt (∫ x, ‖x‖ ^ 2 ∂(μ : Measure (EuclideanSpace ℝ (Fin n))))) ^
        2 := by
  set g : Fin n → (EuclideanSpace ℝ (Fin n)) → ℝ := fun i x =>
    fderiv ℝ F x (EuclideanSpace.single i 1) with hg
  set A : Fin n → ℝ := fun i =>
    ((Energy.Dual.dualNorm μ ((hdF i).toLp _)).toReal * Real.sqrt Z +
        Lf * Real.sqrt (Z - 1) * Real.sqrt (Z * P)) /
      Z with
    hA
  set M : ℝ := ∫ x, ‖x‖ ^ 2 ∂(μ : Measure (EuclideanSpace ℝ (Fin n))) with hM
  have hZ0 : 0 ≤ Z := zero_le_one.trans hZ
  have hZpos : 0 < Z := lt_of_lt_of_le one_pos hZ
  have hLf0 : 0 ≤ Lf := (norm_nonneg _).trans (hLf 0)
  obtain ⟨hσfin, hσmass⟩ := isFiniteMeasure_and_real_univ hZ0 hdec
  have hgc : ∀ i, Continuous (g i) := fun i =>
    (hF.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hgb : ∀ i x, |g i x| ≤ Lf := fun i x => by
    have := (fderiv ℝ F x).le_opNorm (EuclideanSpace.single i 1)
    rw [PiLp.norm_single, norm_one, mul_one] at this
    exact
      (Real.norm_eq_abs _ ▸ this).trans
        (hLf x)
  -- the `η`-means of the partial derivatives are small

  set c : Fin n → ℝ := fun i => ∫ x, g i x ∂(η : Measure (EuclideanSpace ℝ (Fin n))) with hc
  have hcb : ∀ i, |c i| ≤ Lf * (Z - 1) := by
    intro i
    have hgi : Integrable (g i) (η : Measure (EuclideanSpace ℝ (Fin n))) :=
      Integrable.of_bound (hgc i).aestronglyMeasurable Lf (Eventually.of_forall (hgb i))
    obtain ⟨-, -, hsplit⟩ := integral_add_eq_mul_of_smul_eq_add hZ0 hdec hgi
    have hmean : ∫ x, g i x ∂(μ : Measure (EuclideanSpace ℝ (Fin n))) = 0 := by
      have h0 := Energy.Dual.integral_eq_zero_of_dualNorm_ne_top μ _ (hfin i)
      rw [← h0]
      exact (integral_congr_ae (hdF i).coeFn_toLp).symm
    rw [hmean, zero_add] at hsplit
    have hσb : |∫ x, g i x ∂σ| ≤ Lf * σ.real univ := by
      have :=
        norm_integral_le_of_norm_le_const (μ := σ) (f := g i) (C := Lf)
          (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hgb i x)
      rwa [Real.norm_eq_abs] at this
    rw [hσmass, hsplit, abs_mul, abs_of_pos hZpos] at hσb
    have hc0 : 0 ≤ |c i| := abs_nonneg _
    nlinarith
  -- the linear correction

  set v : (EuclideanSpace ℝ (Fin n)) := ∑ i, c i • EuclideanSpace.single i (1 : ℝ) with hv
  have hvi : ∀ i, ⟪v, EuclideanSpace.single i (1 : ℝ)⟫ = c i := fun i => by
    rw [hv, (EuclideanSpace.orthonormal_single (𝕜 := ℝ) (ι := Fin n)).inner_left_fintype]
    rfl
  have hvn : ‖v‖ ≤ n * (Lf * (Z - 1)) := by
    calc
      ‖v‖ ≤ ∑ i, ‖c i • EuclideanSpace.single i (1 : ℝ)‖ := norm_sum_le _ _
      _ = ∑ i, |c i| := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [norm_smul, PiLp.norm_single, norm_one, mul_one, Real.norm_eq_abs]
      _ ≤ ∑ _i : Fin n, Lf * (Z - 1) := Finset.sum_le_sum fun i _ => hcb i
      _ = n * (Lf * (Z - 1)) := by simp
  set ℓ : (EuclideanSpace ℝ (Fin n)) → ℝ := fun x => ⟪v, x⟫ with hℓ
  set F' : (EuclideanSpace ℝ (Fin n)) → ℝ := fun x => F x - ℓ x with hF'
  have hℓd : ∀ x, HasFDerivAt ℓ (innerSL ℝ v) x := fun x => (innerSL ℝ v).hasFDerivAt
  have hF'd : ∀ x, fderiv ℝ F' x = fderiv ℝ F x - innerSL ℝ v := fun x =>
    (((hF.differentiable one_ne_zero) x).hasFDerivAt.sub (hℓd x)).fderiv
  have hF'1 : ContDiff ℝ 1 F' := hF.sub (innerSL ℝ v).contDiff
  have hpart :
    ∀ i, (fun x => fderiv ℝ F' x (EuclideanSpace.single i 1)) = fun x => g i x - c i := fun i => by
    funext x
    rw [hF'd, sub_apply, innerSL_apply_apply, hvi]
  -- integrability on `η`

  have hFlip : LipschitzWith Lf.toNNReal F :=
    lipschitzWith_of_nnnorm_fderiv_le (hF.differentiable one_ne_zero) fun x => by
      rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ hLf0]; exact hLf x
  have hF'bound : ∀ x, ‖F' x‖ ≤ ‖|F 0| + (Lf + ‖v‖) * ‖id x‖‖ := by
    intro x
    have h1 := hFlip.dist_le_mul x 0
    rw [Real.coe_toNNReal _ hLf0, dist_zero_right, Real.dist_eq] at h1
    have h2 := abs_real_inner_le_norm v x
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0 ≤ |F 0| + (Lf + ‖v‖) * ‖id x‖)]
    simp only [hF', hℓ, id]
    have := abs_sub (F x) ⟪v, x⟫
    have := abs_sub_abs_le_abs_sub (F x) (F 0)
    nlinarith [abs_nonneg (F 0)]
  have hF'cont : Continuous F' := hF'1.continuous
  have hF'2 : MemLp F' 2 (η : Measure (EuclideanSpace ℝ (Fin n))) :=
    MemLp.of_le ((memLp_const |F 0|).add (hη2.norm.const_mul (Lf + ‖v‖)))
      hF'cont.aestronglyMeasurable (Eventually.of_forall hF'bound)
  have hdf2 :
    ∀ i,
      MemLp (fun x => fderiv ℝ F' x (EuclideanSpace.single i 1)) 2
        (η : Measure (EuclideanSpace ℝ (Fin n))) :=
    fun i => by
    rw [hpart i]
    exact
      MemLp.of_bound ((hgc i).sub continuous_const).aestronglyMeasurable (Lf + |c i|)
        (Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs];
          exact (abs_sub _ _).trans (by linarith [hgb i x]))
  -- the `C²` theorem on `η`

  have hK :
    ∀ i (h : (EuclideanSpace ℝ (Fin n)) → ℝ),
      ContDiff ℝ ∞ h →
        HasCompactSupport h →
          (∫ x,
                fderiv ℝ F' x (EuclideanSpace.single i 1) *
                  h x ∂(η : Measure (EuclideanSpace ℝ (Fin n)))) ^
              2 ≤
            A i ^ 2 * ∫ x, ‖fderiv ℝ h x‖ ^ 2 ∂(η : Measure (EuclideanSpace ℝ (Fin n))) := by
    intro i h hh hhc
    have := sq_integral_sub_mul_le hZ hdec hP (hgc i) (hgb i) (hdF i) (hfin i) hh hhc
    have hpt : ∀ x, fderiv ℝ F' x (EuclideanSpace.single i 1) = g i x - c i := fun x =>
      congrFun (hpart i) x
    simp_rw [hpt]
    exact this
  have hVη :=
    variance_le_sum_of_partial_dual_bounds volume hη hηW hW hWc hF'1 hF'2 hdf2
      (fun i => A i ^ 2)
      hK
  -- back to `μ`

  obtain ⟨hF'μ, hVμ⟩ := variance_le_mul_of_smul_eq_add hZ0 hdec hF'cont.measurable hF'2
  have hℓμ : MemLp ℓ 2 (μ : Measure (EuclideanSpace ℝ (Fin n))) := by
    have hh :
      MemLp (fun x : (EuclideanSpace ℝ (Fin n)) => ⟪id x, v⟫) 2
        (μ : Measure (EuclideanSpace ℝ (Fin n))) :=
      hμ2.inner_const v
    simpa [hℓ, real_inner_comm] using hh
  have hFsplit : F = fun x => F' x + ℓ x := by funext x; simp [hF']
  have hVF := variance_add_le μ hF'μ hℓμ
  rw [← hFsplit] at hVF
  have hVℓ :
    Real.sqrt (variance ℓ (μ : Measure (EuclideanSpace ℝ (Fin n)))) ≤
      n * (Lf * (Z - 1)) * Real.sqrt M := by
    have hv :=
      variance_le_expectation_sq (μ := (μ : Measure (EuclideanSpace ℝ (Fin n)))) (X := ℓ)
        hℓμ.aestronglyMeasurable
    simp only [Pi.pow_apply] at hv
    have hSint :
      Integrable (fun x : (EuclideanSpace ℝ (Fin n)) => ‖x‖ ^ 2)
        (μ : Measure (EuclideanSpace ℝ (Fin n))) :=
      (memLp_two_iff_integrable_sq_norm hμ2.aestronglyMeasurable).mp hμ2
    have hle : ∫ x, ℓ x ^ 2 ∂(μ : Measure (EuclideanSpace ℝ (Fin n))) ≤ ‖v‖ ^ 2 * M := by
      rw [hM, ← integral_const_mul]
      refine integral_mono hℓμ.integrable_sq (hSint.const_mul _) fun x => ?_
      have := abs_real_inner_le_norm v x
      calc
        ℓ x ^ 2 = |⟪v, x⟫| ^ 2 := (sq_abs _).symm
        _ ≤ (‖v‖ * ‖x‖) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
        _ = ‖v‖ ^ 2 * ‖x‖ ^ 2 := by ring
    calc
      Real.sqrt (variance ℓ (μ : Measure (EuclideanSpace ℝ (Fin n)))) ≤
          Real.sqrt (‖v‖ ^ 2 * M) :=
        Real.sqrt_le_sqrt (hv.trans hle)
      _ = ‖v‖ * Real.sqrt M := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]
      _ ≤ n * (Lf * (Z - 1)) * Real.sqrt M :=
        mul_le_mul_of_nonneg_right hvn (Real.sqrt_nonneg _)
  have hVF' :
    Real.sqrt (variance F' (μ : Measure (EuclideanSpace ℝ (Fin n)))) ≤
      Real.sqrt (Z * ∑ i, A i ^ 2) :=
    Real.sqrt_le_sqrt (hVμ.trans (mul_le_mul_of_nonneg_left hVη hZ0))
  refine hVF.trans (pow_le_pow_left₀ (by positivity) (add_le_add hVF' hVℓ) 2)

/-- **Proposition 2.8 for `C¹` functions with bounded gradient** (given the KLS conjecture):
for a full-dimensional log-concave `μ` on `ℝⁿ`, `F ∈ C¹` with `‖DF‖ ≤ L_F` and finite
`‖∂ᵢF‖_{H⁻¹(μ)}`, `Var_μ F ≤ Σᵢ ‖∂ᵢF‖²_{H⁻¹(μ)}`. -/
private theorem variance_le_sum_toReal_dualNorm_sq_of_bounded_fderiv (hKLS : KLS.Conjecture)
    {μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))} (hμ : LogConcave μ)
    (hfull : Probability.affineSupport μ = ⊤) {F : EuclideanSpace ℝ (Fin n) → ℝ}
    (hF : ContDiff ℝ 1 F) {Lf : ℝ} (hLf : ∀ x, ‖fderiv ℝ F x‖ ≤ Lf)
    (hdF :
      ∀ i,
        MemLp (fun x => fderiv ℝ F x (EuclideanSpace.single i 1)) 2
          (μ : Measure (EuclideanSpace ℝ (Fin n))))
    (hfin : ∀ i, Energy.Dual.dualNorm μ ((hdF i).toLp _) ≠ ⊤) :
    variance F (μ : Measure (EuclideanSpace ℝ (Fin n))) ≤
      ∑ i, (Energy.Dual.dualNorm μ ((hdF i).toLp _)).toReal ^ 2 := by
  obtain ⟨hac, hμ2⟩ := absolutelyContinuous_and_memLp_two_of_affineSupport_eq_top μ hμ hfull
  have hint := hμ.interior_support_nonempty_of_affineSupport_eq_top hfull
  obtain ⟨ρ, hρ⟩ := hμ.exists_isBorellDensity_of_interior_support_nonempty volume hint hac
  obtain ⟨t, ht, hexp, -⟩ := hμ.exists_integrable_exp_norm_contDiffOn_logLaplace
  obtain ⟨W, C₂, hWs, hWc, hWint, -, hZ1, hZlim, hdec, hmom⟩ :=
    hρ.exists_smooth_convex_lower_approximation ht hexp
  obtain ⟨K, -, hKP⟩ := exists_smoothTest_holds_of_conjecture hKLS
  set P : ℝ := K * C₂ + 1 with hP
  set N : Fin n → ℝ := fun i => (Energy.Dual.dualNorm μ ((hdF i).toLp _)).toReal with hN
  set M : ℝ := ∫ x, ‖x‖ ^ 2 ∂(μ : Measure (EuclideanSpace ℝ (Fin n))) with hM
  set Zs : ℕ → ℝ := fun k => ∫ x, Real.exp (-W k x) with hZs
  set R : ℝ → ℝ := fun Z =>
    (Real.sqrt
          (Z *
            ∑ i, ((N i * Real.sqrt Z + Lf * Real.sqrt (Z - 1) * Real.sqrt (Z * P)) / Z) ^ 2) +
        n * (Lf * (Z - 1)) * Real.sqrt M) ^
      2 with
    hR
  have hbound : ∀ k, variance F (μ : Measure (EuclideanSpace ℝ (Fin n))) ≤ R (Zs k) := by
    intro k
    have hprob :
      IsProbabilityMeasure ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-W k)) :=
      isProbabilityMeasure_tilted (hWint k)
    set η : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)) := ⟨_, hprob⟩ with hη
    have hηW : (η : Measure (EuclideanSpace ℝ (Fin n))) = volume.tilted (-W k) := rfl
    have hηlc : LogConcave η := logConcave_of_eq_tilted hηW (hWs k).continuous (hWc k)
    have hη2 : MemLp id 2 (η : Measure (EuclideanSpace ℝ (Fin n))) :=
      (memLp_two_iff_integrable_sq_norm aestronglyMeasurable_id).mpr (hmom k).1
    have hPk := hKP η hηlc hη2 C₂ (hmom k).2
    exact
      variance_le_of_lower_density hηlc hηW ((hWs k).of_le (WithTop.coe_le_coe.mpr le_top))
        (hWc k) (hZ1 k) (hdec k) hPk hη2 hμ2 hF hLf hdF hfin
  have hRcont : ContinuousAt R 1 := by
    simp only [hR]
    fun_prop (disch := norm_num)
  have hlim : Tendsto (fun k => R (Zs k)) atTop (𝓝 (R 1)) := hRcont.tendsto.comp hZlim
  have hR1 : R 1 = ∑ i, N i ^ 2 := by
    simp only [hR, Real.sqrt_one, sub_self, Real.sqrt_zero, mul_zero, zero_mul, add_zero,
      mul_one, div_one, one_mul]
    rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  rw [← hR1]
  exact ge_of_tendsto' hlim hbound

/-- The partial derivative `Df(x) eᵢ` is the `i`-th coordinate of the gradient. -/
private theorem fderiv_single_eq_inner (φ : EuclideanSpace ℝ (Fin n) → ℝ) (i : Fin n)
    (x : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ φ x (EuclideanSpace.single i 1) = ⟪gradient φ x, EuclideanSpace.single i 1⟫ :=
  inner_gradient_left.symm

/-- `‖∇φ(x)‖² = Σᵢ (Dφ(x) eᵢ)²`. -/
private theorem norm_gradient_sq_eq_sum (φ : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖gradient φ x‖ ^ 2 = ∑ i, (fderiv ℝ φ x (EuclideanSpace.single i 1)) ^ 2 := by
  rw [← (EuclideanSpace.basisFun (Fin n) ℝ).sum_sq_inner_right]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [EuclideanSpace.basisFun_apply, fderiv_single_eq_inner, real_inner_comm]

/-- **One smooth approximation step.** Let `μ` be full-dimensional log-concave, `f` locally
Lipschitz with `f, ∂ᵢf ∈ L²(μ)` and finite `N_i = ‖∂ᵢ f‖_{H⁻¹(μ)}`, and let `μ` satisfy the
gradient Poincaré inequality with constant `P`. For `φ ∈ C_c^∞`, with
`δ = ‖∇φ - ∇f‖_{L²(μ)}` and `ε = ‖φ - f‖_{L²(μ)}`,
`Var_μ f ≤ (√(Σᵢ (N_i + √P δ)²) + ε + n δ (∫ ‖x‖² dμ)^{1/2})²`. -/
private theorem variance_le_of_smooth_approx (hKLS : KLS.Conjecture)
    {μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))} (hμ : LogConcave μ)
    (hfull : Probability.affineSupport μ = ⊤)
    (hμ2 : MemLp id 2 (μ : Measure (EuclideanSpace ℝ (Fin n)))) {P : ℝ} (hP0 : 0 ≤ P)
    (hpoinc :
      ∀ g : EuclideanSpace ℝ (Fin n) → ℝ,
        LocallyLipschitz g →
          MemLp g 2 (μ : Measure (EuclideanSpace ℝ (Fin n))) →
            MemLp (gradient g) 2 (μ : Measure (EuclideanSpace ℝ (Fin n))) →
              variance g (μ : Measure (EuclideanSpace ℝ (Fin n))) ≤
                P * ∫ x, ‖gradient g x‖ ^ 2 ∂(μ : Measure (EuclideanSpace ℝ (Fin n))))
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf2 : MemLp f 2 (μ : Measure (EuclideanSpace ℝ (Fin n))))
    (hgf : MemLp (gradient f) 2 (μ : Measure (EuclideanSpace ℝ (Fin n))))
    (hdf :
      ∀ i,
        MemLp (fun x => fderiv ℝ f x (EuclideanSpace.single i 1)) 2
          (μ : Measure (EuclideanSpace ℝ (Fin n))))
    (hfin : ∀ i, Energy.Dual.dualNorm μ ((hdf i).toLp _) ≠ ⊤) {φ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hφs : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφ2 : MemLp φ 2 (μ : Measure (EuclideanSpace ℝ (Fin n))))
    (hgφ : MemLp (gradient φ) 2 (μ : Measure (EuclideanSpace ℝ (Fin n)))) :
    variance f (μ : Measure (EuclideanSpace ℝ (Fin n))) ≤
      (Real.sqrt
            (∑ i,
              ((Energy.Dual.dualNorm μ ((hdf i).toLp _)).toReal +
                  Real.sqrt P *
                    (eLpNorm (fun x => gradient φ x - gradient f x) 2
                        (μ : Measure (EuclideanSpace ℝ (Fin n)))).toReal) ^
                2) +
          ((eLpNorm (fun x => φ x - f x) 2 (μ : Measure (EuclideanSpace ℝ (Fin n)))).toReal +
            n *
                (eLpNorm (fun x => gradient φ x - gradient f x) 2
                    (μ : Measure (EuclideanSpace ℝ (Fin n)))).toReal *
              Real.sqrt (∫ x, ‖x‖ ^ 2 ∂(μ : Measure (EuclideanSpace ℝ (Fin n)))))) ^
        2 := by
  set δ : ℝ :=
    (eLpNorm (fun x => gradient φ x - gradient f x) 2
        (μ : Measure (EuclideanSpace ℝ (Fin n)))).toReal with
    hδ
  set ε : ℝ :=
    (eLpNorm (fun x => φ x - f x) 2 (μ : Measure (EuclideanSpace ℝ (Fin n)))).toReal with hε
  set M : ℝ := ∫ x, ‖x‖ ^ 2 ∂(μ : Measure (EuclideanSpace ℝ (Fin n))) with hM
  set N : Fin n → ℝ := fun i => (Energy.Dual.dualNorm μ ((hdf i).toLp _)).toReal with hN
  have hδ0 : 0 ≤ δ := ENNReal.toReal_nonneg
  have hε0 : 0 ≤ ε :=
    ENNReal.toReal_nonneg
  -- the partial derivatives of `f` are centered

  have hmeanf :
    ∀ i,
      ∫ x, fderiv ℝ f x (EuclideanSpace.single i 1) ∂(μ : Measure (EuclideanSpace ℝ (Fin n))) =
        0 :=
    fun i => by
    have h0 := Energy.Dual.integral_eq_zero_of_dualNorm_ne_top μ _ (hfin i)
    rw [← h0]
    exact
      (integral_congr_ae (hdf i).coeFn_toLp).symm
  -- the differences of partial derivatives

  set X : Fin n → EuclideanSpace ℝ (Fin n) → ℝ := fun i x =>
    fderiv ℝ φ x (EuclideanSpace.single i 1) - fderiv ℝ f x (EuclideanSpace.single i 1) with hX
  have hgd :
    MemLp (fun x => gradient φ x - gradient f x) 2 (μ : Measure (EuclideanSpace ℝ (Fin n))) :=
    hgφ.sub hgf
  have hXle : ∀ i x, |X i x| ≤ ‖gradient φ x - gradient f x‖ := fun i x => by
    simp only [hX, fderiv_single_eq_inner, ← inner_sub_left]
    have := abs_real_inner_le_norm (gradient φ x - gradient f x) (EuclideanSpace.single i 1)
    rwa [PiLp.norm_single, norm_one, mul_one] at this
  have hdφ :
    ∀ i,
      MemLp (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) 2
        (μ : Measure (EuclideanSpace ℝ (Fin n))) :=
    fun i => by
    have hc : Continuous (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) :=
      (hφs.continuous_fderiv (by simp)).clm_apply continuous_const
    obtain ⟨B, hB⟩ :=
      (hφc.fderiv ℝ).exists_bound_of_continuous (hφs.continuous_fderiv (by simp))
    exact
      MemLp.of_bound hc.aestronglyMeasurable B
        (Eventually.of_forall fun x => by
          refine ((fderiv ℝ φ x).le_opNorm _).trans ?_
          rw [PiLp.norm_single, norm_one, mul_one]; exact hB x)
  have hXmem : ∀ i, MemLp (X i) 2 (μ : Measure (EuclideanSpace ℝ (Fin n))) := fun i =>
    (hdφ i).sub (hdf i)
  have hgdsq :
    ∫ x, ‖gradient φ x - gradient f x‖ ^ 2 ∂(μ : Measure (EuclideanSpace ℝ (Fin n))) = δ ^ 2 :=
    L2.integral_norm_sq_eq_eLpNorm_sq hgd
  have hXsq : ∀ i, ∫ x, X i x ^ 2 ∂(μ : Measure (EuclideanSpace ℝ (Fin n))) ≤ δ ^ 2 := fun i => by
    rw [← hgdsq]
    refine
      integral_mono (hXmem i).integrable_sq
        ((memLp_two_iff_integrable_sq_norm hgd.aestronglyMeasurable).mp hgd)
        fun x => ?_
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hXle i x) 2
  set a : Fin n → ℝ := fun i =>
    ∫ x, fderiv ℝ φ x (EuclideanSpace.single i 1) ∂(μ : Measure (EuclideanSpace ℝ (Fin n))) with
    ha
  have haX : ∀ i, a i = ∫ x, X i x ∂(μ : Measure (EuclideanSpace ℝ (Fin n))) := fun i => by
    rw [hX, integral_sub ((hdφ i).integrable one_le_two) ((hdf i).integrable one_le_two),
      hmeanf i, sub_zero]
  have hab : ∀ i, |a i| ≤ δ := fun i => by
    have hv := variance_nonneg (X i) (μ : Measure (EuclideanSpace ℝ (Fin n)))
    rw [variance_eq_sub (hXmem i)] at hv
    simp only [Pi.pow_apply] at hv
    have h1 : a i ^ 2 ≤ δ ^ 2 := by rw [haX i]; linarith [hXsq i]
    exact
      abs_le_of_sq_le_sq' h1 hδ0 |> fun h =>
        abs_le.mpr
          h
  -- the corrected smooth function

  set w : EuclideanSpace ℝ (Fin n) := ∑ i, a i • EuclideanSpace.single i (1 : ℝ) with hw
  have hwi : ∀ i, ⟪w, EuclideanSpace.single i (1 : ℝ)⟫ = a i := fun i => by
    rw [hw, (EuclideanSpace.orthonormal_single (𝕜 := ℝ) (ι := Fin n)).inner_left_fintype]
    rfl
  have hwn : ‖w‖ ≤ n * δ := by
    calc
      ‖w‖ ≤ ∑ i, ‖a i • EuclideanSpace.single i (1 : ℝ)‖ := norm_sum_le _ _
      _ = ∑ i, |a i| := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [norm_smul, PiLp.norm_single, norm_one, mul_one, Real.norm_eq_abs]
      _ ≤ ∑ _i : Fin n, δ := Finset.sum_le_sum fun i _ => hab i
      _ = n * δ := by simp
  set ℓ : EuclideanSpace ℝ (Fin n) → ℝ := fun x => ⟪w, x⟫ with hℓ
  set F : EuclideanSpace ℝ (Fin n) → ℝ := fun x => φ x - ℓ x with hF
  have hFd : ∀ x, fderiv ℝ F x = fderiv ℝ φ x - innerSL ℝ w := fun x =>
    (((hφs.differentiable (by simp)) x).hasFDerivAt.sub (innerSL ℝ w).hasFDerivAt).fderiv
  have hF1 : ContDiff ℝ 1 F := (hφs.of_le (by simp)).sub (innerSL ℝ w).contDiff
  have hpart :
    ∀ i x,
      fderiv ℝ F x (EuclideanSpace.single i 1) =
        fderiv ℝ φ x (EuclideanSpace.single i 1) - a i :=
    fun i x => by rw [hFd, sub_apply, innerSL_apply_apply, hwi]
  obtain ⟨Bφ, hBφ⟩ :=
    (hφc.fderiv ℝ).exists_bound_of_continuous (hφs.continuous_fderiv (by simp))
  have hLF : ∀ x, ‖fderiv ℝ F x‖ ≤ Bφ + ‖w‖ := fun x => by
    rw [hFd]
    refine (norm_sub_le _ _).trans (add_le_add (hBφ x) ?_)
    rw [innerSL_apply_norm]
  have hdF :
    ∀ i,
      MemLp (fun x => fderiv ℝ F x (EuclideanSpace.single i 1)) 2
        (μ : Measure (EuclideanSpace ℝ (Fin n))) :=
    fun i => by
    simp_rw [hpart i]
    exact
      (hdφ i).sub
        (memLp_const _)
  -- the dual norms of the corrected partial derivatives

  have hdual :
    ∀ i, Energy.Dual.dualNorm μ ((hdF i).toLp _) ≤ ENNReal.ofReal (N i + Real.sqrt P * δ) :=
    fun i => by
    set Q := (hdF i).toLp (fun x => fderiv ℝ F x (EuclideanSpace.single i 1))
    set q := (hdf i).toLp (fun x => fderiv ℝ f x (EuclideanSpace.single i 1))
    have hD :
      MemLp
        (fun x =>
          fderiv ℝ F x (EuclideanSpace.single i 1) - fderiv ℝ f x (EuclideanSpace.single i 1))
        2 (μ : Measure (EuclideanSpace ℝ (Fin n))) :=
      (hdF i).sub (hdf i)
    have hQq : Q - q = hD.toLp _ := (MemLp.toLp_sub (hdF i) (hdf i)).symm
    have hDeq :
      (fun x =>
          fderiv ℝ F x (EuclideanSpace.single i 1) - fderiv ℝ f x (EuclideanSpace.single i 1)) =
        fun x => X i x - a i := by
      funext x; rw [hpart i x]; simp only [hX]; ring
    have hmeanD : ∫ x, (Q - q) x ∂(μ : Measure (EuclideanSpace ℝ (Fin n))) = 0 := by
      rw [hQq, integral_congr_ae hD.coeFn_toLp, hDeq,
        integral_sub ((hXmem i).integrable one_le_two) (integrable_const _), integral_const,
        probReal_univ, one_smul, ← haX i, sub_self]
    have hnorm : ‖Q - q‖ ≤ δ := by
      have h1 :
        ‖Q - q‖ ^ 2 = ∫ x, (X i x - a i) ^ 2 ∂(μ : Measure (EuclideanSpace ℝ (Fin n))) := by
        rw [hQq, Lp.norm_toLp, ← L2.integral_norm_sq_eq_eLpNorm_sq hD]
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        simp only [Real.norm_eq_abs, sq_abs]
        rw [show
            fderiv ℝ F x (EuclideanSpace.single i 1) -
                fderiv ℝ f x (EuclideanSpace.single i 1) =
              X i x - a i
            from congrFun hDeq x]
      have h2 : ∫ x, (X i x - a i) ^ 2 ∂(μ : Measure (EuclideanSpace ℝ (Fin n))) ≤ δ ^ 2 := by
        have hv :=
          variance_le_expectation_sq (μ := (μ : Measure (EuclideanSpace ℝ (Fin n))))
            (hXmem i).aestronglyMeasurable
        rw [variance_eq_integral (hXmem i).aestronglyMeasurable.aemeasurable, ← haX i] at hv
        simp only [Pi.pow_apply] at hv
        exact hv.trans (hXsq i)
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) hδ0 two_ne_zero).mp (h1 ▸ h2)
    have hsplit : Q = q + (Q - q) := (add_sub_cancel q Q).symm
    calc
      Energy.Dual.dualNorm μ Q = Energy.Dual.dualNorm μ (q + (Q - q)) := by rw [← hsplit]
      _ ≤ Energy.Dual.dualNorm μ q + Energy.Dual.dualNorm μ (Q - q) :=
        Energy.Dual.dualNorm_add_le μ q (Q - q)
      _ ≤ ENNReal.ofReal (N i) + ENNReal.ofReal (Real.sqrt P * ‖Q - q‖) := by
        gcongr
        · exact (ENNReal.ofReal_toReal (hfin i)).symm.le
        · exact Energy.Dual.dualNorm_le_of_variance_le μ (Q - q) hmeanD hP0 hpoinc
      _ ≤ ENNReal.ofReal (N i) + ENNReal.ofReal (Real.sqrt P * δ) := by gcongr
      _ = ENNReal.ofReal (N i + Real.sqrt P * δ) :=
        (ENNReal.ofReal_add ENNReal.toReal_nonneg (by positivity)).symm
  have hfinF : ∀ i, Energy.Dual.dualNorm μ ((hdF i).toLp _) ≠ ⊤ := fun i =>
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hdual i)
  have hVF :=
    variance_le_sum_toReal_dualNorm_sq_of_bounded_fderiv hKLS hμ hfull hF1 hLF hdF hfinF
  have hVF' :
    variance F (μ : Measure (EuclideanSpace ℝ (Fin n))) ≤ ∑ i, (N i + Real.sqrt P * δ) ^ 2 := by
    refine hVF.trans (Finset.sum_le_sum fun i _ => ?_)
    exact
      pow_le_pow_left₀ ENNReal.toReal_nonneg
        (ENNReal.toReal_le_of_le_ofReal (by positivity) (hdual i))
        2
  -- assemble `f = F + (f - φ) + ℓ`

  have hFcont : Continuous F := hF1.continuous
  have hF2 : MemLp F 2 (μ : Measure (EuclideanSpace ℝ (Fin n))) := by
    have hℓ2 : MemLp ℓ 2 (μ : Measure (EuclideanSpace ℝ (Fin n))) := by
      have hh : MemLp (fun x => ⟪id x, w⟫) 2 (μ : Measure (EuclideanSpace ℝ (Fin n))) :=
        hμ2.inner_const w
      simpa [hℓ, real_inner_comm] using hh
    exact hφ2.sub hℓ2
  have hℓ2 : MemLp ℓ 2 (μ : Measure (EuclideanSpace ℝ (Fin n))) := by
    have hh : MemLp (fun x => ⟪id x, w⟫) 2 (μ : Measure (EuclideanSpace ℝ (Fin n))) :=
      hμ2.inner_const w
    simpa [hℓ, real_inner_comm] using hh
  have hfφ : MemLp (fun x => f x - φ x) 2 (μ : Measure (EuclideanSpace ℝ (Fin n))) :=
    hf2.sub hφ2
  have hG2 : MemLp (fun x => (f x - φ x) + ℓ x) 2 (μ : Measure (EuclideanSpace ℝ (Fin n))) :=
    hfφ.add hℓ2
  have hfeq : f = fun x => F x + ((f x - φ x) + ℓ x) := by funext x; simp only [hF]; ring
  have h1 := variance_add_le μ hF2 hG2
  rw [← hfeq] at h1
  have h2 := variance_add_le μ hfφ hℓ2
  have hVfφ :
    Real.sqrt (variance (fun x => f x - φ x) (μ : Measure (EuclideanSpace ℝ (Fin n)))) ≤ ε := by
    have hv :=
      variance_le_expectation_sq (μ := (μ : Measure (EuclideanSpace ℝ (Fin n))))
        hfφ.aestronglyMeasurable
    simp only [Pi.pow_apply] at hv
    have hsq : ∫ x, (f x - φ x) ^ 2 ∂(μ : Measure (EuclideanSpace ℝ (Fin n))) = ε ^ 2 := by
      have hd : MemLp (fun x => φ x - f x) 2 (μ : Measure (EuclideanSpace ℝ (Fin n))) :=
        hφ2.sub hf2
      rw [hε, ← L2.integral_norm_sq_eq_eLpNorm_sq hd]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [Real.norm_eq_abs, sq_abs]; ring
    calc
      Real.sqrt (variance (fun x => f x - φ x) (μ : Measure (EuclideanSpace ℝ (Fin n)))) ≤
          Real.sqrt (ε ^ 2) :=
        Real.sqrt_le_sqrt (hv.trans hsq.le)
      _ = ε := Real.sqrt_sq hε0
  have hVℓ :
    Real.sqrt (variance ℓ (μ : Measure (EuclideanSpace ℝ (Fin n)))) ≤ n * δ * Real.sqrt M := by
    have hv :=
      variance_le_expectation_sq (μ := (μ : Measure (EuclideanSpace ℝ (Fin n))))
        hℓ2.aestronglyMeasurable
    simp only [Pi.pow_apply] at hv
    have hSint :
      Integrable (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ ^ 2)
        (μ : Measure (EuclideanSpace ℝ (Fin n))) :=
      (memLp_two_iff_integrable_sq_norm hμ2.aestronglyMeasurable).mp hμ2
    have hle : ∫ x, ℓ x ^ 2 ∂(μ : Measure (EuclideanSpace ℝ (Fin n))) ≤ ‖w‖ ^ 2 * M := by
      rw [hM, ← integral_const_mul]
      refine integral_mono hℓ2.integrable_sq (hSint.const_mul _) fun x => ?_
      have := abs_real_inner_le_norm w x
      calc
        ℓ x ^ 2 = |⟪w, x⟫| ^ 2 := (sq_abs _).symm
        _ ≤ (‖w‖ * ‖x‖) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
        _ = ‖w‖ ^ 2 * ‖x‖ ^ 2 := by ring
    calc
      Real.sqrt (variance ℓ (μ : Measure (EuclideanSpace ℝ (Fin n)))) ≤
          Real.sqrt (‖w‖ ^ 2 * M) :=
        Real.sqrt_le_sqrt (hv.trans hle)
      _ = ‖w‖ * Real.sqrt M := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]
      _ ≤ n * δ * Real.sqrt M := mul_le_mul_of_nonneg_right hwn (Real.sqrt_nonneg _)
  have hVG :
    Real.sqrt (variance (fun x => (f x - φ x) + ℓ x) (μ : Measure (EuclideanSpace ℝ (Fin n)))) ≤
      ε + n * δ * Real.sqrt M := by
    calc
      Real.sqrt
            (variance (fun x => (f x - φ x) + ℓ x) (μ : Measure (EuclideanSpace ℝ (Fin n)))) ≤
          Real.sqrt
            ((Real.sqrt
                  (variance (fun x => f x - φ x) (μ : Measure (EuclideanSpace ℝ (Fin n)))) +
                Real.sqrt (variance ℓ (μ : Measure (EuclideanSpace ℝ (Fin n))))) ^
              2) :=
        Real.sqrt_le_sqrt h2
      _ =
          Real.sqrt (variance (fun x => f x - φ x) (μ : Measure (EuclideanSpace ℝ (Fin n)))) +
            Real.sqrt (variance ℓ (μ : Measure (EuclideanSpace ℝ (Fin n)))) :=
        Real.sqrt_sq (by positivity)
      _ ≤ ε + n * δ * Real.sqrt M := add_le_add hVfφ hVℓ
  have hVF'' :
    Real.sqrt (variance F (μ : Measure (EuclideanSpace ℝ (Fin n)))) ≤
      Real.sqrt (∑ i, (N i + Real.sqrt P * δ) ^ 2) :=
    Real.sqrt_le_sqrt hVF'
  exact h1.trans (pow_le_pow_left₀ (by positivity) (add_le_add hVF'' hVG) 2)

end SmoothClass

section Main

variable {n : ℕ}

/-- **The `H⁻¹` variance inequality for log-concave laws, given the KLS conjecture** (Letwin
arXiv:2607.24164v1, Proposition 2.8, quoting Barthe–Klartag, Proposition 10; display (2.20)).
Let `μ` be a log-concave probability law on `ℝⁿ` of full affine dimension
(`affineSupport μ = ⊤`), and let `f` be locally Lipschitz with `f ∈ L²(μ)` and every Fréchet
partial derivative `∂ᵢ f = Df(·) eᵢ ∈ L²(μ)`. Then
`Var_μ f ≤ Σᵢ ‖∂ᵢ f‖²_{H⁻¹(μ)}`
with the `H⁻¹` norm (2.19) of `Energy.Dual.dualNorm` (supremum over locally Lipschitz
unit-energy tests). The right side may be `⊤`; when it is finite each `∂ᵢ f` is centered, which is
the source's premise `E ∂ᵢ f = 0`. The hypothesis `hKLS` only supplies uniform Poincaré
constants along the approximation; see `KLS/Letwin/HminusOne.lean` for the unconditional form.
For laws of lower affine dimension the ambient-gradient statement is ill-posed (Gaussian on
`{xₙ = 0}`, `f = x₁ + |xₙ|`). -/
theorem variance_le_sum_dualNorm_sq_of_conjecture (hKLS : KLS.Conjecture)
    {μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))} (hμ : LogConcave μ)
    (hfull : Probability.affineSupport μ = ⊤) {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : LocallyLipschitz f) (hf2 : MemLp f 2 (μ : Measure (EuclideanSpace ℝ (Fin n))))
    (hdf : ∀ i, MemLp (fun x => fderiv ℝ f x (EuclideanSpace.single i 1)) 2
      (μ : Measure (EuclideanSpace ℝ (Fin n)))) :
    ENNReal.ofReal (variance f (μ : Measure (EuclideanSpace ℝ (Fin n)))) ≤
      ∑ i, Energy.Dual.dualNorm μ ((hdf i).toLp _) ^ 2 := by
  by_cases hfin : ∀ i, Energy.Dual.dualNorm μ ((hdf i).toLp _) ≠ ⊤
  swap
  · push Not at hfin
    obtain ⟨i, hi⟩ := hfin
    have htop : ∑ i, Energy.Dual.dualNorm μ ((hdf i).toLp _) ^ 2 = ⊤ :=
      ENNReal.sum_eq_top.mpr ⟨i, Finset.mem_univ _, by rw [hi]; simp⟩
    rw [htop]
    exact le_top
  set N : Fin n → ℝ := fun i => (Energy.Dual.dualNorm μ ((hdf i).toLp _)).toReal with hN
  suffices hreal : variance f (μ : Measure (EuclideanSpace ℝ (Fin n))) ≤ ∑ i, N i ^ 2 by
    calc ENNReal.ofReal (variance f (μ : Measure (EuclideanSpace ℝ (Fin n))))
        ≤ ENNReal.ofReal (∑ i, N i ^ 2) := ENNReal.ofReal_le_ofReal hreal
      _ = ∑ i, ENNReal.ofReal (N i ^ 2) :=
          ENNReal.ofReal_sum_of_nonneg fun i _ => sq_nonneg _
      _ = ∑ i, Energy.Dual.dualNorm μ ((hdf i).toLp _) ^ 2 :=
          Finset.sum_congr rfl fun i _ => by
            rw [ENNReal.ofReal_pow ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (hfin i)]
  obtain ⟨hac, hμ2⟩ := absolutelyContinuous_and_memLp_two_of_affineSupport_eq_top μ hμ hfull
  obtain ⟨K, -, hKP⟩ := exists_smoothTest_holds_of_conjecture hKLS
  set M : ℝ := ∫ x, ‖x‖ ^ 2 ∂(μ : Measure (EuclideanSpace ℝ (Fin n))) with hM
  have hPμ := hKP μ hμ hμ2 M le_rfl
  set P : ℝ := K * M + 1 with hP
  have hP0 : 0 ≤ P := hPμ.constant_nonneg
  have hpoinc : ∀ g : EuclideanSpace ℝ (Fin n) → ℝ, LocallyLipschitz g →
      MemLp g 2 (μ : Measure (EuclideanSpace ℝ (Fin n))) →
      MemLp (gradient g) 2 (μ : Measure (EuclideanSpace ℝ (Fin n))) →
      variance g (μ : Measure (EuclideanSpace ℝ (Fin n))) ≤
        P * ∫ x, ‖gradient g x‖ ^ 2 ∂(μ : Measure (EuclideanSpace ℝ (Fin n))) :=
    fun g hg h2 hgr => variance_le_of_smoothTest_holds volume hac hPμ hg h2 hgr
  have hgf : MemLp (gradient f) 2 (μ : Measure (EuclideanSpace ℝ (Fin n))) := by
    refine (memLp_two_iff_integrable_sq_norm
      (Energy.Euclidean.LipschitzApproximation.aestronglyMeasurable_gradient f _)).mpr ?_
    have hfun : (fun x => ‖gradient f x‖ ^ 2) =
        fun x => ∑ i, (fderiv ℝ f x (EuclideanSpace.single i 1)) ^ 2 :=
      funext (norm_gradient_sq_eq_sum f)
    rw [hfun]
    exact integrable_finsetSum _ fun i _ => (hdf i).integrable_sq
  obtain ⟨φ, hφ, hφconv, hgconv⟩ :=
    Energy.Euclidean.LipschitzApproximation.exists_smooth_weighted_L2 μ volume hac
      (ContinuousLinearMap.id ℝ _) f hf hf2 (by simpa using hgf)
  set δ : ℕ → ℝ := fun j => (eLpNorm (fun x => gradient (φ j) x - gradient f x) 2
    (μ : Measure (EuclideanSpace ℝ (Fin n)))).toReal with hδdef
  set ε : ℕ → ℝ := fun j => (eLpNorm (fun x => φ j x - f x) 2
    (μ : Measure (EuclideanSpace ℝ (Fin n)))).toReal with hεdef
  have hδ : Tendsto δ atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hgconv
    simpa [hδdef, Function.comp_def] using this
  have hε : Tendsto ε atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hφconv
    simpa [hεdef, Function.comp_def] using this
  have hbound : ∀ j, variance f (μ : Measure (EuclideanSpace ℝ (Fin n))) ≤
      (Real.sqrt (∑ i, (N i + Real.sqrt P * δ j) ^ 2) + (ε j + n * δ j * Real.sqrt M)) ^ 2 :=
    fun j => variance_le_of_smooth_approx hKLS hμ hfull hμ2 hP0 hpoinc hf2 hgf hdf hfin
      (hφ j).1 (hφ j).2.1 (hφ j).2.2.1 (by simpa using (hφ j).2.2.2)
  have h1 : Tendsto (fun j => ∑ i, (N i + Real.sqrt P * δ j) ^ 2) atTop
      (𝓝 (∑ i, (N i + Real.sqrt P * 0) ^ 2)) :=
    tendsto_finsetSum _ fun i _ => (tendsto_const_nhds.add (hδ.const_mul _)).pow 2
  have h2 := ((h1.sqrt).add (hε.add ((hδ.const_mul (n : ℝ)).mul_const (Real.sqrt M)))).pow 2
  have hlim : (Real.sqrt (∑ i, (N i + Real.sqrt P * 0) ^ 2) + (0 + n * 0 * Real.sqrt M)) ^ 2 =
      ∑ i, N i ^ 2 := by
    simp only [mul_zero, add_zero, zero_mul]
    exact Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)
  rw [hlim] at h2
  exact ge_of_tendsto' h2 hbound

end Main

end FunctionalInequalities.KLS.LogConcave
