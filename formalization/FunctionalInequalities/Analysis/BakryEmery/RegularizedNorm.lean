import FunctionalInequalities.Analysis.BakryEmery.WeakGamma

/-!
# The regularized norm `√(ε + ‖a‖²) - √ε` of a square-integrable field

For `ε > 0` and a real inner product space `H`, `regularizedNorm ε a = √(ε + ‖a‖²) - √ε` is a
smooth, `1`-Lipschitz approximation of `‖a‖` from below, vanishing at `0`, and
`regularizedUnit ε a = a / √(ε + ‖a‖²)` is its gradient. This module proves the pointwise facts
and their tested `L²` consequences needed for Bakry's `L¹` self-improvement:

* pointwise: `0 ≤ regularizedNorm ε a ≤ ‖a‖`, the Lipschitz bound, `‖regularizedUnit ε a‖ ≤ 1`, the
  Lipschitz bound `2/√ε` of `regularizedUnit`, the Taylor bound
  `|N(b) - N(a) - ⟪regularizedUnit ε a, b - a⟫| ≤ ‖b - a‖²/√ε`, and `N_ε(a) → ‖a‖` as `ε → 0⁺`;
* tested: joint convergence of `∫ q · N(u)` and `∫ q ⟪regularizedUnit ε u, w⟫` under `L²`
  convergence, and the product rule for `s ↦ ∫ q s · N(u s)`.

Nothing here refers to a gradient or semigroup.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped RealInnerProductSpace

namespace FunctionalInequalities.Analysis.BakryEmery

variable {H : Type*} [NormedAddCommGroup H]

/-- The regularized norm `√(ε + ‖a‖²) - √ε`. -/
def regularizedNorm (ε : ℝ) (a : H) : ℝ := √(ε + ‖a‖ ^ 2) - √ε

theorem regularizedNorm_def (ε : ℝ) (a : H) : regularizedNorm ε a = √(ε + ‖a‖ ^ 2) - √ε := rfl

section Pointwise

variable {ε : ℝ}

private theorem sqrt_pos_add (hε : 0 < ε) (a : H) : 0 < √(ε + ‖a‖ ^ 2) :=
  Real.sqrt_pos.mpr (by positivity)

private theorem sq_sqrt_add (hε : 0 < ε) (a : H) : √(ε + ‖a‖ ^ 2) ^ 2 = ε + ‖a‖ ^ 2 :=
  Real.sq_sqrt (by positivity)

private theorem norm_le_sqrt_add (hε : 0 < ε) (a : H) : ‖a‖ ≤ √(ε + ‖a‖ ^ 2) :=
  Real.le_sqrt_of_sq_le (by linarith)

private theorem sqrt_le_sqrt_add (a : H) : √ε ≤ √(ε + ‖a‖ ^ 2) :=
  Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ‖a‖])

theorem regularizedNorm_nonneg (ε : ℝ) (a : H) : 0 ≤ regularizedNorm ε a := by
  rw [regularizedNorm_def]; linarith [sqrt_le_sqrt_add (ε := ε) a]

theorem regularizedNorm_le_norm (hε : 0 < ε) (a : H) : regularizedNorm ε a ≤ ‖a‖ := by
  rw [regularizedNorm_def, sub_le_iff_le_add]
  have hs := Real.sqrt_nonneg ε
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [Real.sq_sqrt hε.le, norm_nonneg a]

theorem regularizedNorm_zero (ε : ℝ) : regularizedNorm ε (0 : H) = 0 := by
  simp [regularizedNorm_def]

/-- `√(ε + ‖·‖²)` is `1`-Lipschitz. -/
theorem abs_sqrt_add_sq_sub_le (hε : 0 < ε) (a b : H) :
    |√(ε + ‖a‖ ^ 2) - √(ε + ‖b‖ ^ 2)| ≤ ‖a - b‖ := by
  have key : ∀ a b : H, √(ε + ‖a‖ ^ 2) ≤ √(ε + ‖b‖ ^ 2) + ‖a - b‖ := by
    intro a b
    have hb := norm_le_sqrt_add hε b
    have htri : ‖a‖ ≤ ‖b‖ + ‖a - b‖ := by
      have := norm_add_le b (a - b); simpa using this
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [sq_sqrt_add hε b, norm_nonneg a, norm_nonneg b, norm_nonneg (a - b)]
  rw [abs_sub_le_iff]
  constructor
  · linarith [key a b]
  · have := key b a; rw [norm_sub_rev] at this; linarith

theorem abs_regularizedNorm_sub_le (hε : 0 < ε) (a b : H) :
    |regularizedNorm ε a - regularizedNorm ε b| ≤ ‖a - b‖ := by
  simp only [regularizedNorm_def, sub_sub_sub_cancel_right]
  exact abs_sqrt_add_sq_sub_le hε a b

/-- `regularizedNorm ε a → ‖a‖` as `ε → 0⁺`. -/
theorem tendsto_regularizedNorm (a : H) :
    Tendsto (fun ε => regularizedNorm ε a) (𝓝[>] 0) (𝓝 ‖a‖) := by
  have hc : Continuous fun ε : ℝ => √(ε + ‖a‖ ^ 2) - √ε :=
    (Real.continuous_sqrt.comp (continuous_id.add continuous_const)).sub Real.continuous_sqrt
  have h := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  simpa [regularizedNorm_def, Real.sqrt_sq (norm_nonneg a)] using h

end Pointwise

section Inner

variable [InnerProductSpace ℝ H]

/-- The gradient of the regularized norm, `a / √(ε + ‖a‖²)`. -/
def regularizedUnit (ε : ℝ) (a : H) : H := (√(ε + ‖a‖ ^ 2))⁻¹ • a

theorem regularizedUnit_def (ε : ℝ) (a : H) :
    regularizedUnit ε a = (√(ε + ‖a‖ ^ 2))⁻¹ • a := rfl

variable {ε : ℝ}

theorem norm_regularizedUnit_le_one (hε : 0 < ε) (a : H) : ‖regularizedUnit ε a‖ ≤ 1 := by
  rw [regularizedUnit_def, norm_smul, norm_inv, Real.norm_of_nonneg (Real.sqrt_nonneg _),
    inv_mul_le_one₀ (sqrt_pos_add hε a)]
  exact norm_le_sqrt_add hε a

/-- `regularizedUnit ε` is `2/√ε`-Lipschitz. -/
theorem norm_regularizedUnit_sub_le (hε : 0 < ε) (a b : H) :
    ‖regularizedUnit ε a - regularizedUnit ε b‖ ≤ 2 / √ε * ‖a - b‖ := by
  set α := √(ε + ‖a‖ ^ 2)
  set β := √(ε + ‖b‖ ^ 2)
  have hα : 0 < α := sqrt_pos_add hε a
  have hβ : 0 < β := sqrt_pos_add hε b
  have hse : 0 < √ε := Real.sqrt_pos.mpr hε
  have hαε : √ε ≤ α := sqrt_le_sqrt_add (ε := ε) a
  have hbβ : ‖b‖ ≤ β := norm_le_sqrt_add hε b
  have hαβ : |α - β| ≤ ‖a - b‖ := abs_sqrt_add_sq_sub_le hε a b
  have hsplit : regularizedUnit ε a - regularizedUnit ε b =
      α⁻¹ • (a - b) + (α⁻¹ - β⁻¹) • b := by
    simp only [regularizedUnit_def, smul_sub, sub_smul]; abel
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hα.le), Real.norm_eq_abs]
  have h1 : α⁻¹ * ‖a - b‖ ≤ ‖a - b‖ / √ε := by
    rw [inv_mul_eq_div]; exact div_le_div_of_nonneg_left (norm_nonneg _) hse hαε
  have h2 : |α⁻¹ - β⁻¹| * ‖b‖ ≤ ‖a - b‖ / √ε := by
    have e : α⁻¹ - β⁻¹ = (β - α) / (α * β) := by field_simp
    rw [e, abs_div, abs_of_pos (mul_pos hα hβ), abs_sub_comm]
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (mul_pos hα hβ) hse]
    calc |α - β| * ‖b‖ * √ε ≤ ‖a - b‖ * β * α :=
          mul_le_mul (mul_le_mul hαβ hbβ (norm_nonneg _) (norm_nonneg _)) hαε hse.le
            (by positivity)
      _ = ‖a - b‖ * (α * β) := by ring
  calc α⁻¹ * ‖a - b‖ + |α⁻¹ - β⁻¹| * ‖b‖ ≤ ‖a - b‖ / √ε + ‖a - b‖ / √ε := add_le_add h1 h2
    _ = 2 / √ε * ‖a - b‖ := by ring

/-- **Taylor bound for the regularized norm**:
`|N(b) - N(a) - ⟪regularizedUnit ε a, b - a⟫| ≤ ‖b - a‖² / √ε`. -/
theorem abs_regularizedNorm_sub_sub_inner_le (hε : 0 < ε) (a b : H) :
    |regularizedNorm ε b - regularizedNorm ε a - ⟪regularizedUnit ε a, b - a⟫| ≤
      ‖b - a‖ ^ 2 / √ε := by
  set α := √(ε + ‖a‖ ^ 2) with hαdef
  set β := √(ε + ‖b‖ ^ 2) with hβdef
  have hα : 0 < α := sqrt_pos_add hε a
  have hβ : 0 < β := sqrt_pos_add hε b
  have hse : 0 < √ε := Real.sqrt_pos.mpr hε
  have hαε : √ε ≤ α := sqrt_le_sqrt_add (ε := ε) a
  have hβε : √ε ≤ β := sqrt_le_sqrt_add (ε := ε) b
  have hα2 : α ^ 2 = ε + ‖a‖ ^ 2 := sq_sqrt_add hε a
  have hβ2 : β ^ 2 = ε + ‖b‖ ^ 2 := sq_sqrt_add hε b
  set d := b - a with hd
  set p := ⟪a, d⟫ with hp
  have hb2 : ‖b‖ ^ 2 = ‖a‖ ^ 2 + 2 * p + ‖d‖ ^ 2 := by
    have : b = a + d := by rw [hd]; abel
    rw [this, norm_add_sq_real]
  have hpa : |p| ≤ α * ‖d‖ :=
    (abs_real_inner_le_norm a d).trans (mul_le_mul_of_nonneg_right (norm_le_sqrt_add hε a)
      (norm_nonneg _))
  have hαβ : |α - β| ≤ ‖d‖ := by
    have := abs_sqrt_add_sq_sub_le hε a b; rwa [norm_sub_rev] at this
  have hinner : ⟪regularizedUnit ε a, d⟫ = p / α := by
    rw [regularizedUnit_def, real_inner_smul_left, hp, inv_mul_eq_div]
  have hE : regularizedNorm ε b - regularizedNorm ε a - ⟪regularizedUnit ε a, d⟫ =
      (α * ‖d‖ ^ 2 + p * (α - β)) / (α * (α + β)) := by
    rw [hinner, regularizedNorm_def, regularizedNorm_def, ← hαdef, ← hβdef]
    have hβα : β - α = (2 * p + ‖d‖ ^ 2) / (α + β) := by
      rw [eq_div_iff (by positivity)]
      nlinarith [hα2, hβ2, hb2]
    have : √(ε + ‖b‖ ^ 2) - √ε - (√(ε + ‖a‖ ^ 2) - √ε) - p / α = (β - α) - p / α := by
      rw [← hαdef, ← hβdef]; ring
    rw [this, hβα]
    field_simp
    ring
  rw [hE, abs_div, abs_of_pos (mul_pos hα (add_pos hα hβ))]
  rw [div_le_div_iff₀ (mul_pos hα (add_pos hα hβ)) hse]
  have hnum : |α * ‖d‖ ^ 2 + p * (α - β)| ≤ 2 * α * ‖d‖ ^ 2 := by
    calc |α * ‖d‖ ^ 2 + p * (α - β)| ≤ |α * ‖d‖ ^ 2| + |p * (α - β)| := abs_add_le _ _
      _ ≤ α * ‖d‖ ^ 2 + α * ‖d‖ * ‖d‖ := by
          rw [abs_of_nonneg (by positivity), abs_mul]
          gcongr
      _ = 2 * α * ‖d‖ ^ 2 := by ring
  calc |α * ‖d‖ ^ 2 + p * (α - β)| * √ε ≤ 2 * α * ‖d‖ ^ 2 * √ε := by gcongr
    _ = α * ‖d‖ ^ 2 * (2 * √ε) := by ring
    _ ≤ α * ‖d‖ ^ 2 * (α + β) := by gcongr; linarith
    _ = ‖d‖ ^ 2 * (α * (α + β)) := by ring

end Inner

section Continuity

theorem continuous_regularizedNorm (ε : ℝ) : Continuous (regularizedNorm (H := H) ε) :=
  (Real.continuous_sqrt.comp (continuous_const.add (continuous_norm.pow 2))).sub
    continuous_const

variable [InnerProductSpace ℝ H]

theorem continuous_regularizedUnit {ε : ℝ} (hε : 0 < ε) :
    Continuous (regularizedUnit (H := H) ε) := by
  refine (Continuous.inv₀ (Real.continuous_sqrt.comp (continuous_const.add
    (continuous_norm.pow 2))) fun a => ?_).smul continuous_id
  exact (Real.sqrt_pos.mpr (add_pos_of_pos_of_nonneg hε (sq_nonneg ‖a‖))).ne'

end Continuity

section Integral

variable [InnerProductSpace ℝ H] {α : Type*} [MeasurableSpace α] {μ : Measure α}
  [IsFiniteMeasure μ] {ε : ℝ}

/-- The constant `L²` class used to compare `L¹` and `L²` norms on a finite measure. -/
private def oneL2 (μ : Measure α) [IsFiniteMeasure μ] : Lp ℝ 2 μ :=
  (memLp_const (1 : ℝ)).toLp fun _ => (1 : ℝ)

omit [InnerProductSpace ℝ H] in
private theorem integral_norm_le (g : Lp H 2 μ) :
    ∫ x, ‖g x‖ ∂μ ≤ ‖g‖ * ‖oneL2 μ‖ := by
  refine le_trans (le_of_eq ?_) (WeakGamma.integral_norm_mul_norm_le g (oneL2 μ))
  refine integral_congr_ae ?_
  filter_upwards [(memLp_const (1 : ℝ) (μ := μ) (p := 2)).coeFn_toLp] with x hx
  show ‖g x‖ = ‖g x‖ * ‖((memLp_const (1 : ℝ)).toLp fun _ => (1 : ℝ) : Lp ℝ 2 μ) x‖
  rw [hx]; simp

omit [InnerProductSpace ℝ H] [IsFiniteMeasure μ] in
theorem aestronglyMeasurable_regularizedNorm (u : Lp H 2 μ) :
    AEStronglyMeasurable (fun x => regularizedNorm ε (u x)) μ :=
  (continuous_regularizedNorm ε).comp_aestronglyMeasurable (Lp.aestronglyMeasurable u)

section RegularizedNormIntegrability

omit [InnerProductSpace ℝ H]
/-- `regularizedNorm ε (u x)` is dominated by `‖u x‖`, hence integrable. -/
theorem integrable_regularizedNorm (hε : 0 < ε) (u : Lp H 2 μ) :
    Integrable (fun x => regularizedNorm ε (u x)) μ :=
  ((Lp.memLp u).integrable one_le_two).norm.mono' (aestronglyMeasurable_regularizedNorm u)
    (Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (regularizedNorm_nonneg ε _)]
      exact regularizedNorm_le_norm hε _)

/-- Bounded multipliers test `regularizedNorm ε (u x)`. -/
theorem integrable_mul_regularizedNorm (hε : 0 < ε) {q : α → ℝ}
    (hq : AEStronglyMeasurable q μ) {D : ℝ} (hD : ∀ᵐ x ∂μ, |q x| ≤ D) (u : Lp H 2 μ) :
    Integrable (fun x => q x * regularizedNorm ε (u x)) μ :=
  (integrable_regularizedNorm hε u).bdd_mul hq
    (by filter_upwards [hD] with x hx; rwa [Real.norm_eq_abs])

end RegularizedNormIntegrability

omit [IsFiniteMeasure μ] in
theorem aestronglyMeasurable_inner_regularizedUnit (hε : 0 < ε) (u w : Lp H 2 μ) :
    AEStronglyMeasurable (fun x => ⟪regularizedUnit ε (u x), w x⟫) μ :=
  (((continuous_regularizedUnit hε).comp_aestronglyMeasurable
    (Lp.aestronglyMeasurable u))).inner (Lp.aestronglyMeasurable w)

theorem integrable_mul_inner_regularizedUnit (hε : 0 < ε) {q : α → ℝ}
    (hq : AEStronglyMeasurable q μ) {D : ℝ} (hD : ∀ᵐ x ∂μ, |q x| ≤ D) (u w : Lp H 2 μ) :
    Integrable (fun x => q x * ⟪regularizedUnit ε (u x), w x⟫) μ := by
  have hw : Integrable (fun x => ‖w x‖) μ := ((Lp.memLp w).integrable one_le_two).norm
  have hI : Integrable (fun x => ⟪regularizedUnit ε (u x), w x⟫) μ :=
    hw.mono' (aestronglyMeasurable_inner_regularizedUnit hε u w) (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]
      exact (abs_real_inner_le_norm _ _).trans
        (by nlinarith [norm_regularizedUnit_le_one hε (u x), norm_nonneg (w x),
          norm_nonneg (regularizedUnit ε (u x))]))
  exact hI.bdd_mul hq (by filter_upwards [hD] with x hx; rwa [Real.norm_eq_abs])

omit [InnerProductSpace ℝ H] in
/-- **Joint convergence of tested regularized norms.** If `qᵢ → q₀` in `L²` with a uniform bound
`D` and `uᵢ → u₀` in `L²(H)`, then `∫ qᵢ N_ε(uᵢ) → ∫ q₀ N_ε(u₀)`. -/
theorem tendsto_integral_mul_regularizedNorm (hε : 0 < ε) {ι : Type*} {l : Filter ι}
    {q : ι → Lp ℝ 2 μ} {q₀ : Lp ℝ 2 μ} (hq : Tendsto q l (𝓝 q₀)) {D : ℝ} (hD0 : 0 ≤ D)
    (hD : ∀ᶠ i in l, ∀ᵐ x ∂μ, |q i x| ≤ D) (hD₀ : ∀ᵐ x ∂μ, |q₀ x| ≤ D)
    {u : ι → Lp H 2 μ} {u₀ : Lp H 2 μ} (hu : Tendsto u l (𝓝 u₀)) :
    Tendsto (fun i => ∫ x, q i x * regularizedNorm ε (u i x) ∂μ) l
      (𝓝 (∫ x, q₀ x * regularizedNorm ε (u₀ x) ∂μ)) := by
  have hB := FunctionalInequalities.L2.tendsto_integral_mul_of_tendsto hq hD hD₀
    (integrable_regularizedNorm hε u₀)
  have hu' := tendsto_iff_norm_sub_tendsto_zero.mp hu
  have hA : Tendsto (fun i => D * (‖u i - u₀‖ * ‖oneL2 μ‖)) l (𝓝 0) := by
    simpa using (hu'.mul_const ‖oneL2 μ‖).const_mul D
  have hdiff : Tendsto (fun i => (∫ x, q i x * regularizedNorm ε (u i x) ∂μ) -
      ∫ x, q i x * regularizedNorm ε (u₀ x) ∂μ) l (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hA
    filter_upwards [hD] with i hi
    rw [Real.norm_eq_abs, ← integral_sub (integrable_mul_regularizedNorm hε
      (Lp.aestronglyMeasurable _) hi _) (integrable_mul_regularizedNorm hε
        (Lp.aestronglyMeasurable _) hi _)]
    refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ x, |q i x * regularizedNorm ε (u i x) - q i x * regularizedNorm ε (u₀ x)| ∂μ
        ≤ ∫ x, D * ‖(u i - u₀) x‖ ∂μ := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _)
            ((((Lp.memLp (u i - u₀)).integrable one_le_two).norm).const_mul D) ?_
          filter_upwards [hi, Lp.coeFn_sub (u i) u₀] with x hx hsub
          rw [← mul_sub, abs_mul, hsub, Pi.sub_apply]
          exact mul_le_mul hx (abs_regularizedNorm_sub_le hε _ _) (abs_nonneg _) hD0
      _ = D * ∫ x, ‖(u i - u₀) x‖ ∂μ := integral_const_mul _ _
      _ ≤ D * (‖u i - u₀‖ * ‖oneL2 μ‖) := by gcongr; exact integral_norm_le _
  simpa using hdiff.add hB

/-- **Convergence of the tested unit pairing.** For a fixed a.e. bounded `ψ`, if `uᵢ → u` and
`wᵢ → w` in `L²(H)`, then `∫ ψ ⟪U_ε(uᵢ), wᵢ⟫ → ∫ ψ ⟪U_ε(u), w⟫`, `U_ε = regularizedUnit ε`. -/
theorem tendsto_integral_mul_inner_regularizedUnit (hε : 0 < ε) {ψ : α → ℝ}
    (hψ : AEStronglyMeasurable ψ μ) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ᵐ x ∂μ, |ψ x| ≤ C)
    {ι : Type*} {l : Filter ι} {u w : ι → Lp H 2 μ} {u₀ w₀ : Lp H 2 μ}
    (hu : Tendsto u l (𝓝 u₀)) (hw : Tendsto w l (𝓝 w₀)) :
    Tendsto (fun i => ∫ x, ψ x * ⟪regularizedUnit ε (u i x), w i x⟫ ∂μ) l
      (𝓝 (∫ x, ψ x * ⟪regularizedUnit ε (u₀ x), w₀ x⟫ ∂μ)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hu' := tendsto_iff_norm_sub_tendsto_zero.mp hu
  have hw' := tendsto_iff_norm_sub_tendsto_zero.mp hw
  have hse : 0 < √ε := Real.sqrt_pos.mpr hε
  have hA : Tendsto (fun i => C * (2 / √ε * (‖u i - u₀‖ * ‖w₀‖) + ‖w i - w₀‖ * ‖oneL2 μ‖)) l
      (𝓝 0) := by
    simpa using (((hu'.mul_const ‖w₀‖).const_mul (2 / √ε)).add
      (hw'.mul_const ‖oneL2 μ‖)).const_mul C
  refine squeeze_zero (fun _ => norm_nonneg _) (fun i => ?_) hA
  rw [Real.norm_eq_abs, ← integral_sub (integrable_mul_inner_regularizedUnit hε hψ hC _ _)
    (integrable_mul_inner_regularizedUnit hε hψ hC _ _)]
  refine (abs_integral_le_integral_abs).trans ?_
  have hint : Integrable (fun x => C * (2 / √ε * (‖(u i - u₀) x‖ * ‖w₀ x‖) + ‖(w i - w₀) x‖))
      μ :=
    (((WeakGamma.integrable_norm_mul_norm (u i - u₀) w₀).const_mul (2 / √ε)).add
      ((Lp.memLp (w i - w₀)).integrable one_le_two).norm).const_mul C
  calc ∫ x, |ψ x * ⟪regularizedUnit ε (u i x), w i x⟫ - ψ x * ⟪regularizedUnit ε (u₀ x), w₀ x⟫|
        ∂μ ≤ ∫ x, C * (2 / √ε * (‖(u i - u₀) x‖ * ‖w₀ x‖) + ‖(w i - w₀) x‖) ∂μ := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _) hint ?_
        filter_upwards [hC, Lp.coeFn_sub (u i) u₀, Lp.coeFn_sub (w i) w₀] with x hx h1 h2
        rw [← mul_sub, abs_mul, h1, h2, Pi.sub_apply, Pi.sub_apply]
        refine mul_le_mul hx ?_ (abs_nonneg _) hC0
        have hsplit : ⟪regularizedUnit ε (u i x), w i x⟫ - ⟪regularizedUnit ε (u₀ x), w₀ x⟫ =
            ⟪regularizedUnit ε (u i x) - regularizedUnit ε (u₀ x), w₀ x⟫ +
              ⟪regularizedUnit ε (u i x), w i x - w₀ x⟫ := by
          rw [inner_sub_left, inner_sub_right]; ring
        rw [hsplit]
        refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
        · refine (abs_real_inner_le_norm _ _).trans ?_
          have := norm_regularizedUnit_sub_le hε (u i x) (u₀ x)
          nlinarith [norm_nonneg (w₀ x), norm_nonneg (u i x - u₀ x)]
        · refine (abs_real_inner_le_norm _ _).trans ?_
          have := norm_regularizedUnit_le_one hε (u i x)
          nlinarith [norm_nonneg (w i x - w₀ x)]
    _ = C * (2 / √ε * ∫ x, ‖(u i - u₀) x‖ * ‖w₀ x‖ ∂μ + ∫ x, ‖(w i - w₀) x‖ ∂μ) := by
        rw [integral_const_mul, integral_add ((WeakGamma.integrable_norm_mul_norm (u i - u₀) w₀).const_mul
          (2 / √ε)) ((Lp.memLp (w i - w₀)).integrable one_le_two).norm, integral_const_mul]
    _ ≤ C * (2 / √ε * (‖u i - u₀‖ * ‖w₀‖) + ‖w i - w₀‖ * ‖oneL2 μ‖) := by
        gcongr
        · exact WeakGamma.integral_norm_mul_norm_le _ _
        · exact integral_norm_le _

/-- **Product rule for the tested regularized norm.** On a finite measure, let `s ↦ q s ∈ L²`
and `s ↦ u s ∈ L²(H)` have derivatives `q'`, `u'` at `r` within `S`, with `q r`, `q'` and the
difference quotients of `q` a.e. bounded by one `D`. Then `s ↦ ∫ q s · N_ε(u s) dμ` has
derivative `∫ q' N_ε(u r) dμ + ∫ q r ⟪U_ε(u r), u'⟫ dμ` at `r` within `S`. The remainder is
controlled by the Taylor bound `abs_regularizedNorm_sub_sub_inner_le`. -/
theorem hasDerivWithinAt_integral_mul_regularizedNorm (hε : 0 < ε) {q : ℝ → Lp ℝ 2 μ}
    {u : ℝ → Lp H 2 μ} {S : Set ℝ} {r : ℝ} {q' : Lp ℝ 2 μ} {u' : Lp H 2 μ}
    (hq : HasDerivWithinAt q q' S r) (hu : HasDerivWithinAt u u' S r) {D : ℝ} (hD0 : 0 ≤ D)
    (hqb : ∀ᵐ x ∂μ, |q r x| ≤ D)
    (hslope : ∀ᶠ s in 𝓝[S \ {r}] r, ∀ᵐ x ∂μ, |slope q r s x| ≤ D)
    (hq'b : ∀ᵐ x ∂μ, |q' x| ≤ D) :
    HasDerivWithinAt (fun s => ∫ x, q s x * regularizedNorm ε (u s x) ∂μ)
      ((∫ x, q' x * regularizedNorm ε (u r x) ∂μ) +
        ∫ x, q r x * ⟪regularizedUnit ε (u r x), u' x⟫ ∂μ) S r := by
  have hc : Tendsto u (𝓝[S \ {r}] r) (𝓝 (u r)) :=
    hu.continuousWithinAt.tendsto.mono_left (nhdsWithin_mono _ Set.sdiff_subset)
  rw [hasDerivWithinAt_iff_tendsto_slope] at hq hu ⊢
  have hse : 0 < √ε := Real.sqrt_pos.mpr hε
  have h1 := tendsto_integral_mul_regularizedNorm hε hq hD0 hslope hq'b hc
  have h2 := tendsto_integral_mul_inner_regularizedUnit hε (Lp.aestronglyMeasurable (q r)) hD0
    hqb (tendsto_const_nhds (x := u r)) hu
  set E : ℝ → ℝ := fun s =>
    (∫ x, q r x * ((s - r)⁻¹ * (regularizedNorm ε (u s x) - regularizedNorm ε (u r x))) ∂μ) -
      ∫ x, q r x * ⟪regularizedUnit ε (u r x), slope u r s x⟫ ∂μ with hEdef
  have hint₁ : ∀ s, Integrable (fun x => q r x *
      ((s - r)⁻¹ * (regularizedNorm ε (u s x) - regularizedNorm ε (u r x)))) μ := fun s =>
    (((integrable_regularizedNorm hε (u s)).sub (integrable_regularizedNorm hε (u r))).const_mul
      _).bdd_mul (Lp.aestronglyMeasurable _) (by
        filter_upwards [hqb] with x hx; rwa [Real.norm_eq_abs])
  have hE : Tendsto E (𝓝[S \ {r}] r) (𝓝 0) := by
    have hun : Tendsto (fun s => ‖u s - u r‖) (𝓝[S \ {r}] r) (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.mp hc
    have hsl : Tendsto (fun s => ‖slope u r s‖) (𝓝[S \ {r}] r) (𝓝 ‖u'‖) :=
      (continuous_norm.tendsto _).comp hu
    have hA : Tendsto (fun s => D / √ε * (‖u s - u r‖ * ‖slope u r s‖)) (𝓝[S \ {r}] r)
        (𝓝 0) := by simpa using (hun.mul hsl).const_mul (D / √ε)
    refine squeeze_zero_norm' ?_ hA
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hne : s - r ≠ 0 := sub_ne_zero.mpr hs.2
    rw [Real.norm_eq_abs, hEdef]
    simp only
    rw [← integral_sub (hint₁ s) (integrable_mul_inner_regularizedUnit hε
      (Lp.aestronglyMeasurable _) hqb _ _)]
    refine (abs_integral_le_integral_abs).trans ?_
    have hbd : Integrable (fun x => D / √ε * (‖(u s - u r) x‖ * ‖slope u r s x‖)) μ :=
      (WeakGamma.integrable_norm_mul_norm (u s - u r) (slope u r s)).const_mul _
    calc ∫ x, |q r x * ((s - r)⁻¹ * (regularizedNorm ε (u s x) - regularizedNorm ε (u r x))) -
          q r x * ⟪regularizedUnit ε (u r x), slope u r s x⟫| ∂μ
        ≤ ∫ x, D / √ε * (‖(u s - u r) x‖ * ‖slope u r s x‖) ∂μ := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _) hbd ?_
          have hslx : ∀ᵐ x ∂μ, slope u r s x = (s - r)⁻¹ • (u s x - u r x) := by
            rw [slope_def_module]
            filter_upwards [Lp.coeFn_smul (s - r)⁻¹ (u s - u r), Lp.coeFn_sub (u s) (u r)]
              with x h1 h2
            rw [h1, Pi.smul_apply, h2, Pi.sub_apply]
          filter_upwards [hqb, hslx, Lp.coeFn_sub (u s) (u r)] with x hx hsx hsub
          rw [hsub, Pi.sub_apply, hsx, inner_smul_right, ← mul_sub, ← mul_sub, abs_mul, abs_mul,
            norm_smul, Real.norm_eq_abs]
          have ht := abs_regularizedNorm_sub_sub_inner_le hε (u r x) (u s x)
          have hpos : 0 ≤ |(s - r)⁻¹| := abs_nonneg _
          calc |q r x| * (|(s - r)⁻¹| * |regularizedNorm ε (u s x) - regularizedNorm ε (u r x) -
                ⟪regularizedUnit ε (u r x), u s x - u r x⟫|)
              ≤ D * (|(s - r)⁻¹| * (‖u s x - u r x‖ ^ 2 / √ε)) := by gcongr
            _ = D / √ε * (‖u s x - u r x‖ * (|(s - r)⁻¹| * ‖u s x - u r x‖)) := by ring
      _ = D / √ε * ∫ x, ‖(u s - u r) x‖ * ‖slope u r s x‖ ∂μ := integral_const_mul _ _
      _ ≤ D / √ε * (‖u s - u r‖ * ‖slope u r s‖) := by
          gcongr; exact WeakGamma.integral_norm_mul_norm_le _ _
  have hlim := (h1.add h2).add hE
  simp only [add_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [hslope, self_mem_nhdsWithin] with s hs hsS
  have hne : s - r ≠ 0 := sub_ne_zero.mpr hsS.2
  have hsl : ∀ᵐ x ∂μ, slope q r s x = (s - r)⁻¹ * (q s x - q r x) := by
    rw [slope_def_module]
    filter_upwards [Lp.coeFn_smul (s - r)⁻¹ (q s - q r), Lp.coeFn_sub (q s) (q r)] with x h1 h2
    rw [h1, Pi.smul_apply, h2, Pi.sub_apply, smul_eq_mul]
  have hqs : ∀ᵐ x ∂μ, |q s x| ≤ D + |s - r| * D := by
    filter_upwards [hsl, hs, hqb] with x h1 h2 h3
    have heq : q s x = q r x + (s - r) * slope q r s x := by
      rw [h1]; field_simp; ring
    rw [heq]
    calc |q r x + (s - r) * slope q r s x| ≤ |q r x| + |s - r| * |slope q r s x| := by
          rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ D + |s - r| * D := by gcongr
  have i₀ := integrable_mul_regularizedNorm hε (Lp.aestronglyMeasurable (q s)) hqs (u s)
  have i₀' := integrable_mul_regularizedNorm hε (Lp.aestronglyMeasurable (q r)) hqb (u r)
  have i₁ := integrable_mul_regularizedNorm hε (Lp.aestronglyMeasurable (slope q r s)) hs (u s)
  simp only [hEdef, slope_def_field]
  rw [div_eq_inv_mul, ← integral_sub i₀ i₀', ← integral_const_mul, add_assoc, add_sub_cancel,
    ← integral_add i₁ (hint₁ s)]
  refine integral_congr_ae ?_
  filter_upwards [hsl] with x hx
  rw [hx]
  ring

omit [InnerProductSpace ℝ H] in
/-- **Removing the regularization.** For an a.e. bounded multiplier `w` and `u ∈ L²(H)`,
`∫ w N_ε(u) dμ → ∫ w ‖u‖ dμ` as `ε → 0⁺`, by dominated convergence with bound `K ‖u‖`. -/
theorem tendsto_integral_mul_regularizedNorm_zero {w : α → ℝ} (hw : AEStronglyMeasurable w μ)
    {K : ℝ} (hK : ∀ᵐ x ∂μ, |w x| ≤ K) (u : Lp H 2 μ) :
    Tendsto (fun ε => ∫ x, w x * regularizedNorm ε (u x) ∂μ) (𝓝[>] 0)
      (𝓝 (∫ x, w x * ‖u x‖ ∂μ)) := by
  refine tendsto_integral_filter_of_dominated_convergence (fun x => K * ‖u x‖) ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun ε => hw.mul (aestronglyMeasurable_regularizedNorm u)
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    filter_upwards [hK] with x hx
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (regularizedNorm_nonneg ε _)]
    exact mul_le_mul hx (regularizedNorm_le_norm hε _) (regularizedNorm_nonneg ε _)
      ((abs_nonneg _).trans hx)
  · exact ((Lp.memLp u).integrable one_le_two).norm.const_mul K
  · exact Eventually.of_forall fun x => (tendsto_regularizedNorm (u x)).const_mul (w x)

end Integral

end FunctionalInequalities.Analysis.BakryEmery
