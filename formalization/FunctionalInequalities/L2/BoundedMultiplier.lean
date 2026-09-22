import Mathlib.MeasureTheory.Function.L2Space

/-!
# Multiplication of an `L²` class by an almost everywhere bounded multiplier

Two operations are needed whenever a closed differential operator is tested against a smooth
compactly supported function: multiplying a vector-valued `L²` class by a bounded **scalar**
multiplier, and multiplying a scalar `L²` class by a bounded **vector** multiplier. Both are
bounded linear maps on `L²`, and both are packaged here as continuous linear maps so that the
usual `map_sub` and operator-norm estimates are available without repeating the pointwise
argument.

`bddSmulL c` sends `u : Lp H 2 μ` to the class of `x ↦ c x • u x`, and `bddSmulRightL β` sends
`u : Lp ℝ 2 μ` to the class of `x ↦ u x • β x`. In both cases the multiplier is only assumed
a.e. strongly measurable and a.e. bounded by a constant `M`, and the operator norm bound is
`|M|`. No reverse inequality is claimed: `|M|` is a bound, not the operator norm.
-/

noncomputable section

open MeasureTheory

namespace FunctionalInequalities.L2

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
  {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

section BddSmul

variable {c : α → ℝ} {M : ℝ}

/-- An a.e. bounded scalar multiplier preserves `L²`. -/
theorem memLp_bddSmul (hc : AEStronglyMeasurable c μ) (hM : ∀ᵐ x ∂μ, |c x| ≤ M)
    (u : Lp H 2 μ) : MemLp (fun x => c x • (u x)) 2 μ := by
  refine MemLp.of_le ((Lp.memLp u).const_smul M) (hc.smul (Lp.aestronglyMeasurable u)) ?_
  filter_upwards [hM] with x hx
  have h1 : ‖c x • (u x)‖ = |c x| * ‖u x‖ := by
    rw [norm_smul, Real.norm_eq_abs]
  have h2 : ‖(M • (u : α → H)) x‖ = |M| * ‖u x‖ := by
    simp [norm_smul, Real.norm_eq_abs]
  rw [h1, h2]
  exact mul_le_mul_of_nonneg_right (hx.trans (le_abs_self M)) (norm_nonneg _)

/-- Multiplication by an a.e. bounded scalar multiplier, as a linear map on `L²`. -/
def bddSmulₗ (hc : AEStronglyMeasurable c μ) (hM : ∀ᵐ x ∂μ, |c x| ≤ M) :
    Lp H 2 μ →ₗ[ℝ] Lp H 2 μ where
  toFun u := (memLp_bddSmul hc hM u).toLp _
  map_add' u v := by
    refine Lp.ext ?_
    filter_upwards [(memLp_bddSmul hc hM (u + v)).coeFn_toLp, Lp.coeFn_add
      ((memLp_bddSmul hc hM u).toLp _) ((memLp_bddSmul hc hM v).toLp _),
      (memLp_bddSmul hc hM u).coeFn_toLp, (memLp_bddSmul hc hM v).coeFn_toLp,
      Lp.coeFn_add u v] with x h1 h2 h3 h4 h5
    simp only [h1, h2, h3, h4, h5, Pi.add_apply, smul_add]
  map_smul' a u := by
    refine Lp.ext ?_
    filter_upwards [(memLp_bddSmul hc hM (a • u)).coeFn_toLp, Lp.coeFn_smul a
      ((memLp_bddSmul hc hM u).toLp _), (memLp_bddSmul hc hM u).coeFn_toLp,
      Lp.coeFn_smul a u] with x h1 h2 h3 h4
    simp only [RingHom.id_apply, h1, h2, h3, h4, Pi.smul_apply]
    exact smul_comm _ _ _

theorem coeFn_bddSmulₗ (hc : AEStronglyMeasurable c μ) (hM : ∀ᵐ x ∂μ, |c x| ≤ M)
    (u : Lp H 2 μ) :
    (bddSmulₗ hc hM u : α → H) =ᵐ[μ] fun x => c x • (u x) :=
  (memLp_bddSmul hc hM u).coeFn_toLp

theorem norm_bddSmulₗ_le (hc : AEStronglyMeasurable c μ) (hM : ∀ᵐ x ∂μ, |c x| ≤ M)
    (u : Lp H 2 μ) : ‖bddSmulₗ hc hM u‖ ≤ |M| * ‖u‖ := by
  have hle : ‖bddSmulₗ hc hM u‖ ≤ ‖(|M| • u : Lp H 2 μ)‖ := by
    refine Lp.norm_le_norm_of_ae_le ?_
    filter_upwards [coeFn_bddSmulₗ hc hM u, Lp.coeFn_smul (|M|) u, hM] with x h1 h2 h3
    rw [h1, h2, Pi.smul_apply, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_abs]
    exact mul_le_mul_of_nonneg_right (h3.trans (le_abs_self M)) (norm_nonneg _)
  refine hle.trans ?_
  rw [norm_smul, Real.norm_eq_abs, abs_abs]

/-- Multiplication by an a.e. bounded scalar multiplier, as a continuous linear map on `L²`. -/
def bddSmulL (hc : AEStronglyMeasurable c μ) (hM : ∀ᵐ x ∂μ, |c x| ≤ M) :
    Lp H 2 μ →L[ℝ] Lp H 2 μ :=
  LinearMap.mkContinuous (bddSmulₗ hc hM) |M| (norm_bddSmulₗ_le hc hM)

@[simp]
theorem bddSmulL_apply (hc : AEStronglyMeasurable c μ) (hM : ∀ᵐ x ∂μ, |c x| ≤ M)
    (u : Lp H 2 μ) : bddSmulL hc hM u = bddSmulₗ hc hM u := rfl

theorem coeFn_bddSmulL (hc : AEStronglyMeasurable c μ) (hM : ∀ᵐ x ∂μ, |c x| ≤ M)
    (u : Lp H 2 μ) :
    (bddSmulL hc hM u : α → H) =ᵐ[μ] fun x => c x • (u x) :=
  coeFn_bddSmulₗ hc hM u

theorem norm_bddSmulL_sub_le (hc : AEStronglyMeasurable c μ) (hM : ∀ᵐ x ∂μ, |c x| ≤ M)
    (u v : Lp H 2 μ) : ‖bddSmulL hc hM u - bddSmulL hc hM v‖ ≤ |M| * ‖u - v‖ := by
  rw [← map_sub]
  exact norm_bddSmulₗ_le hc hM (u - v)

end BddSmul

section BddSmulRight

variable {β : α → H} {M : ℝ}

/-- An a.e. bounded vector multiplier sends a scalar `L²` class to a vector `L²` class. -/
theorem memLp_bddSmulRight (hβ : AEStronglyMeasurable β μ) (hM : ∀ᵐ x ∂μ, ‖β x‖ ≤ M)
    (u : Lp ℝ 2 μ) : MemLp (fun x => (u x) • β x) 2 μ := by
  refine MemLp.of_le ((Lp.memLp u).const_smul M) ((Lp.aestronglyMeasurable u).smul hβ) ?_
  filter_upwards [hM] with x hx
  have h1 : ‖(u x) • β x‖ = |u x| * ‖β x‖ := by rw [norm_smul, Real.norm_eq_abs]
  have h2 : ‖(M • (u : α → ℝ)) x‖ = |M| * ‖u x‖ := by
    simp [Real.norm_eq_abs]
  rw [h1, h2, Real.norm_eq_abs, mul_comm]
  exact mul_le_mul_of_nonneg_right (hx.trans (le_abs_self M)) (abs_nonneg _)

/-- Multiplication by an a.e. bounded vector multiplier, as a linear map `L²(ℝ) → L²(H)`. -/
def bddSmulRightₗ (hβ : AEStronglyMeasurable β μ) (hM : ∀ᵐ x ∂μ, ‖β x‖ ≤ M) :
    Lp ℝ 2 μ →ₗ[ℝ] Lp H 2 μ where
  toFun u := (memLp_bddSmulRight hβ hM u).toLp _
  map_add' u v := by
    refine Lp.ext ?_
    filter_upwards [(memLp_bddSmulRight hβ hM (u + v)).coeFn_toLp, Lp.coeFn_add
      ((memLp_bddSmulRight hβ hM u).toLp _) ((memLp_bddSmulRight hβ hM v).toLp _),
      (memLp_bddSmulRight hβ hM u).coeFn_toLp, (memLp_bddSmulRight hβ hM v).coeFn_toLp,
      Lp.coeFn_add u v] with x h1 h2 h3 h4 h5
    simp only [h1, h2, h3, h4, h5, Pi.add_apply, add_smul]
  map_smul' a u := by
    refine Lp.ext ?_
    filter_upwards [(memLp_bddSmulRight hβ hM (a • u)).coeFn_toLp, Lp.coeFn_smul a
      ((memLp_bddSmulRight hβ hM u).toLp _), (memLp_bddSmulRight hβ hM u).coeFn_toLp,
      Lp.coeFn_smul a u] with x h1 h2 h3 h4
    simp only [RingHom.id_apply, h1, h2, h3, h4, Pi.smul_apply, smul_assoc]

theorem coeFn_bddSmulRightₗ (hβ : AEStronglyMeasurable β μ) (hM : ∀ᵐ x ∂μ, ‖β x‖ ≤ M)
    (u : Lp ℝ 2 μ) :
    (bddSmulRightₗ hβ hM u : α → H) =ᵐ[μ] fun x => (u x) • β x :=
  (memLp_bddSmulRight hβ hM u).coeFn_toLp

theorem norm_bddSmulRightₗ_le (hβ : AEStronglyMeasurable β μ) (hM : ∀ᵐ x ∂μ, ‖β x‖ ≤ M)
    (u : Lp ℝ 2 μ) : ‖bddSmulRightₗ hβ hM u‖ ≤ |M| * ‖u‖ := by
  have hle : ‖bddSmulRightₗ hβ hM u‖ ≤ ‖(|M| • u : Lp ℝ 2 μ)‖ := by
    refine Lp.norm_le_norm_of_ae_le ?_
    filter_upwards [coeFn_bddSmulRightₗ hβ hM u, Lp.coeFn_smul (|M|) u, hM] with x h1 h2 h3
    rw [h1, h2, Pi.smul_apply, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_abs, mul_comm (|M|)]
    exact mul_le_mul_of_nonneg_left (h3.trans (le_abs_self M)) (abs_nonneg _)
  refine hle.trans ?_
  rw [norm_smul, Real.norm_eq_abs, abs_abs]

/-- Multiplication by an a.e. bounded vector multiplier, as a continuous linear map. -/
def bddSmulRightL (hβ : AEStronglyMeasurable β μ) (hM : ∀ᵐ x ∂μ, ‖β x‖ ≤ M) :
    Lp ℝ 2 μ →L[ℝ] Lp H 2 μ :=
  LinearMap.mkContinuous (bddSmulRightₗ hβ hM) |M| (norm_bddSmulRightₗ_le hβ hM)

@[simp]
theorem bddSmulRightL_apply (hβ : AEStronglyMeasurable β μ) (hM : ∀ᵐ x ∂μ, ‖β x‖ ≤ M)
    (u : Lp ℝ 2 μ) : bddSmulRightL hβ hM u = bddSmulRightₗ hβ hM u := rfl

theorem coeFn_bddSmulRightL (hβ : AEStronglyMeasurable β μ) (hM : ∀ᵐ x ∂μ, ‖β x‖ ≤ M)
    (u : Lp ℝ 2 μ) :
    (bddSmulRightL hβ hM u : α → H) =ᵐ[μ] fun x => (u x) • β x :=
  coeFn_bddSmulRightₗ hβ hM u

theorem norm_bddSmulRightL_sub_le (hβ : AEStronglyMeasurable β μ) (hM : ∀ᵐ x ∂μ, ‖β x‖ ≤ M)
    (u v : Lp ℝ 2 μ) :
    ‖bddSmulRightL hβ hM u - bddSmulRightL hβ hM v‖ ≤ |M| * ‖u - v‖ := by
  rw [← map_sub]
  exact norm_bddSmulRightₗ_le hβ hM (u - v)

end BddSmulRight

section Symmetry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {c : α → ℝ} {M : ℝ}

/-- **A real a.e. bounded scalar multiplier is symmetric on `L²`.** Multiplication by `c` may be
moved from one side of the `L²` inner product to the other; this is the pointwise identity
`⟪c • a, b⟫ = ⟪a, c • b⟫` integrated. The multiplier is real valued, so no conjugation occurs. -/
theorem inner_bddSmulL_left (hc : AEStronglyMeasurable c μ) (hM : ∀ᵐ x ∂μ, |c x| ≤ M)
    (u v : Lp E 2 μ) :
    inner ℝ (bddSmulL hc hM u) v = inner ℝ u (bddSmulL hc hM v) := by
  rw [L2.inner_def, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_bddSmulL hc hM u, coeFn_bddSmulL hc hM v] with x h1 h2
  rw [h1, h2, real_inner_smul_left, real_inner_smul_right]

end Symmetry

end FunctionalInequalities.L2
