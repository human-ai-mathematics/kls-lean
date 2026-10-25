import FunctionalInequalities.Analysis.Convex.Subgradient

/-!
# Proximal points, Moreau derivatives and resolvent symmetry
-/

noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace

section LT12D2ProximalPoint

open Set
open scoped RealInnerProductSpace

/-! The proximal point of a convex function and its Lipschitz dependence. -/

namespace FunctionalInequalities.Analysis

section InnerProduct

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem proximal_subgradient_monotonicity
    {f : E → ℝ} {x x' z w : E}
    (hx : ∀ y, f x + ⟪z - x, y - x⟫ ≤ f y)
    (hx' : ∀ y, f x' + ⟪w - x', y - x'⟫ ≤ f y) :
    ‖x - x'‖ ^ 2 ≤ ⟪x - x', z - w⟫ := by
  have h₁ : f x - ⟪z - x, x - x'⟫ ≤ f x' := by
    simpa only [← neg_sub x x', inner_neg_right, sub_eq_add_neg] using hx x'
  have h₂ := hx' x
  have hm : 0 ≤ ⟪(z - x) - (w - x'), x - x'⟫ := by
    rw [inner_sub_left]
    linarith
  have he : (z - x) - (w - x') = (z - w) - (x - x') := by
    abel
  rw [he, inner_sub_left, real_inner_self_eq_norm_sq] at hm
  have hc := real_inner_comm (x - x') (z - w)
  linarith

set_option maxHeartbeats 800000 in
private theorem exists_proximal_minimizer
    [FiniteDimensional ℝ E] {f : E → ℝ}
    (hconv : ConvexOn ℝ univ f) (z : E) :
    ∃ x, ∀ y,
      f x + (1 / 2 : ℝ) * ‖x - z‖ ^ 2 ≤
        f y + (1 / 2 : ℝ) * ‖y - z‖ ^ 2 := by
  let φ : E → ℝ := fun x => f x + (1 / 2 : ℝ) * ‖x - z‖ ^ 2
  have hf : Continuous f :=
    continuousOn_univ.mp (hconv.continuousOn isOpen_univ)
  have hφ : Continuous φ :=
    hf.add (((continuous_id.sub continuous_const).norm.pow 2).const_mul (1 / 2 : ℝ))
  obtain ⟨g, hg, _⟩ := exists_subgradient_slope_le_inner_add hconv z (0 : E)
  let R : ℝ := 2 * ‖g‖ + 1
  have hR : 0 ≤ R := by
    dsimp [R]
    positivity
  obtain ⟨x, _, hx⟩ :=
    (isCompact_closedBall z R).exists_isMinOn
      ⟨z, Metric.mem_closedBall_self hR⟩ hφ.continuousOn
  refine ⟨x, ?_⟩
  intro y
  by_cases hy : y ∈ Metric.closedBall z R
  · exact (isMinOn_iff.mp hx) y hy
  · have hr : 2 * ‖g‖ + 1 < ‖y - z‖ := by
      simpa only [Metric.mem_closedBall, dist_eq_norm, not_le, R] using hy
    have hr0 : 0 < ‖y - z‖ := by
      linarith [norm_nonneg g]
    have hprod :=
      mul_pos hr0 (show 0 < ‖y - z‖ - 2 * ‖g‖ by linarith)
    have hi := neg_le_of_abs_le (abs_real_inner_le_norm g (y - z))
    have ha := hg y
    have hxz := (isMinOn_iff.mp hx) z (Metric.mem_closedBall_self hR)
    dsimp [φ] at hxz ⊢
    simp only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0),
      mul_zero, add_zero] at hxz
    nlinarith

set_option maxHeartbeats 800000 in
private theorem subgradient_of_proximal_minimizer
    {f : E → ℝ} (hconv : ConvexOn ℝ univ f) {x z : E}
    (hx : ∀ y,
      f x + (1 / 2 : ℝ) * ‖x - z‖ ^ 2 ≤
        f y + (1 / 2 : ℝ) * ‖y - z‖ ^ 2) :
    ∀ y, f x + ⟪z - x, y - x⟫ ≤ f y := by
  intro y
  have ht : ∀ t : ℝ, 0 < t → t ≤ 1 →
      0 ≤ f y - f x + ⟪x - z, y - x⟫ + (t / 2) * ‖y - x‖ ^ 2 := by
    intro t ht ht1
    have he : (1 - t) • x + t • y = x + t • (y - x) := by
      rw [sub_smul, one_smul, smul_sub]
      abel
    have hf := hconv.2 (mem_univ x) (mem_univ y)
      (sub_nonneg.mpr ht1) ht.le (show 1 - t + t = 1 by ring)
    rw [he] at hf
    simp only [smul_eq_mul] at hf
    have hm := hx (x + t • (y - x))
    have he' : x + t • (y - x) - z = (x - z) + t • (y - x) := by
      abel
    rw [he', norm_add_sq_real, inner_smul_right, norm_smul,
      Real.norm_eq_abs, abs_of_pos ht] at hm
    have hmul :
        0 ≤ t * (f y - f x + ⟪x - z, y - x⟫ + (t / 2) * ‖y - x‖ ^ 2) := by
      nlinarith
    exact nonneg_of_mul_nonneg_right hmul ht
  have hcont : Continuous
      (fun t : ℝ => f y - f x + ⟪x - z, y - x⟫ + (t / 2) * ‖y - x‖ ^ 2) :=
    continuous_const.add ((continuous_id.div_const 2).mul continuous_const)
  have hev : ∀ᶠ t : ℝ in nhdsWithin 0 (Ioi 0),
      0 ≤ f y - f x + ⟪x - z, y - x⟫ + (t / 2) * ‖y - x‖ ^ 2 := by
    have hpos : ∀ᶠ t : ℝ in nhdsWithin 0 (Ioi 0), 0 < t :=
      self_mem_nhdsWithin
    have hsmall : ∀ᶠ t : ℝ in nhdsWithin 0 (Ioi 0), t < 1 :=
      (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono
        nhdsWithin_le_nhds
    exact (hpos.and hsmall).mono (fun t h => ht t h.1 h.2.le)
  have hlim : 0 ≤ f y - f x + ⟪x - z, y - x⟫ := by
    simpa only [zero_div, zero_mul, add_zero] using
      ge_of_tendsto ((hcont.tendsto 0).mono_left nhdsWithin_le_nhds) hev
  have hi : ⟪z - x, y - x⟫ = -⟪x - z, y - x⟫ := by
    rw [← neg_sub x z, inner_neg_left]
  rw [hi]
  linarith

/-- The **proximal point** (resolvent of the subdifferential) of `f` at `z`: a point `x` such that
`z − x` is a subgradient of `f` at `x`, i.e. the minimiser of `x ↦ f x + ½‖x − z‖²` (weak Letwin route,
Alexandrov's theorem). For convex `f` on a finite-dimensional space it exists and is unique. -/
def proximalPoint {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (f : E → ℝ) (z : E) : E :=
  Classical.epsilon fun x => ∀ y, f x + ⟪z - x, y - x⟫ ≤ f y

section FiniteDimensional

variable [FiniteDimensional ℝ E]

/-- `z − proximalPoint f z` is a subgradient of the convex `f` at `proximalPoint f z`. -/
theorem proximalPoint_spec {f : E → ℝ} (hconv : ConvexOn ℝ univ f) (z : E) :
    ∀ y, f (proximalPoint f z) + ⟪z - proximalPoint f z, y - proximalPoint f z⟫ ≤ f y := by
  obtain ⟨x, hx⟩ := exists_proximal_minimizer hconv z
  exact Classical.epsilon_spec
    (p := fun x : E => ∀ y, f x + ⟪z - x, y - x⟫ ≤ f y)
    ⟨x, subgradient_of_proximal_minimizer hconv hx⟩

/-- Uniqueness: if `z − x` is a subgradient of `f` at `x`, then `x` is the proximal point of `z`. -/
theorem proximalPoint_eq_of_subgradient {f : E → ℝ} (hconv : ConvexOn ℝ univ f) {x z : E}
    (hx : ∀ y, f x + ⟪z - x, y - x⟫ ≤ f y) : proximalPoint f z = x := by
  have h := proximal_subgradient_monotonicity (proximalPoint_spec hconv z) hx
  simp only [sub_self, inner_zero_right] at h
  have hn : ‖proximalPoint f z - x‖ = 0 := by
    nlinarith [norm_nonneg (proximalPoint f z - x)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

/-- Firm nonexpansiveness of the proximal map. -/
theorem sq_norm_proximalPoint_sub_le_inner {f : E → ℝ} (hconv : ConvexOn ℝ univ f)
    (z w : E) :
    ‖proximalPoint f z - proximalPoint f w‖ ^ 2 ≤
      ⟪proximalPoint f z - proximalPoint f w, z - w⟫ := by
  exact proximal_subgradient_monotonicity
    (proximalPoint_spec hconv z) (proximalPoint_spec hconv w)

/-- The proximal map is `1`-Lipschitz. -/
theorem lipschitzWith_proximalPoint {f : E → ℝ} (hconv : ConvexOn ℝ univ f) :
    LipschitzWith 1 (proximalPoint f) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  have h := sq_norm_proximalPoint_sub_le_inner hconv z w
  have hi := real_inner_le_norm (proximalPoint f z - proximalPoint f w) (z - w)
  have hb : ‖proximalPoint f z - proximalPoint f w‖ ^ 2 ≤
      ‖proximalPoint f z - proximalPoint f w‖ * ‖z - w‖ :=
    h.trans hi
  by_contra hn
  have hlt : ‖z - w‖ < ‖proximalPoint f z - proximalPoint f w‖ :=
    lt_of_not_ge hn
  have hp : 0 < ‖proximalPoint f z - proximalPoint f w‖ :=
    lt_of_le_of_lt (norm_nonneg _) hlt
  have hm := mul_pos hp (sub_pos.mpr hlt)
  nlinarith

end FiniteDimensional

end InnerProduct

end FunctionalInequalities.Analysis

end LT12D2ProximalPoint

section LT12D3MoreauSymmetricDerivative

open Set Filter
open scoped RealInnerProductSpace Topology

/-! Derivative of `½‖x‖² − (Moreau envelope)` and symmetry of the derivative of the resolvent. -/

namespace FunctionalInequalities.Analysis

section InnerProduct

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **The resolvent of a convex function is a gradient** (weak Letwin route, Alexandrov's theorem): if `P z` is a point at which `z − P z` is a subgradient of the convex `f` (the proximal map), then
`w ↦ ½‖w‖² − (f (P w) + ½‖P w − w‖²)` (½‖·‖² minus the Moreau envelope) has derivative `⟪P z, ·⟫` at every `z`. -/
theorem hasFDerivAt_half_sq_sub_moreau
    {f : E → ℝ} {P : E → E} (hP : ∀ z y, f (P z) + ⟪z - P z, y - P z⟫ ≤ f y) (z : E) :
    HasFDerivAt (fun w => (1 / 2) * ‖w‖ ^ 2 - (f (P w) + (1 / 2) * ‖P w - w‖ ^ 2))
      (innerSL ℝ (P z)) z := by
  let g : E → ℝ := fun w =>
    (1 / 2) * ‖w‖ ^ 2 - (f (P w) + (1 / 2) * ‖P w - w‖ ^ 2)
  have hbound (w : E) :
      0 ≤ g w - g z - ⟪P z, w - z⟫ ∧
        g w - g z - ⟪P z, w - z⟫ ≤ (1 / 2) * ‖w - z‖ ^ 2 := by
    have hpw := hP w (P z)
    have hpz := hP z (P w)
    have hsq := sq_nonneg ‖(w - z) - (P w - P z)‖
    have hsq' := sq_nonneg ‖P w - P z‖
    dsimp only [g]
    simp only [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right]
      at hpw hpz hsq hsq' ⊢
    simp only [real_inner_comm] at hpw hpz hsq hsq' ⊢
    constructor
    · linarith only [hpw, hsq']
    · linarith only [hpz, hsq]
  change HasFDerivAt g (innerSL ℝ (P z)) z
  apply HasFDerivAt.of_isLittleO
  apply Asymptotics.IsLittleO.of_bound
  intro c hc
  have hn : ContinuousAt (fun w : E => ‖w - z‖) z :=
    (continuousAt_id.sub continuousAt_const).norm
  have he : ∀ᶠ w in 𝓝 z, ‖w - z‖ < c :=
    hn.eventually_lt continuousAt_const (by simpa only [sub_self, norm_zero] using hc)
  filter_upwards [he] with w hw
  change ‖g w - g z - ⟪P z, w - z⟫‖ ≤ c * ‖w - z‖
  rw [Real.norm_eq_abs, abs_of_nonneg (hbound w).1]
  calc
    g w - g z - ⟪P z, w - z⟫ ≤ (1 / 2) * ‖w - z‖ ^ 2 := (hbound w).2
    _ ≤ c * ‖w - z‖ := by
      have hm := mul_le_mul_of_nonneg_right hw.le (norm_nonneg (w - z))
      nlinarith only [hm, sq_nonneg ‖w - z‖]

/-- **The derivative of the resolvent is symmetric and firmly nonexpansive**: at a point
where the proximal map `P` is differentiable with derivative `T`, `⟪T v, w⟫ = ⟪v, T w⟫` and
`‖T v‖² ≤ ⟪T v, v⟫`. -/
theorem inner_hasFDerivAt_resolvent_symm
    {f : E → ℝ} {P : E → E} (hP : ∀ z y, f (P z) + ⟪z - P z, y - P z⟫ ≤ f y) {z : E}
    {T : E →L[ℝ] E} (hT : HasFDerivAt P T z) (v w : E) :
    ⟪T v, w⟫ = ⟪v, T w⟫ ∧ ‖T v‖ ^ 2 ≤ ⟪T v, v⟫ := by
  constructor
  · have hs := second_derivative_symmetric
      (fun y => hasFDerivAt_half_sq_sub_moreau hP y)
      ((innerSL ℝ : E →L[ℝ] (E →L[ℝ] ℝ)).hasFDerivAt.comp z hT) v w
    change ⟪T v, w⟫ = ⟪T w, v⟫ at hs
    exact hs.trans (real_inner_comm (T w) v).symm
  · have hfirm (a b : E) :
        ‖P a - P b‖ ^ 2 ≤ ⟪P a - P b, a - b⟫ := by
      have hab := hP a (P b)
      have hba := hP b (P a)
      simp only [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right]
        at hab hba ⊢
      simp only [real_inner_comm] at hab hba ⊢
      linarith only [hab, hba]
    have hline : HasDerivAt (fun t : ℝ => P (z + t • v)) (T v) 0 := by
      have hp : HasDerivAt (fun t : ℝ => z + t • v) v 0 := by
        simpa only [id_eq, one_smul] using
          ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add z
      have ht : HasFDerivAt P T (z + (0 : ℝ) • v) := by
        simpa only [zero_smul, add_zero] using hT
      exact ht.comp_hasDerivAt 0 hp
    have hlim :
        Tendsto (fun t : ℝ => t⁻¹ • (P (z + t • v) - P z))
          (𝓝[≠] 0) (𝓝 (T v)) := by
      simpa only [zero_add, zero_smul, add_zero] using hline.tendsto_slope_zero
    have hquot (t : ℝ) :
        ‖t⁻¹ • (P (z + t • v) - P z)‖ ^ 2 ≤
          ⟪t⁻¹ • (P (z + t • v) - P z), v⟫ := by
      by_cases ht : t = 0
      · simp [ht]
      · have hp := hfirm (z + t • v) z
        simp only [add_sub_cancel_left, real_inner_smul_right] at hp
        rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, real_inner_smul_left]
        calc
          (t⁻¹) ^ 2 * ‖P (z + t • v) - P z‖ ^ 2 ≤
              (t⁻¹) ^ 2 * (t * ⟪P (z + t • v) - P z, v⟫) :=
            mul_le_mul_of_nonneg_left hp (sq_nonneg t⁻¹)
          _ = t⁻¹ * ⟪P (z + t • v) - P z, v⟫ := by
            field_simp [ht]
    exact le_of_tendsto_of_tendsto (hlim.norm.pow 2)
      (hlim.inner tendsto_const_nhds) (Filter.Eventually.of_forall hquot)

end InnerProduct

end FunctionalInequalities.Analysis

end LT12D3MoreauSymmetricDerivative
