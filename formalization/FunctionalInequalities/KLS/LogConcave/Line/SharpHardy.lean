module

public import FunctionalInequalities.KLS.LogConcave.Line.Profile
public import FunctionalInequalities.KLS.LogConcave.Line.Hardy
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# The sharp Hardy inequality with constant `4 · Var` for clipped smooth tests

Source: Blueprint `thm:one-dimensional-logconcave-poincare` (sharp form with constant `4`); the
argument follows Sections 6–7 of the collaborator's constant-4 source audit (a locally kept record),
transported to the coordinate of the line. Read `clip`, `LineDensity.integral_sq_clipCentered_eq`,
`LineDensity.groundState_inequality`, `LineDensity.integral_sq_div_le` and
`LineDensity.variance_clip_le`.

For a log-concave law `μ` with Borell density `ρ`, distribution function `F`, `W = F (1 - F)` and
standard deviation `σ`, and for a smooth test `f` clipped to constants outside `[a, b] ⊆ Ω` with
`F a ≤ 1/2 ≤ F b`, let `h = f_{ab} - ∫ f_{ab} dμ` and `G(x) = ∫_{(-∞, x]} h dμ`. Then
`∫ h² dμ = -∫_a^b f' G dx` exactly (the clipped tails cancel the boundary terms of the integration
by parts), and the ground-state identity, integrated over larger intervals `[c, e] ⊆ Ω` with
`F c ≤ 1/2 ≤ F e`, gives `(1/4) ∫_c^e G² ρ / W² ≤ ∫ h² dμ + h(a)² F c + h(b)² (1 - F e)`; letting
`F c → 0` and `F e → 1` yields `∫_a^b G² ρ / W² ≤ 4 ∫ h² dμ`. Finally `x y ≤ x² / 8 + 2 y²` with
the profile bound `W ≤ σ ρ` yields `Var(f_{ab}) ≤ 4 σ² ∫ f'² dμ`.

The passage from clipped tests to all admissible tests is in the following module.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology intervalIntegral
open scoped ContDiff
open FunctionalInequalities.Probability.Line (cdf)

namespace FunctionalInequalities.KLS

/-- The clipping of `f` to constants outside `[a, b]`. -/
def clip (a b : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ := f (max a (min b x))

namespace clip

variable {a b : ℝ} {f : ℝ → ℝ}

theorem of_le (hab : a ≤ b) {x : ℝ} (hx : x ≤ a) : clip a b f x = f a := by
  unfold clip
  rw [min_eq_right (hx.trans hab), max_eq_left hx]

theorem of_ge {x : ℝ} (hx : b ≤ x) (hab : a ≤ b) : clip a b f x = f b := by
  unfold clip
  rw [min_eq_left hx, max_eq_right hab]

theorem of_mem {x : ℝ} (hx : x ∈ Icc a b) : clip a b f x = f x := by
  unfold clip
  rw [min_eq_right hx.2, max_eq_right hx.1]

theorem continuous (hf : Continuous f) : Continuous (clip a b f) :=
  hf.comp (continuous_const.max (continuous_const.min continuous_id))

theorem exists_bound (hab : a ≤ b) (hf : Continuous f) : ∃ C, ∀ x, ‖clip a b f x‖ ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (hf.continuousOn (s := Icc a b))
  refine ⟨C, fun x ↦ hC _ ⟨le_max_left _ _, ?_⟩⟩
  exact max_le hab (min_le_left _ _)

end clip

/-- The clipped test recentered by its mean under `μ`. -/
def clipCentered (μ : ProbabilityMeasure ℝ) (a b : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  clip a b f x - ∫ y, clip a b f y ∂(μ : Measure ℝ)

/-- The running integral `x ↦ ∫_{(-∞, x]} h dμ`. -/
def tailIntegral (μ : ProbabilityMeasure ℝ) (h : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ t in Iic x, h t ∂(μ : Measure ℝ)

/-- The weight `F (1 - F)`. -/
def cdfProd (μ : ProbabilityMeasure ℝ) (x : ℝ) : ℝ := cdf μ x * (1 - cdf μ x)

/-- The boundary term of the ground-state identity, `G² / W · (1 - 2F) / 2`. -/
def boundaryTerm (μ : ProbabilityMeasure ℝ) (h : ℝ → ℝ) (x : ℝ) : ℝ :=
  tailIntegral μ h x ^ 2 / cdfProd μ x * ((1 - 2 * cdf μ x) / 2)

namespace LineDensity

variable {μ : ProbabilityMeasure ℝ} (d : LineDensity μ)

section TailIntegral

variable {h : ℝ → ℝ} (hh : Continuous h) (hhb : ∃ C, ∀ x, ‖h x‖ ≤ C)
include hh hhb

omit d in
theorem integrable_of_bounded_continuous : Integrable h (μ : Measure ℝ) := by
  obtain ⟨C, hC⟩ := hhb
  exact (memLp_one_iff_integrable).mp (MemLp.of_bound hh.aestronglyMeasurable C (ae_of_all _ hC))

theorem integrable_mul_density : Integrable (fun x ↦ h x * d.ρ x) volume := by
  obtain ⟨C, hC⟩ := hhb
  exact d.integrable.bdd_mul hh.aestronglyMeasurable (ae_of_all _ hC)

/-- The running integral through an intermediate point. -/
theorem tailIntegral_eq_add_integral (x₀ x : ℝ) :
    tailIntegral μ h x = tailIntegral μ h x₀ + ∫ t in x₀..x, h t * d.ρ t := by
  have hint := d.integrable_mul_density hh hhb
  have hI := integrable_of_bounded_continuous (μ := μ) hh hhb
  have key :
    ∀ {u v : ℝ}, u ≤ v → tailIntegral μ h v = tailIntegral μ h u + ∫ t in u..v, h t * d.ρ t := by
    intro u v huv
    unfold tailIntegral
    rw [integral_of_le huv, ← d.setIntegral_eq_integral_mul _ measurableSet_Ioc, ←
      setIntegral_union (Iic_disjoint_Ioc le_rfl) measurableSet_Ioc hI.integrableOn
        hI.integrableOn,
      Iic_union_Ioc_eq_Iic huv]
  rcases le_total x₀ x with hle | hle
  · exact key hle
  · rw [integral_symm, key hle]
    ring

include d in
theorem continuous_tailIntegral : Continuous (tailIntegral μ h) := by
  have hint := d.integrable_mul_density hh hhb
  have : tailIntegral μ h = fun x ↦ tailIntegral μ h 0 + ∫ t in (0 : ℝ)..x, h t * d.ρ t :=
    funext fun x ↦ d.tailIntegral_eq_add_integral hh hhb 0 x
  rw [this]
  exact
    continuous_const.add
      (intervalIntegral.continuous_primitive (fun _ _ ↦ hint.intervalIntegrable) 0)

theorem hasDerivAt_tailIntegral {x : ℝ} (hx : x ∈ interior (μ : Measure ℝ).support) :
    HasDerivAt (tailIntegral μ h) (h x * d.ρ x) x := by
  have hint := d.integrable_mul_density hh hhb
  have : tailIntegral μ h = fun x ↦ tailIntegral μ h 0 + ∫ t in (0 : ℝ)..x, h t * d.ρ t :=
    funext fun x ↦ d.tailIntegral_eq_add_integral hh hhb 0 x
  rw [this]
  refine (integral_hasDerivAt_right hint.intervalIntegrable
    (hh.measurable.mul d.measurable).stronglyMeasurable.stronglyMeasurableAtFilter ?_).const_add _
  exact hh.continuousAt.mul (d.continuousOn.continuousAt (isOpen_interior.mem_nhds hx))

end TailIntegral

theorem cdfProd_pos {x : ℝ} (hx : x ∈ interior (μ : Measure ℝ).support) : 0 < cdfProd μ x :=
  mul_pos (Probability.Line.cdf_pos_of_mem_interior_support μ hx)
    (sub_pos.mpr (Probability.Line.cdf_lt_one_of_mem_interior_support μ hx))

include d in
theorem continuous_cdfProd : Continuous (cdfProd μ) :=
  d.continuous_cdf.mul (continuous_const.sub d.continuous_cdf)

theorem hasDerivAt_cdfProd {x : ℝ} (hx : x ∈ interior (μ : Measure ℝ).support) :
    HasDerivAt (cdfProd μ) (d.ρ x * (1 - 2 * cdf μ x)) x := by
  have h := (d.hasDerivAt_cdf hx).mul ((d.hasDerivAt_cdf hx).const_sub 1)
  exact h.congr_deriv (by ring)

include d in
/-- The distribution function is strictly increasing on the interior of the support. -/
theorem cdf_lt_cdf_of_mem {x y : ℝ} (hμ : LogConcave μ) (hx : x ∈ interior (μ : Measure ℝ).support)
    (hy : y ∈ interior (μ : Measure ℝ).support) (hxy : x < y) : cdf μ x < cdf μ y := by
  have hIcc : Icc x y ⊆ interior (μ : Measure ℝ).support :=
    hμ.convex_interior_support.ordConnected.out hx hy
  have h := d.cdf_sub_cdf_eq_integral hxy.le
  have hpos : 0 < ∫ t in x..y, d.ρ t :=
    intervalIntegral.intervalIntegral_pos_of_pos_on d.integrable.intervalIntegrable
      (fun t ht ↦ d.pos (hIcc (Ioo_subset_Icc_self ht))) hxy
  linarith

section Clipped

variable (hμ : LogConcave μ) (hi : (interior (μ : Measure ℝ).support).Nonempty)
  {a b : ℝ} (hab : a ≤ b) (haΩ : a ∈ interior (μ : Measure ℝ).support)
  (hbΩ : b ∈ interior (μ : Measure ℝ).support) {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)

include hf in
theorem continuous_clipCentered : Continuous (clipCentered μ a b f) :=
  (clip.continuous hf.continuous).sub continuous_const

include hab hf in
theorem exists_bound_clipCentered : ∃ C, ∀ x, ‖clipCentered μ a b f x‖ ≤ C := by
  obtain ⟨C, hC⟩ := clip.exists_bound hab hf.continuous
  refine ⟨C + ‖∫ y, clip a b f y ∂(μ : Measure ℝ)‖, fun x ↦ ?_⟩
  exact (norm_sub_le _ _).trans (add_le_add (hC x) le_rfl)

include hab hf in
theorem integral_clipCentered : ∫ x, clipCentered μ a b f x ∂(μ : Measure ℝ) = 0 := by
  have hI : Integrable (clip a b f) (μ : Measure ℝ) :=
    integrable_of_bounded_continuous (clip.continuous hf.continuous)
      (clip.exists_bound hab hf.continuous)
  unfold clipCentered
  rw [integral_sub hI (integrable_const _), MeasureTheory.integral_const]
  simp

include hab in
theorem clipCentered_of_le {x : ℝ} (hx : x ≤ a) :
    clipCentered μ a b f x = clipCentered μ a b f a := by
  unfold clipCentered
  rw [clip.of_le hab hx, clip.of_le hab le_rfl]

include hab in
theorem clipCentered_of_ge {x : ℝ} (hx : b ≤ x) :
    clipCentered μ a b f x = clipCentered μ a b f b := by
  unfold clipCentered
  rw [clip.of_ge hx hab, clip.of_ge le_rfl hab]

theorem clipCentered_of_mem {x : ℝ} (hx : x ∈ Icc a b) :
    clipCentered μ a b f x = f x - ∫ y, clip a b f y ∂(μ : Measure ℝ) := by
  unfold clipCentered
  rw [clip.of_mem hx]

include hab in
/-- The running integral of the centered clipped test left of the clipping interval. -/
theorem tailIntegral_clipCentered_of_le {x : ℝ} (hx : x ≤ a) :
    tailIntegral μ (clipCentered μ a b f) x = clipCentered μ a b f a * cdf μ x := by
  unfold tailIntegral
  rw [setIntegral_congr_fun measurableSet_Iic (g := fun _ ↦ clipCentered μ a b f a)
    (fun y hy ↦ clipCentered_of_le hab (le_trans hy hx)), setIntegral_const, smul_eq_mul, mul_comm]
  rfl

include hab in
theorem tailIntegral_clipCentered_left :
    tailIntegral μ (clipCentered μ a b f) a = clipCentered μ a b f a * cdf μ a :=
  tailIntegral_clipCentered_of_le hab le_rfl

include hab hf in
/-- The running integral of the centered clipped test right of the clipping interval. -/
theorem tailIntegral_clipCentered_of_ge {x : ℝ} (hx : b ≤ x) :
    tailIntegral μ (clipCentered μ a b f) x = -(clipCentered μ a b f b * (1 - cdf μ x)) := by
  have hI : Integrable (clipCentered μ a b f) (μ : Measure ℝ) :=
    integrable_of_bounded_continuous (continuous_clipCentered hf)
      (exists_bound_clipCentered hab hf)
  have hsplit := integral_add_compl (s := Iic x) measurableSet_Iic hI
  rw [compl_Iic, integral_clipCentered hab hf] at hsplit
  have hright :
    ∫ y in Ioi x, clipCentered μ a b f y ∂(μ : Measure ℝ) =
      clipCentered μ a b f b * (1 - cdf μ x) := by
    rw [setIntegral_congr_fun measurableSet_Ioi (g := fun _ ↦ clipCentered μ a b f b)
        (fun y hy ↦ clipCentered_of_ge hab (le_trans hx (le_of_lt hy))),
      setIntegral_const, smul_eq_mul, Probability.Line.measureReal_Ioi, mul_comm]
  unfold tailIntegral
  linarith

include hab hf in
theorem tailIntegral_clipCentered_right :
    tailIntegral μ (clipCentered μ a b f) b = -(clipCentered μ a b f b * (1 - cdf μ b)) :=
  tailIntegral_clipCentered_of_ge hab hf le_rfl

include hab in
/-- The boundary term left of the clipping interval is small when `F` is small. -/
theorem boundaryTerm_le_of_le {x : ℝ} (hx : x ≤ a) (hxΩ : x ∈ interior (μ : Measure ℝ).support)
    (hFx : cdf μ x ≤ 1 / 2) :
    boundaryTerm μ (clipCentered μ a b f) x ≤ clipCentered μ a b f a ^ 2 * cdf μ x := by
  have hF0 := Probability.Line.cdf_pos_of_mem_interior_support μ hxΩ
  have hF1 := Probability.Line.cdf_lt_one_of_mem_interior_support μ hxΩ
  unfold boundaryTerm cdfProd
  rw [tailIntegral_clipCentered_of_le hab hx]
  have h1 : (clipCentered μ a b f a * cdf μ x) ^ 2 / (cdf μ x * (1 - cdf μ x)) *
      ((1 - 2 * cdf μ x) / 2) = clipCentered μ a b f a ^ 2 *
        (cdf μ x * ((1 - 2 * cdf μ x) / (2 * (1 - cdf μ x)))) := by
    field_simp
  rw [h1]
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
  have : (1 - 2 * cdf μ x) / (2 * (1 - cdf μ x)) ≤ 1 := by
    rw [div_le_one (by linarith)]
    linarith
  calc cdf μ x * ((1 - 2 * cdf μ x) / (2 * (1 - cdf μ x))) ≤ cdf μ x * 1 :=
        mul_le_mul_of_nonneg_left this hF0.le
    _ = cdf μ x := mul_one _

include hab hf in
/-- The boundary term right of the clipping interval is small when `1 - F` is small. -/
theorem neg_boundaryTerm_le_of_ge {x : ℝ} (hx : b ≤ x) (hxΩ : x ∈ interior (μ : Measure ℝ).support)
    (hFx : 1 / 2 ≤ cdf μ x) :
    -boundaryTerm μ (clipCentered μ a b f) x ≤ clipCentered μ a b f b ^ 2 * (1 - cdf μ x) := by
  have hF0 := Probability.Line.cdf_pos_of_mem_interior_support μ hxΩ
  have hF1 := Probability.Line.cdf_lt_one_of_mem_interior_support μ hxΩ
  unfold boundaryTerm cdfProd
  rw [tailIntegral_clipCentered_of_ge hab hf hx]
  have h1 : -((-(clipCentered μ a b f b * (1 - cdf μ x))) ^ 2 / (cdf μ x * (1 - cdf μ x)) *
      ((1 - 2 * cdf μ x) / 2)) = clipCentered μ a b f b ^ 2 *
        ((1 - cdf μ x) * ((2 * cdf μ x - 1) / (2 * cdf μ x))) := by
    field_simp
    ring
  rw [h1]
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
  have : (2 * cdf μ x - 1) / (2 * cdf μ x) ≤ 1 := by
    rw [div_le_one (by linarith)]
    linarith
  calc (1 - cdf μ x) * ((2 * cdf μ x - 1) / (2 * cdf μ x)) ≤ (1 - cdf μ x) * 1 :=
        mul_le_mul_of_nonneg_left this (by linarith)
    _ = 1 - cdf μ x := mul_one _

include d hμ hab haΩ hbΩ hf in
/--
Claim B: the squared `L²` norm of the centered clipped test equals `-∫_a^b f' G`, with `G` its
running integral. -/
theorem integral_sq_clipCentered_eq :
    ∫ x, clipCentered μ a b f x ^ 2 ∂(μ : Measure ℝ) =
      -∫ x in a..b, deriv f x * tailIntegral μ (clipCentered μ a b f) x := by
  set c := ∫ y, clip a b f y ∂(μ : Measure ℝ) with hc
  set h := clipCentered μ a b f with hh
  set G := tailIntegral μ h with hG
  have hhc : Continuous h := continuous_clipCentered hf
  have hhb : ∃ C, ∀ x, ‖h x‖ ≤ C := exists_bound_clipCentered hab hf
  have hI : Integrable h (μ : Measure ℝ) := integrable_of_bounded_continuous hhc hhb
  have hI2 : Integrable (fun x ↦ h x ^ 2) (μ : Measure ℝ) :=
    integrable_of_bounded_continuous (hhc.pow 2)
      (by
        obtain ⟨C, hC⟩ := hhb
        exact
          ⟨C ^ 2, fun x ↦ by
            rw [norm_pow]
            exact pow_le_pow_left₀ (norm_nonneg _) (hC x) 2⟩)
  have hIcc : Icc a b ⊆ interior (μ : Measure ℝ).support :=
    hμ.convex_interior_support.ordConnected.out haΩ hbΩ
  have huIcc : uIcc a b = Icc a b :=
    uIcc_of_le
      hab
  -- split the integral into the two tails and the middle part

  have hsplit1 := integral_add_compl (s := Iic b) measurableSet_Iic hI2
  rw [compl_Iic] at hsplit1
  have hsplit2 :
    ∫ x in Iic b, h x ^ 2 ∂(μ : Measure ℝ) =
      ∫ x in Iic a, h x ^ 2 ∂(μ : Measure ℝ) + ∫ x in Ioc a b, h x ^ 2 ∂(μ : Measure ℝ) := by
    rw [←
      setIntegral_union (Iic_disjoint_Ioc le_rfl) measurableSet_Ioc hI2.integrableOn
        hI2.integrableOn,
      Iic_union_Ioc_eq_Iic hab]
  have hleft : ∫ x in Iic a, h x ^ 2 ∂(μ : Measure ℝ) = h a ^ 2 * cdf μ a := by
    rw [setIntegral_congr_fun measurableSet_Iic (g := fun _ ↦ h a ^ 2)
        (fun x hx ↦ by rw [hh, clipCentered_of_le hab hx]),
      setIntegral_const, smul_eq_mul, mul_comm]
    rfl
  have hright : ∫ x in Ioi b, h x ^ 2 ∂(μ : Measure ℝ) = h b ^ 2 * (1 - cdf μ b) := by
    rw [setIntegral_congr_fun measurableSet_Ioi (g := fun _ ↦ h b ^ 2)
        (fun x hx ↦ by rw [hh, clipCentered_of_ge hab (le_of_lt hx)]),
      setIntegral_const, smul_eq_mul, Probability.Line.measureReal_Ioi, mul_comm]
  have hmid :
    ∫ x in Ioc a b, h x ^ 2 ∂(μ : Measure ℝ) = ∫ x in a..b, (f x - c) * (h x * d.ρ x) := by
    rw [d.setIntegral_eq_integral_mul _ measurableSet_Ioc, ← integral_of_le hab]
    refine integral_congr fun x hx ↦ ?_
    rw [huIcc] at hx
    have : h x = f x - c := by rw [hh, clipCentered_of_mem hx]
    rw [this]
    ring
  -- integration by parts on `[a, b]`

  have hfd : ∀ x, HasDerivAt f (deriv f x) x := fun x ↦
    ((hf.differentiable (by simp)) x).hasDerivAt
  have hu : ∀ x ∈ uIcc a b, HasDerivAt (fun x ↦ f x - c) (deriv f x) x := fun x _ ↦
    (hfd x).sub_const c
  have hv : ∀ x ∈ uIcc a b, HasDerivAt G (h x * d.ρ x) x := fun x hx ↦
    d.hasDerivAt_tailIntegral hhc hhb (hIcc (huIcc ▸ hx))
  have hu' : IntervalIntegrable (deriv f) volume a b :=
    (hf.continuous_deriv (by exact_mod_cast le_top)).intervalIntegrable _ _
  have hv' : IntervalIntegrable (fun x ↦ h x * d.ρ x) volume a b :=
    (d.integrable_mul_density hhc hhb).intervalIntegrable
  have hibp := integral_mul_deriv_eq_deriv_mul hu hv hu' hv'
  have hGa : G a = h a * cdf μ a := tailIntegral_clipCentered_left hab
  have hGb : G b = -(h b * (1 - cdf μ b)) := tailIntegral_clipCentered_right hab hf
  have hfa : f a - c = h a := by rw [hh, clipCentered_of_mem ⟨le_rfl, hab⟩]
  have hfb : f b - c = h b := by rw [hh, clipCentered_of_mem ⟨hab, le_rfl⟩]
  rw [hfa, hfb, hGa, hGb] at hibp
  linarith

include hμ hab hf in
/-- The ground-state inequality on an interval `[c, e] ⊆ Ω`:
`(1/4) ∫_c^e G² ρ / W² + (Ξ e - Ξ c) ≤ ∫_c^e h² ρ`. -/
theorem groundState_inequality {c e : ℝ} (hce : c ≤ e)
    (hcΩ : c ∈ interior (μ : Measure ℝ).support) (heΩ : e ∈ interior (μ : Measure ℝ).support) :
    (1 / 4) *
          (∫ x in c..e, tailIntegral μ (clipCentered μ a b f) x ^ 2 * d.ρ x / cdfProd μ x ^ 2) +
        (boundaryTerm μ (clipCentered μ a b f) e - boundaryTerm μ (clipCentered μ a b f) c) ≤
      ∫ x in c..e, clipCentered μ a b f x ^ 2 * d.ρ x := by
  set h := clipCentered μ a b f with hh
  set G := tailIntegral μ h with hG
  set W := cdfProd μ with hW
  have hhc : Continuous h := continuous_clipCentered hf
  have hhb : ∃ C, ∀ x, ‖h x‖ ≤ C := exists_bound_clipCentered hab hf
  have hIcc : Icc c e ⊆ interior (μ : Measure ℝ).support :=
    hμ.convex_interior_support.ordConnected.out hcΩ heΩ
  have huIcc : uIcc c e = Icc c e := uIcc_of_le hce
  have hGc : Continuous G := d.continuous_tailIntegral hhc hhb
  have hWc : Continuous W := d.continuous_cdfProd
  have hρc : ContinuousOn d.ρ (Icc c e) := d.continuousOn.mono hIcc
  have hWpos : ∀ x ∈ Icc c e, 0 < W x := fun x hx ↦ cdfProd_pos (hIcc hx)
  set Ξ : ℝ → ℝ := boundaryTerm μ h with hΞ
  set D : ℝ → ℝ := fun x ↦
    (2 * G x * (h x * d.ρ x) * W x - G x ^ 2 * (d.ρ x * (1 - 2 * cdf μ x))) / W x ^ 2 *
        ((1 - 2 * cdf μ x) / 2) +
      G x ^ 2 / W x * (-d.ρ x) with
    hD
  have hΞderiv : ∀ x ∈ Icc c e, HasDerivAt Ξ (D x) x := by
    intro x hx
    have hxΩ := hIcc hx
    have hGd := d.hasDerivAt_tailIntegral hhc hhb hxΩ
    have hWd := d.hasDerivAt_cdfProd hxΩ
    have hFd := d.hasDerivAt_cdf hxΩ
    have h1 : HasDerivAt (fun x ↦ G x ^ 2) (2 * G x * (h x * d.ρ x)) x := by
      have := hGd.mul hGd
      exact
        (this.congr_deriv (by ring)).congr_of_eventuallyEq
          (Filter.Eventually.of_forall fun y ↦ by show G y ^ 2 = G y * G y; ring)
    have h2 := h1.div hWd (hWpos x hx).ne'
    have h3 : HasDerivAt (fun x ↦ (1 - 2 * cdf μ x) / 2) (-d.ρ x) x := by
      have := ((hFd.const_mul 2).const_sub 1).div_const 2
      exact this.congr_deriv (by ring)
    exact h2.mul h3
  have hDcont : ContinuousOn D (Icc c e) := by
    have hF : Continuous (cdf μ) := d.continuous_cdf
    have hnum :
      ContinuousOn
        (fun x ↦ 2 * G x * (h x * d.ρ x) * W x - G x ^ 2 * (d.ρ x * (1 - 2 * cdf μ x)))
        (Icc c e) :=
      (((continuous_const.mul hGc).continuousOn.mul (hhc.continuousOn.mul hρc)).mul
            hWc.continuousOn).sub
        ((hGc.pow 2).continuousOn.mul
          (hρc.mul (continuous_const.sub (continuous_const.mul hF)).continuousOn))
    have hden : ContinuousOn (fun x ↦ W x ^ 2) (Icc c e) := (hWc.pow 2).continuousOn
    have hlin : ContinuousOn (fun x ↦ (1 - 2 * cdf μ x) / 2) (Icc c e) :=
      ((continuous_const.sub (continuous_const.mul hF)).div_const 2).continuousOn
    refine
      ContinuousOn.add ((hnum.div hden fun x hx ↦ pow_ne_zero 2 (hWpos x hx).ne').mul hlin) ?_
    exact
      ((hGc.pow 2).continuousOn.div hWc.continuousOn fun x hx ↦ (hWpos x hx).ne').mul
        hρc.neg
  -- pointwise ground-state inequality

  have hpt : ∀ x ∈ Icc c e, G x ^ 2 * d.ρ x / (4 * W x ^ 2) + D x ≤ h x ^ 2 * d.ρ x := by
    intro x hx
    have hWx := hWpos x hx
    have hWx' : W x ≠ 0 := hWx.ne'
    have hρx : 0 ≤ d.ρ x := d.nonneg x
    have hWeq : W x = cdf μ x * (1 - cdf μ x) := rfl
    have key :
      h x ^ 2 * d.ρ x - G x ^ 2 * d.ρ x / (4 * W x ^ 2) - D x =
        d.ρ x * (h x - G x * (1 - 2 * cdf μ x) / (2 * W x)) ^ 2 := by
      rw [hD]
      simp only
      field_simp
      rw [hWeq]
      ring
    have : 0 ≤ d.ρ x * (h x - G x * (1 - 2 * cdf μ x) / (2 * W x)) ^ 2 :=
      mul_nonneg hρx (sq_nonneg _)
    linarith
  have hint1 : IntervalIntegrable (fun x ↦ G x ^ 2 * d.ρ x / (4 * W x ^ 2)) volume c e := by
    apply ContinuousOn.intervalIntegrable
    rw [huIcc]
    exact
      ContinuousOn.div (by fun_prop) (by fun_prop) fun x hx ↦ by have := hWpos x hx; positivity
  have hint2 : IntervalIntegrable D volume c e := by
    apply ContinuousOn.intervalIntegrable
    rw [huIcc]
    exact hDcont
  have hint3 : IntervalIntegrable (fun x ↦ h x ^ 2 * d.ρ x) volume c e := by
    apply ContinuousOn.intervalIntegrable
    rw [huIcc]
    exact (hhc.pow 2).continuousOn.mul hρc
  have hmono := integral_mono_on hce (hint1.add hint2) hint3 hpt
  rw [integral_add hint1 hint2,
    integral_eq_sub_of_hasDerivAt (fun x hx ↦ hΞderiv x (huIcc ▸ hx)) hint2] at hmono
  have hquarter :
    ∫ x in c..e, G x ^ 2 * d.ρ x / (4 * W x ^ 2) =
      (1 / 4) * ∫ x in c..e, G x ^ 2 * d.ρ x / W x ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    refine integral_congr fun x _ ↦ ?_
    ring
  rw [hquarter] at hmono
  exact hmono

include hμ hi hab haΩ hbΩ hf in
/--
Claim A: `∫_a^b G² ρ / W² ≤ 4 ∫ h² dμ` for the centered clipped test, when `F a ≤ 1/2 ≤ F b`:
the ground-state inequality on larger intervals `[c, e] ⊆ Ω` has boundary terms controlled by
`h(a)² F c + h(b)² (1 - F e)`, which can be made arbitrarily small. -/
theorem integral_sq_div_le (hFa : cdf μ a ≤ 1 / 2) (hFb : 1 / 2 ≤ cdf μ b) :
    ∫ x in a..b, tailIntegral μ (clipCentered μ a b f) x ^ 2 * d.ρ x / cdfProd μ x ^ 2 ≤
      4 * ∫ x, clipCentered μ a b f x ^ 2 ∂(μ : Measure ℝ) := by
  set h := clipCentered μ a b f with hh
  set G := tailIntegral μ h with hG
  set W := cdfProd μ with hW
  have hhc : Continuous h := continuous_clipCentered hf
  have hhb : ∃ C, ∀ x, ‖h x‖ ≤ C := exists_bound_clipCentered hab hf
  have hI2 : Integrable (fun x ↦ h x ^ 2) (μ : Measure ℝ) :=
    integrable_of_bounded_continuous (hhc.pow 2)
      (by
        obtain ⟨C, hC⟩ := hhb
        exact
          ⟨C ^ 2, fun x ↦ by
            rw [norm_pow]
            exact pow_le_pow_left₀ (norm_nonneg _) (hC x) 2⟩)
  set V := ∫ x, h x ^ 2 ∂(μ : Measure ℝ) with hV
  have hFa0 := Probability.Line.cdf_pos_of_mem_interior_support μ haΩ
  have hFb1 := Probability.Line.cdf_lt_one_of_mem_interior_support μ hbΩ
  have hGc : Continuous G :=
    d.continuous_tailIntegral hhc
      hhb
  -- the integrand is nonnegative on `Ω`

  have hnonneg : ∀ x ∈ interior (μ : Measure ℝ).support, 0 ≤ G x ^ 2 * d.ρ x / W x ^ 2 :=
    fun x hx ↦ div_nonneg (mul_nonneg (sq_nonneg _) (d.nonneg x)) (sq_nonneg _)
  have key : ∀ ε : ℝ, 0 < ε → (1 / 4) * (∫ x in a..b, G x ^ 2 * d.ρ x / W x ^ 2) ≤ V + ε := by
    intro ε
      hε
    -- choose `c ≤ a` with `F c` small and `e ≥ b` with `1 - F e` small

    set εa : ℝ := min (cdf μ a) (ε / (4 * (h a ^ 2 + 1))) with hεa
    set εb : ℝ := min (1 - cdf μ b) (ε / (4 * (h b ^ 2 + 1))) with hεb
    have hεa0 : 0 < εa := lt_min hFa0 (by positivity)
    have hεb0 : 0 < εb := lt_min (by linarith) (by positivity)
    have hεa1 : εa < 1 :=
      lt_of_le_of_lt (min_le_left _ _)
        (Probability.Line.cdf_lt_one_of_mem_interior_support μ haΩ)
    have hεb1 : εb < 1 := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    obtain ⟨c, hc⟩ :=
      Probability.Line.exists_cdf_eq μ d.withDensity_eq d.measurable d.nonneg hεa0 hεa1
    obtain ⟨e, he⟩ :=
      Probability.Line.exists_cdf_eq μ d.withDensity_eq d.measurable d.nonneg (t := 1 - εb)
        (by linarith) (by linarith)
    have hcΩ : c ∈ interior (μ : Measure ℝ).support :=
      hμ.mem_interior_support_of_cdf hi (hc ▸ hεa0) (hc ▸ hεa1)
    have heΩ : e ∈ interior (μ : Measure ℝ).support :=
      hμ.mem_interior_support_of_cdf hi (by rw [he]; linarith) (by rw [he]; linarith)
    have hca : c ≤ a := by
      by_contra hlt
      push Not at hlt
      have := d.cdf_lt_cdf_of_mem hμ haΩ hcΩ hlt
      rw [hc] at this
      exact absurd (min_le_left _ _) (not_le.mpr this)
    have hbe : b ≤ e := by
      by_contra hlt
      push Not at hlt
      have := d.cdf_lt_cdf_of_mem hμ heΩ hbΩ hlt
      rw [he] at this
      have := min_le_left (1 - cdf μ b) (ε / (4 * (h b ^ 2 + 1)))
      linarith
    have hFc : cdf μ c ≤ 1 / 2 := by rw [hc]; exact (min_le_left _ _).trans hFa
    have hFe : 1 / 2 ≤ cdf μ e := by
      rw [he]
      have := min_le_left (1 - cdf μ b) (ε / (4 * (h b ^ 2 + 1)))
      linarith
    have hce : c ≤ e := hca.trans (hab.trans hbe)
    have hIcc : Icc c e ⊆ interior (μ : Measure ℝ).support :=
      hμ.convex_interior_support.ordConnected.out hcΩ heΩ
    have hgs :=
      d.groundState_inequality hμ hab hf hce hcΩ
        heΩ
    -- the middle integral is at most `V`

    have hmid : ∫ x in c..e, h x ^ 2 * d.ρ x ≤ V := by
      rw [integral_of_le hce, ← d.setIntegral_eq_integral_mul _ measurableSet_Ioc]
      exact
        setIntegral_le_integral hI2
          (ae_of_all _ fun x ↦ sq_nonneg _)
    -- monotonicity of the interval integral

    have hint : IntervalIntegrable (fun x ↦ G x ^ 2 * d.ρ x / W x ^ 2) volume c e := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hce]
      exact
        ContinuousOn.div ((hGc.pow 2).continuousOn.mul (d.continuousOn.mono hIcc))
          (d.continuous_cdfProd.pow 2).continuousOn fun x hx ↦
          pow_ne_zero 2 (cdfProd_pos (hIcc hx)).ne'
    have hsub :
      ∫ x in a..b, G x ^ 2 * d.ρ x / W x ^ 2 ≤ ∫ x in c..e, G x ^ 2 * d.ρ x / W x ^ 2 := by
      refine integral_mono_interval hca hab hbe ?_ hint
      rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
      exact
        ae_of_all _ fun x hx ↦
          hnonneg x
            (hIcc (Ioc_subset_Icc_self hx))
    -- boundary terms

    have hΞc : boundaryTerm μ h c ≤ ε / 4 := by
      refine (boundaryTerm_le_of_le hab hca hcΩ hFc).trans ?_
      rw [hc]
      calc
        h a ^ 2 * εa ≤ h a ^ 2 * (ε / (4 * (h a ^ 2 + 1))) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) (sq_nonneg _)
        _ ≤ ε / 4 := by
          rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith [sq_nonneg (h a), hε.le]
    have hΞe : -boundaryTerm μ h e ≤ ε / 4 := by
      refine (neg_boundaryTerm_le_of_ge hab hf hbe heΩ hFe).trans ?_
      rw [he, show 1 - (1 - εb) = εb by ring]
      calc
        h b ^ 2 * εb ≤ h b ^ 2 * (ε / (4 * (h b ^ 2 + 1))) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) (sq_nonneg _)
        _ ≤ ε / 4 := by
          rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith [sq_nonneg (h b), hε.le]
    -- assemble

    have : (1 / 4) * (∫ x in a..b, G x ^ 2 * d.ρ x / W x ^ 2) ≤ V + ε / 4 + ε / 4 := by
      linarith [hgs, hmid, hsub]
    linarith
  by_contra hlt
  push Not at hlt
  have hpos : 0 < ((1 / 4) * (∫ x in a..b, G x ^ 2 * d.ρ x / W x ^ 2) - V) / 2 := by linarith
  have := key _ hpos
  linarith

include d hμ hi hab haΩ hbΩ hf in
/-- The sharp Hardy bound for the clipped test: `Var(f_{ab}) ≤ 4 · Var(μ) · ∫ f'² dμ` when
`[a, b] ⊆ Ω` and `F a ≤ 1/2 ≤ F b`. -/
theorem variance_clip_le (hFa : cdf μ a ≤ 1 / 2) (hFb : 1 / 2 ≤ cdf μ b)
    (hE : Integrable (fun x ↦ deriv f x ^ 2) (μ : Measure ℝ)) :
    variance (clip a b f) (μ : Measure ℝ) ≤
      4 * variance id (μ : Measure ℝ) * ∫ x, deriv f x ^ 2 ∂(μ : Measure ℝ) := by
  set h := clipCentered μ a b f with hh
  set G := tailIntegral μ h with hG
  set W := cdfProd μ with hW
  set σ2 := variance id (μ : Measure ℝ) with hσ2
  set E := ∫ x, deriv f x ^ 2 ∂(μ : Measure ℝ) with hE_def
  have hhc : Continuous h := continuous_clipCentered hf
  have hhb : ∃ C, ∀ x, ‖h x‖ ≤ C := exists_bound_clipCentered hab hf
  have hIcc : Icc a b ⊆ interior (μ : Measure ℝ).support :=
    hμ.convex_interior_support.ordConnected.out haΩ hbΩ
  have huIcc : uIcc a b = Icc a b := uIcc_of_le hab
  have hGc : Continuous G := d.continuous_tailIntegral hhc hhb
  have hWc : Continuous W := d.continuous_cdfProd
  have hρc : ContinuousOn d.ρ (Icc a b) := d.continuousOn.mono hIcc
  have hf'c : Continuous (deriv f) := hf.continuous_deriv (by exact_mod_cast le_top)
  have hWpos : ∀ x ∈ Icc a b, 0 < W x := fun x hx ↦ cdfProd_pos (hIcc hx)
  have hρpos : ∀ x ∈ Icc a b, 0 < d.ρ x := fun x hx ↦
    d.pos
      (hIcc hx)
  -- the variance of the clipped test is `∫ h²`

  set V := ∫ x, h x ^ 2 ∂(μ : Measure ℝ) with hV
  have hvar : variance (clip a b f) (μ : Measure ℝ) = V := by
    rw [variance_eq_integral (clip.continuous hf.continuous).measurable.aemeasurable]
    rfl
  have hB := d.integral_sq_clipCentered_eq hμ hab haΩ hbΩ hf
  have hA :=
    d.integral_sq_div_le hμ hi hab haΩ hbΩ hf hFa
      hFb
  -- pointwise `x y ≤ x² / 8 + 2 y²`

  have hpt :
    ∀ x ∈ Icc a b,
      -(deriv f x * G x) ≤
        G x ^ 2 * d.ρ x / (8 * W x ^ 2) + 2 * deriv f x ^ 2 * W x ^ 2 / d.ρ x := by
    intro x hx
    have hw := hWpos x hx
    have hr := hρpos x hx
    rw [div_add_div _ _ (by positivity) hr.ne', le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (G x * d.ρ x + 4 * deriv f x * W x ^ 2), hw, hr]
  have hint1 : IntervalIntegrable (fun x ↦ G x ^ 2 * d.ρ x / (8 * W x ^ 2)) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [huIcc]
    exact
      ContinuousOn.div ((hGc.pow 2).continuousOn.mul hρc) (by fun_prop) fun x hx ↦ by
        have := hWpos x hx; positivity
  have hint2 : IntervalIntegrable (fun x ↦ 2 * deriv f x ^ 2 * W x ^ 2 / d.ρ x) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [huIcc]
    exact ContinuousOn.div (by fun_prop) hρc fun x hx ↦ (hρpos x hx).ne'
  have hint0 : IntervalIntegrable (fun x ↦ -(deriv f x * G x)) volume a b :=
    ((hf'c.mul hGc).neg).intervalIntegrable _ _
  have hmono := integral_mono_on hab hint0 (hint1.add hint2) hpt
  rw [intervalIntegral.integral_neg, intervalIntegral.integral_add hint1 hint2] at hmono
  have h8 :
    ∫ x in a..b, G x ^ 2 * d.ρ x / (8 * W x ^ 2) =
      (1 / 8) * ∫ x in a..b, G x ^ 2 * d.ρ x / W x ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    refine integral_congr fun x _ ↦ ?_
    ring
  -- the profile bound `W² / ρ ≤ σ² ρ`

  have hprof :
    ∀ x ∈ Icc a b, 2 * deriv f x ^ 2 * W x ^ 2 / d.ρ x ≤ 2 * σ2 * (deriv f x ^ 2 * d.ρ x) := by
    intro x hx
    have hr := hρpos x hx
    have hWx := d.cdf_mul_one_sub_cdf_le_sd_mul hμ hi (hIcc hx)
    have hW0 : 0 ≤ W x := (hWpos x hx).le
    have hsq : W x ^ 2 ≤ σ2 * d.ρ x ^ 2 := by
      have := pow_le_pow_left₀ hW0 hWx 2
      rwa [mul_pow, Real.sq_sqrt (variance_nonneg _ _)] at this
    rw [div_le_iff₀ hr]
    nlinarith [sq_nonneg (deriv f x), hsq, hr]
  have hint3 : IntervalIntegrable (fun x ↦ 2 * σ2 * (deriv f x ^ 2 * d.ρ x)) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [huIcc]
    exact continuousOn_const.mul ((hf'c.pow 2).continuousOn.mul hρc)
  have hE_ab : ∫ x in a..b, 2 * σ2 * (deriv f x ^ 2 * d.ρ x) ≤ 2 * σ2 * E := by
    rw [intervalIntegral.integral_const_mul, integral_of_le hab, ←
      d.setIntegral_eq_integral_mul _ measurableSet_Ioc]
    exact
      mul_le_mul_of_nonneg_left (setIntegral_le_integral hE (ae_of_all _ fun x ↦ sq_nonneg _))
        (mul_nonneg (by norm_num) (variance_nonneg _ _))
  have hmono2 :=
    integral_mono_on hab hint2 hint3
      hprof
  -- assemble: `V ≤ V / 2 + 2 σ² E`

  have : V ≤ (1 / 8) * (4 * V) + 2 * σ2 * E := by
    have h1 : V = -∫ x in a..b, deriv f x * G x := hB
    have h2 : (1 / 8) * ∫ x in a..b, G x ^ 2 * d.ρ x / W x ^ 2 ≤ (1 / 8) * (4 * V) :=
      mul_le_mul_of_nonneg_left hA (by norm_num)
    linarith [hmono, h8, hmono2, hE_ab]
  rw [hvar]
  linarith

end Clipped

end LineDensity

end FunctionalInequalities.KLS
