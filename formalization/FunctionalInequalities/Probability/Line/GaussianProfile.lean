import FunctionalInequalities.Probability.Line.Cdf
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.Support

/-!
# The standard Gaussian density in quantile coordinates

The CDF maps the real line bijectively onto `(0,1)`. Its inverse defines the actual
Gaussian profile, not an abstract function satisfying an assumed differential equation.
The profile is extended by zero outside `(0,1)`; differential statements are interior
statements. These scalar facts are inputs to, not a proof of, the BGL heat estimate.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ContDiff

namespace FunctionalInequalities.Probability.Line.GaussianProfile

/-- Standard Gaussian density. -/
def density : ℝ → ℝ := gaussianPDFReal 0 1

/-- Standard Gaussian distribution function. -/
def distribution : ℝ → ℝ := cdf (ofMeasure (gaussianReal 0 1))

private theorem law_density : (gaussianReal 0 1) =
    volume.withDensity (fun x ↦ ENNReal.ofReal (density x)) := by
  exact gaussianReal_of_var_ne_zero 0 one_ne_zero

theorem density_pos (x : ℝ) : 0 < density x :=
  gaussianPDFReal_pos 0 1 x one_ne_zero

theorem continuous_density : Continuous density := by
  unfold density gaussianPDFReal
  fun_prop

theorem hasDerivAt_density (x : ℝ) : HasDerivAt density (-x * density x) x := by
  have harg : HasDerivAt (fun y : ℝ ↦ -y ^ 2 / 2) (-x) x := by
    convert (((hasDerivAt_id x).pow 2).neg.div_const 2) using 1 <;> first | rfl | (simp; ring)
  have h := harg.exp.const_mul (Real.sqrt (2 * Real.pi))⁻¹
  change HasDerivAt (fun y : ℝ ↦ (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-y ^ 2 / 2))
    ((Real.sqrt (2 * Real.pi))⁻¹ * (Real.exp (-x ^ 2 / 2) * -x)) x at h
  simpa only [density, gaussianPDFReal_def, NNReal.coe_one, mul_one, one_mul, sub_zero,
    mul_neg, neg_mul, mul_comm, mul_left_comm, mul_assoc] using h

theorem hasDerivAt_distribution (x : ℝ) : HasDerivAt distribution (density x) x :=
  hasDerivAt_cdf (ofMeasure (gaussianReal 0 1)) law_density continuous_density.measurable
    (fun x ↦ (density_pos x).le) continuous_density.continuousAt

theorem strictMono_distribution : StrictMono distribution :=
  strictMono_of_deriv_pos fun x ↦ by
    rw [(hasDerivAt_distribution x).deriv]
    exact density_pos x

theorem distribution_mem (x : ℝ) : distribution x ∈ Ioo (0 : ℝ) 1 := by
  constructor
  · exact lt_of_le_of_lt (cdf_nonneg _ (x - 1))
      (strictMono_distribution (by linarith : x - 1 < x))
  · exact lt_of_lt_of_le (strictMono_distribution (by linarith : x < x + 1))
      (cdf_le_one _ (x + 1))

theorem range_distribution : range distribution = Ioo (0 : ℝ) 1 := by
  ext p
  constructor
  · rintro ⟨x, rfl⟩
    exact distribution_mem x
  · intro hp
    exact exists_cdf_eq (ofMeasure (gaussianReal 0 1)) law_density continuous_density.measurable
      (fun x ↦ (density_pos x).le) hp.1 hp.2

private theorem distribution_openEmbedding : IsOpenEmbedding distribution := by
  refine ⟨strictMono_distribution.isEmbedding_of_ordConnected ?_, ?_⟩
  · rw [range_distribution]
    exact ordConnected_Ioo
  · rw [range_distribution]
    exact isOpen_Ioo

private def distributionHomeomorph : OpenPartialHomeomorph ℝ ℝ :=
  distribution_openEmbedding.toOpenPartialHomeomorph distribution

/-- Inverse of the Gaussian CDF on `(0,1)`. Values outside its range are unspecified. -/
def quantile : ℝ → ℝ := distributionHomeomorph.symm

theorem quantile_distribution (x : ℝ) : quantile (distribution x) = x :=
  distribution_openEmbedding.toOpenPartialHomeomorph_left_inv distribution

theorem distribution_quantile {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    distribution (quantile p) = p :=
  distribution_openEmbedding.toOpenPartialHomeomorph_right_inv distribution
    (range_distribution.symm ▸ hp)

theorem hasDerivAt_quantile {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt quantile (density (quantile p))⁻¹ p := by
  apply distributionHomeomorph.hasDerivAt_symm
  · simpa only [distributionHomeomorph,
      IsOpenEmbedding.toOpenPartialHomeomorph_target, range_distribution] using hp
  · exact (density_pos _).ne'
  · exact hasDerivAt_distribution _

/-- The Gaussian profile `I(p) = density (quantile p)`, extended by zero off `(0,1)`. -/
def profile (p : ℝ) : ℝ := if p ∈ Ioo (0 : ℝ) 1 then density (quantile p) else 0

theorem profile_eq {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    profile p = density (quantile p) := if_pos hp

@[simp] theorem profile_zero : profile 0 = 0 := by simp [profile]
@[simp] theorem profile_one : profile 1 = 0 := by simp [profile]

theorem profile_distribution (x : ℝ) : profile (distribution x) = density x := by
  rw [profile_eq (distribution_mem x), quantile_distribution]

theorem profile_nonneg (p : ℝ) : 0 ≤ profile p := by
  unfold profile
  split_ifs
  · exact (density_pos _).le
  · exact le_rfl

theorem profile_pos {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) : 0 < profile p := by
  rw [profile_eq hp]
  exact density_pos _

/-- The exact scalar upper bound needed for the sharp heat-gradient coefficient. -/
theorem profile_le (p : ℝ) : profile p ≤ (Real.sqrt (2 * Real.pi))⁻¹ := by
  have hc : 0 ≤ (Real.sqrt (2 * Real.pi))⁻¹ := by positivity
  unfold profile
  split_ifs
  · unfold density gaussianPDFReal
    simp only [NNReal.coe_one, mul_one, sub_zero]
    exact mul_le_of_le_one_right hc (Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg (quantile p)]))
  · exact hc

theorem hasDerivAt_profile {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt profile (-quantile p) p := by
  have h := (hasDerivAt_density (quantile p)).comp p (hasDerivAt_quantile hp)
  have hn := (density_pos (quantile p)).ne'
  have hd : -quantile p * density (quantile p) * (density (quantile p))⁻¹ =
      -quantile p := by field_simp
  rw [hd] at h
  apply h.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hp] with q hq
  exact profile_eq hq

theorem deriv_profile {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    deriv profile p = -quantile p := (hasDerivAt_profile hp).deriv

/-- The Gaussian profile ODE, with no ODE assumption and no endpoint differentiability claim. -/
theorem hasDerivAt_deriv_profile {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (deriv profile) (-(profile p)⁻¹) p := by
  rw [profile_eq hp]
  apply (hasDerivAt_quantile hp).neg.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hp] with q hq
  exact deriv_profile hq

theorem profile_mul_second_deriv {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    profile p * deriv (deriv profile) p = -1 := by
  rw [(hasDerivAt_deriv_profile hp).deriv]
  field_simp [(profile_pos hp).ne']

/-- The scalar bound is attained (at the distribution value of zero). -/
theorem profile_distribution_zero :
    profile (distribution 0) = (Real.sqrt (2 * Real.pi))⁻¹ := by
  rw [profile_distribution]
  simp [density, gaussianPDFReal]

theorem tendsto_density_atTop : Tendsto density atTop (𝓝 0) := by
  have harg : Tendsto (fun x : ℝ ↦ -x ^ 2 / 2) atTop atBot :=
    Tendsto.atBot_div_const (by norm_num : (0 : ℝ) < 2)
      (tendsto_neg_atTop_atBot.comp (tendsto_pow_atTop two_ne_zero))
  simpa only [density, gaussianPDFReal_def, NNReal.coe_one, mul_one, sub_zero,
    mul_zero, Function.comp_def] using
    (Real.tendsto_exp_atBot.comp harg).const_mul (Real.sqrt (2 * Real.pi))⁻¹

theorem tendsto_density_atBot : Tendsto density atBot (𝓝 0) := by
  have h := tendsto_density_atTop.comp tendsto_neg_atBot_atTop
  simpa only [density, gaussianPDFReal_def, NNReal.coe_one, mul_one, sub_zero,
    neg_sq, Function.comp_def] using h

theorem tendsto_quantile_zero :
    Tendsto quantile (𝓝[Ioo (0 : ℝ) 1] 0) atBot := by
  apply tendsto_atBot.mpr
  intro b
  have hb : ∀ᶠ p in 𝓝[Ioo (0 : ℝ) 1] 0, p < distribution b :=
    (eventually_lt_nhds (distribution_mem b).1).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hb] with p hp hpb
  apply strictMono_distribution.le_iff_le.mp
  rw [distribution_quantile hp]
  exact hpb.le

theorem tendsto_quantile_one :
    Tendsto quantile (𝓝[Ioo (0 : ℝ) 1] 1) atTop := by
  apply tendsto_atTop.mpr
  intro b
  have hb : ∀ᶠ p in 𝓝[Ioo (0 : ℝ) 1] 1, distribution b < p :=
    (eventually_gt_nhds (distribution_mem b).2).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hb] with p hp hbp
  apply strictMono_distribution.le_iff_le.mp
  rw [distribution_quantile hp]
  exact hbp.le

theorem tendsto_profile_zero :
    Tendsto profile (𝓝[Ioo (0 : ℝ) 1] 0) (𝓝 0) := by
  apply (tendsto_density_atBot.comp tendsto_quantile_zero).congr'
  filter_upwards [self_mem_nhdsWithin] with p hp
  exact (profile_eq hp).symm

theorem tendsto_profile_one :
    Tendsto profile (𝓝[Ioo (0 : ℝ) 1] 1) (𝓝 0) := by
  apply (tendsto_density_atTop.comp tendsto_quantile_one).congr'
  filter_upwards [self_mem_nhdsWithin] with p hp
  exact (profile_eq hp).symm

theorem continuousOn_profile : ContinuousOn profile (Icc (0 : ℝ) 1) := by
  intro p hp
  have hset : Icc (0 : ℝ) 1 = insert 0 (insert 1 (Ioo 0 1)) := by
    ext x
    simp only [mem_Icc, mem_insert_iff, mem_Ioo]
    constructor
    · rintro ⟨h0, h1⟩
      rcases h0.eq_or_lt with h | h
      · exact Or.inl h.symm
      · rcases h1.eq_or_lt with h1 | h1
        · exact Or.inr (Or.inl h1)
        · exact Or.inr (Or.inr ⟨h, h1⟩)
    · rintro (rfl | rfl | ⟨h0, h1⟩) <;> constructor <;> linarith
  rw [hset, continuousWithinAt_insert, continuousWithinAt_insert]
  rcases eq_endpoints_or_mem_Ioo_of_mem_Icc hp with rfl | rfl | hp'
  · simpa only [ContinuousWithinAt, profile_zero] using tendsto_profile_zero
  · simpa only [ContinuousWithinAt, profile_one] using tendsto_profile_one
  · exact (hasDerivAt_profile hp').continuousAt.continuousWithinAt

/-- The zero extension of the Gaussian profile is continuous, including both endpoints. -/
theorem continuous_profile : Continuous profile := by
  have h : Continuous (fun p : ℝ ↦ profile (max 0 (min 1 p))) :=
    continuousOn_profile.comp_continuous (by fun_prop) (fun p ↦
      ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩)
  convert h using 1
  ext p
  by_cases hp0 : p ≤ 0
  · rw [min_eq_right (by linarith : p ≤ 1), max_eq_left hp0, profile_zero]
    simp [profile, not_lt.mpr hp0]
  · by_cases hp1 : 1 ≤ p
    · rw [min_eq_left hp1, max_eq_right (by norm_num : (0 : ℝ) ≤ 1), profile_one]
      simp [profile, not_lt.mpr hp1]
    · rw [min_eq_right (le_of_not_ge hp1), max_eq_right (le_of_not_ge hp0)]

theorem strictConcaveOn_profile : StrictConcaveOn ℝ (Icc (0 : ℝ) 1) profile := by
  apply strictConcaveOn_of_deriv2_neg (convex_Icc 0 1) continuousOn_profile
  intro p hp
  rw [interior_Icc] at hp
  change deriv (deriv profile) p < 0
  rw [(hasDerivAt_deriv_profile hp).deriv]
  exact neg_neg_of_pos (inv_pos.mpr (profile_pos hp))

/-- Smoothness is asserted only on the interior of the probability interval. -/
theorem contDiff_density : ContDiff ℝ ∞ density := by
  unfold density gaussianPDFReal
  fun_prop

theorem contDiff_distribution : ContDiff ℝ ∞ distribution := by
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨fun x ↦ (hasDerivAt_distribution x).differentiableAt, ?_⟩
  have h : deriv distribution = density := funext fun x ↦ (hasDerivAt_distribution x).deriv
  rw [h]
  exact contDiff_density

theorem contDiffAt_quantile {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ ∞ quantile p := by
  apply distributionHomeomorph.contDiffAt_symm_deriv (density_pos _).ne'
  · simpa only [distributionHomeomorph,
      IsOpenEmbedding.toOpenPartialHomeomorph_target, range_distribution] using hp
  · exact hasDerivAt_distribution _
  · exact contDiff_distribution.contDiffAt

theorem contDiffAt_profile {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ ∞ profile p := by
  apply (contDiff_density.contDiffAt.comp p (contDiffAt_quantile hp)).congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hp] with q hq
  exact profile_eq hq

theorem contDiffOn_profile : ContDiffOn ℝ ∞ profile (Ioo (0 : ℝ) 1) :=
  fun _ hp ↦ (contDiffAt_profile hp).contDiffWithinAt

@[simp] theorem density_neg (x : ℝ) : density (-x) = density x := by
  simp [density, gaussianPDFReal]

theorem distribution_neg (x : ℝ) : distribution (-x) = 1 - distribution x := by
  let f : ℝ → ℝ := fun y ↦ distribution y + distribution (-y)
  have hd : ∀ y, HasDerivAt f 0 y := by
    intro y
    have h := (hasDerivAt_distribution y).add
      ((hasDerivAt_distribution (-y)).comp y (hasDerivAt_id y).neg)
    convert h using 1 <;> first | rfl | simp [density_neg]
  have hc : ∀ y, f y = f x := fun y ↦ is_const_of_deriv_eq_zero
    (fun y ↦ (hd y).differentiableAt) (fun y ↦ (hd y).deriv) y x
  have ht : Tendsto f atTop (𝓝 (1 + 0)) :=
    (tendsto_cdf_atTop (ofMeasure (gaussianReal 0 1))).add
      ((tendsto_cdf_atBot (ofMeasure (gaussianReal 0 1))).comp tendsto_neg_atTop_atBot)
  have hconst : Tendsto f atTop (𝓝 (f x)) := by
    exact tendsto_const_nhds.congr (fun y ↦ (hc y).symm)
  have heq := tendsto_nhds_unique ht hconst
  dsimp [f] at heq
  linarith

@[simp] theorem distribution_zero : distribution 0 = 1 / 2 := by
  have h := distribution_neg 0
  simp only [neg_zero] at h
  linarith

theorem quantile_one_sub {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    quantile (1 - p) = -quantile p := by
  apply strictMono_distribution.injective
  rw [distribution_quantile (show 1 - p ∈ Ioo (0 : ℝ) 1 by constructor <;> linarith [hp.1, hp.2]),
    distribution_neg, distribution_quantile hp]

theorem profile_one_sub {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) :
    profile (1 - p) = profile p := by
  rcases eq_endpoints_or_mem_Ioo_of_mem_Icc hp with rfl | rfl | hp'
  · simp
  · simp
  · rw [profile_eq (show 1 - p ∈ Ioo (0 : ℝ) 1 by constructor <;> linarith [hp'.1, hp'.2]),
      quantile_one_sub hp', density_neg, profile_eq hp']

theorem profile_half : profile (1 / 2) = (Real.sqrt (2 * Real.pi))⁻¹ := by
  rw [← distribution_zero]
  exact profile_distribution_zero

/-- Shifted profile used on ranges bounded away from the upper endpoint. -/
def shifted (ε x : ℝ) : ℝ := profile (x + ε) - profile ε

@[simp] theorem shifted_zero (ε : ℝ) : shifted ε 0 = 0 := by simp [shifted]

theorem contDiffAt_shifted {ε x : ℝ} (hx : x + ε ∈ Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ ∞ (shifted ε) x :=
  ((contDiffAt_profile hx).comp x (contDiffAt_id.add contDiffAt_const)).sub contDiffAt_const

theorem hasDerivAt_shifted {ε x : ℝ} (hx : x + ε ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (shifted ε) (-quantile (x + ε)) x := by
  have h := ((hasDerivAt_profile hx).comp x ((hasDerivAt_id x).add_const ε)).sub_const (profile ε)
  convert h using 1 <;> first | rfl | simp

theorem hasDerivAt_deriv_shifted {ε x : ℝ} (hx : x + ε ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (deriv (shifted ε)) (-(profile (x + ε))⁻¹) x := by
  have h := ((hasDerivAt_quantile hx).comp x ((hasDerivAt_id x).add_const ε)).neg
  rw [← profile_eq hx, mul_one] at h
  apply h.congr_of_eventuallyEq
  have hn : ∀ᶠ y in 𝓝 x, y + ε ∈ Ioo (0 : ℝ) 1 :=
    (continuous_id.add continuous_const).continuousAt.eventually (isOpen_Ioo.mem_nhds hx)
  filter_upwards [hn] with y hy
  exact (hasDerivAt_shifted hy).deriv

/-- On this range the shift remains inside `(0,1)` with a positive margin. -/
theorem shifted_argument_mem {ε x : ℝ} (hε : 0 < ε)
    (hx : x ∈ Icc (0 : ℝ) (1 - 2 * ε)) : x + ε ∈ Ioo (0 : ℝ) 1 := by
  constructor <;> linarith [hx.1, hx.2]

theorem shifted_nonneg {ε x : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 2)
    (hx : x ∈ Icc (0 : ℝ) (1 - 2 * ε)) : 0 ≤ shifted ε x := by
  have he : ε ∈ Icc (0 : ℝ) 1 := ⟨hε.le, by linarith⟩
  have he' : 1 - ε ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hseg : x + ε ∈ segment ℝ ε (1 - ε) := by
    rw [segment_eq_Icc (by linarith : ε ≤ 1 - ε)]
    constructor <;> linarith [hx.1, hx.2]
  have h := strictConcaveOn_profile.concaveOn.ge_on_segment he he' hseg
  rw [profile_one_sub he, min_self] at h
  exact sub_nonneg.mpr h

theorem shifted_le {ε x : ℝ} : shifted ε x ≤ (Real.sqrt (2 * Real.pi))⁻¹ :=
  sub_le_iff_le_add.mpr ((profile_le _).trans (le_add_of_nonneg_right (profile_nonneg ε)))

/-- The regularization retains the exact reciprocal second derivative. -/
theorem shifted_mul_neg_second_deriv {ε x : ℝ} (hx : x + ε ∈ Ioo (0 : ℝ) 1) :
    shifted ε x * (-deriv (deriv (shifted ε)) x) =
      1 - profile ε / profile (x + ε) := by
  rw [(hasDerivAt_deriv_shifted hx).deriv]
  unfold shifted
  field_simp [(profile_pos hx).ne']

theorem exists_shifted_derivative_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ Icc (0 : ℝ) (1 - 2 * ε),
      |deriv (shifted ε) x| ≤ C ∧ |deriv (deriv (shifted ε)) x| ≤ C := by
  have hq : ContinuousOn (fun x ↦ quantile (x + ε)) (Icc (0 : ℝ) (1 - 2 * ε)) := by
    intro x hx
    exact ((hasDerivAt_quantile (shifted_argument_mem hε hx)).continuousAt.comp (f := fun y : ℝ ↦ y + ε)
      (show ContinuousAt (fun y : ℝ ↦ y + ε) x from continuousAt_id.add_const ε)).continuousWithinAt
  have hr : ContinuousOn (fun x ↦ (profile (x + ε))⁻¹) (Icc (0 : ℝ) (1 - 2 * ε)) := by
    intro x hx
    have hi := shifted_argument_mem hε hx
    exact (((hasDerivAt_profile hi).continuousAt.comp (f := fun y : ℝ ↦ y + ε)
      (show ContinuousAt (fun y : ℝ ↦ y + ε) x from continuousAt_id.add_const ε)).inv₀ (profile_pos hi).ne').continuousWithinAt
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hq
  obtain ⟨D, hD⟩ := isCompact_Icc.exists_bound_of_continuousOn hr
  refine ⟨max (max C D) 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro x hx
  rw [(hasDerivAt_shifted (shifted_argument_mem hε hx)).deriv,
    (hasDerivAt_deriv_shifted (shifted_argument_mem hε hx)).deriv, abs_neg, abs_neg]
  exact ⟨(hC x hx).trans ((le_max_left _ _).trans (le_max_left _ _)),
    (hD x hx).trans ((le_max_right _ _).trans (le_max_left _ _))⟩

theorem exists_lipschitzOnWith_shifted {ε : ℝ} (hε : 0 < ε) :
    ∃ K : NNReal, LipschitzOnWith K (shifted ε) (Icc (0 : ℝ) (1 - 2 * ε)) := by
  obtain ⟨C, hC, hb⟩ := exists_shifted_derivative_bound hε
  refine ⟨⟨C, hC.le⟩, Convex.lipschitzOnWith_of_nnnorm_deriv_le
    (fun x hx ↦ (hasDerivAt_shifted (shifted_argument_mem hε hx)).differentiableAt)
    (fun x hx ↦ ?_) (convex_Icc _ _)⟩
  exact_mod_cast (hb x hx).1

/-- The shifted profiles converge to the genuine profile for interior initial values. -/
theorem tendsto_shifted {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun ε ↦ shifted ε x) (𝓝[>] 0) (𝓝 (profile x)) := by
  have hz : Tendsto profile (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [nhdsWithin_Ioo_eq_nhdsGT zero_lt_one] using tendsto_profile_zero
  have ht : Tendsto (fun ε : ℝ ↦ profile (x + ε)) (𝓝[>] 0) (𝓝 (profile x)) := by
    apply (hasDerivAt_profile hx).continuousAt.tendsto.comp
    simpa using (tendsto_const_nhds.add (tendsto_id.mono_left nhdsWithin_le_nhds :
      Tendsto (fun ε : ℝ ↦ ε) (𝓝[>] 0) (𝓝 0)))
  simpa only [shifted, sub_zero] using ht.sub hz

theorem tendsto_shifted_of_mem_Ico {x : ℝ} (hx : x ∈ Ico (0 : ℝ) 1) :
    Tendsto (fun ε ↦ shifted ε x) (𝓝[>] 0) (𝓝 (profile x)) := by
  rcases hx.1.eq_or_lt with h | h
  · subst x
    simpa only [shifted_zero, profile_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ ↦ (0 : ℝ)) (𝓝[>] 0) (𝓝 0))
  · exact tendsto_shifted ⟨h, hx.2⟩

/-- A uniform bound, including values outside the interval where derivatives are used. -/
theorem abs_shifted_le (ε x : ℝ) : |shifted ε x| ≤ (Real.sqrt (2 * Real.pi))⁻¹ := by
  rw [shifted, abs_sub_le_iff]
  constructor <;> linarith [profile_nonneg (x + ε), profile_nonneg ε,
    profile_le (x + ε), profile_le ε]

/-- Interior smooth data stay smooth under the shifted profile, without a global extension. -/
theorem contDiff_shifted_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {ε : ℝ} (hf : ContDiff ℝ ∞ f)
    (hrange : ∀ x, f x + ε ∈ Ioo (0 : ℝ) 1) :
    ContDiff ℝ ∞ (fun x ↦ shifted ε (f x)) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  exact (contDiffAt_shifted (hrange x)).comp x hf.contDiffAt

theorem hasCompactSupport_shifted_comp {E : Type*} [TopologicalSpace E]
    {f : E → ℝ} (hf : HasCompactSupport f) (ε : ℝ) :
    HasCompactSupport (fun x ↦ shifted ε (f x)) :=
  hf.comp_left (shifted_zero ε)

/-- A globally smooth extension with bounded first and second derivatives, agreeing with
`shifted ε` on a neighborhood of the entire admissible interval. This supplies scalar
inputs for a closed-generator chain rule; that operator theorem is a separate obligation. -/
theorem exists_smooth_shifted_extension {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1 / 2) :
    ∃ Φ : ℝ → ℝ, ContDiff ℝ ∞ Φ ∧ Φ 0 = 0 ∧
      (∀ x ∈ Icc (0 : ℝ) (1 - 2 * ε), Φ =ᶠ[𝓝 x] shifted ε) ∧
      ∃ C : ℝ, 0 < C ∧ ∀ x, |Φ x| ≤ C ∧ |deriv Φ x| ≤ C ∧
        |deriv (deriv Φ) x| ≤ C := by
  let b : ContDiffBump (1 / 2 : ℝ) :=
    ⟨1 / 2 - ε / 2, 1 / 2 - ε / 4, by linarith, by linarith⟩
  have hb : tsupport b ⊆ Ioo (0 : ℝ) 1 := by
    intro x hx
    rw [b.tsupport_eq, Metric.mem_closedBall, Real.dist_eq, abs_le] at hx
    dsimp [b] at hx
    constructor <;> linarith [hx.1, hx.2]
  let g : ℝ → ℝ := fun x ↦ b x * profile x
  have hg : ContDiff ℝ ∞ g := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ Ioo (0 : ℝ) 1
    · exact b.contDiff.contDiffAt.mul (contDiffAt_profile hx)
    · have hz : b =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp (fun h ↦ hx (hb h))
      apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [hz] with y hy
      simp [g, hy]
  have hgc : HasCompactSupport g := b.hasCompactSupport.mul_right
  have hge : ∀ x ∈ Icc (0 : ℝ) (1 - 2 * ε),
      (fun y ↦ g (y + ε) - profile ε) =ᶠ[𝓝 x] shifted ε := by
    intro x hx
    have hball : x + ε ∈ Metric.ball (1 / 2 : ℝ) b.rIn := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      dsimp [b]
      constructor <;> linarith [hx.1, hx.2]
    have he := b.eventuallyEq_one_of_mem_ball hball
    have ht : Tendsto (fun y : ℝ ↦ y + ε) (𝓝 x) (𝓝 (x + ε)) :=
      (continuousAt_id.add_const ε).tendsto
    filter_upwards [ht.eventually he] with y hy
    simp [g, hy, shifted]
  have hΦ : ContDiff ℝ ∞ (fun y ↦ g (y + ε) - profile ε) :=
    (hg.comp (contDiff_id.add contDiff_const)).sub contDiff_const
  have hg₁ : ContDiff ℝ ∞ (deriv g) := (contDiff_infty_iff_deriv.mp hg).2
  have hg₂ : ContDiff ℝ ∞ (deriv (deriv g)) := (contDiff_infty_iff_deriv.mp hg₁).2
  obtain ⟨C₀, hC₀⟩ := hgc.exists_bound_of_continuous hg.continuous
  obtain ⟨C₁, hC₁⟩ := hgc.deriv.exists_bound_of_continuous hg₁.continuous
  obtain ⟨C₂, hC₂⟩ := hgc.deriv.deriv.exists_bound_of_continuous
    hg₂.continuous
  have hd : deriv (fun y ↦ g (y + ε) - profile ε) = fun y ↦ deriv g (y + ε) := by
    funext y
    exact (by simpa using (((hg.differentiable (by simp) (y + ε)).hasDerivAt.comp y
      ((hasDerivAt_id y).add_const ε)).sub_const (profile ε)).deriv)
  have hdd : deriv (fun y ↦ deriv g (y + ε)) = fun y ↦ deriv (deriv g) (y + ε) := by
    funext y
    have hy : HasDerivAt (fun z : ℝ ↦ deriv g (z + ε)) (deriv (deriv g) (y + ε)) y := by
      convert ((hg₁.differentiable (by simp) (y + ε)).hasDerivAt.comp y
        ((hasDerivAt_id y).add_const ε)) using 1 <;> first | rfl | simp
    exact hy.deriv
  refine ⟨_, hΦ, ?_, hge, max (max (C₀ + |profile ε|) C₁) (max C₂ 1),
    lt_of_lt_of_le zero_lt_one ((le_max_right _ _).trans (le_max_right _ _)), ?_⟩
  · rw [(hge 0 ⟨le_rfl, by linarith⟩).eq_of_nhds, shifted_zero]
  · intro x
    rw [hd, hdd]
    refine ⟨?_, ?_, ?_⟩
    · apply (abs_sub _ _).trans
      apply LE.le.trans _ ((le_max_left _ _).trans (le_max_left _ _))
      simpa only [Real.norm_eq_abs] using add_le_add (hC₀ (x + ε)) (le_refl |profile ε|)
    · exact (hC₁ (x + ε)).trans ((le_max_right _ _).trans (le_max_left _ _))
    · exact (hC₂ (x + ε)).trans ((le_max_left _ _).trans (le_max_right _ _))

end FunctionalInequalities.Probability.Line.GaussianProfile
