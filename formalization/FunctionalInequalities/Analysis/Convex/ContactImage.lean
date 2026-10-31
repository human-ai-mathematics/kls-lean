module

public import FunctionalInequalities.Analysis.MetricCover
public import Mathlib.MeasureTheory.Measure.Regular
public import FunctionalInequalities.Analysis.Convex.Subgradient.Basic
public import FunctionalInequalities.Analysis.BakryEmery.Calculus
public import FunctionalInequalities.Analysis.BakryEmery.Hessian.Compact
public import Mathlib.Topology.Compactness.Lindelof
public import FunctionalInequalities.Analysis.Sard.Equidimensional

/-!
# Null images of residual contact sets

Supporting contacts of a quadratic perturbation of a convex C¹ function give a
contraction relative to its gradient. A genuine finite local Alexandrov-measure
upper bound then implies that every null contact subset has null residual-gradient
image. The quadratic theorem is complemented by a genuine locally C2 positive-Hessian
comparison reference, with locally generated constants and countable contained-ball
exhaustion. These are supports
for Letwin arXiv:2607.24164v1 Lemma 2.2 via the nonlinear W²,p route, not a
Dirichlet existence or W²,p theorem.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace

namespace FunctionalInequalities.Analysis

/-- A genuine finite open-set Alexandrov upper bound gives null gradient images
of arbitrary null subsets of the open domain. No N property is supplied. -/
theorem volume_gradient_image_eq_zero_of_alexandrov_upper
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {u : E → ℝ} (hconv : ConvexOn ℝ Set.univ u) (hu : ContDiff ℝ 1 u)
    {Ω : Set E} (hΩ : IsOpen Ω) {C : ℝ} (hC : 0 ≤ C)
    (hMA : ∀ G : Set E, IsOpen G → G ⊆ Ω →
      (volume : Measure E) (subgradientImage u G) ≤
        ENNReal.ofReal C * (volume : Measure E) G) :
    ∀ S : Set E, S ⊆ Ω → (volume : Measure E) S = 0 →
      (volume : Measure E) (gradient u '' S) = 0 := by
  have hdiff : Differentiable ℝ u :=
    hu.differentiable one_ne_zero

  have hgrad : ∀ x y : E, u x + ⟪gradient u x, y - x⟫ ≤ u y := by
    intro x y
    have hh := gradient_le_increment hconv x (y - x) (hdiff x)
    rw [add_sub_cancel] at hh
    linarith
  have hgradient_null : ∀ {S : Set E}, S ⊆ Ω → volume S = 0 →
      volume (gradient u '' S) = 0 := by
    intro S hSΩ hSzero
    have hbound : ∀ ε : ℝ≥0∞, 0 < ε → volume (gradient u '' S) ≤ ENNReal.ofReal C * ε := by
      intro ε hε
      obtain ⟨G, hSG, hG, hGlt⟩ := S.exists_isOpen_lt_of_lt (μ := (volume : Measure E)) ε
        (by simpa only [hSzero] using hε)
      have himage : gradient u '' S ⊆ subgradientImage u (G ∩ Ω) := by
        rintro z ⟨x, hx, rfl⟩
        exact ⟨x, ⟨hSG hx, hSΩ hx⟩, hgrad x⟩
      exact (measure_mono himage).trans ((hMA (G ∩ Ω) (hG.inter hΩ) inter_subset_right).trans
        (mul_le_mul le_rfl ((measure_mono inter_subset_left).trans hGlt.le) bot_le bot_le))
    have hden : 0 < C + 1 := by positivity
    apply le_antisymm ?_ bot_le
    apply ENNReal.le_of_forall_pos_le_add
    intro ε hε _
    have hεR : 0 < (ε : ℝ) := hε
    calc
      volume (gradient u '' S) ≤ ENNReal.ofReal C * ENNReal.ofReal ((ε : ℝ) / (C + 1)) :=
        hbound _ (ENNReal.ofReal_pos.mpr (div_pos hεR hden))
      _ = ENNReal.ofReal (C * ((ε : ℝ) / (C + 1))) := (ENNReal.ofReal_mul hC).symm
      _ ≤ ENNReal.ofReal (ε : ℝ) := ENNReal.ofReal_le_ofReal (by
        rw [← mul_div_assoc]
        apply (div_le_iff₀ hden).mpr
        nlinarith [ε.coe_nonneg])
      _ = 0 + (ε : ℝ≥0∞) := by simp

  exact fun S hS hzero => hgradient_null hS hzero

/-- A reference genuinely C2 on an open neighbourhood of compact convex K
with actual positive Hessian gives the residual-relative gradient bound.
The constant precedes arbitrary unknown u,t and contacts; no global extension
or regularity/Hessian bound of u is an input. Includes dimension zero. -/
theorem exists_residual_gradient_bound_of_posDef_referenceOn {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {v : E → ℝ} {U : Set E} (hU : IsOpen U)
    (hv : ContDiffOn ℝ 2 v U) {K : Set E} (hKU : K ⊆ U) (hK : IsCompact K) (hKc : Convex ℝ K)
    (hPD : ∀ x ∈ K, ∀ z : E, z ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ v x z z) :
    ∃ C : ℝ≥0,
      0 < C ∧
        ∀ (u : E → ℝ) (t : ℝ),
          0 < t →
            ∀ Γ : Set E,
              Γ ⊆ K →
                (∀ x ∈ Γ,
                    ∀ y ∈ K,
                      u x - t * v x + ⟪gradient u x - t • gradient v x, y - x⟫ ≤
                        u y - t * v y) →
                  ∀ x ∈ Γ,
                    ∀ y ∈ Γ,
                      ‖(gradient u x - t • gradient v x) - (gradient u y - t • gradient v y)‖ ≤
                        (C : ℝ) * ‖gradient u x - gradient u y‖ := by
  obtain ⟨κ, L, hκ, hL, hbounds⟩ :=
    BakryEmery.exists_uniform_gradient_bounds_of_posDef_hessianOn hU hv hKU hK hKc hPD
  let C : ℝ≥0 := ⟨1 + L / κ, by positivity⟩
  refine ⟨C, by change 0 < (1 + L / κ : ℝ); positivity, ?_⟩
  intro u t ht Γ hΓ hcontact x hx y hy
  let a : E := gradient u x - gradient u y
  let b : E := (gradient u x - t • gradient v x) - (gradient u y - t • gradient v y)
  let d : E := x - y
  let h : E := gradient v x - gradient v y
  have hab : a = b + t • h := by dsimp [a, b, h]; module
  have hmono : 0 ≤ ⟪b, d⟫ := by
    have hxy := hcontact x hx y (hΓ hy)
    have hyx := hcontact y hy x (hΓ hx)
    have hid :
      ⟪b, d⟫ =
        -(⟪gradient u x - t • gradient v x, y - x⟫ +
            ⟪gradient u y - t • gradient v y, x - y⟫) := by
      dsimp [b, d]
      simp only [inner_sub_left, inner_sub_right]
      ring
    rw [hid]
    linarith
  obtain ⟨hlo, hup⟩ := hbounds x (hΓ hx) y (hΓ hy)
  change κ * ‖d‖ ^ 2 ≤ ⟪h, d⟫ at hlo
  change ‖h‖ ≤ L * ‖d‖ at hup
  have hnorm : t * κ * ‖d‖ ≤ ‖a‖ := by
    by_cases hd : d = 0
    · simp [hd]
    have hdpos : 0 < ‖d‖ := norm_pos_iff.mpr hd
    have heq : ⟪a, d⟫ = ⟪b, d⟫ + t * ⟪h, d⟫ := by rw [hab, inner_add_left, real_inner_smul_left]
    have hh : t * κ * ‖d‖ * ‖d‖ ≤ ‖a‖ * ‖d‖ := by
      nlinarith [real_inner_le_norm a d, mul_le_mul_of_nonneg_left hlo ht.le]
    exact le_of_mul_le_mul_right hh hdpos
  have hcalc : t * L * ‖d‖ ≤ (L / κ) * ‖a‖ := by
    calc
      t * L * ‖d‖ = (L / κ) * (t * κ * ‖d‖) := by field_simp [hκ.ne']
      _ ≤ (L / κ) * ‖a‖ := mul_le_mul_of_nonneg_left hnorm (by positivity)
  have hbeq : b = a - t • h := by rw [hab]; abel
  change ‖b‖ ≤ (1 + L / κ) * ‖a‖
  calc
    ‖b‖ ≤ ‖a‖ + ‖t • h‖ := by rw [hbeq]; exact norm_sub_le _ _
    _ = ‖a‖ + t * ‖h‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    _ ≤ ‖a‖ + t * (L * ‖d‖) := add_le_add le_rfl (mul_le_mul_of_nonneg_left hup ht.le)
    _ ≤ ‖a‖ + (L / κ) * ‖a‖ := by nlinarith only [hcalc]
    _ = (1 + L / κ) * ‖a‖ := by ring

/-- The local residual relative-gradient bound is produced from actual reference C2/PD.
Its constant precedes u, t and the actual contact set. No regularity of u is
required for this contact algebra. -/
theorem exists_residual_gradient_bound_of_posDef_reference {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {v : E → ℝ} (hv : ContDiff ℝ 2 v)
    {K : Set E} (hK : IsCompact K) (hKc : Convex ℝ K)
    (hPD : ∀ x ∈ K, ∀ z : E, z ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ v x z z) :
    ∃ C : ℝ≥0,
      0 < C ∧
        ∀ (u : E → ℝ) (t : ℝ),
          0 < t →
            ∀ Γ : Set E,
              Γ ⊆ K →
                (∀ x ∈ Γ,
                    ∀ y ∈ K,
                      u x - t * v x + ⟪gradient u x - t • gradient v x, y - x⟫ ≤
                        u y - t * v y) →
                  ∀ x ∈ Γ,
                    ∀ y ∈ Γ,
                      ‖(gradient u x - t • gradient v x) - (gradient u y - t • gradient v y)‖ ≤
                        (C : ℝ) * ‖gradient u x - gradient u y‖ := by
  exact
    exists_residual_gradient_bound_of_posDef_referenceOn isOpen_univ hv.contDiffOn
      (subset_univ K) hK hKc hPD

/-- For a convex C¹ function with an actual finite open-set MA upper bound,
any volume-null subset of actual contacts of `u - t ‖x‖²/2` has null image under
`∇u - t Id`. Neither the contact set nor its null subset must be measurable.
The gradient's null-image property and the residual contraction are proved here.
The statement includes zero-dimensional spaces. -/
theorem volume_image_residual_eq_zero_of_quadratic_contacts
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {u : E → ℝ}
    (hconv : ConvexOn ℝ Set.univ u)
    (hu : ContDiff ℝ 1 u)
    {Ω : Set E} (hΩ : IsOpen Ω)
    {C : ℝ} (hC : 0 ≤ C)
    (hMA :
      ∀ G : Set E, IsOpen G → G ⊆ Ω →
        (volume : Measure E) (subgradientImage u G) ≤
          ENNReal.ofReal C * (volume : Measure E) G)
    {t : ℝ} (ht : 0 < t)
    {Γ : Set E}
    (hΓΩ : Γ ⊆ Ω)
    (hcontact :
      ∀ x ∈ Γ, ∀ y ∈ Ω,
        u x - (t / 2) * ‖x‖ ^ 2 +
            ⟪gradient u x - t • x, y - x⟫
          ≤
        u y - (t / 2) * ‖y‖ ^ 2) :
    ∀ N : Set E, N ⊆ Γ → (volume : Measure E) N = 0 →
      (volume : Measure E)
        ((fun x : E => gradient u x - t • x) '' N) = 0 := by
  classical

  have hgradient_null : ∀ {S : Set E}, S ⊆ Ω → volume S = 0 →
      volume (gradient u '' S) = 0 := by
    intro S hS hzero
    exact volume_gradient_image_eq_zero_of_alexandrov_upper hconv hu hΩ hC hMA S hS hzero

  let p : E → E := fun x => gradient u x - t • x

  have hmono :
      ∀ {x y : E}, x ∈ Γ → y ∈ Γ →
        0 ≤ ⟪p x - p y, x - y⟫ := by
    intro x y hx hy

    have hxy :
        u x - (t / 2) * ‖x‖ ^ 2 +
              ⟪p x, y - x⟫
          ≤
        u y - (t / 2) * ‖y‖ ^ 2 := by
      simpa [p] using hcontact x hx y (hΓΩ hy)

    have hyx :
        u y - (t / 2) * ‖y‖ ^ 2 +
              ⟪p y, x - y⟫
          ≤
        u x - (t / 2) * ‖x‖ ^ 2 := by
      simpa [p] using hcontact y hy x (hΓΩ hx)

    have hsum :
        ⟪p x, y - x⟫ + ⟪p y, x - y⟫ ≤ 0 := by
      linarith

    have hrewrite :
        ⟪p x - p y, x - y⟫ =
          -(⟪p x, y - x⟫ + ⟪p y, x - y⟫) := by
      simp only [inner_sub_left, inner_sub_right]
      ring

    rw [hrewrite]
    linarith

  /- The residual contraction on Γ. -/
  have hcontract :
      ∀ {x y : E}, x ∈ Γ → y ∈ Γ →
        ‖p x - p y‖ ≤ ‖gradient u x - gradient u y‖ := by
    intro x y hx hy

    let a : E := gradient u x - gradient u y
    let b : E := p x - p y
    let dxy : E := x - y

    have hab : a = b + t • dxy := by
      dsimp [a, b, dxy, p]
      module

    have hmon :
        0 ≤ ⟪b, dxy⟫ := by
      simpa [b, dxy] using hmono hx hy

    have hmon' :
        0 ≤ ⟪dxy, b⟫ := by
      simpa [real_inner_comm] using hmon

    have hinner :
        ⟪a, b⟫ = ‖b‖ ^ 2 + t * ⟪dxy, b⟫ := by
      rw [hab, inner_add_left, real_inner_smul_left,
        real_inner_self_eq_norm_sq]

    have hcauchy :
        ⟪a, b⟫ ≤ ‖a‖ * ‖b‖ :=
      real_inner_le_norm a b

    have hsq :
        ‖b‖ ^ 2 ≤ ‖a‖ * ‖b‖ := by
      nlinarith [hinner, hcauchy, hmon', ht]

    by_cases hbzero : b = 0
    · change ‖b‖ ≤ ‖a‖
      rw [hbzero, norm_zero]
      exact norm_nonneg _
    · have hbnorm : 0 < ‖b‖ :=
        norm_pos_iff.mpr hbzero
      have hmul :
          ‖b‖ * ‖b‖ ≤ ‖a‖ * ‖b‖ := by
        simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using hsq
      have hnorm :
          ‖b‖ ≤ ‖a‖ :=
        le_of_mul_le_mul_right hmul hbnorm
      simpa [a, b] using hnorm

  have hinj : Set.InjOn (gradient u) Γ := by
    intro x hx y hy hxy
    have hh := hcontract hx hy
    rw [hxy, sub_self, norm_zero] at hh
    have hp : p x = p y := sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hh (norm_nonneg _)))
    dsimp only [p] at hp
    rw [hxy] at hp
    have hs : t • x = t • y := sub_right_inj.mp hp
    have hz : t • (x - y) = 0 := by rw [smul_sub, hs, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_left ht.ne')

  intro N hNΓ hNzero

  let S : Set E := gradient u '' Γ

  let F : E → E :=
    fun q =>
      if hq : q ∈ S then
        p (Classical.choose hq)
      else
        0

  have hF :
      ∀ x ∈ Γ, F (gradient u x) = p x := by
    intro x hx
    have hmem : gradient u x ∈ S := by
      exact ⟨x, hx, rfl⟩

    dsimp [F]
    rw [dite_eq_left hmem]

    have hspec :=
      Classical.choose_spec hmem

    have hchoose :
        Classical.choose hmem = x := by
      apply hinj hspec.1 hx
      exact hspec.2

    rw [hchoose]

  have hFL :
      LipschitzOnWith (1 : NNReal) F S := by
    apply LipschitzOnWith.of_dist_le_mul
    intro q hq r hr

    rcases hq with ⟨x, hx, rfl⟩
    rcases hr with ⟨y, hy, rfl⟩

    rw [hF x hx, hF y hy]

    have hxy := hcontract hx hy
    simpa [dist_eq_norm] using hxy

  have hgradN :
      (volume : Measure E) (gradient u '' N) = 0 :=
    hgradient_null (hNΓ.trans hΓΩ) hNzero

  have himage :
      (volume : Measure E) (F '' (gradient u '' N)) = 0 :=
    volume_image_eq_zero_of_lipschitzOnWith (hFL.mono (image_mono hNΓ)) hgradN

  have hresidual :
      (fun x : E => gradient u x - t • x) '' N =
        F '' (gradient u '' N) := by
    ext q
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨gradient u x, ⟨x, hx, rfl⟩, ?_⟩
      exact hF x (hNΓ hx)
    · rintro ⟨q, ⟨x, hx, rfl⟩, rfl⟩
      refine ⟨x, hx, ?_⟩
      exact (hF x (hNΓ hx)).symm

  rw [hresidual]
  exact himage

/-- Local continuity suffices: the support intersection is closed in the actual
open-domain subtype, hence its image is Borel in the ambient space. -/
theorem measurableSet_support_contactsOn {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] {Ω : Set E} (hΩ : IsOpen Ω)
    {w : E → ℝ} {p : E → E} (hw : ContinuousOn w Ω) (hp : ContinuousOn p Ω) :
    MeasurableSet {x | x ∈ Ω ∧ ∀ y ∈ Ω, w x + ⟪p x, y - x⟫ ≤ w y} := by
  let C : Set Ω := {x | ∀ y ∈ Ω, w x + ⟪p x, y - (x : E)⟫ ≤ w y}
  have hwr : Continuous (fun x : Ω => w x) := continuousOn_iff_continuous_domRestrict.mp hw
  have hpr : Continuous (fun x : Ω => p x) := continuousOn_iff_continuous_domRestrict.mp hp
  have hC : IsClosed C := by
    have heq : C = ⋂ y ∈ Ω, {x : Ω | w x + ⟪p x, y - (x : E)⟫ ≤ w y} := by
      ext x
      simp only [C, mem_ofPred_eq, mem_iInter]
    rw [heq]
    apply isClosed_iInter
    intro y
    apply isClosed_iInter
    intro _hy
    exact
      isClosed_le (hwr.add (hpr.inner (continuous_const.sub continuous_subtype_val)))
        continuous_const
  obtain ⟨T, hT, hTC⟩ := isClosed_induced_iff.mp hC
  have heq : {x | x ∈ Ω ∧ ∀ y ∈ Ω, w x + ⟪p x, y - x⟫ ≤ w y} = Ω ∩ T := by
    ext x
    constructor
    · rintro ⟨hx, h⟩
      refine ⟨hx, ?_⟩
      have hc : (⟨x, hx⟩ : Ω) ∈ C := h
      rw [← hTC] at hc
      exact hc
    · rintro ⟨hx, ht⟩
      refine ⟨hx, ?_⟩
      have hc : (⟨x, hx⟩ : Ω) ∈ C := by
        rw [← hTC]
        exact ht
      exact hc
  rw [heq]
  exact hΩ.measurableSet.inter hT.measurableSet


/-- The global continuous-support statement is the actual local-continuity
specialization, retaining its original generic public interface. -/
theorem measurableSet_support_contacts {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] {w : E → ℝ} {p : E → E}
    (hw : Continuous w) (hp : Continuous p) {Ω : Set E} (hΩ : IsOpen Ω) :
    MeasurableSet {x | x ∈ Ω ∧ ∀ y ∈ Ω,
      w x + ⟪p x, y - x⟫ ≤ w y} := by
  exact measurableSet_support_contactsOn hΩ hw.continuousOn hp.continuousOn

/-- The actual full quadratic contact set is Borel; measurability is derived
from C1 continuity, not supplied with a desired measure bound. -/
theorem measurableSet_quadratic_contacts {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {u : E → ℝ} (hu : ContDiff ℝ 1 u)
    {Ω : Set E} (hΩ : IsOpen Ω) (t : ℝ) :
    MeasurableSet {x | x ∈ Ω ∧ ∀ y ∈ Ω,
      u x - (t / 2) * ‖x‖ ^ 2 + ⟪gradient u x - t • x, y - x⟫ ≤
        u y - (t / 2) * ‖y‖ ^ 2} := by
  exact measurableSet_support_contacts
    (hu.continuous.sub (continuous_const.mul (continuous_norm.pow 2)))
    ((BakryEmery.continuous_gradient hu).sub (continuous_const.smul continuous_id)) hΩ

/-- A genuine local C2 reference with actual positive Hessian on open Ω
maps arbitrary null subsets of actual residual contacts to null residual-gradient
images. Compact reference constants, a fibre factor and a countable contained-ball
cover are produced. Unknown u is only convex C1 with a real finite open-set MA
upper bound. No global reference extension, domain-exterior reference convexity,
N/factor/cover/unknown-u Hessian or W2p input. Dimension zero is included. -/
theorem volume_image_residual_eq_zero_of_posDef_referenceOn {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {u v : E → ℝ} (hconv : ConvexOn ℝ Set.univ u) (hu : ContDiff ℝ 1 u) {Ω : Set E}
    (hΩ : IsOpen Ω) (hv : ContDiffOn ℝ 2 v Ω)
    (hPD : ∀ x ∈ Ω, ∀ z : E, z ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ v x z z) {C : ℝ}
    (hC : 0 ≤ C)
    (hMA :
      ∀ G : Set E,
        IsOpen G → G ⊆ Ω → volume (subgradientImage u G) ≤ ENNReal.ofReal C * volume G)
    {t : ℝ} (ht : 0 < t) {Γ : Set E} (hΓ : Γ ⊆ Ω)
    (hcontact :
      ∀ x ∈ Γ,
        ∀ y ∈ Ω, u x - t * v x + ⟪gradient u x - t • gradient v x, y - x⟫ ≤ u y - t * v y) :
    ∀ N : Set E,
      N ⊆ Γ → volume N = 0 → volume ((fun x : E => gradient u x - t • gradient v x) '' N) = 0 := by
  classical
  have hgradient_null : ∀ {S : Set E}, S ⊆ Ω → volume S = 0 → volume (gradient u '' S) = 0 := by
    intro S hS hSzero
    exact volume_gradient_image_eq_zero_of_alexandrov_upper hconv hu hΩ hC hMA S hS hSzero
  let p : E → E := fun x => gradient u x - t • gradient v x
  have hlocal :
    ∀ (c : E) (R : ℝ),
      closedBall c R ⊆ Ω →
        ∀ A : Set E, A ⊆ Γ ∩ closedBall c R → volume A = 0 → volume (p '' A) = 0 := by
    intro c R hKsub A hA hAzero
    let K : Set E := closedBall c R
    have hKcompact : IsCompact K := by simpa [K] using (isCompact_closedBall c R)
    have hKconv : Convex ℝ K := by simpa [K] using (convex_closedBall c R)
    have hPDK : ∀ x ∈ K, ∀ z : E, z ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ v x z z := by
      intro x hx z hz
      exact hPD x (hKsub (by simpa [K] using hx)) z hz
    obtain ⟨L, _hLpos, hLips⟩ :=
      exists_residual_gradient_bound_of_posDef_referenceOn hΩ hv hKsub hKcompact hKconv hPDK
    have hA' : A ⊆ Γ ∩ K := by
      intro x hx
      exact ⟨hA hx |>.1, by simpa [K] using (hA hx).2⟩
    have hLips' :
      ∀ x ∈ Γ ∩ K, ∀ y ∈ Γ ∩ K, ‖p x - p y‖ ≤ (L : ℝ) * ‖gradient u x - gradient u y‖ := by
      have hbound :=
        hLips u t ht (Γ ∩ K) inter_subset_right
          (by
            intro x hx y hy
            exact hcontact x hx.1 y (hKsub (by simpa [K] using hy)))
      intro x hx y hy
      simpa [p] using hbound x hx y hy
    have hfiber :
      ∀ {x y : E}, x ∈ Γ ∩ K → y ∈ Γ ∩ K → gradient u x = gradient u y → p x = p y := by
      intro x y hx hy hxy
      have hh := hLips' x hx y hy
      rw [hxy] at hh
      have hz : ‖p x - p y‖ ≤ 0 := by simpa using hh
      exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hz (norm_nonneg _)))
    let S : Set E := gradient u '' (Γ ∩ K)
    let F : E → E := fun q => if hq : q ∈ S then p (Classical.choose hq) else 0
    have hF : ∀ x ∈ Γ ∩ K, F (gradient u x) = p x := by
      intro x hx
      have hmem : gradient u x ∈ S := by exact ⟨x, hx, rfl⟩
      dsimp [F]
      rw [dite_eq_left hmem]
      have hspec := Classical.choose_spec hmem
      exact hfiber hspec.1 hx hspec.2
    have hFL : LipschitzOnWith L F S := by
      apply LipschitzOnWith.of_dist_le_mul
      intro q hq r hr
      rcases hq with ⟨x, hx, rfl⟩
      rcases hr with ⟨y, hy, rfl⟩
      rw [hF x hx, hF y hy]
      have hxy := hLips' x hx y hy
      simpa [dist_eq_norm] using hxy
    have hgradA : volume (gradient u '' A) = 0 := by
      apply hgradient_null
      · exact hA'.trans (inter_subset_left.trans hΓ)
      · exact hAzero
    have hFimage : volume (F '' (gradient u '' A)) = 0 :=
      volume_image_eq_zero_of_lipschitzOnWith (hFL.mono (image_mono hA')) hgradA
    have himage : p '' A = F '' (gradient u '' A) := by
      ext q
      constructor
      · rintro ⟨x, hx, rfl⟩
        refine ⟨gradient u x, ⟨x, hx, rfl⟩, ?_⟩
        exact hF x (hA' hx)
      · rintro ⟨q, ⟨x, hx, rfl⟩, rfl⟩
        refine ⟨x, hx, ?_⟩
        exact (hF x (hA' hx)).symm
    rw [himage]
    exact hFimage
  obtain ⟨R, r, hRpos, hRsub, hrcountable, hcover⟩ := exists_countable_buffered_ball_cover hΩ
  let : Countable { x : Ω // x ∈ r } := hrcountable.to_subtype
  intro N hNΓ hNzero
  change volume (p '' N) = 0
  have hNsub : N ⊆ ⋃ i : { x : Ω // x ∈ r }, N ∩ closedBall (i.val : E) (R i.val) := by
    intro z hz
    have hzΩ : z ∈ Ω := hΓ (hNΓ hz)
    rcases mem_iUnion.mp (hcover hzΩ) with ⟨x, hx⟩
    rcases mem_iUnion.mp hx with ⟨hxr, hzb⟩
    exact
      mem_iUnion.2
        ⟨⟨x, hxr⟩, hz, ball_subset_closedBall (ball_subset_ball (by linarith [hRpos x]) hzb)⟩
  have himagesub :
    p '' N ⊆ ⋃ i : { x : Ω // x ∈ r }, p '' (N ∩ closedBall (i.val : E) (R i.val)) := by
    rintro q ⟨z, hz, rfl⟩
    rcases mem_iUnion.mp (hNsub hz) with ⟨i, hi⟩
    exact mem_iUnion.2 ⟨i, z, hi, rfl⟩
  have hpieces :
    ∀ i : { x : Ω // x ∈ r }, volume (p '' (N ∩ closedBall (i.val : E) (R i.val))) = 0 := by
    intro i
    apply hlocal (i.val : E) (R i.val) (hRsub i.val)
    · intro z hz
      exact ⟨hNΓ hz.1, hz.2⟩
    · exact measure_mono_null inter_subset_left hNzero
  have hunion :
    volume (⋃ i : { x : Ω // x ∈ r }, p '' (N ∩ closedBall (i.val : E) (R i.val))) = 0 :=
    measure_iUnion_null hpieces
  apply le_antisymm ?_ bot_le
  calc
    volume (p '' N) ≤
        volume (⋃ i : { x : Ω // x ∈ r }, p '' (N ∩ closedBall (i.val : E) (R i.val))) :=
      measure_mono himagesub
    _ = 0 := hunion

/-- For a genuine globally C2 reference with positive Hessian on an open
set, arbitrary null subsets of actual residual contacts have null residual-
gradient image. The unknown convex potential is only C1 with an actual finite
open-set MA upper bound. Local reference bounds, fibre factor and a countable
contained-ball cover are constructed, not assumed. Includes dimension zero.
This given-reference result supplies neither reference existence nor W2p. -/
theorem volume_image_residual_eq_zero_of_posDef_reference
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {u v : E → ℝ} (hconv : ConvexOn ℝ Set.univ u) (hu : ContDiff ℝ 1 u)
    (hv : ContDiff ℝ 2 v)
    {Ω : Set E} (hΩ : IsOpen Ω)
    (hPD : ∀ x ∈ Ω, ∀ z : E, z ≠ 0 →
      0 < bilinearIteratedFDerivTwo ℝ v x z z)
    {C : ℝ} (hC : 0 ≤ C)
    (hMA : ∀ G : Set E, IsOpen G → G ⊆ Ω →
      volume (subgradientImage u G) ≤ ENNReal.ofReal C * volume G)
    {t : ℝ} (ht : 0 < t) {Γ : Set E} (hΓ : Γ ⊆ Ω)
    (hcontact : ∀ x ∈ Γ, ∀ y ∈ Ω,
      u x - t * v x + ⟪gradient u x - t • gradient v x, y - x⟫ ≤
        u y - t * v y) :
    ∀ N : Set E, N ⊆ Γ → volume N = 0 →
      volume ((fun x : E => gradient u x - t • gradient v x) '' N) = 0 := by
  exact volume_image_residual_eq_zero_of_posDef_referenceOn hconv hu hΩ hv.contDiffOn
    hPD hC hMA ht hΓ hcontact

end FunctionalInequalities.Analysis
