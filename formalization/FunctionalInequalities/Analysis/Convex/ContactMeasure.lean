module

public import FunctionalInequalities.Analysis.Convex.Quadratic
public import FunctionalInequalities.Analysis.Jacobian
public import FunctionalInequalities.Analysis.Convex.ContactImage
public import FunctionalInequalities.Analysis.Convex.Alexandrov.Comparison
public import FunctionalInequalities.Analysis.Convex.Viscosity.Equation
public import FunctionalInequalities.Analysis.Convex.Viscosity.Pointwise
public import FunctionalInequalities.Analysis.Convex.Viscosity.Touching
public import FunctionalInequalities.Analysis.Matrix.DeterminantInequalities
public import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Residual contact image measures

The actual local MA equation produces a genuine gradient derivative and quadratic
expansion with one matrix. At actual contacts its determinant is controlled, and
Jacobian bounds the good image; the proved null-image theorem removes the bad
remainder. This supports Letwin arXiv:2607.24164v1 Lemma 2.2 via BB1207.6128v1
Theorem 2.24(ii). The reference is given and C2 only on the working open domain, with actual
positive Hessian and unit MA there. One interface uses global convexity and the
global subgradient MA measure; another uses only interior strict convexity and
the domain-relative subgradient MA measure. Their actual matrix producers share
one Jacobian and good/bad decomposition. The former retains nonconvex open domains. No
Dirichlet/Pogorelov existence or W²,p theorem is asserted.
A given-reference compact-interior volume gain specializes to the unit-ball
quadratic model; actual general reference existence remains separate.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Metric
open FunctionalInequalities.Probability.Stein
open scoped ENNReal NNReal RealInnerProductSpace Topology Pointwise

/-! Contact/quadratic determinant supports for Letwin arXiv:2607.24164v1
Lemma 2.2 via BB arXiv:1207.6128v1 Theorem 2.24(ii). They give pointwise
and a.e. contact-point control, not a contact-image measure estimate. -/

namespace FunctionalInequalities.Analysis

open MeasureTheory

/-- An actual local supporting affine function forces a quadratic expansion's
matrix to be PSD. The expanded function itself need not be convex or C2. -/
theorem posSemidef_of_contact_expansion {n : ℕ}
    {w : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian)
    {g p : EuclideanSpace ℝ (Fin n)}
    (hexp : ∀ ε > 0, ∀ᶠ y in 𝓝 x,
      |w y - quadraticAt A x g (w x) y| ≤ ε * ‖y - x‖ ^ 2)
    (hsupport : ∀ᶠ y in 𝓝 x, w x + ⟪p, y - x⟫ ≤ w y) : A.PosSemidef := by
  apply posSemidef_of_positive_shifts hA
  intro t ht
  have hs : (A + t • 1).IsHermitian :=
    hA.add (Matrix.isHermitian_one.smul (IsSelfAdjoint.all t))
  have hconv := convexOn_quadraticAt (Matrix.PosSemidef.zero :
    (0 : Matrix (Fin n) (Fin n) ℝ).PosSemidef) x p (w x)
  have heq : quadraticAt (0 : Matrix (Fin n) (Fin n) ℝ) x p (w x) x =
      quadraticAt (A + t • 1) x g (w x) x := by simp [quadraticAt]
  have hupper : ∀ᶠ y in 𝓝 x,
      quadraticAt (0 : Matrix (Fin n) (Fin n) ℝ) x p (w x) y ≤
      quadraticAt (A + t • 1) x g (w x) y := by
    filter_upwards [hexp (t / 2) (by positivity), hsupport] with y hy hsup
    rw [quadraticAt_shift]
    have hyu := (abs_le.mp hy).2
    simpa only [quadraticAt, map_zero, LinearMap.zero_apply, inner_zero_right,
      mul_zero, add_zero] using (show w x + ⟪p, y - x⟫ ≤
        quadraticAt A x g (w x) y + t / 2 * ‖y - x‖ ^ 2 by linarith)
  have hh := posSemidef_hessianMatrix_of_upper_touch hconv
    (contDiff_quadraticAt _ _ _ _).contDiffAt heq hupper
  rwa [hessianMatrix_quadraticAt hs] at hh

/-- Residual expansion and the PSD conclusion are derived from actual contacts
and the two second-order expansions; neither residual PSD nor its determinant
bound is an input. No contact MA measure conclusion is asserted. -/
theorem det_residual_le_of_contact_expansions {n : ℕ} (hn : 0 < n)
    {u v : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    {U B : Matrix (Fin n) (Fin n) ℝ} (hU : U.IsHermitian) (hB : B.PosDef)
    (hdetB : B.det = 1) {g q p : EuclideanSpace ℝ (Fin n)}
    (hu : ∀ η > 0, ∀ᶠ y in 𝓝 x,
      |u y - quadraticAt U x g (u x) y| ≤ η * ‖y - x‖ ^ 2)
    (hv : ∀ η > 0, ∀ᶠ y in 𝓝 x,
      |v y - quadraticAt B x q (v x) y| ≤ η * ‖y - x‖ ^ 2)
    {δ ε : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (hε : 0 ≤ ε)
    (hdetU : U.det ≤ (1 + ε) ^ n)
    (hsupport : ∀ᶠ y in 𝓝 x,
      u x - (1 - δ) * v x + ⟪p, y - x⟫ ≤ u y - (1 - δ) * v y) :
    (U - (1 - δ) • B).PosSemidef ∧
      (U - (1 - δ) • B).det ≤ (ε + δ) ^ n := by
  let t : ℝ := 1 - δ
  have ht : 0 < t := by dsimp [t]; linarith
  let w := fun y => u y - t * v y
  have hres : (U - t • B).IsHermitian :=
    hU.sub (hB.isHermitian.smul (IsSelfAdjoint.all t))
  have hquad (y : EuclideanSpace ℝ (Fin n)) :
      quadraticAt (U - t • B) x (g - t • q) (w x) y =
      quadraticAt U x g (u x) y - t * quadraticAt B x q (v x) y := by
    dsimp [quadraticAt, w]
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
      inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right]
    ring
  have hexp : ∀ η > 0, ∀ᶠ y in 𝓝 x,
      |w y - quadraticAt (U - t • B) x (g - t • q) (w x) y| ≤ η * ‖y - x‖ ^ 2 := by
    intro η hη
    have hden : 0 < 1 + t := by positivity
    filter_upwards [hu (η / (1 + t)) (div_pos hη hden),
      hv (η / (1 + t)) (div_pos hη hden)] with y hyu hyv
    rw [hquad]
    have hid : w y - (quadraticAt U x g (u x) y - t * quadraticAt B x q (v x) y) =
        (u y - quadraticAt U x g (u x) y) - t * (v y - quadraticAt B x q (v x) y) := by
      dsimp [w]; ring
    rw [hid]
    calc
      _ ≤ |u y - quadraticAt U x g (u x) y| +
          |t * (v y - quadraticAt B x q (v x) y)| := by
        simpa only [sub_zero, zero_sub, abs_neg] using
          abs_sub_le (u y - quadraticAt U x g (u x) y) 0
            (t * (v y - quadraticAt B x q (v x) y))
      _ = |u y - quadraticAt U x g (u x) y| +
          t * |v y - quadraticAt B x q (v x) y| := by rw [abs_mul, abs_of_pos ht]
      _ ≤ η / (1 + t) * ‖y - x‖ ^ 2 + t * (η / (1 + t) * ‖y - x‖ ^ 2) :=
        add_le_add hyu (mul_le_mul_of_nonneg_left hyv ht.le)
      _ = η * ‖y - x‖ ^ 2 := by field_simp
  have hPSD := posSemidef_of_contact_expansion hres hexp hsupport
  refine ⟨hPSD, ?_⟩
  apply det_le_pow_of_det_add_smul_le hn hPSD hB hdetB hδ hδ1 hε
  simpa only [t, sub_add_cancel] using hdetU


/-- Actual local Alexandrov equations supply the quadratic matrices almost
everywhere; every genuine residual supporting contact there satisfies the exact
pointwise determinant bound. The reference is given with unit MA density.
This is not a contact-gradient-image or Monge–Ampère measure estimate. -/
theorem ae_det_residual_le_on_contact_of_alexandrov_density {n : ℕ} (hn : 0 < n)
    {u v f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ConvexOn ℝ univ u) (hv : ConvexOn ℝ univ v)
    {Ω : Set (EuclideanSpace ℝ (Fin n))} (hΩ : IsOpen Ω)
    (hf : ContinuousOn f Ω) (hfpos : ∀ x ∈ Ω, 0 < f x)
    (hMAu : ∀ G : Set (EuclideanSpace ℝ (Fin n)), IsOpen G → G ⊆ Ω →
      volume (subgradientImage u G) = ∫⁻ y in G, ENNReal.ofReal (f y))
    (hMAv : ∀ G : Set (EuclideanSpace ℝ (Fin n)), IsOpen G → G ⊆ Ω →
      volume (subgradientImage v G) = volume G)
    {δ ε : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (hε : 0 ≤ ε)
    (hupper : ∀ x ∈ Ω, f x ≤ (1 + ε) ^ n) :
    ∀ᵐ x ∂(volume.restrict Ω),
      ∃ U B : Matrix (Fin n) (Fin n) ℝ,
        U.PosDef ∧ U.det = f x ∧ B.PosDef ∧ B.det = 1 ∧
        ∃ g q : EuclideanSpace ℝ (Fin n),
          (∀ η > 0, ∀ᶠ y in 𝓝 x, |u y - quadraticAt U x g (u x) y| ≤ η * ‖y - x‖ ^ 2) ∧
          (∀ η > 0, ∀ᶠ y in 𝓝 x, |v y - quadraticAt B x q (v x) y| ≤ η * ‖y - x‖ ^ 2) ∧
          ∀ p : EuclideanSpace ℝ (Fin n),
            (∀ᶠ y in 𝓝 x, u x - (1 - δ) * v x + ⟪p, y - x⟫ ≤ u y - (1 - δ) * v y) →
            (U - (1 - δ) • B).PosSemidef ∧
              (U - (1 - δ) • B).det ≤ (ε + δ) ^ n := by
  filter_upwards [ae_restrict_of_ae (ae_exists_quadraticAt_expansion hu),
    ae_restrict_of_ae (ae_exists_quadraticAt_expansion hv),
    ae_restrict_mem hΩ.measurableSet] with x hxu hxv hx
  obtain ⟨U, hU, g, hgu⟩ := hxu
  obtain ⟨B, hB, q, hqv⟩ := hxv
  obtain ⟨hUP, hUd⟩ := posDef_and_det_eq_of_quadratic_expansion hu hΩ hMAu hx
    (hf.continuousAt (hΩ.mem_nhds hx)) (hfpos x hx) hU hgu
  have hMAone : ∀ G : Set (EuclideanSpace ℝ (Fin n)), IsOpen G → G ⊆ Ω →
      volume (subgradientImage v G) = ∫⁻ _y in G, ENNReal.ofReal (1 : ℝ) := by
    intro G hG hGO
    simpa using hMAv G hG hGO
  obtain ⟨hBP, hBd⟩ := posDef_and_det_eq_of_quadratic_expansion hv hΩ hMAone hx
    continuousAt_const (by norm_num : (0 : ℝ) < 1) hB hqv
  refine ⟨U, B, hUP, hUd, hBP, hBd, g, q, hgu, hqv, ?_⟩
  intro p hp
  exact det_residual_le_of_contact_expansions hn hU hBP hBd hgu hqv hδ hδ1 hε
    (hUd.trans_le (hupper x hx)) hp

end FunctionalInequalities.Analysis

namespace FunctionalInequalities.Analysis

private def GradientWitness
    {n : ℕ} (w f : (EuclideanSpace ℝ (Fin n)) → ℝ) (x : (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∃ A : Matrix (Fin n) (Fin n) ℝ,
    A.IsHermitian ∧
    A.PosDef ∧
    A.det = f x ∧
    HasFDerivAt (gradient w)
      (Matrix.toEuclideanLin A).toContinuousLinearMap x ∧
    ∀ η > 0, ∀ᶠ y in 𝓝 x,
      |w y - quadraticAt A x (gradient w x) (w x) y| ≤
        η * ‖y - x‖ ^ 2

private theorem residual_image_bound_of_ae_data
    {n : ℕ} (hn : 0 < n)
    {u v f : (EuclideanSpace ℝ (Fin n)) → ℝ}
    (hconv : ConvexOn ℝ univ u)
    (hu : ContDiff ℝ 1 u)
    {Ω : Set ((EuclideanSpace ℝ (Fin n)))} (hΩ : IsOpen Ω)
    (hv : ContDiffOn ℝ 2 v Ω)
    (hPDv : ∀ x ∈ Ω, ∀ z : (EuclideanSpace ℝ (Fin n)), z ≠ 0 →
      0 < bilinearIteratedFDerivTwo ℝ v x z z)
    (hMA :
      ∀ G : Set ((EuclideanSpace ℝ (Fin n))), IsOpen G → G ⊆ Ω →
        volume (subgradientImage u G) =
          ∫⁻ y in G, ENNReal.ofReal (f y))
    {ε δ : ℝ} (hε : 0 ≤ ε) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hfupper : ∀ x ∈ Ω, f x ≤ (1 + ε) ^ n)
    {Γ : Set ((EuclideanSpace ℝ (Fin n)))} (hΓ : MeasurableSet Γ) (hΓΩ : Γ ⊆ Ω)
    (hcontact :
      ∀ x ∈ Γ, ∀ y ∈ Ω,
        u x - (1 - δ) * v x +
            ⟪gradient u x - (1 - δ) • gradient v x, y - x⟫
          ≤
        u y - (1 - δ) * v y)
    (hdata :
      ∀ᵐ x ∂(volume.restrict Ω),
        GradientWitness u f x ∧
        GradientWitness v (fun _ => (1 : ℝ)) x) :
    volume
        ((fun x : (EuclideanSpace ℝ (Fin n)) =>
          gradient u x - (1 - δ) • gradient v x) '' Γ) ≤
      ENNReal.ofReal ((ε + δ) ^ n) * volume Γ := by
  classical
  let E := (EuclideanSpace ℝ (Fin n))
  let t : ℝ := 1 - δ
  let p : E → E :=
    fun x => gradient u x - t • gradient v x
  let K : ℝ := (ε + δ) ^ n

  have ht : 0 < t := by
    dsimp [t]
    linarith

  have hMAupper :
      ∀ G : Set E, IsOpen G → G ⊆ Ω →
        volume (subgradientImage u G) ≤
          ENNReal.ofReal ((1 + ε) ^ n) * volume G := by
    intro G hG hGΩ
    rw [hMA G hG hGΩ]
    calc
      (∫⁻ y in G, ENNReal.ofReal (f y)) ≤
          ∫⁻ _y in G, ENNReal.ofReal ((1 + ε) ^ n) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem hG.measurableSet] with y hy
        exact ENNReal.ofReal_le_ofReal (hfupper y (hGΩ hy))
      _ = ENNReal.ofReal ((1 + ε) ^ n) * volume G := by
        simp

  have hAE : ∀ᵐ x ∂(volume.restrict Γ),
      ∃ L : E →L[ℝ] E, HasFDerivAt p L x ∧ |L.det| ≤ K := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hΓΩ hdata,
      ae_restrict_mem hΓ] with x hxdata hx
    obtain ⟨⟨A, hAh, hAp, hAdet, hder, hexp⟩,
      ⟨B', hBh, hBp, hBdet, hderv, hexpv⟩⟩ := hxdata
    have hsupport :
        ∀ᶠ y in 𝓝 x,
          u x - (1 - δ) * v x +
              ⟪p x, y - x⟫
            ≤
          u y - (1 - δ) * v y := by
      filter_upwards [hΩ.mem_nhds (hΓΩ hx)] with y hy
      exact hcontact x hx y hy

    have hAdetle : A.det ≤ (1 + ε) ^ n := by
      rw [hAdet]
      exact hfupper x (hΓΩ hx)

    obtain ⟨hR, hRdet⟩ :=
      det_residual_le_of_contact_expansions hn hAh hBp hBdet
        hexp hexpv hδ hδ1 hε hAdetle hsupport

    let R : Matrix (Fin n) (Fin n) ℝ :=
      A - (1 - δ) • B'
    let L : E →L[ℝ] E :=
      (Matrix.toEuclideanLin R).toContinuousLinearMap

    have hL :
        L =
          (Matrix.toEuclideanLin A).toContinuousLinearMap -
            t • (Matrix.toEuclideanLin B').toContinuousLinearMap := by
      ext z
      simp [L, R, t, map_sub, map_smul]

    have hderp : HasFDerivAt p L x := by
      rw [hL]
      exact hder.sub (hderv.const_smul t)

    refine ⟨L, hderp, ?_⟩
    change
      |((Matrix.toEuclideanLin R).toContinuousLinearMap).det| ≤ K
    rw [show
        ((Matrix.toEuclideanLin R).toContinuousLinearMap).det = R.det from
          LinearMap.det_toLpLin 2 R]
    have hRnonneg : 0 ≤ R.det :=
      hR.det_nonneg
    rw [abs_of_nonneg hRnonneg]
    exact hRdet

  have hnull :
      ∀ N : Set E, N ⊆ Γ → volume N = 0 →
        volume (p '' N) = 0 := by
    simpa only [p, t] using
      volume_image_residual_eq_zero_of_posDef_referenceOn
        hconv hu hΩ hv hPDv
        (show 0 ≤ (1 + ε) ^ n by positivity)
        hMAupper ht hΓΩ hcontact

  exact addHaar_image_le_mul_of_ae_derivative volume hΓ hAE hnull

/-- The residual-gradient image bound for a globally convex reference C2 only on the open domain
with positive Hessian and actual local unit Monge–Ampère equation. Both actual
MA equations produce their own same derivative/expansion matrix. The Jacobian
bounds the good image; the proved reference contact null-image theorem removes
the bad remainder. No derivative, N property, residual PSD or image bound is an
input. This given-reference support does not construct a Dirichlet solution. -/
theorem volume_image_residual_le_of_posDef_reference_on_open {n : ℕ} (hn : 0 < n)
    {u v f : EuclideanSpace ℝ (Fin n) → ℝ} (hconv : ConvexOn ℝ univ u) (hu : ContDiff ℝ 1 u)
    (hconvv : ConvexOn ℝ univ v) {Ω : Set (EuclideanSpace ℝ (Fin n))} (hΩ : IsOpen Ω)
    (hv : ContDiffOn ℝ 2 v Ω)
    (hPDv :
      ∀ x ∈ Ω, ∀ z : EuclideanSpace ℝ (Fin n), z ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ v x z z)
    (hf : ContinuousOn f Ω) (hfpos : ∀ x ∈ Ω, 0 < f x)
    (hMA :
      ∀ G : Set (EuclideanSpace ℝ (Fin n)),
        IsOpen G → G ⊆ Ω → volume (subgradientImage u G) = ∫⁻ y in G, ENNReal.ofReal (f y))
    (hMAv :
      ∀ G : Set (EuclideanSpace ℝ (Fin n)),
        IsOpen G → G ⊆ Ω → volume (subgradientImage v G) = volume G)
    {ε δ : ℝ} (hε : 0 ≤ ε) (hδ : 0 < δ) (hδ1 : δ < 1) (hfupper : ∀ x ∈ Ω, f x ≤ (1 + ε) ^ n)
    {Γ : Set (EuclideanSpace ℝ (Fin n))} (hΓ : MeasurableSet Γ) (hΓΩ : Γ ⊆ Ω)
    (hcontact :
      ∀ x ∈ Γ,
        ∀ y ∈ Ω,
          u x - (1 - δ) * v x + ⟪gradient u x - (1 - δ) • gradient v x, y - x⟫ ≤
            u y - (1 - δ) * v y) :
    volume ((fun x => gradient u x - (1 - δ) • gradient v x) '' Γ) ≤
      ENNReal.ofReal ((ε + δ) ^ n) * volume Γ := by
  have hMAv1 :
    ∀ G : Set (EuclideanSpace ℝ (Fin n)),
      IsOpen G → G ⊆ Ω → volume (subgradientImage v G) = ∫⁻ _y in G, ENNReal.ofReal (1 : ℝ) := by
    intro G hG hGO
    rw [hMAv G hG hGO]
    simp
  have hdata :
    ∀ᵐ x ∂(volume.restrict Ω), GradientWitness u f x ∧ GradientWitness v (fun _ => (1 : ℝ)) x := by
    filter_upwards [ae_exists_gradient_posDef_det_eq_on_open hconv hΩ
        (hu.differentiable one_ne_zero).differentiableOn hf hfpos hMA,
      ae_exists_gradient_posDef_det_eq_on_open hconvv hΩ (hv.differentiableOn (by norm_num))
        continuousOn_const (fun _ _ => zero_lt_one) hMAv1] with
      x hxu hxv
    exact ⟨hxu, hxv⟩
  exact
    residual_image_bound_of_ae_data hn hconv hu hΩ hv hPDv hMA hε hδ hδ1 hfupper hΓ hΓΩ hcontact
      hdata

/-- A reference strictly convex and C2 only on the open domain, with its actual
DOMAIN-relative unit MA equation, has the same residual image estimate. The two
actual MA equations produce their own same derivative/expansion matrices; no
outside extension, N property, derivative, PSD or requested image bound is input.
The unknown remains globally convex C1. This does not construct a reference. -/
theorem volume_image_residual_le_of_strict_reference_on_domain
    {n : ℕ} (hn : 0<n)
    {u v f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hconv : ConvexOn ℝ univ u)
    (hu : ContDiff ℝ 1 u)
    {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (hΩ : IsOpen Ω)
    (hstrict : StrictConvexOn ℝ Ω v)
    (hv : ContDiffOn ℝ 2 v Ω)
    (hPDv : ∀ x ∈ Ω, ∀ z : EuclideanSpace ℝ (Fin n), z ≠ 0 →
      0 < bilinearIteratedFDerivTwo ℝ v x z z)
    (hf : ContinuousOn f Ω)
    (hfpos : ∀ x ∈ Ω, 0 < f x)
    (hMA :
      ∀ G : Set (EuclideanSpace ℝ (Fin n)), IsOpen G → G ⊆ Ω →
        volume (subgradientImage u G) =
          ∫⁻ y in G, ENNReal.ofReal (f y))
    (hMAv :
      ∀ G : Set (EuclideanSpace ℝ (Fin n)), IsOpen G → G ⊆ Ω →
        volume {p | ∃ x ∈ G, ∀ y ∈ Ω,
          v x + ⟪p, y - x⟫ ≤ v y} =
          volume G)
    {ε δ : ℝ}
    (hε : 0 ≤ ε)
    (hδ : 0 < δ)
    (hδ1 : δ < 1)
    (hfupper : ∀ x ∈ Ω, f x ≤ (1 + ε) ^ n)
    {Γ : Set (EuclideanSpace ℝ (Fin n))}
    (hΓ : MeasurableSet Γ)
    (hΓΩ : Γ ⊆ Ω)
    (hcontact :
      ∀ x ∈ Γ, ∀ y ∈ Ω,
        u x - (1 - δ) * v x +
            ⟪gradient u x - (1 - δ) • gradient v x, y - x⟫
          ≤
        u y - (1 - δ) * v y) :
    volume
        ((fun x => gradient u x -
          (1 - δ) • gradient v x) '' Γ) ≤
      ENNReal.ofReal ((ε + δ) ^ n) * volume Γ := by
  have hMAv1 :
      ∀ G : Set (EuclideanSpace ℝ (Fin n)), IsOpen G → G ⊆ Ω →
        volume {p | ∃ x ∈ G, ∀ y ∈ Ω,
          v x + ⟪p, y - x⟫ ≤ v y} =
          ∫⁻ _y in G, ENNReal.ofReal (1 : ℝ) := by
    intro G hG hGO
    rw [hMAv G hG hGO]
    simp

  have hdata :
      ∀ᵐ x ∂(volume.restrict Ω),
        GradientWitness u f x ∧
        GradientWitness v (fun _ => (1 : ℝ)) x := by
    filter_upwards
      [ae_exists_gradient_posDef_det_eq_on_open
          hconv hΩ
          (hu.differentiable one_ne_zero).differentiableOn
          hf hfpos hMA,
       ae_exists_gradient_posDef_det_eq_of_strictConvexOn
          hΩ hstrict (hv.of_le (by norm_num))
          continuousOn_const
          (fun _ _ => zero_lt_one)
          hMAv1] with x hxu hxv
    exact ⟨hxu, hxv⟩

  exact residual_image_bound_of_ae_data
    hn hconv hu hΩ hv hPDv hMA
    hε hδ hδ1 hfupper hΓ hΓΩ hcontact hdata

/-- The global-C2 reference image estimate is a true specialization of the
local-C2 common producer, preserving its original public interface. -/
theorem volume_image_residual_le_of_posDef_reference {n : ℕ} (hn : 0 < n)
    {u v f : EuclideanSpace ℝ (Fin n) → ℝ} (hconv : ConvexOn ℝ univ u) (hu : ContDiff ℝ 1 u)
    (hconvv : ConvexOn ℝ univ v) (hv : ContDiff ℝ 2 v) {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (hΩ : IsOpen Ω)
    (hPDv :
      ∀ x ∈ Ω, ∀ z : EuclideanSpace ℝ (Fin n), z ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ v x z z)
    (hf : ContinuousOn f Ω) (hfpos : ∀ x ∈ Ω, 0 < f x)
    (hMA :
      ∀ G : Set (EuclideanSpace ℝ (Fin n)),
        IsOpen G → G ⊆ Ω → volume (subgradientImage u G) = ∫⁻ y in G, ENNReal.ofReal (f y))
    (hMAv :
      ∀ G : Set (EuclideanSpace ℝ (Fin n)),
        IsOpen G → G ⊆ Ω → volume (subgradientImage v G) = volume G)
    {ε δ : ℝ} (hε : 0 ≤ ε) (hδ : 0 < δ) (hδ1 : δ < 1) (hfupper : ∀ x ∈ Ω, f x ≤ (1 + ε) ^ n)
    {Γ : Set (EuclideanSpace ℝ (Fin n))} (hΓ : MeasurableSet Γ) (hΓΩ : Γ ⊆ Ω)
    (hcontact :
      ∀ x ∈ Γ,
        ∀ y ∈ Ω,
          u x - (1 - δ) * v x + ⟪gradient u x - (1 - δ) • gradient v x, y - x⟫ ≤
            u y - (1 - δ) * v y) :
    volume ((fun x => gradient u x - (1 - δ) • gradient v x) '' Γ) ≤
      ENNReal.ofReal ((ε + δ) ^ n) * volume Γ := by
  exact
    volume_image_residual_le_of_posDef_reference_on_open hn hconv hu hconvv hΩ hv.contDiffOn
      hPDv hf hfpos hMA hMAv hε hδ hδ1 hfupper hΓ hΓΩ hcontact

/-- The unit-quadratic specialization constructs the actual reference data;
its image estimate is supplied by the common given-reference theorem. -/
theorem volume_image_residual_le_of_quadratic_contacts {n : ℕ} (hn : 0 < n)
    {u f : EuclideanSpace ℝ (Fin n) → ℝ} (hconv : ConvexOn ℝ Set.univ u) (hu : ContDiff ℝ 1 u)
    {Ω : Set (EuclideanSpace ℝ (Fin n))} (hΩ : IsOpen Ω) (hf : ContinuousOn f Ω)
    (hfpos : ∀ x ∈ Ω, 0 < f x)
    (hMA :
      ∀ G : Set (EuclideanSpace ℝ (Fin n)),
        IsOpen G → G ⊆ Ω → volume (subgradientImage u G) = ∫⁻ y in G, ENNReal.ofReal (f y))
    {ε δ : ℝ} (hε : 0 ≤ ε) (hδ : 0 < δ) (hδ1 : δ < 1) (hfupper : ∀ x ∈ Ω, f x ≤ (1 + ε) ^ n)
    {Γ : Set (EuclideanSpace ℝ (Fin n))} (hΓ : MeasurableSet Γ) (hΓΩ : Γ ⊆ Ω)
    (hcontact :
      ∀ x ∈ Γ,
        ∀ y ∈ Ω,
          u x - ((1 - δ) / 2) * ‖x‖ ^ 2 + ⟪gradient u x - (1 - δ) • x, y - x⟫ ≤
            u y - ((1 - δ) / 2) * ‖y‖ ^ 2) :
    volume ((fun x : EuclideanSpace ℝ (Fin n) => gradient u x - (1 - δ) • x) '' Γ) ≤
      ENNReal.ofReal ((ε + δ) ^ n) * volume Γ := by
  let E := EuclideanSpace ℝ (Fin n)
  let q : E → ℝ := quadraticAt (1 : Matrix (Fin n) (Fin n) ℝ) 0 0 0
  have hq : ContDiff ℝ 2 q := contDiff_quadraticAt _ _ _ _
  have hqconv : ConvexOn ℝ univ q := convexOn_quadraticAt Matrix.PosSemidef.one _ _ _
  have hqform : ∀ x : E, q x = (1 / 2 : ℝ) * ‖x‖ ^ 2 := by
    intro x
    simp [q, quadraticAt, Matrix.toEuclideanLin]
  have hqgradient : gradient q = (fun x : E => x) := by
    funext x
    dsimp [q]
    rw [gradient_quadraticAt Matrix.isHermitian_one]
    simp [Matrix.toEuclideanLin]
  have hqPD : ∀ x ∈ Ω, ∀ z : E, z ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ q x z z := by
    intro x _ z hz
    rw [BakryEmery.bilinearIteratedFDerivTwo_eq_inner_hessianOperator hq]
    change 0 < ⟪(fderiv ℝ (gradient q) x) z, z⟫
    rw [hqgradient]
    simpa only [fderiv_fun_id, ContinuousLinearMap.id_apply, real_inner_self_eq_norm_sq] using
      sq_pos_of_pos (norm_pos_iff.mpr hz)
  have hqMA : ∀ G : Set E, IsOpen G → G ⊆ Ω → volume (subgradientImage q G) = volume G := by
    intro G hG _
    dsimp [q]
    rw [volume_subgradientImage_quadraticAt Matrix.PosDef.one (0 : E) 0 0 hG.measurableSet,
      Matrix.det_one, ENNReal.ofReal_one, one_mul]
  have hs :
    ∀ x ∈ Γ,
      ∀ y ∈ Ω,
        u x - (1 - δ) * q x + ⟪gradient u x - (1 - δ) • gradient q x, y - x⟫ ≤
          u y - (1 - δ) * q y := by
    intro x hx y hy
    rw [hqform x, hqform y, hqgradient]
    convert hcontact x hx y hy using 1 <;> ring
  simpa only [hqgradient] using
    volume_image_residual_le_of_posDef_reference hn hconv hu hqconv hq hΩ hqPD hf hfpos hMA hqMA
      hε hδ hδ1 hfupper hΓ hΓΩ hs

set_option maxHeartbeats 1200000 in
private theorem full_contact_assembly
    {n : ℕ} {u v : EuclideanSpace ℝ (Fin n) → ℝ}
    {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (hΩ : IsOpen Ω)
    (hu : ContDiff ℝ 1 u)
    (hv : ContDiffOn ℝ 1 v Ω)
    {ε δ : ℝ}
    (bound :
      ∀ {Γ : Set (EuclideanSpace ℝ (Fin n))},
        MeasurableSet Γ →
        Γ ⊆ Ω →
        (∀ x ∈ Γ, ∀ y ∈ Ω,
          u x - (1 - δ) * v x +
              ⟪gradient u x - (1 - δ) • gradient v x, y - x⟫
            ≤
          u y - (1 - δ) * v y) →
        volume
            ((fun x => gradient u x -
              (1 - δ) • gradient v x) '' Γ) ≤
          ENNReal.ofReal ((ε + δ) ^ n) * volume Γ) :
    let Γ := {x | x ∈ Ω ∧ ∀ y ∈ Ω,
      u x - (1 - δ) * v x +
          ⟪gradient u x - (1 - δ) • gradient v x, y - x⟫
        ≤
      u y - (1 - δ) * v y}
    volume
        ((fun x => gradient u x -
          (1 - δ) • gradient v x) '' Γ) ≤
      ENNReal.ofReal ((ε + δ) ^ n) * volume Γ := by
  let Γ := {x | x ∈ Ω ∧ ∀ y ∈ Ω,
    u x - (1 - δ) * v x +
        ⟪gradient u x - (1 - δ) • gradient v x, y - x⟫
      ≤
    u y - (1 - δ) * v y}

  have hvg : ContDiffOn ℝ 0 (gradient v) Ω :=
    BakryEmery.contDiffOn_gradient hΩ hv (by norm_num)

  have hw : ContinuousOn (fun x => u x - (1 - δ) * v x) Ω :=
    hu.continuous.continuousOn.sub
      (continuousOn_const.mul hv.continuousOn)

  have hp : ContinuousOn
      (fun x => gradient u x - (1 - δ) • gradient v x) Ω :=
    (BakryEmery.continuous_gradient hu).continuousOn.sub
      (hvg.continuousOn.const_smul (1 - δ))

  have hΓmeas : MeasurableSet Γ := by
    exact measurableSet_support_contactsOn hΩ hw hp

  have hΓΩ : Γ ⊆ Ω := by
    intro x hx
    exact hx.1

  have hΓcontact :
      ∀ x ∈ Γ, ∀ y ∈ Ω,
        u x - (1 - δ) * v x +
            ⟪gradient u x - (1 - δ) • gradient v x, y - x⟫
          ≤
        u y - (1 - δ) * v y := by
    intro x hx y hy
    exact hx.2 y hy

  dsimp [Γ]
  exact bound hΓmeas hΓΩ hΓcontact

/-- The full actual reference contact set has the image bound. Its Borelness
and supporting inequalities are derived from the actual C1/C2 functions. -/
theorem full_reference_contact_image_bound_on_open {n : ℕ} (hn : 0 < n)
    {u v f : EuclideanSpace ℝ (Fin n) → ℝ} (hconv : ConvexOn ℝ univ u) (hu : ContDiff ℝ 1 u)
    (hconvv : ConvexOn ℝ univ v) {Ω : Set (EuclideanSpace ℝ (Fin n))} (hΩ : IsOpen Ω)
    (hv : ContDiffOn ℝ 2 v Ω)
    (hPDv :
      ∀ x ∈ Ω, ∀ z : EuclideanSpace ℝ (Fin n), z ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ v x z z)
    (hf : ContinuousOn f Ω) (hfpos : ∀ x ∈ Ω, 0 < f x)
    (hMA :
      ∀ G : Set (EuclideanSpace ℝ (Fin n)),
        IsOpen G → G ⊆ Ω → volume (subgradientImage u G) = ∫⁻ y in G, ENNReal.ofReal (f y))
    (hMAv :
      ∀ G : Set (EuclideanSpace ℝ (Fin n)),
        IsOpen G → G ⊆ Ω → volume (subgradientImage v G) = volume G)
    {ε δ : ℝ} (hε : 0 ≤ ε) (hδ : 0 < δ) (hδ1 : δ < 1) (hfupper : ∀ x ∈ Ω, f x ≤ (1 + ε) ^ n) :
    let Γ :=
      {x |
        x ∈ Ω ∧
          ∀ y ∈ Ω,
            u x - (1 - δ) * v x + ⟪gradient u x - (1 - δ) • gradient v x, y - x⟫ ≤
              u y - (1 - δ) * v y}
    volume ((fun x => gradient u x - (1 - δ) • gradient v x) '' Γ) ≤
      ENNReal.ofReal ((ε + δ) ^ n) * volume Γ := by
  apply full_contact_assembly hΩ hu (hv.of_le (by norm_num))
  intro Γ hΓ hΓΩ hcontact
  exact
    volume_image_residual_le_of_posDef_reference_on_open hn hconv hu hconvv hΩ hv hPDv hf hfpos
      hMA hMAv hε hδ hδ1 hfupper hΓ hΓΩ hcontact

/-- The old global full-contact interface is the actual contDiffOn specialization
of the local full-contact assembly; no duplicated measurability or image proof. -/
theorem full_reference_contact_image_bound {n : ℕ} (hn : 0 < n)
    {u v f : EuclideanSpace ℝ (Fin n) → ℝ} (hconv : ConvexOn ℝ univ u) (hu : ContDiff ℝ 1 u)
    (hconvv : ConvexOn ℝ univ v) (hv : ContDiff ℝ 2 v) {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (hΩ : IsOpen Ω)
    (hPDv :
      ∀ x ∈ Ω, ∀ z : EuclideanSpace ℝ (Fin n), z ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ v x z z)
    (hf : ContinuousOn f Ω) (hfpos : ∀ x ∈ Ω, 0 < f x)
    (hMA :
      ∀ G : Set (EuclideanSpace ℝ (Fin n)),
        IsOpen G → G ⊆ Ω → volume (subgradientImage u G) = ∫⁻ y in G, ENNReal.ofReal (f y))
    (hMAv :
      ∀ G : Set (EuclideanSpace ℝ (Fin n)),
        IsOpen G → G ⊆ Ω → volume (subgradientImage v G) = volume G)
    {ε δ : ℝ} (hε : 0 ≤ ε) (hδ : 0 < δ) (hδ1 : δ < 1) (hfupper : ∀ x ∈ Ω, f x ≤ (1 + ε) ^ n) :
    let Γ :=
      {x |
        x ∈ Ω ∧
          ∀ y ∈ Ω,
            u x - (1 - δ) * v x + ⟪gradient u x - (1 - δ) • gradient v x, y - x⟫ ≤
              u y - (1 - δ) * v y}
    volume ((fun x => gradient u x - (1 - δ) • gradient v x) '' Γ) ≤
      ENNReal.ofReal ((ε + δ) ^ n) * volume Γ := by
  exact
    full_reference_contact_image_bound_on_open hn hconv hu hconvv hΩ hv.contDiffOn hPDv hf hfpos
      hMA hMAv hε hδ hδ1 hfupper

/-- The actual full contact set for an interior-strict, locally C2 reference with
DOMAIN-relative unit MA has the image bound. Its Borelness and supports are
produced from the real local data, not added as assumptions. -/
theorem full_strict_reference_contact_image_bound
    {n : ℕ} (hn : 0<n)
    {u v f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hconv : ConvexOn ℝ univ u)
    (hu : ContDiff ℝ 1 u)
    {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (hΩ : IsOpen Ω)
    (hstrict : StrictConvexOn ℝ Ω v)
    (hv : ContDiffOn ℝ 2 v Ω)
    (hPDv : ∀ x ∈ Ω, ∀ z : EuclideanSpace ℝ (Fin n), z ≠ 0 →
      0 < bilinearIteratedFDerivTwo ℝ v x z z)
    (hf : ContinuousOn f Ω)
    (hfpos : ∀ x ∈ Ω, 0 < f x)
    (hMA :
      ∀ G : Set (EuclideanSpace ℝ (Fin n)), IsOpen G → G ⊆ Ω →
        volume (subgradientImage u G) =
          ∫⁻ y in G, ENNReal.ofReal (f y))
    (hMAv :
      ∀ G : Set (EuclideanSpace ℝ (Fin n)), IsOpen G → G ⊆ Ω →
        volume {p | ∃ x ∈ G, ∀ y ∈ Ω,
          v x + ⟪p, y - x⟫ ≤ v y} =
          volume G)
    {ε δ : ℝ}
    (hε : 0 ≤ ε)
    (hδ : 0 < δ)
    (hδ1 : δ < 1)
    (hfupper : ∀ x ∈ Ω, f x ≤ (1 + ε) ^ n) :
    let Γ := {x | x ∈ Ω ∧ ∀ y ∈ Ω,
      u x - (1 - δ) * v x +
          ⟪gradient u x - (1 - δ) • gradient v x, y - x⟫
        ≤
      u y - (1 - δ) * v y}
    volume
        ((fun x => gradient u x -
          (1 - δ) • gradient v x) '' Γ) ≤
      ENNReal.ofReal ((ε + δ) ^ n) * volume Γ := by
  apply full_contact_assembly hΩ hu (hv.of_le (by norm_num))
  intro Γ hΓ hΓΩ hcontact
  exact volume_image_residual_le_of_strict_reference_on_domain
    hn hconv hu hΩ hstrict hv hPDv hf hfpos hMA hMAv
    hε hδ hδ1 hfupper hΓ hΓΩ hcontact

/-- Actual full contact set: its measurability and supporting data are derived,
not supplied. The reference is quadratic; no general-reference or W²,p conclusion. -/
theorem full_quadratic_contact_image_bound {n : ℕ} (hn : 0 < n)
    {u f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hconv : ConvexOn ℝ univ u) (hu : ContDiff ℝ 1 u)
    {Ω : Set (EuclideanSpace ℝ (Fin n))} (hΩ : IsOpen Ω)
    (hf : ContinuousOn f Ω) (hfpos : ∀ x ∈ Ω, 0 < f x)
    (hMA : ∀ G : Set (EuclideanSpace ℝ (Fin n)), IsOpen G → G ⊆ Ω →
      volume (subgradientImage u G) = ∫⁻ y in G, ENNReal.ofReal (f y))
    {ε δ : ℝ} (hε : 0 ≤ ε) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hfupper : ∀ x ∈ Ω, f x ≤ (1 + ε) ^ n) :
    let Γ := {x | x ∈ Ω ∧ ∀ y ∈ Ω,
      u x - ((1 - δ) / 2) * ‖x‖ ^ 2 +
        ⟪gradient u x - (1 - δ) • x, y - x⟫ ≤
          u y - ((1 - δ) / 2) * ‖y‖ ^ 2}
    volume ((fun x => gradient u x - (1 - δ) • x) '' Γ) ≤
      ENNReal.ofReal ((ε + δ) ^ n) * volume Γ := by
  apply volume_image_residual_le_of_quadratic_contacts hn hconv hu hΩ hf hfpos hMA
    hε hδ hδ1 hfupper
  · exact measurableSet_quadratic_contacts hu hΩ (1 - δ)
  · exact fun _ hx => hx.1
  · exact fun _ hx => hx.2


/-- Real DOMAIN unit MA produces the reference-image mass lower bound.
No compactness, finite volume, image measurability or sought mass is assumed. -/
theorem volume_le_gradient_image_closure_of_domain_alexandrov {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {v : E → ℝ} {Ω G : Set E} (hΩ : IsOpen Ω) (hd : DifferentiableOn ℝ v Ω) (hG : IsOpen G)
    (hGO : G ⊆ Ω)
    (hMA : ∀ U : Set E, IsOpen U → U ⊆ Ω → volume (subgradientImageOn v Ω U) = volume U) :
    volume G ≤ volume (gradient v '' closure G) := by
  rw [← hMA G hG hGO]
  exact
    measure_mono
      ((subgradientImageOn_subset_gradient_image hΩ hd hGO).trans (image_mono subset_closure))


private theorem exists_contact_volume_gain_from_actual_contacts {n : ℕ} (hn : 0 < n)
    {v : EuclideanSpace ℝ (Fin n) → ℝ} {Ω G : Set (EuclideanSpace ℝ (Fin n))}
    (hmass : volume G ≤ volume (gradient v '' closure G)) {δ η : ℝ} (hδ₀ : 0 < δ) (hη₀ : 0 < η)
    (hη₁ : η < 1)
    (hcontacts :
      ∃ ε : ℝ,
        0 < ε ∧
          ε < 1 ∧
            ∀ u : EuclideanSpace ℝ (Fin n) → ℝ,
              ConvexOn ℝ univ u →
                ContDiff ℝ 1 u →
                  (∀ x ∈ frontier Ω, u x = 0) →
                    (∀ H : Set (EuclideanSpace ℝ (Fin n)),
                        IsOpen H →
                          H ⊆ Ω →
                            ENNReal.ofReal ((1 - ε) ^ n) * volume H ≤
                                volume (subgradientImage u H) ∧
                              volume (subgradientImage u H) ≤
                                ENNReal.ofReal ((1 + ε) ^ n) * volume H) →
                      ∀ z ∈ closure G,
                        ∃ x ∈ Ω,
                          gradient u x - (1 - δ) • gradient v x = δ • gradient v z ∧
                            ∀ y ∈ closure Ω,
                              u x - (1 - δ) * v x + ⟪δ • gradient v z, y - x⟫ ≤
                                u y - (1 - δ) * v y)
    (himages :
      ∀ ε : ℝ,
        0 ≤ ε →
          ∀ u f : EuclideanSpace ℝ (Fin n) → ℝ,
            ConvexOn ℝ univ u →
              ContDiff ℝ 1 u →
                ContinuousOn f Ω →
                  (∀ x ∈ Ω, 0 < f x) →
                    (∀ H : Set (EuclideanSpace ℝ (Fin n)),
                        IsOpen H →
                          H ⊆ Ω →
                            volume (subgradientImage u H) = ∫⁻ x in H, ENNReal.ofReal (f x)) →
                      (∀ x ∈ Ω, f x ≤ (1 + ε) ^ n) →
                        let Γ :=
                          {x |
                            x ∈ Ω ∧
                              ∀ y ∈ Ω,
                                u x - (1 - δ) * v x +
                                    ⟪gradient u x - (1 - δ) • gradient v x, y - x⟫ ≤
                                  u y - (1 - δ) * v y}
                        volume ((fun x => gradient u x - (1 - δ) • gradient v x) '' Γ) ≤
                          ENNReal.ofReal ((ε + δ) ^ n) * volume Γ) :
    ∃ ε : ℝ,
      0 < ε ∧
        ε < 1 ∧
          ∀ (u f : EuclideanSpace ℝ (Fin n) → ℝ),
            ConvexOn ℝ univ u →
              ContDiff ℝ 1 u →
                ContinuousOn f Ω →
                  (∀ x ∈ Ω, 0 < f x) →
                    (∀ x ∈ frontier Ω, u x = 0) →
                      (∀ x ∈ Ω, (1 - ε) ^ n ≤ f x ∧ f x ≤ (1 + ε) ^ n) →
                        (∀ H : Set (EuclideanSpace ℝ (Fin n)),
                            IsOpen H →
                              H ⊆ Ω →
                                volume (subgradientImage u H) =
                                  ∫⁻ x in H, ENNReal.ofReal (f x)) →
                          ENNReal.ofReal (1 - η) * volume G ≤
                            volume
                              {x |
                                x ∈ Ω ∧
                                  ∀ y ∈ Ω,
                                    u x - (1 - δ) * v x +
                                        ⟪gradient u x - (1 - δ) • gradient v x, y - x⟫ ≤
                                      u y - (1 - δ) * v y} := by
  let E := EuclideanSpace ℝ (Fin n)
  let K : Set E := closure G
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hn))
  have hnR : 0 < (n : ℝ) := by positivity
  obtain ⟨ε₀, hε₀, hε₀1, hcontact⟩ := hcontacts
  let ε : ℝ := min ε₀ (δ * η / (n : ℝ))
  have hεpos : 0 < ε := by
    dsimp [ε]
    exact lt_min hε₀ (by positivity)
  have hεle₀ : ε ≤ ε₀ := by exact min_le_left _ _
  have hεleδeta : ε ≤ δ * η / (n : ℝ) := by exact min_le_right _ _
  have hεδ : ε ≤ δ := by
    apply le_trans hεleδeta
    apply (div_le_iff₀ hnR).2
    have hη' : δ * η ≤ δ := by nlinarith [mul_le_mul_of_nonneg_left hη₁.le hδ₀.le]
    nlinarith
  have hε1 : ε < 1 := by exact lt_of_le_of_lt (min_le_left _ _) hε₀1
  have hqnonneg : 0 ≤ ε / δ := by positivity
  have hqone : ε / δ ≤ 1 := by
    apply (div_le_iff₀ hδ₀).2
    simpa only [one_mul] using hεδ
  have hqeta : ε / δ ≤ η / (n : ℝ) := by
    calc
      ε / δ ≤ (δ * η / (n : ℝ)) / δ := div_le_div_of_nonneg_right hεleδeta hδ₀.le
      _ = η / (n : ℝ) := by field_simp [ne_of_gt hδ₀, ne_of_gt hnR]
  have hbern : ∀ m : ℕ, 1 - (m : ℝ) * (ε / δ) ≤ (1 - ε / δ) ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      calc
        1 - ((m + 1 : ℕ) : ℝ) * (ε / δ) ≤ (1 - (m : ℝ) * (ε / δ)) * (1 - ε / δ) := by
          push_cast
          nlinarith [mul_nonneg (show (0 : ℝ) ≤ m by positivity) (sq_nonneg (ε / δ))]
        _ ≤ (1 - ε / δ) ^ m * (1 - ε / δ) :=
          mul_le_mul_of_nonneg_right ih (sub_nonneg.mpr hqone)
        _ = (1 - ε / δ) ^ (m + 1) := by rw [pow_succ]
  have hqmul : (n : ℝ) * (ε / δ) ≤ η := by
    simpa only [mul_comm] using (le_div_iff₀ hnR).mp hqeta
  have hratio₀ : 1 - η ≤ (δ / (ε + δ)) ^ n := by
    have hbase : 1 - ε / δ ≤ δ / (ε + δ) := by
      apply (le_div_iff₀ (by linarith : 0 < ε + δ)).2
      have heq : (1 - ε / δ) * (ε + δ) = δ - ε ^ 2 / δ := by
        field_simp [ne_of_gt hδ₀]
        ring
      rw [heq]
      exact sub_le_self _ (div_nonneg (sq_nonneg ε) hδ₀.le)
    have hpow : (1 - ε / δ) ^ n ≤ (δ / (ε + δ)) ^ n := by gcongr
    calc
      1 - η ≤ 1 - (n : ℝ) * (ε / δ) := by linarith
      _ ≤ (1 - ε / δ) ^ n := hbern n
      _ ≤ (δ / (ε + δ)) ^ n := hpow
  have hratio : (1 - η) * (ε + δ) ^ n ≤ δ ^ n := by
    calc
      (1 - η) * (ε + δ) ^ n ≤ (δ / (ε + δ)) ^ n * (ε + δ) ^ n :=
        mul_le_mul_of_nonneg_right hratio₀ (by positivity)
      _ = δ ^ n := by
        rw [div_pow]
        field_simp [ne_of_gt (show 0 < ε + δ by linarith)]
  refine ⟨ε, hεpos, hε1, ?_⟩
  intro u f hu huC1 hfcont hfpos hu0 hf hMA
  have hfupper₀ : ∀ x ∈ Ω, f x ≤ (1 + ε₀) ^ n := by
    intro x hx
    have hbase : 1 + ε ≤ 1 + ε₀ := by linarith
    have hpow : (1 + ε) ^ n ≤ (1 + ε₀) ^ n := by gcongr
    exact le_trans (hf x hx).2 hpow
  have hflower₀ : ∀ x ∈ Ω, (1 - ε₀) ^ n ≤ f x := by
    intro x hx
    have hbase : 1 - ε₀ ≤ 1 - ε := by linarith
    have hpow : (1 - ε₀) ^ n ≤ (1 - ε) ^ n := by gcongr
    exact le_trans hpow (hf x hx).1
  have hMAcomp :
    ∀ G : Set E,
      IsOpen G →
        G ⊆ Ω →
          ENNReal.ofReal ((1 - ε₀) ^ n) * volume G ≤ volume (subgradientImage u G) ∧
            volume (subgradientImage u G) ≤ ENNReal.ofReal ((1 + ε₀) ^ n) * volume G := by
    intro G hG hGΩ
    rw [hMA G hG hGΩ]
    constructor
    · rw [← setLIntegral_const G]
      apply setLIntegral_mono' hG.measurableSet
      intro y hy
      exact ENNReal.ofReal_le_ofReal (hflower₀ y (hGΩ hy))
    · rw [← setLIntegral_const G]
      apply setLIntegral_mono' hG.measurableSet
      intro y hy
      exact ENNReal.ofReal_le_ofReal (hfupper₀ y (hGΩ hy))
  let Γ : Set E :=
    {x |
      x ∈ Ω ∧
        ∀ y ∈ Ω,
          u x - (1 - δ) * v x + ⟪gradient u x - (1 - δ) • gradient v x, y - x⟫ ≤
            u y - (1 - δ) * v y}
  let p : E → E := fun x => gradient u x - (1 - δ) • gradient v x
  have hcontact_image : δ • (gradient v '' K) ⊆ p '' Γ := by
    rintro q ⟨a, ⟨z, hz, rfl⟩, rfl⟩
    obtain ⟨x, hx, hg, hs⟩ := hcontact u hu huC1 hu0 hMAcomp z hz
    refine ⟨x, ⟨hx, ?_⟩, hg⟩
    intro y hy
    have hsy := hs y (subset_closure hy)
    rw [← hg] at hsy
    exact hsy
  have hscale :
    volume (δ • (gradient v '' K)) = ENNReal.ofReal (δ ^ n) * volume (gradient v '' K) := by
    simpa only [E, finrank_euclideanSpace_fin] using
      (volume : Measure E).addHaar_smul_of_nonneg hδ₀.le (gradient v '' K)
  have himage : volume (p '' Γ) ≤ ENNReal.ofReal ((ε + δ) ^ n) * volume Γ :=
    himages ε hεpos.le u f hu huC1 hfcont hfpos hMA (fun x hx => (hf x hx).2)
  have hmain : ENNReal.ofReal (δ ^ n) * volume G ≤ ENNReal.ofReal ((ε + δ) ^ n) * volume Γ := by
    calc
      ENNReal.ofReal (δ ^ n) * volume G ≤ ENNReal.ofReal (δ ^ n) * volume (gradient v '' K) :=
        mul_le_mul le_rfl hmass bot_le bot_le
      _ = volume (δ • (gradient v '' K)) := hscale.symm
      _ ≤ volume (p '' Γ) := measure_mono hcontact_image
      _ ≤ ENNReal.ofReal ((ε + δ) ^ n) * volume Γ := himage
  have hcoeff :
    ENNReal.ofReal (1 - η) * ENNReal.ofReal ((ε + δ) ^ n) ≤ ENNReal.ofReal (δ ^ n) := by
    rw [← ENNReal.ofReal_mul (by linarith : 0 ≤ 1 - η)]
    exact ENNReal.ofReal_le_ofReal hratio
  have hBpos : 0 < ENNReal.ofReal ((ε + δ) ^ n) := by
    apply ENNReal.ofReal_pos.mpr
    positivity
  have hBtop : ENNReal.ofReal ((ε + δ) ^ n) ≠ ∞ := ENNReal.ofReal_ne_top
  have hcancel :
    ENNReal.ofReal ((ε + δ) ^ n) * (ENNReal.ofReal (1 - η) * volume G) ≤
      ENNReal.ofReal ((ε + δ) ^ n) * volume Γ := by
    calc
      ENNReal.ofReal ((ε + δ) ^ n) * (ENNReal.ofReal (1 - η) * volume G) =
          (ENNReal.ofReal (1 - η) * ENNReal.ofReal ((ε + δ) ^ n)) * volume G := by
        ac_rfl
      _ ≤ ENNReal.ofReal (δ ^ n) * volume G := mul_le_mul hcoeff le_rfl bot_le bot_le
      _ ≤ ENNReal.ofReal ((ε + δ) ^ n) * volume Γ := hmain
  exact (ENNReal.mul_le_mul_iff_right hBpos.ne' hBtop).mp hcancel




/-- A given globally C2 strictly convex positive-Hessian unit-MA reference on
bounded open Ω gives contact-volume gain over every relatively compact open G.
The tolerance precedes both unknown solution and density. Actual MA and genuine
subgradient uniqueness produce the reference image mass; actual comparison
contacts, Haar scaling and the contact-image bound give the gain. No desired
mass/inclusion/gain, N property or unknown-u Hessian/W2p estimate is supplied.
This supports Letwin arXiv2607.24164v1 Lemma2.2 via BB1207.6128v1 Theorem2.24(ii);
it does not construct the comparison reference or close W2p. -/
theorem exists_contact_volume_gain_of_posDef_reference {n : ℕ} (hn : 0 < n)
    {v : EuclideanSpace ℝ (Fin n) → ℝ} (hvstrict : StrictConvexOn ℝ univ v)
    (hv : ContDiff ℝ 2 v) {Ω G : Set (EuclideanSpace ℝ (Fin n))} (hΩo : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω) (hv0 : ∀ x ∈ frontier Ω, v x = 0)
    (hPD :
      ∀ x ∈ Ω, ∀ z : EuclideanSpace ℝ (Fin n), z ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ v x z z)
    (hMAv :
      ∀ H : Set (EuclideanSpace ℝ (Fin n)),
        IsOpen H → H ⊆ Ω → volume (subgradientImage v H) = volume H)
    (hG : IsOpen G) (hGc : IsCompact (closure G)) (hGO : closure G ⊆ Ω) {δ η : ℝ} (hδ₀ : 0 < δ)
    (hδ₁ : δ < 1) (hη₀ : 0 < η) (hη₁ : η < 1) :
    ∃ ε : ℝ,
      0 < ε ∧
        ε < 1 ∧
          ∀ (u f : EuclideanSpace ℝ (Fin n) → ℝ),
            ConvexOn ℝ univ u →
              ContDiff ℝ 1 u →
                ContinuousOn f Ω →
                  (∀ x ∈ Ω, 0 < f x) →
                    (∀ x ∈ frontier Ω, u x = 0) →
                      (∀ x ∈ Ω, (1 - ε) ^ n ≤ f x ∧ f x ≤ (1 + ε) ^ n) →
                        (∀ H : Set (EuclideanSpace ℝ (Fin n)),
                            IsOpen H →
                              H ⊆ Ω →
                                volume (subgradientImage u H) =
                                  ∫⁻ x in H, ENNReal.ofReal (f x)) →
                          ENNReal.ofReal (1 - η) * volume G ≤
                            volume
                              {x |
                                x ∈ Ω ∧
                                  ∀ y ∈ Ω,
                                    u x - (1 - δ) * v x +
                                        ⟪gradient u x - (1 - δ) • gradient v x, y - x⟫ ≤
                                      u y - (1 - δ) * v y} := by
  have hvC1 : ContDiff ℝ 1 v := hv.of_le (by norm_num)
  have hmass : volume G ≤ volume (gradient v '' closure G) := by
    rw [← hMAv G hG (subset_closure.trans hGO)]
    apply measure_mono
    rw [← subgradientImageOn_univ]
    exact
      (subgradientImageOn_subset_gradient_image isOpen_univ
            (hvC1.differentiable one_ne_zero).differentiableOn (subset_univ G)).trans
        (image_mono subset_closure)
  apply
    exists_contact_volume_gain_from_actual_contacts hn hmass hδ₀ hη₀ hη₁
      (exists_residual_contact_of_alexandrov_density_close hn hvstrict hvC1 hΩo hΩb hv0 hMAv hGc
        hGO hδ₀)
  intro ε hε u f hu huC1 hfcont hfpos hMA hfupper
  exact
    full_reference_contact_image_bound hn hu huC1 hvstrict.convexOn hv hΩo hPD hfcont hfpos hMA
      hMAv hε hδ₀ hδ₁ hfupper

/-- A given reference convex/C0 on the closure, interior-strict and locally C2
with actual positive Hessian and DOMAIN unit MA yields compact OPEN G contact
volume gain. Epsilon precedes BOTH unknown globally convex C1 u and its actual
continuous positive MA density. No outside extension or desired mass/contact/
inclusion/gain/N/unknown Hessian/W2p input. This does not construct the reference
or close the nonlinear W2p/smooth-source step of Letwin arXiv2607.24164v1 Lemma2.2. -/
theorem exists_contact_volume_gain_of_strict_reference_on_domain {n : ℕ} (hn : 0 < n)
    {v : EuclideanSpace ℝ (Fin n) → ℝ} {Ω G : Set (EuclideanSpace ℝ (Fin n))} (hΩo : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω) (hvconv : ConvexOn ℝ (closure Ω) v)
    (hvstrict : StrictConvexOn ℝ Ω v) (hvc : ContinuousOn v (closure Ω))
    (hv : ContDiffOn ℝ 2 v Ω) (hv0 : ∀ x ∈ frontier Ω, v x = 0)
    (hPD :
      ∀ x ∈ Ω, ∀ z : EuclideanSpace ℝ (Fin n), z ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ v x z z)
    (hMAv :
      ∀ H : Set (EuclideanSpace ℝ (Fin n)),
        IsOpen H → H ⊆ Ω → volume (subgradientImageOn v Ω H) = volume H)
    (hG : IsOpen G) (hGc : IsCompact (closure G)) (hGO : closure G ⊆ Ω) {δ η : ℝ} (hδ₀ : 0 < δ)
    (hδ₁ : δ < 1) (hη₀ : 0 < η) (hη₁ : η < 1) :
    ∃ ε : ℝ,
      0 < ε ∧
        ε < 1 ∧
          ∀ (u f : EuclideanSpace ℝ (Fin n) → ℝ),
            ConvexOn ℝ univ u →
              ContDiff ℝ 1 u →
                ContinuousOn f Ω →
                  (∀ x ∈ Ω, 0 < f x) →
                    (∀ x ∈ frontier Ω, u x = 0) →
                      (∀ x ∈ Ω, (1 - ε) ^ n ≤ f x ∧ f x ≤ (1 + ε) ^ n) →
                        (∀ H : Set (EuclideanSpace ℝ (Fin n)),
                            IsOpen H →
                              H ⊆ Ω →
                                volume (subgradientImage u H) =
                                  ∫⁻ x in H, ENNReal.ofReal (f x)) →
                          ENNReal.ofReal (1 - η) * volume G ≤
                            volume
                              {x |
                                x ∈ Ω ∧
                                  ∀ y ∈ Ω,
                                    u x - (1 - δ) * v x +
                                        ⟪gradient u x - (1 - δ) • gradient v x, y - x⟫ ≤
                                      u y - (1 - δ) * v y} := by
  have hvC1 : ContDiffOn ℝ 1 v Ω := hv.of_le (by norm_num)
  have hmass : volume G ≤ volume (gradient v '' closure G) :=
    volume_le_gradient_image_closure_of_domain_alexandrov hΩo
      (hvC1.differentiableOn one_ne_zero) hG (subset_closure.trans hGO) hMAv
  apply
    exists_contact_volume_gain_from_actual_contacts hn hmass hδ₀ hη₀ hη₁
      (exists_residual_contact_of_domain_alexandrov_density_close hn hΩo hΩb hvconv hvstrict hvc
        hvC1 hv0 hMAv hGc hGO hδ₀)
  intro ε hε u f hu huC1 hfcont hfpos hMA hfupper
  exact
    full_strict_reference_contact_image_bound hn hu huC1 hΩo hvstrict hv hPD hfcont hfpos hMA
      hMAv hε hδ₀ hδ₁ hfupper


/-- Contact-volume density gain for the actual quadratic residual in the unit
ball. The tolerance precedes both unknown solution and density. Actual comparison
contacts give the image inclusion, and the image upper bound gives the volume
gain. This is the unit-ball quadratic model for Letwin arXiv:2607.24164v1
Lemma 2.2 via BB1207.6128v1 Theorem 2.24(ii), not the general-domain estimate. -/
theorem exists_contact_volume_gain_unitBall
    {n : ℕ} (hn : 0 < n)
    {r δ η : ℝ}
    (hr₀ : 0 < r) (hr₁ : r < 1)
    (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (hη₀ : 0 < η) (hη₁ : η < 1) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
      ∀ (u f : EuclideanSpace ℝ (Fin n) → ℝ),
        ConvexOn ℝ univ u →
        ContDiff ℝ 1 u →
        ContinuousOn f (ball (0 : EuclideanSpace ℝ (Fin n)) 1) →
        (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin n)) 1, 0 < f x) →
        (∀ x ∈ frontier (ball (0 : EuclideanSpace ℝ (Fin n)) 1), u x = 0) →
        (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin n)) 1,
          (1 - ε) ^ n ≤ f x ∧ f x ≤ (1 + ε) ^ n) →
        (∀ G : Set (EuclideanSpace ℝ (Fin n)),
          IsOpen G →
          G ⊆ ball (0 : EuclideanSpace ℝ (Fin n)) 1 →
          volume (subgradientImage u G) =
            ∫⁻ y in G, ENNReal.ofReal (f y)) →
        ENNReal.ofReal (1 - η) *
            volume (closedBall (0 : EuclideanSpace ℝ (Fin n)) r) ≤
          volume
            {x | x ∈ ball (0 : EuclideanSpace ℝ (Fin n)) 1 ∧
              ∀ y ∈ ball (0 : EuclideanSpace ℝ (Fin n)) 1,
                u x - ((1 - δ) / 2) * ‖x‖ ^ 2 +
                    ⟪gradient u x - (1 - δ) • x, y - x⟫ ≤
                  u y - ((1 - δ) / 2) * ‖y‖ ^ 2} := by
  let E := EuclideanSpace ℝ (Fin n)
  let Ω : Set E := ball (0 : E) 1
  let v : E → ℝ :=
    quadraticAt (1 : Matrix (Fin n) (Fin n) ℝ) (0 : E) 0 (-1 / 2)

  have hvstrict : StrictConvexOn ℝ univ v :=
    strictConvexOn_quadraticAt Matrix.PosDef.one _ _ _

  have hvform : ∀ x : E, v x = (1 / 2 : ℝ) * ‖x‖ ^ 2 - 1 / 2 := by
    intro x
    dsimp [v, quadraticAt]
    simp only [sub_zero, inner_zero_left, add_zero, Matrix.toEuclideanLin,
      Matrix.toLpLin_one, LinearMap.id_apply, real_inner_self_eq_norm_sq]
    ring

  have hvgradient : ∀ x : E, gradient v x = x := by
    intro x
    dsimp [v]
    rw [gradient_quadraticAt Matrix.isHermitian_one]
    simp [Matrix.toEuclideanLin]

  have hvboundary : ∀ x ∈ frontier Ω, v x = 0 := by
    intro x hx
    change x ∈ frontier (ball (0 : E) 1) at hx
    rw [frontier_ball (0 : E) (by norm_num : (1 : ℝ) ≠ 0)] at hx
    have hnorm : ‖x‖ = 1 := by
      simpa only [mem_sphere, dist_zero_right] using hx
    rw [hvform]
    norm_num [hnorm]

  have hvMA :
      ∀ G : Set E, IsOpen G → G ⊆ Ω →
        volume (subgradientImage v G) = volume G := by
    intro G hG _
    change volume
        (subgradientImage
          (quadraticAt (1 : Matrix (Fin n) (Fin n) ℝ) (0 : E) 0 (-1 / 2)) G) =
      volume G
    rw [volume_subgradientImage_quadraticAt Matrix.PosDef.one,
      Matrix.det_one, ENNReal.ofReal_one, one_mul]
    exact hG.measurableSet

  have hvC2 : ContDiff ℝ 2 v := contDiff_quadraticAt _ _ _ _
  have hvg : gradient v = (fun x : E => x) := funext hvgradient
  have hPD : ∀ x ∈ Ω, ∀ z : E, z ≠ 0 →
      0 < bilinearIteratedFDerivTwo ℝ v x z z := by
    intro x _ z hz
    rw [BakryEmery.bilinearIteratedFDerivTwo_eq_inner_hessianOperator hvC2]
    change 0 < ⟪(fderiv ℝ (gradient v) x) z, z⟫
    rw [hvg]
    simpa only [fderiv_fun_id, ContinuousLinearMap.id_apply,
      real_inner_self_eq_norm_sq] using sq_pos_of_pos (norm_pos_iff.mpr hz)
  have hGc : IsCompact (closure (ball (0 : E) r)) := by
    rw [closure_ball (0 : E) (ne_of_gt hr₀)]
    exact isCompact_closedBall _ _
  have hGO : closure (ball (0 : E) r) ⊆ Ω := by
    rw [closure_ball (0 : E) (ne_of_gt hr₀)]
    exact closedBall_subset_ball hr₁
  obtain ⟨ε, hε, hε1, hg⟩ := exists_contact_volume_gain_of_posDef_reference
    hn hvstrict hvC2 isOpen_ball isBounded_ball hvboundary hPD hvMA
    isOpen_ball hGc hGO hδ₀ hδ₁ hη₀ hη₁
  refine ⟨ε, hε, hε1, ?_⟩
  intro u f hu huC1 hfcont hfpos hu0 hf hMA
  have hh := hg u f hu huC1 hfcont hfpos hu0 hf hMA
  have hΓ : {x | x ∈ Ω ∧ ∀ y ∈ Ω,
      u x - (1 - δ) * v x +
        ⟪gradient u x - (1 - δ) • gradient v x, y - x⟫ ≤
          u y - (1 - δ) * v y} =
      {x | x ∈ Ω ∧ ∀ y ∈ Ω,
        u x - ((1 - δ) / 2) * ‖x‖ ^ 2 +
          ⟪gradient u x - (1 - δ) • x, y - x⟫ ≤
            u y - ((1 - δ) / 2) * ‖y‖ ^ 2} := by
    ext x
    constructor
    · rintro ⟨hx, hs⟩
      refine ⟨hx, ?_⟩
      intro y hy
      have h := hs y hy
      rw [hvform x, hvform y, hvgradient x] at h
      nlinarith only [h]
    · rintro ⟨hx, hs⟩
      refine ⟨hx, ?_⟩
      intro y hy
      rw [hvform x, hvform y, hvgradient x]
      have h := hs y hy
      nlinarith only [h]
  rw [hΓ] at hh
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hvol : volume (closedBall (0 : E) r) = volume (ball (0 : E) r) :=
    (volume : Measure E).addHaar_closedBall_eq_addHaar_ball _ _
  simpa only [hvol] using hh


end FunctionalInequalities.Analysis
