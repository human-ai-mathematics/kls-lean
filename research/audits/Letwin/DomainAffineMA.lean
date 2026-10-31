module

public import FunctionalInequalities.Analysis.Convex.Alexandrov.Comparison
public import FunctionalInequalities.Analysis.Convex.Alexandrov.Stability
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

noncomputable section
open MeasureTheory Set Filter
open scoped RealInnerProductSpace ENNReal NNReal Pointwise Topology
namespace LetwinDomainAffineAudit
open FunctionalInequalities.Analysis
section AuditedReuse

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]



omit [MeasurableSpace E] [BorelSpace E] in
theorem global_identity_is_univ_specialization (u : E → ℝ) (e : E ≃ᵃ[ℝ] E) (G : Set E) :
    subgradientImage (u ∘ e.symm) (e '' G) =
      (LinearMap.adjoint (e.linear.symm : E →ₗ[ℝ] E)) '' subgradientImage u G := by
  simpa only [Set.image_univ_of_surjective e.surjective, subgradientImageOn_univ] using
    subgradientImageOn_comp_affineEquiv_symm u e univ G

theorem global_volume_is_univ_specialization (u : E → ℝ) (e : E ≃ᵃ[ℝ] E) (G : Set E) :
    (volume : Measure E) (subgradientImage (u ∘ e.symm) (e '' G)) =
      ENNReal.ofReal |LinearMap.det (e.linear : E →ₗ[ℝ] E)|⁻¹ *
        (volume : Measure E) (subgradientImage u G) := by
  simpa only [Set.image_univ_of_surjective e.surjective, subgradientImageOn_univ] using
    volume_subgradientImageOn_comp_affineEquiv_symm u e univ G

end AuditedReuse

section ZeroDimensionalClient

/-- Concrete zero-dimensional client: the affine, reflection, and scalar
identities remain valid without a positive-dimensionality hypothesis. -/
theorem zero_dimensional_affine_scalar_client
    {u : EuclideanSpace ℝ (Fin 0) → ℝ}
    {D G : Set (EuclideanSpace ℝ (Fin 0))}
    {a : ℝ} (ha : 0 < a) :
    (volume : Measure (EuclideanSpace ℝ (Fin 0)))
        (subgradientImageOn
          (fun x => a * u x) D G) =
      ENNReal.ofReal (a ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin 0))) *
        (volume : Measure (EuclideanSpace ℝ (Fin 0)))
          (subgradientImageOn u D G) := by
  let e : EuclideanSpace ℝ (Fin 0) ≃ᵃ[ℝ]
      EuclideanSpace ℝ (Fin 0) := AffineEquiv.refl ℝ _
  simpa [e] using
    volume_subgradientImageOn_mul_pos_comp_affineEquiv_symm
      u e ha D G

end ZeroDimensionalClient

section RealQuadraticClient

private lemma real_quadratic_gradient (x : ℝ) : gradient (fun y : ℝ => y ^ 2 / 2) x = x := by
  have hd := (hasDerivAt_pow 2 x).div_const 2
  rw [gradient_eq_deriv']
  convert hd.deriv using 1; ring

private lemma real_quadratic_support_image {D H : Set ℝ} (hD : IsOpen D) (hH : H ⊆ D) :
    subgradientImageOn (fun y : ℝ => y ^ 2 / 2) D H = H := by
  ext p
  constructor
  · rintro ⟨x, hx, hp⟩
    have hd := ((hasDerivAt_pow 2 x).div_const 2).differentiableAt
    have heq := subgradientOn_eq_gradient hD (hH hx) hd hp
    rw [real_quadratic_gradient] at heq
    exact heq.symm ▸ hx
  · intro hp
    refine ⟨p, hp, ?_⟩
    intro y _hy
    simp only [Real.inner_apply]
    nlinarith [sq_nonneg (y - p)]

/-- The real quadratic has exact unit domain-MA on the interval `(-1,1)`,
proved from its actual supporting inequalities. -/
theorem real_quadratic_domain_MA :
    ∀ H : Set ℝ, IsOpen H → H ⊆ Set.Ioo (-1 : ℝ) 1 →
      (volume : Measure ℝ)
          (subgradientImageOn
            (fun y : ℝ => y ^ 2 / 2) (Set.Ioo (-1 : ℝ) 1) H) =
        ENNReal.ofReal 1 * (volume : Measure ℝ) H := by
  intro H _hH hHD
  rw [real_quadratic_support_image
    (isOpen_Ioo : IsOpen (Set.Ioo (-1 : ℝ) 1)) hHD]
  simp

private lemma real_three_affine_equiv :
    ∃ e : ℝ ≃ᵃ[ℝ] ℝ, (∀ x : ℝ, e x = 3 * x + 1) ∧ LinearMap.det (e.linear : ℝ →ₗ[ℝ] ℝ) = 3 := by
  let T : ℝ →ₗ[ℝ] ℝ :=
    { toFun := fun x => 3 * x
      map_add' := by intro x y; ring
      map_smul' := by intro c x; simp only [smul_eq_mul, RingHom.id_apply]; ring }
  have hT : Function.Bijective T := by
    constructor
    · intro x y hxy
      dsimp [T] at hxy
      linarith
    · intro y
      refine ⟨y / 3, ?_⟩
      dsimp [T]
      ring
  let Te : ℝ ≃ₗ[ℝ] ℝ := LinearEquiv.ofBijective T hT
  let e : ℝ ≃ᵃ[ℝ] ℝ := AffineEquiv.ofLinearEquiv Te 0 1
  have he : ∀ x : ℝ, e x = 3 * x + 1 := by
    intro x
    change 3 * (x - 0) + 1 = 3 * x + 1
    ring
  refine ⟨e, he, ?_⟩
  rw [LinearMap.det_ring]
  have hlin := (AffineEquiv.toAffineMap e).linear_apply_vsub (1 : ℝ) 0
  change (e.linear : ℝ →ₗ[ℝ] ℝ) ((1 : ℝ) - 0) = e 1 - e 0 at hlin
  rw [sub_zero, he 1, he 0] at hlin
  norm_num at hlin
  exact hlin

/-- Actual one-dimensional client with `q(x)=x²/2`, `D=(-1,1)`,
`e(x)=3x+1`, and scalar `a=2`.  The transformed density is `2/9`. -/
theorem real_quadratic_affine_client :
    ∀ U : Set ℝ,
      IsOpen U →
        U ⊆ (fun x : ℝ => 3 * x + 1) '' Set.Ioo (-1 : ℝ) 1 →
          (volume : Measure ℝ)
              (subgradientImageOn (fun x : ℝ => 2 * ((fun y : ℝ => y ^ 2 / 2) ((x - 1) / 3)))
                ((fun x : ℝ => 3 * x + 1) '' Set.Ioo (-1 : ℝ) 1) U) =
            ENNReal.ofReal (2 / 9) * (volume : Measure ℝ) U := by
  obtain ⟨e, he, hdet⟩ := real_three_affine_equiv
  intro U hU hUD
  have hMA :
    ∀ H : Set ℝ,
      IsOpen H →
        H ⊆ Set.Ioo (-1 : ℝ) 1 →
          (volume : Measure ℝ)
              (subgradientImageOn (fun y : ℝ => y ^ 2 / 2) (Set.Ioo (-1 : ℝ) 1) H) =
            ENNReal.ofReal 1 * (volume : Measure ℝ) H :=
    real_quadratic_domain_MA
  have hefun : (e : ℝ → ℝ) = fun x => 3 * x + 1 := funext he
  have hmain :=
    volume_subgradientImageOn_affine_scalar_covariance (u := fun y : ℝ => y ^ 2 / 2) (e := e)
      (a := 2) (c := 1) (by norm_num) (by norm_num) (Ioo (-1 : ℝ) 1) hMA U hU (by rwa [hefun])
  have hinv : (e.symm : ℝ → ℝ) = fun x => (x - 1) / 3 := by
    funext x
    have h := he (e.symm x)
    rw [e.apply_symm_apply] at h
    linarith
  rw [hefun, hinv, hdet] at hmain
  norm_num [Function.comp_def] at hmain ⊢
  exact hmain

private lemma real_quadratic_convex : ConvexOn ℝ (Ioo (-1 : ℝ) 1) (fun y : ℝ => y ^ 2 / 2) := by
  refine ⟨convex_Ioo _ _, ?_⟩
  intro x _hx y _hy a b ha hb hab
  have hb' : b = 1 - a := by linarith
  have hnon := mul_nonneg (mul_nonneg ha hb) (sq_nonneg (x - y))
  rw [hb'] at hnon ⊢
  change (a * x + (1 - a) * y) ^ 2 / 2 ≤ a * (x ^ 2 / 2) + (1 - a) * (y ^ 2 / 2)
  nlinarith

private lemma shifted_real_quadratic_image {t : ℝ} {G : Set ℝ} (hG : G ⊆ Ioo (-1 : ℝ) 1) :
    subgradientImageOn (fun y : ℝ => y ^ 2 / 2 + t) (Ioo (-1) 1) G = G := by
  have heq :
    subgradientImageOn (fun y : ℝ => y ^ 2 / 2 + t) (Ioo (-1) 1) G =
      subgradientImageOn (fun y : ℝ => y ^ 2 / 2) (Ioo (-1) 1) G := by
    ext p
    constructor
    · rintro ⟨x, hx, hp⟩
      refine ⟨x, hx, ?_⟩
      intro y hy
      have h := hp y hy
      linarith
    · rintro ⟨x, hx, hp⟩
      refine ⟨x, hx, ?_⟩
      intro y hy
      have h := hp y hy
      linarith
  rw [heq, real_quadratic_support_image isOpen_Ioo hG]

theorem actual_varying_quadratic_unit_density :
    ∀ G : Set ℝ,
      IsOpen G →
        G ⊆ Ioo (-1 : ℝ) 1 →
          (volume : Measure ℝ) (subgradientImageOn (fun y : ℝ => y ^ 2 / 2) (Ioo (-1) 1) G) =
            volume G := by
  have hc : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hq :
    TendstoUniformly (fun (_ : ℕ) (y : ℝ) => y ^ 2 / 2) (fun y : ℝ => y ^ 2 / 2) atTop := by
    intro V hV
    exact Eventually.of_forall (fun _ _y => refl_mem_uniformity hV)
  have hu :
    TendstoUniformly (fun (n : ℕ) (y : ℝ) => y ^ 2 / 2 + 1 / ((n : ℝ) + 1))
      (fun y : ℝ => y ^ 2 / 2) atTop := by
    have h := hq.add hc.tendstoUniformly_const
    change
      TendstoUniformly (fun (n : ℕ) (y : ℝ) => y ^ 2 / 2 + 1 / ((n : ℝ) + 1))
        (fun y : ℝ => y ^ 2 / 2 + 0) atTop at h
    simpa only [add_zero] using h
  have h :=
    domain_constant_density_of_locally_uniform (1 : ℝ≥0) isOpen_Ioo
      (fun n => real_quadratic_convex.add (convexOn_const _ (convex_Ioo _ _)))
      (fun n =>
        (by fun_prop : Continuous (fun y : ℝ => y ^ 2 / 2 + 1 / ((n : ℝ) + 1))).continuousOn)
      real_quadratic_convex (by fun_prop : Continuous (fun y : ℝ => y ^ 2 / 2)).continuousOn
      hu.tendstoUniformlyOn.tendstoLocallyUniformlyOn
      (by
        intro n G _hGo hG
        change
          (volume : Measure ℝ)
              (subgradientImageOn (fun y : ℝ => y ^ 2 / 2 + 1 / ((n : ℝ) + 1)) (Ioo (-1) 1) G) =
            (1 : ℝ≥0∞) * volume G
        rw [shifted_real_quadratic_image hG]
        simp)
  simpa using h

private lemma fin0_constant_image (t : ℝ) (G : Set (EuclideanSpace ℝ (Fin 0))) :
    subgradientImageOn (fun _ : EuclideanSpace ℝ (Fin 0) => t) univ G = G := by
  ext p
  constructor
  · rintro ⟨x, hx, _hp⟩
    have hpx : p = x := Subsingleton.elim _ _
    exact hpx.symm ▸ hx
  · intro hp
    refine ⟨p, hp, ?_⟩
    intro y _hy
    have hy : y = p := Subsingleton.elim _ _
    simp [hy]

theorem actual_fin0_unit_density :
    ∀ G : Set (EuclideanSpace ℝ (Fin 0)),
      IsOpen G →
        G ⊆ univ →
          (volume : Measure (EuclideanSpace ℝ (Fin 0)))
              (subgradientImageOn (fun _ => (0 : ℝ)) univ G) =
            volume G := by
  have hc : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have h :=
    domain_constant_density_of_locally_uniform (v := fun _ : EuclideanSpace ℝ (Fin 0) =>
      (0 : ℝ)) (1 : ℝ≥0) isOpen_univ (fun _ => convexOn_const _ convex_univ)
      (fun _ => continuous_const.continuousOn) (convexOn_const _ convex_univ)
      continuous_const.continuousOn
      hc.tendstoUniformly_const.tendstoUniformlyOn.tendstoLocallyUniformlyOn
      (by intro n G _hGo _hG; rw [fin0_constant_image]; simp)
  simpa using h


end RealQuadraticClient

end LetwinDomainAffineAudit

set_option pp.fullNames true in
#print axioms LetwinDomainAffineAudit.real_quadratic_affine_client
set_option pp.fullNames true in
#print axioms LetwinDomainAffineAudit.zero_dimensional_affine_scalar_client

#print axioms LetwinDomainAffineAudit.actual_varying_quadratic_unit_density
#print axioms LetwinDomainAffineAudit.actual_fin0_unit_density
