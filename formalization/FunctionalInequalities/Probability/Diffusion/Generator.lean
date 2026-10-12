import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Basis.Fin
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# The generator of a diffusion

`diffusionGenerator b σ F x = DF(x)[b x] + ½ Σ_k D²F(x)[σ_k x, σ_k x]` for drift `b` and noise columns
`σ_k`, coordinate-free on a normed space; it is invariant under continuous linear changes of coordinates
(`diffusionGenerator_transport`), which moves a diffusion on a finite-dimensional state space (for BKL
arXiv:2610.05474v1 (67), the parameter space `E × (E →L[ℝ] E)`) to coordinates `Fin N → ℝ`. Proof bodies: GPT (BKL Claude-controller goal, tasks S5cd); statements and placement: Claude.
-/

noncomputable section

namespace FunctionalInequalities.Probability.Diffusion

/-- `𝓛F(x) = DF(x)[b x] + ½ Σ_k D²F(x)[σ_k x, σ_k x]`. -/
noncomputable def diffusionGenerator {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {d : ℕ} (b : V → V) (σ : V → Fin d → V) (F : V → ℝ) (x : V) : ℝ :=
  fderiv ℝ F x (b x) + (1 / 2 : ℝ) * ∑ k, fderiv ℝ (fderiv ℝ F) x (σ x k) (σ x k)

section Adapter
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- Coordinates of a finite-dimensional state space (`N = finrank ℝ V` definitionally). -/
noncomputable def stateEquiv (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] : V ≃L[ℝ] (Fin (Module.finrank ℝ V) → ℝ) :=
  (Module.finBasis ℝ V).equivFun.toContinuousLinearEquiv

/-- Transported drift / noise. -/
noncomputable def transportDrift {V' : Type*} [NormedAddCommGroup V'] [NormedSpace ℝ V']
    (Φ : V ≃L[ℝ] V') (b : V → V) : V' → V' := fun y => Φ (b (Φ.symm y))

noncomputable def transportNoise {V' : Type*} [NormedAddCommGroup V'] [NormedSpace ℝ V']
    {d : ℕ} (Φ : V ≃L[ℝ] V') (σ : V → Fin d → V) : V' → Fin d → V' :=
  fun y k => Φ (σ (Φ.symm y) k)

/-- **S5c.** The coordinate-free generator is invariant under a continuous linear change of
coordinates (no differentiability hypothesis is needed for a linear equivalence). -/
theorem diffusionGenerator_transport {V' : Type*} [NormedAddCommGroup V'] [NormedSpace ℝ V']
    {d : ℕ} (Φ : V ≃L[ℝ] V') (b : V → V) (σ : V → Fin d → V) (F : V → ℝ) (x : V) :
    diffusionGenerator (transportDrift Φ b) (transportNoise Φ σ) (F ∘ Φ.symm) (Φ x) =
      diffusionGenerator b σ F x := by
  have _hcompact := isCompact_closedBall (0 : V) (1 : ℝ)
  let A := Φ.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ)
  have he : fderiv ℝ (F ∘ Φ.symm) = A ∘ ((fderiv ℝ F) ∘ Φ.symm) := by
    funext y
    rw [Φ.symm.comp_right_fderiv]
    ext z
    simp only [Function.comp_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, A, ContinuousLinearEquiv.arrowCongr_apply,
      ContinuousLinearEquiv.refl_apply]
  have h₂ (u : V) :
      fderiv ℝ (fderiv ℝ (F ∘ Φ.symm)) (Φ x) (Φ u) (Φ u) =
        fderiv ℝ (fderiv ℝ F) x u u := by
    rw [he, A.comp_fderiv, Φ.symm.comp_right_fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.symm_apply_apply, A, ContinuousLinearEquiv.arrowCongr_apply,
      ContinuousLinearEquiv.refl_apply]
  have h₁ :
      fderiv ℝ (F ∘ Φ.symm) (Φ x) (Φ (b x)) = fderiv ℝ F x (b x) := by
    rw [Φ.symm.comp_right_fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.symm_apply_apply]
  simp only [diffusionGenerator, transportDrift, transportNoise,
    ContinuousLinearEquiv.symm_apply_apply, h₁, h₂]

end Adapter

end FunctionalInequalities.Probability.Diffusion

namespace FunctionalInequalities.Probability.Diffusion

section S3B1GeneratorChainRule



/-! Chain rule for the generator, the step (82) of BKL (task S3b1; proof body GPT, statement Claude). -/

/-- **Chain rule for the generator** (Itô's formula for a composite, the step (82) of BKL arXiv:2610.05474v1):
`𝓛(Φ ∘ G) = DΦ[DG·b + ½ Σ_k D²G[σ_k, σ_k]] + ½ Σ_k D²Φ[DG·σ_k, DG·σ_k]`. -/
theorem diffusionGenerator_comp {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {d : ℕ} (b : V → V) (σ : V → Fin d → V)
    (Φ : W → ℝ) (G : V → W) (x : V) (hΦ : ContDiff ℝ 2 Φ) (hG : ContDiff ℝ 2 G) :
    diffusionGenerator b σ (Φ ∘ G) x =
      fderiv ℝ Φ (G x) (fderiv ℝ G x (b x) +
          (1 / 2 : ℝ) • ∑ k, fderiv ℝ (fderiv ℝ G) x (σ x k) (σ x k)) +
        (1 / 2 : ℝ) * ∑ k, fderiv ℝ (fderiv ℝ Φ) (G x) (fderiv ℝ G x (σ x k)) (fderiv ℝ G x (σ x k)) := by
  have hΦd : Differentiable ℝ Φ := hΦ.differentiable (by norm_num)
  have hGd : Differentiable ℝ G := hG.differentiable (by norm_num)
  have hΦ₂ : ContDiff ℝ (1 + 1) Φ := by
    convert hΦ using 1; norm_num
  have hG₂ : ContDiff ℝ (1 + 1) G := by
    convert hG using 1; norm_num
  have hΦf : ContDiff ℝ 1 (fderiv ℝ Φ) :=
    (contDiff_succ_iff_fderiv (𝕜 := ℝ) (f := Φ) (n := 1)).mp hΦ₂ |>.2.2
  have hGf : ContDiff ℝ 1 (fderiv ℝ G) :=
    (contDiff_succ_iff_fderiv (𝕜 := ℝ) (f := G) (n := 1)).mp hG₂ |>.2.2
  have hΦfd : Differentiable ℝ (fderiv ℝ Φ) := hΦf.differentiable_one
  have hGfd : Differentiable ℝ (fderiv ℝ G) := hGf.differentiable_one
  have hfirst :
      fderiv ℝ (Φ ∘ G) =
        fun y => fderiv ℝ Φ (G y) ∘SL fderiv ℝ G y := by
    funext y
    simpa only [Function.comp_apply] using
      (fderiv_comp y hΦd.differentiableAt hGd.differentiableAt)
  have hfirst_apply (u : V) :
      fderiv ℝ (Φ ∘ G) x u =
        fderiv ℝ Φ (G x) (fderiv ℝ G x u) := by
    rw [hfirst]
    simp only [ContinuousLinearMap.comp_apply]
  have hc :
      DifferentiableAt ℝ (fun y : V => fderiv ℝ Φ (G y)) x := by
    change DifferentiableAt ℝ ((fderiv ℝ Φ) ∘ G) x
    exact (hΦfd.comp hGd).differentiableAt
  have hd : DifferentiableAt ℝ (fderiv ℝ G) x :=
    hGfd.differentiableAt
  have hcderiv :
      fderiv ℝ (fun y : V => fderiv ℝ Φ (G y)) x =
        fderiv ℝ (fderiv ℝ Φ) (G x) ∘SL fderiv ℝ G x := by
    change fderiv ℝ ((fderiv ℝ Φ) ∘ G) x = _
    exact fderiv_comp x hΦfd.differentiableAt hGd.differentiableAt
  have hdiag (u : V) :
      fderiv ℝ (fderiv ℝ (Φ ∘ G)) x u u =
        fderiv ℝ Φ (G x) (fderiv ℝ (fderiv ℝ G) x u u) +
          fderiv ℝ (fderiv ℝ Φ) (G x) (fderiv ℝ G x u) (fderiv ℝ G x u) := by
    rw [hfirst, fderiv_clm_comp hc hd, hcderiv]
    simp only [add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.compL_apply, ContinuousLinearMap.flip_apply]
  calc
    diffusionGenerator b σ (Φ ∘ G) x =
        fderiv ℝ (Φ ∘ G) x (b x) +
          (1 / 2 : ℝ) * ∑ k,
            fderiv ℝ (fderiv ℝ (Φ ∘ G)) x (σ x k) (σ x k) := rfl
    _ =
        fderiv ℝ Φ (G x) (fderiv ℝ G x (b x)) +
          (1 / 2 : ℝ) * ∑ k,
            (fderiv ℝ Φ (G x) (fderiv ℝ (fderiv ℝ G) x (σ x k) (σ x k)) +
              fderiv ℝ (fderiv ℝ Φ) (G x) (fderiv ℝ G x (σ x k))
                (fderiv ℝ G x (σ x k))) := by
      rw [hfirst_apply]
      exact congrArg
        (fun z : ℝ => fderiv ℝ Φ (G x) (fderiv ℝ G x (b x)) + z)
        (congrArg (fun z : ℝ => (1 / 2 : ℝ) * z)
          (Finset.sum_congr rfl (fun k hk => hdiag (σ x k))))
    _ =
        fderiv ℝ Φ (G x) (fderiv ℝ G x (b x) +
            (1 / 2 : ℝ) • ∑ k,
              fderiv ℝ (fderiv ℝ G) x (σ x k) (σ x k)) +
          (1 / 2 : ℝ) * ∑ k,
            fderiv ℝ (fderiv ℝ Φ) (G x) (fderiv ℝ G x (σ x k))
              (fderiv ℝ G x (σ x k)) := by
      rw [map_add, map_smul, map_sum, Finset.sum_add_distrib]
      simp only [smul_eq_mul]
      ring

end S3B1GeneratorChainRule

end FunctionalInequalities.Probability.Diffusion
