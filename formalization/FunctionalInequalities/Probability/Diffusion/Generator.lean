import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Basis.Fin

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
