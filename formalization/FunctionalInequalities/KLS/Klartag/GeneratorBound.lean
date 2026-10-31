module

public import FunctionalInequalities.Analysis.BakryEmery.Hessian.Diffusion

/-!
# The potential is a Lyapunov function for the moment-coordinate generator

Klartag, *Logarithmically-concave moment measures I*, arXiv:1309.2767v1, Lemma 4.4. For the
operator `L u = ψ^{ij} u_ij - Σ_j ρ_j(∇ψ) u_j` of (56) (`hessianInverseOperator ψ ρ`), a `C²`
potential `ψ` with positive definite Hessian whose gradient takes values in `K`, and condition
(51) `inf_{y ∈ K} ∇ρ(y)·y > -∞`, one has `Lψ ≤ A` on the whole space with
`A = max {0, n - inf_{y ∈ K} ∇ρ(y)·y}` (`MomentMeasure.hessianInverseOperator_self_le`).

Scope: the bound is stated for the operator in the form (56). Its identification with the
Laplacian of `(ℝⁿ, ∇²ψ, e^{-V} dx)` under the transport equation (50) is Lemma 4.3
(`KLS/Klartag/TransportLaplacian.lean`). The transport equation, the smoothness of `ρ` and the
growth condition (49) are not used here: positive definiteness of `∇²ψ` and `∇ψ(ℝⁿ) ⊆ K` are the
consequences of the paper's hypotheses that the proof needs.
-/

@[expose] public section

noncomputable section
open scoped RealInnerProductSpace
open FunctionalInequalities.Analysis.BakryEmery

namespace FunctionalInequalities.Probability.MomentMeasure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Klartag arXiv:1309.2767v1, Lemma 4.4**: `Lψ ≤ max {0, n - inf_{y ∈ K} ∇ρ(y)·y}` everywhere,
for the operator (56). -/
theorem hessianInverseOperator_self_le {ψ ρ : E → ℝ} (hψ : ContDiff ℝ 2 ψ) {K : Set E}
    (hPD : ∀ x, ∀ v : E, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ ψ x v v)
    (hK : ∀ x, gradient ψ x ∈ K)
    (h51 : BddBelow ((fun y => ⟪gradient ρ y, y⟫) '' K)) (x : E) :
    hessianInverseOperator ψ ρ ψ x ≤
      max 0 ((Module.finrank ℝ E : ℝ) - sInf ((fun y => ⟪gradient ρ y, y⟫) '' K)) := by
  rw [hessianInverseOperator_self hψ ρ x (hPD x)]
  have h : sInf ((fun y => ⟪gradient ρ y, y⟫) '' K) ≤
      ⟪gradient ρ (gradient ψ x), gradient ψ x⟫ :=
    csInf_le h51 ⟨gradient ψ x, hK x, rfl⟩
  exact le_max_of_le_right (by linarith)

/-- **Klartag arXiv:1309.2767v1, Lemma 4.4**, existence form: there is `A ≥ 0` with `Lψ ≤ A`
everywhere. -/
theorem exists_hessianInverseOperator_self_le {ψ ρ : E → ℝ} (hψ : ContDiff ℝ 2 ψ) {K : Set E}
    (hPD : ∀ x, ∀ v : E, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ ψ x v v)
    (hK : ∀ x, gradient ψ x ∈ K)
    (h51 : BddBelow ((fun y => ⟪gradient ρ y, y⟫) '' K)) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ x, hessianInverseOperator ψ ρ ψ x ≤ A :=
  ⟨_, le_max_left _ _, hessianInverseOperator_self_le hψ hPD hK h51⟩

end FunctionalInequalities.Probability.MomentMeasure
