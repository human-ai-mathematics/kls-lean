import FunctionalInequalities.KLS.CEK.MomentRegularity.Smooth

/-!
# Smoothness of a given moment potential with Lipschitz gradient

Letwin, arXiv:2607.24164v1, Lemma 2.2, given-data form. Let `K` be a compact convex body with nonempty
interior, `W` smooth and convex on `interior K`, and `u` a normalized convex Lipschitz potential with
`(∇u)_* e^{-u} dx = 1_K e^{-W} dx`. If `∇u` is `G`-Lipschitz for some `G`, then `u` is `C∞`, its Hessian
is positive definite everywhere with `log det ∇²u = -u + W(∇u)`, and `∇u : ℝⁿ ≃ₜ int K` has a smooth
inverse on `int K` (`smooth_moment_potential_of_lipschitzWith_gradient`). No uniform convexity of `W`
enters: the gradient Lipschitz constant `G` is an input, and convexity of `W` is used only at gradient
values, which lie in `int K`.

For `W − (κ/2)‖·‖²` convex on `interior K` only (`κ > 0`), the CEK moment potential of an isotropic law
has a `16/κ`-Lipschitz gradient and hence all of the above
(`exists_regular_moment_potential_smooth_on_range`). For the merely convex source class of Letwin
Lemma 2.2, `smooth_moment_potential_of_lipschitzWith_gradient` is applied to a limit potential in
`KLS/Letwin/MomentMap.lean`.
-/

noncomputable section
namespace FunctionalInequalities.Analysis

open Set MeasureTheory
open FunctionalInequalities.Probability.Stein
open scoped ContDiff

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- **A given moment potential with Lipschitz gradient is smooth** (given-data Letwin Lemma 2.2): let
`n > 0`, `K` compact convex with nonempty interior, `W` smooth and convex on `interior K`, and
`μ = 1_K e^{-W} dx` a probability measure. A convex `L`-Lipschitz `u` with `∫ e^{-u} = 1`,
`(∇u)_* e^{-u} dx = μ` and `G`-Lipschitz gradient is `C∞` with locally Hölder derivatives of every order,
its Hessian is positive definite with `log det ∇²u = -u + W(∇u)` at every point, `∇u` is a homeomorphism
`ℝⁿ ≃ₜ interior K`, and some left inverse of `∇u` is smooth on `interior K`. The potential is given;
no uniform convexity of `W` and no isotropy is assumed. -/
theorem smooth_moment_potential_of_lipschitzWith_gradient (hn : 0 < n)
    {K : Set E} (hK : IsCompact K) (hKc : Convex ℝ K) (hKint : (interior K).Nonempty)
    {W : E → ℝ} (hW : ContDiff ℝ ∞ W) (hWc : ConvexOn ℝ (interior K) W)
    (μ : ProbabilityMeasure E)
    (hμ : (μ : Measure E) = (volume : Measure E).withDensity
      (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p))))
    {u : E → ℝ} {L G : NNReal} (hc : ConvexOn ℝ univ u) (hl : LipschitzWith L u)
    (hnorm : (∫ x, Real.exp (-u x) ∂(volume : Measure E)) = 1)
    (hmap : ((volume : Measure E).tilted (-u)).map (gradient u) = (μ : Measure E))
    (hG : LipschitzWith G (gradient u)) :
    ContDiff ℝ ∞ u ∧ (∀ m : ℕ, LocHolderDeriv m u) ∧
      (∀ x, (hessianMatrix u x).PosDef) ∧
      (∀ x, Real.log (hessianMatrix u x).det = -u x + W (gradient u x)) ∧
      (∃ e : E ≃ₜ interior K, ∀ x, (e x : E) = gradient u x) ∧
      ∃ Ψ : E → E, Function.LeftInverse Ψ (gradient u) ∧
        (∀ y ∈ interior K, gradient u (Ψ y) = y) ∧ ContDiffOn ℝ ∞ Ψ (interior K) := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hmap' := hmap.trans hμ
  have hC1 : ContDiff ℝ 1 u :=
    contDiff_one_of_map_gradient hl hc hnorm hK hKc hKint hW.continuous hmap'
  obtain ⟨e, he⟩ := Probability.MomentMeasure.exists_gradient_homeomorph_interior_of_map_gradient
    hn hl hc hnorm hC1 hK hKc hKint hW.continuous hmap'
  have hΩ (x : E) : gradient u x ∈ interior K := by
    rw [← he x]
    exact (e x).property
  -- a strictly positive Hessian cap `Λ = G + 1`
  set Λ : ℝ := (G : ℝ) + 1 with hΛdef
  have hΛ : 0 < Λ := by positivity
  have hΛnn : ((Real.toNNReal Λ : NNReal) : ℝ) = Λ := Real.coe_toNNReal _ hΛ.le
  have hGΛ : LipschitzWith (Real.toNNReal Λ) (gradient u) :=
    hG.weaken (by rw [← NNReal.coe_le_coe, hΛnn]; linarith)
  have hd : ∀ᵐ x ∂(volume : Measure E),
      (hessianMatrix u x).PosDef ∧
      Real.log (hessianMatrix u x).det = -u x + W (gradient u x) ∧
      (Λ • (1 : Matrix (Fin n) (Fin n) ℝ) - hessianMatrix u x).PosSemidef := by
    filter_upwards [ae_hessianMatrix_posDef_log_det_of_map_gradient hn hl hc hnorm hK hKc
      hW.continuous hmap' hC1 hG] with x hx
    refine ⟨hx.1, hx.2.1, ?_⟩
    have hsum := hx.2.2.add
      ((Matrix.PosSemidef.one : (1 : Matrix (Fin n) (Fin n) ℝ).PosSemidef).smul (zero_le_one : (0 : ℝ) ≤ 1))
    convert hsum using 1
    rw [hΛdef, add_smul]
    abel
  have hW1 : ContDiff ℝ 1 W := hW.of_le (WithTop.coe_le_coe.mpr le_top)
  obtain ⟨LF, hF⟩ := exists_lipschitzWith_neg_add_comp_gradient hl hGΛ hW1
  have hw (x h : E) : u (x + h) + u (x - h) - 2 * u x ≤ Λ * ‖h‖ ^ 2 := by
    simpa only [hΛnn] using
      secondDifference_le_of_lipschitzWith_gradient (hC1.differentiable one_ne_zero) hGΛ x h
  obtain ⟨T, hT⟩ := exists_weak_third_derivative_on_range hC1 hc hGΛ hW1 hWc hΩ hF hΛ hd hw
  have hlog : ∀ᵐ x ∂(volume : Measure E),
      (hessianMatrix u x).PosDef ∧
      Real.log (hessianMatrix u x).det = -u x + W (gradient u x) :=
    hd.mono fun _ hx => ⟨hx.1, hx.2.1⟩
  obtain ⟨_hexp, hfirst⟩ :=
    hasWeakDerivAlong_log_det_hessianMatrix_of_weak_tensor hc hl hnorm hC1 hGΛ hW1 hF hlog hT
  have hInv := hasWeakDerivAlong_inverse_hessian_of_logdet hGΛ hF hlog hT
  obtain ⟨hC2, _hHc, hEvery, hLocal⟩ := holder_hessian_of_weak_evolution_fields_on_range hn hΛ hW
    isOpen_interior hWc μ hΩ ⟨hc, hl, hnorm, hmap, hC1, hGΛ, hF, hd, hT, hfirst, hInv⟩
  obtain ⟨hsm, hall⟩ := smooth_of_regular_moment_fields hn hC2 hW hl hG
    (fun x => (hEvery x).1) (fun x => (hEvery x).2.1) hLocal
  have hΨ := Probability.MomentMeasure.exists_regular_inverse_of_map_gradient hn
    (k := ∞) (by simp) hl hc hnorm (by simpa using hsm) (fun x => (hEvery x).1)
    hK hKc hKint hW.continuous hmap'
  exact ⟨hsm, hall, fun x => (hEvery x).1, fun x => (hEvery x).2.1, ⟨e, he⟩, hΨ⟩

/-- **Strong regular class with convexity on the interior only** (strong-class case of Letwin,
arXiv:2607.24164v1, Lemma 2.2): let `n > 0`, `K` compact convex with nonempty interior, `W` smooth
on `ℝⁿ` with `W − (κ/2)‖·‖²` convex on `interior K` (`κ > 0`; nothing is assumed off `interior K`),
and `μ = 1_K e^{-W} dx` an isotropic probability measure. There is a convex Lipschitz moment potential `u` with `∫ e^{-u} = 1`,
`(∇u)_* e^{-u} dx = μ` and `16/κ`-Lipschitz gradient, which is `C∞` with locally Hölder derivatives of
every order, has positive definite Hessian with `log det ∇²u = -u + W(∇u)` everywhere, a gradient
homeomorphism `ℝⁿ ≃ₜ interior K`, and a smooth left inverse of `∇u` on `interior K`. -/
theorem exists_regular_moment_potential_smooth_on_range (hn : 0 < n)
    {K : Set E} (hK : IsCompact K) (hKc : Convex ℝ K) (hKint : (interior K).Nonempty)
    {W : E → ℝ} (hW : ContDiff ℝ ∞ W) {κ : ℝ} (hκ : 0 < κ)
    (hstrong : ConvexOn ℝ (interior K) (fun y => W y - (κ / 2) * ‖y‖ ^ 2))
    (μ : ProbabilityMeasure E)
    (hμ : (μ : Measure E) = (volume : Measure E).withDensity
      (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p))))
    (hiso : KLS.Isotropic μ) :
    ∃ (u : E → ℝ) (L : NNReal), ConvexOn ℝ univ u ∧ LipschitzWith L u ∧
      (∫ x, Real.exp (-u x) ∂(volume : Measure E)) = 1 ∧
      ((volume : Measure E).tilted (-u)).map (gradient u) = (μ : Measure E) ∧
      LipschitzWith (Real.toNNReal (16 / κ)) (gradient u) ∧
      ContDiff ℝ ∞ u ∧ (∀ m : ℕ, LocHolderDeriv m u) ∧
      (∀ x, (hessianMatrix u x).PosDef) ∧
      (∀ x, Real.log (hessianMatrix u x).det = -u x + W (gradient u x)) ∧
      (∃ e : E ≃ₜ interior K, ∀ x, (e x : E) = gradient u x) ∧
      ∃ Ψ : E → E, Function.LeftInverse Ψ (gradient u) ∧
        (∀ y ∈ interior K, gradient u (Ψ y) = y) ∧ ContDiffOn ℝ ∞ Ψ (interior K) := by
  obtain ⟨u, L, hstrict, hl, hnorm, hmap, hC1, ⟨e, he⟩, _⟩ :=
    exists_moment_potential_of_continuousOn hn hK hKc hKint hW.continuous.continuousOn μ hμ hiso
  have hc := hstrict.convexOn
  have hΩ (x : E) : gradient u x ∈ interior K := by
    rw [← he x]
    exact (e x).property
  have hG : LipschitzWith (Real.toNNReal (16 / κ)) (gradient u) :=
    lipschitzWith_gradient_of_map_gradient_on_range hl hc hnorm hK hKc
      (hW.of_le (WithTop.coe_le_coe.mpr le_top)) hκ hstrong hΩ (hmap.trans hμ) hC1
  have hWc : ConvexOn ℝ (interior K) W :=
    UniformConvexOn.convexOn (strongConvexOn_iff_convex.mpr hstrong) fun r => by positivity
  exact ⟨u, L, hc, hl, hnorm, hmap, hG,
    smooth_moment_potential_of_lipschitzWith_gradient hn hK hKc hKint hW hWc μ hμ hc hl hnorm hmap
      hG⟩

end FunctionalInequalities.Analysis
