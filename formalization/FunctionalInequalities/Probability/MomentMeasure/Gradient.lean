import FunctionalInequalities.Probability.Support
import FunctionalInequalities.Analysis.Convex.GradientImage
import FunctionalInequalities.Analysis.Convex.GradientInverse
import FunctionalInequalities.Analysis.Convex.Caffarelli
import Mathlib.MeasureTheory.Measure.Tilted

/-!
# Gradient image and inverse of a transporting potential

If `∇u` of a strictly convex `u` pushes an open-positive measure to a measure with support `K`, then `range ∇u = interior K`.
For a given `C¹` convex Lipschitz `u` on `ℝⁿ`, `n > 0`, with `∫ e^{−u} = 1` whose gradient transports `e^{−u} dx` to `1_K e^{−W} dx`
(`K` compact convex with nonempty interior, `W` continuous), strict convexity follows from `strictConvexOn_of_map_gradient`;
hence `∇u` is a homeomorphism `ℝⁿ ≃ₜ interior K`, and with `C^{k+1}` regularity and a positive definite Hessian it has a `C^k`
inverse on `interior K`. The potential is a hypothesis here; its existence and regularity are proved in the CEK modules.
-/

noncomputable section

namespace FunctionalInequalities.Probability.MomentMeasure

open FunctionalInequalities.Analysis

section SupportRange

open Set MeasureTheory
open scoped Topology ENNReal

/-- Let `u` be differentiable and strictly convex with continuous gradient on a proper space. If `∇u` pushes an
open-positive `ν` forward to a measure with support `K`, then `range ∇u = interior K`: the range is open and convex with
closure `K`. -/
theorem range_gradient_eq_interior_of_map_support {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [ProperSpace E]
    [MeasurableSpace E] [BorelSpace E] {u : E → ℝ}
    (hu : StrictConvexOn ℝ univ u) (hd : Differentiable ℝ u)
    (hg : Continuous (gradient u)) (ν : Measure E) [ν.IsOpenPosMeasure]
    {K : Set E} (hs : (ν.map (gradient u)).support = K) :
    range (gradient u) = interior K := by
  have ho := isOpen_range_gradient hu hd
  have hc := convex_range_gradient hu hd
  have hn : (interior (range (gradient u))).Nonempty := by
    rw [ho.interior_eq]
    exact ⟨gradient u 0,mem_range_self 0⟩
  have hh : closure (range (gradient u)) = K :=
    (support_map_eq_closure_range ν hg).symm.trans hs
  rw [← hh,hc.interior_closure_eq_interior_of_nonempty_interior hn,ho.interior_eq]

/-- If `∇u` pushes the tilt of an open-positive `μ` by `−u` (with `e^{−u}` integrable) forward to `1_K e^{−W} μ`, where `K`
is closed and convex with nonempty interior and `W` is continuous, then `range ∇u = interior K`. -/
theorem range_gradient_eq_interior_of_tilted_map {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [ProperSpace E]
    [MeasurableSpace E] [BorelSpace E] {u : E → ℝ}
    (hu : StrictConvexOn ℝ univ u) (hd : Differentiable ℝ u)
    (hg : Continuous (gradient u)) (μ : Measure E) [μ.IsOpenPosMeasure]
    (he : Integrable (fun x => Real.exp (-u x)) μ)
    {K : Set E} (hc : Convex ℝ K) (hK : IsClosed K) (hi : (interior K).Nonempty)
    {W : E → ℝ} (hW : Continuous W)
    (hm : (μ.tilted (-u)).map (gradient u) =
      μ.withDensity (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p)))) :
    range (gradient u) = interior K := by
  let : (μ.tilted (-u)).IsOpenPosMeasure :=
    (absolutelyContinuous_tilted he).isOpenPosMeasure
  apply range_gradient_eq_interior_of_map_support hu hd hg (μ.tilted (-u))
  rw [hm]
  exact support_indicator_exp_neg_eq μ hc hK hi hW

end SupportRange

section TransportRange

open Set MeasureTheory FunctionalInequalities
open scoped Topology

/-- **Gradient image of a moment potential.** Let `u` on `ℝⁿ`, `n > 0`, be `C¹`, convex and Lipschitz with `∫ e^{−u} = 1`,
and let `∇u` transport `e^{−u} dx` to `1_K e^{−W} dx` (`K` compact convex with nonempty interior, `W` continuous). Then
`range ∇u = interior K`. Strict convexity comes from `strictConvexOn_of_map_gradient`. -/
theorem range_gradient_eq_interior_of_map_gradient
    {n : ℕ} (hn : 0 < n) {u : EuclideanSpace ℝ (Fin n) → ℝ} {L : NNReal}
    (hLip : LipschitzWith L u) (hc : ConvexOn ℝ univ u)
    (hnorm : ∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) = 1)
    (hC1 : ContDiff ℝ 1 u)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K) (hKc : Convex ℝ K)
    (hKi : (interior K).Nonempty) {W : EuclideanSpace ℝ (Fin n) → ℝ} (hW : Continuous W)
    (hmap : ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
      (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
        (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p)))) :
    range (gradient u) = interior K := by
  have : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  have hstrict := Analysis.strictConvexOn_of_map_gradient hLip hc hnorm hK hKc
    (hKi.mono interior_subset) hW hmap
  have hexp : Integrable (fun x => Real.exp (-u x)) (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    Integrable.of_integral_ne_zero (by rw [hnorm]; norm_num)
  exact range_gradient_eq_interior_of_tilted_map hstrict
    (hC1.differentiable (by norm_num)) (Analysis.continuous_gradient hC1) volume hexp
    hKc hK.isClosed hKi hW hmap

end TransportRange

section TransportHomeomorphism

open Set MeasureTheory FunctionalInequalities
open scoped Topology

/-- Under the transport hypotheses of `range_gradient_eq_interior_of_map_gradient`, `∇u` is a homeomorphism
`ℝⁿ ≃ₜ interior K`. Regularity of the inverse is not asserted here. -/
theorem exists_gradient_homeomorph_interior_of_map_gradient
    {n : ℕ} (hn : 0 < n) {u : EuclideanSpace ℝ (Fin n) → ℝ} {L : NNReal}
    (hLip : LipschitzWith L u) (hc : ConvexOn ℝ univ u)
    (hnorm : ∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) = 1)
    (hC1 : ContDiff ℝ 1 u)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K) (hKc : Convex ℝ K)
    (hKi : (interior K).Nonempty) {W : EuclideanSpace ℝ (Fin n) → ℝ} (hW : Continuous W)
    (hmap : ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
      (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
        (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p)))) :
    ∃ e : EuclideanSpace ℝ (Fin n) ≃ₜ interior K, ∀ x, (e x : EuclideanSpace ℝ (Fin n)) = gradient u x := by
  have : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  have hs := Analysis.strictConvexOn_of_map_gradient hLip hc hnorm hK hKc
    (hKi.mono interior_subset) hW hmap
  obtain ⟨e,he⟩ := exists_gradient_homeomorph_range hs (hC1.differentiable (by norm_num))
  have hr := range_gradient_eq_interior_of_map_gradient hn hLip hc hnorm hC1 hK hKc hKi hW hmap
  exact ⟨e.trans (Homeomorph.setCongr hr),he⟩

end TransportHomeomorphism

section TransportInverse

open Set MeasureTheory Function FunctionalInequalities
open scoped Topology

/-- Under the same transport hypotheses, if `u` is `C^{k+1}`, `k ≠ 0`, with positive definite Hessian everywhere, some left
inverse `Ψ` of `∇u` satisfies `∇u (Ψ y) = y` on `interior K` and is `C^k` there. -/
theorem exists_regular_inverse_of_map_gradient
    {n : ℕ} (hn : 0 < n) {k : WithTop ℕ∞} (hk : k ≠ 0)
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {L : NNReal}
    (hLip : LipschitzWith L u) (hc : ConvexOn ℝ univ u)
    (hnorm : ∫ x, Real.exp (-u x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) = 1)
    (hu : ContDiff ℝ (k+1) u)
    (hp : ∀ x, (Probability.Stein.hessianMatrix u x).PosDef)
    {K : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K) (hKc : Convex ℝ K)
    (hKi : (interior K).Nonempty) {W : EuclideanSpace ℝ (Fin n) → ℝ} (hW : Continuous W)
    (hmap : ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
      (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
        (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p)))) :
    ∃ Ψ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
      LeftInverse Ψ (gradient u) ∧
      (∀ y ∈ interior K, gradient u (Ψ y) = y) ∧ ContDiffOn ℝ k Ψ (interior K) := by
  have : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  have hs := Analysis.strictConvexOn_of_map_gradient hLip hc hnorm hK hKc
    (hKi.mono interior_subset) hW hmap
  have hd := hu.differentiable (by simp)
  have hi := Analysis.injective_gradient_of_strictConvexOn hd hs
  have hr := range_gradient_eq_interior_of_map_gradient hn hLip hc hnorm
    (hu.of_le (by simp)) hK hKc hKi hW hmap
  refine ⟨invFun (gradient u),leftInverse_invFun hi,?_,?_⟩
  · intro y hy
    exact invFun_eq (show y ∈ range (gradient u) by rwa [hr])
  · rw [← hr]
    exact contDiffOn_invFun_gradient_of_posDef hk hu hs hp

end TransportInverse

end FunctionalInequalities.Probability.MomentMeasure
