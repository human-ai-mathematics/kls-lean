module

public import FunctionalInequalities.KLS.Letwin.SteinKernel

/-!
# Clients of the higher-order Schauder bootstrap

The Euclidean-plane quadratic solves Δw + w = 4 + w with identity leading coefficients,
zero drift and all local hypotheses proved. A second client projects the smooth regular-class
moment map, its transport and its smooth inverse from the original Letwin assumptions.
-/

@[expose] public section
noncomputable section
open Set Metric MeasureTheory
open scoped NNReal ContDiff ENNReal
namespace LetwinBootstrapInductionAudit
open FunctionalInequalities FunctionalInequalities.Analysis
  FunctionalInequalities.Analysis.BakryEmery FunctionalInequalities.Probability.Stein
abbrev E := EuclideanSpace ℝ (Fin 2)

private theorem holder_of_smooth (f : E → ℝ) (hf : ContDiff ℝ ∞ f) (m : ℕ) :
    LocHolderDeriv m f := by
  refine ⟨hf.of_le (natCast_le_infty m), ?_⟩
  exact LocHolderMap.of_contDiff_one (hf.iteratedFDeriv_right (m := 1) (i := m)
    (by change (↑(1 + m : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞); exact WithTop.coe_le_coe.mpr le_top))

def quadratic (x : E) : ℝ := ‖x‖ ^ 2

theorem quadratic_hessian (x : E) :
    fderiv ℝ (fderiv ℝ quadratic) x = 2 • (innerSL ℝ (E := E)) := by
  have hfun : fderiv ℝ quadratic = fun y => 2 • innerSL ℝ y :=
    funext fun y => fderiv_norm_sq_apply y
  rw [hfun]
  exact ((innerSL ℝ (E := E)).hasFDerivAt.const_smul (2 : ℕ)).fderiv

/-- A sixth-order client of the linear theorem with nonzero forcing. -/
theorem quadratic_sixth_order : LocHolderDeriv 6 quadratic := by
  have hw : ContDiff ℝ ∞ quadratic := contDiff_norm_sq ℝ
  let a : Fin 2 → Fin 2 → E → ℝ := fun i j _ => if i = j then 1 else 0
  let b : Fin 2 → E → ℝ := fun _ _ => 0
  let g : E → ℝ := fun x => 4 + quadratic x
  have hell : LocallyUniformElliptic a := by
    intro s _hs
    refine ⟨1, 1, one_pos, le_rfl, fun x _hx ξ => ?_⟩
    have hsum : (∑ i, ∑ j, a i j x * ξ i * ξ j) = ‖ξ‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [a, sq]
    rw [hsum, one_mul]
    exact ⟨le_rfl, le_rfl⟩
  have heq : ∀ x,
      (∑ i, ∑ j, a i j x * fderiv ℝ (fderiv ℝ quadratic) x
        (EuclideanSpace.basisFun (Fin 2) ℝ i) (EuclideanSpace.basisFun (Fin 2) ℝ j)) +
      (∑ i, b i x * fderiv ℝ quadratic x (EuclideanSpace.basisFun (Fin 2) ℝ i)) +
      quadratic x = g x := by
    intro x
    rw [quadratic_hessian]
    simp [a, b, g, Fin.sum_univ_two]
    change 2 * inner ℝ (EuclideanSpace.single 0 1 : E) (EuclideanSpace.single 0 1 : E) +
      2 * inner ℝ (EuclideanSpace.single 1 1 : E) (EuclideanSpace.single 1 1 : E) = 4
    norm_num [EuclideanSpace.inner_single_left]
  exact locHolderDeriv_succ_succ_succ_of_linear_equation (n := 2) le_rfl 3
    (holder_of_smooth _ hw 2) (fun _ _ => LocHolderDeriv.const 4 _)
    (fun _ => LocHolderDeriv.const 4 _) (holder_of_smooth g (contDiff_const.add hw) 4)
    (fun _ i j => by simp only [eq_comm]) hell heq

section Letwin
variable {n : ℕ} (hn : 0 < n) {K : Set (EuclideanSpace ℝ (Fin n))}
  {W : EuclideanSpace ℝ (Fin n) → ℝ} {κ : ℝ}
  (hκ : 0 < κ) (hK : IsCompact K) (hKc : Convex ℝ K) (hKint : (interior K).Nonempty)
  (hW : ContDiff ℝ ∞ W) (hstrong : ConvexOn ℝ univ (fun y => W y - (κ / 2) * ‖y‖ ^ 2))
  (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hμ : (μ : Measure (EuclideanSpace ℝ (Fin n))) =
    (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
      (K.indicator fun p => ENNReal.ofReal (Real.exp (-W p))))
  (hiso : KLS.Isotropic μ)
include hn hκ hK hKc hKint hW hstrong hμ hiso

/-- Smoothness and the smooth inverse at the same original-source transport witness. -/
theorem regular_moment_potential_smooth_client :
    ∃ u : EuclideanSpace ℝ (Fin n) → ℝ,
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).tilted (-u)).map (gradient u) =
        (μ : Measure (EuclideanSpace ℝ (Fin n))) ∧
      ContDiff ℝ ∞ u ∧ (∀ x, (hessianMatrix u x).PosDef) ∧
      ∃ Ψ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
        Function.LeftInverse Ψ (gradient u) ∧
        (∀ y ∈ interior K, gradient u (Ψ y) = y) ∧ ContDiffOn ℝ ∞ Ψ (interior K) := by
  obtain ⟨u, _L, _LF, _T, _hconv, _hl, _hnorm, hmap, _hC1, _hG, _hF, _hd, _hT, _hC2, _hHc,
      hEvery, _hLocal, _he, _hΨ, hsm, _hall, hΨsm⟩ :=
    exists_regular_moment_potential_smooth hn hκ hK hKc hKint hW hstrong μ hμ hiso
  exact ⟨u, hmap, hsm, fun x => (hEvery x).1, hΨsm⟩
/-- The literal kernel formula and coupling at one smooth original-source witness. -/
theorem regular_smooth_stein_kernel_client :
    ∃ (u : EuclideanSpace ℝ (Fin n) → ℝ) (Ψ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
      ContDiff ℝ ∞ u ∧ IsSteinKernel μ (hessianKernel u Ψ) ∧
      (∀ x, (hessianKernel u Ψ x).PosDef) ∧
      ∀ y, hessianKernel u Ψ (gradient u y) = hessianMatrix u y := by
  obtain ⟨u, Ψ, hsm, _hconv, _hnorm, _hmap, _hEvery, _he, _hΨ, _hleft, _hright,
      _hΨsm, hstein, _hsymm, hpos, _hentries, hcouple⟩ :=
    exists_regular_smooth_moment_stein_kernel hn hκ hK hKc hKint hW hstrong μ hμ hiso
  exact ⟨u, Ψ, hsm, hstein, hpos, hcouple⟩

end Letwin
end LetwinBootstrapInductionAudit
#print axioms LetwinBootstrapInductionAudit.quadratic_sixth_order
#print axioms LetwinBootstrapInductionAudit.regular_moment_potential_smooth_client
#print axioms FunctionalInequalities.Analysis.exists_regular_moment_potential_smooth

#print axioms LetwinBootstrapInductionAudit.regular_smooth_stein_kernel_client
#print axioms FunctionalInequalities.Analysis.exists_regular_smooth_moment_stein_kernel
