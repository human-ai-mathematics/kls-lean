import FunctionalInequalities.KLS.BKL.Suspension

/-!
# Audit of the convexity step of BKL Proposition 7.1

Source: Bizeul–Klartag–Lehec, arXiv:2610.05474v1, equations (109)–(110), p. 28.
The client retains the finite-copy potential and the Hessian condition. It also exercises a
non-affine quadratic perturbation at equality in (110). No claim of Proposition 7.1 is made.
-/

noncomputable section

open FunctionalInequalities.KLS.BKL.Suspension

namespace BKLSuspensionAudit

/-- The source potential is convex whenever (110) holds. -/
theorem source_convexity {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {V f : E → ℝ} (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 2 f)
    {a M beta : ℝ} (hbeta : 0 < beta)
    (hVlower : ∀ x v, a * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ V x v v)
    (hfbound : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ M)
    (N : ℕ) (hN : beta / Real.sqrt N * M ≤ a) :
    ConvexOn ℝ Set.univ
      (potential V f beta (Real.sqrt (1 + 2 / beta ^ 2)) N) :=
  convexOn_potential hV hf hbeta.le hVlower hfbound N hN

/-- A finite positive `N` can be chosen for each noise parameter, as required in the source. -/
theorem source_copies {a beta M : ℝ} (ha : 0 < a) (hbeta : 0 < beta) (hM : 0 ≤ M) :
    ∃ N : ℕ, 0 < N ∧ beta / Real.sqrt N * M ≤ a :=
  exists_copies ha hbeta.le hM

private def mulBilinear : ℝ →L[ℝ] ℝ →L[ℝ] ℝ :=
  (ContinuousLinearMap.id ℝ ℝ).smulRight (ContinuousLinearMap.id ℝ ℝ)

private theorem hessian_norm_sq (x : ℝ) :
    fderiv ℝ (fderiv ℝ (fun y : ℝ => ‖y‖ ^ 2)) x = (2 : ℝ) • mulBilinear := by
  have hgrad : fderiv ℝ (fun y : ℝ => ‖y‖ ^ 2) =
      fun y => ((2 : ℝ) • mulBilinear) y := by
    funext y
    rw [fderiv_norm_sq_apply]
    ext
    simp [mulBilinear]
  rw [hgrad]
  exact ((2 : ℝ) • mulBilinear).fderiv

/-- Nonvacuity with a non-affine perturbation: `V = f = ‖x‖²`, `a = M = 2`, `beta = 1`,
`N = 1`. The Hessian condition is an equality; the extra coordinate has the source scale `sqrt 3`.
This verifies convexity, without imposing the separate normalization (108). -/
theorem quadratic :
    ConvexOn ℝ Set.univ
      (potential (fun x : ℝ => ‖x‖ ^ 2) (fun x : ℝ => ‖x‖ ^ 2) 1 (Real.sqrt 3) 1) := by
  apply convexOn_potential (contDiff_norm_sq ℝ) (contDiff_norm_sq ℝ)
    (a := 2) (M := 2) (by norm_num)
  · intro x v
    change 2 * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (fun y : ℝ => ‖y‖ ^ 2)) x v v
    rw [hessian_norm_sq]
    change 2 * ‖v‖ ^ 2 ≤ 2 * (v * v)
    rw [Real.norm_eq_abs, sq_abs]
    nlinarith
  · intro x
    rw [hessian_norm_sq]
    apply ((2 : ℝ) • mulBilinear).opNorm_le_bound₂ (by norm_num)
    intro y z
    change ‖2 * (y * z)‖ ≤ 2 * ‖y‖ * ‖z‖
    rw [norm_mul, norm_mul]
    norm_num
    ring_nf
    exact le_rfl
  · norm_num

/-- The continuous potential is available for the density construction. -/
theorem quadratic_continuous : Continuous
    (potential (fun x : ℝ => ‖x‖ ^ 2) (fun x : ℝ => ‖x‖ ^ 2) 1 (Real.sqrt 3) 1) :=
  continuous_potential (by fun_prop) (by fun_prop) _ _ _

end BKLSuspensionAudit

#print axioms FunctionalInequalities.KLS.BKL.Suspension.convexOn_potential
#print axioms FunctionalInequalities.KLS.BKL.Suspension.exists_copies
#print axioms FunctionalInequalities.KLS.BKL.Suspension.continuous_potential
#print axioms BKLSuspensionAudit.source_convexity
#print axioms BKLSuspensionAudit.quadratic
