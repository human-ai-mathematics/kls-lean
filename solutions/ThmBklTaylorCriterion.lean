import FunctionalInequalities.KLS.BKL.GaussianTaylor

/-!
# Lean certificate: `thm:bkl-taylor-criterion`

Bizeul–Klartag–Lehec, *Presenting a proof of the Kannan–Lovász–Simonovits conjecture*
(arXiv:2610.05474v1), Theorem 3.1: there is a universal constant `C` such that for every centered,
regular, log-concave probability measure `μ` on `ℝⁿ` with covariance at most the identity, and every
`R ≥ 1` with `|T_d f| ≤ R^d ‖f‖_{L²(μ)}` for all `f ∈ L²(μ)` and `d ≥ 1` (29), `C_P(μ) ≤ C R²`.

The certificate states it in the source form. Regularity is `KLS.RegularPotential V a b` (BKL (12):
`V` smooth with every derivative of polynomial growth, `a Id ≤ ∇²V ≤ b Id`, `a > 0`), the law is
`hV.law = volume.tilted (-V)` (log-concavity is derived), centering is `∫ x dμ = 0`, `Cov μ ≤ Id`
is `∫ ⟪v, x⟫² dμ ≤ ‖v‖²`, the Taylor tensor `T_d f = (1/d!) ∇^d F_f(0)` of the tilt average is
measured in the Hilbert–Schmidt norm of its coefficient array in the standard basis, and `C_P` is
the literature Poincaré constant. The universal constant is explicit in the library
(`PoissonIterate.taylorCriterionConstant = 100 (9 · 2^20)²`) but is not part of the claim.

The proof follows the source's Section 3 through the operator domain of the generator instead of
the class `𝒜` and with an approximate first eigenfunction instead of an exact one
(`research/decisions/2026-10-07-bkl-operator-route.md`); only the value of the constant differs.

`dimZero` discharges every hypothesis in dimension zero, and `gaussian` in dimension one: the
standard Gaussian on `ℝ¹` is regular, centered with covariance one, and satisfies (29) with `R = 8`
(`KLS.gaussian_taylor_hypotheses`), so the hypotheses are jointly satisfiable in positive dimension.
-/

noncomputable section

open MeasureTheory FunctionalInequalities FunctionalInequalities.KLS
open FunctionalInequalities.Analysis.Tensor FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace

namespace Solutions.ThmBklTaylorCriterion

/-- **BKL Theorem 3.1** in the source form, with a positive universal constant. -/
theorem certificate :
    ∃ K : ℝ, 0 < K ∧ ∀ (n : ℕ) (V : EuclideanSpace ℝ (Fin n) → ℝ) (a b : ℝ)
      (hV : KLS.RegularPotential V a b),
      (∫ x, x ∂(hV.law : Measure (EuclideanSpace ℝ (Fin n)))) = 0 →
      (∀ v : EuclideanSpace ℝ (Fin n),
        ∫ x, ⟪v, x⟫ ^ 2 ∂(hV.law : Measure (EuclideanSpace ℝ (Fin n))) ≤ ‖v‖ ^ 2) →
      ∀ R : ℝ, 1 ≤ R →
      (∀ (f : EuclideanSpace ℝ (Fin n) → ℝ),
        MemLp f 2 (hV.law : Measure (EuclideanSpace ℝ (Fin n))) → ∀ d : ℕ, 1 ≤ d →
        ‖coordTensor (EuclideanSpace.basisFun (Fin n) ℝ)
            (taylorTensor (hV.law : Measure (EuclideanSpace ℝ (Fin n))) f d)‖ ≤
          R ^ d * (eLpNorm f 2 (hV.law : Measure (EuclideanSpace ℝ (Fin n)))).toReal) →
      Poincare.LocalSlope.Intrinsic.constant hV.law ≤ ENNReal.ofReal (K * R ^ 2) :=
  KLS.RegularPotential.poincare_le_of_taylor

/-- The zero potential in dimension zero. -/
theorem regularPotential_zero :
    KLS.RegularPotential (fun _ : EuclideanSpace ℝ (Fin 0) => (0 : ℝ)) 1 1 where
  temperate := Function.HasTemperateGrowth.const 0
  pos := one_pos
  lower x v := by
    rw [Subsingleton.elim v 0]
    simp
  upper x v := by
    rw [Subsingleton.elim v 0]
    simp

/-- **Nonvacuity in dimension zero.** The zero potential on `ℝ⁰` is regular, its law is centered
with covariance at most the identity, and (29) holds with `R = 1`: all hypotheses of the
certificate are discharged, and it gives `C_P ≤ K`. -/
theorem dimZero : ∃ K : ℝ,
    Poincare.LocalSlope.Intrinsic.constant regularPotential_zero.law ≤ ENNReal.ofReal (K * 1 ^ 2) := by
  obtain ⟨K, -, hK⟩ := certificate
  refine ⟨K, hK 0 _ 1 1 regularPotential_zero ?_ ?_ 1 le_rfl ?_⟩
  · have h : (fun x : EuclideanSpace ℝ (Fin 0) => x) = fun _ => 0 :=
      funext fun x => Subsingleton.elim x 0
    rw [h, integral_zero]
  · intro v
    rw [Subsingleton.elim v 0]
    simp
  · intro f _ d hd
    have hempty : IsEmpty (Fin d → Fin 0) := by
      have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
      infer_instance
    have h0 : coordTensor (EuclideanSpace.basisFun (Fin 0) ℝ)
        (taylorTensor (regularPotential_zero.law : Measure (EuclideanSpace ℝ (Fin 0))) f d) = 0 :=
      Subsingleton.elim _ _
    rw [h0, norm_zero]
    positivity

/--
info: 'Solutions.ThmBklTaylorCriterion.certificate' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Solutions.ThmBklTaylorCriterion.certificate

/--
info: 'Solutions.ThmBklTaylorCriterion.regularPotential_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Solutions.ThmBklTaylorCriterion.regularPotential_zero

/--
info: 'Solutions.ThmBklTaylorCriterion.dimZero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Solutions.ThmBklTaylorCriterion.dimZero

/-- **Nonvacuity in dimension one.** The standard Gaussian `volume.tilted (-‖x‖²/2)` on `ℝ¹`
satisfies every hypothesis of the certificate with `a = b = 1` and `R = 8`, which gives
`C_P ≤ 64 K`. -/
theorem gaussian : ∃ K : ℝ, Poincare.LocalSlope.Intrinsic.constant
    (KLS.regularPotential_half_norm_sq (E := EuclideanSpace ℝ (Fin 1))).law ≤
      ENNReal.ofReal (K * 8 ^ 2) := by
  obtain ⟨K, -, hK⟩ := certificate
  obtain ⟨hcen, hcov, h29⟩ := KLS.gaussian_taylor_hypotheses
  exact ⟨K, hK 1 _ 1 1 KLS.regularPotential_half_norm_sq hcen hcov 8 (by norm_num) h29⟩

/--
info: 'Solutions.ThmBklTaylorCriterion.gaussian' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Solutions.ThmBklTaylorCriterion.gaussian

end Solutions.ThmBklTaylorCriterion
