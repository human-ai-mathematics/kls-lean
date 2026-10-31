module

public import FunctionalInequalities.KLS.BKL.GaussianTaylor

/-!
# Audit: nonvacuity of BKL Theorem 3.1 in dimension one

Bizeul–Klartag–Lehec (arXiv:2610.05474v1), Theorem 3.1, is the route statement `M`
(`KLS.RegularPotential.poincare_le_of_taylor`, audited in `BKL/TaylorCriterionAudit.lean`). This
client restates its hypotheses for `n = 1`, `V x = ‖x‖² / 2`, `a = b = 1` and `R = 8`, in the
text of `M` with these values substituted, and discharges them by the library theorems of
`KLS/BKL/GaussianTaylor.lean`:

* `regular`: the standard Gaussian potential is regular (`regularPotential_half_norm_sq`);
* `hypotheses`: the law is centered, `∫ ⟪v, x⟫² dγ ≤ ‖v‖²`, and the Taylor bound (29) holds
  with `R = 8` in the Hilbert–Schmidt norm of the standard basis (`gaussian_taylor_hypotheses`);
* `witness`: the conclusion of `M` for this law, `C_P(γ) ≤ K · 8²`
  (`gaussian_poincare_le_of_taylor_witness`).

Together with the dimension-zero witness of `solutions/ThmBklTaylorCriterion.lean`, this shows that
the hypotheses of Theorem 3.1 are jointly satisfiable in positive dimension. It says nothing new
about the Gaussian and is not a step towards the KLS bound (Theorem 1.1).
-/

@[expose] public section

noncomputable section

open MeasureTheory FunctionalInequalities FunctionalInequalities.KLS
open FunctionalInequalities.Analysis.Tensor FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace

namespace BKLGaussianTaylorAudit

/-- The standard Gaussian potential on `ℝ¹` is regular with `a = b = 1` (BKL (12)). -/
theorem regular :
    KLS.RegularPotential (fun x : EuclideanSpace ℝ (Fin 1) => ‖x‖ ^ 2 / 2) 1 1 :=
  regularPotential_half_norm_sq

/-- The hypotheses of `M` for `n = 1`, `V = ‖·‖² / 2`, `a = b = 1`, `R = 8`. -/
theorem hypotheses :
    ∃ hV : KLS.RegularPotential (fun x : EuclideanSpace ℝ (Fin 1) => ‖x‖ ^ 2 / 2) 1 1,
      (∫ x, x ∂(hV.law : Measure (EuclideanSpace ℝ (Fin 1)))) = 0 ∧
      (∀ v : EuclideanSpace ℝ (Fin 1),
        ∫ x, ⟪v, x⟫ ^ 2 ∂(hV.law : Measure (EuclideanSpace ℝ (Fin 1))) ≤ ‖v‖ ^ 2) ∧
      (1 : ℝ) ≤ 8 ∧
      (∀ (f : EuclideanSpace ℝ (Fin 1) → ℝ),
        MemLp f 2 (hV.law : Measure (EuclideanSpace ℝ (Fin 1))) → ∀ d : ℕ, 1 ≤ d →
        ‖coordTensor (EuclideanSpace.basisFun (Fin 1) ℝ)
            (taylorTensor (hV.law : Measure (EuclideanSpace ℝ (Fin 1))) f d)‖ ≤
          (8 : ℝ) ^ d * (eLpNorm f 2 (hV.law : Measure (EuclideanSpace ℝ (Fin 1)))).toReal) :=
  ⟨regularPotential_half_norm_sq, gaussian_taylor_hypotheses.1,
    gaussian_taylor_hypotheses.2.1, by norm_num, gaussian_taylor_hypotheses.2.2⟩

/-- The conclusion of `M` for the standard Gaussian on `ℝ¹`. -/
theorem witness :
    ∃ K : ℝ, ∃ hV : KLS.RegularPotential (fun x : EuclideanSpace ℝ (Fin 1) => ‖x‖ ^ 2 / 2) 1 1,
      Poincare.LocalSlope.Intrinsic.constant hV.law ≤ ENNReal.ofReal (K * 8 ^ 2) := by
  obtain ⟨K, hK⟩ := gaussian_poincare_le_of_taylor_witness
  exact ⟨K, regularPotential_half_norm_sq, hK⟩

end BKLGaussianTaylorAudit

#print axioms BKLGaussianTaylorAudit.regular
#print axioms BKLGaussianTaylorAudit.hypotheses
#print axioms BKLGaussianTaylorAudit.witness
#print axioms FunctionalInequalities.KLS.regularPotential_half_norm_sq
#print axioms FunctionalInequalities.KLS.integral_exp_inner_tilted_half_norm_sq
#print axioms FunctionalInequalities.KLS.integral_id_tilted_half_norm_sq
#print axioms FunctionalInequalities.KLS.integral_inner_sq_tilted_half_norm_sq
#print axioms FunctionalInequalities.KLS.norm_iteratedFDeriv_exp_neg_half_norm_sq_le
#print axioms
  FunctionalInequalities.KLS.norm_iteratedFDeriv_integral_exp_inner_smul_tilted_half_norm_sq_le
#print axioms FunctionalInequalities.KLS.norm_taylorTensor_tilted_half_norm_sq_le
#print axioms FunctionalInequalities.KLS.norm_coordTensor_taylorTensor_tilted_half_norm_sq_le
#print axioms FunctionalInequalities.KLS.gaussian_taylor_hypotheses
#print axioms FunctionalInequalities.KLS.gaussian_poincare_le_of_taylor_witness
