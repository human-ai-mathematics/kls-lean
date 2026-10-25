import FunctionalInequalities.Analysis.Tensor.Coordinate
import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Inverse
import FunctionalInequalities.Analysis.BakryEmery.Cumulant.Basic
import FunctionalInequalities.Analysis.BakryEmery.Tilt.Temperate
import FunctionalInequalities.Analysis.BakryEmery.Tilt.SquareIntegrable
import FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.Temperate
import FunctionalInequalities.Analysis.BakryEmery.Bochner.Temperate
import FunctionalInequalities.Analysis.BakryEmery.Tilt.Tensor
import FunctionalInequalities.Analysis.BakryEmery.Bochner.Tensor
import solutions.ThmBakryEmeryPoincare
import FunctionalInequalities.KLS.BKL.Localization.Process.Basic
/-!
# Audit: first dependencies of Bizeul–Klartag–Lehec (arXiv:2610.05474v1)

This client checks the 2026-10-07 BKL foundations against nonvacuous instances.

* **Lemma 2.2 (complete).** `norm_le_four_pow_mul_norm_symmetrize` is applied to the all-ones
  tensor with `n = 1`, `k = 3`, `d = 1` (nonzero, both symmetry hypotheses discharged), with
  trailing indices (`k = 4 > 3d`), and in the boundary cases `d = 0` (every tensor, every `k`) and
  `n = 0` (the zero-dimensional coordinate space), with every symmetry premise discharged.
* **Lemma 2.1, operator-domain part (restricted).** The heat-model inverse is instantiated for the
  constructed scaled Gaussian `volume.tilted (-(ρ/2)‖·‖²)` in every finite-dimensional real inner
  product space, with log-concavity, full-dimensional support and the Hessian bound all proved,
  so the existence/uniqueness/norm statement has no open premise. All bounds of (20) and the
  centered-gradient bound (24) are instantiated with `C = 1/ρ` from the BGL certificate.
* **Lemma 3.6 (restricted to compactly supported `C²` tests) and the cumulant identity.** The
  scaled Gaussian is shown to have all exponential moments, so (49), (50) and
  `T_d ⟪v, ·⟫ = κ_{d+1}(v, ·) / d!` apply to it with every premise proved; (50) is instantiated on
  the nonzero bump `φ` (`φ = 1` on the unit ball) for every `d`, including `d = 0`.
* **Coefficient arrays and L² continuity.** The Taylor coefficient arrays of the bump under the
  Gaussian (standard orthonormal basis, every `d`) are symmetric tensors, and `‖T_d f‖ ≤ C_d ‖f‖₂`
  holds on `L²` of the Gaussian.
* **Lemma 3.6 for the class `𝒜` (temperate growth).** (49) and (50) are instantiated for the
  Gaussian (`∇V(x) = ρx`, proved polynomially bounded) on the linear test `⟪v, ·⟫`, which is not
  compactly supported, and so are the integration by parts (15) for two linear tests and the
  Bochner formula (16) with its curvature form (the inequality behind Lemma 3.4).
* **Lemma 3.6 for tensor-valued `u`.** (49) and (50) for the vector-valued test `u = id : V → V`
  and (50) for the quadratic field `⟪c, ·⟫² • (a ⊗ b)` with two non-symmetric trailing indices,
  under the Gaussian; `T_d` is continuous on `L²` also in the Hilbert–Schmidt norm of (29).
* **Corollary 3.7.** A consumer instance on the Gaussian with the (trivial) pair `h = 0`,
  `g = ⟪c, ·⟫` satisfying the relation (30); nontrivial iterates need Lemma 2.1 on `𝒜`.
* **Stress test for (16).** The quadratic test `⟪v, ·⟫²`, whose Hessian does not vanish, and the
  tensor-valued (15) and (16), with the curvature form, for quadratic vector fields.

Nothing here covers a paper: Lemma 2.1 is a restricted counterpart (no class `𝒜`, smooth
representatives or pointwise equation), and Theorem 1.1 is not addressed.
-/

noncomputable section

open MeasureTheory Finset FunctionalInequalities FunctionalInequalities.Analysis.Tensor
  FunctionalInequalities.KLS FunctionalInequalities.KLS.LogConcave
  FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.Semigroup.Generated
open scoped RealInnerProductSpace

namespace BKLFoundationsAudit

/-! ## Lemma 2.2 -/

/-- The all-ones tensor with `k` indices over `Fin n`. -/
def ones (n k : ℕ) : Coord n k := WithLp.toLp 2 fun _ => 1

theorem slotPerm_ones (n k : ℕ) (σ : Equiv.Perm (Fin k)) : slotPerm n k σ (ones n k) = ones n k := by
  ext i
  rw [slotPerm_apply]
  rfl

theorem norm_ones_ne_zero (k : ℕ) : ‖ones 1 k‖ ≠ 0 := by
  intro h
  have h0 : ones 1 k = 0 := norm_eq_zero.mp h
  have := congrArg (fun A : Coord 1 k => A (fun _ => 0)) h0
  simp [ones] at this

/-- A nonzero instance with `d = 1`, `k = 3`: both block symmetries hold, and the bound reads
`‖A‖ ≤ 4 ‖S₂ A‖`. -/
example : ‖ones 1 3‖ ≤ 4 ^ 1 * ‖symmetrize 1 3 (2 * 1) (ones 1 3)‖ :=
  norm_le_four_pow_mul_norm_symmetrize (by norm_num) (ones 1 3)
    (fun σ _ => slotPerm_ones 1 3 σ) (fun σ _ => slotPerm_ones 1 3 σ)

example : ‖ones 1 3‖ ≠ 0 := norm_ones_ne_zero 3

/-- Trailing indices: `k = 4 > 3d` with `d = 1`. -/
example : ‖ones 2 4‖ ≤ 4 ^ 1 * ‖symmetrize 2 4 (2 * 1) (ones 2 4)‖ :=
  norm_le_four_pow_mul_norm_symmetrize (by norm_num) (ones 2 4)
    (fun σ _ => slotPerm_ones 2 4 σ) (fun σ _ => slotPerm_ones 2 4 σ)

theorem eq_one_of_mem_fixingOutside_empty {k : ℕ} {σ : Equiv.Perm (Fin k)}
    (hσ : σ ∈ fixingOutside (∅ : Finset (Fin k))) : σ = 1 := by
  ext x
  simp only [fixingOutside, Finset.mem_filter, Finset.mem_univ, true_and] at hσ
  simp [hσ x (Finset.notMem_empty x)]

theorem slots_zero_zero (k : ℕ) : slots k 0 0 = ∅ := by
  ext p
  simp [slots]

/-- Boundary `d = 0`: both symmetry hypotheses are discharged (only the identity fixes every
position), and the bound is `‖A‖ ≤ ‖S₀ A‖` for every tensor and every `k`. -/
example (n k : ℕ) (A : Coord n k) : ‖A‖ ≤ 4 ^ 0 * ‖symmetrize n k (2 * 0) A‖ :=
  norm_le_four_pow_mul_norm_symmetrize (Nat.zero_le k) A
    (fun σ hσ => by
      rw [slots_zero_zero] at hσ
      rw [eq_one_of_mem_fixingOutside_empty hσ, map_one]
      rfl)
    (fun σ hσ => by
      rw [show 3 * 0 = 0 from rfl, slots_zero_zero] at hσ
      rw [eq_one_of_mem_fixingOutside_empty hσ, map_one]
      rfl)

/-- Boundary `n = 0`: `Coord 0 3` is the zero space, so both symmetries hold for every tensor. -/
example (A : Coord 0 3) : ‖A‖ ≤ 4 ^ 1 * ‖symmetrize 0 3 (2 * 1) A‖ :=
  norm_le_four_pow_mul_norm_symmetrize (by norm_num) A
    (fun _ _ => Subsingleton.elim _ _) (fun _ _ => Subsingleton.elim _ _)

/-! ## Lemma 2.1, operator-domain part, for the scaled Gaussian -/

section Gaussian

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]

open Solutions.ThmBakryEmeryPoincare

section GaussianLaw

omit [CompleteSpace V] [SecondCountableTopology V]
theorem gaussian_logConcave {ρ : ℝ} (hρ : 0 < ρ) : LogConcave (gaussianLaw (V := V) hρ) :=
  logConcave_of_eq_tilted rfl (contDiff_potential ρ).continuous
    (Analysis.BakryEmery.convexOn_of_hessian_ge (contDiff_potential ρ) hρ.le
      fun x v => (bilinearIteratedFDerivTwo_potential ρ x v).ge)

theorem gaussian_interior {ρ : ℝ} (hρ : 0 < ρ) :
    (interior ((gaussianLaw (V := V) hρ : ProbabilityMeasure V) : Measure V).support).Nonempty :=
  interior_support_nonempty_of_eq_tilted (volume : Measure V) rfl

end GaussianLaw

/-- **Nonvacuity of the restricted Lemma 2.1.** For the constructed Gaussian, every centered
`g ∈ L²` has a unique centered preimage under the closed generator `A = T̄†T̄`, with
`‖u‖ ≤ ρ⁻¹ ‖g‖`; no premise remains open. -/
theorem gaussian_inverse {ρ : ℝ} (hρ : 0 < ρ)
    (g : Lp ℝ 2 ((gaussianLaw (V := V) hρ : ProbabilityMeasure V) : Measure V))
    (hg : L2.mean (gaussianLaw (V := V) hρ) g = 0) :
    ∃! u : (adjointComp ((gaussian_logConcave hρ).closedWeightedOperator (volume : Measure V)
        (ContinuousLinearMap.id ℝ V) (gaussian_interior hρ))).domain,
      L2.mean (gaussianLaw (V := V) hρ) (u : Lp ℝ 2 ((gaussianLaw (V := V) hρ : ProbabilityMeasure V) : Measure V)) = 0 ∧
        adjointComp ((gaussian_logConcave hρ).closedWeightedOperator (volume : Measure V)
          (ContinuousLinearMap.id ℝ V) (gaussian_interior hρ)) u = g ∧
          ‖(u : Lp ℝ 2 ((gaussianLaw (V := V) hρ : ProbabilityMeasure V) : Measure V))‖ ≤ ρ⁻¹ * ‖g‖ :=
  existsUnique_centered_adjointComp_eq_of_hessian (volume : Measure V) (gaussian_logConcave hρ)
    (gaussian_interior hρ) rfl (contDiff_potential ρ) hρ
    (fun x v => (bilinearIteratedFDerivTwo_potential ρ x v).ge) g hg

/-- BKL (20) and (24) for the Gaussian with `C = 1/ρ`, the constant of the BGL certificate:
`‖u‖ ≤ ρ⁻¹ ‖Au‖`, `‖T̄u‖² = ⟪Au, u⟫ ≤ ρ⁻¹ ‖Au‖²`, `‖T̄u‖ ≤ ρ^{-1/2} ‖Au‖` and
`‖∇₀u‖ ≤ ρ^{-1/2} ‖Au‖` for the centered gradient `∇₀u = T̄u - ∫ T̄u`. -/
theorem gaussian_bounds {ρ : ℝ} (hρ : 0 < ρ)
    (u : (adjointComp ((gaussian_logConcave (V := V) hρ).closedWeightedOperator
      (volume : Measure V) (ContinuousLinearMap.id ℝ V) (gaussian_interior hρ))).domain)
    (hu : L2.mean (gaussianLaw (V := V) hρ)
      (u : Lp ℝ 2 ((gaussianLaw (V := V) hρ : ProbabilityMeasure V) : Measure V)) = 0) :
    let T := (gaussian_logConcave (V := V) hρ).closedWeightedOperator (volume : Measure V)
      (ContinuousLinearMap.id ℝ V) (gaussian_interior hρ)
    let ν : Measure V := ((gaussianLaw (V := V) hρ : ProbabilityMeasure V) : Measure V)
    let w : Lp V 2 ν := T ⟨(u : Lp ℝ 2 ν), u.2.2⟩
    ‖(u : Lp ℝ 2 ν)‖ ≤ ρ⁻¹ * ‖adjointComp T u‖ ∧
      ‖w‖ ^ 2 = ⟪adjointComp T u, (u : Lp ℝ 2 ν)⟫ ∧
      ⟪adjointComp T u, (u : Lp ℝ 2 ν)⟫ ≤ ρ⁻¹ * ‖adjointComp T u‖ ^ 2 ∧
      ‖w‖ ≤ Real.sqrt ρ⁻¹ * ‖adjointComp T u‖ ∧
      ‖w - Lp.const 2 ν (∫ x, (w : V → V) x ∂ν)‖ ≤ Real.sqrt ρ⁻¹ * ‖adjointComp T u‖ := by
  intro T ν w
  have hC : Poincare.LocalSlope.Intrinsic.constant (gaussianLaw (V := V) hρ) ≤
      ((ρ⁻¹).toNNReal : ENNReal) := (gaussian hρ).1
  have hc : (((ρ⁻¹).toNNReal : NNReal) : ℝ) = ρ⁻¹ := Real.coe_toNNReal _ (inv_pos.mpr hρ).le
  have h := centered_adjointComp_bounds (volume : Measure V) (gaussian_logConcave hρ)
    (gaussian_interior hρ) rfl (contDiff_potential ρ) hC u hu
  have hg := norm_centered_gradient_le (volume : Measure V) (gaussian_logConcave hρ)
    (gaussian_interior hρ) rfl (contDiff_potential ρ) hC u hu
  rw [hc] at h hg
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, hg⟩

/-! ## Lemma 3.6 and cumulants for the scaled Gaussian -/

omit [InnerProductSpace ℝ V] [CompleteSpace V] [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V] in
private lemma exp_mul_norm_le_gaussian
    {ρ r : ℝ} (hρ : 0 < ρ) (x : V) :
    Real.exp (-Solutions.ThmBakryEmeryPoincare.potential ρ x) *
        Real.exp (r * ‖x‖) ≤
      Real.exp (r ^ 2 / ρ) *
        Real.exp (-Solutions.ThmBakryEmeryPoincare.potential (ρ / 2) x) := by
  calc
    Real.exp (-Solutions.ThmBakryEmeryPoincare.potential ρ x) *
          Real.exp (r * ‖x‖) =
        Real.exp
          (-Solutions.ThmBakryEmeryPoincare.potential ρ x + r * ‖x‖) := by
      rw [← Real.exp_add]
    _ ≤ Real.exp
          (r ^ 2 / ρ -
            Solutions.ThmBakryEmeryPoincare.potential (ρ / 2) x) := by
      apply Real.exp_le_exp.mpr
      dsimp [Solutions.ThmBakryEmeryPoincare.potential]
      have hs :
          ρ *
              (-(ρ / 2 * ‖x‖ ^ 2) + r * ‖x‖ +
                ρ / 4 * ‖x‖ ^ 2) ≤ r ^ 2 := by
        nlinarith [sq_nonneg (ρ * ‖x‖ / 2 - r)]
      have ha :
          -(ρ / 2 * ‖x‖ ^ 2) + r * ‖x‖ + ρ / 4 * ‖x‖ ^ 2
            ≤ r ^ 2 / ρ := by
        apply (le_div_iff₀ hρ).2
        simpa [mul_comm] using hs
      nlinarith
    _ = Real.exp (r ^ 2 / ρ) *
          Real.exp (-Solutions.ThmBakryEmeryPoincare.potential (ρ / 2) x) := by
      rw [show
        r ^ 2 / ρ -
            Solutions.ThmBakryEmeryPoincare.potential (ρ / 2) x =
          r ^ 2 / ρ +
            (-Solutions.ThmBakryEmeryPoincare.potential (ρ / 2) x) by ring]
      rw [Real.exp_add]

omit [CompleteSpace V] [SecondCountableTopology V] in
/-- The scaled Gaussian law `volume.tilted (-(ρ/2)‖·‖²)` has all exponential moments. -/
theorem integrable_exp_mul_norm_gaussianLaw {ρ : ℝ} (hρ : 0 < ρ) (r : ℝ) :
    Integrable (fun x : V => Real.exp (r * ‖x‖))
      ((Solutions.ThmBakryEmeryPoincare.gaussianLaw (V := V) hρ : ProbabilityMeasure V) : Measure V) := by
    change Integrable
      (fun x : V => Real.exp (r * ‖x‖))
      (volume.tilted (-Solutions.ThmBakryEmeryPoincare.potential ρ))
    rw [MeasureTheory.integrable_tilted_iff
      (Solutions.ThmBakryEmeryPoincare.integrable_exp_neg_potential hρ)]
    have hg :
        Integrable
          (fun x : V =>
            Real.exp (r ^ 2 / ρ) *
              Real.exp
                (-Solutions.ThmBakryEmeryPoincare.potential (ρ / 2) x))
          volume := by
      simpa [smul_eq_mul] using
        (Solutions.ThmBakryEmeryPoincare.integrable_exp_neg_potential
          (half_pos hρ)).const_mul (Real.exp (r ^ 2 / ρ))
    have hc :
        Continuous
          (fun x : V =>
            Solutions.ThmBakryEmeryPoincare.potential ρ x) := by
      dsimp [Solutions.ThmBakryEmeryPoincare.potential]
      exact continuous_const.mul (continuous_norm.pow 2)
    have hc₂ : Continuous (fun x : V => r * ‖x‖) :=
      continuous_const.mul continuous_norm
    have hcont :
        Continuous
          (fun x : V =>
            Real.exp (-Solutions.ThmBakryEmeryPoincare.potential ρ x) *
              Real.exp (r * ‖x‖)) :=
      (Real.continuous_exp.comp hc.neg).mul
        (Real.continuous_exp.comp hc₂)
    have hmeas :
        AEStronglyMeasurable
          (fun x : V =>
            Real.exp (-Solutions.ThmBakryEmeryPoincare.potential ρ x) *
              Real.exp (r * ‖x‖))
          volume := by
      exact hcont.aestronglyMeasurable
    refine hg.mono' hmeas ?_
    filter_upwards [] with x
    simpa [norm_smul, abs_of_nonneg (Real.exp_nonneg _)] using
      (exp_mul_norm_le_gaussian (ρ := ρ) (r := r) hρ x)

omit [SecondCountableTopology V] in
/-- **Nonvacuity of the restricted Lemma 3.6, (50).** -/
theorem gaussian_taylorTensor {ρ : ℝ} (hρ : 0 < ρ) {f : V → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (d : ℕ) :
    Analysis.BakryEmery.taylorTensor ((volume : Measure V).tilted (-potential ρ))
        (fun x => -Analysis.BakryEmery.weightedLaplacian (potential ρ) f x) (d + 1) =
      symmetrizeML (appendInner (Analysis.BakryEmery.taylorTensor
        ((volume : Measure V).tilted (-potential ρ)) (gradient f) d)) :=
  Analysis.BakryEmery.taylorTensor_neg_weightedLaplacian (volume : Measure V)
    ((contDiff_potential ρ).of_le (by norm_num)) hf hfc (integrable_exp_mul_norm_gaussianLaw hρ) d

/-- The unit bump `φ` (one on the closed unit ball, zero outside the ball of radius two). -/
def bump : ContDiffBump (0 : V) := ⟨1, 2, one_pos, one_lt_two⟩

omit [CompleteSpace V] [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] in
theorem bump_zero : (bump : ContDiffBump (0 : V)) 0 = 1 :=
  ContDiffBump.one_of_mem_closedBall _ (Metric.mem_closedBall_self zero_le_one)

section GaussianBumps

omit [SecondCountableTopology V]
/-- (50) for the nonzero bump test, every `d`. -/
theorem gaussian_taylorTensor_bump {ρ : ℝ} (hρ : 0 < ρ) (d : ℕ) :
    Analysis.BakryEmery.taylorTensor ((volume : Measure V).tilted (-potential ρ))
        (fun x => -Analysis.BakryEmery.weightedLaplacian (potential ρ) (bump : ContDiffBump (0 : V)) x)
        (d + 1) =
      symmetrizeML (appendInner (Analysis.BakryEmery.taylorTensor
        ((volume : Measure V).tilted (-potential ρ)) (gradient (bump : ContDiffBump (0 : V))) d)) :=
  gaussian_taylorTensor hρ (ContDiffBump.contDiff _) (ContDiffBump.hasCompactSupport _) d

/-- (49) for the bump test. -/
theorem gaussian_taylorTensor_one_bump {ρ : ℝ} (hρ : 0 < ρ) (h : Fin 1 → V) :
    Analysis.BakryEmery.taylorTensor ((volume : Measure V).tilted (-potential ρ))
        (fun x => -Analysis.BakryEmery.weightedLaplacian (potential ρ) (bump : ContDiffBump (0 : V)) x)
        1 h =
      ⟪∫ x, gradient (bump : ContDiffBump (0 : V)) x ∂((volume : Measure V).tilted (-potential ρ)),
        h 0⟫ :=
  Analysis.BakryEmery.taylorTensor_one_neg_weightedLaplacian (volume : Measure V)
    ((contDiff_potential ρ).of_le (by norm_num)) (ContDiffBump.contDiff _)
    (ContDiffBump.hasCompactSupport _) (integrable_exp_mul_norm_gaussianLaw hρ) h

end GaussianBumps

omit [CompleteSpace V] [SecondCountableTopology V] in
/-- The cumulant identity for linear functions under the Gaussian. -/
theorem gaussian_cumulant {ρ : ℝ} (hρ : 0 < ρ) (v : V) (d : ℕ) (h : Fin d → V) :
    Analysis.BakryEmery.taylorTensor ((gaussianLaw (V := V) hρ : ProbabilityMeasure V) : Measure V)
        (fun x => ⟪v, x⟫) d h =
      (d.factorial : ℝ)⁻¹ * Analysis.BakryEmery.cumulant
        ((gaussianLaw (V := V) hρ : ProbabilityMeasure V) : Measure V) (d + 1) (Fin.cons v h) :=
  Analysis.BakryEmery.taylorTensor_inner_eq_cumulant _ (integrable_exp_mul_norm_gaussianLaw hρ) v d h


omit [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V] in
/-- `‖∇V(x)‖ ≤ |ρ| (1 + ‖x‖)` for the Gaussian potential `V = (ρ/2)‖·‖²`. -/
theorem norm_gradient_potential_le (ρ : ℝ) (x : V) :
    ‖gradient (potential (V := V) ρ) x‖ ≤ |ρ| * (1 + ‖x‖) ^ 1 := by
  have h : gradient (potential (V := V) ρ) x = ρ • x := by
    apply (InnerProductSpace.toDual ℝ V).injective
    ext w
    simp only [gradient, LinearIsometryEquiv.apply_symm_apply, InnerProductSpace.toDual_apply_apply,
      fderiv_potential_apply, real_inner_smul_left]
  rw [h, norm_smul, Real.norm_eq_abs, pow_one]
  gcongr
  linarith

section GaussianLinearTests

omit [SecondCountableTopology V]
/-- **Nonvacuity of Lemma 3.6 beyond compact support.** For the scaled Gaussian and the linear test
`u = ⟪v, ·⟫` (temperate growth, not compactly supported), (50) holds for every `d`. -/
theorem gaussian_taylorTensor_linear {ρ : ℝ} (hρ : 0 < ρ) (v : V) (d : ℕ) :
    Analysis.BakryEmery.taylorTensor ((volume : Measure V).tilted (-potential ρ))
        (fun x => -Analysis.BakryEmery.weightedLaplacian (potential ρ) (fun y => ⟪v, y⟫) x) (d + 1) =
      symmetrizeML (appendInner (Analysis.BakryEmery.taylorTensor
        ((volume : Measure V).tilted (-potential ρ)) (gradient fun y => ⟪v, y⟫) d)) :=
  Analysis.BakryEmery.taylorTensor_neg_weightedLaplacian_of_hasTemperateGrowth (volume : Measure V)
    ((contDiff_potential ρ).of_le (by norm_num)) (norm_gradient_potential_le ρ)
    (integrable_exp_mul_norm_gaussianLaw hρ) (Function.hasTemperateGrowth_inner_right v) d

/-- (49) for the linear test: `T_1(-ℒ⟪v, ·⟫)(h) = ⟪∫ ∇⟪v, ·⟫ dμ, h₀⟫`. -/
theorem gaussian_taylorTensor_one_linear {ρ : ℝ} (hρ : 0 < ρ) (v : V) (h : Fin 1 → V) :
    Analysis.BakryEmery.taylorTensor ((volume : Measure V).tilted (-potential ρ))
        (fun x => -Analysis.BakryEmery.weightedLaplacian (potential ρ) (fun y => ⟪v, y⟫) x) 1 h =
      ⟪∫ x, gradient (fun y => ⟪v, y⟫) x ∂((volume : Measure V).tilted (-potential ρ)), h 0⟫ :=
  Analysis.BakryEmery.taylorTensor_one_neg_weightedLaplacian_of_hasTemperateGrowth (volume : Measure V)
    ((contDiff_potential ρ).of_le (by norm_num)) (norm_gradient_potential_le ρ)
    (integrable_exp_mul_norm_gaussianLaw hρ) (Function.hasTemperateGrowth_inner_right v) h

end GaussianLinearTests


section GaussianTaylorSymmetry

omit [CompleteSpace V] [SecondCountableTopology V]
/-- **Coordinate bridge.** In the standard orthonormal basis, the Taylor coefficient arrays of the
bump under the Gaussian are symmetric tensors in the sense of Lemma 2.2 (invariant under every
permutation of index positions). -/
theorem gaussian_coordTensor_taylorTensor_symmetric {ρ : ℝ} (hρ : 0 < ρ) (d : ℕ)
    (σ : Equiv.Perm (Fin d)) :
    slotPerm (Module.finrank ℝ V) d σ (coordTensor (stdOrthonormalBasis ℝ V)
        (Analysis.BakryEmery.taylorTensor
          ((gaussianLaw (V := V) hρ : ProbabilityMeasure V) : Measure V)
          (bump : ContDiffBump (0 : V)) d)) =
      coordTensor (stdOrthonormalBasis ℝ V) (Analysis.BakryEmery.taylorTensor
        ((gaussianLaw (V := V) hρ : ProbabilityMeasure V) : Measure V)
        (bump : ContDiffBump (0 : V)) d) :=
  Analysis.BakryEmery.slotPerm_coordTensor_taylorTensor _ _ _
    (Analysis.BakryEmery.contDiff_tiltAverage _ (integrable_exp_mul_norm_gaussianLaw hρ)
      (ContDiffBump.continuous _).aestronglyMeasurable
      (fun x => by simpa [Real.norm_eq_abs, abs_of_nonneg (ContDiffBump.nonneg _)] using
        ContDiffBump.le_one (bump : ContDiffBump (0 : V)) (x := x)))
    d σ

/-- **Continuity of `T_d` on `L²`** for the Gaussian: `‖T_d f‖ ≤ C_d ‖f‖₂`. -/
theorem gaussian_taylorTensor_continuous {ρ : ℝ} (hρ : 0 < ρ) (d : ℕ) :
    ∃ C : ℝ, ∀ f : V → ℝ, MemLp f 2 ((gaussianLaw (V := V) hρ : ProbabilityMeasure V) : Measure V) →
      ‖Analysis.BakryEmery.taylorTensor
          ((gaussianLaw (V := V) hρ : ProbabilityMeasure V) : Measure V) f d‖ ≤
        C * (eLpNorm f 2 ((gaussianLaw (V := V) hρ : ProbabilityMeasure V) : Measure V)).toReal :=
  Analysis.BakryEmery.exists_norm_taylorTensor_le _ (integrable_exp_mul_norm_gaussianLaw hρ) d

end GaussianTaylorSymmetry


omit [SecondCountableTopology V] in
/-- **BKL (15) on `𝒜`** for the Gaussian and two linear tests (not compactly supported):
`∫ (ℒ⟪v, ·⟫) ⟪w, ·⟫ dμ = -∫ ⟪∇⟪v, ·⟫, ∇⟪w, ·⟫⟫ dμ`. -/
theorem gaussian_integration_by_parts_linear {ρ : ℝ} (hρ : 0 < ρ) (v w : V) :
    ∫ x, Analysis.BakryEmery.weightedLaplacian (potential ρ) (fun y => ⟪v, y⟫) x * ⟪w, x⟫
        ∂((volume : Measure V).tilted (-potential ρ)) =
      -∫ x, ⟪gradient (fun y => ⟪v, y⟫) x, gradient (fun y => ⟪w, y⟫) x⟫
        ∂((volume : Measure V).tilted (-potential ρ)) :=
  Analysis.BakryEmery.integral_weightedLaplacian_mul_eq_neg_of_hasTemperateGrowth (volume : Measure V)
    ((contDiff_potential ρ).of_le (by norm_num)) (norm_gradient_potential_le ρ)
    (integrable_exp_mul_norm_gaussianLaw hρ) (Function.hasTemperateGrowth_inner_right v)
    (Function.hasTemperateGrowth_inner_right w)


omit [CompleteSpace V] [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V] in
theorem hasTemperateGrowth_potential (ρ : ℝ) : (potential (V := V) ρ).HasTemperateGrowth :=
  (Function.HasTemperateGrowth.const (ρ / 2)).mul (Function.hasTemperateGrowth_norm_sq V)

section GaussianLinearIdentities

omit [SecondCountableTopology V]
/-- **BKL (16) on `𝒜`** for the Gaussian (`V = (ρ/2)‖·‖²` of temperate growth) and the linear test
`⟪v, ·⟫`, with the curvature form `∫ ‖∇²u‖²_HS + ρ ∫ ‖∇u‖² ≤ ∫ (ℒu)²` of Lemma 3.4. -/
theorem gaussian_bochner_linear {ρ : ℝ} (hρ : 0 < ρ) (v : V) :
    (∫ x, Analysis.BakryEmery.weightedLaplacian (potential ρ) (fun y => ⟪v, y⟫) x ^ 2
        ∂((volume : Measure V).tilted (-potential ρ)) =
      ∫ x, Analysis.BakryEmery.hessianSqStdBasis (fun y => ⟪v, y⟫) x
          ∂((volume : Measure V).tilted (-potential ρ)) +
        ∫ x, bilinearIteratedFDerivTwo ℝ (potential ρ) x (gradient (fun y => ⟪v, y⟫) x)
          (gradient (fun y => ⟪v, y⟫) x) ∂((volume : Measure V).tilted (-potential ρ))) ∧
    (∫ x, Analysis.BakryEmery.hessianSqStdBasis (fun y => ⟪v, y⟫) x
          ∂((volume : Measure V).tilted (-potential ρ)) +
        ρ * ∫ x, ‖gradient (fun y => ⟪v, y⟫) x‖ ^ 2 ∂((volume : Measure V).tilted (-potential ρ)) ≤
      ∫ x, Analysis.BakryEmery.weightedLaplacian (potential ρ) (fun y => ⟪v, y⟫) x ^ 2
        ∂((volume : Measure V).tilted (-potential ρ))) :=
  ⟨Analysis.BakryEmery.integral_weightedLaplacian_sq_eq_of_hasTemperateGrowth (volume : Measure V)
      (hasTemperateGrowth_potential ρ) (integrable_exp_mul_norm_gaussianLaw hρ)
      (Function.hasTemperateGrowth_inner_right v),
    Analysis.BakryEmery.integral_hessianSq_add_le_of_hasTemperateGrowth (volume : Measure V)
      (hasTemperateGrowth_potential ρ) (integrable_exp_mul_norm_gaussianLaw hρ)
      (Function.hasTemperateGrowth_inner_right v)
      (fun x w => (bilinearIteratedFDerivTwo_potential ρ x w).ge)⟩


/-- **Tensor-valued Lemma 3.6.** For the Gaussian and the vector-valued test `u = id : V → V`
(temperate growth, values in the tensor space `V`), (49) and (50) hold for every `d`. -/
theorem gaussian_taylorTensor_vec_id {ρ : ℝ} (hρ : 0 < ρ) (d : ℕ) :
    Analysis.BakryEmery.taylorTensor ((volume : Measure V).tilted (-potential ρ))
        (fun x => -Analysis.BakryEmery.weightedLaplacianVec (potential ρ) (fun y : V => y) x) (d + 1) =
      symmetrizeML (Analysis.BakryEmery.taylorTensor ((volume : Measure V).tilted (-potential ρ))
        (fderiv ℝ fun y : V => y) d).uncurryRight :=
  Analysis.BakryEmery.taylorTensor_neg_weightedLaplacianVec (volume : Measure V)
    ((contDiff_potential ρ).of_le (by norm_num)) (norm_gradient_potential_le ρ)
    (integrable_exp_mul_norm_gaussianLaw hρ) Function.HasTemperateGrowth.id' d

theorem gaussian_taylorTensor_one_vec_id {ρ : ℝ} (hρ : 0 < ρ) (h : Fin 1 → V) :
    Analysis.BakryEmery.taylorTensor ((volume : Measure V).tilted (-potential ρ))
        (fun x => -Analysis.BakryEmery.weightedLaplacianVec (potential ρ) (fun y : V => y) x) 1 h =
      (∫ x, fderiv ℝ (fun y : V => y) x ∂((volume : Measure V).tilted (-potential ρ))) (h 0) :=
  Analysis.BakryEmery.taylorTensor_one_neg_weightedLaplacianVec (volume : Measure V)
    ((contDiff_potential ρ).of_le (by norm_num)) (norm_gradient_potential_le ρ)
    (integrable_exp_mul_norm_gaussianLaw hρ) Function.HasTemperateGrowth.id' h

end GaussianLinearIdentities

omit [CompleteSpace V] [SecondCountableTopology V] in
/-- **Continuity of `T_d` on `L²` in the Hilbert–Schmidt norm** (the norm of BKL (29)) for the
Gaussian, in the standard orthonormal basis. -/
theorem gaussian_coordTensor_taylorTensor_continuous {ρ : ℝ} (hρ : 0 < ρ) (d : ℕ) :
    ∃ C : ℝ, ∀ f : V → ℝ, MemLp f 2 ((gaussianLaw (V := V) hρ : ProbabilityMeasure V) : Measure V) →
      ‖coordTensor (stdOrthonormalBasis ℝ V) (Analysis.BakryEmery.taylorTensor
          ((gaussianLaw (V := V) hρ : ProbabilityMeasure V) : Measure V) f d)‖ ≤
        C * (eLpNorm f 2 ((gaussianLaw (V := V) hρ : ProbabilityMeasure V) : Measure V)).toReal :=
  Analysis.BakryEmery.exists_norm_coordTensor_taylorTensor_le _
    (integrable_exp_mul_norm_gaussianLaw hρ) _ d


section GaussianQuadraticIdentities

omit [SecondCountableTopology V]
/-- **Stress test for (16)**: the quadratic test `u = ⟪v, ·⟫²`, whose Hessian `2 v ⊗ v` does not
vanish. -/
theorem gaussian_bochner_quadratic {ρ : ℝ} (hρ : 0 < ρ) (v : V) :
    ∫ x, Analysis.BakryEmery.weightedLaplacian (potential ρ) (fun y => ⟪v, y⟫ ^ 2) x ^ 2
        ∂((volume : Measure V).tilted (-potential ρ)) =
      ∫ x, Analysis.BakryEmery.hessianSqStdBasis (fun y => ⟪v, y⟫ ^ 2) x
          ∂((volume : Measure V).tilted (-potential ρ)) +
        ∫ x, bilinearIteratedFDerivTwo ℝ (potential ρ) x (gradient (fun y => ⟪v, y⟫ ^ 2) x)
          (gradient (fun y => ⟪v, y⟫ ^ 2) x) ∂((volume : Measure V).tilted (-potential ρ)) :=
  Analysis.BakryEmery.integral_weightedLaplacian_sq_eq_of_hasTemperateGrowth (volume : Measure V)
    (hasTemperateGrowth_potential ρ) (integrable_exp_mul_norm_gaussianLaw hρ)
    ((Function.hasTemperateGrowth_inner_right v).pow 2)

/-- **Stress test for tensor-valued Lemma 3.6**: the quadratic field
`u(x) = ⟪c, x⟫² • (a ⊗ b)` with values in `V →L[ℝ] V` (two trailing indices, not symmetric when `a`
and `b` are linearly independent; for `c ≠ 0` and `a, b ≠ 0` its second derivative does not
vanish). -/
theorem gaussian_taylorTensor_vec_quadratic {ρ : ℝ} (hρ : 0 < ρ) (a b c : V) (d : ℕ) :
    Analysis.BakryEmery.taylorTensor ((volume : Measure V).tilted (-potential ρ))
        (fun x => -Analysis.BakryEmery.weightedLaplacianVec (potential ρ)
          (fun y : V => ⟪c, y⟫ ^ 2 • (innerSL ℝ a).smulRight b) x) (d + 1) =
      symmetrizeML (Analysis.BakryEmery.taylorTensor ((volume : Measure V).tilted (-potential ρ))
        (fderiv ℝ fun y : V => ⟪c, y⟫ ^ 2 • (innerSL ℝ a).smulRight b) d).uncurryRight :=
  Analysis.BakryEmery.taylorTensor_neg_weightedLaplacianVec (volume : Measure V)
    ((contDiff_potential ρ).of_le (by norm_num)) (norm_gradient_potential_le ρ)
    (integrable_exp_mul_norm_gaussianLaw hρ)
    (((Function.hasTemperateGrowth_inner_right c).pow 2).smul
      (Function.HasTemperateGrowth.const ((innerSL ℝ a).smulRight b))) d


/-- **Tensor-valued (16)** for the Gaussian and the quadratic vector field `u(x) = ⟪c, x⟫² • a` with
values in `V`, with the curvature form of Lemma 3.4. -/
theorem gaussian_tensor_bochner_quadratic {ρ : ℝ} (hρ : 0 < ρ) (a c : V) :
    (∫ x, ‖Analysis.BakryEmery.weightedLaplacianVec (potential ρ) (fun y : V => ⟪c, y⟫ ^ 2 • a) x‖ ^ 2
        ∂((volume : Measure V).tilted (-potential ρ)) =
      ∫ x, ∑ i, ∑ j, ‖iteratedFDeriv ℝ 2 (fun y : V => ⟪c, y⟫ ^ 2 • a) x
          ![stdOrthonormalBasis ℝ V i, stdOrthonormalBasis ℝ V j]‖ ^ 2
          ∂((volume : Measure V).tilted (-potential ρ)) +
        ∫ x, ∑ i, ∑ j, bilinearIteratedFDerivTwo ℝ (potential ρ) x (stdOrthonormalBasis ℝ V i)
            (stdOrthonormalBasis ℝ V j) *
          ⟪fderiv ℝ (fun y : V => ⟪c, y⟫ ^ 2 • a) x (stdOrthonormalBasis ℝ V i),
            fderiv ℝ (fun y : V => ⟪c, y⟫ ^ 2 • a) x (stdOrthonormalBasis ℝ V j)⟫
          ∂((volume : Measure V).tilted (-potential ρ))) ∧
    (∫ x, ∑ i, ∑ j, ‖iteratedFDeriv ℝ 2 (fun y : V => ⟪c, y⟫ ^ 2 • a) x
          ![stdOrthonormalBasis ℝ V i, stdOrthonormalBasis ℝ V j]‖ ^ 2
          ∂((volume : Measure V).tilted (-potential ρ)) +
        ρ * ∫ x, ∑ i, ‖fderiv ℝ (fun y : V => ⟪c, y⟫ ^ 2 • a) x (stdOrthonormalBasis ℝ V i)‖ ^ 2
          ∂((volume : Measure V).tilted (-potential ρ)) ≤
      ∫ x, ‖Analysis.BakryEmery.weightedLaplacianVec (potential ρ) (fun y : V => ⟪c, y⟫ ^ 2 • a) x‖ ^ 2
        ∂((volume : Measure V).tilted (-potential ρ))) :=
  ⟨Analysis.BakryEmery.integral_norm_sq_weightedLaplacianVec_eq (volume : Measure V)
      (hasTemperateGrowth_potential ρ) (integrable_exp_mul_norm_gaussianLaw hρ)
      (((Function.hasTemperateGrowth_inner_right c).pow 2).smul (Function.HasTemperateGrowth.const a)),
    Analysis.BakryEmery.integral_hessian_add_le_norm_sq_weightedLaplacianVec (volume : Measure V)
      (hasTemperateGrowth_potential ρ) (integrable_exp_mul_norm_gaussianLaw hρ)
      (((Function.hasTemperateGrowth_inner_right c).pow 2).smul (Function.HasTemperateGrowth.const a))
      (fun x w => (bilinearIteratedFDerivTwo_potential ρ x w).ge)⟩


/-- **Tensor-valued (15)** for the Gaussian and two quadratic vector fields. -/
theorem gaussian_tensor_ibp_quadratic {ρ : ℝ} (hρ : 0 < ρ) (a b c e : V) :
    ∫ x, ⟪Analysis.BakryEmery.weightedLaplacianVec (potential ρ) (fun y : V => ⟪c, y⟫ ^ 2 • a) x,
        ⟪e, x⟫ ^ 2 • b⟫ ∂((volume : Measure V).tilted (-potential ρ)) =
      -∫ x, ∑ i, ⟪fderiv ℝ (fun y : V => ⟪c, y⟫ ^ 2 • a) x (stdOrthonormalBasis ℝ V i),
          fderiv ℝ (fun y : V => ⟪e, y⟫ ^ 2 • b) x (stdOrthonormalBasis ℝ V i)⟫
        ∂((volume : Measure V).tilted (-potential ρ)) :=
  Analysis.BakryEmery.integral_inner_weightedLaplacianVec_eq_neg (volume : Measure V)
    ((contDiff_potential ρ).of_le (by norm_num)) (norm_gradient_potential_le ρ)
    (integrable_exp_mul_norm_gaussianLaw hρ)
    (((Function.hasTemperateGrowth_inner_right c).pow 2).smul (Function.HasTemperateGrowth.const a))
    (((Function.hasTemperateGrowth_inner_right e).pow 2).smul (Function.HasTemperateGrowth.const b))


/-- **Corollary 3.7, consumer instance.** For the Gaussian, the zero field `h = 0` and the linear
`g = ⟪c, ·⟫` satisfy the relation (30) (`∇₀g = 0`), so (52) holds for every `α` and `d ≥ 1`. -/
theorem gaussian_corollary_3_7_trivial {ρ : ℝ} (hρ : 0 < ρ) (c : V) (α : ℝ) {d : ℕ} (hd : 1 ≤ d) :
    symmetrizeML (Analysis.BakryEmery.taylorTensor ((volume : Measure V).tilted (-potential ρ))
        (Analysis.BakryEmery.centeredFDeriv ((volume : Measure V).tilted (-potential ρ))
          (fun _ : V => (0 : V →L[ℝ] ℝ))) d).uncurryRight =
        Analysis.BakryEmery.taylorTensor ((volume : Measure V).tilted (-potential ρ))
          (fun x => -Analysis.BakryEmery.weightedLaplacianVec (potential ρ)
            (fun _ : V => (0 : V →L[ℝ] ℝ)) x) (d + 1) ∧
      Analysis.BakryEmery.taylorTensor ((volume : Measure V).tilted (-potential ρ))
          (fun x => -Analysis.BakryEmery.weightedLaplacianVec (potential ρ)
            (fun _ : V => (0 : V →L[ℝ] ℝ)) x) (d + 1) =
        α • Analysis.BakryEmery.taylorTensor ((volume : Measure V).tilted (-potential ρ))
          (Analysis.BakryEmery.centeredFDeriv ((volume : Measure V).tilted (-potential ρ))
            (fun x : V => ⟪c, x⟫)) (d + 1) := by
  have : IsProbabilityMeasure ((volume : Measure V).tilted (-potential ρ)) :=
    (gaussianLaw (V := V) hρ).2
  refine Analysis.BakryEmery.symmetrizeML_taylorTensor_centeredFDeriv (volume : Measure V)
    ((contDiff_potential ρ).of_le (by norm_num)) (norm_gradient_potential_le ρ)
    (integrable_exp_mul_norm_gaussianLaw hρ) (Function.HasTemperateGrowth.const 0) (fun x => ?_) hd
  have hD : ∀ y : V, fderiv ℝ (fun x : V => ⟪c, x⟫) y = innerSL ℝ c := fun y =>
    ((innerSL ℝ c).hasFDerivAt (x := y)).fderiv
  simp [Analysis.BakryEmery.weightedLaplacianVec, Analysis.BakryEmery.centeredFDeriv, hD]

end GaussianQuadraticIdentities

end Gaussian

end BKLFoundationsAudit

/-! ## Axiom reports -/

#print axioms FunctionalInequalities.Analysis.Tensor.norm_le_choose_mul_norm_blockAverage
#print axioms FunctionalInequalities.Analysis.Tensor.norm_le_four_pow_mul_norm_blockAverage
#print axioms FunctionalInequalities.Analysis.Tensor.sum_norm_sq_sum_subset_eq
#print axioms FunctionalInequalities.Analysis.Tensor.norm_le_four_pow_mul_norm_symmetrize
#print axioms FunctionalInequalities.Analysis.Semigroup.Generated.exists_adjointComp_eq_of_gap
#print axioms FunctionalInequalities.Analysis.Semigroup.Generated.eq_of_adjointComp_eq
#print axioms FunctionalInequalities.Analysis.Semigroup.Generated.norm_le_of_gap
#print axioms FunctionalInequalities.KLS.LogConcave.existsUnique_centered_adjointComp_eq
#print axioms FunctionalInequalities.KLS.LogConcave.centered_adjointComp_bounds
#print axioms FunctionalInequalities.KLS.LogConcave.norm_centered_gradient_le
#print axioms FunctionalInequalities.KLS.LogConcave.existsUnique_centered_adjointComp_eq_of_hessian
#print axioms BKLFoundationsAudit.gaussian_inverse
#print axioms BKLFoundationsAudit.gaussian_bounds
#print axioms FunctionalInequalities.Analysis.BakryEmery.tiltAverage_neg_weightedLaplacian
#print axioms FunctionalInequalities.Analysis.BakryEmery.taylorTensor_neg_weightedLaplacian
#print axioms FunctionalInequalities.Analysis.BakryEmery.taylorTensor_one_neg_weightedLaplacian
#print axioms FunctionalInequalities.Analysis.BakryEmery.iteratedFDeriv_comp_perm_of_contDiff
#print axioms FunctionalInequalities.Analysis.BakryEmery.iteratedFDeriv_inner_self_apply
#print axioms FunctionalInequalities.Analysis.BakryEmery.contDiff_tiltAverage
#print axioms FunctionalInequalities.Analysis.BakryEmery.taylorTensor_inner_eq_cumulant
#print axioms FunctionalInequalities.Analysis.Tensor.sum_perm_inner_init_last
#print axioms BKLFoundationsAudit.gaussian_taylorTensor_bump
#print axioms BKLFoundationsAudit.gaussian_taylorTensor_one_bump
#print axioms BKLFoundationsAudit.gaussian_cumulant
#print axioms FunctionalInequalities.Analysis.BakryEmery.integral_weightedLaplacian_eq_zero_of_growth
#print axioms FunctionalInequalities.Analysis.BakryEmery.tiltAverage_neg_weightedLaplacian_of_hasTemperateGrowth
#print axioms FunctionalInequalities.Analysis.BakryEmery.taylorTensor_neg_weightedLaplacian_of_hasTemperateGrowth
#print axioms FunctionalInequalities.Analysis.BakryEmery.taylorTensor_one_neg_weightedLaplacian_of_hasTemperateGrowth
#print axioms BKLFoundationsAudit.gaussian_taylorTensor_linear
#print axioms BKLFoundationsAudit.gaussian_taylorTensor_one_linear
#print axioms FunctionalInequalities.Analysis.Tensor.coordTensor_symmetrizeML
#print axioms FunctionalInequalities.Analysis.Tensor.coordTensor_appendInner
#print axioms FunctionalInequalities.Analysis.Tensor.norm_le_norm_coordTensor
#print axioms FunctionalInequalities.Analysis.BakryEmery.slotPerm_coordTensor_taylorTensor
#print axioms FunctionalInequalities.Analysis.BakryEmery.contDiff_tiltAverage_of_memLp
#print axioms FunctionalInequalities.Analysis.BakryEmery.iteratedFDeriv_integral_exp_inner_smul
#print axioms FunctionalInequalities.Analysis.BakryEmery.taylorTensor_add
#print axioms FunctionalInequalities.Analysis.BakryEmery.exists_norm_taylorTensor_le
#print axioms BKLFoundationsAudit.gaussian_coordTensor_taylorTensor_symmetric
#print axioms BKLFoundationsAudit.gaussian_taylorTensor_continuous
#print axioms FunctionalInequalities.Analysis.BakryEmery.integral_weightedLaplacian_mul_eq_neg_of_hasCompactSupport
#print axioms FunctionalInequalities.Analysis.BakryEmery.integral_weightedLaplacian_mul_eq_neg_of_hasTemperateGrowth
#print axioms FunctionalInequalities.Analysis.BakryEmery.integral_weightedLaplacian_mul_comm_of_hasTemperateGrowth
#print axioms BKLFoundationsAudit.gaussian_integration_by_parts_linear
#print axioms FunctionalInequalities.Analysis.BakryEmery.integral_gammaTwo_eq_of_hasTemperateGrowth
#print axioms FunctionalInequalities.Analysis.BakryEmery.integral_weightedLaplacian_sq_eq_of_hasTemperateGrowth
#print axioms FunctionalInequalities.Analysis.BakryEmery.integral_hessianSq_add_le_of_hasTemperateGrowth
#print axioms FunctionalInequalities.Analysis.BakryEmery.hasTemperateGrowth_weightedLaplacian
#print axioms BKLFoundationsAudit.gaussian_bochner_linear
#print axioms FunctionalInequalities.Analysis.BakryEmery.tiltAverage_neg_weightedLaplacianVec
#print axioms FunctionalInequalities.Analysis.BakryEmery.taylorTensor_neg_weightedLaplacianVec
#print axioms FunctionalInequalities.Analysis.BakryEmery.taylorTensor_one_neg_weightedLaplacianVec
#print axioms FunctionalInequalities.Analysis.Tensor.norm_coordTensor_le
#print axioms FunctionalInequalities.Analysis.BakryEmery.exists_norm_coordTensor_taylorTensor_le
#print axioms BKLFoundationsAudit.gaussian_taylorTensor_vec_id
#print axioms BKLFoundationsAudit.gaussian_taylorTensor_one_vec_id
#print axioms BKLFoundationsAudit.gaussian_coordTensor_taylorTensor_continuous
#print axioms BKLFoundationsAudit.gaussian_bochner_quadratic
#print axioms BKLFoundationsAudit.gaussian_taylorTensor_vec_quadratic
#print axioms FunctionalInequalities.Analysis.BakryEmery.integral_inner_weightedLaplacianVec_eq_neg
#print axioms FunctionalInequalities.Analysis.BakryEmery.integral_norm_sq_weightedLaplacianVec_eq
#print axioms FunctionalInequalities.Analysis.BakryEmery.integral_hessian_add_le_norm_sq_weightedLaplacianVec
#print axioms BKLFoundationsAudit.gaussian_tensor_bochner_quadratic
#print axioms BKLFoundationsAudit.gaussian_tensor_ibp_quadratic
#print axioms FunctionalInequalities.Analysis.BakryEmery.symmetrizeML_taylorTensor_centeredFDeriv
#print axioms FunctionalInequalities.Analysis.BakryEmery.taylorTensor_sub_const
#print axioms BKLFoundationsAudit.gaussian_corollary_3_7_trivial
