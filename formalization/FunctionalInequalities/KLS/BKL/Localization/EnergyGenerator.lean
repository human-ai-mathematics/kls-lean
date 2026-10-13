import FunctionalInequalities.KLS.BKL.Localization.CumulantGenerator
import FunctionalInequalities.KLS.BKL.Localization.CovarianceGenerator
import FunctionalInequalities.KLS.BKL.Localization.CumulantDerivative
import FunctionalInequalities.KLS.BKL.Localization.EnergyConjugation
import FunctionalInequalities.KLS.BKL.Localization.NoiseBound
import FunctionalInequalities.Probability.Diffusion.VectorGenerator
import FunctionalInequalities.Analysis.Tensor.EnergyForm

/-!
# The generator of the cumulant energy

The energy tensor, lower tensor and noise tensors of the posterior along the localization (BKL arXiv:2610.05474v1, (81)), and the
chain-rule expression (82) for the generator of `E_m(p) = F(A(p), κ_m(p)(u))` in conjugated coordinates. Proof bodies: GPT
(S-line sub-controller task S-3b-chain); statements by the S-line sub-controller; placement: Claude.
-/

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace ContDiff
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
  FunctionalInequalities.Analysis.BakryEmery FunctionalInequalities.Probability.Diffusion
  FunctionalInequalities.Analysis.CoordinateTensor

namespace FunctionalInequalities.KLS.BKL.Localization

variable {n : ℕ} (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hc : IsCompact (μ : Measure (EuclideanSpace ℝ (Fin n))).support)

def energyTensor (p : Param n) (r : ℕ) (u : EuclideanSpace ℝ (Fin n)) :
    (Fin r → Fin n) → ℝ :=
  fun K => cumulant
    (compactPosterior μ hc p.1 p.2 : Measure (EuclideanSpace ℝ (Fin n))) (r + 1)
    (Fin.cons u fun s =>
      inverseSqrt (cov μ hc p) (EuclideanSpace.basisFun (Fin n) ℝ (K s)))

def lowerTensor (p : Param n) (r : ℕ) (u : EuclideanSpace ℝ (Fin n)) :
    (Fin r → Fin n) → ℝ :=
  fun K => lowerDrift
    (compactPosterior μ hc p.1 p.2 : Measure (EuclideanSpace ℝ (Fin n)))
    (Fin.cons u fun s =>
      inverseSqrt (cov μ hc p) (EuclideanSpace.basisFun (Fin n) ℝ (K s))) 0

def noiseTensor (p : Param n) (r : ℕ) (u : EuclideanSpace ℝ (Fin n))
    (k : Fin n) : (Fin r → Fin n) → ℝ :=
  fun K => cumulant
    (compactPosterior μ hc p.1 p.2 : Measure (EuclideanSpace ℝ (Fin n))) (r + 1 + 1)
    (Fin.cons u
      (Fin.snoc
        (fun s =>
          inverseSqrt (cov μ hc p) (EuclideanSpace.basisFun (Fin n) ℝ (K s)))
        (inverseSqrt (cov μ hc p) (EuclideanSpace.basisFun (Fin n) ℝ k))))

def conjugatedNoiseOperator (p : Param n) (k : Fin n) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  inverseSqrt (cov μ hc p) *
    fderiv ℝ (cov μ hc) p (noise μ hc p k) *
    inverseSqrt (cov μ hc p)

private theorem covariance_contDiff_two :
    ContDiff ℝ 2 (cov μ hc) :=
  (contDiff_posteriorCovariance_joint μ hc).of_le
    (WithTop.coe_le_coe.mpr le_top)

private theorem derivative_cov_inner (p v : Param n)
    (x y : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (fun q => ⟪cov μ hc q x, y⟫) p v =
      ⟪fderiv ℝ (cov μ hc) p v x, y⟫ := by
  have hd : DifferentiableAt ℝ (cov μ hc) p :=
    (covariance_contDiff_two μ hc).contDiffAt.differentiableAt (by norm_num)
  have h := fderiv_clm_comp_apply_vec
    ((innerSL ℝ y).comp (ContinuousLinearMap.apply ℝ _ x)) hd v
  change
    fderiv ℝ (fun q => ⟪y, cov μ hc q x⟫) p v =
      ⟪y, fderiv ℝ (cov μ hc) p v x⟫ at h
  simpa only [real_inner_comm] using h

private theorem derivative_cov_symmetric (p v : Param n) :
    IsSelfAdjoint (fderiv ℝ (cov μ hc) p v) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  have hf :
      (fun q => ⟪cov μ hc q x, y⟫) =
        (fun q => ⟪cov μ hc q y, x⟫) := by
    funext q
    have hs : IsSelfAdjoint (cov μ hc q) :=
      Covariance.operator_isSelfAdjoint _
    calc
      ⟪cov μ hc q x, y⟫ = ⟪x, cov μ hc q y⟫ :=
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hs) x y
      _ = ⟪cov μ hc q y, x⟫ := real_inner_comm _ _
  change
    ⟪fderiv ℝ (cov μ hc) p v x, y⟫ =
      ⟪x, fderiv ℝ (cov μ hc) p v y⟫
  calc
    ⟪fderiv ℝ (cov μ hc) p v x, y⟫ =
        fderiv ℝ (fun q => ⟪cov μ hc q x, y⟫) p v :=
      (derivative_cov_inner μ hc p v x y).symm
    _ = fderiv ℝ (fun q => ⟪cov μ hc q y, x⟫) p v := by rw [hf]
    _ = ⟪fderiv ℝ (cov μ hc) p v y, x⟫ :=
      derivative_cov_inner μ hc p v y x
    _ = ⟪x, fderiv ℝ (cov μ hc) p v y⟫ := real_inner_comm _ _

private theorem derivative_cov_cumulant (p : Param n)
    (x y v : EuclideanSpace ℝ (Fin n)) :
    ⟪fderiv ℝ (cov μ hc) p (v, 0) x, y⟫ =
      cumulant
        (compactPosterior μ hc p.1 p.2 : Measure (EuclideanSpace ℝ (Fin n))) 3
        ![x, y, v] := by
  have hf :
      (fun q => ⟪cov μ hc q x, y⟫) =
        (fun q : Param n =>
          cumulant
            (compactPosterior μ hc q.1 q.2 : Measure (EuclideanSpace ℝ (Fin n)))
            2 ![x, y]) := by
    funext q
    exact inner_cov_apply μ hc q x y
  rw [← derivative_cov_inner μ hc p (v, 0) x y, hf]
  rw [fderiv_cumulant_posterior_apply μ hc (by norm_num)
    (![x, y] : Fin 2 → EuclideanSpace ℝ (Fin n)) p v]
  have ht : Fin.snoc ![x, y] v = (![x, y, v] : Fin 3 → _) := by
    funext i
    fin_cases i <;> rfl
  rw [ht]

private def sandwich
    (P : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) →L[ℝ]
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :=
  ((ContinuousLinearMap.compL ℝ
    (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n))
    (EuclideanSpace ℝ (Fin n))).flip P).comp
    (ContinuousLinearMap.compL ℝ
      (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n))
      (EuclideanSpace ℝ (Fin n)) P)

private theorem covariance_vectorGenerator (hiso : KLS.Isotropic μ) (p : Param n) :
    vectorGenerator (drift μ hc) (noise μ hc) (cov μ hc) p = -cov μ hc p := by
  have hA : ContDiffAt ℝ 2 (cov μ hc) p :=
    (covariance_contDiff_two μ hc).contDiffAt
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℝ
  intro y
  let ℓ :
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ :=
    (innerSL ℝ y).comp (ContinuousLinearMap.apply ℝ _ x)
  have hℓ := vectorGenerator_clm_comp (drift μ hc) (noise μ hc) ℓ hA
  have hs :
      vectorGenerator (drift μ hc) (noise μ hc)
        (fun q => ⟪y, cov μ hc q x⟫) p = -⟪y, cov μ hc p x⟫ := by
    have h := generator_inner_cov μ hc hiso p x y
    simpa only [generator, diffusionGenerator_eq_vectorGenerator, real_inner_comm]
      using h
  calc
    ⟪y, vectorGenerator (drift μ hc) (noise μ hc) (cov μ hc) p x⟫ =
        ℓ (vectorGenerator (drift μ hc) (noise μ hc) (cov μ hc) p) := rfl
    _ = vectorGenerator (drift μ hc) (noise μ hc)
        (fun q => ℓ (cov μ hc q)) p := hℓ.symm
    _ = -⟪y, cov μ hc p x⟫ := hs
    _ = ⟪y, (-cov μ hc p) x⟫ := by
      change -⟪y, cov μ hc p x⟫ = ⟪y, -(cov μ hc p x)⟫
      exact (inner_neg_right y (cov μ hc p x)).symm

theorem inner_energyTensor_self (p : Param n) (r : ℕ) (u : EuclideanSpace ℝ (Fin n)) :
    inner (energyTensor μ hc p r u) (energyTensor μ hc p r u) =
      cumulantEnergy
        (compactPosterior μ hc p.1 p.2 : Measure (EuclideanSpace ℝ (Fin n))) r u := by
  classical
  simp only [CoordinateTensor.inner, energyTensor, cumulantEnergy, pow_two, cov]

theorem sum_inner_noiseTensor_self (p : Param n) (r : ℕ)
    (u : EuclideanSpace ℝ (Fin n)) :
    ∑ k, inner (noiseTensor μ hc p r u k) (noiseTensor μ hc p r u k) =
      cumulantEnergy
        (compactPosterior μ hc p.1 p.2 : Measure (EuclideanSpace ℝ (Fin n)))
        (r + 1) u := by
  classical
  rw [cumulantEnergy_succ_eq]
  simp only [CoordinateTensor.inner, noiseTensor, pow_two]
  rw [Finset.sum_comm]
  rfl

set_option maxHeartbeats 1000000 in
theorem stdMatrix_conjugatedNoiseOperator (hiso : KLS.Isotropic μ)
    (p : Param n) (k : Fin n) :
    stdMatrix (conjugatedNoiseOperator μ hc p k) =
      conjugatedNoiseMatrix μ hc p k := by
  classical
  let P := inverseSqrt (cov μ hc p)
  let D := fderiv ℝ (cov μ hc) p (noise μ hc p k)
  have hP : IsSelfAdjoint P :=
    (Isotropic.compactPosterior_inverseSqrt_spec μ hc hiso p.1 p.2).1
  have hD : IsSelfAdjoint D :=
    derivative_cov_symmetric μ hc p (noise μ hc p k)
  have hsP := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hP
  have hsD := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hD
  have hn :
      noise μ hc p k = (P (EuclideanSpace.basisFun (Fin n) ℝ k), 0) := by
    simp only [noise, P, EuclideanSpace.basisFun_apply]
  ext a b
  change
    ⟪EuclideanSpace.basisFun (Fin n) ℝ a,
      P (D (P (EuclideanSpace.basisFun (Fin n) ℝ b)))⟫ =
      cumulant
        (compactPosterior μ hc p.1 p.2 : Measure (EuclideanSpace ℝ (Fin n))) 3
        ![P (EuclideanSpace.basisFun (Fin n) ℝ a),
          P (EuclideanSpace.basisFun (Fin n) ℝ b),
          P (EuclideanSpace.basisFun (Fin n) ℝ k)]
  calc
    ⟪EuclideanSpace.basisFun (Fin n) ℝ a,
        P (D (P (EuclideanSpace.basisFun (Fin n) ℝ b)))⟫ =
        ⟪P (EuclideanSpace.basisFun (Fin n) ℝ a),
          D (P (EuclideanSpace.basisFun (Fin n) ℝ b))⟫ :=
      (hsP _ _).symm
    _ = ⟪D (P (EuclideanSpace.basisFun (Fin n) ℝ a)),
        P (EuclideanSpace.basisFun (Fin n) ℝ b)⟫ :=
      (hsD _ _).symm
    _ = _ := by
      change
        ⟪fderiv ℝ (cov μ hc) p (noise μ hc p k)
            (P (EuclideanSpace.basisFun (Fin n) ℝ a)),
          P (EuclideanSpace.basisFun (Fin n) ℝ b)⟫ = _
      rw [hn]
      exact derivative_cov_cumulant μ hc p
        (P (EuclideanSpace.basisFun (Fin n) ℝ a))
        (P (EuclideanSpace.basisFun (Fin n) ℝ b))
        (P (EuclideanSpace.basisFun (Fin n) ℝ k))

theorem isSelfAdjoint_conjugatedNoiseOperator (hiso : KLS.Isotropic μ)
    (p : Param n) (k : Fin n) :
    IsSelfAdjoint (conjugatedNoiseOperator μ hc p k) := by
  let P := inverseSqrt (cov μ hc p)
  let D := fderiv ℝ (cov μ hc) p (noise μ hc p k)
  have hP : IsSelfAdjoint P :=
    (Isotropic.compactPosterior_inverseSqrt_spec μ hc hiso p.1 p.2).1
  have hD : IsSelfAdjoint D :=
    derivative_cov_symmetric μ hc p (noise μ hc p k)
  have hsP := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hP
  have hsD := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hD
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  change ⟪P (D (P x)), y⟫ = ⟪x, P (D (P y))⟫
  calc
    ⟪P (D (P x)), y⟫ = ⟪D (P x), P y⟫ := hsP _ _
    _ = ⟪P x, D (P y)⟫ := hsD _ _
    _ = ⟪x, P (D (P y))⟫ := hsP _ _

set_option maxHeartbeats 1000000 in
theorem generator_cumulantEnergy_eq (hiso : KLS.Isotropic μ) {r : ℕ} (hr : 2 ≤ r)
    (u : EuclideanSpace ℝ (Fin n)) (p : Param n) :
    generator μ hc
        (fun q : Param n => cumulantEnergy (compactPosterior μ hc q.1 q.2 : Measure (EuclideanSpace ℝ (Fin n))) r u) p =
      fderiv ℝ (fun q : (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) × ((Fin r → Fin n) → ℝ) =>
          energyForm q.1 q.2) (1, energyTensor μ hc p r u)
          (-1, -(((r : ℝ) + 1) • energyTensor μ hc p r u + lowerTensor μ hc p r u)) +
        (1 / 2 : ℝ) * ∑ k, fderiv ℝ (fderiv ℝ
          (fun q : (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) × ((Fin r → Fin n) → ℝ) =>
            energyForm q.1 q.2)) (1, energyTensor μ hc p r u)
          (conjugatedNoiseOperator μ hc p k, noiseTensor μ hc p r u k)
          (conjugatedNoiseOperator μ hc p k, noiseTensor μ hc p r u k) := by
  classical
  let P := inverseSqrt (cov μ hc p)
  let L := sandwich P
  let dirs (K : Fin r → Fin n) : Fin (r + 1) → EuclideanSpace ℝ (Fin n) :=
    Fin.cons u fun s => P (EuclideanSpace.basisFun (Fin n) ℝ (K s))
  let G₁ : Param n →
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :=
    fun q => L (cov μ hc q)
  let G₂ : Param n → (Fin r → Fin n) → ℝ :=
    fun q K =>
      cumulant
        (compactPosterior μ hc q.1 q.2 : Measure (EuclideanSpace ℝ (Fin n)))
        (r + 1) (dirs K)
  let G := fun q : Param n => (G₁ q, G₂ q)
  let Φ :
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) ×
        ((Fin r → Fin n) → ℝ) → ℝ :=
    fun q => energyForm q.1 q.2
  have hpos (q : Param n) : (cov μ hc q).IsPositive :=
    Isotropic.compactPosterior_covariance_isPositive μ hc hiso q.1 q.2
  have hunit (q : Param n) : IsUnit (cov μ hc q) :=
    Isotropic.compactPosterior_covariance_isUnit μ hc hiso q.1 q.2
  have hP : IsSelfAdjoint P :=
    (Isotropic.compactPosterior_inverseSqrt_spec μ hc hiso p.1 p.2).1
  have hPu : IsUnit P := by
    apply isUnit_of_inner_self_pos P
    intro v hv
    exact
      (Isotropic.compactPosterior_inverseSqrt_spec μ hc hiso p.1 p.2).2.2.1 v hv
  have hroot : P * cov μ hc p * P = 1 :=
    inverseSqrt_mul_mul_inverseSqrt (cov μ hc p) (hpos p) (hunit p)
  have hGp : G p = (1, energyTensor μ hc p r u) := by
    apply Prod.ext
    · exact hroot
    · rfl
  have heq :
      (fun q : Param n =>
        cumulantEnergy
          (compactPosterior μ hc q.1 q.2 : Measure (EuclideanSpace ℝ (Fin n)))
          r u) = Φ ∘ G := by
    funext q
    exact cumulantEnergy_eq_energyForm
      (compactPosterior μ hc q.1 q.2 : Measure (EuclideanSpace ℝ (Fin n)))
      (hpos q) (hunit q) P hP hPu r u
  have hA : ContDiffAt ℝ 2 (cov μ hc) p :=
    (covariance_contDiff_two μ hc).contDiffAt
  have hK (K : Fin r → Fin n) :
      ContDiffAt ℝ 2 (fun q => G₂ q K) p :=
    ((contDiff_cumulant_posterior μ hc (show 1 ≤ r + 1 by omega) (dirs K)).of_le
      (WithTop.coe_le_coe.mpr le_top)).contDiffAt
  have h₁ : ContDiffAt ℝ 2 G₁ p :=
    L.contDiff.contDiffAt.comp p hA
  have h₂ : ContDiffAt ℝ 2 G₂ p :=
    contDiffAt_pi.mpr hK
  have hG : ContDiffAt ℝ 2 G p := h₁.prodMk h₂
  have hΦ : ContDiffAt ℝ 2 Φ (G p) := by
    rw [hGp]
    exact contDiffAt_energyForm 1 isUnit_one (energyTensor μ hc p r u)
  have hv₁ :
      vectorGenerator (drift μ hc) (noise μ hc) G₁ p = -1 := by
    change vectorGenerator (drift μ hc) (noise μ hc)
      (fun q => L (cov μ hc q)) p = -1
    rw [vectorGenerator_clm_comp (drift μ hc) (noise μ hc) L hA,
      covariance_vectorGenerator μ hc hiso p, map_neg]
    change -(P * cov μ hc p * P) = -1
    rw [hroot]
  have hv₂ :
      vectorGenerator (drift μ hc) (noise μ hc) G₂ p =
        -(((r : ℝ) + 1) • energyTensor μ hc p r u + lowerTensor μ hc p r u) := by
    rw [vectorGenerator_pi (drift μ hc) (noise μ hc) hK]
    funext K
    change
      vectorGenerator (drift μ hc) (noise μ hc)
          (fun q : Param n =>
            cumulant
              (compactPosterior μ hc q.1 q.2 : Measure (EuclideanSpace ℝ (Fin n)))
              (r + 1) (dirs K)) p =
        -(((r : ℝ) + 1) *
            cumulant
              (compactPosterior μ hc p.1 p.2 : Measure (EuclideanSpace ℝ (Fin n)))
              (r + 1) (dirs K) +
          lowerDrift
            (compactPosterior μ hc p.1 p.2 : Measure (EuclideanSpace ℝ (Fin n)))
            (dirs K) 0)
    have h := generator_cumulant_posterior μ hc hiso
      (show 3 ≤ r + 1 by omega) (dirs K) 0 p
    rw [generator, diffusionGenerator_eq_vectorGenerator] at h
    simpa only [Nat.cast_succ] using h
  have hv :
      vectorGenerator (drift μ hc) (noise μ hc) G p =
        (-1, -(((r : ℝ) + 1) • energyTensor μ hc p r u + lowerTensor μ hc p r u)) := by
    change
      vectorGenerator (drift μ hc) (noise μ hc)
        (fun q => (G₁ q, G₂ q)) p = _
    rw [vectorGenerator_prodMk (drift μ hc) (noise μ hc) h₁ h₂, hv₁, hv₂]
  have hn (k : Fin n) :
      noise μ hc p k = (P (EuclideanSpace.basisFun (Fin n) ℝ k), 0) := by
    simp only [noise, P, EuclideanSpace.basisFun_apply]
  have hd₁ (k : Fin n) :
      fderiv ℝ G₁ p (noise μ hc p k) = conjugatedNoiseOperator μ hc p k :=
    fderiv_clm_comp_apply_vec L (hA.differentiableAt (by norm_num))
      (noise μ hc p k)
  have hd₂ (k : Fin n) :
      fderiv ℝ G₂ p (noise μ hc p k) = noiseTensor μ hc p r u k := by
    rw [fderiv_pi_apply_vec
      (fun K => (hK K).differentiableAt (by norm_num)) (noise μ hc p k)]
    funext K
    change
      fderiv ℝ
          (fun q : Param n =>
            cumulant
              (compactPosterior μ hc q.1 q.2 : Measure (EuclideanSpace ℝ (Fin n)))
              (r + 1) (dirs K)) p (noise μ hc p k) =
        noiseTensor μ hc p r u k K
    rw [hn, fderiv_cumulant_posterior_apply μ hc
      (show 1 ≤ r + 1 by omega) (dirs K) p
      (P (EuclideanSpace.basisFun (Fin n) ℝ k))]
    exact congrArg
      (cumulant
        (compactPosterior μ hc p.1 p.2 : Measure (EuclideanSpace ℝ (Fin n)))
        (r + 1 + 1))
      (Fin.cons_snoc_eq_snoc_cons u
        (fun s => P (EuclideanSpace.basisFun (Fin n) ℝ (K s)))
        (P (EuclideanSpace.basisFun (Fin n) ℝ k))).symm
  have hd (k : Fin n) :
      fderiv ℝ G p (noise μ hc p k) =
        (conjugatedNoiseOperator μ hc p k, noiseTensor μ hc p r u k) := by
    change fderiv ℝ (fun q => (G₁ q, G₂ q)) p (noise μ hc p k) = _
    rw [fderiv_prodMk_apply_vec
      (h₁.differentiableAt (by norm_num))
      (h₂.differentiableAt (by norm_num)) (noise μ hc p k), hd₁, hd₂]
  rw [heq]
  change diffusionGenerator (drift μ hc) (noise μ hc) (Φ ∘ G) p = _
  rw [diffusionGenerator_comp_of_contDiffAt
    (drift μ hc) (noise μ hc) Φ G p hΦ hG]
  change
    fderiv ℝ Φ (G p) (vectorGenerator (drift μ hc) (noise μ hc) G p) +
      (1 / 2 : ℝ) * ∑ k,
        fderiv ℝ (fderiv ℝ Φ) (G p)
          (fderiv ℝ G p (noise μ hc p k))
          (fderiv ℝ G p (noise μ hc p k)) = _
  rw [hv, hGp]
  simp only [hd]
  rfl

end FunctionalInequalities.KLS.BKL.Localization
