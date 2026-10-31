module

public import FunctionalInequalities.KLS.LogConcave.Regular.Basic
public import FunctionalInequalities.Analysis.BakryEmery.TensorEnergy
public import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.SpectralGap.Temperate
public import solutions.ThmBakryEmeryPoincare

/-!
# Audit: regular laws and the energy recursion (BKL (12), Lemma 3.4, Corollary 3.5)

* **Regular-law adapter.** The scaled Gaussian potential `V = (ρ/2)‖x‖²` satisfies the source's
  regularity (12) with `a = b = ρ` (temperate growth and the Hessian identity are proved here). The
  adapter then derives that `volume.tilted (-V)` is a probability law with all exponential moments,
  and
  the tensor-valued Lemma 3.6, the curvature form of (16) and the operator-domain Lemma 2.1 with
  `C = 1/ρ`, also in its componentwise tensor form, hold for it with no remaining analytic premise.
* **Energy recursion.** Lemma 3.4 is instantiated for the Gaussian law on the pair `g = ⟪c, ·⟫`,
  `h = 0` (which satisfies (30) and (33), since `∇₀g = 0`); Corollary 3.5 is instantiated on an
  explicit
  real sequence and on an explicit chain of iterates through the Poisson-chain endpoint; (36) and
  Lemma 3.2 are instantiated on explicit chains and pairs. The source's
  iterates need Lemma 2.1 on `𝒜` and the first eigenfunction, not proved.
-/

@[expose] public section

noncomputable section

open MeasureTheory FunctionalInequalities FunctionalInequalities.KLS
  FunctionalInequalities.Analysis.BakryEmery FunctionalInequalities.Analysis.Tensor
open scoped RealInnerProductSpace
open Filter Topology

namespace BKLRegularLawAudit

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]

open Solutions.ThmBakryEmeryPoincare

omit [CompleteSpace V] [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
    [FiniteDimensional ℝ V] in
theorem regularPotential_gaussian {ρ : ℝ} (hρ : 0 < ρ) :
    RegularPotential (potential (V := V) ρ) ρ ρ
    where
  temperate :=
    (Function.HasTemperateGrowth.const (ρ / 2)).mul (Function.hasTemperateGrowth_norm_sq V)
  pos := hρ
  lower x v := (bilinearIteratedFDerivTwo_potential ρ x v).ge
  upper x v := (bilinearIteratedFDerivTwo_potential ρ x v).le

/-- The regular law has all exponential moments and is a probability measure (derived). -/
example {ρ : ℝ} (hρ : 0 < ρ) (r : ℝ) :
    IsProbabilityMeasure ((volume : Measure V).tilted (-potential ρ)) ∧
      Integrable (fun x => Real.exp (r * ‖x‖)) ((volume : Measure V).tilted (-potential ρ)) :=
  ⟨(regularPotential_gaussian hρ).isProbabilityMeasure,
    (regularPotential_gaussian hρ).integrable_exp_mul_norm r⟩

/-- Tensor-valued Lemma 3.6 for the regular Gaussian law and `u = id`. -/
example {ρ : ℝ} (hρ : 0 < ρ) (d : ℕ) :
    taylorTensor ((volume : Measure V).tilted (-potential ρ))
        (fun x => -weightedLaplacianVec (potential ρ) (fun y : V => y) x) (d + 1) =
      symmetrizeML (taylorTensor ((volume : Measure V).tilted (-potential ρ))
        (fderiv ℝ fun y : V => y) d).uncurryRight :=
  (regularPotential_gaussian hρ).taylorTensor_neg_weightedLaplacianVec
    Function.HasTemperateGrowth.id' d

/-- The operator-domain Lemma 2.1 for the regular Gaussian law, with `C = 1/ρ`. -/
example {ρ : ℝ} (hρ : 0 < ρ)
    (g :
      Lp ℝ 2 (((regularPotential_gaussian (V := V) hρ).law : ProbabilityMeasure V) : Measure V))
    (hg : L2.mean (regularPotential_gaussian (V := V) hρ).law g = 0) :
    ∃! u :
      (Analysis.Semigroup.adjointComp
          ((regularPotential_gaussian (V := V) hρ).logConcave_law.closedWeightedOperator
            (volume : Measure V) (ContinuousLinearMap.id ℝ V)
            (regularPotential_gaussian (V := V) hρ).interior_support_law)).domain,
      L2.mean (regularPotential_gaussian (V := V) hρ).law
            (u :
              Lp ℝ 2
                (((regularPotential_gaussian (V := V) hρ).law : ProbabilityMeasure V) :
                  Measure V)) =
          0 ∧
        Analysis.Semigroup.adjointComp
              ((regularPotential_gaussian (V := V) hρ).logConcave_law.closedWeightedOperator
                (volume : Measure V) (ContinuousLinearMap.id ℝ V)
                (regularPotential_gaussian (V := V) hρ).interior_support_law)
              u =
            g ∧
          ‖(u :
                Lp ℝ 2
                  (((regularPotential_gaussian (V := V) hρ).law : ProbabilityMeasure V) :
                    Measure V))‖ ≤
            ρ⁻¹ * ‖g‖ :=
  (regularPotential_gaussian hρ).existsUnique_centered_adjointComp_eq g hg

omit [SecondCountableTopology V] in
/-- The componentwise tensor lift of Lemma 2.1 for the regular Gaussian law (`C = 1/ρ`), applied to
`G`-valued centered data in an orthonormal basis. -/
theorem tensor_lift_gaussian {ρ : ℝ} (hρ : 0 < ρ) {G : Type*} [NormedAddCommGroup G]
    [InnerProductSpace ℝ G] [FiniteDimensional ℝ G] {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ G)
    (g : Lp G 2 (((regularPotential_gaussian (V := V) hρ).law : ProbabilityMeasure V) : Measure V))
    (hg : ∫ x, g x ∂(((regularPotential_gaussian (V := V) hρ).law : ProbabilityMeasure V) :
      Measure V) = 0) :
    ∃ u : ι → Lp ℝ 2 (((regularPotential_gaussian (V := V) hρ).law : ProbabilityMeasure V) :
        Measure V),
      (∀ k, L2.mean (regularPotential_gaussian (V := V) hρ).law (u k) = 0) ∧
        ∑ k, ‖u k‖ ^ 2 ≤ ρ⁻¹ ^ 2 * ‖g‖ ^ 2 := by
  obtain ⟨u, ⟨h1, -, h3⟩, -⟩ :=
    (regularPotential_gaussian (V := V) hρ).existsUnique_centered_adjointComp_eq_components b g hg
  exact ⟨fun k => (u k).1, h1, h3⟩

/-- The generator on the class `𝒜` for the regular Gaussian law: the class of the linear function
`⟪c, ·⟫` lies in the domain of `A = T̄†T̄`, with `A [⟪c, ·⟫] = [-ℒ⟪c, ·⟫]`. -/
theorem generator_linear_gaussian {ρ : ℝ} (hρ : 0 < ρ) (c : V) :
    ∃ (hf2 : MemLp (fun x : V => ⟪c, x⟫) 2
        (((regularPotential_gaussian (V := V) hρ).law : ProbabilityMeasure V) : Measure V))
      (hL2 : MemLp (fun x => -weightedLaplacian (potential ρ) (fun x : V => ⟪c, x⟫) x) 2
        (((regularPotential_gaussian (V := V) hρ).law : ProbabilityMeasure V) : Measure V))
      (hmem : hf2.toLp (fun x : V => ⟪c, x⟫) ∈ (Analysis.Semigroup.adjointComp
        ((regularPotential_gaussian (V := V) hρ).logConcave_law.closedWeightedOperator
          (volume : Measure V) (ContinuousLinearMap.id ℝ V)
          (regularPotential_gaussian (V := V) hρ).interior_support_law)).domain),
      Analysis.Semigroup.adjointComp
          ((regularPotential_gaussian (V := V) hρ).logConcave_law.closedWeightedOperator
            (volume : Measure V) (ContinuousLinearMap.id ℝ V)
            (regularPotential_gaussian (V := V) hρ).interior_support_law) ⟨_, hmem⟩ =
        hL2.toLp (fun x => -weightedLaplacian (potential ρ) (fun x : V => ⟪c, x⟫) x) :=
  LogConcave.exists_toLp_mem_adjointComp_domain_of_hasTemperateGrowth (volume : Measure V)
    (regularPotential_gaussian (V := V) hρ).logConcave_law
    (regularPotential_gaussian (V := V) hρ).interior_support_law rfl
    (regularPotential_gaussian (V := V) hρ).temperate
    (regularPotential_gaussian (V := V) hρ).integrable_exp_mul_norm
    (Function.hasTemperateGrowth_inner_right c)

/-- Poincaré on the class `𝒜` for the regular Gaussian law, with `C = 1/ρ` from the Bakry–Émery
bound: `Var f ≤ ρ⁻¹ ∫ ‖∇f‖²` for every `f` of temperate growth. -/
theorem poincare_temperate_gaussian {ρ : ℝ} (hρ : 0 < ρ) {f : V → ℝ} (hf : f.HasTemperateGrowth) :
    ∫ x, (f x - ∫ y, f y ∂(((regularPotential_gaussian (V := V) hρ).law : ProbabilityMeasure V) :
        Measure V)) ^ 2 ∂(((regularPotential_gaussian (V := V) hρ).law : ProbabilityMeasure V) :
        Measure V) ≤
      ρ⁻¹ * ∫ x, ‖gradient f x‖ ^ 2 ∂(((regularPotential_gaussian (V := V) hρ).law :
        ProbabilityMeasure V) : Measure V) := by
  let C : NNReal := ⟨ρ⁻¹, (inv_pos.mpr hρ).le⟩
  have hC : Poincare.LocalSlope.Intrinsic.constant (regularPotential_gaussian (V := V) hρ).law ≤
      (C : ENNReal) := by
    have h := LogConcave.literatureConstant_le_inv (volume : Measure V)
      (regularPotential_gaussian (V := V) hρ).logConcave_law
      (regularPotential_gaussian (V := V) hρ).interior_support_law rfl
      ((regularPotential_gaussian (V := V) hρ).temperate.1.of_le (WithTop.coe_le_coe.mpr le_top))
      hρ (regularPotential_gaussian (V := V) hρ).lower
    rwa [ENNReal.ofReal_eq_coe_nnreal (inv_pos.mpr hρ).le] at h
  exact LogConcave.integral_sq_sub_integral_le_of_hasTemperateGrowth (volume : Measure V)
    (regularPotential_gaussian (V := V) hρ).logConcave_law
    (regularPotential_gaussian (V := V) hρ).interior_support_law
    (regularPotential_gaussian (V := V) hρ).integrable_exp_mul_norm hC hf

section GaussianExamples

omit [SecondCountableTopology V]
/-- The first energy drop of Lemma 3.9 on the regular Gaussian law for the eigenfunction `⟪c, ·⟫`
(`ℒ⟪c, ·⟫ = -ρ ⟪c, ·⟫`; mean zero and covariance `≤ ρ⁻¹` derived from (15) and the Poincaré
inequality on `𝒜`): `‖c‖² ≤ ρ ∫ ⟪c, x⟫²` (the Gaussian attains equality; only the inequality is
proved here). -/
theorem eigen_linear_gaussian {ρ : ℝ} (hρ : 0 < ρ) (c : V) :
    ‖∫ x, gradient (fun y : V => ⟪c, y⟫) x ∂((volume : Measure V).tilted (-potential ρ))‖ ^ 2 ≤
      ρ ^ 2 * ρ⁻¹ * ∫ x, ⟪c, x⟫ ^ 2 ∂((volume : Measure V).tilted (-potential ρ)) := by
  have hR := regularPotential_gaussian (V := V) hρ
  have hP := hR.isProbabilityMeasure
  have hlin : ∀ e : V, (fun y : V => ⟪e, y⟫).HasTemperateGrowth := fun e =>
    Function.hasTemperateGrowth_inner_right e
  have hgrad : ∀ e x, gradient (fun y : V => ⟪e, y⟫) x = e := by
    intro e x
    have hd : fderiv ℝ (fun y : V => ⟪e, y⟫) x = InnerProductSpace.toDual ℝ V e := by
      change fderiv ℝ (⇑(innerSL ℝ e)) x = _
      rw [((innerSL ℝ e).hasFDerivAt (x := x)).fderiv]
      ext y
      simp
    simp only [gradient, hd, LinearIsometryEquiv.symm_apply_apply]
  have hlap : ∀ e x, Laplacian.laplacian (fun y : V => ⟪e, y⟫) x = 0 := by
    intro e x
    have hd : fderiv ℝ (fun y : V => ⟪e, y⟫) = fun _ => innerSL ℝ e := by
      funext y
      exact ((innerSL ℝ e).hasFDerivAt (x := y)).fderiv
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
    simp [iteratedFDeriv_two_apply, hd]
  have hgV : ∀ x : V, gradient (potential (V := V) ρ) x = ρ • x := by
    intro x
    apply (InnerProductSpace.toDual ℝ V).injective
    ext w
    simp only [gradient, LinearIsometryEquiv.apply_symm_apply, InnerProductSpace.toDual_apply_apply]
    rw [fderiv_potential_apply, real_inner_smul_left]
  have heig : ∀ e x, Analysis.BakryEmery.weightedLaplacian (potential ρ) (fun y : V => ⟪e, y⟫) x =
      -ρ * ⟪e, x⟫ := by
    intro e x
    rw [Analysis.BakryEmery.weightedLaplacian_apply, hlap, hgrad, hgV, real_inner_smul_left,
      real_inner_comm]
    ring
  have hmean : ∀ e : V, ∫ x, ⟪e, x⟫ ∂((volume : Measure V).tilted (-potential ρ)) = 0 := by
    intro e
    have hU1 : ContDiff ℝ 1 (potential (V := V) ρ) := hR.temperate.1.of_le (by simp)
    obtain ⟨k, Cb, hCb⟩ := hR.temperate.2 1
    have hUg : ∀ x : V, ‖gradient (potential ρ) x‖ ≤ Cb * (1 + ‖x‖) ^ k := fun x => by
      rw [norm_gradient_eq_norm_iteratedFDeriv_one]; exact hCb x
    have hibp := Analysis.BakryEmery.integral_weightedLaplacian_mul_eq_neg_of_hasTemperateGrowth
      (volume : Measure V) hU1 hUg hR.integrable_exp_mul_norm (hlin e)
      (Function.HasTemperateGrowth.const (1 : ℝ))
    have h0 : ∀ x, gradient (fun _ : V => (1 : ℝ)) x = 0 := fun x => by simp [gradient]
    simp only [mul_one, h0, inner_zero_right, integral_zero, neg_zero, heig] at hibp
    have : ∫ x, -ρ * ⟪e, x⟫ ∂((volume : Measure V).tilted (-potential ρ)) =
        -ρ * ∫ x, ⟪e, x⟫ ∂((volume : Measure V).tilted (-potential ρ)) := integral_const_mul _ _
    rw [this] at hibp
    rcases mul_eq_zero.mp hibp with h | h
    · linarith
    · exact h
  have hcov : ∀ e : V, ∫ x, ⟪e, x - ∫ y, y ∂((volume : Measure V).tilted (-potential ρ))⟫ ^ 2
      ∂((volume : Measure V).tilted (-potential ρ)) ≤ ρ⁻¹ * ‖e‖ ^ 2 := by
    intro e
    have hid : Integrable (fun y : V => y) ((volume : Measure V).tilted (-potential ρ)) := by
      refine (hR.integrable_exp_mul_norm 1).mono' measurable_id.aestronglyMeasurable
        (Filter.Eventually.of_forall fun y => ?_)
      have := Real.add_one_le_exp ‖y‖
      rw [one_mul]
      linarith [norm_nonneg y]
    have hb : ⟪e, ∫ y, y ∂((volume : Measure V).tilted (-potential ρ))⟫ = 0 := by
      rw [← integral_inner hid e, hmean e]
    have hpt : ∀ x, ⟪e, x - ∫ y, y ∂((volume : Measure V).tilted (-potential ρ))⟫ ^ 2 =
        (⟪e, x⟫ - ∫ y, ⟪e, y⟫ ∂((volume : Measure V).tilted (-potential ρ))) ^ 2 := by
      intro x
      rw [inner_sub_right, hb, hmean e]
    simp_rw [hpt]
    have hpo := poincare_temperate_gaussian (V := V) hρ (hlin e)
    simp only [hgrad] at hpo
    rw [integral_const, probReal_univ, one_smul] at hpo
    exact hpo
  have := Analysis.BakryEmery.norm_sq_integral_gradient_le_of_eigen (volume : Measure V)
    hR.temperate hR.integrable_exp_mul_norm (hlin c) (heig c) (hmean c) (inv_pos.mpr hρ).le hcov
  exact this

/-- Lemma 3.4 for the Gaussian law and the pair `g = ⟪c, ·⟫`, `h = 0`. -/
theorem lemma_3_4_trivial_pair {ρ : ℝ} (hρ : 0 < ρ) (c : V) (α : ℝ) :
    ∫ x,
            ‖weightedLaplacianVec (potential ρ)
                  (fun _ : V => (0 : PiLp 2 (fun _ : Fin (Module.finrank ℝ V) => ℝ))) x‖ ^
              2 ∂((volume : Measure V).tilted (-potential ρ)) +
          ∫ x,
            ‖gradCoord (gradCoord fun y : V => ⟪c, y⟫) x -
                  α •
                    gradCoord
                      (fun _ : V => (0 : PiLp 2 (fun _ : Fin (Module.finrank ℝ V) => ℝ))) x‖ ^
              2 ∂((volume : Measure V).tilted (-potential ρ)) +
        ρ *
          ∫ x,
            ‖gradCoord (fun y : V => ⟪c, y⟫) x‖ ^
              2 ∂((volume : Measure V).tilted (-potential ρ)) ≤
      ∫ x,
        ‖weightedLaplacianVec (potential ρ) (fun y : V => ⟪c, y⟫) x‖ ^
          2 ∂((volume : Measure V).tilted (-potential ρ)) := by
  have hP := (regularPotential_gaussian (V := V) hρ).isProbabilityMeasure
  have hd : ∀ x : V, fderiv ℝ (fun y : V => ⟪c, y⟫) x = innerSL ℝ c := fun x =>
    (innerSL ℝ c).fderiv
  have hfun : gradCoord (fun y : V => ⟪c, y⟫) = fun _ => gradCoord (fun y : V => ⟪c, y⟫) 0 := by
    funext x
    simp only [gradCoord, hd]
  refine
    integral_norm_sq_weightedLaplacianVec_ge (volume : Measure V)
      (regularPotential_gaussian hρ).temperate
      (regularPotential_gaussian hρ).integrable_exp_mul_norm
      (regularPotential_gaussian hρ).lower (Function.hasTemperateGrowth_inner_right c)
      (Function.HasTemperateGrowth.const _) (fun x => ?_) ?_
  · rw [hfun]
    simp [weightedLaplacianVec, integral_const]
  · rw [hfun]
    simp only [gradCoord, integral_const, probReal_univ, one_smul, sub_self]
    simp
    rfl

end GaussianExamples

/-- Corollary 3.5 on an explicit real sequence satisfying (45). -/
example :
    Summable (fun i : ℕ => (1 / 2 : ℝ) ^ i) ∧
      Filter.Tendsto (fun i : ℕ => (1 / 2 : ℝ) ^ i) Filter.atTop (nhds 0) := by
  obtain ⟨h1, -, h3⟩ :=
    summable_and_tendsto_zero_of_energy (L := fun i => 2 * (1 / 2 : ℝ) ^ i) (χ := fun _ => 0)
      (v := fun i => (1 / 2 : ℝ) ^ i) (a := 1) one_pos (fun i => by positivity)
      (fun _ => le_rfl) (fun i => by positivity)
      (fun i => by
        simp only [pow_succ]; ring_nf;
        linarith [pow_pos (by norm_num : (0 : ℝ) < 1 / 2) i])
  exact ⟨h1, h3⟩

omit [CompleteSpace V] [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
    [FiniteDimensional ℝ V] in
/--
Corollary 3.5 for an explicit chain of iterates on `ℝ`: `h_k(y) = d_k y` with `d_0 = c`, `d_k = 0`
for `k ≥ 1`, every level `ℝ`, linked by the basis isometry `PiLp 2 (Fin 1 → ℝ) ≃ ℝ`; the relations
(30)
and (33) hold for every scale sequence `α`, and the energies are summable and tend to `0`. -/
theorem chain_client {ρ : ℝ} (hρ : 0 < ρ) (c : ℝ) (α : ℕ → ℝ) :
    Summable
        (fun k =>
          ∫ x,
            ‖gradCoord (fun y : ℝ => (if k = 0 then c else 0) * y) x‖ ^
              2 ∂((volume : Measure ℝ).tilted (-potential ρ))) ∧
      Tendsto
        (fun k =>
          ∫ x,
            ‖gradCoord (fun y : ℝ => (if k = 0 then c else 0) * y) x‖ ^
              2 ∂((volume : Measure ℝ).tilted (-potential ρ)))
        atTop (𝓝 0) := by
  have hP := (regularPotential_gaussian (V := ℝ) hρ).isProbabilityMeasure
  have hfun :
    ∀ d : ℝ, gradCoord (fun y : ℝ => d * y) = fun _ => gradCoord (fun y : ℝ => d * y) 0 := by
    intro d
    funext x
    simp [gradCoord]
  refine
    summable_and_tendsto_zero_of_poisson_chain (volume : Measure ℝ)
      (regularPotential_gaussian hρ).temperate
      (regularPotential_gaussian hρ).integrable_exp_mul_norm hρ
      (regularPotential_gaussian hρ).lower (fun _ => ℝ)
      (fun _ => (stdOrthonormalBasis ℝ ℝ).repr.symm) (fun k y => (if k = 0 then c else 0) * y)
      (fun k => (Function.HasTemperateGrowth.const _).mul Function.HasTemperateGrowth.id') α
      (fun k x => ?_) (fun k => ?_)
  · rw [hfun]
    simp [weightedLaplacianVec, integral_const]
  · rw [hfun (if k = 0 then c else 0)]
    simp only [integral_const, probReal_univ, one_smul, sub_self, norm_zero]
    simp [gradCoord]
    rfl

omit [CompleteSpace V] [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
    [FiniteDimensional ℝ V] in
/-- The (36) form on the explicit chain of `chain_client`: `v_0 = v_N + Σ_{k<N} ‖∫ ∇h_k‖²` (no
identification of `v_0` with `λ₁`). -/
theorem energy_identity_chain {ρ : ℝ} (hρ : 0 < ρ) (c : ℝ) (N : ℕ) :
    ∫ x,
        ‖gradCoord (fun y : ℝ => (if (0 : ℕ) = 0 then c else 0) * y) x‖ ^
          2 ∂((volume : Measure ℝ).tilted (-potential ρ)) =
      ∫ x,
          ‖gradCoord (fun y : ℝ => (if N = 0 then c else 0) * y) x‖ ^
            2 ∂((volume : Measure ℝ).tilted (-potential ρ)) +
        ∑ k ∈ Finset.range N,
          ‖∫ x,
                gradCoord (fun y : ℝ => (if k = 0 then c else 0) * y)
                  x ∂((volume : Measure ℝ).tilted (-potential ρ))‖ ^
            2 := by
  have hP := (regularPotential_gaussian (V := ℝ) hρ).isProbabilityMeasure
  have hfun :
    ∀ d : ℝ, gradCoord (fun y : ℝ => d * y) = fun _ => gradCoord (fun y : ℝ => d * y) 0 := by
    intro d
    funext x
    simp [gradCoord]
  refine
    integral_norm_sq_gradCoord_eq_add_sum (volume : Measure ℝ)
      (regularPotential_gaussian hρ).integrable_exp_mul_norm (fun _ => ℝ)
      (fun k y => (if k = 0 then c else 0) * y)
      (fun k => (Function.HasTemperateGrowth.const _).mul Function.HasTemperateGrowth.id')
      (fun k => ?_) N
  rw [hfun (if k = 0 then c else 0)]
  simp only [integral_const, probReal_univ, one_smul, sub_self, norm_zero]
  simp [gradCoord]
  rfl

omit [CompleteSpace V] [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
    [FiniteDimensional ℝ V] in
/--
The generalized Lemma 3.2 on the Gaussian law of `ℝ` for the pair `g = c·`, `h = 0`, `α = 1`,
`λ = 1` (`λ` is not identified with the spectral gap). -/
theorem lemma_3_2_trivial_pair {ρ : ℝ} (hρ : 0 < ρ) (c : ℝ) :
    ∃ T :
      ℝ →
        PiLp 2
          (fun _ : Fin (Module.finrank ℝ ℝ) => PiLp 2 (fun _ : Fin (Module.finrank ℝ ℝ) => ℝ)),
      (∀ x i j, T x i j = T x j i) ∧
        Integrable
            (fun x =>
              ‖(gradCoord (fun _ : ℝ => (0 : PiLp 2 (fun _ : Fin (Module.finrank ℝ ℝ) => ℝ)))
                        x -
                      ∫ y,
                        gradCoord
                          (fun _ : ℝ => (0 : PiLp 2 (fun _ : Fin (Module.finrank ℝ ℝ) => ℝ)))
                          y ∂((volume : Measure ℝ).tilted (-potential ρ))) -
                    T x‖ ^
                2)
            ((volume : Measure ℝ).tilted (-potential ρ)) ∧
          ∫ x,
              ‖(gradCoord (fun _ : ℝ => (0 : PiLp 2 (fun _ : Fin (Module.finrank ℝ ℝ) => ℝ)))
                        x -
                      ∫ y,
                        gradCoord
                          (fun _ : ℝ => (0 : PiLp 2 (fun _ : Fin (Module.finrank ℝ ℝ) => ℝ)))
                          y ∂((volume : Measure ℝ).tilted (-potential ρ))) -
                    T x‖ ^
                2 ∂((volume : Measure ℝ).tilted (-potential ρ)) ≤
            (∫ x,
                ‖gradCoord (gradCoord fun y : ℝ => c * y) x -
                      (1 : ℝ) •
                        gradCoord
                          (fun _ : ℝ => (0 : PiLp 2 (fun _ : Fin (Module.finrank ℝ ℝ) => ℝ)))
                          x‖ ^
                  2 ∂((volume : Measure ℝ).tilted (-potential ρ))) /
              1 := by
  have hP := (regularPotential_gaussian (V := ℝ) hρ).isProbabilityMeasure
  have hfun : gradCoord (fun y : ℝ => c * y) = fun _ => gradCoord (fun y : ℝ => c * y) 0 := by
    funext x
    simp [gradCoord]
  refine
    exists_symm_integral_norm_sq_sub_le (g := fun y : ℝ => c * y) (volume : Measure ℝ)
      (regularPotential_gaussian hρ).temperate
      (regularPotential_gaussian hρ).integrable_exp_mul_norm
      ((Function.HasTemperateGrowth.const c).mul Function.HasTemperateGrowth.id')
      (Function.HasTemperateGrowth.const _) (fun x => ?_) one_pos (fun _ => by norm_num)
  rw [hfun]
  simp [weightedLaplacianVec, integral_const]

omit [CompleteSpace V] [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
    [FiniteDimensional ℝ V] in
/--
`S₂` on a tensor that is not symmetric in its first two indices: `A` is no farther from `S₂ A`
than from the symmetric tensor `0`. -/
theorem symmetrizeFirstTwo_nonvacuous :
    ‖(WithLp.toLp 2 fun i : Fin 2 =>
            WithLp.toLp 2 fun j : Fin 2 => if i = 0 ∧ j = 1 then (1 : ℝ) else 0) -
          symmetrizeFirstTwo
            (WithLp.toLp 2 fun i : Fin 2 =>
              WithLp.toLp 2 fun j : Fin 2 => if i = 0 ∧ j = 1 then (1 : ℝ) else 0)‖ ≤
      ‖(WithLp.toLp 2 fun i : Fin 2 =>
            WithLp.toLp 2 fun j : Fin 2 => if i = 0 ∧ j = 1 then (1 : ℝ) else 0) -
          0‖ :=
  norm_sub_symmetrizeFirstTwo_le _ _ (fun _ _ => rfl)

omit [CompleteSpace V] [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
    [FiniteDimensional ℝ V] in
/--
Lemma 3.3 for `q = 2` (generalized form) on the Gaussian law of `ℝ` for the pair `g = c·`, `h = 0`,
`α = 1`, `λ = 1`. -/
theorem lemma_3_3_q2_trivial_pair {ρ : ℝ} (hρ : 0 < ρ) (c : ℝ) :
    ∫ x,
        ‖(gradCoord (fun _ : ℝ => (0 : PiLp 2 (fun _ : Fin (Module.finrank ℝ ℝ) => ℝ))) x -
                ∫ y,
                  gradCoord (fun _ : ℝ => (0 : PiLp 2 (fun _ : Fin (Module.finrank ℝ ℝ) => ℝ)))
                    y ∂((volume : Measure ℝ).tilted (-potential ρ))) -
              symmetrizeFirstTwo
                (gradCoord (fun _ : ℝ => (0 : PiLp 2 (fun _ : Fin (Module.finrank ℝ ℝ) => ℝ)))
                    x -
                  ∫ y,
                    gradCoord
                      (fun _ : ℝ => (0 : PiLp 2 (fun _ : Fin (Module.finrank ℝ ℝ) => ℝ)))
                      y ∂((volume : Measure ℝ).tilted (-potential ρ)))‖ ^
          2 ∂((volume : Measure ℝ).tilted (-potential ρ)) ≤
      (∫ x,
          ‖gradCoord (gradCoord fun y : ℝ => c * y) x -
                (1 : ℝ) •
                  gradCoord (fun _ : ℝ => (0 : PiLp 2 (fun _ : Fin (Module.finrank ℝ ℝ) => ℝ)))
                    x‖ ^
            2 ∂((volume : Measure ℝ).tilted (-potential ρ))) /
        1 := by
  have hP := (regularPotential_gaussian (V := ℝ) hρ).isProbabilityMeasure
  have hfun : gradCoord (fun y : ℝ => c * y) = fun _ => gradCoord (fun y : ℝ => c * y) 0 := by
    funext x
    simp [gradCoord]
  refine
    integral_norm_sq_sub_symmetrizeFirstTwo_le (g := fun y : ℝ => c * y) (volume : Measure ℝ)
      (regularPotential_gaussian hρ).temperate
      (regularPotential_gaussian hρ).integrable_exp_mul_norm
      ((Function.HasTemperateGrowth.const c).mul Function.HasTemperateGrowth.id')
      (Function.HasTemperateGrowth.const _) (fun x => ?_) one_pos (fun _ => by norm_num)
  rw [hfun]
  simp [weightedLaplacianVec, integral_const]

end BKLRegularLawAudit

#print axioms BKLRegularLawAudit.regularPotential_gaussian
#print axioms BKLRegularLawAudit.lemma_3_4_trivial_pair
#print axioms BKLRegularLawAudit.chain_client
#print axioms BKLRegularLawAudit.tensor_lift_gaussian
#print axioms BKLRegularLawAudit.energy_identity_chain
#print axioms BKLRegularLawAudit.lemma_3_2_trivial_pair
#print axioms BKLRegularLawAudit.generator_linear_gaussian
#print axioms BKLRegularLawAudit.poincare_temperate_gaussian
#print axioms
  FunctionalInequalities.Analysis.BakryEmery.integral_fderiv_apply_eq_smul_taylorTensor_one
#print axioms FunctionalInequalities.Analysis.BakryEmery.norm_sq_integral_gradCoord_eq
#print axioms FunctionalInequalities.Analysis.BakryEmery.norm_sq_integral_gradient_le_of_eigen
#print axioms BKLRegularLawAudit.eigen_linear_gaussian
#print axioms BKLRegularLawAudit.symmetrizeFirstTwo_nonvacuous
#print axioms BKLRegularLawAudit.lemma_3_3_q2_trivial_pair
#print axioms FunctionalInequalities.Analysis.BakryEmery.integral_norm_sq_sub_symmetrizeFirstTwo_le
#print axioms FunctionalInequalities.KLS.LogConcave.integral_norm_sq_sub_symmetrizeFirstTwo_le_mul
#print axioms
  FunctionalInequalities.KLS.LogConcave.integral_norm_sq_sub_integral_le_of_hasTemperateGrowth
#print axioms
  FunctionalInequalities.KLS.LogConcave.integral_norm_sq_gradCoord_le_of_hasTemperateGrowth
#print axioms FunctionalInequalities.KLS.LogConcave.one_le_mul_sq_of_poisson
#print axioms FunctionalInequalities.KLS.LogConcave.exists_symm_integral_norm_sq_sub_le_mul
#print axioms
  FunctionalInequalities.KLS.LogConcave.exists_toLp_mem_closedWeightedOperator_domain_of_hasTemperateGrowth
#print axioms
  FunctionalInequalities.KLS.LogConcave.exists_toLp_mem_adjointComp_domain_of_hasTemperateGrowth
#print axioms FunctionalInequalities.KLS.LogConcave.centered_inverse_eq_toLp_of_hasTemperateGrowth
#print axioms FunctionalInequalities.Analysis.BakryEmery.exists_symm_integral_norm_sq_sub_le
#print axioms
  FunctionalInequalities.Analysis.BakryEmery.integral_norm_sq_gradCoord_sub_eq_of_normalized
#print axioms FunctionalInequalities.Analysis.BakryEmery.integral_norm_sq_gradCoord_eq_add_sum
#print axioms FunctionalInequalities.Analysis.BakryEmery.gradCoord_gradCoord_symm
#print axioms FunctionalInequalities.KLS.LogConcave.existsUnique_centered_adjointComp_eq_components
#print axioms
  FunctionalInequalities.KLS.RegularPotential.existsUnique_centered_adjointComp_eq_components
#print axioms FunctionalInequalities.L2.sum_norm_sq_compLp_innerSL
#print axioms FunctionalInequalities.L2.mean_compLp_innerSL
#print axioms FunctionalInequalities.KLS.RegularPotential.integrable_exp_mul_norm
#print axioms FunctionalInequalities.KLS.RegularPotential.isProbabilityMeasure
#print axioms FunctionalInequalities.KLS.RegularPotential.taylorTensor_neg_weightedLaplacianVec
#print axioms FunctionalInequalities.KLS.RegularPotential.integral_inner_weightedLaplacianVec_eq_neg
#print axioms
  FunctionalInequalities.KLS.RegularPotential.integral_hessian_add_le_norm_sq_weightedLaplacianVec
#print axioms FunctionalInequalities.KLS.RegularPotential.existsUnique_centered_adjointComp_eq
#print axioms FunctionalInequalities.Analysis.BakryEmery.integral_norm_sq_weightedLaplacianVec_ge
#print axioms FunctionalInequalities.Analysis.BakryEmery.integral_norm_sq_gradCoord_gradCoord_eq
#print axioms FunctionalInequalities.Analysis.BakryEmery.summable_and_tendsto_zero_of_energy
#print axioms FunctionalInequalities.Analysis.BakryEmery.integral_norm_sq_gradCoord_gradCoord_eq_add
#print axioms FunctionalInequalities.Analysis.BakryEmery.weightedLaplacianVec_linearIsometryEquiv
#print axioms FunctionalInequalities.Analysis.BakryEmery.norm_gradCoord_linearIsometryEquiv
#print axioms FunctionalInequalities.Analysis.BakryEmery.summable_and_tendsto_zero_of_poisson_chain
#print axioms FunctionalInequalities.KLS.RegularPotential.logConcave_law
#print axioms FunctionalInequalities.KLS.RegularPotential.exists_norm_gradient_le
