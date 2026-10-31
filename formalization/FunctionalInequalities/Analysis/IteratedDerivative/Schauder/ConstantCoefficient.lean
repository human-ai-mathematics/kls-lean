module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import FunctionalInequalities.Analysis.Newtonian.Schauder.Interior
public import FunctionalInequalities.Analysis.IteratedDerivative.LinearPullback

/-!
# Interior Schauder estimate for constant-coefficient elliptic operators (GT Lemma 6.1)

Lemma 6.1 of Gilbarg–Trudinger, *Elliptic Partial Differential Equations of Second Order*, Classics
2001 (ISBN 3-540-41160-7), p. 88, in its interior form on balls and with the Hessian taken as the
nested Fréchet derivative `fderiv ℝ (fderiv ℝ ·)`. For `n ≥ 2`, `0 < α < 1` and ellipticity
constants `0 < λ ≤ Λ`, `constant_coefficient_interior_hessian_holder` gives one constant
`C(n, α, λ, Λ) > 0`, chosen before the coefficient matrix `A`, the centre `c`, the radius `R` and
the data, such that for every symmetric `A` with `λ‖ξ‖² ≤ Σ_{ij} A_{ij} ξ_i ξ_j ≤ Λ‖ξ‖²` and every
`u ∈ C²(B_{2R}(c))` with `Σ_{ij} A_{ij} D_{ij} u = f` on `B_{2R}(c)`, `|u| ≤ U`, `|f| ≤ M` and
`[f]_{α; B_{2R}(c)} ≤ H`, one has on `B_R(c)`
`‖D²u‖ ≤ C (U R⁻² + M + R^α H)` and `‖D²u(x) - D²u(y)‖ ≤ C (U R^(-2-α) + M R^(-α) + H) ‖x - y‖^α`.

The proof is GT's change of variables on p. 88 reduced to Theorem 4.6
(`poisson_interior_hessian_holder`). With `S = A^{1/2}` the positive square root of `A`
(`CFC.sqrt`, through `Matrix.toEuclideanCLM`), the linear equivalence `T = S` of `ℝⁿ` satisfies
`‖T ξ‖² = ξᵀAξ`, hence `‖T‖ ≤ √Λ` and `‖T⁻¹‖ ≤ 1/√λ`, and
`Σ_i B(T e_i, T e_i) = Σ_{ij} A_{ij} B(e_i, e_j)` for every bilinear `B` (`exists_sqrt_equiv`).
The pullback `v = u ∘ T` therefore solves `Δv = f ∘ T` (`hessian_comp_equiv_of_contDiffAt` with the
orthonormal-basis formula for the Laplacian). For `x₀ ∈ B_R(c)`, `T` maps `B_{2ρ}(T⁻¹x₀)` with
`ρ = R / (2√Λ)` into `B_R(x₀) ⊆ B_{2R}(c)`; Theorem 4.6 on that ball, pulled back through `T⁻¹`
(`norm_bilinearComp_self_le`), gives the pointwise bound and the Hölder bound for `‖x - y‖ < ρ√λ`;
for farther points the Hölder bound follows from the two pointwise bounds. The constant is
`C = C₁ + C₂ + C₃` with `C₁ = C₀ λ⁻¹ (4Λ + 1)`,
`C₂ = C₀ λ^{-1-α/2} ((2√Λ)^{2+α} + (2√Λ)^α + Λ^{α/2})` and `C₃ = 2 C₁ (2√(Λ/λ))^α`, where
`C₀ = C(n, α)` is the constant of `poisson_interior_hessian_holder`.

Scope: the coefficient hypothesis is the quadratic form of `A` on the standard basis and the
equation `Σ_{ij} A_{ij} D_{ij} u = f` is pointwise on the open ball; the estimate is stated on the
open ball `B_R(c)` with the operator norm of the Hessian. The case `α = 1`, the global `C^{2,α}`
norms of GT (6.1)–(6.3), lower-order terms and boundary estimates are not claimed. The constant is
coarse.
-/

@[expose] public section

noncomputable section

open Set Metric Matrix Filter
open scoped Topology ContDiff NNReal MatrixOrder RealInnerProductSpace

namespace FunctionalInequalities.Analysis

/-- Expansion of a continuous bilinear form on `ℝⁿ` in the standard basis. -/
private theorem bilinear_eq_sum_basisFun {n : ℕ}
    (B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (v w : EuclideanSpace ℝ (Fin n)) :
    B v w = ∑ j, ∑ k, v j * w k *
      B (EuclideanSpace.basisFun (Fin n) ℝ j) (EuclideanSpace.basisFun (Fin n) ℝ k) := by
  nth_rewrite 1 [← (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr v]
  nth_rewrite 1 [← (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr w]
  simp only [map_sum, map_smul, _root_.sum_apply, _root_.smul_apply, smul_eq_mul,
    EuclideanSpace.basisFun_repr, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring

/-- The symmetric square root of a symmetric matrix with quadratic form bounds, as a continuous
linear equivalence `T` of `ℝⁿ` with `‖T ξ‖² = ξᵀ A ξ` and `Σ_i B(T e_i, T e_i) = Σ_{ij} A_{ij}
B(e_i, e_j)`
for every continuous bilinear `B`. -/
private theorem exists_sqrt_equiv {n : ℕ} {lam Lam : ℝ} (hlam : 0 < lam)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm)
    (hq :
      ∀ ξ : EuclideanSpace ℝ (Fin n),
        lam * ‖ξ‖ ^ 2 ≤ ∑ i, ∑ j, A i j * ξ i * ξ j ∧
          ∑ i, ∑ j, A i j * ξ i * ξ j ≤ Lam * ‖ξ‖ ^ 2) :
    ∃ T : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n),
      (∀ ξ, ‖T ξ‖ ^ 2 = ∑ i, ∑ j, A i j * ξ i * ξ j) ∧
        ∀ B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ,
          ∑ i,
              B (T (EuclideanSpace.basisFun (Fin n) ℝ i))
                (T (EuclideanSpace.basisFun (Fin n) ℝ i)) =
            ∑ i,
              ∑ j,
                A i j *
                  B (EuclideanSpace.basisFun (Fin n) ℝ i)
                    (EuclideanSpace.basisFun (Fin n) ℝ j) := by
  classical
  have hquad :
    ∀ ξ : EuclideanSpace ℝ (Fin n),
      ⟪ξ, toEuclideanCLM (𝕜 := ℝ) A ξ⟫ = ∑ i, ∑ j, A i j * ξ i * ξ j := by
    intro ξ
    rw [inner_toEuclideanCLM]
    simp only [dotProduct, mulVec, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hAher : A.IsHermitian := isHermitian_iff_isSymm.mpr hA
  have hApos : A.PosDef := by
    rw [posDef_iff_dotProduct_mulVec]
    refine ⟨hAher, fun x hx => ?_⟩
    have h1 := (hq (WithLp.toLp 2 x)).1
    rw [← hquad, inner_toEuclideanCLM] at h1
    have hx' : (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n)) ≠ 0 := by
      intro h
      apply hx
      simpa using congrArg WithLp.ofLp h
    have hpos : 0 < ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))‖ := norm_pos_iff.mpr hx'
    have : 0 < lam * ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))‖ ^ 2 := by positivity
    simpa using lt_of_lt_of_le this h1
  have hA0 : 0 ≤ A := hApos.posSemidef.nonneg
  set S := CFC.sqrt A with hS
  have hSS : S * S = A := CFC.sqrt_mul_sqrt_self A hA0
  have hSher : S.IsHermitian := (CFC.sqrt_nonneg A).posSemidef.1
  have hSsymm : ∀ i j, S i j = S j i := fun i j => by
    have h := congrFun (congrFun (isHermitian_iff_isSymm.mp hSher).eq i) j
    simpa [transpose_apply] using h.symm
  set Sop := toEuclideanCLM (𝕜 := ℝ) S with hSop
  have hSop_sa : IsSelfAdjoint Sop := (CFC.sqrt_nonneg A).isSelfAdjoint.map _
  have hnorm : ∀ ξ, ‖Sop ξ‖ ^ 2 = ∑ i, ∑ j, A i j * ξ i * ξ j := by
    intro ξ
    rw [← real_inner_self_eq_norm_sq, ← ContinuousLinearMap.adjoint_inner_right,
      hSop_sa.adjoint_eq, show Sop (Sop ξ) = (Sop * Sop) ξ from rfl, hSop, ← map_mul, hSS,
      hquad]
  have hinj : Function.Injective Sop := by
    intro a b hab
    by_contra hne
    have hne' : a - b ≠ 0 := sub_ne_zero.mpr hne
    have h0 : Sop (a - b) = 0 := by rw [map_sub, hab, sub_self]
    have h1 := (hq (a - b)).1
    rw [← hnorm, h0, norm_zero] at h1
    have : 0 < ‖a - b‖ ^ 2 := by positivity
    nlinarith
  let T : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
    (LinearEquiv.ofInjectiveEndo Sop.toLinearMap hinj).toContinuousLinearEquiv
  have hT : ∀ ξ, T ξ = Sop ξ := fun ξ => rfl
  refine ⟨T, fun ξ => by rw [hT]; exact hnorm ξ, fun B => ?_⟩
  have hTe : ∀ i j, (T (EuclideanSpace.basisFun (Fin n) ℝ i)) j = S j i := by
    intro i j
    rw [hT, hSop]
    simp [EuclideanSpace.basisFun_apply]
  calc
    ∑ i, B (T (EuclideanSpace.basisFun (Fin n) ℝ i)) (T (EuclideanSpace.basisFun (Fin n) ℝ i)) =
        ∑ i,
          ∑ j,
            ∑ k,
              S j i * S k i *
                B (EuclideanSpace.basisFun (Fin n) ℝ j) (EuclideanSpace.basisFun (Fin n) ℝ k) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [bilinear_eq_sum_basisFun]
      simp only [hTe]
    _ =
        ∑ j,
          ∑ k,
            (∑ i, S j i * S k i) *
              B (EuclideanSpace.basisFun (Fin n) ℝ j) (EuclideanSpace.basisFun (Fin n) ℝ k) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.sum_mul]
    _ =
        ∑ i,
          ∑ j,
            A i j *
              B (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j) := by
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
      congr 1
      rw [← hSS, mul_apply]
      exact Finset.sum_congr rfl fun i _ => by rw [hSsymm i k]

/-- Local form of `hessian_comp_equiv`: `C²` of `f` at `T x` suffices. -/
private theorem hessian_comp_equiv_of_contDiffAt {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : E ≃L[ℝ] F) (f : F → ℝ) {x : E} (hf : ContDiffAt ℝ 2 f (T x)) :
    fderiv ℝ (fderiv ℝ (fun z : E => f (T z))) x =
      (fderiv ℝ (fderiv ℝ f) (T x)).bilinearComp
        T.toContinuousLinearMap T.toContinuousLinearMap := by
  have hev : ∀ᶠ z in 𝓝 x, ContDiffAt ℝ 2 f (T z) :=
    T.continuous.continuousAt.eventually (hf.eventually (by simp))
  have hfirst : fderiv ℝ (fun z : E => f (T z)) =ᶠ[𝓝 x]
      fun z => (fderiv ℝ f (T z)).comp T.toContinuousLinearMap := by
    filter_upwards [hev] with z hz
    exact ((hz.differentiableAt (by norm_num)).hasFDerivAt.comp z
      T.toContinuousLinearMap.hasFDerivAt).fderiv
  let C : (F →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) :=
    (ContinuousLinearMap.compL ℝ E F ℝ).flip T.toContinuousLinearMap
  have hsecond :=
    C.hasFDerivAt.comp x
      (((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt.comp x
        T.toContinuousLinearMap.hasFDerivAt)
  rw [hfirst.fderiv_eq]
  exact hsecond.fderiv.trans (by
    ext v w
    rfl)

/-- A bilinear form composed with `T` in both slots is recovered by composing with `T⁻¹`. -/
private theorem eq_bilinearComp_symm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : E ≃L[ℝ] E) {B D : E →L[ℝ] E →L[ℝ] ℝ}
    (h : D = B.bilinearComp T.toContinuousLinearMap T.toContinuousLinearMap) :
    B = D.bilinearComp T.symm.toContinuousLinearMap T.symm.toContinuousLinearMap := by
  ext a b
  rw [h]
  simp [ContinuousLinearMap.bilinearComp_apply]

set_option maxHeartbeats 800000 in
/-- **GT 2001 Lemma 6.1 (p. 88), interior form.** Interior Hessian and Hessian-Hölder estimates on
`B_R(c)` for `C²` solutions of the constant-coefficient equation `Σ_{ij} A_{ij} D_{ij} u = f` on
`B_{2R}(c)`, with one constant `C(n, α, λ, Λ)` for `n ≥ 2`, `0 < α < 1` and symmetric `A` with
`λ|ξ|² ≤ ξᵀAξ ≤ Λ|ξ|²`. The constant is chosen before `A`, `c`, `R` and the data. -/
theorem constant_coefficient_interior_hessian_holder {n : ℕ} (hn : 2 ≤ n) {α : ℝ≥0} (hα0 : 0 < α)
    (hα1 : α < 1) {lam Lam : ℝ} (hlam : 0 < lam) (hLam : lam ≤ Lam) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : Matrix (Fin n) (Fin n) ℝ), A.IsSymm →
      (∀ ξ : EuclideanSpace ℝ (Fin n), lam * ‖ξ‖ ^ 2 ≤ ∑ i, ∑ j, A i j * ξ i * ξ j ∧
        ∑ i, ∑ j, A i j * ξ i * ξ j ≤ Lam * ‖ξ‖ ^ 2) →
      ∀ (c : EuclideanSpace ℝ (Fin n)) (R : ℝ), 0 < R →
      ∀ (u f : EuclideanSpace ℝ (Fin n) → ℝ) (U M : ℝ) (H : ℝ≥0),
      ContDiffOn ℝ 2 u (ball c (2 * R)) →
      (∀ x ∈ ball c (2 * R), ∑ i, ∑ j, A i j * fderiv ℝ (fderiv ℝ u) x
          (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j) = f x) →
      (∀ x ∈ ball c (2 * R), |u x| ≤ U) → (∀ y ∈ ball c (2 * R), |f y| ≤ M) →
      HolderOnWith H α f (ball c (2 * R)) →
      (∀ x ∈ ball c R, ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ C * (U * R ^ (-(2:ℝ)) + M + R ^ (α:ℝ) * H)) ∧
      ∀ x ∈ ball c R, ∀ y ∈ ball c R,
        ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖ ≤
          C * (U * R ^ (-(2:ℝ) - α) + M * R ^ (-(α:ℝ)) + H) * ‖x - y‖ ^ (α:ℝ) := by
  -- Choose the Poisson estimate and the linear normalization constants.
  obtain ⟨C₀, hC₀, hP⟩ := poisson_interior_hessian_holder hn hα0 hα1
  have hLam0 : 0 < Lam := hlam.trans_le hLam
  -- `σ = √Λ` bounds `T`, `τ = 1/√λ` bounds `T⁻¹`.
  obtain ⟨σ, hσ, hσ2⟩ : ∃ σ : ℝ, 0 < σ ∧ σ ^ 2 = Lam :=
    ⟨Real.sqrt Lam, Real.sqrt_pos.mpr hLam0, Real.sq_sqrt hLam0.le⟩
  obtain ⟨τ, hτ, hτ2⟩ : ∃ τ : ℝ, 0 < τ ∧ lam * τ ^ 2 = 1 :=
    ⟨(Real.sqrt lam)⁻¹, by positivity, by
      rw [inv_pow, Real.sq_sqrt hlam.le]; field_simp⟩
  have hαr0 : (0:ℝ) < α := hα0
  have hαr : (0:ℝ) ≤ α := hαr0.le
  -- The three pieces of the constant: pointwise bound, near-point Hölder bound, far-point bound.
  obtain ⟨C₁, hC₁, hC₁def⟩ : ∃ C₁ : ℝ, 0 < C₁ ∧ C₁ = C₀ * τ ^ 2 * (4 * Lam + 1) :=
    ⟨_, by positivity, rfl⟩
  obtain ⟨C₂, hC₂, hC₂def⟩ : ∃ C₂ : ℝ, 0 < C₂ ∧ C₂ = C₀ * τ ^ 2 * τ ^ (α:ℝ) *
      ((2 * σ) ^ ((2:ℝ) + α) + (2 * σ) ^ (α:ℝ) + σ ^ (α:ℝ)) := ⟨_, by positivity, rfl⟩
  obtain ⟨C₃, hC₃, hC₃def⟩ : ∃ C₃ : ℝ, 0 < C₃ ∧ C₃ = 2 * C₁ * (2 * σ * τ) ^ (α:ℝ) :=
    ⟨_, by positivity, rfl⟩
  refine ⟨C₁ + C₂ + C₃, by positivity, ?_⟩
  intro A hA hq c R hR u f U M H hu hAu hU hM hH
  obtain ⟨T, hTn, hTsum⟩ := exists_sqrt_equiv hlam A hA hq
  -- Step 1: operator bounds `‖T ξ‖ ≤ σ ‖ξ‖` and `‖T⁻¹ η‖ ≤ τ ‖η‖`.
  have hTle : ∀ ξ, ‖T ξ‖ ≤ σ * ‖ξ‖ := by
    intro ξ
    have h : ‖T ξ‖ ^ 2 ≤ (σ * ‖ξ‖) ^ 2 := by
      rw [hTn, mul_pow, hσ2]; exact (hq ξ).2
    have := abs_le_of_sq_le_sq h (by positivity)
    rwa [abs_of_nonneg (norm_nonneg _)] at this
  have hTinv : ∀ η, ‖T.symm η‖ ≤ τ * ‖η‖ := by
    intro η
    have h1 : lam * ‖T.symm η‖ ^ 2 ≤ ‖η‖ ^ 2 := by
      have := (hq (T.symm η)).1
      rwa [← hTn, T.apply_symm_apply] at this
    have h : ‖T.symm η‖ ^ 2 ≤ (τ * ‖η‖) ^ 2 := by
      calc ‖T.symm η‖ ^ 2 = τ ^ 2 * (lam * ‖T.symm η‖ ^ 2) := by
            rw [← mul_assoc, mul_comm (τ ^ 2), hτ2, one_mul]
        _ ≤ τ ^ 2 * ‖η‖ ^ 2 := mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = (τ * ‖η‖) ^ 2 := by ring
    have := abs_le_of_sq_le_sq h (by positivity)
    rwa [abs_of_nonneg (norm_nonneg _)] at this
  have hTsymm_norm : ‖T.symm.toContinuousLinearMap‖ ≤ τ :=
    ContinuousLinearMap.opNorm_le_bound _ hτ.le hTinv
  have hTsymm_sq : ‖T.symm.toContinuousLinearMap‖ ^ 2 ≤ τ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hTsymm_norm 2
  obtain ⟨K, hK⟩ : ∃ K : ℝ≥0, (K : ℝ) = σ := ⟨⟨σ, hσ.le⟩, rfl⟩
  have hTlip : LipschitzWith K T := LipschitzWith.of_dist_le_mul fun a b => by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub, hK]; exact hTle (a - b)
  -- Step 2: the transported data `v = u ∘ T`, `g = f ∘ T` and the identity `Δv = g`.
  set v : EuclideanSpace ℝ (Fin n) → ℝ := fun z => u (T z) with hv
  set g : EuclideanSpace ℝ (Fin n) → ℝ := fun z => f (T z) with hg
  have hB : IsOpen (ball c (2 * R)) := isOpen_ball

  -- Transport the equation and the interior balls through the linear map.
  have hu_at : ∀ x ∈ ball c (2 * R), ContDiffAt ℝ 2 u x := fun x hx =>
    hu.contDiffAt (hB.mem_nhds hx)
  have hvH : ∀ z, T z ∈ ball c (2 * R) → fderiv ℝ (fderiv ℝ v) z =
      (fderiv ℝ (fderiv ℝ u) (T z)).bilinearComp T.toContinuousLinearMap T.toContinuousLinearMap :=
    fun z hz => hessian_comp_equiv_of_contDiffAt T u (hu_at _ hz)
  have huH : ∀ x ∈ ball c (2 * R), fderiv ℝ (fderiv ℝ u) x =
      (fderiv ℝ (fderiv ℝ v) (T.symm x)).bilinearComp T.symm.toContinuousLinearMap
        T.symm.toContinuousLinearMap := by
    intro x hx
    have h := hvH (T.symm x) (by rwa [T.apply_symm_apply])
    rw [T.apply_symm_apply] at h
    exact eq_bilinearComp_symm T h
  have hvLap : ∀ z, T z ∈ ball c (2 * R) → Laplacian.laplacian v z = g z := by
    intro z hz
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis v
      (EuclideanSpace.basisFun (Fin n) ℝ)]
    simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [hvH z hz]
    simp only [ContinuousLinearMap.bilinearComp_apply, ContinuousLinearEquiv.coe_coe]
    rw [hTsum]
    exact hAu (T z) hz
  -- Step 3: geometry. `T` maps `B_{2ρ}(T⁻¹ x₀)` into `B_R(x₀) ⊆ B_{2R}(c)` for `ρ = R / (2σ)`.
  have hρ_pos : 0 < R / (2 * σ) := by positivity
  set ρ := R / (2 * σ) with hρ
  have hρσ : σ * (2 * ρ) = R := by rw [hρ]; field_simp
  have hmaps : ∀ x₀ ∈ ball c R, ∀ z ∈ ball (T.symm x₀) (2 * ρ), T z ∈ ball c (2 * R) := by
    intro x₀ hx₀ z hz
    rw [mem_ball, dist_eq_norm] at hz hx₀ ⊢
    have h1 : ‖T z - x₀‖ < R := by
      have : T z - x₀ = T (z - T.symm x₀) := by rw [map_sub, T.apply_symm_apply]
      rw [this]
      calc ‖T (z - T.symm x₀)‖ ≤ σ * ‖z - T.symm x₀‖ := hTle _
        _ < σ * (2 * ρ) := mul_lt_mul_of_pos_left hz hσ
        _ = R := hρσ
    calc ‖T z - c‖ = ‖(T z - x₀) + (x₀ - c)‖ := by congr 1; abel
      _ ≤ ‖T z - x₀‖ + ‖x₀ - c‖ := norm_add_le _ _
      _ < R + R := add_lt_add h1 hx₀
      _ = 2 * R := by ring
  -- Step 4: the Hölder cap of `g = f ∘ T` is `H σ^α`.
  obtain ⟨H', hH'coe⟩ : ∃ H' : ℝ≥0, (H' : ℝ) = H * σ ^ (α:ℝ) :=
    ⟨⟨H * σ ^ (α:ℝ), by positivity⟩, rfl⟩
  have hH'eq : H * K ^ (α:ℝ) = H' := by
    apply NNReal.coe_injective
    rw [hH'coe, NNReal.coe_mul, NNReal.coe_rpow, hK]
  -- Step 5: GT Theorem 4.6 for `v` on `B_{2ρ}(T⁻¹ x₀)`.
  have hlocal : ∀ x₀ ∈ ball c R,
      (∀ z ∈ ball (T.symm x₀) ρ, ‖fderiv ℝ (fderiv ℝ v) z‖ ≤
        C₀ * (U * ρ ^ (-(2:ℝ)) + M + ρ ^ (α:ℝ) * H')) ∧
      ∀ z ∈ ball (T.symm x₀) ρ, ∀ z' ∈ ball (T.symm x₀) ρ,
        ‖fderiv ℝ (fderiv ℝ v) z - fderiv ℝ (fderiv ℝ v) z'‖ ≤
          C₀ * (U * ρ ^ (-(2:ℝ) - α) + M * ρ ^ (-(α:ℝ)) + H') * ‖z - z'‖ ^ (α:ℝ) := by
    intro x₀ hx₀
    have hm := hmaps x₀ hx₀
    refine hP (T.symm x₀) ρ hρ_pos v g U M H' ?_ ?_ ?_ ?_ ?_
    · exact hu.comp T.contDiff.contDiffOn hm
    · exact fun z hz => hvLap z (hm z hz)
    · exact fun z hz => hU _ (hm z hz)
    · exact fun z hz => hM _ (hm z hz)
    · have h := hH.comp ((holderWith_one.mpr hTlip).holderOnWith (ball (T.symm x₀) (2 * ρ))) hm
      rw [mul_one, hH'eq] at h
      exact h
  -- Step 6: rpow bookkeeping for `ρ = R / (2σ)`.
  have hρ2 : ρ ^ (-(2:ℝ)) = 4 * Lam * R ^ (-(2:ℝ)) := by
    rw [Real.rpow_neg hρ_pos.le, Real.rpow_neg hR.le, Real.rpow_two, Real.rpow_two, hρ, div_pow,
      ← hσ2]
    field_simp
    ring
  have hρα : ρ ^ (α:ℝ) * σ ^ (α:ℝ) ≤ R ^ (α:ℝ) := by
    rw [← Real.mul_rpow hρ_pos.le hσ.le]
    refine Real.rpow_le_rpow (by positivity) ?_ hαr
    rw [hρ, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [mul_pos hR hσ]
  have hρ2α : ρ ^ (-(2:ℝ) - α) = R ^ (-(2:ℝ) - α) * (2 * σ) ^ ((2:ℝ) + α) := by
    rw [hρ, Real.div_rpow hR.le (by positivity), show -(2:ℝ) - α = -((2:ℝ) + α) by ring,
      Real.rpow_neg (by positivity : (0:ℝ) ≤ 2 * σ), div_inv_eq_mul]
  have hρα' : ρ ^ (-(α:ℝ)) = R ^ (-(α:ℝ)) * (2 * σ) ^ (α:ℝ) := by
    rw [hρ, Real.div_rpow hR.le (by positivity), Real.rpow_neg (by positivity : (0:ℝ) ≤ 2 * σ),
      div_inv_eq_mul]
  have hR2' : 0 < 2 * R := by positivity
  have hU0 : 0 ≤ U := (abs_nonneg _).trans (hU c (mem_ball_self hR2'))
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM c (mem_ball_self hR2'))
  have hHr : (0:ℝ) ≤ H := H.coe_nonneg
  -- Step 7: pointwise bound on `B_R(c)` with the constant `C₁`.
  have hsup : ∀ x₀ ∈ ball c R,
      ‖fderiv ℝ (fderiv ℝ u) x₀‖ ≤ C₁ * (U * R ^ (-(2:ℝ)) + M + R ^ (α:ℝ) * H) := by
    intro x₀ hx₀
    have hx₀2 : x₀ ∈ ball c (2 * R) := ball_subset_ball (by linarith) hx₀
    have hz := (hlocal x₀ hx₀).1 (T.symm x₀) (mem_ball_self hρ_pos)
    rw [huH x₀ hx₀2]
    have hR2 : 0 ≤ R ^ (-(2:ℝ)) := by positivity
    have hRα : 0 ≤ R ^ (α:ℝ) := by positivity
    have hpos : 0 ≤ U * ρ ^ (-(2:ℝ)) + M + ρ ^ (α:ℝ) * H' := by positivity
    calc ‖(fderiv ℝ (fderiv ℝ v) (T.symm x₀)).bilinearComp T.symm.toContinuousLinearMap
            T.symm.toContinuousLinearMap‖
        ≤ ‖fderiv ℝ (fderiv ℝ v) (T.symm x₀)‖ * ‖T.symm.toContinuousLinearMap‖ ^ 2 :=
          norm_bilinearComp_self_le _ _
      _ ≤ (C₀ * (U * ρ ^ (-(2:ℝ)) + M + ρ ^ (α:ℝ) * H')) * τ ^ 2 :=
          mul_le_mul hz hTsymm_sq (by positivity) (by positivity)
      _ ≤ C₁ * (U * R ^ (-(2:ℝ)) + M + R ^ (α:ℝ) * H) := by
          rw [hC₁def, hρ2, hH'coe]
          have key : U * (4 * Lam * R ^ (-(2:ℝ))) + M + ρ ^ (α:ℝ) * (H * σ ^ (α:ℝ)) ≤
              (4 * Lam + 1) * (U * R ^ (-(2:ℝ)) + M + R ^ (α:ℝ) * H) := by
            have e1 : ρ ^ (α:ℝ) * (H * σ ^ (α:ℝ)) = (ρ ^ (α:ℝ) * σ ^ (α:ℝ)) * H := by ring
            rw [e1]
            nlinarith [mul_le_mul_of_nonneg_right hρα hHr, mul_nonneg hU0 hR2,
              mul_nonneg (mul_nonneg hU0 hR2) hLam0.le, mul_nonneg hM0 hLam0.le,
              mul_nonneg (mul_nonneg hRα hHr) hLam0.le]
          calc C₀ * (U * (4 * Lam * R ^ (-(2:ℝ))) + M + ρ ^ (α:ℝ) * (H * σ ^ (α:ℝ))) * τ ^ 2
              ≤ C₀ * ((4 * Lam + 1) * (U * R ^ (-(2:ℝ)) + M + R ^ (α:ℝ) * H)) * τ ^ 2 := by
                gcongr
            _ = _ := by ring
  -- Step 8: Hölder bound for near points (`τ ‖x - y‖ < ρ`) with the constant `C₂`.
  have hhol1 : ∀ x ∈ ball c R, ∀ y ∈ ball c R, τ * ‖x - y‖ < ρ →
      ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖ ≤
        C₂ * (U * R ^ (-(2:ℝ) - α) + M * R ^ (-(α:ℝ)) + H) * ‖x - y‖ ^ (α:ℝ) := by
    intro x hx y hy hxy
    have hx2 : x ∈ ball c (2 * R) := ball_subset_ball (by linarith) hx
    have hy2 : y ∈ ball c (2 * R) := ball_subset_ball (by linarith) hy
    have hyx : T.symm y ∈ ball (T.symm x) ρ := by
      rw [mem_ball, dist_eq_norm, ← map_sub]
      calc ‖T.symm (y - x)‖ ≤ τ * ‖y - x‖ := hTinv _
        _ = τ * ‖x - y‖ := by rw [norm_sub_rev]
        _ < ρ := hxy
    have hz := (hlocal x hx).2 (T.symm x) (mem_ball_self hρ_pos) (T.symm y) hyx
    rw [huH x hx2, huH y hy2]
    have hsub : (fderiv ℝ (fderiv ℝ v) (T.symm x)).bilinearComp T.symm.toContinuousLinearMap
          T.symm.toContinuousLinearMap -
        (fderiv ℝ (fderiv ℝ v) (T.symm y)).bilinearComp T.symm.toContinuousLinearMap
          T.symm.toContinuousLinearMap =
        (fderiv ℝ (fderiv ℝ v) (T.symm x) - fderiv ℝ (fderiv ℝ v) (T.symm y)).bilinearComp
          T.symm.toContinuousLinearMap T.symm.toContinuousLinearMap := by
      ext a b
      rfl
    rw [hsub]
    have hdist : ‖T.symm x - T.symm y‖ ^ (α:ℝ) ≤ τ ^ (α:ℝ) * ‖x - y‖ ^ (α:ℝ) := by
      rw [← Real.mul_rpow hτ.le (norm_nonneg _)]
      refine Real.rpow_le_rpow (norm_nonneg _) ?_ hαr
      rw [← map_sub]; exact hTinv _
    have hpos : 0 ≤ C₀ * (U * ρ ^ (-(2:ℝ) - α) + M * ρ ^ (-(α:ℝ)) + H') := by positivity
    calc ‖(fderiv ℝ (fderiv ℝ v) (T.symm x) - fderiv ℝ (fderiv ℝ v) (T.symm y)).bilinearComp
            T.symm.toContinuousLinearMap T.symm.toContinuousLinearMap‖
        ≤ ‖fderiv ℝ (fderiv ℝ v) (T.symm x) - fderiv ℝ (fderiv ℝ v) (T.symm y)‖ *
            ‖T.symm.toContinuousLinearMap‖ ^ 2 := norm_bilinearComp_self_le _ _
      _ ≤ (C₀ * (U * ρ ^ (-(2:ℝ) - α) + M * ρ ^ (-(α:ℝ)) + H') *
            ‖T.symm x - T.symm y‖ ^ (α:ℝ)) * τ ^ 2 :=
          mul_le_mul hz hTsymm_sq (by positivity) (by positivity)
      _ ≤ (C₀ * (U * ρ ^ (-(2:ℝ) - α) + M * ρ ^ (-(α:ℝ)) + H') *
            (τ ^ (α:ℝ) * ‖x - y‖ ^ (α:ℝ))) * τ ^ 2 := by
          gcongr
      _ ≤ C₂ * (U * R ^ (-(2:ℝ) - α) + M * R ^ (-(α:ℝ)) + H) * ‖x - y‖ ^ (α:ℝ) := by
          rw [hC₂def, hH'coe, hρ2α, hρα']
          have ha : 0 ≤ U * R ^ (-(2:ℝ) - α) := by positivity
          have hb : 0 ≤ M * R ^ (-(α:ℝ)) := by positivity
          have hp : 0 ≤ (2 * σ) ^ ((2:ℝ) + α) := by positivity
          have hq' : 0 ≤ (2 * σ) ^ (α:ℝ) := by positivity
          have hr : 0 ≤ σ ^ (α:ℝ) := by positivity
          have key : U * (R ^ (-(2:ℝ) - α) * (2 * σ) ^ ((2:ℝ) + α)) +
              M * (R ^ (-(α:ℝ)) * (2 * σ) ^ (α:ℝ)) + H * σ ^ (α:ℝ) ≤
              ((2 * σ) ^ ((2:ℝ) + α) + (2 * σ) ^ (α:ℝ) + σ ^ (α:ℝ)) *
                (U * R ^ (-(2:ℝ) - α) + M * R ^ (-(α:ℝ)) + H) := by
            have e : ((2 * σ) ^ ((2:ℝ) + α) + (2 * σ) ^ (α:ℝ) + σ ^ (α:ℝ)) *
                  (U * R ^ (-(2:ℝ) - α) + M * R ^ (-(α:ℝ)) + H) -
                (U * (R ^ (-(2:ℝ) - α) * (2 * σ) ^ ((2:ℝ) + α)) +
                  M * (R ^ (-(α:ℝ)) * (2 * σ) ^ (α:ℝ)) + H * σ ^ (α:ℝ)) =
                (U * R ^ (-(2:ℝ) - α)) * ((2 * σ) ^ (α:ℝ) + σ ^ (α:ℝ)) +
                  (M * R ^ (-(α:ℝ))) * ((2 * σ) ^ ((2:ℝ) + α) + σ ^ (α:ℝ)) +
                  H * ((2 * σ) ^ ((2:ℝ) + α) + (2 * σ) ^ (α:ℝ)) := by ring
            have h1 := mul_nonneg ha (add_nonneg hq' hr)
            have h2 := mul_nonneg hb (add_nonneg hp hr)
            have h3 := mul_nonneg hHr (add_nonneg hp hq')
            linarith
          have hfac : 0 ≤ C₀ * τ ^ 2 * τ ^ (α:ℝ) * ‖x - y‖ ^ (α:ℝ) := by positivity
          calc C₀ * (U * (R ^ (-(2:ℝ) - α) * (2 * σ) ^ ((2:ℝ) + α)) +
                  M * (R ^ (-(α:ℝ)) * (2 * σ) ^ (α:ℝ)) + H * σ ^ (α:ℝ)) *
                (τ ^ (α:ℝ) * ‖x - y‖ ^ (α:ℝ)) * τ ^ 2
              = C₀ * τ ^ 2 * τ ^ (α:ℝ) * ‖x - y‖ ^ (α:ℝ) *
                  (U * (R ^ (-(2:ℝ) - α) * (2 * σ) ^ ((2:ℝ) + α)) +
                    M * (R ^ (-(α:ℝ)) * (2 * σ) ^ (α:ℝ)) + H * σ ^ (α:ℝ)) := by ring
            _ ≤ C₀ * τ ^ 2 * τ ^ (α:ℝ) * ‖x - y‖ ^ (α:ℝ) *
                  (((2 * σ) ^ ((2:ℝ) + α) + (2 * σ) ^ (α:ℝ) + σ ^ (α:ℝ)) *
                    (U * R ^ (-(2:ℝ) - α) + M * R ^ (-(α:ℝ)) + H)) :=
                mul_le_mul_of_nonneg_left key hfac
            _ = _ := by ring
  -- Step 9: Hölder bound for far points (`ρ ≤ τ ‖x - y‖`) with the constant `C₃`.
  have hhol2 : ∀ x ∈ ball c R, ∀ y ∈ ball c R, ρ ≤ τ * ‖x - y‖ →
      ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖ ≤
        C₃ * (U * R ^ (-(2:ℝ) - α) + M * R ^ (-(α:ℝ)) + H) * ‖x - y‖ ^ (α:ℝ) := by
    intro x hx y hy hfar
    have hRle : R ≤ 2 * σ * τ * ‖x - y‖ := by
      rw [hρ, div_le_iff₀ (by positivity)] at hfar
      linarith
    have hRα : R ^ (α:ℝ) ≤ (2 * σ * τ) ^ (α:ℝ) * ‖x - y‖ ^ (α:ℝ) := by
      rw [← Real.mul_rpow (by positivity) (norm_nonneg _)]
      exact Real.rpow_le_rpow hR.le hRle hαr
    have hsx := hsup x hx
    have hsy := hsup y hy
    have hsplit : ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖ ≤
        ‖fderiv ℝ (fderiv ℝ u) x‖ + ‖fderiv ℝ (fderiv ℝ u) y‖ := by
      have h := ContinuousLinearMap.opNorm_add_le (fderiv ℝ (fderiv ℝ u) x)
        (-fderiv ℝ (fderiv ℝ u) y)
      rwa [ContinuousLinearMap.opNorm_neg, ← sub_eq_add_neg] at h
    have hR1 : R ^ (-(2:ℝ)) = R ^ (-(2:ℝ) - α) * R ^ (α:ℝ) := by
      rw [← Real.rpow_add hR]; congr 1; ring
    have hR2 : R ^ (-(α:ℝ)) * R ^ (α:ℝ) = 1 := by
      rw [← Real.rpow_add hR]; simp
    have hfactor : U * R ^ (-(2:ℝ)) + M + R ^ (α:ℝ) * H =
        (U * R ^ (-(2:ℝ) - α) + M * R ^ (-(α:ℝ)) + H) * R ^ (α:ℝ) := by
      rw [hR1]
      linear_combination (-M) * hR2
    have hX : 0 ≤ U * R ^ (-(2:ℝ) - α) + M * R ^ (-(α:ℝ)) + H := by positivity
    calc ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖
        ≤ ‖fderiv ℝ (fderiv ℝ u) x‖ + ‖fderiv ℝ (fderiv ℝ u) y‖ := hsplit
      _ ≤ 2 * (C₁ * (U * R ^ (-(2:ℝ)) + M + R ^ (α:ℝ) * H)) := by linarith
      _ = 2 * C₁ * (U * R ^ (-(2:ℝ) - α) + M * R ^ (-(α:ℝ)) + H) * R ^ (α:ℝ) := by
          rw [hfactor]; ring
      _ ≤ 2 * C₁ * (U * R ^ (-(2:ℝ) - α) + M * R ^ (-(α:ℝ)) + H) *
            ((2 * σ * τ) ^ (α:ℝ) * ‖x - y‖ ^ (α:ℝ)) :=
          mul_le_mul_of_nonneg_left hRα (by positivity)
      _ = C₃ * (U * R ^ (-(2:ℝ) - α) + M * R ^ (-(α:ℝ)) + H) * ‖x - y‖ ^ (α:ℝ) := by
          rw [hC₃def]; ring
  -- Step 10: assembly with `C = C₁ + C₂ + C₃`.
  refine ⟨fun x hx => ?_, fun x hx y hy => ?_⟩
  · have hX : 0 ≤ U * R ^ (-(2:ℝ)) + M + R ^ (α:ℝ) * H := by positivity
    calc ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ C₁ * (U * R ^ (-(2:ℝ)) + M + R ^ (α:ℝ) * H) := hsup x hx
      _ ≤ (C₁ + C₂ + C₃) * (U * R ^ (-(2:ℝ)) + M + R ^ (α:ℝ) * H) :=
          mul_le_mul_of_nonneg_right (by linarith) hX
  · have hX : 0 ≤ U * R ^ (-(2:ℝ) - α) + M * R ^ (-(α:ℝ)) + H := by positivity
    have ht : 0 ≤ ‖x - y‖ ^ (α:ℝ) := by positivity

    -- Combine the near-point and separated-point Holder estimates.
    by_cases hcase : τ * ‖x - y‖ < ρ
    · calc ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖
          ≤ C₂ * (U * R ^ (-(2:ℝ) - α) + M * R ^ (-(α:ℝ)) + H) * ‖x - y‖ ^ (α:ℝ) :=
            hhol1 x hx y hy hcase
        _ ≤ (C₁ + C₂ + C₃) * (U * R ^ (-(2:ℝ) - α) + M * R ^ (-(α:ℝ)) + H) * ‖x - y‖ ^ (α:ℝ) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hX) ht
    · calc ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖
          ≤ C₃ * (U * R ^ (-(2:ℝ) - α) + M * R ^ (-(α:ℝ)) + H) * ‖x - y‖ ^ (α:ℝ) :=
            hhol2 x hx y hy (not_lt.mp hcase)
        _ ≤ (C₁ + C₂ + C₃) * (U * R ^ (-(2:ℝ) - α) + M * R ^ (-(α:ℝ)) + H) * ‖x - y‖ ^ (α:ℝ) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hX) ht

end FunctionalInequalities.Analysis
