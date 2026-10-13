import FunctionalInequalities.Analysis.Tensor.SlotAction

/-!
# The energy form of a coordinate tensor

`energyForm A T = ⟨T, (A⁻¹)^{⊗r} T⟩` for an operator `A` and an order-`r` coordinate tensor `T` (BKL arXiv:2610.05474v1, p. 22,
`F(A, T)`), the standard matrix of an operator, `energyForm 1 T = |T|²`, and smoothness near invertible `A`. Proof bodies:
GPT (S-line sub-controller task S-3bF); statements by the S-line sub-controller; placement: Claude.
-/

noncomputable section

open Matrix
open scoped RealInnerProductSpace

namespace FunctionalInequalities.Analysis.CoordinateTensor

variable {n r : ℕ}

/-- The matrix of an operator on `ℝⁿ` in the standard basis: `(stdMatrix H) i k = ⟪e_i, H e_k⟫`. -/
def stdMatrix (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i k => ⟪EuclideanSpace.basisFun (Fin n) ℝ i, H (EuclideanSpace.basisFun (Fin n) ℝ k)⟫

/-- The energy form `F(A, T) = ⟨T, (A⁻¹)^{⊗r} T⟩ = Σ_{J,J'} T_J T_{J'} Π_s ⟪e_{J_s}, A⁻¹ e_{J'_s}⟫` of BKL
arXiv:2610.05474v1, p. 22 (`A⁻¹ = Ring.inverse A`, the canonical inverse of the operator algebra). -/
def energyForm (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (T : (Fin r → Fin n) → ℝ) : ℝ :=
  ∑ J : Fin r → Fin n, ∑ J' : Fin r → Fin n, T J * T J' *
    ∏ s, ⟪EuclideanSpace.basisFun (Fin n) ℝ (J s), Ring.inverse A (EuclideanSpace.basisFun (Fin n) ℝ (J' s))⟫

private lemma delta_product (J K : Fin r → Fin n) :
    (∏ s, if J s = K s then (1 : ℝ) else 0) =
      if J = K then 1 else 0 := by
  classical
  by_cases h : J = K
  · subst K
    simp
  · rw [if_neg h]
    have hex : ∃ s, J s ≠ K s := by
      by_contra hnone
      apply h
      funext s
      by_contra hs
      exact hnone ⟨s, hs⟩
    obtain ⟨s, hs⟩ := hex
    exact Finset.prod_eq_zero (Finset.mem_univ s) (if_neg hs)

/-- At `A = Id` the energy form is the Euclidean norm squared. -/
theorem energyForm_one (T : (Fin r → Fin n) → ℝ) : energyForm 1 T = inner T T := by
  classical
  simp only [energyForm, Ring.inverse_one, one_apply_eq_self,
    OrthonormalBasis.inner_eq_ite]
  simp_rw [delta_product]
  simp [inner, mul_ite]

/-- The energy form is `C²` near every `(A, T)` with `A` a unit. -/
theorem contDiffAt_energyForm (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (hA : IsUnit A)
    (T : (Fin r → Fin n) → ℝ) :
    ContDiffAt ℝ 2 (fun q : (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) × ((Fin r → Fin n) → ℝ) =>
      energyForm q.1 q.2) (A, T) := by
  classical
  have hinv : ContDiffAt ℝ 2 Ring.inverse A := by
    simpa only [hA.unit_spec] using contDiffAt_ringInverse ℝ hA.unit
  have hcoord (J : Fin r → Fin n) :
      ContDiffAt ℝ 2
        (fun q :
          (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) ×
            ((Fin r → Fin n) → ℝ) => q.2 J) (A, T) :=
    (ContinuousLinearMap.proj J :
      ((Fin r → Fin n) → ℝ) →L[ℝ] ℝ).contDiff.contDiffAt.comp
        (A, T) contDiffAt_snd
  unfold energyForm
  apply ContDiffAt.sum
  intro J _
  apply ContDiffAt.sum
  intro K _
  apply ContDiffAt.mul ((hcoord J).mul (hcoord K))
  apply contDiffAt_prod
  intro s _
  exact ContDiffAt.inner ℝ contDiffAt_const
    ((hinv.comp (A, T) contDiffAt_fst).clm_apply contDiffAt_const)

end FunctionalInequalities.Analysis.CoordinateTensor

section S3Bf2EnergyFormFirstOrder

open Matrix
open scoped RealInnerProductSpace

/-! First derivative of the energy form at `A = Id` (BKL (88), first order; task S-3bF2). -/

namespace FunctionalInequalities.Analysis.CoordinateTensor

variable {n r : ℕ}

/-- **Delta collapse on all slots but one**: `Σ_{J'} f(J') Π_{s' ≠ s} δ_{J_{s'} J'_{s'}} = Σ_k f(J[s ↦ k])`. -/
theorem sum_mul_prod_delta_erase (J : Fin r → Fin n) (s : Fin r) (f : (Fin r → Fin n) → ℝ) :
    ∑ J' : Fin r → Fin n, f J' * ∏ s' ∈ Finset.univ.erase s, (if J s' = J' s' then (1 : ℝ) else 0) =
      ∑ k, f (Function.update J s k) := by
  classical
  let p : (Fin r → Fin n) → Prop :=
    fun J' => ∀ s' ∈ Finset.univ.erase s, J s' = J' s'
  have hprod (J' : Fin r → Fin n) :
      (∏ s' ∈ Finset.univ.erase s, (if J s' = J' s' then (1 : ℝ) else 0)) =
        if p J' then 1 else 0 := by
    by_cases hp : p J'
    · simp only [p, if_pos hp]
      apply Finset.prod_eq_one
      intro s' hs'
      exact if_pos (hp s' hs')
    · rw [if_neg hp]
      obtain ⟨s', hs', hne⟩ : ∃ s', s' ∈ Finset.univ.erase s ∧ J s' ≠ J' s' := by
        by_contra h
        apply hp
        intro s' hs'
        by_contra h'
        exact h ⟨s', hs', h'⟩
      exact Finset.prod_eq_zero hs' (if_neg hne)
  have hfilter :
      Finset.univ.filter p = Finset.univ.image (Function.update J s) := by
    ext J'
    constructor
    · intro hJ'
      have hp : p J' := (Finset.mem_filter.mp hJ').2
      have heq : Function.update J s (J' s) = J' := by
        funext s'
        by_cases hss' : s' = s
        · subst s'
          simp
        · have hmem : s' ∈ Finset.univ.erase s := by simp [hss']
          simp [Function.update, hss', hp s' hmem]
      exact Finset.mem_image.mpr ⟨J' s, Finset.mem_univ _, heq⟩
    · intro hJ'
      obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hJ'
      apply Finset.mem_filter.mpr
      constructor
      · exact Finset.mem_univ _
      · intro s' hs'
        have hne : s' ≠ s := by simpa using hs'
        simp [Function.update, hne]
  calc
    ∑ J' : Fin r → Fin n, f J' *
        ∏ s' ∈ Finset.univ.erase s, (if J s' = J' s' then (1 : ℝ) else 0) =
        ∑ J', if p J' then f J' else 0 := by
      apply Finset.sum_congr rfl
      intro J' hJ'
      rw [hprod]
      by_cases hp : p J' <;> simp [hp]
    _ = ∑ J' ∈ Finset.univ.filter p, f J' := by
      rw [← Finset.sum_filter]
    _ = ∑ J' ∈ Finset.univ.image (Function.update J s), f J' := by
      rw [hfilter]
    _ = ∑ k, f (Function.update J s k) := by
      rw [Finset.sum_image]
      intro k hk l hl hkl
      exact (Function.update_injective J s) hkl

private lemma inverse_line {R : Type*} [NormedRing R]
    [NormedAlgebra ℝ R] [HasSummableGeomSeries R] (H : R) :
    HasDerivAt (fun t : ℝ => Ring.inverse (1 + t • H)) (-H) 0 := by
  have hl : HasDerivAt (fun t : ℝ => (1 : R) + t • H) H 0 := by
    simpa only [id_eq, one_smul] using
      (((hasDerivAt_id (0 : ℝ)).smul_const H).const_add (1 : R))
  have hi :
      HasFDerivAt Ring.inverse
        (-((ContinuousLinearMap.mulLeftRight ℝ R) (1 : R)) (1 : R))
        ((1 : R) + (0 : ℝ) • H) := by
    simpa only [zero_smul, add_zero, inv_one, Units.val_one] using
      (hasFDerivAt_ringInverse (𝕜 := ℝ) (1 : Rˣ))
  have hc := hi.comp_hasDerivAt 0 hl
  have heq :
      (-((ContinuousLinearMap.mulLeftRight ℝ R) (1 : R)) (1 : R)) H = -H := by
    change -((1 : R) * H * 1) = -H
    rw [one_mul, mul_one]
  simpa only [Function.comp_def] using hc.congr_deriv heq

/-- The entries of `(1 + εH)⁻¹` have derivative `−⟪e_i, H e_k⟫` at `ε = 0`. -/
theorem hasDerivAt_inner_ringInverse_one_add (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (i k : Fin n) :
    HasDerivAt (fun ε : ℝ => ⟪EuclideanSpace.basisFun (Fin n) ℝ i,
        Ring.inverse (1 + ε • H) (EuclideanSpace.basisFun (Fin n) ℝ k)⟫)
      (-⟪EuclideanSpace.basisFun (Fin n) ℝ i, H (EuclideanSpace.basisFun (Fin n) ℝ k)⟫) 0 := by
  have hi :
      HasDerivAt (fun t : ℝ => Ring.inverse (1 + t • H)) (-H) 0 := by
    convert inverse_line H using 1
  have hv := hi.clm_apply
    (hasDerivAt_const (0 : ℝ) (EuclideanSpace.basisFun (Fin n) ℝ k))
  have h := (hasDerivAt_const (0 : ℝ)
    (EuclideanSpace.basisFun (Fin n) ℝ i)).inner ℝ hv
  simpa using h

/-- The directional derivative is the derivative along the line. -/
theorem fderiv_apply_eq_deriv_line {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] {Φ : W → ℝ} {y : W}
    (hΦ : DifferentiableAt ℝ Φ y) (v : W) :
    fderiv ℝ Φ y v = deriv (fun ε : ℝ => Φ (y + ε • v)) 0 := by
  let line : ℝ → W := fun ε => y + ε • v
  have hl : HasDerivAt line v 0 := by
    simpa only [line, id_eq, one_smul] using
      (((hasDerivAt_id (0 : ℝ)).smul_const v).const_add y)
  have hp : HasFDerivAt Φ (fderiv ℝ Φ y) (line 0) := by
    simpa [line] using hΦ.hasFDerivAt
  have hd := (hp.comp_hasDerivAt 0 hl).deriv.symm
  change fderiv ℝ Φ y v = deriv (fun ε : ℝ => Φ (y + ε • v)) 0 at hd
  exact hd

private lemma real_deriv_mul {f g : ℝ → ℝ} {df dg x : ℝ}
    (hf : HasDerivAt f df x) (hg : HasDerivAt g dg x) :
    HasDerivAt (fun t => f t * g t) (df * g x + f x * dg) x := by
  convert hf.mul hg using 1 <;> rfl

private lemma real_deriv_sum {ι : Type*} (s : Finset ι)
    (f : ι → ℝ → ℝ) (df : ι → ℝ) (x : ℝ)
    (hf : ∀ i ∈ s, HasDerivAt (f i) (df i) x) :
    HasDerivAt (fun t => ∑ i ∈ s, f i t) (∑ i ∈ s, df i) x := by
  have h := HasDerivAt.sum hf
  have he : (∑ i ∈ s, f i) = (fun t => ∑ i ∈ s, f i t) := by
    funext t
    simp
  rw [he] at h
  convert h using 1

private lemma real_deriv_prod {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → ℝ → ℝ) (df : ι → ℝ) (x : ℝ)
    (hf : ∀ i ∈ s, HasDerivAt (f i) (df i) x) :
    HasDerivAt (fun t => ∏ i ∈ s, f i t)
      (∑ i ∈ s, (∏ j ∈ s.erase i, f j x) * df i) x := by
  have h := HasDerivAt.finsetProd hf
  have he : (∏ i ∈ s, f i) = (fun t => ∏ i ∈ s, f i t) := by
    funext t
    simp
  rw [he] at h
  simp only [smul_eq_mul] at h
  convert h using 1

private lemma slot_derivative_sum
    (T : (Fin r → Fin n) → ℝ) (M : Matrix (Fin n) (Fin n) ℝ) :
    (∑ J : Fin r → Fin n, ∑ K : Fin r → Fin n,
      T J * T K * (∑ s : Fin r,
        (∏ u ∈ Finset.univ.erase s, if J u = K u then (1 : ℝ) else 0) *
          (-M (J s) (K s)))) =
      -inner T (actSum M T) := by
  classical
  let D (s : Fin r) (J K : Fin r → Fin n) : ℝ :=
    ∏ u ∈ Finset.univ.erase s, if J u = K u then (1 : ℝ) else 0
  have hc (s : Fin r) (J : Fin r → Fin n) :
      (∑ K, (T K * M (J s) (K s)) * D s J K) =
        ∑ k, T (Function.update J s k) * M (J s) k := by
    simpa only [D, Function.update_self] using
      sum_mul_prod_delta_erase J s (fun K => T K * M (J s) (K s))
  have hs (s : Fin r) (J : Fin r → Fin n) :
      (∑ K, T J * T K * (D s J K * (-M (J s) (K s)))) =
        -(T J * actOn M s T J) := by
    calc
      (∑ K, T J * T K * (D s J K * (-M (J s) (K s)))) =
          ∑ K, -(T J * ((T K * M (J s) (K s)) * D s J K)) := by
        apply Finset.sum_congr rfl
        intro K _
        ring
      _ = -(T J * ∑ K, (T K * M (J s) (K s)) * D s J K) := by
        rw [Finset.sum_neg_distrib, Finset.mul_sum]
      _ = -(T J * actOn M s T J) := by
        rw [hc]
        apply congrArg (fun z : ℝ => -(T J * z))
        unfold actOn
        apply Finset.sum_congr rfl
        intro k _
        exact mul_comm _ _
  have hJ (J : Fin r → Fin n) :
      (∑ K, T J * T K * (∑ s, D s J K * (-M (J s) (K s)))) =
        -(T J * actSum M T J) := by
    calc
      (∑ K, T J * T K * (∑ s, D s J K * (-M (J s) (K s)))) =
          ∑ K, ∑ s, T J * T K * (D s J K * (-M (J s) (K s))) := by
        simp only [Finset.mul_sum]
      _ = ∑ s, ∑ K, T J * T K * (D s J K * (-M (J s) (K s))) := by
        rw [Finset.sum_comm]
      _ = ∑ s, -(T J * actOn M s T J) := by
        apply Finset.sum_congr rfl
        intro s _
        exact hs s J
      _ = -(T J * actSum M T J) := by
        unfold actSum
        rw [Finset.sum_neg_distrib, Finset.mul_sum]
  change (∑ J, ∑ K, T J * T K * (∑ s, D s J K * (-M (J s) (K s)))) =
    -inner T (actSum M T)
  calc
    (∑ J, ∑ K, T J * T K * (∑ s, D s J K * (-M (J s) (K s)))) =
        ∑ J, -(T J * actSum M T J) := by
      apply Finset.sum_congr rfl
      intro J _
      exact hJ J
    _ = -inner T (actSum M T) := by
      simp only [inner, Finset.sum_neg_distrib]

set_option maxHeartbeats 800000 in
/-- **BKL (88), first order, along the line**: `d/dε F(1 + εH, T + εX)|₀ = 2⟨T, X⟩ − ⟨T, Σ_H T⟩`. -/
theorem hasDerivAt_energyForm_line (T : (Fin r → Fin n) → ℝ)
    (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (X : (Fin r → Fin n) → ℝ) :
    HasDerivAt (fun ε : ℝ => energyForm (1 + ε • H) (T + ε • X))
      (2 * inner T X - inner T (actSum (stdMatrix H) T)) 0 := by
  classical
  let a (i k : Fin n) (t : ℝ) : ℝ :=
    ⟪EuclideanSpace.basisFun (Fin n) ℝ i,
      Ring.inverse (1 + t • H) (EuclideanSpace.basisFun (Fin n) ℝ k)⟫
  let P (J K : Fin r → Fin n) : ℝ :=
    ∏ s, if J s = K s then (1 : ℝ) else 0
  let Q (J K : Fin r → Fin n) : ℝ :=
    ∑ s, (∏ u ∈ Finset.univ.erase s, if J u = K u then (1 : ℝ) else 0) *
      (-stdMatrix H (J s) (K s))
  have a0 (i k : Fin n) : a i k 0 = if i = k then 1 else 0 := by
    have hz :
        (1 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) +
          (0 : ℝ) • H = 1 := by
      apply ContinuousLinearMap.ext
      intro v
      change v + (0 : ℝ) • H v = v
      simp
    unfold a
    rw [hz, Ring.inverse_one]
    exact (EuclideanSpace.basisFun (Fin n) ℝ).inner_eq_ite i k
  have ha (i k : Fin n) :
      HasDerivAt (a i k) (-stdMatrix H i k) 0 :=
    hasDerivAt_inner_ringInverse_one_add H i k
  have hp (J K : Fin r → Fin n) :
      HasDerivAt (fun t => ∏ s, a (J s) (K s) t) (Q J K) 0 := by
    have h := real_deriv_prod Finset.univ
      (fun s t => a (J s) (K s) t)
      (fun s => -stdMatrix H (J s) (K s)) 0
      (fun s _ => ha (J s) (K s))
    apply h.congr_deriv
    simp only [a0, Q]
  have hp0 (J K : Fin r → Fin n) :
      (∏ s, a (J s) (K s) 0) = P J K := by
    simp only [a0, P]
  have ht (J : Fin r → Fin n) :
      HasDerivAt (fun t : ℝ => T J + t * X J) (X J) 0 := by
    simpa only [id_eq, one_mul] using
      (((hasDerivAt_id (0 : ℝ)).mul_const (X J)).const_add (T J))
  let d (J K : Fin r → Fin n) : ℝ :=
    (X J * T K + T J * X K) * P J K + T J * T K * Q J K
  have hterm (J K : Fin r → Fin n) :
      HasDerivAt
        (fun t : ℝ => (T J + t * X J) * (T K + t * X K) *
          (∏ s, a (J s) (K s) t))
        (d J K) 0 := by
    have h := real_deriv_mul (real_deriv_mul (ht J) (ht K)) (hp J K)
    apply h.congr_deriv
    simp only [zero_mul, add_zero, hp0, d]
  have hraw :
      HasDerivAt
        (fun t : ℝ => ∑ J, ∑ K,
          (T J + t * X J) * (T K + t * X K) *
            (∏ s, a (J s) (K s) t))
        (∑ J, ∑ K, d J K) 0 := by
    apply real_deriv_sum
    intro J _
    apply real_deriv_sum
    intro K _
    exact hterm J K
  have hfirst :
      (∑ J, ∑ K, (X J * T K + T J * X K) * P J K) =
        2 * inner T X := by
    calc
      (∑ J, ∑ K, (X J * T K + T J * X K) * P J K) =
          ∑ J, (X J * T J + T J * X J) := by
        apply Finset.sum_congr rfl
        intro J _
        simp [P, delta_product, mul_ite]
      _ = ∑ J, 2 * (T J * X J) := by
        apply Finset.sum_congr rfl
        intro J _
        ring
      _ = 2 * inner T X := by
        rw [← Finset.mul_sum]
        rfl
  have hsecond :
      (∑ J, ∑ K, T J * T K * Q J K) =
        -inner T (actSum (stdMatrix H) T) :=
    slot_derivative_sum T (stdMatrix H)
  have hd :
      (∑ J, ∑ K, d J K) =
        2 * inner T X - inner T (actSum (stdMatrix H) T) := by
    simp only [d, Finset.sum_add_distrib]
    rw [hfirst, hsecond]
    rfl
  have h := hraw.congr_deriv hd
  convert h using 1 <;> rfl

set_option maxHeartbeats 800000 in
/-- **BKL (88), first order**: `DF(Id, T)[(H, X)] = 2⟨T, X⟩ − ⟨T, Σ_H T⟩`. -/
theorem fderiv_energyForm_one (T : (Fin r → Fin n) → ℝ)
    (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (X : (Fin r → Fin n) → ℝ) :
    fderiv ℝ (fun q : (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) × ((Fin r → Fin n) → ℝ) =>
        energyForm q.1 q.2) (1, T) (H, X) =
      2 * inner T X - inner T (actSum (stdMatrix H) T) := by
  have hdiff :=
    (contDiffAt_energyForm
      (1 : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
      isUnit_one T).differentiableAt (by norm_num)
  rw [fderiv_apply_eq_deriv_line hdiff (H, X)]
  change deriv (fun t : ℝ => energyForm (1 + t • H) (T + t • X)) 0 =
    2 * inner T X - inner T (actSum (stdMatrix H) T)
  exact (hasDerivAt_energyForm_line T H X).deriv

end FunctionalInequalities.Analysis.CoordinateTensor

end S3Bf2EnergyFormFirstOrder

section S3Bf3B1SecondOrderHelpers

open Matrix
open scoped RealInnerProductSpace

/-! Helpers for the second-order expansion of the energy form: a double-erasure product sum and line derivatives of `⟪(1 + tB)⁻¹ ·, ·⟫` (task S-3bF3b1). -/

namespace FunctionalInequalities.Analysis.CoordinateTensor

variable {n r : ℕ}

private lemma inverse_line_at_unit {R : Type*} [NormedRing R]
    [NormedAlgebra ℝ R] [HasSummableGeomSeries R]
    (H : R) (t : ℝ) (ht : IsUnit (1 + t • H)) :
    HasDerivAt (fun x : ℝ => Ring.inverse (1 + x • H))
      (-(Ring.inverse (1 + t • H) * H * Ring.inverse (1 + t • H))) t := by
  have hl : HasDerivAt (fun x : ℝ => (1 : R) + x • H) H t := by
    simpa only [id_eq, one_smul] using
      ((hasDerivAt_id t).smul_const H).const_add (1 : R)
  have hi := hasFDerivAt_ringInverse (𝕜 := ℝ) ht.unit
  rw [ht.unit_spec] at hi
  have hc := hi.comp_hasDerivAt t hl
  simpa only [Function.comp_def, _root_.neg_apply,
    ContinuousLinearMap.mulLeftRight_apply, ← Ring.inverse_unit, ht.unit_spec] using hc

private lemma inverse_line_at_zero {R : Type*} [NormedRing R]
    [NormedAlgebra ℝ R] [HasSummableGeomSeries R] (H : R) :
    HasDerivAt (fun t : ℝ => Ring.inverse (1 + t • H)) (-H) 0 := by
  have hu : IsUnit ((1 : R) + (0 : ℝ) • H) := by
    simpa only [zero_smul, add_zero] using (isUnit_one : IsUnit (1 : R))
  simpa only [zero_smul, add_zero, Ring.inverse_one, one_mul, mul_one] using
    inverse_line_at_unit H 0 hu

private lemma inverse_entry_at_unit
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (H : E →L[ℝ] E) (L : E →L[ℝ] ℝ) (v : E) (t : ℝ)
    (ht : IsUnit (1 + t • H)) :
    HasDerivAt (fun x : ℝ => L (Ring.inverse (1 + x • H) v))
      (-L (Ring.inverse (1 + t • H) (H (Ring.inverse (1 + t • H) v)))) t := by
  have h := inverse_line_at_unit H t ht
  simpa only [Function.comp_def, _root_.neg_apply, mul_apply_eq_comp,
    map_zero, add_zero, map_neg] using
    L.hasFDerivAt.comp_hasDerivAt t (h.clm_apply (hasDerivAt_const t v))

private lemma inverse_entry_second
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (H : E →L[ℝ] E) (L : E →L[ℝ] ℝ) (v : E) :
    HasDerivAt (deriv fun t : ℝ => L (Ring.inverse (1 + t • H) v))
      (2 * L (H (H v))) 0 := by
  have hR := inverse_line_at_zero H
  have hv := hR.clm_apply (hasDerivAt_const (0 : ℝ) v)
  have hHv := (hasDerivAt_const (0 : ℝ) H).clm_apply hv
  have hboth := hR.clm_apply hHv
  have hh := (-L).hasFDerivAt.comp_hasDerivAt 0 hboth
  have hd :
      HasDerivAt
        (fun t : ℝ =>
          -L (Ring.inverse (1 + t • H) (H (Ring.inverse (1 + t • H) v))))
        (2 * L (H (H v))) 0 := by
    simpa only [Function.comp_def, zero_smul, add_zero, Ring.inverse_one,
      one_apply_eq_self, _root_.neg_apply, _root_.zero_apply, map_zero,
      zero_add, map_neg, map_add, neg_add, neg_neg, two_mul] using hh
  have hopen : {t : ℝ | IsUnit (1 + t • H)} ∈ nhds (0 : ℝ) := by
    have hc : Continuous (fun t : ℝ => (1 : E →L[ℝ] E) + t • H) :=
      continuous_const.add (continuous_id.smul continuous_const)
    apply (Units.isOpen.preimage hc).mem_nhds
    change IsUnit ((1 : E →L[ℝ] E) + (0 : ℝ) • H)
    simpa only [zero_smul, add_zero] using
      (isUnit_one : IsUnit (1 : E →L[ℝ] E))
  have heq :
      (deriv fun t : ℝ => L (Ring.inverse (1 + t • H) v)) =ᶠ[nhds 0]
        (fun t : ℝ =>
          -L (Ring.inverse (1 + t • H) (H (Ring.inverse (1 + t • H) v)))) := by
    filter_upwards [hopen] with t ht
    exact (inverse_entry_at_unit H L v t ht).deriv
  exact hd.congr_of_eventuallyEq heq

/-- **Delta collapse on all slots but two**: for `s ≠ t`,
`Σ_{J'} f(J') Π_{s' ∉ {s,t}} δ_{J_{s'} J'_{s'}} = Σ_{k,l} f(J[s ↦ k][t ↦ l])`. -/
theorem sum_mul_prod_delta_erase_erase (J : Fin r → Fin n) {s t : Fin r} (hst : s ≠ t)
    (f : (Fin r → Fin n) → ℝ) :
    ∑ J' : Fin r → Fin n, f J' *
        ∏ s' ∈ (Finset.univ.erase s).erase t, (if J s' = J' s' then (1 : ℝ) else 0) =
      ∑ k, ∑ l, f (Function.update (Function.update J s k) t l) := by
  classical
  let p : (Fin r → Fin n) → Prop :=
    fun J' => ∀ u ∈ (Finset.univ.erase s).erase t, J u = J' u
  let q : (Fin n × Fin n) → (Fin r → Fin n) :=
    fun kl => Function.update (Function.update J s kl.1) t kl.2
  have hprod (J' : Fin r → Fin n) :
      (∏ u ∈ (Finset.univ.erase s).erase t,
          (if J u = J' u then (1 : ℝ) else 0)) =
        if p J' then 1 else 0 := by
    by_cases hp : p J'
    · simp only [p, if_pos hp]
      apply Finset.prod_eq_one
      intro u hu
      exact if_pos (hp u hu)
    · rw [if_neg hp]
      obtain ⟨u, hu, hne⟩ :
          ∃ u, u ∈ (Finset.univ.erase s).erase t ∧ J u ≠ J' u := by
        by_contra h
        apply hp
        intro u hu
        by_contra h'
        exact h ⟨u, hu, h'⟩
      exact Finset.prod_eq_zero hu (if_neg hne)
  have hfilter : Finset.univ.filter p = Finset.univ.image q := by
    ext J'
    constructor
    · intro hJ'
      have hp : p J' := (Finset.mem_filter.mp hJ').2
      have heq : q (J' s, J' t) = J' := by
        funext u
        by_cases hus : u = s
        · subst u
          change Function.update (Function.update J s (J' s)) t (J' t) s = J' s
          rw [Function.update_of_ne hst, Function.update_self]
        · by_cases hut : u = t
          · subst u
            change Function.update (Function.update J s (J' s)) t (J' t) t = J' t
            rw [Function.update_self]
          · have hu : u ∈ (Finset.univ.erase s).erase t := by
              simp [hus, hut]
            change Function.update (Function.update J s (J' s)) t (J' t) u = J' u
            rw [Function.update_of_ne hut, Function.update_of_ne hus]
            exact hp u hu
      exact Finset.mem_image.mpr ⟨(J' s, J' t), Finset.mem_univ _, heq⟩
    · intro hJ'
      obtain ⟨kl, -, rfl⟩ := Finset.mem_image.mp hJ'
      apply Finset.mem_filter.mpr
      constructor
      · exact Finset.mem_univ _
      · intro u hu
        have hut : u ≠ t := (Finset.mem_erase.mp hu).1
        have hus : u ≠ s :=
          (Finset.mem_erase.mp (Finset.mem_erase.mp hu).2).1
        change J u = Function.update (Function.update J s kl.1) t kl.2 u
        rw [Function.update_of_ne hut, Function.update_of_ne hus]
  have hq : Function.Injective q := by
    intro kl kl' hkl
    have hs' := congrFun hkl s
    have ht' := congrFun hkl t
    have hk : kl.1 = kl'.1 := by
      simpa only [q, Function.update_of_ne hst, Function.update_self] using hs'
    have hl : kl.2 = kl'.2 := by
      simpa only [q, Function.update_self] using ht'
    exact Prod.ext hk hl
  calc
    ∑ J' : Fin r → Fin n, f J' *
        ∏ u ∈ (Finset.univ.erase s).erase t,
          (if J u = J' u then (1 : ℝ) else 0) =
        ∑ J', if p J' then f J' else 0 := by
      apply Finset.sum_congr rfl
      intro J' _
      rw [hprod]
      by_cases hp : p J' <;> simp [hp]
    _ = ∑ J' ∈ Finset.univ.filter p, f J' := by
      rw [← Finset.sum_filter]
    _ = ∑ J' ∈ Finset.univ.image q, f J' := by
      rw [hfilter]
    _ = ∑ kl : Fin n × Fin n, f (q kl) := by
      rw [Finset.sum_image]
      intro kl _ kl' _ hEq
      exact hq hEq
    _ = ∑ k, ∑ l, f (Function.update (Function.update J s k) t l) := by
      simpa only [q] using
        (Fintype.sum_prod_type
          (fun kl : Fin n × Fin n =>
            f (Function.update (Function.update J s kl.1) t kl.2)))

/-- The entries of `(1 + εH)⁻¹` are differentiable near `ε = 0` with derivative
`−⟪e_i, (1+εH)⁻¹ H (1+εH)⁻¹ e_k⟫`. -/
theorem hasDerivAt_inner_ringInverse_one_add_of_isUnit
    (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (i k : Fin n) {ε : ℝ}
    (hε : IsUnit (1 + ε • H)) :
    HasDerivAt (fun ε : ℝ => ⟪EuclideanSpace.basisFun (Fin n) ℝ i,
        Ring.inverse (1 + ε • H) (EuclideanSpace.basisFun (Fin n) ℝ k)⟫)
      (-⟪EuclideanSpace.basisFun (Fin n) ℝ i,
        Ring.inverse (1 + ε • H) (H (Ring.inverse (1 + ε • H) (EuclideanSpace.basisFun (Fin n) ℝ k)))⟫) ε := by
  exact inverse_entry_at_unit H
    (innerSL ℝ (EuclideanSpace.basisFun (Fin n) ℝ i))
    (EuclideanSpace.basisFun (Fin n) ℝ k) ε hε

/-- The second derivative of the entries of `(1 + εH)⁻¹` at `ε = 0` is `2⟪e_i, H² e_k⟫`. -/
theorem hasDerivAt_deriv_inner_ringInverse_one_add
    (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (i k : Fin n) :
    HasDerivAt (deriv fun ε : ℝ => ⟪EuclideanSpace.basisFun (Fin n) ℝ i,
        Ring.inverse (1 + ε • H) (EuclideanSpace.basisFun (Fin n) ℝ k)⟫)
      (2 * ⟪EuclideanSpace.basisFun (Fin n) ℝ i, H (H (EuclideanSpace.basisFun (Fin n) ℝ k))⟫) 0 := by
  exact inverse_entry_second H
    (innerSL ℝ (EuclideanSpace.basisFun (Fin n) ℝ i))
    (EuclideanSpace.basisFun (Fin n) ℝ k)

set_option maxHeartbeats 800000 in
/-- The second directional derivative is the second derivative along the line. -/
theorem fderiv_fderiv_apply_eq_deriv_deriv_line {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {Φ : W → ℝ} {y : W} (hΦ : ContDiffAt ℝ 2 Φ y) (v : W) :
    fderiv ℝ (fderiv ℝ Φ) y v v = deriv (deriv fun ε : ℝ => Φ (y + ε • v)) 0 := by
  have hc : ContDiffAt ℝ 1 (fderiv ℝ Φ) y :=
    hΦ.fderiv_right (by norm_num)
  have hl (t : ℝ) : HasDerivAt (fun a : ℝ => y + a • v) v t := by
    simpa only [id_eq, one_smul] using
      ((hasDerivAt_id t).smul_const v).const_add y
  have hp :
      HasFDerivAt (fderiv ℝ Φ) (fderiv ℝ (fderiv ℝ Φ) y)
        (y + (0 : ℝ) • v) := by
    simpa only [zero_smul, add_zero] using
      (hc.differentiableAt (by norm_num)).hasFDerivAt
  have hd :
      HasDerivAt (fun t : ℝ => fderiv ℝ Φ (y + t • v))
        (fderiv ℝ (fderiv ℝ Φ) y v) 0 :=
    hp.comp_hasDerivAt 0 (hl 0)
  have hd' :
      deriv (fun t : ℝ => fderiv ℝ Φ (y + t • v) v) 0 =
        fderiv ℝ (fderiv ℝ Φ) y v v := by
    simpa only [map_zero, add_zero] using
      (hd.clm_apply (hasDerivAt_const (0 : ℝ) v)).deriv
  have ht :
      Filter.Tendsto (fun t : ℝ => y + t • v) (nhds 0) (nhds y) := by
    simpa only [ContinuousAt, zero_smul, add_zero] using (hl 0).continuousAt
  have heq :
      (deriv fun t : ℝ => Φ (y + t • v)) =ᶠ[nhds 0]
        (fun t : ℝ => fderiv ℝ Φ (y + t • v) v) := by
    filter_upwards [ht.eventually (hΦ.eventually (by norm_num))] with t h
    exact
      ((h.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt t (hl t)).deriv
  exact hd'.symm.trans heq.deriv_eq.symm

end FunctionalInequalities.Analysis.CoordinateTensor

end S3Bf3B1SecondOrderHelpers
