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
