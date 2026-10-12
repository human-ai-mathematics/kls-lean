import FunctionalInequalities.Probability.Stein.HessianKernel
import FunctionalInequalities.Analysis.Matrix.DeterminantDerivative

/-!
# The Piola identity for Hessian adjugates

`Σⱼ ∂ⱼ adj(∇²u)ᵢⱼ = 0` for `C³` functions `u` (`sum_fderiv_adjugate_hessianMatrix_eq_zero`), in terms of
`Probability.Stein.hessianMatrix`; the smooth input of the weak Piola identity on the moment-map route to Letwin
arXiv:2607.24164v1. Proof body: GPT (Letwin sub-controller task L-T6a); statement by the Letwin sub-controller;
placement: Claude.
-/

noncomputable section

open Matrix
open FunctionalInequalities.Probability.Stein

namespace FunctionalInequalities.Analysis

private lemma det_swap_rows {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (j k : Fin n)
    (a b : Fin n → ℝ) (h : j ≠ k) :
    ((A.updateRow j a).updateRow k b).det =
      -((A.updateRow k a).updateRow j b).det := by
  let M := (A.updateRow k a).updateRow j b
  have hkj : k ≠ j := Ne.symm h
  have he :
      M.submatrix (Equiv.swap j k) id =
        (A.updateRow j a).updateRow k b := by
    ext r l
    by_cases hrj : r = j
    · subst r
      simp [M, Matrix.submatrix_apply, Matrix.updateRow_apply, h, hkj]
    · by_cases hrk : r = k
      · subst r
        simp [M, Matrix.submatrix_apply, Matrix.updateRow_apply]
      · simp [M, Matrix.submatrix_apply, Matrix.updateRow_apply, hrj, hrk,
          Equiv.swap_apply_of_ne_of_ne hrj hrk]
  rw [← he, Matrix.det_permute]
  simp [M, Equiv.Perm.sign_swap h]

private lemma fderiv_apply_clm
    {E G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {f : E → G →L[ℝ] H} {x : E} (hf : DifferentiableAt ℝ f x)
    (v : G) (w : E) :
    fderiv ℝ (fun y => f y v) x w = fderiv ℝ f x w v := by
  have h :=
    congrArg (fun L : E →L[ℝ] H => L w)
      (((ContinuousLinearMap.apply ℝ H v).hasFDerivAt.comp x hf.hasFDerivAt).fderiv)
  change fderiv ℝ (fun y => f y v) x w = fderiv ℝ f x w v at h
  exact h

private lemma fderiv_det_updateRow
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : E → Fin n → Fin n → ℝ) (x : E)
    (hA : ∀ k l, DifferentiableAt ℝ (fun y => A y k l) x)
    (j : Fin n) (c : Fin n → ℝ) (v : E) :
    fderiv ℝ (fun y => (Matrix.updateRow (A y) j c).det) x v =
      ∑ k, if k = j then 0
        else ((Matrix.updateRow (A x) j c).updateRow k
          (fun l => fderiv ℝ (fun y => A y k l) x v)).det := by
  let D : E →L[ℝ] Fin n → Fin n → ℝ :=
    ContinuousLinearMap.pi (fun k =>
      ContinuousLinearMap.pi (fun l =>
        if k = j then (0 : E →L[ℝ] ℝ)
        else fderiv ℝ (fun y => A y k l) x))
  let B : E → Fin n → Fin n → ℝ :=
    fun y k l => if k = j then c l else A y k l
  have hD : HasFDerivAt B D x := by
    apply hasFDerivAt_pi.mpr
    intro k
    apply hasFDerivAt_pi.mpr
    intro l
    by_cases h : k = j
    · simpa only [B, h, ite_true] using (hasFDerivAt_const (c l) x)
    · simpa only [B, h, ite_false] using (hA k l).hasFDerivAt
  have he :
      (fun y => (Matrix.updateRow (A y) j c).det) =
        (fun y => (Matrix.of (B y)).det) := by
    funext y
    congr 1
    ext k l
    exact Matrix.updateRow_apply
  rw [he]
  have hd :=
    congrArg (fun L : E →L[ℝ] ℝ => L v)
      ((differentiableAt_det (Matrix.of (B x))).hasFDerivAt.comp x hD).fderiv
  change
    fderiv ℝ (fun y => (Matrix.of (B y)).det) x v =
      fderiv ℝ (fun M : Fin n → Fin n → ℝ => (Matrix.of M).det)
        (B x) (D v) at hd
  have hdet :=
    fderiv_det_eq_sum_updateRow (Matrix.of (B x)) (Matrix.of (D v))
  change
    fderiv ℝ Matrix.det (Matrix.of (B x)) (Matrix.of (D v)) =
      ∑ k, ((Matrix.of (B x)).updateRow k (Matrix.of (D v) k)).det at hdet
  have hB : Matrix.of (B x) = Matrix.updateRow (Matrix.of (A x)) j c := by
    ext k l
    exact Matrix.updateRow_apply.symm
  calc
    fderiv ℝ (fun y => (Matrix.of (B y)).det) x v =
        fderiv ℝ (fun M : Fin n → Fin n → ℝ => (Matrix.of M).det)
          (B x) (D v) := hd
    _ = ∑ k, ((Matrix.of (B x)).updateRow k (Matrix.of (D v) k)).det := hdet
    _ = ∑ k, if k = j then 0
        else ((Matrix.updateRow (A x) j c).updateRow k
          (fun l => fderiv ℝ (fun y => A y k l) x v)).det := by
      rw [hB]
      apply Finset.sum_congr rfl
      intro k _
      by_cases h : k = j
      · subst k
        rw [if_pos rfl]
        apply Matrix.det_eq_zero_of_row_eq_zero j
        intro l
        rw [Matrix.updateRow_self]
        simp [D]
      · rw [if_neg h]
        have hr :
            (Matrix.of (D v)) k =
              fun l => fderiv ℝ (fun y => A y k l) x v := by
          funext l
          simp only [Matrix.of_apply, D, ContinuousLinearMap.pi_apply, if_neg h]
        rw [hr]
        rfl

/-- **Piola identity for the adjugate of a smooth Hessian** (weak Letwin route, step N10, smooth
case): for a `C³` function `u` on `ℝⁿ`, the rows of the adjugate (cofactor) matrix of the Hessian
`H = ∇²u` are divergence-free: `∑ⱼ ∂ⱼ (adj H)ᵢⱼ = 0`. Here `hessianMatrix u y i j = D²u(y)(eᵢ, eⱼ)`
in the standard basis `eⱼ = EuclideanSpace.basisFun (Fin n) ℝ j`. -/
theorem sum_fderiv_adjugate_hessianMatrix_eq_zero {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ 3 u) (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    ∑ j, fderiv ℝ (fun y => (hessianMatrix u y).adjugate i j) x
      (EuclideanSpace.basisFun (Fin n) ℝ j) = 0 := by
  classical
  let e := EuclideanSpace.basisFun (Fin n) ℝ
  have h₂ : ContDiff ℝ 2 (fderiv ℝ u) :=
    hu.fderiv_right (by norm_num)
  have h₁ : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ u)) :=
    h₂.fderiv_right (by norm_num)
  have hentry :
      ∀ k l, DifferentiableAt ℝ (fun y => hessianMatrix u y k l) x := by
    intro k l
    have hclm :
        ContDiff ℝ 1
          (fun y => ((fderiv ℝ (fderiv ℝ u) y) (e k)) (e l)) :=
      (h₁.clm_apply contDiff_const).clm_apply contDiff_const
    change DifferentiableAt ℝ
      (fun y => ((fderiv ℝ (fderiv ℝ u) y) (e k)) (e l)) x
    exact (hclm.differentiable (by norm_num)).differentiableAt
  have hsym :
      ∀ j k l,
        fderiv ℝ (fun y => hessianMatrix u y k l) x (e j) =
          fderiv ℝ (fun y => hessianMatrix u y j l) x (e k) := by
    intro j k l
    change
      fderiv ℝ (fun y => ((fderiv ℝ (fderiv ℝ u) y) (e k)) (e l)) x (e j) =
        fderiv ℝ (fun y => ((fderiv ℝ (fderiv ℝ u) y) (e j)) (e l)) x (e k)
    have hc :
        DifferentiableAt ℝ (fun y => fderiv ℝ (fderiv ℝ u) y) x :=
      (h₁.differentiable (by norm_num)).differentiableAt
    have hck :
        DifferentiableAt ℝ
          (fun y => (fderiv ℝ (fderiv ℝ u) y) (e k)) x :=
      ((h₁.clm_apply contDiff_const).differentiable (by norm_num)).differentiableAt
    have hcj :
        DifferentiableAt ℝ
          (fun y => (fderiv ℝ (fderiv ℝ u) y) (e j)) x :=
      ((h₁.clm_apply contDiff_const).differentiable (by norm_num)).differentiableAt
    have hleft :=
      fderiv_apply_clm (f := fun y => (fderiv ℝ (fderiv ℝ u) y) (e k))
        hck (e l) (e j)
    have hright :=
      fderiv_apply_clm (f := fun y => (fderiv ℝ (fderiv ℝ u) y) (e j))
        hcj (e l) (e k)
    have hmiddle0 :=
      fderiv_apply_clm (f := fun y => fderiv ℝ (fderiv ℝ u) y)
        hc (e k) (e j)
    have hmiddle :
        (fderiv ℝ (fun y => (fderiv ℝ (fderiv ℝ u) y) (e k)) x (e j)) (e l) =
          ((fderiv ℝ (fun y => fderiv ℝ (fderiv ℝ u) y) x (e j)) (e k)) (e l) :=
      congrArg (fun q : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ => q (e l)) hmiddle0
    have hs :=
      (h₂.contDiffAt (x := x)).isSymmSndFDerivAt
        (by rw [minSmoothness_of_isRCLikeNormedField])
        (e j) (e k)
    have hmiddle' :
        ((fderiv ℝ (fun y => fderiv ℝ (fderiv ℝ u) y) x (e j)) (e k)) (e l) =
          ((fderiv ℝ (fun y => fderiv ℝ (fderiv ℝ u) y) x (e k)) (e j)) (e l) :=
      congrArg (fun q : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ => q (e l)) hs
    have hmiddle'' :=
      congrArg (fun q : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ => q (e l))
        (fderiv_apply_clm (f := fun y => fderiv ℝ (fderiv ℝ u) y)
          hc (e j) (e k))
    calc
      fderiv ℝ (fun y => ((fderiv ℝ (fderiv ℝ u) y) (e k)) (e l)) x (e j) =
          (fderiv ℝ (fun y => (fderiv ℝ (fderiv ℝ u) y) (e k)) x (e j)) (e l) :=
        hleft
      _ = ((fderiv ℝ (fun y => fderiv ℝ (fderiv ℝ u) y) x (e j)) (e k)) (e l) :=
        hmiddle
      _ = ((fderiv ℝ (fun y => fderiv ℝ (fderiv ℝ u) y) x (e k)) (e j)) (e l) :=
        hmiddle'
      _ = (fderiv ℝ (fun y => (fderiv ℝ (fderiv ℝ u) y) (e j)) x (e k)) (e l) :=
        hmiddle''.symm
      _ = fderiv ℝ (fun y => ((fderiv ℝ (fderiv ℝ u) y) (e j)) (e l)) x (e k) :=
        hright.symm
  let C : Fin n → Fin n → ℝ :=
    fun j k =>
      if k = j then 0
      else (((Matrix.of (hessianMatrix u x)).updateRow j (Pi.single i 1)).updateRow k
        (fun l => fderiv ℝ (fun y => hessianMatrix u y k l) x (e j))).det
  have hdiv :
      ∀ j, fderiv ℝ (fun y => (hessianMatrix u y).adjugate i j) x (e j) =
        ∑ k, C j k := by
    intro j
    have heq :
        (fun y => (hessianMatrix u y).adjugate i j) =
          (fun y =>
            ((Matrix.of (hessianMatrix u y)).updateRow j
              (Pi.single i 1)).det) := by
      funext y
      rw [Matrix.adjugate_apply]
      rfl
    rw [heq]
    exact fderiv_det_updateRow
      (fun y => hessianMatrix u y) x hentry j (Pi.single i 1) (e j)
  have hanti : ∀ j k, C j k = -C k j := by
    intro j k
    by_cases h : j = k
    · subst k
      simp only [C, if_pos rfl, neg_zero]
    · have hw :
          (fun l => fderiv ℝ (fun y => hessianMatrix u y k l) x (e j)) =
            (fun l => fderiv ℝ (fun y => hessianMatrix u y j l) x (e k)) := by
        funext l
        exact hsym j k l
      simp only [C, if_neg h, if_neg (Ne.symm h)]
      rw [hw]
      exact det_swap_rows (Matrix.of (hessianMatrix u x)) j k (Pi.single i 1)
        (fun l => fderiv ℝ (fun y => hessianMatrix u y j l) x (e k)) h
  calc
    ∑ j, fderiv ℝ (fun y => (hessianMatrix u y).adjugate i j) x (e j) =
        ∑ j, ∑ k, C j k := by
          apply Finset.sum_congr rfl
          intro j _
          exact hdiv j
    _ = 0 := by
      have hS :
          (∑ j, ∑ k, C j k) = -(∑ j, ∑ k, C j k) := by
        calc
          ∑ j, ∑ k, C j k = ∑ j, ∑ k, -C k j := by
            apply Finset.sum_congr rfl
            intro j _
            apply Finset.sum_congr rfl
            intro k _
            exact hanti j k
          _ = ∑ j, -(∑ k, C k j) := by
            apply Finset.sum_congr rfl
            intro j _
            exact Finset.sum_neg_distrib _
          _ = -(∑ j, ∑ k, C k j) := by
            rw [Finset.sum_neg_distrib]
          _ = -(∑ j, ∑ k, C j k) := by
            congr 1
            exact Finset.sum_comm
      linarith

end FunctionalInequalities.Analysis
