module

public import FunctionalInequalities.Analysis.BakryEmery.Calculus

/-!
# Audit: the nondivergence operator and Letwin (2.3) (rank-zero client)

Source: Letwin, arXiv:2607.24164v1, p. 6, (2.3). Clients of the nondivergence operator
`L_{A,b} f = Σ_ij A_ij ∂_ij f − Σ_i b_i ∂_i f` and its Leibniz rule: in dimension zero the operator
vanishes identically for every coefficient field, drift and function (empty coordinate sums); on a
product of two coordinate functions the Leibniz rule exposes the off-diagonal coefficient entry,
`L_{A,b}(⟪e_i,·⟫⟪e_j,·⟫)(x) = 2 A_ij(x) − b_i(x)⟪e_j,x⟫ − b_j(x)⟪e_i,x⟫`, so a nondiagonal,
nonidentity coefficient field is genuinely consumed.
-/

@[expose] public section

open FunctionalInequalities.Analysis.BakryEmery
open scoped ContDiff RealInnerProductSpace

namespace FunctionalInequalities.Analysis.BakryEmery

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Cross-direction value of `L_{A,b}` on a product of two coordinate functions. -/
theorem nondivergenceOperator_inner_mul_inner
    (A : E → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ)
    (hA : ∀ x i j, A x i j = A x j i) (b : E → Fin (Module.finrank ℝ E) → ℝ)
    (i j : Fin (Module.finrank ℝ E)) (x : E) :
    nondivergenceOperator A b
        (fun y => ⟪stdOrthonormalBasis ℝ E i, y⟫ * ⟪stdOrthonormalBasis ℝ E j, y⟫) x =
      2 * A x i j - b x i * ⟪stdOrthonormalBasis ℝ E j, x⟫ -
        b x j * ⟪stdOrthonormalBasis ℝ E i, x⟫ := by
    have hfi_cont : ContDiff ℝ 2
        (fun y : E => ⟪stdOrthonormalBasis ℝ E i, y⟫) := by
      convert (innerSL ℝ (stdOrthonormalBasis ℝ E i)).contDiff using 1
      funext y
      exact innerSL_apply_apply ℝ (stdOrthonormalBasis ℝ E i) y
    have hgj_cont : ContDiff ℝ 2
        (fun y : E => ⟪stdOrthonormalBasis ℝ E j, y⟫) := by
      convert (innerSL ℝ (stdOrthonormalBasis ℝ E j)).contDiff using 1
      funext y
      exact innerSL_apply_apply ℝ (stdOrthonormalBasis ℝ E j) y
    have hderiv_i (y : E) :
        fderiv ℝ (fun z : E => ⟪stdOrthonormalBasis ℝ E i, z⟫) y =
          innerSL ℝ (stdOrthonormalBasis ℝ E i) := by
      have heq :
          (fun z : E => ⟪stdOrthonormalBasis ℝ E i, z⟫) =
            (innerSL ℝ (stdOrthonormalBasis ℝ E i)) := by
        funext z
        exact innerSL_apply_apply ℝ (stdOrthonormalBasis ℝ E i) z
      rw [heq]
      exact
        ((innerSL ℝ (stdOrthonormalBasis ℝ E i)).hasFDerivAt :
          HasFDerivAt (innerSL ℝ (stdOrthonormalBasis ℝ E i))
            (innerSL ℝ (stdOrthonormalBasis ℝ E i)) y).fderiv
    have hderiv_j (y : E) :
        fderiv ℝ (fun z : E => ⟪stdOrthonormalBasis ℝ E j, z⟫) y =
          innerSL ℝ (stdOrthonormalBasis ℝ E j) := by
      have heq :
          (fun z : E => ⟪stdOrthonormalBasis ℝ E j, z⟫) =
            (innerSL ℝ (stdOrthonormalBasis ℝ E j)) := by
        funext z
        exact innerSL_apply_apply ℝ (stdOrthonormalBasis ℝ E j) z
      rw [heq]
      exact
        ((innerSL ℝ (stdOrthonormalBasis ℝ E j)).hasFDerivAt :
          HasFDerivAt (innerSL ℝ (stdOrthonormalBasis ℝ E j))
            (innerSL ℝ (stdOrthonormalBasis ℝ E j)) y).fderiv
    have hfi :
        ∀ (y : E) (k : Fin (Module.finrank ℝ E)),
          fderiv ℝ (fun z : E => ⟪stdOrthonormalBasis ℝ E i, z⟫) y
              (stdOrthonormalBasis ℝ E k) =
            if k = i then 1 else 0 := by
      intro y k
      rw [hderiv_i y]
      simpa [eq_comm] using
        (stdOrthonormalBasis ℝ E).inner_eq_ite i k
    have hgj :
        ∀ (y : E) (k : Fin (Module.finrank ℝ E)),
          fderiv ℝ (fun z : E => ⟪stdOrthonormalBasis ℝ E j, z⟫) y
              (stdOrthonormalBasis ℝ E k) =
            if k = j then 1 else 0 := by
      intro y k
      rw [hderiv_j y]
      simpa [eq_comm] using
        (stdOrthonormalBasis ℝ E).inner_eq_ite j k
    have hff :
        ∀ (y u v : E),
          bilinearIteratedFDerivTwo ℝ
              (fun z : E => ⟪stdOrthonormalBasis ℝ E i, z⟫) y u v = 0 := by
      intro y u v
      rw [bilinearIteratedFDerivTwo_eq_fderiv_apply hfi_cont]
      have hconst :
          (fun z : E =>
            fderiv ℝ (fun w : E => ⟪stdOrthonormalBasis ℝ E i, w⟫) z v) =
            (fun _ : E => ⟪stdOrthonormalBasis ℝ E i, v⟫) := by
        funext z
        rw [hderiv_i z]
        exact innerSL_apply_apply ℝ (stdOrthonormalBasis ℝ E i) v
      have hz := congrArg (fun q : E → ℝ => fderiv ℝ q y u) hconst
      simpa using hz
    have hgg :
        ∀ (y u v : E),
          bilinearIteratedFDerivTwo ℝ
              (fun z : E => ⟪stdOrthonormalBasis ℝ E j, z⟫) y u v = 0 := by
      intro y u v
      rw [bilinearIteratedFDerivTwo_eq_fderiv_apply hgj_cont]
      have hconst :
          (fun z : E =>
            fderiv ℝ (fun w : E => ⟪stdOrthonormalBasis ℝ E j, w⟫) z v) =
            (fun _ : E => ⟪stdOrthonormalBasis ℝ E j, v⟫) := by
        funext z
        rw [hderiv_j z]
        exact innerSL_apply_apply ℝ (stdOrthonormalBasis ℝ E j) v
      have hz := congrArg (fun q : E → ℝ => fderiv ℝ q y u) hconst
      simpa using hz
    have hLf :
        ∀ y : E,
          nondivergenceOperator A b
              (fun z : E => ⟪stdOrthonormalBasis ℝ E i, z⟫) y = -b y i := by
      intro y
      simp [nondivergenceOperator, hfi, hff, Finset.sum_ite_eq']
    have hLg :
        ∀ y : E,
          nondivergenceOperator A b
              (fun z : E => ⟪stdOrthonormalBasis ℝ E j, z⟫) y = -b y j := by
      intro y
      simp [nondivergenceOperator, hgj, hgg, Finset.sum_ite_eq']
    have hm := nondivergenceOperator_mul A hA b hfi_cont hgj_cont x
    rw [hLf x, hLg x] at hm
    convert hm using 1
    all_goals
      simp [hfi, hgj, Finset.sum_ite_eq']
      ring

end FunctionalInequalities.Analysis.BakryEmery

/-! A concrete two-dimensional coefficient field `[[2,1],[1,3]]` (nonidentity, nondiagonal) with
zero drift: the cross-direction value is the off-diagonal entry times `2`. -/
namespace IndependentNondivergence

abbrev E := EuclideanSpace ℝ (Fin 2)
abbrev I := Fin (Module.finrank ℝ E)
def i0 : I := ⟨0, by simp [E]⟩
def i1 : I := ⟨1, by simp [E]⟩
def A (_ : E) (i j : I) : ℝ :=
  if i.val = 0 ∧ j.val = 0 then 2 else if i.val = 1 ∧ j.val = 1 then 3 else 1
theorem A_symmetric (x : E) (i j : I) : A x i j = A x j i := by
  simp only [A, and_comm]
theorem actual_nonidentity : A 0 i0 i0 = 2 := by norm_num [A, i0]
theorem actual_nondiagonal : A 0 i0 i1 = 1 := by norm_num [A, i0, i1]
theorem actual_cross_value :
    nondivergenceOperator A (fun _ _ => 0)
      (fun y => ⟪stdOrthonormalBasis ℝ E i0, y⟫ * ⟪stdOrthonormalBasis ℝ E i1, y⟫) 0 = 2 := by
  have h := nondivergenceOperator_inner_mul_inner A A_symmetric (fun _ _ => 0) i0 i1 0
  simpa only [actual_nondiagonal, mul_one, zero_mul, sub_zero] using h

end IndependentNondivergence

namespace NondivergenceAudit

abbrev E := EuclideanSpace ℝ (Fin 0)

theorem rank_zero (A : E → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ)
    (b : E → Fin (Module.finrank ℝ E) → ℝ) (f : E → ℝ) (x : E) :
    nondivergenceOperator A b f x = 0 := by
  have h : Module.finrank ℝ E = 0 := by simp
  have : IsEmpty (Fin (Module.finrank ℝ E)) := by rw [h]; infer_instance
  simp [nondivergenceOperator]

end NondivergenceAudit

#print axioms FunctionalInequalities.Analysis.BakryEmery.bilinearIteratedFDerivTwo_mul
#print axioms FunctionalInequalities.Analysis.BakryEmery.nondivergenceOperator_mul
#print axioms FunctionalInequalities.Analysis.BakryEmery.nondivergenceOperator_inner_mul_inner
#print axioms IndependentNondivergence.actual_cross_value
#print axioms NondivergenceAudit.rank_zero
