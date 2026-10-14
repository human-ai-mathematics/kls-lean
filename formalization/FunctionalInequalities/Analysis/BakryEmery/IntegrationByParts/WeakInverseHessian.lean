import FunctionalInequalities.Analysis.Matrix.Piola
import FunctionalInequalities.Probability.Diffusion.Cutoff
import FunctionalInequalities.Probability.Stein.HessianKernel
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Real.Star

/-!
# Weak inverse-Hessian generator identities

The two weak integration-by-parts identities for the inverse-Hessian generator
`L f = tr((∇²u)⁻¹ ∇²f) − DV(∇u)(∇f)` of a `C^{1,1}` Monge–Ampère solution `u`
(`det ∇²u = e^{−u + V(∇u)}` almost everywhere, the exponent Lipschitz), tested against `C²` compactly supported
functions with the weight `e^{−u}` (Letwin arXiv:2607.24164v1, equation (2.2), weak `C^{1,1}` counterpart):

* `integral_mul_generator_eq_neg_energy`, `integral_mul_generator_eq_neg_energy'`.

The proof applies the weak inverse-Hessian divergence identity and the inverse-Hessian integrability interface of
`Analysis/Matrix/Piola.lean` to weighted gradient tests. Its one-use supports are private: the Lipschitz constant and
compact support of the test `η e^{−u} ∂ᵢw`, its almost-everywhere derivative (with two coordinate lemmas reproduced
privately from `Probability/Stein/HessianKernel.lean`, which requires only differentiability of the gradient at the
point), the almost-everywhere chain derivative of the Monge–Ampère exponent `−u + V(∇u)`, and a finite inverse-matrix
cancellation. No `C²` regularity of `u` or `w` is used. These are supporting identities; Letwin Theorems 2.5 and 1.2
are not proved here.
-/

noncomputable section

section WeightedGradientTest

open scoped RealInnerProductSpace ContDiff

namespace FunctionalInequalities.Analysis

/-- Compactly supported weighted derivative test for the weak Letwin generator identity.
No global bound on the gradient of w is assumed. -/
private theorem exists_lipschitz_compact_exp_gradient_test {n : ℕ}
    {u w η : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ 1 u) (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η)
    {Gw : NNReal} (hGw : LipschitzWith Gw (gradient w)) (i : Fin n) :
    ∃ L : NNReal,
      LipschitzWith L (fun x => η x * Real.exp (-u x) *
        fderiv ℝ w x (EuclideanSpace.basisFun (Fin n) ℝ i)) ∧
      HasCompactSupport (fun x => η x * Real.exp (-u x) *
        fderiv ℝ w x (EuclideanSpace.basisFun (Fin n) ℝ i)) := by
  let γ : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun x => η x * Real.exp (-u x)
  have hγ : ContDiff ℝ 1 γ := hη.mul hu.neg.exp
  have hγc : HasCompactSupport γ := hηc.mul_right
  obtain ⟨Kγ, hKγ⟩ :=
    ContDiff.lipschitzWith_of_hasCompactSupport hγc hγ one_ne_zero
  let e : EuclideanSpace ℝ (Fin n) :=
    EuclideanSpace.basisFun (Fin n) ℝ i
  have hcoord :
      LipschitzWith (‖(innerSL ℝ) e‖₊ * Gw)
        (fun x => fderiv ℝ w x e) := by
    simpa [Function.comp_def, inner_gradient_left] using
      (((innerSL ℝ) e).lipschitz.comp hGw)
  obtain ⟨⟨L, hL⟩, _⟩ :=
    FunctionalInequalities.Probability.Diffusion.exists_lipschitzWith_smul_of_locallyLipschitz
      hKγ hγc hcoord.locallyLipschitz
  refine ⟨L, ?_, ?_⟩
  · simpa only [smul_eq_mul] using hL
  · exact hγc.mul_right

end FunctionalInequalities.Analysis

end WeightedGradientTest

section WeightedGradientTestDerivative

open MeasureTheory
open FunctionalInequalities.Probability.Stein
open scoped RealInnerProductSpace ContDiff

namespace FunctionalInequalities.Analysis

private lemma differentiableAt_fderiv_of_differentiableAt_gradient
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {u : E → ℝ} {x : E} (hx : DifferentiableAt ℝ (gradient u) x) :
    DifferentiableAt ℝ (fderiv ℝ u) x := by
  have heq :
      fderiv ℝ u = (InnerProductSpace.toDual ℝ E) ∘ gradient u := by
    funext y
    simp [gradient]
  rw [heq]
  exact
    (InnerProductSpace.toDual ℝ E).toContinuousLinearEquiv.differentiableAt.comp x hx

private lemma hessian_coord_of_gradient_diff
    {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    {i j : Fin n} (hx : DifferentiableAt ℝ (gradient u) x) :
    fderiv ℝ (fun y => fderiv ℝ u y (EuclideanSpace.basisFun (Fin n) ℝ j)) x
        (EuclideanSpace.basisFun (Fin n) ℝ i) =
      hessianMatrix u x i j := by
  have hfd : DifferentiableAt ℝ (fderiv ℝ u) x :=
    differentiableAt_fderiv_of_differentiableAt_gradient hx
  have hc :
      DifferentiableAt ℝ
        (fun _ : EuclideanSpace ℝ (Fin n) =>
          EuclideanSpace.basisFun (Fin n) ℝ j) x :=
    (differentiable_const (EuclideanSpace.basisFun (Fin n) ℝ j) :
      Differentiable ℝ
        (fun _ : EuclideanSpace ℝ (Fin n) =>
          EuclideanSpace.basisFun (Fin n) ℝ j)).differentiableAt
  have h := fderiv_clm_apply hfd hc
  have h' := congrArg
    (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ =>
      L (EuclideanSpace.basisFun (Fin n) ℝ i)) h
  simpa [hessianMatrix, bilinearIteratedFDerivTwo] using h'

/-- Almost-everywhere derivative of the actual weighted gradient test for Letwin (2.2).
Only C1 u and eta and a Lipschitz gradient of w are needed. -/
private theorem ae_fderiv_exp_gradient_test {n : ℕ}
    {u w η : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ 1 u) (hη : ContDiff ℝ 1 η)
    {Gw : NNReal} (hGw : LipschitzWith Gw (gradient w)) (i : Fin n) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), ∀ j : Fin n,
      fderiv ℝ (fun y => η y * Real.exp (-u y) *
        fderiv ℝ w y (EuclideanSpace.basisFun (Fin n) ℝ i)) x
          (EuclideanSpace.basisFun (Fin n) ℝ j) =
        Real.exp (-u x) *
          (fderiv ℝ η x (EuclideanSpace.basisFun (Fin n) ℝ j) *
              fderiv ℝ w x (EuclideanSpace.basisFun (Fin n) ℝ i) -
            η x * fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ j) *
              fderiv ℝ w x (EuclideanSpace.basisFun (Fin n) ℝ i) +
            η x * hessianMatrix w x j i) := by
  filter_upwards [hGw.ae_differentiableAt
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))] with x hx
  have hux : DifferentiableAt ℝ u x :=
    (hu.differentiable one_ne_zero).differentiableAt
  have hηx : DifferentiableAt ℝ η x :=
    (hη.differentiable one_ne_zero).differentiableAt
  have hfd : DifferentiableAt ℝ (fderiv ℝ w) x :=
    differentiableAt_fderiv_of_differentiableAt_gradient hx
  have hc :
      DifferentiableAt ℝ
        (fun _ : EuclideanSpace ℝ (Fin n) =>
          EuclideanSpace.basisFun (Fin n) ℝ i) x :=
    (differentiable_const (EuclideanSpace.basisFun (Fin n) ℝ i) :
      Differentiable ℝ
        (fun _ : EuclideanSpace ℝ (Fin n) =>
          EuclideanSpace.basisFun (Fin n) ℝ i)).differentiableAt
  have hcomponent :
      DifferentiableAt ℝ
        (fun y => fderiv ℝ w y (EuclideanSpace.basisFun (Fin n) ℝ i)) x :=
    hfd.clm_apply hc
  have he :
      fderiv ℝ (fun y => η y * Real.exp (-u y) *
        fderiv ℝ w y (EuclideanSpace.basisFun (Fin n) ℝ i)) x =
      (η x * Real.exp (-u x)) •
          fderiv ℝ
            (fun y => fderiv ℝ w y (EuclideanSpace.basisFun (Fin n) ℝ i)) x +
        fderiv ℝ w x (EuclideanSpace.basisFun (Fin n) ℝ i) •
          (η x • (Real.exp (-u x) • (-fderiv ℝ u x)) +
            Real.exp (-u x) • fderiv ℝ η x) :=
    ((hηx.hasFDerivAt.mul hux.hasFDerivAt.neg.exp).mul
      hcomponent.hasFDerivAt).fderiv
  intro j
  rw [he]
  simp only [_root_.add_apply, _root_.smul_apply, _root_.neg_apply, smul_eq_mul]
  rw [hessian_coord_of_gradient_diff (i := j) (j := i) hx]
  ring

end FunctionalInequalities.Analysis

end WeightedGradientTestDerivative

section MongeAmpereExponentDerivative

open MeasureTheory
open FunctionalInequalities.Probability.Stein
open scoped RealInnerProductSpace ContDiff

namespace FunctionalInequalities.Analysis

private lemma gradient_fderiv_coordinate {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanSpace ℝ (Fin n)}
    (hu : ContDiff ℝ 1 u) (hx : DifferentiableAt ℝ (gradient u) x)
    (j k : Fin n) :
    fderiv ℝ (gradient u) x (EuclideanSpace.basisFun (Fin n) ℝ j) k =
      hessianMatrix u x j k := by
  have hm :
      LinearMap.toMatrix
          (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
          (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
          (fderiv ℝ (gradient u) x).toLinearMap =
        hessianMatrix u x := by
    rw [← hessianMatrix_toEuclideanLin_of_differentiableAt_gradient hu hx,
      Matrix.toEuclideanLin_eq_toLin_orthonormal,
      LinearMap.toMatrix_toLin]
  have hentry :
      fderiv ℝ (gradient u) x (EuclideanSpace.basisFun (Fin n) ℝ j) k =
        hessianMatrix u x k j := by
    have he := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M k j) hm
    simp only [LinearMap.toMatrix_apply,
      OrthonormalBasis.coe_toBasis_repr_apply,
      EuclideanSpace.basisFun_repr, OrthonormalBasis.coe_toBasis] at he
    exact he
  calc
    fderiv ℝ (gradient u) x (EuclideanSpace.basisFun (Fin n) ℝ j) k =
        hessianMatrix u x k j := hentry
    _ = hessianMatrix u x j k := by
      simpa only [star_trivial] using
        (hessianMatrix_isHermitian_of_differentiableAt_gradient hu hx).apply j k

/-- AE coordinate chain derivative of the Monge-Ampere right-hand exponent
for Letwin (2.2), with C1 u and Lipschitz gradient, without a C2 premise. -/
private theorem ae_fderiv_mongeAmpere_exponent {n : ℕ}
    {u V : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ 1 u) {G : NNReal} (hG : LipschitzWith G (gradient u))
    (hV : ContDiff ℝ 1 V) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), ∀ j : Fin n,
      fderiv ℝ (fun y => -u y + V (gradient u y)) x
          (EuclideanSpace.basisFun (Fin n) ℝ j) =
        -fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ j) +
          ∑ k, hessianMatrix u x j k *
            fderiv ℝ V (gradient u x) (EuclideanSpace.basisFun (Fin n) ℝ k) := by
  filter_upwards [hG.ae_differentiableAt (μ := volume)] with x hx
  intro j
  have hux : DifferentiableAt ℝ u x := hu.differentiable one_ne_zero x
  have hVx : DifferentiableAt ℝ V (gradient u x) :=
    hV.differentiable one_ne_zero (gradient u x)
  have hexp :
      HasFDerivAt (fun y => -u y + V (gradient u y))
        (-fderiv ℝ u x +
          (fderiv ℝ V (gradient u x)).comp (fderiv ℝ (gradient u) x)) x :=
    hux.hasFDerivAt.neg.add (hVx.hasFDerivAt.comp x hx.hasFDerivAt)
  have heval :
      fderiv ℝ (fun y => -u y + V (gradient u y)) x
          (EuclideanSpace.basisFun (Fin n) ℝ j) =
        -fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ j) +
          fderiv ℝ V (gradient u x)
            (fderiv ℝ (gradient u) x (EuclideanSpace.basisFun (Fin n) ℝ j)) := by
    exact congrArg
      (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ =>
        L (EuclideanSpace.basisFun (Fin n) ℝ j))
      hexp.fderiv
  have hchain :
      fderiv ℝ V (gradient u x)
          (fderiv ℝ (gradient u) x (EuclideanSpace.basisFun (Fin n) ℝ j)) =
        ∑ k, hessianMatrix u x j k *
          fderiv ℝ V (gradient u x) (EuclideanSpace.basisFun (Fin n) ℝ k) := by
    calc
      fderiv ℝ V (gradient u x)
          (fderiv ℝ (gradient u) x (EuclideanSpace.basisFun (Fin n) ℝ j)) =
          ⟪gradient V (gradient u x),
            fderiv ℝ (gradient u) x (EuclideanSpace.basisFun (Fin n) ℝ j)⟫ :=
        inner_gradient_left.symm
      _ = ∑ k, ⟪gradient V (gradient u x) k,
          fderiv ℝ (gradient u) x (EuclideanSpace.basisFun (Fin n) ℝ j) k⟫ :=
        PiLp.inner_apply _ _
      _ = ∑ k, hessianMatrix u x j k *
          fderiv ℝ V (gradient u x) (EuclideanSpace.basisFun (Fin n) ℝ k) := by
        apply Finset.sum_congr rfl
        intro k _
        have hVk :
            fderiv ℝ V (gradient u x) (EuclideanSpace.basisFun (Fin n) ℝ k) =
              gradient V (gradient u x) k := by
          calc
            fderiv ℝ V (gradient u x) (EuclideanSpace.basisFun (Fin n) ℝ k) =
                ⟪gradient V (gradient u x),
                  EuclideanSpace.basisFun (Fin n) ℝ k⟫ :=
              inner_gradient_left.symm
            _ = gradient V (gradient u x) k :=
              EuclideanSpace.inner_basisFun_real
                (Fin n) (gradient V (gradient u x)) k
        calc
          ⟪gradient V (gradient u x) k,
              fderiv ℝ (gradient u) x (EuclideanSpace.basisFun (Fin n) ℝ j) k⟫ =
              gradient V (gradient u x) k *
                fderiv ℝ (gradient u) x (EuclideanSpace.basisFun (Fin n) ℝ j) k :=
            Real.inner_apply _ _
          _ = gradient V (gradient u x) k * hessianMatrix u x j k :=
            congrArg (fun t : ℝ => gradient V (gradient u x) k * t)
              (gradient_fderiv_coordinate hu hx j k)
          _ = hessianMatrix u x j k * gradient V (gradient u x) k :=
            mul_comm _ _
          _ = hessianMatrix u x j k *
              fderiv ℝ V (gradient u x) (EuclideanSpace.basisFun (Fin n) ℝ k) :=
            congrArg (fun t : ℝ => hessianMatrix u x j k * t) hVk.symm
  exact heval.trans
    (congrArg
      (fun t : ℝ => -fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ j) + t)
      hchain)

end FunctionalInequalities.Analysis

end MongeAmpereExponentDerivative

section InverseMatrixCancellation

open scoped BigOperators

namespace FunctionalInequalities.Analysis

/-- Finite inverse-Hessian cancellation for the weak Letwin (2.2) test.
All analytic data are replaced by arbitrary finite matrices and coordinate vectors. -/
private theorem sum_inv_gradient_test_sub_chain_eq {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) (hdet : IsUnit A.det)
    (a : ℝ) (b p q r : Fin n → ℝ) :
    (∑ i, ∑ j, A⁻¹ i j * (b j * r i - a * p j * r i + a * B j i)) -
      (∑ i, ∑ j, A⁻¹ i j * (-p j + ∑ k, A j k * q k) * (a * r i)) =
      (∑ i, ∑ j, A⁻¹ i j * b i * r j) +
        a * ((A⁻¹ * B).trace - ∑ i, q i * r i) := by
  have hsymm (i j : Fin n) : A⁻¹ i j = A⁻¹ j i := by
    simpa only [star_trivial] using hA.inv.apply j i
  have hcancel (i : Fin n) :
      (∑ j, A⁻¹ i j * (∑ k, A j k * q k)) = q i := by
    calc
      (∑ j, A⁻¹ i j * (∑ k, A j k * q k)) =
          ∑ k, (∑ j, A⁻¹ i j * A j k) * q k := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro k _
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = q i := by
        simp only [← Matrix.mul_apply, Matrix.nonsing_inv_mul A hdet]
        simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul]
        simp
  have henergy :
      (∑ i, ∑ j, A⁻¹ i j * b j * r i) =
        ∑ i, ∑ j, A⁻¹ i j * b i * r j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hsymm j i]
  have htrace :
      (A⁻¹ * B).trace = ∑ i, ∑ j, A⁻¹ i j * B j i := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  calc
    (∑ i, ∑ j, A⁻¹ i j * (b j * r i - a * p j * r i + a * B j i)) -
        (∑ i, ∑ j, A⁻¹ i j * (-p j + ∑ k, A j k * q k) * (a * r i)) =
        ∑ i, ∑ j,
          (A⁻¹ i j * b j * r i + a * (A⁻¹ i j * B j i) -
            a * (A⁻¹ i j * (∑ k, A j k * q k) * r i)) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = (∑ i, ∑ j, A⁻¹ i j * b j * r i) +
          a * (∑ i, ∑ j, A⁻¹ i j * B j i) -
          a * (∑ i, q i * r i) := by
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.sum_mul, hcancel]
    _ = (∑ i, ∑ j, A⁻¹ i j * b i * r j) +
          a * ((A⁻¹ * B).trace - ∑ i, q i * r i) := by
      rw [henergy, ← htrace]
      ring

end FunctionalInequalities.Analysis

end InverseMatrixCancellation

section GeneratorIdentities

open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace
open FunctionalInequalities.Probability.Stein

namespace FunctionalInequalities.Analysis

private abbrev coord {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (i : Fin n) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  fderiv ℝ f x (EuclideanSpace.basisFun (Fin n) ℝ i)

private def weightedTest {n : ℕ}
    (u a f : EuclideanSpace ℝ (Fin n) → ℝ) (i : Fin n)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  a x * Real.exp (-u x) * coord f i x

private def energyDensity {n : ℕ}
    (u a f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (∑ i, ∑ j, (hessianMatrix u x)⁻¹ i j * coord a i x * coord f j x) *
    Real.exp (-u x)

private def generatorDensity {n : ℕ}
    (u V a f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  a x * (((hessianMatrix u x)⁻¹ * hessianMatrix f x).trace -
    fderiv ℝ V (gradient u x) (gradient f x)) * Real.exp (-u x)

private lemma coord_eq_gradient {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (i : Fin n)
    (x : EuclideanSpace ℝ (Fin n)) :
    coord f i x = gradient f x i := by
  calc
    coord f i x =
        ⟪gradient f x, EuclideanSpace.basisFun (Fin n) ℝ i⟫ :=
      inner_gradient_left.symm
    _ = gradient f x i :=
      EuclideanSpace.inner_basisFun_real (Fin n) (gradient f x) i

private lemma drift_eq_sum {n : ℕ}
    (u V f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ V (gradient u x) (gradient f x) =
      ∑ i, coord V i (gradient u x) * coord f i x := by
  calc
    fderiv ℝ V (gradient u x) (gradient f x) =
        ⟪gradient V (gradient u x), gradient f x⟫ :=
      inner_gradient_left.symm
    _ = ∑ i, ⟪gradient V (gradient u x) i, gradient f x i⟫ :=
      PiLp.inner_apply _ _
    _ = ∑ i, coord V i (gradient u x) * coord f i x := by
      simp only [Real.inner_apply, coord_eq_gradient]

private lemma measurable_coord {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (i : Fin n) :
    Measurable (coord f i) :=
  (ContinuousLinearMap.apply ℝ ℝ
    (EuclideanSpace.basisFun (Fin n) ℝ i)).measurable.comp
      (measurable_fderiv ℝ f)

private lemma coord_bound {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {L : NNReal}
    (hf : LipschitzWith L f) (i : Fin n)
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖coord f i x‖ ≤ (L : ℝ) * ‖EuclideanSpace.basisFun (Fin n) ℝ i‖ :=
  ((fderiv ℝ f x).le_opNorm
    (EuclideanSpace.basisFun (Fin n) ℝ i)).trans
      (mul_le_mul_of_nonneg_right
        (norm_fderiv_le_of_lipschitz ℝ hf)
        (norm_nonneg (EuclideanSpace.basisFun (Fin n) ℝ i)))

private lemma continuous_coord {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ContDiff ℝ 1 f) (i : Fin n) :
    Continuous (coord f i) :=
  (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const

private lemma continuous_coord_of_lipschitz_gradient {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {L : NNReal}
    (hf : LipschitzWith L (gradient f)) (i : Fin n) :
    Continuous (coord f i) := by
  change Continuous
    (fun x => fderiv ℝ f x (EuclideanSpace.basisFun (Fin n) ℝ i))
  simpa [Function.comp_def, inner_gradient_left] using
    ((((innerSL ℝ) (EuclideanSpace.basisFun (Fin n) ℝ i)).lipschitz.comp
      hf).continuous)

private lemma integrable_inv_test_derivative {n : ℕ}
    {u F ψ : EuclideanSpace ℝ (Fin n) → ℝ}
    {G L : NNReal} (hG : LipschitzWith G (gradient u))
    (hF : Continuous F)
    (hdet : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (hessianMatrix u x).det = Real.exp (F x))
    (hψ : LipschitzWith L ψ) (hψc : HasCompactSupport ψ)
    (i j : Fin n) :
    Integrable (fun x => (hessianMatrix u x)⁻¹ i j * coord ψ j x)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  exact integrable_inv_hessianMatrix_mul_of_bounded_compact hG hF hdet
    (measurable_coord ψ j)
    (hψc.fderiv_apply ℝ (EuclideanSpace.basisFun (Fin n) ℝ j))
    (coord_bound hψ j) i j

private lemma integrable_inv_chain_test {n : ℕ}
    {u F ψ : EuclideanSpace ℝ (Fin n) → ℝ}
    {G LF L : NNReal} (hG : LipschitzWith G (gradient u))
    (hF : LipschitzWith LF F)
    (hdet : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (hessianMatrix u x).det = Real.exp (F x))
    (hψ : LipschitzWith L ψ) (hψc : HasCompactSupport ψ)
    (i j : Fin n) :
    Integrable
      (fun x => (hessianMatrix u x)⁻¹ i j * coord F j x * ψ x)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  obtain ⟨C, hC⟩ := hψc.exists_bound_of_continuous hψ.continuous
  have hb (x : EuclideanSpace ℝ (Fin n)) :
      ‖coord F j x * ψ x‖ ≤
        ((LF : ℝ) * ‖EuclideanSpace.basisFun (Fin n) ℝ j‖) * C := by
    rw [norm_mul]
    exact mul_le_mul (coord_bound hF j x) (hC x) (norm_nonneg _)
      (mul_nonneg LF.coe_nonneg (norm_nonneg _))
  have hi :=
    integrable_inv_hessianMatrix_mul_of_bounded_compact hG hF.continuous hdet
      ((measurable_coord F j).mul hψ.continuous.measurable)
      (hψc.mul_left :
        HasCompactSupport (fun x => coord F j x * ψ x))
      hb i j
  change Integrable
    (fun x => (hessianMatrix u x)⁻¹ i j * (coord F j x * ψ x))
    (volume : Measure (EuclideanSpace ℝ (Fin n))) at hi
  simpa only [mul_assoc] using hi

private lemma integrable_energy {n : ℕ}
    {u F a f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ 1 u) {G : NNReal}
    (hG : LipschitzWith G (gradient u)) (hF : Continuous F)
    (hdet : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (hessianMatrix u x).det = Real.exp (F x))
    (ha : ∀ i, Continuous (coord a i))
    (hf : ∀ j, Continuous (coord f j))
    (hc : ∀ i j, HasCompactSupport
      (fun x => coord a i x * coord f j x * Real.exp (-u x))) :
    Integrable (energyDensity u a f)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  classical
  have hi (i j : Fin n) :
      Integrable
        (fun x => (hessianMatrix u x)⁻¹ i j *
          (coord a i x * coord f j x * Real.exp (-u x)))
        (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    have hcont : Continuous
        (fun x => coord a i x * coord f j x * Real.exp (-u x)) :=
      ((ha i).mul (hf j)).mul
        (Real.continuous_exp.comp hu.continuous.neg)
    obtain ⟨C, hC⟩ := (hc i j).exists_bound_of_continuous hcont
    exact integrable_inv_hessianMatrix_mul_of_bounded_compact
      hG hF hdet hcont.measurable (hc i j) hC i j
  have hs := integrable_finsetSum Finset.univ
    (fun i _ => integrable_finsetSum Finset.univ (fun j _ => hi i j))
  have he :
      (fun x => ∑ i, ∑ j, (hessianMatrix u x)⁻¹ i j *
        (coord a i x * coord f j x * Real.exp (-u x))) =
        energyDensity u a f := by
    funext x
    simp only [energyDensity, Finset.sum_mul, mul_assoc]
  rw [he] at hs
  exact hs

private lemma smooth_test_derivative {n : ℕ}
    {u a f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ 1 u) (ha : ContDiff ℝ 1 a)
    (hf : ContDiff ℝ 2 f) (i j : Fin n)
    (x : EuclideanSpace ℝ (Fin n)) :
    coord (weightedTest u a f i) j x =
      Real.exp (-u x) *
        (coord a j x * coord f i x -
          a x * coord u j x * coord f i x +
          a x * hessianMatrix f x j i) := by
  have hfd : ContDiff ℝ 1 (fderiv ℝ f) :=
    hf.fderiv_right (by norm_num)
  have hfdx := (hfd.differentiable one_ne_zero).differentiableAt (x := x)
  have hc :
      DifferentiableAt ℝ
        (fun _ : EuclideanSpace ℝ (Fin n) =>
          EuclideanSpace.basisFun (Fin n) ℝ i) x :=
    (differentiable_const (EuclideanSpace.basisFun (Fin n) ℝ i) :
      Differentiable ℝ
        (fun _ : EuclideanSpace ℝ (Fin n) =>
          EuclideanSpace.basisFun (Fin n) ℝ i)).differentiableAt
  have hcomponent : DifferentiableAt ℝ (coord f i) x :=
    hfdx.clm_apply hc
  have hcoord :
      coord (coord f i) j x = hessianMatrix f x j i := by
    have he := congrArg
      (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ =>
        L (EuclideanSpace.basisFun (Fin n) ℝ j))
      (fderiv_clm_apply hfdx hc)
    change
      fderiv ℝ
        (fun y => fderiv ℝ f y (EuclideanSpace.basisFun (Fin n) ℝ i)) x
        (EuclideanSpace.basisFun (Fin n) ℝ j) =
          hessianMatrix f x j i
    simpa [hessianMatrix, bilinearIteratedFDerivTwo] using he
  have hux : DifferentiableAt ℝ u x :=
    hu.differentiable one_ne_zero x
  have hax : DifferentiableAt ℝ a x :=
    ha.differentiable one_ne_zero x
  have he :
      fderiv ℝ (weightedTest u a f i) x =
        (a x * Real.exp (-u x)) • fderiv ℝ (coord f i) x +
          coord f i x •
            (a x • (Real.exp (-u x) • (-fderiv ℝ u x)) +
              Real.exp (-u x) • fderiv ℝ a x) :=
    ((hax.hasFDerivAt.mul hux.hasFDerivAt.neg.exp).mul
      hcomponent.hasFDerivAt).fderiv
  change fderiv ℝ (weightedTest u a f i) x
    (EuclideanSpace.basisFun (Fin n) ℝ j) = _
  rw [he]
  simp only [_root_.add_apply, _root_.smul_apply, _root_.neg_apply, smul_eq_mul]
  change
    (a x * Real.exp (-u x)) * coord (coord f i) j x +
      coord f i x *
        (a x * (Real.exp (-u x) * (-coord u j x)) +
          Real.exp (-u x) * coord a j x) = _
  rw [hcoord]
  ring

private lemma assemble_generator {n : ℕ}
    {u V a f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ 1 u) {G : NNReal}
    (hG : LipschitzWith G (gradient u)) (hV : ContDiff ℝ 1 V)
    {LF : NNReal} (hF : LipschitzWith LF (fun x => -u x + V (gradient u x)))
    (hdet : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (hessianMatrix u x).det = Real.exp (-u x + V (gradient u x)))
    (ht : ∀ i, ∃ L : NNReal,
      LipschitzWith L (weightedTest u a f i) ∧
        HasCompactSupport (weightedTest u a f i))
    (hd : ∀ i, ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), ∀ j,
      coord (weightedTest u a f i) j x =
        Real.exp (-u x) *
          (coord a j x * coord f i x -
            a x * coord u j x * coord f i x +
            a x * hessianMatrix f x j i))
    (hE : Integrable (energyDensity u a f)
      (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    (∫ x, generatorDensity u V a f x
      ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        -∫ x, energyDensity u a f x
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  classical
  let F : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun x => -u x + V (gradient u x)
  let P (i j : Fin n) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
    (hessianMatrix u x)⁻¹ i j * coord (weightedTest u a f i) j x
  let Q (i j : Fin n) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
    (hessianMatrix u x)⁻¹ i j * coord F j x * weightedTest u a f i x
  let S (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
    ∑ i, ∑ j, (P i j x - Q i j x)
  have hP (i j : Fin n) :
      Integrable (P i j) (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    obtain ⟨L, hL, hc⟩ := ht i
    exact integrable_inv_test_derivative hG hF.continuous hdet hL hc i j
  have hQ (i j : Fin n) :
      Integrable (Q i j) (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    obtain ⟨L, hL, hc⟩ := ht i
    exact integrable_inv_chain_test hG hF hdet hL hc i j
  have hrowInt (i : Fin n) :
      Integrable (fun x => ∑ j, (P i j x - Q i j x))
        (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    integrable_finsetSum Finset.univ (fun j _ => (hP i j).sub (hQ i j))
  have hS : Integrable S (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    integrable_finsetSum Finset.univ (fun i _ => hrowInt i)
  have hrow (i : Fin n) :
      (∫ x, ∑ j, (P i j x - Q i j x)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 0 := by
    rw [integral_finsetSum Finset.univ
      (f := fun j x => P i j x - Q i j x)
      (fun j _ => (hP i j).sub (hQ i j))]
    have hs (j : Fin n) :
        (∫ x, P i j x - Q i j x
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
            (∫ x, P i j x) - ∫ x, Q i j x :=
      integral_sub (hP i j) (hQ i j)
    simp only [hs, Finset.sum_sub_distrib]
    apply sub_eq_zero.mpr
    obtain ⟨L, hL, hc⟩ := ht i
    exact sum_integral_inv_hessianMatrix_mul_fderiv_eq hu hG hF hdet hL hc i
  have hz : (∫ x, S x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 0 := by
    change (∫ x, ∑ i, ∑ j, (P i j x - Q i j x)) = 0
    rw [integral_finsetSum Finset.univ
      (f := fun i x => ∑ j, (P i j x - Q i j x))
      (fun i _ => hrowInt i)]
    simp only [hrow, Finset.sum_const_zero]
  have hdall :
      ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), ∀ i j,
        coord (weightedTest u a f i) j x =
          Real.exp (-u x) *
            (coord a j x * coord f i x -
              a x * coord u j x * coord f i x +
              a x * hessianMatrix f x j i) :=
    ae_all_iff.mpr hd
  have heq :
      S =ᵐ[volume] (fun x => energyDensity u a f x + generatorDensity u V a f x) := by
    filter_upwards [hdall, ae_fderiv_mongeAmpere_exponent hu hG hV,
      hG.ae_differentiableAt
        (μ := (volume : Measure (EuclideanSpace ℝ (Fin n)))),
      hdet] with x hxD hxF hxG hxdet
    have hA := hessianMatrix_isHermitian_of_differentiableAt_gradient hu hxG
    have hunit : IsUnit (hessianMatrix u x).det := by
      rw [hxdet]
      exact isUnit_iff_ne_zero.mpr (Real.exp_ne_zero _)
    have hc := sum_inv_gradient_test_sub_chain_eq
      (hessianMatrix u x) (hessianMatrix f x) hA hunit
      (a x) (fun i => coord a i x) (fun i => coord u i x)
      (fun i => coord V i (gradient u x)) (fun i => coord f i x)
    calc
      S x =
          Real.exp (-u x) *
            ((∑ i, ∑ j, (hessianMatrix u x)⁻¹ i j *
                (coord a j x * coord f i x -
                  a x * coord u j x * coord f i x +
                  a x * hessianMatrix f x j i)) -
              (∑ i, ∑ j, (hessianMatrix u x)⁻¹ i j *
                (-coord u j x +
                  ∑ k, hessianMatrix u x j k * coord V k (gradient u x)) *
                (a x * coord f i x))) := by
        dsimp only [S]
        rw [mul_sub]
        simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        dsimp only [P, Q]
        rw [hxD i j]
        have hj :
            coord F j x =
              -coord u j x +
                ∑ k, hessianMatrix u x j k * coord V k (gradient u x) :=
          hxF j
        rw [hj]
        dsimp only [weightedTest]
        ring
      _ = energyDensity u a f x + generatorDensity u V a f x := by
        rw [hc]
        dsimp only [energyDensity, generatorDensity]
        rw [drift_eq_sum u V f x]
        ring
  have hcombined :
      Integrable (fun x => energyDensity u a f x + generatorDensity u V a f x)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    hS.congr heq
  have hgen : Integrable (generatorDensity u V a f)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    have hi := hcombined.sub hE
    change Integrable
      (fun x => (energyDensity u a f x + generatorDensity u V a f x) -
        energyDensity u a f x)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) at hi
    simpa only [add_sub_cancel_left] using hi
  have hsum :
      (∫ x, energyDensity u a f x
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) +
        (∫ x, generatorDensity u V a f x
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) = 0 := by
    rw [← integral_add hE hgen, ← integral_congr_ae heq]
    exact hz
  linarith

private lemma energy_swap {n : ℕ}
    {u a f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ 1 u) {G : NNReal}
    (hG : LipschitzWith G (gradient u)) :
    energyDensity u a f =ᵐ[volume] energyDensity u f a := by
  classical
  filter_upwards [hG.ae_differentiableAt
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))] with x hx
  have hA := (hessianMatrix_isHermitian_of_differentiableAt_gradient hu hx).inv
  have hs (i j : Fin n) :
      (hessianMatrix u x)⁻¹ j i = (hessianMatrix u x)⁻¹ i j := by
    simpa only [star_trivial] using hA.apply i j
  unfold energyDensity
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hs i j]
  ring

/-- **The Hessian-metric generator at `C^{1,1}` is symmetric** (Letwin arXiv:2607.24164v1 (2.2), weak form; weak Letwin
route, N10, task N10b): for the `C^{1,1}` Monge–Ampère solution `u` (`det ∇²u = e^{−u + V(∇u)}` a.e., the right side
Lipschitz), with `L f := tr((∇²u)⁻¹ ∇²f) − DV(∇u)(∇f)`, every `w ∈ C¹` with Lipschitz gradient and every `η ∈ C²` with compact
support satisfy `∫ η (L w) e^{−u} = −∫ ⟨(∇²u)⁻¹ ∇η, ∇w⟩ e^{−u}`. -/
theorem integral_mul_generator_eq_neg_energy {n : ℕ} {u V w η : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ 1 u) {G : NNReal} (hG : LipschitzWith G (gradient u)) (hV : ContDiff ℝ 1 V)
    {LF : NNReal} (hF : LipschitzWith LF (fun x => -u x + V (gradient u x)))
    (hdet : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (hessianMatrix u x).det = Real.exp (-u x + V (gradient u x)))
    (hw : ContDiff ℝ 1 w) {Gw : NNReal} (hGw : LipschitzWith Gw (gradient w))
    (hη : ContDiff ℝ 2 η) (hηc : HasCompactSupport η) :
    ∫ x, η x * (((hessianMatrix u x)⁻¹ * hessianMatrix w x).trace -
        fderiv ℝ V (gradient u x) (gradient w x)) * Real.exp (-u x)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) =
      -∫ x, (∑ i, ∑ j, (hessianMatrix u x)⁻¹ i j *
          fderiv ℝ η x (EuclideanSpace.basisFun (Fin n) ℝ i) *
          fderiv ℝ w x (EuclideanSpace.basisFun (Fin n) ℝ j)) * Real.exp (-u x)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  have hη1 : ContDiff ℝ 1 η := hη.of_le (by norm_num)
  have hE : Integrable (energyDensity u η w)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    apply integrable_energy hu hG hF.continuous hdet
      (continuous_coord hη1) (continuous_coord hw)
    intro i j
    exact
      ((hηc.fderiv_apply ℝ (EuclideanSpace.basisFun (Fin n) ℝ i)).mul_right :
        HasCompactSupport (fun x => coord η i x * coord w j x)).mul_right
  exact assemble_generator hu hG hV hF hdet
    (fun i => exists_lipschitz_compact_exp_gradient_test hu hη1 hηc hGw i)
    (fun i => ae_fderiv_exp_gradient_test hu hη1 hGw i) hE

/-- The same identity with the roles exchanged (`η` inside the generator, `w` outside). -/
theorem integral_mul_generator_eq_neg_energy' {n : ℕ} {u V w η : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ 1 u) {G : NNReal} (hG : LipschitzWith G (gradient u)) (hV : ContDiff ℝ 1 V)
    {LF : NNReal} (hF : LipschitzWith LF (fun x => -u x + V (gradient u x)))
    (hdet : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (hessianMatrix u x).det = Real.exp (-u x + V (gradient u x)))
    (hw : ContDiff ℝ 1 w) {Gw : NNReal} (hGw : LipschitzWith Gw (gradient w))
    (hη : ContDiff ℝ 2 η) (hηc : HasCompactSupport η) :
    ∫ x, w x * (((hessianMatrix u x)⁻¹ * hessianMatrix η x).trace -
        fderiv ℝ V (gradient u x) (gradient η x)) * Real.exp (-u x)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) =
      -∫ x, (∑ i, ∑ j, (hessianMatrix u x)⁻¹ i j *
          fderiv ℝ η x (EuclideanSpace.basisFun (Fin n) ℝ i) *
          fderiv ℝ w x (EuclideanSpace.basisFun (Fin n) ℝ j)) * Real.exp (-u x)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  have hη1 : ContDiff ℝ 1 η := hη.of_le (by norm_num)
  have hηfd : ContDiff ℝ 1 (fderiv ℝ η) :=
    hη.fderiv_right (by norm_num)
  have ht (i : Fin n) :
      ∃ L : NNReal, LipschitzWith L (weightedTest u w η i) ∧
        HasCompactSupport (weightedTest u w η i) := by
    have hc : HasCompactSupport (weightedTest u w η i) :=
      (hηc.fderiv_apply ℝ (EuclideanSpace.basisFun (Fin n) ℝ i)).mul_left
    have hd : ContDiff ℝ 1 (weightedTest u w η i) :=
      (hw.mul hu.neg.exp).mul (hηfd.clm_apply contDiff_const)
    obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hc hd one_ne_zero
    exact ⟨L, hL, hc⟩
  have hd (i : Fin n) :
      ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), ∀ j,
        coord (weightedTest u w η i) j x =
          Real.exp (-u x) *
            (coord w j x * coord η i x -
              w x * coord u j x * coord η i x +
              w x * hessianMatrix η x j i) :=
    Eventually.of_forall (fun x j => smooth_test_derivative hu hw hη i j x)
  have hE : Integrable (energyDensity u w η)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    apply integrable_energy hu hG hF.continuous hdet
      (continuous_coord_of_lipschitz_gradient hGw) (continuous_coord hη1)
    intro i j
    exact
      ((hηc.fderiv_apply ℝ (EuclideanSpace.basisFun (Fin n) ℝ j)).mul_left :
        HasCompactSupport (fun x => coord w i x * coord η j x)).mul_right
  change (∫ x, generatorDensity u V w η x) =
    -∫ x, energyDensity u η w x
  calc
    (∫ x, generatorDensity u V w η x) =
        -∫ x, energyDensity u w η x :=
      assemble_generator hu hG hV hF hdet ht hd hE
    _ = -∫ x, energyDensity u η w x := by
      rw [integral_congr_ae (energy_swap (a := w) (f := η) hu hG)]

end FunctionalInequalities.Analysis

end GeneratorIdentities

section GeneratorIntegrability

open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace
open FunctionalInequalities.Probability.Stein

namespace FunctionalInequalities.Analysis

private lemma weak_generator_compact_hessian_entry {n : ℕ}
    {η : EuclideanSpace ℝ (Fin n) → ℝ}
    (hηc : HasCompactSupport η) (i j : Fin n) :
    HasCompactSupport (fun x => hessianMatrix η x i j) := by
  change HasCompactSupport
    ((fun A : EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ =>
      A (EuclideanSpace.basisFun (Fin n) ℝ i)
        (EuclideanSpace.basisFun (Fin n) ℝ j)) ∘
      fderiv ℝ (fderiv ℝ η))
  exact ((hηc.fderiv (𝕜 := ℝ)).fderiv (𝕜 := ℝ)).comp_left (by simp)

private lemma weak_generator_compact_apply {n : ℕ}
    {g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (A : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (hgc : HasCompactSupport g) :
    HasCompactSupport (fun x => A x (g x)) := by
  apply hgc.mono'
  intro x hx
  by_contra hn
  have hz : g x = 0 := image_eq_zero_of_notMem_tsupport hn
  apply hx
  change A x (g x) = 0
  rw [hz, map_zero]

/-- Genuine integrability for the weak inverse-Hessian generator, its exchanged
test density and the absolute RHS of the original N11b energy estimate. -/
theorem integrable_weak_generator_densities {n : ℕ}
    {u V w η : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : Continuous u) {G : NNReal} (hG : LipschitzWith G (gradient u))
    (hV : ContDiff ℝ 1 V)
    (hF : Continuous (fun x => -u x + V (gradient u x)))
    (hdet : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (hessianMatrix u x).det = Real.exp (-u x + V (gradient u x)))
    (hw : Continuous w) {Gw : NNReal} (hGw : LipschitzWith Gw (gradient w))
    (hη : ContDiff ℝ 2 η) (hηc : HasCompactSupport η) :
    Integrable (fun x => η x *
      (((hessianMatrix u x)⁻¹ * hessianMatrix w x).trace -
        fderiv ℝ V (gradient u x) (gradient w x)) * Real.exp (-u x))
      (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
    Integrable (fun x => w x *
      (((hessianMatrix u x)⁻¹ * hessianMatrix η x).trace -
        fderiv ℝ V (gradient u x) (gradient η x)) * Real.exp (-u x))
      (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
    Integrable (fun x =>
      |η x + (((hessianMatrix u x)⁻¹ * hessianMatrix η x).trace -
        fderiv ℝ V (gradient u x) (gradient η x))| * Real.exp (-u x))
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  classical
  have he : Continuous (fun x => Real.exp (-u x)) :=
    Real.continuous_exp.comp hu.neg
  have hDV : Continuous (fun x => fderiv ℝ V (gradient u x)) :=
    (hV.continuous_fderiv one_ne_zero).comp hG.continuous
  have hgradη : Continuous (gradient η) :=
    BakryEmery.continuous_gradient (hη.of_le (by norm_num))

  have htrace :
      ∀ {f a : EuclideanSpace ℝ (Fin n) → ℝ},
        (∀ i j, Integrable
          (fun x => (hessianMatrix u x)⁻¹ i j *
            (a x * hessianMatrix f x j i))
          (volume : Measure (EuclideanSpace ℝ (Fin n)))) →
        Integrable
          (fun x => a x * ((hessianMatrix u x)⁻¹ * hessianMatrix f x).trace)
          (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    intro f a hi
    have hs := integrable_finsetSum Finset.univ
      (fun i _ => integrable_finsetSum Finset.univ (fun j _ => hi i j))
    apply hs.congr
    filter_upwards [] with x
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring

  have hηe : Continuous (fun x => η x * Real.exp (-u x)) :=
    hη.continuous.mul he
  have hηec : HasCompactSupport (fun x => η x * Real.exp (-u x)) :=
    hηc.mul_right
  obtain ⟨B, hB⟩ := hηec.exists_bound_of_continuous hηe
  have hwt : Integrable
      (fun x => (η x * Real.exp (-u x)) *
        ((hessianMatrix u x)⁻¹ * hessianMatrix w x).trace)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    apply htrace
    intro i j
    apply integrable_inv_hessianMatrix_mul_of_bounded_compact hG hF hdet
      (hηe.measurable.mul (measurable_hessianMatrix_entry w j i))
      hηec.mul_right (C := B * (Gw : ℝ)) ?_ i j
    intro x
    change ‖(η x * Real.exp (-u x)) * hessianMatrix w x j i‖ ≤ B * (Gw : ℝ)
    rw [norm_mul]
    exact mul_le_mul (hB x)
      (norm_hessianMatrix_entry_le_of_lipschitz_gradient hGw x j i)
      (norm_nonneg _) (le_trans (norm_nonneg _) (hB x))
  have hwd : Integrable
      (fun x => η x * fderiv ℝ V (gradient u x) (gradient w x) *
        Real.exp (-u x))
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    ((hη.continuous.mul (hDV.clm_apply hGw.continuous)).mul he).integrable_of_hasCompactSupport
      (hηc.mul_right.mul_right)
  have hfirst : Integrable
      (fun x => η x *
        (((hessianMatrix u x)⁻¹ * hessianMatrix w x).trace -
          fderiv ℝ V (gradient u x) (gradient w x)) * Real.exp (-u x))
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    apply (hwt.sub hwd).congr
    filter_upwards [] with x
    change
      (η x * Real.exp (-u x)) *
          ((hessianMatrix u x)⁻¹ * hessianMatrix w x).trace -
        η x * fderiv ℝ V (gradient u x) (gradient w x) * Real.exp (-u x) =
      η x * (((hessianMatrix u x)⁻¹ * hessianMatrix w x).trace -
        fderiv ℝ V (gradient u x) (gradient w x)) * Real.exp (-u x)
    ring

  have hηdc : HasCompactSupport
      (fun x => fderiv ℝ V (gradient u x) (gradient η x)) :=
    weak_generator_compact_apply (fun x => fderiv ℝ V (gradient u x))
      (BakryEmery.hasCompactSupport_gradient hηc)
  have hprimed :
      ∀ {a : EuclideanSpace ℝ (Fin n) → ℝ}, Continuous a →
        Integrable
          (fun x => a x *
            (((hessianMatrix u x)⁻¹ * hessianMatrix η x).trace -
              fderiv ℝ V (gradient u x) (gradient η x)) * Real.exp (-u x))
          (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    intro a ha
    have hat : Integrable
        (fun x => (a x * Real.exp (-u x)) *
          ((hessianMatrix u x)⁻¹ * hessianMatrix η x).trace)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
      apply htrace
      intro i j
      have hc : Continuous
          (fun x => (a x * Real.exp (-u x)) * hessianMatrix η x j i) :=
        (ha.mul he).mul (hessian_entry_continuous hη j i)
      have hcc : HasCompactSupport
          (fun x => (a x * Real.exp (-u x)) * hessianMatrix η x j i) :=
        (weak_generator_compact_hessian_entry hηc j i).mul_left
      obtain ⟨C, hC⟩ := hcc.exists_bound_of_continuous hc
      exact integrable_inv_hessianMatrix_mul_of_bounded_compact
        hG hF hdet hc.measurable hcc hC i j
    have had : Integrable
        (fun x => a x * fderiv ℝ V (gradient u x) (gradient η x) *
          Real.exp (-u x))
        (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
      ((ha.mul (hDV.clm_apply hgradη)).mul he).integrable_of_hasCompactSupport
        (hηdc.mul_left.mul_right)
    apply (hat.sub had).congr
    filter_upwards [] with x
    change
      (a x * Real.exp (-u x)) *
          ((hessianMatrix u x)⁻¹ * hessianMatrix η x).trace -
        a x * fderiv ℝ V (gradient u x) (gradient η x) * Real.exp (-u x) =
      a x * (((hessianMatrix u x)⁻¹ * hessianMatrix η x).trace -
        fderiv ℝ V (gradient u x) (gradient η x)) * Real.exp (-u x)
    ring

  refine ⟨hfirst, hprimed hw, ?_⟩
  have hLη : Integrable
      (fun x => (((hessianMatrix u x)⁻¹ * hessianMatrix η x).trace -
        fderiv ℝ V (gradient u x) (gradient η x)) * Real.exp (-u x))
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    simpa only [one_mul] using
      (hprimed (a := fun _ => (1 : ℝ)) continuous_const)
  have hsum : Integrable
      (fun x => (η x +
        (((hessianMatrix u x)⁻¹ * hessianMatrix η x).trace -
          fderiv ℝ V (gradient u x) (gradient η x))) * Real.exp (-u x))
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    apply ((hηe.integrable_of_hasCompactSupport hηec).add hLη).congr
    filter_upwards [] with x
    exact (add_mul _ _ _).symm
  simpa only [abs_mul, Real.abs_exp] using hsum.abs

end FunctionalInequalities.Analysis

end GeneratorIntegrability
