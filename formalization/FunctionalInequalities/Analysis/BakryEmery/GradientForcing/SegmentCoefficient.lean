import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Module

/-!
# Segment mean coefficients for a `C¹` function on Euclidean space

Supporting the linearization of the lower-order term in Gilbarg–Trudinger, *Elliptic Partial
Differential Equations of Second Order*, Classics 2001 (ISBN 3-540-41160-7), Lemma 17.16,
pp. 463–464, as used with the interior Schauder estimate, Theorem 6.2, pp. 90–92.

For `W : ℝⁿ → ℝ` and endpoints `p, p'`, `segmentMeanCoefficient W p p' i` is the explicit integral
`∫₀¹ ∂ᵢW((1 - θ) p + θ p') dθ` of the coordinate Fréchet derivative along the segment, and
`segmentForcingCoefficient W G d x i` is the same integral at the endpoint pair `G x, G (x + d)`
of a field `G`.

* `fderiv_basisFun_eq_gradient`: coordinate Fréchet derivatives are gradient coordinates;
* `intervalIntegrable_segmentMeanCoefficient`: for `C¹` `W` the integrand is interval integrable;
* `sub_eq_sum_segmentMeanCoefficient`: the fundamental theorem of calculus on the segment,
  `W p' - W p = Σᵢ bᵢ (p'ᵢ - pᵢ)`, with these same coefficients.

Only `C¹` regularity of `W` is used; no Schauder estimate or higher regularity of any potential is
assumed or concluded.
-/
noncomputable section
namespace FunctionalInequalities.Analysis
open Set MeasureTheory
open scoped BigOperators ContDiff
variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

/-- The mean of the coordinate derivative `∂ᵢW` along the segment from `p` to `p'`. -/
def segmentMeanCoefficient (W : E → ℝ) (p p' : E) (i : ι) : ℝ :=
  ∫ θ in (0 : ℝ)..1,
    fderiv ℝ W ((1-θ) • p+θ • p') (EuclideanSpace.basisFun ι ℝ i)

/-- The segment mean coefficient at the endpoint pair `G x, G (x + d)` of one field `G`. -/
def segmentForcingCoefficient (W : E → ℝ) (G : E → E) (d x : E) (i : ι) : ℝ :=
  segmentMeanCoefficient W (G x) (G (x+d)) i

/-- Coordinate Fréchet derivatives are gradient coordinates. -/
theorem fderiv_basisFun_eq_gradient (f : E → ℝ) (x : E) (i : ι) :
    fderiv ℝ f x (EuclideanSpace.basisFun ι ℝ i) = gradient f x i := by
  rw [← inner_gradient_left, EuclideanSpace.inner_basisFun_real]

/-- For `C¹` `W`, the integrand of every segment mean coefficient is interval integrable. -/
theorem intervalIntegrable_segmentMeanCoefficient {W : E → ℝ}
    (hW : ContDiff ℝ 1 W) (p p' : E) (i : ι) :
    IntervalIntegrable (fun θ : ℝ => fderiv ℝ W ((1-θ) • p+θ • p')
      (EuclideanSpace.basisFun ι ℝ i)) volume 0 1 := by
  have hD : Continuous (fderiv ℝ W) := hW.continuous_fderiv (by norm_num)
  have hc : Continuous (fun θ : ℝ => fderiv ℝ W ((1-θ) • p+θ • p')
      (EuclideanSpace.basisFun ι ℝ i)) := by fun_prop
  exact hc.intervalIntegrable 0 1

private theorem apply_eq_sum (L : E →L[ℝ] ℝ) (z : E) :
    L z = ∑ i, L (EuclideanSpace.basisFun ι ℝ i) * z i := by
  have hs : (∑ i, z i • EuclideanSpace.basisFun ι ℝ i) = z :=
    by simpa only [EuclideanSpace.basisFun_inner] using
      (EuclideanSpace.basisFun ι ℝ).sum_repr' z
  calc
    L z = L (∑ i, z i • EuclideanSpace.basisFun ι ℝ i) := congrArg L hs.symm
    _ = ∑ i, L (z i • EuclideanSpace.basisFun ι ℝ i) := map_sum L _ _
    _ = ∑ i, L (EuclideanSpace.basisFun ι ℝ i) * z i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [map_smul,smul_eq_mul,mul_comm]

/-- Fundamental theorem of calculus on the segment from `p` to `p'`, written with the segment mean
coefficients: `W p' - W p = Σᵢ bᵢ (p'ᵢ - pᵢ)`. -/
theorem sub_eq_sum_segmentMeanCoefficient {W : E → ℝ}
    (hW : ContDiff ℝ 1 W) (p p' : E) :
    W p'-W p = ∑ i, segmentMeanCoefficient W p p' i * (p' i-p i) := by
  have hs (θ : ℝ) : p+θ • (p'-p) = (1-θ) • p+θ • p' := by module
  have hp (θ : ℝ) : HasDerivAt (fun t : ℝ => p+t • (p'-p)) (p'-p) θ := by
    exact HasDerivAt.const_add p (by
      simpa only [one_smul, id_eq] using (hasDerivAt_id θ).smul_const (p'-p))
  have hd (θ : ℝ) : HasDerivAt (fun t : ℝ => W (p+t • (p'-p)))
      (fderiv ℝ W (p+θ • (p'-p)) (p'-p)) θ :=
    ((hW.differentiable (by norm_num) _).hasFDerivAt).comp_hasDerivAt θ (hp θ)
  have hD : Continuous (fderiv ℝ W) := hW.continuous_fderiv (by norm_num)
  have hc : Continuous (fun θ : ℝ => fderiv ℝ W (p+θ • (p'-p)) (p'-p)) := by fun_prop
  have ht := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun θ _ => hd θ) (hc.intervalIntegrable 0 1)
  have hleft : p+(1 : ℝ) • (p'-p) = p' := by module
  have he : W p'-W p = ∫ θ in (0 : ℝ)..1,
      fderiv ℝ W ((1-θ) • p+θ • p') (p'-p) := by
    simpa only [zero_smul,add_zero,hleft,hs] using ht.symm
  rw [he]
  have hdecomp : (fun θ : ℝ => fderiv ℝ W ((1-θ) • p+θ • p') (p'-p)) =
      (fun θ : ℝ => ∑ i, fderiv ℝ W ((1-θ) • p+θ • p')
        (EuclideanSpace.basisFun ι ℝ i) * (p' i-p i)) := by
    funext θ
    exact apply_eq_sum _ _
  rw [hdecomp]
  rw [intervalIntegral.integral_finsetSum (s := Finset.univ)
    (f := fun i θ => fderiv ℝ W ((1-θ) • p+θ • p')
      (EuclideanSpace.basisFun ι ℝ i) * (p' i-p i))
    (fun i _ => (intervalIntegrable_segmentMeanCoefficient hW p p' i).mul_const _)]
  apply Finset.sum_congr rfl
  intro i _
  exact intervalIntegral.integral_mul_const _ _

end FunctionalInequalities.Analysis
