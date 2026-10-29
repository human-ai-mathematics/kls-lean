import FunctionalInequalities.Analysis.Newtonian.HessianIntegral.NearExponent

/-!
# The near-field Newtonian Hessian integral for `0 < α < 1`

`newtonian_near_integrable_integral_le`: the near-field estimate of Lemma 4.4 of Gilbarg–Trudinger,
*Elliptic Partial Differential Equations of Second Order*, Classics 2001 (ISBN 3-540-41160-7),
pp. 57–59, in the Hölder range `0 < α < 1`: for `n ≥ 2`, `R > 0` and `f` a.e.-measurable on `B_R(x)` with
`|f y - f x| ≤ H ‖y - x‖^α` there, each `D_ijΓ(x - y)(f(y) - f(x))` is integrable on `B_R(x)` with
integral at most `(n / α) H R^α` in absolute value. It is the case `α < 1 ≤ n` of
`newtonian_near_integrable_integral_le_of_exponent_lt_dim`.
-/

noncomputable section

open Metric MeasureTheory

namespace FunctionalInequalities.Analysis

/-- The actual near Newtonian Hessian integral, with the exact GT2001
n/alpha constant. Integrability is derived from local measurability and the
centered Hölder estimate, not postulated for the singular product. -/
theorem newtonian_near_integrable_integral_le {n : ℕ} (hn : 2 ≤ n)
    (x : EuclideanSpace ℝ (Fin n)) {R alpha H : ℝ} (hR : 0 < R)
    (ha : 0 < alpha) (ha1 : alpha < 1) (hH : 0 ≤ H)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hm : AEMeasurable f (volume.restrict (ball x R)))
    (hf : ∀ y ∈ ball x R, |f y-f x| ≤ H*‖y-x‖^alpha) (i j : Fin n) :
    IntegrableOn (fun y => bilinearIteratedFDerivTwo ℝ (newtonianKernel n) (x-y)
      (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)*(f y-f x))
      (ball x R) volume ∧
    |∫ y in ball x R, bilinearIteratedFDerivTwo ℝ (newtonianKernel n) (x-y)
      (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)*(f y-f x)| ≤
      (n:ℝ)*H/alpha*R^alpha := by
  have hn2 : (2:ℝ) ≤ n := by exact_mod_cast hn
  exact newtonian_near_integrable_integral_le_of_exponent_lt_dim hn x hR ha (by linarith) hH f hm hf i j

end FunctionalInequalities.Analysis
