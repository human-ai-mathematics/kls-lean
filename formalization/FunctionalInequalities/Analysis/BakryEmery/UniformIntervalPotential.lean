import FunctionalInequalities.Analysis.BakryEmery.MongeAmpere
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Convex.Deriv

/-!
# The uniform-interval moment potential

The explicit potential `φ(y) = 2 log cosh(√3 y / 2) + log(4 / √3)` on `ℝ`, whose gradient
`∇φ(y) = √3 tanh(√3 y / 2)` takes values in `K = (−√3, √3)`. (Only this range inclusion is proved here, not that the
gradient pushes `e^{−φ}` forward to the uniform law on `K`.) It is the source potential of the
uniform-interval client of Letwin's moment-measure Lemmas A.4 and A.5 (arXiv:2607.24164v1).

Facts about the potential:

* `uniformInterval_momentPotential_gradient`: the gradient formula;
* `uniformInterval_momentPotential_contDiff_convexOn`: smoothness and convexity;
* `uniformInterval_momentPotential_bilinearIteratedFDerivTwo`: the Hessian `3 / (2 cosh²(√3 x / 2))`;
* `uniformInterval_momentPotential_logDetHessian`: the Monge–Ampère equation with `V ≡ log(2√3)`;
* `uniformInterval_momentPotential_integral_exp_neg`: the normalization `∫ e^{−φ} = 1`;
* `uniformInterval_momentPotential_source_hypotheses`: the combined source-class package.

The nonconstant test function for the Lemma A.5 client, `f = tanh²(√3 y / 2)`:

* `uniformInterval_tanhSq_nonconstant_facts`: `f` is smooth and bounded by `1`, `L f = 1 − 3 tanh²(√3 y / 2)`,
  `L f + 2 f ≥ 0` and `f 0 ≠ f 1`, where `L` is `hessianInverseOperator` for this potential and `V`.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory
open scoped ContDiff

namespace FunctionalInequalities.Analysis.BakryEmery

/-- The gradient of the moment potential: `∇φ(y) = √3 tanh(√3 y / 2)`. -/
theorem uniformInterval_momentPotential_gradient :
    ∀ y : ℝ, gradient (fun y : ℝ => 2 * Real.log (Real.cosh (Real.sqrt 3 * y / 2)) + Real.log (4 / Real.sqrt 3)) y = Real.sqrt 3 * Real.tanh (Real.sqrt 3 * y / 2) := by
    intro y
    rw [gradient_eq_deriv']
    have harg :
        HasDerivAt (fun x : ℝ => Real.sqrt 3 * x / 2) (Real.sqrt 3 / 2) y := by
      simpa using
        (HasDerivAt.div_const
          (HasDerivAt.const_mul (Real.sqrt 3) (hasDerivAt_id y)) 2)
    have hcosh :
        HasDerivAt
          (fun x : ℝ => Real.cosh (Real.sqrt 3 * x / 2))
          (Real.sinh (Real.sqrt 3 * y / 2) * (Real.sqrt 3 / 2)) y := by
      simpa only [Function.comp_def] using
        (Real.hasDerivAt_cosh (Real.sqrt 3 * y / 2)).comp y harg
    have hne : Real.cosh (Real.sqrt 3 * y / 2) ≠ 0 :=
      ne_of_gt (Real.cosh_pos (Real.sqrt 3 * y / 2))
    have hlog :
        HasDerivAt
          (fun x : ℝ => Real.log (Real.cosh (Real.sqrt 3 * x / 2)))
          ((Real.sinh (Real.sqrt 3 * y / 2) * (Real.sqrt 3 / 2)) /
            Real.cosh (Real.sqrt 3 * y / 2)) y := by
      exact HasDerivAt.log hcosh hne
    have hscaled :
        HasDerivAt
          (fun x : ℝ => 2 * Real.log (Real.cosh (Real.sqrt 3 * x / 2)))
          (2 * ((Real.sinh (Real.sqrt 3 * y / 2) * (Real.sqrt 3 / 2)) /
            Real.cosh (Real.sqrt 3 * y / 2))) y := by
      simpa using (HasDerivAt.const_mul 2 hlog)
    have hfull :
        HasDerivAt
          (fun x : ℝ =>
            2 * Real.log (Real.cosh (Real.sqrt 3 * x / 2)) +
              Real.log (4 / Real.sqrt 3))
          (2 * ((Real.sinh (Real.sqrt 3 * y / 2) * (Real.sqrt 3 / 2)) /
            Real.cosh (Real.sqrt 3 * y / 2))) y := by
      simpa using
        (HasDerivAt.add_const (Real.log (4 / Real.sqrt 3)) hscaled)
    rw [HasDerivAt.deriv hfull]
    rw [Real.tanh_eq_sinh_div_cosh]
    field_simp [hne]


/-- The moment potential is `C^∞` and convex on `ℝ`. -/
theorem uniformInterval_momentPotential_contDiff_convexOn :
    ContDiff ℝ ∞ (fun y : ℝ => 2 * Real.log (Real.cosh (Real.sqrt 3 * y / 2)) + Real.log (4 / Real.sqrt 3)) ∧ ConvexOn ℝ Set.univ (fun y : ℝ => 2 * Real.log (Real.cosh (Real.sqrt 3 * y / 2)) + Real.log (4 / Real.sqrt 3)) := by
    have hmul :
        ContDiff ℝ ∞ (fun x : ℝ => Real.sqrt 3 * x) := by
      simpa using
        (ContDiff.mul
          (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => Real.sqrt 3))
          (contDiff_id : ContDiff ℝ ∞ (fun x : ℝ => x)))
    have harg :
        ContDiff ℝ ∞ (fun x : ℝ => Real.sqrt 3 * x / 2) := by
      simpa using (ContDiff.div_const hmul 2)
    have hcosh :
        ContDiff ℝ ∞
          (fun x : ℝ => Real.cosh (Real.sqrt 3 * x / 2)) := by
      simpa only [Function.comp_def] using
        (Real.contDiff_cosh.comp harg)
    have hlog :
        ContDiff ℝ ∞
          (fun x : ℝ => Real.log (Real.cosh (Real.sqrt 3 * x / 2))) := by
      exact
        ContDiff.log hcosh
          (fun x => ne_of_gt (Real.cosh_pos (Real.sqrt 3 * x / 2)))
    have hscaled :
        ContDiff ℝ ∞
          (fun x : ℝ => 2 * Real.log (Real.cosh (Real.sqrt 3 * x / 2))) := by
      simpa using
        (ContDiff.mul
          (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => (2 : ℝ)))
          hlog)
    have hphi :
        ContDiff ℝ ∞
          (fun y : ℝ =>
            2 * Real.log (Real.cosh (Real.sqrt 3 * y / 2)) +
              Real.log (4 / Real.sqrt 3)) := by
      simpa using
        (ContDiff.add hscaled
          (contDiff_const :
            ContDiff ℝ ∞ (fun _ : ℝ => Real.log (4 / Real.sqrt 3))))

    have hgAt (x : ℝ) :
        HasDerivAt
          (fun z : ℝ => Real.sqrt 3 * Real.tanh (Real.sqrt 3 * z / 2))
          (Real.sqrt 3 *
            ((Real.cosh (Real.sqrt 3 * x / 2) * (Real.sqrt 3 / 2) *
                Real.cosh (Real.sqrt 3 * x / 2) -
              Real.sinh (Real.sqrt 3 * x / 2) *
                (Real.sinh (Real.sqrt 3 * x / 2) * (Real.sqrt 3 / 2))) /
              Real.cosh (Real.sqrt 3 * x / 2) ^ 2)) x := by
      have hargAt :
          HasDerivAt
            (fun z : ℝ => Real.sqrt 3 * z / 2)
            (Real.sqrt 3 / 2) x := by
        simpa using
          (HasDerivAt.div_const
            (HasDerivAt.const_mul (Real.sqrt 3) (hasDerivAt_id x)) 2)
      have hsinh :
          HasDerivAt
            (fun z : ℝ => Real.sinh (Real.sqrt 3 * z / 2))
            (Real.cosh (Real.sqrt 3 * x / 2) * (Real.sqrt 3 / 2)) x := by
        simpa only [Function.comp_def] using
          (Real.hasDerivAt_sinh (Real.sqrt 3 * x / 2)).comp x hargAt
      have hcoshAt :
          HasDerivAt
            (fun z : ℝ => Real.cosh (Real.sqrt 3 * z / 2))
            (Real.sinh (Real.sqrt 3 * x / 2) * (Real.sqrt 3 / 2)) x := by
        simpa only [Function.comp_def] using
          (Real.hasDerivAt_cosh (Real.sqrt 3 * x / 2)).comp x hargAt
      have hne : Real.cosh (Real.sqrt 3 * x / 2) ≠ 0 :=
        ne_of_gt (Real.cosh_pos (Real.sqrt 3 * x / 2))
      simpa only [Function.comp_def, Pi.div_apply, Real.tanh_eq_sinh_div_cosh] using
        (HasDerivAt.const_mul (Real.sqrt 3)
          (HasDerivAt.div hsinh hcoshAt hne))

    have hgdiff :
        Differentiable ℝ
          (fun x : ℝ => Real.sqrt 3 * Real.tanh (Real.sqrt 3 * x / 2)) := by
      intro x
      exact (hgAt x).differentiableAt

    have hgnonneg :
        ∀ x : ℝ,
          0 ≤ deriv
            (fun x : ℝ => Real.sqrt 3 * Real.tanh (Real.sqrt 3 * x / 2)) x := by
      intro x
      have hquot :
          ((Real.cosh (Real.sqrt 3 * x / 2) * (Real.sqrt 3 / 2) *
                Real.cosh (Real.sqrt 3 * x / 2) -
              Real.sinh (Real.sqrt 3 * x / 2) *
                (Real.sinh (Real.sqrt 3 * x / 2) * (Real.sqrt 3 / 2))) /
              Real.cosh (Real.sqrt 3 * x / 2) ^ 2) =
            (Real.sqrt 3 / 2) / Real.cosh (Real.sqrt 3 * x / 2) ^ 2 := by
        calc
          ((Real.cosh (Real.sqrt 3 * x / 2) * (Real.sqrt 3 / 2) *
                Real.cosh (Real.sqrt 3 * x / 2) -
              Real.sinh (Real.sqrt 3 * x / 2) *
                (Real.sinh (Real.sqrt 3 * x / 2) * (Real.sqrt 3 / 2))) /
              Real.cosh (Real.sqrt 3 * x / 2) ^ 2) =
              ((Real.sqrt 3 / 2) *
                (Real.cosh (Real.sqrt 3 * x / 2) ^ 2 -
                  Real.sinh (Real.sqrt 3 * x / 2) ^ 2)) /
                Real.cosh (Real.sqrt 3 * x / 2) ^ 2 := by
                  ring
          _ = (Real.sqrt 3 / 2) / Real.cosh (Real.sqrt 3 * x / 2) ^ 2 := by
            simp [Real.cosh_sq_sub_sinh_sq]
      have hcpos : 0 < Real.cosh (Real.sqrt 3 * x / 2) :=
        Real.cosh_pos _
      have hsqrt : 0 ≤ Real.sqrt (3 : ℝ) :=
        Real.sqrt_nonneg _
      rw [HasDerivAt.deriv (hgAt x), hquot]
      positivity

    have hgmono :
        Monotone
          (fun x : ℝ => Real.sqrt 3 * Real.tanh (Real.sqrt 3 * x / 2)) :=
      monotone_of_deriv_nonneg hgdiff hgnonneg

    have hfdiff :
        Differentiable ℝ
          (fun y : ℝ =>
            2 * Real.log (Real.cosh (Real.sqrt 3 * y / 2)) +
              Real.log (4 / Real.sqrt 3)) :=
      hphi.differentiable (by simp)

    have hderiv (x : ℝ) :
        deriv
            (fun y : ℝ =>
              2 * Real.log (Real.cosh (Real.sqrt 3 * y / 2)) +
                Real.log (4 / Real.sqrt 3)) x =
          Real.sqrt 3 * Real.tanh (Real.sqrt 3 * x / 2) := by
      have hx := uniformInterval_momentPotential_gradient x
      rw [gradient_eq_deriv'] at hx
      exact hx

    have hmonoderiv :
        Monotone
          (deriv
            (fun y : ℝ =>
              2 * Real.log (Real.cosh (Real.sqrt 3 * y / 2)) +
                Real.log (4 / Real.sqrt 3))) := by
      intro x y hxy
      rw [hderiv x, hderiv y]
      exact hgmono hxy

    exact
      ⟨hphi,
        Monotone.convexOn_univ_of_deriv hfdiff hmonoderiv⟩


/-- The Hessian of the moment potential: `∇²φ(x)(v, v) = 3 / (2 cosh²(√3 x / 2)) · v²`. -/
theorem uniformInterval_momentPotential_bilinearIteratedFDerivTwo :
    ∀ x v : ℝ, bilinearIteratedFDerivTwo ℝ (fun y : ℝ => 2 * Real.log (Real.cosh (Real.sqrt 3 * y / 2)) + Real.log (4 / Real.sqrt 3)) x v v = 3 / 2 / Real.cosh (Real.sqrt 3 * x / 2) ^ 2 * (v * v) := by
    intro x v
    have h2 :
        ContDiff ℝ 2
          (fun y : ℝ =>
            2 * Real.log (Real.cosh (Real.sqrt 3 * y / 2)) +
              Real.log (4 / Real.sqrt 3)) :=
      uniformInterval_momentPotential_contDiff_convexOn.1.of_le
        (WithTop.coe_le_coe.mpr le_top)
    rw [bilinearIteratedFDerivTwo_eq_fderiv_apply h2 x v v]
    have hfd (y : ℝ) :
        (fderiv ℝ
            (fun z : ℝ =>
              2 * Real.log (Real.cosh (Real.sqrt 3 * z / 2)) +
                Real.log (4 / Real.sqrt 3)) y) v =
          (Real.sqrt 3 * Real.tanh (Real.sqrt 3 * y / 2)) * v := by
      rw [fderiv_eq_deriv_mul]
      calc
        deriv
            (fun z : ℝ =>
              2 * Real.log (Real.cosh (Real.sqrt 3 * z / 2)) +
                Real.log (4 / Real.sqrt 3)) y * v =
            gradient
              (fun z : ℝ =>
                2 * Real.log (Real.cosh (Real.sqrt 3 * z / 2)) +
                  Real.log (4 / Real.sqrt 3)) y * v := by
              rw [gradient_eq_deriv']
        _ = (Real.sqrt 3 * Real.tanh (Real.sqrt 3 * y / 2)) * v := by
          rw [uniformInterval_momentPotential_gradient y]
    have hfun :
        (fun y : ℝ =>
            (fderiv ℝ
              (fun z : ℝ =>
                2 * Real.log (Real.cosh (Real.sqrt 3 * z / 2)) +
                  Real.log (4 / Real.sqrt 3)) y) v) =
          (fun y : ℝ => (Real.sqrt 3 * Real.tanh (Real.sqrt 3 * y / 2)) * v) :=
      funext hfd
    rw [hfun, fderiv_eq_deriv_mul]
    have hgAt (x : ℝ) :
        HasDerivAt
          (fun z : ℝ => Real.sqrt 3 * Real.tanh (Real.sqrt 3 * z / 2))
          (Real.sqrt 3 *
            ((Real.cosh (Real.sqrt 3 * x / 2) * (Real.sqrt 3 / 2) *
                  Real.cosh (Real.sqrt 3 * x / 2) -
                Real.sinh (Real.sqrt 3 * x / 2) *
                  (Real.sinh (Real.sqrt 3 * x / 2) * (Real.sqrt 3 / 2))) /
                Real.cosh (Real.sqrt 3 * x / 2) ^ 2)) x := by
      have hargAt :
          HasDerivAt
            (fun z : ℝ => Real.sqrt 3 * z / 2)
            (Real.sqrt 3 / 2) x := by
        simpa using
          (HasDerivAt.div_const
            (HasDerivAt.const_mul (Real.sqrt 3) (hasDerivAt_id x)) 2)
      have hsinh :
          HasDerivAt
            (fun z : ℝ => Real.sinh (Real.sqrt 3 * z / 2))
            (Real.cosh (Real.sqrt 3 * x / 2) * (Real.sqrt 3 / 2)) x := by
        simpa only [Function.comp_def] using
          (Real.hasDerivAt_sinh (Real.sqrt 3 * x / 2)).comp x hargAt
      have hcoshAt :
          HasDerivAt
            (fun z : ℝ => Real.cosh (Real.sqrt 3 * z / 2))
            (Real.sinh (Real.sqrt 3 * x / 2) * (Real.sqrt 3 / 2)) x := by
        simpa only [Function.comp_def] using
          (Real.hasDerivAt_cosh (Real.sqrt 3 * x / 2)).comp x hargAt
      have hne : Real.cosh (Real.sqrt 3 * x / 2) ≠ 0 :=
        ne_of_gt (Real.cosh_pos (Real.sqrt 3 * x / 2))
      simpa only [Function.comp_def, Pi.div_apply, Real.tanh_eq_sinh_div_cosh] using
        (HasDerivAt.const_mul (Real.sqrt 3)
          (HasDerivAt.div hsinh hcoshAt hne))
    have hquot :
        ((Real.cosh (Real.sqrt 3 * x / 2) * (Real.sqrt 3 / 2) *
              Real.cosh (Real.sqrt 3 * x / 2) -
            Real.sinh (Real.sqrt 3 * x / 2) *
              (Real.sinh (Real.sqrt 3 * x / 2) * (Real.sqrt 3 / 2))) /
            Real.cosh (Real.sqrt 3 * x / 2) ^ 2) =
          (Real.sqrt 3 / 2) / Real.cosh (Real.sqrt 3 * x / 2) ^ 2 := by
      calc
        ((Real.cosh (Real.sqrt 3 * x / 2) * (Real.sqrt 3 / 2) *
              Real.cosh (Real.sqrt 3 * x / 2) -
            Real.sinh (Real.sqrt 3 * x / 2) *
              (Real.sinh (Real.sqrt 3 * x / 2) * (Real.sqrt 3 / 2))) /
            Real.cosh (Real.sqrt 3 * x / 2) ^ 2) =
            ((Real.sqrt 3 / 2) *
              (Real.cosh (Real.sqrt 3 * x / 2) ^ 2 -
                Real.sinh (Real.sqrt 3 * x / 2) ^ 2)) /
              Real.cosh (Real.sqrt 3 * x / 2) ^ 2 := by
                ring
        _ = (Real.sqrt 3 / 2) / Real.cosh (Real.sqrt 3 * x / 2) ^ 2 := by
          simp [Real.cosh_sq_sub_sinh_sq]
    have hsqrt : (Real.sqrt (3 : ℝ)) ^ 2 = 3 :=
      Real.sq_sqrt (by norm_num)
    have hgderiv :
        deriv
            (fun z : ℝ => Real.sqrt 3 * Real.tanh (Real.sqrt 3 * z / 2)) x =
          3 / 2 / Real.cosh (Real.sqrt 3 * x / 2) ^ 2 := by
      rw [HasDerivAt.deriv (hgAt x), hquot]
      field_simp [ne_of_gt (Real.cosh_pos (Real.sqrt 3 * x / 2))]
      nlinarith
    have hgv :
        HasDerivAt
          (fun y : ℝ => (Real.sqrt 3 * Real.tanh (Real.sqrt 3 * y / 2)) * v)
          ((3 / 2 / Real.cosh (Real.sqrt 3 * x / 2) ^ 2) * v) x := by
      simpa [hgderiv] using (hgAt x).differentiableAt.hasDerivAt.mul_const v
    rw [hgv.deriv]
    ring


/-- The Monge–Ampère equation `log det ∇²φ = −φ + V ∘ ∇φ` (standard orthonormal basis) with `V ≡ log(2√3)`. -/
theorem uniformInterval_momentPotential_logDetHessian :
    ∀ y, logDetHessian (fun y : ℝ => 2 * Real.log (Real.cosh (Real.sqrt 3 * y / 2)) + Real.log (4 / Real.sqrt 3)) (stdOrthonormalBasis ℝ ℝ) y =
        -(fun y : ℝ => 2 * Real.log (Real.cosh (Real.sqrt 3 * y / 2)) + Real.log (4 / Real.sqrt 3)) y + (fun _ : ℝ => Real.log (2 * Real.sqrt 3)) (gradient (fun y : ℝ => 2 * Real.log (Real.cosh (Real.sqrt 3 * y / 2)) + Real.log (4 / Real.sqrt 3)) y) := by
    intro y
    let : Unique (Fin (Module.finrank ℝ ℝ)) := by
      rw [Module.finrank_self]
      infer_instance
    have hsqrt : 0 < Real.sqrt (3 : ℝ) := by
      positivity
    have hsqrt_ne : Real.sqrt (3 : ℝ) ≠ 0 := ne_of_gt hsqrt
    have hsq : (Real.sqrt (3 : ℝ)) ^ 2 = 3 := by
      exact Real.sq_sqrt (by norm_num)
    have he_norm :
        ‖(stdOrthonormalBasis ℝ ℝ) (default : Fin (Module.finrank ℝ ℝ))‖ = 1 :=
      (stdOrthonormalBasis ℝ ℝ).orthonormal.norm_eq_one _
    have he :
        (stdOrthonormalBasis ℝ ℝ) (default : Fin (Module.finrank ℝ ℝ)) *
            (stdOrthonormalBasis ℝ ℝ) (default : Fin (Module.finrank ℝ ℝ)) = 1 := by
      have habs :
          |(stdOrthonormalBasis ℝ ℝ) (default : Fin (Module.finrank ℝ ℝ))| = 1 := by
        simpa only [Real.norm_eq_abs] using he_norm
      calc
        (stdOrthonormalBasis ℝ ℝ) (default : Fin (Module.finrank ℝ ℝ)) *
            (stdOrthonormalBasis ℝ ℝ) (default : Fin (Module.finrank ℝ ℝ)) =
            ((stdOrthonormalBasis ℝ ℝ)
              (default : Fin (Module.finrank ℝ ℝ))) ^ 2 := by ring
        _ =
            |(stdOrthonormalBasis ℝ ℝ)
              (default : Fin (Module.finrank ℝ ℝ))| ^ 2 := by
          symm
          exact sq_abs _
        _ = 1 := by rw [habs]; norm_num
    have hc :
        Real.cosh (Real.sqrt 3 * y / 2) ≠ 0 :=
      ne_of_gt (Real.cosh_pos _)
    have hentry :
        hessianMatrixIn
            (fun y : ℝ =>
              2 * Real.log (Real.cosh (Real.sqrt 3 * y / 2)) +
                Real.log (4 / Real.sqrt 3))
            (stdOrthonormalBasis ℝ ℝ) y
            (default : Fin (Module.finrank ℝ ℝ))
            (default : Fin (Module.finrank ℝ ℝ)) =
          3 / 2 / Real.cosh (Real.sqrt 3 * y / 2) ^ 2 := by
      simpa [hessianMatrixIn, he] using
        (uniformInterval_momentPotential_bilinearIteratedFDerivTwo y
          ((stdOrthonormalBasis ℝ ℝ)
            (default : Fin (Module.finrank ℝ ℝ))))
    unfold logDetHessian
    rw [Matrix.det_unique, hentry]
    dsimp
    have hconst :
        Real.log (3 / 2) =
          Real.log (2 * Real.sqrt 3) - Real.log (4 / Real.sqrt 3) := by
      calc
        Real.log (3 / 2) =
            Real.log ((2 * Real.sqrt 3) / (4 / Real.sqrt 3)) := by
              congr 1
              field_simp [hsqrt_ne]
              nlinarith [hsq]
        _ = Real.log (2 * Real.sqrt 3) - Real.log (4 / Real.sqrt 3) := by
          rw [Real.log_div]
          · positivity
          · positivity
    rw [Real.log_div (by norm_num) (pow_ne_zero 2 hc), Real.log_pow]
    rw [hconst]
    ring

end FunctionalInequalities.Analysis.BakryEmery

namespace FunctionalInequalities.Analysis.BakryEmery

private theorem uniformInterval_exp_neg_momentPotential_eq (x : ℝ) :
    Real.exp (-(fun y : ℝ => 2 * Real.log (Real.cosh (Real.sqrt 3 * y / 2)) + Real.log (4 / Real.sqrt 3)) x) =
      Real.sqrt 3 / 4 / Real.cosh (Real.sqrt 3 * x / 2) ^ 2 := by
    dsimp
    have hs : 0 < Real.sqrt 3 := (Real.sqrt_pos).2 (by norm_num)
    have hc : 0 < Real.cosh (Real.sqrt 3 * x / 2) :=
      Real.cosh_pos _
    have hq : 0 < 4 / Real.sqrt 3 := div_pos (by norm_num) hs
    have he :
        Real.exp (2 * Real.log (Real.cosh (Real.sqrt 3 * x / 2))) =
          Real.cosh (Real.sqrt 3 * x / 2) ^ 2 := by
      rw [two_mul, Real.exp_add, Real.exp_log hc, pow_two]
    have hs0 : Real.sqrt 3 ≠ 0 := ne_of_gt hs
    have hc0 : Real.cosh (Real.sqrt 3 * x / 2) ≠ 0 := ne_of_gt hc
    rw [Real.exp_neg, Real.exp_add, he, Real.exp_log hq]
    field_simp [hs0, hc0]

private theorem hasDerivAt_tanh_sqrt_three_mul_div_two_div_two (x : ℝ) :
    HasDerivAt (fun x : ℝ => Real.tanh (Real.sqrt 3 * x / 2) / 2) (Real.sqrt 3 / 4 / Real.cosh (Real.sqrt 3 * x / 2) ^ 2) x := by
    let z : ℝ := Real.sqrt 3 * x / 2
    have hq :
        HasDerivAt (fun y : ℝ => Real.sinh y / Real.cosh y)
          ((Real.cosh z * Real.cosh z - Real.sinh z * Real.sinh z) /
            Real.cosh z ^ 2) z :=
      (Real.hasDerivAt_sinh z).fun_div (Real.hasDerivAt_cosh z)
        (ne_of_gt (Real.cosh_pos z))
    have hqt :
        HasDerivAt (fun y : ℝ => Real.tanh y)
          (1 / Real.cosh z ^ 2) z := by
      have hqt₀ :
          HasDerivAt (fun y : ℝ => Real.tanh y)
            ((Real.cosh z * Real.cosh z - Real.sinh z * Real.sinh z) /
              Real.cosh z ^ 2) z :=
        hq.congr_of_eventuallyEq
          (Filter.Eventually.of_forall (fun y =>
            Real.tanh_eq_sinh_div_cosh y))
      apply hqt₀.congr_deriv
      calc
        (Real.cosh z * Real.cosh z - Real.sinh z * Real.sinh z) /
            Real.cosh z ^ 2 =
            (Real.cosh z ^ 2 - Real.sinh z ^ 2) /
              Real.cosh z ^ 2 := by ring
        _ = 1 / Real.cosh z ^ 2 := by
          rw [Real.cosh_sq_sub_sinh_sq]
    have hi :
        HasDerivAt (fun y : ℝ => Real.sqrt 3 * y / 2)
          (Real.sqrt 3 / 2) x := by
      simpa [Function.id_def] using
        ((hasDerivAt_id x).const_mul (Real.sqrt 3)).div_const 2
    have hc :=
      hqt.comp x hi
    have hf :
        HasDerivAt
          (fun y : ℝ => Real.tanh (Real.sqrt 3 * y / 2) / 2)
          ((1 / Real.cosh (Real.sqrt 3 * x / 2) ^ 2) *
              (Real.sqrt 3 / 2) / 2) x := by
      simpa [Function.comp_def, z] using hc.div_const 2
    exact hf.congr_deriv (by ring)

private theorem integrableOn_Iio_sqrt_three_div_four_div_cosh_sq_of_Ioi
    (hpos : IntegrableOn (fun x : ℝ => Real.sqrt 3 / 4 / Real.cosh (Real.sqrt 3 * x / 2) ^ 2) (Set.Ioi (0 : ℝ)) volume) :
    IntegrableOn (fun x : ℝ => Real.sqrt 3 / 4 / Real.cosh (Real.sqrt 3 * x / 2) ^ 2) (Set.Iio (0 : ℝ)) volume := by
    have hneg :
        IntegrableOn
          (fun x : ℝ =>
            Real.sqrt 3 / 4 / Real.cosh (Real.sqrt 3 * (-x) / 2) ^ 2)
          (Set.Iio (0 : ℝ)) volume := by
      simpa only [neg_zero] using
        (IntegrableOn.comp_neg_Iio (μ := (volume : Measure ℝ))
          (f := fun x : ℝ => Real.sqrt 3 / 4 / Real.cosh (Real.sqrt 3 * x / 2) ^ 2)
          (c := (0 : ℝ)) (by simpa only [neg_zero] using hpos))
    have hfun :
        (fun x : ℝ =>
          Real.sqrt 3 / 4 / Real.cosh (Real.sqrt 3 * (-x) / 2) ^ 2) =
        (fun x : ℝ =>
          Real.sqrt 3 / 4 / Real.cosh (Real.sqrt 3 * x / 2) ^ 2) := by
      funext x
      have hx :
          Real.cosh (Real.sqrt 3 * (-x) / 2) =
            Real.cosh (Real.sqrt 3 * x / 2) := by
        rw [show Real.sqrt 3 * (-x) / 2 = -(Real.sqrt 3 * x / 2) by ring]
        exact Real.cosh_neg _
      rw [hx]
    rw [← hfun]
    exact hneg

/-- The normalization `∫ e^{−φ} = 1` for Lebesgue measure. -/
theorem uniformInterval_momentPotential_integral_exp_neg :
    ∫ x, Real.exp (-(fun y : ℝ => 2 * Real.log (Real.cosh (Real.sqrt 3 * y / 2)) + Real.log (4 / Real.sqrt 3)) x) ∂(volume : Measure ℝ) = 1 := by
    let c : ℝ := Real.sqrt 3
    let f : ℝ → ℝ := fun x => c / 4 / Real.cosh (c * x / 2) ^ 2
    let F : ℝ → ℝ := fun x => Real.tanh (c * x / 2) / 2

    have hc : 0 < c := by
      dsimp [c]
      positivity
    have hc2 : c ^ 2 = 3 := by
      dsimp [c]
      exact Real.sq_sqrt (by norm_num)

    have hden (x : ℝ) :
        Real.exp
            (-(fun y : ℝ =>
              2 * Real.log (Real.cosh (Real.sqrt 3 * y / 2)) +
                Real.log (4 / Real.sqrt 3)) x) =
          f x :=
      uniformInterval_exp_neg_momentPotential_eq x

    have hF (x : ℝ) : HasDerivAt F (f x) x :=
      hasDerivAt_tanh_sqrt_three_mul_div_two_div_two x

    have hFtop : Filter.Tendsto F Filter.atTop (nhds (1 / 2)) := by
      have ha : 0 < (2 : ℝ) * (c / 2) := by positivity
      have hlin :
          Filter.Tendsto (fun x : ℝ => (2 : ℝ) * (c / 2) * x)
            Filter.atTop Filter.atTop :=
        Filter.Tendsto.const_mul_atTop ha Filter.tendsto_id
      have hz :
          Filter.Tendsto
            (fun x : ℝ => Real.exp (-((2 : ℝ) * (c / 2) * x)))
            Filter.atTop (nhds 0) :=
        Real.tendsto_exp_neg_atTop_nhds_zero.comp hlin
      have he :
          ∀ x : ℝ,
            Real.tanh (c * x / 2) =
              (1 - Real.exp (-((2 : ℝ) * (c / 2) * x))) /
                (1 + Real.exp (-((2 : ℝ) * (c / 2) * x))) := by
        intro x
        let t : ℝ := c * x / 2
        have hp : 0 < Real.exp t := Real.exp_pos _
        have hpn : 0 < Real.exp (-t) := Real.exp_pos _
        have hmul : Real.exp t * Real.exp (-t) = 1 := by
          rw [← Real.exp_add]
          simp
        have hmul' : Real.exp (-t) * Real.exp (-t) = Real.exp (-2 * t) := by
          rw [← Real.exp_add]
          congr 1
          ring
        rw [Real.tanh_eq]
        calc
          (Real.exp t - Real.exp (-t)) / (Real.exp t + Real.exp (-t)) =
              ((Real.exp t - Real.exp (-t)) * Real.exp (-t)) /
                ((Real.exp t + Real.exp (-t)) * Real.exp (-t)) := by
                  field_simp
          _ = (1 - Real.exp (-2 * t)) / (1 + Real.exp (-2 * t)) := by
            rw [sub_mul, add_mul, hmul, hmul']
          _ = (1 - Real.exp (-((2 : ℝ) * (c / 2) * x))) /
                (1 + Real.exp (-((2 : ℝ) * (c / 2) * x))) := by
                  congr 2 <;> dsimp [t] <;> ring
      rw [show F = fun x =>
          ((1 - Real.exp (-((2 : ℝ) * (c / 2) * x))) /
            (1 + Real.exp (-((2 : ℝ) * (c / 2) * x)))) / 2 by
            funext x
            dsimp [F]
            rw [he]]
      have hnum :
          Filter.Tendsto
            (fun x : ℝ => 1 - Real.exp (-((2 : ℝ) * (c / 2) * x)))
            Filter.atTop (nhds (1 - 0)) :=
        tendsto_const_nhds.sub hz
      have hdenom :
          Filter.Tendsto
            (fun x : ℝ => 1 + Real.exp (-((2 : ℝ) * (c / 2) * x)))
            Filter.atTop (nhds (1 + 0)) :=
        tendsto_const_nhds.add hz
      have hquot := hnum.div hdenom (by norm_num : (1 + 0 : ℝ) ≠ 0)
      simpa using hquot.div_const 2

    have hFbot : Filter.Tendsto F Filter.atBot (nhds (-1 / 2)) := by
      have hneg :
          Filter.Tendsto (fun x : ℝ => -x) Filter.atBot Filter.atTop :=
        Filter.tendsto_neg_atBot_atTop
      have ht :
          Filter.Tendsto (fun x : ℝ => F (-x)) Filter.atBot (nhds (1 / 2)) :=
        hFtop.comp hneg
      have ho :
          (fun x : ℝ => F (-x)) = fun x : ℝ => -F x := by
        funext x
        dsimp [F]
        rw [show c * (-x) / 2 = -(c * x / 2) by ring, Real.tanh_neg]
        ring
      rw [ho] at ht
      convert ht.neg using 1 <;> norm_num

    have hpos : IntegrableOn f (Set.Ioi (0 : ℝ)) volume := by
      apply integrableOn_Ioi_deriv_of_nonneg' (g := F) (g' := f) (a := 0)
      · intro x hx
        exact hF x
      · intro x hx
        dsimp [f]
        positivity
      · exact hFtop

    have heven : ∀ x : ℝ, f (-x) = f x := by
      intro x
      dsimp [f]
      rw [show c * (-x) / 2 = -(c * x / 2) by ring, Real.cosh_neg]

    have hneg : IntegrableOn f (Set.Iio (0 : ℝ)) volume :=
      integrableOn_Iio_sqrt_three_div_four_div_cosh_sq_of_Ioi hpos

    have hzero : IntegrableOn f ({0} : Set ℝ) volume := by
      refine integrableOn_singleton (f := f) (x := (0 : ℝ)) (hfx := ?_) (hx := ?_)
      · simp
      · simp

    have hint : Integrable f volume := by
      rw [← integrableOn_univ]
      have hu :
          Set.Iio (0 : ℝ) ∪ ({0} : Set ℝ) ∪ Set.Ioi (0 : ℝ) = Set.univ := by
        ext x
        simp only [Set.mem_union, Set.mem_Iio, Set.mem_singleton_iff,
          Set.mem_Ioi, Set.mem_univ]
        rcases lt_trichotomy x 0 with h | h | h <;> simp [h]
      rw [← hu]
      exact (hneg.union hzero).union hpos

    have hformula :
        ∫ x, f x = (1 / 2) - (-1 / 2) :=
      integral_of_hasDerivAt_of_tendsto hF hint hFbot hFtop

    calc
      ∫ x, Real.exp
          (-(fun y : ℝ =>
            2 * Real.log (Real.cosh (Real.sqrt 3 * y / 2)) +
              Real.log (4 / Real.sqrt 3)) x) ∂(volume : Measure ℝ) =
          ∫ x, f x := by
            apply integral_congr_ae
            filter_upwards [] with x
            exact hden x
      _ = 1 := by
        rw [hformula]
        norm_num


/-- The source-class hypotheses of Letwin's Lemmas A.4 and A.5 for the moment potential: `C^∞` and convex, gradient range
in `K = (−√3, √3)`, the Monge–Ampère equation with `V ≡ log(2√3)`, positive definite Hessian and `∫ e^{−φ} = 1`. -/
theorem uniformInterval_momentPotential_source_hypotheses :
    ContDiff ℝ ∞ (fun y : ℝ => 2 * Real.log (Real.cosh (Real.sqrt 3 * y / 2)) + Real.log (4 / Real.sqrt 3)) ∧ ConvexOn ℝ Set.univ (fun y : ℝ => 2 * Real.log (Real.cosh (Real.sqrt 3 * y / 2)) + Real.log (4 / Real.sqrt 3)) ∧
      Set.range (gradient (fun y : ℝ => 2 * Real.log (Real.cosh (Real.sqrt 3 * y / 2)) + Real.log (4 / Real.sqrt 3))) ⊆ Set.Ioo (-Real.sqrt 3) (Real.sqrt 3) ∧
      (∀ y, logDetHessian (fun y : ℝ => 2 * Real.log (Real.cosh (Real.sqrt 3 * y / 2)) + Real.log (4 / Real.sqrt 3)) (stdOrthonormalBasis ℝ ℝ) y =
        -(fun y : ℝ => 2 * Real.log (Real.cosh (Real.sqrt 3 * y / 2)) + Real.log (4 / Real.sqrt 3)) y + (fun _ : ℝ => Real.log (2 * Real.sqrt 3)) (gradient (fun y : ℝ => 2 * Real.log (Real.cosh (Real.sqrt 3 * y / 2)) + Real.log (4 / Real.sqrt 3)) y)) ∧
      (∀ x v : ℝ, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ (fun y : ℝ => 2 * Real.log (Real.cosh (Real.sqrt 3 * y / 2)) + Real.log (4 / Real.sqrt 3)) x v v) ∧
      ∫ x, Real.exp (-(fun y : ℝ => 2 * Real.log (Real.cosh (Real.sqrt 3 * y / 2)) + Real.log (4 / Real.sqrt 3)) x) ∂(volume : Measure ℝ) = 1 := by
    have hcv :=
      uniformInterval_momentPotential_contDiff_convexOn
    refine ⟨hcv.1, hcv.2, ?_, uniformInterval_momentPotential_logDetHessian, ?_,
      uniformInterval_momentPotential_integral_exp_neg⟩
    · intro z hz
      rcases hz with ⟨y, rfl⟩
      rw [uniformInterval_momentPotential_gradient]
      have hs : 0 < Real.sqrt (3 : ℝ) := by
        positivity
      have ht :
          |Real.tanh (Real.sqrt 3 * y / 2)| < (1 : ℝ) :=
        Real.abs_tanh_lt_one _
      have ht' :
          -1 < Real.tanh (Real.sqrt 3 * y / 2) ∧
            Real.tanh (Real.sqrt 3 * y / 2) < 1 :=
        abs_lt.mp ht
      constructor
      · have h := mul_lt_mul_of_pos_left ht'.1 hs
        simpa using h
      · have h := mul_lt_mul_of_pos_left ht'.2 hs
        simpa using h
    · intro x v hv
      rw [uniformInterval_momentPotential_bilinearIteratedFDerivTwo]
      have hc : 0 < Real.cosh (Real.sqrt 3 * x / 2) :=
        Real.cosh_pos _
      have hcoef :
          0 < (3 : ℝ) / 2 / Real.cosh (Real.sqrt 3 * x / 2) ^ 2 := by
        positivity
      have hvv : 0 < v * v :=
        mul_self_pos.mpr hv
      exact mul_pos hcoef hvv

end FunctionalInequalities.Analysis.BakryEmery

/-!
## The test function `f = tanh²(√3 y / 2)`

Its first derivative `√3 tanh(√3 x / 2) / cosh²(√3 x / 2)` and second derivative
`(3/2) sech²(√3 y / 2) (1 − 3 tanh²(√3 y / 2))`.
-/

namespace FunctionalInequalities.Analysis.BakryEmery

private theorem deriv_tanh_sqrt_three_mul_div_two_sq_eq :
    deriv (fun y : ℝ => Real.tanh (Real.sqrt 3 * y / 2) ^ 2) =
      fun x : ℝ => Real.sqrt 3 * Real.tanh (Real.sqrt 3 * x / 2) / Real.cosh (Real.sqrt 3 * x / 2) ^ 2 := by
    funext x
    have hmul :
        HasDerivAt
          (fun y : ℝ =>
            2 * (Real.tanh (Real.sqrt 3 * y / 2) / 2))
          (2 * (Real.sqrt 3 / 4 / Real.cosh (Real.sqrt 3 * x / 2) ^ 2)) x :=
      HasDerivAt.const_mul 2
        (hasDerivAt_tanh_sqrt_three_mul_div_two_div_two x)
    have htanh₀ :
        HasDerivAt
          (fun y : ℝ => Real.tanh (Real.sqrt 3 * y / 2))
          (2 * (Real.sqrt 3 / 4 / Real.cosh (Real.sqrt 3 * x / 2) ^ 2)) x := by
      exact hmul.congr_of_eventuallyEq
        (Filter.Eventually.of_forall (fun y => by ring))
    have htanh :
        HasDerivAt
          (fun y : ℝ => Real.tanh (Real.sqrt 3 * y / 2))
          (Real.sqrt 3 / 2 / Real.cosh (Real.sqrt 3 * x / 2) ^ 2) x := by
      exact htanh₀.congr_deriv (by ring)
    have hsq := htanh.fun_pow 2
    rw [hsq.deriv]
    ring

end FunctionalInequalities.Analysis.BakryEmery

namespace FunctionalInequalities.Analysis.BakryEmery

private theorem deriv_deriv_tanh_sqrt_three_mul_div_two_sq (y : ℝ) :
    deriv (deriv (fun y : ℝ => Real.tanh (Real.sqrt 3 * y / 2) ^ 2)) y =
      3 / 2 / Real.cosh (Real.sqrt 3 * y / 2) ^ 2 * (1 - 3 * Real.tanh (Real.sqrt 3 * y / 2) ^ 2) := by
    rw [deriv_tanh_sqrt_three_mul_div_two_sq_eq]
    have htanh₀ :
        HasDerivAt
          (fun z : ℝ => Real.tanh (Real.sqrt 3 * z / 2))
          (2 * (Real.sqrt 3 / 4 / Real.cosh (Real.sqrt 3 * y / 2) ^ 2)) y := by
      exact
        (HasDerivAt.const_mul 2
          (hasDerivAt_tanh_sqrt_three_mul_div_two_div_two y)).congr_of_eventuallyEq
          (Filter.Eventually.of_forall (fun z => by ring))
    have htanh :
        HasDerivAt
          (fun z : ℝ => Real.tanh (Real.sqrt 3 * z / 2))
          (Real.sqrt 3 / 2 / Real.cosh (Real.sqrt 3 * y / 2) ^ 2) y := by
      exact htanh₀.congr_deriv (by ring)
    have hnum :
        HasDerivAt
          (fun z : ℝ => Real.sqrt 3 * Real.tanh (Real.sqrt 3 * z / 2))
          (Real.sqrt 3 *
            (Real.sqrt 3 / 2 / Real.cosh (Real.sqrt 3 * y / 2) ^ 2)) y :=
      HasDerivAt.const_mul (Real.sqrt 3) htanh
    have harg :
        HasDerivAt
          (fun z : ℝ => Real.sqrt 3 * z / 2)
          (Real.sqrt 3 / 2) y := by
      simpa using ((hasDerivAt_id y).const_mul (Real.sqrt 3)).div_const 2
    have hcosh :
        HasDerivAt
          (fun z : ℝ => Real.cosh (Real.sqrt 3 * z / 2))
          (Real.sinh (Real.sqrt 3 * y / 2) * (Real.sqrt 3 / 2)) y := by
      simpa only [Function.comp_def] using
        (Real.hasDerivAt_cosh (Real.sqrt 3 * y / 2)).comp y harg
    have hcpos : 0 < Real.cosh (Real.sqrt 3 * y / 2) :=
      Real.cosh_pos _
    have hne : Real.cosh (Real.sqrt 3 * y / 2) ≠ 0 :=
      ne_of_gt hcpos
    have hden :
        HasDerivAt
          (fun z : ℝ => Real.cosh (Real.sqrt 3 * z / 2) ^ 2) _ y :=
      hcosh.fun_pow 2
    have hden_ne : Real.cosh (Real.sqrt 3 * y / 2) ^ 2 ≠ 0 := by
      positivity
    have hquot := hnum.fun_div hden hden_ne
    rw [hquot.deriv]
    simp only [Real.tanh_eq_sinh_div_cosh]
    have hsqrt : (Real.sqrt (3 : ℝ)) ^ 2 = 3 :=
      Real.sq_sqrt (by norm_num)
    norm_num only
    field_simp [hne]
    nlinarith [hsqrt, Real.cosh_sq_sub_sinh_sq (Real.sqrt 3 * y / 2)]

end FunctionalInequalities.Analysis.BakryEmery

namespace FunctionalInequalities.Analysis.BakryEmery

private theorem stdOrthonormalBasis_real_mul_self (i : Fin (Module.finrank ℝ ℝ)) :
    stdOrthonormalBasis ℝ ℝ i * stdOrthonormalBasis ℝ ℝ i = 1 := by
    have hbnorm : ‖stdOrthonormalBasis ℝ ℝ i‖ = 1 :=
      OrthonormalBasis.norm_eq_one (stdOrthonormalBasis ℝ ℝ) i
    have habs : |stdOrthonormalBasis ℝ ℝ i| = 1 := by
      simpa only [Real.norm_eq_abs] using hbnorm
    calc
      stdOrthonormalBasis ℝ ℝ i * stdOrthonormalBasis ℝ ℝ i =
          |stdOrthonormalBasis ℝ ℝ i| * |stdOrthonormalBasis ℝ ℝ i| :=
        (abs_mul_abs_self (stdOrthonormalBasis ℝ ℝ i)).symm
      _ = 1 := by rw [habs]; norm_num

private theorem rankOne_mul_eq_div_of_mul_eq_one {A k t : ℝ} (hk : k ≠ 0) (h : A * k = 1) : A * t = t / k := by
    apply (eq_div_iff hk).2
    calc
      A * t * k = t * (A * k) := by ring
      _ = t := by rw [h, mul_one]

private theorem differentiableAt_deriv_of_contDiff_two (g : ℝ → ℝ) (hg : ContDiff ℝ 2 g) (x : ℝ) :
    DifferentiableAt ℝ (deriv g) x := by
    have hfd : ContDiff ℝ 1 (fun y : ℝ => (fderiv ℝ g y) 1) := by
      exact contDiff_fderiv_apply (n := 2) (m := 1) hg (by norm_num) 1
    have hd : ContDiff ℝ 1 (deriv g) := by
      simpa only [fderiv_apply_one_eq_deriv] using hfd
    exact (hd.differentiable (by norm_num)).differentiableAt

end FunctionalInequalities.Analysis.BakryEmery



/-!
## The operator of the uniform-interval potential

With constant `V` the drift vanishes and the Hessian is rank one, so `L g = g″ / ((3/2) sech²(√3 y / 2))` for every
`C²` function `g` on `ℝ`; for `f` this gives `L f = 1 − 3 tanh²(√3 y / 2)`.
-/
namespace FunctionalInequalities.Analysis.BakryEmery

private theorem hessianInverseOperator_uniformInterval_eq_div (g : ℝ → ℝ) (hg : ContDiff ℝ 2 g) (y : ℝ) :
    hessianInverseOperator (fun y : ℝ => 2 * Real.log (Real.cosh (Real.sqrt 3 * y / 2)) + Real.log (4 / Real.sqrt 3)) (fun _ : ℝ => Real.log (2 * Real.sqrt 3)) g y =
      deriv (deriv g) y / (3 / 2 / Real.cosh (Real.sqrt 3 * y / 2) ^ 2) := by
    let b : OrthonormalBasis (Fin (Module.finrank ℝ ℝ)) ℝ ℝ :=
      stdOrthonormalBasis ℝ ℝ
    have hfin : Module.finrank ℝ ℝ = 1 := Module.finrank_self ℝ
    let : Unique (Fin (Module.finrank ℝ ℝ)) := by
      rw [hfin]
      infer_instance

    have hφ :
        ContDiff ℝ 2
          (fun x : ℝ =>
            2 * Real.log (Real.cosh (Real.sqrt 3 * x / 2)) +
              Real.log (4 / Real.sqrt 3)) :=
      uniformInterval_momentPotential_contDiff_convexOn.1.of_le
        (WithTop.coe_le_coe.mpr le_top)

    have hpos (x v : ℝ) (hv : v ≠ 0) :
        0 <
          ((bilinearIteratedFDerivTwo ℝ
              (fun z : ℝ =>
                2 * Real.log (Real.cosh (Real.sqrt 3 * z / 2)) +
                  Real.log (4 / Real.sqrt 3)) x) v) v := by
      rw [uniformInterval_momentPotential_bilinearIteratedFDerivTwo]
      have hvv : 0 < v * v := mul_self_pos.mpr hv
      positivity

    have hbnorm : ‖b default‖ = 1 :=
      OrthonormalBasis.norm_eq_one b default
    have hbsq : b default * b default = 1 :=
      stdOrthonormalBasis_real_mul_self default

    have hinv (x : ℝ) :
        inverseHessianEntry
            (fun z : ℝ =>
              2 * Real.log (Real.cosh (Real.sqrt 3 * z / 2)) +
                Real.log (4 / Real.sqrt 3))
            b x default default *
            (3 / 2 / Real.cosh (Real.sqrt 3 * x / 2) ^ 2) = 1 := by
      have h :=
        sum_inverseHessianEntry_mul_hessian
          (b := b) (φ :=
            fun z : ℝ =>
              2 * Real.log (Real.cosh (Real.sqrt 3 * z / 2)) +
                Real.log (4 / Real.sqrt 3))
          hφ x (hpos x) default default
      simpa [Fintype.sum_unique,
        uniformInterval_momentPotential_bilinearIteratedFDerivTwo, hbsq] using h

    have hgb (x v : ℝ) :
        ((bilinearIteratedFDerivTwo ℝ g x) v) v =
          deriv (deriv g) x * (v * v) := by
      rw [bilinearIteratedFDerivTwo_eq_fderiv_apply hg x v v]
      rw [fderiv_eq_deriv_mul]
      have hfun :
          (fun z : ℝ => (fderiv ℝ g z) v) =
            (fun z : ℝ => deriv g z * v) := by
        funext z
        rw [fderiv_eq_deriv_mul]
      rw [hfun, deriv_mul_const (differentiableAt_deriv_of_contDiff_two g hg x)]
      ring

    have hgb0 (x : ℝ) :
        ((bilinearIteratedFDerivTwo ℝ g x) (b default)) (b default) =
          deriv (deriv g) x := by
      rw [hgb, hbsq, mul_one]

    have hmain (x : ℝ) :
        inverseHessianEntry
            (fun z : ℝ =>
              2 * Real.log (Real.cosh (Real.sqrt 3 * z / 2)) +
                Real.log (4 / Real.sqrt 3))
            b x default default *
            ((bilinearIteratedFDerivTwo ℝ g x) (b default)) (b default) =
          deriv (deriv g) x /
            (3 / 2 / Real.cosh (Real.sqrt 3 * x / 2) ^ 2) := by
      rw [hgb0]
      have hc :
          3 / 2 / Real.cosh (Real.sqrt 3 * x / 2) ^ 2 ≠ 0 := by
        positivity
      exact rankOne_mul_eq_div_of_mul_eq_one hc (hinv x)

    simp [hessianInverseOperator, nondivergenceOperator, b, hmain,
      zero_apply]

end FunctionalInequalities.Analysis.BakryEmery

/-!
## The nonconstant facts used by Lemma A.5

`f` is smooth and bounded by `1`, `L f = 1 − 3 tanh²(√3 y / 2)`, `L f + 2 f ≥ 0`, and `f 0 ≠ f 1`.
-/
namespace FunctionalInequalities.Analysis.BakryEmery

private theorem contDiff_tanh_sqrt_three_mul_div_two :
    ContDiff ℝ ∞ (fun y : ℝ => Real.tanh (Real.sqrt 3 * y / 2)) := by
    have hmul :
        ContDiff ℝ ∞ (fun x : ℝ => Real.sqrt 3 * x) := by
      simpa using
        (ContDiff.mul
          (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => Real.sqrt 3))
          (contDiff_id : ContDiff ℝ ∞ (fun x : ℝ => x)))
    have harg :
        ContDiff ℝ ∞ (fun x : ℝ => Real.sqrt 3 * x / 2) := by
      simpa using (ContDiff.div_const hmul 2)
    have hsinh :
        ContDiff ℝ ∞ (fun x : ℝ => Real.sinh (Real.sqrt 3 * x / 2)) := by
      simpa only [Function.comp_def] using
        (Real.contDiff_sinh.comp harg)
    have hcosh :
        ContDiff ℝ ∞ (fun x : ℝ => Real.cosh (Real.sqrt 3 * x / 2)) := by
      simpa only [Function.comp_def] using
        (Real.contDiff_cosh.comp harg)
    have hquot :
        ContDiff ℝ ∞
          ((fun x : ℝ => Real.sinh (Real.sqrt 3 * x / 2)) /
            (fun x : ℝ => Real.cosh (Real.sqrt 3 * x / 2))) := by
      exact
        ContDiff.div hsinh hcosh
          (fun x => ne_of_gt (Real.cosh_pos (Real.sqrt 3 * x / 2)))
    simpa only [Real.tanh_eq_sinh_div_cosh, Pi.div_def] using hquot

private theorem tanh_sqrt_three_sq_zero_ne_one :
    (fun y : ℝ => Real.tanh (Real.sqrt 3 * y / 2) ^ 2) 0 ≠ (fun y : ℝ => Real.tanh (Real.sqrt 3 * y / 2) ^ 2) 1 := by
    have hleft :
        (fun y : ℝ => Real.tanh (Real.sqrt 3 * y / 2) ^ 2) 0 = 0 := by
      simp
    rw [hleft]
    have hsqrt : 0 < Real.sqrt (3 : ℝ) := by
      exact (Real.sqrt_pos).2 (by norm_num)
    have harg : 0 < Real.sqrt (3 : ℝ) * (1 : ℝ) / 2 := by
      positivity
    have hsinh :
        0 < Real.sinh (Real.sqrt (3 : ℝ) * (1 : ℝ) / 2) := by
      exact (Real.sinh_pos_iff).2 harg
    have hcosh :
        0 < Real.cosh (Real.sqrt (3 : ℝ) * (1 : ℝ) / 2) :=
      Real.cosh_pos _
    have htanh :
        0 < Real.tanh (Real.sqrt (3 : ℝ) * (1 : ℝ) / 2) := by
      rw [Real.tanh_eq_sinh_div_cosh]
      exact div_pos hsinh hcosh
    have hsq :
        0 < Real.tanh (Real.sqrt (3 : ℝ) * (1 : ℝ) / 2) ^ 2 :=
      pow_pos htanh 2
    exact (ne_of_gt hsq).symm

private theorem hessianInverseOperator_uniformInterval_tanhSq (hf : ContDiff ℝ 2 (fun y : ℝ => Real.tanh (Real.sqrt 3 * y / 2) ^ 2)) (y : ℝ) :
    hessianInverseOperator (fun y : ℝ => 2 * Real.log (Real.cosh (Real.sqrt 3 * y / 2)) + Real.log (4 / Real.sqrt 3)) (fun _ : ℝ => Real.log (2 * Real.sqrt 3)) (fun y : ℝ => Real.tanh (Real.sqrt 3 * y / 2) ^ 2) y =
      1 - 3 * Real.tanh (Real.sqrt 3 * y / 2) ^ 2 := by
    have hdiv :=
      hessianInverseOperator_uniformInterval_eq_div
        (fun z : ℝ => Real.tanh (Real.sqrt 3 * z / 2) ^ 2) hf y
    rw [hdiv, deriv_deriv_tanh_sqrt_three_mul_div_two_sq]
    have hk :
        (3 / 2 / Real.cosh (Real.sqrt 3 * y / 2) ^ 2 : ℝ) ≠ 0 := by
      positivity
    apply (div_eq_iff hk).2
    ring

/-- The nonconstant test function `f = tanh²(√3 y / 2)`: `C^∞`, `|f| ≤ 1`, `L f = 1 − 3 tanh²(√3 y / 2)`, `L f + 2 f ≥ 0` and
`f 0 ≠ f 1`, where `L` is `hessianInverseOperator` for the moment potential and `V ≡ log(2√3)`. -/
theorem uniformInterval_tanhSq_nonconstant_facts :
    ContDiff ℝ ∞ (fun y : ℝ => Real.tanh (Real.sqrt 3 * y / 2) ^ 2) ∧ (∀ y, |(fun y : ℝ => Real.tanh (Real.sqrt 3 * y / 2) ^ 2) y| ≤ 1) ∧
      (∀ y, hessianInverseOperator (fun y : ℝ => 2 * Real.log (Real.cosh (Real.sqrt 3 * y / 2)) + Real.log (4 / Real.sqrt 3)) (fun _ : ℝ => Real.log (2 * Real.sqrt 3)) (fun y : ℝ => Real.tanh (Real.sqrt 3 * y / 2) ^ 2) y =
        1 - 3 * Real.tanh (Real.sqrt 3 * y / 2) ^ 2) ∧
      (∀ y, 0 ≤ hessianInverseOperator (fun y : ℝ => 2 * Real.log (Real.cosh (Real.sqrt 3 * y / 2)) + Real.log (4 / Real.sqrt 3)) (fun _ : ℝ => Real.log (2 * Real.sqrt 3)) (fun y : ℝ => Real.tanh (Real.sqrt 3 * y / 2) ^ 2) y + 2 * (fun y : ℝ => Real.tanh (Real.sqrt 3 * y / 2) ^ 2) y) ∧
      (fun y : ℝ => Real.tanh (Real.sqrt 3 * y / 2) ^ 2) 0 ≠ (fun y : ℝ => Real.tanh (Real.sqrt 3 * y / 2) ^ 2) 1 := by
    classical
    let f : ℝ → ℝ := fun y => Real.tanh (Real.sqrt 3 * y / 2) ^ 2
    let φ : ℝ → ℝ :=
      fun y => 2 * Real.log (Real.cosh (Real.sqrt 3 * y / 2)) + Real.log (4 / Real.sqrt 3)
    let V : ℝ → ℝ := fun _ => Real.log (2 * Real.sqrt 3)

    have htanh :
        ContDiff ℝ ∞ (fun y : ℝ => Real.tanh (Real.sqrt 3 * y / 2)) :=
      contDiff_tanh_sqrt_three_mul_div_two

    have hcont : ContDiff ℝ ∞ f := by
      dsimp [f]
      simpa [Function.comp_def] using htanh.pow 2

    have hbound : ∀ y : ℝ, |f y| ≤ 1 := by
      intro y
      have hnonneg : 0 ≤ Real.tanh (Real.sqrt 3 * y / 2) ^ 2 := sq_nonneg _
      have hlt : Real.tanh (Real.sqrt 3 * y / 2) ^ 2 < 1 :=
        Real.tanh_sq_lt_one _
      rw [abs_of_nonneg hnonneg]
      exact le_of_lt hlt

    have hop :
        ∀ y : ℝ,
          hessianInverseOperator φ V f y =
            1 - 3 * Real.tanh (Real.sqrt 3 * y / 2) ^ 2 :=
      hessianInverseOperator_uniformInterval_tanhSq (hcont.of_le (WithTop.coe_le_coe.mpr le_top))

    have hpos :
        ∀ y : ℝ, 0 ≤
          hessianInverseOperator φ V f y + 2 * f y := by
      intro y
      rw [hop]
      dsimp [f]
      nlinarith [Real.tanh_sq_lt_one (Real.sqrt 3 * y / 2)]

    have hne :
        f 0 ≠ f 1 :=
      tanh_sqrt_three_sq_zero_ne_one

    exact ⟨hcont, hbound, hop, hpos, hne⟩

end FunctionalInequalities.Analysis.BakryEmery
