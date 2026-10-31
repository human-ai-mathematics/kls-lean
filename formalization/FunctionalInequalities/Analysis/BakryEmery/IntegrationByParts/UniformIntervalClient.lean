module

public import FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.InverseHessian.Cutoff
public import FunctionalInequalities.Analysis.BakryEmery.UniformIntervalPotential

/-!
# The nonconstant uniform-interval client of Letwin's Lemma A.5

Letwin, arXiv:2607.24164v1, Lemma A.5 (p. 18) applied with Lemma A.4 (p. 17): for the isotropic
uniform law on
`K = (−√3, √3)`, `V ≡ log(2√3)` on `U = ℝ`, its moment potential `φ(y) = 2 log cosh(√3 y / 2) +
log(4 / √3)` and Lebesgue
measure, the nonconstant bounded smooth `f = tanh²(√3 y / 2)` satisfies `L f ∈ L¹(ν)` and `∫ L f dν
= 0` for
`ν = volume.tilted (−φ)`.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory
open scoped ContDiff

namespace FunctionalInequalities.Analysis.BakryEmery

/--
**Letwin Lemma A.5 for the uniform-interval source law** (pp. 17–18): for the moment potential of
the uniform law on
`K = (−√3, √3)` with `V ≡ log(2√3)` and the nonconstant `f = tanh²(√3 y / 2)`, `L f ∈ L¹(ν)` and `∫
L f dν = 0`,
where `ν = volume.tilted (−φ)`. -/
theorem uniformInterval_tanhSq_integrable_and_integral_hessianInverseOperator_eq_zero :
    Integrable
        (hessianInverseOperator
          (fun y : ℝ =>
            2 * Real.log (Real.cosh (Real.sqrt 3 * y / 2)) + Real.log (4 / Real.sqrt 3))
          (fun _ : ℝ => Real.log (2 * Real.sqrt 3))
          (fun y : ℝ => Real.tanh (Real.sqrt 3 * y / 2) ^ 2))
        ((volume : Measure ℝ).tilted
          (-(fun y : ℝ =>
              2 * Real.log (Real.cosh (Real.sqrt 3 * y / 2)) + Real.log (4 / Real.sqrt 3)))) ∧
      (∫ y,
          hessianInverseOperator
            (fun y : ℝ =>
              2 * Real.log (Real.cosh (Real.sqrt 3 * y / 2)) + Real.log (4 / Real.sqrt 3))
            (fun _ : ℝ => Real.log (2 * Real.sqrt 3))
            (fun y : ℝ => Real.tanh (Real.sqrt 3 * y / 2) ^ 2)
            y ∂((volume : Measure ℝ).tilted
            (-(fun y : ℝ =>
                2 * Real.log (Real.cosh (Real.sqrt 3 * y / 2)) +
                  Real.log (4 / Real.sqrt 3))))) =
        0 := by
  obtain ⟨hphi, hconv, hRange, hlog, hPD, hnorm⟩ :=
    uniformInterval_momentPotential_source_hypotheses
  obtain ⟨hf, hfBound, hLf, hnonneg, hnonconst⟩ := uniformInterval_tanhSq_nonconstant_facts
  have hbounded : Bornology.IsBounded (Set.Ioo (-Real.sqrt 3) (Real.sqrt 3) : Set ℝ) :=
    Metric.isBounded_Ioo _ _
  have hU : IsOpen (Set.univ : Set ℝ) := isOpen_univ
  have hclosure : closure (Set.Ioo (-Real.sqrt 3) (Real.sqrt 3) : Set ℝ) ⊆ (Set.univ : Set ℝ) :=
    Set.subset_univ _
  have hV : ContDiffOn ℝ ∞ (fun _ : ℝ => Real.log (2 * Real.sqrt 3)) (Set.univ : Set ℝ) :=
    contDiffOn_const
  obtain
    ⟨χ, C, hC, hχsmooth, hχcompact, hχbounds, hχmono, hχlimit, hχintegrable, hχbound,
      hχdecay⟩ :=
    exists_cutoffs_hessianInverseOperator (m := (volume : Measure ℝ)) (K :=
      Set.Ioo (-Real.sqrt 3) (Real.sqrt 3)) (U := (Set.univ : Set ℝ)) hphi hconv hbounded hRange
      hU hclosure hV hlog hPD hnorm
  exact
    integrable_and_integral_hessianInverseOperator_eq_zero_of_cutoffs (volume : Measure ℝ) hphi
      hf hU hV (Set.subset_univ _) hlog hPD hnorm 1 hfBound 2 (by norm_num) hnonneg χ hχsmooth
      hχcompact hχbounds hχlimit hχintegrable hχdecay

end FunctionalInequalities.Analysis.BakryEmery
