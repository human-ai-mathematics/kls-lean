module

public import FunctionalInequalities.Analysis.Newtonian.Potential.Basic
public import FunctionalInequalities.Analysis.Newtonian.Kernel.L1
public import FunctionalInequalities.Analysis.Newtonian.Potential.BoundaryFormula

/-!
# First-derivative estimate of the Newtonian potential on a ball

The gradient part of the estimate (4.14) of Gilbarg–Trudinger, *Elliptic Partial Differential
Equations
of Second Order*, Classics 2001 (ISBN 3-540-41160-7), p. 60.
`norm_fderiv_newtonianPotential_ball_le`: for
`n ≥ 2` (including `n = 2`) and an a.e.-measurable source with `|f| ≤ M` on `B_R(c)`, the actual
derivative
of `w = ∫_{B_R(c)} Γ(x - y) f(y) dy` satisfies `‖Dw(x)‖ ≤ n (2R) M` on `closedBall c R`. Only the
first
kernel derivative enters, through `∫_{B(0,ρ)} |D_iΓ| ≤ ρ`, so the constant depends on the dimension
alone
and the estimate is scale invariant (no `log R` for `n = 2`).
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory

namespace FunctionalInequalities.Analysis

section GradientBound

variable {n : ℕ}

/--
**Gradient estimate.** For `f` measurable with `|f| ≤ M` on `B_R(c)`, the actual derivative of the
Newtonian potential of `f`
over `B_R(c)` has operator norm at most `n·(2R)·M` at every point of the closed ball. -/
theorem norm_fderiv_newtonianPotential_ball_le (hn : 2 ≤ n) {c : EuclideanSpace ℝ (Fin n)}
    {R M : ℝ} (hR : 0 < R) {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : AEMeasurable f (volume.restrict (ball c R))) (hM : ∀ y ∈ ball c R, |f y| ≤ M)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ closedBall c R) :
    ‖fderiv ℝ (newtonianPotential n (ball c R) f) x‖ ≤ n * (2 * R) * M := by
  have hB : MeasurableSet (ball c R) := measurableSet_ball
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM c (mem_ball_self hR))
  obtain ⟨-, hDi, -, hDf⟩ :=
    newtonianPotential_contDiff_one_of_aebounded hn hB isBounded_ball hf
      (ae_restrict_of_forall_mem hB hM)
  have hentry :
    ∀ i : Fin n,
      |fderiv ℝ (newtonianPotential n (ball c R) f) x (EuclideanSpace.basisFun (Fin n) ℝ i)| ≤
        2 * R * M := by
    intro i
    obtain ⟨hGi, hGle⟩ :=
      integrableOn_fderiv_newtonianKernel_ball hn (by positivity : 0 < 2 * R) i
    set G : EuclideanSpace ℝ (Fin n) → ℝ :=
      (ball 0 (2 * R)).indicator fun z =>
        |fderiv ℝ (newtonianKernel n) z (EuclideanSpace.basisFun (Fin n) ℝ i)|
    have hG : Integrable G volume := (integrable_indicator_iff measurableSet_ball).mpr hGi.abs
    have hGx :
      ∀ y ∈ ball c R,
        G (x - y) =
          |fderiv ℝ (newtonianKernel n) (x - y) (EuclideanSpace.basisFun (Fin n) ℝ i)| := by
      intro y hy
      refine Set.indicator_of_mem ?_ _
      rw [mem_ball, dist_zero_right, ← dist_eq_norm]
      rw [mem_closedBall] at hx; rw [mem_ball] at hy
      linarith [dist_triangle x c y, dist_comm y c]
    rw [hDf x i]
    calc
      |∫ y in ball c R,
              fderiv ℝ (newtonianKernel n) (x - y) (EuclideanSpace.basisFun (Fin n) ℝ i) *
                f y| ≤
          ∫ y in ball c R,
            |fderiv ℝ (newtonianKernel n) (x - y) (EuclideanSpace.basisFun (Fin n) ℝ i) *
                f y| :=
        abs_integral_le_integral_abs
      _ ≤ ∫ y in ball c R, M * G (x - y) := by
        refine
          setIntegral_mono_on (hDi x i).abs ((hG.comp_sub_left x).const_mul M).integrableOn hB
            fun y hy => ?_
        rw [hGx y hy, abs_mul, mul_comm M]
        exact mul_le_mul_of_nonneg_left (hM y hy) (abs_nonneg _)
      _ ≤ ∫ y, M * G (x - y) :=
        setIntegral_le_integral ((hG.comp_sub_left x).const_mul M)
          (Filter.Eventually.of_forall fun y =>
            mul_nonneg hM0 (Set.indicator_nonneg (fun z _ => abs_nonneg _) _))
      _ =
          M *
            ∫ z in ball 0 (2 * R),
              |fderiv ℝ (newtonianKernel n) z (EuclideanSpace.basisFun (Fin n) ℝ i)| := by
        rw [integral_const_mul, integral_sub_left_eq_self G volume x,
          integral_indicator measurableSet_ball]
      _ ≤ M * (2 * R) := mul_le_mul_of_nonneg_left hGle hM0
      _ = 2 * R * M := by ring
  calc
    _ ≤
        ∑ i,
          |fderiv ℝ (newtonianPotential n (ball c R) f) x
              (EuclideanSpace.basisFun (Fin n) ℝ i)| :=
      opNorm_le_sum_abs_basisFun _
    _ ≤ ∑ _i : Fin n, 2 * R * M := Finset.sum_le_sum fun i _ => hentry i
    _ = n * (2 * R) * M := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

end GradientBound

end FunctionalInequalities.Analysis
