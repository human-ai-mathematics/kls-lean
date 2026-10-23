import FunctionalInequalities.Analysis.Newtonian.L1

/-!
# The integrated cutoff majorant in dimensions `n ≥ 3`

`newtonian_cutoff_majorant_integrable_integral_le`: for `n ≥ 3` and `eps > 0`, the majorant
`|∂ᵢΓ| + (2 / eps) |Γ|` is integrable on `B_{2 eps}(0)` with integral at most `2 n eps / (n - 2)`. This is
the quantitative kernel estimate in the proof of Lemma 4.1 of Gilbarg–Trudinger, *Elliptic Partial
Differential Equations of Second Order*, Classics 2001 (ISBN 3-540-41160-7), p. 54. The planar case
is handled through `Analysis/Newtonian/LogL1.lean`.
-/

noncomputable section

open Set Metric MeasureTheory

namespace FunctionalInequalities.Analysis

/-- The integrated radial-cutoff majorant of GT2001 Lemma 4.1, p. 54, in `n > 2`.
This is a quantitative kernel estimate; the cutoff derivative and potential
representation are separate steps. -/
theorem newtonian_cutoff_majorant_integrable_integral_le {n : ℕ} (hn : 3 ≤ n)
    {eps : ℝ} (heps : 0 < eps) (i : Fin n) :
    IntegrableOn (fun y => |fderiv ℝ (newtonianKernel n) y (EuclideanSpace.basisFun (Fin n) ℝ i)| +
      (2/eps)*|newtonianKernel n y|) (ball 0 (2*eps)) volume ∧
    (∫ y in ball 0 (2*eps), |fderiv ℝ (newtonianKernel n) y (EuclideanSpace.basisFun (Fin n) ℝ i)| +
      (2/eps)*|newtonianKernel n y|) ≤ 2*(n:ℝ)*eps/((n:ℝ)-2) := by
  have hR : 0 < 2*eps := by positivity
  obtain ⟨hd,hdb⟩ := integrableOn_fderiv_newtonianKernel_ball (by omega : 2 ≤ n) hR i
  obtain ⟨hk,hkb⟩ := integrableOn_newtonianKernel_ball_of_two_lt hn hR
  have hc : 0 ≤ 2/eps := by positivity
  refine ⟨hd.abs.add (hk.abs.const_mul (2/eps)),?_⟩
  rw [integral_add hd.abs (hk.abs.const_mul (2/eps)),integral_const_mul]
  calc
    _ ≤ 2*eps+(2/eps)*((2*eps)^2/(2*((n:ℝ)-2))) :=
      add_le_add hdb (mul_le_mul_of_nonneg_left hkb hc)
    _ = _ := by
      have hN : (2:ℝ) < n := by exact_mod_cast (by omega : 2 < n)
      field_simp [heps.ne',(by linarith : (n:ℝ)-2 ≠ 0)]
      ring

end FunctionalInequalities.Analysis
