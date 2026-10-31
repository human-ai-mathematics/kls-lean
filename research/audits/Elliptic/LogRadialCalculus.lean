module

public import FunctionalInequalities.Analysis.LogRadial.Calculus
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Clients of the log/radial barrier second derivatives

* `off_axis_log_radial_client`: in `ℝ²` with `p = x₀`, `q = x₁`, `β = 0`, at the off-axis point `x =
  (1, 1)`,
  the main theorem gives the actual second derivatives on the coordinate directions:
  log piece `(e₀,e₀) = 0`, `(e₀,e₁) = 0`, `(e₁,e₁) = -2`; radial piece `1/(2√2)`, `-1/(2√2)`,
  `1/(2√2)`.
* `ambient_line_log_radial_client`: in the ambient line `ℝ¹` (a real direction `e₀`) with `p = 0`,
  `q = x₀`,
  `β = 0`, at `x₀ > 0`: the log piece `-x₀ log x₀²` has second derivative `-2/x₀` and the radial
  piece
  `√(x₀²) = |x₀|` has second derivative `0`.
-/

@[expose] public section

noncomputable section

namespace FunctionalInequalities.Analysis.LogRadialBarrierClient

open FunctionalInequalities.Analysis

/-- **Off-axis point `(1, 1)` in `ℝ²`.** -/
theorem off_axis_log_radial_client :
    let p : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ := EuclideanSpace.proj 0
    let q : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ := EuclideanSpace.proj 1
    let x : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 0 1 + EuclideanSpace.single 1 1
    let e₀ : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 0 1
    let e₁ : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 1 1
    let L := fun y : EuclideanSpace ℝ (Fin 2) => -(q y) * Real.log ((p y - 0) ^ 2 + (q y) ^ 2)
    let Q := fun y : EuclideanSpace ℝ (Fin 2) => Real.sqrt ((p y - 0) ^ 2 + (q y) ^ 2)
    fderiv ℝ (fderiv ℝ L) x e₀ e₀ = 0 ∧
      fderiv ℝ (fderiv ℝ L) x e₀ e₁ = 0 ∧
        fderiv ℝ (fderiv ℝ L) x e₁ e₁ = -2 ∧
          fderiv ℝ (fderiv ℝ Q) x e₀ e₀ = 1 / (2 * Real.sqrt 2) ∧
            fderiv ℝ (fderiv ℝ Q) x e₀ e₁ = -1 / (2 * Real.sqrt 2) ∧
              fderiv ℝ (fderiv ℝ Q) x e₁ e₁ = 1 / (2 * Real.sqrt 2) := by
  intro p q x e₀ e₁ L Q
  have hx : 0 < q x := by simp [q, x]
  have hp : p x = 1 := by simp [p, x]
  have hq : q x = 1 := by simp [q, x]
  have hp0 : p e₀ = 1 := by simp [p, e₀]
  have hq0 : q e₀ = 0 := by simp [q, e₀]
  have hp1 : p e₁ = 0 := by simp [p, e₁]
  have hq1 : q e₁ = 1 := by simp [q, e₁]
  have hs : Real.sqrt 2 ^ 3 = 2 * Real.sqrt 2 := by rw [pow_succ, Real.sq_sqrt (by norm_num)]
  have h00 := fderiv_fderiv_log_radial_barrier p q 0 hx e₀ e₀
  have h01 := fderiv_fderiv_log_radial_barrier p q 0 hx e₀ e₁
  have h11 := fderiv_fderiv_log_radial_barrier p q 0 hx e₁ e₁
  rw [hp, hq, hp0, hq0] at h00
  rw [hp, hq, hp0, hq0, hp1, hq1] at h01
  rw [hp, hq, hp1, hq1] at h11
  refine
    ⟨h00.1.trans ?_, h01.1.trans ?_, h11.1.trans ?_, h00.2.trans ?_, h01.2.trans ?_,
      h11.2.trans ?_⟩
  · norm_num
  · norm_num
  · norm_num
  · norm_num [hs]
  · norm_num [hs]
  · norm_num [hs]

/-- **The ambient line `ℝ¹`**, `p = 0`, `q = x₀`, `β = 0`, at a point with `x₀ > 0`. -/
theorem ambient_line_log_radial_client (x : EuclideanSpace ℝ (Fin 1)) (hx : 0 < x 0) :
    fderiv ℝ (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 1) =>
        -((EuclideanSpace.proj 0 : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ) y) *
          Real.log (((0 : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ) y - 0) ^ 2 +
            ((EuclideanSpace.proj 0 : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ) y) ^ 2))) x
        (EuclideanSpace.single 0 1) (EuclideanSpace.single 0 1) = -2 / x 0 ∧
      fderiv ℝ (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 1) =>
        Real.sqrt (((0 : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ) y - 0) ^ 2 +
            ((EuclideanSpace.proj 0 : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ) y) ^ 2))) x
        (EuclideanSpace.single 0 1) (EuclideanSpace.single 0 1) = 0 := by
  have hq : 0 < (EuclideanSpace.proj 0 : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ) x := hx
  obtain ⟨hL, hR⟩ := fderiv_fderiv_log_radial_barrier (G := EuclideanSpace ℝ (Fin 1)) 0
    (EuclideanSpace.proj 0) 0 hq (EuclideanSpace.single (0 : Fin 1) (1 : ℝ))
    (EuclideanSpace.single (0 : Fin 1) (1 : ℝ))
  refine ⟨?_, ?_⟩
  · rw [hL]
    simp
    field_simp
  · rw [hR]
    simp

end FunctionalInequalities.Analysis.LogRadialBarrierClient

#print axioms FunctionalInequalities.Analysis.LogRadialBarrierClient.off_axis_log_radial_client
#print axioms FunctionalInequalities.Analysis.LogRadialBarrierClient.ambient_line_log_radial_client
