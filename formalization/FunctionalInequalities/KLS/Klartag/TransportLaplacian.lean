import FunctionalInequalities.Analysis.BakryEmery.MongeAmpere
import FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.Basic

/-!
# The Laplacian of `(ℝⁿ, ∇²ψ, e^{-W} dx)` in moment coordinates

Klartag, *Logarithmically-concave moment measures I*, arXiv:1309.2767v1, Lemma 4.3. Under the
transport equation (50) `e^{-ρ(∇ψ)} det ∇²ψ = e^{-W}` (written `log det ∇²ψ = -W + ρ(∇ψ)`), with
`ψ`, `W` smooth, `∇²ψ` positive definite and `ρ` smooth on an open set containing `∇ψ(ℝⁿ)`, the
operator (56) `L u = ψ^{ij} u_ij - Σ_j ρ_j(∇ψ) u_j` (`hessianInverseOperator ψ ρ`) is the Laplacian
of the weighted manifold `(ℝⁿ, ∇²ψ, e^{-W} dx)` in the sense of (53)–(54):
`∫ (Lu) v e^{-W} dx = -∫ ψ^{ij} u_i v_j e^{-W} dx` for smooth `u`, `v`, one of them compactly
supported (`MomentMeasure.integral_hessianInverseOperator_mul_eq_neg_weighted`).

The convexity of `ψ` and conditions (49), (51) of Proposition 4.1 are not used; positive
definiteness of `∇²ψ` is the consequence the proof needs. Stochastic completeness (Proposition 4.1)
is not provided. Lemma 4.4 is in `KLS/Klartag/GeneratorBound.lean`.

The case `W = ψ` is Letwin's chain
(`BakryEmery.inverseHessian_divergence`, `density_inverseHessian_divergence`,
`density_hessianInverseOperator_flux` in `Analysis/BakryEmery/MongeAmpere.lean` and
`integral_hessianInverseOperator_mul_eq_neg` in `IntegrationByParts/InverseHessian/Basic.lean`).
-/

noncomputable section
open MeasureTheory
open scoped ContDiff RealInnerProductSpace

namespace FunctionalInequalities.Probability.MomentMeasure

open FunctionalInequalities.Analysis FunctionalInequalities.Analysis.BakryEmery

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

local notation "e" => stdOrthonormalBasis ℝ E
local notation "dimE" => Module.finrank ℝ E

/-- First derivative of (50): `Σ_ac ψ^{ac} ∂_i ψ_ac = -∂_i W + Σ_a ρ_a(∇ψ) ψ_ai`. -/
private theorem transport_first_derivative {ψ W ρ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hW : ContDiff ℝ ∞ W) {K : Set E} (hK : IsOpen K) (hρ : ContDiffOn ℝ ∞ ρ K)
    (hEq : ∀ y, logDetHessian ψ e y = -W y + ρ (gradient ψ y))
    {x : E} (hx : gradient ψ x ∈ K)
    (hPD : ∀ v : E, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ ψ x v v) (i : Fin dimE) :
    (∑ a, ∑ c, inverseHessianEntry ψ e x a c *
      fderiv ℝ (fun y => bilinearIteratedFDerivTwo ℝ ψ y (e a) (e c)) x (e i)) =
      -fderiv ℝ W x (e i) + ∑ a, fderiv ℝ ρ (gradient ψ x) (e a) *
        bilinearIteratedFDerivTwo ℝ ψ x (e a) (e i) := by
  have h2 : ContDiff ℝ 2 ψ := hψ.of_le (WithTop.coe_le_coe.mpr le_top)
  have heq : logDetHessian ψ e = fun y => -W y + ρ (gradient ψ y) := funext hEq
  have hg : ContDiff ℝ ∞ (gradient ψ) := contDiff_gradient hψ (by simp)
  have hWd := hW.differentiable (by simp) x
  have hρx := (hρ.contDiffAt (hK.mem_nhds hx)).differentiableAt (by simp)
  have hcomp := (contDiffAt_comp_gradient_of_mem hψ hK hρ hx).differentiableAt (by simp)
  rw [← fderiv_logDetHessian_eq_sum e hψ x hPD (e i), heq,
    fderiv_fun_add (f := fun y => -W y) (g := fun y => ρ (gradient ψ y)) hWd.neg hcomp,
    fderiv_fun_neg]
  have hc : fderiv ℝ (fun y => ρ (gradient ψ y)) x =
      fderiv ℝ ρ (gradient ψ x) ∘L fderiv ℝ (gradient ψ) x :=
    fderiv_comp x hρx (hg.differentiable (by simp) x)
  rw [hc]
  simp only [add_apply, neg_apply, ContinuousLinearMap.comp_apply]
  congr 1
  change fderiv ℝ ρ (gradient ψ x) (hessianOperator ψ x (e i)) = _
  conv_lhs => rw [← (e).sum_repr' (hessianOperator ψ x (e i))]
  simp only [map_sum, map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro a _ha
  change operatorEntry e (hessianOperator ψ x) a i * fderiv ℝ ρ (gradient ψ x) (e a) = _
  rw [operatorEntry_hessianOperator e h2 x a i]
  ring

/-- Divergence of the inverse Hessian under (50), Klartag (58): with `A = (∇²ψ)⁻¹`,
`Σ_i ∂_i A_{ij} = Σ_i A_{ij} ∂_i W - ∂_j ρ(∇ψ)`. -/
private theorem transport_inverseHessian_divergence {ψ W ρ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hW : ContDiff ℝ ∞ W) {K : Set E} (hK : IsOpen K)
    (hρ : ContDiffOn ℝ ∞ ρ K)
    (hEq : ∀ y, logDetHessian ψ e y = -W y + ρ (gradient ψ y))
    {x : E} (hx : gradient ψ x ∈ K)
    (hPD : ∀ v : E, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ ψ x v v) (j : Fin dimE) :
    (∑ i, fderiv ℝ (fun y => inverseHessianEntry ψ e y i j) x (e i)) =
      (∑ i, inverseHessianEntry ψ e x i j * fderiv ℝ W x (e i)) -
        fderiv ℝ ρ (gradient ψ x) (e j) := by
  have h2 : ContDiff ℝ 2 ψ := hψ.of_le (WithTop.coe_le_coe.mpr le_top)
  have hHA (d : Fin dimE) :
      (∑ c, bilinearIteratedFDerivTwo ℝ ψ x (e d) (e c) * inverseHessianEntry ψ e x c j) =
        if d = j then 1 else 0 := by
    calc
      _ = ∑ c, inverseHessianEntry ψ e x j c * bilinearIteratedFDerivTwo ℝ ψ x (e c) (e d) := by
        apply Finset.sum_congr rfl
        intro c _hc
        rw [inverseHessianEntry_symm e h2 x c j, bilinearIteratedFDerivTwo_symm h2 x (e d) (e c)]
        ring
      _ = if j = d then 1 else 0 := sum_inverseHessianEntry_mul_hessian e h2 x hPD j d
      _ = _ := by simp only [eq_comm]
  calc
    _ = -(∑ i, ∑ a, ∑ c, inverseHessianEntry ψ e x i a *
        fderiv ℝ (fun y => bilinearIteratedFDerivTwo ℝ ψ y (e i) (e a)) x (e c) *
        inverseHessianEntry ψ e x c j) := by
      have hcyc (u v w : E) : fderiv ℝ (fun y => bilinearIteratedFDerivTwo ℝ ψ y u v) x w =
          fderiv ℝ (fun y => bilinearIteratedFDerivTwo ℝ ψ y w u) x v := by
        have he : (fun y => bilinearIteratedFDerivTwo ℝ ψ y u v) =
            (fun y => bilinearIteratedFDerivTwo ℝ ψ y v u) :=
          funext fun y => bilinearIteratedFDerivTwo_symm h2 y u v
        rw [he]
        exact fderiv_bilinearIteratedFDerivTwo_comm hψ x v u w
      simp_rw [fderiv_inverseHessianEntry_apply e hψ x hPD, hcyc]
      rw [Finset.sum_neg_distrib]
    _ = -(∑ c, (∑ i, ∑ a, inverseHessianEntry ψ e x i a *
        fderiv ℝ (fun y => bilinearIteratedFDerivTwo ℝ ψ y (e i) (e a)) x (e c)) *
        inverseHessianEntry ψ e x c j) := by
      congr 1
      calc
        _ = ∑ i, ∑ c, ∑ a, inverseHessianEntry ψ e x i a *
            fderiv ℝ (fun y => bilinearIteratedFDerivTwo ℝ ψ y (e i) (e a)) x (e c) *
            inverseHessianEntry ψ e x c j :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_comm
        _ = _ := by rw [Finset.sum_comm]; simp_rw [Finset.sum_mul]
    _ = -(∑ c, (-fderiv ℝ W x (e c) + ∑ d, fderiv ℝ ρ (gradient ψ x) (e d) *
        bilinearIteratedFDerivTwo ℝ ψ x (e d) (e c)) * inverseHessianEntry ψ e x c j) := by
      congr 1
      apply Finset.sum_congr rfl
      intro c _hc
      rw [transport_first_derivative hψ hW hK hρ hEq hx hPD c]
    _ = (∑ c, inverseHessianEntry ψ e x c j * fderiv ℝ W x (e c)) -
        ∑ d, fderiv ℝ ρ (gradient ψ x) (e d) *
          (∑ c, bilinearIteratedFDerivTwo ℝ ψ x (e d) (e c) * inverseHessianEntry ψ e x c j) := by
      simp_rw [add_mul, Finset.sum_add_distrib, neg_mul, Finset.sum_neg_distrib,
        Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm (f := fun c d => _)]
      simp only [neg_add, neg_neg, sub_eq_add_neg]
      congr 1
      · apply Finset.sum_congr rfl; intro c _hc; ring
      · congr 1
        apply Finset.sum_congr rfl; intro d _hd
        apply Finset.sum_congr rfl; intro c _hc; ring
    _ = _ := by
      simp_rw [hHA]
      simp

/-- Flux form: `Σ_i ∂_i (e^{-W} A_{ij}) = -e^{-W} ∂_j ρ(∇ψ)`. -/
private theorem transport_density_inverseHessian_divergence {ψ W ρ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hW : ContDiff ℝ ∞ W) {K : Set E} (hK : IsOpen K)
    (hρ : ContDiffOn ℝ ∞ ρ K)
    (hEq : ∀ y, logDetHessian ψ e y = -W y + ρ (gradient ψ y))
    {x : E} (hx : gradient ψ x ∈ K)
    (hPD : ∀ v : E, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ ψ x v v) (j : Fin dimE) :
    (∑ i, fderiv ℝ (fun y => Real.exp (-W y) * inverseHessianEntry ψ e y i j) x (e i)) =
      -Real.exp (-W x) * fderiv ℝ ρ (gradient ψ x) (e j) := by
  have hw := (hW.neg.exp).differentiable (by simp) x
  have hA (i : Fin dimE) := (contDiffAt_inverseHessianEntry e hψ x hPD i j).differentiableAt (by simp)
  have hexp (v : E) : fderiv ℝ (fun y => Real.exp (-W y)) x v =
      -Real.exp (-W x) * fderiv ℝ W x v := by
    have hd : HasFDerivAt (fun y => Real.exp (-W y)) (Real.exp (-W x) • -fderiv ℝ W x) x := by
      simpa only [Pi.neg_apply] using (hW.differentiable (by simp) x).hasFDerivAt.neg.exp
    rw [hd.fderiv]
    simp only [smul_apply, neg_apply, smul_eq_mul]
    ring
  simp_rw [fderiv_mul_apply hw (hA _), hexp]
  rw [Finset.sum_add_distrib]
  have he : (∑ i, inverseHessianEntry ψ e x i j *
      (-Real.exp (-W x) * fderiv ℝ W x (e i))) =
      -Real.exp (-W x) * ∑ i, inverseHessianEntry ψ e x i j * fderiv ℝ W x (e i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _hi; ring
  rw [he, ← Finset.mul_sum, transport_inverseHessian_divergence hψ hW hK hρ hEq hx hPD j]
  ring

/-- Divergence form of (56): `Σ_{ij} ∂_i (e^{-W} A_{ij} ∂_j f) = e^{-W} L f`, with
`L f = Σ_{ij} A_{ij} ∂_{ij} f - Σ_i ∂_i ρ(∇ψ) ∂_i f`. -/
private theorem transport_density_hessianInverseOperator_flux {ψ W ρ f : E → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hW : ContDiff ℝ ∞ W)
    (hf : ContDiff ℝ ∞ f) {K : Set E} (hK : IsOpen K) (hρ : ContDiffOn ℝ ∞ ρ K)
    (hEq : ∀ y, logDetHessian ψ e y = -W y + ρ (gradient ψ y))
    {x : E} (hx : gradient ψ x ∈ K)
    (hPD : ∀ v : E, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ ψ x v v) :
    (∑ i, ∑ j, fderiv ℝ (fun y => Real.exp (-W y) *
      inverseHessianEntry ψ e y i j *
      fderiv ℝ f y (e j)) x (e i)) =
      Real.exp (-W x) * hessianInverseOperator ψ ρ f x := by
  have hf2 : ContDiff ℝ 2 f := hf.of_le (WithTop.coe_le_coe.mpr le_top)
  have hw := (hW.neg.exp).differentiable (by simp) x
  have hA (i j : Fin (Module.finrank ℝ E)) :=
    (contDiffAt_inverseHessianEntry e hψ x hPD i j).differentiableAt (by simp)
  have hwa (i j : Fin (Module.finrank ℝ E)) : DifferentiableAt ℝ
      (fun y => Real.exp (-W y) * inverseHessianEntry ψ e y i j) x := by
    exact hw.fun_mul (hA i j)
  have hdf (j : Fin (Module.finrank ℝ E)) :=
    (contDiff_fderiv_apply hf (m := ∞) (by simp) (e j)).differentiable (by simp) x
  have hFirst :
      (∑ i, ∑ j, (Real.exp (-W x) * inverseHessianEntry ψ e x i j) *
        bilinearIteratedFDerivTwo ℝ f x (e i) (e j)) =
        Real.exp (-W x) * ∑ i, ∑ j, inverseHessianEntry ψ e x i j *
          bilinearIteratedFDerivTwo ℝ f x (e i) (e j) := by
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _hi
    apply Finset.sum_congr rfl; intro j _hj; ring
  have hSecond :
      (∑ i, ∑ j, fderiv ℝ f x (e j) *
        fderiv ℝ (fun y => Real.exp (-W y) * inverseHessianEntry ψ e y i j) x (e i)) =
        -Real.exp (-W x) * ∑ j, fderiv ℝ ρ (gradient ψ x) (e j) * fderiv ℝ f x (e j) := by
    rw [Finset.sum_comm]
    calc
      _ = ∑ j, fderiv ℝ f x (e j) * ∑ i,
          fderiv ℝ (fun y => Real.exp (-W y) * inverseHessianEntry ψ e y i j) x (e i) := by
        simp_rw [Finset.mul_sum]
      _ = _ := by
        simp_rw [transport_density_inverseHessian_divergence hψ hW hK hρ hEq hx hPD]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro j _hj; ring
  calc
    _ = ∑ i, ∑ j,
        ((Real.exp (-W x) * inverseHessianEntry ψ e x i j) *
          bilinearIteratedFDerivTwo ℝ f x (e i) (e j) +
          fderiv ℝ f x (e j) *
          fderiv ℝ (fun y => Real.exp (-W y) * inverseHessianEntry ψ e y i j) x (e i)) := by
      apply Finset.sum_congr rfl; intro i _hi
      apply Finset.sum_congr rfl; intro j _hj
      rw [fderiv_mul_apply (hwa i j) (hdf j),
        ← bilinearIteratedFDerivTwo_eq_fderiv_apply hf2]
    _ = _ := by
      simp_rw [Finset.sum_add_distrib]
      rw [hFirst, hSecond]
      change _ = Real.exp (-W x) *
        ((∑ i, ∑ j, inverseHessianEntry ψ e x i j *
          bilinearIteratedFDerivTwo ℝ f x (e i) (e j)) -
          ∑ i, fderiv ℝ ρ (gradient ψ x) (e i) * fderiv ℝ f x (e i))
      ring


/-- **Klartag arXiv:1309.2767v1, Lemma 4.3.** Let `ψ` be smooth with positive definite Hessian,
`W` smooth, `ρ` smooth on an open `K ⊇ ∇ψ(ℝⁿ)`, and let the transport equation (50)
`e^{-ρ(∇ψ)} det ∇²ψ = e^{-W}` hold, written `log det ∇²ψ = -W + ρ(∇ψ)`. Then the operator (56)
`L u = ψ^{ij} u_ij - Σ_j ρ_j(∇ψ) u_j` is the Laplacian of `(ℝⁿ, ∇²ψ, e^{-W} dx)` in the sense of
(53)–(54): `∫ (Lu) v e^{-W} = -∫ ψ^{ij} u_i v_j e^{-W}` for smooth `u`, `v`, one of them compactly
supported. -/
theorem integral_hessianInverseOperator_mul_eq_neg_weighted [MeasurableSpace E] [BorelSpace E]
    (m : Measure E) [m.IsAddHaarMeasure]
    {ψ W ρ u v : E → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hW : ContDiff ℝ ∞ W)
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) (hc : HasCompactSupport u ∨ HasCompactSupport v)
    {K : Set E} (hK : IsOpen K) (hρ : ContDiffOn ℝ ∞ ρ K) (hRange : ∀ x, gradient ψ x ∈ K)
    (hEq : ∀ y, logDetHessian ψ e y = -W y + ρ (gradient ψ y))
    (hPD : ∀ x, ∀ w : E, w ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ ψ x w w) :
    (∫ x, Real.exp (-W x) * (hessianInverseOperator ψ ρ u x * v x) ∂m) =
      -∫ x, Real.exp (-W x) * (∑ i, ∑ j, inverseHessianEntry ψ e x i j *
        fderiv ℝ u x (e i) * fderiv ℝ v x (e j)) ∂m := by
  let F (i j : Fin dimE) : E → ℝ := fun x =>
    Real.exp (-W x) * inverseHessianEntry ψ e x i j * fderiv ℝ u x (e j)
  have hF (i j : Fin dimE) : ContDiff ℝ ∞ (F i j) := by
    exact ((hW.neg.exp).mul (contDiff_inverseHessianEntry e hψ hPD i j)).mul
      (contDiff_fderiv_apply hu (by simp) (e j))
  have hFc (i j : Fin dimE) : HasCompactSupport (F i j) ∨ HasCompactSupport v := by
    rcases hc with huc | hvc
    · left
      exact (huc.fderiv_apply ℝ (e j)).mul_left
    · exact Or.inr hvc
  have hi (i j : Fin dimE) :=
    integrable_fderiv_mul_of_hasCompactSupport m (hF i j) hv (hFc i j) (e i)
  have hRow1 (i : Fin dimE) : Integrable (fun x => ∑ j, fderiv ℝ (F i j) x (e i) * v x) m :=
    integrable_finsetSum Finset.univ (fun j _ => (hi i j).1)
  have hRow2 (i : Fin dimE) : Integrable (fun x => ∑ j, F i j x * fderiv ℝ v x (e i)) m :=
    integrable_finsetSum Finset.univ (fun j _ => (hi i j).2.1)
  calc
    _ = ∫ x, ∑ i, ∑ j, fderiv ℝ (F i j) x (e i) * v x ∂m := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [← mul_assoc, ← transport_density_hessianInverseOperator_flux hψ hW hu hK hρ hEq
        (hRange x) (hPD x)]
      simp only [Finset.sum_mul, F]
    _ = ∑ i, ∑ j, ∫ x, fderiv ℝ (F i j) x (e i) * v x ∂m := by
      rw [integral_finsetSum _ (fun i _ => hRow1 i)]
      apply Finset.sum_congr rfl; intro i _hi
      exact integral_finsetSum _ (fun j _ => (hi i j).1)
    _ = ∑ i, ∑ j, -∫ x, F i j x * fderiv ℝ v x (e i) ∂m := by
      apply Finset.sum_congr rfl; intro i _hi
      apply Finset.sum_congr rfl; intro j _hj
      exact integral_fderiv_mul_eq_neg_of_hasCompactSupport m (hF i j) hv (hFc i j) (e i)
    _ = -∫ x, ∑ i, ∑ j, F i j x * fderiv ℝ v x (e i) ∂m := by
      rw [integral_finsetSum _ (fun i _ => hRow2 i)]
      simp_rw [integral_finsetSum _ (fun j _ => (hi _ j).2.1)]
      simp only [Finset.sum_neg_distrib]
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with x
      rw [Finset.sum_comm]
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro i _hi
      apply Finset.sum_congr rfl; intro j _hj
      dsimp [F]
      rw [inverseHessianEntry_symm e (hψ.of_le (WithTop.coe_le_coe.mpr le_top)) x j i]
      ring

end FunctionalInequalities.Probability.MomentMeasure
