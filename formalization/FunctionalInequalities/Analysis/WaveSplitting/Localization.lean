module

public import FunctionalInequalities.Analysis.WaveSplitting.Stability
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-! # Compact localization of smooth splitting coefficients -/

@[expose] public section
noncomputable section
open scoped ContDiff
namespace FunctionalInequalities.Analysis.WaveSplitting
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ι : Type*} [Fintype ι]

/-- Compact smooth coefficients have bounded scalar derivatives at each finite order. -/
theorem exists_wordDerivative_bound (a : ι → E) (k : ℕ) {b : ι → E → ℝ}
    (hb : ∀ j, ContDiff ℝ ∞ (b j)) (hc : ∀ j, HasCompactSupport (b j)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ j r, r.length ≤ k → ∀ x, wordDerivative a r (b j) x ^ 2 ≤ B := by
  have hn :
    ∀ n : ℕ,
      ∃ B : ℝ, 0 ≤ B ∧ ∀ j (w : Fin n → ι) x, derivative (fun i => a (w i)) (b j) x ^ 2 ≤ B := by
    intro n
    have hbnd :
      ∀ p : ι × (Fin n → ι), ∃ M : ℝ, ∀ x, ‖derivative (fun i => a (p.2 i)) (b p.1) x‖ ≤ M :=
      fun p =>
      (hasCompactSupport_derivative _ (hc p.1)).exists_bound_of_continuous
        (continuous_derivative _ (hb p.1))
    choose M hM using hbnd
    refine ⟨∑ p : ι × (Fin n → ι), (max (M p) 0) ^ 2, by positivity, ?_⟩
    intro j w x
    have hm := (hM (j, w) x).trans (le_max_left (M (j, w)) 0)
    have hsq : derivative (fun i => a (w i)) (b j) x ^ 2 ≤ (max (M (j, w)) 0) ^ 2 := by
      rw [Real.norm_eq_abs] at hm
      nlinarith [sq_abs (derivative (fun i => a (w i)) (b j) x),
        abs_nonneg (derivative (fun i => a (w i)) (b j) x), le_max_right (M (j, w)) 0]
    exact
      hsq.trans
        (Finset.single_le_sum (fun p _ => sq_nonneg (max (M p) 0)) (Finset.mem_univ (j, w)))
  choose B hB hbound using hn
  refine ⟨∑ n ∈ Finset.range (k + 1), B n, Finset.sum_nonneg (fun n _ => hB n), ?_⟩
  intro j r hr x
  have he := congrFun (wordDerivative_ofFn a r.get (hb j)) x
  rw [List.ofFn_get] at he
  rw [he]
  exact
    (hbound r.length j r.get x).trans
      (Finset.single_le_sum (fun n _ => hB n) (Finset.mem_range.mpr (by omega)))

/-- Localize a smooth coefficient without imposing any global bound on it. The same cutoff
works for every finite derivative order and every finite family of directions. -/
theorem exists_localized_coefficient [FiniteDimensional ℝ E]
    (b : ι → E → ℝ) (hb : ∀ j, ContDiff ℝ ∞ (b j)) (R : ℝ) :
    ∃ c : ι → E → ℝ, (∀ j, ContDiff ℝ ∞ (c j)) ∧
      (∀ j, HasCompactSupport (c j)) ∧
      (∀ j x, ‖x‖ ≤ R → c j x = b j x) ∧
      (∀ (a : ι → E) k, ∃ B : ℝ, 0 ≤ B ∧
        ∀ j r, r.length ≤ k → ∀ x, wordDerivative a r (c j) x ^ 2 ≤ B) := by
  let χ : ContDiffBump (0 : E) := ⟨max R 0 + 1, max R 0 + 2, by positivity, by linarith⟩
  let c : ι → E → ℝ := fun j x => χ x * b j x
  have hs : ∀ j, ContDiff ℝ ∞ (c j) := fun j => χ.contDiff.mul (hb j)
  have hc : ∀ j, HasCompactSupport (c j) := fun j => χ.hasCompactSupport.mul_right
  refine ⟨c, hs, hc, ?_, fun a k => exists_wordDerivative_bound a k hs hc⟩
  intro j x hx
  have hone : χ x = 1 := χ.one_of_mem_closedBall (by
    change dist x 0 ≤ max R 0 + 1
    rw [dist_zero_right]
    linarith [le_max_left R 0])
  simp only [c, hone, one_mul]

omit [NormedSpace ℝ E] in
/-- A reaction on a supported state sees only the coefficient on that support ball. -/
theorem reaction_eq_of_supported {Y : State E ι} {R : ℝ} (hY : Y.Supported R)
    {b c : ι → E → ℝ} (hbc : ∀ j x, ‖x‖ ≤ R → b j x = c j x) (t : ℝ) :
    reaction b t Y = reaction c t Y := by
  have he : coupling b Y = coupling c Y := by
    funext x
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hx : ‖x‖ ≤ R
    · rw [hbc j x hx]
    · simp only [(hY x (lt_of_not_ge hx)).2.2 j, mul_zero]
  simp only [reaction, he]

/-- Agreement on the propagated support suffices for one complete split step. -/
theorem step_eq_of_supported [DecidableEq ι] {Y : State E ι} {R T : ℝ}
    (hY : Y.Supported R) (a : ι → E) (js : List ι) {b c : ι → E → ℝ}
    (hbc : ∀ j x, ‖x‖ ≤ T → b j x = c j x) (t : ℝ)
    (hRT : R + |t| * travel a js ≤ T) : step a b js t Y = step a c js t Y :=
  reaction_eq_of_supported ((hY.sweep a t js).mono hRT) hbc t

/-- The entire finite grid is unchanged by localization on its common propagation ball. -/
theorem nodes_eq_of_supported [DecidableEq ι] {Y : State E ι} {R T δ : ℝ}
    (hY : Y.Supported R) (a : ι → E) (js : List ι) {b c : ι → E → ℝ} (N : ℕ)
    (hbc : ∀ j x, ‖x‖ ≤ T → b j x = c j x)
    (hRT : R + N * (|δ| * travel a js) ≤ T) (k : ℕ) (hk : k ≤ N) :
    nodes a b js δ Y k = nodes a c js δ Y k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have he := step_eq_of_supported (hY.nodes a b js δ k) a js hbc δ
      (show R + k * (|δ| * travel a js) + |δ| * travel a js ≤ T from
        (by
          have hm := mul_le_mul_of_nonneg_right (show (k + 1 : ℝ) ≤ N by exact_mod_cast hk)
            (mul_nonneg (abs_nonneg δ) (travel_nonneg a js))
          nlinarith))
    change step a b js δ (nodes a b js δ Y k) = step a c js δ (nodes a c js δ Y k)
    rw [he, ih (by omega)]

/-- Every actual smooth cell, not just the grid values, is unchanged by localization. -/
theorem cell_eq_of_supported [DecidableEq ι] {Y : State E ι} {R T δ θ : ℝ}
    (hY : Y.Supported R) (a : ι → E) (js : List ι) {b c : ι → E → ℝ} (N : ℕ)
    (hbc : ∀ j x, ‖x‖ ≤ T → b j x = c j x)
    (hRT : R + N * (|δ| * travel a js) ≤ T) (k : ℕ) (hk : k < N)
    (hθ : |θ| ≤ |δ|) : cell a b js δ Y k θ = cell a c js δ Y k θ := by
  have ht := travel_nonneg a js
  have he := step_eq_of_supported (hY.nodes a b js δ k) a js hbc θ
    (show R + k * (|δ| * travel a js) + |θ| * travel a js ≤ T from
      (by
        have hm := mul_le_mul_of_nonneg_right (show (k + 1 : ℝ) ≤ N by exact_mod_cast hk)
          (mul_nonneg (abs_nonneg δ) ht)
        have hθ' := mul_le_mul_of_nonneg_right hθ ht
        nlinarith))
  change step a b js θ (nodes a b js δ Y k) = step a c js θ (nodes a c js δ Y k)
  rw [he, nodes_eq_of_supported hY a js N hbc hRT k hk.le]

section Integration
open MeasureTheory
variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (m : Measure E) [IsFiniteMeasureOnCompacts m] [m.IsAddRightInvariant]

/-- Original smooth coefficients have a fixed-horizon, mesh-uniform energy bound at every
finite order. No global coefficient or derivative bound is assumed. -/
theorem exists_cell_energy_bound [DecidableEq ι] (a : ι → E) (js : List ι)
    {b : ι → E → ℝ} (hb : ∀ j, ContDiff ℝ ∞ (b j)) {Y : State E ι}
    (hY : Y.Smooth) {R : ℝ} (hR : Y.Supported R) (order : ℕ) (L : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (δ : ℝ), 0 ≤ δ → δ ≤ 1 → (N : ℝ) * δ ≤ L →
      ∀ (k : ℕ), k < N → ∀ θ : ℝ, 0 ≤ θ → θ ≤ δ →
        derivativeEnergy m a order (cell a b js δ Y k θ) ≤
          Real.exp (C * L) * derivativeEnergy m a order Y := by
  obtain ⟨c, hcs, _, heq, hbounds⟩ := exists_localized_coefficient b hb (R + L * travel a js)
  obtain ⟨B, hB, hcB⟩ := hbounds a order
  let C := 1 + 4 * couplingConstant (ι := ι) order B
  have hC : 0 ≤ C := by dsimp [C, couplingConstant]; positivity
  refine ⟨C, hC, ?_⟩
  intro N δ hδ hδ1 hL k hk θ hθ hθδ
  have hprop : R + N * (|δ| * travel a js) ≤ R + L * travel a js := by
    rw [abs_of_nonneg hδ]
    nlinarith [mul_le_mul_of_nonneg_right hL (travel_nonneg a js)]
  have he := cell_eq_of_supported (θ := θ) hR a js N (fun j x hx => (heq j x hx).symm)
    hprop k hk (by simpa [abs_of_nonneg hθ, abs_of_nonneg hδ] using hθδ)
  rw [he]
  have h := derivativeEnergy_cell_le_exp m a order js hcs hY hR.hasCompactSupport
    hB hcB hδ hδ1 hθ (hθδ.trans hδ1) k
  apply h.trans
  apply mul_le_mul_of_nonneg_right _
    (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => energy_nonneg m _)
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left _ hC
  have hkn : (k + 1 : ℝ) ≤ N := by exact_mod_cast hk
  nlinarith [mul_le_mul_of_nonneg_right hkn hδ]

end Integration
end FunctionalInequalities.Analysis.WaveSplitting
