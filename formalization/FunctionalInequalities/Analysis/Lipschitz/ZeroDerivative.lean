module

public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.Analysis.Calculus.ContDiff.Basic

/-! # Small Lipschitz pieces on a vanishing-derivative set

The derivative-zero set of a C1 map admits disjoint measurable pieces on which
the map has any prescribed positive Lipschitz bound. This is a zero-derivative
property, not a rank-deficient or critical-value theorem.
-/

@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped NNReal ContDiff
namespace FunctionalInequalities.Analysis

theorem exists_lipschitzOnWith_cover_of_fderiv_eq_zero
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    [SecondCountableTopology W] {u : V → W} (hu : ContDiff ℝ 1 u) {ε : ℝ≥0} (hε : ε ≠ 0) :
    ∃ T : ℕ → Set V, Pairwise (Function.onFun Disjoint T) ∧ (∀ n, MeasurableSet (T n)) ∧
      {x : V | fderiv ℝ u x = 0} ⊆ ⋃ n, T n ∧
      ∀ n, LipschitzOnWith ε u ({x : V | fderiv ℝ u x = 0} ∩ T n) := by
  rcases Set.eq_empty_or_nonempty {x : V | fderiv ℝ u x = 0} with hC | hC
  · refine ⟨fun _ => ∅, fun i j _ => by simp, fun _ => MeasurableSet.empty, by simp [hC], ?_⟩
    intro n
    simp only [Set.inter_empty]
    exact LipschitzOnWith.of_dist_le_mul fun x hx => absurd hx (Set.notMem_empty x)
  obtain ⟨T, A, hdisj, hmeas, hcov, happrox, hA⟩ :=
    exists_partition_approximatesLinearOn_of_hasFDerivWithinAt u {x : V | fderiv ℝ u x = 0}
      (fderiv ℝ u) (fun x _ => ((hu.differentiable one_ne_zero) x).hasFDerivAt.hasFDerivWithinAt)
      (fun _ => ε) (fun _ => hε)
  refine ⟨T, hdisj, hmeas, hcov, fun n => ?_⟩
  obtain ⟨y, hy, hAy⟩ := hA hC n
  have hA0 : A n = 0 := by rw [hAy]; exact hy
  refine LipschitzOnWith.of_dist_le_mul fun x hx y' hy' => ?_
  have h := happrox n x hx y' hy'
  rw [hA0] at h
  simpa [dist_eq_norm] using h


end FunctionalInequalities.Analysis
