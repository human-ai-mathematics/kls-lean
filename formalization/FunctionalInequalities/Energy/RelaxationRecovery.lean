import FunctionalInequalities.Energy.FormCore
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Recovery sequences for sequential relaxation

At every finite point, the infimum defining a sequential relaxation admits a diagonal recovery
sequence. At a point where the relaxation is `⊤`, such a sequence need not exist: for example,
the concrete test type may be empty. A dense realization supplies the missing approximating
sequence and therefore gives recovery sequences at every point, including points of infinite
relaxed energy.

These conclusions use only the pseudometric structure and, for the all-points result, density of
the realization. They do not require a quadratic law, closability, or a Markov property.
-/

noncomputable section

open Filter Topology

namespace FunctionalInequalities.Energy

namespace PreEnergy

universe u

variable {X : Type u} [PseudoMetricSpace X] (P : PreEnergy X)

/-- Every finite point of a sequential relaxation has a recovery sequence.

The proof chooses, for each precision, an approximating sequence whose `liminf` is nearly
minimal and then one sufficiently late concrete test from that sequence.
-/
theorem hasRecoverySequenceAt_sequentialRelaxation_of_finiteAt {x : X}
    (hfinite : P.sequentialRelaxation.FiniteAt x) :
    P.HasRecoverySequenceAt P.sequentialRelaxation x := by
  let metricError : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1)
  let energyError : ℕ → ENNReal := fun n ↦ ((n : NNReal) : ENNReal)⁻¹
  have metricError_pos : ∀ n, 0 < metricError n := by
    intro n
    dsimp [metricError]
    positivity
  have energyError_pos : ∀ n, 0 < energyError n := by
    intro n
    simp [energyError]
  have exists_test : ∀ n, ∃ f : P.Test,
      dist x (P.toAmbient f) < metricError n ∧
        (P.energy f : ENNReal) < P.sequentialRelaxation x + energyError n := by
    intro n
    have hrelaxed :
        P.sequentialRelaxation x < P.sequentialRelaxation x + energyError n :=
      ENNReal.lt_add_right hfinite (energyError_pos n).ne'
    rw [P.sequentialRelaxation_apply, iInf_lt_iff] at hrelaxed
    obtain ⟨approximation, henergy⟩ := hrelaxed
    have happ_tendsto := approximation.2
    have hnear : ∀ᶠ k : ℕ in atTop,
        dist x (P.toAmbient (approximation.1 k)) < metricError n := by
      rw [Metric.tendsto_atTop] at happ_tendsto
      obtain ⟨N, hN⟩ := happ_tendsto (metricError n) (metricError_pos n)
      exact eventually_atTop.2 ⟨N, fun k hk ↦ by simpa [dist_comm] using hN k hk⟩
    have hlow : ∃ᶠ k : ℕ in atTop,
        (P.energy (approximation.1 k) : ENNReal) <
          P.sequentialRelaxation x + energyError n :=
      frequently_lt_of_liminf_lt (by isBoundedDefault) henergy
    obtain ⟨k, hk_energy, hk_near⟩ := (hlow.and_eventually hnear).exists
    exact ⟨approximation.1 k, hk_near, hk_energy⟩
  choose test htest_near htest_energy using exists_test
  have metricError_tendsto : Tendsto metricError atTop (𝓝 0) := by
    simpa [metricError] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hdist :
      Tendsto (fun n ↦ dist x (P.toAmbient (test n))) atTop (𝓝 0) := by
    apply Filter.Tendsto.squeeze tendsto_const_nhds metricError_tendsto
    · intro n
      exact dist_nonneg
    · intro n
      exact (htest_near n).le
  have htest_tendsto : Tendsto (fun n ↦ P.toAmbient (test n)) atTop (𝓝 x) :=
    tendsto_of_tendsto_of_dist tendsto_const_nhds hdist
  let approximation : P.ApproximatingSequence x := ⟨test, htest_tendsto⟩
  have energyError_tendsto : Tendsto energyError atTop (𝓝 0) := by
    simpa [energyError] using ENNReal.tendsto_inv_nat_nhds_zero
  have hupper_tendsto :
      Tendsto (fun n ↦ P.sequentialRelaxation x + energyError n) atTop
        (𝓝 (P.sequentialRelaxation x)) := by
    simpa using (tendsto_const_nhds.add energyError_tendsto)
  have hlower :
      P.sequentialRelaxation x ≤
        liminf (fun n ↦ (P.energy (test n) : ENNReal)) atTop :=
    P.sequentialRelaxation_le_sequenceEnergy approximation
  have hupper :
      limsup (fun n ↦ (P.energy (test n) : ENNReal)) atTop ≤
        P.sequentialRelaxation x := by
    refine (limsup_le_limsup (Eventually.of_forall fun n ↦ (htest_energy n).le)).trans_eq ?_
    exact hupper_tendsto.limsup_eq
  exact ⟨approximation, tendsto_of_le_liminf_of_limsup_le hlower hupper⟩

/-- At an infinite-energy point, density supplies an approximating sequence; its energy must
converge to `⊤` because the relaxed energy is the infimum of all sequence `liminf`s. -/
private theorem hasRecoverySequenceAt_sequentialRelaxation_of_eq_top {x : X}
    (hDense : P.DenseRealization) (htop : P.sequentialRelaxation x = ⊤) :
    P.HasRecoverySequenceAt P.sequentialRelaxation x := by
  let metricError : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1)
  have metricError_pos : ∀ n, 0 < metricError n := by
    intro n
    dsimp [metricError]
    positivity
  have exists_test : ∀ n, ∃ f : P.Test,
      dist x (P.toAmbient f) < metricError n := by
    intro n
    obtain ⟨_, ⟨f, rfl⟩, hf⟩ := hDense.exists_dist_lt x (metricError_pos n)
    exact ⟨f, hf⟩
  choose test htest_near using exists_test
  have metricError_tendsto : Tendsto metricError atTop (𝓝 0) := by
    simpa [metricError] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hdist :
      Tendsto (fun n ↦ dist x (P.toAmbient (test n))) atTop (𝓝 0) := by
    apply Filter.Tendsto.squeeze tendsto_const_nhds metricError_tendsto
    · intro n
      exact dist_nonneg
    · intro n
      exact (htest_near n).le
  have htest_tendsto : Tendsto (fun n ↦ P.toAmbient (test n)) atTop (𝓝 x) :=
    tendsto_of_tendsto_of_dist tendsto_const_nhds hdist
  let approximation : P.ApproximatingSequence x := ⟨test, htest_tendsto⟩
  have hlower : ⊤ ≤ P.sequenceEnergy approximation := by
    simpa only [htop] using P.sequentialRelaxation_le_sequenceEnergy approximation
  have henergy :
      Tendsto (fun n ↦ (P.energy (test n) : ENNReal)) atTop (𝓝 ⊤) :=
    tendsto_of_le_liminf_of_limsup_le hlower le_top
      (by isBoundedDefault) (by isBoundedDefault)
  refine ⟨approximation, ?_⟩
  simpa only [htop] using henergy

/-- A dense concrete realization gives a recovery sequence for the sequential relaxation at
every ambient point.

Density is genuinely needed for the `⊤` branch: with an empty test type there is no
approximating sequence at all, while the defining infimum of the relaxation is still `⊤`.
-/
theorem hasRecoverySequenceAt_sequentialRelaxation
    (hDense : P.DenseRealization) (x : X) :
    P.HasRecoverySequenceAt P.sequentialRelaxation x := by
  by_cases hfinite : P.sequentialRelaxation.FiniteAt x
  · exact P.hasRecoverySequenceAt_sequentialRelaxation_of_finiteAt hfinite
  · have htop : P.sequentialRelaxation x = ⊤ := by
      change ¬ P.sequentialRelaxation x ≠ ⊤ at hfinite
      exact not_ne_iff.mp hfinite
    exact P.hasRecoverySequenceAt_sequentialRelaxation_of_eq_top hDense htop

end PreEnergy

end FunctionalInequalities.Energy
