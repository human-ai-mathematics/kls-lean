import FunctionalInequalities.Energy.Relaxation
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Semicontinuity.Basic

/-!
# Lower semicontinuity of sequential relaxation

In a pseudometric ambient space, the sequential relaxation of every finite pre-energy is lower
semicontinuous. The proof is a diagonal argument: from points with uniformly bounded relaxed
energy, choose concrete tests that are simultaneously close to those points and whose energies
miss the bound by a vanishing error.

No quadratic law, dense-realization hypothesis, or Markov property is used here. Outside a
first-countable setting, a sequential relaxation need not describe the topological
lower-semicontinuous envelope.
-/

noncomputable section

open Filter Topology

namespace FunctionalInequalities.Energy

namespace PreEnergy

universe u

variable {X : Type u} [PseudoMetricSpace X] (P : PreEnergy X)

/-- Sequential relaxation is lower semicontinuous in a pseudometric ambient space. -/
theorem lowerSemicontinuous_sequentialRelaxation :
    LowerSemicontinuous (fun x ↦ P.sequentialRelaxation x) := by
  apply LowerSemicontinuous.of_frequently
  intro x bound hfrequent
  by_cases hbound : bound = ⊤
  · simp [hbound]
  obtain ⟨xseq, hxseq, hxseq_bound⟩ := exists_seq_forall_of_frequently hfrequent
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
      dist (P.toAmbient f) (xseq n) < metricError n ∧
        (P.energy f : ENNReal) < bound + energyError n := by
    intro n
    have hrelaxed : P.sequentialRelaxation (xseq n) < bound + energyError n :=
      (hxseq_bound n).trans_lt
        (ENNReal.lt_add_right hbound (energyError_pos n).ne')
    rw [P.sequentialRelaxation_apply, iInf_lt_iff] at hrelaxed
    obtain ⟨approximation, henergy⟩ := hrelaxed
    have happ_tendsto := approximation.2
    have hnear : ∀ᶠ k : ℕ in atTop,
        dist (P.toAmbient (approximation.1 k)) (xseq n) < metricError n := by
      rw [Metric.tendsto_atTop] at happ_tendsto
      obtain ⟨N, hN⟩ := happ_tendsto (metricError n) (metricError_pos n)
      exact eventually_atTop.2 ⟨N, hN⟩
    have hlow : ∃ᶠ k : ℕ in atTop,
        (P.energy (approximation.1 k) : ENNReal) < bound + energyError n :=
      frequently_lt_of_liminf_lt (by isBoundedDefault) henergy
    obtain ⟨k, hk_energy, hk_near⟩ := (hlow.and_eventually hnear).exists
    exact ⟨approximation.1 k, hk_near, hk_energy⟩
  choose test htest_near htest_energy using exists_test
  have metricError_tendsto : Tendsto metricError atTop (𝓝 0) := by
    simpa [metricError] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hdist :
      Tendsto (fun n ↦ dist (xseq n) (P.toAmbient (test n))) atTop (𝓝 0) := by
    apply Filter.Tendsto.squeeze tendsto_const_nhds metricError_tendsto
    · intro n
      exact dist_nonneg
    · intro n
      simpa [dist_comm] using (htest_near n).le
  have htest_tendsto : Tendsto (fun n ↦ P.toAmbient (test n)) atTop (𝓝 x) :=
    tendsto_of_tendsto_of_dist hxseq hdist
  let approximation : P.ApproximatingSequence x := ⟨test, htest_tendsto⟩
  have energyError_tendsto : Tendsto energyError atTop (𝓝 0) := by
    simpa [energyError] using ENNReal.tendsto_inv_nat_nhds_zero
  calc
    P.sequentialRelaxation x ≤ P.sequenceEnergy approximation :=
      P.sequentialRelaxation_le_sequenceEnergy approximation
    _ ≤ liminf (fun n ↦ bound + energyError n) atTop :=
      liminf_le_liminf (Eventually.of_forall fun n ↦ (htest_energy n).le)
    _ = bound := by
      simpa using (tendsto_const_nhds.add energyError_tendsto).liminf_eq

end PreEnergy

end FunctionalInequalities.Energy
