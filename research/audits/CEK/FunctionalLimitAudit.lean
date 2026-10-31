module

public import FunctionalInequalities.Probability.MomentMeasure.ConjugateMass
public import Mathlib.Tactic.NormNum

/-! Audit clients for the extended-logarithm limit comparison of CEK Proposition 12
(`log_sub_ge_of_integral_limits`, `Probability/MomentMeasure/ConjugateMass.lean`):
zero and infinite masses at a finite prefix. -/

@[expose] public section


set_option autoImplicit false
set_option relaxedAutoImplicit false
open Filter
open scoped ENNReal Topology

namespace CEKFunctionalLimitClients
noncomputable section

def prefixMass (j : ℕ) : ℝ≥0∞ :=
  if j = 0 then 0 else if j = 1 then ⊤ else ENNReal.ofReal (Real.exp 2)

theorem zero_initial_mass : ENNReal.log (prefixMass 0) = ⊥ := by simp [prefixMass]
theorem infinite_second_mass : ENNReal.log (prefixMass 1) = ⊤ := by simp [prefixMass]

/-- Both singular mass endpoints occur in the actual prefix, while the genuine
extended functional has a finite limit and produces a positive limiting mass. -/
theorem prefix_limit_comparison :
    0 < ENNReal.ofReal (Real.exp 2) ∧
      (0 : EReal) ≤ ENNReal.log (ENNReal.ofReal (Real.exp 2)) - (2 : EReal) := by
  have he : prefixMass =ᶠ[atTop] (fun _ => ENNReal.ofReal (Real.exp 2)) := by
    filter_upwards [eventually_ge_atTop 2] with j hj
    have h0 : j ≠ 0 := by omega
    have h1 : j ≠ 1 := by omega
    simp only [prefixMass, ite_eq_right h0, ite_eq_right h1]
  have hF : Tendsto (fun j => ENNReal.log (prefixMass j) - (2 : EReal))
      atTop (𝓝 (0 : EReal)) := by
    apply (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : EReal)) atTop (𝓝 0)).congr'
    filter_upwards [he] with j hj
    rw [hj, ENNReal.log_ofReal_of_pos (Real.exp_pos _), Real.log_exp]
    change (0 : EReal) = ((2 : ℝ) : EReal) - ((2 : ℝ) : EReal)
    rw [← EReal.coe_sub]
    norm_num
  have ha : Tendsto prefixMass atTop (𝓝 (ENNReal.ofReal (Real.exp 2))) :=
    tendsto_const_nhds.congr' he.symm
  apply FunctionalInequalities.Probability.MomentMeasure.log_sub_ge_of_integral_limits
    prefixMass (fun _ => 2) (ENNReal.ofReal (Real.exp 2)) 2 0 2
    (by intro j; norm_num) hF tendsto_const_nhds
  · rw [liminf_const]
  · exact ha.limsup_eq.le

end
end CEKFunctionalLimitClients

#print axioms CEKFunctionalLimitClients.zero_initial_mass
#print axioms CEKFunctionalLimitClients.infinite_second_mass
#print axioms CEKFunctionalLimitClients.prefix_limit_comparison
#print axioms FunctionalInequalities.Probability.MomentMeasure.log_sub_ge_of_integral_limits
