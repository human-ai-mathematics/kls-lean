import FunctionalInequalities.Analysis.Semigroup.Resolvent.Basic

/-!
# The Yosida approximation `L_s = s⁻¹ (1 - J_s)`

Definitions only. Given a closed operator `T : H₀ →ₗ.[ℝ] H₁` between real Hilbert spaces and the
resolvent `J_s = resolventCLM T hT hs` of `Analysis/Semigroup/Resolvent/Basic.lean`, this module packages
the bounded operator `L_s = s⁻¹ • (1 - J_s)` on `H₀`. Formally `L_s = T†T J_s = T†T (1 + s T†T)⁻¹`,
the classical Yosida approximation of `T†T`; that identification is `V5` of
`Analysis/Semigroup/VonNeumann.lean`, not anything proved here.

Its properties (nonnegativity, symmetry, commutation, convergence to `T†T` on `D(T†T)`, and the
strong convergence of `exp (-t • L_s)` which is `S6`) are the `Y`-series obligations of
`research/audits/YosidaLimitRouteStatements.lean`. Everything here is definitional or `simp`-level
glue. No measure, no log-concavity and no KLS content.
-/

noncomputable section

namespace FunctionalInequalities.Analysis.Semigroup

variable {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
  [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]

/-- The Yosida approximation `L_s = s⁻¹ • (1 - J_s)` of `T†T`, a bounded operator on `H₀`. -/
def yosida (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) {s : ℝ} (hs : 0 < s) : H₀ →L[ℝ] H₀ :=
  s⁻¹ • (ContinuousLinearMap.id ℝ H₀ - resolventCLM T hT hs)

/-- `L_s f = s⁻¹ • (f - J_s f)`. -/
theorem yosida_apply (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) {s : ℝ} (hs : 0 < s) (f : H₀) :
    yosida T hT hs f = s⁻¹ • (f - resolventCLM T hT hs f) := by
  simp [yosida]

/-- `s • L_s f = f - J_s f`. -/
theorem smul_yosida_apply (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) {s : ℝ} (hs : 0 < s) (f : H₀) :
    s • yosida T hT hs f = f - resolventCLM T hT hs f := by
  rw [yosida_apply, smul_smul, mul_inv_cancel₀ hs.ne', one_smul]

end FunctionalInequalities.Analysis.Semigroup
