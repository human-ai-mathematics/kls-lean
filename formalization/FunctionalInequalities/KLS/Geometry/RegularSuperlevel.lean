import FunctionalInequalities.KLS.Geometry.SmoothDomain
import FunctionalInequalities.Analysis.SmoothSard

/-! # Regular superlevel sets of smooth functions

Almost every strict superlevel set of a `C^∞` real-valued function is a smooth domain.  This is a
consequence of Sard's theorem in the smooth category, `Analysis.sard_smooth`, which is proved;
it does **not** use the sharp `C^(finrank)` statement `Analysis.sard`, which remains an unproved
obligation in `KLS/WIP/AnalyticPrerequisites.lean`.  This module is free of `sorry` and of
transitive `sorryAx`.

`Geometry/SmoothDomain.lean` is deliberately kept independent of Sard, so the packaging lives one
layer up here rather than beside the `SmoothDomain` structure itself. -/

noncomputable section

open MeasureTheory
open scoped ContDiff

namespace FunctionalInequalities.KLS

universe u

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]

namespace SmoothDomain

omit [InnerProductSpace ℝ V] [CompleteSpace V] [MeasurableSpace V] [BorelSpace V]
  [SecondCountableTopology V] [FiniteDimensional ℝ V] in
/-- The frontier of a strict superlevel set of a continuous function lies in the level set. -/
theorem frontier_superlevel_subset {u : V → ℝ} (hu : Continuous u) (t : ℝ) :
    frontier {x | t < u x} ⊆ {x | u x = t} := by
  intro x hx
  have h1 : x ∈ closure {x | t < u x} := frontier_subset_closure hx
  have h2 : t ≤ u x := closure_lt_subset_le continuous_const hu h1
  have hopen : IsOpen {x | t < u x} := isOpen_lt continuous_const hu
  have h3 : x ∉ {x | t < u x} := by
    have hx2 := hx.2
    rwa [hopen.interior_eq] at hx2
  simp only [Set.mem_ofPred_eq, not_lt] at h3
  exact le_antisymm h3 h2

-- The section variables are kept so that the published interface is unchanged; the geometric
-- construction `SmoothDomain.ofSuperlevel` needs neither a measure structure nor completeness,
-- so the linter is silenced instead of the signature being narrowed by `omit`.
set_option linter.unusedSectionVars false in
/-- Sard: for a `C^∞` real function, almost every strict superlevel set is a smooth domain, with
defining function `t - u` at its regular value `t`.

Proved by packaging `Analysis.ae_forall_fderiv_ne_zero_of_contDiff_top` — a consequence of the
proved smooth Sard theorem `Analysis.sard_smooth` — with the hole-free construction
`SmoothDomain.ofSuperlevel`: at a regular value `t` the frontier of `{x | t < u x}` lies in
`{x | u x = t}` by `frontier_superlevel_subset`, so `fderiv ℝ u` does not vanish there and the
construction applies.  The statement is unchanged from the work-in-progress version it replaces;
only its proof is, and it no longer depends on `sorryAx`. -/
theorem ae_exists_superlevel {u : V → ℝ} (hu : ContDiff ℝ ∞ u) :
    ∀ᵐ t ∂(volume : Measure ℝ), ∃ U : SmoothDomain V, U.carrier = {x | t < u x} := by
  filter_upwards [Analysis.ae_forall_fderiv_ne_zero_of_contDiff_top hu] with t ht
  exact ⟨ofSuperlevel hu fun x hx ↦ ht x (frontier_superlevel_subset hu.continuous t hx), rfl⟩

end SmoothDomain

end FunctionalInequalities.KLS
