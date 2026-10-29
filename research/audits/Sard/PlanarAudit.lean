import FunctionalInequalities.Analysis.Sard.Planar
import FunctionalInequalities.Analysis.Sard.Sharp

/-!
# Scope and axiom audit for the planar Sard theorem

`Analysis/Sard/Planar.lean` had no consumer anywhere: it is not reached from the root aggregate
`FunctionalInequalities.lean`, no library, solution or example module imports it, and no other
audit referred to it.  It was therefore the only live library module outside all three gate
scopes — the certificate import closures scanned by `research/check_ledger.py`, the audited
declaration sets of `research/verify.py`, and the audit import closures — so a proof escape
introduced there would have been reported by nothing but a `lake build` warning.  This client
exists to close that gap: it pins the module's two public theorems to the standard axioms.

**What the module proves.**  Sard's theorem for a `C²` real function on `Fin 2 → ℝ`: the critical
values are Lebesgue-null.  Dimension two only.

**What it does not prove.**  It is *not* `FunctionalInequalities.Analysis.sard`, which is stated in
arbitrary finite dimension at `C^(finrank)` regularity and is proved separately in
`Analysis/Sard/Sharp.lean` by the Morse route.  `sard_agrees_in_dimension_two` records that the
sharp theorem already covers the planar statement, so the planar module is a self-contained
elementary proof of a special case, not an ingredient of the sharp one; nothing here weakens or
re-proves the sharp theorem.  No Cheeger, semigroup, Bakry–Émery or KLS content is involved.
-/

noncomputable section

open MeasureTheory Set Module

namespace PlanarSardAudit

/-- The planar theorem, restated verbatim and discharged. -/
theorem planar_sard :
    (∀ {u : (Fin 2 → ℝ) → ℝ}, ContDiff ℝ 2 u →
      (volume : Measure ℝ) (u '' {x | fderiv ℝ u x = 0}) = 0) :=
  fun hu => FunctionalInequalities.Analysis.sard_plane hu

/-- The nonflat layer, restated verbatim and discharged. -/
theorem planar_nonflat :
    (∀ {u : (Fin 2 → ℝ) → ℝ}, ContDiff ℝ 2 u →
      (volume : Measure ℝ)
        (u '' {x | fderiv ℝ u x = 0 ∧ iteratedFDeriv ℝ 2 u x ≠ 0}) = 0) :=
  fun hu => FunctionalInequalities.Analysis.volume_image_nonflat_eq_zero hu

/-- The sharp finite-regularity Sard theorem already covers the planar case, at the same `C²`
regularity because `finrank ℝ (Fin 2 → ℝ) = 2`.  The planar module is therefore an independent
elementary proof of a special case, not a prerequisite of `Analysis.sard`. -/
theorem sard_agrees_in_dimension_two {u : (Fin 2 → ℝ) → ℝ} (hu : ContDiff ℝ 2 u) :
    (volume : Measure ℝ) (u '' {x | fderiv ℝ u x = 0}) = 0 := by
  have hdim : finrank ℝ (Fin 2 → ℝ) = 2 := by simp
  exact FunctionalInequalities.Analysis.sard (by simpa [hdim] using hu)

end PlanarSardAudit

/-! ### Axiom audit: every report must be standard-only -/

#print axioms FunctionalInequalities.Analysis.sard_plane
#print axioms FunctionalInequalities.Analysis.volume_image_nonflat_eq_zero
#print axioms PlanarSardAudit.planar_sard
#print axioms PlanarSardAudit.planar_nonflat
#print axioms PlanarSardAudit.sard_agrees_in_dimension_two
