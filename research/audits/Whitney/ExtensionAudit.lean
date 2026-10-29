import FunctionalInequalities.Analysis.Whitney.Extension
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
Strict clients of the boundary-gluing step of the compact `C¹` Whitney extension, obligation `L6`
of `research/audits/Coarea/WeightedRouteStatements.lean`. No theorem here proves the extension
itself; the full original statement is pinned in `FirstOrderJetAudit.lean`.

The singleton client prescribes an arbitrary ambient derivative although its values are constant
on the set. The sparse-set client shows why a within-derivative cannot be identified with the
ambient derivative of the original function. Empty-set and zero-dimensional cases are included.
-/

noncomputable section

open Set Metric FunctionalInequalities.Analysis
open scoped ContDiff
open scoped Topology

namespace WhitneyExtensionAudit

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Apply the gluing criterion to a singleton jet with arbitrary derivative. -/
theorem singleton_extension (c : ℝ) (L : V →L[ℝ] ℝ) :
    ∃ v : V → ℝ, ContDiff ℝ 1 v ∧ EqOn v (fun _ => c) {0} ∧
      fderiv ℝ v 0 = L := by
  have hd : ∀ x, HasFDerivAt (fun y => c + L y) L x := by
    intro x
    exact L.hasFDerivAt.const_add c
  have h := WhitneyJet.contDiff_of_nearby_jet (S := {(0 : V)}) isCompact_singleton
    (f := fun _ => c) (F := fun _ => L) (v := fun y => c + L y) (D := fun _ => L)
    continuousOn_const
    (by
      intro ε hε
      refine ⟨1, one_pos, ?_⟩
      intro x hx y hy _
      simp only [mem_singleton_iff] at hx hy
      simp [hx, hy])
    (by intro x hx; simp_all)
    (by intro x _; rfl)
    (fun x _ => hd x)
    continuousOn_const
    (by
      intro ε hε
      refine ⟨1, one_pos, ?_⟩
      intro y _ a ha _ _
      simp only [mem_singleton_iff] at ha
      subst a
      simp only [WhitneyJet.affine, sub_zero, sub_self, norm_zero]
      exact ⟨mul_nonneg hε.le infDist_nonneg, hε.le⟩)
  exact ⟨_, h.1, by intro x hx; simp_all, h.2 0 (by simp)⟩

/-- The gluing interface does not require a nonempty compact set or nearest-point choice. -/
theorem empty_extension (f : V → ℝ) (F : V → V →L[ℝ] ℝ) :
    ∃ v : V → ℝ, ContDiff ℝ 1 v ∧ EqOn v f ∅ ∧
      ∀ x ∈ (∅ : Set V), fderiv ℝ v x = F x := by
  have h := WhitneyJet.contDiff_of_nearby_jet (S := (∅ : Set V)) isCompact_empty
    (f := f) (F := F) (v := fun _ => 0) (D := fun _ => 0)
    (continuousOn_empty F)
    (by intro ε _; exact ⟨1, one_pos, by simp⟩)
    (by simp) (by simp)
    (fun x _ => hasFDerivAt_const 0 x)
    continuousOn_const
    (by intro ε _; exact ⟨1, one_pos, by simp⟩)
  exact ⟨_, h.1, by simp, h.2⟩

/-- On a singleton any linear map is a within-derivative of a constant function.
This is not an ambient derivative assertion. -/
theorem singleton_within (c : ℝ) (L : V →L[ℝ] ℝ) :
    HasFDerivWithinAt (fun _ : V => c) L {0} 0 := by
  apply WhitneyJet.hasFDerivWithinAt (F := fun _ => L) _ (by simp)
  intro ε _
  refine ⟨1, one_pos, ?_⟩
  intro x hx y hy _
  simp only [mem_singleton_iff] at hx hy
  simp [hx, hy]

/-- A concrete guard against recovering ambient derivatives from values on a sparse set. -/
theorem within_does_not_identify_ambient :
    HasFDerivWithinAt (fun _ : ℝ => (0 : ℝ)) (ContinuousLinearMap.id ℝ ℝ) {0} 0 ∧
      fderiv ℝ (fun _ : ℝ => (0 : ℝ)) 0 ≠ ContinuousLinearMap.id ℝ ℝ := by
  refine ⟨singleton_within 0 _, ?_⟩
  intro h
  have he := congrArg (fun L : ℝ →L[ℝ] ℝ => L 1) h
  simp at he

/-- An actual zero-dimensional domain, using the same gluing theorem. -/
theorem zero_dimension :
    ∃ v : EuclideanSpace ℝ (Fin 0) → ℝ, ContDiff ℝ 1 v ∧
      EqOn v (fun _ => (7 : ℝ)) {0} ∧ fderiv ℝ v 0 = 0 :=
  singleton_extension 7 0

/-- The candidate can be discontinuous on the compact set: its value there is discarded.
Here `w 0 = 0`, while the prescribed value and the values off the set are all `1`. -/
theorem discard_wrong_value_on_set :
    ∃ v : ℝ → ℝ, ContDiff ℝ 1 v ∧ EqOn v (fun _ => 1) {0} ∧
      ∀ x ∈ ({0} : Set ℝ), fderiv ℝ v x = 0 := by
  classical
  let w : ℝ → ℝ := fun x => if x = 0 then 0 else 1
  have hwlocal : ∀ x ∉ ({0} : Set ℝ), w =ᶠ[𝓝 x] (fun _ => 1) := by
    intro x hx
    filter_upwards [isClosed_singleton.isOpen_compl.mem_nhds hx] with y hy
    simp only [mem_compl_iff, mem_singleton_iff] at hy
    simp [w, hy]
  have hw : ContDiffOn ℝ 1 w ({0} : Set ℝ)ᶜ := by
    apply (show ContDiffOn ℝ 1 (fun _ : ℝ => (1 : ℝ)) ({0} : Set ℝ)ᶜ from
      contDiffOn_const).congr
    intro x hx
    simp only [mem_compl_iff, mem_singleton_iff] at hx
    simp [w, hx]
  refine WhitneyJet.exists_contDiff_of_compl_approx (S := ({0} : Set ℝ)) isCompact_singleton
    (f := fun _ => 1) (F := fun _ => 0) (w := w) continuousOn_const ?_ hw ?_
  · intro ε _
    refine ⟨1, one_pos, ?_⟩
    intro x hx y hy _
    simp only [mem_singleton_iff] at hx hy
    simp [hx, hy]
  · intro ε hε
    refine ⟨1, one_pos, ?_⟩
    intro y hy a _ _ _
    have hd : fderiv ℝ w y = 0 :=
      ((hasFDerivAt_const (1 : ℝ) y).congr_of_eventuallyEq (hwlocal y hy)).fderiv
    have hy0 : y ≠ 0 := hy
    simp only [WhitneyJet.affine, zero_apply, add_zero, hd, sub_zero]
    simp only [w, if_neg hy0, sub_self, norm_zero]
    exact ⟨mul_nonneg hε.le infDist_nonneg, hε.le⟩

/-! ### The precise remaining construction, type-checked only

This is an open obligation, not an axiom or a theorem. The original Whitney-extension assumptions
are kept; the gluing theorem above consumes exactly this candidate to deliver the original
conclusion.
-/

#check (∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {S : Set V} {f : V → ℝ} {F : V → V →L[ℝ] ℝ},
    IsCompact S → ContinuousOn f S → ContinuousOn F S →
    (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ x ∈ S, ∀ y ∈ S, ‖y - x‖ < δ →
        ‖f y - f x - F x (y - x)‖ ≤ ε * ‖y - x‖) →
    ∃ w : V → ℝ, ContDiffOn ℝ 1 w Sᶜ ∧
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ y ∉ S, ∀ a ∈ S, infDist y S = dist y a → infDist y S < δ →
          ‖w y - WhitneyJet.affine f F a y‖ ≤ ε * infDist y S ∧
            ‖fderiv ℝ w y - F a‖ ≤ ε)

#print axioms FunctionalInequalities.Analysis.WhitneyJet.norm_affine_sub_le
#print axioms FunctionalInequalities.Analysis.WhitneyJet.dist_nearest_le
#print axioms FunctionalInequalities.Analysis.WhitneyJet.hasFDerivWithinAt
#print axioms FunctionalInequalities.Analysis.WhitneyJet.hasFDerivAt_of_nearby_affine
#print axioms FunctionalInequalities.Analysis.WhitneyJet.continuousAt_of_nearby_field
#print axioms FunctionalInequalities.Analysis.WhitneyJet.contDiff_of_nearby_jet
#print axioms FunctionalInequalities.Analysis.WhitneyJet.exists_contDiff_of_compl_approx
#print axioms WhitneyExtensionAudit.singleton_extension
#print axioms WhitneyExtensionAudit.empty_extension
#print axioms WhitneyExtensionAudit.singleton_within
#print axioms WhitneyExtensionAudit.within_does_not_identify_ambient
#print axioms WhitneyExtensionAudit.zero_dimension
#print axioms WhitneyExtensionAudit.discard_wrong_value_on_set

end WhitneyExtensionAudit
