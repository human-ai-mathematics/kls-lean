import FunctionalInequalities.Analysis.Sard.Basic
import FunctionalInequalities.Analysis.Sard.QuadraticCover
import FunctionalInequalities.Analysis.Sard.MorseVanishing

/-! # Sard's theorem at the sharp finite regularity `C^n`

The critical values of a `C^n` real-valued function on an `n`-dimensional real normed space are
Lebesgue-null.  `C^n` is the sharp regularity for a real target.

The descent of `Analysis/Sard/Smooth.lean` restricts the function to the regular zero set of a
`j`-th derivative component, which at finite regularity is only a `C^(n-j)` hypersurface while the
induction in dimension `n - 1` needs `C^(n-1)`; the loss is fatal for every `j ≥ 2`.  Nothing is
restricted here.  Instead the Morse vanishing lemma
`Analysis.MorseSard.hasDecompRel_self` decomposes the critical set itself, the mean value step
`Analysis.MorseSard.abs_sub_le_of_flat_fderiv` turns flatness of the derivative coordinates into a
uniform `o(‖y - x‖ ^ (k + 1))` modulus for the function (`exists_cover_of_critical`), and the
covering count `Analysis.volume_image_eq_zero_of_oscillation_pow` finishes with `k + 1 = n`.
-/

noncomputable section

open Set Metric MeasureTheory Filter Topology
open scoped ContDiff

namespace FunctionalInequalities.Analysis

variable {n k : ℕ}

/-- **The Morse criticality lemma.**  The set on which a `C^(k+1)` function is critical is covered
by a countable set and countably many bounded pieces, on each of which the function has a uniform
`o(‖y - x‖ ^ (k + 1))` modulus.  Neither the set nor the pieces are assumed measurable. -/
theorem exists_cover_of_critical (A : Set (Fin n → ℝ)) {f : (Fin n → ℝ) → ℝ}
    (hf : ContDiff ℝ (k + 1) f) (hA : ∀ x ∈ A, fderiv ℝ f x = 0) :
    ∃ (A₀ : Set (Fin n → ℝ)) (P : Set (Set (Fin n → ℝ))), A₀.Countable ∧ P.Countable ∧
      A ⊆ A₀ ∪ ⋃₀ P ∧
      ∀ S ∈ P, Bornology.IsBounded S ∧ ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ x ∈ S, ∀ y ∈ S, ‖y - x‖ < δ → |f y - f x| ≤ ε * ‖y - x‖ ^ (k + 1) := by
  classical
  obtain ⟨A₀, P, hA₀, hP, hcov, hcar, hflat⟩ := MorseSard.hasDecompRel_self k n A
  have hfd : ContDiff ℝ k (fderiv ℝ f) := hf.fderiv_right (by exact_mod_cast le_rfl)
  have hdiff : Differentiable ℝ f := hf.differentiable (by simp)
  refine ⟨A₀, (fun q : MorseSard.Piece n => q.1) '' P, hA₀, hP.image _, ?_, ?_⟩
  · rw [sUnion_image]
    exact hcov
  · rintro S ⟨q, hq, rfl⟩
    obtain ⟨hq1, hq2, κ, hdisk⟩ := hcar q hq
    have hbody : IsCompact (q.2.2 '' closedBall (0 : Fin q.2.1 → ℝ) 1) :=
      (isCompact_closedBall _ _).image (hdisk.1.continuous)
    refine ⟨hbody.isBounded.subset hq2, ?_⟩
    have hcoord : ∀ j : Fin n,
        MorseSard.FlatAlong q.2.2 q.1 k fun x => fderiv ℝ f x (Pi.single j (1 : ℝ)) := by
      intro j
      refine hflat _ (hfd.clm_apply contDiff_const) (fun x hx => ?_) q hq
      rw [hA x hx]
      simp
    intro ε hε
    obtain ⟨δ, hδ, hδspec⟩ := MorseSard.abs_sub_le_of_flat_fderiv hdisk hdiff hcoord ε hε
    refine ⟨δ, hδ, ?_⟩
    intro x hx y hy hxy
    obtain ⟨a, ha, rfl⟩ := hq2 hx
    obtain ⟨b, hb, rfl⟩ := hq2 hy
    have hb' : a + (1 : ℝ) • (b - a) = b := by module
    have hlt : ‖q.2.2 a - q.2.2 b‖ < δ := by rwa [norm_sub_rev]
    have := hδspec a ha b hb hx hy hlt 1 ⟨zero_le_one, le_refl 1⟩
    rw [hb'] at this
    rw [norm_sub_rev]
    exact this

/-- **Sard's theorem for `C^n` real-valued functions on `Fin n → ℝ`.**  The critical set is not
assumed measurable.  This is the sharp finite regularity: `C^n`, not `C^∞`. -/
theorem sard_pi : ∀ (n : ℕ) (u : (Fin n → ℝ) → ℝ), ContDiff ℝ n u →
    (volume : Measure ℝ) (u '' {x | fderiv ℝ u x = 0}) = 0 := by
  rintro (_ | m) u hu
  · refine Set.Subsingleton.measure_zero ?_ _
    exact Set.Subsingleton.image (fun a _ b _ => Subsingleton.elim a b) u
  · obtain ⟨A₀, P, hA₀, hP, hcov, hmod⟩ :=
      exists_cover_of_critical (k := m) {x : Fin (m + 1) → ℝ | fderiv ℝ u x = 0} hu
        (fun x hx => hx)
    refine measure_mono_null (Set.image_mono hcov) ?_
    rw [Set.image_union]
    refine measure_union_null ((hA₀.image u).measure_zero _) ?_
    rw [Set.sUnion_eq_biUnion, Set.image_iUnion₂]
    refine (measure_biUnion_null_iff hP).mpr fun S hS => ?_
    exact volume_image_eq_zero_of_oscillation_pow (hmod S hS).1 (hmod S hS).2

section FiniteDimensional

variable {V : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- **Sard's theorem at the sharp regularity.**  The set of critical values of a
`C^(finrank ℝ V)` real-valued function on a finite-dimensional real normed space is
Lebesgue-null.  The critical set is not assumed measurable. -/
theorem sard
    {u : V → ℝ} (hu : ContDiff ℝ (Module.finrank ℝ V) u) :
    (volume : Measure ℝ) (u '' {x | fderiv ℝ u x = 0}) = 0 := by
  have hdim : Module.finrank ℝ (Fin (Module.finrank ℝ V) → ℝ) = Module.finrank ℝ V := by
    simp
  set e : (Fin (Module.finrank ℝ V) → ℝ) ≃L[ℝ] V := ContinuousLinearEquiv.ofFinrankEq hdim with he
  rw [image_critical_comp_continuousLinearEquiv e u]
  exact sard_pi _ _ (hu.comp e.contDiff)

/-- Almost every level is a regular value of a `C^n` function on an `n`-dimensional space.
-/
theorem ae_forall_fderiv_ne_zero {u : V → ℝ} (hu : ContDiff ℝ (Module.finrank ℝ V) u) :
    ∀ᵐ t ∂(volume : Measure ℝ), ∀ x, u x = t → fderiv ℝ u x ≠ 0 := by
  rw [ae_iff]
  refine measure_mono_null (fun t ht => ?_) (sard hu)
  by_contra hcon
  exact ht fun x hxt hx0 => hcon ⟨x, hx0, hxt⟩

end FiniteDimensional

end FunctionalInequalities.Analysis
