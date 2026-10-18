import FunctionalInequalities.Analysis.Vector.Coarea.Regular

/-! # The fibres of the regular part have finite Hausdorff measure

On relatively compact regular pieces, almost every fibre of the regular component has finite Hausdorff measure. This module does not state a coarea formula for critical fibres or a Sard theorem.

**What regular-fibre finiteness is for.**  The route repairs the exponent by applying the Eilenberg bound not in `V` but
inside a fibre of the regular component `v = P ∘ u`, with `d = k` and a target of dimension
`m − r`, so that `d + (m − r) = n − r`.  For that bound to say anything the fibre must carry
**finite** `ℋ^{n−r}` measure — otherwise the right-hand side is `∞` and the estimate is vacuous,
exactly as the false exponent-comparison diagnostic records for the one-step method.

**It is a corollary of the proved regular coarea formula**, not new analysis:
`coarea_of_contDiffOn_of_coareaJacobian_ne_zero` with weight `1` says that the total fibre measure
integrates to `∫⁻ coareaJacobian` over the piece, which is finite on a relatively compact piece
because the integrand is continuous there.  A finite integral has almost everywhere finite
integrand.

**Relative compactness is a real hypothesis, not a convenience.**  The coarea Jacobian may be
unbounded near the boundary of the regular open set, and the fibres of a regular map need not have
finite measure globally — a linear projection of the plane has fibres of infinite length.
-/

noncomputable section

open MeasureTheory Module Set
open scoped ENNReal NNReal

namespace FunctionalInequalities.Analysis

section Fibre

variable {V W₁ : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup W₁] [InnerProductSpace ℝ W₁] [FiniteDimensional ℝ W₁]
  [MeasurableSpace W₁] [BorelSpace W₁]

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [InnerProductSpace ℝ W₁]
  [FiniteDimensional ℝ W₁] [MeasurableSpace W₁] [BorelSpace W₁] in
/-- The normalization constant of `KLS.hausdorffNormalized` is positive and finite, so a set has
finite normalized measure exactly when it has finite raw measure.  The companion of the proved
`hausdorffNormalized_eq_zero_iff`. -/
theorem hausdorffNormalized_ne_top_iff (k : ℕ) (A : Set V) :
    KLS.hausdorffNormalized V k A ≠ ⊤ ↔ μH[(k : ℝ)] A ≠ ⊤ := by
  have hpos : 0 < KLS.unitBallVolume k / 2 ^ k := by
    unfold KLS.unitBallVolume; positivity
  have hne : ENNReal.ofReal (KLS.unitBallVolume k / 2 ^ k) ≠ 0 := by
    simp [ENNReal.ofReal_eq_zero, not_le, hpos]
  rw [KLS.hausdorffNormalized, Measure.smul_apply, smul_eq_mul]
  constructor
  · intro h htop
    exact h (by rw [htop, ENNReal.mul_top hne])
  · intro h htop
    rcases ENNReal.mul_eq_top.1 htop with ⟨-, h2⟩ | ⟨h1, -⟩
    · exact h h2
    · exact absurd h1 ENNReal.ofReal_ne_top

/-- **regular-fibre finiteness: at almost every level the fibre of a regular `C¹` map meets a relatively compact piece
in a set of finite `ℋ^{n-r}` measure.**

This is what makes the Eilenberg right-hand side finite at the repaired exponent.  It follows from
the **proved** regular coarea formula with weight `1`; no new analysis is involved, and nothing is
claimed about the critical set of `v`. -/
theorem ae_hausdorffMeasure_fibre_ne_top {O S : Set V} {v : V → W₁} (hO : IsOpen O)
    (hv : ContDiffOn ℝ 1 v O) (hreg : ∀ x ∈ O, coareaJacobian (fderiv ℝ v x) ≠ 0)
    (hS : MeasurableSet S) (hK : IsCompact (closure S)) (hSO : closure S ⊆ O) :
    ∀ᵐ s ∂(volume : Measure W₁),
      μH[((finrank ℝ V - finrank ℝ W₁ : ℕ) : ℝ)] (S ∩ {x : V | v x = s}) ≠ ⊤ := by
  classical
  set k : ℕ := finrank ℝ V - finrank ℝ W₁ with hk
  set ν : Measure V := KLS.hausdorffNormalized V k with hν
  obtain ⟨hmeas, heq⟩ := coarea_of_contDiffOn_of_coareaJacobian_ne_zero (g := fun _ => (1 : ℝ≥0∞))
    hO hv hreg hS (subset_closure.trans hSO) measurable_const
  simp only [setLIntegral_one, mul_one] at hmeas heq
  -- the coarea Jacobian is continuous on the open set, hence bounded on the compact closure
  have hJcont : ContinuousOn (fun x : V => coareaJacobian (fderiv ℝ v x)) O :=
    continuous_coareaJacobian.comp_continuousOn (hv.continuousOn_fderiv_of_isOpen hO le_rfl)
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hJcont.mono hSO)
  have hvolS : (volume : Measure V) S ≠ ⊤ :=
    ((measure_mono subset_closure).trans_lt hK.measure_lt_top).ne
  -- the total integral is finite
  have hfin : (∫⁻ x in S, ENNReal.ofReal (coareaJacobian (fderiv ℝ v x)) ∂(volume : Measure V))
      ≠ ⊤ := by
    have hbound : (∫⁻ x in S, ENNReal.ofReal (coareaJacobian (fderiv ℝ v x))
        ∂(volume : Measure V)) ≤ ENNReal.ofReal M * (volume : Measure V) S := by
      refine (lintegral_mono_ae ?_).trans_eq (setLIntegral_const S (ENNReal.ofReal M))
      filter_upwards [self_mem_ae_restrict hS] with x hx
      exact ENNReal.ofReal_le_ofReal
        ((le_abs_self _).trans (hM x (subset_closure hx)))
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hvolS) hbound
  -- so the fibre measure is finite at almost every level
  rw [heq] at hfin
  filter_upwards [ae_lt_top hmeas hfin] with s hs
  exact (hausdorffNormalized_ne_top_iff k _).1 hs.ne

end Fibre

end FunctionalInequalities.Analysis
