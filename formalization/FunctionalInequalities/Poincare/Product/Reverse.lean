module

public import FunctionalInequalities.Poincare.Product.Tensorization
public import FunctionalInequalities.Poincare.SmoothTest.Transport

/-!
# Binary reverse bounds and equality

Both factor probability instances are explicit. Probability of `prodMeasure μ ν` alone
does not normalize its two factors.

Source: the Poincaré part of the historical manuscript's
[Theorem 3.4](https://github.com/human-ai-mathematics/kls-conjecture-search/blob/cd4a894a0faf40c0180f80b1a31eec1fdb6cb576/modules/02-results-toolkit.tex#L59-L68)
states the product optimal-constant identity. The coordinate lower bounds below are local
steps toward that identity, rather than separately stated manuscript results. The Hilbert,
Borel, finite-energy and extended-real formulation is the present realization. BGL
Proposition 4.3.1 supplies the upper bound used by `constant_prod_eq`, not these reverse steps.
-/

@[expose] public section

noncomputable section

open MeasureTheory

/- The unused ambient instances are retained in the candidate signatures. -/

namespace FunctionalInequalities.Poincare.SmoothTest

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]


private theorem adjoint_fstL :
    (((WithLp.prodContinuousLinearEquiv 2 ℝ E F).symm :
        (E × F) →L[ℝ] WithLp 2 (E × F)).comp (ContinuousLinearMap.inl ℝ E F))
      = (WithLp.fstL 2 ℝ E F).adjoint := by
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro v p
  rw [ContinuousLinearMap.comp_apply]
  simp

private theorem adjoint_sndL :
    (((WithLp.prodContinuousLinearEquiv 2 ℝ E F).symm :
        (E × F) →L[ℝ] WithLp 2 (E × F)).comp (ContinuousLinearMap.inr ℝ E F))
      = (WithLp.sndL 2 ℝ E F).adjoint := by
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro v p
  rw [ContinuousLinearMap.comp_apply]
  simp

/-- Source: local Hilbert-coordinate helper, using `WithLp.norm_toLp_fst`.
The first projection's adjoint inserts a zero second coordinate. -/
theorem isometry_adjoint_fstL : Isometry (WithLp.fstL 2 ℝ E F).adjoint := by
  rw [← adjoint_fstL]
  refine AddMonoidHomClass.isometry_of_norm _ fun v ↦ ?_
  show ‖WithLp.toLp 2 ((v : E), (0 : F))‖ = ‖v‖
  exact WithLp.norm_toLp_fst 2 E F v

/-- Source: local Hilbert-coordinate helper, using `WithLp.norm_toLp_snd`.
The second projection's adjoint inserts a zero first coordinate. -/
theorem isometry_adjoint_sndL : Isometry (WithLp.sndL 2 ℝ E F).adjoint := by
  rw [← adjoint_sndL]
  refine AddMonoidHomClass.isometry_of_norm _ fun v ↦ ?_
  show ‖WithLp.toLp 2 ((0 : E), (v : F))‖ = ‖v‖
  exact WithLp.norm_toLp_snd 2 E F v

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
  {μ : Measure E} {ν : Measure F} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

omit [CompleteSpace E] [CompleteSpace F] [SecondCountableTopology E] [IsProbabilityMeasure μ] in
/-- Source: local transport of Mathlib's `measurePreserving_fst` through `WithLp.toLp`.
The marginal law uses the other factor's probability normalization. -/
theorem measurePreserving_prod_fst :
    MeasurePreserving (WithLp.fstL 2 ℝ E F) (prodMeasure μ ν) μ := by
  refine ⟨(WithLp.fstL 2 ℝ E F).continuous.measurable, ?_⟩
  rw [prodMeasure, Measure.map_map (WithLp.fstL 2 ℝ E F).continuous.measurable
    (WithLp.measurable_toLp 2 (E × F))]
  exact measurePreserving_fst.map_eq

omit [CompleteSpace E] [CompleteSpace F] [SecondCountableTopology E] in
/-- Source: local transport of Mathlib's `measurePreserving_snd` through `WithLp.toLp`.
The marginal law uses the other factor's probability normalization. -/
theorem measurePreserving_prod_snd :
    MeasurePreserving (WithLp.sndL 2 ℝ E F) (prodMeasure μ ν) ν := by
  refine ⟨(WithLp.sndL 2 ℝ E F).continuous.measurable, ?_⟩
  rw [prodMeasure, Measure.map_map (WithLp.sndL 2 ℝ E F).continuous.measurable
    (WithLp.measurable_toLp 2 (E × F))]
  exact measurePreserving_snd.map_eq

section ProductMarginals

omit [SecondCountableTopology E]
/-- Recover the first factor at the same finite real constant.
Source: local coordinate-test deduction using `Admissible.comp_projection` and the first
marginal law; both factor probabilities are retained. -/
theorem Holds.of_prod_left {C : ℝ} (h : Holds (prodMeasure μ ν) C) : Holds μ C := by
  refine ⟨inferInstance, h.constant_nonneg, fun f hf ↦ ?_⟩
  have hlift : Admissible (prodMeasure μ ν) (f ∘ WithLp.fstL 2 ℝ E F) :=
    Admissible.comp_projection _ isometry_adjoint_fstL measurePreserving_prod_fst hf
  have hv := h.variance_le hlift
  rwa [variance_comp_projection _ measurePreserving_prod_fst hf.memLp_two,
    energy_comp_projection _ isometry_adjoint_fstL measurePreserving_prod_fst hf] at hv

/-- Recover the second factor at the same finite real constant.
Source: local coordinate-test deduction using `Admissible.comp_projection` and the second
marginal law; both factor probabilities are retained. -/
theorem Holds.of_prod_right {C : ℝ} (h : Holds (prodMeasure μ ν) C) : Holds ν C := by
  refine ⟨inferInstance, h.constant_nonneg, fun f hf ↦ ?_⟩
  have hlift : Admissible (prodMeasure μ ν) (f ∘ WithLp.sndL 2 ℝ E F) :=
    Admissible.comp_projection _ isometry_adjoint_sndL measurePreserving_prod_snd hf
  have hv := h.variance_le hlift
  rwa [variance_comp_projection _ measurePreserving_prod_snd hf.memLp_two,
    energy_comp_projection _ isometry_adjoint_sndL measurePreserving_prod_snd hf] at hv

/-- Source: local infimum consequence of `Holds.of_prod_left`.
This is the first-factor lower bound needed for the manuscript's product identity. -/
theorem constant_left_le_prod : constant μ ≤ constant (prodMeasure μ ν) :=
  le_constant fun _ hC ↦ constant_le hC.of_prod_left

/-- Source: local infimum consequence of `Holds.of_prod_right`.
This is the second-factor lower bound needed for the manuscript's product identity. -/
theorem constant_right_le_prod : constant ν ≤ constant (prodMeasure μ ν) :=
  le_constant fun _ hC ↦ constant_le hC.of_prod_right

end ProductMarginals

/-- Source: the binary case of the manuscript's Theorem 3.4, linked above.
For the local `Admissible` domain, coordinate lifting gives the reverse bounds and
`constant_prod_le` gives the upper bound. `ENNReal` includes infinite constants. -/
theorem constant_prod_eq :
    constant (prodMeasure μ ν) = max (constant μ) (constant ν) :=
  le_antisymm constant_prod_le (max_le constant_left_le_prod constant_right_le_prod)

end FunctionalInequalities.Poincare.SmoothTest
