import FunctionalInequalities.Analysis.Vector.Graph.CoareaJacobian
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Scope audit for the codimension-`m` fibre Jacobian

**What is proved.**  The two densities of the codimension-`m` coarea formula match: the ambient
one, `coareaJacobian (fderiv ℝ u x)`, and the graph area density
`normDet (graphMapLinear ι κ (Dγ y))` that the normalized graph area formula integrates.  The
linear form is `coareaJacobian_eq_normDet_mul_normDet_graphMapLinear`, the `C¹` form along a level
family is `normDet_fderiv_mul_coareaJacobian`.  Their codimension-one specialization is literally
the already proved scalar identity `abs_deriv_mul_norm_gradient`.

**What is not proved.**  *No coarea formula.*  The regular case of the codimension-`m` coarea
formula additionally needs a parametric implicit-function chart in codimension `m` and a fibrewise
`m`-dimensional change of variables; neither is proved here.  Nothing
about the critical set, sharp Sard, or the Cheeger comparisons is touched.

**The codimension hypothesis is necessary**, and `fails_without_codimension` with `necessity`
below exhibit the failure rather than asserting it: with the zero subspace of `ℝ²` as parameter
space and `ℝ` as target, every other hypothesis holds, the right-hand side is `0` and the left-hand
side is not.

**A second route-statement error, reported and corrected rather than quietly fixed.**  In
`research/audits/Graph/AreaFormulaRouteStatements.lean`, obligation **`A0`** — the route's target,
the Federer area formula — carries **exactly the same normalization defect** as the graph
obligation `B1` (see `GraphAreaAudit.lean`): it pairs the **raw** `μH[finrank H]` on the left with
**Lebesgue** measure on the right.  `route_A0_false` below **proves that statement false**, by
`g = id` on `ℝ²` and the closed unit ball: the two sides differ by `2² / ω₂ = 4 / π`.  The corrected
pairings are raw with raw, or `hausdorffNormalized` with Lebesgue, exactly as for the graph case.
The localization obligation of the same route file writes the same mis-pairing, but in its
hypothesis *and* its conclusion, so the constant cancels and it is **not** falsified by it; its
hypothesis is nevertheless not the true local area formula, so as written it cannot be chained with
the intended meaning of the target.  The measurability, additivity, comparison and degenerate-part
obligations and the normalized graph obligation pair their measures consistently and are not
affected.  The route statements file is left **byte-unchanged**.
-/

noncomputable section

open Set MeasureTheory Module FunctionalInequalities FunctionalInequalities.Analysis
open scoped ENNReal NNReal RealInnerProductSpace

namespace CoareaGraphJacobianAudit

section Restatements

variable {H K V W : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K] [FiniteDimensional ℝ K]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]

/-- **The linear identity, restated independently** and discharged through named arguments. -/
theorem linear_identity (ι : H →ₗᵢ[ℝ] V) (κ : K →ₗᵢ[ℝ] V)
    (hperp : ∀ (y : H) (z : K), ⟪ι y, κ z⟫ = (0 : ℝ))
    (hspan : ∀ x : V, ι (graphProj ι x) + κ (graphProj κ x) = x)
    (hdim : finrank ℝ K = finrank ℝ W) (L : V →L[ℝ] W) (A : H →L[ℝ] K)
    (hA : ∀ y : H, L (κ (A y)) = -L (ι y)) :
    coareaJacobian L
      = LinearMap.normDet ((L ∘L κ.toContinuousLinearMap : K →L[ℝ] W) : K →ₗ[ℝ] W)
        * LinearMap.normDet ((graphMapLinear ι κ A : H →ₗ[ℝ] V)) := by
  refine coareaJacobian_eq_normDet_mul_normDet_graphMapLinear ⟨hperp, hspan⟩ hdim L ?_
  refine ContinuousLinearMap.ext fun y => ?_
  simpa using hA y

/-- **The `C¹` identity, restated independently.**  The level family is taken on the whole space, so
no finiteness, boundedness or regular-value hypothesis is available or used. -/
theorem level_family_identity (ι : H →ₗᵢ[ℝ] V) (κ : K →ₗᵢ[ℝ] V)
    (hs : IsVectorGraphSplitting ι κ) (hdim : finrank ℝ K = finrank ℝ W)
    (ψ : H × W → K) (hψ : ContDiff ℝ 1 ψ) (u : V → W)
    (hlevel : ∀ p : H × W, u (ι p.1 + κ (ψ p)) = p.2)
    (hu : Differentiable ℝ u) (y₀ : H) (t₀ : W) :
    LinearMap.normDet ((fderiv ℝ (fun t => ψ (y₀, t)) t₀ : W →ₗ[ℝ] K))
        * coareaJacobian (fderiv ℝ u (ι y₀ + κ (ψ (y₀, t₀))))
      = LinearMap.normDet
          ((graphMapLinear ι κ (fderiv ℝ (fun y => ψ (y, t₀)) y₀) : H →ₗ[ℝ] V)) :=
  normDet_fderiv_mul_coareaJacobian hs hdim isOpen_univ hψ.contDiffOn
    (fun p _ => hlevel p) (mem_univ _) (hu _)

/-- A **zero-dimensional parameter space** is inside the linear statement: the fibre is a point and
the graph factor is `1`. -/
theorem zero_dimensional_parameter (ι : EuclideanSpace ℝ (Fin 0) →ₗᵢ[ℝ] V) (κ : K →ₗᵢ[ℝ] V)
    (hs : IsVectorGraphSplitting ι κ) (hdim : finrank ℝ K = finrank ℝ W) (L : V →L[ℝ] W)
    (A : EuclideanSpace ℝ (Fin 0) →L[ℝ] K)
    (hA : (L ∘L κ.toContinuousLinearMap) ∘L A = -(L ∘L ι.toContinuousLinearMap)) :
    coareaJacobian L
      = LinearMap.normDet ((L ∘L κ.toContinuousLinearMap : K →L[ℝ] W) : K →ₗ[ℝ] W) := by
  rw [coareaJacobian_eq_normDet_mul_normDet_graphMapLinear hs hdim L hA,
    LinearMap.normDet_of_subsingleton
      ((graphMapLinear ι κ A : EuclideanSpace ℝ (Fin 0) →ₗ[ℝ] V)), mul_one]

omit [FiniteDimensional ℝ W] in
/-- **The hypotheses are satisfiable at every regular point**: the kernel of a surjective
differential and its orthogonal complement form a splitting whose normal factor has exactly the
dimension of the target. -/
theorem regular_point_data (L : V →L[ℝ] W) (hL : Function.Surjective (L : V →ₗ[ℝ] W)) :
    IsVectorGraphSplitting (LinearMap.ker (L : V →ₗ[ℝ] W)).subtypeₗᵢ
        ((LinearMap.ker (L : V →ₗ[ℝ] W))ᗮ).subtypeₗᵢ ∧
      finrank ℝ ((LinearMap.ker (L : V →ₗ[ℝ] W))ᗮ : Submodule ℝ V) = finrank ℝ W :=
  ⟨isVectorGraphSplitting_orthogonal _, finrank_orthogonal_ker_eq L hL⟩

/-- With a normal factor strictly larger than the target the normal volume factor vanishes. -/
theorem normDet_eq_zero_of_finrank_lt (Q : K →ₗ[ℝ] W) (h : finrank ℝ W < finrank ℝ K) :
    LinearMap.normDet Q = 0 := by
  rw [LinearMap.normDet_eq_zero_iff_rank_range_ne]
  have hle := Submodule.finrank_le (LinearMap.range Q)
  omega
/-- **The codimension hypothesis cannot be dropped.**  With everything else in place but
`finrank K` strictly above `finrank W`, the right-hand side is `0` while the left-hand side is not,
so the identity is false. -/
theorem fails_without_codimension {ι : H →ₗᵢ[ℝ] V} {κ : K →ₗᵢ[ℝ] V}
    (hlt : finrank ℝ W < finrank ℝ K) (L : V →L[ℝ] W)
    (hL : Function.Surjective (L : V →ₗ[ℝ] W)) (A : H →L[ℝ] K) :
    coareaJacobian L
      ≠ LinearMap.normDet ((L ∘L κ.toContinuousLinearMap : K →L[ℝ] W) : K →ₗ[ℝ] W)
        * LinearMap.normDet ((graphMapLinear ι κ A : H →ₗ[ℝ] V)) := by
  rw [normDet_eq_zero_of_finrank_lt _ hlt, zero_mul]
  exact (coareaJacobian_ne_zero_iff L).2 hL

end Restatements

/-! ### The failure is not vacuous -/

section Necessity

/-- The two-dimensional model space. -/
abbrev E : Type := EuclideanSpace ℝ (Fin 2)

/-- The zero parameter space inside `E`; its orthogonal complement is all of `E`. -/
abbrev Z : Submodule ℝ E := ⊥

/-- **A concrete failure.**  Parameter space the zero subspace of `ℝ²`, normal factor its
orthogonal complement — the whole plane — and target `ℝ`.  Orthogonality, spanning and the slope
equation all hold; only `finrank K = finrank W` fails, and the identity fails with it. -/
theorem necessity :
    ∃ (L : E →L[ℝ] ℝ) (A : Z →L[ℝ] (Zᗮ : Submodule ℝ E)),
      IsVectorGraphSplitting Z.subtypeₗᵢ (Zᗮ).subtypeₗᵢ ∧
      ((L ∘L (Zᗮ).subtypeₗᵢ.toContinuousLinearMap) ∘L A
        = -(L ∘L Z.subtypeₗᵢ.toContinuousLinearMap)) ∧
      finrank ℝ (Zᗮ : Submodule ℝ E) ≠ finrank ℝ ℝ ∧
      coareaJacobian L
        ≠ LinearMap.normDet
            ((L ∘L (Zᗮ).subtypeₗᵢ.toContinuousLinearMap : (Zᗮ : Submodule ℝ E) →L[ℝ] ℝ)
              : (Zᗮ : Submodule ℝ E) →ₗ[ℝ] ℝ)
          * LinearMap.normDet
            ((graphMapLinear Z.subtypeₗᵢ (Zᗮ).subtypeₗᵢ A : Z →ₗ[ℝ] E)) := by
  classical
  have htop : (Zᗮ : Submodule ℝ E) = ⊤ := Submodule.bot_orthogonal_eq_top
  have hdimE : finrank ℝ E = 2 := finrank_euclideanSpace_fin
  have hdimZ : finrank ℝ (Zᗮ : Submodule ℝ E) = 2 := by
    rw [htop, finrank_top, hdimE]
  refine ⟨innerSL ℝ (EuclideanSpace.single 0 (1 : ℝ)), 0,
    isVectorGraphSplitting_orthogonal Z, ?_, ?_, ?_⟩
  · refine ContinuousLinearMap.ext fun y => ?_
    have hy : y = 0 := Subsingleton.elim _ _
    simp [hy]
  · rw [hdimZ, finrank_self]
    norm_num
  · refine fails_without_codimension ?_ _ ?_ 0
    · rw [hdimZ, finrank_self]; omega
    · intro c
      refine ⟨EuclideanSpace.single 0 c, ?_⟩
      simp [EuclideanSpace.inner_single_left]

end Necessity

/-! ### The Federer area-formula target is false as written -/

section RouteA0

/-- `ω₂ = π`. -/
theorem unitBallVolume_two : KLS.unitBallVolume 2 = Real.pi := by
  have hg : Real.Gamma (((2 : ℕ) : ℝ) / 2 + 1) = 1 := by norm_num
  rw [KLS.unitBallVolume, hg, div_one, sq, Real.mul_self_sqrt Real.pi_nonneg]

/-- The normalization constant between the raw and the normalized convention is `4 / π ≠ 1` in
dimension two; it is `1` only for `k ≤ 1`. -/
theorem normalization_constant_ne_one : (2 : ℝ) ^ (2 : ℕ) / KLS.unitBallVolume 2 ≠ 1 := by
  rw [unitBallVolume_two]
  intro h
  rw [div_eq_one_iff_eq Real.pi_pos.ne'] at h
  have h4 := Real.pi_lt_four
  norm_num at h
  linarith

/-- The plane, where the two conventions already disagree. -/
abbrev Plane : Type := EuclideanSpace ℝ (Fin 2)

/-- The raw Hausdorff measure of the unit ball of the plane is **not** its Lebesgue measure. -/
theorem raw_ne_volume :
    μH[((finrank ℝ Plane : ℕ) : ℝ)] (Metric.closedBall (0 : Plane) 1)
      ≠ (volume : Measure Plane) (Metric.closedBall (0 : Plane) 1) := by
  have hdim : finrank ℝ Plane = 2 := finrank_euclideanSpace_fin
  have hnn : (0 : ℝ) ≤ (2 : ℝ) ^ (2 : ℕ) / KLS.unitBallVolume 2 := by
    rw [unitBallVolume_two]; positivity
  have hpos : (0 : ℝ≥0∞) < volume (Metric.closedBall (0 : Plane) 1) :=
    Metric.measure_closedBall_pos volume 0 one_pos
  have htop : volume (Metric.closedBall (0 : Plane) 1) ≠ ⊤ := measure_closedBall_lt_top.ne
  rw [hausdorffMeasure_finrank_eq_smul_volume (V := Plane), Measure.smul_apply, smul_eq_mul, hdim]
  intro h
  have h' : ENNReal.ofReal ((2 : ℝ) ^ (2 : ℕ) / KLS.unitBallVolume 2)
      * volume (Metric.closedBall (0 : Plane) 1)
        = 1 * volume (Metric.closedBall (0 : Plane) 1) := by
    rw [one_mul]; exact h
  have key := (ENNReal.mul_left_inj hpos.ne' htop).mp h'
  rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm,
    ENNReal.ofReal_eq_ofReal_iff hnn zero_le_one] at key
  exact normalization_constant_ne_one key

/-- **Route statement `A0` of `AreaFormulaRouteStatements.lean` is false as written.**  Its text
is reproduced verbatim except that the universe-polymorphic `Type*` is specialized to `Type`; the
route's own statement specializes to this one, so it is false a fortiori.  The witness is the
identity map of the plane on the closed unit ball: the left-hand side is the raw `μH[2]`, the
right-hand side is Lebesgue measure, and they differ by `4 / π`.  This is the same defect that
`GraphAreaAudit.lean` records for the graph obligation. -/
theorem route_A0_false :
    ¬ (∀ {H V : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
        [MeasurableSpace H] [BorelSpace H]
        [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
        [MeasurableSpace V] [BorelSpace V]
        {g : H → V} {s : Set H}, ContDiff ℝ 1 g → Set.InjOn g s → MeasurableSet s →
        μH[(Module.finrank ℝ H : ℝ)] (g '' s)
          = ∫⁻ y in s, ENNReal.ofReal (LinearMap.normDet ((fderiv ℝ g y : H →ₗ[ℝ] V)))
              ∂(volume : Measure H)) := by
  intro hA0
  have h := hA0 (H := Plane) (V := Plane) (g := id) (s := Metric.closedBall 0 1)
    contDiff_id (Set.injOn_id _) measurableSet_closedBall
  rw [Set.image_id] at h
  have hone : ∀ y : Plane, LinearMap.normDet ((fderiv ℝ (id : Plane → Plane) y : Plane →ₗ[ℝ] Plane))
      = 1 := by
    intro y
    rw [fderiv_id, ContinuousLinearMap.coe_id, LinearMap.normDet_id]
  simp only [hone, ENNReal.ofReal_one, setLIntegral_one] at h
  exact raw_ne_volume h

end RouteA0

end CoareaGraphJacobianAudit

/-! ### Axiom audit: every report is standard-only -/

#print axioms FunctionalInequalities.Analysis.det_id_add_comp_comm
#print axioms FunctionalInequalities.Analysis.normDet_adjoint
#print axioms FunctionalInequalities.Analysis.coareaJacobian_eq_normDet
#print axioms FunctionalInequalities.Analysis.graphProj_adjoint
#print axioms FunctionalInequalities.Analysis.IsVectorGraphSplitting.perp'
#print axioms FunctionalInequalities.Analysis.IsVectorGraphSplitting.proj_left
#print axioms FunctionalInequalities.Analysis.IsVectorGraphSplitting.proj_right
#print axioms FunctionalInequalities.Analysis.IsVectorGraphSplitting.norm_add_sq
#print axioms FunctionalInequalities.Analysis.IsVectorGraphSplitting.comp_adjoint
#print axioms FunctionalInequalities.Analysis.isVectorGraphSplitting_orthogonal
#print axioms FunctionalInequalities.Analysis.finrank_orthogonal_ker_eq
#print axioms FunctionalInequalities.Analysis.splitVectorIsometry
#print axioms FunctionalInequalities.Analysis.splitVectorIsometry_apply
#print axioms FunctionalInequalities.Analysis.measurePreserving_split
#print axioms FunctionalInequalities.Analysis.coareaJacobian_eq_normDet_mul_normDet_graphMapLinear
#print axioms FunctionalInequalities.Analysis.normDet_fderiv_mul_coareaJacobian
#print axioms FunctionalInequalities.Analysis.graphMapLinear_eq_graphLinear
#print axioms FunctionalInequalities.Analysis.normDet_graphMapLinear_eq_graphJacobian
#print axioms FunctionalInequalities.Analysis.abs_deriv_mul_norm_gradient_of_vectorGraphSplitting
#print axioms CoareaGraphJacobianAudit.linear_identity
#print axioms CoareaGraphJacobianAudit.level_family_identity
#print axioms CoareaGraphJacobianAudit.zero_dimensional_parameter
#print axioms CoareaGraphJacobianAudit.regular_point_data
#print axioms CoareaGraphJacobianAudit.normDet_eq_zero_of_finrank_lt
#print axioms CoareaGraphJacobianAudit.fails_without_codimension
#print axioms CoareaGraphJacobianAudit.necessity
#print axioms CoareaGraphJacobianAudit.unitBallVolume_two
#print axioms CoareaGraphJacobianAudit.normalization_constant_ne_one
#print axioms CoareaGraphJacobianAudit.raw_ne_volume
#print axioms CoareaGraphJacobianAudit.route_A0_false
