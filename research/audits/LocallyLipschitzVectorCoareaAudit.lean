import FunctionalInequalities.Analysis.Lipschitz.Local
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Discharge audit for the locally Lipschitz vector coarea route

Every obligation of `research/audits/LocallyLipschitzVectorCoareaRouteStatements.lean` except the
target `N0` is restated here **verbatim** and **proved**.  The route file contains only `#check`s;
this file contains only theorems, and each one is discharged from
`FunctionalInequalities/Analysis/Lipschitz/{Extension,Annuli,Local}.lean`.

**`N0` is not proved here, and nothing in this file proves a coarea formula.**  `X5` is the
implication `L0 → N0`: it takes the codimension-`m` coarea formula for **globally Lipschitz** maps
as a hypothesis, and that formula is still open in
`research/audits/LipschitzVectorCoareaRouteStatements.lean`.  `X5` is the whole content of the
reduction; `N0` follows from it the moment `L0` is proved, and not before.

`D1` is a diagnostic, not a step: it exhibits a map that is locally Lipschitz, globally Lipschitz
for no constant, and not differentiable at the origin, so that neither `L0` nor `R9` reaches it.
`C1` and `C2` record that `N0` would be a common generalization of both.

Every report below uses only `propext`, `Classical.choice` and `Quot.sound`.  No work-in-progress
module is imported.
-/

noncomputable section

open Metric MeasureTheory Module Set FunctionalInequalities FunctionalInequalities.Analysis
open scoped ENNReal NNReal

namespace LocallyLipschitzVectorCoareaAudit

/-! ### `X1` — a vector Lipschitz extension with some constant -/

/-- **`X1`** restated verbatim from the route file and discharged. -/
theorem route_X1 : ∀ {α W : Type*} [PseudoMetricSpace α]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    {u : α → W} {s : Set α} {K : ℝ≥0}, LipschitzOnWith K u s →
    ∃ (K' : ℝ≥0) (w : α → W), LipschitzWith K' w ∧ EqOn w u s := by
  intro α W _ _ _ _ u s K hu
  exact exists_lipschitzWith_eqOn_of_lipschitzOnWith hu

/-! ### `X2` — Lipschitz on every closed ball -/

/-- **`X2`** restated verbatim from the route file and discharged. -/
theorem route_X2 : ∀ {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    {u : V → W}, LocallyLipschitz u → ∀ r : ℝ, ∃ K : ℝ≥0, LipschitzOnWith K u (closedBall 0 r) := by
  intro V W _ _ _ _ _ u hu r
  exact exists_lipschitzOnWith_closedBall hu r

/-! ### `X3` — the half-open annuli -/

/-- **`X3`** restated verbatim from the route file and discharged. -/
theorem route_X3 : ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V],
    (∀ k : ℕ, MeasurableSet (ball (0 : V) (k + 1) \ ball (0 : V) k)) ∧
    Pairwise (fun i j : ℕ =>
      Disjoint (ball (0 : V) (i + 1) \ ball (0 : V) i) (ball (0 : V) (j + 1) \ ball (0 : V) j)) ∧
    (⋃ k : ℕ, ball (0 : V) (k + 1) \ ball (0 : V) k) = univ ∧
    ∀ k : ℕ, ∀ x ∈ ball (0 : V) (k + 1) \ ball (0 : V) k, ball (0 : V) (k + 1) ∈ nhds x := by
  intro V _ _ _ _ _
  exact ⟨fun k => measurableSet_annulus k, pairwise_disjoint_annulus V, iUnion_annulus V,
    fun _ _ hx => ball_mem_nhds_of_mem_annulus hx⟩

/-! ### `X4` — agreement near a point transfers density and slice -/

/-- **`X4`** restated verbatim from the route file and discharged. -/
theorem route_X4 : ∀ {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {u v : V → W} {P : Set V} {O : Set V}, IsOpen O → P ⊆ O → EqOn u v O →
    (∀ x ∈ P, fderiv ℝ u x = fderiv ℝ v x) ∧ ∀ t : W, P ∩ {x | u x = t} = P ∩ {x | v x = t} := by
  intro V W _ _ _ _ u v P O hO hPO huv
  exact fderiv_eq_and_inter_levelSet_eq_of_eqOn hO hPO huv

/-! ### `X5` — the assembly: `L0` on each annulus, then countable additivity

The dimension relation `k + finrank ℝ W = finrank ℝ V` is part of the route statement and is kept,
but the reduction never uses it: it belongs to the globally Lipschitz formula, which enters as a
hypothesis and carries its own. -/

/-- **`X5`** restated verbatim from the route file and discharged.  The globally Lipschitz coarea
formula is the hypothesis, **not** a theorem of this repository. -/
theorem route_X5 : ∀ {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    [MeasurableSpace W] [BorelSpace W] {k : ℕ},
    k + finrank ℝ W = finrank ℝ V →
    (∀ {S : Set V} {u : V → W} {K : ℝ≥0} {g : V → ℝ≥0∞}, LipschitzWith K u →
      MeasurableSet S → Measurable g →
      AEMeasurable (fun t : W => ∫⁻ y in S ∩ {x : V | u x = t}, g y ∂(KLS.hausdorffNormalized V k))
          (volume : Measure W) ∧
        (∫⁻ x in S, ENNReal.ofReal (coareaJacobian (fderiv ℝ u x)) * g x ∂(volume : Measure V)
          = ∫⁻ t, ∫⁻ y in S ∩ {x : V | u x = t}, g y ∂(KLS.hausdorffNormalized V k)
              ∂(volume : Measure W))) →
    ∀ {S : Set V} {u : V → W} {g : V → ℝ≥0∞}, LocallyLipschitz u →
      MeasurableSet S → Measurable g →
      AEMeasurable (fun t : W => ∫⁻ y in S ∩ {x : V | u x = t}, g y ∂(KLS.hausdorffNormalized V k))
          (volume : Measure W) ∧
        (∫⁻ x in S, ENNReal.ofReal (coareaJacobian (fderiv ℝ u x)) * g x ∂(volume : Measure V)
          = ∫⁻ t, ∫⁻ y in S ∩ {x : V | u x = t}, g y ∂(KLS.hausdorffNormalized V k)
              ∂(volume : Measure W)) := by
  intro V W _ _ _ _ _ _ _ _ _ _ k _hk hL S u g hu hS hg
  exact coarea_of_locallyLipschitz_of_lipschitz (k := k) (fun {_ _ _ _} hK hS' hg' => hL hK hS' hg')
    hu hS hg

/-! ### `D1` — the strictness witness

`x ↦ ‖x‖² e₀ + ‖x‖ e₁` on the Euclidean plane: a `C¹` term plus a Lipschitz term, so locally
Lipschitz; the first coordinate grows quadratically, so no global constant works; the second
coordinate is `‖x‖`, so it is not differentiable at the origin. -/

/-- The witness of `D1`. -/
private def witness : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) := fun x =>
  ‖x‖ ^ 2 • EuclideanSpace.single 0 1 + ‖x‖ • EuclideanSpace.single 1 1

theorem witness_locallyLipschitz : LocallyLipschitz witness := by
  have h1 : ContDiff ℝ 1 fun x : EuclideanSpace ℝ (Fin 2) =>
      ‖x‖ ^ 2 • (EuclideanSpace.single 0 1 : EuclideanSpace ℝ (Fin 2)) :=
    (contDiff_norm_sq ℝ).smul contDiff_const
  have h2 : LipschitzWith ‖(EuclideanSpace.single 1 1 : EuclideanSpace ℝ (Fin 2))‖₊
      fun x : EuclideanSpace ℝ (Fin 2) =>
        ‖x‖ • (EuclideanSpace.single 1 1 : EuclideanSpace ℝ (Fin 2)) := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    have h : dist (‖x‖ • (EuclideanSpace.single 1 1 : EuclideanSpace ℝ (Fin 2)))
          (‖y‖ • (EuclideanSpace.single 1 1 : EuclideanSpace ℝ (Fin 2)))
        = |‖x‖ - ‖y‖| * ‖(EuclideanSpace.single 1 1 : EuclideanSpace ℝ (Fin 2))‖ := by
      rw [dist_eq_norm, ← sub_smul, norm_smul]
      simp [Real.norm_eq_abs]
    rw [h, coe_nnnorm,
      mul_comm ‖(EuclideanSpace.single 1 1 : EuclideanSpace ℝ (Fin 2))‖ (dist x y)]
    gcongr
    rw [dist_eq_norm]
    exact abs_norm_sub_norm_le x y
  exact h1.locallyLipschitz.add h2.locallyLipschitz

/-- The witness is globally Lipschitz for **no** constant: its first coordinate is `‖x‖²`. -/
theorem witness_not_lipschitzWith : ∀ K : ℝ≥0, ¬ LipschitzWith K witness := by
  intro K hK
  set x₀ : EuclideanSpace ℝ (Fin 2) := ((K : ℝ) + 1) • EuclideanSpace.single 0 1 with hx₀
  have hpos : (0 : ℝ) ≤ (K : ℝ) + 1 := by positivity
  have hnorm : ‖x₀‖ = (K : ℝ) + 1 := by
    rw [hx₀, norm_smul]
    simp [abs_of_nonneg hpos]
  have h0 : witness 0 = 0 := by simp [witness]
  have hcoord : dist (witness x₀ 0) (witness 0 0) ≤ dist (witness x₀) (witness 0) :=
    PiLp.dist_apply_le _ _ 0
  have hval : witness x₀ 0 = ‖x₀‖ ^ 2 := by simp [witness]
  have hz : witness 0 0 = 0 := by rw [h0]; simp
  rw [hval, hz, Real.dist_eq, sub_zero, abs_of_nonneg (by positivity), hnorm] at hcoord
  have hle := hK.dist_le_mul x₀ 0
  rw [dist_zero_right, hnorm] at hle
  have hfinal : ((K : ℝ) + 1) ^ 2 ≤ (K : ℝ) * ((K : ℝ) + 1) := le_trans hcoord hle
  nlinarith [K.coe_nonneg]

/-- The witness is **not** differentiable at the origin: its second coordinate is `‖x‖`. -/
theorem witness_not_differentiableAt : ¬ DifferentiableAt ℝ witness 0 := by
  intro h
  have hproj : DifferentiableAt ℝ
      (⇑(EuclideanSpace.proj (1 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ) ∘ witness) 0 :=
    (EuclideanSpace.proj (1 : Fin 2)).differentiableAt.comp 0 h
  have heq : (⇑(EuclideanSpace.proj (1 : Fin 2) : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ) ∘ witness)
      = fun x : EuclideanSpace ℝ (Fin 2) => ‖x‖ := by
    funext x
    simp [witness]
  rw [heq] at hproj
  exact not_differentiableAt_norm_zero (EuclideanSpace ℝ (Fin 2)) hproj

/-- **`D1`** restated verbatim from the route file and discharged. -/
theorem route_D1 : ∃ u : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2),
    LocallyLipschitz u ∧ (∀ K : ℝ≥0, ¬ LipschitzWith K u) ∧ ¬ DifferentiableAt ℝ u 0 :=
  ⟨witness, witness_locallyLipschitz, witness_not_lipschitzWith, witness_not_differentiableAt⟩

/-! ### `C1`, `C2` — consistency -/

/-- **`C1`** restated verbatim from the route file and discharged. -/
theorem route_C1 : ∀ {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    {u : V → W} {K : ℝ≥0}, LipschitzWith K u → LocallyLipschitz u := by
  intro V W _ _ _ _ _ _ u K hu
  exact hu.locallyLipschitz

/-- **`C2`** restated verbatim from the route file and discharged. -/
theorem route_C2 : ∀ {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    {u : V → W}, ContDiff ℝ 1 u → LocallyLipschitz u := by
  intro V W _ _ _ _ _ _ u hu
  exact hu.locallyLipschitz

end LocallyLipschitzVectorCoareaAudit

/-! ### Axiom audit: every report is standard-only

#### The library declarations -/

#print axioms FunctionalInequalities.Analysis.exists_lipschitzWith_eqOn_of_lipschitzOnWith
#print axioms FunctionalInequalities.Analysis.exists_lipschitzOnWith_closedBall
#print axioms FunctionalInequalities.Analysis.measurableSet_annulus
#print axioms FunctionalInequalities.Analysis.pairwise_disjoint_annulus
#print axioms FunctionalInequalities.Analysis.iUnion_annulus
#print axioms FunctionalInequalities.Analysis.ball_mem_nhds_of_mem_annulus
#print axioms FunctionalInequalities.Analysis.annulus_subset_ball
#print axioms FunctionalInequalities.Analysis.fderiv_eq_and_inter_levelSet_eq_of_eqOn
#print axioms FunctionalInequalities.Analysis.coarea_of_locallyLipschitz_of_lipschitz

/-! #### The route obligations, verbatim -/

#print axioms LocallyLipschitzVectorCoareaAudit.route_X1
#print axioms LocallyLipschitzVectorCoareaAudit.route_X2
#print axioms LocallyLipschitzVectorCoareaAudit.route_X3
#print axioms LocallyLipschitzVectorCoareaAudit.route_X4
#print axioms LocallyLipschitzVectorCoareaAudit.route_X5

/-! #### The strictness witness and the consistency checks -/

#print axioms LocallyLipschitzVectorCoareaAudit.witness_locallyLipschitz
#print axioms LocallyLipschitzVectorCoareaAudit.witness_not_lipschitzWith
#print axioms LocallyLipschitzVectorCoareaAudit.witness_not_differentiableAt
#print axioms LocallyLipschitzVectorCoareaAudit.route_D1
#print axioms LocallyLipschitzVectorCoareaAudit.route_C1
#print axioms LocallyLipschitzVectorCoareaAudit.route_C2

/-! #### The target `N0`, verbatim, now that `L0` is proved (2026-09-19, integration): `X5` applied to `Analysis.coarea_of_lipschitz` -/

theorem LocallyLipschitzVectorCoareaAudit.route_N0 : ∀ {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    [MeasurableSpace W] [BorelSpace W]
    {S : Set V} {u : V → W} {g : V → ℝ≥0∞} {k : ℕ},
    k + finrank ℝ W = finrank ℝ V → LocallyLipschitz u →
    MeasurableSet S → Measurable g →
    AEMeasurable (fun t : W => ∫⁻ y in S ∩ {x : V | u x = t}, g y ∂(KLS.hausdorffNormalized V k))
        (volume : Measure W) ∧
      (∫⁻ x in S, ENNReal.ofReal (coareaJacobian (fderiv ℝ u x)) * g x ∂(volume : Measure V)
        = ∫⁻ t, ∫⁻ y in S ∩ {x : V | u x = t}, g y ∂(KLS.hausdorffNormalized V k)
            ∂(volume : Measure W)) :=
  fun hk hu hS hg => FunctionalInequalities.Analysis.coarea_of_locallyLipschitz hk hu hS hg

#print axioms FunctionalInequalities.Analysis.coarea_of_locallyLipschitz
#print axioms LocallyLipschitzVectorCoareaAudit.route_N0
