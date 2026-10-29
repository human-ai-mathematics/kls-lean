import FunctionalInequalities.Analysis.Vector.Coarea.Lipschitz
import FunctionalInequalities.Analysis.Lipschitz.Local
import FunctionalInequalities.Analysis.Coarea.Lipschitz
import Mathlib.Analysis.Calculus.Deriv.Abs

/-!
# Strict audit client for the codimension-`m` coarea formula of Lipschitz maps

Independent client of `Analysis/Lipschitz/{Componentwise,Refinement,VectorPieces}.lean` and `Analysis/Vector/Coarea/Lipschitz.lean`.
Every obligation of the Lipschitz vector-coarea route — whose statements are recorded in
`research/audits/Vector/LipschitzCoareaRouteStatements.lean` as `#check`s — is **restated here
verbatim**, binder for binder and instance for instance, as a theorem, and discharged from the library
modules. `route_M2` also checks the locally Lipschitz follow-on using
`Analysis/Lipschitz/Local.lean`; it remains a separate contract from `route_L0`.

**What is proved.**  `route_L0` is the target: `Analysis.coarea_of_contDiff` with `ContDiff ℝ 1 u`
replaced by `LipschitzWith K u` and nothing else changed.  `route_V1` is the vector `C¹` pieces,
`route_V2` the codimension-`m` null slicing of a Lebesgue-null set, `route_V3` the countable common
refinement, `route_V4'`, `route_V4''` and `route_V4` the componentwise calculus, and `route_V5` the
assembly stated as an implication, so that `route_L0` is `route_V5` applied to `route_V1`.

**What is not proved.**  No Sard theorem: nothing is claimed about the measure of the set of
critical values.  The locally Lipschitz follow-on is the separate `route_M2` theorem below. Nothing about the Cheeger–Buser line or the
sharp finite-regularity Sard.

**Why the `C¹` formula is not recovered from `route_L0`.**  The two hypotheses are incomparable: a
Lipschitz map need not be `C¹` — `route_M1` proves this, with a coordinate absolute value on a line, in an arbitrary universe — and a `C¹` map on
a non-compact domain need not be Lipschitz.  So there is no implication either way at the level of
the hypotheses, and in place of a recovery this file checks the **boundary cases** the statement is
supposed to survive: a zero-dimensional target (`zero_dimensional_target`), an equidimensional pair
at `k = 0` (`equidimensional`), a constant map, whose density vanishes and whose every level
therefore carries a null slice integral (`constant_map`), and the codimension-one specialization
`scalar_comparison`, which returns the already proved scalar statement
`KLS.coarea_of_lipschitz` — density `‖gradient u x‖ₑ` through `Analysis.coareaJacobian_fderiv`
(itself `Analysis.coareaJacobian_eq_norm_toDual_symm`), fibre measure `KLS.surfaceMeasure V` — from
`route_L0` alone, without naming the scalar theorem in its proof.
-/

noncomputable section

open MeasureTheory Set Module FunctionalInequalities FunctionalInequalities.Analysis
open scoped ENNReal NNReal

namespace LipschitzVectorCoareaAudit

/-! ### The obligations, restated verbatim from the route statements file -/

/-- **`L0`** of `LipschitzCoareaRouteStatements.lean`, the target of the route. -/
theorem route_L0 : ∀ {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    [MeasurableSpace W] [BorelSpace W]
    {S : Set V} {u : V → W} {K : ℝ≥0} {g : V → ℝ≥0∞} {k : ℕ},
    k + finrank ℝ W = finrank ℝ V → LipschitzWith K u →
    MeasurableSet S → Measurable g →
    AEMeasurable (fun t : W => ∫⁻ y in S ∩ {x : V | u x = t}, g y ∂(KLS.hausdorffNormalized V k))
        (volume : Measure W) ∧
      (∫⁻ x in S, ENNReal.ofReal (coareaJacobian (fderiv ℝ u x)) * g x ∂(volume : Measure V)
        = ∫⁻ t, ∫⁻ y in S ∩ {x : V | u x = t}, g y ∂(KLS.hausdorffNormalized V k)
            ∂(volume : Measure W)) := by
  intro V W _ _ _ _ _ _ _ _ _ _ S u K g k hk hu hS hg
  exact Analysis.coarea_of_lipschitz (S := S) (u := u) (K := K) (g := g) (k := k) hk hu hS hg

/-- **`V1`** of `LipschitzCoareaRouteStatements.lean`, the vector `C¹` pieces. -/
theorem route_V1 : ∀ {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    {u : V → W} {K : ℝ≥0}, LipschitzWith K u →
    ∃ (S : ℕ → Set V) (v : ℕ → V → W),
      (∀ j, MeasurableSet (S j)) ∧ Pairwise (fun i j => Disjoint (S i) (S j)) ∧
      (volume : Measure V) (⋃ j, S j)ᶜ = 0 ∧ (∀ j, ContDiff ℝ 1 (v j)) ∧
      ∀ j, ∀ x ∈ S j, DifferentiableAt ℝ u x ∧
        v j x = u x ∧ fderiv ℝ (v j) x = fderiv ℝ u x := by
  intro V W _ _ _ _ _ _ _ _ u K hu
  exact Analysis.exists_contDiff_pieces_vector (u := u) (K := K) hu

/-- **`V2`** of `LipschitzCoareaRouteStatements.lean`: the Lebesgue-null complement disappears from
almost every level. -/
theorem route_V2 : ∀ {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    [MeasurableSpace W] [BorelSpace W]
    {u : V → W} {N : Set V} {K : ℝ≥0} {k : ℕ},
    k + finrank ℝ W = finrank ℝ V → LipschitzWith K u → (volume : Measure V) N = 0 →
    ∀ᵐ t ∂(volume : Measure W), KLS.hausdorffNormalized V k (N ∩ {x : V | u x = t}) = 0 := by
  intro V W _ _ _ _ _ _ _ _ _ _ u N K k hk hu hN
  exact Analysis.ae_hausdorffNormalized_inter_levelSet_eq_zero_of_volume_eq_zero
    (u := u) (N := N) (K := K) (k := k) hk hu hN

/-- **`V3`** of `LipschitzCoareaRouteStatements.lean`: a countable common refinement of finitely
many countable partitions. -/
theorem route_V3 : ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (m : ℕ) (S : Fin m → ℕ → Set V),
    (∀ i j, MeasurableSet (S i j)) →
    (∀ i, Pairwise (fun a b => Disjoint (S i a) (S i b))) →
    (∀ i, (volume : Measure V) (⋃ j, S i j)ᶜ = 0) →
    ∃ T : ℕ → Set V, (∀ n, MeasurableSet (T n)) ∧
      Pairwise (fun a b => Disjoint (T a) (T b)) ∧
      (volume : Measure V) (⋃ n, T n)ᶜ = 0 ∧
      ∀ n, ∃ f : Fin m → ℕ, T n ⊆ ⋂ i, S i (f i) := by
  intro V _ _ _ _ _ m S hSm hSd hSnull
  exact Analysis.exists_common_refinement m S hSm hSd hSnull

/-- **`V4'`** of `LipschitzCoareaRouteStatements.lean`: the coordinates of a Lipschitz map are
Lipschitz. -/
theorem route_V4' : ∀ {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    (e : W ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ W))) {u : V → W} {K : ℝ≥0},
    LipschitzWith K u → ∀ i, LipschitzWith K (fun y => e (u y) i) := by
  intro V W _ _ _ _ _ _ e u K hu i
  exact Analysis.lipschitzWith_coord e hu i

/-- **`V4`** of `LipschitzCoareaRouteStatements.lean`: componentwise first-order agreement is
first-order agreement. -/
theorem route_V4 : ∀ {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    (e : W ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ W))) {u v : V → W} {x : V},
    DifferentiableAt ℝ u x → DifferentiableAt ℝ v x →
    (∀ i, e (v x) i = e (u x) i) →
    (∀ i, fderiv ℝ (fun y => e (v y) i) x = fderiv ℝ (fun y => e (u y) i) x) →
    v x = u x ∧ fderiv ℝ v x = fderiv ℝ u x := by
  intro V W _ _ _ _ _ _ e u v x hu hv hval hder
  exact Analysis.eq_and_fderiv_eq_of_coord e hu hv hval hder

/-- **`V4''`** of `LipschitzCoareaRouteStatements.lean`: differentiability is detected
coordinatewise. -/
theorem route_V4'' : ∀ {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    (e : W ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ W))) {u : V → W} {x : V},
    (∀ i, DifferentiableAt ℝ (fun y => e (u y) i) x) → DifferentiableAt ℝ u x := by
  intro V W _ _ _ _ _ _ e u x h
  exact Analysis.differentiableAt_of_coord e h

/-- **`V5`** of `LipschitzCoareaRouteStatements.lean`, the assembly, stated as an implication from
the conclusion of `V1`. -/
theorem route_V5 : ∀ {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    [MeasurableSpace W] [BorelSpace W]
    {S : Set V} {u : V → W} {K : ℝ≥0} {g : V → ℝ≥0∞} {k : ℕ},
    k + finrank ℝ W = finrank ℝ V → LipschitzWith K u →
    MeasurableSet S → Measurable g →
    (∃ (P : ℕ → Set V) (v : ℕ → V → W),
      (∀ j, MeasurableSet (P j)) ∧ Pairwise (fun i j => Disjoint (P i) (P j)) ∧
      (volume : Measure V) (⋃ j, P j)ᶜ = 0 ∧ (∀ j, ContDiff ℝ 1 (v j)) ∧
      ∀ j, ∀ x ∈ P j, DifferentiableAt ℝ u x ∧
        v j x = u x ∧ fderiv ℝ (v j) x = fderiv ℝ u x) →
    AEMeasurable (fun t : W => ∫⁻ y in S ∩ {x : V | u x = t}, g y ∂(KLS.hausdorffNormalized V k))
        (volume : Measure W) ∧
      (∫⁻ x in S, ENNReal.ofReal (coareaJacobian (fderiv ℝ u x)) * g x ∂(volume : Measure V)
        = ∫⁻ t, ∫⁻ y in S ∩ {x : V | u x = t}, g y ∂(KLS.hausdorffNormalized V k)
            ∂(volume : Measure W)) := by
  intro V W _ _ _ _ _ _ _ _ _ _ S u K g k hk hu hS hg hpieces
  exact Analysis.coarea_of_lipschitz_of_pieces hk hu hS hg hpieces

/-- **`M1`** of `LipschitzCoareaRouteStatements.lean`, the obstruction: a Lipschitz function need
not be `C¹`.  This is why `route_V1` is needed and why `Analysis.coarea_of_contDiff` cannot be
invoked directly on a Lipschitz map. -/
theorem route_M1 : ¬ ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V]
    {u : V → ℝ} {K : ℝ≥0}, LipschitzWith K u → ContDiff ℝ 1 u := by
  intro h
  have habs : LipschitzWith 1 (fun x : ℝ => |x|) :=
    LipschitzWith.of_dist_le_mul fun a b => by
      simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using abs_abs_sub_abs_le_abs_sub a b
  set i : ULift (Fin 1) := ULift.up 0 with hi
  set φ : ℝ →L[ℝ] EuclideanSpace ℝ (ULift (Fin 1)) :=
    ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (EuclideanSpace.single i 1) with hφdef
  have hφ : ∀ t : ℝ, (φ t) i = t := by
    intro t
    simp [hφdef]
  have hproj : LipschitzWith 1 (fun x : EuclideanSpace ℝ (ULift (Fin 1)) => x i) :=
    fun a b => by simpa using PiLp.edist_apply_le a b i
  have hf : LipschitzWith 1 (fun x : EuclideanSpace ℝ (ULift (Fin 1)) => |x i|) := by
    simpa only [one_mul, Function.comp_def] using habs.comp hproj
  have hC : ContDiff ℝ 1 (fun x : EuclideanSpace ℝ (ULift (Fin 1)) => |x i|) := h hf
  have hd : DifferentiableAt ℝ (fun t : ℝ => |t|) 0 := by
    have hcomp := (hC.differentiable one_ne_zero (φ 0)).comp 0 φ.differentiableAt
    have hrw : (fun x : EuclideanSpace ℝ (ULift (Fin 1)) => |x i|) ∘ (φ : ℝ → _)
        = fun t : ℝ => |t| := funext fun t => by simp [hφ t]
    rwa [hrw] at hcomp
  exact not_differentiableAt_abs_zero hd

/-! ### Axiom audit for the obligations -/

#print axioms LipschitzVectorCoareaAudit.route_L0
#print axioms LipschitzVectorCoareaAudit.route_V1
#print axioms LipschitzVectorCoareaAudit.route_V2
#print axioms LipschitzVectorCoareaAudit.route_V3
#print axioms LipschitzVectorCoareaAudit.route_V4
#print axioms LipschitzVectorCoareaAudit.route_V4'
#print axioms LipschitzVectorCoareaAudit.route_V4''
#print axioms LipschitzVectorCoareaAudit.route_V5
#print axioms LipschitzVectorCoareaAudit.route_M1

section FiniteDimensional

variable {V W : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]

/-! ### Boundary cases

`coarea_of_contDiff` is **not** recoverable from `route_L0`: a `C¹` map on a non-compact domain
need not be Lipschitz, so the hypotheses are incomparable.  These four checks stand in its place. -/

/-- A zero-dimensional target is allowed: the codimension is the full dimension and the statement
is not vacuous. -/
theorem zero_dimensional_target (hW : finrank ℝ W = 0)
    {S : Set V} {u : V → W} {K : ℝ≥0} {g : V → ℝ≥0∞}
    (hu : LipschitzWith K u) (hS : MeasurableSet S) (hg : Measurable g) :
    (∫⁻ x in S, ENNReal.ofReal (coareaJacobian (fderiv ℝ u x)) * g x ∂(volume : Measure V)
      = ∫⁻ t, ∫⁻ y in S ∩ {x : V | u x = t}, g y
          ∂(KLS.hausdorffNormalized V (finrank ℝ V)) ∂(volume : Measure W)) :=
  (Analysis.coarea_of_lipschitz (by omega) hu hS hg).2

/-- The equidimensional case `k = 0`: the fibre measure is the zero-dimensional one and no
positivity of the codimension is hidden in the statement. -/
theorem equidimensional (hVW : finrank ℝ W = finrank ℝ V)
    {S : Set V} {u : V → W} {K : ℝ≥0} {g : V → ℝ≥0∞}
    (hu : LipschitzWith K u) (hS : MeasurableSet S) (hg : Measurable g) :
    (∫⁻ x in S, ENNReal.ofReal (coareaJacobian (fderiv ℝ u x)) * g x ∂(volume : Measure V)
      = ∫⁻ t, ∫⁻ y in S ∩ {x : V | u x = t}, g y ∂(KLS.hausdorffNormalized V 0)
          ∂(volume : Measure W)) :=
  (Analysis.coarea_of_lipschitz (by omega) hu hS hg).2

/-- A constant map into a target of positive dimension: the coarea Jacobian vanishes identically,
so the left-hand side is `0` and the formula forces the whole iterated slice integral to vanish. -/
theorem constant_map {k : ℕ} (hW : 0 < finrank ℝ W)
    (hk : k + finrank ℝ W = finrank ℝ V) {S : Set V} {c : W} {g : V → ℝ≥0∞}
    (hS : MeasurableSet S) (hg : Measurable g) :
    (∫⁻ t, ∫⁻ y in S ∩ {x : V | (fun _ => c) x = t}, g y ∂(KLS.hausdorffNormalized V k)
      ∂(volume : Measure W)) = 0 := by
  have : Nontrivial W := Module.nontrivial_of_finrank_pos hW
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  rw [← (Analysis.coarea_of_lipschitz hk (LipschitzWith.const (α := V) c) hS hg).2]
  refine setLIntegral_eq_zero hS fun x _ => ?_
  have hzero : coareaJacobian (fderiv ℝ (fun _ : V => c) x) = 0 := by
    rw [fderiv_const_apply, Analysis.coareaJacobian_eq_zero_iff]
    intro hsurj
    obtain ⟨v, hv⟩ := hsurj w
    exact hw (by simpa using hv.symm)
  rw [hzero, ENNReal.ofReal_zero, zero_mul]
  rfl

end FiniteDimensional

/-- **The codimension-one specialization returns the scalar theory.**  At `W = ℝ` the density
`coareaJacobian (fderiv ℝ u x)` is `‖gradient u x‖ₑ` and `KLS.hausdorffNormalized V k` is
`KLS.surfaceMeasure V`, so `route_L0` gives back the conclusion of `KLS.coarea_of_lipschitz`
verbatim.  `KLS.coarea_of_lipschitz` is **not** named in this proof.

The one hypothesis the scalar statement does not carry is `k + 1 = finrank ℝ V`, which merely says
that `V` is not the zero space; for `finrank ℝ V = 0` the scalar convention truncates `n - 1` to
`0` and the two statements are about different fibre measures. -/
theorem scalar_comparison {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] {k : ℕ}
    (hk : k + 1 = finrank ℝ V) {S : Set V} {u : V → ℝ} {K : ℝ≥0} {g : V → ℝ≥0∞}
    (hu : LipschitzWith K u) (hS : MeasurableSet S) (hg : Measurable g) :
    AEMeasurable (fun t : ℝ => ∫⁻ y in S ∩ {x | u x = t}, g y ∂(KLS.surfaceMeasure V))
      (volume : Measure ℝ) ∧
    (∫⁻ x in S, ‖gradient u x‖ₑ * g x ∂(volume : Measure V)) =
      ∫⁻ t, ∫⁻ y in S ∩ {x | u x = t}, g y ∂(KLS.surfaceMeasure V) ∂(volume : Measure ℝ) := by
  have hk' : k + finrank ℝ ℝ = finrank ℝ V := by simpa using hk
  have hsurf : KLS.hausdorffNormalized V k = KLS.surfaceMeasure V := by
    rw [KLS.surfaceMeasure]
    congr 1
    omega
  obtain ⟨hmeas, heq⟩ := Analysis.coarea_of_lipschitz (W := ℝ) hk' hu hS hg
  rw [hsurf] at hmeas heq
  refine ⟨hmeas, ?_⟩
  rw [← heq]
  refine setLIntegral_congr_fun hS fun x _ => ?_
  rw [Analysis.coareaJacobian_fderiv, ofReal_norm]

/-! ### Axiom audit for the boundary cases -/

#print axioms LipschitzVectorCoareaAudit.zero_dimensional_target
#print axioms LipschitzVectorCoareaAudit.equidimensional
#print axioms LipschitzVectorCoareaAudit.constant_map
#print axioms LipschitzVectorCoareaAudit.scalar_comparison

end LipschitzVectorCoareaAudit

/-! ### Axiom audit for the library declarations themselves -/

#print axioms FunctionalInequalities.Analysis.lipschitzWith_coord
#print axioms FunctionalInequalities.Analysis.differentiableAt_of_coord
#print axioms FunctionalInequalities.Analysis.fderiv_coord_apply
#print axioms FunctionalInequalities.Analysis.eq_and_fderiv_eq_of_coord
#print axioms FunctionalInequalities.Analysis.exists_common_refinement
#print axioms FunctionalInequalities.Analysis.exists_contDiff_pieces_vector
#print axioms
  FunctionalInequalities.Analysis.ae_hausdorffNormalized_inter_levelSet_eq_zero_of_volume_eq_zero
#print axioms FunctionalInequalities.Analysis.coarea_of_lipschitz_of_pieces
#print axioms FunctionalInequalities.Analysis.coarea_of_lipschitz

/-! #### The locally Lipschitz follow-on `M2` of `LipschitzCoareaRouteStatements.lean`, verbatim -/

theorem LipschitzVectorCoareaAudit.route_M2 : ∀ {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
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
#print axioms LipschitzVectorCoareaAudit.route_M2
