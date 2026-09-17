import FunctionalInequalities.Analysis.RankDeficient.ExponentObstruction
import FunctionalInequalities.Analysis.LevelSet
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Scope audit for the exponent obstructions `N1` and `N2`

`N1` and `N2` of `research/audits/RankDeficientRouteStatements.lean` are the two **diagnostic**
items of the rank-deficient route: they record what the small-Lipschitz method yields and why its
exponent cannot simply be lowered.  Neither is a step towards `R0`, which is proved.

**`N1` is proved**, restated **verbatim** below as `route_N1` and discharged from
`Analysis/RankDeficient/ExponentObstruction.lean`.  It is the obstruction *stated*, not repaired: the exponent it
delivers is `n − dim W₂`, which in the route's notation is `k + r` and **not** `k`
(`N1_exponent_is_k_add_r`), and for `r ≥ 1` that is weaker than `R0` in the useless direction — at
the exponent `k` a set of positive Lebesgue measure has **infinite** Hausdorff measure
(`N1_null_at_higher_exponent_says_nothing_at_k`), so nothing about `μH[k]` follows.  Proving `N1`
therefore confirms the diagnosis; it does **not** advance the route, which is closed by slicing
inside a fibre instead.  Its side condition `0 < finrank ℝ W₂` is **necessary**, not decoration:
`N1_needs_positive_codimension` exhibits a counterexample with a zero-dimensional `W₂`.

**`N2` as written is false**, and this file proves it false.  The route statement reads

  `volume S ≠ 0 → 0 < r → μH[((finrank ℝ V - r : ℕ) : ℝ)] S = ⊤`,

with `finrank ℝ V - r` a **truncated** natural subtraction.  When `finrank ℝ V = 0` the space is a
single point, the only set of nonzero volume is that point, the truncated exponent is `0` rather
than negative, and `μH[0]` of a singleton is `1`, not `⊤`.  `route_N2_is_false` derives a
contradiction from the statement; `N2_counterexample` exhibits the three facts separately so the
failure can be read off without unfolding the refutation.

**The repair is the missing positivity of the dimension, and it is proved** — in the module, as
`Analysis.hausdorffMeasure_finrank_sub_eq_top`, which is `N2` with `0 < finrank ℝ V` added.  That
hypothesis is **necessary**, by the counterexample, so this is not a weakening dressed up as a
statement: `0 < finrank ℝ V` is exactly what `N2` was missing.  It is also **free** where the route
appeals to `N2`: there `r` is a rank with `1 ≤ r < finrank ℝ W ≤ finrank ℝ V`, so the dimension is
positive already.  `N2_repair_is_free_on_the_route` records that implication, so the diagnostic
role of `N2` in the route record survives the correction unchanged.

**Nothing else changes.**  No previously proved statement is touched, no hole is moved, and the
route file `RankDeficientRouteStatements.lean` is left byte-identical, its `N2` still an open and —
as recorded here — false obligation.
-/

noncomputable section

open MeasureTheory Set Module FunctionalInequalities
open FunctionalInequalities.Analysis
open scoped ENNReal NNReal

namespace ExponentObstructionAudit

/-! ### The zero-dimensional space, used by both counterexamples -/

/-- The zero-dimensional inner product space: a single point.  Both side-condition
counterexamples below live over it, `N1`'s as the target `W₂` and `N2`'s as the domain `V`. -/
abbrev Pt : Type := EuclideanSpace ℝ (Fin 0)

/-! ### `N1`, restated verbatim and discharged -/

/-- **Route obligation `N1`**, copied verbatim from
`research/audits/RankDeficientRouteStatements.lean` and discharged. -/
theorem route_N1 :
    (∀ {V W W₂ : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
      [MeasurableSpace V] [BorelSpace V]
      [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
      [NormedAddCommGroup W₂] [InnerProductSpace ℝ W₂] [FiniteDimensional ℝ W₂]
      [MeasurableSpace W₂] [BorelSpace W₂]
      {u : V → W} {S : Set V} (Q : W →L[ℝ] W₂),
      MeasurableSet S → 0 < finrank ℝ W₂ → μH[((finrank ℝ V : ℕ) : ℝ)] S ≠ ⊤ →
      (∀ ε : ℝ≥0, ε ≠ 0 → ∃ T : ℕ → Set V, Pairwise (Function.onFun Disjoint T) ∧
          (∀ n, MeasurableSet (T n)) ∧ S ⊆ ⋃ n, T n ∧
          ∀ n, LipschitzOnWith ε (fun x => Q (u x)) (S ∩ T n)) →
      ∀ᵐ τ ∂(volume : Measure W₂),
        μH[((finrank ℝ V - finrank ℝ W₂ : ℕ) : ℝ)] (S ∩ {x : V | Q (u x) = τ}) = 0) :=
  fun Q hS hW₂ hSfin hpieces =>
    ae_hausdorffMeasure_inter_levelSet_eq_zero_of_lipschitz_pieces Q hS hW₂ hSfin hpieces

/-! ### `N1` is a diagnosis, not a step: the exponent is `k + r` -/

/-- **The exponent `N1` delivers is `k + r`, not `k`.**  In the route's notation `W₂` is the
orthogonal complement of the rank-`r` range inside the `m`-dimensional target, so
`dim W₂ = m − r` and `N1`'s exponent `n − dim W₂` is `k + r`.  Pure arithmetic, stated so the
gap cannot be misread. -/
theorem N1_exponent_is_k_add_r {n m k r : ℕ} (hk : k + m = n) (hr : r ≤ m) :
    n - (m - r) = k + r := by omega

/-! ### `N1` is useless for `R0`: at the exponent `k` the measure is infinite -/

section Useless

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- **Why the weaker exponent is useless.**  `N1` gives nullity at `k + r`.  At `k` itself, with
`r ≥ 1`, every set of positive Lebesgue measure has **infinite** Hausdorff measure, so no
`μH[k]` statement follows from a `μH[k + r]` one.  This is the repaired `N2`, specialized. -/
theorem N1_null_at_higher_exponent_says_nothing_at_k {S : Set V} {k r : ℕ}
    (hn : 0 < finrank ℝ V) (hvol : (volume : Measure V) S ≠ 0) (hr : 0 < r)
    (hkr : k + r = finrank ℝ V) :
    μH[((k : ℕ) : ℝ)] S = ⊤ := by
  have hk : k = finrank ℝ V - r := by omega
  rw [hk]
  exact hausdorffMeasure_finrank_sub_eq_top hn hvol hr

end Useless

/-! ### The side condition `0 < finrank ℝ W₂` is necessary -/

/-- **`N1` fails without `0 < finrank ℝ W₂`.**  With a zero-dimensional `W₂` the Eilenberg constant
`ε ^ (dim W₂)` is `1`, nothing tends to zero, and the conclusion is simply false: take
`V = W = ℝ`, `Q = 0`, `u = id` and `S = [0, 1]`, where every piece hypothesis holds trivially
because `Q ∘ u` is constant, while the single fibre is all of `S` and carries `μH[1] S = 1`. -/
theorem N1_needs_positive_codimension :
    ¬ (∀ {V W W₂ : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
        [MeasurableSpace V] [BorelSpace V]
        [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
        [NormedAddCommGroup W₂] [InnerProductSpace ℝ W₂] [FiniteDimensional ℝ W₂]
        [MeasurableSpace W₂] [BorelSpace W₂]
        {u : V → W} {S : Set V} (Q : W →L[ℝ] W₂),
        MeasurableSet S → μH[((finrank ℝ V : ℕ) : ℝ)] S ≠ ⊤ →
        (∀ ε : ℝ≥0, ε ≠ 0 → ∃ T : ℕ → Set V, Pairwise (Function.onFun Disjoint T) ∧
            (∀ n, MeasurableSet (T n)) ∧ S ⊆ ⋃ n, T n ∧
            ∀ n, LipschitzOnWith ε (fun x => Q (u x)) (S ∩ T n)) →
        ∀ᵐ τ ∂(volume : Measure W₂),
          μH[((finrank ℝ V - finrank ℝ W₂ : ℕ) : ℝ)] (S ∩ {x : V | Q (u x) = τ}) = 0) := by
  intro hN1
  classical
  set S : Set ℝ := Set.Icc (0 : ℝ) 1 with hSdef
  have hmeasS : MeasurableSet S := measurableSet_Icc
  have hH1 : μH[((finrank ℝ ℝ : ℕ) : ℝ)] S = 1 := by
    rw [finrank_self]
    simp [hSdef]
  have hfin : μH[((finrank ℝ ℝ : ℕ) : ℝ)] S ≠ ⊤ := by rw [hH1]; simp
  have hpieces : ∀ ε : ℝ≥0, ε ≠ 0 → ∃ T : ℕ → Set ℝ, Pairwise (Function.onFun Disjoint T) ∧
      (∀ n, MeasurableSet (T n)) ∧ S ⊆ ⋃ n, T n ∧
      ∀ n, LipschitzOnWith ε (fun x => (0 : ℝ →L[ℝ] Pt) (id x)) (S ∩ T n) := by
    intro ε _
    refine ⟨fun n => if n = 0 then Set.univ else ∅, ?_, ?_, ?_, ?_⟩
    · intro i j hij
      rcases Nat.eq_zero_or_pos i with rfl | hi
      · simp [Function.onFun, Ne.symm hij]
      · simp [Function.onFun, hi.ne']
    · intro n; by_cases h : n = 0 <;> simp [h]
    · intro x _; exact Set.mem_iUnion.2 ⟨0, by simp⟩
    · intro n
      refine LipschitzOnWith.of_dist_le_mul fun x _ y _ => ?_
      simpa using mul_nonneg ε.coe_nonneg dist_nonneg
  have hae := hN1 (V := ℝ) (W := ℝ) (W₂ := Pt) (u := id) (S := S) 0 hmeasS hfin hpieces
  have hdim : (finrank ℝ ℝ - finrank ℝ Pt : ℕ) = (finrank ℝ ℝ : ℕ) := by
    simp [finrank_euclideanSpace]
  have hall : ∀ τ : Pt,
      ¬ μH[((finrank ℝ ℝ - finrank ℝ Pt : ℕ) : ℝ)]
          (S ∩ {x : ℝ | (0 : ℝ →L[ℝ] Pt) (id x) = τ}) = 0 := by
    intro τ
    have hslice : S ∩ {x : ℝ | (0 : ℝ →L[ℝ] Pt) (id x) = τ} = S := by
      ext x; simp [Subsingleton.elim (0 : Pt) τ]
    rw [hslice, hdim, hH1]
    exact one_ne_zero
  rw [ae_iff] at hae
  rw [Set.eq_univ_of_forall hall] at hae
  exact (isOpen_univ.measure_pos (volume : Measure Pt) ⟨0, trivial⟩).ne' hae

/-! ### `N2` is false at dimension zero -/

/-- **The counterexample, in three facts.**  `Pt` is zero-dimensional; its whole space has nonzero
volume; and at the truncated exponent `0 - 1 = 0` its Hausdorff measure is `1`, not `⊤`. -/
theorem N2_counterexample :
    finrank ℝ Pt = 0 ∧ (volume : Measure Pt) Set.univ ≠ 0 ∧
      μH[((finrank ℝ Pt - 1 : ℕ) : ℝ)] (Set.univ : Set Pt) = 1 := by
  refine ⟨by simp [finrank_euclideanSpace], ?_, ?_⟩
  · exact (isOpen_univ.measure_pos (volume : Measure Pt) ⟨0, trivial⟩).ne'
  · have hdim : finrank ℝ Pt = 0 := by simp [finrank_euclideanSpace]
    have huniv : (Set.univ : Set Pt) = {(0 : Pt)} := by
      ext x; simp [Subsingleton.elim x 0]
    rw [hdim, huniv]
    simp

/-- **Route obligation `N2` is false.**  The route states it for `V : Type*`; that universe
polymorphic form implies the `Type` instance refuted here, so refuting this one refutes it. -/
theorem route_N2_is_false :
    ¬ (∀ {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
        [MeasurableSpace V] [BorelSpace V] {S : Set V} {r : ℕ},
        (volume : Measure V) S ≠ 0 → 0 < r → μH[((finrank ℝ V - r : ℕ) : ℝ)] S = ⊤) := by
  intro hN2
  obtain ⟨-, hvol, hH⟩ := N2_counterexample
  have htop : μH[((finrank ℝ Pt - 1 : ℕ) : ℝ)] (Set.univ : Set Pt) = ⊤ :=
    hN2 (S := Set.univ) (r := 1) hvol one_pos
  rw [hH] at htop
  exact absurd htop (by simp)

/-! ### The repaired statement lives in the module; here is what it costs the route -/

section Repair

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- **The repair costs the route nothing.**  The repaired statement itself is
`Analysis.hausdorffMeasure_finrank_sub_eq_top` in `Analysis/RankDeficient/ExponentObstruction.lean`.  Wherever
the route record appeals to `N2`, `r` is the rank of a differential `V → W` with
`r < finrank ℝ W` and `finrank ℝ W ≤ finrank ℝ V`, so the dimension is positive already and the
added hypothesis is discharged on the spot. -/
theorem N2_repair_is_free_on_the_route {W : Type*} [NormedAddCommGroup W]
    [InnerProductSpace ℝ W] [FiniteDimensional ℝ W] {r : ℕ}
    (hrW : r < finrank ℝ W) (hWV : finrank ℝ W ≤ finrank ℝ V) (hr : 0 < r) :
    0 < finrank ℝ V := by
  omega

end Repair

end ExponentObstructionAudit

/-! ### Axiom audit: every report is standard-only -/

#print axioms FunctionalInequalities.Analysis.hausdorffMeasure_truncated_add_le
#print axioms FunctionalInequalities.Analysis.exists_measurable_majorant_of_lipschitz_pieces
#print axioms FunctionalInequalities.Analysis.ae_hausdorffMeasure_inter_levelSet_eq_zero_of_lipschitz_pieces
#print axioms ExponentObstructionAudit.route_N1
#print axioms ExponentObstructionAudit.N1_exponent_is_k_add_r
#print axioms ExponentObstructionAudit.N1_null_at_higher_exponent_says_nothing_at_k
#print axioms ExponentObstructionAudit.N1_needs_positive_codimension
#print axioms ExponentObstructionAudit.N2_counterexample
#print axioms ExponentObstructionAudit.route_N2_is_false
#print axioms FunctionalInequalities.Analysis.hausdorffMeasure_finrank_sub_eq_top
#print axioms ExponentObstructionAudit.N2_repair_is_free_on_the_route
