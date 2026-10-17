import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Domain
import FunctionalInequalities.KLS.BKL.Localization.Process.Basic
/-! Independent statement audit for the positive-time smoothing stage.

Every proposition below is restated in full and **proved** from the library. The two headline
statements are the ones the previous two rounds carried as `#check`-only candidates: for an
**arbitrary** datum `g` and `t > 0` the semigroup value lies in the form domain `D(T)` and in the
generator domain `D(T†T)`, with explicit constants. No smooth test class, no compact support and
no classical representative is assumed or produced, and the sharp constants `1/√(2et)` and
`1/(et)` are deliberately not claimed: the audited bounds are `1/√(2t)` and `1/t`. -/
noncomputable section
open MeasureTheory FunctionalInequalities FunctionalInequalities.Analysis.Semigroup
open scoped RealInnerProductSpace LinearPMap
namespace SemigroupSmoothingAudit
variable {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
  [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
  (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) (hd : Dense (T.domain : Set H₀))

/-! ### E0–E1: dissipation on the generator domain -/

/-- `f ∈ D(T†T)`, `t ≥ 0` implies `2 t ‖T (P_t f)‖ ² ≤ ‖f‖ ² - ‖P_t f‖ ²`. -/
theorem E0 (f : (adjointComp T).domain) {t : ℝ} (ht : 0 ≤ t)
    (hft : Generated.apply T hT hd t (f : H₀) ∈ T.domain) :
    2 * t * ‖T ⟨Generated.apply T hT hd t (f : H₀), hft⟩‖ ^ 2
      ≤ ‖(f : H₀)‖ ^ 2 - ‖Generated.apply T hT hd t (f : H₀)‖ ^ 2 :=
  Generated.two_mul_norm_map_apply_sq_le_sub T hT hd f ht hft

/-- `f ∈ D(T†T)`, `t ≥ 0` implies `2 t ‖T†T (P_t f)‖ ² ≤ ‖T f‖ ² - ‖T (P_t f)‖ ²`. -/
theorem E1 (f : (adjointComp T).domain) {t : ℝ} (ht : 0 ≤ t)
    (hft : Generated.apply T hT hd t (f : H₀) ∈ T.domain) :
    2 * t * ‖adjointComp T ⟨Generated.apply T hT hd t (f : H₀),
        Generated.preserves_domain T hT hd f ht⟩‖ ^ 2
      ≤ ‖T ⟨(f : H₀), f.2.2⟩‖ ^ 2 - ‖T ⟨Generated.apply T hT hd t (f : H₀), hft⟩‖ ^ 2 :=
  Generated.two_mul_norm_adjointComp_apply_sq_le_sub T hT hd f ht hft

/-! ### E2: arbitrary data enter the form domain at positive times -/

/-- For **every** `g : H₀` and every `t > 0`, `P_t g ∈ D(T)`. -/
theorem E2 (g : H₀) {t : ℝ} (ht : 0 < t) : Generated.apply T hT hd t g ∈ T.domain :=
  Generated.mem_domain_apply_of_pos T hT hd g ht

/-- The accompanying bound `2 t ‖T (P_t g)‖ ² ≤ ‖g‖ ²`, for every witness of `E2`. -/
theorem E2_bound (g : H₀) {t : ℝ} (ht : 0 < t) (h : Generated.apply T hT hd t g ∈ T.domain) :
    2 * t * ‖T ⟨Generated.apply T hT hd t g, h⟩‖ ^ 2 ≤ ‖g‖ ^ 2 :=
  Generated.two_mul_norm_map_apply_sq_le T hT hd g ht h

/-- Witness and bound in one statement. -/
theorem E2_pack (g : H₀) {t : ℝ} (ht : 0 < t) :
    ∃ h : Generated.apply T hT hd t g ∈ T.domain,
      2 * t * ‖T ⟨Generated.apply T hT hd t g, h⟩‖ ^ 2 ≤ ‖g‖ ^ 2 :=
  Generated.exists_mem_domain_apply_of_pos T hT hd g ht

include hT hd in
/-- The zero vector is allowed, and the bound is then an equality at both ends. -/
theorem E2_zero_vector {t : ℝ} (ht : 0 < t) : Generated.apply T hT hd t (0 : H₀) ∈ T.domain :=
  Generated.mem_domain_apply_of_pos T hT hd 0 ht

/-! ### E3: form-domain data enter the generator domain at positive times -/

/-- For every `f ∈ D(T)` and `t > 0`, `P_t f ∈ D(T†T)` with
`2 t ‖T†T (P_t f)‖ ² ≤ ‖T f‖ ²`. -/
theorem E3 (f : T.domain) {t : ℝ} (ht : 0 < t) :
    ∃ h : Generated.apply T hT hd t (f : H₀) ∈ (adjointComp T).domain,
      2 * t * ‖adjointComp T ⟨Generated.apply T hT hd t (f : H₀), h⟩‖ ^ 2 ≤ ‖T f‖ ^ 2 :=
  Generated.exists_mem_adjointComp_domain_apply_of_mem_domain T hT hd f ht

/-! ### E4: arbitrary data enter the generator domain at positive times -/

/-- For **every** `g : H₀` and every `t > 0`, `P_t g ∈ D(T†T)`. -/
theorem E4 (g : H₀) {t : ℝ} (ht : 0 < t) :
    Generated.apply T hT hd t g ∈ (adjointComp T).domain :=
  Generated.mem_adjointComp_domain_apply_of_pos T hT hd g ht

/-- The accompanying bound `t ‖T†T (P_t g)‖ ≤ ‖g‖`, for every witness of `E4`. -/
theorem E4_bound (g : H₀) {t : ℝ} (ht : 0 < t)
    (h : Generated.apply T hT hd t g ∈ (adjointComp T).domain) :
    t * ‖adjointComp T ⟨Generated.apply T hT hd t g, h⟩‖ ≤ ‖g‖ :=
  Generated.mul_norm_adjointComp_apply_le T hT hd g ht h

/-- Witness and bound in one statement. -/
theorem E4_pack (g : H₀) {t : ℝ} (ht : 0 < t) :
    ∃ h : Generated.apply T hT hd t g ∈ (adjointComp T).domain,
      t * ‖adjointComp T ⟨Generated.apply T hT hd t g, h⟩‖ ≤ ‖g‖ :=
  Generated.exists_mem_adjointComp_domain_apply_of_pos T hT hd g ht

/-- `E4` also gives the gradient of `P_t g` for arbitrary data, through `D(T†T) ⊆ D(T)`. -/
theorem E4_mem_form_domain (g : H₀) {t : ℝ} (ht : 0 < t) :
    Generated.apply T hT hd t g ∈ T.domain :=
  (Generated.mem_adjointComp_domain_apply_of_pos T hT hd g ht).2

/-! ### Generic auxiliary declarations used above -/

/-- Bounded-level norm dissipation for `exp (-u • L)`, `L` symmetric. -/
theorem aux_bounded_norm_dissipation (L : H₀ →L[ℝ] H₀)
    (hsymm : ∀ x z : H₀, ⟪L x, z⟫ = ⟪x, L z⟫) (y : H₀) {u : ℝ} (hu : 0 ≤ u) :
    2 * u * ⟪L (NormedSpace.exp (-u • L) y), NormedSpace.exp (-u • L) y⟫
      ≤ ‖y‖ ^ 2 - ‖NormedSpace.exp (-u • L) y‖ ^ 2 :=
  two_mul_inner_exp_neg_smul_le L hsymm y hu

/-- Bounded-level form dissipation for `exp (-u • L)`, `L` symmetric and nonnegative. -/
theorem aux_bounded_form_dissipation (L : H₀ →L[ℝ] H₀)
    (hsymm : ∀ x z : H₀, ⟪L x, z⟫ = ⟪x, L z⟫) (hnonneg : ∀ x : H₀, 0 ≤ ⟪L x, x⟫) (y : H₀)
    {u : ℝ} (hu : 0 ≤ u) :
    2 * u * ‖L (NormedSpace.exp (-u • L) y)‖ ^ 2
      ≤ ⟪L y, y⟫ - ⟪L (NormedSpace.exp (-u • L) y), NormedSpace.exp (-u • L) y⟫ :=
  two_mul_norm_apply_exp_neg_smul_sq_le L hsymm hnonneg y hu

omit [CompleteSpace H₀] [CompleteSpace H₁] in
/-- A closed operator absorbs graph limits. -/
theorem aux_closed_graph_limit {S : H₀ →ₗ.[ℝ] H₁} (hS : S.IsClosed) {x : ℕ → H₀}
    (hx : ∀ n, x n ∈ S.domain) {a : H₀} {b : H₁}
    (hxa : Filter.Tendsto x Filter.atTop (nhds a))
    (hSb : Filter.Tendsto (fun n => S ⟨x n, hx n⟩) Filter.atTop (nhds b)) :
    ∃ h : a ∈ S.domain, S ⟨a, h⟩ = b :=
  exists_mem_domain_apply_eq_of_tendsto hS hx hxa hSb

include hT hd in
/-- `T†T` is closed, which is what lets `E3` pass to the limit. -/
theorem aux_adjointComp_isClosed : (adjointComp T).IsClosed :=
  (isSelfAdjoint_adjointComp T hT hd).isClosed

/-! ### E5: the closed weighted gradient heat semigroup, arbitrary weight -/

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] (B : V →L[ℝ] V)
  (hν : KLS.LogConcave ν) (hi : (interior (ν : Measure V).support).Nonempty)

/-- Arbitrary `L²(ν)` data acquire a closed weighted gradient at every positive time, for an
arbitrary weight `B`. -/
theorem E5_0 (f : Lp ℝ 2 (ν : Measure V)) {t : ℝ} (ht : 0 < t) :
    KLS.LogConcave.HeatSemigroup.operator m B hν hi ht.le f ∈
      (hν.closedWeightedOperator m B hi).domain :=
  KLS.LogConcave.HeatSemigroup.mem_closedWeightedOperator_domain_of_pos m B hν hi f ht

/-- Its bound: `2 t ‖T̄ (P_t f)‖ ² ≤ ‖f‖ ²`. -/
theorem E5_1 (f : Lp ℝ 2 (ν : Measure V)) {t : ℝ} (ht : 0 < t)
    (hft : KLS.LogConcave.HeatSemigroup.operator m B hν hi ht.le f ∈
      (hν.closedWeightedOperator m B hi).domain) :
    2 * t * ‖hν.closedWeightedOperator m B hi
        ⟨KLS.LogConcave.HeatSemigroup.operator m B hν hi ht.le f, hft⟩‖ ^ 2 ≤ ‖f‖ ^ 2 :=
  KLS.LogConcave.HeatSemigroup.two_mul_norm_closedWeightedOperator_sq_le m B hν hi f ht hft

/-- Arbitrary `L²(ν)` data enter the generator domain at every positive time. -/
theorem E5_2 (f : Lp ℝ 2 (ν : Measure V)) {t : ℝ} (ht : 0 < t) :
    KLS.LogConcave.HeatSemigroup.operator m B hν hi ht.le f ∈
      (adjointComp (hν.closedWeightedOperator m B hi)).domain :=
  KLS.LogConcave.HeatSemigroup.mem_adjointComp_domain_of_pos m B hν hi f ht

/-- Its bound: `t ‖T̄†T̄ (P_t f)‖ ≤ ‖f‖`. -/
theorem E5_3 (f : Lp ℝ 2 (ν : Measure V)) {t : ℝ} (ht : 0 < t)
    (hft : KLS.LogConcave.HeatSemigroup.operator m B hν hi ht.le f ∈
      (adjointComp (hν.closedWeightedOperator m B hi)).domain) :
    t * ‖adjointComp (hν.closedWeightedOperator m B hi)
        ⟨KLS.LogConcave.HeatSemigroup.operator m B hν hi ht.le f, hft⟩‖ ≤ ‖f‖ :=
  KLS.LogConcave.HeatSemigroup.mul_norm_adjointComp_le m B hν hi f ht hft

-- Still candidates after this stage: a classical (continuous or smooth) representative of
-- `P_t f` for `t > 0`, and the sharp constants coming from `sup x exp (-x) = 1/e`.
-- Neither is declared or proved here.
#check fun (S : H₀ →ₗ.[ℝ] H₁) (hS : S.IsClosed) (hsd : Dense (S.domain : Set H₀)) =>
  (∀ (g : H₀) (t : ℝ) (_ht : 0 < t) (h : Generated.apply S hS hsd t g ∈ (adjointComp S).domain),
    Real.exp 1 * t * ‖adjointComp S ⟨Generated.apply S hS hsd t g, h⟩‖ ≤ ‖g‖)

end SemigroupSmoothingAudit

#print axioms FunctionalInequalities.Analysis.Semigroup.exp_neg_smul_apply_comm
#print axioms FunctionalInequalities.Analysis.Semigroup.hasDerivAt_exp_neg_smul_apply
#print axioms FunctionalInequalities.Analysis.Semigroup.hasDerivAt_norm_exp_neg_smul_sq
#print axioms FunctionalInequalities.Analysis.Semigroup.hasDerivAt_inner_exp_neg_smul
#print axioms FunctionalInequalities.Analysis.Semigroup.two_mul_inner_exp_neg_smul_le
#print axioms FunctionalInequalities.Analysis.Semigroup.two_mul_norm_apply_exp_neg_smul_sq_le
#print axioms FunctionalInequalities.Analysis.Semigroup.apply_sub_of_eq_sub
#print axioms FunctionalInequalities.Analysis.Semigroup.exists_mem_domain_apply_eq_of_tendsto
#print axioms FunctionalInequalities.Analysis.Semigroup.Generated.tendsto_exp_neg_smul_yosida
#print axioms FunctionalInequalities.Analysis.Semigroup.Generated.tendsto_yosida_apply
#print axioms FunctionalInequalities.Analysis.Semigroup.Generated.tendsto_yosida_exp_neg_smul_apply
#print axioms FunctionalInequalities.Analysis.Semigroup.Generated.two_mul_norm_map_apply_sq_le_sub
#print axioms FunctionalInequalities.Analysis.Semigroup.Generated.two_mul_norm_adjointComp_apply_sq_le_sub
#print axioms FunctionalInequalities.Analysis.Semigroup.Generated.exists_mem_domain_apply_of_pos
#print axioms FunctionalInequalities.Analysis.Semigroup.Generated.mem_domain_apply_of_pos
#print axioms FunctionalInequalities.Analysis.Semigroup.Generated.two_mul_norm_map_apply_sq_le
#print axioms FunctionalInequalities.Analysis.Semigroup.Generated.exists_mem_adjointComp_domain_apply_of_mem_domain
#print axioms FunctionalInequalities.Analysis.Semigroup.Generated.exists_mem_adjointComp_domain_apply_of_pos
#print axioms FunctionalInequalities.Analysis.Semigroup.Generated.mem_adjointComp_domain_apply_of_pos
#print axioms FunctionalInequalities.Analysis.Semigroup.Generated.mul_norm_adjointComp_apply_le
#print axioms FunctionalInequalities.KLS.LogConcave.HeatSemigroup.mem_closedWeightedOperator_domain_of_pos
#print axioms FunctionalInequalities.KLS.LogConcave.HeatSemigroup.two_mul_norm_closedWeightedOperator_sq_le
#print axioms FunctionalInequalities.KLS.LogConcave.HeatSemigroup.mem_adjointComp_domain_of_pos
#print axioms FunctionalInequalities.KLS.LogConcave.HeatSemigroup.mul_norm_adjointComp_le
#print axioms SemigroupSmoothingAudit.E0
#print axioms SemigroupSmoothingAudit.E1
#print axioms SemigroupSmoothingAudit.E2
#print axioms SemigroupSmoothingAudit.E2_bound
#print axioms SemigroupSmoothingAudit.E2_pack
#print axioms SemigroupSmoothingAudit.E2_zero_vector
#print axioms SemigroupSmoothingAudit.E3
#print axioms SemigroupSmoothingAudit.E4
#print axioms SemigroupSmoothingAudit.E4_bound
#print axioms SemigroupSmoothingAudit.E4_pack
#print axioms SemigroupSmoothingAudit.E4_mem_form_domain
#print axioms SemigroupSmoothingAudit.aux_bounded_norm_dissipation
#print axioms SemigroupSmoothingAudit.aux_bounded_form_dissipation
#print axioms SemigroupSmoothingAudit.aux_closed_graph_limit
#print axioms SemigroupSmoothingAudit.aux_adjointComp_isClosed
#print axioms SemigroupSmoothingAudit.E5_0
#print axioms SemigroupSmoothingAudit.E5_1
#print axioms SemigroupSmoothingAudit.E5_2
#print axioms SemigroupSmoothingAudit.E5_3
