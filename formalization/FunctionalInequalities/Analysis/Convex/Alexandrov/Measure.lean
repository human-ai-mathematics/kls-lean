module

public import FunctionalInequalities.Analysis.Convex.Extension
public import FunctionalInequalities.Analysis.Convex.CompactTilt
public import FunctionalInequalities.Analysis.Convex.Alexandrov.ImageVolume

/-! # Domain Monge--Ampere measures from actual supporting images

Supports the domain Monge--Ampere infrastructure for Letwin
arXiv:2607.24164v1 Lemma 2.2 through BB arXiv:1207.6128v1
Theorem 2.24(ii).
-/

@[expose] public section

noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace ENNReal

namespace FunctionalInequalities.Analysis
section DomainSlopeNull

open Metric

/-- Supporting slopes shared by two distinct points of an open-domain C0
convex function form a null set. Actual buffered pair patches and the global
Lipschitz-convex theorem produce the conclusion; no extension, slope bound,
cover or overlap nullity is an input. All dimensions, including zero. -/
theorem volume_domain_subgradient_two_points_eq_zero {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {v : E → ℝ} {Ω : Set E} (hΩ : IsOpen Ω) (hv : ConvexOn ℝ Ω v) (hvc : ContinuousOn v Ω) :
    (volume : Measure E)
        {p : E |
          ∃ x ∈ Ω,
            ∃ y ∈ Ω,
              x ≠ y ∧ (∀ z ∈ Ω, v x + ⟪p, z - x⟫ ≤ v z) ∧ (∀ z ∈ Ω, v y + ⟪p, z - y⟫ ≤ v z)} =
      0 := by
  classical
  obtain ⟨R, s, hRpos, hRsub, hs, hcover⟩ := exists_countable_buffered_ball_cover hΩ
  let K : (s × s) → Set E := fun q =>
    closedBall (q.1.1 : E) (R q.1.1) ∪ closedBall (q.2.1 : E) (R q.2.1)
  have hKcompact (q : s × s) : IsCompact (K q) := by
    dsimp [K]
    exact
      (isCompact_closedBall (q.1.1 : E) (R q.1.1)).union
        (isCompact_closedBall (q.2.1 : E) (R q.2.1))
  have hKnonempty (q : s × s) : (K q).Nonempty := by
    refine ⟨(q.1.1 : E), Or.inl ?_⟩
    change dist (q.1.1 : E) (q.1.1 : E) ≤ R q.1.1
    simp [le_of_lt (hRpos q.1.1)]
  have hKsubset (q : s × s) : K q ⊆ Ω := by
    intro z hz
    rcases hz with hz | hz
    · exact hRsub q.1.1 hz
    · exact hRsub q.2.1 hz
  have hExt (q : s × s) :
    ∃ (W : E → ℝ) (L : NNReal),
      ConvexOn ℝ univ W ∧
        LipschitzWith L W ∧
          (∀ x ∈ K q, W x = v x) ∧
            (∀ G ⊆ interior (K q), subgradientImage W G = subgradientImageOn v Ω G) := by
    exact
      exists_lipschitz_compact_convex_extension hΩ hv hvc (hKcompact q) (hKnonempty q)
        (hKsubset q)
  let V : (s × s) → E → ℝ := fun q => Classical.choose (hExt q)
  have hVwit (q : s × s) :
    ∃ L : NNReal,
      ConvexOn ℝ univ (V q) ∧
        LipschitzWith L (V q) ∧
          (∀ x ∈ K q, V q x = v x) ∧
            (∀ G ⊆ interior (K q), subgradientImage (V q) G = subgradientImageOn v Ω G) := by
    dsimp [V]
    exact Classical.choose_spec (hExt q)
  let L : (s × s) → NNReal := fun q => Classical.choose (hVwit q)
  have hVspec (q : s × s) :
    ConvexOn ℝ univ (V q) ∧
      LipschitzWith (L q) (V q) ∧
        (∀ x ∈ K q, V q x = v x) ∧
          (∀ G ⊆ interior (K q), subgradientImage (V q) G = subgradientImageOn v Ω G) :=
    Classical.choose_spec (hVwit q)
  have hhalf (q : s × s) (c : E) (r : ℝ) (hr : 0 < r) (hsub : closedBall c r ⊆ K q) :
    ball c (r / 2) ⊆ interior (K q) := by
    apply isOpen_ball.subset_interior_iff.mpr
    intro z hz
    apply hsub
    have hz' : dist z c < r / 2 := hz
    change dist z c ≤ r
    linarith
  have htransfer (q : s × s) (a p : E) (ha : a ∈ interior (K q))
    (hp : ∀ z ∈ Ω, v a + ⟪p, z - a⟫ ≤ v z) : ∀ z, V q a + ⟪p, z - a⟫ ≤ V q z := by
    have hsingleton : ({ a } : Set E) ⊆ interior (K q) := by
      intro z hz
      rcases mem_singleton_iff.mp hz with rfl
      exact ha
    have hpOn : p ∈ subgradientImageOn v Ω ({ a } : Set E) := by exact ⟨a, mem_singleton a, hp⟩
    have hpGlobal : p ∈ subgradientImage (V q) ({ a } : Set E) := by
      rw [(hVspec q).2.2.2 ({ a } : Set E) hsingleton]
      exact hpOn
    rcases hpGlobal with ⟨a', ha', hpa'⟩
    have haa : a' = a := mem_singleton_iff.mp ha'
    simpa [haa] using hpa'
  let N : (s × s) → Set E := fun q =>
    {p : E |
      ∃ x y : E, x ≠ y ∧ (∀ z, V q x + ⟪p, z - x⟫ ≤ V q z) ∧ (∀ z, V q y + ⟪p, z - y⟫ ≤ V q z)}
  have hN (q : s × s) : (volume : Measure E) (N q) = 0 := by
    simpa [N] using
      (volume_subgradient_two_points_eq_zero (u := V q) (hVspec q).2.1 (hVspec q).1)
  let : Encodable s := hs.toEncodable
  have hNull : (volume : Measure E) (⋃ q : s × s, N q) = 0 := by
    apply measure_iUnion_null
    intro q
    exact hN q
  refine measure_mono_null ?_ hNull
  intro p hp
  rcases hp with ⟨x, hx, y, hy, hxy, hxp, hyp⟩
  rcases mem_iUnion.mp (hcover hx) with ⟨i, hi⟩
  rcases mem_iUnion.mp hi with ⟨his, hxi⟩
  rcases mem_iUnion.mp (hcover hy) with ⟨j, hj⟩
  rcases mem_iUnion.mp hj with ⟨hjs, hyj⟩
  let q : s × s := ⟨⟨i, his⟩, ⟨j, hjs⟩⟩
  have hxi' : x ∈ ball (q.1.1 : E) (R q.1.1 / 2) := by simpa [q] using hxi
  have hyj' : y ∈ ball (q.2.1 : E) (R q.2.1 / 2) := by simpa [q] using hyj
  have hxiI : x ∈ interior (K q) :=
    hhalf q _ _ (hRpos q.1.1) (by intro z hz; exact Or.inl hz) hxi'
  have hyjI : y ∈ interior (K q) :=
    hhalf q _ _ (hRpos q.2.1) (by intro z hz; exact Or.inr hz) hyj'
  have hxp' := htransfer q x p hxiI hxp
  have hyp' := htransfer q y p hyjI hyp
  refine mem_iUnion.2 ⟨q, ?_⟩
  change
    ∃ x y : E, x ≠ y ∧ (∀ z, V q x + ⟪p, z - x⟫ ≤ V q z) ∧ (∀ z, V q y + ⟪p, z - y⟫ ≤ V q z)
  exact ⟨x, y, hxy, hxp', hyp'⟩


/-- Disjoint domain subsets have supporting-slope images whose intersection
is null. The images need not be measurable and no positive dimension is required. -/
theorem volume_inter_subgradientImageOn_eq_zero_of_disjoint {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {v : E → ℝ} {Ω G H : Set E} (hΩ : IsOpen Ω) (hv : ConvexOn ℝ Ω v) (hvc : ContinuousOn v Ω)
    (hG : G ⊆ Ω) (hH : H ⊆ Ω) (hGH : Disjoint G H) :
    (volume : Measure E) (subgradientImageOn v Ω G ∩ subgradientImageOn v Ω H) = 0 := by
  apply measure_mono_null ?_ (volume_domain_subgradient_two_points_eq_zero hΩ hv hvc)
  rintro p ⟨⟨x, hx, hpx⟩, ⟨y, hy, hpy⟩⟩
  have hxy : x ≠ y := by
    intro h
    subst y
    exact Set.disjoint_left.mp hGH hx hy
  exact ⟨x, hG hx, y, hH hy, hxy, hpx, hpy⟩

end DomainSlopeNull

section DomainImageMeasurability
open Metric


/-- The support image of a Borel subset of an open continuity domain is analytic
in a Polish real inner-product space. Convexity and finite dimension are not
needed for this graph/projection fact; measurability of the image is not asserted. -/
theorem analyticSet_subgradientImageOn {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [PolishSpace E] [MeasurableSpace E] [BorelSpace E] {v : E → ℝ}
    {Ω G : Set E} (hΩ : IsOpen Ω) (hvc : ContinuousOn v Ω) (hG : MeasurableSet G)
    (hGΩ : G ⊆ Ω) : AnalyticSet (subgradientImageOn v Ω G) := by
  let : PolishSpace Ω := hΩ.polishSpace
  let A : Set (Ω × E) := {q | q.1.val ∈ G ∧ ∀ y ∈ Ω, v q.1.val + ⟪q.2, y - q.1.val⟫ ≤ v y}
  have hAm : MeasurableSet A :=
    (hG.preimage (continuous_subtype_val.comp continuous_fst).measurable).inter
      (isClosed_subgradient_graphOn hvc).measurableSet
  have heq : Prod.snd '' A = subgradientImageOn v Ω G := by
    ext p
    constructor
    · rintro ⟨⟨x, q⟩, hx, rfl⟩
      exact ⟨x.val, hx.1, hx.2⟩
    · rintro ⟨x, hx, hp⟩
      exact ⟨(⟨x, hGΩ hx⟩, p), ⟨hx, hp⟩, rfl⟩
  rw [← heq]
  exact hAm.analyticSet.image_of_continuous continuous_snd


/-- Actual compact supporting images and a genuine countable contained-ball
cover give a Borel supporting image for every open subset. -/
theorem measurableSet_subgradientImageOn_of_isOpen {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {v : E → ℝ} {Ω G : Set E} (hΩ : IsOpen Ω) (hv : ConvexOn ℝ Ω v) (hvc : ContinuousOn v Ω)
    (hG : IsOpen G) (hGΩ : G ⊆ Ω) : MeasurableSet (subgradientImageOn v Ω G) := by
  classical
  obtain ⟨R, s, hRpos, hRsub, hs, hcover⟩ := exists_countable_buffered_ball_cover hG
  let T : s → Set E := fun i => subgradientImageOn v Ω (closedBall i.val.val (R i.val))
  have hT (i : s) : MeasurableSet (T i) := by
    exact
      (isCompact_subgradientImageOn_of_isCompact hΩ hv hvc (isCompact_closedBall _ _)
          ((hRsub i.val).trans hGΩ)).isClosed.measurableSet
  have hGballs : G = ⋃ i : s, closedBall i.val.val (R i.val) := by
    ext x
    constructor
    · intro hx
      rcases mem_iUnion.mp (hcover hx) with ⟨i, hi⟩
      rcases mem_iUnion.mp hi with ⟨his, hxi⟩
      have hball : x ∈ closedBall i.val (R i) := by
        have hdist : dist x i.val < R i / 2 := hxi
        have hr := hRpos i
        change dist x i.val ≤ R i
        linarith
      exact mem_iUnion.mpr ⟨⟨i, his⟩, hball⟩
    · intro hx
      rcases mem_iUnion.mp hx with ⟨i, hx⟩
      exact hRsub i.val hx
  have heq : subgradientImageOn v Ω G = ⋃ i : s, T i := by
    calc
      subgradientImageOn v Ω G =
          subgradientImageOn v Ω (⋃ i : s, closedBall i.val.val (R i.val)) :=
        congrArg (subgradientImageOn v Ω) hGballs
      _ = ⋃ i : s, T i := subgradientImageOn_iUnion v Ω _
  let : Encodable s := hs.toEncodable
  rw [heq]
  exact MeasurableSet.iUnion hT


private theorem analytic_inter_of_pair
    {E : Type*} [TopologicalSpace E] [T2Space E] {A B : Set E}
    (hA : AnalyticSet A) (hB : AnalyticSet B) : AnalyticSet (A ∩ B) := by
  have heq : A ∩ B = ⋂ b : Bool, if b then A else B := by ext x; simp [and_comm]
  rw [heq]
  apply AnalyticSet.iInter
  intro b
  cases b
  · exact hB
  · exact hA

/-- Actual Borel base sets have null-measurable domain supporting images. The
Borel null hull and Lusin separator are produced from true source overlap and
analyticity, without a universal analytic-measurability assumption. -/
theorem nullMeasurableSet_subgradientImageOn_of_measurableSet {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {v : E → ℝ} {Ω G : Set E} (hΩ : IsOpen Ω) (hv : ConvexOn ℝ Ω v) (hvc : ContinuousOn v Ω)
    (hG : MeasurableSet G) (hGΩ : G ⊆ Ω) :
    NullMeasurableSet (subgradientImageOn v Ω G) volume := by
  classical
  let A := subgradientImageOn v Ω G
  let B := subgradientImageOn v Ω (Ω \ G)
  let F := subgradientImageOn v Ω Ω
  have hF : MeasurableSet F :=
    measurableSet_subgradientImageOn_of_isOpen hΩ hv hvc hΩ (subset_refl _)
  have hAB : (volume : Measure E) (A ∩ B) = 0 := by
    apply volume_inter_subgradientImageOn_eq_zero_of_disjoint hΩ hv hvc hGΩ sdiff_subset
    apply Set.disjoint_left.mpr
    intro x hx hxB
    exact hxB.2 hx
  let T := toMeasurable (volume : Measure E) (A ∩ B)
  have hTm : MeasurableSet T := measurableSet_toMeasurable _ _
  have hT0 : (volume : Measure E) T = 0 := by
    dsimp [T]
    rw [measure_toMeasurable, hAB]
  have hAT : AnalyticSet (A \ T) :=
    analytic_inter_of_pair (analyticSet_subgradientImageOn hΩ hvc hG hGΩ) hTm.compl.analyticSet
  have hBT : AnalyticSet (B \ T) :=
    analytic_inter_of_pair
      (analyticSet_subgradientImageOn hΩ hvc (hΩ.measurableSet.diff hG) sdiff_subset)
      hTm.compl.analyticSet
  have hdis : Disjoint (A \ T) (B \ T) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact hx.2 (subset_toMeasurable volume (A ∩ B) ⟨hx.1, hy.1⟩)
  obtain ⟨S, hAS, hBS, hSm⟩ := hAT.measurablySeparable hBT hdis
  have hAF : A ⊆ F := subgradientImageOn_mono v Ω hGΩ
  have hBF : B ⊆ F := subgradientImageOn_mono v Ω sdiff_subset
  have hunion : A ∪ B = F := by
    apply Subset.antisymm (union_subset hAF hBF)
    rintro p ⟨x, hx, hp⟩
    by_cases hxG : x ∈ G
    · exact Or.inl ⟨x, hxG, hp⟩
    · exact Or.inr ⟨x, ⟨hx, hxG⟩, hp⟩
  have heq : A \ T = S ∩ (F \ T) := by
    apply Subset.antisymm
    · intro x hx
      exact ⟨hAS hx, ⟨by rw [← hunion]; exact Or.inl hx.1, hx.2⟩⟩
    · intro x hx
      have hxF : x ∈ A ∪ B := by rw [hunion]; exact hx.2.1
      rcases hxF with hxA | hxB
      · exact ⟨hxA, hx.2.2⟩
      · exact (Set.disjoint_left.mp hBS ⟨hxB, hx.2.2⟩ hx.1).elim
  have hm : MeasurableSet (A \ T) := by rw [heq]; exact hSm.inter (hF.diff hTm)
  have hnull : (volume : Measure E) (A ∩ T) = 0 := measure_mono_null inter_subset_right hT0
  have hu : (A \ T) ∪ (A ∩ T) = A := by
    ext x; simp only [mem_union, mem_sdiff, mem_inter_iff];
    tauto
  change NullMeasurableSet A volume
  rw [← hu]
  exact hm.nullMeasurableSet.union_null hnull

/-- A C0 convex function on an open domain produces its actual Monge--Ampere
measure on ambient space, with the supporting-image formula for every Borel
set and finiteness on compact sets contained INSIDE the domain. No solution,
density, total-mass or desired measure is supplied. Zero dimension is included. -/
theorem exists_domain_mongeAmpere_measure {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {v : E → ℝ} {Ω : Set E} (hΩ : IsOpen Ω) (hv : ConvexOn ℝ Ω v) (hvc : ContinuousOn v Ω) :
    ∃ μ : Measure E,
      (∀ G : Set E,
          MeasurableSet G → μ G = (volume : Measure E) (subgradientImageOn v Ω (G ∩ Ω))) ∧
        (∀ K : Set E, IsCompact K → K ⊆ Ω → μ K < ⊤) := by
  classical
  let m : ∀ G : Set E, MeasurableSet G → ℝ≥0∞ := fun G _ =>
    (volume : Measure E) (subgradientImageOn v Ω (G ∩ Ω))
  have m0 : m ∅ MeasurableSet.empty = 0 := by simp [m, subgradientImageOn]
  have mU :
    ∀ ⦃f : ℕ → Set E⦄ (hf : ∀ i, MeasurableSet (f i)),
      Pairwise (fun i j => Disjoint (f i) (f j)) →
        m (⋃ i, f i) (MeasurableSet.iUnion hf) = ∑' i, m (f i) (hf i) := by
    intro f hf hd
    change
      (volume : Measure E) (subgradientImageOn v Ω ((⋃ i, f i) ∩ Ω)) =
        ∑' i, (volume : Measure E) (subgradientImageOn v Ω (f i ∩ Ω))
    rw [iUnion_inter, subgradientImageOn_iUnion]
    apply measure_iUnion₀
    · intro i j hij
      change
        (volume : Measure E)
            (subgradientImageOn v Ω (f i ∩ Ω) ∩ subgradientImageOn v Ω (f j ∩ Ω)) =
          0
      exact
        volume_inter_subgradientImageOn_eq_zero_of_disjoint hΩ hv hvc inter_subset_right
          inter_subset_right ((hd hij).mono inter_subset_left inter_subset_left)
    · intro i
      exact
        nullMeasurableSet_subgradientImageOn_of_measurableSet hΩ hv hvc
          ((hf i).inter hΩ.measurableSet) inter_subset_right
  let μ : Measure E := Measure.ofMeasurable m m0 mU
  have hμ :
    ∀ G : Set E,
      MeasurableSet G → μ G = (volume : Measure E) (subgradientImageOn v Ω (G ∩ Ω)) := by
    intro G hG
    exact Measure.ofMeasurable_apply G hG
  refine ⟨μ, hμ, ?_⟩
  intro K hK hKΩ
  rw [hμ K hK.isClosed.measurableSet, inter_eq_left.mpr hKΩ]
  exact (isCompact_subgradientImageOn_of_isCompact hΩ hv hvc hK hKΩ).measure_lt_top

/-- Actual supporting-image volume is countably additive on disjoint OPEN
subsets of the domain. This is not yet a constructed measure on Borel sets. -/
theorem volume_subgradientImageOn_iUnion_of_pairwise_disjoint_open {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] {ι : Type*} [Countable ι] {v : E → ℝ} {Ω : Set E} {G : ι → Set E}
    (hΩ : IsOpen Ω) (hv : ConvexOn ℝ Ω v) (hvc : ContinuousOn v Ω) (hG : ∀ i, IsOpen (G i))
    (hGΩ : ∀ i, G i ⊆ Ω) (hdis : Pairwise (fun i j => Disjoint (G i) (G j))) :
    (volume : Measure E) (subgradientImageOn v Ω (⋃ i, G i)) =
      ∑' i, (volume : Measure E) (subgradientImageOn v Ω (G i)) := by
  obtain ⟨μ, hμ, _hfin⟩ := exists_domain_mongeAmpere_measure hΩ hv hvc
  have hUΩ : (⋃ i, G i) ⊆ Ω := iUnion_subset hGΩ
  have hU : μ (⋃ i, G i) = (volume : Measure E) (subgradientImageOn v Ω (⋃ i, G i)) := by
    simpa only [inter_eq_left.mpr hUΩ] using
      hμ (⋃ i, G i) (MeasurableSet.iUnion (fun i => (hG i).measurableSet))
  calc
    (volume : Measure E) (subgradientImageOn v Ω (⋃ i, G i)) = μ (⋃ i, G i) := hU.symm
    _ = ∑' i, μ (G i) := measure_iUnion hdis (fun i => (hG i).measurableSet)
    _ = ∑' i, (volume : Measure E) (subgradientImageOn v Ω (G i)) := by
      apply tsum_congr
      intro i
      simpa only [inter_eq_left.mpr (hGΩ i)] using hμ (G i) (hG i).measurableSet

end DomainImageMeasurability

end FunctionalInequalities.Analysis
