module

public import FunctionalInequalities.Analysis.Convex.Alexandrov.Comparison
public import Mathlib.Topology.MetricSpace.Equicontinuity
public import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
public import Mathlib.Topology.Sequences

/-!
# Equicontinuity of convex Dirichlet solution families

Boundary estimates for actual domain Monge--Ampere equations, combined with
convex interior Lipschitz estimates, give closure equicontinuity without a
regular extension outside the domain. This is compactness infrastructure for
Letwin arXiv:2607.24164v1 Lemma 2.2 through Berman--Berndtsson
arXiv:1207.6128v1 Theorem 2.24(ii), not a reference-existence or W2p theorem.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Metric Filter
open scoped ENNReal RealInnerProductSpace Topology

namespace FunctionalInequalities.Analysis

private lemma le_add_one_of_pow_le
    {n : ℕ} (hn : 0 < n) {t K : ℝ}
    (hK : 0 ≤ K) (hpow : t ^ n ≤ K) :
    t ≤ K + 1 := by
  by_contra hnot
  have htk : K < t := by
    linarith
  have ht1 : 1 ≤ t := by
    linarith
  have htp : t ≤ t ^ n := le_self_pow₀ ht1 hn.ne'
  linarith

private theorem dirichlet_family_compactness_of_mass_and_nonpos
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    {ι : Type*} {Ω : Set E} (hΩ : IsOpen Ω) (hΩconv : Convex ℝ Ω)
    (hb : Bornology.IsBounded Ω) {M : ℝ} (hM : 0 ≤ M)
    (u : ι → E → ℝ)
    (hu : ∀ i, ConvexOn ℝ (closure Ω) (u i))
    (huc : ∀ i, ContinuousOn (u i) (closure Ω))
    (hfr : ∀ i, ∀ x ∈ frontier Ω, u i x = 0)
    (hmass : ∀ i, (volume : Measure E)
      (subgradientImageOn (u i) Ω Ω) ≤ ENNReal.ofReal M)
    (hunonpos : ∀ i, ∀ x ∈ Ω, u i x ≤ 0) :
    ∃ B : ℝ, 0 < B ∧
      (∀ i, ∀ x ∈ closure Ω, |u i x| ≤ B) ∧
      EquicontinuousOn u (closure Ω) := by
  obtain ⟨C, hC, hpower⟩ :=
    exists_pos_boundary_power_bound_of_domain_mass (E := E)

  let K : ℝ :=
    C * M *
      diam Ω ^ (Module.finrank ℝ E - 1) * diam Ω
  let B : ℝ := K + 1

  have hfinrank : 0 < Module.finrank ℝ E :=
    Module.finrank_pos (R := ℝ) (M := E)

  have hdiam : 0 ≤ diam Ω :=
    Metric.diam_nonneg

  have hK : 0 ≤ K := by
    dsimp [K]
    positivity

  have hB : 0 < B := by
    dsimp [B]
    linarith

  have habs_bound :
      ∀ i, ∀ x ∈ closure Ω, |u i x| ≤ B := by
    intro i x hx
    have hxsplit : x ∈ Ω ∪ frontier Ω := by
      rw [← closure_eq_self_union_frontier]
      exact hx
    rcases hxsplit with hxΩ | hxfront
    · have hnonpos : u i x ≤ 0 := hunonpos i x hxΩ
      have hpow' :=
        hpower Ω (u i) M hΩ hΩconv hb (hu i) (huc i)
          (fun y hy => (hfr i y hy).ge) hM (hmass i) x hxΩ
      have hdistdiam :
          infDist x (frontier Ω) ≤ diam Ω :=
        infDist_frontier_le_diam_of_mem hb hxΩ
      have hpowK :
          (max 0 (-u i x)) ^ Module.finrank ℝ E ≤ K := by
        have hcoef :
            0 ≤
              C * M *
                diam Ω ^ (Module.finrank ℝ E - 1) := by
          positivity
        calc
          (max 0 (-u i x)) ^ Module.finrank ℝ E ≤
              C * M *
                diam Ω ^ (Module.finrank ℝ E - 1) *
                  infDist x (frontier Ω) := hpow'
          _ ≤ K := by
            dsimp [K]
            exact mul_le_mul_of_nonneg_left hdistdiam hcoef
      have hmax :
          max 0 (-u i x) ≤ K + 1 :=
        le_add_one_of_pow_le hfinrank
          hK hpowK
      rw [abs_of_nonpos hnonpos]
      simpa only [max_eq_right (neg_nonneg.mpr hnonpos), B] using hmax
    · rw [hfr i x hxfront, abs_zero]
      exact hB.le

  refine ⟨B, hB, habs_bound, ?_⟩

  have local_modulus :
      ∀ x₀ ∈ closure Ω, ∀ ε : ℝ, 0 < ε →
        ∃ δ : ℝ, 0 < δ ∧
          ∀ y ∈ closure Ω, dist y x₀ < δ →
            ∀ i, dist (u i x₀) (u i y) < ε := by
    intro x₀ hx₀ ε hε
    have hxsplit : x₀ ∈ Ω ∪ frontier Ω := by
      rw [← closure_eq_self_union_frontier]
      exact hx₀
    rcases hxsplit with hxΩ | hxfront
    · obtain ⟨r, hr, hball⟩ :=
        Metric.isOpen_iff.mp hΩ x₀ hxΩ
      let e : ℝ := r / 2
      have he : 0 < e := by
        dsimp [e]
        linarith

      have hLip (i : ι) :
          LipschitzOnWith
            (2 * B / e).toNNReal
            (u i)
            (ball x₀ (r - e)) := by
        apply ConvexOn.lipschitzOnWith_of_abs_le
          ((hu i).subset (hball.trans subset_closure) (convex_ball x₀ r))
          he
        intro z hz
        exact habs_bound i z (subset_closure (hball hz))

      let L : NNReal := (2 * B / e).toNNReal
      have hL : 0 ≤ (L : ℝ) := by
        positivity
      have hden : 0 < (L : ℝ) + 1 := by
        linarith
      let δ : ℝ := min e (ε / ((L : ℝ) + 1))
      have hδ : 0 < δ := by
        dsimp [δ]
        exact lt_min he (div_pos hε hden)

      refine ⟨δ, hδ, ?_⟩
      intro y hycl hdist i
      have hdist_e : dist y x₀ < e := by
        exact lt_of_lt_of_le hdist (min_le_left _ _)
      have hxball : x₀ ∈ ball x₀ (r - e) := by
        rw [Metric.mem_ball]
        have : 0 < r - e := by
          dsimp [e]
          linarith
        simpa using this
      have hyball : y ∈ ball x₀ (r - e) := by
        rw [Metric.mem_ball]
        have heq : r - e = e := by
          dsimp [e]
          ring
        rw [heq]
        exact hdist_e

      have hLip' := (hLip i).dist_le_mul _ hxball _ hyball
      have hdistxy : dist x₀ y < ε / ((L : ℝ) + 1) := by
        have hdistxy' : dist x₀ y < δ := by
          simpa only [dist_comm] using hdist
        exact lt_of_lt_of_le hdistxy' (min_le_right _ _)
      have hmul :
          (L : ℝ) * dist x₀ y < ε := by
        have hle :
            (L : ℝ) * dist x₀ y ≤
              ((L : ℝ) + 1) * dist x₀ y := by
          nlinarith [dist_nonneg (x := x₀) (y := y)]
        have hlt :
            ((L : ℝ) + 1) * dist x₀ y <
              ((L : ℝ) + 1) * (ε / ((L : ℝ) + 1)) :=
          mul_lt_mul_of_pos_left hdistxy hden
        have heq :
            ((L : ℝ) + 1) * (ε / ((L : ℝ) + 1)) = ε := by
          field_simp [ne_of_gt hden]
        linarith
      exact hLip'.trans_lt hmul
    · obtain ⟨ρ, hρ, hρmod⟩ :=
        exists_common_boundary_modulus_of_domain_mass
          (E := E) hΩ hΩconv hb hM
          (ε := ε / 2) (half_pos hε)
      refine ⟨ρ, hρ, ?_⟩
      intro y hycl hdist i
      by_cases hyΩ : y ∈ Ω
      · have hinf :
            infDist y (frontier Ω) ≤ dist y x₀ :=
          Metric.infDist_le_dist_of_mem hxfront
        have hdistρ :
            infDist y (frontier Ω) < ρ :=
          lt_of_le_of_lt hinf (by simpa [dist_comm] using hdist)
        have hybound :
            |u i y| ≤ ε / 2 :=
          hρmod (u i) (hu i) (huc i) (hfr i)
            (hmass i) y hyΩ hdistρ
        have hxzero : u i x₀ = 0 :=
          hfr i x₀ hxfront
        have hdistval :
            dist (u i x₀) (u i y) = |u i y| := by
          simp [Real.dist_eq, hxzero]
        rw [hdistval]
        linarith
      · have hyfront : y ∈ frontier Ω := by
          rw [hΩ.frontier_eq]
          exact ⟨hycl, hyΩ⟩
        rw [hfr i x₀ hxfront, hfr i y hyfront, dist_self]
        exact hε

  intro x₀ hx₀ U hU
  rcases mem_uniformity_dist.mp hU with ⟨ε, hε, hεU⟩
  obtain ⟨δ, hδ, hδmod⟩ :=
    local_modulus x₀ hx₀ ε hε
  have hev :
      ∀ᶠ y in 𝓝[closure Ω] x₀, y ∈ ball x₀ δ :=
    nhdsWithin_le_nhds (Metric.ball_mem_nhds x₀ hδ)
  filter_upwards [hev, eventually_mem_nhdsWithin] with y hy hycl
  intro i
  apply hεU
  exact hδmod y hycl (Metric.mem_ball.mp hy) i


/-- Finite actual total domain MA mass produces a common positive closure value
bound and equicontinuity. No density ceiling or positive lower density is
required; all estimates and moduli are derived from the actual source data. -/
theorem exists_uniform_bound_equicontinuousOn_of_domain_mass
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    {ι : Type*} {Ω : Set E} (hΩ : IsOpen Ω) (hΩconv : Convex ℝ Ω)
    (hb : Bornology.IsBounded Ω) {M : ℝ} (hM : 0 ≤ M)
    (u : ι → E → ℝ)
    (hu : ∀ i, ConvexOn ℝ (closure Ω) (u i))
    (huc : ∀ i, ContinuousOn (u i) (closure Ω))
    (hfr : ∀ i, ∀ x ∈ frontier Ω, u i x = 0)
    (hmass : ∀ i, (volume : Measure E)
      (subgradientImageOn (u i) Ω Ω) ≤ ENNReal.ofReal M) :
    ∃ B : ℝ, 0 < B ∧
      (∀ i, ∀ x ∈ closure Ω, |u i x| ≤ B) ∧
      EquicontinuousOn u (closure Ω) := by
  apply dirichlet_family_compactness_of_mass_and_nonpos
    hΩ hΩconv hb hM u hu huc hfr hmass
  intro i x hx
  exact le_on_closure_of_le_frontier_of_convexOn hΩ hΩconv hb (hu i) (huc i)
    (fun y hy => (hfr i y hy).le) x (subset_closure hx)

/-- Actual uniform domain MA density bounds and zero boundary data make a
family of closure-convex continuous solutions equicontinuous on the closure.
Uniform value and local Lipschitz bounds are produced from the MA estimates;
no global extension or desired regularity is an input. This bounded-density
statement does not assert compactness for atomic-MA approximants. -/
theorem equicontinuousOn_of_domain_alexandrov_bounds
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    {ι : Type*} {Ω : Set E} (hΩ : IsOpen Ω) (hΩconv : Convex ℝ Ω)
    (hb : Bornology.IsBounded Ω) {a Λ : ℝ} (ha : 0 < a) (hΛ : 0 ≤ Λ)
    (u : ι → E → ℝ)
    (hu : ∀ i, ConvexOn ℝ (closure Ω) (u i))
    (huc : ∀ i, ContinuousOn (u i) (closure Ω))
    (hfr : ∀ i, ∀ x ∈ frontier Ω, u i x = 0)
    (hMAl : ∀ i, ∀ H : Set E, IsOpen H → H ⊆ Ω →
      ENNReal.ofReal a * (volume : Measure E) H ≤
        volume (FunctionalInequalities.Analysis.subgradientImageOn (u i) Ω H))
    (hMAu : ∀ i, ∀ H : Set E, IsOpen H → H ⊆ Ω →
      volume (FunctionalInequalities.Analysis.subgradientImageOn (u i) Ω H) ≤
        ENNReal.ofReal Λ * (volume : Measure E) H) :
    EquicontinuousOn u (closure Ω) := by
  let M : ℝ := Λ * ((volume : Measure E) Ω).toReal
  have hM : 0 ≤ M := mul_nonneg hΛ ENNReal.toReal_nonneg
  have hmass : ∀ i, (volume : Measure E) (subgradientImageOn (u i) Ω Ω) ≤ ENNReal.ofReal M := by
    intro i
    exact volume_subgradientImageOn_le_of_density_le hΩ hb hΛ (hMAu i)
  have hnonpos : ∀ i, ∀ x ∈ Ω, u i x ≤ 0 := by
    intro i x hx
    exact nonpos_of_pos_domain_alexandrov_lower hΩ hΩconv hb (hu i) (huc i)
      (fun y hy => (hfr i y hy).le) ha (hMAl i) x hx
  obtain ⟨B, hB, hcap, heq⟩ := dirichlet_family_compactness_of_mass_and_nonpos
    hΩ hΩconv hb hM u hu huc hfr hmass hnonpos
  exact heq

/-- Genuine uniform convergence of a strictly increasing subsequence on the
closure, derived from the actual finite-total DOMAIN MA source class. The
limit is a continuous map; no limit MA equation or reference existence is
asserted, and no cap, equicontinuity or subsequence is supplied as input. -/
theorem exists_subseq_uniform_on_closure_of_domain_mass {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E]
    [BorelSpace E] {Ω : Set E} (hΩ : IsOpen Ω) (hΩconv : Convex ℝ Ω)
    (hb : Bornology.IsBounded Ω) {M : ℝ} (hM : 0 ≤ M) (u : ℕ → E → ℝ)
    (hu : ∀ i, ConvexOn ℝ (closure Ω) (u i)) (huc : ∀ i, ContinuousOn (u i) (closure Ω))
    (hfr : ∀ i, ∀ x ∈ frontier Ω, u i x = 0)
    (hmass : ∀ i, (volume : Measure E) (subgradientImageOn (u i) Ω Ω) ≤ ENNReal.ofReal M) :
    ∃ (g : C(closure Ω, ℝ)) (φ : ℕ → ℕ),
      StrictMono φ ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ x : closure Ω, |u (φ n) x - g x| < ε := by
  classical
  obtain ⟨B, hB, hcap, heq⟩ :=
    exists_uniform_bound_equicontinuousOn_of_domain_mass hΩ hΩconv hb hM u hu huc hfr hmass
  let : CompactSpace (closure Ω) := isCompact_iff_compactSpace.mp hb.isCompact_closure
  let f : ℕ → (BoundedContinuousFunction (closure Ω) ℝ) := fun n =>
    BoundedContinuousFunction.mkOfCompact
      ⟨(fun x : closure Ω => u n x), (continuousOn_iff_continuous_domRestrict.mp (huc n))⟩
  have hrestr : Equicontinuous (fun n (x : closure Ω) => f n x) := by
    exact (equicontinuous_restrict_iff u).mpr heq
  have hchoice : ∀ q : range f, ∃ n : ℕ, f n = q.val := fun q => q.property
  choose idx hidx using hchoice
  have hrange : Equicontinuous (fun (q : range f) (x : closure Ω) => q.val x) := by
    convert hrestr.comp idx using 1
    funext q x
    exact congrArg (fun g : BoundedContinuousFunction (closure Ω) ℝ => g x) (hidx q).symm
  have hin :
    ∀ (g : BoundedContinuousFunction (closure Ω) ℝ) (x : closure Ω),
      g ∈ range f → g x ∈ Icc (-B) B := by
    rintro g x ⟨n, rfl⟩
    exact abs_le.mp (hcap n x.val x.property)
  have hcompact :=
    BoundedContinuousFunction.arzela_ascoli (Icc (-B) B) isCompact_Icc (range f) hin hrange
  obtain ⟨g, _hg, φ, hφ, hlim⟩ :=
    hcompact.tendsto_subseq (fun n => subset_closure (mem_range_self n))
  refine ⟨g.toContinuousMap, φ, hφ, ?_⟩
  intro ε hε
  filter_upwards [(Metric.tendsto_nhds.mp hlim) ε hε] with n hn
  intro x
  change dist (f (φ n)) g < ε at hn
  have hp : dist (f (φ n) x) (g x) ≤ dist (f (φ n)) g :=
    BoundedContinuousFunction.dist_coe_le_dist x
  have hfval : f (φ n) x = u (φ n) x := rfl
  rw [hfval, Real.dist_eq] at hp
  change |u (φ n) x - g x| < ε
  linarith only [hp, hn]


/-- The actual finite-total-mass uniform subsequence has a closure-convex,
continuous, zero-boundary limit. These fields follow from genuine uniform and
pointwise convergence, not a supplied limit regularity or MA stability theorem.
No limit MA equation or existence of approximating solutions is asserted. -/
theorem exists_convex_subseq_uniform_of_domain_mass {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E]
    [BorelSpace E] {Ω : Set E} (hΩ : IsOpen Ω) (hΩconv : Convex ℝ Ω)
    (hb : Bornology.IsBounded Ω) {M : ℝ} (hM : 0 ≤ M) (u : ℕ → E → ℝ)
    (hu : ∀ i, ConvexOn ℝ (closure Ω) (u i)) (huc : ∀ i, ContinuousOn (u i) (closure Ω))
    (hfr : ∀ i, ∀ x ∈ frontier Ω, u i x = 0)
    (hmass : ∀ i, (volume : Measure E) (subgradientImageOn (u i) Ω Ω) ≤ ENNReal.ofReal M) :
    ∃ (g : E → ℝ) (φ : ℕ → ℕ),
      StrictMono φ ∧
        ConvexOn ℝ (closure Ω) g ∧
          ContinuousOn g (closure Ω) ∧
            (∀ x ∈ frontier Ω, g x = 0) ∧
              ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ x ∈ closure Ω, |u (φ n) x - g x| < ε := by
  classical
  obtain ⟨g₀, φ, hφ, hlim⟩ :=
    exists_subseq_uniform_on_closure_of_domain_mass hΩ hΩconv hb hM u hu huc hfr hmass
  let g : E → ℝ := fun x => if hx : x ∈ closure Ω then g₀ ⟨x, hx⟩ else 0
  have hg (x : E) (hx : x ∈ closure Ω) : g x = g₀ ⟨x, hx⟩ := by simp only [g, dite_eq_left hx]
  have hpt (x : E) (hx : x ∈ closure Ω) : Tendsto (fun n => u (φ n) x) atTop (𝓝 (g x)) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [hlim ε hε] with n hn
    rw [Real.dist_eq, hg x hx]
    exact hn ⟨x, hx⟩
  have hgc : ContinuousOn g (closure Ω) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have heq : (closure Ω).domRestrict g = g₀ := by
      funext x
      exact hg x.val x.property
    rw [heq]
    exact g₀.continuous
  have hconv : ConvexOn ℝ (closure Ω) g := by
    refine ⟨hΩconv.closure, ?_⟩
    intro x hx y hy a b ha hb hab
    have hz := hΩconv.closure hx hy ha hb hab
    exact
      le_of_tendsto_of_tendsto (hpt _ hz)
        (((tendsto_const_nhds.mul (hpt x hx))).add (tendsto_const_nhds.mul (hpt y hy)))
        (Filter.Eventually.of_forall (fun n => (hu (φ n)).2 hx hy ha hb hab))
  refine ⟨g, φ, hφ, hconv, hgc, ?_, ?_⟩
  · intro x hx
    have heq : (fun n => u (φ n) x) = fun _ : ℕ => (0 : ℝ) := by
      funext n
      exact hfr (φ n) x hx
    have hp := hpt x (frontier_subset_closure hx)
    rw [heq] at hp
    exact tendsto_nhds_unique hp tendsto_const_nhds
  · intro ε hε
    filter_upwards [hlim ε hε] with n hn
    intro x hx
    rw [hg x hx]
    exact hn ⟨x, hx⟩

end FunctionalInequalities.Analysis
