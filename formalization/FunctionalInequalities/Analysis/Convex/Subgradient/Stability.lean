module

public import FunctionalInequalities.Analysis.Convex.Subgradient.Existence
public import Mathlib.Topology.UniformSpace.UniformApproximation
public import Mathlib.Topology.MetricSpace.Thickening

/-!
# Supporting images under locally uniform convergence

Supporting convex infrastructure for Letwin arXiv:2607.24164v1
Theorem 1.2 and Lemma 2.2. Mathematical scopes and source attributions
are retained in the individual declarations. Section `GradientConvergence`:
if convex functions converge pointwise on a finite-dimensional real
inner-product space, their gradients converge at every point where the limit and
all the functions are differentiable (Rockafellar, *Convex Analysis*, Theorem 24.5;
`tendsto_gradient_of_tendsto_of_convexOn`).
-/

@[expose] public section

noncomputable section
open Set
open scoped RealInnerProductSpace

namespace FunctionalInequalities.Analysis
open Set Metric Filter
open scoped Topology
/-- Locally uniform convergence to a continuous function generates an eventual uniform
bound for ALL actual supporting slopes on a compact interior set. The approximating
functions need not be convex, continuous, or differentiable. -/
theorem exists_eventual_support_slope_bound_of_locally_uniform {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {f : ℕ → E → ℝ}
    {v : E → ℝ} {Ω K : Set E} (hΩ : IsOpen Ω) (hvc : ContinuousOn v Ω)
    (hlim : TendstoLocallyUniformlyOn f v atTop Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    ∃ R : ℝ,
      0 ≤ R ∧
        ∀ᶠ n in atTop, ∀ x ∈ K, ∀ p : E, (∀ y ∈ Ω, f n x + ⟪p, y - x⟫ ≤ f n y) → ‖p‖ ≤ R := by
  obtain ⟨δ, hδ, hLΩ⟩ := hK.exists_cthickening_subset_open hΩ hKΩ
  let L := cthickening δ K
  have hL : IsCompact L := hK.cthickening
  obtain ⟨C, hC⟩ := hL.exists_bound_of_continuousOn (hvc.mono hLΩ)
  let M : ℝ := max C 0 + 1
  have hM : 0 < M := by dsimp [M]; positivity
  have hu : TendstoUniformlyOn f v atTop L :=
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hL).mp (hlim.mono hLΩ)
  have herr : ∀ᶠ n in atTop, ∀ y ∈ L, dist (v y) (f n y) < 1 :=
    hu _ (dist_mem_uniformity zero_lt_one)
  refine ⟨2 * M / δ, by positivity, ?_⟩
  filter_upwards [herr] with n hn
  have hfn : ∀ y ∈ L, |f n y| ≤ M := by
    intro y hy
    have hvy : |v y| ≤ C := by simpa only [Real.norm_eq_abs] using hC y hy
    have hdiff : |f n y - v y| < 1 := by simpa only [Real.dist_eq, abs_sub_comm] using hn y hy
    have hh := abs_add_le (f n y - v y) (v y)
    rw [sub_add_cancel] at hh
    have hmax : C ≤ max C 0 := le_max_left _ _
    dsimp [M]
    linarith
  intro x hx p hp
  have hball : closedBall x δ ⊆ L := by
    intro y hy
    exact mem_cthickening_of_dist_le y x δ K hx (mem_closedBall.mp hy)
  exact norm_subgradient_le_of_closedBall hδ (hball.trans hLΩ) (fun y hy => hfn y (hball hy)) hp

/-- Actual supporting images of compact interior sets are upper stable under
locally uniform convergence to a continuous function. Compactness produces the SAME
limit basepoint and slope, and every domain support inequality passes to that limit.
No convexity or regularity of the approximating functions is required. -/
theorem eventually_subgradientImageOn_subset_of_tendstoLocallyUniformlyOn {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {f : ℕ → E → ℝ}
    {v : E → ℝ} {Ω K U : Set E} (hΩ : IsOpen Ω) (hvc : ContinuousOn v Ω)
    (hlim : TendstoLocallyUniformlyOn f v atTop Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (hU : IsOpen U) (hI : subgradientImageOn v Ω K ⊆ U) :
    ∀ᶠ n in atTop, subgradientImageOn (f n) Ω K ⊆ U := by
  classical
  obtain ⟨R, _hR, hcap⟩ :=
    exists_eventual_support_slope_bound_of_locally_uniform hΩ hvc hlim hK hKΩ
  by_contra hno
  have hbad : ∃ᶠ n in atTop, ¬subgradientImageOn (f n) Ω K ⊆ U := by
    simpa only [Filter.Frequently, not_not] using hno
  obtain ⟨j, hj, hjbad⟩ := exists_seq_forall_of_frequently (hbad.and_eventually hcap)
  have hex :
    ∀ n : ℕ,
      ∃ x ∈ K, ∃ p : E, (∀ y ∈ Ω, f (j n) x + ⟪p, y - x⟫ ≤ f (j n) y) ∧ p ∉ U ∧ ‖p‖ ≤ R := by
    intro n
    obtain ⟨p, hp, hpU⟩ := Set.not_subset.mp (hjbad n).1
    obtain ⟨x, hx, hxp⟩ := hp
    exact ⟨x, hx, p, hxp, hpU, (hjbad n).2 x hx p hxp⟩
  choose x hx p hp hpU hpR using hex
  have hcompact : IsCompact (K ×ˢ closedBall (0 : E) R) := hK.prod (isCompact_closedBall 0 R)
  have hmem : ∀ n : ℕ, (x n, p n) ∈ K ×ˢ closedBall (0 : E) R := by
    intro n
    exact ⟨hx n, by simpa only [mem_closedBall, dist_zero_right] using hpR n⟩
  obtain ⟨z, hz, k, hk, hzk⟩ := hcompact.tendsto_subseq hmem
  have hxlim : Tendsto (fun n => x (k n)) atTop (𝓝 z.1) := by
    simpa only [Function.comp_def] using (continuous_fst.tendsto z).comp hzk
  have hplim : Tendsto (fun n => p (k n)) atTop (𝓝 z.2) := by
    simpa only [Function.comp_def] using (continuous_snd.tendsto z).comp hzk
  have hjk : Tendsto (fun n => j (k n)) atTop atTop := hj.comp hk.tendsto_atTop
  have hres : TendstoLocallyUniformlyOn (fun n => f (j (k n))) v atTop Ω := by
    intro V hV a ha
    obtain ⟨t, ht, h⟩ := hlim V hV a ha
    exact ⟨t, ht, hjk.eventually h⟩
  have hxwithin : Tendsto (fun n => x (k n)) atTop (𝓝[Ω] z.1) :=
    tendsto_nhdsWithin_iff.mpr ⟨hxlim, Eventually.of_forall (fun n => hKΩ (hx (k n)))⟩
  have hval : Tendsto (fun n => f (j (k n)) (x (k n))) atTop (𝓝 (v z.1)) :=
    hres.tendsto_comp (hvc z.1 (hKΩ hz.1)) (hKΩ hz.1) hxwithin
  have hs : ∀ y ∈ Ω, v z.1 + ⟪z.2, y - z.1⟫ ≤ v y := by
    intro y hy
    have hyval : Tendsto (fun n => f (j (k n)) y) atTop (𝓝 (v y)) := hres.tendsto_at hy
    have hin : Tendsto (fun n => ⟪p (k n), y - x (k n)⟫) atTop (𝓝 ⟪z.2, y - z.1⟫) :=
      hplim.inner (tendsto_const_nhds.sub hxlim)
    exact
      le_of_tendsto_of_tendsto (hval.add hin) hyval
        (Eventually.of_forall (fun n => hp (k n) y hy))
  have hzU : z.2 ∈ U := hI ⟨z.1, hz.1, hs⟩
  have hev : ∀ᶠ n in atTop, p (k n) ∈ U := hplim.eventually (hU.mem_nhds hzU)
  obtain ⟨n, hn⟩ := hev.exists
  exact hpU (k n) hn

end FunctionalInequalities.Analysis
namespace FunctionalInequalities.Analysis
open Set Metric Filter
open scoped Topology
/-- A genuinely unique supporting contact of a continuous limit persists inside
any open neighborhood under locally uniform convergence of convex continuous
potentials. The sphere gap and interior minimum are produced from the source
conditions; no contact of the approximants is assumed. All finite dimensions. -/
theorem eventually_mem_subgradientImageOn_of_unique_contact {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {f : ℕ → E → ℝ} {v : E → ℝ} {Ω G : Set E}
    {x p : E} (hΩ : IsOpen Ω) (hf : ∀ n, ConvexOn ℝ Ω (f n)) (hfc : ∀ n, ContinuousOn (f n) Ω)
    (hvc : ContinuousOn v Ω) (hlim : TendstoLocallyUniformlyOn f v atTop Ω) (hG : IsOpen G)
    (hGΩ : G ⊆ Ω) (hx : x ∈ G) (hp : ∀ y ∈ Ω, v x + ⟪p, y - x⟫ ≤ v y)
    (hunique : ∀ y ∈ Ω, v y = v x + ⟪p, y - x⟫ → y = x) :
    ∀ᶠ n in atTop, p ∈ subgradientImageOn (f n) Ω G := by
  obtain ⟨ε, hε, hεG⟩ := Metric.mem_nhds_iff.mp ((hG.inter hΩ).mem_nhds ⟨hx, hGΩ hx⟩)
  let r : ℝ := ε / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hBGO : closedBall x r ⊆ G ∩ Ω := by
    intro y hy
    apply hεG
    apply mem_ball.mpr
    have hd := mem_closedBall.mp hy
    dsimp [r] at hd
    linarith
  have hBG : closedBall x r ⊆ G := fun _ hy => (hBGO hy).1
  have hBO : closedBall x r ⊆ Ω := fun _ hy => (hBGO hy).2
  have hSO : sphere x r ⊆ Ω := sphere_subset_closedBall.trans hBO
  let F : E → ℝ := fun y => v y - v x - ⟪p, y - x⟫
  have hFc : ContinuousOn F (sphere x r) := by
    dsimp [F]
    exact
      ((hvc.mono hSO).sub continuousOn_const).sub
        (continuous_const.inner (continuous_id.sub continuous_const)).continuousOn
  have hFp : ∀ y ∈ sphere x r, 0 < F y := by
    intro y hy
    have hxy : y ≠ x := by
      intro hyx
      have heq := mem_sphere.mp hy
      rw [hyx, dist_self] at heq
      linarith
    have hs := hp y (hSO hy)
    have hlt : v x + ⟪p, y - x⟫ < v y := by
      by_contra hh
      have heq : v y = v x + ⟪p, y - x⟫ := by linarith
      exact hxy (hunique y (hSO hy) heq)
    dsimp [F]
    linarith
  obtain ⟨ρ, hρ, hgap⟩ := (isCompact_sphere x r).exists_forall_le' hFc hFp
  have hB : IsCompact (closedBall x r) := isCompact_closedBall x r
  have hu : TendstoUniformlyOn f v atTop (closedBall x r) :=
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hB).mp (hlim.mono hBO)
  have herr : ∀ᶠ n in atTop, ∀ y ∈ closedBall x r, dist (v y) (f n y) < ρ / 4 :=
    hu _ (dist_mem_uniformity (by positivity))
  filter_upwards [herr] with n hn
  let Ψ : E → ℝ := fun y => f n y - ⟪p, y⟫
  have hΨ : ContinuousOn Ψ (closedBall x r) :=
    (hfc n |>.mono hBO).sub (continuous_const.inner continuous_id).continuousOn
  have hxB : x ∈ closedBall x r := mem_closedBall_self hr.le
  have hstrict : ∀ y ∈ sphere x r, Ψ x < Ψ y := by
    intro y hy
    have hfx := hn x hxB
    have hfy := hn y (sphere_subset_closedBall hy)
    rw [Real.dist_eq] at hfx hfy
    have hfx' := abs_lt.mp hfx
    have hfy' := abs_lt.mp hfy
    have hg := hgap y hy
    dsimp [F] at hg
    rw [inner_sub_right] at hg
    dsimp [Ψ]
    linarith
  obtain ⟨z, hzB, hmin⟩ :=
    hB.exists_isMinOn_mem_subset (s := ball x r) hΨ hxB
      (fun y hy =>
        hstrict y
          (mem_sphere.mpr
            (le_antisymm (mem_closedBall.mp hy.1)
              (not_lt.mp (fun h => hy.2 (mem_ball.mpr h))))))
  have hz : z ∈ closedBall x r := ball_subset_closedBall hzB
  have hpB : ∀ y ∈ ball x r, f n z + ⟪p, y - z⟫ ≤ f n y := by
    intro y hy
    have hm := hmin (ball_subset_closedBall hy)
    dsimp [Ψ] at hm
    rw [inner_sub_right]
    linarith
  exact
    ⟨z, hBG hz,
      subgradient_le_on_of_isOpen (hf n) isOpen_ball (ball_subset_closedBall.trans hBO) hzB hpB⟩

section GradientConvergence

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem tendsto_slope_line {f : E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (v : E) :
    Tendsto (fun t : ℝ => (f (x + t • v) - f x) / t)
      (𝓝[>] 0) (𝓝 (fderiv ℝ f x v)) := by
  have hg : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have hf' : HasFDerivAt f (fderiv ℝ f x) (x + (0 : ℝ) • v) := by
    simpa using hf.hasFDerivAt
  have hh := hf'.comp_hasDerivAt 0 hg
  have hsub : Ioi (0 : ℝ) ⊆ ({0} : Set ℝ)ᶜ := by
    intro t ht
    simpa only [mem_compl_iff, mem_singleton_iff] using ne_of_gt ht
  simpa only [Function.comp_apply, zero_add, zero_smul, add_zero,
    smul_eq_mul, div_eq_mul_inv, mul_comm] using
    hh.tendsto_slope_zero.mono_left (nhdsWithin_mono 0 hsub)

/-- First-order convexity at a point of differentiability. -/
private theorem convex_support_le {f : E → ℝ} {x : E}
    (hc : ConvexOn ℝ univ f) (hf : DifferentiableAt ℝ f x) (v : E) :
    fderiv ℝ f x v ≤ f (x + v) - f x := by
  have h := Analysis.convex_support_of_hasFDerivWithinAt hc hf.hasFDerivAt.hasFDerivWithinAt
    (mem_univ x) (mem_univ (x + v))
  rw [add_sub_cancel_left] at h
  linarith

private theorem eventually_fderiv_apply_lt {ψ : ℕ → E → ℝ} {F : E → ℝ}
    (hψ : ∀ n, ConvexOn ℝ univ (ψ n))
    (hlim : ∀ y, Tendsto (fun n => ψ n y) atTop (𝓝 (F y)))
    {x : E} (hF : DifferentiableAt ℝ F x)
    (hd : ∀ n, DifferentiableAt ℝ (ψ n) x)
    (v : E) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, fderiv ℝ (ψ n) x v < fderiv ℝ F x v + ε := by
  have hq : ∀ᶠ t : ℝ in 𝓝[>] 0,
      (F (x + t • v) - F x) / t < fderiv ℝ F x v + ε :=
    (tendsto_slope_line hF v).eventually
      (eventually_lt_nhds (by linarith))
  have hpos : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
  obtain ⟨t, ht, hqt⟩ := (hpos.and hq).exists
  have hseq :
      Tendsto (fun n => (ψ n (x + t • v) - ψ n x) / t)
        atTop (𝓝 ((F (x + t • v) - F x) / t)) :=
    ((hlim (x + t • v)).sub (hlim x)).div_const t
  filter_upwards [hseq.eventually (eventually_lt_nhds hqt)] with n hn
  have hb := convex_support_le (hψ n) (hd n) (t • v)
  rw [map_smul, smul_eq_mul] at hb
  have hb' : fderiv ℝ (ψ n) x v ≤ (ψ n (x + t • v) - ψ n x) / t := by
    apply (le_div_iff₀ ht).2
    nlinarith
  exact lt_of_le_of_lt hb' hn

private theorem tendsto_fderiv_apply_of_convexOn {ψ : ℕ → E → ℝ} {F : E → ℝ}
    (hψ : ∀ n, ConvexOn ℝ univ (ψ n)) (hlim : ∀ y, Tendsto (fun n => ψ n y) atTop (𝓝 (F y)))
    {x : E} (hF : DifferentiableAt ℝ F x) (hd : ∀ n, DifferentiableAt ℝ (ψ n) x) (v : E) :
    Tendsto (fun n => fderiv ℝ (ψ n) x v) atTop (𝓝 (fderiv ℝ F x v)) := by
  apply Metric.tendsto_nhds.2
  intro ε hε
  filter_upwards [eventually_fderiv_apply_lt hψ hlim hF hd v hε,
    eventually_fderiv_apply_lt hψ hlim hF hd (-v) hε] with n hn hneg
  simp only [map_neg] at hneg
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

variable [FiniteDimensional ℝ E]

/-- Gradients of convex functions converge where the pointwise limit is differentiable
(Rockafellar, Theorem 24.5). -/
theorem tendsto_gradient_of_tendsto_of_convexOn {ψ : ℕ → E → ℝ} {F : E → ℝ}
    (hψ : ∀ l, ConvexOn ℝ univ (ψ l)) (hlim : ∀ y, Tendsto (fun l => ψ l y) atTop (𝓝 (F y)))
    {x : E} (hF : DifferentiableAt ℝ F x) (hd : ∀ l, DifferentiableAt ℝ (ψ l) x) :
    Tendsto (fun l => gradient (ψ l) x) atTop (𝓝 (gradient F x)) := by
  let b := stdOrthonormalBasis ℝ E
  have hgrad (f : E → ℝ) (v : E) : fderiv ℝ f x v = ⟪gradient f x, v⟫ := by
    simp [gradient, InnerProductSpace.toDual_symm_apply]
  have hrepr (f : E → ℝ) (i : Fin (Module.finrank ℝ E)) :
      b.repr (gradient f x) i = fderiv ℝ f x (b i) := by
    rw [b.repr_apply_apply, real_inner_comm]
    exact (hgrad f (b i)).symm
  have hi (i : Fin (Module.finrank ℝ E)) :
      Tendsto (fun n => b.repr (gradient (ψ n) x) i) atTop
        (𝓝 (b.repr (gradient F x) i)) := by
    simp only [hrepr]
    exact tendsto_fderiv_apply_of_convexOn hψ hlim hF hd (b i)
  have hs : Tendsto
      (fun n => ∑ i, (b.repr (gradient (ψ n) x) i) • b i)
      atTop (𝓝 (∑ i, (b.repr (gradient F x) i) • b i)) :=
    tendsto_finsetSum _ fun i _ => (hi i).smul tendsto_const_nhds
  simpa only [b.sum_repr] using hs

end GradientConvergence

end FunctionalInequalities.Analysis
