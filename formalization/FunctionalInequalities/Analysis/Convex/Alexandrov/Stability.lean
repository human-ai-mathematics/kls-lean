module

public import FunctionalInequalities.Analysis.Convex.Subgradient.Stability
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import FunctionalInequalities.Analysis.Convex.Alexandrov.Measure

/-! # Locally uniform stability of domain supporting-image measures

Supports the domain Monge--Ampere infrastructure for Letwin
arXiv:2607.24164v1 Lemma 2.2 through BB arXiv:1207.6128v1
Theorem 2.24(ii).
-/

@[expose] public section

noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace ENNReal

namespace FunctionalInequalities.Analysis
open Set Metric Filter
open scoped Topology
/-- Compact supporting images satisfy the upper volume inequality under actual
locally uniform convergence. Haar outer regularity is applied to the compact
limit image. The approximating functions need not be convex or continuous. -/
theorem limsup_volume_subgradientImageOn_le_of_locally_uniform {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] {f : ℕ → E → ℝ} {v : E → ℝ} {Ω K : Set E} (hΩ : IsOpen Ω)
    (hv : ConvexOn ℝ Ω v) (hvc : ContinuousOn v Ω)
    (hlim : TendstoLocallyUniformlyOn f v atTop Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    limsup (fun n => (volume : Measure E) (subgradientImageOn (f n) Ω K)) atTop ≤
      (volume : Measure E) (subgradientImageOn v Ω K) := by
  have hcompact := isCompact_subgradientImageOn_of_isCompact hΩ hv hvc hK hKΩ
  apply (limsup_le_iff (by isBoundedDefault) (by isBoundedDefault)).mpr
  intro b hb
  obtain ⟨U, hIU, hU, hUb⟩ := hcompact.exists_isOpen_lt_of_lt b hb
  filter_upwards [eventually_subgradientImageOn_subset_of_tendstoLocallyUniformlyOn hΩ hvc hlim
      hK hKΩ hU hIU] with
    n hn
  exact (measure_mono hn).trans_lt hUb

/-- Almost every actual supporting slope of the limit persists eventually in
the image of an open test set. The exceptional set and uniqueness are derived
from the actual C0 convex source, rather than assumed as an N property. -/
theorem ae_eventually_mem_subgradientImageOn_of_locally_uniform {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] {f : ℕ → E → ℝ} {v : E → ℝ} {Ω G : Set E} (hΩ : IsOpen Ω)
    (hf : ∀ n, ConvexOn ℝ Ω (f n)) (hfc : ∀ n, ContinuousOn (f n) Ω) (hv : ConvexOn ℝ Ω v)
    (hvc : ContinuousOn v Ω) (hlim : TendstoLocallyUniformlyOn f v atTop Ω) (hG : IsOpen G)
    (hGΩ : G ⊆ Ω) :
    ∀ᵐ p ∂(volume : Measure E),
      p ∈ subgradientImageOn v Ω G → ∀ᶠ n in atTop, p ∈ subgradientImageOn (f n) Ω G := by
  let S : Set E :=
    {p : E |
      ∃ x ∈ Ω,
        ∃ y ∈ Ω, x ≠ y ∧ (∀ z ∈ Ω, v x + ⟪p, z - x⟫ ≤ v z) ∧ (∀ z ∈ Ω, v y + ⟪p, z - y⟫ ≤ v z)}
  have hnull : (volume : Measure E) S = 0 :=
    volume_domain_subgradient_two_points_eq_zero hΩ hv hvc
  have havoid : ∀ᵐ p ∂(volume : Measure E), p ∉ S := by
    apply ae_iff.mpr
    simpa using hnull
  filter_upwards [havoid] with p hp
  rintro ⟨x, hx, hpx⟩
  apply eventually_mem_subgradientImageOn_of_unique_contact hΩ hf hfc hvc hlim hG hGΩ hx hpx
  intro y hy heq
  by_contra hxy
  have hpy : ∀ z ∈ Ω, v y + ⟪p, z - y⟫ ≤ v z := by
    intro z hz
    have hh := hpx z hz
    rw [inner_sub_right] at hh heq ⊢
    linarith
  exact hp ⟨x, hGΩ hx, y, hy, Ne.symm hxy, hpx, hpy⟩

/-- The actual open-domain supporting images satisfy the lower volume inequality
under locally uniform convergence of C0 convex potentials. Actual two-point
nullity supplies almost-everywhere unique contacts; Borel images and Fatou
close the inequality, including infinite volumes and zero dimension. -/
theorem volume_subgradientImageOn_le_liminf_of_locally_uniform {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] {f : ℕ → E → ℝ} {v : E → ℝ} {Ω G : Set E} (hΩ : IsOpen Ω)
    (hf : ∀ n, ConvexOn ℝ Ω (f n)) (hfc : ∀ n, ContinuousOn (f n) Ω) (hv : ConvexOn ℝ Ω v)
    (hvc : ContinuousOn v Ω) (hlim : TendstoLocallyUniformlyOn f v atTop Ω) (hG : IsOpen G)
    (hGΩ : G ⊆ Ω) :
    (volume : Measure E) (subgradientImageOn v Ω G) ≤
      liminf (fun n => (volume : Measure E) (subgradientImageOn (f n) Ω G)) atTop := by
  let A : ℕ → Set E := fun n => subgradientImageOn (f n) Ω G
  let B : Set E := subgradientImageOn v Ω G
  have hA : ∀ n, MeasurableSet (A n) := fun n =>
    measurableSet_subgradientImageOn_of_isOpen hΩ (hf n) (hfc n) hG hGΩ
  have hB : MeasurableSet B := measurableSet_subgradientImageOn_of_isOpen hΩ hv hvc hG hGΩ
  have ha :
    ∀ᵐ p ∂(volume : Measure E),
      B.indicator (fun _ => (1 : ℝ≥0∞)) p ≤
        liminf (fun n => (A n).indicator (fun _ => (1 : ℝ≥0∞)) p) atTop := by
    filter_upwards [ae_eventually_mem_subgradientImageOn_of_locally_uniform hΩ hf hfc hv hvc
        hlim hG hGΩ] with
      p hp
    by_cases hpB : p ∈ B
    · have hm : ∀ᶠ n in atTop, (A n).indicator (fun _ => (1 : ℝ≥0∞)) p = 1 :=
        (hp hpB).mono (fun n hn => indicator_of_mem hn _)
      rw [indicator_of_mem hpB, liminf_congr hm, liminf_const]
    · rw [indicator_of_notMem hpB]
      exact bot_le
  calc
    (volume : Measure E) B = ∫⁻ p, B.indicator (fun _ => (1 : ℝ≥0∞)) p :=
      (lintegral_indicator_one hB).symm
    _ ≤ ∫⁻ p, liminf (fun n => (A n).indicator (fun _ => (1 : ℝ≥0∞)) p) atTop :=
      lintegral_mono_ae ha
    _ ≤ liminf (fun n => ∫⁻ p, (A n).indicator (fun _ => (1 : ℝ≥0∞)) p) atTop :=
      lintegral_liminf_le (fun n => measurable_const.indicator (hA n))
    _ = liminf (fun n => (volume : Measure E) (A n)) atTop := by
      congr 1
      funext n
      exact lintegral_indicator_one (hA n)

end FunctionalInequalities.Analysis

namespace FunctionalInequalities.Analysis
open Set Metric Filter
open scoped Topology
/-- Locally uniform C0 convex sources produce their actual SAME Monge--Ampere
measures, retaining every Borel supporting-image formula and interior compact
finiteness. Source-derived local Portmanteau inequalities yield convergence
on all continuity sets with compact closure INSIDE the domain. No measure or
stability property is an input; no ambient narrow convergence is asserted. -/
theorem exists_domain_mongeAmpere_measures_local_limits {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {f : ℕ → E → ℝ} {v : E → ℝ} {Ω : Set E} (hΩ : IsOpen Ω) (hf : ∀ n, ConvexOn ℝ Ω (f n))
    (hfc : ∀ n, ContinuousOn (f n) Ω) (hv : ConvexOn ℝ Ω v) (hvc : ContinuousOn v Ω)
    (hlim : TendstoLocallyUniformlyOn f v atTop Ω) :
    ∃ (μs : ℕ → Measure E) (μ : Measure E),
      (∀ n,
          ∀ G : Set E,
            MeasurableSet G →
              μs n G = (volume : Measure E) (subgradientImageOn (f n) Ω (G ∩ Ω))) ∧
        (∀ G : Set E,
            MeasurableSet G → μ G = (volume : Measure E) (subgradientImageOn v Ω (G ∩ Ω))) ∧
          (∀ n, ∀ K : Set E, IsCompact K → K ⊆ Ω → μs n K < ⊤) ∧
            (∀ K : Set E, IsCompact K → K ⊆ Ω → μ K < ⊤) ∧
              (∀ K : Set E, IsCompact K → K ⊆ Ω → limsup (fun n => μs n K) atTop ≤ μ K) ∧
                (∀ G : Set E, IsOpen G → G ⊆ Ω → μ G ≤ liminf (fun n => μs n G) atTop) ∧
                  (∀ A : Set E,
                    IsCompact (closure A) →
                      closure A ⊆ Ω →
                        μ (frontier A) = 0 → Tendsto (fun n => μs n A) atTop (𝓝 (μ A))) := by
  classical
  choose μs hμs hfin using fun n => exists_domain_mongeAmpere_measure hΩ (hf n) (hfc n)
  obtain ⟨μ, hμ, hμfin⟩ := exists_domain_mongeAmpere_measure hΩ hv hvc
  have hupper : ∀ K : Set E, IsCompact K → K ⊆ Ω → limsup (fun n => μs n K) atTop ≤ μ K := by
    intro K hK hKΩ
    have heq :
      (fun n => μs n K) = (fun n => (volume : Measure E) (subgradientImageOn (f n) Ω K)) := by
      funext n
      rw [hμs n K hK.measurableSet, inter_eq_left.mpr hKΩ]
    rw [heq, hμ K hK.measurableSet, inter_eq_left.mpr hKΩ]
    exact limsup_volume_subgradientImageOn_le_of_locally_uniform hΩ hv hvc hlim hK hKΩ
  have hlower : ∀ G : Set E, IsOpen G → G ⊆ Ω → μ G ≤ liminf (fun n => μs n G) atTop := by
    intro G hG hGΩ
    have heq :
      (fun n => μs n G) = (fun n => (volume : Measure E) (subgradientImageOn (f n) Ω G)) := by
      funext n
      rw [hμs n G hG.measurableSet, inter_eq_left.mpr hGΩ]
    rw [heq, hμ G hG.measurableSet, inter_eq_left.mpr hGΩ]
    exact volume_subgradientImageOn_le_liminf_of_locally_uniform hΩ hf hfc hv hvc hlim hG hGΩ
  refine ⟨μs, μ, hμs, hμ, hfin, hμfin, hupper, hlower, ?_⟩
  intro A hA hAΩ hboundary
  apply tendsto_measure_of_le_liminf_measure_of_limsup_measure_le interior_subset subset_closure
  · simpa only [frontier] using hboundary
  · exact hlower (interior A) isOpen_interior ((interior_subset.trans subset_closure).trans hAΩ)
  · exact hupper (closure A) hA hAΩ

open scoped NNReal

/-- An actual common constant open-set domain Monge–Ampère equation is preserved
under locally uniform convergence of continuous convex potentials. The coefficient
may be zero; neither the domain nor its open subsets need have finite volume.
The reverse inequality uses compact inner approximation and an actual open
thickening, so no equation on compact sets is assumed. -/
theorem domain_constant_density_of_locally_uniform {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {f : ℕ → E → ℝ} {v : E → ℝ} {Ω : Set E} (c : ℝ≥0) (hΩ : IsOpen Ω)
    (hf : ∀ n, ConvexOn ℝ Ω (f n)) (hfc : ∀ n, ContinuousOn (f n) Ω) (hv : ConvexOn ℝ Ω v)
    (hvc : ContinuousOn v Ω) (hlim : TendstoLocallyUniformlyOn f v atTop Ω)
    (hMA :
      ∀ n,
        ∀ G : Set E,
          IsOpen G →
            G ⊆ Ω →
              (volume : Measure E) (subgradientImageOn (f n) Ω G) = (c : ℝ≥0∞) * volume G) :
    ∀ G : Set E,
      IsOpen G →
        G ⊆ Ω → (volume : Measure E) (subgradientImageOn v Ω G) = (c : ℝ≥0∞) * volume G := by
  intro G hG hGΩ
  have hupper : (volume : Measure E) (subgradientImageOn v Ω G) ≤ (c : ℝ≥0∞) * volume G := by
    have h :=
      volume_subgradientImageOn_le_liminf_of_locally_uniform hΩ hf hfc hv hvc hlim hG hGΩ
    have heq :
      (fun n => (volume : Measure E) (subgradientImageOn (f n) Ω G)) =
        (fun _ : ℕ => (c : ℝ≥0∞) * volume G) := by
      funext n
      exact hMA n G hG hGΩ
    rw [heq, liminf_const] at h
    exact h
  apply le_antisymm hupper
  rw [hG.measure_eq_iSup_isCompact (volume : Measure E)]
  simp_rw [ENNReal.mul_iSup]
  refine iSup_le fun K => iSup_le fun hKG => iSup_le fun hK => ?_
  obtain ⟨δ, hδ, hLG⟩ := hK.exists_cthickening_subset_open hG hKG
  let L : Set E := cthickening δ K
  let T : Set E := thickening δ K
  have hL : IsCompact L := hK.cthickening
  have hTL : T ⊆ L := thickening_subset_cthickening δ K
  have hKT : K ⊆ T := self_subset_thickening hδ K
  have hLΩ : L ⊆ Ω := hLG.trans hGΩ
  have hTΩ : T ⊆ Ω := hTL.trans hLΩ
  have hbound :
    ∀ n : ℕ, (c : ℝ≥0∞) * volume K ≤ (volume : Measure E) (subgradientImageOn (f n) Ω L) := by
    intro n
    calc
      (c : ℝ≥0∞) * volume K ≤ (c : ℝ≥0∞) * volume T :=
        mul_le_mul le_rfl (measure_mono hKT) bot_le bot_le
      _ = (volume : Measure E) (subgradientImageOn (f n) Ω T) :=
        (hMA n T isOpen_thickening hTΩ).symm
      _ ≤ (volume : Measure E) (subgradientImageOn (f n) Ω L) :=
        measure_mono (subgradientImageOn_mono (f n) Ω hTL)
  have hsup :
    (c : ℝ≥0∞) * volume K ≤
      limsup (fun n => (volume : Measure E) (subgradientImageOn (f n) Ω L)) atTop := by
    have h := limsup_le_limsup (f := (atTop : Filter ℕ)) (Eventually.of_forall hbound)
    simpa only [limsup_const] using h
  exact
    hsup.trans
      ((limsup_volume_subgradientImageOn_le_of_locally_uniform hΩ hv hvc hlim hL hLΩ).trans
        (measure_mono (subgradientImageOn_mono v Ω hLG)))

/-- Actual open lower-MA source data give lower bounds on EVERY Borel subset,
using real local finite restrictions rather than an outer-regularity input. -/
theorem volume_le_subgradientImageOn_of_open_lower {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {Ω : Set E} {u : E → ℝ} (hΩ : IsOpen Ω) (hu : ConvexOn ℝ Ω u) (huc : ContinuousOn u Ω)
    (hMA : ∀ G : Set E, IsOpen G → G ⊆ Ω → volume G ≤ volume (subgradientImageOn u Ω G)) :
    ∀ G : Set E, MeasurableSet G → G ⊆ Ω → volume G ≤ volume (subgradientImageOn u Ω G) := by
  obtain ⟨μ, hμ, hfin⟩ := exists_domain_mongeAmpere_measure hΩ hu huc
  have hMAμ : ∀ G : Set E, IsOpen G → G ⊆ Ω → volume G ≤ μ G := by
    intro G hG hGΩ
    rw [hμ G hG.measurableSet, inter_eq_left.mpr hGΩ]
    exact hMA G hG hGΩ
  have hcompact : ∀ K : Set E, IsCompact K → K ⊆ Ω → volume K ≤ μ K := by
    intro K hK hKΩ
    obtain ⟨δ, hδ, hLΩ⟩ := hK.exists_cthickening_subset_open hΩ hKΩ
    let L := cthickening δ K
    let H := thickening δ K
    have hL : IsCompact L := hK.cthickening
    have hHL : H ⊆ L := thickening_subset_cthickening δ K
    have hHΩ : H ⊆ Ω := hHL.trans hLΩ
    have hKH : K ⊆ H := self_subset_thickening hδ K
    have hHfin : μ H < ⊤ := (measure_mono hHL).trans_lt (hfin L hL hLΩ)
    let : IsFiniteMeasure (μ.restrict H) := isFiniteMeasure_restrict.mpr hHfin.ne
    have hopen : ∀ U : Set E, IsOpen U → (volume.restrict H) U ≤ (μ.restrict H) U := by
      intro U hU
      rw [Measure.restrict_apply hU.measurableSet, Measure.restrict_apply hU.measurableSet]
      exact hMAμ (U ∩ H) (hU.inter isOpen_thickening) (inter_subset_right.trans hHΩ)
    have hall : ∀ B : Set E, (volume.restrict H) B ≤ (μ.restrict H) B := by
      intro B
      rw [B.measure_eq_iInf_isOpen (μ.restrict H)]
      exact
        le_iInf fun U =>
          le_iInf fun hBU => le_iInf fun hU => (measure_mono hBU).trans (hopen U hU)
    have hk := hall K
    simpa only [Measure.restrict_apply hK.measurableSet, inter_eq_left.mpr hKH] using hk
  intro G hG hGΩ
  have hbound : volume G ≤ μ G := by
    rw [hG.measure_eq_iSup_isCompact]
    refine iSup_le fun K => iSup_le fun hKG => iSup_le fun hK => ?_
    exact (hcompact K hK (hKG.trans hGΩ)).trans (measure_mono hKG)
  rwa [hμ G hG, inter_eq_left.mpr hGΩ] at hbound


end FunctionalInequalities.Analysis

namespace FunctionalInequalities.Analysis
open Set Metric Filter MeasureTheory
open scoped RealInnerProductSpace Topology

end FunctionalInequalities.Analysis
