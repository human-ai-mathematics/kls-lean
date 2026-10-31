module

public import FunctionalInequalities.Analysis.Convex.Alexandrov.ImageVolume
public import FunctionalInequalities.Analysis.Convex.CompactTilt

/-! # Domain supporting-image and optimizer transport

Identification bridges for a given local gradient map or a given domain
Monge--Ampere measure. They do not construct a measure or require a
locally uniform approximating sequence.
-/

@[expose] public section

noncomputable section
open MeasureTheory Set Metric Filter
open scoped RealInnerProductSpace ENNReal Topology
namespace FunctionalInequalities.Analysis

/-- Actual ordinary locally restricted gradient transport gives exact compact
MA mass. The existing Alexandrov pushforward identity GENERATES bad-fiber/null
control; there is no supplied exceptional set, injectivity or dual MA premise. -/
theorem volume_subgradientImage_eq_of_local_map {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {ψ : E → ℝ} {L : NNReal} (hL : LipschitzWith L ψ) (hcv : ConvexOn ℝ univ ψ)
    (hC1 : ContDiff ℝ 1 ψ) {P : E → E} (hg : ∀ p, gradient ψ p = P p) {T : Set E}
    (hmap : (volume.restrict (P ⁻¹' T)).map P = volume.restrict T) {S : Set E}
    (hS : IsCompact S) (hST : S ⊆ P ⁻¹' T) : volume (subgradientImage ψ S) = volume S := by
  have he : gradient ψ = P := funext hg
  have hmap' : (volume.restrict (P ⁻¹' T)).map (gradient ψ) = volume.restrict T := by
    simpa only [he] using hmap
  have h :=
    lintegral_subgradientImage_eq_of_map_gradient hL hcv
      (Measure.absolutelyContinuous_restrict : volume.restrict (P ⁻¹' T) ≪ (volume : Measure E))
      hmap' (Measure.absolutelyContinuous_restrict : volume.restrict T ≪ (volume : Measure E))
      hS (fun _ => (1 : ENNReal)) measurable_const
  have hm : (volume.restrict T) (subgradientImage ψ S) = (volume.restrict (P ⁻¹' T)) S := by
    simpa only [lintegral_one, Measure.restrict_apply_univ] using h
  have hi : subgradientImage ψ S ⊆ T := by
    rintro q ⟨x, hx, hq⟩
    have hqg := subgradient_eq_gradient (hC1.differentiable (by norm_num) x) hq
    rw [hqg, hg x]
    exact hST hx
  have hI : MeasurableSet (subgradientImage ψ S) :=
    (isClosed_subgradientImage_of_isCompact hL.continuous hS).measurableSet
  simpa only [Measure.restrict_apply hI, Measure.restrict_apply hS.measurableSet,
    inter_eq_self_of_subset_left hi, inter_eq_self_of_subset_left hST] using hm


end FunctionalInequalities.Analysis

namespace FunctionalInequalities.Analysis
open Set Metric Filter MeasureTheory
open scoped RealInnerProductSpace Topology

/-- Ordinary actual local gradient transport gives the true OPEN MA equation,
not a compact-closure substitution. Highest source below GENERATES all inputs. -/
theorem volume_subgradientImage_eq_of_local_map_on_open
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {ψ : E → ℝ} {L : NNReal} (hL : LipschitzWith L ψ)
    (hcv : ConvexOn ℝ univ ψ) (hC1 : ContDiff ℝ 1 ψ)
    {P : E → E} (hg : ∀ p, gradient ψ p = P p) {T : Set E}
    (hmap : (volume.restrict (P ⁻¹' T)).map P = volume.restrict T)
    {G : Set E} (hG : IsOpen G) (hGT : G ⊆ P ⁻¹' T) :
    volume (subgradientImage ψ G) = volume G := by
  exact subgradientImage_open_measure_of_compact_eq hG hGT
    (fun _ hS hST => volume_subgradientImage_eq_of_local_map hL hcv hC1 hg hmap hS hST)


end FunctionalInequalities.Analysis

namespace FunctionalInequalities.Analysis
open Set Metric Filter MeasureTheory
open scoped RealInnerProductSpace Topology

/-- Actual optimizer data and the SAME domain measure formula/identification
give exact image/capacity and restricted-volume transport. No source transport,
image agreement, C1, compactness, open domain, N or injectivity is required. -/
theorem optimizer_transport_of_domain_measure {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {u : E → ℝ} {Ω K : Set E} {μ : Measure E} (hu : ConvexOn ℝ Ω u) (hKΩ : K ⊆ Ω) (P : E → E)
    (hPC : Continuous P)
    (hopt :
      ∀ p,
        P p ∈ K ∧
          (∀ y ∈ K, u (P p) + ⟪p, y - P p⟫ ≤ u y) ∧
            ∀ x ∈ K, (∀ y ∈ K, u x + ⟪p, y - x⟫ ≤ u y) → x = P p)
    (hμ : ∀ G : Set E, MeasurableSet G → μ G = volume (subgradientImageOn u Ω (G ∩ Ω)))
    (hm : μ = volume.restrict Ω) :
    (∀ G : Set E, G ⊆ interior K → subgradientImageOn u Ω G = P ⁻¹' G) ∧
      (∀ G : Set E, MeasurableSet G → G ⊆ interior K → volume (P ⁻¹' G) = volume G) ∧
        (volume.restrict (P ⁻¹' interior K)).map P = volume.restrict (interior K) := by
  have hi (G : Set E) (hG : G ⊆ interior K) : subgradientImageOn u Ω G = P ⁻¹' G :=
    subgradientImageOn_eq_optimizer_preimage hu hKΩ P hopt hG
  have hmass (G : Set E) (hG : MeasurableSet G) (hGK : G ⊆ interior K) :
    volume (P ⁻¹' G) = volume G := by
    have hGO : G ⊆ Ω := hGK.trans (interior_subset.trans hKΩ)
    rw [← hi G hGK, ← inter_eq_self_of_subset_left hGO, ← hμ G hG, hm]
    rw [Measure.restrict_apply hG, inter_eq_self_of_subset_left hGO]
  have hmap : (volume.restrict (P ⁻¹' interior K)).map P = volume.restrict (interior K) := by
    apply Measure.ext
    intro A hA
    rw [Measure.map_apply hPC.measurable hA, Measure.restrict_apply (hPC.measurable hA), ←
      preimage_inter,
      hmass (A ∩ interior K) (hA.inter isOpen_interior.measurableSet) inter_subset_right,
      Measure.restrict_apply hA]
  exact ⟨hi, hmass, hmap⟩

end FunctionalInequalities.Analysis
