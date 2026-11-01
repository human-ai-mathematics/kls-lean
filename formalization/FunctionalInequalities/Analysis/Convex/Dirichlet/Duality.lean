module

public import FunctionalInequalities.Analysis.Convex.Alexandrov.DomainTransport
public import FunctionalInequalities.Analysis.Convex.Dirichlet.Solution
public import FunctionalInequalities.Analysis.Convex.CompactTilt
public import FunctionalInequalities.Analysis.Convex.Caffarelli.DomainContact

/-!
# Compact conjugates and dual measures of unit Dirichlet solutions

Supporting interfaces for Letwin arXiv:2607.24164v1 Lemma 2.2 through
Berman–Berndtsson arXiv:1207.6128v1 Theorem 2.24(ii). Each declaration retains
its own hypotheses and scope; this layout does not assert further regularity.
-/

@[expose] public section

section

open Set Metric Filter
open scoped RealInnerProductSpace Topology
open FunctionalInequalities.Probability.Stein

namespace FunctionalInequalities.Analysis.Dirichlet
open Set Metric Filter MeasureTheory
open scoped RealInnerProductSpace Topology

private lemma mem_interior_sublevel_of_lt {E : Type*} [TopologicalSpace E] {Ω : Set E}
    {u : E → ℝ} {r : ℝ} {x : E} (hΩ : IsOpen Ω) (hC : ContinuousOn u (closure Ω)) (hx : x ∈ Ω)
    (hxr : u x < r) : x ∈ interior {y ∈ closure Ω | u y ≤ r} := by
  have hxi : x ∈ Ω ∩ u ⁻¹' interior (Iic r) := by
    simpa only [interior_Iic, mem_inter_iff, mem_preimage, mem_Iio] using And.intro hx hxr
  have hpx := (hC.mono subset_closure).preimage_interior_subset_interior_preimage hΩ hxi
  change x ∈ interior (closure Ω ∩ u ⁻¹' Iic r)
  rw [interior_inter]
  exact ⟨hΩ.subset_interior_closure hx, hpx.2⟩

private lemma negative_sublevel_optimizer_data {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {Ω : Set E} (hΩ : IsOpen Ω)
    (hcΩ : Convex ℝ Ω) (hb : Bornology.IsBounded Ω) {u : E → ℝ} (hcv : ConvexOn ℝ (closure Ω) u)
    (hC : ContinuousOn u (closure Ω)) (hz : ∀ z ∈ frontier Ω, u z = 0) (hneg : ∀ x ∈ Ω, u x < 0)
    (hstrict : StrictConvexOn ℝ Ω u) {x₀ : E} (hx₀ : x₀ ∈ Ω) :
    ∃ (r : ℝ) (P : E → E),
      u x₀ < r ∧
        r < 0 ∧
          let K := {x ∈ closure Ω | u x ≤ r}
          IsCompact K ∧
            K.Nonempty ∧
              Convex ℝ K ∧
                K ⊆ Ω ∧
                  x₀ ∈ interior K ∧
                    Continuous P ∧
                      (∀ p,
                        P p ∈ K ∧
                          (∀ y ∈ K, u (P p) + ⟪p, y - P p⟫ ≤ u y) ∧
                            ∀ x ∈ K, (∀ y ∈ K, u x + ⟪p, y - x⟫ ≤ u y) → x = P p) := by
  have hxneg := hneg x₀ hx₀
  let r : ℝ := u x₀ / 2
  have hr : r < 0 := by dsimp [r]; linarith
  have hxr : u x₀ < r := by dsimp [r]; linarith
  obtain ⟨hK, hKn, hKΩ, _V, _L, _hV, _hL, _heq, _hweak, _hstrictV, _himage⟩ :=
    exists_negative_sublevel_patch hΩ hcΩ hb hcv hC hz hr hx₀ hxr
  have hcK := hcv.convex_le r
  obtain ⟨P, hPC, hopt⟩ :=
    exists_continuous_tilt_optimizer hK hKn (hstrict.subset hKΩ hcK) (hC.mono inter_subset_left)
  exact ⟨r, P, hxr, hr, hK, hKn, hcK, hKΩ, mem_interior_sublevel_of_lt hΩ hC hx₀ hxr, hPC, hopt⟩

/-- The actual UNIT source, a genuine interior vertex, and real strict
negative sublevels produce a continuous tilt optimizer without any source
potential, sublevel, optimizer or regularity premise. -/
theorem exists_unit_compact_tilt_optimizers {n : ℕ} (hn : 0 < n)
    {Ω : Set (EuclideanSpace ℝ (Fin n))} (hΩ : IsOpen Ω) (hcΩ : Convex ℝ Ω)
    (hb : Bornology.IsBounded Ω) {x₀ : EuclideanSpace ℝ (Fin n)} (hx₀ : x₀ ∈ Ω) :
    ∃ (U : EuclideanSpace ℝ (Fin n) → ℝ) (μ : Measure (EuclideanSpace ℝ (Fin n))) (r : ℝ) (P :
      EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
      U ∈ Dirichlet.subsolutions Ω ∧
        ConvexOn ℝ (closure Ω) U ∧
          ContinuousOn U (closure Ω) ∧
            (∀ z ∈ frontier Ω, U z = 0) ∧
              (∀ G : Set (EuclideanSpace ℝ (Fin n)),
                  MeasurableSet G → μ G = volume (subgradientImageOn U Ω (G ∩ Ω))) ∧
                (∀ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K → K ⊆ Ω → μ K < ⊤) ∧
                  μ = volume.restrict Ω ∧
                    (∀ G : Set (EuclideanSpace ℝ (Fin n)),
                        IsOpen G → G ⊆ Ω → volume (subgradientImageOn U Ω G) = volume G) ∧
                      (∀ x ∈ Ω, U x < 0) ∧
                        (∀ x ∈ Ω,
                            ∀ p : EuclideanSpace ℝ (Fin n),
                              (∀ z ∈ Ω, U x + ⟪p, z - x⟫ ≤ U z) →
                                ∀ y ∈ Ω, U y = U x + ⟪p, y - x⟫ → y = x) ∧
                          StrictConvexOn ℝ Ω U ∧
                            U x₀ < r ∧
                              r < 0 ∧
                                let K := {x ∈ closure Ω | U x ≤ r}
      IsCompact K ∧ K.Nonempty ∧ Convex ℝ K ∧ K ⊆ Ω ∧ Continuous P ∧
      (∀ p, P p ∈ K ∧ (∀ y ∈ K, U (P p) + ⟪p, y-P p⟫ ≤ U y) ∧
        ∀ x ∈ K, (∀ y ∈ K, U x + ⟪p, y-x⟫ ≤ U y) → x = P p) := by
    obtain ⟨U, μ, hU, hcv, hC, hz, hμ, hfin, hm, hMA, hneg, hcontact, hstrict⟩ :=
      Dirichlet.exists_strict_unit_solution hn hΩ hcΩ hb
    obtain ⟨r, P, hxr, hr, hK, hKn, hcK, hKΩ, _hxK, hPC, hopt⟩ :=
      negative_sublevel_optimizer_data hΩ hcΩ hb hcv hC hz hneg hstrict hx₀
    exact
      ⟨U, μ, r, P, hU, hcv, hC, hz, hμ, hfin, hm, hMA, hneg, hcontact, hstrict, hxr, hr,
        hK, hKn, hcK, hKΩ, hPC, hopt⟩


end FunctionalInequalities.Analysis.Dirichlet

namespace FunctionalInequalities.Analysis.Dirichlet
open Set Metric Filter MeasureTheory
open scoped RealInnerProductSpace Topology

/-- Actual domain-only UNIT data and an interior vertex generate a compact
conjugate C1 value at the SAME optimizer, retaining SAME primal/measure and
every prior field. C1 concerns the conjugate value, not the primal potential. -/
theorem exists_unit_compact_conjugate {n : ℕ} (hn : 0 < n) {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (hΩ : IsOpen Ω) (hcΩ : Convex ℝ Ω) (hb : Bornology.IsBounded Ω)
    {x₀ : EuclideanSpace ℝ (Fin n)} (hx₀ : x₀ ∈ Ω) :
    ∃ (U : EuclideanSpace ℝ (Fin n) → ℝ) (μ : Measure (EuclideanSpace ℝ (Fin n))) (r : ℝ) (P :
      EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
      U ∈ Dirichlet.subsolutions Ω ∧
        ConvexOn ℝ (closure Ω) U ∧
          ContinuousOn U (closure Ω) ∧
            (∀ z ∈ frontier Ω, U z = 0) ∧
              (∀ G : Set (EuclideanSpace ℝ (Fin n)),
                  MeasurableSet G → μ G = volume (subgradientImageOn U Ω (G ∩ Ω))) ∧
                (∀ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K → K ⊆ Ω → μ K < ⊤) ∧
                  μ = volume.restrict Ω ∧
                    (∀ G : Set (EuclideanSpace ℝ (Fin n)),
                        IsOpen G → G ⊆ Ω → volume (subgradientImageOn U Ω G) = volume G) ∧
                      (∀ x ∈ Ω, U x < 0) ∧
                        (∀ x ∈ Ω,
                            ∀ p : EuclideanSpace ℝ (Fin n),
                              (∀ z ∈ Ω, U x + ⟪p, z - x⟫ ≤ U z) →
                                ∀ y ∈ Ω, U y = U x + ⟪p, y - x⟫ → y = x) ∧
                          StrictConvexOn ℝ Ω U ∧
                            U x₀ < r ∧
                              r < 0 ∧
                                let K := {x ∈ closure Ω | U x ≤ r}
      IsCompact K ∧ K.Nonempty ∧ Convex ℝ K ∧ K ⊆ Ω ∧ Continuous P ∧
      (∀ p, P p ∈ K ∧ (∀ y ∈ K, U (P p) + ⟪p, y-P p⟫ ≤ U y) ∧
        ∀ x ∈ K, (∀ y ∈ K, U x + ⟪p, y-x⟫ ≤ U y) → x = P p) ∧
      ∃ (ψ : EuclideanSpace ℝ (Fin n) → ℝ) (L : NNReal),
        (∀ p, ψ p = sSup ((fun y => ⟪p, y⟫-U y) '' K)) ∧
        (∀ p, ψ p = ⟪p, P p⟫-U (P p)) ∧
        ConvexOn ℝ univ ψ ∧ LipschitzWith L ψ ∧ ContDiff ℝ 1 ψ ∧
        (∀ p, HasFDerivAt ψ (innerSL ℝ (P p)) p) := by
    obtain
      ⟨U, μ, r, P, hU, hcv, hC, hz, hμ, hfin, hm, hMA, hneg, hcontact, hstrict, hxr, hr,
        hK, hKn, hcK, hKΩ, hPC, hopt⟩ :=
      exists_unit_compact_tilt_optimizers hn hΩ hcΩ hb hx₀
    obtain ⟨ψ, L, hs, hv, hcvψ, hL, hC1, hd⟩ :=
      exists_value_of_optimizer hK P hPC (fun p => ⟨(hopt p).1, (hopt p).2.1⟩)
    exact
      ⟨U, μ, r, P, hU, hcv, hC, hz, hμ, hfin, hm, hMA, hneg, hcontact, hstrict, hxr, hr,
        hK, hKn, hcK, hKΩ, hPC, hopt, ψ, L, hs, hv, hcvψ, hL, hC1, hd⟩

end FunctionalInequalities.Analysis.Dirichlet

namespace FunctionalInequalities.Analysis.Dirichlet
open Set Metric Filter MeasureTheory
open scoped RealInnerProductSpace Topology

/-- Domain-only source GENERATES SAME U/mu/P/psi and actual inverse-image
capacity equality on every Borel subset of interior K. C1 is psi, NOT U;
no dual MA/transport/injectivity/regularity is supplied as input. -/
theorem exists_unit_conjugate_capacity {n : ℕ} (hn : 0 < n) {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (hΩ : IsOpen Ω) (hcΩ : Convex ℝ Ω) (hb : Bornology.IsBounded Ω)
    {x₀ : EuclideanSpace ℝ (Fin n)} (hx₀ : x₀ ∈ Ω) :
    ∃ (U : EuclideanSpace ℝ (Fin n) → ℝ) (μ : Measure (EuclideanSpace ℝ (Fin n))) (r : ℝ) (P :
      EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
      U ∈ Dirichlet.subsolutions Ω ∧
        ConvexOn ℝ (closure Ω) U ∧
          ContinuousOn U (closure Ω) ∧
            (∀ z ∈ frontier Ω, U z = 0) ∧
              (∀ G : Set (EuclideanSpace ℝ (Fin n)),
                  MeasurableSet G → μ G = volume (subgradientImageOn U Ω (G ∩ Ω))) ∧
                (∀ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K → K ⊆ Ω → μ K < ⊤) ∧
                  μ = volume.restrict Ω ∧
                    (∀ G : Set (EuclideanSpace ℝ (Fin n)),
                        IsOpen G → G ⊆ Ω → volume (subgradientImageOn U Ω G) = volume G) ∧
                      (∀ x ∈ Ω, U x < 0) ∧
                        (∀ x ∈ Ω,
                            ∀ p : EuclideanSpace ℝ (Fin n),
                              (∀ z ∈ Ω, U x + ⟪p, z - x⟫ ≤ U z) →
                                ∀ y ∈ Ω, U y = U x + ⟪p, y - x⟫ → y = x) ∧
                          StrictConvexOn ℝ Ω U ∧
                            U x₀ < r ∧
                              r < 0 ∧
                                let K := {x ∈ closure Ω | U x ≤ r}
      IsCompact K ∧ K.Nonempty ∧ Convex ℝ K ∧ K ⊆ Ω ∧ Continuous P ∧
      (∀ p, P p ∈ K ∧ (∀ y ∈ K, U (P p) + ⟪p, y-P p⟫ ≤ U y) ∧
        ∀ x ∈ K, (∀ y ∈ K, U x + ⟪p, y-x⟫ ≤ U y) → x = P p) ∧
      ∃ (ψ : EuclideanSpace ℝ (Fin n) → ℝ) (L : NNReal),
        (∀ p, ψ p = sSup ((fun y => ⟪p, y⟫-U y) '' K)) ∧
        (∀ p, ψ p = ⟪p, P p⟫-U (P p)) ∧
        ConvexOn ℝ univ ψ ∧ LipschitzWith L ψ ∧ ContDiff ℝ 1 ψ ∧
        (∀ p, HasFDerivAt ψ (innerSL ℝ (P p)) p) ∧
        (∀ p, gradient ψ p = P p) ∧
        (∀ G : Set (EuclideanSpace ℝ (Fin n)), G ⊆ interior K →
          subgradientImageOn U Ω G = P ⁻¹' G) ∧
        (∀ G : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet G → G ⊆ interior K →
          volume (P ⁻¹' G) = volume G) ∧
        (volume.restrict (P ⁻¹' interior K)).map P = volume.restrict (interior K) := by
    obtain
      ⟨U, μ, r, P, hU, hcv, hC, hz, hμ, hfin, hm, hMA, hneg, hcontact, hstrict, hxr, hr,
        hK, hKn, hcK, hKΩ, hPC, hopt, ψ, L, hs, hv, hcvψ, hL, hC1, hd⟩ :=
      Dirichlet.exists_unit_compact_conjugate hn hΩ hcΩ hb hx₀
    let K := {x ∈ closure Ω | U x ≤ r}
    obtain ⟨hi, hmass, hmap⟩ :=
      optimizer_transport_of_domain_measure (hcv.subset subset_closure hcΩ) hKΩ P hPC
        hopt hμ hm
    have hg (p) : gradient ψ p = P p :=
      (hasGradientAt_iff_hasFDerivAt.mpr (hd p)).gradient
    exact
      ⟨U, μ, r, P, hU, hcv, hC, hz, hμ, hfin, hm, hMA, hneg, hcontact, hstrict, hxr, hr,
        hK, hKn, hcK, hKΩ, hPC, hopt, ψ, L, hs, hv, hcvψ, hL, hC1, hd, hg, hi, hmass,
        hmap⟩


end FunctionalInequalities.Analysis.Dirichlet

namespace FunctionalInequalities.Analysis.Dirichlet
open Set Metric Filter MeasureTheory
open scoped RealInnerProductSpace Topology

/-- Domain geometry alone generates SAME U/mu/P/psi and actual compact dual
mass on the generated open slope region. No transport/dual MA is source input. -/
theorem exists_unit_compact_dual_mass {n : ℕ} (hn : 0 < n) {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (hΩ : IsOpen Ω) (hcΩ : Convex ℝ Ω) (hb : Bornology.IsBounded Ω)
    {x₀ : EuclideanSpace ℝ (Fin n)} (hx₀ : x₀ ∈ Ω) :
    ∃ (U : EuclideanSpace ℝ (Fin n) → ℝ) (μ : Measure (EuclideanSpace ℝ (Fin n))) (r : ℝ) (P :
      EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
      U ∈ Dirichlet.subsolutions Ω ∧
        ConvexOn ℝ (closure Ω) U ∧
          ContinuousOn U (closure Ω) ∧
            (∀ z ∈ frontier Ω, U z = 0) ∧
              (∀ G : Set (EuclideanSpace ℝ (Fin n)),
                  MeasurableSet G → μ G = volume (subgradientImageOn U Ω (G ∩ Ω))) ∧
                (∀ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K → K ⊆ Ω → μ K < ⊤) ∧
                  μ = volume.restrict Ω ∧
                    (∀ G : Set (EuclideanSpace ℝ (Fin n)),
                        IsOpen G → G ⊆ Ω → volume (subgradientImageOn U Ω G) = volume G) ∧
                      (∀ x ∈ Ω, U x < 0) ∧
                        (∀ x ∈ Ω,
                            ∀ p : EuclideanSpace ℝ (Fin n),
                              (∀ z ∈ Ω, U x + ⟪p, z - x⟫ ≤ U z) →
                                ∀ y ∈ Ω, U y = U x + ⟪p, y - x⟫ → y = x) ∧
                          StrictConvexOn ℝ Ω U ∧
                            U x₀ < r ∧
                              r < 0 ∧
                                let K := {x ∈ closure Ω | U x ≤ r}
      IsCompact K ∧ K.Nonempty ∧ Convex ℝ K ∧ K ⊆ Ω ∧ Continuous P ∧
      (∀ p, P p ∈ K ∧ (∀ y ∈ K, U (P p) + ⟪p, y-P p⟫ ≤ U y) ∧
        ∀ x ∈ K, (∀ y ∈ K, U x + ⟪p, y-x⟫ ≤ U y) → x = P p) ∧
      ∃ (ψ : EuclideanSpace ℝ (Fin n) → ℝ) (L : NNReal),
        (∀ p, ψ p = sSup ((fun y => ⟪p, y⟫-U y) '' K)) ∧
        (∀ p, ψ p = ⟪p, P p⟫-U (P p)) ∧
        ConvexOn ℝ univ ψ ∧ LipschitzWith L ψ ∧ ContDiff ℝ 1 ψ ∧
        (∀ p, HasFDerivAt ψ (innerSL ℝ (P p)) p) ∧
        (∀ p, gradient ψ p = P p) ∧
        (∀ G : Set (EuclideanSpace ℝ (Fin n)), G ⊆ interior K →
          subgradientImageOn U Ω G = P ⁻¹' G) ∧
        (∀ G : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet G → G ⊆ interior K →
          volume (P ⁻¹' G) = volume G) ∧
        (volume.restrict (P ⁻¹' interior K)).map P = volume.restrict (interior K) ∧
        (∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S → S ⊆ P ⁻¹' interior K →
          volume (subgradientImage ψ S) = volume S) := by
    obtain
      ⟨U, μ, r, P, hU, hcv, hC, hz, hμ, hfin, hm, hMA, hneg, hcontact, hstrict, hxr, hr,
        hK, hKn, hcK, hKΩ, hPC, hopt, ψ, L, hs, hv, hcvψ, hL, hC1, hd, hg, hi, hmass,
        hmap⟩ :=
      Dirichlet.exists_unit_conjugate_capacity hn hΩ hcΩ hb hx₀
    have hdual (S : Set (EuclideanSpace ℝ (Fin n))) (hS : IsCompact S)
      (hSD : S ⊆ P ⁻¹' interior {x ∈ closure Ω | U x ≤ r}) :
      volume (subgradientImage ψ S) = volume S :=
      volume_subgradientImage_eq_of_local_map hL hcvψ hC1 hg hmap hS hSD
    exact
      ⟨U, μ, r, P, hU, hcv, hC, hz, hμ, hfin, hm, hMA, hneg, hcontact, hstrict, hxr, hr,
        hK, hKn, hcK, hKΩ, hPC, hopt, ψ, L, hs, hv, hcvψ, hL, hC1, hd, hg, hi, hmass,
        hmap, hdual⟩


end FunctionalInequalities.Analysis.Dirichlet

namespace FunctionalInequalities.Analysis.Dirichlet
open Set Metric Filter MeasureTheory
open scoped RealInnerProductSpace Topology

/-- Domain geometry only GENERATES SAME U/mu/P/psi and actual OPEN dual MA,
retaining every old compact/capacity field and generated open NONEMPTY region. -/
theorem exists_unit_open_dual_mass {n : ℕ} (hn : 0 < n) {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (hΩ : IsOpen Ω) (hcΩ : Convex ℝ Ω) (hb : Bornology.IsBounded Ω)
    {x₀ : EuclideanSpace ℝ (Fin n)} (hx₀ : x₀ ∈ Ω) :
    ∃ (U : EuclideanSpace ℝ (Fin n) → ℝ) (μ : Measure (EuclideanSpace ℝ (Fin n))) (r : ℝ) (P :
      EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
      U ∈ Dirichlet.subsolutions Ω ∧
        ConvexOn ℝ (closure Ω) U ∧
          ContinuousOn U (closure Ω) ∧
            (∀ z ∈ frontier Ω, U z = 0) ∧
              (∀ G : Set (EuclideanSpace ℝ (Fin n)),
                  MeasurableSet G → μ G = volume (subgradientImageOn U Ω (G ∩ Ω))) ∧
                (∀ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K → K ⊆ Ω → μ K < ⊤) ∧
                  μ = volume.restrict Ω ∧
                    (∀ G : Set (EuclideanSpace ℝ (Fin n)),
                        IsOpen G → G ⊆ Ω → volume (subgradientImageOn U Ω G) = volume G) ∧
                      (∀ x ∈ Ω, U x < 0) ∧
                        (∀ x ∈ Ω,
                            ∀ p : EuclideanSpace ℝ (Fin n),
                              (∀ z ∈ Ω, U x + ⟪p, z - x⟫ ≤ U z) →
                                ∀ y ∈ Ω, U y = U x + ⟪p, y - x⟫ → y = x) ∧
                          StrictConvexOn ℝ Ω U ∧
                            U x₀ < r ∧
                              r < 0 ∧
                                let K := {x ∈ closure Ω | U x ≤ r}
      IsCompact K ∧ K.Nonempty ∧ Convex ℝ K ∧ K ⊆ Ω ∧ Continuous P ∧
      (∀ p, P p ∈ K ∧ (∀ y ∈ K, U (P p) + ⟪p, y-P p⟫ ≤ U y) ∧
        ∀ x ∈ K, (∀ y ∈ K, U x + ⟪p, y-x⟫ ≤ U y) → x = P p) ∧
      ∃ (ψ : EuclideanSpace ℝ (Fin n) → ℝ) (L : NNReal),
        (∀ p, ψ p = sSup ((fun y => ⟪p, y⟫-U y) '' K)) ∧
        (∀ p, ψ p = ⟪p, P p⟫-U (P p)) ∧
        ConvexOn ℝ univ ψ ∧ LipschitzWith L ψ ∧ ContDiff ℝ 1 ψ ∧
        (∀ p, HasFDerivAt ψ (innerSL ℝ (P p)) p) ∧
        (∀ p, gradient ψ p = P p) ∧
        (∀ G : Set (EuclideanSpace ℝ (Fin n)), G ⊆ interior K →
          subgradientImageOn U Ω G = P ⁻¹' G) ∧
        (∀ G : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet G → G ⊆ interior K →
          volume (P ⁻¹' G) = volume G) ∧
        (volume.restrict (P ⁻¹' interior K)).map P = volume.restrict (interior K) ∧
        (∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S → S ⊆ P ⁻¹' interior K →
          volume (subgradientImage ψ S) = volume S) ∧
        IsOpen (P ⁻¹' interior K) ∧ (P ⁻¹' interior K).Nonempty ∧
        (∀ G : Set (EuclideanSpace ℝ (Fin n)), IsOpen G → G ⊆ P ⁻¹' interior K →
          volume (subgradientImage ψ G) = volume G) := by
    obtain
      ⟨U, μ, r, P, hU, hcv, hC, hz, hμ, hfin, hm, hMA, hneg, hcontact, hstrict, hxr, hr,
        hK, hKn, hcK, hKΩ, hPC, hopt, ψ, L, hs, hv, hcvψ, hL, hC1, hd, hg, hi, hmass,
        hmap, hdual⟩ :=
      Dirichlet.exists_unit_compact_dual_mass hn hΩ hcΩ hb hx₀
    let K := {x ∈ closure Ω | U x ≤ r}
    have hxK : x₀ ∈ interior K := mem_interior_sublevel_of_lt hΩ hC hx₀ hxr
    obtain ⟨R, _hR, hex, _hbound⟩ :=
      exists_uniform_subgradient_bound_on_compact hΩ (hcv.subset subset_closure hcΩ)
        (hC.mono subset_closure) (isCompact_singleton (x := x₀))
        (singleton_subset_iff.mpr hx₀)
    obtain ⟨p, hp⟩ := hex x₀ (mem_singleton x₀)
    have hpI : p ∈ subgradientImageOn U Ω { x₀ } := ⟨x₀, mem_singleton x₀, hp⟩
    have hp0 : P p = x₀ := by
      have h := (hi { x₀ } (singleton_subset_iff.mpr hxK)).subset hpI
      simpa only [mem_preimage, mem_singleton_iff] using h
    have hDn : (P ⁻¹' interior K).Nonempty :=
      ⟨p, by change P p ∈ interior K; simpa only [hp0] using hxK⟩
    have hopen (G : Set (EuclideanSpace ℝ (Fin n))) (hG : IsOpen G)
      (hGD : G ⊆ P ⁻¹' interior K) : volume (subgradientImage ψ G) = volume G :=
      volume_subgradientImage_eq_of_local_map_on_open hL hcvψ hC1 hg hmap hG hGD
    exact
      ⟨U, μ, r, P, hU, hcv, hC, hz, hμ, hfin, hm, hMA, hneg, hcontact, hstrict, hxr, hr,
        hK, hKn, hcK, hKΩ, hPC, hopt, ψ, L, hs, hv, hcvψ, hL, hC1, hd, hg, hi, hmass,
        hmap, hdual, isOpen_interior.preimage hPC, hDn, hopen⟩


end FunctionalInequalities.Analysis.Dirichlet

namespace FunctionalInequalities.Analysis.Dirichlet
open Set Metric Filter MeasureTheory
open scoped RealInnerProductSpace Topology

/-- Domain geometry alone generates SAME actual U/mu/P/psi and all compact
value tilts are quantitatively coercive/proper. Not primal regularity/containment. -/
theorem exists_unit_coercive_dual {n : ℕ} (hn : 0 < n) {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (hΩ : IsOpen Ω) (hcΩ : Convex ℝ Ω) (hb : Bornology.IsBounded Ω)
    {x₀ : EuclideanSpace ℝ (Fin n)} (hx₀ : x₀ ∈ Ω) :
    ∃ (U : EuclideanSpace ℝ (Fin n) → ℝ) (μ : Measure (EuclideanSpace ℝ (Fin n))) (r : ℝ) (P :
      EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
      U ∈ Dirichlet.subsolutions Ω ∧
        ConvexOn ℝ (closure Ω) U ∧
          ContinuousOn U (closure Ω) ∧
            (∀ z ∈ frontier Ω, U z = 0) ∧
              (∀ G : Set (EuclideanSpace ℝ (Fin n)),
                  MeasurableSet G → μ G = volume (subgradientImageOn U Ω (G ∩ Ω))) ∧
                (∀ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K → K ⊆ Ω → μ K < ⊤) ∧
                  μ = volume.restrict Ω ∧
                    (∀ G : Set (EuclideanSpace ℝ (Fin n)),
                        IsOpen G → G ⊆ Ω → volume (subgradientImageOn U Ω G) = volume G) ∧
                      (∀ x ∈ Ω, U x < 0) ∧
                        (∀ x ∈ Ω,
                            ∀ p : EuclideanSpace ℝ (Fin n),
                              (∀ z ∈ Ω, U x + ⟪p, z - x⟫ ≤ U z) →
                                ∀ y ∈ Ω, U y = U x + ⟪p, y - x⟫ → y = x) ∧
                          StrictConvexOn ℝ Ω U ∧
                            U x₀ < r ∧
                              r < 0 ∧
                                let K := {x ∈ closure Ω | U x ≤ r}
      IsCompact K ∧ K.Nonempty ∧ Convex ℝ K ∧ K ⊆ Ω ∧ Continuous P ∧
      (∀ p, P p ∈ K ∧ (∀ y ∈ K, U (P p) + ⟪p, y-P p⟫ ≤ U y) ∧
        ∀ x ∈ K, (∀ y ∈ K, U x + ⟪p, y-x⟫ ≤ U y) → x = P p) ∧
      ∃ (ψ : EuclideanSpace ℝ (Fin n) → ℝ) (L : NNReal),
        (∀ p, ψ p = sSup ((fun y => ⟪p, y⟫-U y) '' K)) ∧
        (∀ p, ψ p = ⟪p, P p⟫-U (P p)) ∧
        ConvexOn ℝ univ ψ ∧ LipschitzWith L ψ ∧ ContDiff ℝ 1 ψ ∧
        (∀ p, HasFDerivAt ψ (innerSL ℝ (P p)) p) ∧
        (∀ p, gradient ψ p = P p) ∧
        (∀ G : Set (EuclideanSpace ℝ (Fin n)), G ⊆ interior K →
          subgradientImageOn U Ω G = P ⁻¹' G) ∧
        (∀ G : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet G → G ⊆ interior K →
          volume (P ⁻¹' G) = volume G) ∧
        (volume.restrict (P ⁻¹' interior K)).map P = volume.restrict (interior K) ∧
        (∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S → S ⊆ P ⁻¹' interior K →
          volume (subgradientImage ψ S) = volume S) ∧
        IsOpen (P ⁻¹' interior K) ∧ (P ⁻¹' interior K).Nonempty ∧
        (∀ G : Set (EuclideanSpace ℝ (Fin n)), IsOpen G → G ⊆ P ⁻¹' interior K →
          volume (subgradientImage ψ G) = volume G) ∧
        (∀ x ∈ interior K, ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧
          (∀ p, δ * ‖p‖ - C ≤ ψ p - ⟪p, x⟫) ∧
          ∀ R : ℝ, IsCompact {p | ψ p - ⟪p, x⟫ ≤ R}) := by
    obtain
      ⟨U, μ, r, P, hU, hcv, hC, hz, hμ, hfin, hm, hMA, hneg, hcontact, hstrict, hxr, hr,
        hK, hKn, hcK, hKΩ, hPC, hopt, ψ, L, hs, hv, hcvψ, hL, hC1, hd, hg, hi, hmass,
        hmap, hdual, hDo, hDn, hopen⟩ :=
      Dirichlet.exists_unit_open_dual_mass hn hΩ hcΩ hb hx₀
    have hproper (x : EuclideanSpace ℝ (Fin n))
      (hx : x ∈ interior {x ∈ closure Ω | U x ≤ r}) :
      ∃ δ C : ℝ,
        0 < δ ∧
          0 < C ∧
            (∀ p, δ * ‖p‖ - C ≤ ψ p - ⟪p, x⟫) ∧
              ∀ R : ℝ, IsCompact {p | ψ p - ⟪p, x⟫ ≤ R} :=
      exists_compact_tilt_sublevels hK (hC.mono inter_subset_left) hC1.continuous hs hx
    exact
      ⟨U, μ, r, P, hU, hcv, hC, hz, hμ, hfin, hm, hMA, hneg, hcontact, hstrict, hxr, hr,
        hK, hKn, hcK, hKΩ, hPC, hopt, ψ, L, hs, hv, hcvψ, hL, hC1, hd, hg, hi, hmass,
        hmap, hdual, hDo, hDn, hopen, hproper⟩


end FunctionalInequalities.Analysis.Dirichlet

namespace FunctionalInequalities.Analysis.Dirichlet
open Set Metric Filter MeasureTheory
open scoped RealInnerProductSpace Topology

/-- Actual generated full-section source; no primal regularity claim. -/
theorem exists_unit_contained_dual_sections {n : ℕ} (hn : 0 < n)
    {Ω : Set (EuclideanSpace ℝ (Fin n))} (hΩ : IsOpen Ω) (hcΩ : Convex ℝ Ω)
    (hb : Bornology.IsBounded Ω) {x₀ : EuclideanSpace ℝ (Fin n)} (hx₀ : x₀ ∈ Ω) :
    ∃ (U : EuclideanSpace ℝ (Fin n) → ℝ) (μ : Measure (EuclideanSpace ℝ (Fin n))) (r : ℝ) (P :
      EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
      U ∈ Dirichlet.subsolutions Ω ∧
        ConvexOn ℝ (closure Ω) U ∧
          ContinuousOn U (closure Ω) ∧
            (∀ z ∈ frontier Ω, U z = 0) ∧
              (∀ G : Set (EuclideanSpace ℝ (Fin n)),
                  MeasurableSet G → μ G = volume (subgradientImageOn U Ω (G ∩ Ω))) ∧
                (∀ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K → K ⊆ Ω → μ K < ⊤) ∧
                  μ = volume.restrict Ω ∧
                    (∀ G : Set (EuclideanSpace ℝ (Fin n)),
                        IsOpen G → G ⊆ Ω → volume (subgradientImageOn U Ω G) = volume G) ∧
                      (∀ x ∈ Ω, U x < 0) ∧
                        (∀ x ∈ Ω,
                            ∀ p : EuclideanSpace ℝ (Fin n),
                              (∀ z ∈ Ω, U x + ⟪p, z - x⟫ ≤ U z) →
                                ∀ y ∈ Ω, U y = U x + ⟪p, y - x⟫ → y = x) ∧
                          StrictConvexOn ℝ Ω U ∧
                            U x₀ < r ∧
                              r < 0 ∧
                                let K := {x ∈ closure Ω | U x ≤ r}
      IsCompact K ∧ K.Nonempty ∧ Convex ℝ K ∧ K ⊆ Ω ∧ Continuous P ∧
      (∀ p, P p ∈ K ∧ (∀ y ∈ K, U (P p) + ⟪p, y-P p⟫ ≤ U y) ∧
        ∀ x ∈ K, (∀ y ∈ K, U x + ⟪p, y-x⟫ ≤ U y) → x = P p) ∧
      ∃ (ψ : EuclideanSpace ℝ (Fin n) → ℝ) (L : NNReal),
        (∀ p, ψ p = sSup ((fun y => ⟪p, y⟫-U y) '' K)) ∧
        (∀ p, ψ p = ⟪p, P p⟫-U (P p)) ∧
        ConvexOn ℝ univ ψ ∧ LipschitzWith L ψ ∧ ContDiff ℝ 1 ψ ∧
        (∀ p, HasFDerivAt ψ (innerSL ℝ (P p)) p) ∧
        (∀ p, gradient ψ p = P p) ∧
        (∀ G : Set (EuclideanSpace ℝ (Fin n)), G ⊆ interior K →
          subgradientImageOn U Ω G = P ⁻¹' G) ∧
        (∀ G : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet G → G ⊆ interior K →
          volume (P ⁻¹' G) = volume G) ∧
        (volume.restrict (P ⁻¹' interior K)).map P = volume.restrict (interior K) ∧
        (∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S → S ⊆ P ⁻¹' interior K →
          volume (subgradientImage ψ S) = volume S) ∧
        IsOpen (P ⁻¹' interior K) ∧ (P ⁻¹' interior K).Nonempty ∧
        (∀ G : Set (EuclideanSpace ℝ (Fin n)), IsOpen G → G ⊆ P ⁻¹' interior K →
          volume (subgradientImage ψ G) = volume G) ∧
        (∀ x ∈ interior K, ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧
          (∀ p, δ * ‖p‖ - C ≤ ψ p - ⟪p, x⟫) ∧
          ∀ R : ℝ, IsCompact {p | ψ p - ⟪p, x⟫ ≤ R}) ∧
        (∀ x ∈ interior K, ∃ (p₀ : EuclideanSpace ℝ (Fin n)) (R : ℝ),
          P p₀=x ∧ ψ p₀-⟪p₀, x⟫ = -U x ∧ -U x < R ∧
          IsCompact {p | ψ p-⟪p, x⟫ ≤ R} ∧
          {p | ψ p-⟪p, x⟫ ≤ R} ⊆ P ⁻¹' interior K) ∧
        (∀ x ∈ interior K, ∀ p q : EuclideanSpace ℝ (Fin n),
          (∀ y ∈ Ω, U x+⟪p, y-x⟫ ≤ U y) →
          (∀ y ∈ Ω, U x+⟪q, y-x⟫ ≤ U y) → p=q) := by
    obtain
      ⟨U, μ, r, P, hU, hcv, hC, hz, hμ, hfin, hm, hMA, hneg, hcontact, hstrict, hxr, hr,
        hK, hKn, hcK, hKΩ, hPC, hopt, ψ, L, hs, hv, hcvψ, hL, hC1, hd, hg, hi, hmass,
        hmap, hdual, hDo, hDn, hopen, hproper⟩ :=
      Dirichlet.exists_unit_coercive_dual hn hΩ hcΩ hb hx₀
    have hsections (x : EuclideanSpace ℝ (Fin n))
      (hx : x ∈ interior {x ∈ closure Ω | U x ≤ r}) :=
      exists_contained_section_unique_supports hΩ (hcv.subset subset_closure hcΩ)
        (hC.mono subset_closure) hK hKΩ P hPC hopt hC1.continuous hcvψ hs hv hopen hx
    have hcontained (x : EuclideanSpace ℝ (Fin n))
      (hx : x ∈ interior {x ∈ closure Ω | U x ≤ r}) :
      ∃ (p₀ : EuclideanSpace ℝ (Fin n)) (R : ℝ),
        P p₀ = x ∧
          ψ p₀ - ⟪p₀, x⟫ = -U x ∧
            -U x < R ∧
              IsCompact {p | ψ p - ⟪p, x⟫ ≤ R} ∧
                {p | ψ p - ⟪p, x⟫ ≤ R} ⊆ P ⁻¹' interior {x ∈ closure Ω | U x ≤ r} := by
      obtain ⟨p₀, R, hP₀, hvalue, hR, hcomp, hsection, _huniq⟩ := hsections x hx
      exact ⟨p₀, R, hP₀, hvalue, hR, hcomp, hsection⟩
    have hslopes (x : EuclideanSpace ℝ (Fin n))
      (hx : x ∈ interior {x ∈ closure Ω | U x ≤ r}) (p q : EuclideanSpace ℝ (Fin n))
      (hp : ∀ y ∈ Ω, U x + ⟪p, y - x⟫ ≤ U y) (hq : ∀ y ∈ Ω, U x + ⟪q, y - x⟫ ≤ U y) :
      p = q := by
      obtain ⟨_p₀, _R, _hP₀, _hvalue, _hR, _hcomp, _hsection, huniq⟩ := hsections x hx
      exact huniq p q hp hq
    exact
      ⟨U, μ, r, P, hU, hcv, hC, hz, hμ, hfin, hm, hMA, hneg, hcontact, hstrict, hxr, hr,
        hK, hKn, hcK, hKΩ, hPC, hopt, ψ, L, hs, hv, hcvψ, hL, hC1, hd, hg, hi, hmass,
        hmap, hdual, hDo, hDn, hopen, hproper, hcontained, hslopes⟩

end FunctionalInequalities.Analysis.Dirichlet

namespace FunctionalInequalities.Analysis.Dirichlet
open Set Metric Filter MeasureTheory
open scoped RealInnerProductSpace Topology

/-- GIVEN actual strict negative C0 UNIT data produce a unique domain support
at an arbitrary vertex for THIS SAME u/mu. No primal differentiability input.
Shared actual negative-sublevel/optimizer and Borel-capacity/map producers
serve both the older vertex source and this fixed-u construction. -/
theorem exists_unique_support_of_unit_data {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {Ω : Set E} (hΩ : IsOpen Ω) (hcΩ : Convex ℝ Ω) (hb : Bornology.IsBounded Ω) {u : E → ℝ}
    {μ : Measure E} (hcv : ConvexOn ℝ (closure Ω) u) (hC : ContinuousOn u (closure Ω))
    (hz : ∀ z ∈ frontier Ω, u z = 0) (hneg : ∀ x ∈ Ω, u x < 0) (hstrict : StrictConvexOn ℝ Ω u)
    (hμ : ∀ G : Set E, MeasurableSet G → μ G = volume (subgradientImageOn u Ω (G ∩ Ω)))
    (hm : μ = volume.restrict Ω) {x₀ : E} (hx₀ : x₀ ∈ Ω) :
    ∃ p : E,
      (∀ y ∈ Ω, u x₀ + ⟪p, y - x₀⟫ ≤ u y) ∧
        ∀ q : E, (∀ y ∈ Ω, u x₀ + ⟪q, y - x₀⟫ ≤ u y) → q = p := by
  obtain ⟨r, P, _hxr, _hr, hK, _hKn, _hcK, hKΩ, hxK, hPC, hopt⟩ :=
    negative_sublevel_optimizer_data hΩ hcΩ hb hcv hC hz hneg hstrict hx₀
  let K := {x ∈ closure Ω | u x ≤ r}
  obtain ⟨ψ, L, hs, hv, hcvψ, hL, hC1, hd⟩ :=
    exists_value_of_optimizer hK P hPC (fun p => ⟨(hopt p).1, (hopt p).2.1⟩)
  obtain ⟨hi, _hmass, hmap⟩ :=
    optimizer_transport_of_domain_measure (hcv.subset subset_closure hcΩ) hKΩ P hPC hopt hμ hm
  have hg (p : E) : gradient ψ p = P p := (hasGradientAt_iff_hasFDerivAt.mpr (hd p)).gradient
  have hopen (G : Set E) (hG : IsOpen G) (hGD : G ⊆ P ⁻¹' interior K) :
    volume (subgradientImage ψ G) = volume G :=
    volume_subgradientImage_eq_of_local_map_on_open hL hcvψ hC1 hg hmap hG hGD
  obtain ⟨p₀, _R, hP₀, _hvalue, _hR, _hcomp, _hsection, huniq⟩ :=
    exists_contained_section_unique_supports hΩ (hcv.subset subset_closure hcΩ)
      (hC.mono subset_closure) hK hKΩ P hPC hopt hC1.continuous hcvψ hs hv hopen hxK
  have hpim : p₀ ∈ subgradientImageOn u Ω { x₀ } := by
    rw [hi { x₀ } (singleton_subset_iff.mpr hxK)]
    simp only [mem_preimage, mem_singleton_iff, hP₀]
  obtain ⟨y, hy, hp₀⟩ := hpim
  have hyx : y = x₀ := mem_singleton_iff.mp hy
  subst y
  exact ⟨p₀, hp₀, fun q hq => huniq q p₀ hq hp₀⟩

/-- Domain geometry ONLY chooses strict UNIT u/mu ONCE, then the GIVEN-u
factory works at EVERY domain point. Correct exists-u-forall-x quantifiers.
All actual base fields retained; no derivative/C1/C2/PD conclusion. -/
theorem exists_unit_unique_supports {n : ℕ} (hn : 0 < n) {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (hΩ : IsOpen Ω) (hcΩ : Convex ℝ Ω) (hb : Bornology.IsBounded Ω) :
    ∃ (U : EuclideanSpace ℝ (Fin n) → ℝ) (μ : Measure (EuclideanSpace ℝ (Fin n))),
      U ∈ Dirichlet.subsolutions Ω ∧
        ConvexOn ℝ (closure Ω) U ∧
          ContinuousOn U (closure Ω) ∧
            (∀ z ∈ frontier Ω, U z = 0) ∧
              (∀ G : Set (EuclideanSpace ℝ (Fin n)),
                  MeasurableSet G → μ G = volume (subgradientImageOn U Ω (G ∩ Ω))) ∧
                (∀ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K → K ⊆ Ω → μ K < ⊤) ∧
                  μ = volume.restrict Ω ∧
                    (∀ G : Set (EuclideanSpace ℝ (Fin n)),
                        IsOpen G → G ⊆ Ω → volume (subgradientImageOn U Ω G) = volume G) ∧
                      (∀ x ∈ Ω, U x < 0) ∧
                        (∀ x ∈ Ω,
                            ∀ p : EuclideanSpace ℝ (Fin n),
                              (∀ z ∈ Ω, U x + ⟪p, z - x⟫ ≤ U z) →
                                ∀ y ∈ Ω, U y = U x + ⟪p, y - x⟫ → y = x) ∧
                          StrictConvexOn ℝ Ω U ∧
                            ∀ x ∈ Ω,
                              ∃ p : EuclideanSpace ℝ (Fin n),
                                (∀ y ∈ Ω, U x + ⟪p, y - x⟫ ≤ U y) ∧
                                  ∀ q : EuclideanSpace ℝ (Fin n),
                                    (∀ y ∈ Ω, U x + ⟪q, y - x⟫ ≤ U y) → q = p := by
  obtain ⟨U, μ, hU, hcv, hC, hz, hμ, hfin, hm, hMA, hneg, hcontact, hstrict⟩ :=
    Dirichlet.exists_strict_unit_solution hn hΩ hcΩ hb
  have hs (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ Ω) :=
    exists_unique_support_of_unit_data hΩ hcΩ hb hcv hC hz hneg hstrict hμ hm hx
  exact ⟨U, μ, hU, hcv, hC, hz, hμ, hfin, hm, hMA, hneg, hcontact, hstrict, hs⟩

end FunctionalInequalities.Analysis.Dirichlet
