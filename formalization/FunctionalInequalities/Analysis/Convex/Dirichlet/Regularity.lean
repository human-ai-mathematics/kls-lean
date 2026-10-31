module

public import FunctionalInequalities.Analysis.Convex.Dirichlet.Duality
public import FunctionalInequalities.Analysis.Convex.Subgradient.Basic
public import FunctionalInequalities.Analysis.Convex.Subgradient.Regularity

/-!
# Unique supporting slopes and interior C¹ of unit Dirichlet solutions

Supporting interfaces for Letwin arXiv:2607.24164v1 Lemma 2.2 through
Berman–Berndtsson arXiv:1207.6128v1 Theorem 2.24(ii). Each declaration retains
its own hypotheses and scope; this layout does not assert further regularity.
-/

@[expose] public section

noncomputable section

open Set Metric Filter
open scoped RealInnerProductSpace Topology
open FunctionalInequalities.Probability.Stein

namespace FunctionalInequalities.Analysis.Dirichlet
open Set Metric Filter MeasureTheory
open scoped RealInnerProductSpace Topology

/-- Domain-only SAME-U source with generated primal C1 on the open domain. -/
theorem exists_unit_c1_solution {n : ℕ} (hn : 0<n)
    {Ω : Set (EuclideanSpace ℝ (Fin n))} (hΩ : IsOpen Ω) (hcΩ : Convex ℝ Ω)
    (hb : Bornology.IsBounded Ω) :
    ∃ (U : EuclideanSpace ℝ (Fin n) → ℝ) (μ : Measure (EuclideanSpace ℝ (Fin n))),
      U ∈ Dirichlet.subsolutions Ω ∧ ConvexOn ℝ (closure Ω) U ∧ ContinuousOn U (closure Ω) ∧
      (∀ z ∈ frontier Ω, U z=0) ∧
      (∀ G : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet G →
        μ G=volume (subgradientImageOn U Ω (G ∩ Ω))) ∧
      (∀ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K → K ⊆ Ω → μ K<⊤) ∧
      μ=volume.restrict Ω ∧
      (∀ G : Set (EuclideanSpace ℝ (Fin n)), IsOpen G → G ⊆ Ω →
        volume (subgradientImageOn U Ω G)=volume G) ∧
      (∀ x ∈ Ω, U x<0) ∧
      (∀ x ∈ Ω, ∀ p : EuclideanSpace ℝ (Fin n),
        (∀ z ∈ Ω, U x+⟪p, z-x⟫ ≤ U z) →
        ∀ y ∈ Ω, U y=U x+⟪p, y-x⟫ → y=x) ∧ StrictConvexOn ℝ Ω U ∧
      (∀ x ∈ Ω, ∃ p : EuclideanSpace ℝ (Fin n),
        (∀ y ∈ Ω, U x+⟪p, y-x⟫ ≤ U y) ∧
        ∀ q : EuclideanSpace ℝ (Fin n), (∀ y ∈ Ω, U x+⟪q, y-x⟫ ≤ U y) → q=p) ∧
      ∃ g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
        ContinuousOn g Ω ∧ (∀ x ∈ Ω, HasFDerivAt U (innerSL ℝ (g x)) x) ∧
        ContDiffOn ℝ 1 U Ω ∧ (∀ x ∈ Ω, gradient U x=g x) ∧
        ∀ x ∈ Ω, (∀ y ∈ Ω, U x+⟪g x, y-x⟫ ≤ U y) ∧
          ∀ q : EuclideanSpace ℝ (Fin n), (∀ y ∈ Ω, U x+⟪q, y-x⟫ ≤ U y) → q=g x := by
    obtain ⟨U, μ, hU, hcv, hC, hz, hμ, hfin, hm, hMA, hneg, hcontact, hstrict, hs⟩ :=
      exists_unit_unique_supports hn hΩ hcΩ hb
    obtain ⟨g, hg, hd, hC1, hgrad, hsp⟩ :=
      exists_c1_of_unique_supports hΩ (hcv.subset subset_closure hcΩ)
        (hC.mono subset_closure) hs
    exact
      ⟨U, μ, hU, hcv, hC, hz, hμ, hfin, hm, hMA, hneg, hcontact, hstrict, hs, g, hg, hd,
        hC1, hgrad, hsp⟩

end FunctionalInequalities.Analysis.Dirichlet
