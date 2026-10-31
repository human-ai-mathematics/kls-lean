module

public import FunctionalInequalities.Analysis.Convex.Alexandrov.Measure
public import FunctionalInequalities.Analysis.Convex.GaugeCone.Measure
public import FunctionalInequalities.Analysis.Convex.Alexandrov.Comparison
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Prescribed positive one-atom Dirichlet data

An actual gauge cone on a bounded open convex neighborhood of zero is scaled
to any prescribed positive atomic weight in positive dimension. The unit
vertex coefficient is generated, proved positive and finite, then normalized
using the existing DOMAIN scalar/Haar theorem. Its actual MA measure is
constructed once and the SAME witness identified with the prescribed atom.
This supports the Dirichlet prerequisites of Letwin arXiv:2607.24164v1,
Lemma 2.2 / BB arXiv:1207.6128v1, Theorem 2.24(ii). It is a centered ONE-ATOM
source, not a finite-atomic allocator, a smooth unit-density reference,
Pogorelov estimate or Sobolev regularity theorem. The translated source also accepts any actual
interior vertex and zero
weight in positive dimension, using the genuine constant source. Arbitrary
zero-dimensional weights are deliberately not asserted.
-/

@[expose] public section

noncomputable section
open Set Metric MeasureTheory
open scoped RealInnerProductSpace ENNReal Topology
namespace FunctionalInequalities.Analysis.GaugeCone

section PrescribedMass
open Classical

/-- A genuine positive-height zero-boundary cone with any prescribed positive
atomic weight in positive dimension. No source mass or normalization identity
is supplied; the actual coefficient is generated then normalized. -/
theorem exists_height_of_mass {n : ℕ} (hn : 0 < n) {D : Set (EuclideanSpace ℝ (Fin n))}
    (hD : IsOpen D) (hDc : Convex ℝ D) (h0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ D)
    (hb : Bornology.IsBounded D) {m : ℝ} (hm : 0 < m) :
    ∃ h : ℝ,
      0 < h ∧
        ConvexOn ℝ univ (potential D h) ∧
          Continuous (potential D h) ∧
            (∀ z ∈ frontier D, potential D h z = 0) ∧
              ∀ G : Set (EuclideanSpace ℝ (Fin n)),
                G ⊆ D →
                  (volume : Measure (EuclideanSpace ℝ (Fin n)))
                      (subgradientImageOn (potential D h) D G) =
                    if (0 : EuclideanSpace ℝ (Fin n)) ∈ G then ENNReal.ofReal m else 0 := by
  let E := EuclideanSpace ℝ (Fin n)
  let M : ℝ≥0∞ := (volume : Measure E) (polar D 1)
  have hMp := volume_polar_pos hb (h := 1) (by norm_num)
  have hMt := volume_polar_lt_top hD hDc h0 (h := 1) (by norm_num)
  change 0 < M at hMp
  change M < ⊤ at hMt
  have hMr : 0 < M.toReal := ENNReal.toReal_pos hMp.ne' hMt.ne
  let c : ℝ := (m / M.toReal) ^ ((n : ℝ)⁻¹)
  have hc : 0 < c := Real.rpow_pos_of_pos (div_pos hm hMr) _
  have hcpow : c ^ n = m / M.toReal :=
    Real.rpow_inv_natCast_pow (div_nonneg hm.le hMr.le) hn.ne'
  have hcoef : ENNReal.ofReal (c ^ n) * M = ENNReal.ofReal m := by
    calc
      _ = ENNReal.ofReal (c ^ n) * ENNReal.ofReal M.toReal := by
        rw [ENNReal.ofReal_toReal hMt.ne]
      _ = ENNReal.ofReal (c ^ n * M.toReal) := (ENNReal.ofReal_mul (pow_nonneg hc.le n)).symm
      _ = ENNReal.ofReal m := by rw [hcpow, div_mul_cancel₀ _ hMr.ne']
  have ht := geometry hD hDc h0 hc
  refine ⟨c, hc, ht.1, ht.2.1, ht.2.2.2.1, ?_⟩
  intro G hG
  have heq : potential D c = (fun x => c * potential D 1 x) := by
    funext x
    simp only [potential, one_mul]
  rw [heq, volume_subgradientImageOn_mul_pos (potential D 1) hc D G, finrank_euclideanSpace_fin,
    volume_image hD hDc h0 (h := 1) (by norm_num) G hG]
  split_ifs
  · exact hcoef
  · simp

/-- One actual MA construction and atomic identification, shared by the
centered height source and the translated/nonnegative source. The public
callers each generate the raw image equation from their genuine data. -/
private theorem atomic_measure_of_image {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {Ω : Set E} {u : E → ℝ} {x₀ : E} {m : ℝ} (hΩ : IsOpen Ω) (hcv : ConvexOn ℝ Ω u)
    (hct : ContinuousOn u Ω) (hx₀ : x₀ ∈ Ω)
    (hraw :
      ∀ G : Set E,
        G ⊆ Ω → volume (subgradientImageOn u Ω G) = if x₀ ∈ G then ENNReal.ofReal m else 0) :
    ∃ μ : Measure E,
      (∀ G : Set E, MeasurableSet G → μ G = volume (subgradientImageOn u Ω (G ∩ Ω))) ∧
        (∀ K : Set E, IsCompact K → K ⊆ Ω → μ K < ⊤) ∧
          μ = ENNReal.ofReal m • Measure.dirac x₀ := by
  obtain ⟨μ, hμ, hfin⟩ := exists_domain_mongeAmpere_measure hΩ hcv hct
  refine ⟨μ, hμ, hfin, ?_⟩
  apply Measure.ext
  intro G hG
  rw [hμ G hG, hraw (G ∩ Ω) inter_subset_right, Measure.smul_apply, Measure.dirac_apply]
  by_cases hxG : x₀ ∈ G <;> simp [hxG, hx₀]

/-- The actual canonical MA constructor is called once for the generated
cone. The SAME measure keeps its all-Borel formula/local finiteness and is
then identified with the prescribed atom; no measure witness is an input. -/
theorem exists_mongeAmpere_measure_of_mass {n : ℕ} (hn : 0 < n)
    {D : Set (EuclideanSpace ℝ (Fin n))} (hD : IsOpen D) (hDc : Convex ℝ D)
    (h0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ D) (hb : Bornology.IsBounded D) {m : ℝ}
    (hm : 0 < m) :
    ∃ (h : ℝ) (μ : Measure (EuclideanSpace ℝ (Fin n))),
      0 < h ∧
        ConvexOn ℝ univ (potential D h) ∧
          Continuous (potential D h) ∧
            (∀ z ∈ frontier D, potential D h z = 0) ∧
              (∀ G : Set (EuclideanSpace ℝ (Fin n)),
                  MeasurableSet G →
                    μ G =
                      (volume : Measure (EuclideanSpace ℝ (Fin n)))
                        (subgradientImageOn (potential D h) D (G ∩ D))) ∧
                (∀ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K → K ⊆ D → μ K < ⊤) ∧
                  μ = ENNReal.ofReal m • Measure.dirac 0 := by
  obtain ⟨h, hh, hcv, hct, hfr, hraw⟩ := exists_height_of_mass hn hD hDc h0 hb hm
  obtain ⟨μ, hμ, hfin, heq⟩ :=
    atomic_measure_of_image hD (hcv.subset (subset_univ _) hDc) hct.continuousOn h0 hraw
  exact ⟨h, μ, hh, hcv, hct, hfr, hμ, hfin, heq⟩


/-- Actual affine translation of the centered source, using the established
DOMAIN affine/Haar identity rather than assuming MA agreement. -/
private theorem translated_positive {n : ℕ} (hn : 0 < n) {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (hΩ : IsOpen Ω) (hcΩ : Convex ℝ Ω) (hb : Bornology.IsBounded Ω)
    {x₀ : EuclideanSpace ℝ (Fin n)} (hx₀ : x₀ ∈ Ω) {m : ℝ} (hm : 0 < m) :
    ∃ u : EuclideanSpace ℝ (Fin n) → ℝ,
      ConvexOn ℝ univ u ∧
        Continuous u ∧
          (∀ z ∈ frontier Ω, u z = 0) ∧
            ∀ G : Set (EuclideanSpace ℝ (Fin n)),
              G ⊆ Ω →
                (volume : Measure (EuclideanSpace ℝ (Fin n))) (subgradientImageOn u Ω G) =
                  if x₀ ∈ G then ENNReal.ofReal m else 0 := by
  let E := EuclideanSpace ℝ (Fin n)
  let e : E ≃ᵃ[ℝ] E := AffineEquiv.constVAdd ℝ E x₀
  let D : Set E := e ⁻¹' Ω
  have hD : IsOpen D := hΩ.preimage e.toAffineMap.continuous_of_finiteDimensional
  have hcD : Convex ℝ D := Convex.affine_preimage e.toAffineMap hcΩ
  have hD0 : (0 : E) ∈ D := by simpa [D, e] using hx₀
  have hi : Isometry (e : E → E) := by
    intro a b
    change edist (x₀ + a) (x₀ + b) = edist a b
    exact edist_add_left x₀ a b
  have hbD : Bornology.IsBounded D := hi.antilipschitzWith.isBounded_preimage hb
  have heD : e '' D = Ω := image_preimage_eq Ω e.surjective
  obtain ⟨h, hh, hcv, hct, hfr, hraw⟩ := exists_height_of_mass hn hD hcD hD0 hbD hm
  let q := potential D h
  let u : E → ℝ := q ∘ e.symm
  have hucv : ConvexOn ℝ univ u := by
    change ConvexOn ℝ univ (potential D h ∘ e.symm.toAffineMap)
    exact (hcv.comp_affineMap e.symm.toAffineMap)
  have huct : Continuous u := hct.comp e.symm.toAffineMap.continuous_of_finiteDimensional
  refine ⟨u, hucv, huct, ?_, ?_⟩
  · intro y hy
    have hf : e ⁻¹' frontier Ω = frontier D := by
      exact (AffineIsometryEquiv.constVAdd ℝ E x₀).toHomeomorph.preimage_frontier Ω
    have hmem : e.symm y ∈ frontier D := by
      rw [← hf]
      change e (e.symm y) ∈ frontier Ω
      simpa only [e.apply_symm_apply] using hy
    exact hfr (e.symm y) hmem
  · intro G hG
    let H : Set E := e.symm '' G
    have hH : H ⊆ D := by
      rintro y ⟨z, hz, rfl⟩
      change e (e.symm z) ∈ Ω
      simpa only [e.apply_symm_apply] using hG hz
    have heG : e '' H = G := by
      dsimp only [H]
      rw [image_image]
      simp
    have hdet : ENNReal.ofReal |LinearMap.det (e.linear : E →ₗ[ℝ] E)|⁻¹ = 1 := by simp [e]
    have hv := volume_subgradientImageOn_comp_affineEquiv_symm q e D H
    have hv' :
      (volume : Measure E) (subgradientImageOn u Ω G) = volume (subgradientImageOn q D H) := by
      simpa only [heD, heG, hdet, one_mul] using hv
    have hiff : (0 : E) ∈ H ↔ x₀ ∈ G := by
      constructor
      · rintro ⟨z, hz, hz0⟩
        have hzEq : z = x₀ := by
          have ht := congrArg e hz0
          simpa [e] using ht
        exact hzEq ▸ hz
      · intro hx
        refine ⟨x₀, hx, ?_⟩
        simp [e]
    rw [hv', hraw H hH]
    simp only [hiff]

/-- A generated one-atom Dirichlet solution for every nonnegative target
weight and every actual interior vertex, with its SAME actual MA measure.
No source mass/MA agreement/measure witness is supplied as an assumption. -/
theorem exists_one_atom {n : ℕ} (hn : 0 < n) {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (hΩ : IsOpen Ω) (hcΩ : Convex ℝ Ω) (hb : Bornology.IsBounded Ω)
    {x₀ : EuclideanSpace ℝ (Fin n)} (hx₀ : x₀ ∈ Ω) {m : ℝ} (hm : 0 ≤ m) :
    ∃ (u : EuclideanSpace ℝ (Fin n) → ℝ) (μ : Measure (EuclideanSpace ℝ (Fin n))),
      ConvexOn ℝ univ u ∧
        Continuous u ∧
          (∀ z ∈ frontier Ω, u z = 0) ∧
            (∀ G : Set (EuclideanSpace ℝ (Fin n)),
                MeasurableSet G → μ G = volume (subgradientImageOn u Ω (G ∩ Ω))) ∧
              (∀ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K → K ⊆ Ω → μ K < ⊤) ∧
                μ = ENNReal.ofReal m • Measure.dirac x₀ := by
  classical
  let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  have hdata :
    ∃ u : EuclideanSpace ℝ (Fin n) → ℝ,
      ConvexOn ℝ univ u ∧
        Continuous u ∧
          (∀ z ∈ frontier Ω, u z = 0) ∧
            ∀ G : Set (EuclideanSpace ℝ (Fin n)),
              G ⊆ Ω →
                (volume : Measure (EuclideanSpace ℝ (Fin n))) (subgradientImageOn u Ω G) =
                  if x₀ ∈ G then ENNReal.ofReal m else 0 := by
    by_cases hm0 : m = 0
    · refine ⟨fun _ => 0, convexOn_const _ convex_univ, continuous_const, by intros; simp, ?_⟩
      intro G hG
      rw [volume_subgradientImageOn_const 0 hΩ hG]
      simp [hm0]
    · exact translated_positive hn hΩ hcΩ hb hx₀ (lt_of_le_of_ne hm (Ne.symm hm0))
  obtain ⟨u, hcv, hct, hfr, hraw⟩ := hdata
  obtain ⟨μ, hμ, hfin, heq⟩ :=
    atomic_measure_of_image hΩ (hcv.subset (subset_univ _) hcΩ) hct.continuousOn hx₀ hraw
  exact ⟨u, μ, hcv, hct, hfr, hμ, hfin, heq⟩

end PrescribedMass
end FunctionalInequalities.Analysis.GaugeCone
