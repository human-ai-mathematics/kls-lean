import FunctionalInequalities.Analysis.Convex.Legendre.Basic
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Topology.Semicontinuity.Basic

/-!
# The Fenchel–Moreau theorem for extended-real potentials

For a convex, lower semicontinuous potential `ψ : E → ℝ ∪ {+∞}` on a real Hilbert space that is
finite somewhere, the biconjugate is `ψ` itself: `ψ** = ψ` (`legendre_legendre_eq`). This is the
identity `(ψ*)* = ψ` recalled in Cordero-Erausquin–Klartag, *Moment measures*
(arXiv:1304.0630v1), Section 2, after (12).

Proof: the epigraph `{(y, r) | ψ y ≤ r}` is closed and convex, so each point `(x, a)` with
`a < ψ x` is strictly separated from it by a continuous linear functional `(y, r) ↦ ⟪w, y⟫ + βr`
with `β ≤ 0`. A non-vertical separator (`β < 0`) is an affine minorant of `ψ` exceeding `a` at `x`;
a vertical one (`β = 0`) is added with arbitrary weight to a fixed affine minorant, which exists by
separating a point below the graph over the effective domain. Affine minorants bound the
biconjugate from below (`le_legendre_legendre_of_affine_le`).
-/

noncomputable section

open Set

namespace FunctionalInequalities.Analysis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- An affine minorant `y ↦ ⟪y, p⟫ − c` of `ψ` is a lower bound for the biconjugate `ψ**`. -/
theorem le_legendre_legendre_of_affine_le {ψ : E → EReal} {p : E} {c : ℝ}
    (h : ∀ y, ((inner ℝ y p - c : ℝ) : EReal) ≤ ψ y) (x : E) :
    ((inner ℝ x p - c : ℝ) : EReal) ≤ legendre (legendre ψ) x := by
  have hp : legendre ψ p ≤ (c : EReal) := by
    apply iSup_le
    intro y
    have hy := h y
    generalize ψ y = s at hy ⊢
    induction s using EReal.rec with
    | bot => exact absurd hy (not_le.mpr (EReal.bot_lt_coe _))
    | top => simp
    | coe s =>
      rw [← EReal.coe_sub, EReal.coe_le_coe_iff]
      rw [EReal.coe_le_coe_iff] at hy
      linarith
  calc ((inner ℝ x p - c : ℝ) : EReal) = (inner ℝ p x : EReal) - (c : EReal) := by
        rw [EReal.coe_sub, real_inner_comm]
    _ ≤ (inner ℝ p x : EReal) - legendre ψ p := EReal.sub_le_sub le_rfl hp
    _ ≤ legendre (legendre ψ) x :=
        le_iSup (fun q : E => (inner ℝ q x : EReal) - legendre ψ q) p

/-- The vertical coefficient of a separating functional is nonpositive: the epigraph is unbounded
upwards above any point of the effective domain. -/
private theorem coeff_nonpos {ψ : E → EReal} (hne : ∃ x, ψ x ≠ ⊤) (hbot : ∀ x, ψ x ≠ ⊥)
    {w : E} {β u : ℝ} (hS : ∀ y (r : ℝ), ψ y ≤ r → inner ℝ w y + r * β < u) : β ≤ 0 := by
  by_contra hβ
  replace hβ : 0 < β := not_le.mp hβ
  obtain ⟨y, hy⟩ := hne
  set r₀ := (ψ y).toReal
  have hr₀ : ψ y = (r₀ : EReal) := (EReal.coe_toReal hy (hbot y)).symm
  set t : ℝ := max 0 ((u - inner ℝ w y) / β - r₀) + 1
  have ht : (u - inner ℝ w y) / β - r₀ < t := by
    have := le_max_right 0 ((u - inner ℝ w y) / β - r₀)
    linarith
  have hle : ψ y ≤ ((r₀ + t : ℝ) : EReal) := by
    rw [hr₀, EReal.coe_le_coe_iff]
    have : 0 ≤ t := by positivity
    linarith
  have h := hS y (r₀ + t) hle
  have h2 : u - inner ℝ w y < (r₀ + t) * β := by
    have := (div_lt_iff₀ hβ).mp (show (u - inner ℝ w y) / β < r₀ + t by linarith)
    linarith
  linarith

variable [CompleteSpace E]

/-- Strict separation of a point below the graph from the closed convex epigraph, written with
the Riesz representative `w` of the horizontal part and the vertical coefficient `β`. -/
private theorem exists_separation {ψ : E → EReal} (hψ : ConvexPotential ψ)
    (hlsc : LowerSemicontinuous ψ) {x : E} {a : ℝ} (ha : (a : EReal) < ψ x) :
    ∃ (w : E) (β u : ℝ), (∀ y (r : ℝ), ψ y ≤ r → inner ℝ w y + r * β < u) ∧
      u < inner ℝ w x + a * β := by
  set S : Set (E × ℝ) := {q | ψ q.1 ≤ (q.2 : EReal)} with hSdef
  have hSclosed : IsClosed S :=
    hlsc.isClosed_epigraph.preimage
      (continuous_fst.prodMk (continuous_coe_real_ereal.comp continuous_snd))
  have hx : (x, a) ∉ S := fun h => absurd h (not_le.mpr ha)
  obtain ⟨f, u, hfS, hfx⟩ := geometric_hahn_banach_closed_point hψ.2 hSclosed hx
  set w : E := (InnerProductSpace.toDual ℝ E).symm (f.comp (ContinuousLinearMap.inl ℝ E ℝ))
  have hf : ∀ (y : E) (r : ℝ), f (y, r) = inner ℝ w y + r * f ((0 : E), (1 : ℝ)) := by
    intro y r
    have hyr : ((y, r) : E × ℝ) = (y, 0) + r • ((0 : E), (1 : ℝ)) := by
      ext <;> simp
    rw [hyr, map_add, map_smul, smul_eq_mul, InnerProductSpace.toDual_symm_apply]
    rfl
  refine ⟨w, f ((0 : E), (1 : ℝ)), u, fun y r hyr => ?_, by rw [← hf]; exact hfx⟩
  rw [← hf]
  exact hfS (y, r) hyr

omit [CompleteSpace E] in
/-- A non-vertical separator yields an affine minorant that exceeds `a` at `x`. -/
private theorem affine_of_separation {ψ : E → EReal} (hbot : ∀ x, ψ x ≠ ⊥) {w : E} {β u : ℝ}
    (hβ : β < 0) (hS : ∀ y (r : ℝ), ψ y ≤ r → inner ℝ w y + r * β < u) :
    ∀ y, ((inner ℝ y ((-β)⁻¹ • w) - u / (-β) : ℝ) : EReal) ≤ ψ y := by
  intro y
  by_cases hy : ψ y = ⊤
  · rw [hy]; exact le_top
  have hr : ψ y = ((ψ y).toReal : EReal) := (EReal.coe_toReal hy (hbot y)).symm
  have h := hS y (ψ y).toReal hr.le
  rw [hr, EReal.coe_le_coe_iff, real_inner_smul_right, real_inner_comm]
  have hγ : 0 < -β := neg_pos.mpr hβ
  rw [show (-β)⁻¹ * inner ℝ w y - u / -β = (inner ℝ w y - u) / -β by ring, div_le_iff₀ hγ]
  nlinarith

/-- **Fenchel–Moreau theorem**: a convex, lower semicontinuous extended-real potential that is
finite somewhere equals its biconjugate, `ψ** = ψ`. -/
theorem legendre_legendre_eq {ψ : E → EReal} (hψ : ConvexPotential ψ)
    (hlsc : LowerSemicontinuous ψ) (hne : ∃ x, ψ x ≠ ⊤) : legendre (legendre ψ) = ψ := by
  have hprop : ProperPotential ψ := ⟨hψ.1, hne⟩
  -- a fixed affine minorant, from a point below the graph over the domain
  obtain ⟨p₀, c₀, hminor⟩ : ∃ (p : E) (c : ℝ), ∀ y, ((inner ℝ y p - c : ℝ) : EReal) ≤ ψ y := by
    obtain ⟨y₀, hy₀⟩ := hne
    obtain ⟨r, hr⟩ : ∃ r : ℝ, ψ y₀ = r := ⟨_, (EReal.coe_toReal hy₀ (hψ.1 y₀)).symm⟩
    have hlt : ((r - 1 : ℝ) : EReal) < ψ y₀ := by
      rw [hr, EReal.coe_lt_coe_iff]; linarith
    obtain ⟨w, β, u, hS, hx⟩ := exists_separation hψ hlsc hlt
    have hβ0 := coeff_nonpos ⟨y₀, hy₀⟩ hψ.1 hS
    have hβ : β < 0 := by
      refine lt_of_le_of_ne hβ0 fun hβ => ?_
      have h1 := hS y₀ r hr.le
      rw [hβ] at h1 hx
      simp only [mul_zero, add_zero] at h1 hx
      linarith
    exact ⟨_, _, affine_of_separation hψ.1 hβ hS⟩
  funext x
  refine le_antisymm (biconjugate_le ψ hprop x) ?_
  refine EReal.ge_of_forall_gt_iff_ge.mp fun a ha => ?_
  obtain ⟨w, β, u, hS, hx⟩ := exists_separation hψ hlsc ha
  have hβ0 := coeff_nonpos hne hψ.1 hS
  rcases lt_or_eq_of_le hβ0 with hβ | hβ
  · -- non-vertical separation
    refine le_trans ?_ (le_legendre_legendre_of_affine_le (affine_of_separation hψ.1 hβ hS) x)
    rw [EReal.coe_le_coe_iff, real_inner_smul_right, real_inner_comm]
    have hγ : 0 < -β := neg_pos.mpr hβ
    rw [show (-β)⁻¹ * inner ℝ w x - u / -β = (inner ℝ w x - u) / -β by ring, le_div_iff₀ hγ]
    nlinarith
  · -- vertical separation: add it to the fixed affine minorant with a large weight
    subst hβ
    simp only [mul_zero, add_zero] at hS hx
    have hdom : ∀ y, ψ y ≠ ⊤ → inner ℝ w y < u := fun y hy =>
      hS y (ψ y).toReal (EReal.coe_toReal hy (hψ.1 y)).symm.le
    set gap : ℝ := inner ℝ w x - u with hgap
    have hgap0 : 0 < gap := by rw [hgap]; linarith
    set lam : ℝ := max 0 ((a - (inner ℝ x p₀ - c₀)) / gap) with hlam
    have hlam0 : 0 ≤ lam := le_max_left _ _
    have hminor' : ∀ y, ((inner ℝ y (p₀ + lam • w) - (c₀ + lam * u) : ℝ) : EReal) ≤ ψ y := by
      intro y
      by_cases hy : ψ y = ⊤
      · rw [hy]; exact le_top
      refine le_trans ?_ (hminor y)
      rw [EReal.coe_le_coe_iff, inner_add_right, real_inner_smul_right, real_inner_comm w y]
      nlinarith [hdom y hy, mul_le_mul_of_nonneg_left (hdom y hy).le hlam0]
    refine le_trans ?_ (le_legendre_legendre_of_affine_le hminor' x)
    rw [EReal.coe_le_coe_iff, inner_add_right, real_inner_smul_right, real_inner_comm w x]
    have hl : (a - (inner ℝ x p₀ - c₀)) / gap ≤ lam := le_max_right _ _
    have hl' : a - (inner ℝ x p₀ - c₀) ≤ lam * gap := by
      rwa [div_le_iff₀ hgap0] at hl
    rw [hgap] at hl'
    nlinarith

end FunctionalInequalities.Analysis
