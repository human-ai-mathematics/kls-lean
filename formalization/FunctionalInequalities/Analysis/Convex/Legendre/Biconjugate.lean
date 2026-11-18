module

public import FunctionalInequalities.Analysis.Convex.Legendre.Basic
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Topology.Semicontinuity.Basic
import TauCeti.Analysis.Convex.FenchelMoreau

/-!
# The Fenchel–Moreau theorem for extended-real potentials

For a convex, lower semicontinuous potential `ψ : E → ℝ ∪ {+∞}` on a real Hilbert space that is
finite somewhere, the biconjugate is `ψ` itself: `ψ** = ψ` (`legendre_legendre_eq`). This is the
identity `(ψ*)* = ψ` recalled in Cordero-Erausquin–Klartag, *Moment measures*
(arXiv:1304.0630v1), Section 2, after (12).

For the reverse inequality `ψ ≤ ψ**`, the proof identifies the Legendre transform with Tau
Ceti's Fenchel conjugate for the inner product pairing and applies its Fenchel–Moreau theorem.
The affine-minorant estimate is `le_legendre_legendre_of_affine_le`.
-/

@[expose] public section

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

private theorem legendre_eq_fenchelConjugate (ψ : E → EReal) :
    legendre ψ = TauCeti.fenchelConjugate (innerₗ E) ψ := by
  funext x
  rw [legendre, TauCeti.fenchelConjugate_apply]
  rfl

variable [CompleteSpace E]

/-- **Fenchel–Moreau theorem**: a convex, lower semicontinuous extended-real potential that is
finite somewhere equals its biconjugate, `ψ** = ψ`. -/
theorem legendre_legendre_eq {ψ : E → EReal} (hψ : ConvexPotential ψ)
    (hlsc : LowerSemicontinuous ψ) (hne : ∃ x, ψ x ≠ ⊤) : legendre (legendre ψ) = ψ := by
  refine le_antisymm (biconjugate_le ψ ⟨hψ.1, hne⟩) ?_
  rw [legendre_eq_fenchelConjugate, legendre_eq_fenchelConjugate, TauCeti.fenchelConjugate_innerₗ_fenchelConjugate_innerₗ
    hψ.2 hlsc hψ.1]

end FunctionalInequalities.Analysis
