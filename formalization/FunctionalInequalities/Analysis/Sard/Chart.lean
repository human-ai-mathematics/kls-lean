module

public import FunctionalInequalities.Analysis.PiCoordinates
public import FunctionalInequalities.Analysis.Sard.CoordinateChange
public import FunctionalInequalities.Analysis.LocalExtension
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # The `C^k` graph chart of a regular zero set

The finite-regularity counterpart of the `C^∞` chart `Analysis.exists_local_graph`.
-/

@[expose] public section

noncomputable section

open Set Metric Filter Topology
open scoped ContDiff

namespace FunctionalInequalities.Analysis.MorseSard

variable {n : ℕ}

/-- Dropping one coordinate does not increase the sup norm. -/
theorem norm_sub_le_insertNth (i : Fin (n + 1)) (θ : (Fin n → ℝ) → ℝ) (a b : Fin n → ℝ) :
    ‖a - b‖ ≤ ‖Fin.insertNth (α := fun _ => ℝ) i (θ a) a
      - Fin.insertNth (α := fun _ => ℝ) i (θ b) b‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun j => ?_
  have := norm_le_pi_norm (Fin.insertNth (α := fun _ => ℝ) i (θ a) a
      - Fin.insertNth (α := fun _ => ℝ) i (θ b) b) (i.succAbove j)
  simpa using this

/-- The graph map of a `C^k` function is `C^k`. -/
theorem contDiff_insertNth {k : ℕ} {θ : (Fin n → ℝ) → ℝ} (i : Fin (n + 1))
    (hθ : ContDiff ℝ k θ) :
    ContDiff ℝ k (fun y : Fin n → ℝ => Fin.insertNth (α := fun _ => ℝ) i (θ y) y) := by
  rw [contDiff_pi]
  intro m
  rcases eq_or_ne m i with rfl | hm
  · simpa using hθ
  · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hm
    simpa using contDiff_apply (𝕜 := ℝ) (F' := fun _ => ℝ) j

/-- Graph maps are injective. -/
theorem injective_insertNth (i : Fin (n + 1)) (θ : (Fin n → ℝ) → ℝ) :
    Function.Injective (fun y : Fin n → ℝ => Fin.insertNth (α := fun _ => ℝ) i (θ y) y) := by
  intro a b hab
  have := congrArg (Fin.removeNth (α := fun _ => ℝ) i) hab
  simpa using this


/-- **The `C^k` graph chart of a regular zero set.**  Near a regular zero `x₀` of a `C^k`
function `w` with `1 ≤ k`, every zero of `w` is the graph point of a globally `C^k` function `θ`
of the remaining `n` coordinates.  The chart is the `C^k` inverse function theorem
`ContDiffAt.to_localInverse` applied to the map replacing the `i`-th coordinate by `w`, exactly
as in the `C^∞` statement `Analysis.exists_local_graph`; no manifold framework. -/
theorem exists_graph {k : ℕ} (hk : 1 ≤ k) {w : (Fin (n + 1) → ℝ) → ℝ}
    {x₀ : Fin (n + 1) → ℝ} (hw : ContDiff ℝ k w) (hx₀ : w x₀ = 0) (hd : fderiv ℝ w x₀ ≠ 0) :
    ∃ (i : Fin (n + 1)) (θ : (Fin n → ℝ) → ℝ), ContDiff ℝ k θ ∧
      ∀ᶠ x in 𝓝 x₀, w x = 0 →
        x = Fin.insertNth (α := fun _ => ℝ) i (θ (Fin.removeNth i x)) (Fin.removeNth i x) := by
  classical
  obtain ⟨i, hi⟩ := PiCoordinates.exists_apply_single_ne_zero hd
  have hkne : ((k : ℕ) : WithTop ℕ∞) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    omega
  have hdiff : Differentiable ℝ w := hw.differentiable hkne
  obtain ⟨Le, hLecoe⟩ := Sard.CoordinateChange.exists_updateEquiv i hi
  have hΦc : ContDiffAt ℝ k (fun x => Function.update x i (w x)) x₀ :=
    (Sard.CoordinateChange.contDiff_update i hw).contDiffAt
  have hΦd : HasFDerivAt (fun x => Function.update x i (w x))
      (Le : (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ)) x₀ := by
    rw [hLecoe]
    exact Sard.CoordinateChange.hasFDerivAt_update i hdiff x₀
  set ψ : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) := hΦc.localInverse hΦd hkne with hψdef
  have hψc : ContDiffAt ℝ k ψ (Function.update x₀ i (w x₀)) := hΦc.to_localInverse hΦd hkne
  have hleft : ∀ᶠ x in 𝓝 x₀, ψ (Function.update x i (w x)) = x :=
    (hΦc.hasStrictFDerivAt' hΦd hkne).eventually_left_inverse
  -- the zero set is straightened onto the `i`-th coordinate hyperplane
  have hkey : ∀ x : Fin (n + 1) → ℝ, w x = 0 →
      Function.update x i (w x)
        = Fin.insertNth (α := fun _ => ℝ) i (0 : ℝ) (Fin.removeNth i x) := by
    intro x hx
    simp only [Fin.insertNth_removeNth, hx]

  set emb : (Fin n → ℝ) → (Fin (n + 1) → ℝ) :=
    fun y => Fin.insertNth (α := fun _ => ℝ) i (0 : ℝ) y with hembdef
  have hembc : ContDiff ℝ k emb := contDiff_insertNth (θ := fun _ => (0 : ℝ)) i contDiff_const
  have hembx₀ : emb (Fin.removeNth i x₀) = Function.update x₀ i (w x₀) := (hkey x₀ hx₀).symm
  have hθ₀ : ContDiffAt ℝ k (fun y : Fin n → ℝ => ψ (emb y) i) (Fin.removeNth i x₀) := by
    have hcomp : ContDiffAt ℝ k (fun y : Fin n → ℝ => ψ (emb y)) (Fin.removeNth i x₀) := by
      refine ContDiffAt.comp _ ?_ hembc.contDiffAt
      rw [hembx₀]
      exact hψc
    exact (contDiff_apply (𝕜 := ℝ) (F' := fun _ => ℝ) i).contDiffAt.comp _ hcomp
  obtain ⟨u, hu, hθ₀u⟩ := hθ₀.contDiffOn (m := (k : ℕ)) le_rfl (by simp)
  obtain ⟨O, hOu, hOopen, hOmem⟩ := _root_.mem_nhds_iff.mp hu
  obtain ⟨θ, hθc, hθeq⟩ :=
    exists_contDiff_eventuallyEq hOopen (hθ₀u.mono hOu) hOmem
  refine ⟨i, θ, hθc, ?_⟩
  have hcont : ContinuousAt (fun x : Fin (n + 1) → ℝ => Fin.removeNth (α := fun _ => ℝ) i x) x₀ :=
    (continuous_pi fun j => continuous_apply _).continuousAt
  filter_upwards [hleft, hcont hθeq] with x hxinv hxθ hw0
  have hΦx : Function.update x i (w x) = emb (Fin.removeNth i x) := hkey x hw0
  rw [hΦx] at hxinv
  have hθx : θ (Fin.removeNth i x) = x i := by
    rw [hxθ, hxinv]
  rw [hθx, Fin.insertNth_self_removeNth]
