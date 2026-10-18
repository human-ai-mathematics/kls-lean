import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.Lipschitz

/-! # A Lipschitz extension into a finite-dimensional inner-product space

global Lipschitz extension of the route recorded in
`research/decisions/2026-09-19-locally-lipschitz-vector-coarea-route.md`: a map into a
finite-dimensional real inner-product space that is Lipschitz on a set agrees on that set with a
map that is Lipschitz on the **whole** space.

**This is not Kirszbraun's theorem.**  Nothing whatever is claimed about the constant: it is
existentially quantified, and the construction below loses a factor `√m`.  The extension is the
componentwise McShane extension `LipschitzOnWith.extend_pi` on `Fin m → ℝ` with the sup norm,
transported to the target through the linear isometry `(stdOrthonormalBasis ℝ W).repr` onto
`EuclideanSpace ℝ (Fin m)` and the `PiLp` equivalences `WithLp.ofLp`, `WithLp.toLp`, whose Lipschitz
constants are `1` and `m ^ (1 / 2)`.  It is bookkeeping, not analysis, and it is all the locally
Lipschitz coarea route needs, because the globally Lipschitz formula it feeds only asks for *some*
constant.

The source is an arbitrary pseudometric space: no completeness, separability, boundedness or
nonemptiness of the set is used, and the zero-dimensional target is allowed.
-/

noncomputable section

open Metric Module Set
open scoped ENNReal NNReal

namespace FunctionalInequalities.Analysis

/-- **global Lipschitz extension: a map Lipschitz on a set extends to a globally Lipschitz map into the same
finite-dimensional inner-product space.**  The Lipschitz constant of the extension is existentially
quantified and **no optimality is claimed**; this is the componentwise McShane extension, not
Kirszbraun's theorem. -/
theorem exists_lipschitzWith_eqOn_of_lipschitzOnWith {α W : Type*} [PseudoMetricSpace α]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    {u : α → W} {s : Set α} {K : ℝ≥0} (hu : LipschitzOnWith K u s) :
    ∃ (K' : ℝ≥0) (w : α → W), LipschitzWith K' w ∧ EqOn w u s := by
  classical
  set m := finrank ℝ W
  -- A linear isometry onto the model Euclidean space, and the two `PiLp` transports.
  let e : W ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin m) := (stdOrthonormalBasis ℝ W).repr
  have he : LipschitzWith 1 (e : W → EuclideanSpace ℝ (Fin m)) := e.isometry.lipschitz
  have hf : LipschitzOnWith (1 * (1 * K))
      ((WithLp.ofLp : EuclideanSpace ℝ (Fin m) → (Fin m → ℝ)) ∘
        (e : W → EuclideanSpace ℝ (Fin m)) ∘ u) s :=
    (PiLp.lipschitzWith_ofLp 2 (fun _ : Fin m => ℝ)).comp_lipschitzOnWith
      (he.comp_lipschitzOnWith hu)
  -- Componentwise McShane on `Fin m → ℝ` with the sup norm.
  obtain ⟨g, hgL, hgeq⟩ := hf.extend_pi
  refine ⟨1 * (((Fintype.card (Fin m) : ℝ≥0) ^ ((1 : ℝ≥0∞) / 2).toReal) * (1 * (1 * K))),
    (e.symm : EuclideanSpace ℝ (Fin m) → W) ∘ (WithLp.toLp 2) ∘ g, ?_, ?_⟩
  · exact e.symm.isometry.lipschitz.comp
      ((PiLp.lipschitzWith_toLp 2 (fun _ : Fin m => ℝ)).comp hgL)
  · intro x hx
    have hx' := hgeq hx
    simp only [Function.comp_apply] at hx' ⊢
    rw [← hx']
    simp

end FunctionalInequalities.Analysis
