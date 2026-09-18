import FunctionalInequalities.Analysis.RankDeficient.Coarea
import FunctionalInequalities.KLS.Geometry.LocallyLipschitzCoarea

/-!
# Route statements for the codimension-`m` coarea formula of locally Lipschitz maps

**This file contains only `#check`s.  A proposition that type-checks is not a proof.**  It declares
nothing, proves nothing, and introduces no placeholder axiom.  Each proposition below is an
obligation of the route recorded in
`research/decisions/2026-09-19-locally-lipschitz-vector-coarea-route.md`, and **at the time of this
route snapshot none of `N0`, `X1`, `X3`–`X5` had been proved**.  Same convention as
`LipschitzVectorCoareaRouteStatements.lean`, whose `M2` is the target `N0` here.

## Position in the coarea program

`Analysis/RankDeficient/Coarea.lean` proves the codimension-`m` coarea formula for `C¹` maps (`R9`);
the route of the same day (`LipschitzVectorCoareaRouteStatements.lean`) states it for globally
Lipschitz maps (`L0`, open).  The scalar side ends one step further, at **locally Lipschitz**
functions with no global constant and no global modulus (`KLS.coarea_of_locallyLipschitz`, `L13`).
`N0` is the codimension-`m` `L13`; it is a common generalization of `L0` and `R9`.

## How the scalar `L13` did it, and what changes in codimension `m`

`L13` reduces to `L12` by half-open annuli: `u` is Lipschitz on each closed ball (compactness), a
McShane extension `LipschitzOnWith.extend_real` replaces it there by a globally Lipschitz `v k`, the
piece `S ∩ (ball 0 (k+1) \ ball 0 k)` lies in the open ball where `u = v k` near every point, so
gradients and level sets agree on the piece, `L12` applies to `v k`, and countable additivity sums.

In codimension `m` every step is the same except the extension: `extend_real` is scalar, and
Kirszbraun's theorem is not in Mathlib.  It is not needed: `L0` only asks for **some** Lipschitz
constant, so a **componentwise** McShane extension through a linear isometry onto
`EuclideanSpace ℝ (Fin m)` — Mathlib's `LipschitzOnWith.extend_pi` on `Fin m → ℝ` with the sup norm,
transported back through the `PiLp` equivalences at the cost of a factor `√m` — is enough (`X1`).
The assembly `X5` is then the codimension-`m` copy of `L13`, consuming `L0`; it is stated as an
implication from `L0`, so `N0 = X5 ∘ L0`, and the whole vector chain `C¹ → Lipschitz → locally
Lipschitz` closes once `L0` does.

## What Mathlib has

`LipschitzOnWith.extend_pi` (componentwise McShane), `LocallyLipschitzOn.exists_lipschitzOnWith_of_compact`
(a locally Lipschitz map is Lipschitz on a compact set), `Filter.EventuallyEq.fderiv_eq`, and the
`PiLp` Lipschitz equivalences.  No Kirszbraun, no coarea formula.
-/

noncomputable section

open MeasureTheory Set Module Metric FunctionalInequalities FunctionalInequalities.Analysis
open scoped ENNReal NNReal

/-! ### Proved inputs, for reference

The scalar `L13` (the template of the whole route) and the `C¹` codimension-`m` formula `R9`. -/

#check @FunctionalInequalities.KLS.coarea_of_locallyLipschitz
#check @FunctionalInequalities.Analysis.coarea_of_contDiff

/-! ### N0 — the target: the codimension-`m` coarea formula for locally Lipschitz maps

`coarea_of_contDiff` with `ContDiff ℝ 1 u` replaced by `LocallyLipschitz u`; identical to `M2` of
`LipschitzVectorCoareaRouteStatements.lean`.  No global Lipschitz constant, no `C¹` regularity, no
boundedness of `S`, no positivity of the codimension. -/

#check (∀ {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    [MeasurableSpace W] [BorelSpace W]
    {S : Set V} {u : V → W} {g : V → ℝ≥0∞} {k : ℕ},
    k + finrank ℝ W = finrank ℝ V → LocallyLipschitz u →
    MeasurableSet S → Measurable g →
    AEMeasurable (fun t : W => ∫⁻ y in S ∩ {x : V | u x = t}, g y ∂(KLS.hausdorffNormalized V k))
        (volume : Measure W) ∧
      (∫⁻ x in S, ENNReal.ofReal (coareaJacobian (fderiv ℝ u x)) * g x ∂(volume : Measure V)
        = ∫⁻ t, ∫⁻ y in S ∩ {x : V | u x = t}, g y ∂(KLS.hausdorffNormalized V k)
            ∂(volume : Measure W)))

/-! ### X1 — a vector Lipschitz extension with some constant

A map into a finite-dimensional inner-product space that is Lipschitz on a set agrees on that set
with a globally Lipschitz map.  The constant is existential: componentwise McShane through
`EuclideanSpace ℝ (Fin m)` gives `√m · K` and nothing is claimed about optimality (this is **not**
Kirszbraun).  Bookkeeping, not analysis. -/

#check (∀ {α W : Type*} [PseudoMetricSpace α]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    {u : α → W} {s : Set α} {K : ℝ≥0}, LipschitzOnWith K u s →
    ∃ (K' : ℝ≥0) (w : α → W), LipschitzWith K' w ∧ EqOn w u s)

/-! ### X2 — Lipschitz on every closed ball

A locally Lipschitz map on a proper space is Lipschitz on each closed ball.  Mathlib's
`LocallyLipschitzOn.exists_lipschitzOnWith_of_compact` on the compact closed ball; recorded because
`X5` cites it in this form. -/

#check (∀ {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    {u : V → W}, LocallyLipschitz u → ∀ r : ℝ, ∃ K : ℝ≥0, LipschitzOnWith K u (closedBall 0 r))

/-! ### X3 — the half-open annuli

`A k = ball 0 (k+1) \ ball 0 k` are measurable, pairwise disjoint, cover `V`, and each lies in the
open ball of radius `k + 1`, which is a neighbourhood of each of its points. -/

#check (∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V],
    (∀ k : ℕ, MeasurableSet (ball (0 : V) (k + 1) \ ball (0 : V) k)) ∧
    Pairwise (fun i j : ℕ =>
      Disjoint (ball (0 : V) (i + 1) \ ball (0 : V) i) (ball (0 : V) (j + 1) \ ball (0 : V) j)) ∧
    (⋃ k : ℕ, ball (0 : V) (k + 1) \ ball (0 : V) k) = univ ∧
    ∀ k : ℕ, ∀ x ∈ ball (0 : V) (k + 1) \ ball (0 : V) k, ball (0 : V) (k + 1) ∈ nhds x)

/-! ### X4 — agreement near a point transfers density and slice

If `u = v` on a neighbourhood of every point of a piece `P`, then `fderiv ℝ u = fderiv ℝ v` on `P`
(so the densities `coareaJacobian (fderiv ℝ · x)` agree) and `P ∩ {u = t} = P ∩ {v = t}` for every
`t`.  `Filter.EventuallyEq.fderiv_eq` and set extensionality. -/

#check (∀ {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {u v : V → W} {P : Set V} {O : Set V}, IsOpen O → P ⊆ O → EqOn u v O →
    (∀ x ∈ P, fderiv ℝ u x = fderiv ℝ v x) ∧ ∀ t : W, P ∩ {x | u x = t} = P ∩ {x | v x = t})

/-! ### X5 — the assembly: `L0` on each annulus, then countable additivity

The codimension-`m` copy of the `L13` proof, stated as an implication from `L0` (the globally
Lipschitz formula, itself open in `LipschitzVectorCoareaRouteStatements.lean`): on the piece
`S ∩ A k` apply `L0` to the extension `v k` of `X1`/`X2`, transport density and slice back to `u` by
`X4`, and sum over the disjoint measurable pieces with `lintegral_iUnion` and `lintegral_tsum`; the
slice measurability comes from the per-piece `AEMeasurable` through `AEMeasurable.tsum`, since a
locally Lipschitz `u` need not be Lipschitz on an unbounded `S`. -/

#check (∀ {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    [MeasurableSpace W] [BorelSpace W] {k : ℕ},
    k + finrank ℝ W = finrank ℝ V →
    (∀ {S : Set V} {u : V → W} {K : ℝ≥0} {g : V → ℝ≥0∞}, LipschitzWith K u →
      MeasurableSet S → Measurable g →
      AEMeasurable (fun t : W => ∫⁻ y in S ∩ {x : V | u x = t}, g y ∂(KLS.hausdorffNormalized V k))
          (volume : Measure W) ∧
        (∫⁻ x in S, ENNReal.ofReal (coareaJacobian (fderiv ℝ u x)) * g x ∂(volume : Measure V)
          = ∫⁻ t, ∫⁻ y in S ∩ {x : V | u x = t}, g y ∂(KLS.hausdorffNormalized V k)
              ∂(volume : Measure W))) →
    ∀ {S : Set V} {u : V → W} {g : V → ℝ≥0∞}, LocallyLipschitz u →
      MeasurableSet S → Measurable g →
      AEMeasurable (fun t : W => ∫⁻ y in S ∩ {x : V | u x = t}, g y ∂(KLS.hausdorffNormalized V k))
          (volume : Measure W) ∧
        (∫⁻ x in S, ENNReal.ofReal (coareaJacobian (fderiv ℝ u x)) * g x ∂(volume : Measure V)
          = ∫⁻ t, ∫⁻ y in S ∩ {x : V | u x = t}, g y ∂(KLS.hausdorffNormalized V k)
              ∂(volume : Measure W)))

/-! ### D1 — the strictness witness: a map that neither `L0` nor `R9` reaches

On the plane, `x ↦ ‖x‖² e₀ + ‖x‖ e₁` is locally Lipschitz (a `C¹` term plus a Lipschitz term), is
globally Lipschitz for **no** constant (the first coordinate is `‖x‖²`), and is not differentiable
at `0` (the second coordinate is `‖x‖`).  `N0` applies to it in codimension `2` with `k = 0`; `L0`
and `R9` do not.  A diagnostic, true and cheap, not a step. -/

#check (∃ u : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2),
    LocallyLipschitz u ∧ (∀ K : ℝ≥0, ¬ LipschitzWith K u) ∧ ¬ DifferentiableAt ℝ u 0)

/-! ### C1, C2 — consistency: `N0` recovers `L0` and `R9`, statement for statement

A globally Lipschitz map and a `C¹` map are locally Lipschitz, so `N0` implies the statements of `L0`
and `R9`.  These record that `N0` is the common generalization; they are not steps. -/

#check (∀ {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    {u : V → W} {K : ℝ≥0}, LipschitzWith K u → LocallyLipschitz u)

#check (∀ {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    {u : V → W}, ContDiff ℝ 1 u → LocallyLipschitz u)
