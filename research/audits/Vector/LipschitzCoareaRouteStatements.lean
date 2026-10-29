import FunctionalInequalities.Analysis.Vector.RankDeficient.Coarea
import FunctionalInequalities.Analysis.Lipschitz.C1Pieces
import FunctionalInequalities.Analysis.Vector.Slice.Hausdorff
import FunctionalInequalities.Analysis.Coarea.LocallyLipschitz

/-!
# Route statements for the codimension-`m` coarea formula of Lipschitz maps

**This file contains only `#check`s. A proposition that type-checks is not a proof.**
It preserves the Lipschitz vector-coarea contracts `L0`, `V1`–`V5` and the boundary/follow-on items.
Current sources are `Analysis/Lipschitz/VectorPieces.lean` and
`Analysis/Vector/Coarea/Lipschitz.lean`; the independent client is
`research/audits/Vector/LipschitzCoareaAudit.lean`.
Same convention as `research/audits/Sard/SharpRouteStatements.lean` and `RankDeficientRouteStatements.lean`.

## The regularity distinction

`Analysis/Vector/RankDeficient/Coarea.lean` proves the codimension-`m` coarea formula `coarea_of_contDiff`
for **`C¹`** maps with no hypothesis on the critical set.  Federer's coarea formula holds for merely
**Lipschitz** maps, and the scalar side already went the whole way `C¹ → Lipschitz → locally
Lipschitz` (`Analysis/Coarea/Smooth.lean`, `Analysis/Coarea/Lipschitz.lean`,
`Analysis/Coarea/LocallyLipschitz.lean`). The vector globally Lipschitz contract is `L0` below.

## Scalar assembly and its vector counterpart

The scalar Lipschitz formula `KLS.coarea_of_lipschitz` has three steps:
`Analysis.exists_contDiff_pieces` cuts the domain into countably many disjoint measurable pieces
carrying `C¹` functions that agree with `u` **to first order** (value and derivative) and leave a
Lebesgue-null complement; the `C¹` formula applies on each piece, first-order agreement making
density and slice agree; countable additivity sums the pieces and the null complement is removed
from almost every level.

In codimension `m` the assembly uses `coarea_of_contDiff`, the codimension-`m` null slicing
`ae_hausdorffMeasure_inter_levelSet_eq_zero_vector`, and vector `C¹` pieces. The scalar jet
and Whitney chain behind the scalar pieces (`LipschitzJet.exists_compact_jets`,
`WhitneyJet.exists_contDiff_extension`, `exists_contDiff_pieces`) is stated for `u : V → ℝ`.
**`V1` is its componentwise vector counterpart.**

## The route for `V1`: componentwise, not a vector Whitney extension

Against a fixed linear isometry `e : W ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin m)`, each coordinate
`fun y => e (u y) i` is a scalar Lipschitz function (`V4'`) and gets its own countable partition
from the proved `exists_contDiff_pieces`; `V3` takes a countable common refinement of the `m`
partitions (`ℕ ^ m` is countable, the complement is a finite union of null sets); on a common piece
every coordinate agrees to first order with a `C¹` scalar function, and `V4` upgrades this to
first-order agreement of `u` with the `C¹` vector map assembled through `e.symm`.  No new analysis:
bookkeeping and calculus.  `V5` is then the codimension-`m` copy of the scalar Lipschitz assembly,
stated as an implication so the route closes by supplying `V1` alone.

## What Mathlib and this repository have

The route uses Rademacher's theorem, `exists_contDiff_pieces` for real-valued
functions, the `C¹` codimension-`m` coarea formula, codimension-`m` null slicing in the shape
`V2` needs, and unconditional slice measurability.
-/

noncomputable section

open MeasureTheory Set Module FunctionalInequalities FunctionalInequalities.Analysis
open scoped ENNReal NNReal

/-! ### Proved inputs, for reference

The scalar `C¹` pieces, the `C¹` codimension-`m` formula, the scalar Lipschitz and locally
Lipschitz formulas, and the codimension-`m` null slicing. -/

#check @FunctionalInequalities.Analysis.exists_contDiff_pieces
#check @FunctionalInequalities.Analysis.coarea_of_contDiff
#check @FunctionalInequalities.KLS.coarea_of_lipschitz
#check @FunctionalInequalities.KLS.coarea_of_locallyLipschitz
#check @FunctionalInequalities.Analysis.ae_hausdorffMeasure_inter_levelSet_eq_zero_vector

/-! ### L0 — the target: the codimension-`m` coarea formula for Lipschitz maps

Exactly `coarea_of_contDiff` with `ContDiff ℝ 1 u` replaced by `LipschitzWith K u`.  The density
`coareaJacobian (fderiv ℝ u x)` is unchanged: `fderiv` is junk off the differentiability set, which
is Lebesgue-null by Rademacher, so the integrand is unaffected almost everywhere — the convention
the scalar `KLS.coarea_of_lipschitz` uses for `gradient`.  No positivity of the codimension is
required. -/

#check (∀ {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    [MeasurableSpace W] [BorelSpace W]
    {S : Set V} {u : V → W} {K : ℝ≥0} {g : V → ℝ≥0∞} {k : ℕ},
    k + finrank ℝ W = finrank ℝ V → LipschitzWith K u →
    MeasurableSet S → Measurable g →
    AEMeasurable (fun t : W => ∫⁻ y in S ∩ {x : V | u x = t}, g y ∂(KLS.hausdorffNormalized V k))
        (volume : Measure W) ∧
      (∫⁻ x in S, ENNReal.ofReal (coareaJacobian (fderiv ℝ u x)) * g x ∂(volume : Measure V)
        = ∫⁻ t, ∫⁻ y in S ∩ {x : V | u x = t}, g y ∂(KLS.hausdorffNormalized V k)
            ∂(volume : Measure W)))

/-! ### V1 — the vector `C¹` pieces

`exists_contDiff_pieces` verbatim with target `W`.  Agreement is to first order, value and
derivative, which is what transfers density and slice to the piece. -/

#check (∀ {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    {u : V → W} {K : ℝ≥0}, LipschitzWith K u →
    ∃ (S : ℕ → Set V) (v : ℕ → V → W),
      (∀ j, MeasurableSet (S j)) ∧ Pairwise (fun i j => Disjoint (S i) (S j)) ∧
      (volume : Measure V) (⋃ j, S j)ᶜ = 0 ∧ (∀ j, ContDiff ℝ 1 (v j)) ∧
      ∀ j, ∀ x ∈ S j, DifferentiableAt ℝ u x ∧
        v j x = u x ∧ fderiv ℝ (v j) x = fderiv ℝ u x)

/-! ### V2 — the Lebesgue-null complement disappears from almost every level

The derivation uses `ae_hausdorffMeasure_inter_levelSet_eq_zero_vector` at
`d = k`, whose hypothesis `μH[k + m] N = 0` is, under `k + m = n`, Lebesgue-nullity of `N` through
`Analysis.hausdorffMeasure_finrank_eq_smul_volume`; the normalized fibre measure is a scalar
multiple of `μH[k]`. See `route_V2` in `research/audits/Vector/LipschitzCoareaAudit.lean`. -/

#check (∀ {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    [MeasurableSpace W] [BorelSpace W]
    {u : V → W} {N : Set V} {K : ℝ≥0} {k : ℕ},
    k + finrank ℝ W = finrank ℝ V → LipschitzWith K u → (volume : Measure V) N = 0 →
    ∀ᵐ t ∂(volume : Measure W), KLS.hausdorffNormalized V k (N ∩ {x : V | u x = t}) = 0)

/-! ### V3 — a countable common refinement of finitely many countable partitions

Each of the `m` coordinates gets its own partition from `exists_contDiff_pieces`; the vector
statement needs one partition on which all coordinates agree at once.  `ℕ ^ m` is countable, so the
refinement is again indexed by `ℕ`; its complement is contained in the union of the `m` null
complements. -/

#check (∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    (m : ℕ) (S : Fin m → ℕ → Set V),
    (∀ i j, MeasurableSet (S i j)) →
    (∀ i, Pairwise (fun a b => Disjoint (S i a) (S i b))) →
    (∀ i, (volume : Measure V) (⋃ j, S i j)ᶜ = 0) →
    ∃ T : ℕ → Set V, (∀ n, MeasurableSet (T n)) ∧
      Pairwise (fun a b => Disjoint (T a) (T b)) ∧
      (volume : Measure V) (⋃ n, T n)ᶜ = 0 ∧
      ∀ n, ∃ f : Fin m → ℕ, T n ⊆ ⋂ i, S i (f i))

/-! ### V4' — the coordinates of a Lipschitz map are Lipschitz

Through a linear isometry equivalence onto `EuclideanSpace ℝ (Fin m)`, each coordinate is
`1`-Lipschitz in the vector, so `K`-Lipschitz in `y`.  This is what feeds the scalar
`exists_contDiff_pieces`. -/

#check (∀ {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    (e : W ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ W))) {u : V → W} {K : ℝ≥0},
    LipschitzWith K u → ∀ i, LipschitzWith K (fun y => e (u y) i))

/-! ### V4 — componentwise first-order agreement is first-order agreement

If `u` and `v` are differentiable at `x` and every coordinate of `v` matches the corresponding
coordinate of `u` in value and in derivative at `x`, then `v x = u x` and
`fderiv ℝ v x = fderiv ℝ u x`.  Pure calculus against the fixed isometry; the `C¹` vector map of `V1`
is `e.symm` of the `C¹` scalar representatives, so its differentiability is free. -/

#check (∀ {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    (e : W ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ W))) {u v : V → W} {x : V},
    DifferentiableAt ℝ u x → DifferentiableAt ℝ v x →
    (∀ i, e (v x) i = e (u x) i) →
    (∀ i, fderiv ℝ (fun y => e (v y) i) x = fderiv ℝ (fun y => e (u y) i) x) →
    v x = u x ∧ fderiv ℝ v x = fderiv ℝ u x)

/-! ### V4'' — differentiability is detected coordinatewise

The differentiability of `u` at `x` in `V1` comes from the conclusions of the scalar
`exists_contDiff_pieces` on each coordinate; this is the converse direction of the standard
`differentiableAt_pi` through `e`. -/

#check (∀ {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    (e : W ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ W))) {u : V → W} {x : V},
    (∀ i, DifferentiableAt ℝ (fun y => e (u y) i) x) → DifferentiableAt ℝ u x)

/-! ### V5 — the assembly: countable additivity over the pieces

The codimension-`m` copy of the proof of the scalar `KLS.coarea_of_lipschitz`: on each piece
`coarea_of_contDiff` applies to `v j`; first-order agreement makes its density and its slice
coincide with those of `u` there; the pieces are disjoint and measurable, so both sides add up;
`V2` deletes the complement.  Stated as an implication from the conclusion of `V1`, so
`L0 = V5 ∘ V1`. -/

#check (∀ {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    [MeasurableSpace W] [BorelSpace W]
    {S : Set V} {u : V → W} {K : ℝ≥0} {g : V → ℝ≥0∞} {k : ℕ},
    k + finrank ℝ W = finrank ℝ V → LipschitzWith K u →
    MeasurableSet S → Measurable g →
    (∃ (P : ℕ → Set V) (v : ℕ → V → W),
      (∀ j, MeasurableSet (P j)) ∧ Pairwise (fun i j => Disjoint (P i) (P j)) ∧
      (volume : Measure V) (⋃ j, P j)ᶜ = 0 ∧ (∀ j, ContDiff ℝ 1 (v j)) ∧
      ∀ j, ∀ x ∈ P j, DifferentiableAt ℝ u x ∧
        v j x = u x ∧ fderiv ℝ (v j) x = fderiv ℝ u x) →
    AEMeasurable (fun t : W => ∫⁻ y in S ∩ {x : V | u x = t}, g y ∂(KLS.hausdorffNormalized V k))
        (volume : Measure W) ∧
      (∫⁻ x in S, ENNReal.ofReal (coareaJacobian (fderiv ℝ u x)) * g x ∂(volume : Measure V)
        = ∫⁻ t, ∫⁻ y in S ∩ {x : V | u x = t}, g y ∂(KLS.hausdorffNormalized V k)
            ∂(volume : Measure W)))

/-! ### M1 — the obstruction, stated: the `C¹` formula does not apply to a Lipschitz map

A Lipschitz map need not be `C¹`, so `coarea_of_contDiff` cannot be invoked directly; `|·|` on the
line is the witness.  This is the whole reason `V1` is needed. -/

#check (¬ ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    {u : V → ℝ} {K : ℝ≥0}, LipschitzWith K u → ContDiff ℝ 1 u)

/-! ### M2 — the follow-on, stated but outside this route

The scalar theory continues to **locally** Lipschitz maps (`KLS.coarea_of_locallyLipschitz`, by
McShane representatives on closed balls).  Recorded so the boundary is explicit: `L0` is the globally
Lipschitz statement, and this one is **not** an obligation of this route. -/

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
