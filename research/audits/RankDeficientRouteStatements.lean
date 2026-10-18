import FunctionalInequalities.Analysis.Vector.Slice.Critical
import Mathlib.Analysis.InnerProductSpace.ProdL2
import FunctionalInequalities.KLS.BKL.Localization.Process.Basic
/-!
# Route statements for the rank-deficient part of the codimension-`m` critical set

**This file contains only `#check`s. A proposition that type-checks is not a proof.**
The anonymous propositions preserve the rank-deficient coarea contracts `R0`–`R10`, `N1` and `N2`.
Current source is in `Analysis/Vector/RankDeficient/`; independent clients include
`research/audits/RankStratificationAudit.lean` and `research/audits/RankDeficientCoareaAudit.lean`.
The route explanations below distinguish the vanishing-derivative argument from intermediate rank.

Same convention as `AreaFormulaRouteStatements.lean` and `WeightedCoareaRouteStatements.lean`.

## Regular and vanishing-derivative scope

`Analysis/Vector/Coarea/Regular.lean` proves the codimension-`m` coarea formula **where the
differential is surjective**.  `Analysis/Vector/Slice/Critical.lean` proves that almost every level
meets `{x | fderiv ℝ u x = 0}` in an `ℋ^k`-null set, and extends the coarea formula to the whole
space **under the hypothesis that the derivative vanishes wherever it fails to be surjective**.

For `m ≥ 2` that hypothesis is a genuine restriction: the coarea critical set is
`{x | fderiv ℝ u x` is not surjective`}`, where the rank drops below `m`, and it is strictly larger
than the vanishing-derivative set.  Everything below is about the difference — the **rank-deficient**
part, where the derivative is nonzero but not surjective.

## Why the vanishing-derivative method does not cover intermediate rank

The proved argument covers `{Du = 0}` because there Mathlib's approximating partition makes `u`
itself `ε`-Lipschitz on each piece: the approximating linear maps are values of the derivative,
which vanish, so the linear part drops out.  On a stratum of rank `r ≥ 1` the derivative does not
vanish and `u` is not `ε`-Lipschitz on any piece, in any direction inside the range of `Du`.

Only the `m − r` directions orthogonal to the range survive.  Composing with the orthogonal
projection `Q` onto them does give a map `Q ∘ u` that is `ε`-Lipschitz on the pieces, and the
Eilenberg inequality `exists_measurable_majorant_vector` applies to it — but with the **wrong
exponent**.  Its shape is

`∫⁻ τ, μH[d] (S ∩ {Q ∘ u = τ}) dτ ≤ C · ε ^ (m − r) · μH[d + (m − r)] S`,

so a finite right-hand side for `S` of positive Lebesgue measure forces `d + (m − r) = n`, that is
`d = k + r`, and the conclusion is about `μH[k + r]`, not `μH[k]`.  A `μH[k + r]`-null set can have
infinite `μH[k]`, so this is the wrong direction: `N1` below states exactly what the method yields.
Insisting on `d = k` instead makes the right-hand side `μH[k + (m − r)] S = μH[n − r] S`, which
`N2` below states is `∞` for every `r ≥ 1` once `S` has positive Lebesgue measure.  The bound is
then vacuous.

## The route: slice first along the `r` good directions

The exponent is repaired by applying the Eilenberg bound not in `V` but inside a fibre of the
`r`-dimensional **regular** part.  At a point of the rank-`r` stratum let `W₁` be the range of the
differential, `P` and `Q` the orthogonal projections of `W` onto `W₁` and `W₁ᗮ`.  Near that point
`v := P ∘ u` is a submersion onto `W₁`, so the **proved** regular coarea formula applies to it and
its fibres carry finite `ℋ^(n−r)` measure.  The linear-algebra content is `R2`: on the stratum the
differential kills the kernel of `P ∘ Du`, so `Q ∘ u` has vanishing derivative **along the fibre**.
Inside a fibre the Eilenberg bound is used with `d = k` and target `W₁ᗮ` of dimension `m − r`, and
now `d + (m − r) = k + m − r = n − r` is exactly the dimension in which the fibre has finite
measure.  This is an **iterated** slicing: first in codimension `r` by `v`, then in codimension
`m − r` by `Q ∘ u` inside each fibre.  `R6` puts the two levels back together by Fubini across the
orthogonal splitting of the target.

## What Mathlib and this repository have

The route uses `isOpen_setOfPred_nat_le_rank` (lower semicontinuity of rank),
`exists_partition_approximatesLinearOn_of_hasFDerivWithinAt`, `ApproximatesLinearOn`,
`addHaar_image_eq_zero_of_det_fderivWithin_eq_zero`, `Submodule.orthogonalDecomposition`,
`LinearIsometryEquiv.measurePreserving` and `WithLp.volume_preserving_ofLp`.
The repository's rank-stratum assembly and exponent diagnostics are in
`Analysis/Vector/RankDeficient/Coarea.lean` and
`Analysis/Vector/RankDeficient/ExponentObstruction.lean`.
-/

noncomputable section

open MeasureTheory Set Module FunctionalInequalities FunctionalInequalities.Analysis
open scoped ENNReal NNReal RealInnerProductSpace

/-! ### R0 — the target: the rank-deficient part of almost every level is null

The statement `Analysis/Vector/Slice/Critical.lean` proves with `{x | fderiv ℝ u x = 0}` in place of
the full critical set.  For `m = 1` the two agree and this is the proved scalar `L10`.

Unlike the proved vanishing-derivative statement, this one needs **no** `0 < finrank ℝ W`: a
zero-dimensional target makes every linear map surjective, so the critical set is empty and the
claim is vacuous rather than false.  The hypothesis is therefore not imposed here. -/

#check (∀ {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    [MeasurableSpace W] [BorelSpace W]
    {u : V → W} {k : ℕ}, ContDiff ℝ 1 u → k + finrank ℝ W = finrank ℝ V →
    ∀ᵐ t ∂(volume : Measure W),
      μH[(k : ℝ)] ({x : V | ¬ Function.Surjective (fderiv ℝ u x)} ∩ {x : V | u x = t}) = 0)

/-! ### R1 — the rank stratification is measurable, and finite

`{f | r ≤ rank f}` is open by Mathlib's `isOpen_setOfPred_nat_le_rank`, so each stratum is the
difference of two open sets.  The critical set is the union of the strata of rank `r < m`. -/

#check (∀ {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    {u : V → W}, ContDiff ℝ 1 u → ∀ r : ℕ,
    MeasurableSet {x : V | (fderiv ℝ u x).toLinearMap.rank = (r : Cardinal)})

#check (∀ {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    {u : V → W},
    {x : V | ¬ Function.Surjective (fderiv ℝ u x)}
      = ⋃ r ∈ Finset.range (finrank ℝ W),
          {x : V | (fderiv ℝ u x).toLinearMap.rank = (r : Cardinal)})

/-! ### R2 — the kernel lemma: on the stratum the differential dies along the fibre

Pure linear algebra, and the structural heart of the route.  If `P ∘ L` is already surjective onto
a space of the same dimension as the range of `L`, then `P` is injective on that range, so the two
kernels agree and `L` vanishes on the kernel of `P ∘ L` — the tangent space of the fibre of the
regular part. -/

#check (∀ {V W W₁ : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    [NormedAddCommGroup W₁] [InnerProductSpace ℝ W₁] [FiniteDimensional ℝ W₁]
    (L : V →L[ℝ] W) (P : W →L[ℝ] W₁), Function.Surjective (P.comp L) →
    finrank ℝ W₁ = finrank ℝ (LinearMap.range L.toLinearMap) →
    ∀ z : V, P (L z) = 0 → L z = 0)

/-! ### R3 — an approximate right inverse, pointwise and locally uniform

A chord of a fibre is not tangent to it; it is only **nearly** in the kernel of the differential,
and turning that into a quantitative statement needs a right inverse of the surjection.  The
constant must be uniform over the neighbourhood, because the limit `ε → 0` is taken with a
different approximating partition at every scale. -/

#check (∀ {V W₁ : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W₁] [InnerProductSpace ℝ W₁] [FiniteDimensional ℝ W₁]
    (L : V →L[ℝ] W₁), Function.Surjective L →
    ∃ C : ℝ≥0, ∀ z : V, ∃ w : V, L w = 0 ∧ ‖z - w‖ ≤ C * ‖L z‖)

#check (∀ {V W₁ : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W₁] [InnerProductSpace ℝ W₁] [FiniteDimensional ℝ W₁]
    {v : V → W₁} {O : Set V} {x₀ : V}, IsOpen O → x₀ ∈ O → ContDiffOn ℝ 1 v O →
    coareaJacobian (fderiv ℝ v x₀) ≠ 0 →
    ∃ U ∈ nhds x₀, ∃ C M : ℝ≥0, U ⊆ O ∧ ∀ x ∈ U,
      ‖fderiv ℝ v x‖₊ ≤ M ∧
        ∀ z : V, ∃ w : V, fderiv ℝ v x w = 0 ∧ ‖z - w‖ ≤ C * ‖fderiv ℝ v x z‖)

/-! ### R4 — the tangential small-Lipschitz estimate

The new analytic content, and the replacement for the step that fails in the rank-deficient case.
On a piece where `f` is `ε`-approximated by a single linear map `A` that satisfies `R2` and `R3`,
the projected map `Q ∘ f` is Lipschitz with constant proportional to `ε` **on each fibre of
`P ∘ f`** — even though `f` itself is not Lipschitz-small in any direction of the range of `A`.
The constant depends only on `‖A‖`, `‖P‖`, `‖Q‖` and the right-inverse bound, never on `ε`. -/

#check (∀ {V W W₁ W₂ : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    [NormedAddCommGroup W₁] [InnerProductSpace ℝ W₁] [FiniteDimensional ℝ W₁]
    [NormedAddCommGroup W₂] [InnerProductSpace ℝ W₂] [FiniteDimensional ℝ W₂]
    (A : V →L[ℝ] W) (P : W →L[ℝ] W₁) (Q : W →L[ℝ] W₂) (C : ℝ≥0),
    (∀ z : V, P (A z) = 0 → A z = 0) →
    (∀ z : V, ∃ w : V, P (A w) = 0 ∧ ‖z - w‖ ≤ C * ‖P (A z)‖) →
    ∃ c : ℝ≥0, ∀ (ε : ℝ≥0) (f : V → W) (S : Set V) (s : W₁),
      ApproximatesLinearOn f A S ε →
        LipschitzOnWith (c * ε) (fun x => Q (f x)) (S ∩ {x : V | P (f x) = s}))

/-! ### R5 — the fibres of the regular part carry finite `ℋ^(n−r)` measure

This is what makes the Eilenberg right-hand side finite at the repaired exponent.  It is a
corollary of the **proved** regular coarea formula
`coarea_of_contDiffOn_of_coareaJacobian_ne_zero` with weight `1`: the total integral is finite on a
relatively compact piece, so the fibre measure is finite at almost every level. -/

#check (∀ {V W₁ : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    [NormedAddCommGroup W₁] [InnerProductSpace ℝ W₁] [FiniteDimensional ℝ W₁]
    [MeasurableSpace W₁] [BorelSpace W₁]
    {O S : Set V} {v : V → W₁}, IsOpen O → ContDiffOn ℝ 1 v O →
    (∀ x ∈ O, coareaJacobian (fderiv ℝ v x) ≠ 0) → MeasurableSet S →
    IsCompact (closure S) → closure S ⊆ O →
    ∀ᵐ s ∂(volume : Measure W₁),
      μH[((finrank ℝ V - finrank ℝ W₁ : ℕ) : ℝ)] (S ∩ {x : V | v x = s}) ≠ ⊤)

/-! ### R6 — Fubini across the orthogonal splitting of the target

The two slicings produce "for almost every `s ∈ W₁`, for almost every `τ ∈ W₁ᗮ`"; the conclusion
is about almost every `t ∈ W`.  Mathlib supplies `Submodule.orthogonalDecomposition`,
`LinearIsometryEquiv.measurePreserving` and `WithLp.volume_preserving_ofLp`, so this is
the measure-theoretic transport contract. See `Analysis/Vector/RankDeficient/TargetSplitFubini.lean`. -/

#check (∀ {W W₁ W₂ : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    [MeasurableSpace W] [BorelSpace W]
    [NormedAddCommGroup W₁] [InnerProductSpace ℝ W₁] [FiniteDimensional ℝ W₁]
    [MeasurableSpace W₁] [BorelSpace W₁]
    [NormedAddCommGroup W₂] [InnerProductSpace ℝ W₂] [FiniteDimensional ℝ W₂]
    [MeasurableSpace W₂] [BorelSpace W₂]
    (e : W ≃ₗᵢ[ℝ] WithLp 2 (W₁ × W₂)) (N : Set W), MeasurableSet N →
    (∀ᵐ s ∂(volume : Measure W₁),
        (volume : Measure W₂) {τ : W₂ | e.symm (WithLp.toLp 2 (s, τ)) ∈ N} = 0) →
    (volume : Measure W) N = 0)

/-! ### R7 — the local per-stratum slicing: the assembly of `R1`–`R6`

The hard step.  Only points **of the stratum** are reachable: the choice of `W₁` is the range of
the differential there, and at a point of lower rank no fixed `P` of rank `r` works, however close
the stratum comes.  That is enough, because `R8` only has to cover the set being sliced.

Near each point of the stratum the projections `P` and `Q` are fixed, the approximating partition
is taken for `u` itself so that one partition serves both components, `R4` gives the small
tangential Lipschitz constant on each fibre piece, `R5` the finite measure at the repaired
exponent, and the codimension-`(m − r)` Eilenberg bound of `Analysis/Vector/Slice/Hausdorff.lean`
finishes as `ε → 0`. -/

#check (∀ {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    [MeasurableSpace W] [BorelSpace W]
    {u : V → W} {k r : ℕ}, ContDiff ℝ 1 u → k + finrank ℝ W = finrank ℝ V →
    r < finrank ℝ W →
    ∀ x₀ ∈ {x : V | (fderiv ℝ u x).toLinearMap.rank = (r : Cardinal)}, ∃ U ∈ nhds x₀,
      ∀ᵐ t ∂(volume : Measure W),
        μH[(k : ℝ)] ({x : V | (fderiv ℝ u x).toLinearMap.rank = (r : Cardinal)} ∩ U
          ∩ {x : V | u x = t}) = 0)

/-! ### R8 — localization: a local null-slicing statement patches to a global one

`V` is second countable, so a neighbourhood family has a countable subcover and the almost-every
quantifier survives a countable intersection.  With `R7` and `R1` this gives `R0`. -/

#check (∀ {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    [MeasurableSpace W] [BorelSpace W]
    {u : V → W} {A : Set V} {k : ℕ},
    (∀ x₀ ∈ A, ∃ U ∈ nhds x₀, ∀ᵐ t ∂(volume : Measure W),
        μH[(k : ℝ)] (A ∩ U ∩ {x : V | u x = t}) = 0) →
    ∀ᵐ t ∂(volume : Measure W), μH[(k : ℝ)] (A ∩ {x : V | u x = t}) = 0)

/-! ### R9 — the consumer: the codimension-`m` coarea formula with no dichotomy hypothesis

Exactly `Analysis.coarea_of_contDiff_of_critical_eq_zeroDeriv` with its hypothesis
`∀ x, coareaJacobian (fderiv ℝ u x) ≠ 0 ∨ fderiv ℝ u x = 0` deleted.  Given `R0` its proof is the
proved one verbatim.  The remaining `0 < finrank ℝ W` is kept exactly as the proved conditional
theorem carries it, and is not an addition; the `m = 0` case is separately trivial. -/

#check (∀ {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    [MeasurableSpace W] [BorelSpace W]
    {S : Set V} {u : V → W} {g : V → ℝ≥0∞} {k : ℕ},
    k + finrank ℝ W = finrank ℝ V → 0 < finrank ℝ W → ContDiff ℝ 1 u →
    MeasurableSet S → Measurable g →
    AEMeasurable (fun t : W => ∫⁻ y in S ∩ {x : V | u x = t}, g y ∂(KLS.hausdorffNormalized V k))
        (volume : Measure W) ∧
      (∫⁻ x in S, ENNReal.ofReal (coareaJacobian (fderiv ℝ u x)) * g x ∂(volume : Measure V)
        = ∫⁻ t, ∫⁻ y in S ∩ {x : V | u x = t}, g y ∂(KLS.hausdorffNormalized V k)
            ∂(volume : Measure W)))

/-! ### R10 — the equidimensional degenerate case, independent of `R1`–`R8`

When `n = m` the fibre dimension is `k = 0` and `μH[0]`-nullity of a slice means the slice is
**empty**, so the statement is that almost no level is a critical value.  Mathlib's
`addHaar_image_eq_zero_of_det_fderivWithin_eq_zero` gives it directly, transported along the
repository's `isometryEquivOfFinrankEq`; this is the one obligation on the list that is cheap.
It is a sanity check on `R0`, not a step towards it: the route above is empty when `r` ranges over
`r < m` with `n = m`, since it still has to cover every intermediate rank. -/

#check (∀ {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    [MeasurableSpace W] [BorelSpace W]
    {u : V → W}, ContDiff ℝ 1 u → finrank ℝ V = finrank ℝ W →
    ∀ᵐ t ∂(volume : Measure W),
      {x : V | ¬ Function.Surjective (fderiv ℝ u x)} ∩ {x : V | u x = t} = ∅)

/-! ### N1 — the obstruction, stated: what the small-Lipschitz method actually yields

Projecting away the range of the differential and running the proved Eilenberg bound gives a null
slicing statement at exponent `n − dim W₂ = k + r`, **not** `k`.  For `r ≥ 1` this is strictly
weaker than `R0` in the useless direction: a set can be `μH[k + r]`-null and have infinite
`μH[k]`.

Both side conditions are real: `S` must be measurable for the majorants of the disjoint pieces to
add up, and `0 < finrank ℝ W₂` is what makes the Eilenberg constant `ε ^ (dim W₂)` tend to `0` —
with `r = m` there is nothing left to project onto and the statement is false. -/

#check (∀ {V W W₂ : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    [NormedAddCommGroup W₂] [InnerProductSpace ℝ W₂] [FiniteDimensional ℝ W₂]
    [MeasurableSpace W₂] [BorelSpace W₂]
    {u : V → W} {S : Set V} (Q : W →L[ℝ] W₂),
    MeasurableSet S → 0 < finrank ℝ W₂ → μH[((finrank ℝ V : ℕ) : ℝ)] S ≠ ⊤ →
    (∀ ε : ℝ≥0, ε ≠ 0 → ∃ T : ℕ → Set V, Pairwise (Function.onFun Disjoint T) ∧
        (∀ n, MeasurableSet (T n)) ∧ S ⊆ ⋃ n, T n ∧
        ∀ n, LipschitzOnWith ε (fun x => Q (u x)) (S ∩ T n)) →
    ∀ᵐ τ ∂(volume : Measure W₂),
      μH[((finrank ℝ V - finrank ℝ W₂ : ℕ) : ℝ)] (S ∩ {x : V | Q (u x) = τ}) = 0)

/-! ### N2 — the obstruction, quantified: the exponent cannot simply be lowered

Running the same bound at the exponent `k` that `R0` needs puts `μH[k + (m − r)] S = μH[n − r] S`
on the right-hand side, and for `r ≥ 1` that is `∞` as soon as `S` has positive Lebesgue measure.
The bound is then vacuous, which is why the slicing has to be iterated instead. -/

#check (∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] {S : Set V} {r : ℕ},
    (volume : Measure V) S ≠ 0 → 0 < r → μH[((finrank ℝ V - r : ℕ) : ℝ)] S = ⊤)
