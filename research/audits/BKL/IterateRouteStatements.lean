import FunctionalInequalities.KLS.BKL.PoissonIterate.Basic
import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Hessian
import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Tilt
import FunctionalInequalities.KLS.LogConcave.Regular.Basic

/-!
# Route statements: the BKL iterates in `D(A)` and Theorem 3.1

This file contains only `#check`s. A proposition that type-checks is not a proof. These are the
obligations of `research/handoffs/2026-10-07-eight-hour-bkl-operator-route.md` for
Bizeul–Klartag–Lehec (arXiv:2610.05474v1), Section 3, in the operator route of
`research/decisions/2026-10-07-bkl-operator-route.md`.

Common premises of `I*`–`J*`: the heat model `ν = m.tilted (-U)` with `U` of temperate growth, all
exponential moments, `a ‖v‖² ≤ ∇²U` (`a` may be any real number unless `0 < a` is stated),
`C_P(ν) ≤ C` with `0 < C` (so `λ = 1/C ≤ λ₁`), and a centered `f ∈ D(A)`. `iter T̄ f k` is the
source's `h_{k+1}` (see `PoissonIterate/Basic.lean` for the conventions).

* `I1`–`I8`: the iterates (target 1): domain, (30), (33), (46), (35)–(36), (32), (47), Lemma 3.4,
  Corollary 3.5, Lemma 3.2.
* `S1`–`S2`: Lemma 3.3 for every `q` with `α² ≤ β/C`, and Corollary 3.7 (target 2).
* `J1`–`J2`: Lemma 3.8 and Lemma 3.9 in the route form (target 3).
* `M`: Theorem 3.1, the exact source statement for regular laws (target 4).
-/

noncomputable section

open MeasureTheory Filter Topology FunctionalInequalities
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Analysis.Tensor FunctionalInequalities.KLS.LogConcave.PoissonIterate
open scoped ENNReal NNReal RealInnerProductSpace InnerProductSpace ContDiff

section HeatModel

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : ProbabilityMeasure V} (m : Measure V) [m.IsAddHaarMeasure] (hν : KLS.LogConcave ν)
  (hi : (interior (ν : Measure V).support).Nonempty) {U : V → ℝ}

local notation "T̄" => hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi

/-! ## `I1`: domain and centering of every component; `I2`: the Poisson relation (30) -/

#check ((ν : Measure V) = m.tilted (-U) → ContDiff ℝ 2 U →
    ∀ {C : NNReal}, Poincare.LocalSlope.Intrinsic.constant ν ≤ (C : ENNReal) →
    ∀ (f : Lp ℝ 2 (ν : Measure V)), f ∈ (adjointComp T̄).domain → L2.mean ν f = 0 →
    ∀ k I, iter T̄ f k I ∈ (adjointComp T̄).domain ∧ L2.mean ν (iter T̄ f k I) = 0)

#check ((ν : Measure V) = m.tilted (-U) → ContDiff ℝ 2 U →
    ∀ {C : NNReal}, Poincare.LocalSlope.Intrinsic.constant ν ≤ (C : ENNReal) →
    ∀ (f : Lp ℝ 2 (ν : Measure V)), f ∈ (adjointComp T̄).domain → L2.mean ν f = 0 →
    ∀ k, genField T̄ (iter T̄ f (k + 1)) = scale T̄ (iter T̄ f k) • grad0 T̄ (iter T̄ f k))

/-! ## `I3`: the normalization (33), `(46)`, the energy drop (35)–(36) and (32) -/

#check ((ν : Measure V) = m.tilted (-U) → ContDiff ℝ 2 U →
    ∀ {C : NNReal}, 0 < C → Poincare.LocalSlope.Intrinsic.constant ν ≤ (C : ENNReal) →
    ∀ (f : Lp ℝ 2 (ν : Measure V)), f ∈ (adjointComp T̄).domain → L2.mean ν f = 0 →
    ∀ k, energy T̄ (iter T̄ f (k + 1)) = normSq (grad0 T̄ (iter T̄ f k)) ∧
      normSq (genField T̄ (iter T̄ f (k + 1))) =
        scale T̄ (iter T̄ f k) ^ 2 * energy T̄ (iter T̄ f (k + 1)) ∧
      energy T̄ (iter T̄ f k) - energy T̄ (iter T̄ f (k + 1)) = meanGradSq T̄ (iter T̄ f k) ∧
      (0 < scale T̄ (iter T̄ f k) → (C : ℝ)⁻¹ ≤ scale T̄ (iter T̄ f k) ^ 2))

/-! ## `I4`: the Pythagorean identity (47) and `I5`: Lemma 3.4 -/

#check ((ν : Measure V) = m.tilted (-U) → U.HasTemperateGrowth →
    (∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (ν : Measure V)) →
    ∀ {C : NNReal}, 0 < C → Poincare.LocalSlope.Intrinsic.constant ν ≤ (C : ENNReal) →
    ∀ (f : Lp ℝ 2 (ν : Measure V)), f ∈ (adjointComp T̄).domain → L2.mean ν f = 0 →
    ∀ k, normSq (gradField T̄ (gradField T̄ (iter T̄ f k))) =
      normSq (genField T̄ (iter T̄ f (k + 1))) + defect T̄ (iter T̄ f k))

#check ((ν : Measure V) = m.tilted (-U) → U.HasTemperateGrowth →
    (∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (ν : Measure V)) →
    ∀ {a : ℝ}, (∀ x v, a * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ U x v v) →
    ∀ {C : NNReal}, 0 < C → Poincare.LocalSlope.Intrinsic.constant ν ≤ (C : ENNReal) →
    ∀ (f : Lp ℝ 2 (ν : Measure V)), f ∈ (adjointComp T̄).domain → L2.mean ν f = 0 →
    ∀ k, normSq (genField T̄ (iter T̄ f (k + 1))) + defect T̄ (iter T̄ f k) +
        a * energy T̄ (iter T̄ f k) ≤ normSq (genField T̄ (iter T̄ f k)))

/-! ## `I6`: Corollary 3.5 and the summed defects; `I7`: the identity (36) -/

#check ((ν : Measure V) = m.tilted (-U) → U.HasTemperateGrowth →
    (∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (ν : Measure V)) →
    ∀ {a : ℝ}, 0 < a → (∀ x v, a * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ U x v v) →
    ∀ {C : NNReal}, 0 < C → Poincare.LocalSlope.Intrinsic.constant ν ≤ (C : ENNReal) →
    ∀ (f : Lp ℝ 2 (ν : Measure V)), f ∈ (adjointComp T̄).domain → L2.mean ν f = 0 →
    Tendsto (fun k => energy T̄ (iter T̄ f k)) atTop (𝓝 0) ∧
      ∀ N, ∑ k ∈ Finset.range N, defect T̄ (iter T̄ f k) ≤ normSq (genField T̄ (iter T̄ f 0)))

#check ((ν : Measure V) = m.tilted (-U) → ContDiff ℝ 2 U →
    ∀ {C : NNReal}, 0 < C → Poincare.LocalSlope.Intrinsic.constant ν ≤ (C : ENNReal) →
    ∀ (f : Lp ℝ 2 (ν : Measure V)), f ∈ (adjointComp T̄).domain → L2.mean ν f = 0 →
    ∀ N, energy T̄ (iter T̄ f 0) =
      energy T̄ (iter T̄ f N) + ∑ k ∈ Finset.range N, meanGradSq T̄ (iter T̄ f k))

/-! ## `I8`: Lemma 3.2, with `λ = 1/C`: `∇₀h_{i+1}` is within `C χ_i` of a field symmetric in its
first two index positions -/

#check ((ν : Measure V) = m.tilted (-U) → U.HasTemperateGrowth →
    (∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (ν : Measure V)) →
    ∀ {C : NNReal}, 0 < C → Poincare.LocalSlope.Intrinsic.constant ν ≤ (C : ENNReal) →
    ∀ (f : Lp ℝ 2 (ν : Measure V)), f ∈ (adjointComp T̄).domain → L2.mean ν f = 0 →
    ∀ k, ∃ S : Field ν (k + 2), (∀ J, S (J ∘ Equiv.swap 0 1) = S J) ∧
      normSq (grad0 T̄ (iter T̄ f (k + 1)) - S) ≤ (C : ℝ) * defect T̄ (iter T̄ f k))

/-! ## `S1`: Lemma 3.3 for every `q`, under `0 < α_j² ≤ β/C` on the relevant steps

The source's `2 ≤ q ≤ i` and `i - q + 2 ≤ j ≤ i` become `2 ≤ q ≤ k + 1` and
`k + 1 - q ≤ m < k` for `α_j = scale (iter (j - 2))`; the defects `χ_j`,
`i - q + 1 ≤ j ≤ i - 1`, are `defect (iter m)`, `k + 1 - q ≤ m < k`. -/

#check ((ν : Measure V) = m.tilted (-U) → U.HasTemperateGrowth →
    (∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (ν : Measure V)) →
    ∀ {C : NNReal}, 0 < C → Poincare.LocalSlope.Intrinsic.constant ν ≤ (C : ENNReal) →
    ∀ (f : Lp ℝ 2 (ν : Measure V)), f ∈ (adjointComp T̄).domain → L2.mean ν f = 0 →
    ∀ {β : ℝ} (k q : ℕ), 2 ≤ q → q ≤ k + 1 →
      (∀ j, k + 1 - q ≤ j → j < k →
        0 < scale T̄ (iter T̄ f j) ∧ scale T̄ (iter T̄ f j) ^ 2 ≤ β / C) →
      normSq (grad0 T̄ (iter T̄ f k) - symField q (grad0 T̄ (iter T̄ f k))) ≤
        4 * (q : ℝ) ^ 4 * max 1 β ^ q * C *
          ∑ j ∈ Finset.Ico (k + 1 - q) k, defect T̄ (iter T̄ f j))

/-! ## `S2`: Corollary 3.7, `S_{d+1} T_d(∇₀h_{i+1}) = α_{i+1} T_{d+1}(∇₀h_i)` for `d ≥ 1` (for
`d = 0` the left side is `∫ ∇₀h = 0`), with the index positions of the two coefficient arrays
identified by `Fin.cast` -/

#check ((ν : Measure V) = m.tilted (-U) → U.HasTemperateGrowth →
    (∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (ν : Measure V)) →
    ∀ {C : NNReal}, Poincare.LocalSlope.Intrinsic.constant ν ≤ (C : ENNReal) →
    ∀ (f : Lp ℝ 2 (ν : Measure V)), f ∈ (adjointComp T̄).domain → L2.mean ν f = 0 →
    ∀ (k d : ℕ), 1 ≤ d → ∀ (J : Fin (d + 1 + (k + 1)) → Fin (Module.finrank ℝ V)),
      symmetrize (Module.finrank ℝ V) (d + (k + 2)) (d + 1)
          (taylorField d (grad0 T̄ (iter T̄ f (k + 1)))) (J ∘ Fin.cast (by omega)) =
        scale T̄ (iter T̄ f k) * taylorField (d + 1) (grad0 T̄ (iter T̄ f k)) J)

/-! ## `J1`: Lemma 3.8, with hypothesis (29) componentwise and `α_j² ≤ β/C` for all earlier steps,
with the explicit constant `c = 2^20 max(1, β)²` (from (57)–(59), Lemma 2.2 and `S1` with `q = 2d`),
which does not depend on the measure

The source's `2d ≤ i ≤ N` with `i = k + 1`; `∇₀h_{i-d}` is `grad0 (iter (k - d))`; the defects are
`defect (iter j)`, `k + 1 - 2d ≤ j < k`. -/

#check ((ν : Measure V) = m.tilted (-U) → U.HasTemperateGrowth →
    (∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (ν : Measure V)) →
    ∀ {C : NNReal}, 0 < C → Poincare.LocalSlope.Intrinsic.constant ν ≤ (C : ENNReal) →
    ∀ {R : ℝ}, 1 ≤ R →
    (∀ (u : Lp ℝ 2 (ν : Measure V)) (d : ℕ), 1 ≤ d →
      ‖coordTensor (stdOrthonormalBasis ℝ V) (taylorTensor (ν : Measure V) (⇑u) d)‖ ≤
        R ^ d * ‖u‖) →
    ∀ (f : Lp ℝ 2 (ν : Measure V)), f ∈ (adjointComp T̄).domain → L2.mean ν f = 0 →
    ∀ {β : ℝ} (k d : ℕ), 1 ≤ d → 2 * d ≤ k + 1 →
      (∀ j < k, 0 < scale T̄ (iter T̄ f j) ∧ scale T̄ (iter T̄ f j) ^ 2 ≤ β / C) →
      ‖taylorField d (grad0 T̄ (iter T̄ f k))‖ ^ 2 ≤
        (2 ^ 20 * max 1 β ^ 2 / C) ^ d *
            ‖taylorField (2 * d) (grad0 T̄ (iter T̄ f (k - d)))‖ ^ 2 +
          (2 ^ 20 * max 1 β ^ 2) ^ d * R ^ (2 * d) * C *
            ∑ j ∈ Finset.Ico (k + 1 - 2 * d) k, defect T̄ (iter T̄ f j))

/-! ## `J2`: Lemma 3.9 in the route form, for a centered law with `Cov ν ≤ Id`:
`Σ_{k<N} p_k ≤ ‖L h₁‖² + (β/C) Σ_{k<N-1} |T₁(∇₀h_{k+1})|²` -/

#check ((ν : Measure V) = m.tilted (-U) → U.HasTemperateGrowth →
    (∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (ν : Measure V)) →
    (∫ x, x ∂(ν : Measure V)) = 0 →
    (∀ v : V, ∫ x, ⟪v, x⟫ ^ 2 ∂(ν : Measure V) ≤ ‖v‖ ^ 2) →
    ∀ {C : NNReal}, 0 < C → Poincare.LocalSlope.Intrinsic.constant ν ≤ (C : ENNReal) →
    ∀ (f : Lp ℝ 2 (ν : Measure V)), f ∈ (adjointComp T̄).domain → L2.mean ν f = 0 →
    ∀ {β : ℝ} (N : ℕ), (∀ j, j + 1 < N → scale T̄ (iter T̄ f j) ^ 2 ≤ β / C) →
      ∑ k ∈ Finset.range N, meanGradSq T̄ (iter T̄ f k) ≤
        normSq (genField T̄ (iter T̄ f 0)) +
          β / C * ∑ k ∈ Finset.range (N - 1), ‖taylorField 1 (grad0 T̄ (iter T̄ f k))‖ ^ 2)

end HeatModel

/-! ## `M`: BKL Theorem 3.1 (exact statement)

There is a universal constant `K` such that for every `n`, every regular potential `V` on `ℝⁿ`
(BKL (12)) whose law `μ` is centered with `Cov μ ≤ Id`, and every `R ≥ 1` with
`|T_d f| ≤ R^d ‖f‖_{L²(μ)}` for all `f ∈ L²(μ)` and `d ≥ 1` (29) (Hilbert–Schmidt norm in the
standard basis), the literature Poincaré constant satisfies `C_P(μ) ≤ K R²`. -/

#check (∃ K : ℝ, ∀ (n : ℕ) (V : EuclideanSpace ℝ (Fin n) → ℝ) (a b : ℝ)
    (hV : KLS.RegularPotential V a b),
    (∫ x, x ∂(hV.law : Measure (EuclideanSpace ℝ (Fin n)))) = 0 →
    (∀ v : EuclideanSpace ℝ (Fin n),
      ∫ x, ⟪v, x⟫ ^ 2 ∂(hV.law : Measure (EuclideanSpace ℝ (Fin n))) ≤ ‖v‖ ^ 2) →
    ∀ R : ℝ, 1 ≤ R →
    (∀ (f : EuclideanSpace ℝ (Fin n) → ℝ),
      MemLp f 2 (hV.law : Measure (EuclideanSpace ℝ (Fin n))) → ∀ d : ℕ, 1 ≤ d →
      ‖coordTensor (EuclideanSpace.basisFun (Fin n) ℝ)
          (taylorTensor (hV.law : Measure (EuclideanSpace ℝ (Fin n))) f d)‖ ≤
        R ^ d * (eLpNorm f 2 (hV.law : Measure (EuclideanSpace ℝ (Fin n)))).toReal) →
    Poincare.LocalSlope.Intrinsic.constant hV.law ≤ ENNReal.ofReal (K * R ^ 2))
