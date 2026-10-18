import FunctionalInequalities.KLS.BKL.Suspension.Law
import FunctionalInequalities.KLS.LogConcave.Regular.Basic
import FunctionalInequalities.KLS.Isotropic
import FunctionalInequalities.Analysis.BakryEmery.Cumulant.Basic
import FunctionalInequalities.Analysis.Tensor.Coefficients
import FunctionalInequalities.KLS.BKL.Localization.Process.Basic
/-!
# Route statements: BKL Proposition 7.1

This file contains only `#check`s. A proposition that type-checks is not a proof. Source:
Bizeul–Klartag–Lehec, arXiv:2610.05474v1, Proposition 7.1 and its proof, pp. 28–30. The joint law of `(S, X₁, …, X_N)`
lives on `JointSpace N n = EuclideanSpace ℝ (Option (Fin N × Fin n))` (`KLS/BKL/Suspension/Law.lean`):
`none` is `S`, `some (i, j)` the `j`-th coordinate of `X_i`.

* `R1` isotropy of the joint law from (108); `R2` the density (109); `R3` its log-concavity under
  (110); `R4` (111) and `R5` (112) for the source's chosen `N`; `R6` the Hilbert–Schmidt lower bound; `R7` (113) for smooth `f`
  satisfying (108); `R8` (113) for every `f` orthogonal to the affine functions; `M71` (107).
-/

noncomputable section

open MeasureTheory FunctionalInequalities FunctionalInequalities.Probability.Line
open FunctionalInequalities.Analysis.BakryEmery FunctionalInequalities.Analysis.Tensor
open FunctionalInequalities.KLS.LogConcave.Suspension
open scoped RealInnerProductSpace ContDiff

/-! ## `R1`: isotropy of the joint law (from (108), independence and `E η² = 2/β²`) -/

#check (∀ {n N : ℕ}, 0 < N → ∀ (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ],
    MemLp id 2 μ → ∫ x, x ∂μ = 0 →
    (∀ u v : EuclideanSpace ℝ (Fin n), ∫ x, ⟪u, x⟫ * ⟪v, x⟫ ∂μ = ⟪u, v⟫) →
    ∀ {f : EuclideanSpace ℝ (Fin n) → ℝ}, Measurable f → MemLp f 2 μ → ∫ x, f x ∂μ = 0 →
    ∫ x, f x ^ 2 ∂μ = 1 → (∀ u, ∫ x, ⟪u, x⟫ * f x ∂μ = 0) →
    ∀ {β : ℝ}, 0 < β →
    MemLp id 2 (jointLaw μ f β (sigma β) N) ∧ ∫ p, p ∂(jointLaw μ f β (sigma β) N) = 0 ∧
      ∀ u v : JointSpace N n, ∫ p, ⟪u, p⟫ * ⟪v, p⟫ ∂(jointLaw μ f β (sigma β) N) = ⟪u, v⟫)

/-! ## `R2`, `R3`: the density (109) and log-concavity under (110)

`jointPotential` is the source's `W_N` in the joint coordinates: `Suspension.potential` at
`(p none, (p (some (i, ·)))_i)`. -/

#check (∀ {n N : ℕ} (V f : EuclideanSpace ℝ (Fin n) → ℝ) {β : ℝ}, 0 < β →
    Measurable V → Measurable f → Integrable (fun x => Real.exp (-V x)) →
    jointLaw (volume.tilted fun x => -V x) f β (sigma β) N =
      (volume : Measure (JointSpace N n)).tilted fun p =>
        -potential V f β (sigma β) N
          (p none, fun i => WithLp.toLp 2 fun j => p (some (i, j))))

#check (∀ {n N : ℕ} (V f : EuclideanSpace ℝ (Fin n) → ℝ) {a M β : ℝ}, 0 < β →
    ContDiff ℝ 2 V → ContDiff ℝ 2 f →
    (∀ x v, a * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ V x v v) →
    (∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ M) → β / Real.sqrt N * M ≤ a →
    Integrable (fun x => Real.exp (-V x)) →
    ∀ h : IsProbabilityMeasure (jointLaw (volume.tilted fun x => -V x) f β (sigma β) N),
      KLS.LogConcave (⟨_, h⟩ : ProbabilityMeasure (JointSpace N n)))

/-! ## `R4` (111) and `R5` (112), for a regular law and `f ∈ C²` with bounded Hessian, under (110)

The source fixes `N` by (110), `β M/√N ≤ a`; the joint law is then log-concave (`logConcave_jointLaw`)
and `Λ_ν` is smooth near `0` (`exists_integrable_exp_norm_contDiffOn_logLaplace_jointLaw`).
`R4`: at a point `z` with `z none = 0`, the derivative of `Λ_ν` along `e_none` is
`(σ√N)⁻¹ Σ_i F_f(z_i)`. `R5`: the mixed cumulant entries, for `d ≥ 1` (for `d = 0` the sum over the
`N` blocks does not collapse: `κ₁(e₀) = N (σ√N)⁻¹ ∫ f`). -/

#check (∀ {n N : ℕ}, 0 < N → ∀ (V : EuclideanSpace ℝ (Fin n) → ℝ) {a b' : ℝ}
    (hV : KLS.RegularPotential V a b') {f : EuclideanSpace ℝ (Fin n) → ℝ} {M β : ℝ}, 0 < β →
    ContDiff ℝ 2 f → (∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ M) → β / Real.sqrt N * M ≤ a →
    ∃ r > 0, ∀ z : JointSpace N n, ‖z‖ < r → z none = 0 →
      fderiv ℝ (logLaplace (jointLaw (hV.law : Measure _) f β (sigma β) N)) z
          (EuclideanSpace.single none 1) =
        (sigma β * Real.sqrt N)⁻¹ *
          ∑ i, tiltAverage (hV.law : Measure _) f (WithLp.toLp 2 fun j => z (some (i, j))))

#check (∀ {n N : ℕ}, 0 < N → ∀ (V : EuclideanSpace ℝ (Fin n) → ℝ) {a b' : ℝ}
    (hV : KLS.RegularPotential V a b') {f : EuclideanSpace ℝ (Fin n) → ℝ} {M β : ℝ}, 0 < β →
    ContDiff ℝ 2 f → (∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ M) → β / Real.sqrt N * M ≤ a →
    ∀ {d : ℕ}, 1 ≤ d → ∀ (I : Fin d → Fin N) (J : Fin d → Fin n),
      cumulant (jointLaw (hV.law : Measure _) f β (sigma β) N) (d + 1)
          (Fin.cons (EuclideanSpace.single none 1) fun k =>
            EuclideanSpace.single (some (I k, J k)) 1) =
        if ∀ k k', I k = I k' then
          (d.factorial : ℝ) / (sigma β * Real.sqrt N) *
            taylorTensor (hV.law : Measure _) f d fun k => EuclideanSpace.basisFun (Fin n) ℝ (J k)
        else 0)

/-! ## `R6`: the Hilbert–Schmidt lower bound after (112), `|κ(e₀)|² ≥ (d!)²/σ² |T_d f|²` -/

#check (∀ {n N : ℕ}, 0 < N → ∀ (V : EuclideanSpace ℝ (Fin n) → ℝ) {a b' : ℝ}
    (hV : KLS.RegularPotential V a b') {f : EuclideanSpace ℝ (Fin n) → ℝ} {M : ℝ},
    ContDiff ℝ ∞ f → (∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ M) → ∀ {β : ℝ}, 0 < β →
    ∀ d : ℕ, 1 ≤ d →
      (d.factorial : ℝ) ^ 2 / sigma β ^ 2 *
          ‖coordTensor (EuclideanSpace.basisFun (Fin n) ℝ) (taylorTensor (hV.law : Measure _) f d)‖ ^ 2 ≤
        ∑ K : Fin d → Option (Fin N × Fin n),
          cumulant (jointLaw (hV.law : Measure _) f β (sigma β) N) (d + 1)
            (Fin.cons (EuclideanSpace.single none 1) fun k => EuclideanSpace.single (K k) 1) ^ 2)

/-! ## `R7`: (113) for smooth `f` with bounded Hessian satisfying (108) -/

#check (∀ (d : ℕ), 2 ≤ d → ∀ b : ℝ, 0 < b → CumulantBound d b →
    ∀ {n : ℕ} (V : EuclideanSpace ℝ (Fin n) → ℝ) {a b' : ℝ} (hV : KLS.RegularPotential V a b'),
    KLS.Isotropic hV.law → ∀ {f : EuclideanSpace ℝ (Fin n) → ℝ} {M : ℝ}, ContDiff ℝ ∞ f →
    (∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ M) → ∫ x, f x ∂(hV.law : Measure _) = 0 →
    ∫ x, f x ^ 2 ∂(hV.law : Measure _) = 1 → (∀ u, ∫ x, ⟪u, x⟫ * f x ∂(hV.law : Measure _) = 0) →
    ‖coordTensor (EuclideanSpace.basisFun (Fin n) ℝ) (taylorTensor (hV.law : Measure _) f d)‖ ^ 2 ≤
      b / (d.factorial : ℝ) ^ 2)

/-! ## `R8`: (113) for every `f ∈ L²` orthogonal to the affine functions -/

#check (∀ (d : ℕ), 2 ≤ d → ∀ b : ℝ, 0 < b → CumulantBound d b →
    ∀ {n : ℕ} (V : EuclideanSpace ℝ (Fin n) → ℝ) {a b' : ℝ} (hV : KLS.RegularPotential V a b'),
    KLS.Isotropic hV.law → ∀ {f : EuclideanSpace ℝ (Fin n) → ℝ}, MemLp f 2 (hV.law : Measure _) →
    ∫ x, f x ∂(hV.law : Measure _) = 0 → (∀ u, ∫ x, ⟪u, x⟫ * f x ∂(hV.law : Measure _) = 0) →
    ‖coordTensor (EuclideanSpace.basisFun (Fin n) ℝ) (taylorTensor (hV.law : Measure _) f d)‖ ^ 2 ≤
      b / (d.factorial : ℝ) ^ 2 * (eLpNorm f 2 (hV.law : Measure _)).toReal ^ 2)

/-! ## `M71`: BKL Proposition 7.1, (107) -/

#check (∀ (d : ℕ), 2 ≤ d → ∀ b : ℝ, 0 < b → CumulantBound d b →
    ∀ {n : ℕ} (V : EuclideanSpace ℝ (Fin n) → ℝ) {a b' : ℝ} (hV : KLS.RegularPotential V a b'),
    KLS.Isotropic hV.law → ∀ (f : EuclideanSpace ℝ (Fin n) → ℝ), MemLp f 2 (hV.law : Measure _) →
    ‖coordTensor (EuclideanSpace.basisFun (Fin n) ℝ) (taylorTensor (hV.law : Measure _) f d)‖ ^ 2 ≤
      2 * b / (d.factorial : ℝ) ^ 2 * (eLpNorm f 2 (hV.law : Measure _)).toReal ^ 2)
