import FunctionalInequalities.Analysis.BakryEmery.Cumulant.Leibniz
import FunctionalInequalities.Analysis.Operator.InverseSqrt

/-!
# Cumulant energies and the middle term `L_m` of the localization

Bizeul–Klartag–Lehec arXiv:2610.05474v1, (72) and (75)–(76), at a fixed law `ν` with covariance `A` and
`σ = A^{-1/2}`: the middle term `L_m(h) = Σ_{J ∋ i₀, 2 ≤ |J|, |Jᶜ| ≥ 2} ⟪κ_{|J|+1}(h_J, ·), A⁻¹ κ_{m−|J|+1}(h_{Jᶜ}, ·)⟫`
(`lowerDrift`, in the mask form of `Analysis/BakryEmery/Cumulant/Leibniz.lean`) and the cumulant energy
`E_{r+1} = |κ_{r+1}(u)|²_A = Σ_J κ_{r+1}(u, σ e_{J_1}, …, σ e_{J_r})²` (`cumulantEnergy`). Definitions only;
statements and placement: Claude (BKL Claude-controller goal).
-/

noncomputable section

open MeasureTheory
open FunctionalInequalities.Analysis FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace

namespace FunctionalInequalities.KLS.BKL

variable {n : ℕ}

/-- The middle term `L_m` of BKL arXiv:2610.05474v1, (72), at a fixed law `ν` with covariance `A`:
`L_m(h) = Σ_{J ∋ i₀, 2 ≤ |J|, |Jᶜ| ≥ 2} ⟪κ_{|J|+1}(h_J, ·), A⁻¹ κ_{m−|J|+1}(h_{Jᶜ}, ·)⟫` (slot `i₀ = 0`). -/
def lowerDrift (ν : Measure (EuclideanSpace ℝ (Fin n))) {m : ℕ} (h : Fin m → EuclideanSpace ℝ (Fin n))
    (i₀ : Fin m) : ℝ :=
  ∑ q ∈ Finset.univ.filter (fun q : Fin m → Bool =>
      q i₀ = true ∧ 2 ≤ (selected h q).length ∧ 2 ≤ (selected h (fun i => !(q i))).length),
    ⟪cumulantVector ν (selected h q),
      Ring.inverse (Covariance.operator ν) (cumulantVector ν (selected h (fun i => !(q i))))⟫

/-- The cumulant energy `E_{r+1} = |κ_{r+1}(u)|²_A = Σ_J κ_{r+1}(u, σ e_{J_1}, …, σ e_{J_r})²`, `σ = A^{-1/2}`
(BKL (75)–(76)). -/
def cumulantEnergy (ν : Measure (EuclideanSpace ℝ (Fin n))) (r : ℕ) (u : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑ J : Fin r → Fin n, cumulant ν (r + 1)
    (Fin.cons u fun k => inverseSqrt (Covariance.operator ν) (EuclideanSpace.basisFun (Fin n) ℝ (J k))) ^ 2

end FunctionalInequalities.KLS.BKL
