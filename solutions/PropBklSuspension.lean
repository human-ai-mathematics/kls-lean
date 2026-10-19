import FunctionalInequalities.KLS.BKL.TaylorBound

/-!
# Lean certificate: `prop:bkl-suspension`

Bizeul–Klartag–Lehec, *Presenting a proof of the Kannan–Lovász–Simonovits conjecture*
(arXiv:2610.05474v1), Proposition 7.1, p. 28, proof pp. 28–30: let `d ≥ 2` and `b > 0`, and assume
`R^ν_{d+1} ≤ b Id` for every isotropic log-concave probability measure `ν` in every dimension. Then
every isotropic regular log-concave `μ` on `ℝⁿ` satisfies `|T_d f|² ≤ 2b/(d!)² ‖f‖²_{L²(μ)}` for all
`f ∈ L²(μ)`.

The certificate states it in the source form: the universal cumulant hypothesis is
`Suspension.CumulantBound d b` (`Σ_J κ^ν_{d+1}(u, e_{J 1}, …, e_{J d})² ≤ b |u|²` for every isotropic
log-concave `ν` on every `EuclideanSpace ℝ (Fin m)` and every `u`), regularity is
`KLS.RegularPotential V a b'` (BKL (12)) with the law `hV.law`, isotropy is `KLS.Isotropic`, and
`T_d f` is measured in the Hilbert–Schmidt norm of its coefficient array in the standard basis.
The hypothesis is the source's own hypothesis. The separately certified Theorem 4.1 supplies it
in the final assembly; this certificate retains the conditional statement.

The proof follows the source: the suspension `(S, X₁, …, X_N)` with `N` chosen by (110), its
isotropy and log-concavity, the mixed cumulants (111)–(112), the Hilbert–Schmidt step and `β → ∞`
give (113) for smooth normalized `f`; density and the affine decomposition give (107).
-/

noncomputable section

open MeasureTheory FunctionalInequalities FunctionalInequalities.KLS
open FunctionalInequalities.Analysis.Tensor FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.KLS.LogConcave.Suspension
open scoped RealInnerProductSpace

namespace Solutions.PropBklSuspension

/-- **BKL Proposition 7.1** in the source form. -/
theorem certificate {d : ℕ} (hd : 2 ≤ d) {b : ℝ} (hb : 0 < b) (hcb : CumulantBound d b) {n : ℕ}
    (V : EuclideanSpace ℝ (Fin n) → ℝ) {a b' : ℝ} (hV : KLS.RegularPotential V a b')
    (hiso : KLS.Isotropic hV.law) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : MemLp f 2 (hV.law : Measure (EuclideanSpace ℝ (Fin n)))) :
    ‖coordTensor (EuclideanSpace.basisFun (Fin n) ℝ)
        (taylorTensor (hV.law : Measure (EuclideanSpace ℝ (Fin n))) f d)‖ ^ 2 ≤
      2 * b / (d.factorial : ℝ) ^ 2 *
        (eLpNorm f 2 (hV.law : Measure (EuclideanSpace ℝ (Fin n)))).toReal ^ 2 :=
  norm_coordTensor_taylorTensor_sq_le_two_mul hd hb hcb V hV hiso f hf

/-- The case `d = 2` with the explicit constant `b/2`: the source's leading case (used with
`R_3 ≤ 8 Id` in the paper). No instance of the hypothesis is asserted. -/
theorem two {b : ℝ} (hb : 0 < b) (hcb : CumulantBound 2 b) {n : ℕ}
    (V : EuclideanSpace ℝ (Fin n) → ℝ) {a b' : ℝ} (hV : KLS.RegularPotential V a b')
    (hiso : KLS.Isotropic hV.law) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : MemLp f 2 (hV.law : Measure (EuclideanSpace ℝ (Fin n)))) :
    ‖coordTensor (EuclideanSpace.basisFun (Fin n) ℝ)
        (taylorTensor (hV.law : Measure (EuclideanSpace ℝ (Fin n))) f 2)‖ ^ 2 ≤
      b / 2 * (eLpNorm f 2 (hV.law : Measure (EuclideanSpace ℝ (Fin n)))).toReal ^ 2 := by
  have h := certificate le_rfl hb hcb V hV hiso f hf
  have h4 : ((Nat.factorial 2 : ℕ) : ℝ) ^ 2 = 4 := by norm_num [Nat.factorial]
  rw [h4] at h
  have h2 : 2 * b / 4 = b / 2 := by ring
  rw [h2] at h
  exact h

/--
info: 'Solutions.PropBklSuspension.certificate' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Solutions.PropBklSuspension.certificate

/--
info: 'Solutions.PropBklSuspension.two' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Solutions.PropBklSuspension.two

end Solutions.PropBklSuspension
