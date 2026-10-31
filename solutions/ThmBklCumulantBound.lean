module

public import FunctionalInequalities.KLS.BKL.Cumulant.Bound
/-!
# Lean source-form certificate: `thm:bkl-cumulant-bound` (BKL Theorem 4.1)

Bizeul–Klartag–Lehec arXiv:2610.05474v1, Theorem 4.1, (65)–(66): one universal K ≥ 1 such that every
isotropic log-concave probability measure in every dimension and every order m ≥ 2 satisfy
R_m ≤ K^{m−1}((m−1)!)² Id. Here m = d + 1 with d ≥ 1, so the base order m = 2 is included, and
⟨R_m u, u⟩ is the coordinate sum (65). The law is arbitrary: no compactness, Letwin, energy,
induction
or extra integrability premise. K = 153 is the constant of the accepted cutoff induction (BKL (95)
in
finite-horizon cutoff form, from the actual compact Letwin constant 8); the noncompact case is the
truncation argument `cumulantBound_of_compact`. This proves the cumulant theorem only: the uncut
Eldan
process and the literal stochastic identities (68)–(73) are not constructed, and BKL Theorem 1.1 and
KLS are not claimed.
-/

@[expose] public section

noncomputable section
open MeasureTheory
open FunctionalInequalities.KLS.BKL FunctionalInequalities.KLS.BKL.Localization
namespace Solutions.ThmBklCumulantBound

/--
The cumulant bound for every order d + 1 ≥ 2 with one universal K, in the library predicate form. -/
theorem bound :
    ∃ K : ℝ,
      1 ≤ K ∧
        ∀ d : ℕ,
          1 ≤ d →
            FunctionalInequalities.KLS.LogConcave.Suspension.CumulantBound d
              ((d.factorial : ℝ) ^ 2 * K ^ d) :=
  ⟨153, by norm_num, cumulantBound_153⟩

/--
**BKL Theorem 4.1**, fully expanded: one universal K ≥ 1; for every order m = d + 1 ≥ 2, every
dimension
n, every isotropic log-concave probability measure μ on `EuclideanSpace ℝ (Fin n)` and every u,
Σ_{i₂,…,i_m} κ_m(μ)(u, e_{i₂}, …, e_{i_m})² ≤ K^{m−1} ((m−1)!)² ‖u‖². -/
theorem certificate :
    ∃ K : ℝ,
      1 ≤ K ∧
        ∀ d : ℕ,
          1 ≤ d →
            ∀ (n : ℕ) (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))),
              FunctionalInequalities.KLS.Isotropic μ →
                FunctionalInequalities.KLS.LogConcave μ →
                  ∀ u : EuclideanSpace ℝ (Fin n),
                    ∑ J : Fin d → Fin n,
                        FunctionalInequalities.Analysis.BakryEmery.cumulant
                            (μ : Measure (EuclideanSpace ℝ (Fin n))) (d + 1)
                            (Fin.cons u fun k => EuclideanSpace.basisFun (Fin n) ℝ (J k)) ^
                          2 ≤
                      K ^ d * (d.factorial : ℝ) ^ 2 * ‖u‖ ^ 2 := by
  obtain ⟨K, hK, h⟩ := bound
  refine ⟨K, hK, fun d hd n μ hiso hLC u => ?_⟩
  have hb := h d hd n μ hiso hLC u
  calc
    _ ≤ (d.factorial : ℝ) ^ 2 * K ^ d * ‖u‖ ^ 2 := hb
    _ = K ^ d * (d.factorial : ℝ) ^ 2 * ‖u‖ ^ 2 := by ring

/--
info: 'Solutions.ThmBklCumulantBound.bound' depends on axioms: [propext, Classical.choice,
Quot.sound]
-/
#guard_msgs (whitespace := lax) in
  #print axioms Solutions.ThmBklCumulantBound.bound

/--
info: 'Solutions.ThmBklCumulantBound.certificate' depends on axioms: [propext, Classical.choice,
Quot.sound]
-/
#guard_msgs (whitespace := lax) in
  #print axioms Solutions.ThmBklCumulantBound.certificate

end Solutions.ThmBklCumulantBound
