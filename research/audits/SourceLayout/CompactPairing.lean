module

public import FunctionalInequalities.L2.Pairing
public import FunctionalInequalities.Analysis.Cutoff.Profile
public import FunctionalInequalities.Analysis.BakryEmery.Hessian.Weak

@[expose] public section

noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace

namespace CompactPairingAudit

/-- The shared pairing works for Lebesgue measure, whose total mass is infinite. -/
theorem volume_pairing (ψ : Lp ℝ 2 (volume : Measure ℝ)) {q : ℝ → ℝ}
    (hq : Continuous q) (hqc : HasCompactSupport q) :
    Integrable (fun x => ψ x * q x) volume :=
  FunctionalInequalities.L2.integrable_mul_continuous_of_hasCompactSupport ψ hq hqc

theorem sublevel_support {φ g : ℝ → ℝ} {T : ℝ}
    (hφ : Continuous φ) (hsub : IsCompact {y | φ y ≤ T})
    (hg : ∀ s, T ≤ s → g s = 0) : HasCompactSupport (fun x => g (φ x)) :=
  FunctionalInequalities.Analysis.hasCompactSupport_comp_of_isCompact_sublevel hφ hsub hg

/-- Total Hessian entries need no C2 or equation assumption for this bound. -/
theorem hessian_bound {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ} {G : NNReal}
    (hG : LipschitzWith G (gradient u)) (i j : Fin n)
    (S : Set (EuclideanSpace ℝ (Fin n))) (hS : IsCompact S) :
    MemLp (fun x => FunctionalInequalities.Probability.Stein.hessianMatrix u x i j)
      (⊤ : ENNReal) ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S) :=
  FunctionalInequalities.Probability.Stein.memLp_top_hessianMatrix_entry_of_isCompact
    hG i j S hS

#print axioms volume_pairing
#print axioms sublevel_support
#print axioms hessian_bound
end CompactPairingAudit
