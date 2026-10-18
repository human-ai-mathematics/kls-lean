import FunctionalInequalities.L2.Pairing
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# The `H^{-1}` dual energy norm

Letwin, arXiv:2607.24164v1, (2.19): for a probability law `μ` and `q ∈ L²(μ)`,
`‖q‖_{H^{-1}(μ)} = sup { ∫ q f dμ : f locally Lipschitz, ∫ ‖∇f‖² dμ ≤ 1 }`. The supremum is taken as
an extended real over the full test class (no centering, smoothness or compact support); it is
identified with the real signed supremum only once finiteness is proved. Constant inputs have
infinite dual norm (constants are zero-energy tests).
-/

open MeasureTheory Filter
open scoped RealInnerProductSpace Topology

noncomputable section

namespace FunctionalInequalities.Energy.Dual

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E]

/-- **Unit-energy tests** (Letwin (2.19)): locally Lipschitz `f ∈ L²(μ)` with `∇f ∈ L²(μ)` and
`∫ ‖∇f‖² dμ ≤ 1`; no centering, smoothness or compact support is required. -/
structure UnitEnergyTest (μ : ProbabilityMeasure E) where
  fn : E → ℝ
  locallyLipschitz : LocallyLipschitz fn
  memLp : MemLp fn 2 (μ : Measure E)
  gradLp : MemLp (gradient fn) 2 (μ : Measure E)
  energy : ‖gradLp.toLp (gradient fn)‖ ≤ 1

/-- The signed pairing `⟪q, f⟫_{L²(μ)}` of `q ∈ L²(μ)` with a unit-energy test. -/
def pairing (μ : ProbabilityMeasure E) (q : Lp ℝ 2 (μ : Measure E)) (t : UnitEnergyTest μ) : ℝ :=
  ⟪q, t.memLp.toLp t.fn⟫

/-- The `H^{-1}(μ)` dual norm `‖q‖_{H^{-1}} = sup_f ⟪q, f⟫` over unit-energy tests, as an extended real
(the positive part of each signed pairing). -/
def dualNorm (μ : ProbabilityMeasure E) (q : Lp ℝ 2 (μ : Measure E)) : ENNReal :=
  ⨆ t : UnitEnergyTest μ, ENNReal.ofReal (pairing μ q t)

def signedPairings (μ : ProbabilityMeasure E) (q : Lp ℝ 2 (μ : Measure E)) : Set ℝ :=
  Set.range (pairing μ q)

/-- The unit-energy condition is `∫ ‖∇f‖² dμ ≤ 1`. -/
theorem unit_gradient_norm_iff (μ : ProbabilityMeasure E) {f : E → ℝ}
    (hgrad : MemLp (gradient f) 2 (μ : Measure E)) :
    ‖hgrad.toLp (gradient f)‖ ≤ 1 ↔ ∫ x, ‖gradient f x‖ ^ 2 ∂(μ : Measure E) ≤ 1 := by
  rw [Lp.norm_toLp, L2.integral_norm_sq_eq_eLpNorm_sq hgrad]
  have hn : 0 ≤ (eLpNorm (gradient f) 2 (μ : Measure E)).toReal := ENNReal.toReal_nonneg
  constructor <;> intro h <;> nlinarith

/-- The zero test. -/
def zeroTest (μ : ProbabilityMeasure E) : UnitEnergyTest μ where
  fn := fun _ => 0
  locallyLipschitz := LocallyLipschitz.const 0
  memLp := memLp_const 0
  gradLp := by rw [gradient_fun_const']; exact memLp_const (0 : E)
  energy := by
    have hg : gradient (fun _ : E => (0 : ℝ)) = 0 := by funext x; exact gradient_fun_const x 0
    rw [Lp.norm_toLp, hg, eLpNorm_zero, ENNReal.toReal_zero]
    norm_num

@[simp] theorem pairing_zero (μ : ProbabilityMeasure E) (q : Lp ℝ 2 (μ : Measure E)) :
    pairing μ q (zeroTest μ) = 0 := by
  change ⟪q, (0 : Lp ℝ 2 (μ : Measure E))⟫ = 0
  exact inner_zero_right q

omit [MeasurableSpace E] in
/-- `∇(−f) = −∇f`. -/
theorem gradient_neg_fn (f : E → ℝ) : gradient (fun x => -f x) = -gradient f := by
  funext x
  simp only [gradient, fderiv_fun_neg, map_neg, Pi.neg_apply]

/-- Negation of a unit-energy test. -/
def negTest (μ : ProbabilityMeasure E) (t : UnitEnergyTest μ) : UnitEnergyTest μ where
  fn := fun x => -t.fn x
  locallyLipschitz := by
    have hn : LocallyLipschitz (fun y : ℝ => -y) :=
      (LipschitzWith.id.neg).locallyLipschitz
    exact hn.comp t.locallyLipschitz
  memLp := t.memLp.neg
  gradLp := by rw [gradient_neg_fn]; exact t.gradLp.neg
  energy := by
    rw [Lp.norm_toLp, gradient_neg_fn, eLpNorm_neg]
    simpa only [Lp.norm_toLp] using t.energy

@[simp] theorem pairing_neg (μ : ProbabilityMeasure E) (q : Lp ℝ 2 (μ : Measure E))
    (t : UnitEnergyTest μ) : pairing μ q (negTest μ t) = -pairing μ q t := by
  change ⟪q, t.memLp.neg.toLp (-t.fn)⟫ = -⟪q, t.memLp.toLp t.fn⟫
  rw [MemLp.toLp_neg, inner_neg_right]

/-- The dual norm is also the supremum of the absolute pairings. -/
theorem dualNorm_eq_iSup_abs (μ : ProbabilityMeasure E) (q : Lp ℝ 2 (μ : Measure E)) :
    dualNorm μ q = ⨆ t : UnitEnergyTest μ, ENNReal.ofReal |pairing μ q t| := by
  apply le_antisymm
  · apply iSup_le
    intro t
    exact (ENNReal.ofReal_le_ofReal (le_abs_self _)).trans (le_iSup (fun s : UnitEnergyTest μ => ENNReal.ofReal |pairing μ q s|) t)
  · apply iSup_le
    intro t
    by_cases hp : 0 ≤ pairing μ q t
    · rw [abs_of_nonneg hp]
      exact le_iSup (fun s : UnitEnergyTest μ => ENNReal.ofReal (pairing μ q s)) t
    · rw [abs_of_neg (lt_of_not_ge hp), ← pairing_neg μ q t]
      exact le_iSup (fun s : UnitEnergyTest μ => ENNReal.ofReal (pairing μ q s)) (negTest μ t)

/-- Each signed pairing is at most the (finite) dual norm. -/
theorem pairing_le_toReal_of_ne_top (μ : ProbabilityMeasure E) (q : Lp ℝ 2 (μ : Measure E))
    (hfinite : dualNorm μ q ≠ ⊤) (t : UnitEnergyTest μ) :
    pairing μ q t ≤ (dualNorm μ q).toReal := by
  by_cases hp : 0 ≤ pairing μ q t
  · have h := (ENNReal.toReal_le_toReal (by simp) hfinite).mpr
      (le_iSup (fun s : UnitEnergyTest μ => ENNReal.ofReal (pairing μ q s)) t)
    simpa only [ENNReal.toReal_ofReal hp] using h
  · exact (lt_of_not_ge hp).le.trans ENNReal.toReal_nonneg

/-- Finite dual norm bounds the set of signed pairings. -/
theorem signedPairings_bdd_of_ne_top (μ : ProbabilityMeasure E) (q : Lp ℝ 2 (μ : Measure E))
    (hfinite : dualNorm μ q ≠ ⊤) : BddAbove (signedPairings μ q) := by
  refine ⟨(dualNorm μ q).toReal, ?_⟩
  rintro r ⟨t, rfl⟩
  exact pairing_le_toReal_of_ne_top μ q hfinite t

/-- When finite, the dual norm is the real supremum of the signed pairings (the paper's (2.19)). -/
theorem toReal_dualNorm_eq_signed_sSup (μ : ProbabilityMeasure E)
    (q : Lp ℝ 2 (μ : Measure E)) (hfinite : dualNorm μ q ≠ ⊤) :
    (dualNorm μ q).toReal = sSup (signedPairings μ q) := by
  have hb := signedPairings_bdd_of_ne_top μ q hfinite
  have hz : (0 : ℝ) ∈ signedPairings μ q := ⟨zeroTest μ, pairing_zero μ q⟩
  have hs0 : 0 ≤ sSup (signedPairings μ q) := le_csSup hb hz
  apply le_antisymm
  · have hle : dualNorm μ q ≤ ENNReal.ofReal (sSup (signedPairings μ q)) := by
      apply iSup_le
      intro t
      exact ENNReal.ofReal_le_ofReal (le_csSup hb ⟨t, rfl⟩)
    have h := (ENNReal.toReal_le_toReal hfinite (by simp)).mpr hle
    simpa only [ENNReal.toReal_ofReal hs0] using h
  · apply csSup_le ⟨0, hz⟩
    rintro r ⟨t, rfl⟩
    exact pairing_le_toReal_of_ne_top μ q hfinite t

end FunctionalInequalities.Energy.Dual

end
