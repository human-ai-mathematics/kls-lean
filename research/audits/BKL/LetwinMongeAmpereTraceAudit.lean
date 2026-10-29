import FunctionalInequalities.Analysis.BakryEmery.Hessian.Trace
import FunctionalInequalities.Analysis.BakryEmery.UniformIntervalPotential

/-!
# Audit: (2.10) and the pointwise generator condition for a nonconstant interval potential

Source: Letwin, arXiv:2607.24164v1, (2.9)–(2.10) in the proof of Theorem 2.5 (support only). The
explicit given potential `φ(y) = 2 log cosh(√3 y/2) + log(4/√3)` with constant `V = log(2√3)`,
`K = (−√3, √3)` and `U = ℝ`: smoothness, the Monge–Ampère relation, positive definiteness, gradient
range in `K` and `∫ e^{−φ} = 1` are derived from `UniformIntervalPotential.lean`; the Hessian
`3/(2 cosh²(√3x/2))` is nonconstant; the library identity `traceGenerator_210_on_range` and the
generator condition `traceGeneratorCondition_on_range` are invoked with `B = 1`. `generator_const`
is an audit-local helper. A given-potential client: not a push-forward to the uniform law, not a
moment-map or A.5 consumption client.
-/

noncomputable section

open scoped BigOperators ContDiff RealInnerProductSpace Matrix.Norms.Elementwise Kronecker
open FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis.BakryEmery
open Matrix MeasureTheory

namespace LetwinMongeAmpereTraceAudit

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A local calculus helper for the nonconstancy witness below. -/
theorem generator_const (φ V : E → ℝ) (c : ℝ) (x : E) :
    hessianInverseOperator φ V (fun _ : E => c) x = 0 := by
  have hz (i j : StdBasisIndex E) :
      bilinearIteratedFDerivTwo ℝ (fun _ : E => c) x
        (stdOrthonormalBasis ℝ E i) (stdOrthonormalBasis ℝ E j) = 0 := by
    rw [bilinearIteratedFDerivTwo_eq_fderiv_apply contDiff_const]
    simp
  unfold hessianInverseOperator nondivergenceOperator
  simp [hz]

/-- The explicit given potential; no pushforward assertion is included. -/
def uniformIntervalPotential (y : ℝ) : ℝ :=
  2 * Real.log (Real.cosh (Real.sqrt 3 * y / 2)) + Real.log (4 / Real.sqrt 3)

def uniformIntervalV : ℝ → ℝ := fun _ => Real.log (2 * Real.sqrt 3)

def uniformIntervalK : Set ℝ := Set.Ioo (-Real.sqrt 3) (Real.sqrt 3)

def uniformIntervalU : Set ℝ := Set.univ

/-- All local source assumptions and exponential normalization are derived from
 the explicit-potential package. -/
theorem uniformInterval_source_data :
    ContDiff ℝ ∞ uniformIntervalPotential ∧
    IsOpen uniformIntervalK ∧
    IsOpen uniformIntervalU ∧
    closure uniformIntervalK ⊆ uniformIntervalU ∧
    ContDiffOn ℝ ∞ uniformIntervalV uniformIntervalU ∧
    ConvexOn ℝ uniformIntervalK uniformIntervalV ∧
    Set.range (gradient uniformIntervalPotential) ⊆ uniformIntervalK ∧
    (∀ y, logDetHessian uniformIntervalPotential (stdOrthonormalBasis ℝ ℝ) y =
      -uniformIntervalPotential y + uniformIntervalV (gradient uniformIntervalPotential y)) ∧
    (∀ x v : ℝ, v ≠ 0 →
      0 < bilinearIteratedFDerivTwo ℝ uniformIntervalPotential x v v) ∧
    (∫ x, Real.exp (-uniformIntervalPotential x) ∂(volume : Measure ℝ)) = 1 := by
  rcases uniformInterval_momentPotential_source_hypotheses with
    ⟨hφ, hconv, hRange, hMA, hPD, hNorm⟩
  refine ⟨hφ, ?_, ?_, ?_, ?_, ?_, hRange, hMA, hPD, hNorm⟩
  · exact isOpen_Ioo
  · exact isOpen_univ
  · intro y hy
    exact Set.mem_univ y
  · exact contDiff_const.contDiffOn
  · change ConvexOn ℝ (Set.Ioo (-Real.sqrt 3) (Real.sqrt 3))
      (fun _ : ℝ => Real.log (2 * Real.sqrt 3))
    refine ⟨convex_Ioo _ _, ?_⟩
    intro y hy z hz a b ha hb hab
    change Real.log (2 * Real.sqrt 3) ≤
      a * Real.log (2 * Real.sqrt 3) + b * Real.log (2 * Real.sqrt 3)
    apply le_of_eq
    rw [← add_mul, hab, one_mul]

/-- The actual Hessian formula in the standard orthonormal basis of ℝ. -/
theorem uniformInterval_hessian_diagonal (x : ℝ) (i : StdBasisIndex ℝ) :
    stdHessianMatrix uniformIntervalPotential x i i =
      3 / 2 / Real.cosh (Real.sqrt 3 * x / 2) ^ 2 := by
  let e : ℝ := stdOrthonormalBasis ℝ ℝ i
  have he_norm : ‖e‖ = 1 := by
    dsimp [e]
    exact (stdOrthonormalBasis ℝ ℝ).norm_eq_one i
  have habs : |e| = 1 := by
    simpa only [Real.norm_eq_abs] using he_norm
  have hee : e * e = 1 := by
    calc
      e * e = e ^ 2 := by ring
      _ = |e| ^ 2 := by rw [sq_abs]
      _ = 1 := by rw [habs]; norm_num
  change bilinearIteratedFDerivTwo ℝ
    (fun y : ℝ => 2 * Real.log (Real.cosh (Real.sqrt 3 * y / 2)) +
      Real.log (4 / Real.sqrt 3)) x e e = _
  rw [uniformInterval_momentPotential_bilinearIteratedFDerivTwo, hee, mul_one]

/-- The Hessian really is nonconstant. The contradiction uses actual (2.9),
constant V, and the explicit positive Hessian value at zero. -/
theorem uniformIntervalHessian_nonconstant :
    ¬ ∃ M : Matrix (StdBasisIndex ℝ) (StdBasisIndex ℝ) ℝ,
      ∀ x : ℝ, stdHessianMatrix uniformIntervalPotential x = M := by
  rintro ⟨M, hM⟩
  rcases uniformInterval_source_data with
    ⟨hφ, hK, hU, hKU, hV, hc, hRange, hMA, hPD, hNorm⟩
  let i : StdBasisIndex ℝ := ⟨0, by simp [Module.finrank_self]⟩
  have he (j k : StdBasisIndex ℝ) :
      (fun y : ℝ => stdHessianMatrix uniformIntervalPotential y j k) =
        (fun _ : ℝ => M j k) := by
    funext y
    exact congrArg
      (fun Q : Matrix (StdBasisIndex ℝ) (StdBasisIndex ℝ) ℝ => Q j k) (hM y)
  have hT (a : StdBasisIndex ℝ) : stdHessianMatrixDeriv uniformIntervalPotential 0 a = 0 := by
    ext j k
    change fderiv ℝ (fun y : ℝ => stdHessianMatrix uniformIntervalPotential y j k)
      0 (stdOrthonormalBasis ℝ ℝ a) = 0
    rw [he j k]
    simp
  have hG : stdThirdGram uniformIntervalPotential 0 = 0 := by
    ext j k
    simp [stdThirdGram, hT]
  have hL : stdHessianMatrixGenerator uniformIntervalPotential uniformIntervalV 0 i i = 0 := by
    change hessianInverseOperator uniformIntervalPotential uniformIntervalV
      (fun y : ℝ => stdHessianMatrix uniformIntervalPotential y i i) 0 = 0
    rw [he i i]
    exact generator_const uniformIntervalPotential uniformIntervalV (M i i) 0
  have hVV :
      hessianMatrixIn uniformIntervalV (stdOrthonormalBasis ℝ ℝ)
        (gradient uniformIntervalPotential 0) = 0 := by
    ext j k
    change bilinearIteratedFDerivTwo ℝ
      (fun _ : ℝ => Real.log (2 * Real.sqrt 3))
      (gradient uniformIntervalPotential 0)
      (stdOrthonormalBasis ℝ ℝ j) (stdOrthonormalBasis ℝ ℝ k) = 0
    rw [bilinearIteratedFDerivTwo_eq_fderiv_apply contDiff_const]
    simp
  have hh := stdHessianMatrixGenerator_apply_on_range
    hφ hU hKU hV hRange hMA hPD (0 : ℝ) i i
  rw [hL, hVV, hG] at hh
  simp only [mul_zero, zero_mul, Matrix.zero_apply, add_zero] at hh
  have hd := uniformInterval_hessian_diagonal 0 i
  simp only [mul_zero, zero_div, Real.cosh_zero, one_pow, div_one] at hd
  linarith

theorem uniformIntervalPotential_nonconstant :
    ¬ ∃ c : ℝ, uniformIntervalPotential = fun _ : ℝ => c := by
  rintro ⟨c, hc⟩
  apply uniformIntervalHessian_nonconstant
  refine ⟨0, ?_⟩
  intro x
  ext i j
  change bilinearIteratedFDerivTwo ℝ uniformIntervalPotential x
    (stdOrthonormalBasis ℝ ℝ i) (stdOrthonormalBasis ℝ ℝ j) = 0
  rw [hc, bilinearIteratedFDerivTwo_eq_fderiv_apply contDiff_const]
  simp

/-- (2.10) applied to the explicit nonconstant uniform-interval potential,
with the constant matrix B = 1. -/
theorem uniformInterval_trace_210 (x : ℝ) :
    hessianInverseOperator uniformIntervalPotential uniformIntervalV
        (fun y => (stdHessianMatrix uniformIntervalPotential y *
          stdHessianMatrix uniformIntervalPotential y).trace) x =
      -2 * (stdHessianMatrix uniformIntervalPotential x *
        stdHessianMatrix uniformIntervalPotential x).trace +
      2 * ∑ a, ∑ b,
        inverseHessianEntry uniformIntervalPotential (stdOrthonormalBasis ℝ ℝ) x a b *
          (stdHessianMatrixDeriv uniformIntervalPotential x a *
            stdHessianMatrixDeriv uniformIntervalPotential x b).trace +
      2 * (stdHessianMatrix uniformIntervalPotential x *
        (stdHessianMatrix uniformIntervalPotential x *
          hessianMatrixIn uniformIntervalV (stdOrthonormalBasis ℝ ℝ)
            (gradient uniformIntervalPotential x) *
          stdHessianMatrix uniformIntervalPotential x)).trace +
      2 * (stdHessianMatrix uniformIntervalPotential x *
        stdThirdGram uniformIntervalPotential x).trace := by
  rcases uniformInterval_source_data with
    ⟨hφ, hK, hU, hKU, hV, hc, hRange, hMA, hPD, hNorm⟩
  simpa only [one_mul, mul_one] using
    (traceGenerator_210_on_range hφ hU hKU hV hRange hMA hPD
      (1 : Matrix (StdBasisIndex ℝ) (StdBasisIndex ℝ) ℝ) x)

/-- A hypothesis-free explicit-potential client of the pointwise generator
condition. This is not a gradient-pushforward or source-law theorem. -/
theorem uniformInterval_traceGeneratorCondition (x : ℝ) :
    0 ≤ hessianInverseOperator uniformIntervalPotential uniformIntervalV
        (fun y => (stdHessianMatrix uniformIntervalPotential y *
          stdHessianMatrix uniformIntervalPotential y).trace) x +
      2 * (stdHessianMatrix uniformIntervalPotential x *
        stdHessianMatrix uniformIntervalPotential x).trace := by
  rcases uniformInterval_source_data with
    ⟨hφ, hK, hU, hKU, hV, hc, hRange, hMA, hPD, hNorm⟩
  have hI : (1 : Matrix (StdBasisIndex ℝ) (StdBasisIndex ℝ) ℝ).PosSemidef := by
    apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
    constructor
    · change (1 : Matrix (StdBasisIndex ℝ) (StdBasisIndex ℝ) ℝ).conjTranspose = 1
      simp
    · intro v
      simp only [Matrix.one_mulVec, dotProduct, Pi.star_apply, star_trivial]
      exact Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)
  simpa only [one_mul, mul_one] using
    (traceGeneratorCondition_on_range hφ hK hU hKU hV hc hRange hMA hPD
      (1 : Matrix (StdBasisIndex ℝ) (StdBasisIndex ℝ) ℝ) hI x)

end LetwinMongeAmpereTraceAudit

#print axioms FunctionalInequalities.Analysis.sum_entry_mul_nonneg
#print axioms FunctionalInequalities.Analysis.trace_mul_nonneg
#print axioms FunctionalInequalities.Analysis.traceGram_posSemidef
#print axioms FunctionalInequalities.Analysis.BakryEmery.stdHessianMatrixGenerator_eq_on_range
#print axioms FunctionalInequalities.Analysis.BakryEmery.traceGenerator_210_on_range
#print axioms FunctionalInequalities.Analysis.BakryEmery.weightedDerivativeTrace_nonneg
#print axioms FunctionalInequalities.Analysis.BakryEmery.hessianConjugateTrace_nonneg_on_range
#print axioms FunctionalInequalities.Analysis.BakryEmery.thirdGramTrace_nonneg
#print axioms FunctionalInequalities.Analysis.BakryEmery.traceGeneratorCondition_on_range
#print axioms LetwinMongeAmpereTraceAudit.uniformInterval_source_data
#print axioms LetwinMongeAmpereTraceAudit.uniformIntervalHessian_nonconstant
#print axioms LetwinMongeAmpereTraceAudit.uniformIntervalPotential_nonconstant
#print axioms LetwinMongeAmpereTraceAudit.uniformInterval_trace_210
#print axioms LetwinMongeAmpereTraceAudit.uniformInterval_traceGeneratorCondition
