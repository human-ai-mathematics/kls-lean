import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Cutting off a locally regular function

Local-to-global cutoff calculus supporting the fixed unit-ball harmonic route of Gilbarg–Trudinger,
Classics 2001 (ISBN 3-540-41160-7), Theorem 4.6, p. 60. The source needs to be `C^k` only on an open
set containing the cutoff's support.

* `contDiff_cutoff_mul`: the product with such a cutoff is globally `C^k`; compact support of the
  product is `HasCompactSupport.mul_right`;
* `iteratedFDeriv_bump_mul`: where a smooth bump is locally one, the product has the same total
  iterated derivatives as the source;
* `bump_mul_local`: the combined `C²`, compact-support and derivative-preservation statement used to
  feed the compact `C²` representation.

No Green representation or harmonic derivative estimate is proved here.
-/
noncomputable section
open scoped Topology ContDiff
namespace FunctionalInequalities.Analysis
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A cutoff whose closed support lies in the regularity domain makes a local Ck
function globally Ck, without extending the uncut source outside its domain. -/
theorem contDiff_cutoff_mul {η h : E → ℝ} {U : Set E} {k : ℕ∞ω}
    (hU : IsOpen U) (hη : ContDiff ℝ k η) (hh : ContDiffOn ℝ k h U)
    (hs : tsupport η ⊆ U) : ContDiff ℝ k (fun x ↦ η x * h x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ U
  · exact hη.contDiffAt.mul (hh.contDiffAt (hU.mem_nhds hx))
  · have hzero : η =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp (fun hmem ↦ hx (hs hmem))
    have hz : ContDiffAt ℝ k (fun _ : E ↦ (0 : ℝ)) x := contDiffAt_const
    apply hz.congr_of_eventuallyEq
    filter_upwards [hzero] with y hy
    simp [hy]

variable [HasContDiffBump E]

/-- On the region where a smooth bump is locally one, cutting off preserves
all total iterated Fréchet derivatives of the actual source. -/
theorem iteratedFDeriv_bump_mul {c x : E} (η : ContDiffBump c) (h : E → ℝ)
    (hx : x ∈ Metric.ball c η.rIn) (k : ℕ) :
    iteratedFDeriv ℝ k (fun y ↦ η y * h y) x = iteratedFDeriv ℝ k h x := by
  have heq : (fun y ↦ η y * h y) =ᶠ[𝓝 x] h := by
    filter_upwards [η.eventuallyEq_one_of_mem_ball hx] with y hy
    simp [hy]
  exact (heq.iteratedFDeriv ℝ k).self_of_nhds

/-- A genuine local source can be inserted into the compact-C² representation
toolchain: this produces the compact function and its derivative preservation. -/
theorem bump_mul_local {c : E} [FiniteDimensional ℝ E] (η : ContDiffBump c)
    {h : E → ℝ} {U : Set E} (hU : IsOpen U) (hh : ContDiffOn ℝ 2 h U)
    (hs : Metric.closedBall c η.rOut ⊆ U) :
    ContDiff ℝ 2 (fun x ↦ η x * h x) ∧
    HasCompactSupport (fun x ↦ η x * h x) ∧
    ∀ x ∈ Metric.ball c η.rIn, ∀ k : ℕ,
      iteratedFDeriv ℝ k (fun y ↦ η y * h y) x = iteratedFDeriv ℝ k h x := by
  refine ⟨contDiff_cutoff_mul hU (η.contDiff (n := 2)) hh ?_,
    η.hasCompactSupport.mul_right, ?_⟩
  · simpa only [η.tsupport_eq] using hs
  · exact fun x hx k ↦ iteratedFDeriv_bump_mul η h hx k
end FunctionalInequalities.Analysis
