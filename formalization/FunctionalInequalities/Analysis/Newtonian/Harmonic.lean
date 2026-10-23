import FunctionalInequalities.Analysis.Newtonian.Trace
import FunctionalInequalities.Analysis.Newtonian.First
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic

/-!
# Harmonicity of the Newtonian kernel off the origin

In Mathlib's vocabulary, for `n ≥ 2`: `laplacian_newtonianKernel_eq_zero` (`ΔΓ(x) = 0` for `x ≠ 0`),
`harmonicAt_newtonianKernel` and `harmonicOnNhd_newtonianKernel` (on `{0}ᶜ`), for the kernel of
Gilbarg–Trudinger, *Elliptic Partial Differential Equations of Second Order*, Classics 2001
(ISBN 3-540-41160-7), (2.12). Nothing is asserted at the singularity.
-/

noncomputable section

open scoped Topology
open InnerProductSpace

namespace FunctionalInequalities.Analysis

/-- The actual Mathlib Laplacian of the normalized kernel vanishes off zero. -/
theorem laplacian_newtonianKernel_eq_zero {n : ℕ} (hn : 2 ≤ n)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ≠ 0) :
    Laplacian.laplacian (newtonianKernel n) x = 0 := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis
    (newtonianKernel n) (EuclideanSpace.basisFun (Fin n) ℝ)]
  simp_rw [← bilinearIteratedFDerivTwo_eq_iteratedFDeriv]
  exact sum_bilinear_newtonianKernel_basis_self_eq_zero hn x hx

/-- Off-origin harmonicity in the existing Mathlib predicate. -/
theorem harmonicAt_newtonianKernel {n : ℕ} (hn : 2 ≤ n)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ≠ 0) :
    HarmonicAt (newtonianKernel n) x := by
  refine ⟨contDiffAt_newtonianKernel hn x hx 2, ?_⟩
  filter_upwards [eventually_ne_nhds hx] with y hy
  exact laplacian_newtonianKernel_eq_zero hn y hy

theorem harmonicOnNhd_newtonianKernel {n : ℕ} (hn : 2 ≤ n) :
    HarmonicOnNhd (newtonianKernel n) ({0}ᶜ : Set (EuclideanSpace ℝ (Fin n))) := by
  intro x hx
  exact harmonicAt_newtonianKernel hn x (by simpa only [Set.mem_compl_iff,
    Set.mem_singleton_iff] using hx)

end FunctionalInequalities.Analysis
