module

public import FunctionalInequalities.Analysis.IteratedDerivative.Affine
public import FunctionalInequalities.Analysis.Cutoff.LocalRegularity
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith

/-!
# Audit: affine derivative scaling and local cutoffs

Real clients of `FunctionalInequalities/Analysis/IteratedDerivative/Affine.lean` and
`FunctionalInequalities/Analysis/Cutoff/LocalRegularity.lean` (support for Gilbarg–Trudinger,
Classics 2001,
Theorem 4.6, p. 60): nonzero harmonic linear functions on `ℝ` and `ℝ²` with their actual affine
derivative and
Laplacian scaling and a transferred physical derivative cap, and a reciprocal source regular only on
the
cutoff domain. No harmonic representation or derivative estimate is assumed or claimed.
-/

@[expose] public section
noncomputable section
open scoped Topology
open InnerProductSpace Laplacian
namespace AffineDerivativeScaleAudit
open FunctionalInequalities.Analysis

def linearH (x : ℝ) : ℝ := x

theorem linearH_harmonic : HarmonicOnNhd linearH Set.univ := by
  intro x _
  refine ⟨contDiffAt_id, ?_⟩
  filter_upwards with y
  simp only [laplacian_eq_iteratedDeriv_real, iteratedDeriv_succ]
  change deriv (deriv (fun z : ℝ ↦ z)) y = 0
  simp

theorem linearH_nonzero : linearH 1 = 1 := rfl

theorem linearH_scaled_first (x : ℝ) :
    ‖iteratedFDeriv ℝ 1 (fun z ↦ linearH (2 + (3 : ℝ) • z)) x‖ = 3 := by
  rw [norm_iteratedFDeriv_affine]
  rw [norm_iteratedFDeriv_one]
  change |(3 : ℝ)| ^ 1 * ‖fderiv ℝ id (2 + 3 * x)‖ = 3
  norm_num [fderiv_id]

theorem linearH_physical_cap : ∀ y ∈ Metric.ball (2 : ℝ) 3,
    ‖iteratedFDeriv ℝ 1 linearH y‖ ≤ 1 := by
  have hcap : ∀ x ∈ Metric.ball (0 : ℝ) 1,
      ‖iteratedFDeriv ℝ 1 (fun z ↦ linearH (2 + (3 : ℝ) • z)) x‖ ≤ 3 := by
    intro x _
    exact (linearH_scaled_first x).le
  have h := derivative_cap_transfer linearH 2 (by norm_num : (0 : ℝ) < 3) 1 hcap
  norm_num at h
  simpa only [Metric.mem_ball, norm_iteratedFDeriv_one] using h

def planeH (x : EuclideanSpace ℝ (Fin 2)) : ℝ := x 0

theorem planeH_harmonic : HarmonicOnNhd planeH Set.univ := by
  intro x _
  have hid : HarmonicAt (fun z : EuclideanSpace ℝ (Fin 2) ↦ z) x := by
    refine ⟨contDiffAt_id, ?_⟩
    filter_upwards with y
    have hder : fderiv ℝ (fun z : EuclideanSpace ℝ (Fin 2) ↦ z) =
        fun _ ↦ ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2)) := funext fun z ↦ fderiv_id
    simp only [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis, iteratedFDeriv_two_apply]
    rw [hder]
    simp
  exact hid.comp_CLM (PiLp.proj (𝕜 := ℝ) (p := 2) (β := fun _ : Fin 2 ↦ ℝ) 0)

theorem planeH_nonzero : planeH (EuclideanSpace.single 0 1) = 1 := by
  simp [planeH]

theorem planeH_scaled_laplacian (c : EuclideanSpace ℝ (Fin 2)) (a : ℝ)
    (x : EuclideanSpace ℝ (Fin 2)) :
    Δ (fun z ↦ planeH (c + a • z)) x = 0 := by
  rw [laplacian_affine]
  have hz : Δ planeH (c + a • x) = 0 :=
    (planeH_harmonic (c + a • x) (Set.mem_univ _)).2.self_of_nhds
  rw [hz, smul_zero]

def unitBump : ContDiffBump (0 : ℝ) := ⟨1, 3 / 2, by norm_num, by norm_num⟩
def localSource (x : ℝ) : ℝ := (3 - x)⁻¹

theorem localSource_regular : ContDiffOn ℝ 2 localSource (Metric.ball (0 : ℝ) 2) := by
  apply (contDiff_const.sub contDiff_id).contDiffOn.inv
  intro x hx
  change (3 : ℝ) - x ≠ 0
  have hnorm : |x| < 2 := by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hx
  have hxlt := (abs_lt.mp hnorm).2
  linarith

theorem cutoff_source :
    ContDiff ℝ 2 (fun x ↦ unitBump x * localSource x) ∧
    HasCompactSupport (fun x ↦ unitBump x * localSource x) ∧
    ∀ x ∈ Metric.ball (0 : ℝ) unitBump.rIn, ∀ k : ℕ,
      iteratedFDeriv ℝ k (fun y ↦ unitBump y * localSource y) x =
        iteratedFDeriv ℝ k localSource x := by
  apply bump_mul_local unitBump Metric.isOpen_ball localSource_regular
  intro x hx
  have hx' : dist x 0 ≤ (3 : ℝ) / 2 := hx
  show dist x 0 < 2
  linarith

theorem cutoff_source_nonzero : unitBump 0 * localSource 0 = 1 / 3 := by
  rw [unitBump.one_of_mem_closedBall (Metric.mem_closedBall_self unitBump.rIn_pos.le)]
  norm_num [localSource]
end AffineDerivativeScaleAudit

#print axioms AffineDerivativeScaleAudit.linearH_harmonic
#print axioms AffineDerivativeScaleAudit.linearH_nonzero
#print axioms AffineDerivativeScaleAudit.linearH_scaled_first
#print axioms AffineDerivativeScaleAudit.linearH_physical_cap
#print axioms AffineDerivativeScaleAudit.planeH_harmonic
#print axioms AffineDerivativeScaleAudit.planeH_nonzero
#print axioms AffineDerivativeScaleAudit.planeH_scaled_laplacian
#print axioms AffineDerivativeScaleAudit.localSource_regular
#print axioms AffineDerivativeScaleAudit.cutoff_source
#print axioms AffineDerivativeScaleAudit.cutoff_source_nonzero
