module

public import FunctionalInequalities.Analysis.Elliptic.Operator
public import FunctionalInequalities.Analysis.Convex.Quadratic
public import FunctionalInequalities.Analysis.Convex.Viscosity.Touching
public import FunctionalInequalities.Analysis.Matrix.Positivity

/-!
# Maximum principles and quadratic barriers for linear elliptic operators

CNS1984 section2 pp374-376 and Lemma5.1 pp385-387 use these ordinary
maximum/comparison tools. Bounded open domains need not be convex; zero
dimension and empty domains are included. Coefficients and drift need not be
continuous or bounded. Strict positivity is required only above the threshold.
The weak theorem additionally requires positive coefficient trace. A symmetric
part generated from the raw quadratic form handles nonsymmetric coefficients.
These estimates do not construct a linear inverse or a classical solution.
-/

@[expose] public section
noncomputable section
open Set Metric Filter
open scoped RealInnerProductSpace Topology
namespace FunctionalInequalities.Analysis
open Probability.Stein

private lemma trace_hessian_nonpos_of_isLocalMax {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hu : ContDiffAt ℝ 2 u x) (hm : IsLocalMax u x)
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef) :
    Matrix.trace (A * hessianMatrix u x) ≤ 0 := by
  have hc : ConvexOn ℝ univ (fun _ : EuclideanSpace ℝ (Fin n) => (0 : ℝ)) :=
    ⟨convex_univ, by intros; simp⟩
  have hps := posSemidef_hessianMatrix_of_upper_touch hc (contDiffAt_const.sub hu)
    (show (0 : ℝ) = u x - u x by ring) (hm.mono fun y hy => sub_nonneg.mpr hy)
  rw [hessianMatrix_sub_of_contDiffAt contDiffAt_const hu, hessianMatrix_const_fun, zero_sub] at hps
  have hnonneg := trace_mul_nonneg hA hps
  simp only [Matrix.mul_neg, Matrix.trace_neg] at hnonneg
  linarith

/--
**Strict drift maximum principle** (supporting the CNS1984 Lemma 5.1 comparison, pp. 386–387): if
the drift
operator `tr(A D²u) + ∑ bᵢ ∂ᵢu` is strictly positive wherever `u` exceeds `M`, then `M` bounds `u`
on the closure.
Any `n`, empty or nonconvex bounded open `Ω`; no coefficient continuity, bound or trace positivity.
The compact
maximum is interior, where `IsLocalMax.fderiv_eq_zero` kills the drift and the upper-touch trace
sign applies. -/
theorem strict_drift_maximum_principle {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {A : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ}
    {b : EuclideanSpace ℝ (Fin n) → Fin n → ℝ} {M : ℝ} (hΩ : IsOpen Ω)
    (hb : Bornology.IsBounded Ω) (hu : ContDiffOn ℝ 2 u Ω) (huc : ContinuousOn u (closure Ω))
    (hA : ∀ x ∈ Ω, (A x).PosSemidef)
    (hLu :
      ∀ x ∈ Ω,
        M < u x →
          0 <
            Matrix.trace (A x * hessianMatrix u x) +
              ∑ i, b x i * fderiv ℝ u x (EuclideanSpace.single i 1))
    (hbd : ∀ x ∈ frontier Ω, u x ≤ M) : ∀ x ∈ closure Ω, u x ≤ M := by
  intro x₀ hx₀
  by_contra hnot
  obtain ⟨x, hxcl, hxmax⟩ := hb.isCompact_closure.exists_isMaxOn ⟨x₀, hx₀⟩ huc
  have hux : M < u x := (lt_of_not_ge hnot).trans_le (hxmax hx₀)
  have hx : x ∈ Ω := by
    by_contra hx
    have hfr : x ∈ frontier Ω := ⟨hxcl, by rwa [hΩ.interior_eq]⟩
    exact (not_le.mpr hux) (hbd x hfr)
  have hmax : IsLocalMax u x :=
    hxmax.isLocalMax (mem_of_superset (hΩ.mem_nhds hx) subset_closure)
  have ht := trace_hessian_nonpos_of_isLocalMax (hu.contDiffAt (hΩ.mem_nhds hx)) hmax (hA x hx)
  have hdrift : ∑ i, b x i * fderiv ℝ u x (EuclideanSpace.single i 1) = 0 := by
    simp [hmax.fderiv_eq_zero]
  linarith [hLu x hx hux]

/-- The actual linear maximum principle, with no coefficient continuity or convexity of Ω. -/
theorem linearized_maximum_principle {n : ℕ}
    {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {A : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ}
    {M : ℝ} (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hu : ContDiffOn ℝ 2 u Ω) (huc : ContinuousOn u (closure Ω))
    (hA : ∀ x ∈ Ω, (A x).PosSemidef ∧ 0 < (A x).trace)
    (hLu : ∀ x ∈ Ω, 0 ≤ Matrix.trace (A x * Probability.Stein.hessianMatrix u x))
    (hbd : ∀ x ∈ frontier Ω, u x ≤ M) :
    ∀ x ∈ closure Ω, u x ≤ M := by
  intro x₀ hx₀
  by_contra hnot
  obtain ⟨R, hR⟩ := hb.subset_closedBall (0 : EuclideanSpace ℝ (Fin n))
  have hRc : closure Ω ⊆ closedBall (0 : EuclideanSpace ℝ (Fin n)) R :=
    closure_minimal hR isClosed_closedBall
  have hnorm : ∀ y ∈ closure Ω, ‖y‖ ^ 2 ≤ R ^ 2 := fun y hy =>
    pow_le_pow_left₀ (norm_nonneg y) (by simpa using hRc hy) 2
  let ε : ℝ := (u x₀ - M) / (2 * (R ^ 2 + 1))
  have hε : 0 < ε := by dsimp [ε]; have := sub_pos.mpr (lt_of_not_ge hnot); positivity
  have hq : ContDiff ℝ 2 (fun y : EuclideanSpace ℝ (Fin n) => ε * ‖y‖ ^ 2) :=
    contDiff_const.mul (contDiff_norm_sq ℝ)
  -- the strict core for `u + ε‖·‖²`, zero drift, threshold `M + εR²`
  have hs := strict_drift_maximum_principle (b := fun _ _ => 0) (M := M + ε * R ^ 2) hΩ hb
    (hu.add hq.contDiffOn) (huc.add hq.continuous.continuousOn) (fun x hx => (hA x hx).1)
    (fun x hx _ => by
      have hux : ContDiffAt ℝ 2 u x := hu.contDiffAt (hΩ.mem_nhds hx)
      have hH : hessianMatrix (fun y => u y + ε * ‖y‖ ^ 2) x = hessianMatrix u x + (2 * ε) • 1 := by
        rw [hessianMatrix_add_of_contDiffAt hux hq.contDiffAt]
        simpa only [sub_zero] using congrArg (fun B => hessianMatrix u x + B)
          (hessianMatrix_mul_norm_sub_sq ε 0 x)
      rw [hH, Matrix.mul_add, Matrix.trace_add, Matrix.mul_smul, Matrix.mul_one,
        Matrix.trace_smul, smul_eq_mul]
      simp only [zero_mul, Finset.sum_const_zero, add_zero]
      have hpos : 0 < (2 * ε) * (A x).trace := mul_pos (by positivity) (hA x hx).2
      linarith [hLu x hx])
    (fun x hx => by
      have h1 := hnorm x (frontier_subset_closure hx)
      have h2 := hbd x hx
      nlinarith [hε.le])
    x₀ hx₀
  have htop : ε * R ^ 2 < u x₀ - M := by
    have hδ : 0 < u x₀ - M := sub_pos.mpr (lt_of_not_ge hnot)
    dsimp [ε]
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  have hsq : 0 ≤ ε * ‖x₀‖ ^ 2 := by positivity
  change u x₀ + ε * ‖x₀‖ ^ 2 ≤ M + ε * R ^ 2 at hs
  linarith

private lemma linearized_le_barrier {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {A : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ}
    {c : EuclideanSpace ℝ (Fin n)} {R B F τ : ℝ} (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hball : closure Ω ⊆ closedBall c R) (hF : 0 ≤ F) (hτ : 0 < τ) (hu : ContDiffOn ℝ 2 u Ω)
    (huc : ContinuousOn u (closure Ω)) (hA : ∀ x ∈ Ω, (A x).PosSemidef ∧ τ ≤ (A x).trace)
    (hLu : ∀ x ∈ Ω, -F ≤ Matrix.trace (A x * hessianMatrix u x))
    (hbd : ∀ x ∈ frontier Ω, u x ≤ B) :
    ∀ x ∈ closure Ω, u x ≤ B + F / (2 * τ) * (R ^ 2 - ‖x - c‖ ^ 2) := by
  let k : ℝ := F / (2 * τ)
  let q : EuclideanSpace ℝ (Fin n) → ℝ := fun y => B + k * (R ^ 2 - ‖y - c‖ ^ 2)
  have hk : 0 ≤ k := div_nonneg hF (by positivity)
  have hnc : ContDiff ℝ 2 (fun y : EuclideanSpace ℝ (Fin n) => ‖y - c‖ ^ 2) :=
    (contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)
  have hq : ContDiff ℝ 2 q := contDiff_const.add (contDiff_const.mul (contDiff_const.sub hnc))
  have hq_eq : q = fun y => (B + k * R ^ 2) + (-k) * ‖y - c‖ ^ 2 := by
    funext y
    dsimp only [q]
    ring
  have hHq : ∀ x, hessianMatrix q x = (-(2 * k)) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
    intro x
    rw [hq_eq,
      hessianMatrix_add_of_contDiffAt contDiffAt_const (contDiffAt_const.mul hnc.contDiffAt),
      hessianMatrix_const_fun, zero_add, hessianMatrix_mul_norm_sub_sq]
    congr 1
    ring
  have hqbd : ∀ x ∈ closure Ω, B ≤ q x := by
    intro x hx
    have hn : ‖x - c‖ ≤ R := by simpa [mem_closedBall, dist_eq_norm] using hball hx
    have hs := pow_le_pow_left₀ (norm_nonneg (x - c)) hn 2
    dsimp only [q]
    exact le_add_of_nonneg_right (mul_nonneg hk (sub_nonneg.mpr hs))
  have hLq : ∀ x ∈ Ω, 0 ≤ Matrix.trace (A x * hessianMatrix (fun y => u y - q y) x) := by
    intro x hx
    have hux := hu.contDiffAt (hΩ.mem_nhds hx)
    have hlin :=
      elliptic_operator_linear_combination (A x) (0 : EuclideanSpace ℝ (Fin n)) 0 1 (-1) hux
        hq.contDiffAt
    have hT :
      Matrix.trace (A x * hessianMatrix (fun y => u y - q y) x) =
        Matrix.trace (A x * hessianMatrix u x) - Matrix.trace (A x * hessianMatrix q x) := by
      simpa only [one_mul, neg_one_mul, map_zero, mul_zero, zero_mul, add_zero,
        sub_eq_add_neg] using hlin
    rw [hT, hHq x, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, smul_eq_mul]
    have hid : (2 * k) * τ = F := by
      dsimp only [k]
      field_simp
    have hmin : F ≤ (2 * k) * (A x).trace := by
      rw [← hid]
      exact mul_le_mul_of_nonneg_left (hA x hx).2 (by positivity)
    nlinarith [hLu x hx]
  have hs :=
    linearized_maximum_principle hΩ hb (hu.sub hq.contDiffOn)
      (huc.sub hq.continuous.continuousOn) (fun x hx => ⟨(hA x hx).1, hτ.trans_le (hA x hx).2⟩)
      hLq (fun x hx => sub_nonpos.mpr ((hbd x hx).trans (hqbd x (frontier_subset_closure hx))))
  intro x hx
  have h := hs x hx
  change u x - q x ≤ (0 : ℝ) at h
  exact sub_nonpos.mp h

/-- A concrete quadratic barrier gives a linear C0 estimate without a supplied inverse. -/
theorem abs_le_linearized_c0_barrier {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {A : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ}
    {c : EuclideanSpace ℝ (Fin n)} {R B F τ : ℝ} (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hball : closure Ω ⊆ Metric.closedBall c R) (hR : 0 ≤ R) (hB : 0 ≤ B) (hF : 0 ≤ F)
    (hτ : 0 < τ) (hu : ContDiffOn ℝ 2 u Ω) (huc : ContinuousOn u (closure Ω))
    (hA : ∀ x ∈ Ω, (A x).PosSemidef ∧ τ ≤ (A x).trace)
    (hLu : ∀ x ∈ Ω, |Matrix.trace (A x * Probability.Stein.hessianMatrix u x)| ≤ F)
    (hbd : ∀ x ∈ frontier Ω, |u x| ≤ B) :
    ∀ x ∈ closure Ω, |u x| ≤ B + F / (2 * τ) * (R ^ 2 - ‖x - c‖ ^ 2) := by
  have hp :=
    linearized_le_barrier hΩ hb hball hF hτ hu huc hA (fun x hx => (abs_le.mp (hLu x hx)).1)
      (fun x hx => (le_abs_self (u x)).trans (hbd x hx))
  have hm :=
    linearized_le_barrier hΩ hb hball hF hτ hu.neg huc.neg hA
      (fun x hx => by
        rw [hessianMatrix_neg_of_contDiffAt (hu.contDiffAt (hΩ.mem_nhds hx)), Matrix.mul_neg,
          Matrix.trace_neg]
        linarith [(abs_le.mp (hLu x hx)).2])
      (fun x hx => (neg_le_abs (u x)).trans (hbd x hx))
  intro x hx
  have hn : ‖x - c‖ ^ 2 ≤ R ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hR).mpr (by simpa [mem_closedBall, dist_eq_norm] using hball hx)
  have hnonneg : 0 ≤ B + F / (2 * τ) * (R ^ 2 - ‖x - c‖ ^ 2) :=
    add_nonneg hB (mul_nonneg (div_nonneg hF (by positivity)) (sub_nonneg.mpr hn))
  have hp' : u x ≤ max (B + F / (2 * τ) * (R ^ 2 - ‖x - c‖ ^ 2)) 0 :=
    (hp x hx).trans (le_max_left _ _)
  have hm' : -u x ≤ max (B + F / (2 * τ) * (R ^ 2 - ‖x - c‖ ^ 2)) 0 :=
    (hm x hx).trans (le_max_left _ _)
  rw [max_eq_left hnonneg] at hp' hm'
  exact abs_le.mpr ⟨by linarith, hp'⟩


/-- The coordinate Hessian of a function that is `C²` at `x` is symmetric there. -/
private lemma hessianMatrix_isHermitian_of_contDiffAt {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanSpace ℝ (Fin n)} (hu : ContDiffAt ℝ 2 u x) : (hessianMatrix u x).IsHermitian := by
  ext i j
  rw [Matrix.conjTranspose_apply, star_trivial]
  exact BakryEmery.bilinearIteratedFDerivTwo_symm_at hu _ _

theorem strict_drift_maximum_principle_of_quadratic_nonneg {n : ℕ}
    {Ω : Set (EuclideanSpace ℝ (Fin n))} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {A : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ}
    {b : EuclideanSpace ℝ (Fin n) → Fin n → ℝ} {M : ℝ} (hΩ : IsOpen Ω)
    (hb : Bornology.IsBounded Ω) (hu : ContDiffOn ℝ 2 u Ω) (huc : ContinuousOn u (closure Ω))
    (hA : ∀ x ∈ Ω, ∀ v : Fin n → ℝ, 0 ≤ ∑ i, ∑ j, A x i j * v i * v j)
    (hLu :
      ∀ x ∈ Ω,
        M < u x →
          0 <
            Matrix.trace (A x * hessianMatrix u x) +
              ∑ i, b x i * fderiv ℝ u x (EuclideanSpace.single i 1))
    (hbd : ∀ x ∈ frontier Ω, u x ≤ M) : ∀ x ∈ closure Ω, u x ≤ M := by
  -- the pointwise normalization, prepared ONCE and projected for positivity and the trace rewrite

  have hnorm := fun x (hx : x ∈ Ω) =>
    posSemidef_symmetricPart_of_quadratic_nonneg (A x) (hA x hx)
  exact
    strict_drift_maximum_principle (A := fun x => (1 / 2 : ℝ) • (A x + (A x).transpose)) (b :=
      b) hΩ hb hu huc (fun x hx => (hnorm x hx).1)
      (fun x hx hux => by
        beta_reduce
        rw [(hnorm x hx).2.2 _
            (hessianMatrix_isHermitian_of_contDiffAt (hu.contDiffAt (hΩ.mem_nhds hx)))]
        exact hLu x hx hux)
      hbd


end FunctionalInequalities.Analysis
