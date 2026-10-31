module

public import FunctionalInequalities.Analysis.IteratedDerivative.OperatorNorm
public import FunctionalInequalities.Analysis.IteratedDerivative.LocalHolder
public import FunctionalInequalities.Analysis.IteratedDerivative.Bootstrap.LinearEquation
public import FunctionalInequalities.Analysis.Matrix.CompactEllipticity

/-!
# Higher-order interior regularity for linear elliptic equations

Gilbarg–Trudinger, Classics 2001 (ISBN 3-540-41160-7), Theorem 6.2, pp. 90–92,
and the repeated difference-quotient argument of Lemma 17.16, pp. 463–464; supporting
Letwin arXiv:2607.24164v1, Lemma 2.2, strong-class smoothness.

For n ≥ 2, a given locally C^{2,α} solution of Σ aⁱʲ Dᵢⱼw + Σ bⁱ Dᵢw + w = g,
with symmetric locally uniformly elliptic a and locally C^{m+1,α} data a, b, g,
is locally C^{m+3,α}. Exponents and bounds may depend on the ball. The proof first
obtains uniform local third-derivative estimates, patches them on each ball, and
then differentiates the equation and inducts on the order. The given solution is retained.
-/

@[expose] public section

local macro "nat_cast_le" : tactic => `(tactic| first | (norm_cast; done) | (norm_cast; omega))

noncomputable section

namespace FunctionalInequalities.Analysis

open scoped FunctionalInequalities.Analysis.DerivativeNorms

open Set Metric Filter Topology
open scoped NNReal ContDiff BigOperators

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)


/-- Positive quadratic bounds uniform on each closed ball. -/
def LocallyUniformElliptic (a : Fin n → Fin n → E → ℝ) : Prop :=
  ∀ s : ℝ, 0 < s → ∃ lam Lam : ℝ, 0 < lam ∧ lam ≤ Lam ∧
    ∀ x ∈ closedBall (0 : E) s, ∀ ξ : E,
      lam * ‖ξ‖ ^ 2 ≤ ∑ i, ∑ j, a i j x * ξ i * ξ j ∧
        (∑ i, ∑ j, a i j x * ξ i * ξ j) ≤ Lam * ‖ξ‖ ^ 2

private lemma local_caps_family {ι : Type*} [Fintype ι] {G : Type*}
    [NormedAddCommGroup G] {F : ι → E → G} (hF : ∀ i, LocHolderMap (F i))
    {r : ℝ} (hr : 0 < r) :
    ∃ η₀ : ℝ≥0, 0 < η₀ ∧ η₀ < 1 ∧
      ∀ η : ℝ≥0, 0 < η → η ≤ η₀ →
        ∃ K : ℝ, 0 ≤ K ∧
          ∀ i, ∀ x ∈ closedBall (0 : E) r, ‖F i x‖ ≤ K ∧
            ∀ y ∈ closedBall (0 : E) r,
              ‖F i x - F i y‖ ≤ K * ‖x - y‖ ^ (η : ℝ) := by
  have hr' : 0 < r + 1 := by linarith
  choose η hη0 hη1 C hC hhol using fun i => hF i (r + 1) hr'
  obtain ⟨η₀, hη₀0, hη₀1, hη₀le⟩ := exists_common_exponent η hη0 hη1
  choose B hB hBnd using fun i => (hF i).exists_bound hr'
  refine ⟨η₀, hη₀0, hη₀1, ?_⟩
  intro β hβ hβle
  let D : ℝ := 2 * (r + 1)
  let K : ℝ := ∑ i, (B i + C i * D ^ ((η i : ℝ) - (β : ℝ)))
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hK : 0 ≤ K := by
    dsimp [K]
    exact Finset.sum_nonneg fun i _ =>
      add_nonneg (hB i) (mul_nonneg (hC i) (Real.rpow_nonneg hD _))
  refine ⟨K, hK, ?_⟩
  have hsub : closedBall (0 : E) r ⊆ ball 0 (r + 1) := by
    intro x hx
    rw [mem_closedBall, dist_eq_norm] at hx
    rw [mem_ball_zero_iff]
    have hx' : ‖x‖ ≤ r := by simpa using hx
    linarith
  have hdiam : ∀ x ∈ ball (0 : E) (r + 1), ∀ y ∈ ball (0 : E) (r + 1),
      ‖x - y‖ ≤ D := by
    intro x hx y hy
    dsimp [D]
    exact norm_sub_le_two_mul_of_mem_ball hx hy
  intro i x hx
  have hterm : B i + C i * D ^ ((η i : ℝ) - (β : ℝ)) ≤ K := by
    dsimp [K]
    exact Finset.single_le_sum (f := fun j => B j + C j * D ^ ((η j : ℝ) - (β : ℝ)))
      (fun j _ => add_nonneg (hB j) (mul_nonneg (hC j) (Real.rpow_nonneg hD _)))
      (Finset.mem_univ i)
  have hBi : B i ≤ K :=
    (le_add_of_nonneg_right (mul_nonneg (hC i) (Real.rpow_nonneg hD _))).trans hterm
  have hCi : C i * D ^ ((η i : ℝ) - (β : ℝ)) ≤ K :=
    (le_add_of_nonneg_left (hB i)).trans hterm
  refine ⟨(hBnd i x (hsub hx)).trans hBi, ?_⟩
  have hleη : (β : ℝ) ≤ (η i : ℝ) := by
    exact_mod_cast le_trans hβle (hη₀le i)
  have hlow := holder_lower_exponent (hC i) hleη (by exact_mod_cast hη0 i)
    hdiam (hhol i)
  intro y hy
  have hxy := hlow x (hsub hx) y (hsub hy)
  have hpow : 0 ≤ ‖x - y‖ ^ (β : ℝ) := by positivity
  exact hxy.trans (mul_le_mul_of_nonneg_right hCi hpow)

private lemma norm_iteratedFDeriv_three_eq {f : E → ℝ} (x : E) :
    ‖iteratedFDeriv ℝ 3 f x‖ =
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ f)) x‖ := by
  simp only [iteratedFDeriv_succ_eq_comp_right, iteratedFDeriv_zero_eq_comp,
    Function.comp_apply, LinearIsometryEquiv.norm_map]

private lemma local_linear_schauder_data (hn : 2 ≤ n)
    {w g : E → ℝ} {a : Fin n → Fin n → E → ℝ} {b : Fin n → E → ℝ}
    (hw : LocHolderDeriv 2 w) (ha : ∀ i j, LocHolderDeriv 1 (a i j))
    (hb : ∀ i, LocHolderDeriv 1 (b i)) (hg : LocHolderDeriv 1 g)
    (hsymm : ∀ x i j, a i j x = a j i x)
    (hell : LocallyUniformElliptic a)
    (heq : ∀ x, (∑ i, ∑ j, a i j x * fderiv ℝ (fderiv ℝ w) x
        (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)) +
        (∑ i, b i x * fderiv ℝ w x (EuclideanSpace.basisFun (Fin n) ℝ i)) + w x = g x)
    {s : ℝ} (hs : 0 < s) :
    ∃ α : ℝ≥0, 0 < α ∧ α < 1 ∧ ∃ R K : ℝ, 0 < R ∧ 0 ≤ K ∧
      ∀ c ∈ ball (0 : E) s,
        ContDiffOn ℝ 3 w (ball c R) ∧
        (∀ x ∈ ball c R,
          ‖fderiv ℝ (fderiv ℝ (fderiv ℝ w)) x‖ ≤ K) ∧
        ∀ x ∈ ball c R, ∀ y ∈ ball c R,
          ‖fderiv ℝ (fderiv ℝ (fderiv ℝ w)) x -
              fderiv ℝ (fderiv ℝ (fderiv ℝ w)) y‖ ≤
            K * ‖x - y‖ ^ (α : ℝ) := by
  have hA : ∀ i j, LocHolderMap (fun x => fderiv ℝ (a i j) x) := by
    intro i j
    exact (ha i j).2.of_le_norm zero_le_one fun x y => by
      rw [one_mul, norm_iteratedFDeriv_one_sub]
  have hB : ∀ i, LocHolderMap (fun x => b i x) :=
    fun i => locHolderDeriv_zero_iff.mp (hb i).weaken
  have hBd : ∀ i, LocHolderMap (fun x => fderiv ℝ (b i) x) := by
    intro i
    exact (hb i).2.of_le_norm zero_le_one fun x y => by
      rw [one_mul, norm_iteratedFDeriv_one_sub]
  have hG : LocHolderMap (fun x => fderiv ℝ g x) :=
    hg.2.of_le_norm zero_le_one fun x y => by
      rw [one_mul, norm_iteratedFDeriv_one_sub]
  have hH : LocHolderMap (fun x => fderiv ℝ (fderiv ℝ w) x) :=
    hw.2.of_le_norm zero_le_one fun x y => by
      rw [one_mul, norm_iteratedFDeriv_two_sub]
  have hAfam : ∀ p : Fin n × Fin n, LocHolderMap (fun x => fderiv ℝ (a p.1 p.2) x) := by
    intro p; exact hA p.1 p.2
  have hBfam : ∀ i : Fin n, LocHolderMap (fun x => b i x) := by
    intro i; exact hB i
  have hBdfam : ∀ i : Fin n, LocHolderMap (fun x => fderiv ℝ (b i) x) := by
    intro i; exact hBd i
  have hHfam : ∀ _ : Unit, LocHolderMap (fun x => fderiv ℝ (fderiv ℝ w) x) := by
    intro u; exact hH
  have hbig : 0 < s + 2 := by linarith
  obtain ⟨ηA, hηA0, hηA1, hηAcap⟩ := local_caps_family hAfam hbig
  obtain ⟨ηB, hηB0, hηB1, hηBcap⟩ := local_caps_family hBfam hbig
  obtain ⟨ηBd, hηBd0, hηBd1, hηBdcap⟩ := local_caps_family hBdfam hbig
  obtain ⟨ηG, hηG0, hηG1, hηGcap⟩ := local_caps_family (ι := Unit)
    (fun _ => hG) hbig
  obtain ⟨ηH, hηH0, hηH1, hηHcap⟩ := local_caps_family hHfam hbig
  let α : ℝ≥0 := min (min ηA ηB) (min (min ηBd ηG) ηH)
  have hα0 : 0 < α := by
    dsimp [α]
    exact lt_min (lt_min hηA0 hηB0) (lt_min (lt_min hηBd0 hηG0) hηH0)
  have hα1 : α < 1 := by
    have hle : α ≤ ηA := by
      dsimp [α]
      exact (min_le_left _ _).trans (min_le_left _ _)
    exact hle.trans_lt hηA1
  have hαA : α ≤ ηA := by dsimp [α]; exact (min_le_left _ _).trans (min_le_left _ _)
  have hαB : α ≤ ηB := by dsimp [α]; exact (min_le_left _ _).trans (min_le_right _ _)
  have hαBd : α ≤ ηBd := by
    dsimp [α]
    exact (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hαG : α ≤ ηG := by
    dsimp [α]
    exact (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hαH : α ≤ ηH := by
    dsimp [α]
    exact (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨KA, hKA, hAcap⟩ := hηAcap α hα0 hαA
  obtain ⟨KB, hKB, hBcap⟩ := hηBcap α hα0 hαB
  obtain ⟨KBd, hKBd, hBdCap⟩ := hηBdcap α hα0 hαBd
  obtain ⟨KG, hKG, hGcap⟩ := hηGcap α hα0 hαG
  obtain ⟨KH, hKH, hHcap⟩ := hηHcap α hα0 hαH
  obtain ⟨lam, Lam, hlam, hLam, hellbig⟩ := hell (s + 2) hbig
  have hgradC : ContinuousOn (fderiv ℝ w) (closedBall (0 : E) (s + 2)) :=
    ((hw.1.fderiv_right (m := 1) (by norm_num)).continuous).continuousOn
  obtain ⟨Ngrad, hNgrad⟩ :=
    (isCompact_closedBall (0 : E) (s + 2)).exists_bound_of_continuousOn hgradC
  have hNgrad0 : 0 ≤ Ngrad :=
    (norm_nonneg _).trans (hNgrad 0 (mem_closedBall_self hbig.le))
  let K : ℝ := KA + KB + KBd + KG + KH + Ngrad + 1
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  have hmem : ∀ c ∈ ball (0 : E) s, ∀ x ∈ closedBall c 1,
      x ∈ closedBall (0 : E) (s + 2) := by
    intro c hc x hx
    rw [mem_ball_zero_iff] at hc
    rw [mem_closedBall, dist_eq_norm] at hx ⊢
    have he : ‖x‖ = ‖(x - c) + c‖ := by congr 1; abel
    rw [sub_zero, he]
    calc
      ‖(x - c) + c‖ ≤ ‖x - c‖ + ‖c‖ := norm_add_le _ _
      _ ≤ s + 2 := by linarith
  have hKA' : KA ≤ K := by dsimp [K]; linarith
  have hKB' : KB ≤ K := by dsimp [K]; linarith
  have hKBd' : KBd ≤ K := by dsimp [K]; linarith
  have hKG' : KG ≤ K := by dsimp [K]; linarith
  have hKH' : KH ≤ K := by dsimp [K]; linarith
  have hNgrad' : Ngrad ≤ K := by dsimp [K]; linarith
  obtain ⟨R, Kc, hR, hKc, hstep⟩ :=
    contDiffOn_three_ball_of_linear_equation hn
      (α := α) (by exact_mod_cast hα0) (by exact_mod_cast hα1)
      hlam hLam (S := 1) one_pos
      (Ka := K) (Kb := K) (Kg := K) (Nw := K) hK hK hK hK
  refine ⟨α, hα0, hα1, R, Kc, hR, hKc, ?_⟩
  intro c hc
  have hbase : ∀ x ∈ closedBall c 1, x ∈ closedBall (0 : E) (s + 2) :=
    hmem c hc
  have hsym : ∀ x ∈ closedBall c 1, ∀ i j, a i j x = a j i x := by
    intro x hx i j
    exact hsymm x i j
  have hellc : ∀ x ∈ closedBall c 1, ∀ ξ : E,
      lam * ‖ξ‖ ^ 2 ≤ ∑ i, ∑ j, a i j x * ξ i * ξ j ∧
        (∑ i, ∑ j, a i j x * ξ i * ξ j) ≤ Lam * ‖ξ‖ ^ 2 := by
    intro x hx ξ
    exact hellbig x (hbase x hx) ξ
  have haN : ∀ i j, ∀ x ∈ closedBall c 1, ‖fderiv ℝ (a i j) x‖ ≤ K := by
    intro i j x hx
    exact (hAcap (i, j) x (hbase x hx)).1.trans hKA'
  have hahol : ∀ i j, ∀ x ∈ closedBall c 1, ∀ y ∈ closedBall c 1,
      ‖fderiv ℝ (a i j) x - fderiv ℝ (a i j) y‖ ≤
        K * ‖x - y‖ ^ (α : ℝ) := by
    intro i j x hx y hy
    exact ((hAcap (i, j) x (hbase x hx)).2 y (hbase y hy)).trans
      (mul_le_mul_of_nonneg_right hKA' (by positivity))
  have hbN : ∀ i, ∀ x ∈ closedBall c 1, |b i x| ≤ K := by
    intro i x hx
    simpa [Real.norm_eq_abs] using
      (hBcap i x (hbase x hx)).1.trans hKB'
  have hbdN : ∀ i, ∀ x ∈ closedBall c 1, ‖fderiv ℝ (b i) x‖ ≤ K := by
    intro i x hx
    exact (hBdCap i x (hbase x hx)).1.trans hKBd'
  have hbhol : ∀ i, ∀ x ∈ closedBall c 1, ∀ y ∈ closedBall c 1,
      ‖fderiv ℝ (b i) x - fderiv ℝ (b i) y‖ ≤
        K * ‖x - y‖ ^ (α : ℝ) := by
    intro i x hx y hy
    exact ((hBdCap i x (hbase x hx)).2 y (hbase y hy)).trans
      (mul_le_mul_of_nonneg_right hKBd' (by positivity))
  have hgN : ∀ x ∈ closedBall c 1, ‖fderiv ℝ g x‖ ≤ K := by
    intro x hx
    exact (hGcap () x (hbase x hx)).1.trans hKG'
  have hghol : ∀ x ∈ closedBall c 1, ∀ y ∈ closedBall c 1,
      ‖fderiv ℝ g x - fderiv ℝ g y‖ ≤
        K * ‖x - y‖ ^ (α : ℝ) := by
    intro x hx y hy
    exact ((hGcap () x (hbase x hx)).2 y (hbase y hy)).trans
      (mul_le_mul_of_nonneg_right hKG' (by positivity))
  have hwN : ∀ x ∈ closedBall c 1, ‖fderiv ℝ w x‖ ≤ K := by
    intro x hx
    exact (hNgrad (x) (hbase x hx)).trans hNgrad'
  have hw2N : ∀ x ∈ closedBall c 1,
      ‖fderiv ℝ (fderiv ℝ w) x‖ ≤ K := by
    intro x hx
    exact (hHcap () x (hbase x hx)).1.trans hKH'
  have hw2hol : ∀ x ∈ closedBall c 1, ∀ y ∈ closedBall c 1,
      ‖fderiv ℝ (fderiv ℝ w) x - fderiv ℝ (fderiv ℝ w) y‖ ≤
        K * ‖x - y‖ ^ (α : ℝ) := by
    intro x hx y hy
    exact ((hHcap () x (hbase x hx)).2 y (hbase y hy)).trans
      (mul_le_mul_of_nonneg_right hKH' (by positivity))
  exact hstep c w g a b
    (hw.1.of_le (by norm_num))
    (fun i j => (ha i j).1)
    (fun i => (hb i).1)
    hg.1 hsym hellc haN hahol hbN hbdN hbhol hgN hghol hwN hw2N hw2hol
    (fun x hx => heq x)

set_option maxHeartbeats 1600000 in
/-- Interior Schauder regularity through every finite derivative order, at the given solution. -/
theorem locHolderDeriv_succ_succ_succ_of_linear_equation (hn : 2 ≤ n) (m : ℕ)
    {w g : E → ℝ} {a : Fin n → Fin n → E → ℝ} {b : Fin n → E → ℝ}
    (hw : LocHolderDeriv 2 w) (ha : ∀ i j, LocHolderDeriv (m + 1) (a i j))
    (hb : ∀ i, LocHolderDeriv (m + 1) (b i)) (hg : LocHolderDeriv (m + 1) g)
    (hsymm : ∀ x i j, a i j x = a j i x) (hell : LocallyUniformElliptic a)
    (heq : ∀ x, (∑ i, ∑ j, a i j x * fderiv ℝ (fderiv ℝ w) x
        (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)) +
        (∑ i, b i x * fderiv ℝ w x (EuclideanSpace.basisFun (Fin n) ℝ i)) + w x = g x) :
    LocHolderDeriv (m + 3) w := by
  induction m generalizing w g a b with
  | zero =>
      have hlocal :
          ∀ s : ℝ, 0 < s →
            ∃ α : ℝ≥0, 0 < α ∧ α < 1 ∧ ∃ R K : ℝ, 0 < R ∧ 0 ≤ K ∧
              ∀ c ∈ ball (0 : E) s,
                ContDiffOn ℝ 3 w (ball c R) ∧
                (∀ x ∈ ball c R,
                  ‖fderiv ℝ (fderiv ℝ (fderiv ℝ w)) x‖ ≤ K) ∧
                ∀ x ∈ ball c R, ∀ y ∈ ball c R,
                  ‖fderiv ℝ (fderiv ℝ (fderiv ℝ w)) x -
                      fderiv ℝ (fderiv ℝ (fderiv ℝ w)) y‖ ≤
                    K * ‖x - y‖ ^ (α : ℝ) := by
        intro s hs
        exact local_linear_schauder_data hn hw ha hb hg hsymm hell heq hs
      have hw3 : ContDiff ℝ 3 w := by
        rw [contDiff_iff_contDiffAt]
        intro x
        obtain ⟨α, hα0, hα1, R, K, hR, hK, hloc⟩ :=
          hlocal (‖x‖ + 1) (by positivity)
        have hx : x ∈ ball (0 : E) (‖x‖ + 1) := by
          rw [mem_ball_zero_iff]
          linarith
        exact (hloc x hx).1.contDiffAt (isOpen_ball.mem_nhds (mem_ball_self hR))
      refine ⟨hw3, ?_⟩
      intro s hs
      obtain ⟨α, hα0, hα1, R, K, hR, hK, hloc⟩ := hlocal s hs
      have hpatch :
          ∀ c ∈ ball (0 : E) s,
            (∀ x ∈ ball c R, ‖iteratedFDeriv ℝ 3 w x‖ ≤ K) ∧
            ∀ x ∈ ball c R, ∀ y ∈ ball c R,
              ‖iteratedFDeriv ℝ 3 w x - iteratedFDeriv ℝ 3 w y‖ ≤
                K * ‖x - y‖ ^ (α : ℝ) := by
        intro c hc
        have hlocc := hloc c hc
        constructor
        · intro x hx
          rw [norm_iteratedFDeriv_three_eq]
          exact hlocc.2.1 x hx
        · intro x hx y hy
          rw [norm_iteratedFDeriv_three_sub]
          exact hlocc.2.2 x hx y hy
      have hglobal :
          ∀ x ∈ ball (0 : E) s, ∀ y ∈ ball (0 : E) s,
            ‖iteratedFDeriv ℝ 3 w x - iteratedFDeriv ℝ 3 w y‖ ≤
              K * (1 + 2 * R ^ (-(α : ℝ))) * ‖x - y‖ ^ (α : ℝ) := by
        intro x hx y hy
        exact holder_of_local_holder_of_bound hR hK (by positivity) hpatch x hx y hy
      refine ⟨α, hα0, hα1, K * (1 + 2 * R ^ (-(α : ℝ))),
        mul_nonneg hK (by positivity), ?_⟩
      exact hglobal
  | succ k ih =>
      have hwweak : LocHolderDeriv (k + 3) w :=
        ih hw (fun i j => (ha i j).weaken) (fun i => (hb i).weaken) hg.weaken hsymm hell heq
      have haw : ∀ i j, LocHolderDeriv (k + 2) (a i j) := ha
      have hbw : ∀ i, LocHolderDeriv (k + 2) (b i) := hb
      have hgw : LocHolderDeriv (k + 2) g := hg
      have hw3 : ContDiff ℝ 3 w := hwweak.1.of_le (by nat_cast_le)
      have had : ∀ i j, Differentiable ℝ (a i j) :=
        fun i j => (haw i j).1.differentiable (by nat_cast_le)
      have hbd : ∀ i, Differentiable ℝ (b i) :=
        fun i => (hbw i).1.differentiable (by nat_cast_le)
      have hforcing : ∀ e : E, LocHolderDeriv (k + 1)
          (fun x => fderiv ℝ g x e -
            (∑ i, ∑ j, fderiv ℝ (a i j) x e *
              fderiv ℝ (fderiv ℝ w) x
                (EuclideanSpace.basisFun (Fin n) ℝ i)
                (EuclideanSpace.basisFun (Fin n) ℝ j)) -
            (∑ i, fderiv ℝ (b i) x e *
              fderiv ℝ w x (EuclideanSpace.basisFun (Fin n) ℝ i))) := by
        intro e
        have hg' := hgw.directional e
        have ha' : ∀ i j, LocHolderDeriv (k + 1)
            (fun x => fderiv ℝ (a i j) x e *
              fderiv ℝ (fderiv ℝ w) x
                (EuclideanSpace.basisFun (Fin n) ℝ i)
                (EuclideanSpace.basisFun (Fin n) ℝ j)) := by
          intro i j
          exact ((haw i j).directional e).mul (hwweak.hessianEntry i j)
        have hb' : ∀ i, LocHolderDeriv (k + 1)
            (fun x => fderiv ℝ (b i) x e *
              fderiv ℝ w x (EuclideanSpace.basisFun (Fin n) ℝ i)) := by
          intro i
          exact ((hbw i).directional e).mul
            (hwweak.directional (EuclideanSpace.basisFun (Fin n) ℝ i)).weaken
        exact (hg'.sub (LocHolderDeriv.finset_sum Finset.univ (fun i _ =>
          LocHolderDeriv.finset_sum Finset.univ (fun j _ => ha' i j)))).sub
          (LocHolderDeriv.finset_sum Finset.univ (fun i _ => hb' i))
      have hz : ∀ e : E, LocHolderDeriv (k + 3)
          (fun x => fderiv ℝ w x e) := by
        intro e
        exact ih ((hwweak.directional e).of_le (by omega))
          (fun i j => (haw i j).weaken) (fun i => (hbw i).weaken)
          (hforcing e) hsymm hell (fun x => directional_linear_equation hw3 had hbd heq e x)
      exact LocHolderDeriv.of_coordinate (hwweak.1.of_le (by nat_cast_le))
        (fun i => hz (EuclideanSpace.basisFun (Fin n) ℝ i))

end FunctionalInequalities.Analysis
