module

public import FunctionalInequalities.Analysis.Convex.Viscosity.Equation
public import FunctionalInequalities.Analysis.Convex.Viscosity.Pointwise
public import FunctionalInequalities.Analysis.Convex.Dirichlet.Envelope
public import FunctionalInequalities.Analysis.Jacobian
public import FunctionalInequalities.Analysis.Matrix.DeterminantInequalities

/-!
# Buffered regularization of the Dirichlet envelope

Supporting interfaces for Letwin arXiv:2607.24164v1 Lemma 2.2 through
Berman–Berndtsson arXiv:1207.6128v1 Theorem 2.24(ii). Each declaration retains
its own hypotheses and scope; this layout does not assert further regularity.
-/

@[expose] public section

section

open Set Metric Filter MeasureTheory
open scoped RealInnerProductSpace Topology
open FunctionalInequalities.Probability.Stein

namespace FunctionalInequalities.Analysis

namespace Dirichlet
section QuadraticLowerTests
open Classical Matrix

private theorem scalar_shrink {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hd : 1 < A.det) :
    ∃ a : ℝ, 0 < a ∧ a < 1 ∧ 1 < a ^ n * A.det := by
  have hc : Continuous (fun a : ℝ => a ^ n * A.det) := by fun_prop
  have ho : IsOpen {a : ℝ | 1 < a ^ n * A.det} := isOpen_lt continuous_const hc
  have h1 : (1 : ℝ) ∈ {a : ℝ | 1 < a ^ n * A.det} := by simpa using hd
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (ho.mem_nhds h1)
  let t := min (δ / 2) (1 / 2 : ℝ)
  have ht : 0 < t := by dsimp [t]; positivity
  have ht1 : t ≤ 1 / 2 := min_le_right _ _
  have htd : t < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  refine ⟨1 - t, by linarith, by linarith, ?_⟩
  apply hball
  change |(1 - t) - 1| < δ
  rw [show (1 - t) - 1 = -t by ring, abs_neg, abs_of_pos ht]
  exact htd

private theorem euclidean_floor {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {k : ℝ}
    (hk : QuadraticFloor A k) (v : EuclideanSpace ℝ (Fin n)) :
    k * ‖v‖ ^ 2 ≤ ⟪v, Matrix.toEuclideanLin A v⟫ := by
  have h := hk v.ofLp
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  change k * ‖v‖ ^ 2 ≤ (A *ᵥ v.ofLp) ⬝ᵥ star v.ofLp
  simpa only [EuclideanSpace.real_norm_sq_eq, star_trivial, dotProduct_comm] using h

/-- Private implementation: the public source below PRODUCES this comparison
field, rather than assuming it as an input to an existence statement. -/
private theorem det_le_one_of_comparison {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (hΩ : IsOpen Ω) (hcΩ : Convex ℝ Ω) {U : EuclideanSpace ℝ (Fin n) → ℝ}
    (hcomp :
      ∀ (q : EuclideanSpace ℝ (Fin n) → ℝ),
        ConvexOn ℝ Ω q →
          ContinuousOn q (closure Ω) →
            (∀ G, IsOpen G → G ⊆ Ω → volume G ≤ volume (subgradientImageOn q Ω G)) →
              ∀ (c : EuclideanSpace ℝ (Fin n)) (r : ℝ),
                0 < r →
                  closedBall c r ⊆ Ω →
                    (∀ z ∈ sphere c r, q z ≤ U z) → ∀ x ∈ ball c r, q x ≤ U x)
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ Ω)
    (b : EuclideanSpace ℝ (Fin n)) (htouch : ∀ᶠ y in 𝓝 x, quadraticAt A x b (U x) y ≤ U y) :
    A.det ≤ 1 := by
  by_contra hd
  have hd' : 1 < A.det := lt_of_not_ge hd
  obtain ⟨a, ha, ha1, had⟩ := scalar_shrink hd'
  let B := a • A
  have hB : B.PosDef := hA.smul ha
  have hBd : 1 < B.det := by simpa [B, Matrix.det_smul] using had
  obtain ⟨k, hk, hfloor⟩ := exists_quadraticFloor_of_posDef hA
  have hnb : {y | quadraticAt A x b (U x) y ≤ U y} ∩ Ω ∈ 𝓝 x :=
    inter_mem htouch (hΩ.mem_nhds hx)
  obtain ⟨R, hR, hRset⟩ := Metric.mem_nhds_iff.mp hnb
  let r := R / 2
  have hr : 0 < r := half_pos hR
  have hbuf : closedBall x r ⊆ ball x R := by
    intro y hy
    change dist y x ≤ r at hy
    change dist y x < R
    exact lt_of_le_of_lt hy (by dsimp [r]; linarith)
  have hball : closedBall x r ⊆ Ω := fun y hy => (hRset (hbuf hy)).2
  have htest : ∀ y ∈ closedBall x r, quadraticAt A x b (U x) y ≤ U y := fun y hy =>
    (hRset (hbuf hy)).1
  let e := (1 - a) * k * r ^ 2 / 4
  have he : 0 < e := by dsimp [e]; positivity
  let q := quadraticAt B x b (U x + e)
  have hform (y : EuclideanSpace ℝ (Fin n)) :
    q y =
      quadraticAt A x b (U x) y + e - (1 - a) / 2 * ⟪y - x, Matrix.toEuclideanLin A (y - x)⟫ := by
    dsimp [q, B, quadraticAt]
    simp only [map_smul, LinearMap.smul_apply, inner_smul_right]
    ring
  have hqc : Continuous q := (contDiff_quadraticAt B x b (U x + e)).continuous
  have hqcv : ConvexOn ℝ univ q := convexOn_quadraticAt hB.posSemidef _ _ _
  have hqMA : ∀ G, IsOpen G → G ⊆ Ω → volume G ≤ volume (subgradientImageOn q Ω G) := by
    intro G _hG hGΩ
    dsimp only [q]
    rw [volume_subgradientImageOn_quadraticAt hB _ _ _ hΩ hGΩ]
    have hm : (1 : ENNReal) ≤ ENNReal.ofReal B.det := by
      rw [← ENNReal.ofReal_one];
      exact ENNReal.ofReal_le_ofReal hBd.le
    calc
      volume G = 1 * volume G := by rw [one_mul]
      _ ≤ ENNReal.ofReal B.det * volume G := by gcongr
  have hbd : ∀ y ∈ sphere x r, q y ≤ U y := by
    intro y hy
    have hn : ‖y - x‖ = r := by simpa only [mem_sphere, dist_eq_norm] using hy
    have hf := euclidean_floor hfloor (y - x)
    rw [hn] at hf
    have hc : 0 ≤ (1 - a) / 2 := by positivity
    have hm := mul_le_mul_of_nonneg_left hf hc
    have hprod : 2 * e ≤ (1 - a) / 2 * ⟪y - x, Matrix.toEuclideanLin A (y - x)⟫ := by
      calc
        2 * e = (1 - a) / 2 * (k * r ^ 2) := by dsimp [e]; ring
        _ ≤ _ := hm
    have hgap : q y ≤ quadraticAt A x b (U x) y := by
      rw [hform]
      linarith only [hprod, he.le]
    exact hgap.trans (htest y (sphere_subset_closedBall hy))
  have hlocal :=
    hcomp q (hqcv.subset (subset_univ _) hcΩ) hqc.continuousOn hqMA x r hr hball hbd x
      (mem_ball_self hr)
  have hqx : q x = U x + e := by simp [q, quadraticAt]
  rw [hqx] at hlocal
  linarith

/-- Source-only actual envelope with genuine PD quadratic lower-test bound.
The old actual source is called ONCE and EVERY field is retained. -/
theorem exists_envelope_quadratic_lower_test_bound {n : ℕ} (hn : 0 < n)
    {Ω : Set (EuclideanSpace ℝ (Fin n))} (hΩ : IsOpen Ω) (hcΩ : Convex ℝ Ω)
    (hb : Bornology.IsBounded Ω) :
    ∃ (U : EuclideanSpace ℝ (Fin n) → ℝ) (f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ),
      (∀ x ∈ closure Ω, U x = sSup ((fun w => w x) '' subsolutions Ω)) ∧
        U ∈ subsolutions Ω ∧
          (∀ z ∈ frontier Ω, U z = 0) ∧
            (∀ w ∈ subsolutions Ω, ∀ x ∈ closure Ω, w x ≤ U x) ∧
              (∀ j, f j ∈ subsolutions Ω) ∧
                (∀ j, ∀ x ∈ closure Ω, f j x ≤ U x ∧ |f j x - U x| < 1 / ((j : ℝ) + 1)) ∧
                  (∀ x, Monotone (fun j => f j x)) ∧
                    TendstoUniformlyOn f U atTop (closure Ω) ∧
                      (∀ (q : EuclideanSpace ℝ (Fin n) → ℝ),
                          ConvexOn ℝ Ω q →
                            ContinuousOn q (closure Ω) →
                              (∀ G,
                                  IsOpen G →
                                    G ⊆ Ω → volume G ≤ volume (subgradientImageOn q Ω G)) →
                                ∀ (c : EuclideanSpace ℝ (Fin n)) (r : ℝ),
                                  0 < r →
                                    closedBall c r ⊆ Ω →
                                      (∀ z ∈ sphere c r, q z ≤ U z) →
                                        ∀ x ∈ ball c r, q x ≤ U x) ∧
                        (∀ (A : Matrix (Fin n) (Fin n) ℝ),
                          A.PosDef →
                            ∀ x ∈ Ω,
                              ∀ b,
                                (∀ᶠ y in 𝓝 x, quadraticAt A x b (U x) y ≤ U y) → A.det ≤ 1) := by
  obtain ⟨U, f, hs, hU, hz, hd, hf, he, hm, hu, hcomp⟩ :=
    exists_envelope_local_comparison hn hΩ hcΩ hb
  refine ⟨U, f, hs, hU, hz, hd, hf, he, hm, hu, hcomp, ?_⟩
  intro A hA x hx b ht
  exact det_le_one_of_comparison hΩ hcΩ hcomp hA hx b ht

end QuadraticLowerTests
end Dirichlet

section PerronC2LowerTests
open Classical Matrix


namespace Dirichlet
theorem exists_envelope_c2_lower_test_bound {n : ℕ} (hn : 0 < n)
    {Ω : Set (EuclideanSpace ℝ (Fin n))} (hΩ : IsOpen Ω) (hcΩ : Convex ℝ Ω)
    (hb : Bornology.IsBounded Ω) :
    ∃ (U : EuclideanSpace ℝ (Fin n) → ℝ) (f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ),
      (∀ x ∈ closure Ω, U x = sSup ((fun w => w x) '' subsolutions Ω)) ∧
        U ∈ subsolutions Ω ∧
          (∀ z ∈ frontier Ω, U z = 0) ∧
            (∀ w ∈ subsolutions Ω, ∀ x ∈ closure Ω, w x ≤ U x) ∧
              (∀ j, f j ∈ subsolutions Ω) ∧
                (∀ j, ∀ x ∈ closure Ω, f j x ≤ U x ∧ |f j x - U x| < 1 / ((j : ℝ) + 1)) ∧
                  (∀ x, Monotone (fun j => f j x)) ∧
                    TendstoUniformlyOn f U atTop (closure Ω) ∧
                      (∀ (q : EuclideanSpace ℝ (Fin n) → ℝ),
                          ConvexOn ℝ Ω q →
                            ContinuousOn q (closure Ω) →
                              (∀ G,
                                  IsOpen G →
                                    G ⊆ Ω → volume G ≤ volume (subgradientImageOn q Ω G)) →
                                ∀ (c : EuclideanSpace ℝ (Fin n)) (r : ℝ),
                                  0 < r →
                                    closedBall c r ⊆ Ω →
                                      (∀ z ∈ sphere c r, q z ≤ U z) →
                                        ∀ x ∈ ball c r, q x ≤ U x) ∧
                        (∀ (A : Matrix (Fin n) (Fin n) ℝ),
                            A.PosDef →
                              ∀ x ∈ Ω,
                                ∀ b,
                                  (∀ᶠ y in 𝓝 x, quadraticAt A x b (U x) y ≤ U y) → A.det ≤ 1) ∧
                          (∀ (ψ : EuclideanSpace ℝ (Fin n) → ℝ),
                            ∀ x ∈ Ω,
                              ContDiffAt ℝ 2 ψ x →
                                (hessianMatrix ψ x).PosSemidef →
                                  U x = ψ x →
                                    (∀ᶠ y in 𝓝 x, ψ y ≤ U y) → (hessianMatrix ψ x).det ≤ 1) := by
  obtain ⟨U, f, hs, hU, hz, hd, hf, he, hm, hu, hcomp, hquad⟩ :=
    exists_envelope_quadratic_lower_test_bound hn hΩ hcΩ hb
  refine ⟨U, f, hs, hU, hz, hd, hf, he, hm, hu, hcomp, hquad, ?_⟩
  intro ψ x hx hψ hH hcontact htouch
  exact det_hessianMatrix_le_of_quadratic_lower_tests hquad hx hψ hH hcontact htouch

end Dirichlet
end PerronC2LowerTests

namespace Dirichlet
section BufferedMoreau
open Classical Matrix

private theorem buffered_quadratic_transfer {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {U V : EuclideanSpace ℝ (Fin n) → ℝ} (hV : ConvexOn ℝ univ V) {L : NNReal}
    (hL : LipschitzWith L V)
    (hquad :
      ∀ (A : Matrix (Fin n) (Fin n) ℝ),
        A.PosDef → ∀ y ∈ Ω, ∀ b, (∀ᶠ w in 𝓝 y, quadraticAt A y b (U y) w ≤ U w) → A.det ≤ 1)
    {c : EuclideanSpace ℝ (Fin n)} {R ε : ℝ} (hball : closedBall c R ⊆ Ω)
    (heq : ∀ y ∈ closedBall c R, V y = U y) (hε : 0 < ε) (hsmall : ε * ((L : ℝ) + 1) < R / 2)
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ ball c (R / 2)) (b : EuclideanSpace ℝ (Fin n))
    (ht : ∀ᶠ z in 𝓝 x, quadraticAt A x b (moreauEnvelope V ε x) z ≤ moreauEnvelope V ε z) :
    A.det ≤ 1 := by
  let y := (proximalPoint (fun z => ε * V z)) x
  let k := (2 * ε)⁻¹ * ‖y - x‖ ^ 2
  have hd : dist y x ≤ ε * (L : ℝ) := by
    simpa only [y, dist_eq_norm] using (moreauEnvelope_approximation V hV hL hε x).2.2
  have hs : ε * (L : ℝ) < R / 2 :=
    (mul_le_mul_of_nonneg_left (by linarith : (L : ℝ) ≤ (L : ℝ) + 1) hε.le).trans_lt hsmall
  have hy : y ∈ ball c R := by
    have hh := dist_triangle y x c
    have hxx : dist x c < R / 2 := hx
    change dist y c < R
    linarith
  have hc : moreauEnvelope V ε x = quadraticAt A x b (moreauEnvelope V ε x) x := by
    simp [quadraticAt]
  obtain ⟨hcontact, hgerm⟩ := lower_contact_moreauEnvelope V hV hε hc ht
  change V y = quadraticAt A x b (moreauEnvelope V ε x) (y + (x - y)) - k at hcontact
  change ∀ᶠ w in 𝓝 y, quadraticAt A x b (moreauEnvelope V ε x) (w + (x - y)) - k ≤ V w at hgerm
  have he : V y = moreauEnvelope V ε x - k := by
    simpa only [show y + (x - y) = x by abel, quadraticAt, sub_self, inner_zero_right,
      inner_zero_left, zero_add, add_zero, mul_zero] using hcontact
  have hform (w : EuclideanSpace ℝ (Fin n)) :
    quadraticAt A y b (V y) w = quadraticAt A x b (moreauEnvelope V ε x) (w + (x - y)) - k := by
    dsimp only [quadraticAt]
    rw [show (w + (x - y)) - x = w - y by abel, he]
    ring
  have htU : ∀ᶠ w in 𝓝 y, quadraticAt A y b (U y) w ≤ U w := by
    filter_upwards [hgerm, isOpen_ball.mem_nhds hy] with w hw hwb
    rw [← heq y (ball_subset_closedBall hy), ← heq w (ball_subset_closedBall hwb), hform]
    exact hw
  exact hquad A hA y (hball (ball_subset_closedBall hy)) b htU

theorem exists_envelope_buffered_moreau {n : ℕ} (hn : 0<n)
    {Ω : Set (EuclideanSpace ℝ (Fin n))} (hΩ : IsOpen Ω) (hcΩ : Convex ℝ Ω)
    (hb : Bornology.IsBounded Ω) :
    ∃ (U : EuclideanSpace ℝ (Fin n)→ℝ) (f : ℕ→EuclideanSpace ℝ (Fin n)→ℝ),
      (∀ x∈closure Ω, U x=sSup ((fun w => w x) '' subsolutions Ω)) ∧
      U∈subsolutions Ω ∧ (∀ z∈frontier Ω, U z=0) ∧
      (∀ w∈subsolutions Ω, ∀ x∈closure Ω, w x≤U x) ∧
      (∀ j, f j∈subsolutions Ω) ∧
      (∀ j, ∀ x∈closure Ω, f j x≤U x ∧ |f j x-U x|<1 / ((j:ℝ) + 1)) ∧
      (∀ x, Monotone (fun j => f j x)) ∧
      TendstoUniformlyOn f U atTop (closure Ω) ∧
      (∀ (q : EuclideanSpace ℝ (Fin n)→ℝ), ConvexOn ℝ Ω q→ ContinuousOn q (closure Ω)→
        (∀ G, IsOpen G→G⊆Ω→volume G≤volume (subgradientImageOn q Ω G))→
        ∀ (c : EuclideanSpace ℝ (Fin n)) (r : ℝ), 0<r→closedBall c r⊆Ω→
          (∀ z∈sphere c r, q z≤U z)→∀ x∈ball c r, q x≤U x) ∧
      (∀ (A : Matrix (Fin n) (Fin n) ℝ), A.PosDef→∀ x∈Ω, ∀ b,
        (∀ᶠ y in 𝓝 x, quadraticAt A x b (U x) y≤U y)→A.det≤1) ∧
      (∀ (ψ : EuclideanSpace ℝ (Fin n)→ℝ), ∀ x∈Ω,
        ContDiffAt ℝ 2 ψ x→(hessianMatrix ψ x).PosSemidef→U x=ψ x→
        (∀ᶠ y in 𝓝 x, ψ y≤U y)→(hessianMatrix ψ x).det≤1) ∧
      (∀ (c : EuclideanSpace ℝ (Fin n)) (R : ℝ), 0<R→closedBall c R⊆Ω→
        ∃ (V : EuclideanSpace ℝ (Fin n)→ℝ) (L : NNReal),
          ConvexOn ℝ univ V ∧ LipschitzWith L V ∧ (∀ y∈closedBall c R, V y=U y) ∧
          (∀ ε : ℝ, 0<ε→ε * ((L:ℝ) + 1)<R / 2→
            ConvexOn ℝ univ (moreauEnvelope V ε) ∧ ContDiff ℝ 1 (moreauEnvelope V ε) ∧
            LipschitzWith (‖(ε⁻¹:ℝ)‖₊*2) (gradient (moreauEnvelope V ε)) ∧
            (∀ (A : Matrix (Fin n) (Fin n) ℝ), A.PosDef→∀ x∈ball c (R / 2), ∀ b,
              (∀ᶠ z in 𝓝 x, quadraticAt A x b (moreauEnvelope V ε x) z≤ moreauEnvelope V ε
                z)→A.det≤1)) ∧
          TendstoUniformlyOn (fun ε : ℝ => moreauEnvelope V ε) U (𝓝[>] (0:ℝ)) (closedBall c
            R)) := by
    obtain ⟨U, f, hs, hU, hz, hd, hf, he, hm, hu, hcomp, hquad, hc2⟩ :=
      Dirichlet.exists_envelope_c2_lower_test_bound hn hΩ hcΩ hb
    refine ⟨U, f, hs, hU, hz, hd, hf, he, hm, hu, hcomp, hquad, hc2, ?_⟩
    intro c R hR hball
    have hcv : ConvexOn ℝ Ω U := hU.1.subset subset_closure hcΩ
    have hC : ContinuousOn U Ω := hU.2.1.mono subset_closure
    obtain ⟨V, L, hV, hL, heq, hreg, hunif⟩ :=
      exists_compact_moreau_regularization hΩ hcv hC (isCompact_closedBall c R)
        ⟨c, mem_closedBall_self hR.le⟩ hball
    refine ⟨V, L, hV, hL, heq, ?_, hunif⟩
    intro ε hε hsmall
    obtain ⟨hc, hd, hl, _, _⟩ := hreg ε hε
    refine ⟨hc, hd, hl, ?_⟩
    intro A hA x hx b ht
    exact buffered_quadratic_transfer hV hL hquad hball heq hε hsmall hA hx b ht

end BufferedMoreau
end Dirichlet

end FunctionalInequalities.Analysis

namespace FunctionalInequalities.Analysis
namespace Dirichlet
open Set Filter Matrix MeasureTheory Metric
open scoped RealInnerProductSpace ENNReal Topology
open FunctionalInequalities.Probability.Stein
open Classical

private lemma psd_det_of_quadratic_tests {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (hconv : ConvexOn ℝ univ u) {x : EuclideanSpace ℝ (Fin n)} {B : Matrix (Fin n) (Fin n) ℝ}
    (hB : B.IsHermitian) {g : EuclideanSpace ℝ (Fin n)}
    (hexp : ∀ ε > 0, ∀ᶠ y in 𝓝 x, |u y - quadraticAt B x g (u x) y| ≤ ε * ‖y - x‖ ^ 2)
    (htest :
      ∀ (A : Matrix (Fin n) (Fin n) ℝ),
        A.PosDef → ∀ b, (∀ᶠ y in 𝓝 x, quadraticAt A x b (u x) y ≤ u y) → A.det ≤ 1) :
    B.PosSemidef ∧ B.det ≤ 1 := by
  have hps : B.PosSemidef := posSemidef_of_quadratic_expansion hconv hB hexp
  refine ⟨hps, ?_⟩
  by_contra hd
  have hbad : 1 < B.det := lt_of_not_ge hd
  have hpd : B.PosDef := hps.posDef_iff_det_ne_zero.mpr (ne_of_gt (lt_trans zero_lt_one hbad))
  obtain ⟨a, ha, ha1, had⟩ := scalar_shrink hbad
  let C := a • B
  have hC : C.PosDef := hpd.smul ha
  have hCd : 1 < C.det := by simpa [C, Matrix.det_smul] using had
  obtain ⟨k, hk, hfloor⟩ := exists_quadraticFloor_of_posDef hpd
  let δ := (1 - a) * k / 4
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hform (y : EuclideanSpace ℝ (Fin n)) :
    quadraticAt C x g (u x) y =
      quadraticAt B x g (u x) y - (1 - a) / 2 * ⟪y - x, Matrix.toEuclideanLin B (y - x)⟫ := by
    dsimp [quadraticAt, C]
    simp only [map_smul, LinearMap.smul_apply, inner_smul_right]
    ring
  have htouch : ∀ᶠ y in 𝓝 x, quadraticAt C x g (u x) y ≤ u y := by
    filter_upwards [hexp δ hδ] with y hy
    have hf := euclidean_floor hfloor (y - x)
    have hm := mul_le_mul_of_nonneg_left hf (show 0 ≤ (1 - a) / 2 by positivity)
    have hprod : 2 * δ * ‖y - x‖ ^ 2 ≤ (1 - a) / 2 * ⟪y - x, Matrix.toEuclideanLin B (y - x)⟫ := by
      calc
        _ = (1 - a) / 2 * (k * ‖y - x‖ ^ 2) := by dsimp [δ]; ring
        _ ≤ _ := hm
    have hn : 0 ≤ δ * ‖y - x‖ ^ 2 := mul_nonneg hδ.le (sq_nonneg _)
    have hh := (abs_le.mp hy).1
    rw [hform]
    nlinarith only [hprod, hn, hh]
  exact (not_lt_of_ge (htest C hC g htouch)) hCd

private lemma ae_matrix_of_quadratic_tests {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (hconv : ConvexOn ℝ univ u) {Ω : Set (EuclideanSpace ℝ (Fin n))} (hΩ : IsOpen Ω)
    (hdiff : DifferentiableOn ℝ u Ω)
    (htest :
      ∀ (A : Matrix (Fin n) (Fin n) ℝ),
        A.PosDef → ∀ x ∈ Ω, ∀ b, (∀ᶠ y in 𝓝 x, quadraticAt A x b (u x) y ≤ u y) → A.det ≤ 1) :
    ∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict Ω),
      ∃ A : Matrix (Fin n) (Fin n) ℝ,
        A.IsHermitian ∧
          HasFDerivAt (gradient u) (Matrix.toEuclideanLin A).toContinuousLinearMap x ∧
            A.PosSemidef ∧
              A.det ≤ 1 ∧
                ∀ t > 0,
                  ∀ᶠ y in 𝓝 x,
                    |u y - quadraticAt A x (gradient u x) (u x) y| ≤ t * ‖y - x‖ ^ 2 := by
  filter_upwards [ae_exists_gradient_quadraticAt_expansion_on_open hconv hΩ hdiff,
    ae_restrict_mem hΩ.measurableSet] with x hx hxΩ
  obtain ⟨A, hA, hd, he⟩ := hx
  obtain ⟨hp, hdet⟩ :=
    psd_det_of_quadratic_tests hconv hA he (fun B hB b ht => htest B hB x hxΩ b ht)
  exact ⟨A, hA, hd, hp, hdet, he⟩

/-- Actual buffered regularization of the SAME Perron envelope has an a.e. SAME
gradient derivative and value-expansion matrix, positive semidefinite with determinant
at most one. The envelope and all regularization data are generated from the domain. -/
theorem exists_envelope_buffered_moreau_ae_matrix {n : ℕ} (hn : 0<n)
    {Ω : Set (EuclideanSpace ℝ (Fin n))} (hΩ : IsOpen Ω) (hcΩ : Convex ℝ Ω)
    (hb : Bornology.IsBounded Ω) :
    ∃ (U : EuclideanSpace ℝ (Fin n)→ℝ) (f : ℕ→EuclideanSpace ℝ (Fin n)→ℝ),
      (∀ x∈closure Ω, U x=sSup ((fun w => w x) '' subsolutions Ω)) ∧
      U∈subsolutions Ω ∧ (∀ z∈frontier Ω, U z=0) ∧
      (∀ w∈subsolutions Ω, ∀ x∈closure Ω, w x≤U x) ∧
      (∀ j, f j∈subsolutions Ω) ∧
      (∀ j, ∀ x∈closure Ω, f j x≤U x ∧ |f j x-U x|<1 / ((j:ℝ) + 1)) ∧
      (∀ x, Monotone (fun j => f j x)) ∧
      TendstoUniformlyOn f U atTop (closure Ω) ∧
      (∀ (q : EuclideanSpace ℝ (Fin n)→ℝ), ConvexOn ℝ Ω q→ ContinuousOn q (closure Ω)→
        (∀ G, IsOpen G→G⊆Ω→volume G≤volume (subgradientImageOn q Ω G))→
        ∀ (c : EuclideanSpace ℝ (Fin n)) (r : ℝ), 0<r→closedBall c r⊆Ω→
          (∀ z∈sphere c r, q z≤U z)→∀ x∈ball c r, q x≤U x) ∧
      (∀ (A : Matrix (Fin n) (Fin n) ℝ), A.PosDef→∀ x∈Ω, ∀ b,
        (∀ᶠ y in 𝓝 x, quadraticAt A x b (U x) y≤U y)→A.det≤1) ∧
      (∀ (ψ : EuclideanSpace ℝ (Fin n)→ℝ), ∀ x∈Ω,
        ContDiffAt ℝ 2 ψ x→(hessianMatrix ψ x).PosSemidef→U x=ψ x→
        (∀ᶠ y in 𝓝 x, ψ y≤U y)→(hessianMatrix ψ x).det≤1) ∧
      (∀ (c : EuclideanSpace ℝ (Fin n)) (R : ℝ), 0<R→closedBall c R⊆Ω→
        ∃ (V : EuclideanSpace ℝ (Fin n)→ℝ) (L : NNReal),
          ConvexOn ℝ univ V ∧ LipschitzWith L V ∧ (∀ y∈closedBall c R, V y=U y) ∧
          (∀ ε : ℝ, 0<ε→ε * ((L:ℝ) + 1)<R / 2→
            ConvexOn ℝ univ (moreauEnvelope V ε) ∧ ContDiff ℝ 1 (moreauEnvelope V ε) ∧
            LipschitzWith (‖(ε⁻¹:ℝ)‖₊*2) (gradient (moreauEnvelope V ε)) ∧
            (∀ (A : Matrix (Fin n) (Fin n) ℝ), A.PosDef→∀ x∈ball c (R / 2), ∀ b,
              (∀ᶠ z in 𝓝 x, quadraticAt A x b (moreauEnvelope V ε x) z≤ moreauEnvelope V ε
                z)→A.det≤1) ∧
            (∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (ball c (R / 2))),
              ∃ A : Matrix (Fin n) (Fin n) ℝ, A.IsHermitian ∧
                HasFDerivAt (gradient (moreauEnvelope V ε))
                  (Matrix.toEuclideanLin A).toContinuousLinearMap x ∧
                A.PosSemidef ∧ A.det≤1 ∧
                ∀ t>0, ∀ᶠ y in 𝓝 x,
                  |moreauEnvelope V ε y-quadraticAt A x (gradient (moreauEnvelope V ε) x)
                    (moreauEnvelope V ε x) y|≤t*‖y-x‖^2)) ∧
          TendstoUniformlyOn (fun ε : ℝ => moreauEnvelope V ε) U (𝓝[>] (0:ℝ)) (closedBall c
            R)) := by
    obtain ⟨U, f, hs, hU, hz, hd, hf, he, hm, hu, hcomp, hquad, hc2, hbuf⟩ :=
      exists_envelope_buffered_moreau hn hΩ hcΩ hb
    refine ⟨U, f, hs, hU, hz, hd, hf, he, hm, hu, hcomp, hquad, hc2, ?_⟩
    intro c R hR hball
    obtain ⟨V, L, hV, hL, heq, hreg, hunif⟩ := hbuf c R hR hball
    refine ⟨V, L, hV, hL, heq, ?_, hunif⟩
    intro ε hε hsmall
    obtain ⟨hcv, hC, hLip, hTest⟩ := hreg ε hε hsmall
    refine ⟨hcv, hC, hLip, hTest, ?_⟩
    exact
      ae_matrix_of_quadratic_tests hcv isOpen_ball
        (hC.differentiable (by norm_num)).differentiableOn hTest

end Dirichlet
end FunctionalInequalities.Analysis

namespace FunctionalInequalities.Analysis.Dirichlet
open Set Filter Metric MeasureTheory
open scoped RealInnerProductSpace ENNReal Topology
open FunctionalInequalities.Probability.Stein

private theorem gradient_image_bound_of_ae_matrix {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {Ω Γ : Set (EuclideanSpace ℝ (Fin n))} {L : NNReal} (hLip : LipschitzWith L (gradient u))
    (hΓ : MeasurableSet Γ) (hΓΩ : Γ ⊆ Ω)
    (hAE :
      ∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict Ω),
        ∃ A : Matrix (Fin n) (Fin n) ℝ,
          A.IsHermitian ∧
            HasFDerivAt (gradient u) (Matrix.toEuclideanLin A).toContinuousLinearMap x ∧
              A.PosSemidef ∧
                A.det ≤ 1 ∧
                  ∀ t > 0,
                    ∀ᶠ y in 𝓝 x,
                      |u y - quadraticAt A x (gradient u x) (u x) y| ≤ t * ‖y - x‖ ^ 2) :
    volume ((gradient u) '' Γ) ≤ volume Γ := by
  have hd :
    ∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict Γ),
      ∃ D : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n),
        HasFDerivAt (gradient u) D x ∧ |D.det| ≤ (1 : ℝ) := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hΓΩ hAE] with x hx
    obtain ⟨A, _, hD, hp, hd, _⟩ := hx
    refine ⟨(Matrix.toEuclideanLin A).toContinuousLinearMap, hD, ?_⟩
    rw [show ((Matrix.toEuclideanLin A).toContinuousLinearMap).det = A.det from
        LinearMap.det_toLpLin 2 A,
      abs_of_nonneg hp.det_nonneg]
    exact hd
  simpa using
    addHaar_image_le_mul_of_ae_derivative volume hΓ hd
      (fun N _ hN => volume_image_eq_zero_of_lipschitzOnWith hLip.lipschitzOnWith hN)

/-- The SAME domain-generated buffered Perron regularizers have actual gradient
and DOMAIN supporting-image upper bounds. Actual Lipschitz gradients remove
singular null images; no AE/N/MA upper or unknown-U regularity is a source input. -/
theorem exists_envelope_buffered_moreau_image_upper {n : ℕ} (hn : 0<n)
    {Ω : Set (EuclideanSpace ℝ (Fin n))} (hΩ : IsOpen Ω) (hcΩ : Convex ℝ Ω)
    (hb : Bornology.IsBounded Ω) :
    ∃ (U : EuclideanSpace ℝ (Fin n)→ℝ) (f : ℕ→EuclideanSpace ℝ (Fin n)→ℝ),
      (∀ x∈closure Ω, U x=sSup ((fun w => w x) '' subsolutions Ω)) ∧
      U∈subsolutions Ω ∧ (∀ z∈frontier Ω, U z=0) ∧
      (∀ w∈subsolutions Ω, ∀ x∈closure Ω, w x≤U x) ∧
      (∀ j, f j∈subsolutions Ω) ∧
      (∀ j, ∀ x∈closure Ω, f j x≤U x ∧ |f j x-U x|<1 / ((j:ℝ) + 1)) ∧
      (∀ x, Monotone (fun j => f j x)) ∧
      TendstoUniformlyOn f U atTop (closure Ω) ∧
      (∀ (q : EuclideanSpace ℝ (Fin n)→ℝ), ConvexOn ℝ Ω q→ ContinuousOn q (closure Ω)→
        (∀ G, IsOpen G→G⊆Ω→volume G≤volume (subgradientImageOn q Ω G))→
        ∀ (c : EuclideanSpace ℝ (Fin n)) (r : ℝ), 0<r→closedBall c r⊆Ω→
          (∀ z∈sphere c r, q z≤U z)→∀ x∈ball c r, q x≤U x) ∧
      (∀ (A : Matrix (Fin n) (Fin n) ℝ), A.PosDef→∀ x∈Ω, ∀ b,
        (∀ᶠ y in 𝓝 x, quadraticAt A x b (U x) y≤U y)→A.det≤1) ∧
      (∀ (ψ : EuclideanSpace ℝ (Fin n)→ℝ), ∀ x∈Ω,
        ContDiffAt ℝ 2 ψ x→(hessianMatrix ψ x).PosSemidef→U x=ψ x→
        (∀ᶠ y in 𝓝 x, ψ y≤U y)→(hessianMatrix ψ x).det≤1) ∧
      (∀ (c : EuclideanSpace ℝ (Fin n)) (R : ℝ), 0<R→closedBall c R⊆Ω→
        ∃ (V : EuclideanSpace ℝ (Fin n)→ℝ) (L : NNReal),
          ConvexOn ℝ univ V ∧ LipschitzWith L V ∧ (∀ y∈closedBall c R, V y=U y) ∧
          (∀ ε : ℝ, 0<ε→ε * ((L:ℝ) + 1)<R / 2→
            ConvexOn ℝ univ (moreauEnvelope V ε) ∧ ContDiff ℝ 1 (moreauEnvelope V ε) ∧
            LipschitzWith (‖(ε⁻¹:ℝ)‖₊*2) (gradient (moreauEnvelope V ε)) ∧
            (∀ (A : Matrix (Fin n) (Fin n) ℝ), A.PosDef→∀ x∈ball c (R / 2), ∀ b,
              (∀ᶠ z in 𝓝 x, quadraticAt A x b (moreauEnvelope V ε x) z≤ moreauEnvelope V ε
                z)→A.det≤1) ∧
            (∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (ball c (R / 2))),
              ∃ A : Matrix (Fin n) (Fin n) ℝ, A.IsHermitian ∧
                HasFDerivAt (gradient (moreauEnvelope V ε))
                  (Matrix.toEuclideanLin A).toContinuousLinearMap x ∧
                A.PosSemidef ∧ A.det≤1 ∧
                ∀ t>0, ∀ᶠ y in 𝓝 x,
                  |moreauEnvelope V ε y-quadraticAt A x (gradient (moreauEnvelope V ε) x)
                    (moreauEnvelope V ε x) y|≤t*‖y-x‖^2) ∧
            (∀ Γ : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet Γ→Γ⊆ball c (R / 2)→
              volume ((gradient (moreauEnvelope V ε)) '' Γ)≤volume Γ ∧
              volume (subgradientImageOn (moreauEnvelope V ε) (ball c (R / 2)) Γ)≤volume Γ)) ∧
          TendstoUniformlyOn (fun ε : ℝ => moreauEnvelope V ε) U (𝓝[>] (0:ℝ)) (closedBall c
            R)) := by
    obtain ⟨U, f, hs, hU, hz, hd, hf, he, hm, hu, hcomp, hquad, hc2, hbuf⟩ :=
      exists_envelope_buffered_moreau_ae_matrix hn hΩ hcΩ hb
    refine ⟨U, f, hs, hU, hz, hd, hf, he, hm, hu, hcomp, hquad, hc2, ?_⟩
    intro c R hR hball
    obtain ⟨V, L, hV, hL, heq, hreg, hunif⟩ := hbuf c R hR hball
    refine ⟨V, L, hV, hL, heq, ?_, hunif⟩
    intro ε hε hsmall
    obtain ⟨hcv, hC, hLip, hTest, hAE⟩ := hreg ε hε hsmall
    refine ⟨hcv, hC, hLip, hTest, hAE, ?_⟩
    intro Γ hΓ hΓΩ
    have hgrad := gradient_image_bound_of_ae_matrix hLip hΓ hΓΩ hAE
    refine ⟨hgrad, le_trans ?_ hgrad⟩
    exact
      measure_mono
        (subgradientImageOn_subset_gradient_image isOpen_ball
          (hC.differentiable (by norm_num)).differentiableOn hΓΩ)

end FunctionalInequalities.Analysis.Dirichlet
