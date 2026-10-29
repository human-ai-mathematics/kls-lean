import FunctionalInequalities.Analysis.Convex.Legendre.Biconjugate
import FunctionalInequalities.Analysis.Convex.Legendre.Variation.Attainment
import FunctionalInequalities.Probability.MomentMeasure.FirstVariation
import FunctionalInequalities.Analysis.Convex.Subgradient.Basic

/-!
# Linear growth and ball truncation of a moment potential

Let `ψ : E → ℝ ∪ {+∞}` be a convex, lower semicontinuous potential on a finite-dimensional real
inner-product space with `0 < ∫ e^{-ψ} < ∞`, and let `φ = ψ*`.

* `exists_linear_lower_bound_of_mass`: `ψ(x) ≥ c‖x‖ − b` for some `c > 0`
  (Cordero-Erausquin–Klartag, *Moment measures*, arXiv:1304.0630v1, (7)). The sublevel set
  `{ψ ≤ M + 1}` above a ball where `ψ ≤ M` is convex of finite volume, hence bounded, and
  convexity along rays gives linear growth.
* `ballTruncate φ k`: the restriction of `φ` to the closed ball of radius `k` (`+∞` outside). Its
  conjugate `(ballTruncate ψ* k)*` is a finite convex `k`-Lipschitz minorant of `ψ`, increasing to
  `ψ` as `k → ∞` (Fenchel–Moreau), equal to `ψ` with the same gradient where `‖∇ψ‖ ≤ k`, and the
  Legendre supremum defining it is attained at its gradient. These are the finite potentials whose
  moment measures approximate that of `ψ` in the proof of CEK Theorem 8 for essentially continuous
  potentials.
-/

noncomputable section

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology RealInnerProductSpace

namespace FunctionalInequalities.Probability.MomentMeasure

open FunctionalInequalities.Analysis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

section Convexity

/-- Convexity of an extended-real potential in finite-value form. -/
private theorem le_combo_of_convexPotential {ψ : E → EReal} (hψ : ConvexPotential ψ) {a b : E} {s A B : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ha : ψ a ≤ A) (hb : ψ b ≤ B) :
    ψ ((1 - s) • a + s • b) ≤ (((1 - s) * A + s * B : ℝ) : EReal) := by
  have h := hψ.2 (show ((a, A) : E × ℝ) ∈ {p : E × ℝ | ψ p.1 ≤ (p.2 : EReal)} from ha)
    (show ((b, B) : E × ℝ) ∈ {p : E × ℝ | ψ p.1 ≤ (p.2 : EReal)} from hb)
    (show (0 : ℝ) ≤ 1 - s by linarith) hs0 (by ring)
  simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] at h
  exact h

end Convexity

section Truncation

/-- The restriction of a dual potential `φ` to the closed ball of radius `k`, `+∞` outside. -/
def ballTruncate (φ : E → EReal) (k : ℝ) (p : E) : EReal := if ‖p‖ ≤ k then φ p else ⊤

omit [InnerProductSpace ℝ E] in
theorem ballTruncate_of_norm_le (φ : E → EReal) {k : ℝ} {p : E} (hp : ‖p‖ ≤ k) :
    ballTruncate φ k p = φ p := if_pos hp

omit [InnerProductSpace ℝ E] in
theorem le_ballTruncate (φ : E → EReal) (k : ℝ) (p : E) : φ p ≤ ballTruncate φ k p := by
  unfold ballTruncate
  split_ifs
  · exact le_rfl
  · exact le_top

omit [InnerProductSpace ℝ E] in
theorem ballTruncate_anti (φ : E → EReal) {k k' : ℝ} (hk : k ≤ k') (p : E) :
    ballTruncate φ k' p ≤ ballTruncate φ k p := by
  unfold ballTruncate
  by_cases hp : ‖p‖ ≤ k
  · rw [if_pos hp, if_pos (hp.trans hk)]
  · rw [if_neg hp]; exact le_top

omit [InnerProductSpace ℝ E] in
theorem lowerSemicontinuous_ballTruncate {φ : E → EReal} (hφ : LowerSemicontinuous φ) (k : ℝ) :
    LowerSemicontinuous (ballTruncate φ k) := by
  intro p y hy
  by_cases hp : ‖p‖ ≤ k
  · rw [ballTruncate_of_norm_le φ hp] at hy
    filter_upwards [hφ p y hy] with q hq
    exact hq.trans_le (le_ballTruncate φ k q)
  · have hopen : IsOpen {q : E | k < ‖q‖} := isOpen_lt continuous_const continuous_norm
    filter_upwards [hopen.mem_nhds (not_le.mp hp)] with q hq
    have hq' : ¬‖q‖ ≤ k := not_le.mpr hq
    rw [ballTruncate, if_neg hq']
    rw [ballTruncate, if_neg hp] at hy
    exact hy

/-- A primal potential above `c‖x‖ − b` has conjugate at most `b` on the ball of radius `c`. -/
theorem legendre_le_of_linear_lower_bound {ψ : E → EReal} {c b : ℝ}
    (hlow : ∀ x, ((c * ‖x‖ - b : ℝ) : EReal) ≤ ψ x) {p : E} (hp : ‖p‖ ≤ c) :
    legendre ψ p ≤ (b : EReal) := by
  apply iSup_le
  intro x
  have h := hlow x
  have hin : inner ℝ x p ≤ c * ‖x‖ := by
    have := real_inner_le_norm x p
    nlinarith [norm_nonneg x]
  generalize ψ x = s at h ⊢
  induction s using EReal.rec with
  | bot => exact absurd h (not_le.mpr (EReal.bot_lt_coe _))
  | top => simp
  | coe s =>
    rw [← EReal.coe_sub, EReal.coe_le_coe_iff]
    rw [EReal.coe_le_coe_iff] at h
    linarith

section Conjugate

variable {ψ : E → EReal}

/-- Ball truncations increase with the radius. -/
theorem legendre_ballTruncate_mono (φ : E → EReal) {k k' : ℝ} (hk : k ≤ k') (x : E) :
    legendre (ballTruncate φ k) x ≤ legendre (ballTruncate φ k') x :=
  legendre_antitone (ballTruncate_anti φ hk) x

section Complete

variable [CompleteSpace E]

/-- The conjugate of a ball truncation of `ψ*` lies below `ψ` (Fenchel–Moreau). -/
theorem legendre_ballTruncate_le (hψ : ConvexPotential ψ) (hlsc : LowerSemicontinuous ψ)
    (hne : ∃ x, ψ x ≠ ⊤) (k : ℝ) (x : E) :
    legendre (ballTruncate (legendre ψ) k) x ≤ ψ x := by
  conv_rhs => rw [← legendre_legendre_eq hψ hlsc hne]
  exact legendre_antitone (le_ballTruncate _ k) x

/-- The conjugates of the ball truncations of `ψ*` converge to `ψ` (Fenchel–Moreau). -/
theorem iSup_legendre_ballTruncate (hψ : ConvexPotential ψ) (hlsc : LowerSemicontinuous ψ)
    (hne : ∃ x, ψ x ≠ ⊤) (x : E) :
    ⨆ k : ℕ, legendre (ballTruncate (legendre ψ) k) x = ψ x := by
  refine le_antisymm (iSup_le fun k => legendre_ballTruncate_le hψ hlsc hne k x) ?_
  conv_lhs => rw [← legendre_legendre_eq hψ hlsc hne]
  apply iSup_le
  intro p
  obtain ⟨k, hk⟩ := exists_nat_ge ‖p‖
  refine le_trans ?_ (le_iSup _ k)
  refine le_trans ?_ (le_iSup _ p)
  rw [ballTruncate_of_norm_le _ hk]

end Complete

/-- Linear growth passes to the ball truncations of radius at least the growth rate. -/
theorem linear_lower_bound_legendre_ballTruncate {c b : ℝ}
    (hlow : ∀ x, ((c * ‖x‖ - b : ℝ) : EReal) ≤ ψ x) (hc : 0 ≤ c) {k : ℝ} (hk : c ≤ k) (x : E) :
    ((c * ‖x‖ - b : ℝ) : EReal) ≤ legendre (ballTruncate (legendre ψ) k) x := by
  by_cases hx : x = 0
  · subst hx
    have h0 : legendre ψ 0 ≤ (b : EReal) :=
      legendre_le_of_linear_lower_bound hlow (by rw [norm_zero]; exact hc)
    refine le_trans ?_ (le_iSup _ (0 : E))
    rw [ballTruncate_of_norm_le _ (by rw [norm_zero]; linarith), inner_zero_left, norm_zero,
      mul_zero, zero_sub, EReal.coe_neg, EReal.coe_zero, zero_sub]
    exact EReal.neg_le_neg_iff.mpr h0
  · set p : E := (c / ‖x‖) • x with hpdef
    have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hpn : ‖p‖ = c := by
      rw [hpdef, norm_smul, Real.norm_of_nonneg (div_nonneg hc hxn.le)]
      field_simp
    have hpx : inner ℝ p x = c * ‖x‖ := by
      rw [hpdef, real_inner_smul_left, real_inner_self_eq_norm_sq]
      field_simp
    have hφ : legendre ψ p ≤ (b : EReal) := legendre_le_of_linear_lower_bound hlow hpn.le
    refine le_trans ?_ (le_iSup _ p)
    rw [ballTruncate_of_norm_le _ (by rw [hpn]; exact hk), hpx, EReal.coe_sub]
    exact EReal.sub_le_sub le_rfl hφ

/-- Conjugates of ball truncations are finite: `(φ|_{B_k})*(x) ≤ k‖x − x₁‖ + ψ(x₁)`. -/
theorem legendre_ballTruncate_le_add {x₁ : E} {A : ℝ} (hx₁ : ψ x₁ ≤ A) (k : ℝ) (x : E) :
    legendre (ballTruncate (legendre ψ) k) x ≤ ((k * ‖x - x₁‖ + A : ℝ) : EReal) := by
  apply iSup_le
  intro p
  by_cases hp : ‖p‖ ≤ k
  · rw [ballTruncate_of_norm_le _ hp]
    have hφ : ((inner ℝ x₁ p - A : ℝ) : EReal) ≤ legendre ψ p := by
      refine le_trans ?_ (le_iSup _ x₁)
      rw [EReal.coe_sub]
      exact EReal.sub_le_sub le_rfl hx₁
    have hin : inner ℝ p x - inner ℝ x₁ p ≤ k * ‖x - x₁‖ := by
      rw [real_inner_comm p x₁, ← inner_sub_right]
      have := real_inner_le_norm p (x - x₁)
      nlinarith [norm_nonneg (x - x₁)]
    calc (inner ℝ p x : EReal) - legendre ψ p
        ≤ (inner ℝ p x : EReal) - ((inner ℝ x₁ p - A : ℝ) : EReal) :=
          EReal.sub_le_sub le_rfl hφ
      _ = ((inner ℝ p x - (inner ℝ x₁ p - A) : ℝ) : EReal) := by norm_cast
      _ ≤ ((k * ‖x - x₁‖ + A : ℝ) : EReal) := EReal.coe_le_coe_iff.mpr (by linarith)
  · rw [ballTruncate, if_neg hp]; simp

/-- Conjugates of ball truncations of radius `k` are `k`-Lipschitz from above. -/
theorem legendre_ballTruncate_le_add_norm (φ : E → EReal) (k : ℝ) (x y : E) :
    legendre (ballTruncate φ k) x ≤
      legendre (ballTruncate φ k) y + ((k * ‖x - y‖ : ℝ) : EReal) := by
  apply iSup_le
  intro p
  by_cases hp : ‖p‖ ≤ k
  · have hin : inner ℝ p x ≤ inner ℝ p y + k * ‖x - y‖ := by
      have := real_inner_le_norm p (x - y)
      rw [inner_sub_right] at this
      nlinarith [norm_nonneg (x - y)]
    have hy := le_iSup (fun q => (inner ℝ q y : EReal) - ballTruncate φ k q) p
    change (inner ℝ p y : EReal) - ballTruncate φ k p ≤ legendre (ballTruncate φ k) y at hy
    generalize ballTruncate φ k p = t at hy ⊢
    induction t using EReal.rec with
    | bot =>
      simp only [EReal.sub_bot (EReal.coe_ne_bot _), top_le_iff] at hy
      rw [hy, EReal.top_add_coe]
      exact le_top
    | top => simp
    | coe t =>
      rw [← EReal.coe_sub] at hy ⊢
      calc ((inner ℝ p x - t : ℝ) : EReal) ≤ ((inner ℝ p y - t : ℝ) : EReal) +
            ((k * ‖x - y‖ : ℝ) : EReal) := by
            rw [← EReal.coe_add, EReal.coe_le_coe_iff]; linarith
        _ ≤ _ := by gcongr
  · rw [ballTruncate, if_neg hp]; simp

end Conjugate

end Truncation

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

section Growth

omit [FiniteDimensional ℝ E] in
/-- A convex set of finite Haar measure containing a ball around the origin is bounded. -/
private theorem isBounded_of_convex_of_measure_lt_top (m : Measure E) [m.IsAddHaarMeasure]
    (s : Set E) (hcs : Convex ℝ s) (hms : m s < (⊤ : ENNReal))
    (hrball : ∃ r : ℝ, 0 < r ∧ Metric.ball (0 : E) r ⊆ s) : Bornology.IsBounded s := by
  obtain ⟨r, hr, hball⟩ := hrball
  have hzero : (0 : E) ∈ s := hball (by simpa using hr)
  let b : ENNReal := m (Metric.ball (0 : E) (r / 2))
  have hbfinite : b < (⊤ : ENNReal) := by
    apply lt_of_le_of_lt _ hms
    apply measure_mono
    exact (Metric.ball_subset_ball (by linarith : r / 2 ≤ r)).trans hball
  have hbne : b ≠ 0 :=
    ne_of_gt (Metric.measure_ball_pos m (0 : E) (by linarith : 0 < r / 2))
  have hbpos : 0 < b.toReal := by
    by_contra hh
    have hz : b.toReal = 0 :=
      le_antisymm (le_of_not_gt hh) ENNReal.toReal_nonneg
    have he := ENNReal.ofReal_toReal (ne_of_lt hbfinite)
    rw [hz, ENNReal.ofReal_zero] at he
    exact hbne he.symm
  have hballmeasure (z : E) :
      m (Metric.ball z (r / 2)) = b := by
    dsimp [b]
    have hh :
        Metric.ball (0 : E) (r / 2) =
          (z + ·) ⁻¹' Metric.ball z (r / 2) := by
      simp [preimage_add_ball]
    rw [hh, measure_preimage_add]
  obtain ⟨N, hN⟩ := exists_nat_gt (max ((m s).toReal / b.toReal) 1)
  have hNratio : (m s).toReal / b.toReal < (N : ℝ) :=
    lt_of_le_of_lt (le_max_left _ _) hN
  have hNpos : 0 < (N : ℝ) :=
    lt_trans (by norm_num : (0 : ℝ) < 1)
      (lt_of_le_of_lt (le_max_right _ _) hN)
  apply (Metric.isBounded_iff_subset_closedBall (0 : E)).2
  refine ⟨2 * (N : ℝ) * r, ?_⟩
  intro x hx
  change dist x 0 ≤ 2 * (N : ℝ) * r
  rw [dist_zero_right]
  by_contra hnx
  have hlarge : 2 * (N : ℝ) * r < ‖x‖ := lt_of_not_ge hnx
  have hxpos : 0 < ‖x‖ :=
    lt_trans (by positivity) hlarge
  let f : Fin N → E := fun i => ((i.val : ℝ) * r / ‖x‖) • x
  have hinside (i : Fin N) :
      Metric.ball (f i) (r / 2) ⊆ s := by
    intro z hz
    let t : ℝ := (i.val : ℝ) * r / ‖x‖
    have ht : 0 ≤ t := by
      dsimp [t]
      positivity
    have hi : (i.val : ℝ) < (N : ℝ) := by
      exact_mod_cast i.isLt
    have hir : (i.val : ℝ) * r < (N : ℝ) * r :=
      mul_lt_mul_of_pos_right hi hr
    have htupper : 2 * t ≤ 1 := by
      dsimp [t]
      rw [← mul_div_assoc, div_le_iff₀ hxpos]
      nlinarith [hir, hlarge]
    have hu : (2 : ℝ) • (z - t • x) ∈ s := by
      apply hball
      rw [Metric.mem_ball, dist_eq_norm, sub_zero, norm_smul,
        Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      have hz' : ‖z - t • x‖ < r / 2 := by
        rw [Metric.mem_ball, dist_eq_norm] at hz
        simpa [f, t] using hz
      linarith
    have hv : (2 * t) • x ∈ s := by
      have hv' := hcs hzero hx
        (a := 1 - 2 * t) (b := 2 * t)
        (by linarith) (by positivity) (by ring)
      simpa using hv'
    have hm := hcs hu hv
      (a := (1 / 2 : ℝ)) (b := (1 / 2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num)
    have he :
        (1 / 2 : ℝ) • ((2 : ℝ) • (z - t • x)) +
            (1 / 2 : ℝ) • ((2 * t) • x) = z := by
      module
    rwa [he] at hm
  have hdis :
      Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin N)))
        (fun i => Metric.ball (f i) (r / 2)) := by
    intro i _ j _ hij
    apply Metric.ball_disjoint_ball
    have hdist :
        dist (f i) (f j) = |(i.val : ℝ) - (j.val : ℝ)| * r := by
      dsimp [f]
      rw [dist_eq_norm, ← sub_smul, norm_smul, Real.norm_eq_abs]
      have he :
          (i.val : ℝ) * r / ‖x‖ - (j.val : ℝ) * r / ‖x‖ =
            ((i.val : ℝ) - (j.val : ℝ)) * (r / ‖x‖) := by
        ring
      rw [he, abs_mul, abs_of_pos (div_pos hr hxpos)]
      field_simp [ne_of_gt hxpos]
    have hval : i.val ≠ j.val := by
      intro he
      exact hij (Fin.ext he)
    have habs : 1 ≤ |(i.val : ℝ) - (j.val : ℝ)| := by
      have hord : i.val + 1 ≤ j.val ∨ j.val + 1 ≤ i.val := by
        omega
      rcases hord with hij' | hji'
      · have hh : (i.val : ℝ) + 1 ≤ (j.val : ℝ) := by
          exact_mod_cast hij'
        rw [abs_of_nonpos (by linarith)]
        linarith
      · have hh : (j.val : ℝ) + 1 ≤ (i.val : ℝ) := by
          exact_mod_cast hji'
        rw [abs_of_nonneg (by linarith)]
        linarith
    have hmul :
        (1 : ℝ) * r ≤ |(i.val : ℝ) - (j.val : ℝ)| * r :=
      mul_le_mul_of_nonneg_right habs (le_of_lt hr)
    rw [hdist]
    nlinarith [hmul]
  have hmass : (N : ENNReal) * b ≤ m s := by
    calc
      _ = ∑ i : Fin N, b := by
        simp [nsmul_eq_mul]
      _ = ∑ i : Fin N, m (Metric.ball (f i) (r / 2)) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact (hballmeasure (f i)).symm
      _ = ∑ i ∈ (Finset.univ : Finset (Fin N)),
          m (Metric.ball (f i) (r / 2)) := by
        simp
      _ = m (⋃ i ∈ (Finset.univ : Finset (Fin N)),
          Metric.ball (f i) (r / 2)) :=
        (measure_biUnion_finset hdis
          (fun _ _ => measurableSet_ball)).symm
      _ ≤ m s := by
        apply measure_mono
        intro z hz
        obtain ⟨i, _, hzi⟩ := Set.mem_iUnion₂.mp hz
        exact hinside i hzi
  have hreal := ENNReal.toReal_mono (ne_of_lt hms) hmass
  simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast] at hreal
  have hstrict : (m s).toReal < (N : ℝ) * b.toReal :=
    (div_lt_iff₀ hbpos).mp hNratio
  exact (not_lt_of_ge hreal) hstrict


omit [MeasurableSpace E] [BorelSpace E] in
/-- A lower semicontinuous convex potential that is finite somewhere has an affine minorant
`⟪x, p⟫ − C`; it comes from a point where the conjugate is finite (Fenchel–Moreau). -/
theorem exists_affine_minorant {ψ : E → EReal} (hψ : ConvexPotential ψ)
    (hlsc : LowerSemicontinuous ψ) (hne : ∃ x, ψ x ≠ ⊤) :
    ∃ (p : E) (C : ℝ), ∀ x, ((inner ℝ x p - C : ℝ) : EReal) ≤ ψ x := by
  have hbi := legendre_legendre_eq hψ hlsc hne
  obtain ⟨p, hp⟩ : ∃ p, legendre ψ p ≠ ⊤ := by
    by_contra hall
    push Not at hall
    obtain ⟨x, hx⟩ := hne
    have hbot : legendre (legendre ψ) x = ⊥ := by
      refine le_antisymm (iSup_le fun q => ?_) bot_le
      simp [hall q]
    exact hψ.1 x (by rw [← hbi]; exact hbot)
  have hpb : legendre ψ p ≠ ⊥ := legendre_ne_bot ψ ⟨hψ.1, hne⟩ p
  refine ⟨p, (legendre ψ p).toReal, fun x => ?_⟩
  have h := fenchel_le ψ ⟨hψ.1, hne⟩ x p
  rw [← EReal.coe_toReal hp hpb] at h
  rw [EReal.coe_sub]
  exact EReal.sub_le_of_le_add h

/-- **Linear growth of a potential with finite nonzero mass** (Cordero-Erausquin–Klartag,
arXiv:1304.0630v1, (7)): a convex, lower semicontinuous `ψ : E → ℝ ∪ {+∞}` with
`0 < ∫ e^{-ψ} < ∞` satisfies `ψ(x) ≥ c‖x‖ − b` for some `c > 0`. -/
theorem exists_linear_lower_bound_of_mass {ψ : E → EReal} (hψ : ConvexPotential ψ)
    (hlsc : LowerSemicontinuous ψ) (h0 : mass volume ψ ≠ 0) (htop : mass volume ψ ≠ ⊤) :
    ∃ c : ℝ, 0 < c ∧ ∃ b : ℝ, ∀ x, ((c * ‖x‖ - b : ℝ) : EReal) ≤ ψ x := by
  set K := {x | ψ x ≠ ⊤} with hKdef
  obtain ⟨x₀, hx₀⟩ := interior_domain_nonempty_of_mass_ne_zero volume hψ h0
  have hne : ∃ x, ψ x ≠ ⊤ := ⟨x₀, interior_subset hx₀⟩
  have hconv : ConvexOn ℝ (interior K) (fun x => (ψ x).toReal) :=
    hψ.convexOn_toReal.subset interior_subset hψ.convex_domain.interior
  have hcont : ContinuousOn (fun x => (ψ x).toReal) (interior K) :=
    hconv.continuousOn isOpen_interior
  have hcoe : ∀ y ∈ interior K, ψ y = ((ψ y).toReal : EReal) := fun y hy =>
    (EReal.coe_toReal (interior_subset hy) (hψ.1 y)).symm
  obtain ⟨r, hr, hrball⟩ := Metric.isOpen_iff.mp isOpen_interior x₀ hx₀
  have hcb : closedBall x₀ (r / 2) ⊆ interior K :=
    (closedBall_subset_ball (by linarith)).trans hrball
  obtain ⟨y₁, -, hmax⟩ := (isCompact_closedBall x₀ (r / 2)).exists_isMaxOn
    (nonempty_closedBall.mpr (by linarith)) (hcont.mono hcb)
  set M := (ψ y₁).toReal with hMdef
  have hM : ∀ y ∈ closedBall x₀ (r / 2), ψ y ≤ (M : EReal) := fun y hy => by
    rw [hcoe y (hcb hy), EReal.coe_le_coe_iff]
    exact isMaxOn_iff.mp hmax y hy
  -- the sublevel set `{ψ ≤ M + 1}` has finite volume
  set S : Set E := {y | ψ y ≤ ((M + 1 : ℝ) : EReal)} with hSdef
  have hSconv : Convex ℝ S := by
    intro a ha b hb u v hu hv huv
    have h := le_combo_of_convexPotential hψ (s := v) hv (by linarith) ha hb
    rw [show 1 - v = u by linarith] at h
    refine h.trans ?_
    rw [EReal.coe_le_coe_iff, ← add_mul, huv, one_mul]
  have hSvol : volume S < ⊤ := by
    have hle : ENNReal.ofReal (Real.exp (-(M + 1))) * volume S ≤ mass volume ψ := by
      rw [← lintegral_indicator_const₀ (hSconv.nullMeasurableSet (μ := volume)), mass]
      refine lintegral_mono fun y => ?_
      by_cases hy : y ∈ S
      · rw [indicator_of_mem hy, density]
        have h := EReal.exp_monotone (EReal.neg_le_neg_iff.mpr (show ψ y ≤ _ from hy))
        rwa [← EReal.coe_neg, EReal.exp_coe] at h
      · rw [indicator_of_notMem hy]; exact zero_le
    have hc : ENNReal.ofReal (Real.exp (-(M + 1))) ≠ 0 :=
      (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
    by_contra hS
    rw [not_lt, top_le_iff] at hS
    rw [hS, ENNReal.mul_top hc] at hle
    exact htop (top_le_iff.mp hle)
  set T : Set E := (fun y => y + x₀) ⁻¹' S with hTdef
  have hT : Bornology.IsBounded T := by
    refine isBounded_of_convex_of_measure_lt_top volume T ?_ ?_ ⟨r / 2, by linarith, ?_⟩
    · exact hSconv.translate_preimage_left x₀
    · rw [hTdef, measure_preimage_add_right]; exact hSvol
    · intro y hy
      have : y + x₀ ∈ closedBall x₀ (r / 2) := by
        rw [mem_closedBall, dist_eq_norm, add_sub_cancel_right]
        exact (mem_ball_zero_iff.mp hy).le
      exact (hM _ this).trans (EReal.coe_le_coe_iff.mpr (by linarith))
  obtain ⟨D, hD⟩ := hT.subset_closedBall (0 : E)
  set D' : ℝ := max D 0 + 1 with hD'def
  have hD'pos : 0 < D' := by positivity
  have hfar : ∀ y, ψ y ≤ ((M + 1 : ℝ) : EReal) → ‖y - x₀‖ ≤ max D 0 := by
    intro y hy
    have h := hD (show y - x₀ ∈ T by rw [hTdef, mem_preimage, sub_add_cancel]; exact hy)
    rw [mem_closedBall, dist_zero_right] at h
    exact h.trans (le_max_left _ _)
  obtain ⟨p, C, hpC⟩ := exists_affine_minorant hψ hlsc hne
  have hx₀M : (ψ x₀).toReal ≤ M := by
    have h := hM x₀ (mem_closedBall_self (by linarith))
    rwa [hcoe x₀ hx₀, EReal.coe_le_coe_iff] at h
  refine ⟨1 / D', by positivity, max (‖x₀‖ / D' - M)
    ((‖x₀‖ + D') * ‖p‖ + |C| + (‖x₀‖ + D') / D'), fun x => ?_⟩
  by_cases hxt : ψ x = ⊤
  · rw [hxt]; exact le_top
  have hxr : ψ x = ((ψ x).toReal : EReal) := (EReal.coe_toReal hxt (hψ.1 x)).symm
  rw [hxr, EReal.coe_le_coe_iff]
  by_cases hxd : D' ≤ ‖x - x₀‖
  · -- far points: compare with the point at distance `D'` on the segment from `x₀`
    set t := ‖x - x₀‖ with ht
    have htpos : 0 < t := lt_of_lt_of_le hD'pos hxd
    set σ : ℝ := D' / t with hσ
    have hσ0 : 0 < σ := by positivity
    have hσ1 : σ ≤ 1 := (div_le_one htpos).mpr hxd
    set z : E := (1 - σ) • x₀ + σ • x with hz
    have hzx : z - x₀ = σ • (x - x₀) := by rw [hz]; module
    have hzn : ‖z - x₀‖ = D' := by
      rw [hzx, norm_smul, Real.norm_of_nonneg hσ0.le, hσ, ← ht]
      field_simp
    have hzS : ¬ψ z ≤ ((M + 1 : ℝ) : EReal) := fun h => by
      have := hfar z h
      rw [hzn, hD'def] at this
      linarith
    have hcomb := le_combo_of_convexPotential hψ hσ0.le hσ1 (hcoe x₀ hx₀).le hxr.le
    have hlt : M + 1 < (1 - σ) * (ψ x₀).toReal + σ * (ψ x).toReal := by
      by_contra hle
      exact hzS (hcomb.trans (EReal.coe_le_coe_iff.mpr (not_lt.mp hle)))
    have hkey : 1 < σ * ((ψ x).toReal - M) := by nlinarith
    have hσt : σ * t = D' := by rw [hσ]; field_simp
    have hxn : ‖x‖ ≤ t + ‖x₀‖ := by
      have := norm_sub_norm_le x x₀
      linarith
    have hineq : t / D' ≤ (ψ x).toReal - M := by
      rw [div_le_iff₀ hD'pos, ← hσt]
      nlinarith
    have hb := le_max_left (‖x₀‖ / D' - M) ((‖x₀‖ + D') * ‖p‖ + |C| + (‖x₀‖ + D') / D')
    have : 1 / D' * ‖x‖ ≤ t / D' + ‖x₀‖ / D' := by
      rw [one_div_mul_eq_div, ← add_div]
      exact div_le_div_of_nonneg_right hxn hD'pos.le
    linarith
  · -- near points: the affine minorant
    push Not at hxd
    have hxn : ‖x‖ ≤ ‖x₀‖ + D' := by
      have := norm_le_norm_add_norm_sub' x x₀
      linarith [norm_sub_rev x x₀]
    have h := hpC x
    rw [hxr, EReal.coe_le_coe_iff] at h
    have hin : -(‖x‖ * ‖p‖) ≤ inner ℝ x p := by
      have := abs_real_inner_le_norm x p
      linarith [neg_abs_le (inner ℝ x p)]
    have hb := le_max_right (‖x₀‖ / D' - M) ((‖x₀‖ + D') * ‖p‖ + |C| + (‖x₀‖ + D') / D')
    have h1 : 1 / D' * ‖x‖ ≤ (‖x₀‖ + D') / D' := by
      rw [one_div_mul_eq_div]
      exact div_le_div_of_nonneg_right hxn hD'pos.le
    have h2 : ‖x‖ * ‖p‖ ≤ (‖x₀‖ + D') * ‖p‖ := mul_le_mul_of_nonneg_right hxn (norm_nonneg _)
    linarith [le_abs_self C]

end Growth

section RealTruncation

variable {ψ : E → EReal}

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The ball truncation of `ψ*` is finite at the origin when `ψ ≥ c‖·‖ − b`. -/
theorem ballTruncate_legendre_zero_ne_top {c b : ℝ}
    (hlow : ∀ x, ((c * ‖x‖ - b : ℝ) : EReal) ≤ ψ x) (hc : 0 ≤ c) {k : ℝ} (hk : c ≤ k) :
    ballTruncate (legendre ψ) k 0 ≠ ⊤ := by
  have h0 : legendre ψ 0 ≤ (b : EReal) :=
    legendre_le_of_linear_lower_bound hlow (by rw [norm_zero]; exact hc)
  rw [ballTruncate_of_norm_le _ (by rw [norm_zero]; exact hc.trans hk)]
  exact ne_top_of_le_ne_top (EReal.coe_ne_top _) h0

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Ball truncations of radius `k ≥ c` of a potential above `c‖x‖ − b` and finite at `x₁` have
finite conjugates. -/
theorem legendre_ballTruncate_ne_top_ne_bot {c b : ℝ}
    (hlow : ∀ x, ((c * ‖x‖ - b : ℝ) : EReal) ≤ ψ x) (hc : 0 ≤ c) {k : ℝ} (hk : c ≤ k)
    {x₁ : E} (hx₁ : ψ x₁ ≠ ⊤) (x : E) :
    legendre (ballTruncate (legendre ψ) k) x ≠ ⊤ ∧
      legendre (ballTruncate (legendre ψ) k) x ≠ ⊥ := by
  have hb : ψ x₁ ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (hlow x₁)
  refine ⟨ne_top_of_le_ne_top (EReal.coe_ne_top _)
    (legendre_ballTruncate_le_add (EReal.coe_toReal hx₁ hb).symm.le k x), ?_⟩
  exact ne_bot_of_le_ne_bot (EReal.coe_ne_bot _)
    (linear_lower_bound_legendre_ballTruncate hlow hc hk x)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The real truncated potential is convex on the whole space. -/
theorem convexOn_toReal_legendre_ballTruncate {c b : ℝ}
    (hlow : ∀ x, ((c * ‖x‖ - b : ℝ) : EReal) ≤ ψ x) (hc : 0 ≤ c) {k : ℝ} (hk : c ≤ k)
    {x₁ : E} (hx₁ : ψ x₁ ≠ ⊤) :
    ConvexOn ℝ univ (fun x => (legendre (ballTruncate (legendre ψ) k) x).toReal) := by
  have hfin := legendre_ballTruncate_ne_top_ne_bot hlow hc hk hx₁
  have hconv := (convexPotential_legendre (ballTruncate (legendre ψ) k)
    ⟨0, ballTruncate_legendre_zero_ne_top hlow hc hk⟩).convexOn_toReal
  have hdom : {x | legendre (ballTruncate (legendre ψ) k) x ≠ ⊤} = univ :=
    eq_univ_of_forall fun x => (hfin x).1
  rwa [hdom] at hconv

omit [MeasurableSpace E] [BorelSpace E] in
/-- The real truncated potential of radius `k` has gradient of norm at most `k`. -/
theorem norm_gradient_toReal_legendre_ballTruncate_le {c b : ℝ}
    (hlow : ∀ x, ((c * ‖x‖ - b : ℝ) : EReal) ≤ ψ x) (hc : 0 ≤ c) {k : ℝ} (hk : c ≤ k)
    {x₁ : E} (hx₁ : ψ x₁ ≠ ⊤) (x : E) :
    ‖gradient (fun x => (legendre (ballTruncate (legendre ψ) k) x).toReal) x‖ ≤ k := by
  set F := fun x => (legendre (ballTruncate (legendre ψ) k) x).toReal
  have hfin := legendre_ballTruncate_ne_top_ne_bot hlow hc hk hx₁
  have hk0 : 0 ≤ k := hc.trans hk
  have hlip : LipschitzWith (Real.toNNReal k) F := by
    refine LipschitzWith.of_dist_le_mul fun y z => ?_
    rw [Real.dist_eq, Real.coe_toNNReal _ hk0, dist_eq_norm]
    have h1 := legendre_ballTruncate_le_add_norm (legendre ψ) k y z
    have h2 := legendre_ballTruncate_le_add_norm (legendre ψ) k z y
    rw [← EReal.coe_toReal (hfin y).1 (hfin y).2, ← EReal.coe_toReal (hfin z).1 (hfin z).2,
      ← EReal.coe_add, EReal.coe_le_coe_iff] at h1 h2
    rw [norm_sub_rev] at h2
    exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
  have h := norm_fderiv_le_of_lipschitz ℝ (x₀ := x) hlip
  rw [Real.coe_toNNReal _ hk0] at h
  rw [gradient, LinearIsometryEquiv.norm_map]
  exact h

omit [MeasurableSpace E] [BorelSpace E] in
/-- **The truncated Legendre supremum is attained at the gradient**: where the real truncated
potential `Ψₖ` is differentiable, `‖∇Ψₖ(x)‖ ≤ k` and `ψ*(∇Ψₖ(x)) = ⟪x, ∇Ψₖ(x)⟫ − Ψₖ(x)`. -/
theorem legendre_gradient_toReal_legendre_ballTruncate {c b : ℝ}
    (hψ : ConvexPotential ψ)
    (hlow : ∀ x, ((c * ‖x‖ - b : ℝ) : EReal) ≤ ψ x) (hc : 0 ≤ c) {k : ℝ} (hk : c ≤ k)
    {x₁ : E} (hx₁ : ψ x₁ ≠ ⊤) {x : E}
    (hd : DifferentiableAt ℝ (fun x => (legendre (ballTruncate (legendre ψ) k) x).toReal) x) :
    ‖gradient (fun x => (legendre (ballTruncate (legendre ψ) k) x).toReal) x‖ ≤ k ∧
      legendre ψ (gradient (fun x => (legendre (ballTruncate (legendre ψ) k) x).toReal) x) =
        ((inner ℝ x (gradient (fun x => (legendre (ballTruncate (legendre ψ) k) x).toReal) x) -
          (legendre (ballTruncate (legendre ψ) k) x).toReal : ℝ) : EReal) := by
  have hfin := legendre_ballTruncate_ne_top_ne_bot hlow hc hk hx₁
  have hne : ∃ y, ψ y ≠ ⊤ := ⟨x₁, hx₁⟩
  have hφ0 : (ballTruncate (legendre ψ) k) 0 ≠ ⊤ := ballTruncate_legendre_zero_ne_top hlow hc hk
  have hprop : ProperPotential (ballTruncate (legendre ψ) k) :=
    ⟨fun p => ne_bot_of_le_ne_bot (legendre_ne_bot ψ ⟨hψ.1, hne⟩ p) (le_ballTruncate _ k p),
      0, hφ0⟩
  have hint : x ∈ interior {q : E | legendre (ballTruncate (legendre ψ) k) q ≠ ⊤} := by
    rw [show {q : E | legendre (ballTruncate (legendre ψ) k) q ≠ ⊤} = univ from
      eq_univ_of_forall fun q => (hfin q).1,
      interior_univ]
    exact mem_univ x
  obtain ⟨z, hz, hzg⟩ :=
    exists_legendre_maximizer_with_gradient_identity (ballTruncate (legendre ψ) k) hprop
    (lowerSemicontinuous_ballTruncate (lowerSemicontinuous_legendre ψ) k) x hint
  have hzeq := hzg hd
  rw [← hzeq]
  have hxr : legendre (ballTruncate (legendre ψ) k) x =
      ((legendre (ballTruncate (legendre ψ) k) x).toReal : EReal) :=
    (EReal.coe_toReal (hfin x).1 (hfin x).2).symm
  have hzk : ‖z‖ ≤ k := by
    by_contra hzk
    unfold ballTruncate at hz
    rw [if_neg hzk, EReal.sub_top] at hz
    exact (hfin x).2 hz.symm
  refine ⟨hzk, ?_⟩
  rw [ballTruncate_of_norm_le _ hzk] at hz
  rw [hxr] at hz
  have hzb : legendre ψ z ≠ ⊥ := legendre_ne_bot ψ ⟨hψ.1, hne⟩ z
  have hzt : legendre ψ z ≠ ⊤ := by
    intro h
    rw [h] at hz
    simp at hz
  rw [← EReal.coe_toReal hzt hzb] at hz ⊢
  rw [← EReal.coe_sub, EReal.coe_eq_coe_iff] at hz
  rw [EReal.coe_eq_coe_iff, real_inner_comm]
  linarith

omit [MeasurableSpace E] [BorelSpace E] in
/-- At an interior differentiability point of a convex potential, its gradient is a subgradient:
`ψ*(∇ψ(x)) ≤ ⟪x, ∇ψ(x)⟫ − ψ(x)`. -/
theorem legendre_gradient_le (hψ : ConvexPotential ψ) {x : E}
    (hx : x ∈ interior {y | ψ y ≠ ⊤}) (hd : DifferentiableAt ℝ (fun y => (ψ y).toReal) x) :
    legendre ψ (gradient (fun y => (ψ y).toReal) x) ≤
      ((inner ℝ x (gradient (fun y => (ψ y).toReal) x) - (ψ x).toReal : ℝ) : EReal) := by
  set p := gradient (fun y => (ψ y).toReal) x
  apply iSup_le
  intro y
  by_cases hy : ψ y = ⊤
  · rw [hy, EReal.sub_top]; exact bot_le
  have hsupp := convex_support_of_hasFDerivWithinAt hψ.convexOn_toReal
    hd.hasFDerivAt.hasFDerivWithinAt (interior_subset hx) hy
  have hg : fderiv ℝ (fun y => (ψ y).toReal) x (y - x) = inner ℝ p (y - x) := by
    rw [show p = (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ (fun y => (ψ y).toReal) x) from rfl,
      InnerProductSpace.toDual_symm_apply]
  rw [hg, inner_sub_right] at hsupp
  rw [← EReal.coe_toReal hy (hψ.1 y), ← EReal.coe_sub, EReal.coe_le_coe_iff,
    real_inner_comm p y, real_inner_comm p x]
  linarith

omit [MeasurableSpace E] [BorelSpace E] in
/-- **Agreement of the truncation**: at an interior differentiability point where
`‖∇ψ(x)‖ ≤ k`, the conjugate of the ball truncation of `ψ*` equals `ψ`. -/
theorem legendre_ballTruncate_eq_of_norm_gradient_le (hψ : ConvexPotential ψ) {x : E}
    (hx : x ∈ interior {y | ψ y ≠ ⊤}) (hd : DifferentiableAt ℝ (fun y => (ψ y).toReal) x)
    {k : ℝ} (hk : ‖gradient (fun y => (ψ y).toReal) x‖ ≤ k)
    (hle : ∀ y, legendre (ballTruncate (legendre ψ) k) y ≤ ψ y) :
    legendre (ballTruncate (legendre ψ) k) x = ψ x := by
  refine le_antisymm (hle x) ?_
  set p := gradient (fun y => (ψ y).toReal) x
  have h := legendre_gradient_le hψ hx hd
  have hge := le_iSup (fun q => (inner ℝ q x : EReal) - ballTruncate (legendre ψ) k q) p
  rw [ballTruncate_of_norm_le _ hk] at hge
  refine le_trans ?_ hge
  have hxr : ψ x = ((ψ x).toReal : EReal) :=
    (EReal.coe_toReal (interior_subset hx) (hψ.1 x)).symm
  calc ψ x = (((ψ x).toReal : ℝ) : EReal) := hxr
    _ = ((inner ℝ p x : ℝ) : EReal) - ((inner ℝ x p - (ψ x).toReal : ℝ) : EReal) := by
        rw [← EReal.coe_sub, real_inner_comm x p]; congr 1; ring
    _ ≤ (inner ℝ p x : EReal) - legendre ψ p := EReal.sub_le_sub le_rfl h

omit [MeasurableSpace E] [BorelSpace E] in
/-- **Agreement of gradients**: where the truncation agrees with `ψ` at an interior
differentiability point of both, the gradients agree. -/
theorem gradient_toReal_legendre_ballTruncate_eq {x : E}
    (hx : x ∈ interior {y | ψ y ≠ ⊤}) (hd : DifferentiableAt ℝ (fun y => (ψ y).toReal) x)
    {k : ℝ} (hle : ∀ y, legendre (ballTruncate (legendre ψ) k) y ≤ ψ y)
    (hbot : ∀ y, legendre (ballTruncate (legendre ψ) k) y ≠ ⊥)
    (heq : legendre (ballTruncate (legendre ψ) k) x = ψ x)
    (hdk : DifferentiableAt ℝ (fun y => (legendre (ballTruncate (legendre ψ) k) y).toReal) x) :
    gradient (fun y => (legendre (ballTruncate (legendre ψ) k) y).toReal) x =
      gradient (fun y => (ψ y).toReal) x := by
  set F := fun y => (legendre (ballTruncate (legendre ψ) k) y).toReal
  set Ψ := fun y => (ψ y).toReal
  have hmin : IsLocalMin (fun y => Ψ y - F y) x := by
    filter_upwards [isOpen_interior.mem_nhds hx] with y hy
    have hyt : ψ y ≠ ⊤ := interior_subset hy
    have h1 : F y ≤ Ψ y := EReal.toReal_le_toReal (hle y) (hbot y) hyt
    have h2 : F x = Ψ x := by simp only [F, Ψ, heq]
    linarith
  have hz := hmin.fderiv_eq_zero
  rw [show (fun y => Ψ y - F y) = Ψ - F from rfl, fderiv_sub hd hdk, sub_eq_zero] at hz
  simp only [gradient]
  rw [hz]

end RealTruncation

end FunctionalInequalities.Probability.MomentMeasure
