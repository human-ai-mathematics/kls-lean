import FunctionalInequalities.Analysis.Whitney.FirstOrderJet

/-!
# Boundary gluing for the compact first-order Whitney extension problem

This module starts the sufficiency direction of obligation compact Whitney extension. It proves the boundary step:
a candidate defined and differentiable off the compact set, with controlled value and derivative
errors relative to nearest-point affine jets, extends the prescribed jet as a globally C¹ map.

It does **not** construct that candidate. The quantitative covering, partition and affine-jet
estimates are supplied by `WhitneyCover`, `WhitneyBump`, `WhitneyPartition` and
`WhitneyConstruction`. The last module proves the full compact-set compact Whitney extension extension theorem;
this module provides its boundary step. `FirstOrderJet` supplies the necessity direction.
-/

noncomputable section

open Set Metric Filter Asymptotics
open scoped Topology ContDiff

namespace FunctionalInequalities.Analysis.WhitneyJet

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The affine polynomial prescribed by a first-order jet at `a`. -/
def affine (f : V → ℝ) (F : V → V →L[ℝ] ℝ) (a y : V) : ℝ :=
  f a + F a (y - a)

/-- Comparison of two affine jets, with the jet remainder based at `x`. -/
theorem norm_affine_sub_le (f : V → ℝ) (F : V → V →L[ℝ] ℝ) (a x y : V) :
    ‖affine f F a y - affine f F x y‖ ≤
      ‖f a - f x - F x (a - x)‖ + ‖F a - F x‖ * ‖y - a‖ := by
  have heq : affine f F a y - affine f F x y =
      (f a - f x - F x (a - x)) + (F a - F x) (y - a) := by
    simp only [affine, sub_apply, map_sub]
    ring
  rw [heq]
  exact (norm_add_le _ _).trans (add_le_add_right ((F a - F x).le_opNorm _) _)

omit [NormedSpace ℝ V] in
/-- A nearest point to `y` is at most twice as far from any `x ∈ S` as `y` is. -/
theorem dist_nearest_le {S : Set V} {x y a : V} (hx : x ∈ S)
    (ha : infDist y S = dist y a) : dist a x ≤ 2 * dist y x := by
  have hnear : dist y a ≤ dist y x := ha ▸ infDist_le_dist_of_mem hx
  calc
    dist a x ≤ dist a y + dist y x := dist_triangle _ _ _
    _ ≤ 2 * dist y x := by rw [dist_comm a y]; linarith

/-- The Whitney remainder already gives a derivative **within** the set. This does not identify
`fderivWithin` on a sparse set and does not assert any ambient extension. -/
theorem hasFDerivWithinAt {S : Set V} {f : V → ℝ} {F : V → V →L[ℝ] ℝ}
    (hR : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ x ∈ S, ∀ y ∈ S, ‖y - x‖ < δ →
        ‖f y - f x - F x (y - x)‖ ≤ ε * ‖y - x‖)
    {x : V} (hx : x ∈ S) : HasFDerivWithinAt f (F x) S x := by
  rw [hasFDerivWithinAt_iff_isLittleO]
  refine IsLittleO.of_bound fun ε hε => ?_
  obtain ⟨δ, hδ, hb⟩ := hR ε hε
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds x hδ)] with y hy hyd
  exact hb x hx y hy (by simpa [mem_ball, dist_eq_norm] using hyd)

/-- If a candidate agrees with the jet values on `S` and has uniformly small affine errors
off `S` relative to distance from `S`, it is differentiable at every point of `S` with the
prescribed derivative. No regularity of the candidate off `S` is needed for this boundary step. -/
theorem hasFDerivAt_of_nearby_affine {S : Set V} (hS : IsCompact S)
    {f v : V → ℝ} {F : V → V →L[ℝ] ℝ} (hF : ContinuousOn F S)
    (hR : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ x ∈ S, ∀ y ∈ S, ‖y - x‖ < δ →
        ‖f y - f x - F x (y - x)‖ ≤ ε * ‖y - x‖)
    (hv : EqOn v f S)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ y ∉ S, ∀ a ∈ S, infDist y S = dist y a → infDist y S < δ →
        ‖v y - affine f F a y‖ ≤ ε * infDist y S)
    {x : V} (hx : x ∈ S) : HasFDerivAt v (F x) x := by
  rw [hasFDerivAt_iff_isLittleO]
  refine IsLittleO.of_bound fun ε hε => ?_
  have he : 0 < ε / 4 := by positivity
  obtain ⟨δR, hδR, hrem⟩ := hR (ε / 4) he
  obtain ⟨δF, hδF, hder⟩ := Metric.continuousWithinAt_iff.1 (hF x hx) (ε / 4) he
  obtain ⟨δA, hδA, happ⟩ := happrox (ε / 4) he
  let δ := min (δR / 2) (min (δF / 2) δA)
  have hδ : 0 < δ := lt_min (by positivity) (lt_min (by positivity) hδA)
  filter_upwards [Metric.ball_mem_nhds x hδ] with y hy
  have hyδ : dist y x < δ := hy
  have hyR : dist y x < δR / 2 := hyδ.trans_le (min_le_left _ _)
  have hyF : dist y x < δF / 2 :=
    hyδ.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hyA : dist y x < δA :=
    hyδ.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  rw [hv hx]
  by_cases hys : y ∈ S
  · rw [hv hys]
    exact (hrem x hx y hys (by rw [← dist_eq_norm]; linarith)).trans
      (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
  · obtain ⟨a, haS, ha⟩ := hS.exists_infDist_eq_dist ⟨x, hx⟩ y
    have hnear : infDist y S ≤ dist y x := infDist_le_dist_of_mem hx
    have hax := dist_nearest_le hx ha
    have haR : ‖a - x‖ < δR := by rw [← dist_eq_norm]; linarith
    have haF : ‖F a - F x‖ ≤ ε / 4 := by
      have := hder haS (show dist a x < δF by linarith)
      exact (by simpa only [dist_eq_norm] using this.le)
    have hrem' := hrem x hx a haS haR
    have happ' := happ y hys a haS ha (hnear.trans_lt hyA)
    have hcomp := norm_affine_sub_le f F a x y
    have hsum := norm_sub_le_norm_sub_add_norm_sub (v y) (affine f F a y) (affine f F x y)
    have heq : v y - f x - F x (y - x) = v y - affine f F x y := by
      simp only [affine]; ring
    rw [heq]
    have hcomp' : ‖affine f F a y - affine f F x y‖ ≤
        ε / 4 * ‖a - x‖ + ε / 4 * ‖y - a‖ :=
      hcomp.trans (add_le_add hrem' (mul_le_mul_of_nonneg_right haF (norm_nonneg _)))
    simp only [← dist_eq_norm] at hcomp' hsum happ' ⊢
    have h1 : ε / 4 * infDist y S ≤ ε / 4 * dist y x :=
      mul_le_mul_of_nonneg_left hnear he.le
    have h2 : ε / 4 * dist a x ≤ ε / 4 * (2 * dist y x) :=
      mul_le_mul_of_nonneg_left hax he.le
    have h3 : ε / 4 * dist y a ≤ ε / 4 * dist y x := by
      rw [← ha]; exact h1
    linarith

/-- Uniform convergence to the prescribed derivative at nearest points gives continuity at
the compact set. This assertion does not require the field to be a derivative off the set. -/
theorem continuousAt_of_nearby_field {S : Set V} (hS : IsCompact S)
    {F D : V → V →L[ℝ] ℝ} (hF : ContinuousOn F S) (hD : EqOn D F S)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ y ∉ S, ∀ a ∈ S, infDist y S = dist y a → infDist y S < δ →
        ‖D y - F a‖ ≤ ε)
    {x : V} (hx : x ∈ S) : ContinuousAt D x := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  have he : 0 < ε / 3 := by positivity
  obtain ⟨δF, hδF, hder⟩ := Metric.continuousWithinAt_iff.1 (hF x hx) (ε / 3) he
  obtain ⟨δA, hδA, happ⟩ := happrox (ε / 3) he
  refine ⟨min (δF / 2) δA, lt_min (by positivity) hδA, fun y hy => ?_⟩
  have hyF : dist y x < δF / 2 := hy.trans_le (min_le_left _ _)
  have hyA : dist y x < δA := hy.trans_le (min_le_right _ _)
  rw [hD hx]
  by_cases hys : y ∈ S
  · rw [hD hys]
    exact (hder hys (by linarith)).trans (by linarith)
  · obtain ⟨a, haS, ha⟩ := hS.exists_infDist_eq_dist ⟨x, hx⟩ y
    have hax := dist_nearest_le hx ha
    have hnear : infDist y S ≤ dist y x := infDist_le_dist_of_mem hx
    have h1 := happ y hys a haS ha (hnear.trans_lt hyA)
    have h2 := hder haS (show dist a x < δF by linarith)
    rw [← dist_eq_norm] at h1
    have := dist_triangle (D y) (F a) (F x)
    linarith

/-- The boundary gluing criterion for compact Whitney extension. The hypotheses concern a candidate and a continuous
derivative field on the **complement** of the compact set, together with two quantitative
nearest-jet estimates. The conclusion includes the ambient derivative on `S`, even when `S`
has empty interior. `WhitneyConstruction` constructs such candidates in finite dimension. -/
theorem contDiff_of_nearby_jet {S : Set V} (hS : IsCompact S)
    {f v : V → ℝ} {F D : V → V →L[ℝ] ℝ} (hF : ContinuousOn F S)
    (hR : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ x ∈ S, ∀ y ∈ S, ‖y - x‖ < δ →
        ‖f y - f x - F x (y - x)‖ ≤ ε * ‖y - x‖)
    (hv : EqOn v f S) (hD : EqOn D F S)
    (hdiff : ∀ x ∉ S, HasFDerivAt v (D x) x) (hDc : ContinuousOn D Sᶜ)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ y ∉ S, ∀ a ∈ S, infDist y S = dist y a → infDist y S < δ →
        ‖v y - affine f F a y‖ ≤ ε * infDist y S ∧ ‖D y - F a‖ ≤ ε) :
    ContDiff ℝ 1 v ∧ ∀ x ∈ S, fderiv ℝ v x = F x := by
  have hvalue : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ y ∉ S, ∀ a ∈ S, infDist y S = dist y a → infDist y S < δ →
        ‖v y - affine f F a y‖ ≤ ε * infDist y S := by
    intro ε hε
    obtain ⟨δ, hδ, h⟩ := happrox ε hε
    exact ⟨δ, hδ, fun y hy a ha hn hd => (h y hy a ha hn hd).1⟩
  have hfield : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ y ∉ S, ∀ a ∈ S, infDist y S = dist y a → infDist y S < δ →
        ‖D y - F a‖ ≤ ε := by
    intro ε hε
    obtain ⟨δ, hδ, h⟩ := happrox ε hε
    exact ⟨δ, hδ, fun y hy a ha hn hd => (h y hy a ha hn hd).2⟩
  have hboundary : ∀ x ∈ S, HasFDerivAt v (F x) x :=
    fun _ hx => hasFDerivAt_of_nearby_affine hS hF hR hv hvalue hx
  refine ⟨contDiff_one_iff_hasFDerivAt.2 ⟨D, ?_, ?_⟩, fun x hx => (hboundary x hx).fderiv⟩
  · rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : x ∈ S
    · exact continuousAt_of_nearby_field hS hF hD hfield hx
    · exact (hDc x hx).continuousAt (hS.isClosed.isOpen_compl.mem_nhds hx)
  · intro x
    by_cases hx : x ∈ S
    · rw [hD hx]; exact hboundary x hx
    · exact hdiff x hx

/-- Reduction of compact Whitney extension to a controlled C¹ function on the complement. The input `w` need not
agree with `f`, be continuous, or have the prescribed derivative on `S`. The extension is
constructed by replacing its values on `S` with `f`; boundary gluing proves it is globally C¹.
Existence of such a controlled `w` is proved separately in `WhitneyConstruction`; it is an
explicit hypothesis of this boundary-gluing theorem. -/
theorem exists_contDiff_of_compl_approx {S : Set V} (hS : IsCompact S)
    {f w : V → ℝ} {F : V → V →L[ℝ] ℝ} (hF : ContinuousOn F S)
    (hR : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ x ∈ S, ∀ y ∈ S, ‖y - x‖ < δ →
        ‖f y - f x - F x (y - x)‖ ≤ ε * ‖y - x‖)
    (hw : ContDiffOn ℝ 1 w Sᶜ)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ y ∉ S, ∀ a ∈ S, infDist y S = dist y a → infDist y S < δ →
        ‖w y - affine f F a y‖ ≤ ε * infDist y S ∧ ‖fderiv ℝ w y - F a‖ ≤ ε) :
    ∃ v : V → ℝ, ContDiff ℝ 1 v ∧ EqOn v f S ∧
      ∀ x ∈ S, fderiv ℝ v x = F x := by
  classical
  let v := S.piecewise f w
  let D := S.piecewise F (fderiv ℝ w)
  have hv : EqOn v f S := fun x hx => piecewise_eq_of_mem S f w hx
  have hD : EqOn D F S := fun x hx => piecewise_eq_of_mem S F (fderiv ℝ w) hx
  have hvout : ∀ x ∉ S, v =ᶠ[𝓝 x] w := by
    intro x hx
    filter_upwards [hS.isClosed.isOpen_compl.mem_nhds hx] with y hy
    exact piecewise_eq_of_notMem S f w hy
  have hdiff : ∀ x ∉ S, HasFDerivAt v (D x) x := by
    intro x hx
    dsimp [D]
    rw [piecewise_eq_of_notMem S F (fderiv ℝ w) hx]
    exact ((hw.differentiableOn one_ne_zero x hx).differentiableAt
      (hS.isClosed.isOpen_compl.mem_nhds hx)).hasFDerivAt.congr_of_eventuallyEq (hvout x hx)
  have hDc : ContinuousOn D Sᶜ :=
    (hw.continuousOn_fderiv_of_isOpen hS.isClosed.isOpen_compl le_rfl).congr
      (fun x hx => piecewise_eq_of_notMem S F (fderiv ℝ w) hx)
  have happ : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ y ∉ S, ∀ a ∈ S, infDist y S = dist y a → infDist y S < δ →
        ‖v y - affine f F a y‖ ≤ ε * infDist y S ∧ ‖D y - F a‖ ≤ ε := by
    intro ε hε
    obtain ⟨δ, hδ, h⟩ := happrox ε hε
    refine ⟨δ, hδ, fun y hy a ha hn hd => ?_⟩
    simpa only [v, D, piecewise_eq_of_notMem S f w hy,
      piecewise_eq_of_notMem S F (fderiv ℝ w) hy] using h y hy a ha hn hd
  have h := contDiff_of_nearby_jet hS hF hR hv hD hdiff hDc happ
  exact ⟨v, h.1, hv, h.2⟩

end FunctionalInequalities.Analysis.WhitneyJet
