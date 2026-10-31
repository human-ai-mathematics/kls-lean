module

public import FunctionalInequalities.Analysis.Convex.Quadratic
public import FunctionalInequalities.Analysis.Convex.Dirichlet.Solution
public import FunctionalInequalities.Analysis.Convex.Dirichlet.Regularization
public import FunctionalInequalities.Analysis.Convex.Pogorelov
public import FunctionalInequalities.Analysis.BakryEmery.LinearizedEquation
public import FunctionalInequalities.Analysis.Convex.Viscosity.Equation
public import FunctionalInequalities.Analysis.Convex.Viscosity.Mollification
public import FunctionalInequalities.Analysis.Convex.Viscosity.Pointwise
public import FunctionalInequalities.Analysis.Convex.Viscosity.Touching
public import FunctionalInequalities.Analysis.Convex.Dirichlet.Envelope
public import Mathlib.Analysis.Calculus.Deriv.Abs

noncomputable section
open Set Metric MeasureTheory
open scoped RealInnerProductSpace ENNReal Topology
namespace LetwinDirichletEnvelopeAudit
open FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis.Dirichlet

/-- An actual positive-dimensional unit-ball source, with no subsolution family
or supremum fields supplied by the client. -/
theorem actual_unitBall_envelope {n : ℕ} (hn : 0 < n) :
    ∃ U : EuclideanSpace ℝ (Fin n) → ℝ,
      ConvexOn ℝ (closedBall 0 1) U ∧
        ContinuousOn U (ball 0 1) ∧
          (∀ x ∈ closedBall 0 1, U x ≤ 0) ∧
            (∀ w ∈ subsolutions (ball (0 : EuclideanSpace ℝ (Fin n)) 1),
              ∀ x ∈ closedBall 0 1, w x ≤ U x) := by
  let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  obtain ⟨_hne, U, _hSup, hconv, hcont, hcap, hle⟩ :=
    exists_finite_convex_envelope hn (Ω := ball (0 : EuclideanSpace ℝ (Fin n)) 1) isOpen_ball
      (convex_ball _ _) isBounded_ball
  rw [closure_ball _ (by norm_num : (1 : ℝ) ≠ 0)] at hconv hcap hle
  exact ⟨U, hconv, hcont, hcap, hle⟩

/-- Dimension zero still has actual quadratic subsolutions. A finite envelope
is deliberately not claimed there: its frontier upper-bound argument requires
positive dimension. -/
theorem actual_fin0_subsolutions :
    (subsolutions (univ : Set (EuclideanSpace ℝ (Fin 0)))).Nonempty := by
  obtain ⟨R, _hR, hq⟩ :=
    exists_quadratic_subsolution (Ω := (univ : Set (EuclideanSpace ℝ (Fin 0)))) isOpen_univ
      convex_univ isCompact_univ.isBounded
  exact ⟨quadraticAt 1 0 0 (-R ^ 2 / 2), hq⟩


/-- The shared supremum tool genuinely works in a vector space without
finite-dimensional, normed, topological or measure instances. -/
theorem pure_vector_supremum {E : Type*} [AddCommMonoid E] [Module ℝ E] {D : Set E}
    (hD : Convex ℝ D) (c : ℝ) :
    ConvexOn ℝ D (fun _x => sSup ((fun _i : Unit => c) '' (univ : Set Unit))) := by
  exact
    convexOn_sSup_image_of_bddAbove hD ⟨(), mem_univ _⟩ (fun _ _ => c)
      (fun _ _ => convexOn_const c hD) (by intro x _hx; exact ⟨c, by simp⟩)

/-- A source excluded by any local-C1-at-vertex premise is admitted by the
actual nondifferentiable DOMAIN/global support-image bridge. -/
theorem actual_nondifferentiable_bridge :
    (¬DifferentiableAt ℝ (fun x : ℝ => |x|) 0) ∧
      subgradientImageOn (fun x : ℝ => |x|) (Ioo (-1) 1) {0} =
        subgradientImage (fun x : ℝ => |x|) {0} := by
  refine ⟨not_differentiableAt_abs_zero, ?_⟩
  have hc : ConvexOn ℝ univ (fun x : ℝ => |x|) := by
    have heq : (norm : ℝ → ℝ) = (fun x : ℝ => |x|) := funext Real.norm_eq_abs
    rw [← heq]
    exact convexOn_norm convex_univ
  exact subgradientImageOn_eq_subgradientImage_of_isOpen hc isOpen_Ioo (by simp)

/-- An actual unit interval source invokes the full generated envelope, with
true frontier values and closure continuity rather than assumed limit fields. -/
theorem actual_interval_envelope :
    ∃ U : EuclideanSpace ℝ (Fin 1) → ℝ,
      ConvexOn ℝ (closure (ball 0 1)) U ∧
        ContinuousOn U (closure (ball 0 1)) ∧ ∀ z ∈ frontier (ball 0 1), U z = 0 := by
  obtain ⟨_, U, _, hcv, hct, hzero, _⟩ :=
    exists_continuous_envelope (by norm_num : 0 < 1) isOpen_ball (convex_ball _ _)
      isBounded_ball
  exact ⟨U, hcv, hct, hzero⟩

private def actualHalfBall : Set (EuclideanSpace ℝ (Fin 2)) :=
  ball 0 1 ∩ {x | x 0<0}

private theorem halfball_geometry :
    IsOpen actualHalfBall ∧
      Convex ℝ actualHalfBall ∧
        Bornology.IsBounded actualHalfBall ∧
          (0 : EuclideanSpace ℝ (Fin 2)) ∈ frontier actualHalfBall := by
  have ho : IsOpen actualHalfBall :=
    isOpen_ball.inter
      (isOpen_lt (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).continuous continuous_const)
  have hc : Convex ℝ actualHalfBall :=
    (convex_ball _ _).inter
      ((convex_Iio (0 : ℝ)).linear_preimage
        (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).toLinearMap)
  refine ⟨ho, hc, isBounded_ball.subset inter_subset_left, ?_, ?_⟩
  · apply Metric.mem_closure_iff.mpr
    intro ε hε
    let t : ℝ := min (ε / 2) (1 / 2)
    have ht : 0 < t := lt_min (by linarith) (by norm_num)
    have htε : t < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have ht1 : t < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
    let y : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 0 (-t)
    have hny : ‖y‖ = t := by simp [y, Real.norm_eq_abs, abs_of_pos ht]
    refine ⟨y, ⟨?_, ?_⟩, ?_⟩
    · simpa only [mem_ball, dist_zero_right, hny] using ht1
    · change y 0 < 0
      simpa [y] using neg_neg_of_pos ht
    · simpa only [dist_zero_left, hny] using htε
  · simpa only [ho.interior_eq] using
      (show (0 : EuclideanSpace ℝ (Fin 2)) ∉ actualHalfBall by simp [actualHalfBall])

/-- A genuine half-ball domain with its planar boundary point at zero:
barriers, frontier equality and closure continuity are all source-derived. -/
theorem actual_halfball_envelope :
    ∃ U : EuclideanSpace ℝ (Fin 2) → ℝ,
      ConvexOn ℝ (closure actualHalfBall) U ∧
        ContinuousOn U (closure actualHalfBall) ∧
          (∀ z ∈ frontier actualHalfBall, U z = 0) ∧ U 0 = 0 := by
  obtain ⟨ho, hc, hb, hzero⟩ := halfball_geometry
  obtain ⟨_, U, _, hcv, hct, hfr, _⟩ :=
    exists_continuous_envelope (by norm_num : 0 < 2) ho hc hb
  exact ⟨U, hcv, hct, hfr, hfr 0 hzero⟩


/-- Real quadratic MA data shared by the tilted unit and scalar-two models. -/
private theorem actual_quadratic_lower_ma {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (hΩ : IsOpen Ω) {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef) (hd : 1 ≤ A.det)
    (b : EuclideanSpace ℝ (Fin n)) (k : ℝ) :
    ∀ G, IsOpen G → G ⊆ Ω → volume G ≤ volume (subgradientImageOn (quadraticAt A 0 b k) Ω G) := by
  intro G _hG hGΩ
  rw [volume_subgradientImageOn_quadraticAt hA _ _ _ hΩ hGΩ]
  have he : (1 : ENNReal) ≤ ENNReal.ofReal A.det := by
    rw [← ENNReal.ofReal_one];
    exact ENNReal.ofReal_le_ofReal hd
  calc
    volume G = 1 * volume G := by rw [one_mul]
    _ ≤ ENNReal.ofReal A.det * volume G := by gcongr

private def actualQ (s : ℝ) : EuclideanSpace ℝ (Fin 1)→ℝ :=
  quadraticAt 1 0 (s • EuclideanSpace.single 0 1) (-2)

private theorem actual_qformula (s : ℝ) (x : EuclideanSpace ℝ (Fin 1)) :
    actualQ s x = -2 + ⟪s • EuclideanSpace.single 0 1, x⟫ + (1 / 2 : ℝ) * ‖x‖ ^ 2 := by
  simp [actualQ, quadraticAt, Matrix.toEuclideanLin]

private theorem actual_qclass (s : ℝ) (hs : |s| ≤ 1) :
    actualQ s ∈ Dirichlet.subsolutions (ball (0 : EuclideanSpace ℝ (Fin 1)) 1) := by
  let D : Set (EuclideanSpace ℝ (Fin 1)) := ball 0 1
  have hcv : ConvexOn ℝ univ (actualQ s) := convexOn_quadraticAt Matrix.PosSemidef.one _ _ _
  have hct : Continuous (actualQ s) := by
    rw [show
        actualQ s = (fun x => -2 + ⟪s • EuclideanSpace.single 0 1, x⟫ + (1 / 2 : ℝ) * ‖x‖ ^ 2)
        from funext (actual_qformula s)]
    fun_prop
  refine ⟨hcv.subset (subset_univ _) (convex_ball _ _).closure, hct.continuousOn, ?_, ?_⟩
  · intro z hz
    have hzb : z ∈ closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1 := by
      simpa only [closure_ball _ (by norm_num : (1 : ℝ) ≠ 0)] using frontier_subset_closure hz
    have hzn : ‖z‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using hzb
    have hb : ‖s • (EuclideanSpace.single 0 1 : EuclideanSpace ℝ (Fin 1))‖ ≤ 1 := by
      simpa [norm_smul, Real.norm_eq_abs] using hs
    have hi :=
      abs_real_inner_le_norm (s • (EuclideanSpace.single 0 1 : EuclideanSpace ℝ (Fin 1))) z
    have hprod : ‖s • (EuclideanSpace.single 0 1 : EuclideanSpace ℝ (Fin 1))‖ * ‖z‖ ≤ 1 := by
      nlinarith [norm_nonneg z,
        norm_nonneg (s • (EuclideanSpace.single 0 1 : EuclideanSpace ℝ (Fin 1)))]
    have hi' :=
      (le_abs_self ⟪s • (EuclideanSpace.single 0 1 : EuclideanSpace ℝ (Fin 1)), z⟫).trans
        (hi.trans hprod)
    rw [actual_qformula]
    nlinarith [norm_nonneg z]
  · exact
      actual_quadratic_lower_ma isOpen_ball Matrix.PosDef.one (by simp)
        (s • EuclideanSpace.single 0 1) (-2)

/-- Genuine crossing quadratic subsolutions: BOTH max-contact regions have
actual interior points; class membership/MA are constructed from real data. -/
theorem actual_crossing_max :
    (actualQ 1) ∈ Dirichlet.subsolutions (ball (0 : EuclideanSpace ℝ (Fin 1)) 1) ∧
      (actualQ (-1)) ∈ Dirichlet.subsolutions (ball (0 : EuclideanSpace ℝ (Fin 1)) 1) ∧
        (fun x => max (actualQ 1 x) (actualQ (-1) x)) ∈
            Dirichlet.subsolutions (ball (0 : EuclideanSpace ℝ (Fin 1)) 1) ∧
          (∃ x ∈ ball (0 : EuclideanSpace ℝ (Fin 1)) 1, actualQ 1 x < actualQ (-1) x) ∧
            (∃ y ∈ ball (0 : EuclideanSpace ℝ (Fin 1)) 1, actualQ (-1) y < actualQ 1 y) := by
  have hu := actual_qclass 1 (by norm_num)
  have hv := actual_qclass (-1) (by norm_num)
  refine ⟨hu, hv, max_mem_subsolutions isOpen_ball (convex_ball _ _) hu hv, ?_, ?_⟩
  · refine ⟨EuclideanSpace.single 0 (-1 / 2), ?_, ?_⟩
    · norm_num [mem_ball, Real.norm_eq_abs]
    · rw [actual_qformula, actual_qformula]
      simp only [one_smul, neg_smul, inner_neg_left, EuclideanSpace.inner_single_left]
      norm_num
  · refine ⟨EuclideanSpace.single 0 (1 / 2), ?_, ?_⟩
    · norm_num [mem_ball, Real.norm_eq_abs]
    · rw [actual_qformula, actual_qformula]
      simp only [one_smul, neg_smul, inner_neg_left, EuclideanSpace.inner_single_left]
      norm_num

/-- True zero-dimensional carrier: constants have actual image=G and mass
ONE on the whole space; max closure is used without a fictitious empty carrier. -/
theorem actual_fin0_max :
    (fun _ : EuclideanSpace ℝ (Fin 0) => max (0 : ℝ) 1) ∈
        Dirichlet.subsolutions (univ : Set (EuclideanSpace ℝ (Fin 0))) ∧
      volume
          (subgradientImageOn (fun _ : EuclideanSpace ℝ (Fin 0) => max (0 : ℝ) 1) univ univ) =
        1 := by
  have himage (c : ℝ) (G : Set (EuclideanSpace ℝ (Fin 0))) :
    subgradientImageOn (fun _ => c) univ G = G := by
    ext p
    constructor
    · rintro ⟨x, hx, _⟩
      exact (Subsingleton.elim x p) ▸ hx
    · intro hp
      refine ⟨p, hp, ?_⟩
      intro y _
      simp only [show y - p = 0 from sub_eq_zero.mpr (Subsingleton.elim _ _), inner_zero_right,
        add_zero, le_refl]
  have hclass (c : ℝ) : (fun _ : EuclideanSpace ℝ (Fin 0) => c) ∈ Dirichlet.subsolutions univ := by
    refine ⟨convexOn_const c convex_univ.closure, continuous_const.continuousOn, by simp, ?_⟩
    intro G _ _
    rw [himage]
  refine ⟨max_mem_subsolutions isOpen_univ convex_univ (hclass 0) (hclass 1), ?_⟩
  rw [himage, volume_euclideanSpace_eq_dirac]
  simp


section UniformApproximationClients
open Filter

/-- Actual positive-dimensional unit-ball data GENERATE the class sequence,
its increasing property and its uniform limit, rather than supplying them. -/
theorem actual_unit_ball {n : ℕ} (hn : 0 < n) :
    ∃ (U : EuclideanSpace ℝ (Fin n) → ℝ) (f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ),
      U ∈ subsolutions (ball 0 1) ∧
        (∀ z ∈ frontier (ball 0 1), U z = 0) ∧
          (∀ j, f j ∈ subsolutions (ball 0 1)) ∧
            (∀ x, Monotone (fun j => f j x)) ∧
              TendstoUniformlyOn f U atTop (closure (ball 0 1)) := by
  obtain ⟨U, f, _, hU, hzero, _, hf, _, hmono, hunif⟩ :=
    exists_uniform_class_approximation hn (Ω := ball (0 : EuclideanSpace ℝ (Fin n)) 1)
      isOpen_ball (convex_ball _ _) isBounded_ball
  exact ⟨U, f, hU, hzero, hf, hmono, hunif⟩

/-- Empty compact closure still yields a genuine nonempty finite family by
inserting the source-generated baseline member, with no cover input. -/
theorem actual_empty_domain :
    ∃ (U : EuclideanSpace ℝ (Fin 1) → ℝ) (f : ℕ → EuclideanSpace ℝ (Fin 1) → ℝ),
      U ∈ subsolutions ∅ ∧
        (∀ j, f j ∈ subsolutions ∅) ∧
          (∀ x, Monotone (fun j => f j x)) ∧ TendstoUniformlyOn f U atTop ∅ := by
  obtain ⟨U, f, _, hU, _, _, hf, _, hmono, hunif⟩ :=
    exists_uniform_class_approximation (by norm_num : 0 < 1) (Ω := ∅) isOpen_empty convex_empty
      isCompact_empty.isBounded
  exact ⟨U, f, hU, hf, hmono, by simpa only [closure_empty] using hunif⟩

end UniformApproximationClients

section PiecewiseMaximumClients
open Classical

/-- An actual nonsmooth source and positive quadratic are glued locally.
At 4 the result is STRICTLY BELOW the global maximum with q. -/
theorem actual_absolute_quadratic_patch :
    let Ω : Set ℝ := Ioo (-5) 5
    let q : ℝ → ℝ := fun x => x ^ 2 / 4 + 1 / 4
    let w : ℝ → ℝ := fun y => if y ∈ ball 0 1 then max |y| (q y) else |y|
    ConvexOn ℝ (closure Ω) w ∧
      ContinuousOn w (closure Ω) ∧
        w 0 = 1 / 4 ∧ w 4 < q 4 ∧ (∀ y ∈ closure Ω, w 0 + ⟪(0 : ℝ), y - 0⟫ ≤ w y) := by
  dsimp only
  let Ω : Set ℝ := Ioo (-5) 5
  let q : ℝ → ℝ := fun x => x ^ 2 / 4 + 1 / 4
  let w : ℝ → ℝ := fun y => if y ∈ ball 0 1 then max |y| (q y) else |y|
  have hΩ : IsOpen Ω := isOpen_Ioo
  have hu : ConvexOn ℝ univ (fun y : ℝ => |y|) := by
    refine ⟨convex_univ, ?_⟩
    intro x _hx y _hy a b ha hb _hab
    have he := abs_add_le (a * x) (b * y)
    rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb] at he
    exact he
  have hsq : ConvexOn ℝ univ (fun y : ℝ => y ^ 2) := (show Even 2 by decide).convexOn_pow
  have hq : ConvexOn ℝ univ q := by
    refine ⟨convex_univ, ?_⟩
    intro x hx y hy a b ha hb hab
    have he := hsq.2 hx hy ha hb hab
    change (a * x + b * y) ^ 2 ≤ a * x ^ 2 + b * y ^ 2 at he
    change (a * x + b * y) ^ 2 / 4 + 1 / 4 ≤ a * (x ^ 2 / 4 + 1 / 4) + b * (y ^ 2 / 4 + 1 / 4)
    nlinarith only [he, hab]
  have hb : closedBall (0 : ℝ) 1 ⊆ Ω := by
    intro z hz
    have ha : |z| ≤ 1 := by simpa [Real.dist_eq] using hz
    have hl := neg_le_abs z
    have hr := le_abs_self z
    constructor <;> linarith
  have hbd : ∀ z ∈ sphere (0 : ℝ) 1, q z ≤ |z| := by
    intro z hz
    have ha : |z| = 1 := by simpa [Real.dist_eq] using hz
    have hs : z ^ 2 = 1 := by nlinarith [sq_abs z]
    dsimp [q]; rw [hs, ha]; norm_num
  have huc : Continuous (fun y : ℝ => |y|) := continuous_abs
  have hqc : Continuous q := by dsimp [q]; fun_prop
  have hconv :=
    convexOn_closure_piecewise_max_ball hΩ
      (hu.subset (subset_univ _) (convex_Ioo (-5 : ℝ) 5).closure)
      (hq.subset (subset_univ _) (convex_Ioo (-5 : ℝ) 5)) hqc.continuousOn hb hbd
  have hcont :=
    continuousOn_piecewise_max_ball (Ω := Ω) (by norm_num : (0 : ℝ) < 1) huc.continuousOn
      hqc.continuousOn hbd
  refine ⟨hconv, hcont, ?_, ?_, ?_⟩
  · norm_num [Metric.mem_ball, Real.dist_eq]
  · norm_num [Metric.mem_ball, Real.dist_eq]
  · intro y hy
    have hsup : ∀ t ∈ closedBall (0 : ℝ) 1, q 0 + ⟪(0 : ℝ), t - 0⟫ ≤ q t := by
      intro t _ht
      simp only [inner_zero_left, add_zero]
      dsimp [q]
      nlinarith [sq_nonneg t]
    have hm :=
      subgradient_le_piecewise_max_ball
        (hu.subset (subset_univ _) (convex_Ioo (-5 : ℝ) 5).closure)
        (fun t ht => subset_closure (hb ht)) hbd
        (by norm_num [Metric.mem_ball] : (0 : ℝ) ∈ ball 0 1) (by norm_num [q] : |(0 : ℝ)| ≤ q 0)
        hsup y hy
    convert hm using 1; norm_num [q, Metric.mem_ball]

/-- The zero-dimensional carrier is genuine; the same convex/C0 gluing
works without a nontriviality assumption. -/
theorem actual_zero_dimensional_patch :
    let E := EuclideanSpace ℝ (Fin 0)
    let w : E → ℝ := fun y => if y ∈ ball 0 1 then max 0 (1 / 4 : ℝ) else 0
    ConvexOn ℝ univ w ∧ Continuous w ∧ w 0 = 1 / 4 := by
  let E := EuclideanSpace ℝ (Fin 0)
  have hb : closedBall (0 : E) 1 ⊆ (univ : Set E) := subset_univ _
  have hbd : ∀ z ∈ sphere (0 : E) 1, (1 / 4 : ℝ) ≤ 0 := by
    intro z hz
    have he : z = 0 := Subsingleton.elim _ _
    simp [he] at hz
  have hconv :=
    convexOn_closure_piecewise_max_ball isOpen_univ
      (by simpa using (convexOn_const (0 : ℝ) (convex_univ : Convex ℝ (univ : Set E))))
      (convexOn_const (1 / 4 : ℝ) convex_univ) continuousOn_const hb hbd
  have hcont :=
    continuousOn_piecewise_max_ball (Ω := (univ : Set E)) (by norm_num : (0 : ℝ) < 1)
      (continuousOn_const : ContinuousOn (fun _ : E => (0 : ℝ)) (closure univ))
      (continuousOn_const : ContinuousOn (fun _ : E => (1 / 4 : ℝ)) (closure univ)) hbd
  refine ⟨by simpa only [closure_univ] using hconv, ?_, ?_⟩
  · exact continuousOn_univ.mp (by simpa only [closure_univ] using hcont)
  · norm_num [Metric.mem_ball]

end PiecewiseMaximumClients

section LocalRaisingClients
open Classical

/-- Explicit genuinely raising quadratic data, all finite dimensions including0. -/
theorem actual_quadratic_local_raise (n : ℕ) :
    let Ω : Set (EuclideanSpace ℝ (Fin n)) := ball 0 2
    let u := quadraticAt ((2 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)) 0 0 (-4)
    let q := quadraticAt (1 : Matrix (Fin n) (Fin n) ℝ) 0 0 (-15 / 4)
    let w := fun y => if y ∈ ball 0 1 then max (u y) (q y) else u y
    u ∈ subsolutions Ω ∧
      w ∈ subsolutions Ω ∧ u 0 < w 0 ∧ w 0 = -15 / 4 ∧ (∀ y ∉ ball 0 1, w y = u y) := by
  let E := EuclideanSpace ℝ (Fin n)
  let Ω : Set E := ball 0 2
  let A : Matrix (Fin n) (Fin n) ℝ := (2 : ℝ) • 1
  let u := quadraticAt A 0 0 (-4)
  let q := quadraticAt (1 : Matrix (Fin n) (Fin n) ℝ) 0 0 (-15 / 4)
  let w := fun y => if y ∈ ball 0 1 then max (u y) (q y) else u y
  have hA : A.PosDef := Matrix.PosDef.one.smul (by norm_num : (0 : ℝ) < 2)
  have huf (x : E) : u x = -4 + ‖x‖ ^ 2 := by
    simp [u, A, quadraticAt, Matrix.toEuclideanLin, inner_smul_right]
  have hqf (x : E) : q x = -15 / 4 + (1 / 2 : ℝ) * ‖x‖ ^ 2 := by
    simp [q, quadraticAt, Matrix.toEuclideanLin]
  have huc : Continuous u := by rw [show u = (fun x => -4 + ‖x‖ ^ 2) from funext huf]; fun_prop
  have hqc : Continuous q := by
    rw [show q = (fun x => -15 / 4 + (1 / 2 : ℝ) * ‖x‖ ^ 2) from funext hqf]; fun_prop
  have hΩ : IsOpen Ω := isOpen_ball
  have hcΩ : Convex ℝ Ω := convex_ball 0 2
  have hucv : ConvexOn ℝ univ u := convexOn_quadraticAt hA.posSemidef _ _ _
  have hqcv : ConvexOn ℝ univ q := convexOn_quadraticAt Matrix.PosSemidef.one _ _ _
  have hqMA : ∀ G, IsOpen G → G ⊆ Ω → volume G ≤ volume (subgradientImageOn q Ω G) :=
    actual_quadratic_lower_ma hΩ Matrix.PosDef.one (by simp) 0 (-15 / 4)
  have hu : u ∈ subsolutions Ω := by
    refine ⟨hucv.subset (subset_univ _) hcΩ.closure, huc.continuousOn, ?_, ?_⟩
    · intro z hz
      have hz' : ‖z‖ = 2 := by
        simpa [Ω, frontier_ball (0 : E) (by norm_num : (2 : ℝ) ≠ 0)] using hz
      rw [huf, hz']; norm_num
    · have hd : A.det = (2 : ℝ) ^ n := by simp [A]
      have hdet : 1 ≤ A.det := by rw [hd]; exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
      exact actual_quadratic_lower_ma hΩ hA hdet 0 (-4)
  have hb : closedBall (0 : E) 1 ⊆ Ω := by
    intro z hz
    have hzn : ‖z‖ ≤ 1 := by simpa using hz
    have : ‖z‖ < 2 := by linarith
    simpa [Ω] using this
  have hbd : ∀ z ∈ sphere (0 : E) 1, q z ≤ u z := by
    intro z hz
    have hn : ‖z‖ = 1 := by simpa using hz
    rw [huf, hqf, hn]; norm_num
  have hw :=
    piecewise_max_ball_mem_subsolutions hΩ hcΩ hu (hqcv.subset (subset_univ _) hcΩ)
      hqc.continuousOn hqMA (by norm_num : (0 : ℝ) < 1) hb hbd
  refine ⟨hu, hw, ?_, ?_, ?_⟩
  · norm_num [u, q, quadraticAt, Metric.mem_ball]
  · norm_num [u, q, quadraticAt, Metric.mem_ball]
  · intro y hy
    exact ite_eq_right hy

/-- An actual unit-ball source generates the SAME envelope/local comparison,
retaining its real class sequence and approximation fields. -/
theorem actual_unit_ball_local_comparison {n : ℕ} (hn : 0 < n) :
    ∃ U : EuclideanSpace ℝ (Fin n) → ℝ,
      U ∈ subsolutions (ball 0 1) ∧
        (∀ z ∈ frontier (ball 0 1), U z = 0) ∧
          (∀ (q : EuclideanSpace ℝ (Fin n) → ℝ),
            ConvexOn ℝ (ball 0 1) q →
              ContinuousOn q (closure (ball 0 1)) →
                (∀ G,
                    IsOpen G →
                      G ⊆ ball 0 1 → volume G ≤ volume (subgradientImageOn q (ball 0 1) G)) →
                  ∀ (c : EuclideanSpace ℝ (Fin n)) (r : ℝ),
                    0 < r →
                      closedBall c r ⊆ ball 0 1 →
                        (∀ z ∈ sphere c r, q z ≤ U z) → ∀ x ∈ ball c r, q x ≤ U x) := by
  obtain ⟨U, _f, _hs, hU, hz, _hd, _hf, _herr, _hm, _hunif, hcomp⟩ :=
    exists_envelope_local_comparison hn (Ω := ball (0 : EuclideanSpace ℝ (Fin n)) 1) isOpen_ball
      (convex_ball _ _) isBounded_ball
  exact ⟨U, hU, hz, hcomp⟩

end LocalRaisingClients

section QuadraticLowerTests
open Filter

/-- Actual positive-dimensional unit-ball source, with no supplied U or test bound. -/
theorem actual_unit_ball_quadratic_tests {n : ℕ} (hn : 0 < n) :
    ∃ U : EuclideanSpace ℝ (Fin n) → ℝ,
      U ∈ subsolutions (ball 0 1) ∧
        (∀ z ∈ frontier (ball 0 1), U z = 0) ∧
          (∀ (A : Matrix (Fin n) (Fin n) ℝ),
            A.PosDef →
              ∀ x ∈ ball 0 1,
                ∀ b, (∀ᶠ y in 𝓝 x, quadraticAt A x b (U x) y ≤ U y) → A.det ≤ 1) := by
  obtain ⟨U, _f, _hs, hU, hz, _hd, _hf, _he, _hm, _hu, _hc, hb⟩ :=
    exists_envelope_quadratic_lower_test_bound hn (Ω := ball (0 : EuclideanSpace ℝ (Fin n)) 1)
      isOpen_ball (convex_ball _ _) isBounded_ball
  exact ⟨U, hU, hz, hb⟩

end QuadraticLowerTests

section C2LowerTests
open Filter
open FunctionalInequalities.Probability.Stein

/-- Source-generated SAME envelope and a genuinely constructed affine C2 lower
contact, with actual PSD Hessian zero and actual determinant conclusion. -/
theorem actual_unit_ball_affine_contact {n : ℕ} (hn : 0 < n) :
    ∃ (U : EuclideanSpace ℝ (Fin n) → ℝ) (p : EuclideanSpace ℝ (Fin n)),
      U ∈ subsolutions (ball (0 : EuclideanSpace ℝ (Fin n)) 1) ∧
        (∀ z ∈ frontier (ball (0 : EuclideanSpace ℝ (Fin n)) 1), U z = 0) ∧
          let ψ := quadraticAt (0 : Matrix (Fin n) (Fin n) ℝ) 0 p (U 0)
          ContDiff ℝ 2 ψ ∧
            U 0 = ψ 0 ∧
              (∀ᶠ y in 𝓝 0, ψ y ≤ U y) ∧
                (hessianMatrix ψ 0).PosSemidef ∧ (hessianMatrix ψ 0).det ≤ 1 := by
  let Ω := ball (0 : EuclideanSpace ℝ (Fin n)) 1
  have hcΩ : Convex ℝ Ω := convex_ball _ _
  have hΩ : IsOpen Ω := isOpen_ball
  obtain ⟨U, f, _, hU, hz, _, _, _, _, _, _, _, hc2⟩ :=
    exists_envelope_c2_lower_test_bound hn hΩ hcΩ isBounded_ball
  have hcv : ConvexOn ℝ Ω U := hU.1.subset subset_closure hcΩ
  have hC : ContinuousOn U Ω := hU.2.1.mono subset_closure
  have hx : (0 : EuclideanSpace ℝ (Fin n)) ∈ Ω := mem_ball_self zero_lt_one
  obtain ⟨R, hR, hs, _⟩ :=
    exists_uniform_subgradient_bound_on_compact hΩ hcv hC
      (isCompact_singleton (x := (0 : EuclideanSpace ℝ (Fin n)))) (singleton_subset_iff.mpr hx)
  obtain ⟨p, hp⟩ := hs 0 (mem_singleton 0)
  let ψ := quadraticAt (0 : Matrix (Fin n) (Fin n) ℝ) 0 p (U 0)
  have hψ : ContDiff ℝ 2 ψ := contDiff_quadraticAt _ _ _ _
  have hcontact : U 0 = ψ 0 := by simp [ψ, quadraticAt]
  have ht : ∀ᶠ y in 𝓝 0, ψ y ≤ U y := by
    filter_upwards [hΩ.mem_nhds hx] with y hy
    simpa [ψ, quadraticAt] using hp y hy
  have hH : (hessianMatrix ψ 0).PosSemidef := by
    rw [show hessianMatrix ψ 0 = (0 : Matrix (Fin n) (Fin n) ℝ) from
        hessianMatrix_quadraticAt (by simp) _ _ _ _]
    exact Matrix.PosSemidef.zero
  have hd := hc2 ψ 0 hx hψ.contDiffAt hH hcontact ht
  exact ⟨U, p, hU, hz, hψ, hcontact, ht, hH, hd⟩

end C2LowerTests

section BufferedMoreauClient
open Filter

private lemma half_closedBall_subset_unitBall {n : ℕ} :
    closedBall (0 : EuclideanSpace ℝ (Fin n)) (1 / 2) ⊆ ball 0 1 := by
  intro y hy
  change dist y 0 < 1
  change dist y 0 ≤ 1 / 2 at hy
  linarith

private lemma actual_small_epsilon (L : NNReal) :
    0 < (16 * ((L : ℝ) + 1))⁻¹ ∧ (16 * ((L : ℝ) + 1))⁻¹ * ((L : ℝ) + 1) < (1 / 2) / 2 := by
  have he : (16 * ((L : ℝ) + 1))⁻¹ * ((L : ℝ) + 1) = 1 / 16 := by field_simp
  exact ⟨by positivity, by rw [he]; norm_num⟩


/-- Source-only unit-ball data and an actual positive epsilon generate a C1,1
regularized family member with genuine transferred PD quadratic lower tests. -/
theorem actual_unit_ball_buffer {n : ℕ} (hn : 0 < n) :
    ∃ (U V : EuclideanSpace ℝ (Fin n) → ℝ) (L : NNReal) (ε : ℝ),
      U ∈ subsolutions (ball (0 : EuclideanSpace ℝ (Fin n)) 1) ∧
        (∀ z ∈ frontier (ball (0 : EuclideanSpace ℝ (Fin n)) 1), U z = 0) ∧
          ConvexOn ℝ univ V ∧
            LipschitzWith L V ∧
              (∀ y ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) (1 / 2), V y = U y) ∧
                0 < ε ∧
                  ContDiff ℝ 1 (moreauEnvelope V ε) ∧
                    LipschitzWith (‖(ε⁻¹ : ℝ)‖₊ * 2) (gradient (moreauEnvelope V ε)) ∧
                      (∀ (A : Matrix (Fin n) (Fin n) ℝ),
                          A.PosDef →
                            ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin n)) (1 / 4),
                              ∀ b,
                                (∀ᶠ z in 𝓝 x,
                                    quadraticAt A x b (moreauEnvelope V ε x) z ≤
                                      moreauEnvelope V ε z) →
                                  A.det ≤ 1) ∧
                        TendstoUniformlyOn (fun t : ℝ => moreauEnvelope V t) U (𝓝[>] (0 : ℝ))
                          (closedBall (0 : EuclideanSpace ℝ (Fin n)) (1 / 2)) := by
  let Ω := ball (0 : EuclideanSpace ℝ (Fin n)) 1
  obtain ⟨U, f, _, hU, hz, _, _, _, _, _, _, _, _, hbuf⟩ :=
    exists_envelope_buffered_moreau hn isOpen_ball (convex_ball _ _) isBounded_ball
  have hball : closedBall (0 : EuclideanSpace ℝ (Fin n)) (1 / 2) ⊆ Ω :=
    half_closedBall_subset_unitBall
  obtain ⟨V, L, hV, hL, heq, hreg, hunif⟩ := hbuf 0 (1 / 2) (by norm_num) hball
  let ε := (16 * ((L : ℝ) + 1))⁻¹
  obtain ⟨hε, hsmall⟩ := actual_small_epsilon L
  obtain ⟨_, hc, hl, hquad⟩ := hreg ε hε hsmall
  refine ⟨U, V, L, ε, hU, hz, hV, hL, heq, hε, hc, hl, ?_, hunif⟩
  simpa only [show (1 / 2 : ℝ) / 2 = 1 / 4 by norm_num] using hquad

/-- Actual unit-ball source displaying generated regularity and SAME a.e. matrix. -/
theorem actual_unit_ball_ae_matrix {n : ℕ} (hn : 0<n) :
    ∃ (U V : EuclideanSpace ℝ (Fin n)→ℝ) (L : NNReal) (ε : ℝ),
      U∈subsolutions (ball (0 : EuclideanSpace ℝ (Fin n)) 1) ∧
      (∀ z∈frontier (ball (0 : EuclideanSpace ℝ (Fin n)) 1), U z=0) ∧
      ConvexOn ℝ univ V ∧ LipschitzWith L V ∧
      (∀ y∈closedBall (0 : EuclideanSpace ℝ (Fin n)) (1 / 2), V y=U y) ∧
      0<ε ∧ ContDiff ℝ 1 (moreauEnvelope V ε) ∧
      LipschitzWith (‖(ε⁻¹:ℝ)‖₊*2) (gradient (moreauEnvelope V ε)) ∧
      (∀ (A : Matrix (Fin n) (Fin n) ℝ), A.PosDef→∀ x∈ball (0 : EuclideanSpace ℝ (Fin n)) (1 / 4),
        ∀ b,
        (∀ᶠ z in 𝓝 x, quadraticAt A x b (moreauEnvelope V ε x) z≤ moreauEnvelope V ε z)→A.det≤1) ∧
      (∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict
          (ball (0 : EuclideanSpace ℝ (Fin n)) (1 / 4))),
        ∃ A : Matrix (Fin n) (Fin n) ℝ, A.IsHermitian ∧
          HasFDerivAt (gradient (moreauEnvelope V ε))
            (Matrix.toEuclideanLin A).toContinuousLinearMap x ∧
          A.PosSemidef ∧ A.det≤1 ∧
          ∀ t>0, ∀ᶠ y in 𝓝 x,
            |moreauEnvelope V ε y-quadraticAt A x (gradient (moreauEnvelope V ε) x)
              (moreauEnvelope V ε x) y|≤t*‖y-x‖^2) ∧
      TendstoUniformlyOn (fun t : ℝ => moreauEnvelope V t) U (𝓝[>] (0:ℝ))
        (closedBall (0 : EuclideanSpace ℝ (Fin n)) (1 / 2)) := by
    let Ω := ball (0 : EuclideanSpace ℝ (Fin n)) 1
    obtain ⟨U, f, _, hU, hz, _, _, _, _, _, _, _, _, hbuf⟩ :=
      exists_envelope_buffered_moreau_ae_matrix hn isOpen_ball (convex_ball _ _)
        isBounded_ball
    have hball : closedBall (0 : EuclideanSpace ℝ (Fin n)) (1 / 2) ⊆ Ω :=
      half_closedBall_subset_unitBall
    obtain ⟨V, L, hV, hL, heq, hreg, hunif⟩ := hbuf 0 (1 / 2) (by norm_num) hball
    let ε := (16 * ((L : ℝ) + 1))⁻¹
    obtain ⟨hε, hsmall⟩ := actual_small_epsilon L
    obtain ⟨_, hc, hl, hquad, hAE⟩ := hreg ε hε hsmall
    refine ⟨U, V, L, ε, hU, hz, hV, hL, heq, hε, hc, hl, ?_, ?_, hunif⟩
    · simpa only [show (1 / 2 : ℝ) / 2 = 1 / 4 by norm_num] using hquad
    · simpa only [show (1 / 2 : ℝ) / 2 = 1 / 4 by norm_num] using hAE

/-- Genuine source-generated unit-ball image upper and true zero-dimensional
Haar/Jacobian clients. -/
theorem actual_unit_ball_image_upper {n : ℕ} (hn : 0 < n) :
    ∃ (U V : EuclideanSpace ℝ (Fin n) → ℝ) (L : NNReal) (ε : ℝ),
      U ∈ subsolutions (ball (0 : EuclideanSpace ℝ (Fin n)) 1) ∧
        (∀ z ∈ frontier (ball (0 : EuclideanSpace ℝ (Fin n)) 1), U z = 0) ∧
          ConvexOn ℝ univ V ∧
            LipschitzWith L V ∧
              (∀ y ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) (1 / 2), V y = U y) ∧
                0 < ε ∧
                  ContDiff ℝ 1 (moreauEnvelope V ε) ∧
                    LipschitzWith (‖(ε⁻¹ : ℝ)‖₊ * 2) (gradient (moreauEnvelope V ε)) ∧
                      (∀ Γ : Set (EuclideanSpace ℝ (Fin n)),
                          MeasurableSet Γ →
                            Γ ⊆ ball 0 (1 / 4) →
                              volume ((gradient (moreauEnvelope V ε)) '' Γ) ≤ volume Γ ∧
                                volume
                                    (subgradientImageOn (moreauEnvelope V ε) (ball 0 (1 / 4))
                                      Γ) ≤
                                  volume Γ) ∧
                        TendstoUniformlyOn (fun t : ℝ => moreauEnvelope V t) U (𝓝[>] (0 : ℝ))
                          (closedBall (0 : EuclideanSpace ℝ (Fin n)) (1 / 2)) := by
  obtain ⟨U, f, _, hU, hz, _, _, _, _, _, _, _, _, hbuf⟩ :=
    exists_envelope_buffered_moreau_image_upper hn isOpen_ball (convex_ball _ _) isBounded_ball
  have hball : closedBall (0 : EuclideanSpace ℝ (Fin n)) (1 / 2) ⊆ ball 0 1 :=
    half_closedBall_subset_unitBall
  obtain ⟨V, L, hV, hL, heq, hreg, hunif⟩ := hbuf 0 (1 / 2) (by norm_num) hball
  let ε := (16 * ((L : ℝ) + 1))⁻¹
  obtain ⟨hε, hsmall⟩ := actual_small_epsilon L
  obtain ⟨_, hc, hl, _, _, himage⟩ := hreg ε hε hsmall
  refine ⟨U, V, L, ε, hU, hz, hV, hL, heq, hε, hc, hl, ?_, hunif⟩
  simpa only [show (1 / 2 : ℝ) / 2 = 1 / 4 by norm_num] using himage

theorem actual_fin0_jacobian_mass_one :
    volume ((id : EuclideanSpace ℝ (Fin 0) → EuclideanSpace ℝ (Fin 0)) '' univ) ≤
        (volume : Measure (EuclideanSpace ℝ (Fin 0))) univ ∧
      (volume : Measure (EuclideanSpace ℝ (Fin 0))) univ = 1 := by
  have hAE :
    ∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin 0))).restrict univ),
      ∃ D : EuclideanSpace ℝ (Fin 0) →L[ℝ] EuclideanSpace ℝ (Fin 0),
        HasFDerivAt id D x ∧ |D.det| ≤ (1 : ℝ) := by
    exact
      Filter.Eventually.of_forall
        (fun x =>
          ⟨ContinuousLinearMap.id ℝ _, hasFDerivAt_id x,
            by
            change
              |(LinearMap.id : EuclideanSpace ℝ (Fin 0) →ₗ[ℝ] EuclideanSpace ℝ (Fin 0)).det| ≤
                (1 : ℝ)
            rw [LinearMap.det_id]
            norm_num⟩)
  have h :=
    addHaar_image_le_mul_of_ae_derivative volume MeasurableSet.univ hAE
      (fun N _ hN =>
        volume_image_eq_zero_of_lipschitzOnWith LipschitzWith.id.lipschitzOnWith hN)
  refine ⟨h.trans_eq (by rw [ENNReal.ofReal_one, one_mul]), ?_⟩
  rw [volume_euclideanSpace_eq_dirac]
  simp

/-- Actual source-derived buffered U DOMAIN upper bound, not a supplied limit. -/
theorem actual_unit_ball_local_upper {n : ℕ} (hn : 0 < n) :
    ∃ U : EuclideanSpace ℝ (Fin n) → ℝ,
      U ∈ subsolutions (ball (0 : EuclideanSpace ℝ (Fin n)) 1) ∧
        (∀ z ∈ frontier (ball (0 : EuclideanSpace ℝ (Fin n)) 1), U z = 0) ∧
          (∀ G : Set (EuclideanSpace ℝ (Fin n)),
            IsOpen G →
              G ⊆ ball 0 (1 / 4) → volume (subgradientImageOn U (ball 0 1) G) ≤ volume G) := by
  obtain ⟨U, f, _, hU, hz, _, _, _, _, _, _, _, _, hbuf⟩ :=
    exists_envelope_buffered_local_ma_upper hn isOpen_ball (convex_ball _ _) isBounded_ball
  have hball : closedBall (0 : EuclideanSpace ℝ (Fin n)) (1 / 2) ⊆ ball 0 1 :=
    half_closedBall_subset_unitBall
  obtain ⟨V, L, _, _, _, _, _, hup⟩ := hbuf 0 (1 / 2) (by norm_num) hball
  refine ⟨U, hU, hz, ?_⟩
  simpa only [show (1 / 2 : ℝ) / 2 = 1 / 4 by norm_num] using hup

end BufferedMoreauClient

end LetwinDirichletEnvelopeAudit
#print axioms LetwinDirichletEnvelopeAudit.actual_unitBall_envelope
#print axioms LetwinDirichletEnvelopeAudit.actual_fin0_subsolutions
#print axioms LetwinDirichletEnvelopeAudit.pure_vector_supremum

#print axioms LetwinDirichletEnvelopeAudit.actual_nondifferentiable_bridge

#print axioms LetwinDirichletEnvelopeAudit.actual_interval_envelope
#print axioms LetwinDirichletEnvelopeAudit.actual_halfball_envelope

#print axioms LetwinDirichletEnvelopeAudit.actual_crossing_max
#print axioms LetwinDirichletEnvelopeAudit.actual_fin0_max

#print axioms LetwinDirichletEnvelopeAudit.actual_unit_ball
#print axioms LetwinDirichletEnvelopeAudit.actual_empty_domain

#print axioms LetwinDirichletEnvelopeAudit.actual_absolute_quadratic_patch
#print axioms LetwinDirichletEnvelopeAudit.actual_zero_dimensional_patch

#print axioms LetwinDirichletEnvelopeAudit.actual_quadratic_local_raise
#print axioms LetwinDirichletEnvelopeAudit.actual_unit_ball_local_comparison
#check LetwinDirichletEnvelopeAudit.actual_quadratic_local_raise 0

#print axioms LetwinDirichletEnvelopeAudit.actual_unit_ball_quadratic_tests

#print axioms LetwinDirichletEnvelopeAudit.actual_unit_ball_affine_contact

#print axioms LetwinDirichletEnvelopeAudit.actual_unit_ball_buffer

#print axioms LetwinDirichletEnvelopeAudit.actual_unit_ball_ae_matrix

#print axioms LetwinDirichletEnvelopeAudit.actual_unit_ball_image_upper
#print axioms LetwinDirichletEnvelopeAudit.actual_fin0_jacobian_mass_one

#print axioms LetwinDirichletEnvelopeAudit.actual_unit_ball_local_upper

namespace LetwinDirichletEnvelopeAudit
open FunctionalInequalities.Analysis FunctionalInequalities.Probability.Stein Filter Matrix
open scoped Matrix.Norms.Elementwise Topology ContDiff

private theorem unit_ball_data {n : ℕ} :
    let u := quadraticAt (1 : Matrix (Fin n) (Fin n) ℝ) 0 0 (-1 / 2)
    ContDiff ℝ 4 u ∧
      (∀ y, hessianMatrix u y = 1) ∧
        (∀ y ∈ ball 0 1, u y < 0) ∧ (∀ y ∈ frontier (ball 0 1), u y = 0) := by
  dsimp only
  let u := quadraticAt (1 : Matrix (Fin n) (Fin n) ℝ) 0 0 (-1 / 2)
  have hv (y : EuclideanSpace ℝ (Fin n)) : u y = -(1 / 2 : ℝ) + (1 / 2 : ℝ) * ‖y‖ ^ 2 := by
    norm_num [u, quadraticAt, Matrix.toEuclideanLin]
  refine
    ⟨contDiff_quadraticAt_all _ _ _ _, fun _ => hessianMatrix_quadraticAt (by simp) _ _ _ _, ?_,
      ?_⟩
  · intro y hy
    have hn : ‖y‖ < 1 := by simpa using hy
    change u y < 0
    rw [hv y]
    nlinarith [norm_nonneg y]
  · intro y hy
    have hs := frontier_ball_subset_sphere hy
    have hn : ‖y‖ = 1 := by simpa [mem_sphere] using hs
    change u y = 0
    rw [hv y, hn]
    norm_num

/-- Actual canonical quadratic calculus generates a classical determinant-one
source and applies BOTH differential identities, in every dimension including0.
This explicit source is not the chosen general-domain UNIT solution. -/
theorem actual_quadratic_classical {n : ℕ} :
    let u := quadraticAt (1 : Matrix (Fin n) (Fin n) ℝ) 0 0 (-1 / 2)
    ContDiff ℝ 4 u ∧
      (∀ x, (hessianMatrix u x).det = 1) ∧
        ∀ x : EuclideanSpace ℝ (Fin n),
          (∀ v : EuclideanSpace ℝ (Fin n),
              ((hessianMatrix u x)⁻¹ * fderiv ℝ (hessianMatrix u) x v).trace = 0) ∧
            ∀ v w : EuclideanSpace ℝ (Fin n),
              ((hessianMatrix u x)⁻¹ *
                    fderiv ℝ (fun y => fderiv ℝ (hessianMatrix u) y w) x v).trace =
                ((hessianMatrix u x)⁻¹ * fderiv ℝ (hessianMatrix u) x v *
                      (hessianMatrix u x)⁻¹ *
                    fderiv ℝ (hessianMatrix u) x w).trace := by
  dsimp only
  obtain ⟨hC, hH, _hneg, _hbd⟩ := unit_ball_data (n := n)
  have hd (x : EuclideanSpace ℝ (Fin n)) :
    (hessianMatrix (quadraticAt (1 : Matrix (Fin n) (Fin n) ℝ) 0 0 (-1 / 2)) x).det = 1 := by
    rw [hH x, Matrix.det_one]
  refine ⟨hC, hd, ?_⟩
  intro x
  exact
    classical_hessian_trace_identities hC.contDiffAt (by norm_num : (1 : ℝ) ≠ 0)
      (Filter.Eventually.of_forall hd)

end LetwinDirichletEnvelopeAudit
set_option pp.fullNames true in
#print axioms LetwinDirichletEnvelopeAudit.actual_quadratic_classical

namespace LetwinDirichletEnvelopeAudit
open FunctionalInequalities.Analysis FunctionalInequalities.Probability.Stein Filter Matrix
open scoped ContDiff Topology Matrix.Norms.Elementwise

/-- The actual unit quadratic GENERATES every classical hypothesis, its maximizer
and gradient cap. This works also in dimension0, where there is no direction k. -/
theorem actual_unit_ball_height_bound {n : ℕ} :
    let u := quadraticAt (1 : Matrix (Fin n) (Fin n) ℝ) 0 0 (-1 / 2)
    ∃ B : ℝ,
      0 < B ∧
        (∀ x ∈ closure (ball 0 1), ‖fderiv ℝ u x‖ ≤ B) ∧
          ∀ x ∈ ball 0 1,
            ∀ k : Fin n,
              hessianMatrix u x k k * (-u x) ≤ ((n : ℝ) + B) * Real.exp ((1 / 2 : ℝ) * B ^ 2) := by
  dsimp only
  obtain ⟨hu, hH, hneg, hbd⟩ := unit_ball_data (n := n)
  apply
    Pogorelov.exists_directional_height_bound (c := 1) isOpen_ball isBounded_ball
      (fun _ _ => hu.contDiffAt)
      (fun _ _ => (hu.of_le (show (2 : ℕ∞ω) ≤ 4 by norm_num)).contDiffAt) (by norm_num)
  · intro y _; rw [hH y, Matrix.det_one]
  · intro y _; rw [hH y]; exact Matrix.PosDef.one
  · exact hneg
  · exact hbd

/-- SAME actual quadratic source exercises the FULL Hessian estimate and generated
compact-interior cap. No derivative/Hessian cap or maximizing point is supplied. -/
theorem actual_unit_ball_interior_bound {n : ℕ} :
    let u := quadraticAt (1 : Matrix (Fin n) (Fin n) ℝ) 0 0 (-1 / 2)
    ∃ B : ℝ,
      0 < B ∧
        (∀ x ∈ closure (ball 0 1), ‖fderiv ℝ u x‖ ≤ B) ∧
          (∀ x ∈ ball 0 1,
              ‖hessianMatrix u x‖ * (-u x) ≤ ((n : ℝ) + B) * Real.exp ((1 / 2 : ℝ) * B ^ 2)) ∧
            ∀ K : Set (EuclideanSpace ℝ (Fin n)),
              IsCompact K → K ⊆ ball 0 1 → ∃ R : ℝ, 0 < R ∧ ∀ x ∈ K, ‖hessianMatrix u x‖ ≤ R := by
  dsimp only
  obtain ⟨hu, hH, hneg, hbd⟩ := unit_ball_data (n := n)
  apply
    Pogorelov.exists_hessian_height_and_interior_bound (c := 1) isOpen_ball isBounded_ball
      (fun _ _ => hu.contDiffAt)
      (fun _ _ => (hu.of_le (show (2 : ℕ∞ω) ≤ 4 by norm_num)).contDiffAt) (by norm_num)
  · intro y _; rw [hH y, Matrix.det_one]
  · intro y _; rw [hH y]; exact Matrix.PosDef.one
  · exact hneg
  · exact hbd

/-- Empty domain permits an arbitrary ambient function, with no regularity source
assumption. The actual SAME factory constructs the bounds. -/
theorem actual_empty_interior_bound (u : EuclideanSpace ℝ (Fin 1) → ℝ) :
    ∃ B : ℝ,
      0 < B ∧
        (∀ x ∈ closure (∅ : Set (EuclideanSpace ℝ (Fin 1))), ‖fderiv ℝ u x‖ ≤ B) ∧
          (∀ x ∈ (∅ : Set (EuclideanSpace ℝ (Fin 1))),
              ‖hessianMatrix u x‖ * (-u x) ≤ ((1 : ℝ) + B) * Real.exp ((1 / 2 : ℝ) * B ^ 2)) ∧
            ∀ K : Set (EuclideanSpace ℝ (Fin 1)),
              IsCompact K → K ⊆ ∅ → ∃ R : ℝ, 0 < R ∧ ∀ x ∈ K, ‖hessianMatrix u x‖ ≤ R := by
  simpa only [Nat.cast_one] using
    (Pogorelov.exists_hessian_height_and_interior_bound (n := 1) (u := u) (c := 1) isOpen_empty
      Bornology.isBounded_empty (by simp) (by simp) (by norm_num) (by simp) (by simp) (by simp)
      (by simp))

/-- True Fin0 point: the carrier is a singleton, and the empty Hessian matrix has
norm0. The SAME estimate supplies a positive cap; this is not a Haar mass claim. -/
theorem actual_fin0_point_cap :
    let u := quadraticAt (1 : Matrix (Fin 0) (Fin 0) ℝ) 0 0 (-1 / 2)
    ‖hessianMatrix u 0‖ = 0 ∧ ∃ R : ℝ, 0 < R ∧ ‖hessianMatrix u 0‖ ≤ R := by
  dsimp only
  obtain ⟨_, hH, _, _⟩ := unit_ball_data (n := 0)
  have hn : (1 : Matrix (Fin 0) (Fin 0) ℝ) = 0 := Subsingleton.elim _ _
  refine ⟨by rw [hH 0, hn, norm_zero], ?_⟩
  obtain ⟨B, hB, hBd, hheight, hcap⟩ := actual_unit_ball_interior_bound (n := 0)
  obtain ⟨R, hR, hRcap⟩ := hcap {0} isCompact_singleton (by simp)
  exact ⟨R, hR, hRcap 0 (by simp)⟩

end LetwinDirichletEnvelopeAudit

#print axioms LetwinDirichletEnvelopeAudit.actual_unit_ball_height_bound

#print axioms LetwinDirichletEnvelopeAudit.actual_unit_ball_interior_bound

#print axioms LetwinDirichletEnvelopeAudit.actual_empty_interior_bound

#print axioms LetwinDirichletEnvelopeAudit.actual_fin0_point_cap
