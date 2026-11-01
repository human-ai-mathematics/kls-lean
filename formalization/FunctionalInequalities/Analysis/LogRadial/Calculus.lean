module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Second Fréchet derivatives of the CNS1984 log/radial barrier pieces (Lemma 5.1, p. 386)

On an arbitrary real normed space `G` (no finite dimension, completeness or nontriviality), for real
continuous
linear functionals `p`, `q` (not assumed independent), a shift `β`, and a point with `0 < q x`, put
`S y = (p y - β)² + (q y)²`. The barrier pieces are the logarithmic term `-q y · log S y` and the
radial term
`√(S y)`.

* `barrierQuadratic_prep`: the ONE shared preparation, used by both pieces: `S` is smooth and, near
  `x`,
  positive with derivative `2(p y - β) p + 2 q y q`.
* `hasFDerivAt_log_radial_barrier`: near `x`, the actual first derivatives of both pieces.
* `contDiffAt_log_radial_barrier`: both pieces are `C^∞` at `x`.
* `fderiv_fderiv_log_radial_barrier`: the actual second Fréchet derivatives, evaluated on `v, w`.
* `contDiffAt_fderiv_fderiv_log_radial_profile`: the constructed barrier profile
  `(√S + (p - β) - ε q log S) / 2` is smooth with the explicit second derivative (radial and
  logarithmic pieces,
  affine part zero), through the scalar-combination rule for second derivatives.

The second derivative is reduced to the derivative of the scalar function `y ↦ fderiv f y w`
(Mathlib
`fderiv_clm_apply`), which is computed with Mathlib's product, inverse, logarithm and square-root
rules.
-/

@[expose] public section

section
open Filter
open scoped ContDiff Topology

namespace FunctionalInequalities.Analysis

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/--
**Shared positive quadratic.** `S y = (p y - β)² + (q y)²` is smooth, and near a point with `0 < S
x` it is
positive with Fréchet derivative `2(p y - β) p + 2 q y q`. -/
theorem barrierQuadratic_prep_of_pos (p q : G →L[ℝ] ℝ) (β : ℝ) {x : G}
    (hS : 0 < (p x - β) ^ 2 + (q x) ^ 2) :
    ContDiff ℝ ∞ (fun y : G => (p y - β) ^ 2 + (q y) ^ 2) ∧
      ∀ᶠ y in 𝓝 x,
        0 < (p y - β) ^ 2 + (q y) ^ 2 ∧
          HasFDerivAt (fun y : G => (p y - β) ^ 2 + (q y) ^ 2)
            ((2 * (p y - β)) • p + (2 * q y) • q) y := by
  have hc : ContDiff ℝ ∞ (fun y : G => (p y - β) ^ 2 + (q y) ^ 2) :=
    ((p.contDiff.sub contDiff_const).pow 2).add (q.contDiff.pow 2)
  refine ⟨hc, ?_⟩
  filter_upwards [(hc.continuous.tendsto x).eventually (lt_mem_nhds hS)] with y hy
  refine ⟨hy, ?_⟩
  have h : HasFDerivAt (fun y : G => (p y - β) ^ 2 + (q y) ^ 2) _ y :=
    ((p.hasFDerivAt.sub_const β).pow 2).add (q.hasFDerivAt.pow 2)
  refine h.congr_fderiv ?_
  ext w
  simp

/-- **Shared positive quadratic** near a point with `0 < q x` (then `0 < S x`). -/
theorem barrierQuadratic_prep (p q : G →L[ℝ] ℝ) (β : ℝ) {x : G} (hx : 0 < q x) :
    ContDiff ℝ ∞ (fun y : G => (p y - β) ^ 2 + (q y) ^ 2) ∧
      ∀ᶠ y in 𝓝 x, 0 < (p y - β) ^ 2 + (q y) ^ 2 ∧
        HasFDerivAt (fun y : G => (p y - β) ^ 2 + (q y) ^ 2)
          ((2 * (p y - β)) • p + (2 * q y) • q) y :=
  barrierQuadratic_prep_of_pos p q β (add_pos_of_nonneg_of_pos (sq_nonneg _) (pow_pos hx 2))

/--
The second derivative of a `C²` function, evaluated on `v, w`, is the derivative in direction `v` of
any
scalar function agreeing near `x` with `y ↦ fderiv f y w`. -/
private lemma fderiv_fderiv_apply_eq {f Φ : G → ℝ} {x : G} (hf : ContDiffAt ℝ 2 f x) (w : G)
    (hΦ : ∀ᶠ y in 𝓝 x, fderiv ℝ f y w = Φ y) (v : G) :
    fderiv ℝ (fderiv ℝ f) x v w = fderiv ℝ Φ x v := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have h := fderiv_clm_apply hd (differentiableAt_const w)
  have hE : (fun y => fderiv ℝ f y w) =ᶠ[𝓝 x] Φ := hΦ
  rw [← hE.fderiv_eq, h]
  simp

/--
**First derivatives of the log and radial pieces**: near a point with `0 < S x`, the actual Fréchet
derivatives,
with `S' = 2 (p y - β) p + 2 q y q`. -/
theorem hasFDerivAt_log_radial_barrier_of_pos {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] (p q : G →L[ℝ] ℝ) (β : ℝ) {x : G} (hS : 0 < (p x - β) ^ 2 + (q x) ^ 2) :
    ∀ᶠ y in 𝓝 x,
      HasFDerivAt (fun y : G => -(q y) * Real.log ((p y - β) ^ 2 + (q y) ^ 2))
          ((-(q y)) • (((p y - β) ^ 2 + (q y) ^ 2)⁻¹ • ((2 * (p y - β)) • p + (2 * q y) • q)) +
            Real.log ((p y - β) ^ 2 + (q y) ^ 2) • (-q))
          y ∧
        HasFDerivAt (fun y : G => Real.sqrt ((p y - β) ^ 2 + (q y) ^ 2))
          ((1 / (2 * Real.sqrt ((p y - β) ^ 2 + (q y) ^ 2))) •
            ((2 * (p y - β)) • p + (2 * q y) • q))
          y := by
  filter_upwards [(barrierQuadratic_prep_of_pos p q β hS).2] with y hy
  exact ⟨q.hasFDerivAt.neg.mul (hy.2.log hy.1.ne'), hy.2.sqrt hy.1.ne'⟩

/-- **First derivatives of the log and radial pieces** near a point with `0 < q x`. -/
theorem hasFDerivAt_log_radial_barrier {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (p q : G →L[ℝ] ℝ) (β : ℝ) {x : G} (hx : 0 < q x) :
    ∀ᶠ y in 𝓝 x,
      HasFDerivAt (fun y : G => -(q y) * Real.log ((p y - β) ^ 2 + (q y) ^ 2))
          ((-(q y)) • (((p y - β) ^ 2 + (q y) ^ 2)⁻¹ • ((2 * (p y - β)) • p + (2 * q y) • q)) +
            Real.log ((p y - β) ^ 2 + (q y) ^ 2) • (-q))
          y ∧
        HasFDerivAt (fun y : G => Real.sqrt ((p y - β) ^ 2 + (q y) ^ 2))
          ((1 / (2 * Real.sqrt ((p y - β) ^ 2 + (q y) ^ 2))) •
            ((2 * (p y - β)) • p + (2 * q y) • q))
          y :=
  hasFDerivAt_log_radial_barrier_of_pos p q β
    (add_pos_of_nonneg_of_pos (sq_nonneg _) (pow_pos hx 2))

/-- Both pieces are `C^∞` at a point with `0 < S x`. -/
theorem contDiffAt_log_radial_barrier_of_pos {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (p q : G →L[ℝ] ℝ) (β : ℝ) {x : G} (hS : 0 < (p x - β) ^ 2 + (q x) ^ 2) :
    ContDiffAt ℝ ∞ (fun y : G => -(q y) * Real.log ((p y - β) ^ 2 + (q y) ^ 2)) x ∧
      ContDiffAt ℝ ∞ (fun y : G => Real.sqrt ((p y - β) ^ 2 + (q y) ^ 2)) x := by
  obtain ⟨hS, hev⟩ := barrierQuadratic_prep_of_pos p q β hS
  have hSx : (p x - β) ^ 2 + (q x) ^ 2 ≠ 0 := hev.self_of_nhds.1.ne'
  exact ⟨q.contDiff.neg.contDiffAt.mul (hS.contDiffAt.log hSx), hS.contDiffAt.sqrt hSx⟩

theorem contDiffAt_log_radial_barrier {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (p q : G →L[ℝ] ℝ) (β : ℝ) {x : G} (hx : 0 < q x) :
    ContDiffAt ℝ ∞ (fun y : G => -(q y) * Real.log ((p y - β) ^ 2 + (q y) ^ 2)) x ∧
      ContDiffAt ℝ ∞ (fun y : G => Real.sqrt ((p y - β) ^ 2 + (q y) ^ 2)) x :=
  contDiffAt_log_radial_barrier_of_pos p q β (add_pos_of_nonneg_of_pos (sq_nonneg _) (pow_pos hx 2))

theorem fderiv_fderiv_log_radial_barrier {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (p q : G →L[ℝ] ℝ) (β : ℝ) {x : G} (hx : 0 < q x) (v w : G) :
    fderiv ℝ (fderiv ℝ (fun y : G => -(q y) * Real.log ((p y - β) ^ 2 + (q y) ^ 2))) x v w =
        (2 * q x * ((p x - β) ^ 2 - (q x) ^ 2) * p v * p w +
              2 * (p x - β) * ((q x) ^ 2 - (p x - β) ^ 2) * (p v * q w + q v * p w) -
            2 * q x * (3 * (p x - β) ^ 2 + (q x) ^ 2) * q v * q w) /
          (((p x - β) ^ 2 + (q x) ^ 2) ^ 2) ∧
      fderiv ℝ (fderiv ℝ (fun y : G => Real.sqrt ((p y - β) ^ 2 + (q y) ^ 2))) x v w =
        ((q x) ^ 2 * p v * p w - (p x - β) * q x * (p v * q w + q v * p w) +
            (p x - β) ^ 2 * q v * q w) /
          (Real.sqrt ((p x - β) ^ 2 + (q x) ^ 2)) ^ 3 := by
  obtain ⟨-, hev⟩ := barrierQuadratic_prep p q β hx
  have hSpos : 0 < (p x - β) ^ 2 + (q x) ^ 2 := hev.self_of_nhds.1
  have hSx : (p x - β) ^ 2 + (q x) ^ 2 ≠ 0 := hSpos.ne'
  have hSd := hev.self_of_nhds.2
  obtain ⟨hlog, hrad⟩ := contDiffAt_log_radial_barrier p q β hx
  have h2 : (2 : ℕ∞ω) ≤ ∞ :=
    WithTop.coe_le_coe.mpr
      le_top
  -- the scalar derivative of `y ↦ 2 (p y - β) p w + 2 q y q w`, shared by both pieces

  have hN : HasFDerivAt (fun y : G => 2 * (p y - β) * p w + 2 * q y * q w) _ x :=
    (((p.hasFDerivAt.sub_const β).const_mul 2).mul_const (p w)).add
      ((q.hasFDerivAt.const_mul 2).mul_const (q w))
  constructor
  ·
    -- logarithmic piece: `fderiv f y w = -(q y) (S y)⁻¹ (2 (p y - β) p w + 2 q y q w) - log (S y) q
    -- w`

    rw [fderiv_fderiv_apply_eq (hlog.of_le h2) w (Φ := fun y : G =>
        -(q y) * (((p y - β) ^ 2 + (q y) ^ 2)⁻¹ * (2 * (p y - β) * p w + 2 * q y * q w)) +
          Real.log ((p y - β) ^ 2 + (q y) ^ 2) * -(q w))
        ?_ v]
    · have hΦ :
        HasFDerivAt
          (fun y : G =>
            -(q y) * (((p y - β) ^ 2 + (q y) ^ 2)⁻¹ * (2 * (p y - β) * p w + 2 * q y * q w)) +
              Real.log ((p y - β) ^ 2 + (q y) ^ 2) * -(q w))
          _ x :=
        (q.hasFDerivAt.neg.mul (((hasDerivAt_inv hSx).comp_hasFDerivAt x hSd).mul hN)).add
          ((hSd.log hSx).mul_const (-(q w)))
      rw [hΦ.fderiv]
      simp
      field_simp
      ring
    · filter_upwards [hasFDerivAt_log_radial_barrier p q β hx] with y hy
      rw [hy.1.fderiv]
      simp
      ring
  · -- radial piece: `fderiv f y w = (2 √(S y))⁻¹ (2 (p y - β) p w + 2 q y q w)`

    rw [fderiv_fderiv_apply_eq (hrad.of_le h2) w (Φ := fun y : G =>
        (2 * Real.sqrt ((p y - β) ^ 2 + (q y) ^ 2))⁻¹ * (2 * (p y - β) * p w + 2 * q y * q w))
        ?_ v]
    · have hr : 0 < Real.sqrt ((p x - β) ^ 2 + (q x) ^ 2) := Real.sqrt_pos.mpr hSpos
      have hr2 : Real.sqrt ((p x - β) ^ 2 + (q x) ^ 2) ^ 2 = (p x - β) ^ 2 + (q x) ^ 2 :=
        Real.sq_sqrt hSpos.le
      have hΦ :
        HasFDerivAt
          (fun y : G =>
            (2 * Real.sqrt ((p y - β) ^ 2 + (q y) ^ 2))⁻¹ *
              (2 * (p y - β) * p w + 2 * q y * q w))
          _ x :=
        (((hasDerivAt_inv (by positivity)).comp_hasFDerivAt x ((hSd.sqrt hSx).const_mul 2)).mul
          hN)
      rw [hΦ.fderiv]
      simp
      refine
        Eq.trans (b :=
          (Real.sqrt ((p x - β) ^ 2 + (q x) ^ 2) ^ 2 * (p v * p w + q v * q w) -
              ((p x - β) * p v + q x * q v) * ((p x - β) * p w + q x * q w)) /
            Real.sqrt ((p x - β) ^ 2 + (q x) ^ 2) ^ 3)
          ?_ ?_
      · field_simp
        ring
      · rw [hr2]
        ring
    · filter_upwards [hasFDerivAt_log_radial_barrier p q β hx] with y hy
      rw [hy.2.fderiv]
      simp
      ring

/--
**Second derivative of a scalar combination** `(f + g + c h) / 2` of functions that are `C²` at `x`.
-/
private lemma fderiv_fderiv_half_combination {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] {f g h : G → ℝ} {x : G} (c : ℝ) (hf : ContDiffAt ℝ 2 f x)
    (hg : ContDiffAt ℝ 2 g x) (hh : ContDiffAt ℝ 2 h x) (v w : G) :
    fderiv ℝ (fderiv ℝ (fun y => (f y + g y + c * h y) / 2)) x v w =
      (fderiv ℝ (fderiv ℝ f) x v w + fderiv ℝ (fderiv ℝ g) x v w +
          c * fderiv ℝ (fderiv ℝ h) x v w) /
        2 := by
  have hfun : (fun y => (f y + g y + c * h y) / 2) = fun y => 2⁻¹ * (f y + g y + c * h y) := by
    funext y
    ring
  have ev :
    (fun y => fderiv ℝ (fun y => 2⁻¹ * (f y + g y + c * h y)) y) =ᶠ[𝓝 x] fun y =>
      (2⁻¹ : ℝ) • (fderiv ℝ f y + fderiv ℝ g y + c • fderiv ℝ h y) := by
    filter_upwards [hf.eventually (by simp), hg.eventually (by simp),
      hh.eventually (by simp)] with y hfy hgy hhy
    exact
      ((((hfy.differentiableAt (by simp)).hasFDerivAt.add
                  (hgy.differentiableAt (by simp)).hasFDerivAt).add
              ((hhy.differentiableAt (by simp)).hasFDerivAt.const_mul c)).const_mul
          2⁻¹).fderiv
  have d1 :
    ∀ {k : G → ℝ}, ContDiffAt ℝ 2 k x → HasFDerivAt (fderiv ℝ k) (fderiv ℝ (fderiv ℝ k) x) x :=
    fun hk =>
    ((hk.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hD :
    HasFDerivAt (fun y => (2⁻¹ : ℝ) • (fderiv ℝ f y + fderiv ℝ g y + c • fderiv ℝ h y)) _ x :=
    (((d1 hf).add (d1 hg)).add ((d1 hh).const_smul c)).const_smul (2⁻¹ : ℝ)
  rw [hfun, ev.fderiv_eq, hD.fderiv]
  simp
  ring

/-- The barrier profile as a scalar combination of the radial, affine and logarithmic pieces. -/
private lemma log_radial_profile_fun_eq {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (p q : G →L[ℝ] ℝ) (β ε : ℝ) :
    (fun y : G => (Real.sqrt ((p y - β) ^ 2 + (q y) ^ 2) + (p y - β) -
      ε * q y * Real.log ((p y - β) ^ 2 + (q y) ^ 2)) / 2) =
      fun y => (Real.sqrt ((p y - β) ^ 2 + (q y) ^ 2) + (p y - β) +
        ε * (-(q y) * Real.log ((p y - β) ^ 2 + (q y) ^ 2))) / 2 := by
  funext y
  ring

/-- **The barrier profile is `C^∞`** at a point with `0 < S x`. -/
theorem contDiffAt_log_radial_profile_of_pos {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] (p q : G →L[ℝ] ℝ) (β ε : ℝ) {x : G} (hS : 0 < (p x - β) ^ 2 + (q x) ^ 2) :
    ContDiffAt ℝ ∞
      (fun y : G =>
        (Real.sqrt ((p y - β) ^ 2 + (q y) ^ 2) + (p y - β) -
            ε * q y * Real.log ((p y - β) ^ 2 + (q y) ^ 2)) /
          2)
      x := by
  obtain ⟨hLc, hRc⟩ := contDiffAt_log_radial_barrier_of_pos p q β hS
  rw [log_radial_profile_fun_eq]
  exact
    ((hRc.add (p.contDiff.sub contDiff_const).contDiffAt).add
          (contDiffAt_const.mul hLc)).div_const
      2

/-- **First derivative of the barrier profile** at a point with `0 < S x`:
`DΦ(x) = ½ (R' + p + ε L')`. -/
theorem hasFDerivAt_log_radial_profile_of_pos {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (p q : G →L[ℝ] ℝ) (β ε : ℝ) {x : G} (hS : 0 < (p x - β) ^ 2 + (q x) ^ 2) :
    HasFDerivAt (fun y : G => (Real.sqrt ((p y - β) ^ 2 + (q y) ^ 2) + (p y - β) -
        ε * q y * Real.log ((p y - β) ^ 2 + (q y) ^ 2)) / 2)
      ((2⁻¹ : ℝ) • ((1 / (2 * Real.sqrt ((p x - β) ^ 2 + (q x) ^ 2))) •
          ((2 * (p x - β)) • p + (2 * q x) • q) + p +
        ε • ((-(q x)) • (((p x - β) ^ 2 + (q x) ^ 2)⁻¹ • ((2 * (p x - β)) • p + (2 * q x) • q)) +
          Real.log ((p x - β) ^ 2 + (q x) ^ 2) • (-q)))) x := by
  obtain ⟨hL, hR⟩ := (hasFDerivAt_log_radial_barrier_of_pos p q β hS).self_of_nhds
  have hP : HasFDerivAt (fun y : G => p y - β) p x := p.hasFDerivAt.sub_const β
  have hΦ : HasFDerivAt (fun y : G => 2⁻¹ * (Real.sqrt ((p y - β) ^ 2 + (q y) ^ 2) + (p y - β) +
      ε * (-(q y) * Real.log ((p y - β) ^ 2 + (q y) ^ 2)))) _ x :=
    ((hR.add hP).add (hL.const_mul ε)).const_mul (2⁻¹ : ℝ)
  refine hΦ.congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)
  ring

theorem contDiffAt_fderiv_fderiv_log_radial_profile {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] (p q : G →L[ℝ] ℝ) (β ε : ℝ) {x : G} (hx : 0 < q x) :
    ContDiffAt ℝ ∞
        (fun y : G =>
          (Real.sqrt ((p y - β) ^ 2 + (q y) ^ 2) + (p y - β) -
              ε * q y * Real.log ((p y - β) ^ 2 + (q y) ^ 2)) /
            2)
        x ∧
      ∀ v w : G,
        fderiv ℝ
            (fderiv ℝ
              (fun y : G =>
                (Real.sqrt ((p y - β) ^ 2 + (q y) ^ 2) + (p y - β) -
                    ε * q y * Real.log ((p y - β) ^ 2 + (q y) ^ 2)) /
                  2))
            x v w =
          (((q x) ^ 2 * p v * p w - (p x - β) * q x * (p v * q w + q v * p w) +
                  (p x - β) ^ 2 * q v * q w) /
                (Real.sqrt ((p x - β) ^ 2 + (q x) ^ 2)) ^ 3 +
              ε *
                ((2 * q x * ((p x - β) ^ 2 - (q x) ^ 2) * p v * p w +
                      2 * (p x - β) * ((q x) ^ 2 - (p x - β) ^ 2) * (p v * q w + q v * p w) -
                    2 * q x * (3 * (p x - β) ^ 2 + (q x) ^ 2) * q v * q w) /
                  (((p x - β) ^ 2 + (q x) ^ 2) ^ 2))) /
            2 := by
  obtain ⟨hLc, hRc⟩ := contDiffAt_log_radial_barrier p q β hx
  have hPc : ContDiff ℝ ∞ (fun y : G => p y - β) := p.contDiff.sub contDiff_const
  refine
    ⟨contDiffAt_log_radial_profile_of_pos p q β ε
        (add_pos_of_nonneg_of_pos (sq_nonneg _) (pow_pos hx 2)),
      fun v w => ?_⟩
  · have h2 : (2 : ℕ∞ω) ≤ ∞ :=
      WithTop.coe_le_coe.mpr
        le_top
    -- the affine part has constant first derivative `p`

    have hP2 : fderiv ℝ (fderiv ℝ (fun y : G => p y - β)) x v w = 0 := by
      have hd : fderiv ℝ (fun y : G => p y - β) = fun _ => p :=
        funext fun y => (p.hasFDerivAt.sub_const β).fderiv
      rw [hd]
      simp
    obtain ⟨hL2, hR2⟩ := fderiv_fderiv_log_radial_barrier p q β hx v w
    have hc :=
      fderiv_fderiv_half_combination ε (hRc.of_le h2) (hPc.contDiffAt.of_le h2) (hLc.of_le h2) v
        w
    rw [hR2, hP2, hL2] at hc
    rw [log_radial_profile_fun_eq, hc]
    ring

end FunctionalInequalities.Analysis

end
