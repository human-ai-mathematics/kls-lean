module

public import FunctionalInequalities.Analysis.MeasureGrowth
public import FunctionalInequalities.Analysis.Cutoff.SmoothBall
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# All-ball Morrey bounds from cutoff energy

For a density `b : Fin n → ℝⁿ → ℝ` whose weighted cutoff energy satisfies `∫ χ² Σ b_i² ≤ E0 ∫ Σ (∂_i
χ)² + E1 ∫ χ²` for every
`C¹` cutoff with values in `[0,1]` supported in `closedBall 0 (4R)`, the density `√(Σ b_i²)`
restricted to `B_R` satisfies
`∫_{B_R ∩ B_r(c)} √(Σ b_i²) ≤ K r^{n-1}` for EVERY center and EVERY radius `r > 0`, with `K = ω_n
2^n (1 + E0 n D² + E1 R²)`;
`D` is the uniform constant of the concentric cutoffs, fixed before every radius and datum. This is
hypothesis (7.51) of
Gilbarg–Trudinger (2001), Theorem 7.21, from the logarithmic energy (8.49); it is not Theorem 7.21
(John–Nirenberg).
The constant is a coarse explicit choice.

The buffered form `exists_buffered_morrey_bound_of_cutoff_energy` uses the same energy on
`closedBall 0 (4R)` and bounds
the density restricted to `B_3R`, with `K = ω_n 16^n (1 + E0 n D² + E1 R²)`; both share one per-ball
energy estimate.
`exists_centered_buffered_morrey_bound_of_cutoff_energy` is the same estimate at an arbitrary domain
center `x0`.
-/

@[expose] public section

noncomputable section
open MeasureTheory Set Metric
open scoped ContDiff ENNReal
namespace FunctionalInequalities.Analysis

/-- Pointwise Young inequality `√Q ≤ s Q + 1/(4s)` for `Q ≥ 0`, `s > 0`. -/
private theorem sqrt_le_mul_add_inv {Q s : ℝ} (hQ : 0 ≤ Q) (hs : 0 < s) :
    Real.sqrt Q ≤ s * Q + 1 / (4 * s) := by
  set t := Real.sqrt Q with ht
  have htQ : t ^ 2 = Q := Real.sq_sqrt hQ
  rw [← htQ, ← sub_nonneg]
  have he : s * t ^ 2 + 1 / (4 * s) - t = (2 * s * t - 1) ^ 2 / (4 * s) := by
    field_simp
    ring
  rw [he]
  positivity

/--
**One ball from one cutoff energy.** A `C¹` cutoff `χ ∈ [0,1]`, equal to one on `closedBall y ρ`,
supported in
`closedBall y ρ'`, with `‖Dχ‖ ≤ L` and the cutoff energy bound, gives for every `t > 0`
`∫_{B(y,ρ)} √(Σ b²) ≤ t (E0 n L² ω ρ'^n + E1 ω ρ'^n) + ω ρ^n / (4t)`. -/
private theorem lintegral_ball_sqrt_le_of_cutoff_energy {n : ℕ} {E0 E1 L ρ ρ' t : ℝ}
    {b : Fin n → EuclideanSpace ℝ (Fin n) → ℝ} {χ : EuclideanSpace ℝ (Fin n) → ℝ}
    (y : EuclideanSpace ℝ (Fin n)) (hE0 : 0 ≤ E0) (hE1 : 0 ≤ E1) (hρ : 0 < ρ) (hρ' : 0 ≤ ρ')
    (ht : 0 < t) (hχt : tsupport χ ⊆ closedBall y ρ') (h01 : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1)
    (hone : ∀ x ∈ closedBall y ρ, χ x = 1) (hder : ∀ x, ‖fderiv ℝ χ x‖ ≤ L)
    (hint :
      Integrable (fun x => χ x ^ 2 * ∑ i : Fin n, (b i x) ^ 2)
        (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hen :
      (∫ x, χ x ^ 2 * ∑ i : Fin n, (b i x) ^ 2) ≤
        E0 * (∫ x, ∑ i : Fin n, (fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ i)) ^ 2) +
          E1 * (∫ x, χ x ^ 2)) :
    (∫⁻ x in ball y ρ, ENNReal.ofReal (Real.sqrt (∑ i : Fin n, (b i x) ^ 2))) ≤
      ENNReal.ofReal
        (t *
            (E0 *
                ((n : ℝ) * L ^ 2 *
                  ((volume : Measure (EuclideanSpace ℝ (Fin n))).real (ball 0 1) * ρ' ^ n)) +
              E1 * ((volume : Measure (EuclideanSpace ℝ (Fin n))).real (ball 0 1) * ρ' ^ n)) +
          1 / (4 * t) *
            ((volume : Measure (EuclideanSpace ℝ (Fin n))).real (ball 0 1) * ρ ^ n)) := by
  classical
  set vB : ℝ := (volume : Measure (EuclideanSpace ℝ (Fin n))).real (ball 0 1) with hvBdef
  have hvB : 0 ≤ vB := measureReal_nonneg
  have hball1 : (volume : Measure (EuclideanSpace ℝ (Fin n))) (ball 0 1) ≠ ⊤ :=
    measure_ball_lt_top.ne
  have hvolc :
    (volume : Measure (EuclideanSpace ℝ (Fin n))).real (closedBall y ρ') = vB * ρ' ^ n := by
    rw [measureReal_def,
      Measure.addHaar_closedBall (volume : Measure (EuclideanSpace ℝ (Fin n))) y hρ',
      finrank_euclideanSpace_fin, ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hρ' n),
      hvBdef, measureReal_def]
    ring
  have hvolb :
    (volume : Measure (EuclideanSpace ℝ (Fin n))) (ball y ρ) = ENNReal.ofReal (vB * ρ ^ n) := by
    rw [Measure.addHaar_ball_of_pos (volume : Measure (EuclideanSpace ℝ (Fin n))) y hρ,
      finrank_euclideanSpace_fin, hvBdef, measureReal_def,
      ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hball1, mul_comm]
  set Q : EuclideanSpace ℝ (Fin n) → ℝ := fun x => ∑ i : Fin n, (b i x) ^ 2 with hQdef
  have hQ0 (x : EuclideanSpace ℝ (Fin n)) : 0 ≤ Q x := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hB0 :
    (∫ x, ∑ i : Fin n, (fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ i)) ^ 2) ≤
      (n : ℝ) * L ^ 2 * (vB * ρ' ^ n) := by
    have hpt :
      ∀ x,
        ∑ i : Fin n, (fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ i)) ^ 2 ≤
          (closedBall y ρ').indicator (fun _ => (n : ℝ) * L ^ 2) x := by
      intro x
      by_cases hx : x ∈ closedBall y ρ'
      · rw [indicator_of_mem hx]
        calc
          _ ≤ ∑ _i : Fin n, L ^ 2 :=
            Finset.sum_le_sum fun i _ => by
              have h1 : |fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ i)| ≤ L := by
                have := (fderiv ℝ χ x).le_opNorm (EuclideanSpace.basisFun (Fin n) ℝ i)
                rw [(EuclideanSpace.basisFun (Fin n) ℝ).orthonormal.1 i, mul_one,
                  Real.norm_eq_abs] at this
                exact this.trans (hder x)
              rw [← sq_abs]
              exact pow_le_pow_left₀ (abs_nonneg _) h1 2
          _ = _ := by simp
      · rw [indicator_of_notMem hx]
        have hxt : x ∉ tsupport χ := fun h => hx (hχt h)
        simp [fderiv_of_notMem_tsupport ℝ hxt]
    calc
      _ ≤ ∫ x, (closedBall y ρ').indicator (fun _ => (n : ℝ) * L ^ 2) x :=
        integral_mono_of_nonneg (ae_of_all _ fun x => Finset.sum_nonneg fun i _ => sq_nonneg _)
          ((integrableOn_const (measure_closedBall_lt_top.ne)).integrable_indicator
            measurableSet_closedBall)
          (ae_of_all _ hpt)
      _ = _ := by
        rw [integral_indicator_const _ measurableSet_closedBall, hvolc, smul_eq_mul]
        ring
  have hB1 : (∫ x, χ x ^ 2) ≤ vB * ρ' ^ n := by
    have hpt : ∀ x, χ x ^ 2 ≤ (closedBall y ρ').indicator (fun _ => (1 : ℝ)) x := by
      intro x
      by_cases hx : x ∈ closedBall y ρ'
      · rw [indicator_of_mem hx]
        have := h01 x
        nlinarith [this.1, this.2]
      · rw [indicator_of_notMem hx]
        have hxt : x ∉ tsupport χ := fun h => hx (hχt h)
        simp [image_eq_zero_of_notMem_tsupport hxt]
    calc
      _ ≤ ∫ x, (closedBall y ρ').indicator (fun _ => (1 : ℝ)) x :=
        integral_mono_of_nonneg (ae_of_all _ fun x => sq_nonneg _)
          ((integrableOn_const (measure_closedBall_lt_top.ne)).integrable_indicator
            measurableSet_closedBall)
          (ae_of_all _ hpt)
      _ = _ := by
        rw [integral_indicator_const _ measurableSet_closedBall, hvolc, smul_eq_mul, mul_one]
  have hQball :
    (∫⁻ x in ball y ρ, ENNReal.ofReal (Q x)) ≤
      ENNReal.ofReal (E0 * ((n : ℝ) * L ^ 2 * (vB * ρ' ^ n)) + E1 * (vB * ρ' ^ n)) := by
    calc
      _ = ∫⁻ x, (ball y ρ).indicator (fun x => ENNReal.ofReal (Q x)) x :=
        (lintegral_indicator measurableSet_ball _).symm
      _ ≤ ∫⁻ x, ENNReal.ofReal (χ x ^ 2 * Q x) := by
        apply lintegral_mono
        intro x
        dsimp only
        by_cases hx : x ∈ ball y ρ
        · rw [indicator_of_mem hx, hone x (ball_subset_closedBall hx)]
          simp
        · rw [indicator_of_notMem hx]
          exact zero_le
      _ = ENNReal.ofReal (∫ x, χ x ^ 2 * Q x) :=
        (ofReal_integral_eq_lintegral_ofReal hint
            (ae_of_all _ fun x => mul_nonneg (sq_nonneg _) (hQ0 x))).symm
      _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        refine hen.trans ?_
        gcongr
  have hY :
    (∫⁻ x in ball y ρ, ENNReal.ofReal (Real.sqrt (Q x))) ≤
      ENNReal.ofReal t * (∫⁻ x in ball y ρ, ENNReal.ofReal (Q x)) +
        ENNReal.ofReal (1 / (4 * t)) *
          (volume : Measure (EuclideanSpace ℝ (Fin n))) (ball y ρ) := by
    calc
      _ ≤
          ∫⁻ x in ball y ρ,
            (ENNReal.ofReal t * ENNReal.ofReal (Q x) + ENNReal.ofReal (1 / (4 * t))) := by
        apply lintegral_mono
        intro x
        dsimp only
        rw [← ENNReal.ofReal_mul ht.le, ←
          ENNReal.ofReal_add (mul_nonneg ht.le (hQ0 x)) (by positivity)]
        exact ENNReal.ofReal_le_ofReal (sqrt_le_mul_add_inv (hQ0 x) ht)
      _ = _ := by
        rw [lintegral_add_right _ measurable_const,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_const,
          Measure.restrict_apply_univ]
  refine hY.trans ?_
  rw [hvolb]
  refine (add_le_add (mul_le_mul le_rfl hQball zero_le zero_le) le_rfl).trans ?_
  have hX0 : 0 ≤ E0 * ((n : ℝ) * L ^ 2 * (vB * ρ' ^ n)) + E1 * (vB * ρ' ^ n) := by positivity
  rw [← ENNReal.ofReal_mul ht.le, ← ENNReal.ofReal_mul (by positivity), ←
    ENNReal.ofReal_add (mul_nonneg ht.le hX0) (by positivity)]

/-- **Cutoff energy gives all-ball Morrey bounds.** If the gradient density `b` satisfies the
cutoff energy bound for every `C¹` cutoff in `[0,1]` supported in `closedBall 0 (4R)`, then for
EVERY center and EVERY
positive radius `∫_{B_R ∩ B_r(c)} √(Σ b²) ≤ K r^{n-1}` with `K = ω_n 2^n (1 + E0 n D² + E1 R²)`
(`ω_n` the volume of the unit ball). -/
theorem exists_morrey_bound_of_cutoff_energy {n : ℕ} (hn : 0 < n) :
    ∃ D : ℝ, 0 < D ∧ ∀ (R E0 E1 : ℝ) (b : Fin n → EuclideanSpace ℝ (Fin n) → ℝ),
      0 < R → 0 ≤ E0 → 0 ≤ E1 →
      (∀ i : Fin n, AEStronglyMeasurable (b i) (volume : Measure (EuclideanSpace ℝ (Fin n)))) →
      (∀ i : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp (b i) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) →
      (∀ χ : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ 1 χ → HasCompactSupport χ →
        tsupport χ ⊆ closedBall 0 (4 * R) → (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) →
        Integrable (fun x => χ x ^ 2 * ∑ i : Fin n, (b i x) ^ 2)
          (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
        (∫ x, χ x ^ 2 * ∑ i : Fin n, (b i x) ^ 2) ≤
          E0 * (∫ x, ∑ i : Fin n, (fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ i)) ^ 2) +
          E1 * (∫ x, χ x ^ 2)) →
      let K := (volume : Measure (EuclideanSpace ℝ (Fin n))).real (ball 0 1) * (2 : ℝ) ^ n *
        (1 + E0 * (n : ℝ) * D ^ 2 + E1 * R ^ 2)
      ∀ c : EuclideanSpace ℝ (Fin n), ∀ r : ℝ, 0 < r →
        (∫⁻ x in ball (0 : EuclideanSpace ℝ (Fin n)) R ∩ ball c r,
          ENNReal.ofReal (Real.sqrt (∑ i : Fin n, (b i x) ^ 2))) ≤
          ENNReal.ofReal (K * r ^ ((n : ℝ) - 1)) := by
  classical
    obtain ⟨D, hD, hcut⟩ :=
      exists_smooth_concentric_cutoff_norm_fderiv_le (E := EuclideanSpace ℝ (Fin n))
    refine ⟨D, hD, ?_⟩
    intro R E0 E1 b hR hE0 hE1 _hbm _hb2 henergy K c r hr
    set vB : ℝ := (volume : Measure (EuclideanSpace ℝ (Fin n))).real (ball 0 1) with
      hvBdef
    have hvB : 0 ≤ vB :=
      measureReal_nonneg
    -- the density `√(Σ b²)` as a measure

    set Q : EuclideanSpace ℝ (Fin n) → ℝ := fun x => ∑ i : Fin n, (b i x) ^ 2 with hQdef
    let ν :=
      (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
        (fun x => ENNReal.ofReal (Real.sqrt (Q x)))
    have hn1 : (0 : ℝ) ≤ (n : ℝ) - 1 := by
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have hK : 0 ≤ K := by
      have h2 : (0 : ℝ) ≤ 2 ^ n := by positivity
      have : 0 ≤ 1 + E0 * (n : ℝ) * D ^ 2 + E1 * R ^ 2 := by positivity
      exact
        mul_nonneg (mul_nonneg hvB h2)
          this
    -- local growth for centers in B_{2R} and radii ≤ R, from one cutoff `s → 2s` per ball

    have hlocal :
      ∀ y : EuclideanSpace ℝ (Fin n),
        dist y 0 < 2 * R →
          ∀ s : ℝ,
            0 < s → s ≤ R → ν (ball y s) ≤ ENNReal.ofReal (K * s ^ ((n : ℝ) - 1)) := by
      intro y hy s hs hsR
      obtain ⟨χ, hχs, hχc, hχt, h01, hone, -, hder⟩ :=
        hcut y s (2 * s) hs.le (by linarith)
      have hgap : 2 * s - s = s := by ring
      rw [hgap] at hder
      have hχ1 : ContDiff ℝ 1 χ := hχs.of_le (by exact_mod_cast le_top)
      have hsub4 : tsupport χ ⊆ closedBall 0 (4 * R) :=
        hχt.trans (closedBall_subset_closedBall' (by linarith))
      obtain ⟨hint, hen⟩ := henergy χ hχ1 hχc hsub4 h01
      have hb :=
        lintegral_ball_sqrt_le_of_cutoff_energy y hE0 hE1 hs (by linarith : 0 ≤ 2 * s)
          hs hχt h01 hone hder hint hen
      have hνball : ν (ball y s) = ∫⁻ x in ball y s, ENNReal.ofReal (Real.sqrt (Q x)) :=
        withDensity_apply _ measurableSet_ball
      rw [hνball]
      refine hb.trans (ENNReal.ofReal_le_ofReal ?_)
      rw [← hvBdef]
      set X :=
        E0 * ((n : ℝ) * (D / s) ^ 2 * (vB * (2 * s) ^ n)) + E1 * (vB * (2 * s) ^ n) with
        hX
      have hrp : s ^ ((n : ℝ) - 1) = s ^ n / s := by
        rw [Real.rpow_sub_one hs.ne', Real.rpow_natCast]
      rw [hrp]
      have ht : 0 ≤ s ^ n := pow_nonneg hs.le n
      have hp : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
      have hRs : 0 ≤ R ^ 2 - s ^ 2 := by nlinarith
      have hdiff :
        K * (s ^ n / s) - (s * X + 1 / (4 * s) * (vB * s ^ n)) =
          vB * s ^ n * ((2 ^ n - 1 / 4) + 2 ^ n * E1 * (R ^ 2 - s ^ 2)) / s := by
        simp only [hX, K, mul_pow]
        field_simp
        ring
      have hnn :
        0 ≤ vB * s ^ n * ((2 ^ n - 1 / 4) + 2 ^ n * E1 * (R ^ 2 - s ^ 2)) / s := by
        apply div_nonneg _ hs.le
        apply mul_nonneg (mul_nonneg hvB ht)
        have : 0 ≤ 2 ^ n * E1 * (R ^ 2 - s ^ 2) := by positivity
        linarith
      linarith
    -- all centers and all radii for the measure restricted to B_R

    have hall := restrict_ball_growth_of_local_ball_growth ν 0 hR hK hn1 hlocal c r hr
    rw [Measure.restrict_apply measurableSet_ball,
      withDensity_apply _ (measurableSet_ball.inter measurableSet_ball),
      inter_comm] at hall
    exact hall

/-- **Buffered all-ball Morrey bounds on `B_3R`.** If the gradient density `b` satisfies the cutoff
energy bound for
every `C¹` cutoff in `[0,1]` supported in `closedBall 0 (4R)`, then for EVERY center and EVERY
positive radius
`∫_{B_3R ∩ B_r(c)} √(Σ b²) ≤ K r^{n-1}` with `K = ω_n 16^n (1 + E0 n D² + E1 R²)`. Small balls (`r ≤
R/4`, centers
within `13R/4`) use cutoffs `r → 2r` inside `B(0, 15R/4)`; the total mass of `B_3R` uses the cutoff
`3R → 4R`. -/
theorem exists_buffered_morrey_bound_of_cutoff_energy {n : ℕ} (hn : 0 < n) :
    ∃ D : ℝ, 0 < D ∧ ∀ (R E0 E1 : ℝ) (b : Fin n → EuclideanSpace ℝ (Fin n) → ℝ),
      0 < R → 0 ≤ E0 → 0 ≤ E1 →
      (∀ i : Fin n, AEStronglyMeasurable (b i) (volume : Measure (EuclideanSpace ℝ (Fin n)))) →
      (∀ i : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp (b i) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) →
      (∀ χ : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ 1 χ → HasCompactSupport χ →
        tsupport χ ⊆ closedBall 0 (4 * R) → (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) →
        Integrable (fun x => χ x ^ 2 * ∑ i : Fin n, (b i x) ^ 2)
          (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
        (∫ x, χ x ^ 2 * ∑ i : Fin n, (b i x) ^ 2) ≤
          E0 * (∫ x, ∑ i : Fin n, (fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ i)) ^ 2) +
          E1 * (∫ x, χ x ^ 2)) →
      let K := (volume : Measure (EuclideanSpace ℝ (Fin n))).real (ball 0 1) * (16 : ℝ) ^ n *
        (1 + E0 * (n : ℝ) * D ^ 2 + E1 * R ^ 2)
      ∀ c : EuclideanSpace ℝ (Fin n), ∀ r : ℝ, 0 < r →
        (∫⁻ x in ball (0 : EuclideanSpace ℝ (Fin n)) (3 * R) ∩ ball c r,
          ENNReal.ofReal (Real.sqrt (∑ i : Fin n, (b i x) ^ 2))) ≤
          ENNReal.ofReal (K * r ^ ((n : ℝ) - 1)) := by
  classical
  obtain ⟨D, hD, hcut⟩ :=
    exists_smooth_concentric_cutoff_norm_fderiv_le (E := EuclideanSpace ℝ (Fin n))
  refine ⟨D, hD, ?_⟩
  intro R E0 E1 b hR hE0 hE1 _hbm _hb2 henergy K c r hr
  set vB : ℝ := (volume : Measure (EuclideanSpace ℝ (Fin n))).real (ball 0 1) with hvBdef
  have hvB : 0 ≤ vB := measureReal_nonneg
  set Q : EuclideanSpace ℝ (Fin n) → ℝ := fun x => ∑ i : Fin n, (b i x) ^ 2 with hQdef
  let ν :=
    (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
      (fun x => ENNReal.ofReal (Real.sqrt (Q x)))
  have hn1 : (0 : ℝ) ≤ (n : ℝ) - 1 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hM0 : 0 ≤ E0 * (n : ℝ) * D ^ 2 + E1 * R ^ 2 := by positivity
  have h1_2 : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  have h2_16 : (2 : ℝ) ^ n ≤ 16 ^ n := pow_le_pow_left₀ (by norm_num) (by norm_num) n
  have h3_4 : (3 : ℝ) ^ n ≤ 4 ^ n := pow_le_pow_left₀ (by norm_num) (by norm_num) n
  have h16 : (16 : ℝ) ^ n = 4 ^ n * 4 ^ n := by rw [← mul_pow]; norm_num
  have hK : 0 ≤ K := by
    have : 0 ≤ 1 + E0 * (n : ℝ) * D ^ 2 + E1 * R ^ 2 := by positivity
    exact mul_nonneg (mul_nonneg hvB (by positivity)) this
  -- small balls: centers within `13R/4`, radii `≤ R/4`, cutoffs `s → 2s` supported in `B(0, 15R/4)
  -- ⊆ B(0, 4R)`
  have hgrowth :
    ∀ y : EuclideanSpace ℝ (Fin n),
      dist y 0 < 3 * R + R / 4 →
        ∀ s : ℝ,
          0 < s → s ≤ R / 4 → ν (ball y s) ≤ ENNReal.ofReal (K * s ^ ((n : ℝ) - 1)) := by
    intro y hy s hs hsR
    obtain ⟨χ, hχs, hχc, hχt, h01, hone, -, hder⟩ :=
      hcut y s (2 * s) hs.le (by linarith)
    have hgap : 2 * s - s = s := by ring
    rw [hgap] at hder
    have hχ1 : ContDiff ℝ 1 χ := hχs.of_le (by exact_mod_cast le_top)
    have hsub4 : tsupport χ ⊆ closedBall 0 (4 * R) :=
      hχt.trans (closedBall_subset_closedBall' (by linarith))
    obtain ⟨hint, hen⟩ := henergy χ hχ1 hχc hsub4 h01
    have hb :=
      lintegral_ball_sqrt_le_of_cutoff_energy y hE0 hE1 hs (by linarith : 0 ≤ 2 * s) hs
        hχt h01 hone hder hint hen
    have hνball : ν (ball y s) = ∫⁻ x in ball y s, ENNReal.ofReal (Real.sqrt (Q x)) :=
      withDensity_apply _ measurableSet_ball
    rw [hνball]
    refine hb.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [← hvBdef]
    have hrp : s ^ ((n : ℝ) - 1) = s ^ n / s := by
      rw [Real.rpow_sub_one hs.ne', Real.rpow_natCast]
    rw [hrp]
    have ht : 0 ≤ s ^ n := pow_nonneg hs.le n
    have hRs : 0 ≤ 16 ^ n * R ^ 2 - 2 ^ n * s ^ 2 := by
      have hs2 : s ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ hs.le (by linarith) 2
      nlinarith [mul_le_mul h2_16 hs2 (sq_nonneg s) (by positivity : (0 : ℝ) ≤ 16 ^ n)]
    have hdiff :
      K * (s ^ n / s) -
          (s *
              (E0 * ((n : ℝ) * (D / s) ^ 2 * (vB * (2 * s) ^ n)) +
                E1 * (vB * (2 * s) ^ n)) +
            1 / (4 * s) * (vB * s ^ n)) =
        vB * s ^ n *
            ((16 ^ n - 1 / 4) + (16 ^ n - 2 ^ n) * (E0 * (n : ℝ) * D ^ 2) +
              E1 * (16 ^ n * R ^ 2 - 2 ^ n * s ^ 2)) /
          s := by
      simp only [K, mul_pow]
      field_simp
      ring
    have hnn :
      0 ≤
        vB * s ^ n *
            ((16 ^ n - 1 / 4) + (16 ^ n - 2 ^ n) * (E0 * (n : ℝ) * D ^ 2) +
              E1 * (16 ^ n * R ^ 2 - 2 ^ n * s ^ 2)) /
          s := by
      apply div_nonneg _ hs.le
      apply mul_nonneg (mul_nonneg hvB ht)
      have h1 : 0 ≤ (16 ^ n - 2 ^ n) * (E0 * (n : ℝ) * D ^ 2) :=
        mul_nonneg (by linarith) (by positivity)
      have h2 : 0 ≤ E1 * (16 ^ n * R ^ 2 - 2 ^ n * s ^ 2) := mul_nonneg hE1 hRs
      linarith
    linarith
  -- the total mass of `B_3R` from the cutoff `3R → 4R`, Young at `R`
  have hmass : ν (ball 0 (3 * R)) ≤ ENNReal.ofReal (K * (R / 4) ^ ((n : ℝ) - 1)) := by
    obtain ⟨χ, hχs, hχc, hχt, h01, hone, -, hder⟩ :=
      hcut 0 (3 * R) (4 * R) (by linarith) (by linarith)
    have hgap : 4 * R - 3 * R = R := by ring
    rw [hgap] at hder
    have hχ1 : ContDiff ℝ 1 χ := hχs.of_le (by exact_mod_cast le_top)
    obtain ⟨hint, hen⟩ := henergy χ hχ1 hχc hχt h01
    have hb :=
      lintegral_ball_sqrt_le_of_cutoff_energy 0 hE0 hE1 (by linarith : 0 < 3 * R)
        (by linarith : 0 ≤ 4 * R) hR hχt h01 hone hder hint hen
    have hνball :
      ν (ball 0 (3 * R)) = ∫⁻ x in ball 0 (3 * R), ENNReal.ofReal (Real.sqrt (Q x)) :=
      withDensity_apply _ measurableSet_ball
    rw [hνball]
    refine hb.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [← hvBdef]
    have hR4 : 0 < R / 4 := by linarith
    have hrp : (R / 4) ^ ((n : ℝ) - 1) = (R / 4) ^ n / (R / 4) := by
      rw [Real.rpow_sub_one hR4.ne', Real.rpow_natCast]
    rw [hrp]
    have ht : 0 ≤ R ^ n := pow_nonneg hR.le n
    have h4n : (0 : ℝ) < 4 ^ n := by positivity
    have hdiff :
      K * ((R / 4) ^ n / (R / 4)) -
          (R *
              (E0 * ((n : ℝ) * (D / R) ^ 2 * (vB * (4 * R) ^ n)) +
                E1 * (vB * (4 * R) ^ n)) +
            1 / (4 * R) * (vB * (3 * R) ^ n)) =
        vB * R ^ n *
            (4 * 4 ^ n - 3 ^ n / 4 + 3 * 4 ^ n * (E0 * (n : ℝ) * D ^ 2 + E1 * R ^ 2)) /
          R := by
      simp only [K, mul_pow, div_pow, h16]
      field_simp
      ring
    have hnn :
      0 ≤
        vB * R ^ n *
            (4 * 4 ^ n - 3 ^ n / 4 + 3 * 4 ^ n * (E0 * (n : ℝ) * D ^ 2 + E1 * R ^ 2)) /
          R := by
      apply div_nonneg _ hR.le
      apply mul_nonneg (mul_nonneg hvB ht)
      have : 0 ≤ 3 * 4 ^ n * (E0 * (n : ℝ) * D ^ 2 + E1 * R ^ 2) := by positivity
      linarith
    linarith
  -- every center and every radius for the measure restricted to `B_3R`
  have hall := restrict_ball_growth_of_small_ball_growth_and_mass ν 0 (A := 3 * R)
    (by linarith : (0 : ℝ) < R / 4) hK hn1 hmass hgrowth c r hr
  rw [Measure.restrict_apply measurableSet_ball,
    withDensity_apply _ (measurableSet_ball.inter measurableSet_ball),
    inter_comm] at hall
  exact hall

/-- **Centered buffered Morrey bound.** One `D`, fixed before every domain center `x0`, radius and
datum: cutoff
energy for every `C¹` cutoff in `[0,1]` supported in `closedBall x0 (4R)` gives `∫_{B(x0,3R) ∩
B_r(c)} √(Σ b²) ≤ K r^{n-1}`
for every `c` and `r > 0`, with `K = ω_n 16^n (1 + E0 n D² + E1 R²)`. -/
theorem exists_centered_buffered_morrey_bound_of_cutoff_energy {n : ℕ} (hn : 0 < n) :
    ∃ D : ℝ, 0 < D ∧ ∀ (x0 : EuclideanSpace ℝ (Fin n)) (R E0 E1 : ℝ) (b : Fin n → EuclideanSpace ℝ
      (Fin n) → ℝ),
      0 < R → 0 ≤ E0 → 0 ≤ E1 →
      (∀ i : Fin n, AEStronglyMeasurable (b i) (volume : Measure (EuclideanSpace ℝ (Fin n)))) →
      (∀ i : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp (b i) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) →
      (∀ χ : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ 1 χ → HasCompactSupport χ →
        tsupport χ ⊆ closedBall x0 (4 * R) → (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) →
        Integrable (fun x => χ x ^ 2 * ∑ i : Fin n, (b i x) ^ 2)
          (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
        (∫ x, χ x ^ 2 * ∑ i : Fin n, (b i x) ^ 2) ≤
          E0 * (∫ x, ∑ i : Fin n, (fderiv ℝ χ x (EuclideanSpace.basisFun (Fin n) ℝ i)) ^ 2) +
          E1 * (∫ x, χ x ^ 2)) →
      let K := (volume : Measure (EuclideanSpace ℝ (Fin n))).real (ball 0 1) * (16 : ℝ) ^ n *
        (1 + E0 * (n : ℝ) * D ^ 2 + E1 * R ^ 2)
      ∀ c : EuclideanSpace ℝ (Fin n), ∀ r : ℝ, 0 < r →
        (∫⁻ x in ball x0 (3 * R) ∩ ball c r,
          ENNReal.ofReal (Real.sqrt (∑ i : Fin n, (b i x) ^ 2))) ≤
          ENNReal.ofReal (K * r ^ ((n : ℝ) - 1)) := by
  classical
  obtain ⟨D, hD, hcut⟩ :=
    exists_smooth_concentric_cutoff_norm_fderiv_le (E := EuclideanSpace ℝ (Fin n))
  refine ⟨D, hD, ?_⟩
  intro x0 R E0 E1 b hR hE0 hE1 _hbm _hb2 henergy K c r hr
  set vB : ℝ := (volume : Measure (EuclideanSpace ℝ (Fin n))).real (ball 0 1) with hvBdef
  have hvB : 0 ≤ vB := measureReal_nonneg
  set Q : EuclideanSpace ℝ (Fin n) → ℝ := fun x => ∑ i : Fin n, (b i x) ^ 2 with hQdef
  let ν :=
    (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
      (fun x => ENNReal.ofReal (Real.sqrt (Q x)))
  have hn1 : (0 : ℝ) ≤ (n : ℝ) - 1 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hM0 : 0 ≤ E0 * (n : ℝ) * D ^ 2 + E1 * R ^ 2 := by positivity
  have h1_2 : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  have h2_16 : (2 : ℝ) ^ n ≤ 16 ^ n := pow_le_pow_left₀ (by norm_num) (by norm_num) n
  have h3_4 : (3 : ℝ) ^ n ≤ 4 ^ n := pow_le_pow_left₀ (by norm_num) (by norm_num) n
  have h16 : (16 : ℝ) ^ n = 4 ^ n * 4 ^ n := by rw [← mul_pow]; norm_num
  have hK : 0 ≤ K := by
    have : 0 ≤ 1 + E0 * (n : ℝ) * D ^ 2 + E1 * R ^ 2 := by positivity
    exact mul_nonneg (mul_nonneg hvB (by positivity)) this
  -- small balls: centers within `13R/4`, radii `≤ R/4`, cutoffs `s → 2s` supported in `B(0, 15R/4)
  -- ⊆ B(0, 4R)`
  have hgrowth :
    ∀ y : EuclideanSpace ℝ (Fin n),
      dist y x0 < 3 * R + R / 4 →
        ∀ s : ℝ,
          0 < s → s ≤ R / 4 → ν (ball y s) ≤ ENNReal.ofReal (K * s ^ ((n : ℝ) - 1)) := by
    intro y hy s hs hsR
    obtain ⟨χ, hχs, hχc, hχt, h01, hone, -, hder⟩ :=
      hcut y s (2 * s) hs.le (by linarith)
    have hgap : 2 * s - s = s := by ring
    rw [hgap] at hder
    have hχ1 : ContDiff ℝ 1 χ := hχs.of_le (by exact_mod_cast le_top)
    have hsub4 : tsupport χ ⊆ closedBall x0 (4 * R) :=
      hχt.trans (closedBall_subset_closedBall' (by linarith))
    obtain ⟨hint, hen⟩ := henergy χ hχ1 hχc hsub4 h01
    have hb :=
      lintegral_ball_sqrt_le_of_cutoff_energy y hE0 hE1 hs (by linarith : 0 ≤ 2 * s) hs
        hχt h01 hone hder hint hen
    have hνball : ν (ball y s) = ∫⁻ x in ball y s, ENNReal.ofReal (Real.sqrt (Q x)) :=
      withDensity_apply _ measurableSet_ball
    rw [hνball]
    refine hb.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [← hvBdef]
    have hrp : s ^ ((n : ℝ) - 1) = s ^ n / s := by
      rw [Real.rpow_sub_one hs.ne', Real.rpow_natCast]
    rw [hrp]
    have ht : 0 ≤ s ^ n := pow_nonneg hs.le n
    have hRs : 0 ≤ 16 ^ n * R ^ 2 - 2 ^ n * s ^ 2 := by
      have hs2 : s ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ hs.le (by linarith) 2
      nlinarith [mul_le_mul h2_16 hs2 (sq_nonneg s) (by positivity : (0 : ℝ) ≤ 16 ^ n)]
    have hdiff :
      K * (s ^ n / s) -
          (s *
              (E0 * ((n : ℝ) * (D / s) ^ 2 * (vB * (2 * s) ^ n)) +
                E1 * (vB * (2 * s) ^ n)) +
            1 / (4 * s) * (vB * s ^ n)) =
        vB * s ^ n *
            ((16 ^ n - 1 / 4) + (16 ^ n - 2 ^ n) * (E0 * (n : ℝ) * D ^ 2) +
              E1 * (16 ^ n * R ^ 2 - 2 ^ n * s ^ 2)) /
          s := by
      simp only [K, mul_pow]
      field_simp
      ring
    have hnn :
      0 ≤
        vB * s ^ n *
            ((16 ^ n - 1 / 4) + (16 ^ n - 2 ^ n) * (E0 * (n : ℝ) * D ^ 2) +
              E1 * (16 ^ n * R ^ 2 - 2 ^ n * s ^ 2)) /
          s := by
      apply div_nonneg _ hs.le
      apply mul_nonneg (mul_nonneg hvB ht)
      have h1 : 0 ≤ (16 ^ n - 2 ^ n) * (E0 * (n : ℝ) * D ^ 2) :=
        mul_nonneg (by linarith) (by positivity)
      have h2 : 0 ≤ E1 * (16 ^ n * R ^ 2 - 2 ^ n * s ^ 2) := mul_nonneg hE1 hRs
      linarith
    linarith
  -- the total mass of `B_3R` from the cutoff `3R → 4R`, Young at `R`
  have hmass : ν (ball x0 (3 * R)) ≤ ENNReal.ofReal (K * (R / 4) ^ ((n : ℝ) - 1)) := by
    obtain ⟨χ, hχs, hχc, hχt, h01, hone, -, hder⟩ :=
      hcut x0 (3 * R) (4 * R) (by linarith) (by linarith)
    have hgap : 4 * R - 3 * R = R := by ring
    rw [hgap] at hder
    have hχ1 : ContDiff ℝ 1 χ := hχs.of_le (by exact_mod_cast le_top)
    obtain ⟨hint, hen⟩ := henergy χ hχ1 hχc hχt h01
    have hb :=
      lintegral_ball_sqrt_le_of_cutoff_energy x0 hE0 hE1 (by linarith : 0 < 3 * R)
        (by linarith : 0 ≤ 4 * R) hR hχt h01 hone hder hint hen
    have hνball :
      ν (ball x0 (3 * R)) = ∫⁻ x in ball x0 (3 * R), ENNReal.ofReal (Real.sqrt (Q x)) :=
      withDensity_apply _ measurableSet_ball
    rw [hνball]
    refine hb.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [← hvBdef]
    have hR4 : 0 < R / 4 := by linarith
    have hrp : (R / 4) ^ ((n : ℝ) - 1) = (R / 4) ^ n / (R / 4) := by
      rw [Real.rpow_sub_one hR4.ne', Real.rpow_natCast]
    rw [hrp]
    have ht : 0 ≤ R ^ n := pow_nonneg hR.le n
    have h4n : (0 : ℝ) < 4 ^ n := by positivity
    have hdiff :
      K * ((R / 4) ^ n / (R / 4)) -
          (R *
              (E0 * ((n : ℝ) * (D / R) ^ 2 * (vB * (4 * R) ^ n)) +
                E1 * (vB * (4 * R) ^ n)) +
            1 / (4 * R) * (vB * (3 * R) ^ n)) =
        vB * R ^ n *
            (4 * 4 ^ n - 3 ^ n / 4 + 3 * 4 ^ n * (E0 * (n : ℝ) * D ^ 2 + E1 * R ^ 2)) /
          R := by
      simp only [K, mul_pow, div_pow, h16]
      field_simp
      ring
    have hnn :
      0 ≤
        vB * R ^ n *
            (4 * 4 ^ n - 3 ^ n / 4 + 3 * 4 ^ n * (E0 * (n : ℝ) * D ^ 2 + E1 * R ^ 2)) /
          R := by
      apply div_nonneg _ hR.le
      apply mul_nonneg (mul_nonneg hvB ht)
      have : 0 ≤ 3 * 4 ^ n * (E0 * (n : ℝ) * D ^ 2 + E1 * R ^ 2) := by positivity
      linarith
    linarith
  -- every center and every radius for the measure restricted to `B_3R`
  have hall := restrict_ball_growth_of_small_ball_growth_and_mass ν x0 (A := 3 * R)
    (by linarith : (0 : ℝ) < R / 4) hK hn1 hmass hgrowth c r hr
  rw [Measure.restrict_apply measurableSet_ball,
    withDensity_apply _ (measurableSet_ball.inter measurableSet_ball),
    inter_comm] at hall
  exact hall

end FunctionalInequalities.Analysis
