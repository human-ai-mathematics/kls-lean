import FunctionalInequalities.Analysis.Vector.RankDeficient.TangentialLipschitz
import FunctionalInequalities.Analysis.Vector.RankDeficient.RegularFibreFinite
import FunctionalInequalities.Analysis.Vector.RankDeficient.TargetSplitFubini
import FunctionalInequalities.Analysis.Vector.Slice.Critical
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.Prod

/-! # The per-stratum slicing

**Obligation `R7`** of the rank-deficient route recorded in
`research/decisions/2026-09-17-rank-deficient-route.md`, **proved** here as
`exists_nhds_ae_hausdorffMeasure_stratum_inter_levelSet_eq_zero`: around every point of the rank-`r`
stratum there is a neighbourhood in which almost every level meets the stratum in an `ℋ^k`-null set.
With `R1`–`R6` that is seven of the route's obligations.  **`R0` is still open**: it needs `R8`, the
localization of this statement to the whole stratum, and the finite union over `r < m`.  Nothing
here is a coarea formula in a new case, a slicing statement about the full critical set, or a Sard
theorem.

**The argument.**  Near a point of the stratum let `K` be the range of the differential there and
`P`, `Q` the orthogonal projections onto `K` and `Kᗮ`.

* `exists_stratum_local_data` — the **local package**.  There is an open neighbourhood with compact
  closure on which `P ∘ u` is a submersion, together with **one** constant `c` such that for
  **every** stratum point `y` in it, every `ε` and every set on which `u` is `ε`-approximated by
  `fderiv ℝ u y`, the projected map `Q ∘ u` is `c ε`-Lipschitz along every fibre of `P ∘ u`.  The
  uniformity of `c` over `y` is the difficulty, since `R4`'s constant depends on the piece's linear
  model; it comes from `R2`, the **locally uniform** half of `R3`, and a bound on `‖fderiv ℝ u‖`.
* `lintegral_split_target` — an integral over the target is the iterated integral over an orthogonal
  splitting of it, by `LinearIsometryEquiv.measurePreserving`, `WithLp.volume_preserving_toLp` and
  Tonelli.  This is the integral form of what `R6` does for null sets.
* `lintegral_hausdorffMeasure_stratum_le` — the **per-scale bound**.  Run Mathlib's approximating
  partition on `u` **itself**, so one partition serves both components; on each piece the local
  package makes `Q ∘ u` small-Lipschitz along fibres; the Eilenberg bound of
  `Analysis/Vector/Slice/Hausdorff.lean` applies **inside a fibre** at exponent `k` with a target of
  dimension `m − r`, where `k + (m − r) = n − r` is exactly right; integrating over the fibre
  parameter against the **proved** regular coarea formula for `P ∘ u` turns the fibre measures into
  an ordinary integral of the coarea Jacobian, and `lintegral_split_target` reads the result as an
  integral over the target.  The constant does **not** depend on `ε`.
* `exists_nhds_ae_hausdorffMeasure_stratum_inter_levelSet_eq_zero` — the limit `ε → 0`.  The
  right-hand factor is finite because the closure of the neighbourhood is compact, and the exponent
  `m − r` is positive exactly because `r < m`, so the integral over the target vanishes and the
  integrand vanishes almost everywhere.

**Where the wrong exponent of the one-step method is repaired** is the fibre: applying the Eilenberg
bound in the ambient space would force the exponent `k + r`, and forcing it back to `k` would make
the right-hand side `μH[n − r]` of a set of positive Lebesgue measure, which is `∞`.  Inside a fibre
the same bound is used at `k` and the right-hand side is the fibre's own finite `ℋ^{n−r}` measure.
-/
noncomputable section
open MeasureTheory Module Set Filter Topology
open scoped ENNReal NNReal

namespace FunctionalInequalities.Analysis

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]

/-- The range of the differential of `u` at `x₀`, as a submodule of the target. -/
abbrev tangentRange (u : V → W) (x₀ : V) : Submodule ℝ W :=
  LinearMap.range ((fderiv ℝ u x₀).toLinearMap)

/-- The rank-`r` stratum of the differential of `u`. -/
abbrev stratum (u : V → W) (r : ℕ) : Set V :=
  {x : V | (fderiv ℝ u x).toLinearMap.rank = (r : Cardinal)}

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W] in
theorem fderiv_clm_comp {u : V → W} (hu : ContDiff ℝ 1 u) {W₁ : Type*} [NormedAddCommGroup W₁]
    [NormedSpace ℝ W₁] (P : W →L[ℝ] W₁) (x : V) :
    fderiv ℝ (fun y => P (u y)) x = P.comp (fderiv ℝ u x) :=
  (P.hasFDerivAt.comp x ((hu.differentiable one_ne_zero).differentiableAt.hasFDerivAt)).fderiv

omit [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ W] [MeasurableSpace W]
  [BorelSpace W] in
theorem surjective_proj_comp (u : V → W) (x₀ : V) :
    Function.Surjective ((tangentRange u x₀).orthogonalProjectionOnto.comp (fderiv ℝ u x₀)) := by
  intro y
  obtain ⟨z, hz⟩ := (LinearMap.mem_range).1 y.2
  refine ⟨z, ?_⟩
  rw [ContinuousLinearMap.comp_apply, show (fderiv ℝ u x₀) z = (y : W) from hz]
  exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self y

omit [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ W] [MeasurableSpace W]
  [BorelSpace W] in
theorem finrank_tangentRange_eq {u : V → W} {r : ℕ} {x₀ x : V} (hx₀ : x₀ ∈ stratum u r)
    (hx : x ∈ stratum u r) :
    finrank ℝ (tangentRange u x₀) = finrank ℝ (LinearMap.range ((fderiv ℝ u x).toLinearMap)) := by
  have h0 := rank_toLinearMap_eq (fderiv ℝ u x₀)
  have h1 := rank_toLinearMap_eq (fderiv ℝ u x)
  have e0 : (finrank ℝ (tangentRange u x₀) : Cardinal) = (r : Cardinal) := by
    rw [← h0]; exact hx₀
  have e1 : (finrank ℝ (LinearMap.range ((fderiv ℝ u x).toLinearMap)) : Cardinal) = (r : Cardinal) := by
    rw [← h1]; exact hx
  exact_mod_cast e0.trans e1.symm

omit [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ W] [MeasurableSpace W]
  [BorelSpace W] in
/-- **The local package at a point of the rank stratum.** -/
theorem exists_stratum_local_data {u : V → W} (hu : ContDiff ℝ 1 u) {r : ℕ} {x₀ : V}
    (hx₀ : x₀ ∈ stratum u r) :
    ∃ (U : Set V) (c : ℝ≥0), IsOpen U ∧ x₀ ∈ U ∧ IsCompact (closure U) ∧
      (∀ x ∈ closure U, coareaJacobian
        (fderiv ℝ (fun y => (tangentRange u x₀).orthogonalProjectionOnto (u y)) x) ≠ 0) ∧
      (∀ y ∈ stratum u r ∩ U, ∀ (ε : ℝ≥0) (S : Set V) (s : tangentRange u x₀),
        ApproximatesLinearOn u (fderiv ℝ u y) S ε →
          LipschitzOnWith (c * ε)
            (fun x => (tangentRange u x₀)ᗮ.orthogonalProjectionOnto (u x))
            (S ∩ {x : V | (tangentRange u x₀).orthogonalProjectionOnto (u x) = s})) := by
  classical
  set K : Submodule ℝ W := tangentRange u x₀ with hKdef
  set P : W →L[ℝ] K := K.orthogonalProjectionOnto with hP
  set Q : W →L[ℝ] (Kᗮ : Submodule ℝ W) := Kᗮ.orthogonalProjectionOnto with hQ
  set v : V → K := fun y => P (u y) with hv
  have hvC : ContDiff ℝ 1 v := P.contDiff.comp hu
  have hdv : ∀ x, fderiv ℝ v x = P.comp (fderiv ℝ u x) := fderiv_clm_comp hu P
  have hsurj₀ : Function.Surjective (fderiv ℝ v x₀) := by
    rw [hdv]; exact surjective_proj_comp u x₀
  set O : Set V := {x : V | coareaJacobian (fderiv ℝ v x) ≠ 0} with hO
  have hOopen : IsOpen O := isOpen_coareaJacobian_ne_zero hvC
  have hx₀O : x₀ ∈ O := (coareaJacobian_ne_zero_iff _).2 hsurj₀
  obtain ⟨U₁, hU₁mem, C, M, hU₁O, hU₁bound⟩ :=
    exists_nhds_uniform_rightInverse_bound hOopen hx₀O hvC.contDiffOn hsurj₀
  -- a separate bound on the full differential
  set M₂ : ℝ≥0 := ‖fderiv ℝ u x₀‖₊ + 1 with hM₂
  have hducont : ContinuousAt (fun x => ‖fderiv ℝ u x‖) x₀ :=
    continuous_norm.continuousAt.comp (hu.continuous_fderiv one_ne_zero).continuousAt
  have hnear : ∀ᶠ x in 𝓝 x₀, ‖fderiv ℝ u x‖ < ‖fderiv ℝ u x₀‖ + 1 :=
    hducont.tendsto.eventually_lt_const (lt_add_one _)
  have hmem : U₁ ∩ {x : V | ‖fderiv ℝ u x‖ < ‖fderiv ℝ u x₀‖ + 1} ∈ 𝓝 x₀ :=
    Filter.inter_mem hU₁mem hnear
  obtain ⟨ρ, hρpos, hballsub⟩ := Metric.mem_nhds_iff.1 hmem
  refine ⟨Metric.ball x₀ (ρ / 2), 1 + M₂ * C, Metric.isOpen_ball,
    Metric.mem_ball_self (by positivity),
    (isCompact_closedBall x₀ (ρ / 2)).of_isClosed_subset isClosed_closure
      (closure_minimal Metric.ball_subset_closedBall Metric.isClosed_closedBall), ?_, ?_⟩
  · intro x hx
    have hx' : x ∈ Metric.ball x₀ ρ := by
      have := Metric.closure_ball_subset_closedBall hx
      exact Metric.mem_ball.2 (lt_of_le_of_lt (Metric.mem_closedBall.1 this) (by linarith))
    exact hU₁O (hballsub hx').1
  · rintro y ⟨hyS, hyU⟩ ε S s hf
    have hyρ : y ∈ Metric.ball x₀ ρ :=
      Metric.mem_ball.2 (lt_trans (Metric.mem_ball.1 hyU) (by linarith))
    obtain ⟨hyU₁, hyN⟩ := hballsub hyρ
    obtain ⟨hyM, hyinv⟩ := hU₁bound y hyU₁
    have hyO : y ∈ O := hU₁O hyU₁
    have hsurjy : Function.Surjective (P.comp (fderiv ℝ u y)) := by
      have := (coareaJacobian_ne_zero_iff (fderiv ℝ v y)).1 hyO
      rwa [hdv y] at this
    have hrank : finrank ℝ K = finrank ℝ (LinearMap.range ((fderiv ℝ u y).toLinearMap)) :=
      finrank_tangentRange_eq hx₀ hyS
    have hker : ∀ z : V, P ((fderiv ℝ u y) z) = 0 → (fderiv ℝ u y) z = 0 :=
      fun z hz => apply_eq_zero_of_comp_apply_eq_zero (fderiv ℝ u y) P hsurjy hrank z hz
    have hinv : ∀ z : V, ∃ w : V, P ((fderiv ℝ u y) w) = 0 ∧
        ‖z - w‖ ≤ C * ‖P ((fderiv ℝ u y) z)‖ := by
      intro z
      obtain ⟨w, hw1, hw2⟩ := hyinv z
      rw [hdv y] at hw1 hw2
      exact ⟨w, hw1, hw2⟩
    have hlip := lipschitzOnWith_of_ker_bound (fderiv ℝ u y) P Q C hker hinv ε u S s hf
    refine hlip.weaken ?_
    have hPle : ‖P‖₊ ≤ 1 := by
      rw [← NNReal.coe_le_coe]; simpa using Submodule.orthogonalProjectionOnto_norm_le K
    have hQle : ‖Q‖₊ ≤ 1 := by
      rw [← NNReal.coe_le_coe]; simpa using Submodule.orthogonalProjectionOnto_norm_le Kᗮ
    have hAle : ‖fderiv ℝ u y‖₊ ≤ M₂ := by
      rw [← NNReal.coe_le_coe]
      push_cast
      exact hyN.le
    have hfac : ‖Q‖₊ * (1 + ‖fderiv ℝ u y‖₊ * C * ‖P‖₊) ≤ 1 + M₂ * C := by
      calc ‖Q‖₊ * (1 + ‖fderiv ℝ u y‖₊ * C * ‖P‖₊)
          ≤ 1 * (1 + M₂ * C * 1) := by gcongr
        _ = 1 + M₂ * C := by ring
    gcongr


section TargetSplit

variable {W₁ W₂ : Type*}
  [NormedAddCommGroup W₁] [InnerProductSpace ℝ W₁] [FiniteDimensional ℝ W₁]
  [MeasurableSpace W₁] [BorelSpace W₁]
  [NormedAddCommGroup W₂] [InnerProductSpace ℝ W₂] [FiniteDimensional ℝ W₂]
  [MeasurableSpace W₂] [BorelSpace W₂]

/-- **The integral form of the target splitting.**  An integral over the target is the iterated
integral over an orthogonal splitting of it.  This is what `R6` does for null sets, in the form the
per-scale estimate has to be integrated against: the inner integral is over the directions the
second slicing uses, the outer one over the fibre parameter of the regular component. -/
theorem lintegral_split_target (e : W ≃ₗᵢ[ℝ] WithLp 2 (W₁ × W₂)) {f : W → ℝ≥0∞}
    (hf : AEMeasurable f (volume : Measure W)) :
    ∫⁻ t, f t ∂(volume : Measure W)
      = ∫⁻ s, ∫⁻ τ, f (e.symm (WithLp.toLp 2 (s, τ))) ∂(volume : Measure W₂)
          ∂(volume : Measure W₁) := by
  have h1 := (e.symm.measurePreserving).lintegral_comp_emb
    (e.symm.toHomeomorph.measurableEmbedding) f
  have h2 := (WithLp.volume_preserving_toLp W₁ W₂).lintegral_comp_emb
    (MeasurableEquiv.toLp 2 (W₁ × W₂)).measurableEmbedding (fun q => f (e.symm q))
  have hmp : MeasurePreserving (fun p : W₁ × W₂ => e.symm (WithLp.toLp 2 p))
      (volume : Measure (W₁ × W₂)) (volume : Measure W) :=
    (e.symm.measurePreserving).comp (WithLp.volume_preserving_toLp W₁ W₂)
  have hmeas : AEMeasurable (fun p : W₁ × W₂ => f (e.symm (WithLp.toLp 2 p)))
      (volume : Measure (W₁ × W₂)) :=
    hf.comp_quasiMeasurePreserving hmp.quasiMeasurePreserving
  have h3 : ∫⁻ p, f (e.symm (WithLp.toLp 2 p)) ∂(volume : Measure (W₁ × W₂))
      = ∫⁻ s, ∫⁻ τ, f (e.symm (WithLp.toLp 2 (s, τ))) ∂(volume : Measure W₂)
          ∂(volume : Measure W₁) := by
    rw [Measure.volume_eq_prod]
    exact lintegral_prod _ (by rwa [Measure.volume_eq_prod] at hmeas)
  rw [← h1, ← h2, h3]

end TargetSplit

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W] in
theorem hausdorffMeasure_eq_inv_mul_normalized (k : ℕ) (X : Set V) :
    μH[(k : ℝ)] X = (ENNReal.ofReal (KLS.unitBallVolume k / 2 ^ k))⁻¹
      * KLS.hausdorffNormalized V k X := by
  have hpos : 0 < KLS.unitBallVolume k / 2 ^ k := by unfold KLS.unitBallVolume; positivity
  have hne : ENNReal.ofReal (KLS.unitBallVolume k / 2 ^ k) ≠ 0 := by
    simp [ENNReal.ofReal_eq_zero, not_le, hpos]
  rw [KLS.hausdorffNormalized, Measure.smul_apply, smul_eq_mul, ← mul_assoc,
    ENNReal.inv_mul_cancel hne ENNReal.ofReal_ne_top, one_mul]

omit [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ W] [MeasurableSpace W]
  [BorelSpace W] in
theorem finrank_tangentRange_eq_of_mem {u : V → W} {r : ℕ} {x₀ : V} (hx₀ : x₀ ∈ stratum u r) :
    finrank ℝ (tangentRange u x₀) = r := by
  have h0 := rank_toLinearMap_eq (fderiv ℝ u x₀)
  have : (finrank ℝ (tangentRange u x₀) : Cardinal) = (r : Cardinal) := by rw [← h0]; exact hx₀
  exact_mod_cast this

theorem lintegral_hausdorffMeasure_stratum_le
    {u : V → W} (hu : ContDiff ℝ 1 u) {k r : ℕ} (hk : k + finrank ℝ W = finrank ℝ V)
    (hr : r < finrank ℝ W) {x₀ : V} (hx₀ : x₀ ∈ stratum u r) {U : Set V} {c : ℝ≥0}
    (hUopen : IsOpen U) (hUcl : ∀ x ∈ closure U, coareaJacobian
      (fderiv ℝ (fun y => (tangentRange u x₀).orthogonalProjectionOnto (u y)) x) ≠ 0)
    (hlip : ∀ y ∈ stratum u r ∩ U, ∀ (ε : ℝ≥0) (S : Set V) (s : tangentRange u x₀),
      ApproximatesLinearOn u (fderiv ℝ u y) S ε →
        LipschitzOnWith (c * ε)
          (fun x => (tangentRange u x₀)ᗮ.orthogonalProjectionOnto (u x))
          (S ∩ {x : V | (tangentRange u x₀).orthogonalProjectionOnto (u x) = s})) :
    ∃ Cst : ℝ≥0∞, Cst ≠ ⊤ ∧ ∀ ε : ℝ≥0, ε ≠ 0 →
      (∫⁻ t, μH[(k : ℝ)] (stratum u r ∩ U ∩ {x : V | u x = t}) ∂(volume : Measure W))
        ≤ Cst * ((c * ε : ℝ≥0) : ℝ≥0∞) ^ (finrank ℝ W - r)
            * ∫⁻ x in stratum u r ∩ U,
                ENNReal.ofReal (coareaJacobian
                  (fderiv ℝ (fun y => (tangentRange u x₀).orthogonalProjectionOnto (u y)) x))
                ∂(volume : Measure V) := by
  classical
  set K : Submodule ℝ W := tangentRange u x₀ with hKdef
  set P : W →L[ℝ] K := K.orthogonalProjectionOnto with hPdef
  set Q : W →L[ℝ] (Kᗮ : Submodule ℝ W) := Kᗮ.orthogonalProjectionOnto with hQdef
  set v : V → K := fun y => P (u y) with hvdef
  set A : Set V := stratum u r ∩ U with hAdef
  set m₂ : ℕ := finrank ℝ (Kᗮ : Submodule ℝ W) with hm₂def
  set k₂ : ℕ := finrank ℝ V - finrank ℝ K with hk₂def
  have hKr : finrank ℝ K = r := finrank_tangentRange_eq_of_mem hx₀
  have hm₂ : m₂ = finrank ℝ W - r := by
    have := K.finrank_add_finrank_orthogonal
    omega
  have hk₂ : k + m₂ = k₂ := by
    have := K.finrank_add_finrank_orthogonal
    omega
  have hvC : ContDiff ℝ 1 v := P.contDiff.comp hu
  have hAmeas : MeasurableSet A := (measurableSet_rank_fderiv_eq hu r).inter hUopen.measurableSet
  set O : Set V := {x : V | coareaJacobian (fderiv ℝ v x) ≠ 0} with hOdef
  have hOopen : IsOpen O := isOpen_coareaJacobian_ne_zero hvC
  have hAO : A ⊆ O := fun x hx => hUcl x (subset_closure hx.2)
  set α : ℝ≥0∞ := ENNReal.ofReal (KLS.unitBallVolume k₂ / 2 ^ k₂) with hαdef
  have hαne : α ≠ 0 := by
    have hpos : 0 < KLS.unitBallVolume k₂ / 2 ^ k₂ := by unfold KLS.unitBallVolume; positivity
    simp [hαdef, ENNReal.ofReal_eq_zero, not_le, hpos]
  set Cst₁ : ℝ≥0∞ := (volume : Measure (Kᗮ : Submodule ℝ W)) (Metric.closedBall 0 1) with hC₁
  have hCst₁ : Cst₁ ≠ ⊤ := measure_closedBall_lt_top.ne
  refine ⟨Cst₁ * α⁻¹, ENNReal.mul_ne_top hCst₁ (ENNReal.inv_ne_top.2 hαne), fun ε hε => ?_⟩
  rcases Set.eq_empty_or_nonempty A with hAe | hAne
  · rw [hAe]; simp
  obtain ⟨T, Aj, hdisj, hTmeas, hcov, happrox, hAj⟩ :=
    exists_partition_approximatesLinearOn_of_hasFDerivWithinAt u A (fderiv ℝ u)
      (fun x _ => ((hu.differentiable one_ne_zero) x).hasFDerivAt.hasFDerivWithinAt)
      (fun _ => ε) (fun _ => hε)
  choose yy hyA hyEq using hAj hAne
  have hlipn : ∀ (n : ℕ) (s : K),
      LipschitzOnWith (c * ε) (fun x => Q (u x)) ((A ∩ T n) ∩ {x : V | P (u x) = s}) := by
    intro n s
    exact hlip (yy n) (hyA n) ε (A ∩ T n) s (by rw [← hyEq n]; exact happrox n)
  choose F hFmeas hFdom hFint using fun (n : ℕ) (s : K) =>
    exists_measurable_majorant_vector (X := V) (u := fun x => Q (u x))
      (S := (A ∩ T n) ∩ {x : V | P (u x) = s}) (d := (k : ℝ)) (Nat.cast_nonneg k) (hlipn n s)
  set f : W → ℝ≥0∞ := fun t => μH[(k : ℝ)] (A ∩ {x : V | u x = t}) with hfdef
  have hfAE : AEMeasurable f (volume : Measure W) := by
    have hν := aemeasurable_setLIntegral_inter_levelSet_of_contDiffOn_vector (k := k)
      (g := fun _ => (1 : ℝ≥0∞)) hk isOpen_univ hu.contDiffOn hAmeas (Set.subset_univ A)
      measurable_const
    simp only [setLIntegral_one] at hν
    have hrw : f = fun t => (ENNReal.ofReal (KLS.unitBallVolume k / 2 ^ k))⁻¹ *
        KLS.hausdorffNormalized V k (A ∩ {x : V | u x = t}) := by
      funext t; exact hausdorffMeasure_eq_inv_mul_normalized k _
    rw [hrw]
    exact hν.const_mul _
  have hcast : (k : ℝ) + ((m₂ : ℕ) : ℝ) = ((k₂ : ℕ) : ℝ) := by
    rw [← hk₂]; push_cast; ring
  -- the pointwise bound on a fibre
  have hpt : ∀ (s : K) (τ : (Kᗮ : Submodule ℝ W)),
      f (K.orthogonalDecomposition.symm (WithLp.toLp 2 (s, τ))) ≤ ∑' n, F n s τ := by
    intro s τ
    have hsub : A ∩ {x : V | u x = K.orthogonalDecomposition.symm (WithLp.toLp 2 (s, τ))}
        ⊆ ⋃ n, ((A ∩ T n) ∩ {x : V | P (u x) = s}) ∩ {x : V | Q (u x) = τ} := by
      rintro x ⟨hxA, hxu⟩
      obtain ⟨n, hn⟩ := Set.mem_iUnion.1 (hcov hxA)
      have he : K.orthogonalDecomposition (u x) = WithLp.toLp 2 (s, τ) := by
        rw [show u x = K.orthogonalDecomposition.symm (WithLp.toLp 2 (s, τ)) from hxu]
        exact K.orthogonalDecomposition.apply_symm_apply _
      rw [Submodule.orthogonalDecomposition_apply] at he
      have h2 : (K.orthogonalProjectionOnto (u x), Kᗮ.orthogonalProjectionOnto (u x)) = (s, τ) := by
        simpa using congrArg WithLp.ofLp he
      exact Set.mem_iUnion.2 ⟨n, ⟨⟨⟨hxA, hn⟩, (Prod.mk.injEq _ _ _ _ ▸ h2).1⟩,
        (Prod.mk.injEq _ _ _ _ ▸ h2).2⟩⟩
    calc f (K.orthogonalDecomposition.symm (WithLp.toLp 2 (s, τ)))
        ≤ μH[(k : ℝ)] (⋃ n, ((A ∩ T n) ∩ {x : V | P (u x) = s}) ∩ {x : V | Q (u x) = τ}) :=
          measure_mono hsub
      _ ≤ ∑' n, μH[(k : ℝ)] (((A ∩ T n) ∩ {x : V | P (u x) = s}) ∩ {x : V | Q (u x) = τ}) :=
          measure_iUnion_le _
      _ ≤ ∑' n, F n s τ := ENNReal.tsum_le_tsum fun n => hFdom n s τ
  -- integrate over the second factor
  have hτ : ∀ s : K,
      (∫⁻ τ, f (K.orthogonalDecomposition.symm (WithLp.toLp 2 (s, τ)))
        ∂(volume : Measure (Kᗮ : Submodule ℝ W)))
        ≤ Cst₁ * ((c * ε : ℝ≥0) : ℝ≥0∞) ^ m₂
            * ∑' n, μH[((k₂ : ℕ) : ℝ)] ((A ∩ T n) ∩ {x : V | v x = s}) := by
    intro s
    calc (∫⁻ τ, f (K.orthogonalDecomposition.symm (WithLp.toLp 2 (s, τ)))
            ∂(volume : Measure (Kᗮ : Submodule ℝ W)))
        ≤ ∫⁻ τ, ∑' n, F n s τ ∂(volume : Measure (Kᗮ : Submodule ℝ W)) :=
          lintegral_mono (hpt s)
      _ = ∑' n, ∫⁻ τ, F n s τ ∂(volume : Measure (Kᗮ : Submodule ℝ W)) :=
          lintegral_tsum fun n => (hFmeas n s).aemeasurable
      _ ≤ ∑' n, Cst₁ * ((c * ε : ℝ≥0) : ℝ≥0∞) ^ m₂
            * μH[((k₂ : ℕ) : ℝ)] ((A ∩ T n) ∩ {x : V | v x = s}) := by
          refine ENNReal.tsum_le_tsum fun n => ?_
          have h := hFint n s
          rwa [hcast] at h
      _ = Cst₁ * ((c * ε : ℝ≥0) : ℝ≥0∞) ^ m₂
            * ∑' n, μH[((k₂ : ℕ) : ℝ)] ((A ∩ T n) ∩ {x : V | v x = s}) := by
          rw [ENNReal.tsum_mul_left]
  -- the coarea formula for the regular component
  have hcoarea : ∀ n : ℕ,
      (∫⁻ s, KLS.hausdorffNormalized V k₂ ((A ∩ T n) ∩ {x : V | v x = s})
        ∂(volume : Measure K))
        = ∫⁻ x in A ∩ T n, ENNReal.ofReal (coareaJacobian (fderiv ℝ v x))
            ∂(volume : Measure V) := by
    intro n
    obtain ⟨-, heq⟩ := coarea_of_contDiffOn_of_coareaJacobian_ne_zero (g := fun _ => (1 : ℝ≥0∞))
      hOopen hvC.contDiffOn (fun x hx => hx) (hAmeas.inter (hTmeas n))
      (Set.inter_subset_left.trans hAO) measurable_const
    simp only [setLIntegral_one, mul_one] at heq
    exact heq.symm
  have hmeass : ∀ n : ℕ, Measurable
      (fun s : K => KLS.hausdorffNormalized V k₂ ((A ∩ T n) ∩ {x : V | v x = s})) := by
    intro n
    obtain ⟨hm, -⟩ := coarea_of_contDiffOn_of_coareaJacobian_ne_zero (g := fun _ => (1 : ℝ≥0∞))
      hOopen hvC.contDiffOn (fun x hx => hx) (hAmeas.inter (hTmeas n))
      (Set.inter_subset_left.trans hAO) measurable_const
    simpa only [setLIntegral_one] using hm
  have hdisj' : Pairwise (Function.onFun Disjoint fun n => A ∩ T n) := fun i j hij =>
    (hdisj hij).mono Set.inter_subset_right Set.inter_subset_right
  have hAunion : A = ⋃ n, A ∩ T n := by
    refine Set.Subset.antisymm (fun x hx => ?_) (Set.iUnion_subset fun n => Set.inter_subset_left)
    obtain ⟨n, hn⟩ := Set.mem_iUnion.1 (hcov hx)
    exact Set.mem_iUnion.2 ⟨n, hx, hn⟩
  have hsum : (∑' n : ℕ, ∫⁻ x in A ∩ T n, ENNReal.ofReal (coareaJacobian (fderiv ℝ v x))
      ∂(volume : Measure V))
      = ∫⁻ x in A, ENNReal.ofReal (coareaJacobian (fderiv ℝ v x)) ∂(volume : Measure V) := by
    rw [← lintegral_iUnion (fun n => hAmeas.inter (hTmeas n)) hdisj', ← hAunion]
  have hstep : ∀ s : K, ∑' n, μH[((k₂ : ℕ) : ℝ)] ((A ∩ T n) ∩ {x : V | v x = s})
      = α⁻¹ * ∑' n, KLS.hausdorffNormalized V k₂ ((A ∩ T n) ∩ {x : V | v x = s}) := by
    intro s
    rw [← ENNReal.tsum_mul_left]
    exact tsum_congr fun n => hausdorffMeasure_eq_inv_mul_normalized k₂ _
  have hconst : Cst₁ * ((c * ε : ℝ≥0) : ℝ≥0∞) ^ m₂ ≠ ⊤ :=
    ENNReal.mul_ne_top hCst₁ (ENNReal.pow_ne_top ENNReal.coe_ne_top)
  calc (∫⁻ t, μH[(k : ℝ)] (A ∩ {x : V | u x = t}) ∂(volume : Measure W))
      = ∫⁻ s, ∫⁻ τ, f (K.orthogonalDecomposition.symm (WithLp.toLp 2 (s, τ)))
          ∂(volume : Measure (Kᗮ : Submodule ℝ W)) ∂(volume : Measure K) :=
        lintegral_split_target K.orthogonalDecomposition hfAE
    _ ≤ ∫⁻ s, Cst₁ * ((c * ε : ℝ≥0) : ℝ≥0∞) ^ m₂
          * ∑' n, μH[((k₂ : ℕ) : ℝ)] ((A ∩ T n) ∩ {x : V | v x = s}) ∂(volume : Measure K) :=
        lintegral_mono hτ
    _ = Cst₁ * ((c * ε : ℝ≥0) : ℝ≥0∞) ^ m₂ * (α⁻¹
          * ∑' n, ∫⁻ x in A ∩ T n, ENNReal.ofReal (coareaJacobian (fderiv ℝ v x))
              ∂(volume : Measure V)) := by
        simp only [hstep]
        rw [lintegral_const_mul' _ _ hconst,
          lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 hαne),
          lintegral_tsum fun n => (hmeass n).aemeasurable]
        simp only [hcoarea]
    _ = Cst₁ * α⁻¹ * ((c * ε : ℝ≥0) : ℝ≥0∞) ^ (finrank ℝ W - r)
          * ∫⁻ x in A, ENNReal.ofReal (coareaJacobian (fderiv ℝ v x)) ∂(volume : Measure V) := by
        rw [hsum, hm₂]
        ring


/-- **`R7`: the local per-stratum slicing.** -/
theorem exists_nhds_ae_hausdorffMeasure_stratum_inter_levelSet_eq_zero
    {u : V → W} (hu : ContDiff ℝ 1 u) {k r : ℕ} (hk : k + finrank ℝ W = finrank ℝ V)
    (hr : r < finrank ℝ W) {x₀ : V} (hx₀ : x₀ ∈ stratum u r) :
    ∃ U ∈ nhds x₀, ∀ᵐ t ∂(volume : Measure W),
      μH[(k : ℝ)] (stratum u r ∩ U ∩ {x : V | u x = t}) = 0 := by
  classical
  obtain ⟨U, c, hUopen, hx₀U, hUcompact, hreg, hlip⟩ := exists_stratum_local_data hu hx₀
  obtain ⟨Cst, hCst, hbound⟩ :=
    lintegral_hausdorffMeasure_stratum_le hu hk hr hx₀ hUopen hreg hlip
  set K : Submodule ℝ W := tangentRange u x₀ with hKdef
  set P : W →L[ℝ] K := K.orthogonalProjectionOnto with hPdef
  set v : V → K := fun y => P (u y) with hvdef
  set A : Set V := stratum u r ∩ U with hAdef
  set m₂ : ℕ := finrank ℝ W - r with hm₂def
  have hm₂pos : m₂ ≠ 0 := by omega
  have hvC : ContDiff ℝ 1 v := P.contDiff.comp hu
  have hAmeas : MeasurableSet A := (measurableSet_rank_fderiv_eq hu r).inter hUopen.measurableSet
  -- the right-hand factor is finite
  have hJcont : Continuous fun x : V => coareaJacobian (fderiv ℝ v x) :=
    continuous_coareaJacobian.comp (hvC.continuous_fderiv one_ne_zero)
  obtain ⟨M, hM⟩ := hUcompact.exists_bound_of_continuousOn hJcont.continuousOn
  have hvolA : (volume : Measure V) A ≠ ⊤ :=
    ((measure_mono (Set.Subset.trans Set.inter_subset_right subset_closure)).trans_lt
      hUcompact.measure_lt_top).ne
  have hD : (∫⁻ x in A, ENNReal.ofReal (coareaJacobian (fderiv ℝ v x)) ∂(volume : Measure V))
      ≠ ⊤ := by
    have hbnd : (∫⁻ x in A, ENNReal.ofReal (coareaJacobian (fderiv ℝ v x))
        ∂(volume : Measure V)) ≤ ENNReal.ofReal M * (volume : Measure V) A := by
      refine (lintegral_mono_ae ?_).trans_eq (setLIntegral_const A (ENNReal.ofReal M))
      filter_upwards [self_mem_ae_restrict hAmeas] with x hx
      exact ENNReal.ofReal_le_ofReal
        ((le_abs_self _).trans (hM x (subset_closure hx.2)))
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hvolA) hbnd
  -- the bound tends to zero
  have htend : Filter.Tendsto (fun j : ℕ => Cst
      * ((c * ((j : ℝ≥0) + 1)⁻¹ : ℝ≥0) : ℝ≥0∞) ^ m₂
      * ∫⁻ x in A, ENNReal.ofReal (coareaJacobian (fderiv ℝ v x)) ∂(volume : Measure V))
      Filter.atTop (nhds 0) := by
    have hinv : Filter.Tendsto (fun j : ℕ => ((c * ((j : ℝ≥0) + 1)⁻¹ : ℝ≥0) : ℝ≥0∞))
        Filter.atTop (nhds 0) := by
      have h : ∀ j : ℕ, ((c * ((j : ℝ≥0) + 1)⁻¹ : ℝ≥0) : ℝ≥0∞)
          = (c : ℝ≥0∞) * (((j : ℝ≥0∞) + 1)⁻¹) := by
        intro j
        rw [ENNReal.coe_mul, ENNReal.coe_inv (by positivity)]
        push_cast
        ring
      simp only [h]
      have hbase : Filter.Tendsto (fun j : ℕ => ((j : ℝ≥0∞) + 1)⁻¹) Filter.atTop (nhds 0) := by
        have he : (fun j : ℕ => ((j : ℝ≥0∞) + 1)⁻¹) = fun j : ℕ => ((j + 1 : ℕ) : ℝ≥0∞)⁻¹ := by
          funext j; norm_cast
        rw [he]
        exact ENNReal.tendsto_inv_nat_nhds_zero.comp (Filter.tendsto_add_atTop_nat 1)
      simpa using ENNReal.Tendsto.const_mul hbase (Or.inr ENNReal.coe_ne_top)
    have hpow : Filter.Tendsto (fun j : ℕ => ((c * ((j : ℝ≥0) + 1)⁻¹ : ℝ≥0) : ℝ≥0∞) ^ m₂)
        Filter.atTop (nhds 0) := by
      have h0 : (0 : ℝ≥0∞) ^ m₂ = 0 := zero_pow hm₂pos
      have := (ENNReal.continuous_pow m₂).continuousAt.tendsto.comp hinv
      rw [h0] at this
      simpa [Function.comp_def] using this
    have h1 := ENNReal.Tendsto.const_mul hpow (Or.inr hCst)
    simp only [mul_zero] at h1
    have h2 := ENNReal.Tendsto.mul_const h1 (Or.inr hD)
    simpa using h2
  have hzero : (∫⁻ t, μH[(k : ℝ)] (A ∩ {x : V | u x = t}) ∂(volume : Measure W)) = 0 := by
    refine le_antisymm (ge_of_tendsto' htend fun j => ?_) (by simp)
    exact hbound _ (by positivity)
  -- conclude
  have hfAE : AEMeasurable (fun t : W => μH[(k : ℝ)] (A ∩ {x : V | u x = t}))
      (volume : Measure W) := by
    have hν := aemeasurable_setLIntegral_inter_levelSet_of_contDiffOn_vector (k := k)
      (g := fun _ => (1 : ℝ≥0∞)) hk isOpen_univ hu.contDiffOn hAmeas (Set.subset_univ A)
      measurable_const
    simp only [setLIntegral_one] at hν
    have hrw : (fun t : W => μH[(k : ℝ)] (A ∩ {x : V | u x = t}))
        = fun t => (ENNReal.ofReal (KLS.unitBallVolume k / 2 ^ k))⁻¹ *
          KLS.hausdorffNormalized V k (A ∩ {x : V | u x = t}) := by
      funext t; exact hausdorffMeasure_eq_inv_mul_normalized k _
    rw [hrw]
    exact hν.const_mul _
  refine ⟨U, hUopen.mem_nhds hx₀U, ?_⟩
  exact (lintegral_eq_zero_iff' hfAE).1 hzero


end FunctionalInequalities.Analysis
