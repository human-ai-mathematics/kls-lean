module

public import FunctionalInequalities.KLS.BKL.Suspension.Law
public import FunctionalInequalities.KLS.BKL.Suspension.Density
public import FunctionalInequalities.KLS.BKL.Suspension.Cumulant
public import FunctionalInequalities.KLS.BKL.Suspension.Moments
public import FunctionalInequalities.KLS.BKL.Suspension.Derivatives
public import FunctionalInequalities.KLS.BKL.TaylorBound
public import FunctionalInequalities.L2.AffineDecomposition
public import FunctionalInequalities.KLS.LogConcave.Regular.Basic
public import FunctionalInequalities.Analysis.Tensor.Coordinate
public import FunctionalInequalities.KLS.BKL.Localization.Process.Basic
/-!
# Audit: supporting endpoints of BKL Proposition 7.1 with source-style consumers

Source: Bizeul–Klartag–Lehec, arXiv:2610.05474v1, Proposition 7.1, pp. 28–30. Supporting
results; none of them is Proposition 7.1.

* `blocks_source`: the Hilbert–Schmidt step after (112) — if every copy-block entry equals
  `d!/(σ√N) T_J`, then `(d!)²/σ² |T|² ≤ |κ(e₀)|²` (`card_mul_sq_mul_sum_sq_le_of_blocks`).
* `linear_step_isotropic`: the linear-function step on p. 30 with the source's normalization
  `‖ℓ‖₂ = |v|` from isotropy (`norm_coordTensor_taylorTensor_inner_sq_le`).
* `jointLaw_regular`: the joint law of a regular law is a probability measure
  (`isProbabilityMeasure_jointLaw_of_pos`, through `isProbabilityMeasure_laplaceMeasure`).
* `laplace_rate_two`: the Laplace law with `β = 2` has mean `0` and second moment `1/2`.
* `scalar_moments_source`: `S = (F_N + η_β)/σ_β` has mean `0` and second moment `1`, with the
  Laplace data discharged by `laplaceMeasure_moments` (no assumed noise moments).
* `jointLaw_eq_tilted_no_copies`, `jointLaw_eq_tilted_dim_zero`: the density (109) at `N = 0`
  and at `n = 0`.
* `logConcave_jointLaw_regular`: (109)–(110) for a regular law, with no assumed density identity.
* `graph_moment_regular`: an exponential moment of the joint law of a regular law gives an
  exponential moment of the graph law `x ↦ (f x, x)`.
* `jointLaw_radius_regular`: under (110) the joint law of a regular law has an exponential moment
  and a smooth `Λ` near `0`, with no assumed density identity
  (`exists_integrable_exp_norm_contDiffOn_logLaplace_jointLaw`).
* `isotropic_jointLaw_regular`: the joint law of an isotropic regular law and an `f` satisfying
  (108) is isotropic (`isotropic_jointLaw`, with `Isotropic.integral_inner_mul_inner`).
* `fderiv_logLaplace_jointLaw_none_regular`: (111) for a regular law (re-export of the exact
  statement, to pin its type).
* `taylor_bound_smooth_two`: (113) at `d = 2` for a smooth normalized `f` (re-export pinning the
  type of
  `norm_coordTensor_taylorTensor_sq_le_of_cumulantBound`, conditional on `CumulantBound 2 b`).
* `taylor_bound_orthogonal_two`: (113) at `d = 2` for every `f ∈ L²` orthogonal to the affine
  functions
  (`norm_coordTensor_taylorTensor_sq_le_of_orthogonal`, conditional on `CumulantBound 2 b`).
* `cumulant_jointLaw_none_entries_two`: (112) at `d = 2` with two copy indices, pinning the exact
  entry `2/(σ√N) · T_2 f(e_{j_1}, e_{j_2})` when the copies agree and `0` otherwise.
-/

@[expose] public section

noncomputable section

open MeasureTheory FunctionalInequalities FunctionalInequalities.Analysis.Tensor
open FunctionalInequalities.Analysis.BakryEmery FunctionalInequalities.KLS.LogConcave.Suspension
open FunctionalInequalities.Probability.Line
open scoped RealInnerProductSpace

namespace BKLProposition71SupportAudit

/-- The source's Hilbert–Schmidt step after (112), from the block entries. -/
theorem blocks_source {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    [Nonempty κ] {d : ℕ} (hd : 0 < d) (A : (Fin d → Option (κ × ι)) → ℝ) {σ : ℝ} (hσ : 0 < σ)
    (T : (Fin d → ι) → ℝ)
    (hA : ∀ i j, A (fun k => some (i, j k)) =
      (d.factorial : ℝ) / (σ * Real.sqrt (Fintype.card κ)) * T j) :
    (d.factorial : ℝ) ^ 2 / σ ^ 2 * ∑ j, T j ^ 2 ≤ ∑ J, A J ^ 2 := by
  have h := card_mul_sq_mul_sum_sq_le_of_blocks hd A _ T hA
  have hN : (0 : ℝ) < Fintype.card κ := by exact_mod_cast Fintype.card_pos
  have hs : Real.sqrt (Fintype.card κ : ℝ) ^ 2 = Fintype.card κ := Real.sq_sqrt hN.le
  have hc : (Fintype.card κ : ℝ) * ((d.factorial : ℝ) / (σ * Real.sqrt (Fintype.card κ))) ^ 2 =
      (d.factorial : ℝ) ^ 2 / σ ^ 2 := by
    rw [div_pow, mul_pow, hs]
    field_simp
  rw [hc] at h
  exact h

/-- The linear-function step of p. 30 with isotropy: `|T_d ℓ|² ≤ b/(d!)² ‖ℓ‖₂²` for
`ℓ = ⟪v, ·⟫`, when `∫ ⟪v, x⟫² dμ = |v|²`. -/
theorem linear_step_isotropic {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    [IsProbabilityMeasure μ] (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ)
    {d : ℕ} {b : ℝ}
    (hR : ∀ u : E, ∑ J : Fin d → Fin (Module.finrank ℝ E),
      cumulant μ (d + 1) (Fin.cons u fun k => stdOrthonormalBasis ℝ E (J k)) ^ 2 ≤ b * ‖u‖ ^ 2)
    (v : E) (hiso : ∫ x, ⟪v, x⟫ ^ 2 ∂μ = ‖v‖ ^ 2) :
    ‖coordTensor (stdOrthonormalBasis ℝ E) (taylorTensor μ (fun x => ⟪v, x⟫) d)‖ ^ 2 ≤
      b / (d.factorial : ℝ) ^ 2 * ∫ x, ⟪v, x⟫ ^ 2 ∂μ := by
  rw [hiso]
  exact norm_coordTensor_taylorTensor_inner_sq_le μ hexp hR v

/-- The joint law built from a regular law is a probability measure. -/
theorem jointLaw_regular {n : ℕ} (V : EuclideanSpace ℝ (Fin n) → ℝ) {a b' : ℝ}
    (hV : KLS.RegularPotential V a b') {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Measurable f)
    {β : ℝ} (hβ : 0 < β) (N : ℕ) :
    IsProbabilityMeasure (jointLaw (hV.law : Measure _) f β (sigma β) N) :=
  isProbabilityMeasure_jointLaw_of_pos _ hf hβ _ N

/-- The Laplace law with rate `2`: mean `0`, second moment `1/2`. -/
theorem laplace_rate_two :
    (∫ s : ℝ, s ∂laplaceMeasure 2) = 0 ∧ (∫ s : ℝ, s ^ 2 ∂laplaceMeasure 2) = 1 / 2 := by
  obtain ⟨-, -, h0, h2⟩ := laplaceMeasure_moments (β := 2) (by norm_num)
  exact ⟨h0, by rw [h2]; norm_num⟩

/-- The suspension coordinate has unit variance, with the Laplace moments proved. -/
theorem scalar_moments_source {n N : ℕ} (hN : 0 < N)
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ]
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf2 : MemLp f 2 μ)
    (hf0 : ∫ x, f x ∂μ = 0) (hf1 : ∫ x, f x ^ 2 ∂μ = 1) {β : ℝ} (hβ : 0 < β) :
    (∫ q : (Fin N → EuclideanSpace ℝ (Fin n)) × ℝ,
        ((copyStat f N q.1 + q.2) / sigma β) ^ 2
        ∂((Measure.pi (fun _ : Fin N => μ)).prod (laplaceMeasure β))) = 1 := by
  have := isProbabilityMeasure_laplaceMeasure hβ
  obtain ⟨h1, h2, h0, hv⟩ := laplaceMeasure_moments hβ
  exact (scalar_moments hN μ f hf2 hf0 hf1 hβ h1 h2 h0 hv).2.2

/-- (109) with no copies. -/
theorem jointLaw_eq_tilted_no_copies {n : ℕ} (V f : EuclideanSpace ℝ (Fin n) → ℝ) {β : ℝ}
    (hβ : 0 < β) (hV : Measurable V) (hf : Measurable f)
    (hint : Integrable (fun x => Real.exp (-V x))) :
    jointLaw (volume.tilted fun x => -V x) f β (sigma β) 0 =
      (volume : Measure (JointSpace 0 n)).tilted fun p =>
        -potential V f β (sigma β) 0 (p none, fun i => WithLp.toLp 2 fun j => p (some (i, j))) :=
  jointLaw_eq_tilted V f hβ hV hf hint

/-- (109) in dimension zero. -/
theorem jointLaw_eq_tilted_dim_zero {N : ℕ} (V f : EuclideanSpace ℝ (Fin 0) → ℝ) {β : ℝ}
    (hβ : 0 < β) (hV : Measurable V) (hf : Measurable f)
    (hint : Integrable (fun x => Real.exp (-V x))) :
    jointLaw (volume.tilted fun x => -V x) f β (sigma β) N =
      (volume : Measure (JointSpace N 0)).tilted fun p =>
        -potential V f β (sigma β) N (p none, fun i => WithLp.toLp 2 fun j => p (some (i, j))) :=
  jointLaw_eq_tilted V f hβ hV hf hint

/-- (109)–(110) for a regular law: the joint law is log-concave once `β M/√N ≤ a`. -/
theorem logConcave_jointLaw_regular {n N : ℕ} (V : EuclideanSpace ℝ (Fin n) → ℝ) {a b' : ℝ}
    (hV : KLS.RegularPotential V a b') {f : EuclideanSpace ℝ (Fin n) → ℝ} {M β : ℝ} (hβ : 0 < β)
    (hf : ContDiff ℝ 2 f) (hfM : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ M)
    (hN : β / Real.sqrt N * M ≤ a)
    (h : IsProbabilityMeasure (jointLaw (volume.tilted fun x => -V x) f β (sigma β) N)) :
    KLS.LogConcave (⟨_, h⟩ : ProbabilityMeasure (JointSpace N n)) :=
  logConcave_jointLaw V f hβ (hV.temperate.1.of_le (WithTop.coe_le_coe.mpr le_top)) hf hV.lower
    hfM hN hV.integrable_exp_neg h

/-- The graph law of a regular law has an exponential moment when the joint law has one. -/
theorem graph_moment_regular {n N : ℕ} (V : EuclideanSpace ℝ (Fin n) → ℝ) {a b' : ℝ}
    (hV : KLS.RegularPotential V a b') {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Measurable f)
    {β r : ℝ} (hβ : 0 < β) (hN : 0 < N) (hr : 0 < r)
    (hexp : Integrable (fun p : JointSpace N n => Real.exp (r * ‖p‖))
      (jointLaw (hV.law : Measure _) f β (sigma β) N)) :
    ∃ t : ℝ, 0 < t ∧
      Integrable (fun y : EuclideanSpace ℝ (Option (Fin n)) => Real.exp (t * ‖y‖))
        ((hV.law : Measure _).map (fun x : EuclideanSpace ℝ (Fin n) =>
          (WithLp.toLp 2 fun o => Option.elim o (f x) fun j => x j :
            EuclideanSpace ℝ (Option (Fin n))))) :=
  exists_graph_norm_moment_from_joint _ hf hβ hN hr one_pos hexp
    (hV.integrable_exp_mul_norm 1)

open scoped ContDiff in
/--
Under (110), the joint law of a regular law has an exponential moment and `Λ_ν ∈ C^∞` near `0`. -/
theorem jointLaw_radius_regular {n N : ℕ} (V : EuclideanSpace ℝ (Fin n) → ℝ) {a b' : ℝ}
    (hV : KLS.RegularPotential V a b') {f : EuclideanSpace ℝ (Fin n) → ℝ} {M β : ℝ} (hβ : 0 < β)
    (hf : ContDiff ℝ 2 f) (hfM : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ M)
    (hN : β / Real.sqrt N * M ≤ a) :
    ∃ r : ℝ,
      0 < r ∧
        Integrable (fun p => Real.exp (r * ‖p‖))
            (jointLaw (hV.law : Measure _) f β (sigma β) N) ∧
          ContDiffOn ℝ ∞ (logLaplace (jointLaw (hV.law : Measure _) f β (sigma β) N))
            (Metric.ball 0 r) :=
  exists_integrable_exp_norm_contDiffOn_logLaplace_jointLaw V f hβ
    (hV.temperate.1.of_le (WithTop.coe_le_coe.mpr le_top)) hf hV.lower hfM hN
    hV.integrable_exp_neg

/-- The joint law of an isotropic regular law is isotropic (BKL p. 28). -/
theorem isotropic_jointLaw_regular {n N : ℕ} (hN : 0 < N) (V : EuclideanSpace ℝ (Fin n) → ℝ)
    {a b' : ℝ} (hV : KLS.RegularPotential V a b') (hiso : KLS.Isotropic hV.law)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Measurable f)
    (hf2 : MemLp f 2 (hV.law : Measure _)) (hf0 : ∫ x, f x ∂(hV.law : Measure _) = 0)
    (hf1 : ∫ x, f x ^ 2 ∂(hV.law : Measure _) = 1)
    (hfx : ∀ u, ∫ x, ⟪u, x⟫ * f x ∂(hV.law : Measure _) = 0) {β : ℝ} (hβ : 0 < β) :
    KLS.Isotropic
      (⟨jointLaw (hV.law : Measure _) f β (sigma β) N,
          isProbabilityMeasure_jointLaw_of_pos _ hf hβ (sigma β) N⟩ :
        ProbabilityMeasure (JointSpace N n)) :=
  isotropic_jointLaw hN _ hiso.memLp_two hiso.mean_zero
    (fun u v => hiso.integral_inner_mul_inner u v) hf hf2 hf0 hf1 hfx hβ

/-- (111) for a regular law and `f ∈ C²` with bounded Hessian, `N` chosen by (110). -/
theorem fderiv_logLaplace_jointLaw_none_regular {n N : ℕ} (hN : 0 < N)
    (V : EuclideanSpace ℝ (Fin n) → ℝ) {a b' : ℝ} (hV : KLS.RegularPotential V a b')
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {M β : ℝ} (hβ : 0 < β) (hf : ContDiff ℝ 2 f)
    (hfM : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ M) (h110 : β / Real.sqrt N * M ≤ a) :
    ∃ r > 0, ∀ z : JointSpace N n, ‖z‖ < r → z none = 0 →
      fderiv ℝ (logLaplace (jointLaw (hV.law : Measure _) f β (sigma β) N)) z
          (EuclideanSpace.single none 1) =
        (sigma β * Real.sqrt N)⁻¹ *
          ∑ i, tiltAverage (hV.law : Measure _) f (WithLp.toLp 2 fun j => z (some (i, j))) :=
  fderiv_logLaplace_jointLaw_none hN V hV hβ hf hfM h110

/-- (112) at `d = 2`: the entry with copies `i₁, i₂` and coordinates `j₁, j₂`. -/
theorem cumulant_jointLaw_none_entries_two {n N : ℕ} (hN : 0 < N)
    (V : EuclideanSpace ℝ (Fin n) → ℝ) {a b' : ℝ} (hV : KLS.RegularPotential V a b')
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {M β : ℝ} (hβ : 0 < β) (hf : ContDiff ℝ 2 f)
    (hfM : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ M) (h110 : β / Real.sqrt N * M ≤ a) (i₁ i₂ : Fin N)
    (j₁ j₂ : Fin n) :
    cumulant (jointLaw (hV.law : Measure _) f β (sigma β) N) 3
        (Fin.cons (EuclideanSpace.single none 1) fun k =>
          EuclideanSpace.single (some (![i₁, i₂] k, ![j₁, j₂] k)) 1) =
      if ∀ k k', ![i₁, i₂] k = ![i₁, i₂] k' then
        (2 : ℝ) / (sigma β * Real.sqrt N) *
          taylorTensor (hV.law : Measure _) f 2 fun k =>
            EuclideanSpace.basisFun (Fin n) ℝ (![j₁, j₂] k)
      else 0 := by
  have h :=
    cumulant_jointLaw_none_entries hN V hV hβ hf hfM h110 (d := 2) (by norm_num) ![i₁, i₂]
      ![j₁, j₂]
  simpa [Nat.factorial] using h

/-- (113) at `d = 2` for a smooth normalized `f`, conditional on `CumulantBound 2 b`. -/
theorem taylor_bound_smooth_two {b : ℝ} (hb : 0 < b) (hcb : CumulantBound 2 b) {n : ℕ}
    (V : EuclideanSpace ℝ (Fin n) → ℝ) {a b' : ℝ} (hV : KLS.RegularPotential V a b')
    (hiso : KLS.Isotropic hV.law) {f : EuclideanSpace ℝ (Fin n) → ℝ} {M : ℝ} (hf : ContDiff ℝ 2 f)
    (hfM : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ M) (hf2 : MemLp f 2 (hV.law : Measure _))
    (hf0 : ∫ x, f x ∂(hV.law : Measure _) = 0) (hf1 : ∫ x, f x ^ 2 ∂(hV.law : Measure _) = 1)
    (hfx : ∀ u, ∫ x, ⟪u, x⟫ * f x ∂(hV.law : Measure _) = 0) :
    ‖coordTensor (EuclideanSpace.basisFun (Fin n) ℝ) (taylorTensor (hV.law : Measure _) f 2)‖ ^ 2 ≤
      b / 4 := by
  have h := norm_coordTensor_taylorTensor_sq_le_of_cumulantBound le_rfl hb hcb V hV hiso hf hfM hf2
    hf0 hf1 hfx
  have h4 : ((Nat.factorial 2 : ℕ) : ℝ) ^ 2 = 4 := by norm_num [Nat.factorial]
  rw [h4] at h
  exact h

/--
(113) at `d = 2` for `f ∈ L²` orthogonal to the affine functions, conditional on `CumulantBound 2
b`. -/
theorem taylor_bound_orthogonal_two {b : ℝ} (hb : 0 < b) (hcb : CumulantBound 2 b) {n : ℕ}
    (V : EuclideanSpace ℝ (Fin n) → ℝ) {a b' : ℝ} (hV : KLS.RegularPotential V a b')
    (hiso : KLS.Isotropic hV.law) {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : MemLp f 2 (hV.law : Measure _)) (hf0 : ∫ x, f x ∂(hV.law : Measure _) = 0)
    (hfx : ∀ u, ∫ x, ⟪u, x⟫ * f x ∂(hV.law : Measure _) = 0) :
    ‖coordTensor (EuclideanSpace.basisFun (Fin n) ℝ) (taylorTensor (hV.law : Measure _) f 2)‖ ^
        2 ≤
      b / 4 * (eLpNorm f 2 (hV.law : Measure _)).toReal ^ 2 := by
  have h := norm_coordTensor_taylorTensor_sq_le_of_orthogonal le_rfl hb hcb V hV hiso hf hf0 hfx
  have h4 : ((Nat.factorial 2 : ℕ) : ℝ) ^ 2 = 4 := by norm_num [Nat.factorial]
  rw [h4] at h
  exact h

end BKLProposition71SupportAudit

#print axioms BKLProposition71SupportAudit.blocks_source
#print axioms BKLProposition71SupportAudit.linear_step_isotropic
#print axioms BKLProposition71SupportAudit.jointLaw_regular
#print axioms FunctionalInequalities.Analysis.Tensor.sum_sq_blocks_le
#print axioms FunctionalInequalities.Analysis.Tensor.card_mul_sq_mul_sum_sq_le_of_blocks
#print axioms FunctionalInequalities.Analysis.BakryEmery.norm_coordTensor_taylorTensor_inner_sq_le
#print axioms FunctionalInequalities.KLS.isotropic_of_moments
#print axioms FunctionalInequalities.Probability.Line.isProbabilityMeasure_laplaceMeasure
#print axioms FunctionalInequalities.KLS.LogConcave.Suspension.isProbabilityMeasure_jointLaw
#print axioms FunctionalInequalities.KLS.LogConcave.Suspension.isProbabilityMeasure_jointLaw_of_pos
#print axioms BKLProposition71SupportAudit.laplace_rate_two
#print axioms BKLProposition71SupportAudit.scalar_moments_source
#print axioms BKLProposition71SupportAudit.jointLaw_eq_tilted_no_copies
#print axioms BKLProposition71SupportAudit.jointLaw_eq_tilted_dim_zero
#print axioms BKLProposition71SupportAudit.logConcave_jointLaw_regular
#print axioms BKLProposition71SupportAudit.graph_moment_regular
#print axioms BKLProposition71SupportAudit.jointLaw_radius_regular
#print axioms BKLProposition71SupportAudit.isotropic_jointLaw_regular
#print axioms BKLProposition71SupportAudit.fderiv_logLaplace_jointLaw_none_regular
#print axioms BKLProposition71SupportAudit.cumulant_jointLaw_none_entries_two
#print axioms BKLProposition71SupportAudit.taylor_bound_smooth_two
#print axioms BKLProposition71SupportAudit.taylor_bound_orthogonal_two
#print axioms
  FunctionalInequalities.KLS.LogConcave.Suspension.norm_coordTensor_taylorTensor_sq_le_of_smooth
#print axioms
  FunctionalInequalities.KLS.LogConcave.Suspension.norm_coordTensor_taylorTensor_sq_le_of_orthogonal
#print axioms
  FunctionalInequalities.KLS.LogConcave.Suspension.norm_coordTensor_taylorTensor_sq_le_of_cumulantBound
#print axioms
  FunctionalInequalities.Analysis.BakryEmery.norm_coordTensor_taylorTensor_inner_sq_le_of_basis
#print axioms
  FunctionalInequalities.Analysis.BakryEmery.exists_bound_fderiv_fderiv_of_hasCompactSupport
#print axioms FunctionalInequalities.L2.integral_sq_eq_affine_decomposition
#print axioms FunctionalInequalities.L2.integral_affineOrthPart_sq_le
#print axioms FunctionalInequalities.L2.integral_affine_sq
#print axioms FunctionalInequalities.L2.integral_affineOrthPart_mul_sub
#print axioms FunctionalInequalities.KLS.LogConcave.Suspension.cumulant_jointLaw_none_entries
#print axioms FunctionalInequalities.KLS.LogConcave.Suspension.jointLaw_moments_of_laplace
#print axioms FunctionalInequalities.KLS.LogConcave.Suspension.isotropic_jointLaw
#print axioms FunctionalInequalities.KLS.LogConcave.Suspension.fderiv_logLaplace_jointLaw_none
#print axioms FunctionalInequalities.KLS.LogConcave.Suspension.le_of_forall_le_mul_sigma_sq
#print axioms FunctionalInequalities.KLS.LogConcave.Suspension.cumulantBound_jointSpace
#print axioms FunctionalInequalities.KLS.Isotropic.map_linearIsometryEquiv
#print axioms FunctionalInequalities.Analysis.BakryEmery.cumulant_map_linearIsometryEquiv
#print axioms FunctionalInequalities.Analysis.BakryEmery.iteratedFDeriv_comp_clm_of_isOpen
#print axioms FunctionalInequalities.Analysis.BakryEmery.iteratedFDeriv_comp_perm_of_contDiffOn
#print axioms FunctionalInequalities.L2.affineOrthPart
#print axioms FunctionalInequalities.L2.integral_affineOrthPart
#print axioms FunctionalInequalities.L2.integral_inner_mul_affineOrthPart
#print axioms FunctionalInequalities.L2.memLp_affineOrthPart
#print axioms FunctionalInequalities.L2.sub_affineOrthPart_eq
#print axioms FunctionalInequalities.L2.eLpNorm_le_eLpNorm_of_integral_sq_le
#print axioms FunctionalInequalities.L2.contDiff_affineOrthPart
#print axioms FunctionalInequalities.KLS.LogConcave.exists_integrable_exp_norm_contDiffOn_logLaplace
#print axioms
  FunctionalInequalities.KLS.LogConcave.Suspension.exists_integrable_exp_norm_contDiffOn_logLaplace_jointLaw
#print axioms FunctionalInequalities.Probability.Line.laplaceMeasure_moments
#print axioms FunctionalInequalities.Probability.lintegral_pi_prod_fin
#print axioms FunctionalInequalities.Probability.pi_normalizedSum_moments
#print axioms FunctionalInequalities.Probability.integral_mul_comp_eval_pi
#print axioms FunctionalInequalities.Probability.integral_normalizedSum_mul_comp_eval_pi
#print axioms FunctionalInequalities.Probability.prod_add_moments
#print axioms FunctionalInequalities.Probability.integral_prod_add_mul_eq_zero
#print axioms FunctionalInequalities.KLS.LogConcave.Suspension.jointLaw_eq_tilted
#print axioms FunctionalInequalities.KLS.LogConcave.Suspension.logConcave_jointLaw
#print axioms FunctionalInequalities.KLS.LogConcave.Suspension.lintegral_exp_inner_jointLaw
#print axioms FunctionalInequalities.KLS.LogConcave.Suspension.joint_integrability_factorization
#print axioms FunctionalInequalities.KLS.LogConcave.Suspension.logLaplace_jointLaw_factorization
#print axioms FunctionalInequalities.KLS.LogConcave.Suspension.exists_f_abs_exponential_moment
#print axioms
  FunctionalInequalities.KLS.LogConcave.Suspension.exists_graph_norm_moment_of_local_moments
#print axioms FunctionalInequalities.KLS.LogConcave.Suspension.exists_graph_norm_moment_from_joint
#print axioms FunctionalInequalities.KLS.LogConcave.Suspension.graph_map_measurable
#print axioms FunctionalInequalities.KLS.LogConcave.Suspension.graph_map_probability
#print axioms FunctionalInequalities.KLS.LogConcave.Suspension.copyStat_moments
#print axioms FunctionalInequalities.KLS.LogConcave.Suspension.integral_copyStat_mul_inner
#print axioms FunctionalInequalities.KLS.LogConcave.Suspension.integral_inner_mul_inner_pi
#print axioms FunctionalInequalities.KLS.LogConcave.Suspension.scalar_moments
#print axioms FunctionalInequalities.KLS.LogConcave.Suspension.integral_scalar_mul_inner
