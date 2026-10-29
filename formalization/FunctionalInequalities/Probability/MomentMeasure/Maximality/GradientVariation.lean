import FunctionalInequalities.Analysis.Convex.ExpVariation
import FunctionalInequalities.Analysis.Convex.EssentialContinuity
import FunctionalInequalities.Probability.MomentMeasure.Maximality.BallTruncation
import FunctionalInequalities.Probability.MomentMeasure.ConjugateMass
import FunctionalInequalities.Probability.Line.Haar
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner

/-!
# Directional variation of the density of a moment potential

For a convex, lower semicontinuous potential `ψ : E → ℝ ∪ {+∞}` with `0 < ∫ e^{-ψ} < ∞` and a unit
vector `θ`, the integral `∫ |⟪∇ψ, θ⟫| e^{-ψ}` is computed line by line (Fubini along `θ`): on each
line it is the variation of a log-concave function of one variable, hence at most twice its maximum
(Cordero-Erausquin–Klartag, *Moment measures*, arXiv:1304.0630v1, proof of Lemma 4). When `ψ` is
essentially continuous (CEK Definition 2) almost every line meets the domain of `ψ` in an open
interval at whose ends `e^{-ψ}` tends to `0` (CEK Lemma 3), and the variation equals twice the
maximum.

Comparing the finite truncations `ψₖ = (ψ*|_{B_k})*` with `ψ` line by line, the maxima converge,
so `limsup_k ∫ |⟪∇ψₖ, θ⟫| e^{-ψₖ} ≤ ∫ |⟪∇ψ, θ⟫| e^{-ψ}` for an essentially continuous `ψ`
(`limsup_lintegral_directional_le`). This controls the gradient mass of `e^{-ψₖ}` in the region
where the truncation is active, which is the boundary term in CEK Theorem 8.
-/

noncomputable section

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology RealInnerProductSpace

namespace FunctionalInequalities.Probability.MomentMeasure

open FunctionalInequalities.Analysis

section OneDimensional

/-- On a continuous coercive line function, a finite value at `m` is preceded by a finite value
at least `T`. -/
private theorem exists_le_of_continuous {u : ℝ → EReal} (hu : Continuous u) {c B : ℝ}
    (hc : 0 < c) (hlow : ∀ s, ((c * |s| - B : ℝ) : EReal) ≤ u s) {m : ℝ} (hm : u m ≠ ⊤)
    (T : ℝ) : ∃ a ≤ m, u a ≠ ⊤ ∧ (T : EReal) ≤ u a := by
  set S : Set ℝ := {s | s ≤ m ∧ (T : EReal) ≤ u s} with hSdef
  set s₀ : ℝ := min m (-(|T| + |B|) / c - 1) with hs₀
  have hs₀S : s₀ ∈ S := by
    refine ⟨min_le_left _ _, le_trans ?_ (hlow s₀)⟩
    rw [EReal.coe_le_coe_iff]
    have h1 : s₀ ≤ -(|T| + |B|) / c - 1 := min_le_right _ _
    have hq : 0 ≤ (|T| + |B|) / c := by positivity
    have hq' : -(|T| + |B|) / c = -((|T| + |B|) / c) := by ring
    rw [hq'] at h1
    have hcq : c * ((|T| + |B|) / c) = |T| + |B| := by field_simp
    generalize (|T| + |B|) / c = q at hq h1 hcq ⊢
    have hneg : s₀ < 0 := by linarith
    have h2 : q + 1 ≤ |s₀| := by rw [abs_of_neg hneg]; linarith
    have h3 : c * (q + 1) ≤ c * |s₀| := mul_le_mul_of_nonneg_left h2 hc.le
    linarith [le_abs_self T, le_abs_self B]
  have hclosed : IsClosed S := isClosed_Iic.inter (isClosed_Ici.preimage hu)
  have hbdd : BddAbove S := ⟨m, fun s hs => hs.1⟩
  have ha := hclosed.csSup_mem ⟨s₀, hs₀S⟩ hbdd
  set a := sSup S
  by_cases hat : u a = ⊤
  · exfalso
    have ham : a < m := lt_of_le_of_ne ha.1 fun h => hm (h ▸ hat)
    have hev : ∀ᶠ s in 𝓝 a, (T : EReal) < u s :=
      hu.continuousAt.eventually (lt_mem_nhds (by rw [hat]; exact EReal.coe_lt_top T))
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hev
    set s := min (a + δ / 2) m
    have has : a < s := lt_min (by linarith) ham
    have hsb : dist s a < δ := by
      rw [Real.dist_eq, abs_of_pos (by linarith)]
      have := min_le_left (a + δ / 2) m
      linarith
    have hsS : s ∈ S := ⟨min_le_right _ _, (hball hsb).le⟩
    exact absurd (le_csSup hbdd hsS) (not_le.mpr has)
  · exact ⟨a, ha.1, hat, ha.2⟩

/-- **Convergence of maxima** along a line: if continuous, uniformly coercive `uₖ` increase to
`v`, then `infₖ supₛ e^{-uₖ(s)} ≤ supₛ e^{-v(s)}`. -/
private theorem iInf_iSup_exp_neg_le {u : ℕ → ℝ → EReal} {v : ℝ → EReal}
    (hcont : ∀ k, Continuous (u k)) (hmono : ∀ s, Monotone fun k => u k s)
    (hlim : ∀ s, ⨆ k, u k s = v s) {c B : ℝ} (hc : 0 < c)
    (hlow : ∀ k s, ((c * |s| - B : ℝ) : EReal) ≤ u k s) :
    ⨅ k, ⨆ s, EReal.exp (-u k s) ≤ ⨆ s, EReal.exp (-v s) := by
  refine le_of_forall_gt_imp_ge_of_dense fun r hr => ?_
  by_cases hrt : r = ⊤
  · rw [hrt]; exact le_top
  have hr0 : 0 < r := lt_of_le_of_lt (zero_le) hr
  set T : ℝ := -Real.log r.toReal with hT
  have hrT : EReal.exp (-(T : EReal)) = r := by
    rw [← EReal.coe_neg, EReal.exp_coe, hT, neg_neg,
      Real.exp_log (ENNReal.toReal_pos hr0.ne' hrt), ENNReal.ofReal_toReal hrt]
  have hTv : ∀ s, (T : EReal) < v s := by
    intro s
    have h : EReal.exp (-v s) < EReal.exp (-(T : EReal)) := by
      rw [hrT]; exact lt_of_le_of_lt (le_iSup (fun s => EReal.exp (-v s)) s) hr
    rw [EReal.exp_lt_exp_iff, EReal.neg_lt_neg_iff] at h
    exact h
  obtain ⟨q, hcq⟩ : ∃ q : ℝ, c * q = T + B := ⟨(T + B) / c, by field_simp⟩
  set R : ℝ := max 0 q + 1 with hR
  set F : ℕ → Set ℝ := fun k => {s | u k s ≤ T} with hF
  have hFc : ∀ k, IsClosed (F k) := fun k => isClosed_le (hcont k) continuous_const
  have hdir : Directed (· ⊇ ·) F := by
    intro j k
    refine ⟨max j k, fun s hs => ?_, fun s hs => ?_⟩
    · exact (hmono s (le_max_left j k)).trans hs
    · exact (hmono s (le_max_right j k)).trans hs
  have hempty : Icc (-R) R ∩ ⋂ k, F k = ∅ := by
    refine eq_empty_of_forall_notMem fun s hs => ?_
    have hle : v s ≤ T := by
      rw [← hlim s]
      exact iSup_le fun k => mem_iInter.mp hs.2 k
    exact absurd (hTv s) (not_lt.mpr hle)
  obtain ⟨k, hk⟩ := isCompact_Icc.elim_directed_family_closed F hFc hempty hdir
  refine (iInf_le _ k).trans (iSup_le fun s => ?_)
  rw [← hrT, EReal.exp_le_exp_iff, EReal.neg_le_neg_iff]
  by_cases hs : s ∈ Icc (-R) R
  · have : s ∉ F k := fun h => (eq_empty_iff_forall_notMem.mp hk) s ⟨hs, h⟩
    exact (not_le.mp this).le
  · have hsR : R < |s| := by
      rw [mem_Icc, not_and_or, not_le, not_le] at hs
      rcases hs with hs | hs
      · rw [abs_of_neg (by linarith [show 0 < R by positivity])]; linarith
      · rw [abs_of_pos (by linarith [show 0 < R by positivity])]; exact hs
    refine le_trans ?_ (hlow k s)
    rw [EReal.coe_le_coe_iff]
    have h1 : q ≤ R := (le_max_right 0 q).trans (by linarith)
    have h2 : T + B ≤ c * R := by rw [← hcq]; exact mul_le_mul_of_nonneg_left h1 hc.le
    have h3 : c * R ≤ c * |s| := mul_le_mul_of_nonneg_left hsR.le hc.le
    linarith

end OneDimensional

section OneDimensionalIntegral

/-- The integral of the variation density over a compact interval inside the convexity domain, as
a lower integral. -/
private theorem setLIntegral_Icc_eq_ofReal {G : ℝ → ℝ} {J : Set ℝ} (hJ : IsOpen J)
    (hG : ConvexOn ℝ J G) {a b : ℝ} (hab : a ≤ b) (hsub : Icc a b ⊆ J) :
    ∫⁻ s in Icc a b, ENNReal.ofReal (|derivWithin G (Ioi s) s| * Real.exp (-G s)) =
      ENNReal.ofReal (∫ s in a..b, |derivWithin G (Ioi s) s| * Real.exp (-G s)) := by
  have hcontJ : ContinuousOn G J := hG.continuousOn hJ
  have hmono : MonotoneOn (fun s => derivWithin G (Ioi s) s) (uIcc a b) := by
    rw [uIcc_of_le hab]
    exact (hG.monotoneOn_rightDeriv).mono (by rw [hJ.interior_eq]; exact hsub)
  have hint : IntervalIntegrable (fun s => |derivWithin G (Ioi s) s| * Real.exp (-G s))
      volume a b :=
    hmono.intervalIntegrable.abs.mul_continuousOn (by
      rw [uIcc_of_le hab]; exact (hcontJ.mono hsub).neg.rexp)
  have hon : IntegrableOn (fun s => |derivWithin G (Ioi s) s| * Real.exp (-G s)) (Icc a b) :=
    (integrableOn_Icc_iff_integrableOn_Ioc).mpr ((intervalIntegrable_iff_integrableOn_Ioc_of_le
      hab).mp hint)
  rw [← ofReal_integral_eq_lintegral_ofReal hon (Eventually.of_forall fun s =>
      mul_nonneg (abs_nonneg _) (Real.exp_pos _).le),
    intervalIntegral.integral_of_le hab, integral_Icc_eq_integral_Ioc]

/-- **Variation of `e^{-G}` on the line** for a convex `G : ℝ → ℝ`:
`∫ |G'₊| e^{−G} ≤ 2S` when `e^{−G} ≤ S`. -/
private theorem lintegral_variation_le {G : ℝ → ℝ} (hG : ConvexOn ℝ univ G) {S : ℝ}
    (hS : ∀ s, Real.exp (-G s) ≤ S) :
    ∫⁻ s, ENNReal.ofReal (|derivWithin G (Ioi s) s| * Real.exp (-G s)) ≤
      ENNReal.ofReal (2 * S) := by
  set f : ℝ → ℝ≥0∞ := fun s => ENNReal.ofReal (|derivWithin G (Ioi s) s| * Real.exp (-G s))
  have hGc : Continuous G := continuousOn_univ.mp (hG.continuousOn isOpen_univ)
  have hf : Measurable f :=
    ENNReal.measurable_ofReal.comp ((continuous_abs.measurable.comp
      (measurable_derivWithin_Ioi G)).mul
      (Real.measurable_exp.comp hGc.measurable.neg))
  have hsup : f = fun s => ⨆ j : ℕ, (Icc (-(j : ℝ)) j).indicator f s := by
    funext s
    refine le_antisymm ?_ (iSup_le fun j => indicator_le_self _ _ s)
    obtain ⟨j, hj⟩ := exists_nat_ge |s|
    refine le_trans (le_of_eq ?_) (le_iSup _ j)
    rw [indicator_of_mem (mem_Icc.mpr (abs_le.mp hj))]
  rw [hsup, lintegral_iSup (fun j => hf.indicator measurableSet_Icc) (fun i j hij s => by
    exact indicator_le_indicator_of_subset (Icc_subset_Icc (by
      simp only [neg_le_neg_iff, Nat.cast_le]; exact hij) (Nat.cast_le.mpr hij))
      (fun _ => zero_le) s)]
  refine iSup_le fun j => ?_
  rw [lintegral_indicator measurableSet_Icc,
    setLIntegral_Icc_eq_ofReal isOpen_univ hG (by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)])
      (subset_univ _)]
  exact ENNReal.ofReal_le_ofReal (integral_abs_rightDeriv_mul_exp_neg_le isOpen_univ hG
    (by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]) (subset_univ _) fun s _ => hS s)

/-- **Variation of `e^{-u}` for a continuous coercive line function**: if `u : ℝ → ℝ ∪ {+∞}` is
continuous, convex on its domain and above `c|s| − B`, then `e^{−u}` vanishes at the ends of its
support and `2 supₛ e^{−u(s)} ≤ ∫_{u < ∞} |u'₊| e^{−u}`. -/
private theorem two_mul_iSup_le_lintegral {u : ℝ → EReal} (hu : Continuous u)
    (hconv : ConvexOn ℝ {s | u s ≠ ⊤} fun s => (u s).toReal) {c B : ℝ} (hc : 0 < c)
    (hlow : ∀ s, ((c * |s| - B : ℝ) : EReal) ≤ u s) :
    2 * ⨆ s, EReal.exp (-u s) ≤ ∫⁻ s in {s | u s ≠ ⊤},
      ENNReal.ofReal (|derivWithin (fun s => (u s).toReal) (Ioi s) s| *
        Real.exp (-(u s).toReal)) := by
  set J : Set ℝ := {s | u s ≠ ⊤} with hJdef
  set G : ℝ → ℝ := fun s => (u s).toReal with hGdef
  have hJo : IsOpen J := isOpen_ne_fun hu continuous_const
  set I := ∫⁻ s in J, ENNReal.ofReal (|derivWithin G (Ioi s) s| * Real.exp (-G s))
  rw [ENNReal.mul_iSup]
  refine iSup_le fun m => ?_
  by_cases hm : u m = ⊤
  · rw [hm]; simp
  have hbot : ∀ s, u s ≠ ⊥ := fun s => ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (hlow s)
  have hcoe : ∀ s, u s ≠ ⊤ → u s = (G s : EReal) := fun s hs =>
    (EReal.coe_toReal hs (hbot s)).symm
  have hexp : ∀ s, u s ≠ ⊤ → EReal.exp (-u s) = ENNReal.ofReal (Real.exp (-G s)) := by
    intro s hs
    rw [hcoe s hs, ← EReal.coe_neg, EReal.exp_coe]
  rw [hexp m hm]
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  -- choose a level `T` with `2e^{-T} ≤ ε`
  obtain ⟨T, hT⟩ : ∃ T : ℝ, 2 * Real.exp (-T) ≤ ε := by
    refine ⟨-Real.log (ε / 2), ?_⟩
    rw [neg_neg, Real.exp_log (by positivity)]
    linarith
  obtain ⟨a, ham, hat, haT⟩ := exists_le_of_continuous hu hc hlow hm T
  have hlow' : ∀ s, ((c * |s| - B : ℝ) : EReal) ≤ (fun s => u (-s)) s := fun s => by
    simpa only [abs_neg] using hlow (-s)
  obtain ⟨b', hb'm, hbt, hbT⟩ := exists_le_of_continuous (hu.comp continuous_neg) hc hlow'
    (m := -m) (by simpa using hm) T
  set b := -b'
  have hmb : m ≤ b := by linarith
  have hsub : Icc a b ⊆ J := by
    intro s hs
    have hJc : Convex ℝ J := hconv.1
    have hbJ : b ∈ J := hbt
    exact hJc.ordConnected.out hat hbJ hs
  have hGa : T ≤ G a := by rw [← EReal.coe_le_coe_iff, ← hcoe a hat]; exact haT
  have hGb : T ≤ G b := by
    rw [← EReal.coe_le_coe_iff, ← hcoe b hbt]; exact hbT
  have hvar := two_mul_exp_neg_sub_le_integral_abs hJo hconv ham hmb hsub
  have hea : Real.exp (-G a) ≤ Real.exp (-T) := Real.exp_le_exp.mpr (by linarith)
  have heb : Real.exp (-G b) ≤ Real.exp (-T) := Real.exp_le_exp.mpr (by linarith)
  have hIcc : ENNReal.ofReal (∫ s in a..b, |derivWithin G (Ioi s) s| * Real.exp (-G s)) ≤ I := by
    rw [← setLIntegral_Icc_eq_ofReal hJo hconv (ham.trans hmb) hsub]
    exact lintegral_mono_set hsub
  calc 2 * ENNReal.ofReal (Real.exp (-G m))
      = ENNReal.ofReal (2 * Real.exp (-G m)) := by
        rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
    _ ≤ ENNReal.ofReal (2 * Real.exp (-G m) - Real.exp (-G a) - Real.exp (-G b)) +
          ENNReal.ofReal (2 * Real.exp (-T)) := by
        exact (ENNReal.ofReal_le_ofReal (by linarith)).trans ENNReal.ofReal_add_le
    _ ≤ I + ε := by
        gcongr
        · exact (ENNReal.ofReal_le_ofReal hvar).trans hIcc
        · exact (ENNReal.ofReal_le_ofReal hT).trans_eq (ENNReal.ofReal_coe_nnreal)

end OneDimensionalIntegral

section HausdorffNull

/-- In a finite-dimensional real normed space of dimension `d`, a set of zero `d`-dimensional
Hausdorff measure is null for every additive Haar measure. -/
theorem addHaar_eq_zero_of_hausdorffMeasure_eq_zero {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
    (ν : Measure F) [ν.IsAddHaarMeasure] {A : Set F} (hA : μH[(Module.finrank ℝ F : ℝ)] A = 0) :
    ν A = 0 := by
  set d := Module.finrank ℝ F
  let e : F ≃L[ℝ] (Fin d → ℝ) := ContinuousLinearEquiv.ofFinrankEq (by simp [d])
  have h1 : μH[((Fintype.card (Fin d) : ℕ) : ℝ)] (e '' A) = 0 := by
    have h := e.lipschitz.hausdorffMeasure_image_le (Nat.cast_nonneg d) A
    rw [Fintype.card_fin]
    rw [hA, mul_zero] at h
    exact le_antisymm h (zero_le)
  rw [hausdorffMeasure_pi_real] at h1
  set em : (Fin d → ℝ) ≃ᵐ F := e.symm.toHomeomorph.toMeasurableEquiv
  have : ((volume : Measure (Fin d → ℝ)).map em).IsAddHaarMeasure :=
    e.symm.isAddHaarMeasure_map volume
  have hmap : ((volume : Measure (Fin d → ℝ)).map em) A = 0 := by
    rw [MeasurableEquiv.map_apply]
    have : (em : (Fin d → ℝ) → F) ⁻¹' A = e '' A := by
      ext y
      simp [em, ContinuousLinearEquiv.image_eq_preimage_symm]
    rw [this]; exact h1
  rw [Measure.isAddLeftInvariant_eq_smul ν ((volume : Measure (Fin d → ℝ)).map em),
    Measure.smul_apply, hmap, smul_zero]

end HausdorffNull

section Lines

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The projection along a unit vector `θ` onto `θ^⊥`. -/
private def lineProj {θ : E} (hθ : ‖θ‖ = 1) : E →L[ℝ] (ℝ ∙ θ)ᗮ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.fst ℝ (ℝ ∙ θ)ᗮ ℝ).comp (Probability.lineEquiv hθ).symm.toLinearMap)

omit [MeasurableSpace E] [BorelSpace E] in
private theorem lineProj_apply {θ : E} (hθ : ‖θ‖ = 1) (z : (ℝ ∙ θ)ᗮ) (s : ℝ) :
    lineProj hθ ((z : E) + s • θ) = z := by
  have h : (Probability.lineEquiv hθ).symm ((z : E) + s • θ) = (z, s) := by
    rw [LinearEquiv.symm_apply_eq, Probability.lineEquiv_apply]
  simp [lineProj, h]

/-- **Lines missing a Hausdorff-null set** (Cordero-Erausquin–Klartag, arXiv:1304.0630v1, proof
of Lemma 3): if `H^{n−1}(N) = 0`, then almost every line parallel to the unit vector `θ` misses
`N`. -/
theorem addHaar_setOf_exists_line_mem_eq_zero {θ : E} (hθ : ‖θ‖ = 1) {N : Set E}
    (hN : μH[(Module.finrank ℝ E : ℝ) - 1] N = 0) :
    (Measure.addHaar : Measure (ℝ ∙ θ)ᗮ) {z : (ℝ ∙ θ)ᗮ | ∃ s : ℝ, (z : E) + s • θ ∈ N} = 0 := by
  have hθ0 : θ ≠ 0 := by
    intro h; rw [h, norm_zero] at hθ; exact zero_ne_one hθ
  have hdim : (Module.finrank ℝ (ℝ ∙ θ)ᗮ : ℝ) = (Module.finrank ℝ E : ℝ) - 1 := by
    have h := Submodule.finrank_add_finrank_orthogonal (ℝ ∙ θ)
    rw [finrank_span_singleton hθ0] at h
    rw [← h]; push_cast; ring_nf
  have hpos : 1 ≤ Module.finrank ℝ E := by
    have : Nontrivial E := nontrivial_of_ne θ 0 hθ0
    exact Module.finrank_pos
  have hsub : {z : (ℝ ∙ θ)ᗮ | ∃ s : ℝ, (z : E) + s • θ ∈ N} ⊆ lineProj hθ '' N := by
    rintro z ⟨s, hs⟩
    exact ⟨_, hs, lineProj_apply hθ z s⟩
  refine measure_mono_null hsub (addHaar_eq_zero_of_hausdorffMeasure_eq_zero _ ?_)
  rw [hdim]
  have hd0 : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) - 1 := by
    have : (1 : ℝ) ≤ Module.finrank ℝ E := by exact_mod_cast hpos
    linarith
  have h := (lineProj hθ).lipschitz.hausdorffMeasure_image_le hd0 N
  rw [hN, mul_zero] at h
  exact le_antisymm h (zero_le)

/-- **Fubini for null sets**: a Lebesgue-null Borel set meets almost every line parallel to `θ`
in a null set. -/
theorem ae_ae_line_notMem {θ : E} (hθ : ‖θ‖ = 1) {B : Set E} (hB : MeasurableSet B)
    (h0 : volume B = 0) :
    ∀ᵐ z : (ℝ ∙ θ)ᗮ ∂(Measure.addHaar : Measure (ℝ ∙ θ)ᗮ), ∀ᵐ s : ℝ, (z : E) + s • θ ∉ B := by
  obtain ⟨c, -, -, hfub⟩ := Probability.exists_lintegral_line (volume : Measure E) hθ
  have hm : Measurable (B.indicator (1 : E → ℝ≥0∞)) := measurable_one.indicator hB
  have h := hfub _ hm
  rw [lintegral_indicator_one hB, h0, mul_zero] at h
  have hmeas : Measurable fun p : (ℝ ∙ θ)ᗮ × ℝ =>
      B.indicator (1 : E → ℝ≥0∞) ((p.1 : E) + p.2 • θ) :=
    hm.comp ((continuous_subtype_val.comp continuous_fst).add
      (continuous_snd.smul continuous_const)).measurable
  have hz := (lintegral_eq_zero_iff hmeas.lintegral_prod_right').mp h.symm
  filter_upwards [hz] with z hz
  have hs : Measurable fun s : ℝ => B.indicator (1 : E → ℝ≥0∞) ((z : E) + s • θ) :=
    hm.comp (continuous_const.add (continuous_id.smul continuous_const)).measurable
  filter_upwards [(lintegral_eq_zero_iff hs).mp hz] with s hs'
  intro hmem
  simp [indicator_of_mem hmem] at hs'

end Lines

section Directional

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem lineMap_eq (z θ : E) (s : ℝ) :
    AffineMap.lineMap z (z + θ) s = z + s • θ := by
  rw [AffineMap.lineMap_apply_module', add_sub_cancel_left, add_comm]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- A convex function restricted to a line is convex. -/
private theorem convexOn_line {S : Set E} {f : E → ℝ} (hf : ConvexOn ℝ S f) (z θ : E) :
    ConvexOn ℝ {s : ℝ | z + s • θ ∈ S} fun s => f (z + s • θ) := by
  have h := hf.comp_affineMap (AffineMap.lineMap z (z + θ))
  have hset : (AffineMap.lineMap z (z + θ) : ℝ →ᵃ[ℝ] E) ⁻¹' S = {s : ℝ | z + s • θ ∈ S} := by
    ext s; simp only [mem_preimage, lineMap_eq]; rfl
  have hfun : (f ∘ (AffineMap.lineMap z (z + θ) : ℝ →ᵃ[ℝ] E)) = fun s => f (z + s • θ) := by
    funext s; simp only [Function.comp_apply, lineMap_eq]
  rwa [hset, hfun] at h

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- On a line orthogonal to `θ` the distance to the origin dominates the parameter. -/
private theorem abs_le_norm_add_smul {θ : E} (hθ : ‖θ‖ = 1) {z : E} (hz : inner ℝ θ z = 0)
    (s : ℝ) : |s| ≤ ‖z + s • θ‖ ∧ ‖z‖ ≤ ‖z + s • θ‖ := by
  have hsq : ‖z + s • θ‖ ^ 2 = ‖z‖ ^ 2 + s ^ 2 := by
    rw [norm_add_sq_real, norm_smul, Real.norm_eq_abs, hθ, real_inner_smul_right,
      real_inner_comm, hz, mul_one, mul_zero, mul_zero, add_zero, sq_abs]
  constructor
  · rw [← sq_le_sq₀ (abs_nonneg s) (norm_nonneg _), sq_abs, hsq]
    nlinarith [sq_nonneg ‖z‖]
  · rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), hsq]
    nlinarith [sq_nonneg s]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Derivative of a function along a line at a differentiability point. -/
private theorem rightDeriv_line_eq {f : E → ℝ} {z θ : E} {s : ℝ}
    (hd : DifferentiableAt ℝ f (z + s • θ)) [CompleteSpace E] :
    derivWithin (fun t => f (z + t • θ)) (Ioi s) s = inner ℝ (gradient f (z + s • θ)) θ := by
  have hline : HasDerivAt (fun t : ℝ => z + t • θ) θ s := by
    simpa using ((hasDerivAt_id s).smul_const θ).const_add z
  have h : HasDerivAt (fun t => f (z + t • θ)) (fderiv ℝ f (z + s • θ) θ) s :=
    hd.hasFDerivAt.comp_hasDerivAt s hline
  rw [h.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ioi s)]
  rw [show gradient f (z + s • θ) = (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f (z + s • θ))
    from rfl, InnerProductSpace.toDual_symm_apply]

section Truncated

variable {ψ : E → EReal}

omit [MeasurableSpace E] [BorelSpace E] in
/-- The conjugates of the ball truncations of radii `c + k` increase to `ψ`. -/
theorem iSup_legendre_ballTruncate_add (hψ : ConvexPotential ψ) (hlsc : LowerSemicontinuous ψ)
    (hne : ∃ x, ψ x ≠ ⊤) {c : ℝ} (hc : 0 ≤ c) (x : E) :
    ⨆ k : ℕ, legendre (ballTruncate (legendre ψ) (c + k)) x = ψ x := by
  refine le_antisymm (iSup_le fun k => legendre_ballTruncate_le hψ hlsc hne _ x) ?_
  rw [← iSup_legendre_ballTruncate hψ hlsc hne x]
  exact iSup_mono fun k => legendre_ballTruncate_mono _ (by linarith) x

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
  [BorelSpace E] in
private theorem density_eq_ofReal {φ : E → EReal} {x : E} (ht : φ x ≠ ⊤) (hb : φ x ≠ ⊥) :
    density φ x = ENNReal.ofReal (Real.exp (-(φ x).toReal)) := by
  rw [density, ← EReal.coe_toReal ht hb, ← EReal.coe_neg, EReal.exp_coe, EReal.toReal_coe]

/-- The line-by-line variation bound for the truncated potentials. -/
private theorem lintegral_line_truncate_le {c b : ℝ}
    (hlow : ∀ x, ((c * ‖x‖ - b : ℝ) : EReal) ≤ ψ x) (hc : 0 ≤ c) {x₁ : E} (hx₁ : ψ x₁ ≠ ⊤)
    {θ : E} (hθ : ‖θ‖ = 1) (k : ℕ) :
    ∀ᵐ z : (ℝ ∙ θ)ᗮ ∂(Measure.addHaar : Measure (ℝ ∙ θ)ᗮ),
      ∫⁻ s : ℝ, ENNReal.ofReal (|inner ℝ (gradient (fun x =>
          (legendre (ballTruncate (legendre ψ) (c + k)) x).toReal) ((z : E) + s • θ)) θ| *
        Real.exp (-(legendre (ballTruncate (legendre ψ) (c + k)) ((z : E) + s • θ)).toReal)) ≤
      2 * ⨆ s : ℝ, density (legendre (ballTruncate (legendre ψ) (c + k))) ((z : E) + s • θ) := by
  set ψk := legendre (ballTruncate (legendre ψ) (c + k)) with hψk
  set Ψk : E → ℝ := fun x => (ψk x).toReal with hΨk
  have hk : c ≤ c + k := by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hconv : ConvexOn ℝ univ Ψk := convexOn_toReal_legendre_ballTruncate hlow hc hk hx₁
  have hfin : ∀ y, ψk y ≠ ⊤ ∧ ψk y ≠ ⊥ := legendre_ballTruncate_ne_top_ne_bot hlow hc hk hx₁
  have hB : MeasurableSet {x | ¬DifferentiableAt ℝ Ψk x} :=
    (measurableSet_of_differentiableAt ℝ Ψk).compl
  have h0 : volume {x | ¬DifferentiableAt ℝ Ψk x} = 0 := by
    have h := hconv.ae_differentiableAt_of_isOpen volume isOpen_univ
    exact ae_iff.mp (h.mono fun x hx => hx (mem_univ x))
  filter_upwards [ae_ae_line_notMem hθ hB h0] with z hz
  set G : ℝ → ℝ := fun s => Ψk ((z : E) + s • θ) with hG
  have hGc : ConvexOn ℝ univ G := by
    have h := convexOn_line hconv (z : E) θ
    simpa only [mem_univ, ofPred_true] using h
  have hlowk : ∀ y, ((c * ‖y‖ - b : ℝ) : EReal) ≤ ψk y :=
    linear_lower_bound_legendre_ballTruncate hlow hc hk
  have hdens : ∀ y, density ψk y = ENNReal.ofReal (Real.exp (-Ψk y)) := fun y =>
    density_eq_ofReal (hfin y).1 (hfin y).2
  have hbound : ∀ y, density ψk y ≤ ENNReal.ofReal (Real.exp b) := by
    intro y
    rw [hdens y]
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
    have h := hlowk y
    rw [← EReal.coe_toReal (hfin y).1 (hfin y).2, EReal.coe_le_coe_iff] at h
    nlinarith [norm_nonneg y]
  set S := ⨆ s : ℝ, density ψk ((z : E) + s • θ) with hSdef
  have hSt : S ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (iSup_le fun s => hbound _)
  have hS : ∀ s, Real.exp (-G s) ≤ S.toReal := by
    intro s
    have h := le_iSup (fun s : ℝ => density ψk ((z : E) + s • θ)) s
    rw [hdens] at h
    exact (ENNReal.ofReal_le_iff_le_toReal hSt).mp h
  have hcongr : (fun s : ℝ => ENNReal.ofReal (|inner ℝ (gradient Ψk ((z : E) + s • θ)) θ| *
      Real.exp (-Ψk ((z : E) + s • θ)))) =ᵐ[volume]
      fun s => ENNReal.ofReal (|derivWithin G (Ioi s) s| * Real.exp (-G s)) := by
    filter_upwards [hz] with s hs
    have hd : DifferentiableAt ℝ Ψk ((z : E) + s • θ) := not_not.mp hs
    rw [hG, rightDeriv_line_eq hd]
  rw [lintegral_congr_ae hcongr]
  refine (lintegral_variation_le hGc hS).trans_eq ?_
  rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_toReal hSt, ENNReal.ofReal_ofNat]

/-- The line-by-line lower bound for an essentially continuous potential (CEK Lemma 3 and the
boundary term of Lemma 9). -/
private theorem two_mul_iSup_le_lintegral_line (hψ : ConvexPotential ψ)
    (hess : EssentiallyContinuous ψ) {c b : ℝ} (hc : 0 < c)
    (hlow : ∀ x, ((c * ‖x‖ - b : ℝ) : EReal) ≤ ψ x) {θ : E} (hθ : ‖θ‖ = 1) :
    ∀ᵐ z : (ℝ ∙ θ)ᗮ ∂(Measure.addHaar : Measure (ℝ ∙ θ)ᗮ),
      2 * ⨆ s : ℝ, density ψ ((z : E) + s • θ) ≤
        ∫⁻ s : ℝ, (interior {x | ψ x ≠ ⊤} ∩
          {x | DifferentiableAt ℝ (fun x => (ψ x).toReal) x}).indicator
          (fun x => ENNReal.ofReal (|inner ℝ (gradient (fun x => (ψ x).toReal) x) θ| *
            Real.exp (-(ψ x).toReal))) ((z : E) + s • θ) := by
  set K := {x | ψ x ≠ ⊤} with hKdef
  set Ψ : E → ℝ := fun x => (ψ x).toReal with hΨ
  set N := {x | ¬ContinuousAt ψ x} with hNdef
  have hlines : ∀ᵐ z : (ℝ ∙ θ)ᗮ ∂(Measure.addHaar : Measure (ℝ ∙ θ)ᗮ),
      z ∉ {z : (ℝ ∙ θ)ᗮ | ∃ s : ℝ, (z : E) + s • θ ∈ N} :=
    measure_eq_zero_iff_ae_notMem.mp (addHaar_setOf_exists_line_mem_eq_zero hθ hess.2)
  have hconvI : ConvexOn ℝ (interior K) Ψ :=
    hψ.convexOn_toReal.subset interior_subset hψ.convex_domain.interior
  set B₀ := interior K ∩ {x | ¬DifferentiableAt ℝ Ψ x} with hB₀
  have hB₀m : MeasurableSet B₀ :=
    isOpen_interior.measurableSet.inter (measurableSet_of_differentiableAt ℝ Ψ).compl
  have hB₀0 : volume B₀ = 0 := by
    have h := hconvI.ae_differentiableAt_of_isOpen volume isOpen_interior
    refine measure_mono_null (fun x (hx : x ∈ B₀) => ?_) (ae_iff.mp h)
    exact fun hx' => hx.2 (hx' hx.1)
  filter_upwards [hlines, ae_ae_line_notMem hθ hB₀m hB₀0] with z hzN hzB
  have hzθ : inner ℝ θ (z : E) = 0 := Submodule.mem_orthogonal_singleton_iff_inner_right.mp z.2
  have hnotN : ∀ s : ℝ, ContinuousAt ψ ((z : E) + s • θ) := fun s => by
    by_contra h
    exact hzN ⟨s, h⟩
  set u : ℝ → EReal := fun s => ψ ((z : E) + s • θ) with hu
  have hline : Continuous fun s : ℝ => (z : E) + s • θ :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hucont : Continuous u := continuous_iff_continuousAt.mpr fun s =>
    (hnotN s).comp (f := fun s : ℝ => (z : E) + s • θ) hline.continuousAt
  have huconv : ConvexOn ℝ {s | u s ≠ ⊤} fun s => (u s).toReal :=
    convexOn_line hψ.convexOn_toReal (z : E) θ
  have hulow : ∀ s, ((c * |s| - b : ℝ) : EReal) ≤ u s := by
    intro s
    refine le_trans (EReal.coe_le_coe_iff.mpr ?_) (hlow _)
    have := (abs_le_norm_add_smul hθ hzθ s).1
    nlinarith
  have hmain := two_mul_iSup_le_lintegral hucont huconv hc hulow
  refine hmain.trans ?_
  have hJm : MeasurableSet {s | u s ≠ ⊤} := (isOpen_ne_fun hucont continuous_const).measurableSet
  rw [← lintegral_indicator hJm]
  refine lintegral_mono_ae ?_
  filter_upwards [hzB] with s hs
  by_cases hsJ : s ∈ {s | u s ≠ ⊤}
  · rw [indicator_of_mem hsJ]
    have hxK : (z : E) + s • θ ∈ K := hsJ
    have hxI : (z : E) + s • θ ∈ interior K := by
      by_contra hI
      exact not_continuousAt_of_mem_domain_diff_interior ⟨hxK, hI⟩ (hnotN s)
    have hxd : DifferentiableAt ℝ Ψ ((z : E) + s • θ) := by
      by_contra hd
      exact hs ⟨hxI, hd⟩
    rw [indicator_of_mem (show (z : E) + s • θ ∈ interior K ∩
      {x | DifferentiableAt ℝ (fun x => (ψ x).toReal) x} from ⟨hxI, hxd⟩)]
    rw [show (fun s => (u s).toReal) = fun s => Ψ ((z : E) + s • θ) from rfl,
      rightDeriv_line_eq hxd]
  · rw [indicator_of_notMem hsJ]
    exact zero_le

/-- **Uniform gradient mass of the truncated potentials** (Cordero-Erausquin–Klartag,
arXiv:1304.0630v1, proof of Lemma 4). For a lower semicontinuous potential `ψ ≥ c‖·‖ − b`
(`c > 0`) finite somewhere and a unit vector `θ`, the integrals
`∫ |⟪∇ψₖ, θ⟫| e^{−ψₖ}` of the ball truncations `ψₖ = (ψ*|_{B_{c+k}})*` are bounded uniformly in
`k`: on each line `e^{−ψₖ}` is log-concave, so its variation is at most twice its maximum, which is
at most `e^{b − c‖z‖}` at distance `‖z‖` from the origin. -/
theorem lintegral_directional_truncate_le_const {c b : ℝ} (hc : 0 < c)
    (hlow : ∀ x, ((c * ‖x‖ - b : ℝ) : EReal) ≤ ψ x) {x₁ : E} (hx₁ : ψ x₁ ≠ ⊤)
    {θ : E} (hθ : ‖θ‖ = 1) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ k : ℕ,
      ∫⁻ x, ENNReal.ofReal (|inner ℝ (gradient (fun x =>
          (legendre (ballTruncate (legendre ψ) (c + k)) x).toReal) x) θ| *
        Real.exp (-(legendre (ballTruncate (legendre ψ) (c + k)) x).toReal)) ≤ C := by
  obtain ⟨c', hc'0, hc'top, hfub⟩ := Probability.exists_lintegral_line (volume : Measure E) hθ
  set ψk : ℕ → E → EReal := fun k => legendre (ballTruncate (legendre ψ) (c + k)) with hψk
  have hk : ∀ k : ℕ, c ≤ c + k := fun k => by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hlowk : ∀ k y, ((c * ‖y‖ - b : ℝ) : EReal) ≤ ψk k y := fun k =>
    linear_lower_bound_legendre_ballTruncate hlow hc.le (hk k)
  have hcont : ∀ k, Continuous fun y => (ψk k y).toReal := fun k =>
    continuousOn_univ.mp ((convexOn_toReal_legendre_ballTruncate hlow hc.le (hk k) hx₁).continuousOn
      isOpen_univ)
  set Fk : ℕ → E → ℝ≥0∞ := fun k x => ENNReal.ofReal (|inner ℝ (gradient (fun x =>
      (ψk k x).toReal) x) θ| * Real.exp (-(ψk k x).toReal)) with hFk
  have hFkm : ∀ k, Measurable (Fk k) := fun k =>
    ENNReal.measurable_ofReal.comp ((continuous_abs.measurable.comp
      (Measurable.inner (measurable_gradient_toReal (ψk k)) measurable_const)).mul
      (Real.measurable_exp.comp (hcont k).measurable.neg))
  set Sk : ℕ → (ℝ ∙ θ)ᗮ → ℝ≥0∞ := fun k z => ⨆ s : ℝ, density (ψk k) ((z : E) + s • θ) with hSk
  have hA : ∀ k, c' * ∫⁻ x, Fk k x ≤ ∫⁻ z, 2 * Sk k z ∂(Measure.addHaar) := fun k => by
    rw [hfub _ (hFkm k)]
    exact lintegral_mono_ae (lintegral_line_truncate_le hlow hc.le hx₁ hθ k)
  have hzθ : ∀ z : (ℝ ∙ θ)ᗮ, inner ℝ θ (z : E) = 0 := fun z =>
    Submodule.mem_orthogonal_singleton_iff_inner_right.mp z.2
  have hdom : ∀ k z, Sk k z ≤ ENNReal.ofReal (Real.exp (b - c * ‖(z : E)‖)) := by
    intro k z
    refine iSup_le fun s => ?_
    have h1 : ((c * ‖(z : E)‖ - b : ℝ) : EReal) ≤ ψk k ((z : E) + s • θ) := by
      refine le_trans (EReal.coe_le_coe_iff.mpr ?_) (hlowk k _)
      have := (abs_le_norm_add_smul hθ (hzθ z) s).2
      nlinarith
    have h2 := EReal.exp_monotone (EReal.neg_le_neg_iff.mpr h1)
    rw [← EReal.coe_neg, EReal.exp_coe, neg_sub] at h2
    exact h2
  have hdomfin : ∫⁻ z, 2 * ENNReal.ofReal (Real.exp (b - c * ‖(z : E)‖))
      ∂(Measure.addHaar : Measure (ℝ ∙ θ)ᗮ) ≠ ⊤ := by
    have hm : Measurable fun z : (ℝ ∙ θ)ᗮ => ENNReal.ofReal (Real.exp (b - c * ‖(z : E)‖)) :=
      (ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_const.sub
        (continuous_const.mul (continuous_norm.comp continuous_subtype_val))))).measurable
    rw [lintegral_const_mul _ hm]
    refine ENNReal.mul_ne_top ENNReal.ofNat_ne_top (ne_of_lt ?_)
    exact (integrable_exp_sub_norm (Measure.addHaar : Measure (ℝ ∙ θ)ᗮ) hc b).lintegral_lt_top
  have h2mul : ∀ {a a' : ℝ≥0∞}, a ≤ a' → 2 * a ≤ 2 * a' := fun h => by gcongr
  refine ⟨c'⁻¹ * ∫⁻ z, 2 * ENNReal.ofReal (Real.exp (b - c * ‖(z : E)‖))
      ∂(Measure.addHaar : Measure (ℝ ∙ θ)ᗮ),
    ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hc'0) hdomfin, fun k => ?_⟩
  rw [← ENNReal.mul_le_mul_iff_right hc'0 hc'top, ← mul_assoc, ENNReal.mul_inv_cancel hc'0 hc'top,
    one_mul]
  exact (hA k).trans (lintegral_mono fun z => h2mul (hdom k z))

/-- **Gradient mass of the truncated potentials** (Cordero-Erausquin–Klartag,
arXiv:1304.0630v1, Lemmas 3, 4 and 9). Let `ψ : E → ℝ ∪ {+∞}` be convex and essentially
continuous with `ψ ≥ c‖·‖ − b` (`c > 0`), finite somewhere, let `ψₖ = (ψ*|_{B_{c+k}})*` and let
`θ` be a unit vector. For every `ε > 0`, `∫ |⟪∇ψₖ, θ⟫| e^{−ψₖ}` is eventually at most
`∫_G |⟪∇ψ, θ⟫| e^{−ψ} + ε`, where `G` is the set of differentiability points in the interior of
the domain of `ψ`: on almost every line the maxima of `e^{−ψₖ}` converge to that of `e^{−ψ}`,
and essential continuity makes the variation of `e^{−ψ}` on the line equal to twice its maximum. -/
theorem eventually_lintegral_directional_truncate_le (hψ : ConvexPotential ψ)
    (hess : EssentiallyContinuous ψ) {c b : ℝ} (hc : 0 < c)
    (hlow : ∀ x, ((c * ‖x‖ - b : ℝ) : EReal) ≤ ψ x) {x₁ : E} (hx₁ : ψ x₁ ≠ ⊤)
    {θ : E} (hθ : ‖θ‖ = 1) :
    ∀ ε : ℝ≥0∞, ε ≠ 0 → ∀ᶠ k : ℕ in atTop,
      ∫⁻ x, ENNReal.ofReal (|inner ℝ (gradient (fun x =>
          (legendre (ballTruncate (legendre ψ) (c + k)) x).toReal) x) θ| *
        Real.exp (-(legendre (ballTruncate (legendre ψ) (c + k)) x).toReal)) ≤
      (∫⁻ x, (interior {x | ψ x ≠ ⊤} ∩
          {x | DifferentiableAt ℝ (fun x => (ψ x).toReal) x}).indicator
          (fun x => ENNReal.ofReal (|inner ℝ (gradient (fun x => (ψ x).toReal) x) θ| *
            Real.exp (-(ψ x).toReal))) x) + ε := by
  have hlsc := hess.1
  have hne : ∃ x, ψ x ≠ ⊤ := ⟨x₁, hx₁⟩
  obtain ⟨c', hc'0, hc'top, hfub⟩ := Probability.exists_lintegral_line (volume : Measure E) hθ
  set ψk : ℕ → E → EReal := fun k => legendre (ballTruncate (legendre ψ) (c + k)) with hψk
  have hk : ∀ k : ℕ, c ≤ c + k := fun k => by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hfin : ∀ k y, ψk k y ≠ ⊤ ∧ ψk k y ≠ ⊥ := fun k =>
    legendre_ballTruncate_ne_top_ne_bot hlow hc.le (hk k) hx₁
  have hlowk : ∀ k y, ((c * ‖y‖ - b : ℝ) : EReal) ≤ ψk k y := fun k =>
    linear_lower_bound_legendre_ballTruncate hlow hc.le (hk k)
  have hcont : ∀ k, Continuous fun y => (ψk k y).toReal := fun k =>
    continuousOn_univ.mp ((convexOn_toReal_legendre_ballTruncate hlow hc.le (hk k) hx₁).continuousOn
      isOpen_univ)
  set Fk : ℕ → E → ℝ≥0∞ := fun k x => ENNReal.ofReal (|inner ℝ (gradient (fun x =>
      (ψk k x).toReal) x) θ| * Real.exp (-(ψk k x).toReal)) with hFk
  set F : E → ℝ≥0∞ := (interior {x | ψ x ≠ ⊤} ∩
      {x | DifferentiableAt ℝ (fun x => (ψ x).toReal) x}).indicator
      (fun x => ENNReal.ofReal (|inner ℝ (gradient (fun x => (ψ x).toReal) x) θ| *
        Real.exp (-(ψ x).toReal))) with hF
  have hFkm : ∀ k, Measurable (Fk k) := fun k =>
    ENNReal.measurable_ofReal.comp ((continuous_abs.measurable.comp
      (Measurable.inner (measurable_gradient_toReal (ψk k)) measurable_const)).mul
      (Real.measurable_exp.comp (hcont k).measurable.neg))
  have hΨm : Measurable fun x => (ψ x).toReal := measurable_ereal_toReal.comp hlsc.measurable
  have hFm : Measurable F :=
    (ENNReal.measurable_ofReal.comp ((continuous_abs.measurable.comp
      (Measurable.inner (measurable_gradient_toReal ψ) measurable_const)).mul
      (Real.measurable_exp.comp hΨm.neg))).indicator
      (isOpen_interior.measurableSet.inter (measurableSet_of_differentiableAt ℝ _))
  set Sk : ℕ → (ℝ ∙ θ)ᗮ → ℝ≥0∞ := fun k z => ⨆ s : ℝ, density (ψk k) ((z : E) + s • θ) with hSk
  set S : (ℝ ∙ θ)ᗮ → ℝ≥0∞ := fun z => ⨆ s : ℝ, density ψ ((z : E) + s • θ) with hS
  -- the two line estimates
  have hA : ∀ k, c' * ∫⁻ x, Fk k x ≤ ∫⁻ z, 2 * Sk k z ∂(Measure.addHaar) := fun k => by
    rw [hfub _ (hFkm k)]
    exact lintegral_mono_ae (lintegral_line_truncate_le hlow hc.le hx₁ hθ k)
  have hB : ∫⁻ z, 2 * S z ∂(Measure.addHaar) ≤ c' * ∫⁻ x, F x := by
    rw [hfub _ hFm]
    exact lintegral_mono_ae (two_mul_iSup_le_lintegral_line hψ hess hc hlow hθ)
  -- domination, measurability and monotonicity of the line maxima
  have hzθ : ∀ z : (ℝ ∙ θ)ᗮ, inner ℝ θ (z : E) = 0 := fun z =>
    Submodule.mem_orthogonal_singleton_iff_inner_right.mp z.2
  have hdom : ∀ k z, Sk k z ≤ ENNReal.ofReal (Real.exp (b - c * ‖(z : E)‖)) := by
    intro k z
    refine iSup_le fun s => ?_
    have h1 : ((c * ‖(z : E)‖ - b : ℝ) : EReal) ≤ ψk k ((z : E) + s • θ) := by
      refine le_trans (EReal.coe_le_coe_iff.mpr ?_) (hlowk k _)
      have := (abs_le_norm_add_smul hθ (hzθ z) s).2
      nlinarith
    have h2 := EReal.exp_monotone (EReal.neg_le_neg_iff.mpr h1)
    rw [← EReal.coe_neg, EReal.exp_coe, neg_sub] at h2
    exact h2
  have hdomfin : ∫⁻ z, 2 * ENNReal.ofReal (Real.exp (b - c * ‖(z : E)‖))
      ∂(Measure.addHaar : Measure (ℝ ∙ θ)ᗮ) ≠ ⊤ := by
    have hm : Measurable fun z : (ℝ ∙ θ)ᗮ => ENNReal.ofReal (Real.exp (b - c * ‖(z : E)‖)) :=
      (ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_const.sub
        (continuous_const.mul (continuous_norm.comp continuous_subtype_val))))).measurable
    rw [lintegral_const_mul _ hm]
    refine ENNReal.mul_ne_top ENNReal.ofNat_ne_top (ne_of_lt ?_)
    exact (integrable_exp_sub_norm (Measure.addHaar : Measure (ℝ ∙ θ)ᗮ) hc b).lintegral_lt_top
  have hSkm : ∀ k, Measurable (Sk k) := by
    intro k
    refine LowerSemicontinuous.measurable (lowerSemicontinuous_iSup fun s => ?_)
    refine Continuous.lowerSemicontinuous ?_
    have hrw : (fun z : (ℝ ∙ θ)ᗮ => density (ψk k) ((z : E) + s • θ)) =
        fun z : (ℝ ∙ θ)ᗮ => ENNReal.ofReal (Real.exp (-(ψk k ((z : E) + s • θ)).toReal)) := by
      funext z; exact density_eq_ofReal (hfin k _).1 (hfin k _).2
    rw [hrw]
    exact ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp ((hcont k).comp
      (continuous_subtype_val.add continuous_const)).neg)
  have h2mul : ∀ {a a' : ℝ≥0∞}, a ≤ a' → 2 * a ≤ 2 * a' := fun h => by gcongr
  have hanti : Antitone fun k => fun z => 2 * Sk k z := by
    intro j k hjk z
    refine h2mul (iSup_mono fun s => ?_)
    exact EReal.exp_monotone (EReal.neg_le_neg_iff.mpr
      (legendre_ballTruncate_mono _ (by
        have : (j : ℝ) ≤ k := Nat.cast_le.mpr hjk
        linarith) _))
  -- convergence of the line maxima
  have hinf : ∀ z, ⨅ k, Sk k z ≤ S z := by
    intro z
    refine iInf_iSup_exp_neg_le (u := fun k (s : ℝ) => ψk k ((z : E) + s • θ))
      (v := fun s : ℝ => ψ ((z : E) + s • θ)) (B := b) (fun k => ?_) (fun s j k hjk => ?_)
      (fun s => iSup_legendre_ballTruncate_add hψ hlsc hne hc.le _) hc (fun k s => ?_)
    · have hcoe : (fun s : ℝ => ψk k ((z : E) + s • θ)) =
          fun s : ℝ => (((ψk k ((z : E) + s • θ)).toReal : ℝ) : EReal) := by
        funext s; exact (EReal.coe_toReal (hfin k _).1 (hfin k _).2).symm
      rw [hcoe]
      have hline : Continuous fun s : ℝ => (z : E) + s • θ :=
        continuous_const.add (continuous_id.smul continuous_const)
      exact continuous_coe_real_ereal.comp ((hcont k).comp hline)
    · exact legendre_ballTruncate_mono _ (by
        have : (j : ℝ) ≤ k := Nat.cast_le.mpr hjk
        linarith) _
    · refine le_trans (EReal.coe_le_coe_iff.mpr ?_) (hlowk k _)
      have := (abs_le_norm_add_smul hθ (hzθ z) s).1
      nlinarith
  have hlim : ⨅ k, ∫⁻ z, 2 * Sk k z ∂(Measure.addHaar : Measure (ℝ ∙ θ)ᗮ) ≤ c' * ∫⁻ x, F x := by
    rw [← lintegral_iInf (fun k => (hSkm k).const_mul 2) hanti
      (ne_top_of_le_ne_top hdomfin (lintegral_mono fun z => h2mul (hdom 0 z)))]
    refine le_trans (lintegral_mono fun z => ?_) hB
    rw [← ENNReal.mul_iInf_of_ne two_ne_zero ENNReal.ofNat_ne_top]
    exact h2mul (hinf z)
  intro ε hε
  by_cases hFt : ∫⁻ x, F x = ⊤
  · refine Eventually.of_forall fun k => ?_
    rw [hFt, top_add]; exact le_top
  have hL : c' * ∫⁻ x, F x ≠ ⊤ := ENNReal.mul_ne_top hc'top hFt
  have hlt : ⨅ k, ∫⁻ z, 2 * Sk k z ∂(Measure.addHaar : Measure (ℝ ∙ θ)ᗮ) <
      c' * (∫⁻ x, F x) + c' * ε :=
    lt_of_le_of_lt hlim (ENNReal.lt_add_right hL (mul_ne_zero hc'0 hε))
  obtain ⟨K, hK⟩ := iInf_lt_iff.mp hlt
  refine eventually_atTop.mpr ⟨K, fun k hk => ?_⟩
  have hmono : ∫⁻ z, 2 * Sk k z ∂(Measure.addHaar : Measure (ℝ ∙ θ)ᗮ) ≤
      ∫⁻ z, 2 * Sk K z ∂(Measure.addHaar : Measure (ℝ ∙ θ)ᗮ) :=
    lintegral_mono fun z => hanti hk z
  have h := ((hA k).trans hmono).trans hK.le
  rw [← mul_add] at h
  exact (ENNReal.mul_le_mul_iff_right hc'0 hc'top).mp h

end Truncated

end Directional

end FunctionalInequalities.Probability.MomentMeasure
