module

public import FunctionalInequalities.Analysis.EssentialExtrema.Basic
public import FunctionalInequalities.Analysis.MeasureAverage
public import FunctionalInequalities.Analysis.Iteration.Modulus
public import FunctionalInequalities.Analysis.MeasureGrowth

/-!
# Essential oscillation of finite families

Essential widths `essSup f_k − essInf f_k` of finitely many a.e. bounded functions: their
contraction on nested measures from
a pairwise deficit comparison and averaged deficits, and their uniform power decay on Euclidean
balls from a quarter-scale
contraction (Gilbarg–Trudinger (2001), Lemmas 8.23 and 17.14, measure-theoretic part). Essential
extrema only; no
representative is asserted.
-/

@[expose] public section

/-! ## Contraction and power decay of essential widths -/

section EssentialWidths

open MeasureTheory Set Metric Filter Finset

namespace FunctionalInequalities.Analysis

/--
Essential width contraction for finitely many functions on nested measures `μin ≤ μmid ≤ μout`.
Inputs: `0 ≤ f_k ≤ K`
a.e., a pairwise deficit comparison `lc (essSup f_k − f_k y) ≤ uc ∑_j (essSup f_j − f_j x) + E` (`y`
a.e. for `μin`, `x`
a.e. for `μmid`) and averaged deficits `≤ H (essSup_out f_k − essSup_in f_k) + J`. Then the
essential widths on `μin`
contract with factor `C/(1+C) < 1`, `C = 1 + N uc H/lc`, plus an explicit error. This is the
measure-theoretic step of the
rough-divergence form of Gilbarg–Trudinger (2001), Lemma 17.14. -/
theorem finite_essential_width_contraction {X : Type*} [MeasurableSpace X] {N : ℕ}
    (μout μmid μin : Measure X) [NeZero μout] [IsFiniteMeasure μmid] [NeZero μmid] [NeZero μin]
    (hmid : μmid ≤ μout) (hin : μin ≤ μmid) (f : Fin N → X → ℝ) {K lc uc H J E : ℝ}
    (hlc : 0 < lc) (huc : 0 ≤ uc) (hH : 0 ≤ H) (hf : ∀ k, Integrable (f k) μmid)
    (hf0 : ∀ k, ∀ᵐ x ∂μout, 0 ≤ f k x) (hfK : ∀ k, ∀ᵐ x ∂μout, f k x ≤ K)
    (hpair :
      ∀ k,
        ∀ᵐ y ∂μin,
          ∀ᵐ x ∂μmid,
            lc * (essSup (f k) μout - f k y) ≤ uc * (∑ j, (essSup (f j) μout - f j x)) + E)
    (havg :
      ∀ k,
        (∫ x, (essSup (f k) μout - f k x) ∂μmid) / μmid.real Set.univ ≤
          H * (essSup (f k) μout - essSup (f k) μin) + J) :
    let C := 1 + (N : ℝ) * (uc / lc * H)
    0 < C / (1 + C) ∧
      C / (1 + C) < 1 ∧
        (∑ k, (essSup (f k) μin - essInf (f k) μin)) ≤
          (C / (1 + C)) * (∑ k, (essSup (f k) μout - essInf (f k) μout)) +
            (N : ℝ) * ((uc / lc) * (N : ℝ) * J + E / lc) / (1 + C) := by
  intro C
  let outerM := fun k => essSup (f k) μout
  let outerm := fun k => essInf (f k) μout
  let innerM := fun k => essSup (f k) μin
  let innerm := fun k => essInf (f k) μin
  have hino : μin ≤ μout := hin.trans hmid
  have hlo (k : Fin N) : ∀ᵐ x ∂μin, 0 ≤ f k x :=
    (Measure.absolutelyContinuous_of_le hino).ae_le (hf0 k)
  have hhi (k : Fin N) : ∀ᵐ x ∂μin, f k x ≤ K :=
    (Measure.absolutelyContinuous_of_le hino).ae_le (hfK k)
  have horder (k : Fin N) : outerm k ≤ innerm k ∧ innerm k ≤ innerM k ∧ innerM k ≤ outerM k := by
    have hm := real_essential_bounds_mono_measure μout μin hino (f k) (hf0 k) (hfK k)
    exact ⟨hm.1, (real_essential_bounds μin (f k) (hlo k) (hhi k)).2.1, hm.2⟩
  have hdint (k : Fin N) : Integrable (fun x => outerM k - f k x) μmid :=
    (integrable_const _).sub (hf k)
  have hsint : Integrable (fun x => ∑ j, (outerM j - f j x)) μmid :=
    integrable_finsetSum _ (fun j _ => hdint j)
  have hsavg :
    (∫ x, (∑ j, (outerM j - f j x)) ∂μmid) / μmid.real Set.univ ≤
      H * (∑ j, (outerM j - innerM j)) + (N : ℝ) * J := by
    rw [integral_finsetSum _ (fun j _ => hdint j), Finset.sum_div]
    have hh := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin N))) (fun k _ => havg k)
    simpa only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] using hh
  have hwidth (k : Fin N) :
    innerM k - innerm k ≤
      (uc / lc * H) * (∑ j, (outerM j - innerM j)) + ((uc / lc) * (N : ℝ) * J + E / lc) := by
    have hcap : ∀ᵐ y ∂μin, f k y ≤ outerM k := by
      have hout : ∀ᵐ y ∂μout, f k y ≤ outerM k := ae_le_essSup ⟨K, hfK k⟩
      exact (Measure.absolutelyContinuous_of_le hino).ae_le hout
    have hd0 : ∀ᵐ y ∂μin, 0 ≤ outerM k - f k y := hcap.mono fun _ hy => sub_nonneg.mpr hy
    have hess :=
      essSup_le_average_of_ae_pairwise_bound μmid μin (fun x => ∑ j, (outerM j - f j x))
        (fun y => outerM k - f k y) hlc hsint hd0 (hpair k)
    rw [real_essSup_deficit μin (f k) (outerM k) (hlo k) (hhi k)] at hess
    calc
      _ ≤ outerM k - innerm k := sub_le_sub_right (horder k).2.2 _
      _ ≤ (uc / lc) * ((∫ x, (∑ j, (outerM j - f j x)) ∂μmid) / μmid.real Set.univ) + E / lc :=
        hess
      _ ≤ (uc / lc) * (H * (∑ j, (outerM j - innerM j)) + (N : ℝ) * J) + E / lc := by gcongr
      _ = _ := by ring
  exact
    finite_sum_width_contraction (mul_nonneg (div_nonneg huc hlc.le) hH) outerM outerm innerM
      innerm horder hwidth

/-- Uniform power decay of essential widths on Euclidean balls: a quarter-scale contraction
`ω_x(r/4) ≤ θ ω_x(r) + E (r + r²)` for every center `x ∈ T` and `r ∈ (0,1]` gives `η, Q`, chosen
before every center and
radius, with `ω_x(r) ≤ Q r^η`. Essential widths only; no representative is asserted. -/
theorem essential_width_power_of_quarter_contraction {n N : ℕ}
    (q : Fin N → EuclideanSpace ℝ (Fin n) → ℝ) (T : Set (EuclideanSpace ℝ (Fin n))) {K θ E : ℝ}
    (hK : 0 ≤ K) (hθ : 0 < θ) (hθ1 : θ < 1) (hE : 0 < E)
    (hq0 : ∀ k, ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), 0 ≤ q k x)
    (hqK : ∀ k, ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), q k x ≤ K)
    (hrec :
      ∀ x0 ∈ T,
        ∀ r ∈ Ioc (0 : ℝ) 1,
          (∑ k,
              (essSup (q k)
                  ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict
                    (ball x0 ((1 / 4) * r))) -
                essInf (q k)
                  ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict
                    (ball x0 ((1 / 4) * r))))) ≤
            θ *
                (∑ k,
                  (essSup (q k)
                      ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (ball x0 r)) -
                    essInf (q k)
                      ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (ball x0 r)))) +
              E * (r + r ^ 2)) :
    ∃ η Q : ℝ,
      0 < η ∧
        η < 1 ∧
          0 < Q ∧
            ∀ x0 ∈ T,
              ∀ r ∈ Ioc (0 : ℝ) 1,
                (∑ k,
                    (essSup (q k)
                        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (ball x0 r)) -
                      essInf (q k)
                        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (ball x0 r)))) ≤
                  Q * r ^ η := by
  obtain ⟨η, Q, hη, hη1, hQ, hpow⟩ :=
    power_modulus_of_quarter_scale_contraction hθ hθ1 (mul_nonneg (Nat.cast_nonneg N) hK) hE
  refine ⟨η, Q, hη, hη1, hQ, fun x0 hx0 r hr => ?_⟩
  let ω := fun s : ℝ =>
    ∑ k,
      (essSup (q k) ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (ball x0 s)) -
        essInf (q k) ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (ball x0 s)))
  have hext (s : ℝ) (hs : 0 < s) (k : Fin N) := by
    let ν := (volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (ball x0 s)
    let : NeZero ν := ⟨restricted_ball_ne_zero x0 hs⟩
    exact real_essential_bounds ν (q k) (ae_restrict_of_ae (hq0 k)) (ae_restrict_of_ae (hqK k))
  have hω0 : 0 ≤ ω 1 := Finset.sum_nonneg fun k _ => sub_nonneg.mpr (hext 1 one_pos k).2.1
  have hωK : ω 1 ≤ (N : ℝ) * K := by
    have hh : ω 1 ≤ ∑ _k : Fin N, K :=
      Finset.sum_le_sum fun k _ => by
        have h := hext 1 one_pos k
        linarith [h.1, h.2.2.1]
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using hh
  have hω : MonotoneOn ω (Ioc (0 : ℝ) 1) := by
    intro s hs t ht hst
    let νs := (volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (ball x0 s)
    let νt := (volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (ball x0 t)
    let : NeZero νs := ⟨restricted_ball_ne_zero x0 hs.1⟩
    let : NeZero νt := ⟨restricted_ball_ne_zero x0 ht.1⟩
    have hstμ : νs ≤ νt := Measure.restrict_mono (Metric.ball_subset_ball hst) le_rfl
    apply Finset.sum_le_sum
    intro k _
    have hm :=
      real_essential_bounds_mono_measure νt νs hstμ (q k) (ae_restrict_of_ae (hq0 k))
        (ae_restrict_of_ae (hqK k))
    linarith [hm.1, hm.2]
  exact hpow ω hω hω0 hωK (fun s hs => hrec x0 hx0 s hs) r hr

end FunctionalInequalities.Analysis

end EssentialWidths
