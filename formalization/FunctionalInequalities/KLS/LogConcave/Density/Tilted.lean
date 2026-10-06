import FunctionalInequalities.KLS.LogConcave.Density.FromBorell
import Mathlib.MeasureTheory.Measure.Tilted

/-!
# Tilted laws of Haar measure

For a potential `W` on a finite-dimensional real inner product space and a Haar measure `m`,
the tilted law `m.tilted (-W)` has density `e^{-W} / ∫ e^{-W} dm` with respect to `m`. When it is
a probability law, `e^{-W}` is `m`-integrable; the law then has full support, and it is
log-concave when `W` is continuous and convex (its density is a log-concave Borell density for
Lebesgue measure `volume`).
-/

noncomputable section

open MeasureTheory Set

namespace FunctionalInequalities.KLS.LogConcave

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {ν : ProbabilityMeasure V}



omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [BorelSpace V] in
/-- A tilted law of total mass one has an integrable density: `e^{-W} ∈ L¹(m)`. -/
theorem integrable_exp_neg_of_eq_tilted {m : Measure V} {W : V → ℝ}
    (hνW : (ν : Measure V) = m.tilted (-W)) :
    Integrable (fun x => Real.exp (-W x)) m := by
  by_contra h
  have h' : ¬ Integrable (fun x => Real.exp ((-W) x)) m := by
    intro hI
    apply h
    simpa using hI
  have hzero : m.tilted (-W) = 0 :=
    tilted_of_not_integrable h'
  have hνzero : (ν : Measure V) = 0 := by
    rw [hνW, hzero]
  have huniv : (ν : Measure V) Set.univ = 1 := by
    simp
  rw [hνzero] at huniv
  norm_num at huniv

omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [BorelSpace V] in
/-- A tilted law of total mass one has a positive normalizing constant `∫ e^{-W} dm`. -/
theorem integral_exp_neg_pos_of_eq_tilted {m : Measure V} {W : V → ℝ}
    (hνW : (ν : Measure V) = m.tilted (-W)) :
    0 < ∫ x, Real.exp (-W x) ∂m := by
  have hint : Integrable (fun x => Real.exp (-W x)) m :=
    integrable_exp_neg_of_eq_tilted hνW
  have hm : m ≠ 0 := by
    intro hmzero
    have hzero : m.tilted (-W) = 0 := by
      simp [hmzero, Measure.tilted]
    have hνzero : (ν : Measure V) = 0 := hνW.trans hzero
    have huniv : (ν : Measure V) Set.univ = 1 := by
      simp
    rw [hνzero] at huniv
    norm_num at huniv
  have hmuniv : 0 < m Set.univ := by
    rw [pos_iff_ne_zero]
    intro hzero
    exact hm (Measure.measure_univ_eq_zero.mp hzero)
  have hsupp :
      Function.support (fun x => Real.exp (-W x)) = (Set.univ : Set V) := by
    ext x
    simp [Function.support]
  rw [integral_pos_iff_support_of_nonneg (fun x => (Real.exp_pos _).le) hint, hsupp]
  exact hmuniv

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- For convex `W` and `Z > 0`, the normalized weight `e^{-W} / Z` is log-concave:
`ρ(x)^t ρ(y)^{1-t} ≤ ρ(t x + (1 - t) y)` for `0 < t < 1`. -/
theorem rpow_mul_rpow_le_of_convexOn {W : V → ℝ} (hconv : ConvexOn ℝ Set.univ W) {Z : ℝ}
    (hZ : 0 < Z) (x y : V) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    (Real.exp (-W x) / Z) ^ t * (Real.exp (-W y) / Z) ^ (1 - t) ≤
      Real.exp (-W (t • x + (1 - t) • y)) / Z := by
  have hAx : 0 < Real.exp (-W x) / Z :=
    div_pos (Real.exp_pos _) hZ
  have hAy : 0 < Real.exp (-W y) / Z :=
    div_pos (Real.exp_pos _) hZ
  have hlogx :
      Real.log (Real.exp (-W x) / Z) = -W x - Real.log Z := by
    rw [Real.log_div (ne_of_gt (Real.exp_pos _)) (ne_of_gt hZ), Real.log_exp]
  have hlogy :
      Real.log (Real.exp (-W y) / Z) = -W y - Real.log Z := by
    rw [Real.log_div (ne_of_gt (Real.exp_pos _)) (ne_of_gt hZ), Real.log_exp]
  have hleft :
      (Real.exp (-W x) / Z) ^ t * (Real.exp (-W y) / Z) ^ (1 - t) =
        Real.exp ((-W x - Real.log Z) * t +
          (-W y - Real.log Z) * (1 - t)) := by
    rw [Real.rpow_def_of_pos hAx, Real.rpow_def_of_pos hAy, hlogx, hlogy,
      ← Real.exp_add]
  have hright :
      Real.exp (-W (t • x + (1 - t) • y)) / Z =
        Real.exp (-W (t • x + (1 - t) • y) - Real.log Z) := by
    calc
      Real.exp (-W (t • x + (1 - t) • y)) / Z =
          Real.exp (-W (t • x + (1 - t) • y)) / Real.exp (Real.log Z) := by
            rw [Real.exp_log hZ]
      _ = Real.exp (-W (t • x + (1 - t) • y) - Real.log Z) := by
        rw [Real.exp_sub]
  rw [hleft, hright]
  apply Real.exp_le_exp.mpr
  have hW0 :=
    hconv.2 (Set.mem_univ x) (Set.mem_univ y) ht0.le
      (by linarith : 0 ≤ 1 - t) (by ring : t + (1 - t) = 1)
  have hW :
      W (t • x + (1 - t) • y) ≤ t * W x + (1 - t) * W y := by
    simpa [smul_eq_mul] using hW0
  calc
    (-W x - Real.log Z) * t + (-W y - Real.log Z) * (1 - t) =
        -(t * W x + (1 - t) * W y) - Real.log Z := by ring
    _ ≤ -W (t • x + (1 - t) • y) - Real.log Z := by linarith

omit [FiniteDimensional ℝ V] in
/-- For continuous convex `W`, the density `e^{-W} / ∫ e^{-W} dm` of `ν = m.tilted (-W)` is a
log-concave Borell density with respect to `m`. -/
theorem isBorellDensity_of_eq_tilted {m : Measure V} {W : V → ℝ}
    (hνW : (ν : Measure V) = m.tilted (-W)) (hW : Continuous W)
    (hconv : ConvexOn ℝ Set.univ W) :
    IsBorellDensity (ν : Measure V) m (fun x => Real.exp (-W x) / ∫ y, Real.exp (-W y) ∂m) := by
  have hZ : 0 < ∫ y, Real.exp (-W y) ∂m :=
    integral_exp_neg_pos_of_eq_tilted hνW
  have hcont :
      Continuous (fun x => Real.exp (-W x) / ∫ y, Real.exp (-W y) ∂m) :=
    (Real.continuous_exp.comp hW.neg).div_const _
  refine
    { measurable := hcont.measurable
      nonneg := fun x => div_nonneg (Real.exp_pos _).le hZ.le
      upperSemicontinuous := hcont.upperSemicontinuous
      logConcave := fun x y t ht0 ht1 =>
        rpow_mul_rpow_le_of_convexOn hconv hZ x y ht0 ht1
      withDensity_eq := ?_ }
  rw [hνW]
  rfl

/-- A law `ν = volume.tilted (-W)` with continuous convex `W` is log-concave: its density
`e^{-W} / ∫ e^{-W}` is a log-concave Borell density (`IsBorellDensity.compactLogConcave`). -/
theorem logConcave_of_eq_tilted {W : V → ℝ}
    (hνW : (ν : Measure V) = (volume : Measure V).tilted (-W)) (hW : Continuous W)
    (hconv : ConvexOn ℝ Set.univ W) : LogConcave ν := by
  exact
    IsBorellDensity.compactLogConcave
      (isBorellDensity_of_eq_tilted hνW hW hconv)

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [BorelSpace V] in
/-- A tilted Haar law has full support, so its support has nonempty interior. -/
theorem interior_support_nonempty_of_eq_tilted (m : Measure V) [m.IsAddHaarMeasure] {W : V → ℝ}
    (hνW : (ν : Measure V) = m.tilted (-W)) :
    (interior (ν : Measure V).support).Nonempty := by
  have hint : Integrable (fun x => Real.exp (-W x)) m :=
    integrable_exp_neg_of_eq_tilted hνW
  have hac : m ≪ (ν : Measure V) := by
    rw [hνW]
    exact absolutelyContinuous_tilted (by simpa using hint)
  have hsupp : (ν : Measure V).support = (Set.univ : Set V) := by
    apply Set.eq_univ_of_forall
    intro x
    apply (Measure.mem_support_iff_forall x).2
    intro U hU
    have hmU : 0 < m U := Measure.measure_pos_of_mem_nhds m hU
    exact pos_iff_ne_zero.2 fun h0 =>
      (pos_iff_ne_zero.1 hmU) (hac h0)
  rw [hsupp, interior_univ]
  exact Set.univ_nonempty

end FunctionalInequalities.KLS.LogConcave
