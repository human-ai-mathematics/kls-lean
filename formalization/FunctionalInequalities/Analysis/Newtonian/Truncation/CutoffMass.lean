module

public import FunctionalInequalities.Analysis.Newtonian.Kernel.Basic
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The radial cutoff profile and its unit mass

The smooth radial cutoff `newtonianCutoffProfile eps r = 1 - smoothTransition (2 - r / eps)` used to
truncate the Newtonian kernel derivatives in the proofs of Lemmas 4.1–4.2 of Gilbarg–Trudinger,
*Elliptic Partial Differential Equations of Second Order*, Classics 2001 (ISBN 3-540-41160-7):

* smoothness, the values `0` on `r ≤ eps` and `1` on `r ≥ 2 eps`, compact support of its derivative;
* `integral_deriv_newtonianCutoffProfile`: the derivative has mass one on `(0, ∞)`;
* `newtonian_radial_cutoff_mass` (`n ≥ 2`): the radial density
  `(n ω_n)⁻¹ ‖z‖^(1-n) η'_eps(‖z‖)` is integrable on `ℝⁿ` with integral one.

Identification of this density with the divergence of the truncated kernel gradient is in
`Analysis/Newtonian/Truncation/Gradient.lean`.
-/

@[expose] public section

noncomputable section

open Set Metric Filter MeasureTheory
open scoped ContDiff Topology

namespace FunctionalInequalities.Analysis

/-- The scalar cutoff profile `r ↦ 1 - smoothTransition (2 - r / eps)` of the Newtonian
truncation: it vanishes for `r ≤ eps` and equals one for `r ≥ 2 eps`. -/
def newtonianCutoffProfile (eps r : ℝ) : ℝ :=
  1 - Real.smoothTransition (2 - r / eps)

theorem contDiff_newtonianCutoffProfile (eps : ℝ) :
    ContDiff ℝ ∞ (newtonianCutoffProfile eps) :=
  contDiff_const.sub (Real.smoothTransition.contDiff.comp
    (contDiff_const.sub (contDiff_id.div_const eps)))

theorem newtonianCutoffProfile_zero {eps r : ℝ} (heps : 0 < eps) (hr : r ≤ eps) :
    newtonianCutoffProfile eps r = 0 := by
  have hd : r / eps ≤ 1 := (div_le_one heps).mpr hr
  unfold newtonianCutoffProfile
  rw [Real.smoothTransition.one_of_one_le (by linarith)]
  ring

theorem newtonianCutoffProfile_one {eps r : ℝ} (heps : 0 < eps) (hr : 2 * eps ≤ r) :
    newtonianCutoffProfile eps r = 1 := by
  have hd : 2 ≤ r / eps := (le_div_iff₀ heps).mpr hr
  unfold newtonianCutoffProfile
  rw [Real.smoothTransition.zero_of_nonpos (by linarith), sub_zero]

theorem hasCompactSupport_deriv_newtonianCutoffProfile {eps : ℝ} (heps : 0 < eps) :
    HasCompactSupport (deriv (newtonianCutoffProfile eps)) := by
  apply HasCompactSupport.intro (isCompact_Icc : IsCompact (Icc eps (2 * eps)))
  intro r hr
  have hout : r < eps ∨ 2 * eps < r := by simpa only [mem_Icc, not_and_or, not_le] using hr
  rcases hout with hnear | hfar
  · have he : newtonianCutoffProfile eps =ᶠ[𝓝 r] (fun _ : ℝ => 0) := by
      filter_upwards [Iio_mem_nhds hnear] with t ht
      exact newtonianCutoffProfile_zero heps ht.le
    simpa only [deriv_const] using he.deriv_eq
  · have he : newtonianCutoffProfile eps =ᶠ[𝓝 r] (fun _ : ℝ => 1) := by
      filter_upwards [Ioi_mem_nhds hfar] with t ht
      exact newtonianCutoffProfile_one heps ht.le
    simpa only [deriv_const] using he.deriv_eq

/-- The selected profile derivative has exactly mass one on the positive half-line. -/
theorem integral_deriv_newtonianCutoffProfile {eps : ℝ} (heps : 0 < eps) :
    Integrable (deriv (newtonianCutoffProfile eps)) volume ∧
      (∫ r in Ioi (0 : ℝ), deriv (newtonianCutoffProfile eps) r) = 1 := by
  have hχ := contDiff_newtonianCutoffProfile eps
  have hi : Integrable (deriv (newtonianCutoffProfile eps)) volume :=
    (hχ.continuous_deriv (by simp)).integrable_of_hasCompactSupport
      (hasCompactSupport_deriv_newtonianCutoffProfile heps)
  have ht : Tendsto (newtonianCutoffProfile eps) atTop (𝓝 1) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (2 * eps)] with r hr
    exact (newtonianCutoffProfile_one heps hr).symm
  refine ⟨hi, ?_⟩
  have h :=
    integral_Ioi_of_hasDerivAt_of_tendsto'
      (fun r (_ : r ∈ Ici (0 : ℝ)) => (hχ.differentiable (by simp) r).hasDerivAt)
      hi.integrableOn ht
  simpa only [newtonianCutoffProfile_zero heps heps.le, sub_zero] using h

/-- The actual radial density arising from the cutoff-gradient trace has mass one.
Identification with that trace, and the potential Poisson equation, are separate steps. -/
theorem newtonian_radial_cutoff_mass {n : ℕ} (hn : 2 ≤ n) {eps : ℝ} (heps : 0 < eps) :
    Integrable
        (fun z : EuclideanSpace ℝ (Fin n) =>
          (1 / ((n : ℝ) * euclideanUnitBallVolume n)) * ‖z‖ ^ (1 - (n : ℝ)) *
            deriv (newtonianCutoffProfile eps) ‖z‖)
        volume ∧
      (∫ z : EuclideanSpace ℝ (Fin n),
          (1 / ((n : ℝ) * euclideanUnitBallVolume n)) * ‖z‖ ^ (1 - (n : ℝ)) *
            deriv (newtonianCutoffProfile eps) ‖z‖) =
        1 := by
  let : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  let c : ℝ := 1 / ((n : ℝ) * euclideanUnitBallVolume n)
  let F : ℝ → ℝ := fun r => c * r ^ (1 - (n : ℝ)) * deriv (newtonianCutoffProfile eps) r
  obtain ⟨hi, hI⟩ := integral_deriv_newtonianCutoffProfile heps
  have hweight (r : ℝ) (hr : r ∈ Ioi (0 : ℝ)) :
    r ^ (n - 1) • F r = c * deriv (newtonianCutoffProfile eps) r := by
    have he : ((n - 1 : ℕ) : ℝ) + (1 - (n : ℝ)) = 0 := by
      rw [Nat.cast_sub (by omega : 1 ≤ n)]
      push_cast
      ring
    have hp : r ^ (n - 1) * r ^ (1 - (n : ℝ)) = (1 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hr, he, Real.rpow_zero]
    change r ^ (n - 1) * (c * r ^ (1 - (n : ℝ)) * deriv (newtonianCutoffProfile eps) r) = _
    calc
      _ = c * (r ^ (n - 1) * r ^ (1 - (n : ℝ))) * deriv (newtonianCutoffProfile eps) r := by
        ring
      _ = _ := by rw [hp, mul_one]
  have hw : IntegrableOn (fun r : ℝ => r ^ (n - 1) • F r) (Ioi 0) volume :=
    (hi.const_mul c).integrableOn.congr
      (ae_restrict_of_forall_mem measurableSet_Ioi (fun r hr => (hweight r hr).symm))
  have hF : Integrable (fun z : EuclideanSpace ℝ (Fin n) => F ‖z‖) volume := by
    apply (integrable_fun_norm_addHaar volume).mpr
    simpa only [finrank_euclideanSpace_fin] using hw
  have hWi : (∫ r in Ioi (0 : ℝ), r ^ (n - 1) • F r) = c := by
    rw [setIntegral_congr_fun measurableSet_Ioi hweight, integral_const_mul, hI, mul_one]
  have hvol :
    (volume : Measure (EuclideanSpace ℝ (Fin n))).real (ball 0 1) = euclideanUnitBallVolume n :=
    rfl
  have hrad := integral_fun_norm_addHaar (volume : Measure (EuclideanSpace ℝ (Fin n))) F
  simp only [finrank_euclideanSpace_fin, hvol] at hrad
  rw [hWi] at hrad
  refine ⟨hF, hrad.trans ?_⟩
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hv0 := (euclideanUnitBallVolume_pos n).ne'
  simp only [nsmul_eq_mul, smul_eq_mul]
  dsimp [c]
  field_simp

end FunctionalInequalities.Analysis
