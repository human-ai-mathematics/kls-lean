module

public import FunctionalInequalities.Analysis.Convex.Subgradient.Piecewise
public import FunctionalInequalities.Analysis.Convex.Alexandrov.ImageVolume
public import FunctionalInequalities.Analysis.Convex.Alexandrov.Measure
public import FunctionalInequalities.Analysis.Convex.Alexandrov.Stability
public import FunctionalInequalities.Analysis.Convex.Supremum
public import Mathlib.Analysis.Convex.Continuous

/-!
# Dirichlet subsolution envelope and boundary barriers

For the local Monge–Ampere regularity prerequisites of Letwin
arXiv:2607.24164v1, Lemma 2.2 / BB arXiv:1207.6128v1, Theorem 2.24(ii),
this constructs an actual lower-MA subsolution family and its finite convex
supremum. A shifted unit quadratic generates nonemptiness; the pure convex
frontier maximum gives the common upper bound zero. Positive dimension is
needed for the envelope. Actual supporting hyperplanes, anisotropic positive
quadratics and the matrix determinant lemma generate lower-MA barriers at
every boundary point. These force zero boundary and continuity on the whole
closure of the actual envelope, without strict boundary convexity. No MA
equation of the envelope, Dirichlet solution existence, total MA mass bound,
Pogorelov estimate or Sobolev regularity is asserted.
-/

@[expose] public section

noncomputable section
open Set Metric MeasureTheory
open scoped RealInnerProductSpace ENNReal Topology
namespace FunctionalInequalities.Analysis.Dirichlet

/-- Actual lower-MA subsolutions with nonpositive boundary data, not an assumed
solution class. No total-mass upper bound is imposed or inferred. -/
def subsolutions {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n))) :
    Set (EuclideanSpace ℝ (Fin n) → ℝ) :=
  {w | ConvexOn ℝ (closure Ω) w ∧ ContinuousOn w (closure Ω) ∧
    (∀ z ∈ frontier Ω, w z ≤ 0) ∧
    (∀ G : Set (EuclideanSpace ℝ (Fin n)), IsOpen G → G⊆Ω →
      volume G ≤ volume (subgradientImageOn w Ω G))}

/-- A genuine shifted unit quadratic belongs to the actual subsolution family.
The family is therefore nonempty, rather than supplied as a hypothesis. -/
theorem exists_quadratic_subsolution {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (hΩ : IsOpen Ω) (hΩconv : Convex ℝ Ω) (hb : Bornology.IsBounded Ω) :
    ∃ R : ℝ,
      0 < R ∧ quadraticAt (1 : Matrix (Fin n) (Fin n) ℝ) 0 0 (-R ^ 2 / 2) ∈ subsolutions Ω := by
  obtain ⟨R, hR, hbound⟩ := hb.closure.exists_pos_norm_le
  let q := quadraticAt (1 : Matrix (Fin n) (Fin n) ℝ) 0 0 (-R ^ 2 / 2)
  have hqconv : ConvexOn ℝ univ q := convexOn_quadraticAt Matrix.PosSemidef.one _ _ _
  have hqform : ∀ x, q x = (-R ^ 2 / 2) + (1 / 2 : ℝ) * ‖x‖ ^ 2 := by
    intro x
    simp [q, quadraticAt, Matrix.toEuclideanLin]
  have hqc : Continuous q := by
    have heq : q = (fun x => (-R ^ 2 / 2) + (1 / 2 : ℝ) * ‖x‖ ^ 2) := funext hqform
    rw [heq]
    fun_prop
  refine ⟨R, hR, hqconv.subset (subset_univ _) hΩconv.closure, hqc.continuousOn, ?_, ?_⟩
  · intro z hz
    change q z ≤ 0
    rw [hqform]
    have hzbound := hbound z (frontier_subset_closure hz)
    nlinarith [norm_nonneg z]
  · intro G _hG hGΩ
    rw [volume_subgradientImageOn_quadraticAt Matrix.PosDef.one _ _ _ hΩ hGΩ, Matrix.det_one,
      ENNReal.ofReal_one, one_mul]

/-- The actual Perron supremum is finite and convex on the closed domain,
continuous in the interior, and lies between an actual quadratic subsolution
and zero. Boundary equality and any MA equation of the envelope are NOT asserted. -/
theorem exists_finite_convex_envelope {n : ℕ} (hn : 0 < n) {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (hΩ : IsOpen Ω) (hΩconv : Convex ℝ Ω) (hb : Bornology.IsBounded Ω) :
    (subsolutions Ω).Nonempty ∧
      ∃ U : EuclideanSpace ℝ (Fin n) → ℝ,
        (∀ x ∈ closure Ω, U x = sSup ((fun w => w x) '' subsolutions Ω)) ∧
          ConvexOn ℝ (closure Ω) U ∧
            ContinuousOn U Ω ∧
              (∀ x ∈ closure Ω, U x ≤ 0) ∧ (∀ w ∈ subsolutions Ω, ∀ x ∈ closure Ω, w x ≤ U x) := by
  classical
  let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  obtain ⟨R, _hR, hq⟩ := exists_quadratic_subsolution hΩ hΩconv hb
  let q := quadraticAt (1 : Matrix (Fin n) (Fin n) ℝ) 0 0 (-R ^ 2 / 2)
  have hSne : (subsolutions Ω).Nonempty := ⟨q, hq⟩
  have hcap : ∀ w ∈ subsolutions Ω, ∀ x ∈ closure Ω, w x ≤ 0 := by
    intro w hw
    exact le_on_closure_of_le_frontier_of_convexOn hΩ hΩconv hb hw.1 hw.2.1 hw.2.2.1
  let U := fun x => sSup ((fun w => w x) '' subsolutions Ω)
  have hne : ∀ x, ((fun w => w x) '' subsolutions Ω).Nonempty := by
    intro x
    exact ⟨q x, q, hq, rfl⟩
  have hbdd : ∀ x ∈ closure Ω, BddAbove ((fun w => w x) '' subsolutions Ω) := by
    intro x hx
    exact ⟨0, by rintro _ ⟨w, hw, rfl⟩; exact hcap w hw x hx⟩
  have hle : ∀ w ∈ subsolutions Ω, ∀ x ∈ closure Ω, w x ≤ U x := by
    intro w hw x hx
    exact le_csSup (hbdd x hx) ⟨w, hw, rfl⟩
  have hconv : ConvexOn ℝ (closure Ω) U :=
    convexOn_sSup_image_of_bddAbove hΩconv.closure hSne (fun w x => w x) (fun w hw => hw.1) hbdd
  refine ⟨hSne, U, (fun _ _ => rfl), hconv, ?_, ?_, hle⟩
  · exact (hconv.subset subset_closure hΩconv).continuousOn hΩ
  · intro x hx
    exact csSup_le (hne x) (by rintro _ ⟨w, hw, rfl⟩; exact hcap w hw x hx)


private theorem rank_one_det {n : ℕ} (a d : ℝ) (ν : EuclideanSpace ℝ (Fin n)) (hν : ‖ν‖ = 1) :
    (a • ((1 : Matrix (Fin n) (Fin n) ℝ) + d • Matrix.vecMulVec ν ν)).det = a ^ n * (1 + d) := by
  classical
  rw [Matrix.det_smul, Fintype.card_fin]
  have heq :
    d • Matrix.vecMulVec ν ν =
      Matrix.replicateCol Unit (d • (ν : Fin n → ℝ)) *
        Matrix.replicateRow Unit (ν : Fin n → ℝ) := by
    ext i j
    simp [Matrix.mul_apply, Matrix.vecMulVec_apply, mul_assoc]
  rw [heq, Matrix.det_one_add_replicateCol_mul_replicateRow]
  have hn : ((ν : Fin n → ℝ) ⬝ᵥ (ν : Fin n → ℝ)) = 1 := by
    have hi := real_inner_self_eq_norm_sq ν
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, hν, one_pow] using hi
  simp [dotProduct_smul, hn]

private theorem quadratic_formula {n : ℕ} (a d c ε : ℝ) (ν z y : EuclideanSpace ℝ (Fin n)) :
    quadraticAt (a • ((1 : Matrix (Fin n) (Fin n) ℝ) + d • Matrix.vecMulVec ν ν)) z (c • ν) (-ε)
        y =
      -ε + c * ⟪ν, y - z⟫ + (a / 2) * ‖y - z‖ ^ 2 + (a * d / 2) * ⟪ν, y - z⟫ ^ 2 := by
  simp only [quadraticAt, real_inner_smul_left]
  have hact :
    Matrix.toEuclideanLin (Matrix.vecMulVec (ν : Fin n → ℝ) ν) (y - z) = ⟪ν, y - z⟫ • ν := by
    have ht :=
      congrArg (fun T : Matrix (Fin n) (Fin n) ℝ => Matrix.toEuclideanLin T (y - z))
        (InnerProductSpace.symm_toEuclideanLin_rankOne ν ν)
    simpa only [LinearEquiv.apply_symm_apply, star_trivial, ContinuousLinearMap.coe_coe,
      InnerProductSpace.rankOne_apply] using ht.symm
  have hid : Matrix.toEuclideanLin (1 : Matrix (Fin n) (Fin n) ℝ) (y - z) = y - z := by
    ext i
    simp [Matrix.toEuclideanLin]
  simp only [map_smul, map_add, LinearMap.add_apply, LinearMap.smul_apply, hid, hact,
    inner_smul_right, inner_add_right, real_inner_self_eq_norm_sq, real_inner_comm (y - z) ν]
  ring

/-- Actual anisotropic quadratic barrier from a genuine supporting unit normal. -/
private theorem barrier_of_normal {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))} (hΩ : IsOpen Ω)
    (hcΩ : Convex ℝ Ω) (hb : Bornology.IsBounded Ω) (z ν : EuclideanSpace ℝ (Fin n))
    (hν : ‖ν‖ = 1) (hs : ∀ y ∈ closure Ω, ⟪ν, y - z⟫ ≤ 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ q : EuclideanSpace ℝ (Fin n) → ℝ, q ∈ subsolutions Ω ∧ q z = -ε := by
  classical
  obtain ⟨R₀, hR₀, hbound⟩ := hb.closure.exists_pos_norm_le
  let R := R₀ + ‖z‖ + 1
  have hR : 0 < R := by dsimp [R]; positivity
  have hdist : ∀ y ∈ closure Ω, ‖y - z‖ ≤ R := by
    intro y hy
    calc
      ‖y - z‖ ≤ ‖y‖ + ‖z‖ := norm_sub_le _ _
      _ ≤ R := by have := hbound y hy; dsimp [R]; linarith
  let a := ε / (R ^ 2 + 1)
  have ha : 0 < a := div_pos hε (by positivity)
  let d := (a ^ n)⁻¹
  have hd : 0 ≤ d := inv_nonneg.mpr (pow_nonneg ha.le n)
  let A : Matrix (Fin n) (Fin n) ℝ := a • (1 + d • Matrix.vecMulVec ν ν)
  have hpsd : (Matrix.vecMulVec (ν : Fin n → ℝ) ν).PosSemidef := by
    simpa only [star_trivial] using Matrix.posSemidef_vecMulVec_self_star (ν : Fin n → ℝ)
  have hA : A.PosDef := (Matrix.PosDef.one.add_posSemidef (hpsd.smul hd)).smul ha
  have hdet : 1 ≤ A.det := by
    rw [rank_one_det a d ν hν]
    dsimp only [d]
    rw [mul_add, mul_one, mul_inv_cancel₀ (pow_pos ha n).ne']
    exact le_add_of_nonneg_left (pow_nonneg ha.le n)
  let c := a * d * R / 2
  let q := quadraticAt A z (c • ν) (-ε)
  have hform :
    ∀ y, q y = -ε + c * ⟪ν, y - z⟫ + (a / 2) * ‖y - z‖ ^ 2 + (a * d / 2) * ⟪ν, y - z⟫ ^ 2 :=
    quadratic_formula a d c ε ν z
  have hct : Continuous q := by
    rw [show
        q =
          (fun y => -ε + c * ⟪ν, y - z⟫ + (a / 2) * ‖y - z‖ ^ 2 + (a * d / 2) * ⟪ν, y - z⟫ ^ 2)
        from funext hform]
    fun_prop
  have hcap : ∀ y ∈ closure Ω, q y ≤ 0 := by
    intro y hy
    have ht := hs y hy
    have hlow : -R ≤ ⟪ν, y - z⟫ := by
      have ht' := abs_real_inner_le_norm ν (y - z)
      rw [hν, one_mul] at ht'
      exact (neg_le_of_abs_le ht').trans' (neg_le_neg (hdist y hy))
    have hmix : c * ⟪ν, y - z⟫ + (a * d / 2) * ⟪ν, y - z⟫ ^ 2 ≤ 0 := by
      have hprod : ⟪ν, y - z⟫ * (⟪ν, y - z⟫ + R) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg ht (by linarith)
      have hmul := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ a * d / 2 by positivity) hprod
      dsimp only [c]
      nlinarith
    have hsq : ‖y - z‖ ^ 2 ≤ R ^ 2 := sq_le_sq₀ (norm_nonneg _) hR.le |>.mpr (hdist y hy)
    have hnum : a * (R ^ 2 + 1) = ε := div_mul_cancel₀ ε (by positivity : (R ^ 2 + 1 : ℝ) ≠ 0)
    rw [hform]
    nlinarith [mul_le_mul_of_nonneg_left hsq ha.le]
  refine
    ⟨q,
      ⟨(convexOn_quadraticAt hA.posSemidef _ _ _).subset (subset_univ _) hcΩ.closure,
        hct.continuousOn, (fun y hy => hcap y (frontier_subset_closure hy)), ?_⟩,
      ?_⟩
  · intro G _hG hGΩ
    change volume G ≤ volume (subgradientImageOn (quadraticAt A z (c • ν) (-ε)) Ω G)
    rw [volume_subgradientImageOn_quadraticAt hA _ _ _ hΩ hGΩ]
    calc
      volume G = 1 * volume G := (one_mul _).symm
      _ ≤ ENNReal.ofReal A.det * volume G := by
        gcongr
        exact ENNReal.one_le_ofReal.mpr hdet
  · rw [hform]
    simp

/-- Actual bounded open convex domain data generate quadratic lower-MA
barriers at EVERY frontier point, without strict boundary convexity. -/
theorem exists_boundary_barrier {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))} (hΩ : IsOpen Ω)
    (hcΩ : Convex ℝ Ω) (hb : Bornology.IsBounded Ω) {z : EuclideanSpace ℝ (Fin n)}
    (hz : z ∈ frontier Ω) {ε : ℝ} (hε : 0 < ε) :
    ∃ q : EuclideanSpace ℝ (Fin n) → ℝ, q ∈ subsolutions Ω ∧ q z = -ε := by
  classical
  let E := EuclideanSpace ℝ (Fin n)
  have hint : (interior Ω).Nonempty := by
    rw [hΩ.interior_eq]
    exact closure_nonempty_iff.mp ⟨z, frontier_subset_closure hz⟩
  obtain ⟨L, hL, hsep⟩ := geometric_hahn_banach_of_nonempty_interior_point hcΩ hz.2 hint
  let v : E := (InnerProductSpace.toDual ℝ E).symm L
  have hv : v ≠ 0 := by
    intro heq
    apply hL
    have ht := congrArg (InnerProductSpace.toDual ℝ E) heq
    simpa [v] using ht
  let ν : E := ‖v‖⁻¹ • v
  have hn : ‖ν‖ = 1 := by
    simp only [ν, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg v),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]
  have hs : ∀ y ∈ closure Ω, ⟪ν, y - z⟫ ≤ 0 := by
    intro y hy
    have hsepc : L y ≤ L z :=
      (closure_minimal (fun w hw => hsep w hw) (isClosed_le L.continuous continuous_const)) hy
    have hrepr : ⟪v, y - z⟫ = L y - L z := by
      rw [show v = (InnerProductSpace.toDual ℝ E).symm L from rfl,
        InnerProductSpace.toDual_symm_apply, map_sub]
    change ⟪‖v‖⁻¹ • v, y - z⟫ ≤ 0
    rw [real_inner_smul_left, hrepr]
    exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr (norm_nonneg _)) (sub_nonpos.mpr hsepc)
  exact barrier_of_normal hΩ hcΩ hb z ν hn hs hε

/-- The actual finite Perron envelope now has genuine zero boundary and
closure continuity. No envelope boundary/C0 field is a source premise. -/
theorem exists_continuous_envelope {n : ℕ} (hn : 0 < n) {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (hΩ : IsOpen Ω) (hcΩ : Convex ℝ Ω) (hb : Bornology.IsBounded Ω) :
    (subsolutions Ω).Nonempty ∧
      ∃ U : EuclideanSpace ℝ (Fin n) → ℝ,
        (∀ x ∈ closure Ω, U x = sSup ((fun w => w x) '' subsolutions Ω)) ∧
          ConvexOn ℝ (closure Ω) U ∧
            ContinuousOn U (closure Ω) ∧
              (∀ z ∈ frontier Ω, U z = 0) ∧
                (∀ w ∈ subsolutions Ω, ∀ x ∈ closure Ω, w x ≤ U x) := by
  obtain ⟨hne, U, heq, hcv, hct, hcap, hdom⟩ := exists_finite_convex_envelope hn hΩ hcΩ hb
  have hzero : ∀ z ∈ frontier Ω, U z = 0 := by
    intro z hz
    apply le_antisymm (hcap z (frontier_subset_closure hz))
    by_contra h
    have hneg : U z < 0 := lt_of_not_ge h
    obtain ⟨q, hq, hqz⟩ := exists_boundary_barrier hΩ hcΩ hb hz (show 0 < -U z / 2 by linarith)
    have hle := hdom q hq z (frontier_subset_closure hz)
    rw [hqz] at hle
    linarith
  refine ⟨hne, U, heq, hcv, ?_, hzero, hdom⟩
  intro z hz
  by_cases hzΩ : z ∈ Ω
  · exact (hct.continuousAt (hΩ.mem_nhds hzΩ)).continuousWithinAt
  · have hzf : z ∈ frontier Ω := ⟨hz, by simpa only [hΩ.interior_eq] using hzΩ⟩
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    obtain ⟨q, hq, hqz⟩ := exists_boundary_barrier hΩ hcΩ hb hzf (show 0 < ε / 2 by linarith)
    obtain ⟨δ, hδ, hnear⟩ :=
      Metric.continuousWithinAt_iff.mp (hq.2.1 z hz) (ε / 2) (by linarith)
    refine ⟨δ, hδ, ?_⟩
    intro y hy hyd
    have hqdist := hnear hy hyd
    have hqy : -ε < q y := by
      rw [Real.dist_eq, hqz] at hqdist
      have := (abs_lt.mp hqdist).1
      linarith
    have hUy := hdom q hq y hy
    have hUy0 := hcap y hy
    rw [Real.dist_eq, hzero z hzf]
    apply abs_lt.mpr
    constructor <;> linarith

/-- One actual measure/contact-partition implementation, shared by the true
global max and local patch sources. Its inputs are derived internally by each
public source; no public conclusion-bearing closure record is introduced. -/
private theorem lower_ma_of_contact_partition {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (hΩ : IsOpen Ω) {u v w : EuclideanSpace ℝ (Fin n) → ℝ} (hu : ConvexOn ℝ Ω u)
    (hv : ConvexOn ℝ Ω v) (huc : ContinuousOn u (closure Ω)) (hvc : ContinuousOn v Ω)
    (huMA : ∀ G, IsOpen G → G ⊆ Ω → volume G ≤ volume (subgradientImageOn u Ω G))
    (hvMA : ∀ G, IsOpen G → G ⊆ Ω → volume G ≤ volume (subgradientImageOn v Ω G))
    (hwcv : ConvexOn ℝ Ω w) (hwc : ContinuousOn w (closure Ω)) (huw : ∀ y ∈ Ω, u y ≤ w y)
    (hactive :
      ∀ x ∈ Ω,
        w x ≠ u x → ∀ p, (∀ y ∈ Ω, v x + ⟪p, y - x⟫ ≤ v y) → ∀ y ∈ Ω, w x + ⟪p, y - x⟫ ≤ w y) :
    ∀ G, IsOpen G → G ⊆ Ω → volume G ≤ volume (subgradientImageOn w Ω G) := by
  obtain ⟨μ, hμ, _⟩ := exists_domain_mongeAmpere_measure hΩ hwcv (hwc.mono subset_closure)
  have hformula : ∀ T, MeasurableSet T → T ⊆ Ω → μ T = volume (subgradientImageOn w Ω T) := by
    intro T hT hTΩ
    simpa only [inter_eq_left.mpr hTΩ] using hμ T hT
  intro G hG hGΩ
  let C := {x ∈ closure Ω | w x = u x}
  let A := G ∩ C
  let B := G \ C
  have hC : IsClosed C := isClosed_closure.isClosed_eq hwc huc
  have hA : MeasurableSet A := hG.measurableSet.inter hC.measurableSet
  have hB : MeasurableSet B := hG.measurableSet.diff hC.measurableSet
  have hAΩ : A ⊆ Ω := inter_subset_left.trans hGΩ
  have hBΩ : B ⊆ Ω := sdiff_subset.trans hGΩ
  have hAB : Disjoint A B := disjoint_left.mpr (by intro x hx hx'; exact hx'.2 hx.2)
  have hunion : A ∪ B = G := inter_union_sdiff G C
  have hleft : subgradientImageOn u Ω A ⊆ subgradientImageOn w Ω A :=
    subgradientImageOn_subset_of_le_of_eqOn u w Ω A huw (fun _ hx => hx.2.2.symm)
  have hright : subgradientImageOn v Ω B ⊆ subgradientImageOn w Ω B := by
    rintro p ⟨x, hx, hp⟩
    have hn : w x ≠ u x := fun h => hx.2 ⟨subset_closure (hBΩ hx), h⟩
    exact ⟨x, hx, hactive x (hBΩ hx) hn p hp⟩
  calc
    volume G = volume A + volume B := by rw [← hunion, measure_union hAB hB]
    _ ≤ volume (subgradientImageOn u Ω A) + volume (subgradientImageOn v Ω B) :=
      add_le_add
        (volume_le_subgradientImageOn_of_open_lower hΩ hu (huc.mono subset_closure) huMA A hA
          hAΩ)
        (volume_le_subgradientImageOn_of_open_lower hΩ hv hvc hvMA B hB hBΩ)
    _ ≤ volume (subgradientImageOn w Ω A) + volume (subgradientImageOn w Ω B) :=
      add_le_add (measure_mono hleft) (measure_mono hright)
    _ = μ A + μ B := by rw [hformula A hA hAΩ, hformula B hB hBΩ]
    _ = μ G := by rw [← hunion, measure_union hAB hB]
    _ = volume (subgradientImageOn w Ω G) := hformula G hG.measurableSet hGΩ

/-- Actual lower-MA Perron class is closed under a genuine two-function max.
No Borel extension, max-closure, cap or regularity is supplied as a premise. -/
theorem max_mem_subsolutions {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))} (hΩ : IsOpen Ω)
    (hcΩ : Convex ℝ Ω) {u v : EuclideanSpace ℝ (Fin n) → ℝ} (hu : u ∈ subsolutions Ω)
    (hv : v ∈ subsolutions Ω) : (fun x => max (u x) (v x)) ∈ subsolutions Ω := by
  let w := fun x => max (u x) (v x)
  have hwcv : ConvexOn ℝ (closure Ω) w := hu.1.sup hv.1
  have hwc : ContinuousOn w (closure Ω) := hu.2.1.sup hv.2.1
  refine ⟨hwcv, hwc, ?_, ?_⟩
  · intro z hz
    exact max_le (hu.2.2.1 z hz) (hv.2.2.1 z hz)
  · apply
      lower_ma_of_contact_partition hΩ (hu.1.subset subset_closure hcΩ)
        (hv.1.subset subset_closure hcΩ) hu.2.1 (hv.2.1.mono subset_closure) hu.2.2.2 hv.2.2.2
        (hwcv.subset subset_closure hcΩ) hwc (fun _ _ => le_max_left _ _)
    intro x _hx hn p hp y hy
    have hlt : u x < v x := by
      by_contra h
      exact hn (max_eq_left (le_of_not_gt h))
    dsimp only [w]
    rw [max_eq_right hlt.le]
    exact (hp y hy).trans (le_max_right _ _)

/-- Genuine nonempty finite maxima stay in the actual class, using the
source-derived binary closure rather than an assumed closure property. -/
theorem finite_sup_mem_subsolutions {n : ℕ} {ι : Type*} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (hΩ : IsOpen Ω) (hcΩ : Convex ℝ Ω) (S : Finset ι) (hS : S.Nonempty)
    (f : ι → EuclideanSpace ℝ (Fin n) → ℝ) (hf : ∀ i ∈ S, f i ∈ subsolutions Ω) :
    S.sup' hS f ∈ subsolutions Ω := by
  exact Finset.sup'_induction hS f (fun u hu v hv => max_mem_subsolutions hΩ hcΩ hu hv) hf

section UniformApproximation
open Filter

/-- Source Sup/compactness GENERATE a real uniform class approximation;
no sequence, finite cover, cap or desired approximation is a premise. -/
theorem exists_uniform_class_approximation {n : ℕ} (hn : 0 < n)
    {Ω : Set (EuclideanSpace ℝ (Fin n))} (hΩ : IsOpen Ω) (hcΩ : Convex ℝ Ω)
    (hb : Bornology.IsBounded Ω) :
    ∃ (U : EuclideanSpace ℝ (Fin n) → ℝ) (f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ),
      (∀ x ∈ closure Ω, U x = sSup ((fun w => w x) '' subsolutions Ω)) ∧
        U ∈ subsolutions Ω ∧
          (∀ z ∈ frontier Ω, U z = 0) ∧
            (∀ w ∈ subsolutions Ω, ∀ x ∈ closure Ω, w x ≤ U x) ∧
              (∀ j, f j ∈ subsolutions Ω) ∧
                (∀ j, ∀ x ∈ closure Ω, f j x ≤ U x ∧ |f j x - U x| < 1 / ((j : ℝ) + 1)) ∧
                  (∀ x, Monotone (fun j => f j x)) ∧ TendstoUniformlyOn f U atTop (closure Ω) := by
  classical
  obtain ⟨hne, U, heq, hcv, hct, hzero, hdom⟩ := exists_continuous_envelope hn hΩ hcΩ hb
  let S := subsolutions Ω
  obtain ⟨w₀, hw₀⟩ := hne
  have happrox : ∀ ε : ℝ, 0 < ε → ∃ W, W ∈ S ∧ ∀ x ∈ closure Ω, W x ≤ U x ∧ |W x - U x| < ε := by
    intro ε hε
    have hpoint : ∀ x ∈ closure Ω, ∃ w ∈ S, U x - ε < w x := by
      intro x hx
      have hne' : ((fun w => w x) '' S).Nonempty := ⟨w₀ x, w₀, hw₀, rfl⟩
      have hbdd : BddAbove ((fun w => w x) '' S) :=
        ⟨U x, by rintro t ⟨w, hw, rfl⟩; exact hdom w hw x hx⟩
      have hlt : U x - ε < sSup ((fun w => w x) '' S) := by
        rw [← heq x hx]
        linarith
      obtain ⟨t, ⟨w, hw, rfl⟩, ht⟩ := (lt_csSup_iff hbdd hne').mp hlt
      exact ⟨w, hw, ht⟩
    let K := closure Ω
    have hK : IsCompact K := hb.isCompact_closure
    let : CompactSpace K := isCompact_iff_compactSpace.mp hK
    let cover : S → Set K := fun w => {x | U x - w.val x < ε}
    have hU : Continuous (fun x : K => U x) := continuousOn_iff_continuous_domRestrict.mp hct
    have hopen : ∀ w : S, IsOpen (cover w) := by
      intro w
      have hw : Continuous (fun x : K => w.val x) :=
        continuousOn_iff_continuous_domRestrict.mp w.prop.2.1
      exact isOpen_lt (hU.sub hw) continuous_const
    have hcover : (univ : Set K) ⊆ ⋃ w : S, cover w := by
      intro x _
      obtain ⟨w, hw, ht⟩ := hpoint x.val x.prop
      refine mem_iUnion.mpr ⟨⟨w, hw⟩, ?_⟩
      change U x - w x < ε
      linarith
    obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover cover hopen hcover
    let base : S := ⟨w₀, hw₀⟩
    let T := insert base s
    have hT : T.Nonempty := Finset.insert_nonempty _ _
    let W := T.sup' hT (fun w : S => w.val)
    have hW : W ∈ S :=
      finite_sup_mem_subsolutions hΩ hcΩ T hT (fun w : S => w.val) (fun w _ => w.prop)
    refine ⟨W, hW, ?_⟩
    intro x hx
    have hle := hdom W hW x hx
    have hcov := hs (mem_univ (⟨x, hx⟩ : K))
    obtain ⟨w, hw, hclose⟩ := mem_iUnion₂.mp hcov
    have hw' : w ∈ T := Finset.mem_insert_of_mem hw
    have hfun : w.val ≤ W := Finset.le_sup' (fun w : S => w.val) hw'
    have hxle : w.val x ≤ W x := hfun x
    have hgap : U x - w.val x < ε := hclose
    refine ⟨hle, ?_⟩
    rw [abs_of_nonpos (sub_nonpos.mpr hle)]
    linarith
  choose g hg hgerr using fun j : ℕ => happrox (1 / ((j : ℝ) + 1)) (by positivity)
  have hT : ∀ j : ℕ, (Finset.range (j + 1)).Nonempty := fun j => ⟨0, by simp⟩
  let f := fun j : ℕ => (Finset.range (j + 1)).sup' (hT j) g
  have hf : ∀ j, f j ∈ S := by
    intro j
    exact finite_sup_mem_subsolutions hΩ hcΩ _ (hT j) g (fun i _ => hg i)
  have herr : ∀ j, ∀ x ∈ closure Ω, f j x ≤ U x ∧ |f j x - U x| < 1 / ((j : ℝ) + 1) := by
    intro j x hx
    have hle := hdom (f j) (hf j) x hx
    have hfun : g j ≤ f j := Finset.le_sup' g (Finset.mem_range.mpr (Nat.lt_succ_self j))
    have hlast := hgerr j x hx
    refine ⟨hle, ?_⟩
    rw [abs_of_nonpos (sub_nonpos.mpr hle)]
    have hlast' := hlast.2
    rw [abs_of_nonpos (sub_nonpos.mpr hlast.1)] at hlast'
    linarith [hfun x]
  have hmono : Monotone f := by
    intro j k hjk
    apply Finset.sup'_le
    intro i hi
    exact
      Finset.le_sup' g
        (Finset.mem_range.mpr ((Finset.mem_range.mp hi).trans_le (Nat.add_le_add_right hjk 1)))
  have hunif : TendstoUniformlyOn f U atTop (closure Ω) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hs : Tendsto (fun j : ℕ => (1 : ℝ) / ((j : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    filter_upwards [(Metric.tendsto_nhds.mp hs) ε hε] with j hj x hx
    have hr : (1 : ℝ) / ((j : ℝ) + 1) < ε := by
      have ht : |(1 : ℝ) / ((j : ℝ) + 1)| < ε := by simpa only [Real.dist_eq, sub_zero] using hj
      exact (le_abs_self _).trans_lt ht
    rw [Real.dist_eq, abs_sub_comm]
    exact (herr j x hx).2.trans hr
  have hlocal : TendstoLocallyUniformlyOn f U atTop Ω :=
    (hunif.mono subset_closure).tendstoLocallyUniformlyOn
  have hMAU :
    ∀ G : Set (EuclideanSpace ℝ (Fin n)),
      IsOpen G → G ⊆ Ω → volume G ≤ volume (subgradientImageOn U Ω G) := by
    intro G hG hGΩ
    rw [hG.measure_eq_iSup_isCompact (volume : Measure (EuclideanSpace ℝ (Fin n)))]
    refine iSup_le fun K => iSup_le fun hKG => iSup_le fun hK => ?_
    have hKΩ : K ⊆ Ω := hKG.trans hGΩ
    have hbound : ∀ j : ℕ, volume K ≤ volume (subgradientImageOn (f j) Ω K) := by
      intro j
      exact
        volume_le_subgradientImageOn_of_open_lower hΩ ((hf j).1.subset subset_closure hcΩ)
          ((hf j).2.1.mono subset_closure) (hf j).2.2.2 K hK.measurableSet hKΩ
    have hsup : volume K ≤ limsup (fun j => volume (subgradientImageOn (f j) Ω K)) atTop := by
      have ht := limsup_le_limsup (f := (atTop : Filter ℕ)) (Eventually.of_forall hbound)
      simpa only [limsup_const] using ht
    exact
      hsup.trans
        ((limsup_volume_subgradientImageOn_le_of_locally_uniform hΩ
              (hcv.subset subset_closure hcΩ) (hct.mono subset_closure) hlocal hK hKΩ).trans
          (measure_mono (subgradientImageOn_mono U Ω hKG)))
  exact
    ⟨U, f, heq, ⟨hcv, hct, (fun z hz => (hzero z hz).le), hMAU⟩, hzero, hdom, hf, herr,
      (fun x j k hjk => hmono hjk x), hunif⟩

end UniformApproximation

section LocalRaising
open Filter Classical

/-- The actual locally glued function stays in the real lower-MA class.
q has actual local convex/C0/lower-MA source data; no glued class/MA assumption. -/
theorem piecewise_max_ball_mem_subsolutions {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (hΩ : IsOpen Ω) (hcΩ : Convex ℝ Ω) {u q : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : u ∈ subsolutions Ω) (hq : ConvexOn ℝ Ω q) (hqc : ContinuousOn q (closure Ω))
    (hqMA : ∀ G, IsOpen G → G ⊆ Ω → volume G ≤ volume (subgradientImageOn q Ω G))
    {c : EuclideanSpace ℝ (Fin n)} {r : ℝ} (hr : 0 < r) (hball : closedBall c r ⊆ Ω)
    (hbd : ∀ z ∈ sphere c r, q z ≤ u z) :
    (fun y => if y ∈ ball c r then max (u y) (q y) else u y) ∈ subsolutions Ω := by
  let w := fun y => if y ∈ ball c r then max (u y) (q y) else u y
  have hwcv : ConvexOn ℝ (closure Ω) w :=
    convexOn_closure_piecewise_max_ball hΩ hu.1 hq (hqc.mono subset_closure) hball hbd
  have hwc : ContinuousOn w (closure Ω) := continuousOn_piecewise_max_ball hr hu.2.1 hqc hbd
  have hwu (y) : u y ≤ w y := by
    dsimp only [w]
    split_ifs
    · exact le_max_left _ _
    · exact le_rfl
  refine ⟨hwcv, hwc, ?_, ?_⟩
  · intro z hz
    have hnΩ : z ∉ Ω := by rw [hΩ.frontier_eq] at hz; exact hz.2
    have hn : z ∉ ball c r := fun h => hnΩ (hball (ball_subset_closedBall h))
    dsimp only [w]; rw [ite_eq_right hn]
    exact hu.2.2.1 z hz
  · apply
      lower_ma_of_contact_partition hΩ (hu.1.subset subset_closure hcΩ) hq hu.2.1
        (hqc.mono subset_closure) hu.2.2.2 hqMA (hwcv.subset subset_closure hcΩ) hwc
        (fun y _hy => hwu y)
    intro x _hx hn p hp y hy
    have hxb : x ∈ ball c r := by
      by_contra h
      exact hn (by dsimp only [w]; rw [ite_eq_right h])
    have hxu : u x ≤ q x := by
      by_contra h
      exact hn (by dsimp only [w]; rw [ite_eq_left hxb, max_eq_left (le_of_not_ge h)])
    have hxw : w x = q x := by dsimp only [w]; rw [ite_eq_left hxb, max_eq_right hxu]
    rw [hxw]
    exact
      subgradient_le_piecewise_max_ball (hu.1.subset subset_closure hcΩ) hball hbd hxb hxu
        (fun t ht => hp t (hball ht)) y hy

/-- The actual canonical envelope is generated ONCE and retains ALL its
approximation fields while gaining genuine local lower-MA comparison. -/
theorem exists_envelope_local_comparison {n : ℕ} (hn : 0 < n)
    {Ω : Set (EuclideanSpace ℝ (Fin n))} (hΩ : IsOpen Ω) (hcΩ : Convex ℝ Ω)
    (hb : Bornology.IsBounded Ω) :
    ∃ (U : EuclideanSpace ℝ (Fin n) → ℝ) (f : ℕ → EuclideanSpace ℝ (Fin n) → ℝ),
      (∀ x ∈ closure Ω, U x = sSup ((fun w => w x) '' subsolutions Ω)) ∧
        U ∈ subsolutions Ω ∧
          (∀ z ∈ frontier Ω, U z = 0) ∧
            (∀ w ∈ subsolutions Ω, ∀ x ∈ closure Ω, w x ≤ U x) ∧
              (∀ j, f j ∈ subsolutions Ω) ∧
                (∀ j, ∀ x ∈ closure Ω, f j x ≤ U x ∧ |f j x - U x| < 1 / ((j : ℝ) + 1)) ∧
                  (∀ x, Monotone (fun j => f j x)) ∧
                    TendstoUniformlyOn f U Filter.atTop (closure Ω) ∧
                      (∀ (q : EuclideanSpace ℝ (Fin n) → ℝ),
                        ConvexOn ℝ Ω q →
                          ContinuousOn q (closure Ω) →
                            (∀ G,
                                IsOpen G →
                                  G ⊆ Ω → volume G ≤ volume (subgradientImageOn q Ω G)) →
                              ∀ (c : EuclideanSpace ℝ (Fin n)) (r : ℝ),
                                0 < r →
                                  closedBall c r ⊆ Ω →
                                    (∀ z ∈ sphere c r, q z ≤ U z) →
                                      ∀ x ∈ ball c r, q x ≤ U x) := by
  obtain ⟨U, f, heq, hU, hzero, hdom, hf, herr, hmono, hunif⟩ :=
    exists_uniform_class_approximation hn hΩ hcΩ hb
  refine ⟨U, f, heq, hU, hzero, hdom, hf, herr, hmono, hunif, ?_⟩
  intro q hq hqc hqMA c r hr hball hbd x hx
  let w := fun y => if y ∈ ball c r then max (U y) (q y) else U y
  have hw := piecewise_max_ball_mem_subsolutions hΩ hcΩ hU hq hqc hqMA hr hball hbd
  have hcomp := hdom w hw x (subset_closure (hball (ball_subset_closedBall hx)))
  have hqx : q x ≤ w x := by dsimp only [w]; rw [ite_eq_left hx]; exact le_max_right _ _
  exact hqx.trans hcomp

end LocalRaising

end FunctionalInequalities.Analysis.Dirichlet
