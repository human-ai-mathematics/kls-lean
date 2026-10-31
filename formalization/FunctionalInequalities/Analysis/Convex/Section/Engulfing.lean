module

public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import FunctionalInequalities.Analysis.Convex.Section.Growth
public import FunctionalInequalities.Analysis.Convex.Section.Affine

/-!
# Normalized section geometry and Caffarelli's interior C¹,α gain

Supporting Letwin arXiv:2607.24164v1 Lemma 2.2, through Berman–Berndtsson
arXiv:1207.6128v1 Theorem 2.24(i). The constructive tangent-growth argument is
Forzani–Maldonado, Nonlinear Analysis 57 (2004), 815–829, Theorem 7, equation (4.18).

John normalization and two-sided Alexandrov density bounds give a common boundary
margin for half-height sections. The affine determinant factors cancel in the
ratio of the density bounds. Supporting-plane errors in the two directions are
therefore comparable. A real-power quotient along each ray converts this comparison
into tangent growth, then into a Hölder gradient. No Hessian or Hölder estimate is
a hypothesis of the closed Alexandrov-density theorem. The existence of the
transporting source potential is supplied separately by MomentRegularity.

The all-points normalized comparison also gives full small-section engulfing,
with constants and a height chosen before all centres in a compact set.
This does not prove the W²,p or second-order regularity gain.
-/

@[expose] public section

noncomputable section

open Set Metric MeasureTheory
open scoped RealInnerProductSpace ENNReal

namespace FunctionalInequalities.Analysis.SoftEngulfing


section AffineDet

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- An affine equivalence moves differences by its linear part. -/
private theorem affineEquiv_sub (e : E ≃ᵃ[ℝ] E) (y z : E) : e z - e y = e.linear (z - y) := by
  exact ((AffineEquiv.toAffineMap e).linear_apply_vsub z y).symm

end AffineDet

section Normalized

variable {n : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin n)

/-- **Balanced normalized sections.** In a normalized frame (`closedBall 0 1 ⊆ T ⊆ closedBall 0 R`,
`T` open
bounded convex), a convex `w` with `w = 0` on `∂T`, `w ≥ −H` everywhere, lower density `a'` on open
subsets and upper
density `b'` on `T` satisfies: every `y ∈ T` with `w y < −(1−η) H` is at distance at least
`κ(n, R) (1−η)^n (a'/b')` from `∂T`. `κ` is chosen before all data. -/
theorem exists_normalized_margin (hn : 0 < n) (R : ℝ) (hR : 0 < R) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (w : 𝔼 → ℝ), ConvexOn ℝ Set.univ w →
      ∀ T : Set 𝔼, IsOpen T → Convex ℝ T → Bornology.IsBounded T → closedBall (0 : 𝔼) 1 ⊆ T →
      T ⊆ closedBall (0 : 𝔼) R → (∀ y ∈ frontier T, w y = 0) →
      ∀ H : ℝ, 0 < H → (∀ y, -H ≤ w y) →
      ∀ a' b' : ℝ, 0 < a' → 0 < b' →
      (∀ G : Set 𝔼, IsOpen G → G ⊆ T →
        ENNReal.ofReal a' * (volume : Measure 𝔼) G ≤ (volume : Measure 𝔼) (subgradientImage w G)) →
      (volume : Measure 𝔼) (subgradientImage w T) ≤ ENNReal.ofReal b' * (volume : Measure 𝔼) T →
      ∀ η : ℝ, 0 < η → η < 1 → ∀ y ∈ T, w y < -(1 - η) * H →
        κ * (1 - η) ^ n * (a' / b') ≤ infDist y (frontier T) := by
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    obtain ⟨c, hc, hmax⟩ := exists_pos_alexandrov_maximum_principle (E := 𝔼)
    set V : ℝ := ((volume : Measure 𝔼) (closedBall (0 : 𝔼) R)).toReal with hVdef
    have hV : 0 < V :=
      ENNReal.toReal_pos (measure_closedBall_pos volume (0 : 𝔼) hR).ne'
        measure_closedBall_lt_top.ne
    have h2R : 0 < (2 * R) ^ (n - 1) := by positivity
    refine ⟨c / (2 ^ (n + 1) * V * (2 * R) ^ (n - 1)), by positivity, ?_⟩
    intro w hwconv T hTo hTc hTb hball hTR hfr H hH hwge a' b' ha' hb' hA hB η hη hη1 y
      hyT hwy
    have hn' : (n : ℝ) ≠ 0 := by
      exact_mod_cast
        hn.ne'
    -- the minimum estimate: `(a'/2)^{1/n} ≤ 2H`, hence `a'/2^{n+1} ≤ H^n`

    have hfr₁ : ∀ y ∈ frontier T, w y ≤ 0 := fun y hy => (hfr y hy).le
    have hfr₂ : ∀ y ∈ frontier T, 0 ≤ w y := fun y hy => (hfr y hy).ge
    have hmin := le_neg_of_lower_alexandrov_bound hn hwconv hTo hTb hball hfr₁ ha' hA
    have hkey : (a' / 2) ^ (1 / (n : ℝ)) ≤ 2 * H := by linarith [hwge 0]
    have hkey2 : a' / 2 ≤ (2 * H) ^ n := by
      have hbase : 0 ≤ a' / 2 := by positivity
      have := Real.rpow_le_rpow (Real.rpow_nonneg hbase _) hkey (Nat.cast_nonneg n)
      rw [← Real.rpow_mul hbase, one_div, inv_mul_cancel₀ hn', Real.rpow_one,
        Real.rpow_natCast] at this
      exact this
    have hHn : a' / 2 ^ (n + 1) ≤ H ^ n := by
      rw [mul_pow] at hkey2
      rw [pow_succ, div_le_iff₀ (by positivity)]
      calc
        a' = 2 * (a' / 2) := by ring
        _ ≤ 2 * (2 ^ n * H ^ n) := by gcongr
        _ = H ^ n * (2 ^ n * 2) := by
          ring
    -- the maximum principle at `y`

    have h1η : 0 < 1 - η := by linarith
    have hwy0 : w y < 0 := by nlinarith
    have hmp :=
      hmax w hwconv T hTo hTc hTb hfr₂ y hyT
        hwy0
    -- bound the right-hand side

    have hdiam : diam T ≤ 2 * R :=
      (diam_mono hTR isBounded_closedBall).trans (diam_closedBall hR.le)
    have hdiam0 : 0 ≤ diam T := diam_nonneg
    set d : ℝ := infDist y (frontier T) with hddef
    have hd0 : 0 ≤ d := infDist_nonneg
    have hvolT : (volume : Measure 𝔼) T ≤ ENNReal.ofReal V := by
      rw [hVdef, ENNReal.ofReal_toReal measure_closedBall_lt_top.ne]
      exact measure_mono hTR
    have hrhs :
      (volume : Measure 𝔼) (subgradientImage w T) *
          ENNReal.ofReal (diam T ^ (n - 1) * d) ≤
        ENNReal.ofReal (b' * V * ((2 * R) ^ (n - 1) * d)) := by
      have hL :
        (volume : Measure 𝔼) (subgradientImage w T) ≤
          ENNReal.ofReal b' * ENNReal.ofReal V :=
        hB.trans (mul_le_mul' le_rfl hvolT)
      have hRr :
        ENNReal.ofReal (diam T ^ (n - 1) * d) ≤
          ENNReal.ofReal ((2 * R) ^ (n - 1) * d) :=
        ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hdiam0 hdiam _) hd0)
      calc
        (volume : Measure 𝔼) (subgradientImage w T) *
              ENNReal.ofReal (diam T ^ (n - 1) * d) ≤
            ENNReal.ofReal b' * ENNReal.ofReal V *
              ENNReal.ofReal ((2 * R) ^ (n - 1) * d) :=
          mul_le_mul' hL hRr
        _ = ENNReal.ofReal (b' * V * ((2 * R) ^ (n - 1) * d)) := by
          rw [← ENNReal.ofReal_mul hb'.le, ← ENNReal.ofReal_mul (by positivity)]
    have hreal : c * (-w y) ^ n ≤ b' * V * ((2 * R) ^ (n - 1) * d) := by
      rw [finrank_euclideanSpace_fin] at hmp
      have := hmp.trans hrhs
      exact
        (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp
          this
    -- `(-w y)^n ≥ ((1-η) H)^n ≥ (1-η)^n a'/2^{n+1}`

    have hpow : (1 - η) ^ n * (a' / 2 ^ (n + 1)) ≤ (-w y) ^ n := by
      calc
        (1 - η) ^ n * (a' / 2 ^ (n + 1)) ≤ (1 - η) ^ n * H ^ n := by gcongr
        _ = ((1 - η) * H) ^ n := by rw [mul_pow]
        _ ≤ (-w y) ^ n := pow_le_pow_left₀ (by positivity) (by linarith) n
    set P : ℝ := b' * V * (2 * R) ^ (n - 1) with hPdef
    have hP : 0 < P := by positivity
    have h1 : c * ((1 - η) ^ n * (a' / 2 ^ (n + 1))) ≤ P * d := by
      calc
        c * ((1 - η) ^ n * (a' / 2 ^ (n + 1))) ≤ c * (-w y) ^ n := by gcongr
        _ ≤ b' * V * ((2 * R) ^ (n - 1) * d) := hreal
        _ = P * d := by rw [hPdef]; ring
    have heq :
      c / (2 ^ (n + 1) * V * (2 * R) ^ (n - 1)) * (1 - η) ^ n * (a' / b') =
        c * ((1 - η) ^ n * (a' / 2 ^ (n + 1))) / P := by
      rw [hPdef]
      field_simp
    rw [heq, div_le_iff₀ hP]
    exact h1.trans_eq (mul_comm P d)

end Normalized

section Main

variable {n : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin n)

private theorem exists_bregman_comparison_core (hn : 0 < n) {a b : ℝ} (ha : 0 < a)
    (hb : 0 < b) :
    ∃ K : ℝ,
      0 < K ∧
        ∀ (u : 𝔼 → ℝ),
          ConvexOn ℝ Set.univ u →
            Continuous u →
              ∀ (x p : 𝔼) (H : ℝ),
                0 < H →
                  (∀ z, u x + ⟪p, z - x⟫ ≤ u z) →
                    Bornology.IsBounded {z | u z < u x + ⟪p, z - x⟫ + H} →
                      (∀ G : Set 𝔼,
                          IsOpen G →
                            G ⊆ {z | u z < u x + ⟪p, z - x⟫ + H} →
                              ENNReal.ofReal a * (volume : Measure 𝔼) G ≤
                                  (volume : Measure 𝔼) (subgradientImage u G) ∧
                                (volume : Measure 𝔼) (subgradientImage u G) ≤
                                  ENNReal.ofReal b * (volume : Measure 𝔼) G) →
                        ∀ y,
                          u y < u x + ⟪p, y - x⟫ + H / 2 →
                            ∀ q : 𝔼,
                              (∀ z, u y + ⟪q, z - y⟫ ≤ u z) →
                                ∀ z : 𝔼,
                                  u z < u x + ⟪p, z - x⟫ + H → u z - u y - ⟪q, z - y⟫ < K * H := by
  -- Fix normalization and interior-margin constants before choosing the section.
  obtain ⟨C₀, hC₀, hnorm⟩ := exists_affine_normalization (E := 𝔼)
  obtain ⟨κ, hκ, hmargin⟩ :=
    exists_normalized_margin hn (2 * C₀)
      (by positivity)
  -- the margin at `η = 1/2`, and the constant `K = 1 + 8 C₀ / m`

  set m : ℝ := κ * (1 / 2) ^ n * (a / b) with hmdef
  have hm : 0 < m := by positivity
  refine ⟨1 + 8 * C₀ / m, by positivity, ?_⟩
  intro u hconv hcont x p H hH hp hbdd hAB y hy q
    hq
  -- the section and the shifted function

  set S : Set 𝔼 := {z | u z < u x + ⟪p, z - x⟫ + H} with hSdef
  set v : 𝔼 → ℝ := fun z => u z - (⟪p, z⟫ + (u x - ⟪p, x⟫ + H)) with hvdef
  have hSv : S = {z | v z < 0} := section_eq_sublevel u x p H
  have hvcont : Continuous v := by rw [hvdef]; fun_prop
  have hvconv : ConvexOn ℝ Set.univ v := convexOn_sub_inner_add_const hconv p _
  have hSo : IsOpen S := by
    apply isOpen_lt hcont
    fun_prop
  have hSc : Convex ℝ S := by
    rw [hSv]
    simpa only [Set.mem_univ, true_and] using hvconv.convex_lt 0
  have hvx : v x = -H := by simp only [hvdef]; ring
  have hxS : x ∈ S := by
    rw [hSv]
    change v x < 0
    rw [hvx]
    linarith
  have hvge : ∀ z, -H ≤ v z := by
    intro z
    have := hp z
    simp only [hvdef]
    rw [inner_sub_right] at this
    linarith
  have hvcl : ∀ z ∈ closure S, v z ≤ 0 := by
    have hsub : closure S ⊆ {z | v z ≤ 0} := by
      apply closure_minimal
      · intro z hz
        rw [hSv] at hz
        change v z < 0 at hz
        exact le_of_lt hz
      · exact isClosed_le hvcont continuous_const
    exact fun z hz => hsub hz
  have hvy : v y < -(1 - 1 / 2) * H := by
    change u y < u x + ⟪p, y - x⟫ + H / 2 at hy
    simp only [hvdef]
    rw [inner_sub_right] at hy
    linarith
  have hyS : y ∈ S := by
    rw [hSv]
    change v y < 0
    linarith
  -- normalization of `closure S` and the dilation by `2`


  -- Normalize the section by an affine map.
  have hKc : IsCompact (closure S) := hbdd.isCompact_closure
  have hKconv : Convex ℝ (closure S) := hSc.closure
  have hintS : interior S = S := hSo.interior_eq
  have hKint : (interior (closure S)).Nonempty := by
    rw [hSc.interior_closure_eq_interior_of_nonempty_interior ⟨x, by rw [hintS]; exact hxS⟩,
      hintS]
    exact ⟨x, hxS⟩
  obtain ⟨e, he1, he2⟩ := hnorm (closure S) hKc hKconv hKint
  let d : 𝔼 ≃ᵃ[ℝ] 𝔼 := (LinearEquiv.smulOfNeZero ℝ 𝔼 (2 : ℝ) two_ne_zero).toAffineEquiv
  have hd : ∀ z : 𝔼, d z = (2 : ℝ) • z := fun z => rfl
  let f : 𝔼 ≃ᵃ[ℝ] 𝔼 := e.trans d
  have hf : ∀ z : 𝔼, f z = (2 : ℝ) • e z := fun z => by
    rw [show f z = d (e z) from AffineEquiv.trans_apply e d z, hd]
  set D : ℝ := |LinearMap.det (f.linear : 𝔼 →ₗ[ℝ] 𝔼)| with hDdef
  have hD : 0 < D := abs_pos.mpr (LinearEquiv.isUnit_det' f.linear).ne_zero
  have hball : closedBall (0 : 𝔼) 2 ⊆ f '' closure S := by
    intro z hz
    rw [mem_closedBall, dist_zero_right] at hz
    have hz' : (1 / 2 : ℝ) • z ∈ closedBall (0 : 𝔼) 1 := by
      rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      linarith
    obtain ⟨z', hz', hez⟩ := he1 hz'
    refine ⟨z', hz', ?_⟩
    rw [hf, hez, smul_smul]
    norm_num
  have hcap : f '' closure S ⊆ closedBall (0 : 𝔼) (2 * C₀) := by
    rintro _ ⟨z, hz, rfl⟩
    have hz' := he2 ⟨z, hz, rfl⟩
    rw [mem_closedBall, dist_zero_right] at hz' ⊢
    rw [hf, norm_smul, Real.norm_eq_abs, abs_two]
    linarith
  -- the normalized section `T = f '' S`

  let Hm : 𝔼 ≃ₜ 𝔼 :=
    { toEquiv := f.toEquiv
      continuous_toFun := f.toAffineMap.continuous_of_finiteDimensional
      continuous_invFun := f.symm.toAffineMap.continuous_of_finiteDimensional }
  have hHm : ⇑Hm = ⇑f := rfl
  have hHms : ⇑Hm.symm = ⇑f.symm := rfl
  have hTo : IsOpen (f '' S) := by
    rw [← hHm]
    exact Hm.isOpenMap S hSo
  have hTcl : closure (f '' S) = f '' closure S := by rw [← hHm, Hm.image_closure]
  have hTc : Convex ℝ (f '' S) := by
    have := hSc.affine_image f.toAffineMap
    simpa only [AffineEquiv.coe_toAffineMap] using this
  have hTsub : f '' S ⊆ closedBall (0 : 𝔼) (2 * C₀) := subset_closure.trans (hTcl ▸ hcap)
  have hTb : Bornology.IsBounded (f '' S) := isBounded_closedBall.subset hTsub
  have hTball : closedBall (0 : 𝔼) 1 ⊆ f '' S := by
    apply closedBall_subset_of_ball_subset_closure (R := 2) hTo hTc ⟨f x, x, hxS, rfl⟩ (by norm_num)
    rw [hTcl]
    exact ball_subset_closedBall.trans hball
  -- the transported function `w = v ∘ f.symm`

  have hwconv : ConvexOn ℝ Set.univ (v ∘ f.symm) := by
    have := hvconv.comp_affineMap f.symm.toAffineMap
    simpa only [Set.preimage_univ, AffineEquiv.coe_toAffineMap] using this
  have hwfr : ∀ z ∈ frontier (f '' S), (v ∘ f.symm) z = 0 := by
    intro z hz
    have hzcl : z ∈ closure (f '' S) := frontier_subset_closure hz
    have hzT : z ∉ f '' S := by
      rw [hTo.frontier_eq] at hz
      exact hz.2
    rw [hTcl] at hzcl
    obtain ⟨z', hz', rfl⟩ := hzcl
    show v (f.symm (f z')) = 0
    rw [f.symm_apply_apply]
    have hle : v z' ≤ 0 := hvcl z' hz'
    have hge : 0 ≤ v z' := by
      have hz'S : z' ∉ S := fun hmem => hzT ⟨z', hmem, rfl⟩
      rw [hSv] at hz'S
      change ¬(v z' < 0) at hz'S
      exact not_lt.mp hz'S
    linarith
  have hwge : ∀ z, -H ≤ (v ∘ f.symm) z := fun z => hvge (f.symm z)
  have hDinv0 : 0 ≤ D⁻¹ :=
    inv_nonneg.mpr
      hD.le
  -- transported density bounds: `a D⁻²` below on open subsets, `b D⁻²` above on `T`


  -- Transport volume and subgradient measure through the normalization.
  have hvolG' :
    ∀ G : Set 𝔼, (volume : Measure 𝔼) (f.symm '' G) = ENNReal.ofReal D⁻¹ * volume G := by
    intro G
    rw [volume_image_affineEquiv f.symm G, abs_det_linear_symm]
  have hsub :
    ∀ G : Set 𝔼,
      (volume : Measure 𝔼) (subgradientImage (v ∘ f.symm) G) =
        ENNReal.ofReal D⁻¹ * (volume : Measure 𝔼) (subgradientImage v (f.symm '' G)) := by
    intro G
    have hGG' : f '' (f.symm '' G) = G := by
      rw [Set.image_image]
      simp only [AffineEquiv.apply_symm_apply, Set.image_id']
    conv_lhs => rw [← hGG']
    exact volume_subgradientImage_comp_affineEquiv_symm v f (f.symm '' G)
  have hvAB :
    ∀ G : Set 𝔼,
      IsOpen G →
        G ⊆ S →
          ENNReal.ofReal a * (volume : Measure 𝔼) G ≤
              (volume : Measure 𝔼) (subgradientImage v G) ∧
            (volume : Measure 𝔼) (subgradientImage v G) ≤
              ENNReal.ofReal b * (volume : Measure 𝔼) G := by
    intro G hG hGS
    rw [hvdef, volume_subgradientImage_sub_inner_add_const]
    exact hAB G hG hGS
  have hwA :
    ∀ G : Set 𝔼,
      IsOpen G →
        G ⊆ f '' S →
          ENNReal.ofReal (a * D⁻¹ * D⁻¹) * (volume : Measure 𝔼) G ≤
            (volume : Measure 𝔼) (subgradientImage (v ∘ f.symm) G) := by
    intro G hG hGT
    have hG'o : IsOpen (f.symm '' G) := by
      rw [← hHms]
      exact Hm.symm.isOpenMap G hG
    have hG'S : f.symm '' G ⊆ S := by
      rintro _ ⟨z, hz, rfl⟩
      obtain ⟨z', hz'S, rfl⟩ := hGT hz
      rw [f.symm_apply_apply]
      exact hz'S
    calc
      ENNReal.ofReal (a * D⁻¹ * D⁻¹) * (volume : Measure 𝔼) G =
          ENNReal.ofReal D⁻¹ *
            (ENNReal.ofReal a * (ENNReal.ofReal D⁻¹ * (volume : Measure 𝔼) G)) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul ha.le]
        ring
      _ = ENNReal.ofReal D⁻¹ * (ENNReal.ofReal a * (volume : Measure 𝔼) (f.symm '' G)) := by
        rw [hvolG']
      _ ≤ ENNReal.ofReal D⁻¹ * (volume : Measure 𝔼) (subgradientImage v (f.symm '' G)) := by
        gcongr
        exact (hvAB _ hG'o hG'S).1
      _ = (volume : Measure 𝔼) (subgradientImage (v ∘ f.symm) G) := (hsub G).symm
  have hwB :
    (volume : Measure 𝔼) (subgradientImage (v ∘ f.symm) (f '' S)) ≤
      ENNReal.ofReal (b * D⁻¹ * D⁻¹) * (volume : Measure 𝔼) (f '' S) := by
    have hSS : f.symm '' (f '' S) = S := by
      rw [Set.image_image]
      simp only [AffineEquiv.symm_apply_apply, Set.image_id']
    calc
      (volume : Measure 𝔼) (subgradientImage (v ∘ f.symm) (f '' S)) =
          ENNReal.ofReal D⁻¹ * (volume : Measure 𝔼) (subgradientImage v S) := by
        rw [hsub, hSS]
      _ ≤ ENNReal.ofReal D⁻¹ * (ENNReal.ofReal b * (volume : Measure 𝔼) S) := by
        gcongr
        exact (hvAB S hSo subset_rfl).2
      _ = ENNReal.ofReal D⁻¹ * (ENNReal.ofReal b * (volume : Measure 𝔼) (f.symm '' (f '' S))) := by
        rw [hSS]
      _ = ENNReal.ofReal (b * D⁻¹ * D⁻¹) * (volume : Measure 𝔼) (f '' S) := by
        rw [hvolG', ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hb.le]
        ring
  -- the margin at `f y`

  have hfyT : f y ∈ f '' S := ⟨y, hyS, rfl⟩
  have hwfy : (v ∘ f.symm) (f y) < -(1 - 1 / 2) * H := by
    show v (f.symm (f y)) < -(1 - 1 / 2) * H
    rw [f.symm_apply_apply]
    exact hvy
  have ha' : 0 < a * D⁻¹ * D⁻¹ := by positivity
  have hb' : 0 < b * D⁻¹ * D⁻¹ := by positivity
  have hmarg :=
    hmargin (v ∘ f.symm) hwconv (f '' S) hTo hTc hTb hTball hTsub hwfr H hH hwge _ _ ha' hb' hwA
      hwB (1 / 2) (by norm_num) (by norm_num) (f y) hfyT hwfy
  have hratio : a * D⁻¹ * D⁻¹ / (b * D⁻¹ * D⁻¹) = a / b := by field_simp
  rw [hratio] at hmarg
  have hmarg' : m ≤ infDist (f y) (frontier (f '' S)) := by
    have hhalf : ((1 : ℝ) - 1 / 2) = 1 / 2 := by norm_num
    rw [hhalf] at hmarg
    exact
      hmarg
  -- test points `f y + (m/2) • w₀` lie in the normalized section


  -- Use the interior margin to test all directions and bound the final affine defect.
  have htest : ∀ w₀ : 𝔼, ‖w₀‖ = 1 → f y + (m / 2) • w₀ ∈ f '' S := by
    intro w₀ hw₀
    by_contra
      hnot
    -- the segment from `f y` to the test point meets the frontier within distance `m/2 < m`

    have hseg : IsPreconnected (segment ℝ (f y) (f y + (m / 2) • w₀)) :=
      (convex_segment _ _).isPreconnected
    have hne : (segment ℝ (f y) (f y + (m / 2) • w₀) ∩ f '' S).Nonempty :=
      ⟨f y, left_mem_segment _ _ _, hfyT⟩
    have hnot' : ¬segment ℝ (f y) (f y + (m / 2) • w₀) ⊆ f '' S := fun hsub' =>
      hnot (hsub' (right_mem_segment _ _ _))
    have hcross : ¬(closure (f '' S) ∩ segment ℝ (f y) (f y + (m / 2) • w₀) ⊆ f '' S) :=
      fun hc => hnot' (hseg.subset_of_closure_inter_subset hTo hne hc)
    rw [Set.not_subset] at hcross
    obtain ⟨z, ⟨hzcl, hzseg⟩, hzT⟩ := hcross
    have hzfr : z ∈ frontier (f '' S) := by
      rw [hTo.frontier_eq]
      exact ⟨hzcl, hzT⟩
    rw [segment_eq_image'] at hzseg
    obtain ⟨t, ht, rfl⟩ := hzseg
    have hdist : dist (f y) (f y + t • (f y + (m / 2) • w₀ - f y)) ≤ m / 2 := by
      rw [dist_eq_norm, add_sub_cancel_left, smul_smul, sub_add_cancel_left, norm_neg,
        norm_smul, hw₀, mul_one, Real.norm_eq_abs, abs_mul, abs_of_nonneg ht.1,
        abs_of_pos (by positivity : (0 : ℝ) < m / 2)]
      nlinarith [ht.2, hm]
    have := infDist_le_dist_of_mem (x := f y) hzfr
    linarith [hmarg']
  -- bound `⟪q - p, f.symm.linear w₀⟫ ≤ 2H/m` for unit `w₀`

  have hpair : ∀ w₀ : 𝔼, ‖w₀‖ = 1 → ⟪q - p, f.symm.linear w₀⟫ ≤ 2 * H / m := by
    intro w₀ hw₀
    obtain ⟨z, hzS, hz⟩ :=
      htest w₀
        hw₀
    -- `z = f.symm (f y + (m/2) • w₀)`, so `z - y = f.symm.linear ((m/2) • w₀)`

    have hzy : z - y = (m / 2) • f.symm.linear w₀ := by
      have h1 : z = f.symm (f y + (m / 2) • w₀) := by rw [← hz, f.symm_apply_apply]
      have h3 := affineEquiv_sub f.symm (f y) (f y + (m / 2) • w₀)
      rw [f.symm_apply_apply] at h3
      rw [h1, h3, add_sub_cancel_left, map_smul]
    have hq' := hq z
    have hvz : v z < 0 := by rw [hSv] at hzS; exact hzS
    have hvyH : -H ≤ v y := hvge y
    have hvz' : u z - u y = v z - v y + ⟪p, z - y⟫ := by
      simp only [hvdef]
      rw [inner_sub_right]
      ring
    have hkey : ⟪q - p, z - y⟫ ≤ H := by
      rw [inner_sub_left]
      linarith
    rw [hzy, inner_smul_right] at hkey
    rw [le_div_iff₀ hm]
    linarith
  intro z hz
  have hzS : z ∈ S :=
    hz
  -- Both normalized points lie in the ball of radius `2 C₀`.

  have hzy : z - y = f.symm.linear (f z - f y) := by
    rw [← affineEquiv_sub f.symm, f.symm_apply_apply, f.symm_apply_apply]
  have hfzy : ‖f z - f y‖ ≤ 4 * C₀ := by
    have hz' := hTsub ⟨z, hzS, rfl⟩
    have hy' := hTsub hfyT
    rw [mem_closedBall, dist_zero_right] at hz' hy'
    calc
      ‖f z - f y‖ ≤ ‖f z‖ + ‖f y‖ := norm_sub_le _ _
      _ ≤ 2 * C₀ + 2 * C₀ := add_le_add hz' hy'
      _ = 4 * C₀ := by ring
  have hinner : -(4 * C₀ * (2 * H / m)) ≤ ⟪q - p, z - y⟫ := by
    by_cases hzy0 : f z - f y = 0
    · rw [hzy, hzy0, map_zero, inner_zero_right]
      have : 0 ≤ 4 * C₀ * (2 * H / m) := by positivity
      linarith
    · set r : ℝ := ‖f z - f y‖ with hrdef
      have hr : 0 < r := norm_pos_iff.mpr hzy0
      set w₀ : 𝔼 := (-(1 / r)) • (f z - f y) with hw₀def
      have hw₀ : ‖w₀‖ = 1 := by
        rw [hw₀def, norm_smul, norm_neg, Real.norm_eq_abs, abs_of_pos (by positivity), ← hrdef]
        field_simp
      have hrep : f z - f y = (-r) • w₀ := by
        rw [hw₀def, smul_smul]
        have : -r * -(1 / r) = 1 := by field_simp
        rw [this, one_smul]
      have h := hpair w₀ hw₀
      rw [hzy, hrep, map_smul, inner_smul_right]
      have hm2 : 0 ≤ 2 * H / m := by positivity
      nlinarith [hfzy, h, hm2, hr]
  have hdefect : u z - u y - ⟪q, z - y⟫ = v z - v y - ⟪q - p, z - y⟫ := by
    simp only [hvdef, inner_sub_left, inner_sub_right]
    ring
  have hvz : v z < 0 := by
    rw [hSv] at hzS
    exact hzS
  have hvyH : -H ≤ v y := hvge y
  have hK : (1 + 8 * C₀ / m) * H = H + 4 * C₀ * (2 * H / m) := by
    field_simp
    ring
  rw [hdefect, hK]
  linarith

/--
**Bregman comparison on the half-height section (soft engulfing).** For every `n > 0` and density
bounds
`0 < a`, `0 < b` there is `K = K(n, a, b) > 0` such that: for every convex continuous `u`,
supporting slope `p` at
`x`, `H > 0` with bounded section `S = S_H(x)` and `a |G| ≤ |∂u(G)| ≤ b |G|` for open `G ⊆ S`, every
`y` in the
half-height section `S_{H/2}(x)` and every subgradient `q` of `u` at `y` satisfy
`u x − u y − ⟪q, x − y⟫ ≤ K H`.

This comparison is an instance of the section geometry of Forzani–Maldonado (2004). -/
theorem exists_bregman_comparison (hn : 0 < n) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∃ K : ℝ,
      0 < K ∧
        ∀ (u : 𝔼 → ℝ),
          ConvexOn ℝ Set.univ u →
            Continuous u →
              ∀ (x p : 𝔼) (H : ℝ),
                0 < H →
                  (∀ z, u x + ⟪p, z - x⟫ ≤ u z) →
                    Bornology.IsBounded {z | u z < u x + ⟪p, z - x⟫ + H} →
                      (∀ G : Set 𝔼,
                          IsOpen G →
                            G ⊆ {z | u z < u x + ⟪p, z - x⟫ + H} →
                              ENNReal.ofReal a * (volume : Measure 𝔼) G ≤
                                  (volume : Measure 𝔼) (subgradientImage u G) ∧
                                (volume : Measure 𝔼) (subgradientImage u G) ≤
                                  ENNReal.ofReal b * (volume : Measure 𝔼) G) →
                        ∀ y,
                          u y < u x + ⟪p, y - x⟫ + H / 2 →
                            ∀ q : 𝔼,
                              (∀ z, u y + ⟪q, z - y⟫ ≤ u z) → u x - u y - ⟪q, x - y⟫ ≤ K * H := by
  obtain ⟨K, hK, hcore⟩ := exists_bregman_comparison_core hn ha hb
  refine ⟨K, hK, ?_⟩
  intro u hconv hcont x p H hH hp hbdd hAB y hy q hq
  have hx : u x < u x + ⟪p, x - x⟫ + H := by
    simp only [sub_self, inner_zero_right, add_zero]
    linarith
  exact (hcore u hconv hcont x p H hH hp hbdd hAB y hy q hq x hx).le

/-- **Small-section engulfing (Forzani–Maldonado, 2004, section geometry).**
For positive two-sided Alexandrov density bounds, there is `C = C(n, a, b) > 1`
such that, whenever `S_{2h}(x)` is bounded and has those bounds on every open
subset, each `y ∈ S_h(x)` and every supporting slope `q` at `y` satisfy
`S_h(x) ⊆ S_{C h}(y)`. Both sections in the inclusion use strict inequalities. -/
theorem exists_section_engulfing (hn : 0 < n) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∃ C : ℝ, 1 < C ∧ ∀ (u : 𝔼 → ℝ), ConvexOn ℝ Set.univ u → Continuous u →
      ∀ (x p : 𝔼) (h : ℝ), 0 < h → (∀ z, u x + ⟪p, z - x⟫ ≤ u z) →
      Bornology.IsBounded {z | u z < u x + ⟪p, z - x⟫ + 2 * h} →
      (∀ G : Set 𝔼, IsOpen G → G ⊆ {z | u z < u x + ⟪p, z - x⟫ + 2 * h} →
        ENNReal.ofReal a * (volume : Measure 𝔼) G ≤ (volume : Measure 𝔼) (subgradientImage u G) ∧
        (volume : Measure 𝔼) (subgradientImage u G) ≤ ENNReal.ofReal b * (volume : Measure 𝔼) G) →
      ∀ y, u y < u x + ⟪p, y - x⟫ + h →
        ∀ q : 𝔼, (∀ z, u y + ⟪q, z - y⟫ ≤ u z) →
          {z | u z < u x + ⟪p, z - x⟫ + h} ⊆
            {z | u z < u y + ⟪q, z - y⟫ + C * h} := by
  obtain ⟨K, hK, hcore⟩ := exists_bregman_comparison_core hn ha hb
  refine ⟨2 * (K + 1), by linarith, ?_⟩
  intro u hconv hcont x p h hh hp hbdd hAB y hy q hq z hz
  change u z < u x + ⟪p, z - x⟫ + h at hz
  have hy' : u y < u x + ⟪p, y - x⟫ + (2 * h) / 2 := by
    linarith
  have hz' : u z < u x + ⟪p, z - x⟫ + 2 * h := by
    linarith
  have hDz := hcore u hconv hcont x p (2 * h) (by linarith)
    hp hbdd hAB y hy' q hq z hz'
  change u z < u y + ⟪q, z - y⟫ + (2 * (K + 1)) * h
  nlinarith only [hDz, hh]

/-- The `κ`-form of the comparison (Forzani–Maldonado): if for every height `H` with `2 D(x, y) < H
≤ H₀` the
section `S_H(x)` is bounded with the density bounds, then `D(y, x) ≤ 2K · D(x, y)`, where
`D(x, y) = u y − u x − ⟪p, y − x⟫` and `D(y, x) = u x − u y − ⟪q, x − y⟫` for the given
subgradients. -/
theorem bregman_comparison_of_sections (hn : 0 < n) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∃ K : ℝ, 0 < K ∧ ∀ (u : 𝔼 → ℝ), ConvexOn ℝ Set.univ u → Continuous u →
      ∀ (x p : 𝔼), (∀ z, u x + ⟪p, z - x⟫ ≤ u z) →
      ∀ (y q : 𝔼), (∀ z, u y + ⟪q, z - y⟫ ≤ u z) →
      ∀ H₀ : ℝ, 2 * (u y - u x - ⟪p, y - x⟫) < H₀ →
      (∀ H : ℝ, 2 * (u y - u x - ⟪p, y - x⟫) < H → H ≤ H₀ →
        Bornology.IsBounded {z | u z < u x + ⟪p, z - x⟫ + H} ∧
        ∀ G : Set 𝔼, IsOpen G → G ⊆ {z | u z < u x + ⟪p, z - x⟫ + H} →
          ENNReal.ofReal a * (volume : Measure 𝔼) G ≤ (volume : Measure 𝔼) (subgradientImage u G) ∧
          (volume : Measure 𝔼) (subgradientImage u G) ≤ ENNReal.ofReal b * (volume : Measure 𝔼) G) →
      u x - u y - ⟪q, x - y⟫ ≤ 2 * K * (u y - u x - ⟪p, y - x⟫) := by
  obtain ⟨K, hK, hcomp⟩ := exists_bregman_comparison hn ha hb
  refine ⟨K, hK, fun u hconv hcont x p hp y q hq H₀ hH₀ hsec => ?_⟩
  set Dxy : ℝ := u y - u x - ⟪p, y - x⟫ with hDxy
  have hDxy0 : 0 ≤ Dxy := by
    have := hp y
    rw [hDxy]
    linarith
  -- for every `ε > 0` small, `H = 2 Dxy + ε` is admissible and `y ∈ S_{H/2}(x)`
  apply le_of_forall_pos_le_add
  intro ε hε
  set ε' : ℝ := min (ε / K) (H₀ - 2 * Dxy) with hε'def
  have hε'0 : 0 < ε' := lt_min (by positivity) (by linarith)
  have hKε : K * ε' ≤ ε := by
    calc K * ε' ≤ K * (ε / K) := by gcongr; exact min_le_left _ _
      _ = ε := by field_simp
  have hH : 2 * Dxy < 2 * Dxy + ε' := by linarith
  have hHle : 2 * Dxy + ε' ≤ H₀ := by
    have := min_le_right (ε / K) (H₀ - 2 * Dxy)
    rw [← hε'def] at this
    linarith
  obtain ⟨hbdd, hAB⟩ := hsec (2 * Dxy + ε') hH hHle
  have hy : u y < u x + ⟪p, y - x⟫ + (2 * Dxy + ε') / 2 := by rw [hDxy]; linarith
  have h := hcomp u hconv hcont x p (2 * Dxy + ε') (by positivity) hp hbdd hAB y hy q hq
  calc u x - u y - ⟪q, x - y⟫ ≤ K * (2 * Dxy + ε') := h
    _ = 2 * K * Dxy + K * ε' := by ring
    _ ≤ 2 * K * Dxy + ε := by linarith

end Main

section Scalar

/-- A scalar differential inequality makes the real-power quotient
monotone on `(0,1]`. No sign assumption on `F` is required. -/
private theorem monotoneOn_div_rpow_of_mul_le_deriv
    {F F' : ℝ → ℝ} {q : ℝ}
    (hF : ∀ t ∈ Ioc (0 : ℝ) 1, HasDerivAt F (F' t) t)
    (hineq : ∀ t ∈ Ioc (0 : ℝ) 1, q * F t ≤ t * F' t) :
    MonotoneOn (fun t : ℝ => F t / t ^ q) (Ioc (0 : ℝ) 1) := by
  let G : ℝ → ℝ := fun t => F t / t ^ q
  let H : ℝ → ℝ := fun t =>
    (F' t * t ^ q - F t * (q * t ^ (q - 1))) / (t ^ q) ^ 2
  have hG : ∀ t ∈ Ioc (0 : ℝ) 1, HasDerivAt G (H t) t := by
    intro t ht
    dsimp only [G, H]
    exact (hF t ht).div
      (Real.hasDerivAt_rpow_const (Or.inl ht.1.ne'))
      (Real.rpow_pos_of_pos ht.1 q).ne'
  have hH : ∀ t ∈ Ioc (0 : ℝ) 1, 0 ≤ H t := by
    intro t ht
    have hpow : t ^ q = t * t ^ (q - 1) := by
      calc
        t ^ q = t ^ (1 + (q - 1)) := by
          rw [show (1 : ℝ) + (q - 1) = q by ring]
        _ = t ^ (1 : ℝ) * t ^ (q - 1) :=
          Real.rpow_add ht.1 _ _
        _ = t * t ^ (q - 1) := by rw [Real.rpow_one]
    have hnum :
        F' t * t ^ q - F t * (q * t ^ (q - 1)) =
          t ^ (q - 1) * (t * F' t - q * F t) := by
      rw [hpow]
      ring
    dsimp only [H]
    rw [hnum]
    exact div_nonneg
      (mul_nonneg
        (Real.rpow_nonneg ht.1.le _)
        (sub_nonneg.mpr (hineq t ht)))
      (sq_nonneg _)
  change MonotoneOn G (Ioc (0 : ℝ) 1)
  apply monotoneOn_of_deriv_nonneg (convex_Ioc (0 : ℝ) 1)
  · intro t ht
    exact (hG t ht).continuousAt.continuousWithinAt
  · intro t ht
    exact (hG t (interior_subset ht)).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [(hG t (interior_subset ht)).deriv]
    exact hH t (interior_subset ht)

end Scalar

section InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

/-- The increment above the tangent plane at the first point. -/
def defect (u : E → ℝ) (x z : E) : ℝ :=
  u z - u x - ⟪gradient u x, z - x⟫

/-- The derivative of the tangent defect along an affine ray. -/
private theorem hasDerivAt_defect_ray
    {u : E → ℝ} (hdiff : Differentiable ℝ u)
    (x v : E) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ => defect u x (x + s • v))
      ⟪gradient u (x + t • v) - gradient u x, v⟫ t := by
  have hp : HasDerivAt (fun s : ℝ => x + s • v) v t := by
    simpa only [id_eq, one_smul] using
      ((hasDerivAt_id t).smul_const v).const_add x
  have hu :
      HasDerivAt (fun s : ℝ => u (x + s • v))
        ⟪gradient u (x + t • v), v⟫ t := by
    simpa only [Function.comp_def, InnerProductSpace.toDual_apply_apply] using
      (hdiff (x + t • v)).hasGradientAt.hasFDerivAt.comp_hasDerivAt t hp
  have hlin :
      HasDerivAt
        (fun s : ℝ => s * ⟪gradient u x, v⟫)
        ⟪gradient u x, v⟫ t := by
    simpa only [id_eq, one_mul] using
      (hasDerivAt_id t).mul_const ⟪gradient u x, v⟫
  have heq : (fun s : ℝ => defect u x (x + s • v)) =
      ((fun s : ℝ => u (x + s • v) - u x) - fun s : ℝ => s * ⟪gradient u x, v⟫) := by
    funext s
    simp only [defect, Pi.sub_apply, add_sub_cancel_left, inner_smul_right]
  rw [heq, inner_sub_left]
  exact (hu.sub_const (u x)).sub hlin

/-- Local soft engulfing, in the stated direction, makes the tangent-defect
quotient monotone along each ray whose endpoint lies in the allowed ball.

Only differentiability is needed for this analytic implication. -/
theorem monotoneOn_ray_quotient_of_soft
    {u : E → ℝ} (hdiff : Differentiable ℝ u)
    {r₀ κ : ℝ} (hκ : 1 ≤ κ) {x : E}
    (hsoft : ∀ z : E, ‖z - x‖ ≤ r₀ →
      defect u x z ≤ κ * defect u z x)
    {v : E} (hv : ‖v‖ ≤ r₀) :
    MonotoneOn
      (fun t : ℝ =>
        defect u x (x + t • v) / t ^ (1 + κ⁻¹))
      (Ioc (0 : ℝ) 1) := by
  refine monotoneOn_div_rpow_of_mul_le_deriv
    (F' := fun t : ℝ =>
      ⟪gradient u (x + t • v) - gradient u x, v⟫) ?_ ?_
  · intro t _
    exact hasDerivAt_defect_ray hdiff x v t
  · intro t ht
    have hdist : ‖x + t • v - x‖ ≤ r₀ := by
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_pos ht.1]
      calc
        t * ‖v‖ ≤ 1 * ‖v‖ :=
          mul_le_mul_of_nonneg_right ht.2 (norm_nonneg _)
        _ ≤ r₀ := by simpa only [one_mul] using hv
    have hrev :
        defect u (x + t • v) x =
          t * ⟪gradient u (x + t • v) - gradient u x, v⟫ -
            defect u x (x + t • v) := by
      simp only [defect,
        show x - (x + t • v) = -(t • v) by abel,
        add_sub_cancel_left, inner_neg_right, inner_smul_right,
        inner_sub_left]
      ring
    have hs := hsoft (x + t • v) hdist
    rw [hrev] at hs
    have hkpos : 0 < κ := lt_of_lt_of_le zero_lt_one hκ
    have hdiv :
        defect u x (x + t • v) / κ ≤
          t * ⟪gradient u (x + t • v) - gradient u x, v⟫ -
            defect u x (x + t • v) := by
      apply (div_le_iff₀ hkpos).mpr
      simpa only [mul_comm] using hs
    have hscaled :
        κ⁻¹ * defect u x (x + t • v) ≤
          t * ⟪gradient u (x + t • v) - gradient u x, v⟫ -
            defect u x (x + t • v) := by
      simpa only [div_eq_mul_inv, mul_comm] using hdiv
    nlinarith only [hscaled]

/-- Pointwise ray growth from local soft engulfing, for `0 < t ≤ 1`. -/
theorem defect_ray_le_of_soft
    {u : E → ℝ} (hdiff : Differentiable ℝ u)
    {r₀ κ : ℝ} (hκ : 1 ≤ κ) {x : E}
    (hsoft : ∀ z : E, ‖z - x‖ ≤ r₀ →
      defect u x z ≤ κ * defect u z x)
    {v : E} (hv : ‖v‖ ≤ r₀)
    {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) :
    defect u x (x + t • v) ≤
      defect u x (x + v) * t ^ (1 + κ⁻¹) := by
  have hmono :=
    monotoneOn_ray_quotient_of_soft hdiff hκ hsoft hv
  have hone : (1 : ℝ) ∈ Ioc (0 : ℝ) 1 := ⟨zero_lt_one, le_rfl⟩
  have hquot := hmono ht hone ht.2
  have hquot' :
      defect u x (x + t • v) / t ^ (1 + κ⁻¹) ≤
        defect u x (x + v) := by
    simpa only [one_smul, Real.one_rpow, div_one] using hquot
  exact
    (div_le_iff₀ (Real.rpow_pos_of_pos ht.1 (1 + κ⁻¹))).mp hquot'

/-- Quantitative radial growth from a sphere bound and local soft engulfing.

The norm hypothesis is precisely membership in the closed ball of radius `R`.
The case `z = x` is included. -/
theorem defect_le_sphere_bound_of_soft
    {u : E → ℝ} (hdiff : Differentiable ℝ u)
    {R κ : ℝ} (hR : 0 < R) (hκ : 1 ≤ κ) {x : E}
    (hsoft : ∀ z : E, ‖z - x‖ ≤ R →
      defect u x z ≤ κ * defect u z x)
    {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ z : E, ‖z - x‖ = R → defect u x z ≤ M) :
    ∀ z : E, ‖z - x‖ ≤ R →
      defect u x z ≤ M * (‖z - x‖ / R) ^ (1 + κ⁻¹) := by
  intro z hz
  by_cases hzx : z = x
  · have hzdef : defect u x z = 0 := by
      simp [defect, hzx]
    rw [hzdef]
    exact mul_nonneg hM
      (Real.rpow_nonneg
        (div_nonneg (norm_nonneg _) hR.le) _)
  · have hr : 0 < ‖z - x‖ :=
      norm_pos_iff.mpr (sub_ne_zero.mpr hzx)
    let v : E := (R / ‖z - x‖) • (z - x)
    have hvnorm : ‖v‖ = R := by
      dsimp only [v]
      rw [norm_smul, Real.norm_eq_abs,
        abs_of_pos (div_pos hR hr),
        div_mul_cancel₀ _ hr.ne']
    have ht : ‖z - x‖ / R ∈ Ioc (0 : ℝ) 1 := by
      refine ⟨div_pos hr hR, ?_⟩
      apply (div_le_iff₀ hR).mpr
      simpa only [one_mul] using hz
    have hscale :
        (‖z - x‖ / R) * (R / ‖z - x‖) = (1 : ℝ) := by
      field_simp [hR.ne', hr.ne']
    have hpath : x + (‖z - x‖ / R) • v = z := by
      dsimp only [v]
      rw [smul_smul, hscale, one_smul]
      abel
    have hb : defect u x (x + v) ≤ M := by
      apply hbound (x + v)
      simpa only [add_sub_cancel_left] using hvnorm
    have hgrowth :=
      defect_ray_le_of_soft hdiff hκ hsoft (le_of_eq hvnorm) ht
    rw [hpath] at hgrowth
    exact hgrowth.trans
      (mul_le_mul_of_nonneg_right hb
        (Real.rpow_nonneg
          (div_nonneg (norm_nonneg _) hR.le) _))

/-- A global Lipschitz bound and a bound on the gradient at the centre give
the explicit sphere constant `M = (L + B) * R`.

Neither convexity nor positivity of the tangent defect is needed here. -/
theorem defect_le_of_lipschitz_soft
    {u : E → ℝ} (hdiff : Differentiable ℝ u)
    {L : NNReal} (hLip : LipschitzWith L u)
    {R κ : ℝ} (hR : 0 < R) (hκ : 1 ≤ κ)
    {x : E} {B : ℝ} (hB : ‖gradient u x‖ ≤ B)
    (hsoft : ∀ z : E, ‖z - x‖ ≤ R →
      defect u x z ≤ κ * defect u z x) :
    ∀ z : E, ‖z - x‖ ≤ R →
      defect u x z ≤
        (((L : ℝ) + B) * R) *
          (‖z - x‖ / R) ^ (1 + κ⁻¹) := by
  have hB0 : 0 ≤ B := (norm_nonneg (gradient u x)).trans hB
  refine defect_le_sphere_bound_of_soft hdiff hR hκ hsoft
    (mul_nonneg (add_nonneg L.coe_nonneg hB0) hR.le) ?_
  intro z hz
  have huabs : |u z - u x| ≤ (L : ℝ) * ‖z - x‖ := by
    simpa only [dist_eq_norm, Real.norm_eq_abs] using
      hLip.dist_le_mul z x
  have hu : u z - u x ≤ (L : ℝ) * ‖z - x‖ :=
    (le_abs_self _).trans huabs
  have hinner :
      -⟪gradient u x, z - x⟫ ≤ B * ‖z - x‖ := by
    calc
      -⟪gradient u x, z - x⟫ ≤ |⟪gradient u x, z - x⟫| :=
        neg_le_abs _
      _ ≤ ‖gradient u x‖ * ‖z - x‖ :=
        abs_real_inner_le_norm _ _
      _ ≤ B * ‖z - x‖ :=
        mul_le_mul_of_nonneg_right hB (norm_nonneg _)
  calc
    defect u x z ≤ ((L : ℝ) + B) * ‖z - x‖ := by
      dsimp only [defect]
      nlinarith only [hu, hinner]
    _ = ((L : ℝ) + B) * R := by rw [hz]

/-- Compact-local soft engulfing yields a finite Hölder constant for the
gradient, with exponent `κ⁻¹`.

The compact set, radius, and engulfing constant are fixed before the
centres and comparison points. This is a conditional analytic theorem,
not a producer of the soft-engulfing hypothesis. -/
theorem exists_holder_gradient_of_lipschitz_local_soft
    {u : E → ℝ}
    (hconv : ConvexOn ℝ univ u)
    (hC1 : ContDiff ℝ 1 u)
    {L : NNReal} (hLip : LipschitzWith L u)
    {K : Set E} (hK : IsCompact K)
    {r₀ κ : ℝ} (hr₀ : 0 < r₀) (hκ : 1 ≤ κ)
    (hsoft : ∀ x ∈ K, ∀ z : E, ‖z - x‖ ≤ r₀ →
      defect u x z ≤ κ * defect u z x) :
    ∃ C' : ℝ, 0 ≤ C' ∧
      ∀ x ∈ K, ∀ y ∈ K,
        ‖gradient u y - gradient u x‖ ≤
          C' * ‖y - x‖ ^ κ⁻¹ := by
  have hdiff : Differentiable ℝ u :=
    hC1.differentiable one_ne_zero
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn
    (FunctionalInequalities.Analysis.BakryEmery.continuous_gradient
      hC1).continuousOn
  let Bp : ℝ := max B 0
  have hBp0 : 0 ≤ Bp := le_max_right _ _
  have hgrad : ∀ x ∈ K, ‖gradient u x‖ ≤ Bp := by
    intro x hx
    exact (hB x hx).trans (le_max_left _ _)
  let C : ℝ :=
    (((L : ℝ) + Bp) * r₀) / r₀ ^ (1 + κ⁻¹)
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact div_nonneg
      (mul_nonneg (add_nonneg L.coe_nonneg hBp0) hr₀.le)
      (Real.rpow_nonneg hr₀.le _)
  have hκ0 : 0 ≤ κ := le_trans zero_le_one hκ
  have hα : 0 ≤ κ⁻¹ := inv_nonneg.mpr hκ0
  refine exists_holder_gradient_of_growth
    hconv hC1 hK hC hα hr₀ ?_
  intro x hx z hz
  have hrad :=
    defect_le_of_lipschitz_soft hdiff hLip hr₀ hκ
      (hgrad x hx) (hsoft x hx) z hz
  have hgrowth :
      defect u x z ≤ C * ‖z - x‖ ^ (1 + κ⁻¹) := by
    calc
      defect u x z ≤
          (((L : ℝ) + Bp) * r₀) *
            (‖z - x‖ / r₀) ^ (1 + κ⁻¹) := hrad
      _ = C * ‖z - x‖ ^ (1 + κ⁻¹) := by
        dsimp only [C]
        rw [Real.div_rpow (norm_nonneg _) hr₀.le]
        ring
  dsimp only [defect] at hgrowth
  linarith

end InnerProduct


end FunctionalInequalities.Analysis.SoftEngulfing

namespace FunctionalInequalities.Analysis
section ClosedHolder
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

private theorem gradient_support {u : E → ℝ} (hc : ConvexOn ℝ univ u)
    (hdiff : Differentiable ℝ u) (x y : E) : u x + ⟪gradient u x, y - x⟫ ≤ u y := by
  have hp : HasDerivAt (fun t : ℝ => x + t • (y - x)) (y - x) 0 := by
    simpa only [id_eq, one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const (y - x)).const_add x
  have hu :
    HasFDerivAt u ((InnerProductSpace.toDual ℝ E) (gradient u x)) (x + (0 : ℝ) • (y - x)) := by
    simpa only [zero_smul, add_zero] using (hdiff x).hasGradientAt.hasFDerivAt
  have hline := hu.comp_hasDerivAt 0 hp
  have hcl : ConvexOn ℝ univ (fun t : ℝ => u (x + t • (y - x))) := by
    simpa only [Set.preimage_univ, Function.comp_def, AffineMap.lineMap_apply_module',
      add_comm] using hc.comp_affineMap (AffineMap.lineMap x y)
  have h := hcl.le_slope_of_hasDerivAt (mem_univ 0) (mem_univ 1) zero_lt_one hline
  simp only [slope_def_field, zero_smul, one_smul, add_zero, add_sub_cancel, sub_zero, div_one,
    InnerProductSpace.toDual_apply_apply] at h
  linarith

/-- Compact-uniform engulfing at an actual Alexandrov solution. The constant
and height precede all centres and points; no engulfing or regularity estimate
is supplied as an input. -/
theorem exists_section_engulfing_of_alexandrov_density (hn : 0 < n)
    {u f : E → ℝ} (hs : StrictConvexOn ℝ univ u) (hC1 : ContDiff ℝ 1 u)
    (hf : Continuous f) (hfpos : ∀ x, 0 < f x)
    (hMA : ∀ G : Set E, IsOpen G → volume (subgradientImage u G) =
      ∫⁻ y in G, ENNReal.ofReal (f y)) {K : Set E} (hK : IsCompact K) :
    ∃ C H : ℝ, 1 < C ∧ 0 < H ∧ ∀ x ∈ K, ∀ h : ℝ, 0 < h → h ≤ H →
      ∀ y z : E, SoftEngulfing.defect u x y < h → SoftEngulfing.defect u x z < h →
        SoftEngulfing.defect u y z < C * h := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨a, b, H, ha, hb, hH, hsections⟩ :=
    exists_uniform_section_density_bounds hs hC1 hf hfpos hMA hK
  obtain ⟨C, hC, heng⟩ := SoftEngulfing.exists_section_engulfing hn ha hb
  have hsup := gradient_support hs.convexOn (hC1.differentiable one_ne_zero)
  refine ⟨C, H / 2, hC, by positivity, ?_⟩
  intro x hx h hh hhH y z hy hz
  obtain ⟨hbdd, hAB⟩ := hsections x hx (2 * h) (by positivity) (by linarith)
  have hy' : u y < u x + ⟪gradient u x, y - x⟫ + h := by
    dsimp only [SoftEngulfing.defect] at hy
    linarith
  have hz' : u z < u x + ⟪gradient u x, z - x⟫ + h := by
    dsimp only [SoftEngulfing.defect] at hz
    linarith
  have hh' := heng u hs.convexOn hC1.continuous x (gradient u x) h hh (hsup x)
    hbdd hAB y hy' (gradient u y) (hsup y) hz'
  change u z < u y + ⟪gradient u y, z - y⟫ + C * h at hh'
  dsimp only [SoftEngulfing.defect]
  linarith

/-- Caffarelli's local C¹,α gain at an actual Lipschitz Alexandrov solution.
No section contraction, Bregman comparison or Hölder bound is supplied as an input. -/
theorem exists_holder_gradient_of_alexandrov_density (hn : 0 < n)
    {u f : E → ℝ} {L : NNReal} (hL : LipschitzWith L u)
    (hs : StrictConvexOn ℝ univ u) (hC1 : ContDiff ℝ 1 u)
    (hf : Continuous f) (hfpos : ∀ x, 0 < f x)
    (hMA : ∀ G : Set E, IsOpen G → volume (subgradientImage u G) =
      ∫⁻ y in G, ENNReal.ofReal (f y))
    {K : Set E} (hK : IsCompact K) :
    ∃ α C : ℝ, 0 < α ∧ α ≤ 1 ∧ 0 ≤ C ∧ ∀ x ∈ K, ∀ y ∈ K,
      ‖gradient u y - gradient u x‖ ≤ C * ‖y - x‖ ^ α := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hdiff := hC1.differentiable one_ne_zero
  have hsup := gradient_support hs.convexOn hdiff
  have hgrad (x : E) : ‖gradient u x‖ ≤ (L : ℝ) := by
    simpa only [gradient, LinearIsometryEquiv.norm_map] using
      (norm_fderiv_le_of_lipschitz (x₀ := x) ℝ hL)
  obtain ⟨R, hR, hKR⟩ := hK.isBounded.exists_pos_norm_le
  let Q : Set E := closedBall (0 : E) (R + 1)
  obtain ⟨a, b, H₀, ha, hb, hH₀, hsections⟩ :=
    exists_uniform_section_density_bounds hs hC1 hf hfpos hMA
      (isCompact_closedBall (0 : E) (R + 1))
  obtain ⟨A, hA, hcomparison⟩ := SoftEngulfing.bregman_comparison_of_sections hn ha hb
  let κ : ℝ := max (2 * A) 1
  have hκ : 1 ≤ κ := le_max_right _ _
  let r : ℝ := min 1 (H₀ / (8 * ((L : ℝ) + 1)))
  have hr : 0 < r := lt_min zero_lt_one (by positivity)
  have hr1 : r ≤ 1 := min_le_left _ _
  have hrH : r ≤ H₀ / (8 * ((L : ℝ) + 1)) := min_le_right _ _
  have hsoft : ∀ x ∈ K, ∀ z : E, ‖z - x‖ ≤ r →
      SoftEngulfing.defect u x z ≤ κ * SoftEngulfing.defect u z x := by
    intro x hx z hz
    have hzQ : z ∈ Q := by
      change dist z 0 ≤ R + 1
      have hdist : dist z x ≤ 1 := by simpa only [dist_eq_norm] using hz.trans hr1
      calc dist z 0 ≤ dist z x + dist x 0 := dist_triangle _ _ _
        _ ≤ R + 1 := by rw [dist_zero_right]; linarith [hKR x hx]
    have hgap0 : 0 ≤ SoftEngulfing.defect u z x := by
      dsimp only [SoftEngulfing.defect]
      linarith [hsup z x]
    have hgap : SoftEngulfing.defect u z x ≤ 2 * (L : ℝ) * ‖z - x‖ := by
      have hu : u x - u z ≤ (L : ℝ) * ‖x - z‖ := by
        have hh := hL.dist_le_mul x z
        rw [dist_eq_norm, dist_eq_norm, Real.norm_eq_abs] at hh
        exact (le_abs_self _).trans hh
      have hi : -⟪gradient u z, x - z⟫ ≤ (L : ℝ) * ‖x - z‖ :=
        (neg_le_abs _).trans ((abs_real_inner_le_norm _ _).trans
          (mul_le_mul_of_nonneg_right (hgrad z) (norm_nonneg _)))
      dsimp only [SoftEngulfing.defect]
      rw [norm_sub_rev x z] at hu hi
      linarith
    have hheight : 2 * SoftEngulfing.defect u z x < H₀ := by
      have hscale : 8 * ((L : ℝ) + 1) * r ≤ H₀ := by
        have hh := (le_div_iff₀ (by positivity : 0 < 8 * ((L : ℝ) + 1))).mp hrH
        nlinarith
      have hL0 : 0 ≤ (L : ℝ) := L.coe_nonneg
      nlinarith [hz]
    have hcomp := hcomparison u hs.convexOn hC1.continuous z (gradient u z) (hsup z)
      x (gradient u x) (hsup x) H₀ hheight
      (fun H hH hHH => hsections z hzQ H (by
        have hh := hsup z x
        dsimp only [SoftEngulfing.defect] at hheight hgap0
        linarith) hHH)
    change SoftEngulfing.defect u x z ≤ 2 * A * SoftEngulfing.defect u z x at hcomp
    exact hcomp.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hgap0)
  obtain ⟨C, hC, hholder⟩ := SoftEngulfing.exists_holder_gradient_of_lipschitz_local_soft
    hs.convexOn hC1 hL hK hr hκ hsoft
  refine ⟨κ⁻¹, C, inv_pos.mpr (lt_of_lt_of_le zero_lt_one hκ), ?_, hC, hholder⟩
  exact inv_le_one_of_one_le₀ hκ
/-- Power-radius inclusion for every small section, with one exponent and coefficient
before all centres in a compact set and all heights. -/
theorem exists_section_power_inclusion_of_alexandrov_density (hn : 0 < n)
    {u f : E → ℝ} {L : NNReal} (hL : LipschitzWith L u)
    (hs : StrictConvexOn ℝ univ u) (hC1 : ContDiff ℝ 1 u)
    (hf : Continuous f) (hfpos : ∀ x, 0 < f x)
    (hMA : ∀ G : Set E, IsOpen G → volume (subgradientImage u G) =
      ∫⁻ y in G, ENNReal.ofReal (f y))
    {K : Set E} (hK : IsCompact K) :
    ∃ α c : ℝ, 0 < α ∧ α ≤ 1 ∧ 0 < c ∧ ∀ x ∈ K, ∀ h : ℝ,
      0 < h → h ≤ 1 → closedBall x (c * h ^ (1 + α)⁻¹) ⊆
        {z | u z ≤ u x + ⟪gradient u x, z - x⟫ + h} := by
  obtain ⟨R, hR, hKR⟩ := hK.isBounded.exists_pos_norm_le
  let Q : Set E := closedBall (0 : E) (R + 1)
  obtain ⟨α, C, hα, hα1, hC, hHolder⟩ := exists_holder_gradient_of_alexandrov_density
    hn hL hs hC1 hf hfpos hMA (isCompact_closedBall (0 : E) (R + 1))
  let c : ℝ := (C + 1)⁻¹
  have hCp : 0 < C + 1 := by linarith
  have hc : 0 < c := inv_pos.mpr hCp
  have hc1 : c ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  have hq : 0 < 1 + α := by linarith
  have hCc : C * c ≤ 1 := by
    dsimp only [c]
    rw [← div_eq_mul_inv, div_le_one hCp]
    linarith
  refine ⟨α, c, hα, hα1, hc, fun x hx h hh hh1 z hz => ?_⟩
  have hhp : h ^ (1 + α)⁻¹ ≤ 1 :=
    Real.rpow_le_one hh.le hh1 (inv_nonneg.mpr hq.le)
  have hzdist : ‖z - x‖ ≤ c * h ^ (1 + α)⁻¹ := by
    simpa only [mem_closedBall, dist_eq_norm] using hz
  have hz1 : ‖z - x‖ ≤ 1 := hzdist.trans ((mul_le_of_le_one_right hc.le hhp).trans hc1)
  have hxQ : x ∈ Q := by
    change dist x 0 ≤ R + 1
    rw [dist_zero_right]
    linarith [hKR x hx]
  have hzQ : z ∈ Q := by
    change dist z 0 ≤ R + 1
    calc dist z 0 ≤ dist z x + dist x 0 := dist_triangle _ _ _
      _ ≤ R + 1 := by rw [dist_eq_norm, dist_zero_right]; linarith [hKR x hx]
  have hsup := gradient_support hs.convexOn (hC1.differentiable one_ne_zero) z x
  have hg : ‖gradient u z - gradient u x‖ ≤ C * ‖z - x‖ ^ α := hHolder x hxQ z hzQ
  have hgap : u z - u x - ⟪gradient u x, z - x⟫ ≤ C * ‖z - x‖ ^ (1 + α) := by
    have hi := real_inner_le_norm (gradient u z - gradient u x) (z - x)
    have hmul := mul_le_mul_of_nonneg_right hg (norm_nonneg (z - x))
    have hp : ‖z - x‖ ^ (1 + α) = ‖z - x‖ ^ α * ‖z - x‖ := by
      rw [add_comm, Real.rpow_add' (norm_nonneg _) (by linarith : α + 1 ≠ 0), Real.rpow_one]
    rw [show x - z = -(z - x) by abel, inner_neg_right] at hsup
    rw [inner_sub_left] at hi
    rw [hp]
    nlinarith
  have hpower : (c * h ^ (1 + α)⁻¹) ^ (1 + α) = c ^ (1 + α) * h := by
    rw [Real.mul_rpow hc.le (Real.rpow_nonneg hh.le _), ← Real.rpow_mul hh.le,
      inv_mul_cancel₀ hq.ne', Real.rpow_one]
  have hcp : c ^ (1 + α) ≤ c := by
    have hp := Real.rpow_le_rpow_of_exponent_ge hc hc1 (show (1 : ℝ) ≤ 1 + α by linarith)
    simpa only [Real.rpow_one] using hp
  have hupper : C * ‖z - x‖ ^ (1 + α) ≤ h := by
    calc C * ‖z - x‖ ^ (1 + α) ≤ C * (c * h ^ (1 + α)⁻¹) ^ (1 + α) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) hzdist hq.le) hC
      _ = C * (c ^ (1 + α) * h) := by rw [hpower]
      _ ≤ C * (c * h) := by gcongr
      _ = (C * c) * h := by ring
      _ ≤ h := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hCc hh.le
  change u z ≤ u x + ⟪gradient u x, z - x⟫ + h
  linarith

end ClosedHolder
end FunctionalInequalities.Analysis
