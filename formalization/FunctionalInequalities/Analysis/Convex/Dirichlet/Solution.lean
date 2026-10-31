module

public import FunctionalInequalities.Analysis.Convex.Caffarelli.DomainContact
public import FunctionalInequalities.Analysis.Convex.Dirichlet.Regularization

/-!
# Unit Monge–Ampère solutions on bounded convex domains

Supporting interfaces for Letwin arXiv:2607.24164v1 Lemma 2.2 through
Berman–Berndtsson arXiv:1207.6128v1 Theorem 2.24(ii). Each declaration retains
its own hypotheses and scope; this layout does not assert further regularity.
-/

@[expose] public section

noncomputable section

open Set Metric Filter
open scoped RealInnerProductSpace Topology
open FunctionalInequalities.Probability.Stein

namespace FunctionalInequalities.Analysis.Dirichlet
open Set Metric Filter MeasureTheory
open scoped RealInnerProductSpace ENNReal Topology

private lemma local_upper_from_actual_family {n : ℕ} {U V : EuclideanSpace ℝ (Fin n) → ℝ}
    {Ω : Set (EuclideanSpace ℝ (Fin n))} (hcΩ : Convex ℝ Ω)
    (hU : U ∈ FunctionalInequalities.Analysis.Dirichlet.subsolutions Ω)
    {c : EuclideanSpace ℝ (Fin n)} {R : ℝ} (hR : 0 < R) (hball : closedBall c R ⊆ Ω)
    (L : NNReal)
    (hreg :
      ∀ ε : ℝ,
        0 < ε →
          ε * ((L : ℝ) + 1) < R / 2 →
            ConvexOn ℝ univ (moreauEnvelope V ε) ∧
              ContDiff ℝ 1 (moreauEnvelope V ε) ∧
                ∀ G : Set (EuclideanSpace ℝ (Fin n)),
                  IsOpen G →
                    G ⊆ ball c (R / 2) →
                      volume (subgradientImageOn (moreauEnvelope V ε) (ball c (R / 2)) G) ≤
                        volume G)
    (hunif :
      TendstoUniformlyOn (fun ε : ℝ => moreauEnvelope V ε) U (𝓝[>] (0 : ℝ)) (closedBall c R)) :
    ∀ G : Set (EuclideanSpace ℝ (Fin n)),
      IsOpen G → G ⊆ ball c (R / 2) → volume (subgradientImageOn U Ω G) ≤ volume G := by
  let a : ℝ := R / (4 * ((L : ℝ) + 1))
  let ε : ℕ → ℝ := fun j => a * (1 / ((j : ℝ) + 1))
  have ha : 0 < a := by dsimp [a]; positivity
  have hε (j : ℕ) : 0 < ε j := by dsimp [ε]; positivity
  have hsmall (j : ℕ) : ε j * ((L : ℝ) + 1) < R / 2 := by
    have hj : 0 < (j : ℝ) + 1 := by positivity
    have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    have hr : (1 : ℝ) / ((j : ℝ) + 1) ≤ 1 := (div_le_one hj).mpr (by linarith)
    have he : ε j * ((L : ℝ) + 1) = R / 4 * (1 / ((j : ℝ) + 1)) := by
      dsimp [ε, a]
      field_simp
    rw [he]
    nlinarith
  have he0 : Tendsto ε atTop (𝓝 (0 : ℝ)) := by
    have h : Tendsto (fun j : ℕ => a * (1 / ((j : ℝ) + 1))) atTop (𝓝 (a * 0)) :=
      tendsto_const_nhds.mul tendsto_one_div_add_atTop_nhds_zero_nat
    simpa [ε] using h
  have heps : Tendsto ε atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨he0, Filter.Eventually.of_forall hε⟩
  have hTK : ball c (R / 2) ⊆ closedBall c R := by
    intro y hy
    exact mem_closedBall.mpr (le_trans (mem_ball.mp hy).le (by linarith))
  have hTD : ball c (R / 2) ⊆ Ω := hTK.trans hball
  have hlim :
    TendstoUniformlyOn (fun j : ℕ => moreauEnvelope V (ε j)) U atTop (ball c (R / 2)) := by
    intro W hW
    exact heps.eventually ((hunif.mono hTK) W hW)
  intro G hG hGT
  rw [←
    subgradientImageOn_eq_of_isOpen_subset (hU.1.subset subset_closure hcΩ) isOpen_ball hTD hGT]
  have hlow :=
    volume_subgradientImageOn_le_liminf_of_locally_uniform isOpen_ball
      (fun j => (hreg (ε j) (hε j) (hsmall j)).1.subset (subset_univ _) (convex_ball _ _))
      (fun j => (hreg (ε j) (hε j) (hsmall j)).2.1.continuous.continuousOn)
      (hU.1.subset (hTD.trans subset_closure) (convex_ball _ _))
      (hU.2.1.mono (hTD.trans subset_closure)) hlim.tendstoLocallyUniformlyOn hG hGT
  exact
    hlow.trans
      (liminf_le_of_frequently_le'
        (Filter.Eventually.of_forall
            (fun j => (hreg (ε j) (hε j) (hsmall j)).2.2 G hG hGT)).frequently)

/-- The SAME domain-generated envelope and regularization data have genuine
DOMAIN MA upper bounds on every open subset of each actual half-buffer.
The positive parameter sequence, uniform limit and support localization are
produced; no image/MA agreement or unknown-U regularity is assumed. -/
theorem exists_envelope_buffered_local_ma_upper {n : ℕ} (hn : 0<n)
    {Ω : Set (EuclideanSpace ℝ (Fin n))} (hΩ : IsOpen Ω) (hcΩ : Convex ℝ Ω)
    (hb : Bornology.IsBounded Ω) :
    ∃ (U : EuclideanSpace ℝ (Fin n)→ℝ) (f : ℕ→EuclideanSpace ℝ (Fin n)→ℝ),
      (∀ x∈closure Ω, U x=sSup ((fun w => w x) '' subsolutions Ω)) ∧
      U∈subsolutions Ω ∧ (∀ z∈frontier Ω, U z=0) ∧
      (∀ w∈subsolutions Ω, ∀ x∈closure Ω, w x≤U x) ∧
      (∀ j, f j∈subsolutions Ω) ∧
      (∀ j, ∀ x∈closure Ω, f j x≤U x ∧ |f j x-U x|<1 / ((j:ℝ) + 1)) ∧
      (∀ x, Monotone (fun j => f j x)) ∧
      TendstoUniformlyOn f U atTop (closure Ω) ∧
      (∀ (q : EuclideanSpace ℝ (Fin n)→ℝ), ConvexOn ℝ Ω q→ ContinuousOn q (closure Ω)→
        (∀ G, IsOpen G→G⊆Ω→volume G≤volume (subgradientImageOn q Ω G))→
        ∀ (c : EuclideanSpace ℝ (Fin n)) (r : ℝ), 0<r→closedBall c r⊆Ω→
          (∀ z∈sphere c r, q z≤U z)→∀ x∈ball c r, q x≤U x) ∧
      (∀ (A : Matrix (Fin n) (Fin n) ℝ), A.PosDef→∀ x∈Ω, ∀ b,
        (∀ᶠ y in 𝓝 x, quadraticAt A x b (U x) y≤U y)→A.det≤1) ∧
      (∀ (ψ : EuclideanSpace ℝ (Fin n)→ℝ), ∀ x∈Ω,
        ContDiffAt ℝ 2 ψ x→(hessianMatrix ψ x).PosSemidef→U x=ψ x→
        (∀ᶠ y in 𝓝 x, ψ y≤U y)→(hessianMatrix ψ x).det≤1) ∧
      (∀ (c : EuclideanSpace ℝ (Fin n)) (R : ℝ), 0<R→closedBall c R⊆Ω→
        ∃ (V : EuclideanSpace ℝ (Fin n)→ℝ) (L : NNReal),
          ConvexOn ℝ univ V ∧ LipschitzWith L V ∧ (∀ y∈closedBall c R, V y=U y) ∧
          (∀ ε : ℝ, 0<ε→ε * ((L:ℝ) + 1)<R / 2→
            ConvexOn ℝ univ (moreauEnvelope V ε) ∧ ContDiff ℝ 1 (moreauEnvelope V ε) ∧
            LipschitzWith (‖(ε⁻¹:ℝ)‖₊*2) (gradient (moreauEnvelope V ε)) ∧
            (∀ (A : Matrix (Fin n) (Fin n) ℝ), A.PosDef→∀ x∈ball c (R / 2), ∀ b,
              (∀ᶠ z in 𝓝 x, quadraticAt A x b (moreauEnvelope V ε x) z≤ moreauEnvelope V ε
                z)→A.det≤1) ∧
            (∀ᵐ x ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (ball c (R / 2))),
              ∃ A : Matrix (Fin n) (Fin n) ℝ, A.IsHermitian ∧
                HasFDerivAt (gradient (moreauEnvelope V ε))
                  (Matrix.toEuclideanLin A).toContinuousLinearMap x ∧
                A.PosSemidef ∧ A.det≤1 ∧
                ∀ t>0, ∀ᶠ y in 𝓝 x,
                  |moreauEnvelope V ε y-quadraticAt A x (gradient (moreauEnvelope V ε) x)
                    (moreauEnvelope V ε x) y|≤t*‖y-x‖^2) ∧
            (∀ Γ : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet Γ→Γ⊆ball c (R / 2)→
              volume ((gradient (moreauEnvelope V ε)) '' Γ)≤volume Γ ∧
              volume (subgradientImageOn (moreauEnvelope V ε) (ball c (R / 2)) Γ)≤volume Γ)) ∧
          TendstoUniformlyOn (fun ε : ℝ => moreauEnvelope V ε) U (𝓝[>] (0:ℝ)) (closedBall c R) ∧
          (∀ G : Set (EuclideanSpace ℝ (Fin n)), IsOpen G→G⊆ball c (R / 2)→
            volume (subgradientImageOn U Ω G)≤volume G)) := by
    obtain ⟨U, f, hs, hU, hz, hd, hf, he, hm, hu, hcomp, hquad, hc2, hbuf⟩ :=
      exists_envelope_buffered_moreau_image_upper hn hΩ hcΩ hb
    refine ⟨U, f, hs, hU, hz, hd, hf, he, hm, hu, hcomp, hquad, hc2, ?_⟩
    intro c R hR hball
    obtain ⟨V, L, hV, hL, heq, hreg, hunif⟩ := hbuf c R hR hball
    refine ⟨V, L, hV, hL, heq, hreg, hunif, ?_⟩
    apply local_upper_from_actual_family hcΩ hU hR hball L ?_ hunif
    intro ε hε hsmall
    obtain ⟨hcv, hC, _, _, _, himage⟩ := hreg ε hε hsmall
    refine ⟨hcv, hC, ?_⟩
    intro G hG hGT
    exact (himage G hG.measurableSet hGT).2

/-- A bounded open convex domain in positive dimension generates an actual
C0 convex zero-boundary unit-density DOMAIN Dirichlet solution. The SAME measure
retains every Borel supporting-image formula and local compact finiteness, then
is identified with restricted volume. No solution, measure, equation, stability
or regularity is a source premise; interior strictness/C2/PD remain separate. -/
theorem exists_unit_solution {n : ℕ} (hn : 0 < n) {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (hΩ : IsOpen Ω) (hcΩ : Convex ℝ Ω) (hb : Bornology.IsBounded Ω) :
    ∃ (U : EuclideanSpace ℝ (Fin n) → ℝ) (μ : Measure (EuclideanSpace ℝ (Fin n))),
      U ∈ subsolutions Ω ∧
        ConvexOn ℝ (closure Ω) U ∧
          ContinuousOn U (closure Ω) ∧
            (∀ z ∈ frontier Ω, U z = 0) ∧
              (∀ G : Set (EuclideanSpace ℝ (Fin n)),
                  MeasurableSet G → μ G = volume (subgradientImageOn U Ω (G ∩ Ω))) ∧
                (∀ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K → K ⊆ Ω → μ K < ⊤) ∧
                  μ = volume.restrict Ω ∧
                    (∀ G : Set (EuclideanSpace ℝ (Fin n)),
                      IsOpen G → G ⊆ Ω → volume (subgradientImageOn U Ω G) = volume G) := by
  obtain ⟨U, f, _, hU, hz, _, _, _, _, _, _, _, _, hbuf⟩ :=
    exists_envelope_buffered_local_ma_upper hn hΩ hcΩ hb
  have hcv : ConvexOn ℝ Ω U := hU.1.subset subset_closure hcΩ
  have hC : ContinuousOn U Ω := hU.2.1.mono subset_closure
  obtain ⟨μ, hμ, hfin⟩ := exists_domain_mongeAmpere_measure hΩ hcv hC
  have hlocal :
    ∀ (c : EuclideanSpace ℝ (Fin n)) (R : ℝ),
      0 < R →
        closedBall c R ⊆ Ω → μ.restrict (ball c (R / 2)) = volume.restrict (ball c (R / 2)) := by
    intro c R hR hball
    obtain ⟨V, L, _, _, _, _, _, hupper⟩ := hbuf c R hR hball
    have hTK : ball c (R / 2) ⊆ closedBall c R := by
      intro x hx
      exact mem_closedBall.mpr (le_trans (mem_ball.mp hx).le (by linarith))
    have hTΩ : ball c (R / 2) ⊆ Ω := hTK.trans hball
    have hTfin : μ (ball c (R / 2)) < ⊤ :=
      (measure_mono hTK).trans_lt (hfin (closedBall c R) (isCompact_closedBall c R) hball)
    let : IsFiniteMeasure (μ.restrict (ball c (R / 2))) := isFiniteMeasure_restrict.mpr hTfin.ne
    let :
      IsFiniteMeasure
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict (ball c (R / 2))) :=
      isFiniteMeasure_restrict.mpr Metric.isBounded_ball.measure_lt_top.ne
    apply Measure.OuterRegular.ext_isOpen
    intro O hO
    rw [Measure.restrict_apply hO.measurableSet, Measure.restrict_apply hO.measurableSet]
    have hOTΩ : O ∩ ball c (R / 2) ⊆ Ω := inter_subset_right.trans hTΩ
    rw [hμ _ (hO.inter isOpen_ball).measurableSet, inter_eq_left.mpr hOTΩ]
    exact
      le_antisymm (hupper _ (hO.inter isOpen_ball) inter_subset_right)
        (hU.2.2.2 _ (hO.inter isOpen_ball) hOTΩ)
  obtain ⟨R, s, hR, hfull, hs, hcover⟩ := exists_countable_buffered_ball_cover hΩ
  have hhalf (x : Ω) : ball (x : EuclideanSpace ℝ (Fin n)) (R x / 2) ⊆ Ω := by
    intro y hy
    apply hfull x
    exact mem_closedBall.mpr (le_trans (mem_ball.mp hy).le (by linarith [hR x]))
  have heq : (⋃ x ∈ s, ball (x : EuclideanSpace ℝ (Fin n)) (R x / 2)) = Ω :=
    Subset.antisymm (iUnion₂_subset (fun x _ => hhalf x)) hcover
  have hres :
    μ.restrict (⋃ x ∈ s, ball (x : EuclideanSpace ℝ (Fin n)) (R x / 2)) =
      volume.restrict (⋃ x ∈ s, ball (x : EuclideanSpace ℝ (Fin n)) (R x / 2)) :=
    (Measure.restrict_biUnion_congr hs).mpr (fun x _ => hlocal x (R x) (hR x) (hfull x))
  rw [heq] at hres
  have hμΩ : μ.restrict Ω = μ := by
    ext A hA
    rw [Measure.restrict_apply hA, hμ _ (hA.inter hΩ.measurableSet), hμ A hA]
    simp only [inter_assoc, inter_self]
  rw [hμΩ] at hres
  refine ⟨U, μ, hU, hU.1, hU.2.1, hz, hμ, hfin, hres, ?_⟩
  intro G hG hGΩ
  have hformula := hμ G hG.measurableSet
  rw [inter_eq_left.mpr hGΩ] at hformula
  rw [← hformula, hres, Measure.restrict_apply hG.measurableSet, inter_eq_left.mpr hGΩ]

end FunctionalInequalities.Analysis.Dirichlet

namespace FunctionalInequalities.Analysis.Dirichlet
open Set Metric Filter MeasureTheory
open scoped RealInnerProductSpace ENNReal Topology

/-- The SAME actual domain-generated UNIT solution is strictly negative at every
interior point. Actual boundary maximum, strong-maximum rigidity and the true
UNIT equation produce the sign. Negativity is not strict convexity or C1/C2. -/
theorem exists_unit_solution_neg {n : ℕ} (hn : 0 < n) {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (hΩ : IsOpen Ω) (hcΩ : Convex ℝ Ω) (hb : Bornology.IsBounded Ω) :
    ∃ (U : EuclideanSpace ℝ (Fin n) → ℝ) (μ : Measure (EuclideanSpace ℝ (Fin n))),
      U ∈ subsolutions Ω ∧
        ConvexOn ℝ (closure Ω) U ∧
          ContinuousOn U (closure Ω) ∧
            (∀ z ∈ frontier Ω, U z = 0) ∧
              (∀ G : Set (EuclideanSpace ℝ (Fin n)),
                  MeasurableSet G → μ G = volume (subgradientImageOn U Ω (G ∩ Ω))) ∧
                (∀ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K → K ⊆ Ω → μ K < ⊤) ∧
                  μ = volume.restrict Ω ∧
                    (∀ G : Set (EuclideanSpace ℝ (Fin n)),
                        IsOpen G → G ⊆ Ω → volume (subgradientImageOn U Ω G) = volume G) ∧
                      (∀ x ∈ Ω, U x < 0) := by
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨U, μ, hU, hcv, hC, hz, hμ, hfin, hm, hMA⟩ := exists_unit_solution hn hΩ hcΩ hb
  refine ⟨U, μ, hU, hcv, hC, hz, hμ, hfin, hm, hMA, ?_⟩
  have hnonpos : ∀ x ∈ closure Ω, U x ≤ 0 :=
    le_on_closure_of_le_frontier_of_convexOn hΩ hcΩ hb hcv hC (fun z h => le_of_eq (hz z h))
  intro x hx
  by_contra hnlt
  have hux : U x = 0 := le_antisymm (hnonpos x (subset_closure hx)) (le_of_not_gt hnlt)
  have hmax : IsMaxOn U (closure Ω) x := by
    intro y hy
    rw [hux]
    exact hnonpos y hy
  have hall := eq_on_of_interior_max_of_convexOn hcv hΩ subset_closure hx hmax
  have hu0 : ∀ y ∈ closure Ω, U y = 0 := by
    intro y hy
    rw [hall y hy, hux]
  have himg : subgradientImageOn U Ω Ω ⊆ {0} := by
    rintro p ⟨z, hzΩ, hp⟩
    apply subgradientImageOn_const_subset_singleton (0 : ℝ) hΩ (subset_refl Ω)
    refine ⟨z, hzΩ, ?_⟩
    intro y hyΩ
    have h := hp y hyΩ
    simpa only [hu0 z (subset_closure hzΩ), hu0 y (subset_closure hyΩ), zero_add] using h
  have himg0 : volume (subgradientImageOn U Ω Ω) = 0 :=
    measure_mono_null himg (measure_singleton (0 : EuclideanSpace ℝ (Fin n)))
  have hvol0 : volume Ω = 0 := by
    rw [← hMA Ω hΩ (subset_refl Ω)]
    exact himg0
  exact (ne_of_gt (hΩ.measure_pos volume ⟨x, hx⟩)) hvol0

end FunctionalInequalities.Analysis.Dirichlet

namespace FunctionalInequalities.Analysis.Dirichlet
open Set Metric Filter MeasureTheory
open scoped RealInnerProductSpace Topology

/-- The actual zero-boundary UNIT DOMAIN solution is generated strictly convex
INSIDE the domain. Only domain geometry is supplied; the SAME potential and
measure retain every prior field, including actual interior contact uniqueness. -/
theorem exists_strict_unit_solution {n : ℕ} (hn : 0 < n) {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (hΩ : IsOpen Ω) (hcΩ : Convex ℝ Ω) (hb : Bornology.IsBounded Ω) :
    ∃ (U : EuclideanSpace ℝ (Fin n) → ℝ) (μ : Measure (EuclideanSpace ℝ (Fin n))),
      U ∈ Dirichlet.subsolutions Ω ∧
        ConvexOn ℝ (closure Ω) U ∧
          ContinuousOn U (closure Ω) ∧
            (∀ z ∈ frontier Ω, U z = 0) ∧
              (∀ G : Set (EuclideanSpace ℝ (Fin n)),
                  MeasurableSet G → μ G = volume (subgradientImageOn U Ω (G ∩ Ω))) ∧
                (∀ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K → K ⊆ Ω → μ K < ⊤) ∧
                  μ = volume.restrict Ω ∧
                    (∀ G : Set (EuclideanSpace ℝ (Fin n)),
                        IsOpen G → G ⊆ Ω → volume (subgradientImageOn U Ω G) = volume G) ∧
                      (∀ x ∈ Ω, U x < 0) ∧
                        (∀ x ∈ Ω,
                            ∀ p : EuclideanSpace ℝ (Fin n),
                              (∀ z ∈ Ω, U x + ⟪p, z - x⟫ ≤ U z) →
                                ∀ y ∈ Ω, U y = U x + ⟪p, y - x⟫ → y = x) ∧
                          StrictConvexOn ℝ Ω U := by
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨U, μ, hU, hcv, hC, hz, hμ, hfin, hm, hMA, hneg⟩ :=
    exists_unit_solution_neg hn hΩ hcΩ hb
  have hcontact :
    ∀ x ∈ Ω,
      ∀ p : EuclideanSpace ℝ (Fin n),
        (∀ z ∈ Ω, U x + ⟪p, z - x⟫ ≤ U z) → ∀ y ∈ Ω, U y = U x + ⟪p, y - x⟫ → y = x := by
    intro x hx p hp y hy hxy
    exact eq_of_domain_unit_contact hΩ hcΩ hb hcv hC hz hneg hMA hx hy hp hxy
  have hstrict :=
    strictConvexOn_of_domain_contact_eq hΩ (hcv.subset subset_closure hcΩ)
      (hC.mono subset_closure) hcontact
  exact ⟨U, μ, hU, hcv, hC, hz, hμ, hfin, hm, hMA, hneg, hcontact, hstrict⟩

end FunctionalInequalities.Analysis.Dirichlet
