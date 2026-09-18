import FunctionalInequalities.Analysis.Sard.Smooth

/-! # The `C^k` graph chart of a regular zero set

The finite-regularity counterpart of the `C^∞` chart `Analysis.exists_local_graph`.
-/

noncomputable section

open Set Metric Filter Topology
open scoped ContDiff

namespace FunctionalInequalities.Analysis.MorseSard

variable {n : ℕ}

/-- Dropping one coordinate does not increase the sup norm. -/
theorem norm_sub_le_insertNth (i : Fin (n + 1)) (θ : (Fin n → ℝ) → ℝ) (a b : Fin n → ℝ) :
    ‖a - b‖ ≤ ‖Fin.insertNth (α := fun _ => ℝ) i (θ a) a
      - Fin.insertNth (α := fun _ => ℝ) i (θ b) b‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun j => ?_
  have := norm_le_pi_norm (Fin.insertNth (α := fun _ => ℝ) i (θ a) a
      - Fin.insertNth (α := fun _ => ℝ) i (θ b) b) (i.succAbove j)
  simpa using this

/-- The graph map of a `C^k` function is `C^k`. -/
theorem contDiff_insertNth {k : ℕ} {θ : (Fin n → ℝ) → ℝ} (i : Fin (n + 1))
    (hθ : ContDiff ℝ k θ) :
    ContDiff ℝ k (fun y : Fin n → ℝ => Fin.insertNth (α := fun _ => ℝ) i (θ y) y) := by
  rw [contDiff_pi]
  intro m
  rcases eq_or_ne m i with rfl | hm
  · simpa using hθ
  · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hm
    simpa using contDiff_apply ℝ ℝ j

/-- Graph maps are injective. -/
theorem injective_insertNth (i : Fin (n + 1)) (θ : (Fin n → ℝ) → ℝ) :
    Function.Injective (fun y : Fin n → ℝ => Fin.insertNth (α := fun _ => ℝ) i (θ y) y) := by
  intro a b hab
  have := congrArg (Fin.removeNth (α := fun _ => ℝ) i) hab
  simpa using this

section Extension

/-- A function of finite differentiability class on an open set agrees near any of its points
with a globally `C^k` function.  The `C^∞` statement is `Analysis.exists_contDiff_eventuallyEq`;
the proof is the same bump multiplication. -/
theorem exists_contDiff_eventuallyEq_nat {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {m : ℕ}
    {f : E → F} {O : Set E} {z : E} (hO : IsOpen O) (hf : ContDiffOn ℝ m f O) (hz : z ∈ O) :
    ∃ g : E → F, ContDiff ℝ m g ∧ g =ᶠ[𝓝 z] f := by
  classical
  obtain ⟨r, hr, hrO⟩ := Metric.isOpen_iff.mp hO z hz
  set χ : ContDiffBump z := ⟨r / 3, r / 2, by positivity, by linarith⟩ with hχ
  have htsupp : tsupport (χ : E → ℝ) ⊆ O := by
    rw [χ.tsupport_eq]
    exact fun y hy => hrO (by
      simp only [mem_closedBall] at hy
      simpa [mem_ball] using hy.trans_lt (by simp [hχ]; linarith))
  refine ⟨fun y => if y ∈ O then (χ y) • f y else 0, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : y ∈ O
    · refine ContDiffAt.congr_of_eventuallyEq
        (χ.contDiff.contDiffAt.smul (hf.contDiffAt (hO.mem_nhds hy))) ?_
      filter_upwards [hO.mem_nhds hy] with y' hy'
      simp [hy']
    · have hyt : y ∈ (tsupport (χ : E → ℝ))ᶜ := fun hc => hy (htsupp hc)
      refine ContDiffAt.congr_of_eventuallyEq (contDiffAt_const (c := (0 : F))) ?_
      filter_upwards [(isClosed_tsupport (χ : E → ℝ)).isOpen_compl.mem_nhds hyt] with y' hy'
      have hzero : χ y' = 0 := image_eq_zero_of_notMem_tsupport hy'
      by_cases hy'O : y' ∈ O <;> simp [hy'O, hzero]
  · filter_upwards [Metric.ball_mem_nhds z (by positivity : (0:ℝ) < r / 3)] with y hy
    have hyO : y ∈ O := hrO (by simpa [mem_ball] using (mem_ball.mp hy).trans (by linarith))
    have hone : χ y = 1 := χ.one_of_mem_closedBall (by
      simpa [mem_closedBall, hχ] using (mem_ball.mp hy).le)
    simp [hyO, hone]

end Extension

section Straighten

/-- A nonzero functional on a finite product of lines is nonzero on a basis vector. -/
private lemma exists_single_ne_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : (ι → ℝ) →L[ℝ] ℝ} (hα : α ≠ 0) : ∃ i : ι, α (Pi.single i (1 : ℝ)) ≠ 0 := by
  by_contra h
  push Not at h
  refine hα (ContinuousLinearMap.ext fun v => ?_)
  have hv : v = ∑ i : ι, v i • Pi.single i (1 : ℝ) := by
    funext k
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hv]
  simp [map_sum, h]

/-- Replacing the `i`-th coordinate by `w` keeps the differentiability class. -/
private lemma contDiff_update {k : ℕ} (i : Fin (n + 1)) {w : (Fin (n + 1) → ℝ) → ℝ}
    (hw : ContDiff ℝ k w) : ContDiff ℝ k (fun x => Function.update x i (w x)) := by
  rw [contDiff_pi]
  intro m
  rcases eq_or_ne m i with rfl | hm
  · simpa using hw
  · simpa [Function.update_apply, hm] using contDiff_apply ℝ ℝ m

/-- The differential of that chart. -/
private lemma hasFDerivAt_update (i : Fin (n + 1)) {w : (Fin (n + 1) → ℝ) → ℝ}
    (hw : Differentiable ℝ w) (x : Fin (n + 1) → ℝ) :
    HasFDerivAt (fun x => Function.update x i (w x))
      (ContinuousLinearMap.pi fun m => if m = i then fderiv ℝ w x
        else ContinuousLinearMap.proj m) x := by
  refine hasFDerivAt_pi'' fun m => ?_
  rw [ContinuousLinearMap.proj_pi]
  rcases eq_or_ne m i with rfl | hm
  · simpa using (hw x).hasFDerivAt
  · simpa [Function.update_apply, hm] using hasFDerivAt_apply (𝕜 := ℝ) m x

/-- That differential is injective as soon as `w` really depends on the `i`-th coordinate. -/
private lemma injective_updateDeriv (i : Fin (n + 1)) {α : (Fin (n + 1) → ℝ) →L[ℝ] ℝ}
    (hα : α (Pi.single i (1 : ℝ)) ≠ 0) :
    Function.Injective (ContinuousLinearMap.pi fun m : Fin (n + 1) =>
      if m = i then α else ContinuousLinearMap.proj m) := by
  intro v₁ v₂ hv
  rw [← sub_eq_zero]
  set v : Fin (n + 1) → ℝ := v₁ - v₂ with hvdef
  have h0 : (ContinuousLinearMap.pi fun m : Fin (n + 1) =>
      if m = i then α else ContinuousLinearMap.proj m) v = 0 := by
    rw [hvdef, map_sub, hv, sub_self]
  have hoff : ∀ m, m ≠ i → v m = 0 := by
    intro m hm
    have := congrFun h0 m
    simpa [ContinuousLinearMap.pi_apply, hm] using this
  have hsingle : v = v i • Pi.single i (1 : ℝ) := by
    funext m
    rcases eq_or_ne m i with rfl | hm
    · simp
    · simp [hoff m hm, hm]
  have hαv : α v = 0 := by
    have := congrFun h0 i
    simpa [ContinuousLinearMap.pi_apply] using this
  rw [hsingle, map_smul, smul_eq_mul] at hαv
  have hvi : v i = 0 := by
    rcases mul_eq_zero.mp hαv with h | h
    · exact h
    · exact absurd h hα
  rw [hsingle, hvi, zero_smul]

/-- The straightening differential is a linear equivalence wherever `w` really depends on the
`i`-th coordinate. -/
private lemma exists_updateEquiv (i : Fin (n + 1)) {α : (Fin (n + 1) → ℝ) →L[ℝ] ℝ}
    (hα : α (Pi.single i (1 : ℝ)) ≠ 0) :
    ∃ Le : (Fin (n + 1) → ℝ) ≃L[ℝ] (Fin (n + 1) → ℝ),
      (Le : (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ)) =
        ContinuousLinearMap.pi fun m : Fin (n + 1) =>
          if m = i then α else ContinuousLinearMap.proj m := by
  refine ⟨(LinearEquiv.ofInjectiveEndo _ (injective_updateDeriv i hα)).toContinuousLinearEquiv, ?_⟩
  ext v m
  rfl

end Straighten

/-- **The `C^k` graph chart of a regular zero set.**  Near a regular zero `x₀` of a `C^k`
function `w` with `1 ≤ k`, every zero of `w` is the graph point of a globally `C^k` function `θ`
of the remaining `n` coordinates.  The chart is the `C^k` inverse function theorem
`ContDiffAt.to_localInverse` applied to the map replacing the `i`-th coordinate by `w`, exactly
as in the `C^∞` statement `Analysis.exists_local_graph`; no manifold framework. -/
theorem exists_graph {k : ℕ} (hk : 1 ≤ k) {w : (Fin (n + 1) → ℝ) → ℝ}
    {x₀ : Fin (n + 1) → ℝ} (hw : ContDiff ℝ k w) (hx₀ : w x₀ = 0) (hd : fderiv ℝ w x₀ ≠ 0) :
    ∃ (i : Fin (n + 1)) (θ : (Fin n → ℝ) → ℝ), ContDiff ℝ k θ ∧
      ∀ᶠ x in 𝓝 x₀, w x = 0 →
        x = Fin.insertNth (α := fun _ => ℝ) i (θ (Fin.removeNth i x)) (Fin.removeNth i x) := by
  classical
  obtain ⟨i, hi⟩ := exists_single_ne_zero hd
  have hkne : ((k : ℕ) : WithTop ℕ∞) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    omega
  have hdiff : Differentiable ℝ w := hw.differentiable hkne
  obtain ⟨Le, hLecoe⟩ := exists_updateEquiv i hi
  have hΦc : ContDiffAt ℝ k (fun x => Function.update x i (w x)) x₀ :=
    (contDiff_update i hw).contDiffAt
  have hΦd : HasFDerivAt (fun x => Function.update x i (w x))
      (Le : (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ)) x₀ := by
    rw [hLecoe]
    exact hasFDerivAt_update i hdiff x₀
  set ψ : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) := hΦc.localInverse hΦd hkne with hψdef
  have hψc : ContDiffAt ℝ k ψ (Function.update x₀ i (w x₀)) := hΦc.to_localInverse hΦd hkne
  have hleft : ∀ᶠ x in 𝓝 x₀, ψ (Function.update x i (w x)) = x :=
    (hΦc.hasStrictFDerivAt' hΦd hkne).eventually_left_inverse
  -- the zero set is straightened onto the `i`-th coordinate hyperplane
  have hkey : ∀ x : Fin (n + 1) → ℝ, w x = 0 →
      Function.update x i (w x)
        = Fin.insertNth (α := fun _ => ℝ) i (0 : ℝ) (Fin.removeNth i x) := by
    intro x hx
    funext m
    rcases eq_or_ne m i with rfl | hm
    · simp [hx]
    · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hm
      simp [Fin.succAbove_ne i j, Fin.removeNth]
  set emb : (Fin n → ℝ) → (Fin (n + 1) → ℝ) :=
    fun y => Fin.insertNth (α := fun _ => ℝ) i (0 : ℝ) y with hembdef
  have hembc : ContDiff ℝ k emb := contDiff_insertNth (θ := fun _ => (0 : ℝ)) i contDiff_const
  have hembx₀ : emb (Fin.removeNth i x₀) = Function.update x₀ i (w x₀) := (hkey x₀ hx₀).symm
  have hθ₀ : ContDiffAt ℝ k (fun y : Fin n → ℝ => ψ (emb y) i) (Fin.removeNth i x₀) := by
    have hcomp : ContDiffAt ℝ k (fun y : Fin n → ℝ => ψ (emb y)) (Fin.removeNth i x₀) := by
      refine ContDiffAt.comp _ ?_ hembc.contDiffAt
      rw [hembx₀]
      exact hψc
    exact (contDiff_apply ℝ ℝ i).contDiffAt.comp _ hcomp
  obtain ⟨u, hu, hθ₀u⟩ := hθ₀.contDiffOn (m := (k : ℕ)) le_rfl (by simp)
  obtain ⟨O, hOu, hOopen, hOmem⟩ := _root_.mem_nhds_iff.mp hu
  obtain ⟨θ, hθc, hθeq⟩ :=
    exists_contDiff_eventuallyEq_nat hOopen (hθ₀u.mono hOu) hOmem
  refine ⟨i, θ, hθc, ?_⟩
  have hcont : ContinuousAt (fun x : Fin (n + 1) → ℝ => Fin.removeNth (α := fun _ => ℝ) i x) x₀ :=
    (continuous_pi fun j => continuous_apply _).continuousAt
  filter_upwards [hleft, hcont hθeq] with x hxinv hxθ hw0
  have hΦx : Function.update x i (w x) = emb (Fin.removeNth i x) := hkey x hw0
  rw [hΦx] at hxinv
  have hθx : θ (Fin.removeNth i x) = x i := by
    rw [hxθ, hxinv]
  rw [hθx, Fin.insertNth_self_removeNth]
