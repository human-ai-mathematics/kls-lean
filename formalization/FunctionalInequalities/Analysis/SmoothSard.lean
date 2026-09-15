import FunctionalInequalities.Analysis.QuadraticCover
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-! # Ingredients for Sard's theorem in the smooth category

Three independent pieces of the descent used by Sard's theorem for `C^∞` real-valued functions
on `Fin n → ℝ`.

* `critical_subset_layers` splits the critical set into the fully flat layer, already handled by
  `Analysis.volume_image_flat_pow_univ_eq_zero`, and the finitely many intermediate layers.
* `exists_flat_direction` turns a nonvanishing derivative of order `j + 1` into a scalar `C^∞`
  function that vanishes on the `j`-th layer and has nonvanishing differential.
* `exists_local_graph` presents the regular zero set of such a function, near the base point, as
  the image of a map that is `C^∞` on an open set of parameters, with a fixed continuous
  parameter map. The chart is the inverse function theorem applied to the map replacing one
  coordinate by the function; no manifold framework and no new implicit-function framework is
  built, and `Analysis/ImplicitGraph.lean` does not apply here since it needs `C^∞` data with an
  inner-product graph splitting.

These are ingredients only. Sard's theorem itself is **not** proved here: the dimension descent
that consumes them, and the open-domain form of the flat layer it needs, are still missing, and
the sharp `C^n` `Analysis.sard` remains a direct hole in `KLS/WIP/AnalyticPrerequisites.lean`.
-/

noncomputable section

open Set Metric MeasureTheory
open scoped ContDiff Topology

namespace FunctionalInequalities.Analysis

section Extension

/-- A function smooth on an open set agrees near any of its points with a globally smooth
function. Multiplication by a bump supported in the open set; smoothness is local. -/
theorem exists_contDiff_eventuallyEq {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {O : Set E} {z : E} (hO : IsOpen O) (hf : ContDiffOn ℝ ∞ f O) (hz : z ∈ O) :
    ∃ g : E → F, ContDiff ℝ ∞ g ∧ g =ᶠ[𝓝 z] f := by
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

section LocalGraph

variable {n : ℕ}

/-- A nonzero functional on a finite product of lines is nonzero on a basis vector. -/
private lemma exists_apply_single_ne_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : (ι → ℝ) →L[ℝ] ℝ} (hα : α ≠ 0) : ∃ i : ι, α (Pi.single i (1 : ℝ)) ≠ 0 := by
  by_contra h
  push Not at h
  refine hα (ContinuousLinearMap.ext fun v => ?_)
  have hv : v = ∑ i : ι, v i • Pi.single i (1 : ℝ) := by
    funext k
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hv]
  simp [map_sum, h]

/-- Replacing the `i`-th coordinate by `w` keeps smoothness. -/
private lemma contDiff_straighten (i : Fin (n + 1)) {w : (Fin (n + 1) → ℝ) → ℝ}
    (hw : ContDiff ℝ ∞ w) : ContDiff ℝ ∞ (fun x => Function.update x i (w x)) := by
  rw [contDiff_pi]
  intro k
  by_cases hk : k = i
  · subst hk
    simpa using hw
  · simpa [Function.update_apply, hk] using contDiff_apply ℝ ℝ k

/-- The differential of that chart. -/
private lemma hasFDerivAt_straighten (i : Fin (n + 1)) {w : (Fin (n + 1) → ℝ) → ℝ}
    (hw : Differentiable ℝ w) (x : Fin (n + 1) → ℝ) :
    HasFDerivAt (fun x => Function.update x i (w x))
      (ContinuousLinearMap.pi fun k => if k = i then fderiv ℝ w x
        else ContinuousLinearMap.proj k) x := by
  refine hasFDerivAt_pi''  fun k => ?_
  rw [ContinuousLinearMap.proj_pi]
  by_cases hk : k = i
  · subst hk
    simpa using (hw x).hasFDerivAt
  · simpa [Function.update_apply, hk] using hasFDerivAt_apply (𝕜 := ℝ) k x

/-- That differential is injective as soon as `w` really depends on the `i`-th coordinate. -/
private lemma injective_straightenDeriv (i : Fin (n + 1)) {α : (Fin (n + 1) → ℝ) →L[ℝ] ℝ}
    (hα : α (Pi.single i (1 : ℝ)) ≠ 0) :
    Function.Injective (ContinuousLinearMap.pi fun k : Fin (n + 1) =>
      if k = i then α else ContinuousLinearMap.proj k) := by
  intro v₁ v₂ hv
  rw [← sub_eq_zero]
  set v : Fin (n + 1) → ℝ := v₁ - v₂ with hvdef
  have h0 : (ContinuousLinearMap.pi fun k : Fin (n + 1) =>
      if k = i then α else ContinuousLinearMap.proj k) v = 0 := by
    rw [hvdef, map_sub, hv, sub_self]
  have hoff : ∀ k, k ≠ i → v k = 0 := by
    intro k hk
    have := congrFun h0 k
    simpa [ContinuousLinearMap.pi_apply, hk] using this
  have hsingle : v = v i • Pi.single i (1 : ℝ) := by
    funext k
    by_cases hk : k = i
    · subst hk; simp
    · simp [hoff k hk, hk]
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
private lemma exists_straightenEquiv (i : Fin (n + 1)) {α : (Fin (n + 1) → ℝ) →L[ℝ] ℝ}
    (hα : α (Pi.single i (1 : ℝ)) ≠ 0) :
    ∃ Le : (Fin (n + 1) → ℝ) ≃L[ℝ] (Fin (n + 1) → ℝ),
      (Le : (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ)) =
        ContinuousLinearMap.pi fun k : Fin (n + 1) =>
          if k = i then α else ContinuousLinearMap.proj k := by
  refine ⟨(LinearEquiv.ofInjectiveEndo _ (injective_straightenDeriv i hα)).toContinuousLinearEquiv,
    ?_⟩
  ext v k
  rfl

/-- Local `C^∞` graph of a regular zero set. Near `x₀` every zero of `w` is `γ (p x)`, where the
parameter map `p` is a fixed continuous projection onto the remaining coordinates and `γ` is
`C^∞` on an open set of parameters. No manifold or chart framework is introduced: the chart is
the inverse function theorem applied to the map that replaces one coordinate by `w`. -/
theorem exists_local_graph {w : (Fin (n + 1) → ℝ) → ℝ} {x₀ : Fin (n + 1) → ℝ}
    (hw : ContDiff ℝ ∞ w) (hx₀ : w x₀ = 0) (hd : fderiv ℝ w x₀ ≠ 0) :
    ∃ (p : (Fin (n + 1) → ℝ) → (Fin n → ℝ)) (γ : (Fin n → ℝ) → (Fin (n + 1) → ℝ))
      (O : Set (Fin n → ℝ)),
      Continuous p ∧ IsOpen O ∧ p x₀ ∈ O ∧ ContDiffOn ℝ ∞ γ O ∧ γ (p x₀) = x₀ ∧
        ∀ᶠ x in 𝓝 x₀, w x = 0 → p x ∈ O ∧ γ (p x) = x := by
  classical
  obtain ⟨i, hi⟩ := exists_apply_single_ne_zero hd
  have hne : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have hdiff : Differentiable ℝ w := hw.differentiable (by simp)
  have hWopen : IsOpen {x : Fin (n + 1) → ℝ | fderiv ℝ w x (Pi.single i (1 : ℝ)) ≠ 0} :=
    isOpen_ne.preimage ((hw.continuous_fderiv (by simp)).clm_apply continuous_const)
  obtain ⟨Le, hLecoe⟩ := exists_straightenEquiv i hi
  have hΦd : HasFDerivAt (fun x => Function.update x i (w x))
      (Le : (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ)) x₀ := by
    rw [hLecoe]
    exact hasFDerivAt_straighten i hdiff x₀
  have hΦc : ContDiffAt ℝ ∞ (fun x => Function.update x i (w x)) x₀ :=
    (contDiff_straighten i hw).contDiffAt
  set H := hΦc.toOpenPartialHomeomorph (fun x => Function.update x i (w x)) hΦd hne with hH
  have hHcoe : ⇑H = fun x => Function.update x i (w x) := rfl
  have hx₀src : x₀ ∈ H.source := hΦc.mem_toOpenPartialHomeomorph_source hΦd hne
  have hsymm : ∀ y ∈ H.target, fderiv ℝ w (H.symm y) (Pi.single i (1 : ℝ)) ≠ 0 →
      ContDiffAt ℝ ∞ H.symm y := by
    intro y hy hWy
    obtain ⟨Le', hLe'⟩ := exists_straightenEquiv i hWy
    refine H.contDiffAt_symm (f₀' := Le') hy ?_ ?_
    · rw [hHcoe, hLe']
      exact hasFDerivAt_straighten i hdiff (H.symm y)
    · rw [hHcoe]
      exact (contDiff_straighten i hw).contDiffAt
  have hembc : ContDiff ℝ ∞ (fun y : Fin n → ℝ => Fin.insertNth (α := fun _ => ℝ) i (0 : ℝ) y) := by
    rw [contDiff_pi]
    intro k
    rcases eq_or_ne k i with rfl | hk
    · simpa using contDiff_const (c := (0 : ℝ))
    · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hk
      simpa using contDiff_apply ℝ ℝ j
  have hkey : ∀ x : Fin (n + 1) → ℝ, w x = 0 →
      Function.update x i (w x) = Fin.insertNth (α := fun _ => ℝ) i (0 : ℝ) (Fin.removeNth i x) := by
    intro x hx
    funext k
    rcases eq_or_ne k i with rfl | hk
    · simp [hx]
    · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hk
      simp [Fin.succAbove_ne i j, Fin.removeNth]
  set T : Set (Fin (n + 1) → ℝ) :=
    H.target ∩ H.symm ⁻¹' {x : Fin (n + 1) → ℝ | fderiv ℝ w x (Pi.single i (1 : ℝ)) ≠ 0} with hT
  have hTopen : IsOpen T :=
    H.continuousOn_symm.isOpen_inter_preimage H.open_target hWopen
  have hΦx₀ : Function.update x₀ i (w x₀) = Fin.insertNth (α := fun _ => ℝ) i (0 : ℝ)
      (Fin.removeNth i x₀) := hkey x₀ hx₀
  have hsymmx₀ : H.symm (Fin.insertNth (α := fun _ => ℝ) i (0 : ℝ) (Fin.removeNth i x₀)) = x₀ := by
    rw [← hΦx₀]
    exact H.left_inv hx₀src
  have hmemT : Fin.insertNth (α := fun _ => ℝ) i (0 : ℝ) (Fin.removeNth i x₀) ∈ T := by
    refine ⟨?_, ?_⟩
    · rw [← hΦx₀]
      exact hΦc.image_mem_toOpenPartialHomeomorph_target hΦd hne
    · rw [Set.mem_preimage, hsymmx₀]
      exact hi
  refine ⟨fun x => Fin.removeNth i x, fun y => H.symm (Fin.insertNth (α := fun _ => ℝ) i (0 : ℝ) y),
    (fun y : Fin n → ℝ => Fin.insertNth (α := fun _ => ℝ) i (0 : ℝ) y) ⁻¹' T,
    continuous_pi fun j => continuous_apply _, hTopen.preimage hembc.continuous, hmemT, ?_,
    hsymmx₀, ?_⟩
  · intro y hy
    exact ((hsymm _ hy.1 hy.2).comp y hembc.contDiffAt).contDiffWithinAt
  · have hcont : ContinuousAt (fun x : Fin (n + 1) → ℝ => Fin.removeNth i x) x₀ :=
      (continuous_pi fun j => continuous_apply _).continuousAt
    filter_upwards [H.open_source.mem_nhds hx₀src,
      hcont (hTopen.preimage hembc.continuous |>.mem_nhds hmemT)] with x hxsrc hxO hw0
    refine ⟨hxO, ?_⟩
    rw [← hkey x hw0]
    exact H.left_inv hxsrc

end LocalGraph

section FlatDirection

/-- A nonvanishing derivative of order `j + 1` produces a scalar `C^∞` function that vanishes
wherever the derivative of order `j` does, and whose differential does not vanish at the base
point. For `j = 1` this is the construction used in the planar case. -/
theorem exists_flat_direction {n j : ℕ} {u : (Fin n → ℝ) → ℝ} {x₀ : Fin n → ℝ}
    (hu : ContDiff ℝ ∞ u) (h : iteratedFDeriv ℝ (j + 1) u x₀ ≠ 0) :
    ∃ m : Fin j → (Fin n → ℝ),
      ContDiff ℝ ∞ (fun x => iteratedFDeriv ℝ j u x m) ∧
        fderiv ℝ (fun x => iteratedFDeriv ℝ j u x m) x₀ ≠ 0 := by
  obtain ⟨v, hv⟩ : ∃ v : Fin (j + 1) → (Fin n → ℝ), iteratedFDeriv ℝ (j + 1) u x₀ v ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact h (by ext v; simpa using hcon v)
  rw [iteratedFDeriv_succ_apply_left] at hv
  refine ⟨Fin.tail v, ?_, ?_⟩
  · have hFc : ContDiff ℝ ∞ (iteratedFDeriv ℝ j u) := hu.iteratedFDeriv_right le_rfl
    exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => (Fin n → ℝ)) ℝ
      (Fin.tail v)).contDiff.comp hFc
  · have hFd : HasFDerivAt (iteratedFDeriv ℝ j u)
        (fderiv ℝ (iteratedFDeriv ℝ j u) x₀) x₀ :=
      ((hu.iteratedFDeriv_right le_rfl :
        ContDiff ℝ ∞ (iteratedFDeriv ℝ j u)).differentiable (by simp) x₀).hasFDerivAt
    rw [(hFd.continuousMultilinear_apply_const (Fin.tail v)).fderiv]
    intro hzero
    apply hv
    have := congrArg (fun L : (Fin n → ℝ) →L[ℝ] ℝ => L (v 0)) hzero
    simpa using this

end FlatDirection

section Layers

/-- The largest index below `n` at which a downward-closed predicate still holds. -/
private lemma exists_top_index {n : ℕ} {Q : ℕ → Prop} (hn1 : 1 ≤ n) (hQ1 : Q 1) (hnot : ¬ Q n) :
    ∃ j, 1 ≤ j ∧ j < n ∧ Q j ∧ ¬ Q (j + 1) := by
  classical
  have hspec : Q (Nat.findGreatest Q n) := Nat.findGreatest_spec hn1 hQ1
  have hlt : Nat.findGreatest Q n < n := by
    rcases lt_or_eq_of_le (Nat.findGreatest_le (P := Q) n) with h | h
    · exact h
    · exact absurd (h ▸ hspec) hnot
  have hgreat : ¬ Q (Nat.findGreatest Q n + 1) :=
    Nat.findGreatest_is_greatest (P := Q) (n := n) (by omega) (by omega)
  exact ⟨Nat.findGreatest Q n, Nat.le_findGreatest hn1 hQ1, hlt, hspec, hgreat⟩

/-- The critical set is covered by the fully flat layer and the finitely many intermediate
layers. Pure set algebra over `fderiv u x = 0 ↔ iteratedFDeriv 1 u x = 0`; no analysis. -/
theorem critical_subset_layers {n : ℕ} (u : (Fin n → ℝ) → ℝ) (O : Set (Fin n → ℝ)) :
    {x ∈ O | fderiv ℝ u x = 0} ⊆
      {x ∈ O | ∀ k : ℕ, 1 ≤ k → k ≤ n → iteratedFDeriv ℝ k u x = 0} ∪
        ⋃ j ∈ Finset.Ico 1 n,
          {x ∈ O | (∀ k : ℕ, 1 ≤ k → k ≤ j → iteratedFDeriv ℝ k u x = 0) ∧
            iteratedFDeriv ℝ (j + 1) u x ≠ 0} := by
  rintro x ⟨hxO, hx⟩
  by_cases hall : ∀ k : ℕ, 1 ≤ k → k ≤ n → iteratedFDeriv ℝ k u x = 0
  · exact Or.inl ⟨hxO, hall⟩
  refine Or.inr ?_
  have h1 : iteratedFDeriv ℝ 1 u x = 0 := by
    refine norm_eq_zero.mp ?_
    rw [norm_iteratedFDeriv_one, hx]
    simp
  have hn1 : 1 ≤ n := by
    by_contra hc
    exact hall fun k hk1 hk2 => absurd (hk1.trans hk2) (by omega)
  have hP1 : ∀ k : ℕ, 1 ≤ k → k ≤ 1 → iteratedFDeriv ℝ k u x = 0 := by
    intro k hk1 hk2
    have hk : k = 1 := by omega
    rw [hk]
    exact h1
  obtain ⟨j, hj1, hjlt, hPj, hPj1⟩ :=
    exists_top_index (Q := fun j => ∀ k : ℕ, 1 ≤ k → k ≤ j → iteratedFDeriv ℝ k u x = 0)
      hn1 hP1 hall
  have hne' : iteratedFDeriv ℝ (j + 1) u x ≠ 0 := by
    intro hzero
    refine hPj1 fun k hk1 hk2 => ?_
    rcases Nat.lt_or_ge k (j + 1) with hk | hk
    · exact hPj k hk1 (by omega)
    · have hk' : k = j + 1 := by omega
      rw [hk']
      exact hzero
  exact Set.mem_biUnion (Finset.mem_Ico.mpr ⟨hj1, hjlt⟩) ⟨hxO, hPj, hne'⟩

end Layers



section Induction

private lemma fderiv_eq_zero_of_iteratedFDeriv_one {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {u : V → ℝ} {x : V} (h : iteratedFDeriv ℝ 1 u x = 0) :
    fderiv ℝ u x = 0 := by
  refine ContinuousLinearMap.ext fun v => ?_
  have hv := congrArg
    (fun L : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => V) ℝ => L fun _ => v) h
  simpa [iteratedFDeriv_one_apply] using hv

/-- One intermediate layer is locally null, given Sard in one dimension less. -/
private lemma exists_nhds_layer_image_null {m j : ℕ} {u : (Fin (m + 1) → ℝ) → ℝ}
    (hu : ContDiff ℝ ∞ u) (hj : 1 ≤ j)
    (ih : ∀ v : (Fin m → ℝ) → ℝ, ContDiff ℝ ∞ v →
      (volume : Measure ℝ) (v '' {y | fderiv ℝ v y = 0}) = 0)
    {x₀ : Fin (m + 1) → ℝ}
    (hflat : ∀ k : ℕ, 1 ≤ k → k ≤ j → iteratedFDeriv ℝ k u x₀ = 0)
    (hnf : iteratedFDeriv ℝ (j + 1) u x₀ ≠ 0) :
    ∃ V : Set (Fin (m + 1) → ℝ), IsOpen V ∧ x₀ ∈ V ∧
      (volume : Measure ℝ)
        (u '' ({x | (∀ k : ℕ, 1 ≤ k → k ≤ j → iteratedFDeriv ℝ k u x = 0) ∧
          iteratedFDeriv ℝ (j + 1) u x ≠ 0} ∩ V)) = 0 := by
  obtain ⟨mm, hwc, hwd⟩ := exists_flat_direction hu hnf
  have hw0 : iteratedFDeriv ℝ j u x₀ mm = 0 := by rw [hflat j hj le_rfl]; simp
  obtain ⟨p, γ, O, hpc, hOopen, hpO, hγ, _, hev⟩ := exists_local_graph hwc hw0 hwd
  obtain ⟨γ', hγ'c, hγ'eq⟩ := exists_contDiff_eventuallyEq hOopen hγ hpO
  have hIH := ih (fun y => u (γ' y)) (hu.comp hγ'c)
  have hnbhd : ∀ᶠ x in 𝓝 x₀,
      (iteratedFDeriv ℝ j u x mm = 0 → p x ∈ O ∧ γ (p x) = x) ∧ γ' (p x) = γ (p x) :=
    hev.and (hpc.continuousAt.eventually hγ'eq)
  obtain ⟨V, hVsub, hVopen, hVmem⟩ := _root_.mem_nhds_iff.mp hnbhd
  refine ⟨V, hVopen, hVmem, measure_mono_null ?_ hIH⟩
  rintro _ ⟨x, ⟨⟨hxflat, _⟩, hxV⟩, rfl⟩
  obtain ⟨hgraph, hγ'γ⟩ := hVsub hxV
  have hwx : iteratedFDeriv ℝ j u x mm = 0 := by rw [hxflat j hj le_rfl]; simp
  obtain ⟨_, hγpx⟩ := hgraph hwx
  have hγ'px : γ' (p x) = x := by rw [hγ'γ, hγpx]
  have hcrit : fderiv ℝ u x = 0 :=
    fderiv_eq_zero_of_iteratedFDeriv_one (hxflat 1 le_rfl hj)
  refine ⟨p x, ?_, ?_⟩
  · have hcomp : HasFDerivAt (fun y => u (γ' y))
        ((fderiv ℝ u (γ' (p x))).comp (fderiv ℝ γ' (p x))) (p x) :=
      ((hu.differentiable (by simp)) (γ' (p x))).hasFDerivAt.comp _
        ((hγ'c.differentiable (by simp)) (p x)).hasFDerivAt
    show fderiv ℝ (fun y => u (γ' y)) (p x) = 0
    rw [hcomp.fderiv, hγ'px, hcrit, ContinuousLinearMap.zero_comp]
  · exact congrArg u hγ'px

/-- **Sard's theorem for `C^∞` real-valued functions on `Fin n → ℝ`.** The critical set is not
assumed measurable. This is the smooth category: the sharp `C^n` statement is not proved. -/
theorem sard_smooth_pi : ∀ (n : ℕ) (u : (Fin n → ℝ) → ℝ), ContDiff ℝ ∞ u →
    (volume : Measure ℝ) (u '' {x | fderiv ℝ u x = 0}) = 0 := by
  intro n
  induction n with
  | zero =>
    intro u hu
    refine measure_mono_null (Set.image_mono ?_)
      (volume_image_flat_pow_univ_eq_zero (n := 0) (hu.of_le (by simp)))
    intro x _ k hk1 hk2
    exact absurd (hk1.trans hk2) (by omega)
  | succ m ih =>
    intro u hu
    have hsub : {x : Fin (m + 1) → ℝ | fderiv ℝ u x = 0} ⊆
        {x | ∀ k : ℕ, 1 ≤ k → k ≤ m + 1 → iteratedFDeriv ℝ k u x = 0} ∪
          ⋃ j ∈ Finset.Ico 1 (m + 1),
            {x | (∀ k : ℕ, 1 ≤ k → k ≤ j → iteratedFDeriv ℝ k u x = 0) ∧
              iteratedFDeriv ℝ (j + 1) u x ≠ 0} := by
      intro x hx
      rcases critical_subset_layers u Set.univ ⟨Set.mem_univ x, hx⟩ with h | h
      · exact Or.inl h.2
      · obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.mp h
        exact Or.inr (Set.mem_iUnion₂.mpr ⟨j, hj, hxj.2⟩)
    refine measure_mono_null (Set.image_mono hsub) ?_
    rw [Set.image_union]
    refine measure_union_null
      (volume_image_flat_pow_univ_eq_zero (hu.of_le (by norm_cast; exact le_top))) ?_
    rw [Set.image_iUnion₂]
    refine (measure_biUnion_null_iff (Finset.countable_toSet _)).mpr ?_
    intro j hj
    have hj1 : 1 ≤ j := (Finset.mem_Ico.mp hj).1
    choose V hVopen hVmem hVnull using fun x₀ :
        {x : Fin (m + 1) → ℝ | (∀ k : ℕ, 1 ≤ k → k ≤ j → iteratedFDeriv ℝ k u x = 0) ∧
          iteratedFDeriv ℝ (j + 1) u x ≠ 0} =>
      exists_nhds_layer_image_null hu hj1 ih x₀.2.1 x₀.2.2
    obtain ⟨I, hIc, hIeq⟩ := TopologicalSpace.isOpen_iUnion_countable V hVopen
    refine measure_mono_null ?_ ((measure_biUnion_null_iff hIc).mpr fun q _ => hVnull q)
    rintro _ ⟨x, hx, rfl⟩
    have hxcov : x ∈ ⋃ q ∈ I, V q := by
      rw [hIeq]
      exact mem_iUnion.mpr ⟨⟨x, hx⟩, hVmem _⟩
    obtain ⟨q, hq, hxq⟩ := mem_iUnion₂.mp hxcov
    exact mem_iUnion₂.mpr ⟨q, hq, ⟨x, ⟨hx, hxq⟩, rfl⟩⟩

/-- **Sard's theorem for `C^∞` real-valued functions** on an arbitrary finite-dimensional real
normed space. The critical set is not assumed measurable. This is the smooth category: the sharp
`C^(finrank)` statement `Analysis.sard` is a different, still unproved, obligation. -/
theorem sard_smooth {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {u : V → ℝ} (hu : ContDiff ℝ ∞ u) :
    (volume : Measure ℝ) (u '' {x | fderiv ℝ u x = 0}) = 0 := by
  have hdim : Module.finrank ℝ (Fin (Module.finrank ℝ V) → ℝ) = Module.finrank ℝ V := by
    simp
  set e : (Fin (Module.finrank ℝ V) → ℝ) ≃L[ℝ] V := ContinuousLinearEquiv.ofFinrankEq hdim with he
  have hdu : Differentiable ℝ u := hu.differentiable (by simp)
  have hchain : ∀ y, fderiv ℝ (u ∘ e) y =
      (fderiv ℝ u (e y)).comp (e : (Fin (Module.finrank ℝ V) → ℝ) →L[ℝ] V) :=
    fun y => ((hdu (e y)).hasFDerivAt.comp y e.hasFDerivAt).fderiv
  have himg : u '' {x | fderiv ℝ u x = 0} = (u ∘ e) '' {y | fderiv ℝ (u ∘ e) y = 0} := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨e.symm x, ?_, by simp⟩
      show fderiv ℝ (u ∘ e) (e.symm x) = 0
      rw [hchain, ContinuousLinearEquiv.apply_symm_apply]
      rw [show fderiv ℝ u x = 0 from hx]
      exact ContinuousLinearMap.zero_comp _
    · rintro ⟨y, hy, rfl⟩
      refine ⟨e y, ?_, rfl⟩
      show fderiv ℝ u (e y) = 0
      refine ContinuousLinearMap.ext fun v => ?_
      have hzero : fderiv ℝ (u ∘ e) y = 0 := hy
      rw [hchain] at hzero
      have := congrArg (fun L : (Fin (Module.finrank ℝ V) → ℝ) →L[ℝ] ℝ => L (e.symm v)) hzero
      simpa using this
  rw [himg]
  exact sard_smooth_pi _ _ (hu.comp e.contDiff)

/-- Almost every value of a `C^∞` real-valued function on a finite-dimensional real normed space
is a regular value. `C^∞` variant of the still unproved `Analysis.ae_forall_fderiv_ne_zero`. -/
theorem ae_forall_fderiv_ne_zero_of_contDiff_top {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] {u : V → ℝ} (hu : ContDiff ℝ ∞ u) :
    ∀ᵐ t ∂(volume : Measure ℝ), ∀ x, u x = t → fderiv ℝ u x ≠ 0 := by
  rw [ae_iff]
  refine measure_mono_null (fun t ht => ?_) (sard_smooth hu)
  by_contra hcon
  exact ht fun x hxt hx0 => hcon ⟨x, hx0, hxt⟩

end Induction

end FunctionalInequalities.Analysis
