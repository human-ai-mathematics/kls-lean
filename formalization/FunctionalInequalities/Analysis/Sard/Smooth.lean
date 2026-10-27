import FunctionalInequalities.Analysis.Sard.Basic
import FunctionalInequalities.Analysis.PiCoordinates
import FunctionalInequalities.Analysis.Sard.CoordinateChange
import FunctionalInequalities.Analysis.LocalExtension
import FunctionalInequalities.Analysis.Sard.QuadraticCover
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
  built, and `Analysis/Graph/Implicit.lean` does not apply here since it needs `C^∞` data with an
  inner-product graph splitting.

The dimension descent below combines these ingredients to prove `sard_smooth_pi` and
`sard_smooth`, without assuming the critical set measurable. The sharp `C^n` statement
`Analysis.sard` is proved separately by Morse's decomposition in `Analysis/Sard/Sharp.lean`.
-/

noncomputable section

open Set Metric MeasureTheory
open scoped ContDiff Topology

namespace FunctionalInequalities.Analysis

section LocalGraph

variable {n : ℕ}

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
  obtain ⟨i, hi⟩ := PiCoordinates.exists_apply_single_ne_zero hd
  have hne : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have hdiff : Differentiable ℝ w := hw.differentiable (by simp)
  have hWopen : IsOpen {x : Fin (n + 1) → ℝ | fderiv ℝ w x (Pi.single i (1 : ℝ)) ≠ 0} :=
    isOpen_ne.preimage ((hw.continuous_fderiv (by simp)).clm_apply continuous_const)
  obtain ⟨Le, hLecoe⟩ := Sard.CoordinateChange.exists_updateEquiv i hi
  have hΦd : HasFDerivAt (fun x => Function.update x i (w x))
      (Le : (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ)) x₀ := by
    rw [hLecoe]
    exact Sard.CoordinateChange.hasFDerivAt_update i hdiff x₀
  have hΦc : ContDiffAt ℝ ∞ (fun x => Function.update x i (w x)) x₀ :=
    (Sard.CoordinateChange.contDiff_update i hw).contDiffAt
  set H := hΦc.toOpenPartialHomeomorph (fun x => Function.update x i (w x)) hΦd hne with hH
  have hHcoe : ⇑H = fun x => Function.update x i (w x) := rfl
  have hx₀src : x₀ ∈ H.source := hΦc.mem_toOpenPartialHomeomorph_source hΦd hne
  have hsymm : ∀ y ∈ H.target, fderiv ℝ w (H.symm y) (Pi.single i (1 : ℝ)) ≠ 0 →
      ContDiffAt ℝ ∞ H.symm y := by
    intro y hy hWy
    obtain ⟨Le', hLe'⟩ := Sard.CoordinateChange.exists_updateEquiv i hWy
    refine H.contDiffAt_symm (f₀' := Le') hy ?_ ?_
    · rw [hHcoe, hLe']
      exact Sard.CoordinateChange.hasFDerivAt_update i hdiff (H.symm y)
    · rw [hHcoe]
      exact (Sard.CoordinateChange.contDiff_update i hw).contDiffAt
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
    simp only [Fin.insertNth_removeNth, hx]

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
assumed measurable. The sharp `C^n` theorem is proved separately in `Analysis/Sard/Sharp.lean`. -/
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

section FiniteDimensional

variable {V : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- **Sard's theorem for `C^∞` real-valued functions** on an arbitrary finite-dimensional real
normed space. The critical set is not assumed measurable. This is the smooth category: the sharp
`C^(finrank)` statement `Analysis.sard` is proved separately in `Analysis/Sard/Sharp.lean`. -/
theorem sard_smooth {u : V → ℝ} (hu : ContDiff ℝ ∞ u) :
    (volume : Measure ℝ) (u '' {x | fderiv ℝ u x = 0}) = 0 := by
  have hdim : Module.finrank ℝ (Fin (Module.finrank ℝ V) → ℝ) = Module.finrank ℝ V := by
    simp
  set e : (Fin (Module.finrank ℝ V) → ℝ) ≃L[ℝ] V := ContinuousLinearEquiv.ofFinrankEq hdim with he
  rw [image_critical_comp_continuousLinearEquiv e u]
  exact sard_smooth_pi _ _ (hu.comp e.contDiff)

/-- Almost every value of a `C^∞` real-valued function on a finite-dimensional real normed space
is a regular value. The sharp finite-regularity theorem `Analysis.ae_forall_fderiv_ne_zero`
is proved separately in `Analysis/Sard/Sharp.lean`. -/
theorem ae_forall_fderiv_ne_zero_of_contDiff_top {u : V → ℝ} (hu : ContDiff ℝ ∞ u) :
    ∀ᵐ t ∂(volume : Measure ℝ), ∀ x, u x = t → fderiv ℝ u x ≠ 0 := by
  rw [ae_iff]
  refine measure_mono_null (fun t ht => ?_) (sard_smooth hu)
  by_contra hcon
  exact ht fun x hxt hx0 => hcon ⟨x, hx0, hxt⟩

end FiniteDimensional

end Induction

end FunctionalInequalities.Analysis
