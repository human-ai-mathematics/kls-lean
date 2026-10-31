module

public import FunctionalInequalities.KLS.Klartag.PowerSupersolution
public import FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.Basic
public import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# The Laplacian of the dual moment-measure manifold

Klartag, *Logarithmically-concave moment measures I*, arXiv:1309.2767v1, Lemma 5.1, in the dual
(transport onto `K`) form of Section 5. For `φ` smooth on an open set `K` with positive definite
Hessian, `ρ` smooth on `K` and the dual transport equation (66)
`log det ∇²φ = ⟪x, ∇φ x⟫ - φ x - ρ x` on `K`, the operator `L u = Σ φ^{ij} u_ij - Σ x^i u_i` of (67)
satisfies `∫_K φ^{ij} u_i v_j e^{-ρ} = -∫_K v (L u) e^{-ρ}` whenever one of the smooth `u`, `v` is
compactly supported in `K`
(`MomentMeasure.integral_inverseHessian_gradient_mul_eq_neg_laplacian`).

The proof follows the source: (66) and Jacobi's formula give the divergence of the inverse
Hessian, Klartag (68), `Σ_i ∂_i φ^{ij} = -x_j + Σ_a φ^{ja} ∂_aρ` (in the source's raised-index
notation `φ^{ij}_j = x^i - φ^{ij}ρ_j`), hence the flux form
`Σ_ij ∂_i(e^{-ρ} φ^{ij} ∂_j u) = e^{-ρ} L u`; a smooth cutoff equal to one near the compact
support turns the locally smooth flux into a global compactly supported field, and Haar
integration by parts concludes. Regularity on `K` is localized by germ transfer as in
`KLS/Klartag/PowerSupersolution.lean`.

Scope: a conditional statement for a GIVEN `φ` satisfying (66) on `K`; no boundedness or
convexity of `K` or `ρ` is used. Existence of the potential, Theorem 1.1 and the diffusion of
Section 5 are not provided.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ContDiff RealInnerProductSpace Manifold

namespace FunctionalInequalities.Analysis.BakryEmery

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

local notation "dimE" => Module.finrank ℝ E
local notation "e" => stdOrthonormalBasis ℝ E

/-- A compact subset of an open set has a smooth compactly supported cutoff inside the open set
that equals one near each of its points. -/
private theorem exists_contDiff_cutoff_of_isCompact_subset_isOpen {S K : Set E}
    (hS : IsCompact S) (hK : IsOpen K) (hSK : S ⊆ K) :
    ∃ χ : E → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ K ∧
      ∀ x ∈ S, χ =ᶠ[𝓝 x] fun _ => 1 := by
  obtain ⟨δ, hδ, hδK⟩ := hS.exists_cthickening_subset_open hK hSK
  have hd : Disjoint (thickening δ S)ᶜ S :=
    disjoint_compl_left_iff_subset.mpr (self_subset_thickening hδ S)
  obtain ⟨f, hf0, hf1, -⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed 𝓘(ℝ, E)
    (n := (⊤ : ℕ∞)) isOpen_thickening.isClosed_compl hS.isClosed hd
  have hsupp : tsupport f ⊆ cthickening δ S := by
    refine (closure_mono ?_).trans (closure_thickening_subset_cthickening δ S)
    intro x hx
    by_contra hxs
    exact hx (hf0.self_of_nhdsSet x hxs)
  refine ⟨f, contMDiff_iff_contDiff.mp f.contMDiff, ?_, hsupp.trans hδK, ?_⟩
  · exact isCompact_of_isClosed_isBounded (isClosed_tsupport _)
      (hS.isBounded.cthickening.subset hsupp)
  · intro x hx
    exact hf1.filter_mono (nhds_le_nhdsSet hx)

/-- Coordinate algebra behind the divergence of the inverse Hessian. -/
private theorem divergence_algebra {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A H : ι → ι → ℝ) (T : ι → ι → ι → ℝ) (x r : ι → ℝ) (j : ι)
    (hfd : ∀ c, ∑ i, ∑ a, A i a * T c i a = ∑ k, x k * H k c - r c)
    (hinv : ∀ k, ∑ c, H k c * A c j = if k = j then 1 else 0)
    (hsym : ∀ c, A c j = A j c) :
    ∑ i, -(∑ a, ∑ c, A i a * T c i a * A c j) = -x j + ∑ a, A j a * r a := by
  have h1 : ∑ i, -(∑ a, ∑ c, A i a * T c i a * A c j) =
      -∑ c, (∑ i, ∑ a, A i a * T c i a) * A c j := by
    rw [Finset.sum_neg_distrib]
    congr 1
    simp_rw [Finset.sum_mul]
    exact (Finset.sum_congr rfl fun i _ => Finset.sum_comm).trans Finset.sum_comm
  rw [h1]
  simp_rw [hfd, sub_mul]
  rw [Finset.sum_sub_distrib]
  have h2 : ∑ c, (∑ k, x k * H k c) * A c j = ∑ k, x k * ∑ c, H k c * A c j := by
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [mul_assoc]
  rw [h2]
  simp_rw [hinv]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [neg_sub, sub_eq_neg_add]
  congr 1
  exact Finset.sum_congr rfl fun a _ => by rw [hsym]; ring

/-- Coordinate algebra behind the flux form of the operator. -/
private theorem flux_algebra {ι : Type*} [Fintype ι] (w : ℝ) (A U2 D : ι → ι → ℝ)
    (u r x : ι → ℝ) (hdiv : ∀ j, ∑ i, D i j = -x j + ∑ a, A j a * r a)
    (hsym : ∀ i j, A i j = A j i) :
    ∑ i, ∑ j, (w * A i j * U2 i j + u j * (w * D i j + A i j * (-w * r i))) =
      w * ((∑ i, ∑ j, A i j * U2 i j) - ∑ i, x i * u i) := by
  have hM : ∑ i, ∑ j, u j * (w * D i j) = ∑ j, u j * w * (-x j + ∑ a, A j a * r a) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hdiv j, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hT : ∑ i, ∑ j, u j * (A i j * (-w * r i)) = -∑ j, u j * w * ∑ a, A j a * r a := by
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun a _ => by rw [hsym a j]; ring
  have hF : ∑ i, ∑ j, w * A i j * U2 i j = w * ∑ i, ∑ j, A i j * U2 i j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hX : ∑ j, u j * w * (-x j + ∑ a, A j a * r a) - ∑ j, u j * w * ∑ a, A j a * r a =
      -(w * ∑ i, x i * u i) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp only [mul_add, Finset.sum_add_distrib]
  rw [hM, hT, hF]
  linear_combination hX

/-- Divergence of the inverse Hessian under the dual transport equation (66), Klartag (68):
`Σ_i ∂_i φ^{ij} = -x_j + Σ_a φ^{ja} ∂_a ρ`. -/
private theorem dualTransport_inverseHessian_divergence {φ ρ : E → ℝ} (hφ : ContDiff ℝ ∞ φ)
    {x : E} (hPD : ∀ᶠ y in 𝓝 x, ∀ v : E, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ φ y v v)
    (hρ : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ ρ y)
    (hEq : ∀ᶠ y in 𝓝 x, logDetHessian φ e y = ⟪y, gradient φ y⟫ - φ y - ρ y) (j : Fin dimE) :
    ∑ i, fderiv ℝ (fun y => inverseHessianEntry φ e y i j) x (e i) =
      -⟪x, e j⟫ + ∑ a, inverseHessianEntry φ e x j a * fderiv ℝ ρ x (e a) := by
  have h2 : ContDiff ℝ 2 φ := hφ.of_le (WithTop.coe_le_coe.mpr le_top)
  have hPDx := hPD.self_of_nhds
  have hcyc (a c i : Fin dimE) :
      fderiv ℝ (fun y => bilinearIteratedFDerivTwo ℝ φ y (e a) (e c)) x (e i) =
        stdHessianMatrixDeriv φ x c i a := by
    have hs : (fun y => bilinearIteratedFDerivTwo ℝ φ y (e a) (e c)) =
        fun y => bilinearIteratedFDerivTwo ℝ φ y (e c) (e a) :=
      funext fun y => bilinearIteratedFDerivTwo_symm h2 y _ _
    rw [hs, fderiv_bilinearIteratedFDerivTwo_comm hφ x (e c) (e a) (e i)]
    rfl
  have hfd (c : Fin dimE) := (dualTransport_first_derivative hφ hPD hρ hEq c).self_of_nhds
  have hinv (k : Fin dimE) : ∑ c, bilinearIteratedFDerivTwo ℝ φ x (e k) (e c) *
      inverseHessianEntry φ e x c j = if k = j then 1 else 0 := by
    have hjk : (if k = j then (1 : ℝ) else 0) = if j = k then 1 else 0 := by
      simp only [eq_comm]
    rw [hjk, ← sum_inverseHessianEntry_mul_hessian e h2 x hPDx j k]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [inverseHessianEntry_symm e h2 x c j, bilinearIteratedFDerivTwo_symm h2 x (e k) (e c)]
    ring
  rw [Finset.sum_congr rfl fun i _ => fderiv_inverseHessianEntry_apply e hφ x hPDx i j i]
  simp_rw [hcyc]
  exact divergence_algebra (fun a c => inverseHessianEntry φ e x a c)
    (fun k c => bilinearIteratedFDerivTwo ℝ φ x (e k) (e c)) (stdHessianMatrixDeriv φ x)
    (fun k => ⟪x, e k⟫) (fun c => fderiv ℝ ρ x (e c)) j hfd hinv
    (fun c => inverseHessianEntry_symm e h2 x c j)

/-- Flux form of the operator (67) under (66): `Σ_ij ∂_i (e^{-ρ} φ^{ij} ∂_j u) = e^{-ρ} L u`. -/
private theorem dualTransport_flux {φ ρ u : E → ℝ} (hφ : ContDiff ℝ ∞ φ) {x : E}
    (hPD : ∀ᶠ y in 𝓝 x, ∀ v : E, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ φ y v v)
    (hρ : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ ρ y)
    (hEq : ∀ᶠ y in 𝓝 x, logDetHessian φ e y = ⟪y, gradient φ y⟫ - φ y - ρ y)
    (hu : ContDiff ℝ ∞ u) :
    ∑ i, ∑ j, fderiv ℝ (fun y => Real.exp (-ρ y) * inverseHessianEntry φ e y i j *
      fderiv ℝ u y (e j)) x (e i) =
      Real.exp (-ρ x) * nondivergenceOperator (fun y => inverseHessianEntry φ e y)
        (fun y i => ⟪y, e i⟫) u x := by
  have h2 : ContDiff ℝ 2 φ := hφ.of_le (WithTop.coe_le_coe.mpr le_top)
  have hu2 : ContDiff ℝ 2 u := hu.of_le (WithTop.coe_le_coe.mpr le_top)
  have hPDx := hPD.self_of_nhds
  have hρx := hρ.self_of_nhds
  have hexp : HasFDerivAt (fun y => Real.exp (-ρ y)) (Real.exp (-ρ x) • -fderiv ℝ ρ x) x := by
    simpa only [Pi.neg_apply] using hρx.hasFDerivAt.neg.exp
  have hA (i j : Fin dimE) : DifferentiableAt ℝ (fun y => inverseHessianEntry φ e y i j) x :=
    (contDiffAt_inverseHessianEntry e hφ x hPDx i j).differentiableAt (by simp)
  have hdu (j : Fin dimE) : DifferentiableAt ℝ (fun y => fderiv ℝ u y (e j)) x :=
    (contDiff_fderiv_apply (m := ∞) hu (by simp) (e j)).differentiable (by simp) x
  have hterm (i j : Fin dimE) :
      fderiv ℝ (fun y => Real.exp (-ρ y) * inverseHessianEntry φ e y i j *
        fderiv ℝ u y (e j)) x (e i) =
      Real.exp (-ρ x) * inverseHessianEntry φ e x i j *
          bilinearIteratedFDerivTwo ℝ u x (e i) (e j) +
        fderiv ℝ u x (e j) * (Real.exp (-ρ x) *
          fderiv ℝ (fun y => inverseHessianEntry φ e y i j) x (e i) +
          inverseHessianEntry φ e x i j * (-Real.exp (-ρ x) * fderiv ℝ ρ x (e i))) := by
    rw [fderiv_mul_apply (f := fun y => Real.exp (-ρ y) * inverseHessianEntry φ e y i j)
        (hexp.differentiableAt.fun_mul (hA i j)) (hdu j),
      fderiv_mul_apply hexp.differentiableAt (hA i j), hexp.fderiv,
      ← bilinearIteratedFDerivTwo_eq_fderiv_apply hu2]
    simp only [smul_apply, neg_apply, smul_eq_mul]
    ring
  simp_rw [hterm]
  unfold nondivergenceOperator
  exact flux_algebra (Real.exp (-ρ x)) (fun i j => inverseHessianEntry φ e x i j)
    (fun i j => bilinearIteratedFDerivTwo ℝ u x (e i) (e j))
    (fun i j => fderiv ℝ (fun y => inverseHessianEntry φ e y i j) x (e i))
    (fun j => fderiv ℝ u x (e j)) (fun i => fderiv ℝ ρ x (e i)) (fun i => ⟪x, e i⟫)
    (dualTransport_inverseHessian_divergence hφ hPD hρ hEq) (inverseHessianEntry_symm e h2 x)

/--
Germ transfer of the inverse-Hessian regularity, symmetry and flux identity to a point of `K`. -/
private theorem dualTransport_local {K : Set E} (hK : IsOpen K) {φ ρ u : E → ℝ}
    (hφ : ContDiffOn ℝ ∞ φ K) (hρ : ContDiffOn ℝ ∞ ρ K)
    (hPD : ∀ y ∈ K, ∀ v : E, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ φ y v v)
    (hEq : ∀ y ∈ K, logDetHessian φ e y = ⟪y, gradient φ y⟫ - φ y - ρ y) (hu : ContDiff ℝ ∞ u)
    {x : E} (hx : x ∈ K) :
    (∀ i j, ContDiffAt ℝ ∞ (fun y => inverseHessianEntry φ e y i j) x) ∧
      (∀ i j, inverseHessianEntry φ e x i j = inverseHessianEntry φ e x j i) ∧
        ∑ i,
            ∑ j,
              fderiv ℝ
                (fun y => Real.exp (-ρ y) * inverseHessianEntry φ e y i j * fderiv ℝ u y (e j))
                x (e i) =
          Real.exp (-ρ x) *
            nondivergenceOperator (fun y => inverseHessianEntry φ e y) (fun y i => ⟪y, e i⟫) u
              x := by
  obtain ⟨ψ, hψ, hloc⟩ := exists_contDiff_eventuallyEq_germ hK hφ hx
  have hKx : ∀ᶠ y in 𝓝 x, y ∈ K := hK.mem_nhds hx
  have hPD' : ∀ᶠ y in 𝓝 x, ∀ v : E, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ ψ y v v := by
    filter_upwards [hloc, hKx] with y hy hyK
    rw [bilinearIteratedFDerivTwo_congr_of_eventuallyEq hy]
    exact hPD y hyK
  have hEq' : ∀ᶠ y in 𝓝 x, logDetHessian ψ e y = ⟪y, gradient ψ y⟫ - ψ y - ρ y := by
    filter_upwards [hloc, hKx] with y hy hyK
    have hg : gradient ψ y = gradient φ y := by
      unfold gradient
      rw [hy.fderiv_eq]
    rw [logDetHessian_congr_of_eventuallyEq _ hy, hg, hy.eq_of_nhds]
    exact hEq y hyK
  have hρd : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ ρ y := by
    filter_upwards [hKx] with y hyK
    exact (hρ.contDiffAt (hK.mem_nhds hyK)).differentiableAt (by simp)
  have hAeq : ∀ᶠ y in 𝓝 x, inverseHessianEntry ψ e y = inverseHessianEntry φ e y := by
    filter_upwards [hloc] with y hy
    exact inverseHessianEntry_congr_of_eventuallyEq _ hy
  have hψ2 : ContDiff ℝ 2 ψ := hψ.of_le (WithTop.coe_le_coe.mpr le_top)
  refine ⟨fun i j => ?_, fun i j => ?_, ?_⟩
  · refine
      (contDiffAt_inverseHessianEntry e hψ x hPD'.self_of_nhds i j).congr_of_eventuallyEq ?_
    filter_upwards [hAeq] with y hy
    rw [hy]
  · rw [← hAeq.self_of_nhds]
    exact inverseHessianEntry_symm e hψ2 x i j
  · have hflux := dualTransport_flux hψ hPD' hρd hEq' hu
    have hL :=
      nondivergenceOperator_congr (b := fun y i => ⟪y, e i⟫) (u := u) (u' := u) (A := fun y =>
        inverseHessianEntry ψ e y) (A' := fun y => inverseHessianEntry φ e y) hAeq.self_of_nhds
        EventuallyEq.rfl
    rw [← hL, ← hflux]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    refine congrArg (fun L : E →L[ℝ] ℝ => L (e i)) (EventuallyEq.fderiv_eq ?_)
    filter_upwards [hAeq] with y hy
    rw [hy]

end FunctionalInequalities.Analysis.BakryEmery

namespace FunctionalInequalities.Probability.MomentMeasure

open FunctionalInequalities.Analysis.BakryEmery

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

local notation "e" => stdOrthonormalBasis ℝ E

/-- **Klartag, Logarithmically-concave moment measures I, arXiv:1309.2767v1, Lemma 5.1**, in
the dual (transport-to-`K`) form of Section 5 with the regularity localized to `K`.
Let `K` be open, `φ` smooth on `K` with positive definite Hessian there, `ρ` smooth on `K`, and
`det ∇²φ(x) = exp(x·∇φ(x) - φ(x) - ρ(x))` on `K`, (66), written as
`log det ∇²φ = ⟪x, ∇φ x⟫ - φ x - ρ x`. Then the operator `L u = φ^{ij} u_ij - x^i u_i` of (67)
is the Laplacian of `(K, ∇²φ, e^{-ρ} dx)`:
`∫_K φ^{ij} u_i v_j e^{-ρ} = -∫_K v (L u) e^{-ρ}` for smooth `u`, `v`, one of them compactly
supported in `K`, against any additive Haar measure. -/
theorem integral_inverseHessian_gradient_mul_eq_neg_laplacian (m : Measure E)
    [m.IsAddHaarMeasure] {K : Set E} (hK : IsOpen K) {φ ρ u v : E → ℝ} (hφ : ContDiffOn ℝ ∞ φ K)
    (hρ : ContDiffOn ℝ ∞ ρ K)
    (hPD : ∀ y ∈ K, ∀ w : E, w ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ φ y w w)
    (hEq : ∀ y ∈ K, logDetHessian φ e y = ⟪y, gradient φ y⟫ - φ y - ρ y) (hu : ContDiff ℝ ∞ u)
    (hv : ContDiff ℝ ∞ v)
    (hc : (HasCompactSupport u ∧ tsupport u ⊆ K) ∨ (HasCompactSupport v ∧ tsupport v ⊆ K)) :
    (∫ x in K,
        (∑ i, ∑ j, inverseHessianEntry φ e x i j * fderiv ℝ u x (e i) * fderiv ℝ v x (e j)) *
          Real.exp (-ρ x) ∂m) =
      -∫ x in K,
          v x *
              nondivergenceOperator (fun y => inverseHessianEntry φ e y) (fun y i => ⟪y, e i⟫) u
                x *
            Real.exp (-ρ x) ∂m := by
  obtain ⟨S, hS, hSK, hvan⟩ :
    ∃ S : Set E, IsCompact S ∧ S ⊆ K ∧ ((∀ x ∉ S, u =ᶠ[𝓝 x] 0) ∨ (∀ x ∉ S, v =ᶠ[𝓝 x] 0)) := by
    rcases hc with ⟨hcu, hsu⟩ | ⟨hcv, hsv⟩
    · exact ⟨tsupport u, hcu, hsu, Or.inl fun x hx => notMem_tsupport_iff_eventuallyEq.mp hx⟩
    · exact ⟨tsupport v, hcv, hsv, Or.inr fun x hx => notMem_tsupport_iff_eventuallyEq.mp hx⟩
  obtain ⟨χ, hχ, hχc, hχK, hχ1⟩ := exists_contDiff_cutoff_of_isCompact_subset_isOpen hS hK hSK
  have hloc (x : E) (hx : x ∈ K) := dualTransport_local hK hφ hρ hPD hEq hu hx
  let G : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → E → ℝ := fun i j y =>
    Real.exp (-ρ y) * inverseHessianEntry φ e y i j * fderiv ℝ u y (e j)
  let F : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → E → ℝ := fun i j y =>
    χ y * G i j y
  have hχ0 (x : E) (hx : x ∉ K) : χ =ᶠ[𝓝 x] 0 :=
    notMem_tsupport_iff_eventuallyEq.mp fun h => hx (hχK h)
  have hF0 (i j : Fin (Module.finrank ℝ E)) (x : E) (hx : x ∉ K) : F i j =ᶠ[𝓝 x] 0 := by
    filter_upwards [hχ0 x hx] with y hy
    simp [F, hy]
  have hF (i j : Fin (Module.finrank ℝ E)) : ContDiff ℝ ∞ (F i j) := by
    refine contDiff_iff_contDiffAt.mpr fun y => ?_
    by_cases hy : y ∈ K
    · exact
        hχ.contDiffAt.mul
          ((((hρ.contDiffAt (hK.mem_nhds hy)).neg.exp).mul ((hloc y hy).1 i j)).mul
            (contDiff_fderiv_apply (m := ∞) hu (by simp) (e j)).contDiffAt)
    · exact contDiffAt_const.congr_of_eventuallyEq (hF0 i j y hy)
  have hFc (i j : Fin (Module.finrank ℝ E)) : HasCompactSupport (F i j) := hχc.mul_right
  have hint (i j : Fin (Module.finrank ℝ E)) :=
    integrable_fderiv_mul_of_hasCompactSupport m (hF i j) hv (Or.inl (hFc i j))
      (e i)
  -- the integration by parts identity on all of `E`

  have hIBP :
    (∫ x, ∑ i, ∑ j, fderiv ℝ (F i j) x (e i) * v x ∂m) =
      -∫ x, ∑ i, ∑ j, F i j x * fderiv ℝ v x (e i) ∂m := by
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hint i j).1,
      integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hint i j).2.1, ←
      Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => (hint i j).1,
      integral_finsetSum _ fun j _ => (hint i j).2.1, ← Finset.sum_neg_distrib]
    exact
      Finset.sum_congr rfl fun j _ =>
        integral_fderiv_mul_eq_neg_of_hasCompactSupport m (hF i j) hv (Or.inl (hFc i j))
          (e i)
  -- pointwise identification

  have hzero_fderiv {f : E → ℝ} {x : E} (h : f =ᶠ[𝓝 x] 0) : fderiv ℝ f x = 0 := by
    rw [h.fderiv_eq]
    exact fderiv_const_apply 0
  have hS1 (x : E) (hx : x ∈ S) (i j : Fin (Module.finrank ℝ E)) : F i j =ᶠ[𝓝 x] G i j := by
    filter_upwards [hχ1 x hx] with y hy
    simp [F, hy]
  have h1 (x : E) (hx : x ∈ K) :
    v x * nondivergenceOperator (fun y => inverseHessianEntry φ e y) (fun y i => ⟪y, e i⟫) u x *
        Real.exp (-ρ x) =
      ∑ i, ∑ j, fderiv ℝ (F i j) x (e i) * v x := by
    by_cases hxS : x ∈ S
    · simp_rw [(hS1 x hxS _ _).fderiv_eq]
      have hfl :
        ∑ i, ∑ j, fderiv ℝ (G i j) x (e i) =
          Real.exp (-ρ x) *
            nondivergenceOperator (fun y => inverseHessianEntry φ e y) (fun y i => ⟪y, e i⟫) u
              x :=
        (hloc x hx).2.2
      simp_rw [← Finset.sum_mul]
      rw [hfl]
      ring
    · rcases hvan with hu0 | hv0
      · have hG0 (i j : Fin (Module.finrank ℝ E)) : F i j =ᶠ[𝓝 x] 0 := by
          filter_upwards [(hu0 x hxS).fderiv (𝕜 := ℝ)] with y hy
          simp [F, G, hy]
        have hL :
          nondivergenceOperator (fun y => inverseHessianEntry φ e y) (fun y i => ⟪y, e i⟫) u x =
            0 := by
          rw [nondivergenceOperator_congr rfl (hu0 x hxS)]
          unfold nondivergenceOperator bilinearIteratedFDerivTwo
          simp
        simp [hL, hzero_fderiv (hG0 _ _)]
      · simp [(hv0 x hxS).eq_of_nhds]
  have h2 (x : E) (hx : x ∈ K) :
    (∑ i, ∑ j, inverseHessianEntry φ e x i j * fderiv ℝ u x (e i) * fderiv ℝ v x (e j)) *
        Real.exp (-ρ x) =
      ∑ i, ∑ j, F i j x * fderiv ℝ v x (e i) := by
    by_cases hxS : x ∈ S
    · simp_rw [(hS1 x hxS _ _).eq_of_nhds]
      rw [Finset.sum_comm, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [(hloc x hx).2.1 j i]
      simp only [G]
      ring
    · rcases hvan with hu0 | hv0
      · have hdu : fderiv ℝ u x = 0 := hzero_fderiv (hu0 x hxS)
        simp [F, G, hdu]
      · have hdv : fderiv ℝ v x = 0 := hzero_fderiv (hv0 x hxS)
        simp [hdv]
  have hK' : MeasurableSet K := hK.measurableSet
  rw [setIntegral_congr_fun hK' h1, setIntegral_congr_fun hK' h2,
    setIntegral_eq_integral_of_forall_compl_eq_zero,
    setIntegral_eq_integral_of_forall_compl_eq_zero, hIBP, neg_neg]
  · intro x hx
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    rw [hzero_fderiv (hF0 i j x hx)]
    simp
  · intro x hx
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    rw [(hF0 i j x hx).eq_of_nhds]
    simp

end FunctionalInequalities.Probability.MomentMeasure
