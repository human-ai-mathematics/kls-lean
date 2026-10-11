import FunctionalInequalities.Analysis.BakryEmery.Calculus
import FunctionalInequalities.Analysis.Operator.Coordinates
import FunctionalInequalities.Analysis.Cutoff.Profile
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# The Hessian operator, its inverse and the inverse-Hessian diffusion operator

Letwin arXiv:2607.24164v1, pp. 5–7: for a smooth potential `φ` with positive definite Hessian, the
Hessian operator `∇²φ(x) = D(∇φ)(x)` is a self-adjoint unit with positive definite inverse; the
inverse Hessian is symmetric, inverts the Hessian in coordinates, and satisfies the derivative formula
(2.5) `∂_k ((∇²φ)⁻¹)_{ij} = −Σ_{a,c} ((∇²φ)⁻¹)_{ia} ∂_{kac}φ ((∇²φ)⁻¹)_{cj}` (operator and coordinate
forms). The operator `L = Σ ((∇²φ)⁻¹)_{ij} ∂_{ij} − Σ (∂_i V ∘ ∇φ) ∂_i` of (2.3) with the inverse Hessian as
coefficient field has the Leibniz rule. The potential `φ` is given (Letwin Lemma 2.2, moment-map
existence, is not provided); no Monge–Ampère equation, Lemma 2.4, Lemma 2.6, Brascamp–Lieb or
positive-semidefinite estimate is used or claimed. Proof bodies: Codex route bundle `MA-Inverse`
(independently accepted); statements and placement: Claude.

Letwin Lemma A.4 (p. 17) supporting results for the operator `L` of a given potential: the self-generator identity
`L φ = n − ⟨∇V(∇φ), ∇φ⟩` at a point with positive definite Hessian (`hessianInverseOperator_self`), its uniform bound
when `∇φ` takes values in a bounded `K` and `V` is `C¹` on an open set containing `closure K`
(`bounded_hessianInverseOperator_self`, compact-image bound of the pointwise identity), and the composition rule
`L(h ∘ W) = h′(W) LW + h″(W) Σ_{ij} ((∇²φ)⁻¹)_{ij} ∂_iW ∂_jW` for `C²` `W`, `h` with no hypothesis on `φ`
(`hessianInverseOperator_comp`). The minimum of `φ` is in `Analysis/Convex/Coercivity.lean`; the cutoffs `η(W/R)` and
their defect bound (Lemma A.4) are constructed in `IntegrationByParts/InverseHessianCutoff.lean`. Not provided: the
moment map. Proof bodies: Codex API jobs
`letwin-a4-self-astra-high-v2` (ff901785…), `letwin-a4-bounded-astra-high-v2` (f666a094…) and
`letwin-a4-chain-astra-high-v4` (d2f84023…), independently verified; statements and placement: Claude.

Also for Lemma A.4: the coefficient extraction `Σ_ij A_ij ∂_iφ ∂_j(h ∘ φ) = h′(φ) Σ_ij A_ij ∂_iφ ∂_jφ` in any orthonormal
basis (`sum_inverseHessianEntry_mul_fderiv_comp`, used by the energy identity in `IntegrationByParts/InverseHessian.lean`)
and the pointwise defect domination
`|L(e((φ − c)/R))| ≤ |R⁻¹e′((φ − c)/R)| |Lφ| + R⁻² |e″((φ − c)/R)| |Σ_ij A_ij ∂_iφ ∂_jφ|` for `C²` `φ`, `e` and all real
`c`, `R` (`abs_hessianInverseOperator_comp_sub_div_le`; the affine rescaling comes from the scalar leaf
`Analysis/Cutoff/Profile.lean`). Proof bodies: Codex API jobs `letwin-a4-energy-pointwise-astra-high-responses-v2`
(e0a237b1…) and `letwin-a4-pointwise-defect-astra-high-responses-v2` (one compiler-reported unused tactic removed,
a2f63c12…), independently verified, verbatim. The operator `L f` of a `C²` `f` is continuous for smooth `φ` with
positive definite Hessian and `V` `C¹` on an open set containing the gradient range
(`continuous_hessianInverseOperator`; `letwin-a4-operator-continuity-astra-feedback-responses-v7`, dadbfa97…).
-/

noncomputable section
open scoped ContDiff RealInnerProductSpace
open FunctionalInequalities.Analysis

namespace FunctionalInequalities.Analysis.BakryEmery

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The Hessian operator `∇²φ(x) = D(∇φ)(x) : E →L[ℝ] E`. The Euclidean coordinate object
`Probability.Stein.hessianMatrix` is its standard-basis entry matrix (`Probability.Stein.hessianMatrix_eq_operatorEntry_hessianOperator`). -/
def hessianOperator (φ : E → ℝ) (x : E) : E →L[ℝ] E := fderiv ℝ (gradient φ) x

/-- `D²φ(x)(u, v) = ⟪∇²φ(x) u, v⟫` (the same identity as `Probability.Stein.hessian_eq_inner_fderiv_gradient`,
restated for the operator; the Hessian–Stein chain source is credited). -/
theorem bilinearIteratedFDerivTwo_eq_inner_hessianOperator {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ) (x u v : E) :
    bilinearIteratedFDerivTwo ℝ φ x u v = ⟪hessianOperator φ x u, v⟫ := by
  have hg : ContDiff ℝ 1 (gradient φ) := contDiff_gradient hφ (by norm_num)
  have hfun : (fun x : E => fderiv ℝ φ x v) = fun x => ⟪gradient φ x, v⟫ := by
    funext x
    exact inner_gradient_left.symm
  rw [bilinearIteratedFDerivTwo_eq_fderiv_apply hφ, hfun,
    fderiv_inner_apply ℝ (hg.differentiable one_ne_zero x) (differentiableAt_const v)]
  simp [hessianOperator]

theorem operatorEntry_hessianOperator {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ E)
    {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ) (x : E) (i j : Fin m) :
    operatorEntry b (hessianOperator φ x) i j = bilinearIteratedFDerivTwo ℝ φ x (b i) (b j) := by
  rw [bilinearIteratedFDerivTwo_symm hφ x (b i) (b j), bilinearIteratedFDerivTwo_eq_inner_hessianOperator hφ]
  exact real_inner_comm _ _

/-- A positive definite Hessian is a unit (including rank zero). -/
theorem hessianOperator_isUnit_of_posDef {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ) (x : E)
    (hPD : ∀ v : E, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ φ x v v) :
    IsUnit (hessianOperator φ x) := by
  apply ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap.mpr
  apply (LinearMap.isUnit_iff_ker_eq_bot (hessianOperator φ x).toLinearMap).2
  apply LinearMap.ker_eq_bot.mpr
  intro u v huv
  change hessianOperator φ x u = hessianOperator φ x v at huv
  apply sub_eq_zero.mp
  by_contra hne
  have hp := hPD (u - v) hne
  have hz : hessianOperator φ x (u - v) = 0 := by
    rw [map_sub, huv, sub_self]
  rw [bilinearIteratedFDerivTwo_eq_inner_hessianOperator hφ, hz, inner_zero_left] at hp
  exact (lt_irrefl 0) hp

/-- The Hessian operator is self-adjoint. -/
theorem hessianOperator_isSelfAdjoint {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ) (x : E) :
    IsSelfAdjoint (hessianOperator φ x) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.2
  intro u v
  change ⟪hessianOperator φ x u, v⟫ = ⟪u, hessianOperator φ x v⟫
  calc
    ⟪hessianOperator φ x u, v⟫ = bilinearIteratedFDerivTwo ℝ φ x u v := (bilinearIteratedFDerivTwo_eq_inner_hessianOperator hφ x u v).symm
    _ = bilinearIteratedFDerivTwo ℝ φ x v u := bilinearIteratedFDerivTwo_symm hφ x u v
    _ = ⟪hessianOperator φ x v, u⟫ := bilinearIteratedFDerivTwo_eq_inner_hessianOperator hφ x v u
    _ = ⟪u, hessianOperator φ x v⟫ := real_inner_comm _ _

/-- The inverse of a positive definite Hessian is positive definite. -/
theorem inner_ringInverse_hessianOperator_pos {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ) (x : E)
    (hPD : ∀ v : E, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ φ x v v)
    (v : E) (hv : v ≠ 0) : 0 < ⟪Ring.inverse (hessianOperator φ x) v, v⟫ := by
  have hunit := hessianOperator_isUnit_of_posDef hφ x hPD
  have hright : hessianOperator φ x (Ring.inverse (hessianOperator φ x) v) = v := by
    have h := congrArg (fun L : E →L[ℝ] E => L v) (Ring.mul_inverse_cancel (hessianOperator φ x) hunit)
    simpa only [mul_apply_eq_comp, one_apply_eq_self] using h
  have hne : Ring.inverse (hessianOperator φ x) v ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hright
    exact hv hright.symm
  have hp := hPD (Ring.inverse (hessianOperator φ x) v) hne
  rw [bilinearIteratedFDerivTwo_eq_inner_hessianOperator hφ, hright] at hp
  calc
    0 < ⟪v, Ring.inverse (hessianOperator φ x) v⟫ := hp
    _ = ⟪Ring.inverse (hessianOperator φ x) v, v⟫ := real_inner_comm _ _

/-- The entries `((∇²φ)⁻¹)_{ij}` of the inverse Hessian in an orthonormal basis. -/
def inverseHessianEntry {m : ℕ} (φ : E → ℝ) (b : OrthonormalBasis (Fin m) ℝ E)
    (x : E) (i j : Fin m) : ℝ := operatorEntry b (Ring.inverse (hessianOperator φ x)) i j

/-- The inverse Hessian is symmetric. -/
theorem inverseHessianEntry_symm {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ E)
    {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ) (x : E) (i j : Fin m) :
    inverseHessianEntry φ b x i j = inverseHessianEntry φ b x j i := by
  have h := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1
    (hessianOperator_isSelfAdjoint hφ x).ringInverse
  change ⟪b i, Ring.inverse (hessianOperator φ x) (b j)⟫ =
    ⟪b j, Ring.inverse (hessianOperator φ x) (b i)⟫
  calc
    ⟪b i, Ring.inverse (hessianOperator φ x) (b j)⟫ =
        ⟪Ring.inverse (hessianOperator φ x) (b j), b i⟫ := real_inner_comm _ _
    _ = ⟪b j, Ring.inverse (hessianOperator φ x) (b i)⟫ := h (b j) (b i)

/-- `(∇²φ)⁻¹ ∇²φ = Id` in coordinates. -/
theorem sum_inverseHessianEntry_mul_hessian {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ E)
    {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ) (x : E)
    (hPD : ∀ v : E, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ φ x v v) (i j : Fin m) :
    (∑ a, inverseHessianEntry φ b x i a *
      bilinearIteratedFDerivTwo ℝ φ x (b a) (b j)) = if i = j then 1 else 0 := by
  obtain ⟨U, hU⟩ := hessianOperator_isUnit_of_posDef hφ x hPD
  have hInv : Ring.inverse (hessianOperator φ x) * hessianOperator φ x = 1 := by
    rw [← hU, Ring.inverse_unit]
    simp
  simp_rw [← operatorEntry_hessianOperator b hφ x]
  change (∑ a, operatorEntry b (Ring.inverse (hessianOperator φ x)) i a * operatorEntry b (hessianOperator φ x) a j) = _
  rw [← operatorEntry_mul, hInv]
  simp [operatorEntry, b.inner_eq_ite]

/-- **Letwin (2.5), operator form**: `D((∇²φ)⁻¹)(x)[v] = −(∇²φ)⁻¹ (D(∇²φ)(x)[v]) (∇²φ)⁻¹` for a smooth `φ`
with positive definite Hessian at `x`. -/
theorem fderiv_ringInverse_hessianOperator_apply {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (x : E)
    (hPD : ∀ v : E, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ φ x v v) (v : E) :
    fderiv ℝ (fun y => Ring.inverse (hessianOperator φ y)) x v =
      -(Ring.inverse (hessianOperator φ x) * fderiv ℝ (hessianOperator φ) x v * Ring.inverse (hessianOperator φ x)) := by
  have h2 : ContDiff ℝ 2 φ := hφ.of_le (WithTop.coe_le_coe.mpr le_top)
  have hg : ContDiff ℝ ∞ (gradient φ) := contDiff_gradient hφ (by simp)
  have hH : ContDiff ℝ ∞ (hessianOperator φ) := hg.fderiv_right (by simp)
  exact fderiv_ringInverse_comp_apply (hH.differentiable (by simp) x) (hessianOperator_isUnit_of_posDef h2 x hPD) v

/-- Exact directional (2.5): the middle factor is the ACTUAL derivative of the Hessian
operatorEntry, hence source `partial_abk phi`. No such identity is supplied as a premise. -/
theorem fderiv_inverseHessianEntry_apply {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ E)
    {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (x : E)
    (hPD : ∀ v : E, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ φ x v v) (i j k : Fin m) :
    fderiv ℝ (fun y => inverseHessianEntry φ b y i j) x (b k) =
      -(∑ a, ∑ c, inverseHessianEntry φ b x i a *
        fderiv ℝ (fun y => bilinearIteratedFDerivTwo ℝ φ y (b a) (b c)) x (b k) *
        inverseHessianEntry φ b x c j) := by
  have h2 : ContDiff ℝ 2 φ := hφ.of_le (WithTop.coe_le_coe.mpr le_top)
  have hg : ContDiff ℝ ∞ (gradient φ) := contDiff_gradient hφ (by simp)
  have hH : ContDiff ℝ ∞ (hessianOperator φ) := hg.fderiv_right (by simp)
  have hd : DifferentiableAt ℝ (hessianOperator φ) x := hH.differentiable (by simp) x
  have h := operatorEntry_ringInverse_fderiv_apply b hd (hessianOperator_isUnit_of_posDef h2 x hPD) i j (b k)
  change fderiv ℝ (fun y => operatorEntry b (Ring.inverse (hessianOperator φ y)) i j) x (b k) = _
  rw [h]
  congr 1
  apply Finset.sum_congr rfl
  intro a _ha
  apply Finset.sum_congr rfl
  intro c _hc
  have heq : (fun y => operatorEntry b (hessianOperator φ y) a c) =
      fun y => bilinearIteratedFDerivTwo ℝ φ y (b a) (b c) := by
    ext y
    exact operatorEntry_hessianOperator b h2 y a c
  rw [← operatorEntry_fderiv_apply b hd a c (b k), heq]
  rfl

section LocalRegularity

/-- The inverse-Hessian entries are `C^∞` at a point of positive definiteness. -/
theorem contDiffAt_inverseHessianEntry {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ E)
    {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (x : E)
    (hPD : ∀ v : E, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ φ x v v) (i j : Fin m) :
    ContDiffAt ℝ ∞ (fun y => inverseHessianEntry φ b y i j) x := by
  have h2 : ContDiff ℝ 2 φ := hφ.of_le (WithTop.coe_le_coe.mpr le_top)
  have hg : ContDiff ℝ ∞ (gradient φ) := contDiff_gradient hφ (by simp)
  have hH : ContDiff ℝ ∞ (hessianOperator φ) := hg.fderiv_right (by simp)
  obtain ⟨Q, hQ⟩ := hessianOperator_isUnit_of_posDef h2 x hPD
  have hInvAt : ContDiffAt ℝ ∞ Ring.inverse (hessianOperator φ x) :=
    hQ ▸ contDiffAt_ringInverse ℝ Q
  have hInv := hInvAt.comp x hH.contDiffAt
  exact contDiffAt_const.inner ℝ (hInv.clm_apply contDiffAt_const)

/-- Derivative of the drift coordinate `∂_a V ∘ ∇φ`: `∂_j (∂_aV(∇φ)) = Σ_c ∂_{ac}V(∇φ) ∂_{cj}φ`, for `V` smooth on an
open set containing `∇φ(x)`. -/
theorem fderiv_fderiv_comp_gradient_apply {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ E)
    {φ V : E → ℝ} (hφ : ContDiff ℝ ∞ φ) {U : Set E} (hU : IsOpen U)
    (hV : ContDiffOn ℝ ∞ V U) {x : E} (hx : gradient φ x ∈ U) (a j : Fin m) :
    fderiv ℝ (fun y => fderiv ℝ V (gradient φ y) (b a)) x (b j) =
      ∑ c, bilinearIteratedFDerivTwo ℝ V (gradient φ x) (b a) (b c) *
        bilinearIteratedFDerivTwo ℝ φ x (b c) (b j) := by
  have h2 : ContDiff ℝ 2 φ := hφ.of_le (WithTop.coe_le_coe.mpr le_top)
  have hVx : ContDiffAt ℝ ∞ V (gradient φ x) := hV.contDiffAt (hU.mem_nhds hx)
  have hV2 : ContDiffAt ℝ 2 V (gradient φ x) := hVx.of_le (WithTop.coe_le_coe.mpr le_top)
  have ha : ContDiffAt ℝ ∞ (fun z => fderiv ℝ V z (b a)) (gradient φ x) :=
    (hVx.fderiv_right (by simp)).clm_apply contDiffAt_const
  have hg : ContDiff ℝ ∞ (gradient φ) := contDiff_gradient hφ (by simp)
  have hc : fderiv ℝ (fun y => fderiv ℝ V (gradient φ y) (b a)) x =
      fderiv ℝ (fun z => fderiv ℝ V z (b a)) (gradient φ x) ∘L fderiv ℝ (gradient φ) x :=
    fderiv_comp x (ha.differentiableAt (by simp)) ((hg.differentiable (by simp)) x)
  rw [hc, ContinuousLinearMap.comp_apply]
  change fderiv ℝ (fun z => fderiv ℝ V z (b a)) (gradient φ x) (hessianOperator φ x (b j)) = _
  conv_lhs => rw [← b.sum_repr' (hessianOperator φ x (b j))]
  simp only [map_sum, map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro c _hc
  change operatorEntry b (hessianOperator φ x) c j * _ = _
  rw [operatorEntry_hessianOperator b h2, ← bilinearIteratedFDerivTwo_eq_fderiv_apply_at hV2, bilinearIteratedFDerivTwo_symm_at hV2 (b c) (b a)]
  ring

end LocalRegularity

section Diffusion

/-- Letwin's second-order operator with the inverse Hessian as coefficient field and the drift
`∂_i V ∘ ∇φ`: `L f = Σ_ij ((∇²φ)⁻¹)_{ij} ∂_{ij} f − Σ_i (∂_i V)(∇φ) ∂_i f` (the `nondivergenceOperator` of (2.3)
with `A = (∇²φ)⁻¹`, `b = ∇V ∘ ∇φ`, standard orthonormal basis). No Markov or symmetric-`L²` claim. -/
def hessianInverseOperator (φ V f : E → ℝ) (x : E) : ℝ :=
  nondivergenceOperator (fun y => inverseHessianEntry φ (stdOrthonormalBasis ℝ E) y)
    (fun y i => fderiv ℝ V (gradient φ y) (stdOrthonormalBasis ℝ E i)) f x

/-- The Leibniz rule (2.3) for the inverse-Hessian operator. -/
theorem hessianInverseOperator_mul {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ) (V : E → ℝ)
    {f g : E → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (x : E) :
    hessianInverseOperator φ V (fun y => f y * g y) x =
      f x * hessianInverseOperator φ V g x + g x * hessianInverseOperator φ V f x +
        2 * ∑ i, ∑ j, inverseHessianEntry φ (stdOrthonormalBasis ℝ E) x i j *
          fderiv ℝ f x (stdOrthonormalBasis ℝ E i) * fderiv ℝ g x (stdOrthonormalBasis ℝ E j) := by
  exact nondivergenceOperator_mul
    (fun y => inverseHessianEntry φ (stdOrthonormalBasis ℝ E) y)
    (fun y i j => inverseHessianEntry_symm (stdOrthonormalBasis ℝ E) hφ y i j)
    (fun y i => fderiv ℝ V (gradient φ y) (stdOrthonormalBasis ℝ E i)) hf hg x

end Diffusion

end FunctionalInequalities.Analysis.BakryEmery

/-! ### Letwin Lemma A.4 support: self-generator identity, its bound, composition

Declarations below are verbatim from the independently verified API sources (statements with their own binders, hence a
fresh namespace block without the section variables above). Order: the pointwise identity, its compact-image bound
(which uses it), the pointwise composition rule, the coefficient extraction, then the pointwise defect domination
(which uses the composition rule), then the operator continuity. -/

namespace FunctionalInequalities.Analysis.BakryEmery

section SelfGenerator

/-- **Self-generator identity** (Letwin Lemma A.4, p. 17): at a point where the Hessian of a `C²` potential is positive
definite, `L φ = dim E − ⟨∇V(∇φ), ∇φ⟩`. -/
theorem hessianInverseOperator_self {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {φ : E → ℝ}
    (hφ : ContDiff ℝ 2 φ) (V : E → ℝ) (x : E)
    (hPD : ∀ v : E, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ φ x v v) :
    hessianInverseOperator φ V φ x = (Module.finrank ℝ E : ℝ) -
      inner ℝ (gradient V (gradient φ x)) (gradient φ x) := by
    let b := stdOrthonormalBasis ℝ E
    have hrow (i : Fin (Module.finrank ℝ E)) :
        (∑ j, inverseHessianEntry φ b x i j *
          bilinearIteratedFDerivTwo ℝ φ x (b i) (b j)) = 1 := by
      calc
        _ = ∑ j, inverseHessianEntry φ b x i j *
            bilinearIteratedFDerivTwo ℝ φ x (b j) (b i) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [bilinearIteratedFDerivTwo_symm hφ x (b i) (b j)]
        _ = 1 := by
          simpa using sum_inverseHessianEntry_mul_hessian b hφ x hPD i i
    have hrepr :
        (∑ i, (fderiv ℝ φ x (b i)) • b i) = gradient φ x := by
      simpa [inner_gradient_right] using b.sum_repr' (gradient φ x)
    have hdrift :
        (∑ i, fderiv ℝ V (gradient φ x) (b i) *
          fderiv ℝ φ x (b i)) =
        fderiv ℝ V (gradient φ x) (gradient φ x) := by
      calc
        _ = fderiv ℝ V (gradient φ x)
            (∑ i, (fderiv ℝ φ x (b i)) • b i) := by
          simp only [map_sum, map_smul, smul_eq_mul]
          apply Finset.sum_congr rfl
          intro i hi
          exact mul_comm _ _
        _ = _ := by rw [hrepr]
    rw [inner_gradient_left]
    unfold hessianInverseOperator nondivergenceOperator
    change
      (∑ i, ∑ j, inverseHessianEntry φ b x i j *
        bilinearIteratedFDerivTwo ℝ φ x (b i) (b j)) -
        (∑ i, fderiv ℝ V (gradient φ x) (b i) *
          fderiv ℝ φ x (b i)) =
      (Module.finrank ℝ E : ℝ) -
        fderiv ℝ V (gradient φ x) (gradient φ x)
    simp only [hrow]
    rw [hdrift]
    simp

end SelfGenerator

section CompactImage

/-- **Bounded self-generator** (Letwin Lemma A.4, p. 17): if `∇φ` takes values in a bounded `K` and `V` is `C¹` on an
open set containing `closure K`, then `L φ` is uniformly bounded; the bound is constructed from `dim E` and the
compact-image bounds of `DV` and of `∇φ`. -/
theorem bounded_hessianInverseOperator_self {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {φ V : E → ℝ}
    (hφ : ContDiff ℝ 2 φ)
    (hPD : ∀ x v : E, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ φ x v v)
    {K U : Set E} (hK : Bornology.IsBounded K)
    (hRange : Set.range (gradient φ) ⊆ K)
    (hU : IsOpen U) (hKU : closure K ⊆ U) (hV : ContDiffOn ℝ 1 V U) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ x : E, |hessianInverseOperator φ V φ x| ≤ D := by
    have hcont : ContinuousOn (fderiv ℝ V) (closure K) :=
      (hV.continuousOn_fderiv_of_isOpen hU le_rfl).mono hKU
    obtain ⟨B, hB⟩ := hK.isCompact_closure.exists_bound_of_continuousOn hcont
    obtain ⟨R, hR⟩ := hK.exists_norm_le
    have hB0 : 0 ≤ max B 0 := le_max_right _ _
    have hR0 : 0 ≤ max R 0 := le_max_right _ _
    have hn : 0 ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
    refine ⟨(Module.finrank ℝ E : ℝ) + max B 0 * max R 0,
      add_nonneg hn (mul_nonneg hB0 hR0), ?_⟩
    intro x
    have hxK : gradient φ x ∈ K := hRange ⟨x, rfl⟩
    have hxcl : gradient φ x ∈ closure K := subset_closure hxK
    have hBx : ‖fderiv ℝ V (gradient φ x)‖ ≤ max B 0 :=
      (hB _ hxcl).trans (le_max_left _ _)
    have hRx : ‖gradient φ x‖ ≤ max R 0 :=
      (hR _ hxK).trans (le_max_left _ _)
    have hbound :
        |fderiv ℝ V (gradient φ x) (gradient φ x)| ≤ max B 0 * max R 0 := by
      calc
        |fderiv ℝ V (gradient φ x) (gradient φ x)| =
            ‖fderiv ℝ V (gradient φ x) (gradient φ x)‖ := by
          rw [Real.norm_eq_abs]
        _ ≤ ‖fderiv ℝ V (gradient φ x)‖ * ‖gradient φ x‖ :=
          ContinuousLinearMap.le_opNorm _ _
        _ ≤ max B 0 * max R 0 :=
          mul_le_mul hBx hRx (norm_nonneg _) hB0
    rw [hessianInverseOperator_self hφ V x (hPD x), inner_gradient_left]
    calc
      |(Module.finrank ℝ E : ℝ) -
          fderiv ℝ V (gradient φ x) (gradient φ x)| ≤
          (Module.finrank ℝ E : ℝ) +
            |fderiv ℝ V (gradient φ x) (gradient φ x)| := by
        simpa only [sub_zero, zero_sub, abs_neg, abs_of_nonneg hn] using
          (abs_sub_le (Module.finrank ℝ E : ℝ) 0
            (fderiv ℝ V (gradient φ x) (gradient φ x)))
      _ ≤ (Module.finrank ℝ E : ℝ) + max B 0 * max R 0 :=
        add_le_add_right hbound (Module.finrank ℝ E : ℝ)

end CompactImage

section Composition

/-- **Composition rule** (Letwin Lemma A.4, p. 17, `Lχ_R = R⁻¹η′(W/R) LW + R⁻²η″(W/R) φ^{ij}∂_iW∂_jW`): for `C²` `W`
and `h`, `L(h ∘ W) = h′(W) LW + h″(W) Σ_{ij} ((∇²φ)⁻¹)_{ij} ∂_iW ∂_jW`; the inverse-Hessian entries are arbitrary
coefficients here (no hypothesis on `φ`). -/
theorem hessianInverseOperator_comp {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {φ V W : E → ℝ} {h : ℝ → ℝ} (hW : ContDiff ℝ 2 W) (hh : ContDiff ℝ 2 h) (x : E) :
    hessianInverseOperator φ V (fun y => h (W y)) x =
      deriv h (W x) * hessianInverseOperator φ V W x +
        deriv (deriv h) (W x) * ∑ i, ∑ j, inverseHessianEntry φ (stdOrthonormalBasis ℝ E) x i j *
          fderiv ℝ W x (stdOrthonormalBasis ℝ E i) * fderiv ℝ W x (stdOrthonormalBasis ℝ E j) := by
    have hWd : Differentiable ℝ W := hW.differentiable (by norm_num)
    have hhd : Differentiable ℝ h := hh.differentiable (by norm_num)
    have hh' : ContDiff ℝ 1 (deriv h) := by
      change ContDiff ℝ 1 (fun y => fderiv ℝ h y (1 : ℝ))
      exact contDiff_fderiv_apply hh (by norm_num) 1
    have hh'd : Differentiable ℝ (deriv h) :=
      hh'.differentiable (by norm_num)
    have hcomp : ContDiff ℝ 2 (fun y => h (W y)) := by
      simpa only [Function.comp_def] using hh.comp hW
    have hfirst (y : E) :
        fderiv ℝ (fun z => h (W z)) y =
          deriv h (W y) • fderiv ℝ W y := by
      exact ((hhd (W y)).hasDerivAt.comp_hasFDerivAt y
        (hWd y).hasFDerivAt).fderiv
    have hfirst' (y : E) :
        fderiv ℝ (fun z => deriv h (W z)) y =
          deriv (deriv h) (W y) • fderiv ℝ W y := by
      exact ((hh'd (W y)).hasDerivAt.comp_hasFDerivAt y
        (hWd y).hasFDerivAt).fderiv
    have hsecond (v w : E) :
        bilinearIteratedFDerivTwo ℝ (fun y => h (W y)) x v w =
          deriv h (W x) * bilinearIteratedFDerivTwo ℝ W x v w +
            deriv (deriv h) (W x) * fderiv ℝ W x v * fderiv ℝ W x w := by
      rw [bilinearIteratedFDerivTwo_eq_fderiv_apply hcomp x v w,
        bilinearIteratedFDerivTwo_eq_fderiv_apply hW x v w]
      have hfun :
          (fun y => fderiv ℝ (fun z => h (W z)) y w) =
            (fun y => deriv h (W y) * fderiv ℝ W y w) := by
        funext y
        simp only [hfirst, smul_apply, smul_eq_mul]
      rw [hfun]
      change
        fderiv ℝ
            ((fun y => deriv h (W y)) * (fun y => fderiv ℝ W y w)) x v =
          _
      have hdiff : DifferentiableAt ℝ (fun y => deriv h (W y)) x := by
        simpa only [Function.comp_def] using
          ((hh'd (W x)).comp x (hWd x))
      rw [fderiv_mul hdiff
        (differentiable_fderiv_apply hW w x), hfirst']
      simp only [add_apply, smul_apply, smul_eq_mul]
      ring
    simp only [hessianInverseOperator, nondivergenceOperator, hsecond, hfirst,
      smul_apply, smul_eq_mul]
    simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.mul_sum]
    simp only [mul_left_comm, mul_comm]
    ring

end Composition

section CoefficientExtraction

/-- **Coefficient extraction** (Letwin Lemma A.4, p. 17, energy identity after (2.2)): in any orthonormal basis,
`Σ_ij A_ij ∂_iφ ∂_j(h ∘ φ) = h′(φ) Σ_ij A_ij ∂_iφ ∂_jφ` for smooth `φ`, `h`. -/
theorem sum_inverseHessianEntry_mul_fderiv_comp {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ E)
    {φ : E → ℝ} {h : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hh : ContDiff ℝ ∞ h) (x : E) :
    (∑ i, ∑ j, inverseHessianEntry φ b x i j * fderiv ℝ φ x (b i) *
      fderiv ℝ (fun y => h (φ y)) x (b j)) =
    deriv h (φ x) * ∑ i, ∑ j, inverseHessianEntry φ b x i j *
      fderiv ℝ φ x (b i) * fderiv ℝ φ x (b j) := by
    have hchain (v : E) :
        fderiv ℝ (fun y => h (φ y)) x v =
          deriv h (φ x) * fderiv ℝ φ x v := by
      have hd := ((hh.differentiable (by simp)) (φ x)).hasDerivAt.comp_hasFDerivAt x
        ((hφ.differentiable (by simp)) x).hasFDerivAt
      have hv := congrArg (fun L : E →L[ℝ] ℝ => L v) hd.fderiv
      simpa only [Function.comp_def, smul_apply, smul_eq_mul] using hv
    simp_rw [hchain, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring

end CoefficientExtraction

section DefectDomination

/-- **Pointwise defect domination** (Letwin Lemma A.4, p. 17, `Lχ_R = R⁻¹η′(W/R) LW + R⁻²η″(W/R) Γ(W)`): for `C²` `φ`
and a `C²` profile `e`, all real `c`, `R` (total conventions), the generator of `e((φ − c)/R)` is dominated by the
first- and second-derivative terms; no hypothesis on `V` or definiteness. -/
theorem abs_hessianInverseOperator_comp_sub_div_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {φ V : E → ℝ} {e : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) (he : ContDiff ℝ 2 e) (c R : ℝ) (x : E) :
    |hessianInverseOperator φ V (fun y => e ((φ y - c) / R)) x| ≤
      |R⁻¹ * deriv e ((φ x - c) / R)| * |hessianInverseOperator φ V φ x| +
        (R⁻¹) ^ 2 * |deriv (deriv e) ((φ x - c) / R)| *
          |∑ i, ∑ j, inverseHessianEntry φ (stdOrthonormalBasis ℝ E) x i j *
            fderiv ℝ φ x (stdOrthonormalBasis ℝ E i) * fderiv ℝ φ x (stdOrthonormalBasis ℝ E j)| := by
    let h : ℝ → ℝ := fun s => e ((s - c) / R)
    have hh : ContDiff ℝ 2 h := by
      exact he.comp ((contDiff_id.sub contDiff_const).div_const R)
    have hd :
        deriv h (φ x) = R⁻¹ * deriv e ((φ x - c) / R) ∧
        deriv (deriv h) (φ x) =
          (R⁻¹) ^ 2 * deriv (deriv e) ((φ x - c) / R) := by
      dsimp only [h]
      apply FunctionalInequalities.Analysis.deriv_comp_sub_div_and_deriv_deriv
    change |hessianInverseOperator φ V (fun y => h (φ y)) x| ≤ _
    rw [hessianInverseOperator_comp hφ hh x, hd.1, hd.2]
    refine (abs_add_le _ _).trans ?_
    apply le_of_eq
    simp only [abs_mul, abs_of_nonneg (sq_nonneg (R⁻¹))]

end DefectDomination

section Continuity

/-- **Operator continuity** (Letwin Lemma A.4, p. 17, measurability of `Lχ_R`, hence `Lχ_R ∈ L¹(ν)` by domination):
for smooth `φ` with positive definite Hessian, `V` `C¹` on an open set containing the gradient range and `C²` `f`,
`L f` is continuous. Proof body: Codex API job `letwin-a4-operator-continuity-astra-feedback-responses-v7`
(dadbfa97…), independently verified, verbatim. -/
theorem continuous_hessianInverseOperator {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {φ V f : E → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hPD : ∀ x v : E, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ φ x v v)
    {U : Set E} (hU : IsOpen U) (hV : ContDiffOn ℝ 1 V U) (hRange : Set.range (gradient φ) ⊆ U)
    (hf : ContDiff ℝ 2 f) :
    Continuous (hessianInverseOperator φ V f) := by
    let b := stdOrthonormalBasis ℝ E
    have hInv (i j : Fin (Module.finrank ℝ E)) :
        Continuous (fun x => inverseHessianEntry φ b x i j) := by
      exact
        (contDiff_iff_contDiffAt.mpr
          (fun x =>
            contDiffAt_inverseHessianEntry b hφ x (hPD x) i j)).continuous
    have hφ' : Continuous (fderiv ℝ φ) :=
      hφ.continuous_fderiv (by norm_num)
    have hgrad : Continuous (gradient φ) := by
      unfold gradient
      continuity
    have hV' : ContinuousOn (fun x => fderiv ℝ V x) U :=
      hV.continuousOn_fderiv_of_isOpen hU le_rfl
    have hDV : Continuous (fun x => fderiv ℝ V (gradient φ x)) := by
      simpa [Function.comp_def] using
        hV'.comp_continuous hgrad
          (fun x => hRange (Set.mem_range_self x))
    have hDVcoord (i : Fin (Module.finrank ℝ E)) :
        Continuous (fun x => (fderiv ℝ V (gradient φ x)) (b i)) := by
      exact hDV.clm_apply (continuous_const : Continuous (fun _ : E => b i))
    have hfirst (i : Fin (Module.finrank ℝ E)) :
        Continuous (fun x => (fderiv ℝ f x) (b i)) := by
      exact
        (hf.continuous_fderiv (by norm_num)).clm_apply
          (continuous_const : Continuous (fun _ : E => b i))
    have hsecond (i j : Fin (Module.finrank ℝ E)) :
        Continuous
          (fun x => bilinearIteratedFDerivTwo ℝ f x (b i) (b j)) := by
      have hcf :
          ContDiff ℝ 1 (fun y => (fderiv ℝ f y) (b j)) :=
        contDiff_fderiv_apply hf (by norm_num) (b j)
      have hc :
          Continuous (fderiv ℝ (fun y => (fderiv ℝ f y) (b j))) :=
        hcf.continuous_fderiv (by norm_num)
      have hright :
          Continuous
            (fun x => (fderiv ℝ (fun y => (fderiv ℝ f y) (b j)) x) (b i)) :=
        hc.clm_apply (continuous_const : Continuous (fun _ : E => b i))
      have heq :
          (fun x => bilinearIteratedFDerivTwo ℝ f x (b i) (b j)) =
            (fun x => (fderiv ℝ (fun y => (fderiv ℝ f y) (b j)) x) (b i)) := by
        funext x
        exact bilinearIteratedFDerivTwo_eq_fderiv_apply hf x (b i) (b j)
      rw [heq]
      exact hright
    unfold hessianInverseOperator nondivergenceOperator
    continuity

end Continuity

end FunctionalInequalities.Analysis.BakryEmery
