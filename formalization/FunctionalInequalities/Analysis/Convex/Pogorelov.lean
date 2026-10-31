module

public import FunctionalInequalities.Analysis.BakryEmery.LinearizedEquation
public import FunctionalInequalities.Analysis.Convex.Viscosity.Touching
public import FunctionalInequalities.Analysis.Matrix.Positivity
public import Mathlib.Algebra.BigOperators.Field

/-!
# Classical Pogorelov point estimates

Savin, *The obstacle problem for Monge Ampere equation*, Calc. Var. PDE 22 (2005),
303–320, Proposition 4.1, proof (10)–(15), pp. 13–14, DOI 10.1007/s00526-004-0275-8.

For a GIVEN classical potential, the actual constant-determinant equation and a
logarithmic local maximum give a directional height–Hessian estimate. Positive
definiteness generates coordinates fixing the chosen axis. On bounded open domains
with C4 interior, C2 at every closure point, negativity and zero WHOLE frontier,
compactness then generates the maximizing point, a gradient cap, the full elementwise
Hessian-height estimate and bounds on every compact interior set. The open domain
need not be convex. Empty domains and zero dimension are included.

This is an interior estimate for classical solutions, not construction of such
solutions or C2 regularity of the merely C1 UNIT Alexandrov reference.
-/

@[expose] public section

noncomputable section
open Filter
open scoped Topology ContDiff Matrix.Norms.Elementwise BigOperators
open FunctionalInequalities.Analysis.BakryEmery FunctionalInequalities.Probability.Stein
namespace FunctionalInequalities.Analysis.Pogorelov

private abbrev D {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (v : E) : E → ℝ := fun y => fderiv ℝ f y v

private theorem smooth_D_at {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ}
    {x : E} {k : ℕ∞ω} (hf : ContDiffAt ℝ (k + 1) f x) (v : E) : ContDiffAt ℝ k (D f v) x :=
  (hf.fderiv_right le_rfl).clm_apply contDiffAt_const

private theorem D_congr {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℝ} {x : E} (h : f =ᶠ[𝓝 x] g) (v : E) :
    D f v =ᶠ[𝓝 x] D g v :=
  h.fderiv.mono fun _ hy => congrArg (fun L : E →L[ℝ] ℝ => L v) hy

/-- The positive quadratic energy contains the distinguished row twice,
with the diagonal counted once. This is actual symmetric finite-sum algebra. -/
private theorem row_energy_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (E : ι → ι → ℝ) (k : ι) (hE : ∀ i j, 0 ≤ E i j)
    (hsym : ∀ i j, E i j = E j i) :
    E k k + 2 * ∑ i ∈ Finset.univ.erase k, E k i ≤ ∑ i, ∑ j, E i j := by
  have hrow (i : ι) : E i k ≤ ∑ j, E i j :=
    Finset.single_le_sum (fun j _ => hE i j) (Finset.mem_univ k)
  have hsum := Finset.sum_le_sum (s := Finset.univ.erase k) (fun i _ => hrow i)
  have hc : (∑ i ∈ Finset.univ.erase k, E i k) =
      ∑ i ∈ Finset.univ.erase k, E k i := by
    apply Finset.sum_congr rfl
    intro i _
    exact hsym i k
  have hk : E k k + ∑ i ∈ Finset.univ.erase k, E k i = ∑ i, E k i :=
    Finset.add_sum_erase _ _ (Finset.mem_univ k)
  have hall : (∑ j, E k j) + ∑ i ∈ Finset.univ.erase k, (∑ j, E i j) =
      ∑ i, ∑ j, E i j := Finset.add_sum_erase _ (fun i => ∑ j, E i j) (Finset.mem_univ k)
  rw [hc] at hsum
  linarith

/-- Finite-jet cancellation in Savin Prop4.1 proof(10)-(15), pp13-14.
Inputs are ordinary diagonal positive Hessian entries, symmetric third jets,
PDE derivative identities and first/second logarithmic maximum conditions.
The conclusion is the actual directional height-Hessian bound, not an input.
No classical solution, maximizing point or regularity is constructed here. -/
private theorem directional_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ι) (lam g Q : ι → ℝ) (S : ι → ι → ℝ) (u : ℝ)
    (hlam : ∀ i, 0 < lam i) (hu : u < 0)
    (hS : ∀ i j, S i j = S j i)
    (hfirst : ∑ i, S i i / lam i = 0)
    (hsecond : ∑ i, Q i / lam i = ∑ i, ∑ j, S i j ^ 2 / (lam i * lam j))
    (hcritical : ∀ i, i ≠ k → S k i / lam k + g i / u = 0)
    (hmaximum : (∑ i, Q i / lam i) / lam k -
      (∑ i, S k i ^ 2 / (lam k ^ 2 * lam i)) +
      (Fintype.card ι : ℝ) / u - (∑ i, g i ^ 2 / (lam i * u ^ 2)) +
      g k * (∑ i, S i i / lam i) + lam k ≤ 0) :
    lam k * (-u) ≤ (Fintype.card ι : ℝ) + |g k| := by
  let E := fun i j => S i j ^ 2 / (lam k * lam i * lam j)
  have hnz (i : ι) : lam i ≠ 0 := (hlam i).ne'
  have hunz : u ≠ 0 := hu.ne
  have he := row_energy_le E k
    (fun i j => div_nonneg (sq_nonneg _)
      (mul_nonneg (mul_nonneg (hlam k).le (hlam i).le) (hlam j).le))
    (by intro i j; dsimp [E]; rw [hS i j]; congr 1; ring)
  have hq : (∑ i, Q i / lam i) / lam k = ∑ i, ∑ j, E i j := by
    rw [hsecond, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    dsimp [E]
    field_simp
  have heki (i : ι) : E k i = S k i ^ 2 / (lam k ^ 2 * lam i) := by
    dsimp [E]
    congr 1
    ring
  have hoff (i : ι) (hi : i ∈ Finset.univ.erase k) :
      S k i ^ 2 / (lam k ^ 2 * lam i) = g i ^ 2 / (lam i * u ^ 2) := by
    have h := hcritical i (Finset.mem_erase.mp hi).1
    field_simp [hnz, hunz] at h ⊢
    have hs : S k i * u = -(lam k * g i) := by linarith
    have hh := congrArg (fun z : ℝ => z ^ 2) hs
    nlinarith only [hh]
  have ht : S k k ^ 2 / (lam k ^ 2 * lam k) +
      ∑ i ∈ Finset.univ.erase k, S k i ^ 2 / (lam k ^ 2 * lam i) =
      ∑ i, S k i ^ 2 / (lam k ^ 2 * lam i) :=
    Finset.add_sum_erase _ (fun i => S k i ^ 2 / (lam k ^ 2 * lam i)) (Finset.mem_univ k)
  have hg : g k ^ 2 / (lam k * u ^ 2) +
      ∑ i ∈ Finset.univ.erase k, g i ^ 2 / (lam i * u ^ 2) =
      ∑ i, g i ^ 2 / (lam i * u ^ 2) :=
    Finset.add_sum_erase _ (fun i => g i ^ 2 / (lam i * u ^ 2)) (Finset.mem_univ k)
  have hsum : (∑ i ∈ Finset.univ.erase k, S k i ^ 2 / (lam k ^ 2 * lam i)) =
      ∑ i ∈ Finset.univ.erase k, g i ^ 2 / (lam i * u ^ 2) :=
    Finset.sum_congr rfl hoff
  simp_rw [heki] at he
  rw [hfirst, mul_zero, add_zero, hq] at hmaximum
  have hred : (Fintype.card ι : ℝ) / u - g k ^ 2 / (lam k * u ^ 2) + lam k ≤ 0 := by
    linarith
  have hm := mul_nonpos_of_nonpos_of_nonneg hred (mul_nonneg (hlam k).le (sq_nonneg u))
  have hpoly : (lam k * (-u)) ^ 2 - (Fintype.card ι : ℝ) * (lam k * (-u)) ≤ g k ^ 2 := by
    field_simp [hnz, hunz] at hm
    nlinarith
  have hc : 0 ≤ (Fintype.card ι : ℝ) := by positivity
  have hx : 0 < lam k * (-u) := mul_pos (hlam k) (neg_pos.mpr hu)
  have ha := abs_nonneg (g k)
  have hasq := sq_abs (g k)
  by_contra h
  have hgt : (Fintype.card ι : ℝ) + |g k| < lam k * (-u) := lt_of_not_ge h
  have hgX : |g k| ^ 2 ≤ |g k| * (lam k * (-u)) := by
    nlinarith [mul_nonneg ha (show 0 ≤ lam k * (-u) - |g k| by linarith)]
  have hp := mul_pos hx
    (show 0 < lam k * (-u) - (Fintype.card ι : ℝ) - |g k| by linarith)
  nlinarith

private theorem matrix_entry_derivative {ι G : Type*} [Fintype ι]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {M : G → Matrix ι ι ℝ} {x : G} (hM : DifferentiableAt ℝ M x)
    (v : G) (i j : ι) :
    (fderiv ℝ M x v) i j = D (fun y => M y i j) v x := by
  dsimp [D]
  rw [fderiv_apply (differentiableAt_pi.mp hM i) j, fderiv_apply hM i]
  rfl

private theorem hessian_entry_near {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanSpace ℝ (Fin n)} (hu : ContDiffAt ℝ 3 u x) (i j : Fin n) :
    (fun y => hessianMatrix u y i j) =ᶠ[𝓝 x]
      D (D u (EuclideanSpace.basisFun (Fin n) ℝ j)) (EuclideanSpace.basisFun (Fin n) ℝ i) := by
  have hn : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 2 u y :=
    (hu.of_le (show (2 : ℕ∞ω) ≤ 3 by norm_num)).eventually (by norm_num)
  filter_upwards [hn] with y hy
  exact bilinearIteratedFDerivTwo_eq_fderiv_apply_at hy _ _

private theorem D_log {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {x : E} (hf : DifferentiableAt ℝ f x) (hx : f x ≠ 0) (v : E) :
    D (fun y => Real.log (f y)) v x = D f v x / f x := by
  have h := congrArg (fun L : E →L[ℝ] ℝ => L v) (hf.hasFDerivAt.log hx).fderiv
  simpa [D, div_eq_mul_inv, mul_comm] using h

private theorem D_log_second {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ}
    {x : E} (hf : ContDiffAt ℝ 2 f x) (hx : f x ≠ 0) (v : E) :
    D (D (fun y => Real.log (f y)) v) v x = D (D f v) v x / f x - (D f v x) ^ 2 / (f x) ^ 2 := by
  have h0 : DifferentiableAt ℝ f x := hf.differentiableAt (by norm_num)
  have h1 : DifferentiableAt ℝ (D f v) x :=
    (smooth_D_at (k := 1) hf v).differentiableAt one_ne_zero
  have he : D (fun y => Real.log (f y)) v =ᶠ[𝓝 x] (fun y => D f v y / f y) := by
    have hn : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 2 f y := hf.eventually (by norm_num)
    filter_upwards [hn, h0.continuousAt.eventually_ne hx] with y hy hy0
    exact D_log (hy.differentiableAt (by norm_num)) hy0 v
  have hI := (hasDerivAt_inv hx).comp_hasFDerivAt x h0.hasFDerivAt
  have hm := h1.hasFDerivAt.mul hI
  rw [(D_congr he v).eq_of_nhds]
  change fderiv ℝ (fun y => D f v y / f y) x v = _
  simp_rw [div_eq_mul_inv]
  change (fderiv ℝ (D f v * ((fun y : ℝ => y⁻¹) ∘ f)) x) v = _
  rw [hm.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul]
  dsimp [D, Function.comp_def]
  ring

private theorem D_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℝ} {x : E} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (v : E) :
    D (fun y => f y + g y) v x = D f v x + D g v x := by
  change fderiv ℝ (fun y => f y + g y) x v = _
  rw [fderiv_fun_add hf hg]
  rfl

private theorem D_add_second {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x)
    (hg : ContDiffAt ℝ 2 g x) (v : E) :
    D (D (fun y => f y + g y) v) v x = D (D f v) v x + D (D g v) v x := by
  have he : D (fun y => f y + g y) v =ᶠ[𝓝 x] (fun y => D f v y + D g v y) := by
    filter_upwards [hf.eventually (by norm_num), hg.eventually (by norm_num)] with y hy hz
    exact D_add (hy.differentiableAt (by norm_num)) (hz.differentiableAt (by norm_num)) v
  rw [(D_congr he v).eq_of_nhds]
  exact D_add ((smooth_D_at (k:=1) hf v).differentiableAt one_ne_zero)
    ((smooth_D_at (k:=1) hg v).differentiableAt one_ne_zero) v

private theorem D_half_square {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ}
    {x : E} (hf : DifferentiableAt ℝ f x) (v : E) :
    D (fun y => (1 / 2 : ℝ) * (f y) ^ 2) v x = f x * D f v x := by
  have hd := (hf.hasFDerivAt.mul hf.hasFDerivAt).const_mul (1 / 2 : ℝ)
  change (fderiv ℝ (fun y => (1 / 2 : ℝ) * (f y) ^ 2) x) v = _
  simp_rw [pow_two]
  change (fderiv ℝ (fun y => (1 / 2 : ℝ) * (f * f) y) x) v = _
  rw [hd.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul]
  dsimp [D]
  ring

private theorem D_half_square_second {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) (v : E) :
    D (D (fun y => (1 / 2 : ℝ) * (f y) ^ 2) v) v x = (D f v x) ^ 2 + f x * D (D f v) v x := by
  have he : D (fun y => (1 / 2 : ℝ) * (f y) ^ 2) v =ᶠ[𝓝 x] (fun y => f y * D f v y) := by
    filter_upwards [hf.eventually (by norm_num)] with y hy
    exact D_half_square (hy.differentiableAt (by norm_num)) v
  rw [(D_congr he v).eq_of_nhds]
  have hd :=
    (hf.differentiableAt (by norm_num)).hasFDerivAt.mul
      ((smooth_D_at (k := 1) hf v).differentiableAt one_ne_zero).hasFDerivAt
  change (fderiv ℝ (f * D f v) x) v = _
  rw [hd.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul]
  dsimp [D]
  ring

/-- First and second directional derivative inequalities at a logarithmic local maximum. -/
theorem logarithmic_maximum_conditions {n : ℕ} {a u b : EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanSpace ℝ (Fin n)} (ha : ContDiffAt ℝ 2 a x) (hu : ContDiffAt ℝ 2 u x)
    (hb : ContDiffAt ℝ 2 b x) (hax : 0 < a x) (hux : u x < 0)
    (hmax : IsLocalMax (fun y => Real.log (a y) + Real.log (u y) + (1 / 2 : ℝ) * (b y) ^ 2) x) :
    (∀ v, fderiv ℝ a x v / a x + fderiv ℝ u x v / u x + b x * fderiv ℝ b x v = 0) ∧
      ∀ i : Fin n,
        let v := EuclideanSpace.basisFun (Fin n) ℝ i
        fderiv ℝ (fun y => fderiv ℝ a y v) x v / a x - (fderiv ℝ a x v) ^ 2 / (a x) ^ 2 +
                  fderiv ℝ (fun y => fderiv ℝ u y v) x v / u x -
                (fderiv ℝ u x v) ^ 2 / (u x) ^ 2 +
              (fderiv ℝ b x v) ^ 2 +
            b x * fderiv ℝ (fun y => fderiv ℝ b y v) x v ≤
          0 := by
  let F := fun y => Real.log (a y) + Real.log (u y) + (1 / 2 : ℝ) * (b y) ^ 2
  have hFa : ContDiffAt ℝ 2 (fun y => Real.log (a y)) x := ha.log hax.ne'
  have hFu : ContDiffAt ℝ 2 (fun y => Real.log (u y)) x := hu.log hux.ne
  have hFb : ContDiffAt ℝ 2 (fun y => (1 / 2 : ℝ) * (b y) ^ 2) x :=
    contDiffAt_const.mul (hb.pow 2)
  have hF : ContDiffAt ℝ 2 F x := (hFa.add hFu).add hFb
  have hfirst (v) : D F v x = D a v x / a x + D u v x / u x + b x * D b v x := by
    rw [D_add ((hFa.add hFu).differentiableAt (by norm_num))
        (hFb.differentiableAt (by norm_num)),
      D_add (hFa.differentiableAt (by norm_num)) (hFu.differentiableAt (by norm_num)),
      D_log (ha.differentiableAt (by norm_num)) hax.ne',
      D_log (hu.differentiableAt (by norm_num)) hux.ne,
      D_half_square (hb.differentiableAt (by norm_num))]
  constructor
  · intro v
    rw [← hfirst v]
    change fderiv ℝ F x v = 0
    rw [hmax.fderiv_eq_zero]
    rfl
  · intro i
    dsimp only
    let v := EuclideanSpace.basisFun (Fin n) ℝ i
    have hp :=
      posSemidef_hessianMatrix_of_upper_touch (u := fun _ => -F x) (ψ := fun y => -F y)
        (convexOn_const _ convex_univ) hF.neg rfl (hmax.mono fun _ hy => neg_le_neg hy)
    have hi : 0 ≤ hessianMatrix (fun y => -F y) x i i := hp.diag_nonneg
    have hneg : hessianMatrix (fun y => -F y) x i i = -hessianMatrix F x i i := by
      simp only [hessianMatrix, bilinearIteratedFDerivTwo_eq_iteratedFDeriv]
      rw [show (fun y => -F y) = -F from rfl, iteratedFDeriv_neg_apply]
      rfl
    rw [hneg] at hi
    have hh : D (D F v) v x ≤ 0 := by
      change fderiv ℝ (fun y => fderiv ℝ F y v) x v ≤ 0
      rw [← bilinearIteratedFDerivTwo_eq_fderiv_apply_at hF v v]
      exact neg_nonneg.mp hi
    change
      D (D F (EuclideanSpace.basisFun (Fin n) ℝ i)) (EuclideanSpace.basisFun (Fin n) ℝ i) x ≤
        0 at hh
    dsimp only [F] at hh
    rw [D_add_second (hFa.add hFu) hFb, D_add_second hFa hFu, D_log_second ha hax.ne',
      D_log_second hu hux.ne, D_half_square_second hb] at hh
    linarith

/-- Third and fourth directional identities for the Hessian of a locally `C⁴` function. -/
private theorem hessian_jet_identification {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanSpace ℝ (Fin n)} (hu : ContDiffAt ℝ 4 u x) (k : Fin n) :
    let e := EuclideanSpace.basisFun (Fin n) ℝ
    let M := hessianMatrix u
    let a := fun y => M y k k
    let b := D u (e k)
    let S := fun i j => D (fun y => M y i j) (e k) x
    (∀ i j, S i j = S j i) ∧
      ∀ i,
        D a (e i) x = S k i ∧
          D (D a (e i)) (e i) x = D (D (fun y => M y i i) (e k)) (e k) x ∧
            D b (e i) x = M x i k ∧ D (D b (e i)) (e i) x = S i i := by
  dsimp only
  let e := EuclideanSpace.basisFun (Fin n) ℝ
  have h3 : ContDiffAt ℝ 3 u x := hu.of_le (by norm_num)
  have h2 : ContDiffAt ℝ 2 u x := hu.of_le (by norm_num)
  have he (i j) := hessian_entry_near h3 i j
  constructor
  · intro i j
    have hg : (fun y => hessianMatrix u y i j) =ᶠ[𝓝 x] (fun y => hessianMatrix u y j i) := by
      filter_upwards [h2.eventually (by norm_num)] with y hy
      exact bilinearIteratedFDerivTwo_symm_at hy _ _
    exact (D_congr hg (e k)).eq_of_nhds
  · intro i
    refine ⟨?_, ?_, ?_, ?_⟩
    · calc
        _ = D (D (D u (e k)) (e k)) (e i) x := (D_congr (he k k) (e i)).eq_of_nhds
        _ = D (D (D u (e i)) (e k)) (e k) x := fderiv_fderiv_fderiv_apply_comm_at h3 (e k) (e i)
        _ = _ := (D_congr (he k i) (e k)).eq_of_nhds.symm
    · calc
        _ = D (D (D (D u (e k)) (e k)) (e i)) (e i) x :=
          (D_congr (D_congr (he k k) (e i)) (e i)).eq_of_nhds
        _ = D (D (D (D u (e i)) (e i)) (e k)) (e k) x :=
          fderiv_fourth_pair_comm_at hu (e k) (e k) (e i) (e i)
        _ = _ := (D_congr (D_congr (he i i) (e k)) (e k)).eq_of_nhds.symm
    · exact (bilinearIteratedFDerivTwo_eq_fderiv_apply_at h2 (e i) (e k)).symm
    · calc
        _ = D (D (D u (e i)) (e i)) (e k) x :=
          (fderiv_fderiv_fderiv_apply_comm_at h3 (e i) (e k)).symm
        _ = _ := (D_congr (he i i) (e k)).eq_of_nhds.symm

private theorem matrix_entry_second {ι G : Type*} [Fintype ι]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {M : G → Matrix ι ι ℝ} {x : G} (hM : ContDiffAt ℝ 2 M x)
    (v : G) (i j : ι) :
    (fderiv ℝ (fun y => fderiv ℝ M y v) x v) i j =
      D (D (fun y => M y i j) v) v x := by
  have hd : DifferentiableAt ℝ (fun y => fderiv ℝ M y v) x :=
    ((hM.fderiv_right (m:=1) (by norm_num)).differentiableAt one_ne_zero).clm_apply
      (differentiableAt_const v)
  have he : (fun y => (fderiv ℝ M y v) i j) =ᶠ[𝓝 x] D (fun y => M y i j) v := by
    filter_upwards [hM.eventually (by norm_num)] with y hy
    exact matrix_entry_derivative (hy.differentiableAt (by norm_num)) v i j
  exact (matrix_entry_derivative hd v i j).trans ((D_congr he v).eq_of_nhds)

/-- Diagonal-coordinate forms of the two differentiated constant-determinant equations. -/
private theorem classical_diagonal_traces_core {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanSpace ℝ (Fin n)} {c : ℝ} (hu : ContDiffAt ℝ 4 u x) (hc : c ≠ 0)
    (heq : ∀ᶠ y in 𝓝 x, (hessianMatrix u y).det = c) (hp : (hessianMatrix u x).PosDef)
    (hdiag : hessianMatrix u x = Matrix.diagonal (fun i => hessianMatrix u x i i)) (k : Fin n)
    (hs :
      ∀ i j,
        D (fun y => hessianMatrix u y i j) (EuclideanSpace.basisFun (Fin n) ℝ k) x =
          D (fun y => hessianMatrix u y j i) (EuclideanSpace.basisFun (Fin n) ℝ k) x) :
    let e := EuclideanSpace.basisFun (Fin n) ℝ
    let M := hessianMatrix u
    let lam := fun i => M x i i
    let S := fun i j => D (fun y => M y i j) (e k) x
    let Q := fun i => D (D (fun y => M y i i) (e k)) (e k) x
    (∀ i, 0 < lam i) ∧
      (∀ i j, S i j = S j i) ∧
        (∑ i, S i i / lam i = 0) ∧ ∑ i, Q i / lam i = ∑ i, ∑ j, S i j ^ 2 / (lam i * lam j) := by
  dsimp only
  let e := EuclideanSpace.basisFun (Fin n) ℝ
  let M := hessianMatrix u
  let lam := fun i => M x i i
  let A := fderiv ℝ M x (e k)
  have hM2 : ContDiffAt ℝ 2 M x := contDiffAt_hessianMatrix (k := 2) hu
  have hM0 : DifferentiableAt ℝ M x := hM2.differentiableAt (by norm_num)
  have hnz (i) : lam i ≠ 0 := hp.diag_pos.ne'
  have hi : (M x)⁻¹ = Matrix.diagonal (fun i => (lam i)⁻¹) := by
    apply Matrix.inv_eq_left_inv
    rw [show M x = Matrix.diagonal lam from hdiag, Matrix.diagonal_mul_diagonal]
    apply Matrix.ext
    intro i j
    by_cases h : i = j
    · subst j; simp [hnz]
    · simp [h]
  have hdata := classical_hessian_trace_identities hu hc heq
  have hfirst := hdata.1 (e k)
  have hsecond := hdata.2 (e k) (e k)
  have htrace :
    ((M x)⁻¹ * fderiv ℝ M x (e k)).trace = ∑ i, D (fun y => M y i i) (e k) x / lam i := by
    rw [hi]
    simp only [Matrix.trace, Matrix.diag, Matrix.diagonal_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [matrix_entry_derivative hM0]
    ring
  have htrace2 :
    ((M x)⁻¹ * fderiv ℝ (fun y => fderiv ℝ M y (e k)) x (e k)).trace =
      ∑ i, D (D (fun y => M y i i) (e k)) (e k) x / lam i := by
    rw [hi]
    simp only [Matrix.trace, Matrix.diag, Matrix.diagonal_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [matrix_entry_second hM2]
    ring
  have hentry (i j) : ((M x)⁻¹ * A * (M x)⁻¹) i j = (lam i)⁻¹ * A i j * (lam j)⁻¹ := by
    rw [hi, Matrix.mul_diagonal, Matrix.diagonal_mul]
  have henergy :
    ((M x)⁻¹ * A * (M x)⁻¹ * A).trace =
      ∑ i, ∑ j, (D (fun y => M y i j) (e k) x) ^ 2 / (lam i * lam j) := by
    simp only [Matrix.trace, Matrix.diag]
    apply Finset.sum_congr rfl
    intro i _
    rw [Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [hentry]
    dsimp [A]
    rw [matrix_entry_derivative hM0, matrix_entry_derivative hM0, hs j i]
    ring
  refine ⟨fun i => hp.diag_pos, hs, ?_, ?_⟩
  · exact htrace.symm.trans hfirst
  · exact htrace2.symm.trans (hsecond.trans henergy)

/-- Savin Proposition 4.1, proof (10)–(15): the directional height–Hessian bound
at a logarithmic local maximum in diagonal coordinates. The determinant is only
required to be locally constant and nonzero; the bound is independent of its value. -/
theorem bound_of_diagonal_local_max {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanSpace ℝ (Fin n)} {c : ℝ} (hu : ContDiffAt ℝ 4 u x) (hc : c ≠ 0)
    (heq : ∀ᶠ y in 𝓝 x, (hessianMatrix u y).det = c) (hp : (hessianMatrix u x).PosDef)
    (hdiag : hessianMatrix u x = Matrix.diagonal (fun i => hessianMatrix u x i i))
    (hneg : u x < 0) (k : Fin n)
    (hmax :
      IsLocalMax
        (fun y =>
          Real.log (hessianMatrix u y k k) + Real.log (u y) +
            (1 / 2 : ℝ) * (fderiv ℝ u y (EuclideanSpace.basisFun (Fin n) ℝ k)) ^ 2)
        x) :
    hessianMatrix u x k k * (-u x) ≤
      (n : ℝ) + |fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ k)| := by
  let e := EuclideanSpace.basisFun (Fin n) ℝ
  let M := hessianMatrix u
  let lam := fun i => M x i i
  let g := fun i => D u (e i) x
  let S := fun i j => D (fun y => M y i j) (e k) x
  let Q := fun i => D (D (fun y => M y i i) (e k)) (e k) x
  let a := fun y => M y k k
  let b := D u (e k)
  have hJ := hessian_jet_identification hu k
  dsimp only at hJ
  have hP := classical_diagonal_traces_core hu hc heq hp hdiag k hJ.1
  dsimp only at hP
  have hlam (i) : 0 < lam i := hP.1 i
  have hnz (i) : lam i ≠ 0 := (hlam i).ne'
  have hMDiag : M x = Matrix.diagonal lam := hdiag
  have hM2 : ContDiffAt ℝ 2 M x := contDiffAt_hessianMatrix (k := 2) hu
  have ha : ContDiffAt ℝ 2 a x := contDiffAt_pi.mp (contDiffAt_pi.mp hM2 k) k
  have hb : ContDiffAt ℝ 2 b x := smooth_D_at (k := 2) (hu.of_le (by norm_num)) (e k)
  have hu2 : ContDiffAt ℝ 2 u x := hu.of_le (by norm_num)
  have hC := logarithmic_maximum_conditions ha hu2 hb (hlam k) hneg hmax
  have huD (i) : D (D u (e i)) (e i) x = lam i :=
    (bilinearIteratedFDerivTwo_eq_fderiv_apply_at hu2 (e i) (e i)).symm
  have hik (i) : M x i k = if i = k then lam k else 0 := by
    by_cases h : i = k
    · subst i; simp only [ite_true]; rfl
    · rw [hMDiag]; simp [h]
  have hcritical (i) (hi : i ≠ k) : S k i / lam k + g i / u x = 0 := by
    have hh := hC.1 (e i)
    change D a (e i) x / a x + D u (e i) x / u x + b x * D b (e i) x = 0 at hh
    have hA : D a (e i) x = S k i := (hJ.2 i).1
    have hB : D b (e i) x = M x i k := (hJ.2 i).2.2.1
    rw [hA, hB, hik i, ite_eq_right hi, mul_zero, add_zero] at hh
    exact hh
  have hterm (i) :
    Q i / (lam k * lam i) - S k i ^ 2 / (lam k ^ 2 * lam i) + 1 / u x -
            g i ^ 2 / (lam i * (u x) ^ 2) +
          (if i = k then lam k else 0) +
        g k * (S i i / lam i) ≤
      0 := by
    have hh := hC.2 i
    dsimp only at hh
    change
      D (D a (e i)) (e i) x / a x - (D a (e i) x) ^ 2 / (a x) ^ 2 +
                D (D u (e i)) (e i) x / u x -
              (D u (e i) x) ^ 2 / (u x) ^ 2 +
            (D b (e i) x) ^ 2 +
          b x * D (D b (e i)) (e i) x ≤
        0 at hh
    have hA : D a (e i) x = S k i := (hJ.2 i).1
    have hQ : D (D a (e i)) (e i) x = Q i := (hJ.2 i).2.1
    have hB : D b (e i) x = M x i k := (hJ.2 i).2.2.1
    have hS : D (D b (e i)) (e i) x = S i i := (hJ.2 i).2.2.2
    rw [hQ, hA, huD, hB, hS, hik i] at hh
    have hs := div_nonpos_of_nonpos_of_nonneg hh (hlam i).le
    by_cases hi : i = k
    · subst i
      simp only [ite_true] at hs ⊢
      have hnk : M x k k ≠ 0 := hp.diag_pos.ne'
      convert hs using 1
      dsimp only [a, b, g, lam, e]
      field_simp [hnk, hneg.ne]
    · simp only [ite_eq_right hi] at hs ⊢
      have hnk : M x k k ≠ 0 := hp.diag_pos.ne'
      have hni : M x i i ≠ 0 := hp.diag_pos.ne'
      convert hs using 1
      dsimp only [a, b, g, lam, e]
      field_simp [hnk, hni, hneg.ne]
      ring
  have hqsum : (∑ i, Q i / (lam k * lam i)) = (∑ i, Q i / lam i) / lam k := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    field_simp
  have hsum := Finset.sum_nonpos (s := Finset.univ) (fun i _ => hterm i)
  have hid : (∑ i : Fin n, if i = k then lam k else 0) = lam k := by simp
  have hexpand :
    (∑ i,
        (Q i / (lam k * lam i) - S k i ^ 2 / (lam k ^ 2 * lam i) + 1 / u x -
              g i ^ 2 / (lam i * (u x) ^ 2) +
            (if i = k then lam k else 0) +
          g k * (S i i / lam i))) =
      (∑ i, Q i / lam i) / lam k - (∑ i, S k i ^ 2 / (lam k ^ 2 * lam i)) +
              (Fintype.card (Fin n) : ℝ) / u x -
            (∑ i, g i ^ 2 / (lam i * (u x) ^ 2)) +
          g k * (∑ i, S i i / lam i) +
        lam k := by
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [hqsum, hid, ← Finset.mul_sum]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  rw [hexpand] at hsum
  have hbound :=
    directional_bound k lam g Q S (u x) hlam hneg hP.2.1 hP.2.2.1 hP.2.2.2 hcritical hsum
  simpa only [Fintype.card_fin] using hbound



section Coordinates
open Set Metric Matrix Module

/--
An invertible matrix gives a continuous linear coordinate equivalence with that SAME matrix. -/
private theorem exists_equiv_of_isUnit {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : IsUnit A) :
    ∃ L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n),
      (∀ y, L y = Matrix.toEuclideanLin A y) ∧
        LinearMap.toMatrix (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
            (EuclideanSpace.basisFun (Fin n) ℝ).toBasis L.toLinearMap =
          A := by
  classical
  obtain ⟨a, rfl⟩ := hA
  let e := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let L := (Matrix.toLinOfInv e e a.val_inv a.inv_val).toContinuousLinearEquiv
  refine ⟨L, ?_, ?_⟩
  · intro y
    rfl
  · change LinearMap.toMatrix e e (Matrix.toLin e e (a : Matrix (Fin n) (Fin n) ℝ)) = a
    exact LinearMap.toMatrix_toLin e e a

/-- The actual positive Hessian generates axis-preserving diagonal coordinates.
The estimate concerns the ORIGINAL given classical function and local logarithmic maximum. -/
theorem bound_of_local_max {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanSpace ℝ (Fin n)} {c : ℝ} (hu : ContDiffAt ℝ 4 u x) (hc : c ≠ 0)
    (heq : ∀ᶠ y in 𝓝 x, (hessianMatrix u y).det = c) (hp : (hessianMatrix u x).PosDef)
    (hneg : u x < 0) (k : Fin n)
    (hmax :
      IsLocalMax
        (fun y =>
          Real.log (hessianMatrix u y k k) + Real.log (u y) +
            (1 / 2 : ℝ) * (fderiv ℝ u y (EuclideanSpace.basisFun (Fin n) ℝ k)) ^ 2)
        x) :
    hessianMatrix u x k k * (-u x) ≤
      (n : ℝ) + |fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ k)| := by
  classical
  let E := EuclideanSpace ℝ (Fin n)
  let e := EuclideanSpace.basisFun (Fin n) ℝ
  obtain ⟨A, d, hA, hAk, hd, hdiag⟩ :=
    exists_diagonal_frame_fixing_axis (hessianMatrix u x) hp k
  obtain ⟨L, hL, hmat⟩ := exists_equiv_of_isUnit hA
  have haxis : L (e k) = e k := by
    rw [hL]
    change Matrix.toLpLin 2 2 A (e k) = e k
    rw [Matrix.toLpLin_apply]
    simp only [e, EuclideanSpace.basisFun_apply, PiLp.ofLp_single]
    exact congrArg (WithLp.toLp 2) hAk
  let T : E → E := fun y => L y + x
  let V : E → ℝ := fun y => u (T y)
  have hT (y : E) : HasFDerivAt T (L : E →L[ℝ] E) y := L.hasFDerivAt.add_const x
  have hT0 : T 0 = x := by simp [T]
  have ht : Tendsto T (𝓝 0) (𝓝 x) := by
    have htt := (hT 0).continuousAt
    change Tendsto T (𝓝 0) (𝓝 (T 0)) at htt
    rwa [hT0] at htt
  have hv4 : ContDiffAt ℝ 4 V 0 := by
    exact (hT0 ▸ hu).comp 0 (L.contDiff.add contDiff_const).contDiffAt
  have h2 : ∀ᶠ z in 𝓝 x, ContDiffAt ℝ 2 u z :=
    (hu.of_le (show (2 : ℕ∞ω) ≤ 4 by norm_num)).eventually (by norm_num)
  have hVmatrix : ∀ᶠ y in 𝓝 (0 : E), hessianMatrix V y = Aᵀ * hessianMatrix u (T y) * A := by
    filter_upwards [ht.eventually h2] with y hy
    have hh := hessianMatrix_comp_affine_at L x y hy
    dsimp only at hh
    rw [hmat] at hh
    exact hh
  have hV0 : hessianMatrix V 0 = Matrix.diagonal d := by
    have hh := hVmatrix.self_of_nhds
    rw [hT0, hdiag] at hh
    exact hh
  have hvp : (hessianMatrix V 0).PosDef := by
    rw [hV0]
    exact Matrix.posDef_diagonal_iff.mpr hd
  have hvdiag : hessianMatrix V 0 = Matrix.diagonal (fun i => hessianMatrix V 0 i i) := by
    rw [hV0]
    simp
  have hdetA : A.det ≠ 0 := (Matrix.isUnit_iff_isUnit_det A).mp hA |>.ne_zero
  have hvdet : ∀ᶠ y in 𝓝 (0 : E), (hessianMatrix V y).det = A.det * A.det * c := by
    filter_upwards [hVmatrix, ht.eventually heq] with y hy hz
    rw [hy, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hz]
    ring
  have hsame :
    ∀ᶠ y in 𝓝 (0 : E),
      hessianMatrix V y k k = hessianMatrix u (T y) k k ∧
        fderiv ℝ V y (e k) = fderiv ℝ u (T y) (e k) := by
    filter_upwards [ht.eventually h2] with y hy
    constructor
    · change
        bilinearIteratedFDerivTwo ℝ (fun z => u (L z + x)) y (e k) (e k) =
          bilinearIteratedFDerivTwo ℝ u (L y + x) (e k) (e k)
      rw [bilinearIteratedFDerivTwo_comp_affine_at L x y _ _ hy, haxis]
    · change ContDiffAt ℝ 2 u (T y) at hy
      have hf :=
        congrArg (fun f : E →L[ℝ] ℝ => f (e k))
          ((hy.differentiableAt (by norm_num)).hasFDerivAt.comp y (hT y)).fderiv
      change fderiv ℝ V y (e k) = fderiv ℝ u (T y) (L (e k)) at hf
      rw [haxis] at hf
      exact hf
  have hmaxV :
    IsLocalMax
      (fun y =>
        Real.log (hessianMatrix V y k k) + Real.log (V y) +
          (1 / 2 : ℝ) * (fderiv ℝ V y (e k)) ^ 2)
      0 := by
    have hm := ht.eventually hmax
    filter_upwards [hm, hsame] with y hy hs
    dsimp only [V]
    rw [hs.1, hs.2]
    have hs0 := hsame.self_of_nhds
    rw [hs0.1, hs0.2, hT0]
    exact hy
  have hvneg : V 0 < 0 := by simpa only [V, hT0] using hneg
  have hb :=
    Pogorelov.bound_of_diagonal_local_max hv4 (mul_ne_zero (mul_ne_zero hdetA hdetA) hc) hvdet
      hvp hvdiag hvneg k hmaxV
  have hs0 := hsame.self_of_nhds
  rw [hs0.1, hs0.2] at hb
  simpa only [V, hT0] using hb

/-- Actual compactness chooses the maximizing point for a GIVEN classical zero-boundary
solution and generates the derivative cap and height-Hessian estimate. Empty domains allowed. -/
theorem exists_directional_height_bound {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {Ω : Set (EuclideanSpace ℝ (Fin n))} {c : ℝ} (hΩ : IsOpen Ω)
    (hbounded : Bornology.IsBounded Ω) (hu4 : ∀ x ∈ Ω, ContDiffAt ℝ 4 u x)
    (hu2 : ∀ x ∈ closure Ω, ContDiffAt ℝ 2 u x) (hc : c ≠ 0)
    (heq : ∀ x ∈ Ω, (hessianMatrix u x).det = c) (hp : ∀ x ∈ Ω, (hessianMatrix u x).PosDef)
    (hneg : ∀ x ∈ Ω, u x < 0) (hbd : ∀ x ∈ frontier Ω, u x = 0) :
    ∃ B : ℝ,
      0 < B ∧
        (∀ x ∈ closure Ω, ‖fderiv ℝ u x‖ ≤ B) ∧
          ∀ x ∈ Ω,
            ∀ k : Fin n,
              hessianMatrix u x k k * (-u x) ≤ ((n : ℝ) + B) * Real.exp ((1 / 2 : ℝ) * B ^ 2) := by
  classical
  let E := EuclideanSpace ℝ (Fin n)
  let e := EuclideanSpace.basisFun (Fin n) ℝ
  have hK : IsCompact (closure Ω) := hbounded.isCompact_closure
  have hdf : ContinuousOn (fderiv ℝ u) (closure Ω) := by
    intro y hy
    exact ((hu2 y hy).fderiv_right (m := 1) (by norm_num)).continuousAt.continuousWithinAt
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hdf
  let B := max C 1
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hBd (y : E) (hy : y ∈ closure Ω) : ‖fderiv ℝ u y‖ ≤ B :=
    (hC y hy).trans (le_max_left _ _)
  refine ⟨B, hB, hBd, ?_⟩
  intro x hx k
  let a : E → ℝ := fun y => hessianMatrix u y k k
  let b : E → ℝ := fun y => fderiv ℝ u y (e k)
  let M : E → ℝ := fun y => a y * (-u y) * Real.exp ((1 / 2 : ℝ) * (b y) ^ 2)
  have hbB (y : E) (hy : y ∈ closure Ω) : |b y| ≤ B := by
    calc
      |b y| = ‖fderiv ℝ u y (e k)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖fderiv ℝ u y‖ * ‖e k‖ := (fderiv ℝ u y).le_opNorm _
      _ = ‖fderiv ℝ u y‖ := by rw [e.orthonormal.norm_eq_one, mul_one]
      _ ≤ B := hBd y hy
  have ha (y : E) (hy : y ∈ Ω) : 0 < a y := (hp y hy).diag_pos
  have hMp (y : E) (hy : y ∈ Ω) : 0 < M y :=
    mul_pos (mul_pos (ha y hy) (neg_pos.mpr (hneg y hy))) (Real.exp_pos _)
  have hMc : ContinuousOn M (closure Ω) := by
    intro y hy
    have hH : ContDiffAt ℝ 0 (hessianMatrix u) y :=
      contDiffAt_hessianMatrix (k := 0) (by simpa using hu2 y hy)
    have hac : ContinuousAt a y := (contDiffAt_pi.mp (contDiffAt_pi.mp hH k) k).continuousAt
    have hbc : ContinuousAt b y :=
      (((hu2 y hy).fderiv_right (m := 1) (by norm_num)).continuousAt).clm_apply
        continuousAt_const
    have he : ContinuousAt (fun z => Real.exp ((1 / 2 : ℝ) * (b z) ^ 2)) y :=
      Real.continuous_exp.continuousAt.comp ((hbc.pow 2).const_mul (1 / 2 : ℝ))
    exact ((hac.mul (hu2 y hy).continuousAt.neg).mul he).continuousWithinAt
  obtain ⟨z, hz, hmax⟩ := hK.exists_isMaxOn ⟨x, subset_closure hx⟩ hMc
  have hzΩ : z ∈ Ω := by
    by_contra hn
    have hzf : z ∈ frontier Ω := by rw [hΩ.frontier_eq]; exact ⟨hz, hn⟩
    have hzero : M z = 0 := by simp [M, hbd z hzf]
    have hh := hmax (subset_closure hx)
    rw [hzero] at hh
    exact (hMp x hx).not_ge hh
  have hlog (y : E) (hy : y ∈ Ω) :
    Real.log (M y) = Real.log (a y) + Real.log (u y) + (1 / 2 : ℝ) * (b y) ^ 2 := by
    dsimp only [M]
    rw [Real.log_mul (mul_ne_zero (ha y hy).ne' (neg_ne_zero.mpr (hneg y hy).ne))
        (Real.exp_ne_zero _),
      Real.log_mul (ha y hy).ne' (neg_ne_zero.mpr (hneg y hy).ne), Real.log_exp,
      Real.log_neg_eq_log]
  have hlogmax :
    IsLocalMax (fun y => Real.log (a y) + Real.log (u y) + (1 / 2 : ℝ) * (b y) ^ 2) z := by
    filter_upwards [hΩ.mem_nhds hzΩ] with y hy
    rw [← hlog y hy, ← hlog z hzΩ]
    exact Real.log_le_log (hMp y hy) (hmax (subset_closure hy))
  have heqz : ∀ᶠ y in 𝓝 z, (hessianMatrix u y).det = c := by
    filter_upwards [hΩ.mem_nhds hzΩ] with y hy
    exact heq y hy
  have hb := bound_of_local_max (hu4 z hzΩ) hc heqz (hp z hzΩ) (hneg z hzΩ) k hlogmax
  have hhz : a z * (-u z) ≤ (n : ℝ) + B :=
    hb.trans (by simpa only [add_comm] using add_le_add_left (hbB z hz) (n : ℝ))
  have hs : (b z) ^ 2 ≤ B ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (b z)) hB.le).mpr (hbB z hz)
  have hEz : Real.exp ((1 / 2 : ℝ) * (b z) ^ 2) ≤ Real.exp ((1 / 2 : ℝ) * B ^ 2) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hs (by norm_num))
  have hMz : M z ≤ ((n : ℝ) + B) * Real.exp ((1 / 2 : ℝ) * B ^ 2) :=
    mul_le_mul hhz hEz (Real.exp_pos _).le (by positivity)
  have hMx : a x * (-u x) ≤ M x := by
    have hE : 1 ≤ Real.exp ((1 / 2 : ℝ) * (b x) ^ 2) := Real.one_le_exp (by positivity)
    have h :=
      mul_le_mul_of_nonneg_left hE (mul_nonneg (ha x hx).le (neg_nonneg.mpr (hneg x hx).le))
    simpa only [mul_one] using h
  exact hMx.trans ((hmax (subset_closure hx)).trans hMz)

private theorem weighted_norm_le_of_diag {n : ℕ} {H : Matrix (Fin n) (Fin n) ℝ}
    (hH : H.PosSemidef) {s C : ℝ} (hs : 0 ≤ s) (hC : 0 ≤ C) (hd : ∀ i, H i i * s ≤ C) :
    ‖H‖ * s ≤ C := by
  classical
  have he (i j : Fin n) : |s * H i j| ≤ C := by
    let ei : Fin n → ℝ := Pi.single i 1
    let ej : Fin n → ℝ := Pi.single j 1
    have hp := hH.dotProduct_mulVec_nonneg (ei + ej)
    have hm := hH.dotProduct_mulVec_nonneg (ei - ej)
    have hsym : H j i = H i j := by simpa using hH.isHermitian.apply i j
    have hp' : 0 ≤ H i i + H j j + 2 * H i j := by
      simpa [ei, ej, star_trivial, add_dotProduct, dotProduct_add, mulVec_add,
        dotProduct_single, mulVec_single, hsym, add_assoc, add_comm, add_left_comm,
        two_mul] using hp
    have hm' : 0 ≤ H i i + H j j - 2 * H i j := by
      simpa [ei, ej, star_trivial, sub_dotProduct, dotProduct_sub, mulVec_sub, mulVec_add,
        mulVec_neg, dotProduct_single, mulVec_single, hsym, sub_eq_add_neg, add_assoc, add_comm,
        add_left_comm, two_mul] using hm
    rw [abs_le]
    constructor <;> nlinarith [hd i, hd j, mul_nonneg hp' hs, mul_nonneg hm' hs]
  have hn : ‖s • H‖ ≤ C :=
    (Matrix.norm_le_iff hC).mpr
      (by
        intro i j
        simpa only [Matrix.smul_apply, smul_eq_mul, Real.norm_eq_abs] using he i j)
  simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs, mul_comm] using hn

/-- Full elementwise Hessian height bound and actual compact interior caps are GENERATED
for the SAME GIVEN classical solution, without source caps, maximizers or diagonal coordinates. -/
theorem exists_hessian_height_and_interior_bound {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {Ω : Set (EuclideanSpace ℝ (Fin n))} {c : ℝ} (hΩ : IsOpen Ω)
    (hbounded : Bornology.IsBounded Ω) (hu4 : ∀ x ∈ Ω, ContDiffAt ℝ 4 u x)
    (hu2 : ∀ x ∈ closure Ω, ContDiffAt ℝ 2 u x) (hc : c ≠ 0)
    (heq : ∀ x ∈ Ω, (hessianMatrix u x).det = c) (hp : ∀ x ∈ Ω, (hessianMatrix u x).PosDef)
    (hneg : ∀ x ∈ Ω, u x < 0) (hbd : ∀ x ∈ frontier Ω, u x = 0) :
    ∃ B : ℝ,
      0 < B ∧
        (∀ x ∈ closure Ω, ‖fderiv ℝ u x‖ ≤ B) ∧
          (∀ x ∈ Ω,
              ‖hessianMatrix u x‖ * (-u x) ≤ ((n : ℝ) + B) * Real.exp ((1 / 2 : ℝ) * B ^ 2)) ∧
            ∀ K : Set (EuclideanSpace ℝ (Fin n)),
              IsCompact K → K ⊆ Ω → ∃ R : ℝ, 0 < R ∧ ∀ x ∈ K, ‖hessianMatrix u x‖ ≤ R := by
  obtain ⟨B, hB, hBd, hdiag⟩ :=
    exists_directional_height_bound hΩ hbounded hu4 hu2 hc heq hp hneg hbd
  let C := ((n : ℝ) + B) * Real.exp ((1 / 2 : ℝ) * B ^ 2)
  have hC : 0 < C := mul_pos (by positivity) (Real.exp_pos _)
  have hH (x) (hx : x ∈ Ω) : ‖hessianMatrix u x‖ * (-u x) ≤ C :=
    weighted_norm_le_of_diag (hp x hx).posSemidef (neg_nonneg.mpr (hneg x hx).le) hC.le
      (hdiag x hx)
  refine ⟨B, hB, hBd, hH, ?_⟩
  intro K hK hKΩ
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, by norm_num, by simp⟩
  have hcont : ContinuousOn (fun x => -u x) K := by
    intro x hx
    exact (hu4 x (hKΩ hx)).continuousAt.neg.continuousWithinAt
  obtain ⟨z, hz, hmin⟩ := hK.exists_isMinOn hne hcont
  have hzpos : 0 < -u z := neg_pos.mpr (hneg z (hKΩ hz))
  refine ⟨C / (-u z) + 1, by positivity, ?_⟩
  intro x hx
  have hm : -u z ≤ -u x := hmin hx
  have hn : ‖hessianMatrix u x‖ * (-u z) ≤ C :=
    (mul_le_mul_of_nonneg_left hm (norm_nonneg _)).trans (hH x (hKΩ hx))
  have hh : ‖hessianMatrix u x‖ ≤ C / (-u z) := (le_div_iff₀ hzpos).mpr hn
  exact hh.trans (by linarith)

end Coordinates

end FunctionalInequalities.Analysis.Pogorelov
