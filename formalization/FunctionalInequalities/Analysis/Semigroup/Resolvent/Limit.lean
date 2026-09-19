import FunctionalInequalities.Analysis.Semigroup.Resolvent.Basic

/-!
# Resolvent limits: `J_s → 1` as `s ↓ 0`, and commutation

Part B (`R1`–`R3`) of the von Neumann route recorded in
`research/decisions/2026-09-19-von-neumann-route.md`, restated in
`research/audits/VonNeumannRouteStatements.lean`:

* `R1`, `norm_resolventCLM_sub_sq_le`: for `f ∈ D(T)`, `‖J_s f - f‖ ^ 2 ≤ s * ‖T f‖ ^ 2`;
* `R2`, `exists_delta_norm_resolventCLM_sub_lt`: `J_s → 1` strongly as `s ↓ 0`, in `ε`–`δ` form
  (`resolventCLM` carries the proof `0 < s` as an argument, so this is how the route states it);
* `R3`, `resolventCLM_comp_comm`: the resolvents commute, `J_s J_r = J_r J_s`.

Everything is proved from the **weak equation** `WeakResolvent T s f u` of `Resolvent/Form.lean`
and the unique solvability of `Resolvent/Basic.lean`.  In particular:

**The adjoint never appears.**  No declaration here refers to `LinearPMap.adjoint`, to
`adjointComp` or to `adjointCompDomain`; the module does not import
`FunctionalInequalities.Analysis.Semigroup.AdjointComp`, and it proves none of `V1`–`V5` of the
same route.  It also proves nothing about `S6`–`S8` of the semigroup-generation route (the Yosida
exponentials, the semigroup laws, the generator), nothing about the Markov property or
Bakry–Émery calculus, and no step of Buser's inequality.  This is general real Hilbert space
material: no measure, no log-concavity, no KLS quantity.

## Strengthenings over the route statements

`R1` is proved through the **sharper** `norm_resolventCLM_sub_sq_le_quarter`, with the constant
`s ‖T f‖ ^ 2 / 4` (the route asks only for `s ‖T f‖ ^ 2`).  The sharp form is the honest output of
the computation `‖u - f‖ ^ 2 = -s ‖T u‖ ^ 2 + s ⟪T u, T f⟫ ≤ s ‖T f‖ ^ 2 / 4`, so the route's
bound is kept verbatim as a wrapper.  No route hypothesis is dropped: `R1` and `R3` use
closedness only through `resolventCLM`, `R2` genuinely needs density, and completeness of `H₀`
and `H₁` is required for `resolventCLM` to exist at all.  The route's `R3` suggests routing
through the resolvent identity `J_s - J_r = (r - s) J_s T†T J_r`; the proof here instead shows
that `s • J_s f - r • J_r f + (r - s) • J_s (J_r f)` solves the weak equation with datum `0`,
hence vanishes, which is the same identity with the adjoint removed.
-/

noncomputable section

open InnerProductSpace

open scoped RealInnerProductSpace

namespace FunctionalInequalities.Analysis.Semigroup

variable {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
  [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]

/-! ## `R1` — quantitative convergence on the domain -/

/-- The exact form of `R1`'s computation: testing the weak equation for `u = J_s f` against
`v = u - f ∈ D(T)` gives `‖u - f‖ ^ 2 = -s ‖T u‖ ^ 2 + s ⟪T u, T f⟫`.

This is the only place where the weak equation is used in the proof of `R1`. -/
theorem norm_resolventCLM_sub_sq_eq (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) {s : ℝ} (hs : 0 < s)
    (f : T.domain) :
    ‖resolventCLM T hT hs f - f‖ ^ 2
      = -(s * ‖T (resolventDomain T hT hs (f : H₀))‖ ^ 2)
        + s * ⟪T (resolventDomain T hT hs (f : H₀)), T f⟫ := by
  set u := resolventDomain T hT hs (f : H₀) with hudef
  have h := resolventDomain_spec T hT hs (f : H₀) (u - f)
  have hcoe : ((u - f : T.domain) : H₀) = (u : H₀) - (f : H₀) := rfl
  have hTsub : T (u - f) = T u - T f := T.map_sub u f
  rw [hcoe, hTsub] at h
  simp only [inner_sub_right] at h
  have hsym : ⟪(f : H₀), (u : H₀)⟫ = ⟪(u : H₀), (f : H₀)⟫ := real_inner_comm _ _
  have hTself : ⟪T u, T u⟫ = ‖T u‖ ^ 2 := real_inner_self_eq_norm_sq _
  have hself : ‖resolventCLM T hT hs f - (f : H₀)‖ ^ 2
      = ⟪(u : H₀), (u : H₀)⟫ - 2 * ⟪(u : H₀), (f : H₀)⟫ + ⟪(f : H₀), (f : H₀)⟫ := by
    have hru : resolventCLM T hT hs (f : H₀) = (u : H₀) := rfl
    rw [hru, ← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right, hsym]
    ring
  rw [hself]
  rw [hTself] at h
  linarith [hsym]

/-- `R1`, sharp form: for `f ∈ D(T)`, `‖J_s f - f‖ ^ 2 ≤ s ‖T f‖ ^ 2 / 4`.

Sharper than the route's `R1` by the factor `4`: the computation
`‖u - f‖ ^ 2 = -s ‖T u‖ ^ 2 + s ⟪T u, T f⟫` is closed by Cauchy–Schwarz and
`s (‖T u‖ - ‖T f‖ / 2) ^ 2 ≥ 0`, so the bound `‖T u‖ ≤ ‖T f‖` suggested by the route sketch is
not needed. -/
theorem norm_resolventCLM_sub_sq_le_quarter (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) {s : ℝ}
    (hs : 0 < s) (f : T.domain) :
    ‖resolventCLM T hT hs f - f‖ ^ 2 ≤ s * ‖T f‖ ^ 2 / 4 := by
  have hkey := norm_resolventCLM_sub_sq_eq T hT hs f
  have hcs : ⟪T (resolventDomain T hT hs (f : H₀)), T f⟫
      ≤ ‖T (resolventDomain T hT hs (f : H₀))‖ * ‖T f‖ := real_inner_le_norm _ _
  have h1 : s * ⟪T (resolventDomain T hT hs (f : H₀)), T f⟫
      ≤ s * (‖T (resolventDomain T hT hs (f : H₀))‖ * ‖T f‖) :=
    mul_le_mul_of_nonneg_left hcs hs.le
  have h2 : 0 ≤ s * (‖T (resolventDomain T hT hs (f : H₀))‖ - ‖T f‖ / 2) ^ 2 :=
    mul_nonneg hs.le (sq_nonneg _)
  nlinarith [h1, h2]

/-- `R1` of the von Neumann route: for `f ∈ D(T)`, `‖J_s f - f‖ ^ 2 ≤ s ‖T f‖ ^ 2`.

The route's statement, obtained from the sharp `norm_resolventCLM_sub_sq_le_quarter`. -/
theorem norm_resolventCLM_sub_sq_le (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) {s : ℝ} (hs : 0 < s)
    (f : T.domain) : ‖resolventCLM T hT hs f - f‖ ^ 2 ≤ s * ‖T f‖ ^ 2 := by
  have h := norm_resolventCLM_sub_sq_le_quarter T hT hs f
  nlinarith [mul_nonneg hs.le (sq_nonneg ‖T f‖)]

/-! ## `R2` — strong convergence to the identity -/

/-- `R2` of the von Neumann route: `J_s f → f` as `s ↓ 0`, for every `f : H₀`.

Stated in `ε`–`δ` form because `resolventCLM` carries the proof `0 < s` as an argument.  Split
`‖J_s f - f‖ ≤ ‖J_s (f - g)‖ + ‖J_s g - g‖ + ‖g - f‖` for `g ∈ D(T)` within `ε / 3` of `f`
(density), bound the outer terms by the contraction property `norm_resolventCLM_le` and the middle
term by `R1`, and take `δ = (ε / 3) ^ 2 / (‖T g‖ ^ 2 + 1)`. -/
theorem exists_delta_norm_resolventCLM_sub_lt (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed)
    (hD : Dense (T.domain : Set H₀)) (f : H₀) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ {s : ℝ} (hs : 0 < s), s < δ → ‖resolventCLM T hT hs f - f‖ < ε := by
  have hε3 : (0 : ℝ) < ε / 3 := by linarith
  obtain ⟨g, hgmem, hgdist⟩ := Metric.mem_closure_iff.mp (hD f) (ε / 3) hε3
  set gd : T.domain := ⟨g, hgmem⟩ with hgd
  have hfg : ‖f - g‖ < ε / 3 := by rwa [← dist_eq_norm]
  refine ⟨(ε / 3) ^ 2 / (‖T gd‖ ^ 2 + 1), by positivity, ?_⟩
  intro s hs hsδ
  have hden : (0 : ℝ) < ‖T gd‖ ^ 2 + 1 := by positivity
  have hsmall : s * ‖T gd‖ ^ 2 < (ε / 3) ^ 2 := by
    have h1 : s * (‖T gd‖ ^ 2 + 1) < (ε / 3) ^ 2 := by
      have := (lt_div_iff₀ hden).mp hsδ
      linarith
    nlinarith [hs.le, sq_nonneg ‖T gd‖]
  have hmid : ‖resolventCLM T hT hs g - g‖ < ε / 3 := by
    have hR1 : ‖resolventCLM T hT hs gd - gd‖ ^ 2 ≤ s * ‖T gd‖ ^ 2 :=
      norm_resolventCLM_sub_sq_le T hT hs gd
    have hcoe : ((gd : T.domain) : H₀) = g := rfl
    rw [hcoe] at hR1
    nlinarith [norm_nonneg (resolventCLM T hT hs g - g), hR1, hsmall]
  have houter : ‖resolventCLM T hT hs f - resolventCLM T hT hs g‖ < ε / 3 := by
    have hlin : resolventCLM T hT hs f - resolventCLM T hT hs g
        = resolventCLM T hT hs (f - g) := (map_sub _ _ _).symm
    rw [hlin]
    exact lt_of_le_of_lt (norm_resolventCLM_le T hT hs (f - g)) hfg
  have hlast : ‖g - f‖ < ε / 3 := by rwa [norm_sub_rev]
  have htri : ‖resolventCLM T hT hs f - f‖
      ≤ ‖resolventCLM T hT hs f - resolventCLM T hT hs g‖
        + ‖resolventCLM T hT hs g - g‖ + ‖g - f‖ := by
    have h1 : resolventCLM T hT hs f - f
        = (resolventCLM T hT hs f - resolventCLM T hT hs g)
          + (resolventCLM T hT hs g - g) + (g - f) := by abel
    have hab := norm_add_le (resolventCLM T hT hs f - resolventCLM T hT hs g)
      (resolventCLM T hT hs g - g)
    rw [h1]
    exact le_trans (norm_add_le _ _) (by linarith)
  linarith

/-! ## `R3` — the resolvents commute -/

/-- The weak resolvent identity, with the adjoint removed: for all `s, r > 0` and every datum `f`,
`s • J_s f - r • J_r f + (r - s) • J_s (J_r f) = 0` inside `D(T)`.

Spectrally this is `s / (1 + s a) - r / (1 + r a) + (r - s) / ((1 + s a)(1 + r a)) = 0`.  The proof
is by uniqueness: the left-hand side solves the weak `s`-equation with datum `0`. -/
theorem resolventDomain_identity (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) {s r : ℝ} (hs : 0 < s)
    (hr : 0 < r) (f : H₀) :
    s • resolventDomain T hT hs f - r • resolventDomain T hT hr f
        + (r - s) • resolventDomain T hT hs (resolventDomain T hT hr f : H₀) = 0 := by
  set p := resolventDomain T hT hs f with hp
  set q := resolventDomain T hT hr f with hq
  set w := resolventDomain T hT hs (q : H₀) with hw
  set z : T.domain := s • p - r • q + (r - s) • w with hz
  have hzcoe : (z : H₀) = s • (p : H₀) - r • (q : H₀) + (r - s) • (w : H₀) := rfl
  have hzT : T z = s • T p - r • T q + (r - s) • T w := by
    rw [hz, T.map_add, T.map_sub, T.map_smul, T.map_smul, T.map_smul]
  have hzero : WeakResolvent T s (0 : H₀) z := by
    intro v
    have hA := resolventDomain_spec T hT hs f v
    have hB := resolventDomain_spec T hT hr f v
    have hC := resolventDomain_spec T hT hs (q : H₀) v
    rw [hzcoe, hzT]
    simp only [inner_add_left, inner_sub_left, real_inner_smul_left, inner_zero_left]
    linear_combination s * hA - s * hB + (r - s) * hC
  have hzero' : WeakResolvent T s (0 : H₀) (0 : T.domain) := by
    intro v
    simp [T.map_zero]
  exact weakResolvent_unique hs hzero hzero'

/-- `R3` of the von Neumann route: the resolvents commute, `J_s J_r = J_r J_s`.

From `resolventDomain_identity`: `w = J_s (J_r f)` satisfies the weak `r`-equation with datum
`J_s f`, so `w = J_r (J_s f)` by uniqueness. -/
theorem resolventCLM_comp_comm (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) {s r : ℝ} (hs : 0 < s)
    (hr : 0 < r) :
    (resolventCLM T hT hs).comp (resolventCLM T hT hr)
      = (resolventCLM T hT hr).comp (resolventCLM T hT hs) := by
  ext f
  set p := resolventDomain T hT hs f with hp
  set q := resolventDomain T hT hr f with hq
  set w := resolventDomain T hT hs (q : H₀) with hw
  have hid := resolventDomain_identity T hT hs hr f
  rw [← hp, ← hq, ← hw] at hid
  have hidT : s • T p - r • T q + (r - s) • T w = 0 := by
    have : T (s • p - r • q + (r - s) • w) = s • T p - r • T q + (r - s) • T w := by
      rw [T.map_add, T.map_sub, T.map_smul, T.map_smul, T.map_smul]
    rw [← this, hid, T.map_zero]
  have hgoal : WeakResolvent T r (p : H₀) w := by
    intro v
    have hA := resolventDomain_spec T hT hs f v
    have hB := resolventDomain_spec T hT hr f v
    have hC := resolventDomain_spec T hT hs (q : H₀) v
    have hZ2 : s * ⟪T p, T v⟫ - r * ⟪T q, T v⟫ + (r - s) * ⟪T w, T v⟫ = 0 := by
      have := congrArg (fun x : H₁ => ⟪x, T v⟫) hidT
      simpa only [inner_add_left, inner_sub_left, real_inner_smul_left, inner_zero_left]
        using this
    linear_combination hC + hZ2 + hB - hA
  have hfin : w = resolventDomain T hT hr (p : H₀) := eq_resolventDomain T hT hr hgoal
  simp only [ContinuousLinearMap.comp_apply, resolventCLM_apply, ← hp, ← hq, ← hw]
  exact congrArg (fun x : T.domain => (x : H₀)) hfin

end FunctionalInequalities.Analysis.Semigroup
