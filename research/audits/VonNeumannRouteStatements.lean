import FunctionalInequalities.Analysis.Semigroup.AdjointComp
import FunctionalInequalities.Analysis.Semigroup.Resolvent.Basic

/-!
# Route statements: von Neumann's theorem and the resolvent limits (`S6` prerequisites)

**This file contains only `#check`s.  A proposition that type-checks is not a proof.**  It declares
nothing, proves nothing, and introduces no placeholder axiom.  Each proposition below is an
obligation of the route recorded in `research/decisions/2026-09-19-von-neumann-route.md`, and **at
the time of this route snapshot none of `V1`–`V5`, `R1`–`R3` had been proved**.

## Why this route exists

`S1`–`S5` of `SemigroupGenerationRouteStatements.lean` are proved
(`Analysis/Semigroup/{Form,Resolvent,Yosida}.lean`).  `S6`, the strong convergence of the Yosida
exponentials `exp (-t • L_s)` as `s ↓ 0`, is the step with no Mathlib precedent, and its classical
proof needs two inputs that `S1`–`S5` deliberately avoided:

* **von Neumann's theorem**: for `T` closed and densely defined, `T†T` (Mathlib's
  `LinearPMap.adjoint` composed with `T`, packaged as `Analysis.Semigroup.adjointComp T`) is
  self-adjoint with dense domain, and `(1 + s T†T) J_s = 1` for the resolvent `J_s` already built in
  `Resolvent.lean`;
* **resolvent limits**: `J_s → 1` strongly as `s ↓ 0`, and the resolvents commute.

Both are general real Hilbert space material with no measure, no log-concavity and no KLS
content.  The owner has fixed the Buser target at the sharp constant `π`
(`2026-09-19-semigroup-handoff.md`, §5 addendum), so the semigroup route must be completed and this
is its next block.

## Deliberately out of scope

`S6`–`S8` themselves are not stated here; neither are the Markov property, Bakry–Émery calculus,
small-time heat estimates or any step of Buser's inequality.
`thm:logconcave-cheeger-poincare-comparison` gains no progress marker from this route.

## Conventions

`⟪x, y⟫` is the real inner product.  `T†` is `LinearPMap.adjoint T` (`open scoped LinearPMap`).
`adjointComp T` is `T†T` with domain `{x ∈ D(T) | T x ∈ D(T†)}`; its domain is definitionally
`adjointCompDomain T ⊓ T.domain`, so for `x : (adjointComp T).domain` the term `⟨x, x.2.2⟩ : T.domain`
is available without any lemma.  `resolventCLM T hT hs` is `J_s = (1 + s T†T)⁻¹` as a
`ContinuousLinearMap`, characterised by the weak equation `WeakResolvent T s f (resolventDomain …)`.
-/

noncomputable section

open Filter Topology InnerProductSpace FunctionalInequalities.Analysis.Semigroup

open scoped RealInnerProductSpace LinearPMap

/-! ### Proved inputs, for reference -/

#check @LinearPMap.adjoint_isFormalAdjoint
#check @LinearPMap.adjoint_apply_eq
#check @LinearPMap.mem_adjoint_domain_of_exists
#check @LinearPMap.IsFormalAdjoint.le_adjoint
#check @LinearPMap.isSelfAdjoint_def
#check @IsSelfAdjoint.dense_domain
#check @FunctionalInequalities.Analysis.Semigroup.adjointComp
#check @FunctionalInequalities.Analysis.Semigroup.adjointComp_apply
#check @FunctionalInequalities.Analysis.Semigroup.resolventCLM
#check @FunctionalInequalities.Analysis.Semigroup.resolventDomain_spec
#check @FunctionalInequalities.Analysis.Semigroup.eq_resolventDomain
#check @FunctionalInequalities.Analysis.Semigroup.resolventCLM_symm

/-! ## Part A — von Neumann's theorem for `T†T` -/

/-! ### `V1` — `T†T` acts through the form

For `x ∈ D(T†T)` and `y ∈ D(T)`, `⟪T†T x, y⟫ = ⟪T x, T y⟫`.  This is `adjoint_isFormalAdjoint`
unfolded through `adjointComp_apply`; it needs density of `D(T)` because Mathlib's adjoint carries a
junk value otherwise. -/

#check (∀ {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
    [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
    (T : H₀ →ₗ.[ℝ] H₁), Dense (T.domain : Set H₀) →
      ∀ (x : (adjointComp T).domain) (y : T.domain),
        ⟪adjointComp T x, (y : H₀)⟫ = ⟪T ⟨(x : H₀), x.2.2⟩, T y⟫)

/-! ### `V2` — the resolvent inverts `1 + s T†T`

For `s > 0` and every `f`, the weak solution `J_s f` lies in `D(T†T)` and `(1 + s T†T) J_s f = f`.
From the weak equation `⟪u, v⟫ + s ⟪T u, T v⟫ = ⟪f, v⟫`, the vector `T u` pairs continuously against
`T v` (with `w = s⁻¹ (f - u)`), so `T u ∈ D(T†)` by `mem_adjoint_domain_of_exists`, and
`adjoint_apply_eq` identifies `T† (T u) = s⁻¹ (f - u)`. -/

#check (∀ {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
    [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
    (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed), Dense (T.domain : Set H₀) → ∀ {s : ℝ} (hs : 0 < s),
      ∀ f : H₀, ∃ hu : resolventCLM T hT hs f ∈ (adjointComp T).domain,
        resolventCLM T hT hs f + s • adjointComp T ⟨resolventCLM T hT hs f, hu⟩ = f)

/-! ### `V3` — `T†T` is self-adjoint (von Neumann)

Symmetry `⟪T†T x, y⟫ = ⟪x, T†T y⟫` on `D(T†T)` follows from `V1` and gives `T†T ≤ (T†T)†`
(`IsFormalAdjoint.le_adjoint`).  For the reverse inclusion take `y ∈ D((T†T)†)`, put
`f = y + (T†T)† y` and `u = J_1 f`; by `V2`, `u + T†T u = f`, and testing against `x + T†T x` for
`x ∈ D(T†T)` shows `⟪x + T†T x, y - u⟫ = 0`.  Since `1 + T†T` is onto by `V2`, `y = u ∈ D(T†T)`. -/

#check (∀ {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
    [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
    (T : H₀ →ₗ.[ℝ] H₁), T.IsClosed → Dense (T.domain : Set H₀) →
      IsSelfAdjoint (adjointComp T))

/-! ### `V4` — `D(T†T)` is dense

Immediate from `V3` and Mathlib's `IsSelfAdjoint.dense_domain`; also provable directly: if
`g ⊥ D(T†T)`, write `g = u + T†T u` with `u = J_1 g` (`V2`), then `0 = ⟪g, u⟫ = ‖u‖² + ‖T u‖²`. -/

#check (∀ {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
    [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
    (T : H₀ →ₗ.[ℝ] H₁), T.IsClosed → Dense (T.domain : Set H₀) →
      Dense ((adjointComp T).domain : Set H₀))

/-! ### `V5` — the Yosida approximation on `D(T†T)`

For `f ∈ D(T†T)`, `f - J_s f = s • J_s (T†T f)`; equivalently the Yosida approximation
`L_s f = s⁻¹ (f - J_s f)` equals `J_s (T†T f)`, which is what makes `L_s f → T†T f` as `s ↓ 0` once
`R2` is known.  Proof: `f` itself solves the weak equation with datum `f + s T†T f` (by `V1`), so by
uniqueness `J_s (f + s T†T f) = f`, and `J_s` is linear. -/

#check (∀ {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
    [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
    (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed), Dense (T.domain : Set H₀) → ∀ {s : ℝ} (hs : 0 < s),
      ∀ f : (adjointComp T).domain,
        (f : H₀) - resolventCLM T hT hs f = s • resolventCLM T hT hs (adjointComp T f))

/-! ## Part B — resolvent limits (no adjoint involved) -/

/-! ### `R1` — quantitative convergence on `D(T)`

For `f ∈ D(T)`, `‖J_s f - f‖² ≤ s ‖T f‖²`.  Test the weak equation against `v = u - f ∈ D(T)`:
`‖u - f‖² = -s ⟪T u, T u - T f⟫ ≤ s ‖T u‖ ‖T f‖ - s ‖T u‖² ≤ s ‖T f‖²`, using `‖T u‖ ≤ ‖T f‖` from
the same equation tested against `v = u`. -/

#check (∀ {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
    [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
    (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) {s : ℝ} (hs : 0 < s) (f : T.domain),
      ‖resolventCLM T hT hs f - f‖ ^ 2 ≤ s * ‖T f‖ ^ 2)

/-! ### `R2` — strong convergence `J_s → 1` as `s ↓ 0`

For every `f : H₀` and `ε > 0` there is `δ > 0` with `‖J_s f - f‖ < ε` for `0 < s < δ`.  Approximate
`f` by `g ∈ D(T)` (density), use `R1` on `g` and the contraction bound `‖J_s‖ ≤ 1` on `f - g`.  Stated
in `ε`–`δ` form because `resolventCLM` carries the proof `0 < s` as an argument. -/

#check (∀ {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
    [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
    (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed), Dense (T.domain : Set H₀) → ∀ (f : H₀) {ε : ℝ}, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧ ∀ {s : ℝ} (hs : 0 < s), s < δ → ‖resolventCLM T hT hs f - f‖ < ε)

/-! ### `R3` — the resolvents commute

`J_s J_r = J_r J_s`.  This discharges the commutation hypothesis that `S6` assumes of the Yosida
family.  Proof: with `B_s(u, v) = ⟪u, v⟫ + s ⟪T u, T v⟫`, `J_s f` is the unique `u ∈ D(T)` with
`B_s(u, v) = ⟪f, v⟫` for all `v`; verify that `J_s (J_r f)` solves the `r`-equation with datum
`J_s f` (the resolvent identity `J_s - J_r = (r - s) J_s T†T J_r` in weak form), and conclude by
uniqueness. -/

#check (∀ {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
    [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
    (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) {s r : ℝ} (hs : 0 < s) (hr : 0 < r),
      (resolventCLM T hT hs).comp (resolventCLM T hT hr) =
        (resolventCLM T hT hr).comp (resolventCLM T hT hs))
