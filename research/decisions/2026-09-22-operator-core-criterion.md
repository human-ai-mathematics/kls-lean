# The operator-core criterion: `C0`–`C5`

2026-09-22, after the generator form of the weak `Γ₂` inequality
(`2026-09-21-generator-gamma-two.md`). The task of this round was to **discharge** the `hcore`
hypothesis of `HeatSemigroup.integral_mul_weakGamma_apply_nonneg_of_core` and deliver an
unconditional heat-flow weak `Γ₂` theorem. It preserves all earlier work, makes no commit or
push, does not upgrade Lean/Mathlib, and does **not** complete Bakry–Émery, Buser or KLS.

**Headline, stated without varnish.** `hcore` is **not** discharged. What is proved is one of its
two classical halves, unconditionally and in Lean: the global cutoff ("completeness at infinity")
argument. The heat-flow weak `Γ₂` theorem therefore still carries one hypothesis, but that
hypothesis is now **local**: interior regularity of distributional solutions of `ℒ u = u`. It is
not an operator core, not an essential-self-adjointness statement, not an approximation sequence,
and it mentions no `φ`, no `g` and no `t`. Section 6 states exactly what is proved, section 7 the
route check, and section 8 the residual gap. **This round does not complete its stated target.**

## 1. The setting, stated in full

`V` is a finite-dimensional real inner product space with its Borel structure
(`[CompleteSpace V] [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
[FiniteDimensional ℝ V]`), `m` a Haar measure on `V`, and `ν : ProbabilityMeasure V`
full-dimensional log-concave (`hν : LogConcave ν`,
`hi : (interior (ν : Measure V).support).Nonempty`) with `(ν : Measure V) = m.tilted (-U)`.

`T̄ = hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi` is the closed unit-weight
gradient, `A = adjointComp T̄ = T̄†T̄ ≥ 0` the generator, `ℒ = -A`, and `P_t` the semigroup the
repository constructs.

| Result | weight `B` | `U` | extra |
| --- | --- | --- | --- |
| locality of `ℒ` (`C0`) | — | arbitrary | none; `f` not even assumed differentiable |
| symmetry of a bounded multiplier (`C1`) | — | — | real scalar multiplier |
| vanishing theorem (`C2`) | `B = I` | `C¹` | no convexity, no semigroup |
| operator-core criterion (`C3`) | `B = I` | `C¹` | no convexity, no semigroup |
| global-hypothesis versions (`C4`) | `B = I` (and arbitrary `B` for the implication) | `C¹` | — |
| heat-flow weak `Γ₂` (`C5`) | `B = I` | `C^∞`, `ConvexOn ℝ Set.univ U` | `φ ∈ C_c^∞`, `φ ≥ 0`, `t > 0` |

## 2. Placement plan (recorded before editing)

| Item | Object and role | Destination | Decision |
| --- | --- | --- | --- |
| `C0` the classical weighted Laplacian vanishes off `tsupport f` | elementary property of `weightedLaplacian` | `Analysis/BakryEmery/Laplacian.lean` | **extend**: that module owns the object and already carries continuity, compact support and `Lp` membership |
| `C1` a real a.e. bounded scalar multiplier is symmetric on `L²` | elementary property of `bddSmulL` | `L2/BoundedMultiplier.lean` | **extend**: same object, same role as `norm_bddSmulL_sub_le`; stated in a separate section because it needs an inner-product target |
| `C2`–`C4` the cutoff estimate, the vanishing theorem and the operator-core criterion | substantive theorem about `A = T̄†T̄` in the tilted model | `KLS/LogConcave/HeatSemigroup/OperatorCore.lean` | **create**: `Generator.lean` is the per-test identification and must not acquire bump functions and orthogonal complements; `Multiplier.lean` is deliberately free of the generator; `GammaTwo.lean` owns the `Γ₂` inequality. The operator-core question is a third responsibility |
| `C5` the heat-flow frontend with the local hypothesis | concrete specialization beside the `hcore` version | `KLS/LogConcave/HeatSemigroup/GammaTwo.lean` | **extend**: that module owns the heat-flow `Γ₂` frontends and already imports everything else |

No empty module, compatibility alias or old-path wrapper was created. No existing statement was
weakened, renamed or removed. `FunctionalInequalities.lean` gains the new leaf. The scaled
cutoffs are `private` helpers of the new module: reusing
`Analysis.WhitneyCover.bump` would have pulled Vitali/Besicovitch covering theory into a
log-concave analysis module for four elementary facts.

## 3. `C0` and `C1`: the two elementary additions

`Analysis.BakryEmery.weightedLaplacian_eq_zero_of_notMem_tsupport`: for any potential `U` and any
`f`, `x ∉ tsupport f` implies `weightedLaplacian U f x = 0`. Both `fderiv ℝ f x` and
`fderiv ℝ (fderiv ℝ f) x` vanish there, by `support_fderiv_subset` and `tsupport_fderiv_subset`.
This is what makes `A [f] = [-ℒ f]` a *local* object in the cutoff argument.

`FunctionalInequalities.L2.inner_bddSmulL_left`: `⟪c · u, v⟫ = ⟪u, c · v⟫` for a real a.e.
bounded `c`. This replaces every pointwise Cauchy–Schwarz estimate in the cutoff argument by a
Hilbert-space identity.

## 4. The cutoffs

`cutoff r y = profile (r⁻¹ • y)` for one fixed `ContDiffBump (0 : V)` with radii `5 < 8`: smooth,
compactly supported, `0 ≤ χ_r ≤ 1`, `χ_r = 1` on `closedBall 0 (5 r)`,
`tsupport χ_r ⊆ closedBall 0 (8 r)`, `∇χ_r = 0` on `ball 0 (5 r)`, and one **uniform** bound
`‖∇χ_r‖ ≤ M / r` for all `r > 0` and all points (`exists_norm_gradient_cutoff_le`), obtained from
the chain rule for `y ↦ r⁻¹ • y`. Three scales are used at once: `χ_r` is the test cutoff, `χ_{2r}`
localizes the approximating sequence, and `χ_{4r}` localizes `u`.

## 5. The cutoff estimate

`norm_toLp_mul_cutoff_le` (private): under the hypotheses of `C2`, for every `r > 0`,

`‖[χ_r u]‖ ≤ (M / r) ‖u‖`.

Proof. Put `w = [χ_{4r} u] ∈ D(T̄)` (local regularity), `w₁ = χ_r w`, `z = χ_r w₁`, all in `D(T̄)`
by the Leibniz rule of `Multiplier.lean`, which also gives
`T̄ z = χ_r² (T̄ w) + 2 χ_r w ∇χ_r` almost everywhere. With
`p = χ_r (T̄ w)` and `q = w ∇χ_r` as `L²` classes this reads
`T̄ z = χ_r p + 2 (χ_r q)`, so by `C1`

`⟪T̄ z, T̄ w⟫ = ‖p‖² + 2 ⟪q, p⟫`  and  `⟪z, u⟫ = ‖[χ_r u]‖²`.

Separately, `z` is a graph limit of smooth compactly supported `gₙ`; the localized sequence
`fₙ = χ_{2r} gₙ` has the same two limits, because `χ_{2r} = 1` and `∇χ_{2r} = 0` on
`tsupport χ_r`, and it is supported in `closedBall 0 (16 r)`, where `χ_{4r} = 1`. Since
`A [fₙ] = [-ℒ fₙ]` vanishes off `tsupport fₙ` (`C0`), the orthogonality hypothesis may be tested
against `w` instead of `u`, and weak integration by parts `⟪A f, x⟫ = ⟪T̄ f, T̄ x⟫` turns it into
`⟪T̄ z, T̄ w⟫ = -⟪z, u⟫`. Hence

`‖p‖² + ‖[χ_r u]‖² = -2 ⟪q, p⟫ ≤ 2 ‖q‖ ‖p‖ ≤ ‖p‖² + ‖q‖²`,

so `‖[χ_r u]‖ ≤ ‖q‖ ≤ (M / r) ‖w‖ ≤ (M / r) ‖u‖`. Only the **first** derivative of the cutoff
occurs anywhere: the commutator `⟪∇U, ∇χ⟫`, which is unbounded for a general smooth convex `U`
and which blocks a naive truncation of `F ∈ D(A)`, never appears.

## 6. `C2`–`C5`: what is proved

* `KLS.LogConcave.eq_zero_of_localRegularity` — **`C2`.** For `ν = m.tilted (-U)` with `C¹` `U`
  and unit weight: if `u ∈ L²(ν)` satisfies `⟪A [f], u⟫ + ⟪[f], u⟫ = 0` for every
  `f ∈ C_c^∞(V)`, and if `[χ u] ∈ D(T̄)` for every `χ ∈ C_c^∞(V)`, then `u = 0`. Letting `r → ∞`
  in section 5 with dominated convergence.
* `KLS.LogConcave.exists_seq_smooth_tendsto_adjointComp_of_localRegularity` — **`C3`.** If that
  local regularity holds for **every** such `u`, then every `F ∈ D(A)` satisfies the conclusion of
  `hcore`: there are `fₙ ∈ C_c^∞(V)` with `[fₙ] → F` and `A [fₙ] → A F` in `L²(ν)`. Proof: `C2`
  says the orthogonal complement of `(A + 1) C_c^∞(V)` is trivial, so that subspace is dense; and
  `‖(A + 1) v‖² = ‖A v‖² + 2 ‖T̄ v‖² + ‖v‖²` converts approximation of `(A + 1) F` into
  simultaneous approximation of `F` and `A F`.
* `KLS.LogConcave.eq_zero_of_mem_closedWeightedOperator_domain` and
  `exists_seq_smooth_tendsto_adjointComp_of_mem_domain` — **`C4`.** The same two statements with
  the stronger and more familiar hypothesis `u ∈ D(T̄)`; the local hypothesis follows from it by
  the Leibniz rule, for an arbitrary weight `B`.
* `KLS.LogConcave.HeatSemigroup.integral_mul_weakGamma_apply_nonneg_of_localRegularity` — **`C5`.**
  For `C^∞` convex `U`, unit weight, arbitrary `g ∈ L²(ν)`, every `t > 0` and every nonnegative
  `φ ∈ C_c^∞(V)`, with `F = P_t g`,
  `0 ≤ (∫ (ℒφ) Γ(T̄ F, T̄ F) dν)/2 + ∫ φ Γ(T̄ F, T̄ (A F)) dν`,
  under the local hypothesis instead of `hcore`.

The `hcore` version `integral_mul_weakGamma_apply_nonneg_of_core` is unchanged and still exported.

## 7. Route check, with the sources actually consulted

The statement behind `hcore` is classical: on a **complete** weighted Riemannian manifold with a
smooth positive density, the weighted Laplacian is essentially self-adjoint on `C_c^∞`. For
`ℝⁿ` with `dν = e^{-U} dx` and `U ∈ C^∞` this is the case of a complete Euclidean metric with a
smooth positive weight. The standard proofs (R. S. Strichartz, *Analysis of the Laplacian on the
complete Riemannian manifold*, J. Funct. Anal. 52 (1983), 48–79; A. Grigor'yan, *Heat Kernel and
Analysis on Manifolds*, AMS/IP 47, 2009, §11; E. B. Davies, *Heat Kernels and Spectral Theory*,
CUP 1989, §5.2) all have the two-ingredient shape recorded in section 8. Conventions and the
`Γ`/`Γ₂` normalizations remain Bakry–Gentil–Ledoux, *Analysis and Geometry of Markov Diffusion
Operators* (Grundlehren 348, 2014); the algebra `𝒜₀` that BGL **assumes** is exactly what `hcore`
would provide. Non-uniqueness for singular weights, and therefore the necessity of some regularity
hypothesis, is the subject of A. Eberle, *Uniqueness and Non-Uniqueness of Semigroups Generated by
Singular Diffusion Operators* (LNM 1718, 1999). **No step of any of these papers is used as a
proof here**; the citations record the target, the conventions and the shape of the argument.

The four routes were compared before implementing:

* **Smooth truncation of `F ∈ D(A)` directly.** `A(χ F) = χ A F - 2 Γ(T̄ F, ∇χ) - F ℒχ`, and
  `ℒχ = Δχ - ⟪∇U, ∇χ⟫` is **not** uniformly small for a general smooth convex `U`; convexity gives
  only the one-sided bound `ℒ‖·‖ ≤ (n-1)/‖·‖`. Rejected: it cannot give graph convergence.
* **Weak convergence plus Mazur.** With `sup ‖A fₙ‖ < ∞` one gets `A fₙ ⇀ A F`, and the term
  `∫ φ (A F)²` enters with a `+` sign, so weak lower semicontinuity points the wrong way; and
  since the graph of `A|_{C_c^∞}` is a linear subspace, its weak and strong closures agree, so
  Mazur adds nothing. Rejected: it defines the same class.
* **Mollification with a Friedrichs commutator, then Caccioppoli.** This is the standard proof of
  ingredient 1. It needs the Friedrichs lemma `‖ρ_ε * (a ∂ᵢ v) - a ∂ᵢ(ρ_ε * v)‖_{L²} → 0`, local
  Sobolev spaces and weak compactness — none of which Mathlib has. Not attempted.
* **Localized Fourier bootstrap.** `Δ(χ u) = χ u + u Δχ - u div V + div(u V)` with
  `V = χ ∇U + 2 ∇χ` smooth and compactly supported, so `Δ(χ u) ∈ H^{-1}` while `χ u ∈ L²`, and
  `v, Δ v ∈ H^{-1} ⟹ v ∈ H¹` is a Bessel-potential identity. Mathlib does have
  `TemperedDistribution.MemSobolev` (Fourier/Bessel Sobolev spaces on a finite-dimensional inner
  product space). Rejected **for this round, not in principle**: it needs a `MeasureSpace V`
  instance compatible with the abstract Haar `m` (i.e. transport of the whole model to
  `EuclideanSpace`), an `Lp → 𝓢'` bridge, a passage from `C_c^∞` testing to Schwartz testing, and
  a passage from `MemSobolev 1 2` back to the repository's `D(T̄)`. That is a separate development,
  not a lemma.

The chosen route is the one closest to the existing foundations: it reuses the Leibniz rule for
`T̄` against a `C_c^∞` multiplier, the sequential smooth graph core of `T̄` and the weak
integration by parts, all proved in earlier rounds, and adds only bump functions.

## 8. The residual gap, stated exactly

The classical proof has two independent ingredients:

1. **interior regularity** — a distributional solution of `ℒ u = u` with `u ∈ L²(ν)` is locally in
   the form domain: `[χ u] ∈ D(T̄)` for every `χ ∈ C_c^∞(V)`;
2. **completeness at infinity** — such a solution which is locally in the form domain vanishes.

Ingredient 2 is `C2` and is now proved in Lean, in the quantitative form of section 5. Ingredient
1 is the hypothesis of `C3`–`C5` and is **not proved**. It is a genuine interior elliptic
regularity theorem for `div(e^{-U} ∇ ·)` with smooth coefficients; Mathlib has no local Sobolev
theory, no Friedrichs commutator lemma and no Weyl lemma for variable smooth coefficients. It is
the **whole** remaining gap between `C5` and an unconditional heat-flow weak `Γ₂` inequality.

That the round's stated target — a heat-flow weak `Γ₂` theorem with no operator-core and no
approximation hypothesis — is **not** met is recorded here and in the handoff. What changed is the
shape and the size of the hypothesis, not its presence.

## 8b. The local hypothesis is equivalent to `hcore`, not weaker

This must be said explicitly, because the opposite claim would be the same error the previous
round's addendum corrects. If `hcore` holds, then `(A + 1) C_c^∞(V)` is dense, so there is no
nonzero class orthogonal to it and the hypothesis of `C3`–`C5` holds **vacuously**; `C3` proves
the converse. The two hypotheses are therefore **logically equivalent**, and nothing here is a
weakening in the logical sense.

What the round delivers is different and is worth stating precisely: the global cutoff argument —
ingredient 2, which is where completeness of the space is used and which is the part a
localization-based attack has to redo every time — is now proved once and for all, and the
remaining obligation is a single, standard, purely local PDE statement about one equation, with no
operator theory, no semigroup, no test function and no time in it. That is a change in the shape
and location of the gap, not in its logical strength.

## 9. Boundaries

No essential self-adjointness is proved. No classical or smooth representative of `P_t g` is
produced or claimed to exist. No `Γ₂` condition, operator core, approximation sequence or
regularity statement is packaged into a structure, a type-class instance or a definition: the
hypotheses of `C3`–`C5` are explicit `∀`-statements in their types. No existing public signature
is weakened, renamed or removed. Zero `sorry`, zero custom axiom, no circular dependency. The
deliberate `KLS/Target.lean` hole is unchanged and untouched. `Γ(P_t f) ≤ P_t Γ(f)`, the `Γ` time
interpolation, the square and first-order gradient estimates, the passage from smooth potentials
to general log-concave laws, the constant `π`, Buser and KLS all remain open and are not advanced
by this round.

## 10. Validation

New: `FunctionalInequalities/KLS/LogConcave/HeatSemigroup/OperatorCore.lean`, audit
`research/audits/BakryEmeryOperatorCoreAudit.lean`.
Extended: `FunctionalInequalities/Analysis/BakryEmery/Laplacian.lean`,
`FunctionalInequalities/L2/BoundedMultiplier.lean`,
`FunctionalInequalities/KLS/LogConcave/HeatSemigroup/GammaTwo.lean`,
`FunctionalInequalities.lean`.
All are checked with `-DwarningAsError=true`. The audit restates and **proves** every public
conclusion of the round, checks the sign of the tested equation (`A + 1`, not `A - 1`), exercises
the zero multiplier, the zero class as a non-vacuity witness, the empty-support case of the
locality lemma and the implication from the global hypothesis to the local one; it prints **18
axiom reports, all standard** (`propext`, `Classical.choice`, `Quot.sound`). The earlier audits
`BakryEmeryGeneratorGammaTwoAudit.lean` and `BakryEmeryWeakGammaAudit.lean` are rerun unchanged,
which is the check that extending `L2/BoundedMultiplier.lean` and `Laplacian.lean` weakened
nothing. Default `lake build` passes with the single deliberate `KLS/Target.lean` warning.
Progress views are regenerated from a temporary Git index that preserves the real staging area,
and the root `python3 research/verify.py` is rerun at the **end** of the round, after every
tracked edit, so that its snapshot is the delivered one; the receipt is identified in
`build/audit/operator-core-criterion/final-snapshot.json`, with its gate, strict-audit-client,
module-replay and declaration-audit counts and its source digest. An earlier run of the same
gates, started before the final source reflow, certifies only its own snapshot and is not quoted
as evidence for the delivered one.

| 已有证明 | 仅接口（假设显式可见） | 仍是非形式化方案 |
| --- | --- | --- |
| `C0`–`C2` and `C4` in full; the cutoff estimate; the equivalence of the deficiency condition with orthogonality to `(A+1) C_c^∞`; the reduction of `hcore` to interior regularity | `C3` and `C5`, which need interior regularity of distributional solutions of `ℒ u = u` | interior elliptic regularity for `div(e^{-U} ∇ ·)`, essential self-adjointness of `ℒ` on `C_c^∞`, `Γ(P_t f) ≤ P_t Γ(f)`, the `Γ` time interpolation with the outer semigroup, BGL/BV, general-law passage, the constant `π`, Buser, KLS |

## 11. Minimal remaining obligations toward the `Γ` time interpolation

1. ~~`hcore`: `C_c^∞(V)` is an operator core of `A`~~ — **reduced, not proved**: by `C3` it now
   suffices to prove that a distributional solution of `ℒ u = u` in `L²(ν)` satisfies
   `[χ u] ∈ D(T̄)` for every `χ ∈ C_c^∞(V)`. This is interior elliptic regularity and is open.
2. The time interpolation is `s ↦ ∫ (P_s φ) Γ(T̄ (P_{t-s} f)) dν`, with the **outer semigroup**
   applied to the test function. A pairing against a fixed `φ` is a different object and does not
   replace it.
3. Consequently, extending the weak `Γ₂` inequality from smooth compactly supported test functions
   to the test class `{P_s φ}` is a separate obligation: `P_s φ` is an `L²` class, not a smooth
   compactly supported function, and neither its boundedness, nor a classical representative, nor
   the integrability of `(ℒ P_s φ) Γ(·)` is available. This is not a formal product-rule
   computation.
4. Only after 1–3 do the differentiability in `s`, the interchange of derivative and integral, and
   the square and first-order gradient estimates become the next objects. No claim is made that a
   single dominated-convergence step separates `hcore` from the interpolation.
