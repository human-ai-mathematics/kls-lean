# Semigroup-generated paths: Completed portions and handover checklist

2026-09-19. This document draws the boundary between "proven in this session" and "transferred elsewhere", and provides an exact specification for the latter.
Both start and end points are `HEAD = origin/main = 7986adf` (the workspace is not commit).

## 1. Proven (high confidence, verified)

Module `Analysis/Semigroup/{Form,Resolvent}.lean`, audit `research/audits/SemigroupFormAudit.lean`.

| Number | Statement | Notes |
| --- | --- | --- |
| `S1` | `completeSpace_graph` | one line: `IsClosed` by definition is graph closed |
| `S2` | `min_one_mul_graphNormSq_le` | **Does not require `0 < s`**, holds for any real `s` |
| `S3` | `existsUnique_weakResolvent` | **Does not need `Dense`**; uses orthogonal projection, not Lax–Milgram |
| `S4` | `norm_le_of_weakResolvent`, `inner_nonneg_of_weakResolvent` | weak equation takes `v = u` |
| off-the-route | `resolventCLM` + contraction/self-adjoint/non-negative three | `J_s = (1 + sT*T)⁻¹` packaged into `H₀ →L[ℝ] H₀` |

**23 statement `#print axioms` all only `propext, Classical.choice, Quot.sound`, 0 statements `sorryAx`.**
`lake build` 3519 jobs passed; verification receipt `20260919T084529.261763Z`, 10/10 gates, 246 module replay.

## 2. Handover: `S5` (boundary case, moderate confidence)

**Goal**: `L` bounded, non-negative, self-adjoint ⟹ `‖NormedSpace.exp (-t • L) f‖ ≤ ‖f‖` (`t ≥ 0`).

**Recommended proof (monotonicity of derivative)**: Let `φ(t) = ‖exp(-t • L) f‖²`, then
`φ'(t) = -2⟪L exp(-t•L) f, exp(-t•L) f⟫ ≤ 0`, hence `φ` is decreasing on `[0,∞)`, `φ(t) ≤ φ(0) = ‖f‖²`.

* **Confirmed existence**: `hasDerivAt_exp_smul_const` (`Mathlib/Analysis/SpecialFunctions/Exponential.lean`), `NormedSpace.exp_add_of_commute`, `AntitoneOn` by the criterion of non-positive derivative.
* **Confirmed non-existence**: `IsSelfAdjoint.spectralRadius_eq_nnnorm`. Do not take the spectral radius route—
  this session has checked, the name is not present in pinned Mathlib; instead, a continuous functional calculus approach would require additional historical investigation.
* Main friction: connecting the product rule of the inner product with `hasDerivAt_exp_smul_const`.

My judgment on this is **it's possible but not "confident"**, so I didn't start working on it, leaving it for the next person.

## Three, Handover: `S6`–`S8` (Low confidence, `S6` is the real bottleneck)

* **`S6`** (`exp(-t L_s)` with `s ↓ 0` strong convergence): This approach is initially labeled as **high risk**, with no precedent in Mathlib.
  The classical proof uses `‖exp(-tL_s)f - exp(-tL_r)f‖ ≤ t‖L_s f - L_r f‖` (the difference of two commuting bounded semigroups),
  then proves `L_s f → T*T f` on `D(T*T)`, and extends it using density and uniform boundedness.
  **Note**: This step genuinely requires `Dense (T.domain)` and the adjoint operator `T*`—these assumptions were not needed for `S1`–`S4`,
  so the successor must first establish the self-adjointness of `T*T` and the density of `D(T*T)` (Mathlib has `LinearPMap.adjoint`,
  but lacks von Neumann's `T*T` self-adjointness theorem, which may need to be proven independently).
* **`S7`**, **`S8`**: Depend on `S6`, and thereafter follow a standard pattern.

**Ready-to-use starting point**: `resolventCLM T hT hs` is already a packaged `J_s`,
Yosida approximation is directly written as `L_s := s⁻¹ • (ContinuousLinearMap.id ℝ H₀ - resolventCLM T hT hs)`.

**Evening addendum, 2026-09-19: two prerequisites of `S6` are proved.** The von Neumann results (self-adjointness of `T†T`, density of `D(T†T)`, `(1 + sT†T)J_s = 1`, and `f − J_s f = s·J_s(T†T f)`) are in `Analysis/Semigroup/VonNeumann.lean`; the resolvent limits (strong convergence `J_s → 1` and `J_s J_r = J_r J_s`) are in `Analysis/Semigroup/ResolventLimit.lean`; `T†T` is defined in `AdjointComp.lean`. See the [von Neumann route record](2026-09-19-von-neumann-route.md). `R3` directly discharges the commutativity assumption in `S6`. `S6` itself remains unproved.

**2026-09-19 Night addition: `S6` is proven.** `exp(-t L_s) f` follows `s ↓ 0` strong convergence (`Analysis/Semigroup/YosidaLimit.lean`), and the core is `‖e^{-tA}f − e^{-tB}f‖ ≤ t‖Af − Bf‖` (`SemigroupLimit.lean`). **Note**: The abstract formulation (only assuming non-negativity and commutativity) of the entry in the route document `S6` has been proven false (`YosidaFamily.lean`'s `Y0`), with the corrected version adding the assumption of Cauchy on a dense subset; see [Yosida limit route record](2026-09-19-yosida-limit-route.md). `S7` and `S8` remain open.

**2026-09-19 Late addition: `S7`, `S8` proven, route `S1`–`S8` completed.** `P_t = semigroupApply` (`Generated.lean`), semigroup law, contraction, symmetry, strong continuity in `SemigroupLaws.lean`, generator `−T†T` in `Generator.lean` (via the mean value bound from `ExpMeanValue.lean`, without Bochner integral); see [Generation semigroup route record](2026-09-19-generated-semigroup-route.md). Section III handover `S6`–`S8` fully closed. Gaps II/III/IV (next section) remain unchanged.

**2026-09-19 Append: `T` has been instantiated.** `KLS/LogConcave/HeatSemigroup.lean` Maps the abstract semigroup to the closure of weighted gradients: `heatSemigroup hν m B hi ht` is `L²(ν)` on `P_t`, with all semigroup laws, generators, and `⟪T̄†T̄ f, f⟫ = ‖T̄ f‖²` (Dirichlet form = closed energy) transferred; `intrinsicHeatSemigroup` covers any log-concave law. Gap one is hereby closed. Handoff prompt for gap two: [markov-handoff-prompt](2026-09-19-markov-handoff-prompt.md).

## Four. Handover: Gaps Two/Three/Four (Programmatic Level)

See [infrastructure assessment](2026-09-19-buser-infrastructure-assessment.md). Among them, the **regularization of gap three** is the only part explicitly stating that **the cost is unestimable**: generally, the potential of a log-concave measure `V` is not smooth, its support may have a boundary or undergo dimension reduction, the Bochner formula does not apply, and one must instead proceed via "smooth strictly log-concave approximation + Neumann boundary conditions + limit transition". This is the actual mathematical content at the heart of the Buser program.

## Five. A Decision That Could Significantly Reduce Costs (Not Yet Adopted)

The only downstream consumer of the comparison node in Blueprint is `cor:tight-window-consumption`,
which requires the "infimum boundary" of dimension-free, and does **not** need the constant π. Relaxing the target from `Ψ² ≤ π C_P` to
`Ψ² ≤ C·C_P` (with `C` explicitly stated, without requiring optimality) is justified and much cheaper—π must instead take the refined form of Bakry–Émery.
Phase one already uses 12 in one dimension rather than π, representing the same trade-off. **This decision is the owner's, and has not yet been written into `tasks.json`.**

**2026-09-19 Evening, owner decides: not adopted.** The goal remains `Ψ² ≤ π·C_P`, with the constant π unchanged. Thus, the Buser half's `n ≥ 2` path can only follow the semigroup / Bakry–Émery (sharp form by De Ponti–Mondino), while localized paths fail to yield π and are no longer considered as alternative options; the one-dimensional constant 12 proven so far remains a partial result, not a proof for this node. The next piece of Lean work accordingly becomes the prerequisite for `S6`: the von Neumann theorem (`T*T` self-adjoint, `D(T*T)` dense).
