# Semigroup generation route: `S5` proved (the exponential of a bounded nonnegative operator is a contraction)

2026-09-19, following the [`S1`–`S4` round](2026-09-19-semigroup-form-proofs.md) and
Section 2 of the [handoff checklist](2026-09-19-semigroup-handoff.md). `S5` is **proved**; `S6`–`S8` are unchanged.
Direct proof holes remain **0**, certificates **26**. No commit or push; the aggregate root and `tasks.json` are unchanged (see “Bookkeeping”).

Starting point: `HEAD = origin/main = 7986adf` (the worktree contains uncommitted semigroup modules from previous rounds).

## Result

New module: `formalization/FunctionalInequalities/Analysis/Semigroup/Yosida.lean`,
namespace `FunctionalInequalities.Analysis.Semigroup` (general real Hilbert spaces; no measures, log-concavity, or KLS quantities):

| Obligation | Declaration | Description |
| --- | --- | --- |
| Lemma | `hasDerivAt_exp_smul_apply` | The orbit `t ↦ exp (t • A) f` has derivative `A (exp (t • A) f)` |
| Lemma | `antitone_normSq_exp_smul_neg` | Nonnegative `L` implies `t ↦ ‖exp (t • (-L)) f‖²` is nonincreasing on **all of ℝ** |
| Stronger `S5` | `norm_exp_neg_smul_apply_le` | Assuming only nonnegativity, `t ≥ 0` implies `‖exp (-t • L) f‖ ≤ ‖f‖` |
| Original `S5` | `route_S5` | Wraps the route statement verbatim, accepting but discarding self-adjointness |

## Proof: follows the handoff recommendation

Use the derivative monotonicity argument in the handoff: let `u t = exp (t • (-L)) f` and `φ t = ‖u t‖² = ⟪u t, u t⟫`.

* `hasDerivAt_exp_smul_const'` (the **primed version**, with the operator on the left) gives `u' t = -L (u t)`;
  apply it to the constant vector `f` using `HasDerivAt.clm_apply`. The primed version makes the derivative
  **literally** `-L (u t)`, so no commutation lemma for `L` and `exp` (such as `Commute.exp_right`) is needed.
* `HasDerivAt.inner ℝ` gives `φ' t = ⟪u t, -L (u t)⟫ + ⟪-L (u t), u t⟫ = -2⟪L (u t), u t⟫ ≤ 0`.
* `antitone_of_deriv_nonpos` gives `Antitone φ`. At `0 ≤ t`, obtain `φ t ≤ φ 0 = ‖f‖²`
  using `NormedSpace.exp_zero` and `one_apply_eq_self`, then take square roots with `sq_le_sq₀`.

The proof uses **none** of the three dead ends flagged in the handoff: spectral radius, continuous functional calculus,
or the operator norm bound `‖exp (-t • L)‖ ≤ 1`. The conclusion stays pointwise, avoiding the CLM norm instance diamond.

### Two minor obstacles

* At the derivative step, `convert h using 1` leaves an `AddCommGroup ℝ` instance equality goal
  (`Real.instAddCommGroup = Real.instRCLike.toDivisionRing.toAddCommGroup`), because the instance obtained by
  `HasDerivAt.inner` through `RCLike ℝ` differs from the direct instance. Using `HasDerivAt.congr_deriv`
  compares only derivative values and resolves the issue.
* This Mathlib version deprecates `ContinuousLinearMap.neg_apply` and `ContinuousLinearMap.one_apply`.
  Deprecations are errors under `-DwarningAsError`; use root-namespace `neg_apply` and `one_apply_eq_self`.

## Unused route assumption: self-adjointness

The route assumes `∀ f g, ⟪L f, g⟫ = ⟪f, L g⟫`. The proof **never uses it**: both terms of `φ'`,
`⟪u, -L u⟫` and `⟪-L u, u⟫`, equal `-⟪L u, u⟫` by **symmetry of the real inner product** (`real_inner_comm`).
The module therefore proves the strictly stronger `norm_exp_neg_smul_apply_le` for arbitrary bounded nonnegative `L`.
Both the module and audit versions of `route_S5` accept the original assumption and discard it. This is
**recorded explicitly**, as with dropping `0 < s` in `S2` and `Dense` in `S3`.

The condition `0 ≤ t` **is necessary**: since `φ` decreases on all of ℝ, for `t < 0` one has
`‖exp (-t • L) f‖ ≥ ‖f‖`, the reverse inequality.

## Explicit limits

`S6` (strong convergence of Yosida exponentials), `S7` (semigroup law and strong continuity), and `S8` (generator)
remain unproved; `S6` remains high risk. This is one step in semigroup construction, **not** Markovianity,
Bakry–Émery Γ calculus, or any step of the Buser inequality.
`thm:logconcave-cheeger-poincare-comparison` has no `\leanok`; the gap entries in `tasks.json` are unchanged
(the first gap remains open as a whole). No new certificate or Blueprint change.

## Bookkeeping (for integration by the main session)

This round did **not** change `formalization/FunctionalInequalities.lean`, `lakefile.toml`, `research/tasks.json`,
or any Blueprint `.tex`, and did not run `git add/commit/push`. To let the audit client import the module,
`lake build FunctionalInequalities.Analysis.Semigroup.Yosida` generated its olean separately without changing any source files.

Integration requires:

1. Add `import FunctionalInequalities.Analysis.Semigroup.Yosida` to the aggregate root `FunctionalInequalities.lean`
   (otherwise `lake build` and CI do not build it; the repository should not gain another orphan module).
2. Register the sha256 evidence for `Analysis/Semigroup/Yosida.lean` and
   `research/audits/SemigroupYosidaAudit.lean` in `tasks.json`, then run `verify.py`.
3. Mark `S5` in Section 2 of the handoff as proved and record that self-adjointness was unused.

## Validation

The module and audit pass `lake env lean -DwarningAsError=true` with **0 errors and 0 warnings**.
The audit client `research/audits/SemigroupYosidaAudit.lean` restates `S5` verbatim as `route_S5` and proves it;
it also gives `route_S5_of_nonneg` without self-adjointness and two boundary cases (equality at `t = 0`, and `L = 0`).
The `S5` text in the route file and audit was compared token by token with `diff` and matches.
**All 8 `#print axioms` reports contain only `propext, Classical.choice, Quot.sound`, with 0 occurrences of `sorryAx`.**
