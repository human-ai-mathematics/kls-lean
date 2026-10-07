# 2026-10-07 eight-hour block: first dependencies of Bizeul–Klartag–Lehec

Goal: [research/handoffs/2026-10-07-eight-hour-bkl-foundations.md](../handoffs/2026-10-07-eight-hour-bkl-foundations.md).
Source: Bizeul–Klartag–Lehec, *Presenting a proof of the Kannan–Lovász–Simonovits conjecture*,
arXiv:2610.05474v1, PDF SHA-256 `86824722318f2213daf5ae624391b41f76bb4d41118b1657db9ab00d2d1bb0db`.
Window: T0 = 2026-10-07 03:25:22 +08:00; stop expansion 09:25:22; freeze and final verifier
09:55:22; hard stop 11:25:22. Baseline: `main` = `origin/main` = `36e7c78`, index tree `e3969ca1`.
Full evidence (execution record, worker logs and provenance, Codex reviews, verifier pointer,
final report): `build/reviews/2026-10-07-bkl-eight-hour/` (local, not committed).

## Results (uncommitted working tree)

| Source item | Lean | Relation | Module |
| --- | --- | --- | --- |
| Lemma 2.2 and identity (25) | `Tensor.norm_le_four_pow_mul_norm_symmetrize`, `norm_le_four_pow_mul_norm_blockAverage`, `norm_le_choose_mul_norm_blockAverage`, `sum_norm_sq_sum_subset_eq` | same (`d = 0` included) | `Analysis/Tensor/{Symmetrization,Coordinate}.lean` |
| Lemma 2.1, operator-domain part, (20), (23), (24) | `KLS.LogConcave.existsUnique_centered_adjointComp_eq`, `centered_adjointComp_bounds`, `norm_centered_gradient_le`, `existsUnique_centered_adjointComp_eq_of_hessian`; generic `Generated.exists_adjointComp_eq_of_gap` | partial | `Analysis/Semigroup/Generated/Inverse.lean`, `KLS/LogConcave/HeatSemigroup/Inverse.lean` |
| (26)–(28), (48), Lemma 3.6 (49)/(50) | scalar: `BakryEmery.taylorTensor_neg_weightedLaplacian(_of_hasTemperateGrowth)`, `taylorTensor_one_neg_weightedLaplacian(_of_hasTemperateGrowth)`; tensor: `taylorTensor_neg_weightedLaplacianVec`, `taylorTensor_one_neg_weightedLaplacianVec`, `tiltAverage_neg_weightedLaplacianVec` | Lemma 3.6 and (48) stronger (Codex reviews 3, 4) | `Analysis/BakryEmery/{Tilt,TemperateTilt,TensorTilt}.lean` |
| Corollary 3.7 | `symmetrizeML_taylorTensor_centeredFDeriv` (for any pair satisfying (30)) | stronger (Codex strategy 11 opinion) | `Analysis/BakryEmery/TensorTilt.lean` |
| (15), (16) on `𝒜` | scalar `integral_weightedLaplacian_mul_eq_neg_of_hasTemperateGrowth`, `integral_weightedLaplacian_sq_eq_of_hasTemperateGrowth`, `integral_hessianSq_add_le_of_hasTemperateGrowth`; tensor `integral_inner_weightedLaplacianVec_eq_neg`, `integral_norm_sq_weightedLaplacianVec_eq`, `integral_hessian_add_le_norm_sq_weightedLaplacianVec` | stronger (Codex review 4) | `Analysis/BakryEmery/{TemperateIBP,TemperateBochner,TensorBochner}.lean` |
| Proposition 7.1, steps | `taylorTensor_inner_eq_cumulant` (linear functions), `exists_norm_taylorTensor_le`, `exists_norm_coordTensor_taylorTensor_le` (continuity of `T_d` on `L²`, operator and Hilbert–Schmidt norms) | partial | `Analysis/BakryEmery/{Cumulant,SquareIntegrableTilt}.lean` |
| Tensor conventions of Section 2 | `Tensor.coordTensor`, `coordTensor_symmetrizeML`, `norm_le_norm_coordTensor`, `BakryEmery.slotPerm_coordTensor_taylorTensor` | infrastructure | `Analysis/Tensor/{Multilinear,Coefficients}.lean`, `Tilt.lean` |
| Calculus | `BakryEmery.iteratedFDeriv_comp_perm_of_contDiff` (symmetry of iterated derivatives of `C^∞` maps; Mathlib states it only for analytic maps), `iteratedFDeriv_inner_self_apply` | infrastructure | `Analysis/BakryEmery/IteratedDerivative.lean` |

A conditional Lemma 4.2 (from the Letwin bound as an explicit hypothesis) was frozen at 06:01 and
left two steps open; it is not in the library. The session was idle from about 06:17 to 10:14
(an API outage; the separately running Prove2Me agent failed with an authentication error in the same
interval), so the final verifier started after the planned 09:55 freeze. No paper is newly covered; `KLS.kls` stays open. The audit client
`research/audits/BKLFoundationsAudit.lean` instantiates every endpoint on the constructed scaled
Gaussian (log-concavity, full-dimensional support, Hessian bound and all exponential moments
proved), on nonzero tensors, in the boundary cases `d = 0` and `n = 0`, and on the linear test
`⟪v, ·⟫`, which is not compactly supported.

## Decisions and corrections

- Placement followed `research/workflow.md`: a new `Analysis/Tensor/` family for finite tensors and
  symmetrizations; the generic inverse extends `Analysis/Semigroup/Generated`; the heat-model inverse
  extends `KLS/LogConcave/HeatSemigroup`; tilt calculus extends `Analysis/BakryEmery`. The planned
  single `Tilt.lean` was split by dependency (generic calculus, multilinear algebra, measures).
- The frozen name `Array` for coordinate tensors would shadow Lean core `Array`; it is `Tensor.Coord`.
- Three proved statements dropped hypotheses their proofs never use (`apply_eq_of_image_eq`,
  `card_fiber_eq`, `card_slots`); a frozen `weightedLaplacian_mul` duplicated the existing
  `BakryEmery/Gamma.lean` lemma and was dropped in favour of it.
- Codex reviews 1–4 (design; acceptance of the integrated modules, of the temperate/tensor modules, and
  of the final refactors and register relations) found no BLOCKING or MAJOR issue in the final statements; review 2's seven MINOR/NIT items were fixed (documentation of
  the total zero-measure case and of the operator norm of `taylorTensor`, narrower symmetry
  docstrings, a private generic helper, a renamed helper, stronger audit clients).
- Roles: Luna (`gpt-5.6-luna`) proved most helper and many endpoint statements; the owner's Codex
  (`gpt-6.1-sol`, xhigh, read-only CLI with ChatGPT authentication) proved the hardest steps
  (Leibniz rule, differentiation under the integral, the `T†T` range argument, the Schwarz step,
  the cutoff/dominated-convergence identities, the `L²` continuity) and reviewed; Claude froze
  statements, repaired near-miss candidates, wrote a few short proofs and integrated. Each accepted
  proof is attributed in `build/reviews/2026-10-07-bkl-eight-hour/accepted-statements.csv`.
- No commit, push, tag, remote CI, Prove2Me upload or Slack message was made for this block.
