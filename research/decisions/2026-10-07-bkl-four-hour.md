# 2026-10-07 four-hour block: BKL continuation

Goal: [research/handoffs/2026-10-07-four-hour-bkl-continuation.md](../handoffs/2026-10-07-four-hour-bkl-continuation.md).
Source: Bizeul–Klartag–Lehec, arXiv:2610.05474v1, PDF SHA-256
`86824722318f2213daf5ae624391b41f76bb4d41118b1657db9ab00d2d1bb0db`.
Window (Asia/Shanghai): T0 = 2026-10-07 10:54:59; stop expansion 13:39:59; freeze and final verifier
13:54:59; hard stop 14:54:59, enforced by a local supervisor that does not depend on model responses.
Baseline: `main` = `origin/main` = `36e7c78`, real index tree `e3969ca1`, dirty eight-hour tree
saved in `build/reviews/2026-10-07-bkl-four-hour/baseline/`. Full evidence (execution record,
worker logs and provenance, Codex reviews, verifier pointer, final report):
`build/reviews/2026-10-07-bkl-four-hour/` (local, not committed).

## Results

Committed to `main` after the block at the owner's request (with the eight-hour block as a
separate preceding commit).

| Source item | Lean | Relation | Module |
| --- | --- | --- | --- |
| Lemma 4.2, conditional on the Letwin bound | `LetwinQuadraticBound` (premise), `fderiv_logLaplace_zero_apply`, `taylorTensor_two_inner_eq_of_centered`, `cumulant_three_eq_integral`, `sum_sq_cumulant_three_le_of_letwin` | partial (conditional) | `Analysis/BakryEmery/Cumulant.lean` |
| (12), regular potentials | `KLS.RegularPotential` and its consequences: probability law, Gaussian domination, all exponential moments, polynomial growth of `∇V`, log-concavity and full support; the tensor Lemma 3.6, curvature form of (16) and Lemma 2.1 (operator domain, `C = 1/a`, scalar and componentwise) for regular laws | same | `KLS/LogConcave/Regular.lean` |
| (33)–(39), (45)–(47), Lemma 3.4 | `gradCoord`, `integral_norm_sq_weightedLaplacianVec_eq_of_poisson` (46), `integral_norm_sq_gradCoord_gradCoord_eq` (39), `integral_norm_sq_gradCoord_gradCoord_eq_add` (47), `integral_norm_sq_weightedLaplacianVec_ge` (45) | partial (supplied pair) | `Analysis/BakryEmery/TensorEnergy.lean` |
| Corollary 3.5 | `summable_and_tendsto_zero_of_energy`; `summable_and_tendsto_zero_of_poisson_chain` (sequence of tensor iterates, levels linked by linear isometries) | partial (supplied sequence) | same |
| (35), (36), Lemma 3.2 | `integral_norm_sq_gradCoord_sub_eq_of_normalized`, `integral_norm_sq_gradCoord_eq_add_sum`; `gradCoord_gradCoord_symm`, `exists_symm_integral_norm_sq_sub_le` (squared form of (38); (33) not needed) | partial (supplied pair/sequence) | same |
| Lemma 3.3, case `q = 2` | `swapFirstTwo`, `symmetrizeFirstTwo`, `norm_sub_symmetrizeFirstTwo_le`, `integral_norm_sq_sub_symmetrizeFirstTwo_le` (generic), `KLS.LogConcave.integral_norm_sq_sub_symmetrizeFirstTwo_le_mul` (heat model, `C χ`) | partial (`q ≥ 3` not proved) | `TensorEnergy.lean`, `HeatSemigroup/Temperate.lean` |
| (61) and the `p₁` bound (steps of Lemma 3.9) | `integral_fderiv_apply_eq_smul_taylorTensor_one`, `norm_sq_integral_gradCoord_eq` (`‖∫∇h‖² = α² Σ_i ‖T₁(∇₀g)(e_i)‖²` for a supplied pair); `norm_sq_integral_gradient_le_of_eigen` (`‖∫∇f‖² ≤ λ²K‖f‖²` for a supplied centered eigenfunction) | partial | `Analysis/BakryEmery/TensorEnergy.lean` |
| Lemma 2.1, componentwise tensor lift (operator domain) | `L2.mean_compLp_innerSL`, `L2.sum_norm_sq_compLp_innerSL` (Parseval); `KLS.LogConcave.existsUnique_centered_adjointComp_eq_components(_of_hessian)`; `RegularPotential.existsUnique_centered_adjointComp_eq_components` | partial | `L2/Components.lean`, `KLS/LogConcave/HeatSemigroup/Inverse.lean`, `KLS/LogConcave/Regular.lean` |
| Lemma 2.1 on `𝒜` (bridge) | `KLS.LogConcave.exists_toLp_mem_closedWeightedOperator_domain_of_hasTemperateGrowth` (`T̄[f] = [∇f]`), `exists_toLp_mem_adjointComp_domain_of_hasTemperateGrowth` (`A[f] = [−ℒf]`), `centered_inverse_eq_toLp_of_hasTemperateGrowth` | partial (existence of temperate solutions not proved) | `KLS/LogConcave/HeatSemigroup/Temperate.lean` |
| Energy bound of (20) on `𝒜`, (32), Lemma 3.2 with bound `C χ` (`C ≥ C_P`) | `integral_sq_sub_integral_le_of_hasTemperateGrowth`, `integral_norm_sq_sub_integral_le_of_hasTemperateGrowth` (Poincaré on `𝒜`), `integral_norm_sq_gradCoord_le_of_hasTemperateGrowth`, `one_le_mul_sq_of_poisson`, `exists_symm_integral_norm_sq_sub_le_mul` | partial (supplied pairs) | same |

Audit clients: `research/audits/BKLThirdCumulantWitnessAudit.lean` (the uniform law on
`[−√3, √3]` and the skewed two-point law `(1/5)δ₂ + (4/5)δ_{−1/2}` with `κ₃(1,1,1) = 3/2` discharge every
premise of the conditional Lemma 4.2, including the Letwin bound; 10 axiom reports) and
`research/audits/BKLRegularLawAudit.lean` (the scaled Gaussian as a regular potential; consumers of
Lemmas 3.2–3.4 (generalized forms), Corollary 3.5 on an explicit chain, (36), the tensor lift, the
generator on `𝒜`, the Poincaré inequality on `𝒜`, and the `p₁` bound on the eigenfunction `⟪c, ·⟫`,
where it is an equality; 46 axiom reports). All reports list only `propext`, `Classical.choice`,
`Quot.sound`. No paper is newly covered; `KLS.kls` stays open.

## Decisions and corrections

- Batch N (eight-hour candidate) failed the strict build only through unused `[CompleteSpace E]`
  instances; repaired with explicit `omit … in` on three theorems, re-frozen and integrated after
  Codex review N (accepted as conditional).
- The regular-law structure holds only the assumptions of (12); every analytic premise of the earlier
  general theorems is derived. `law` is `volume.tilted (-V)`, so the source's normalized potential is
  `V + log Z` (documented).
- Lemmas 3.2–3.4 (3.3 for `q = 2`), Corollary 3.5, (35)–(36) and the steps of Lemma 3.9 take the
  pairs, the sequence or the eigenfunction as hypotheses: the
  identities (39) and (47) are derived, not assumed, and `α = 0` is included. The source's iterates
  (Lemma 2.1 on `𝒜`, the first eigenfunction) are not constructed. Codex's final review recommended
  the relation partial for these (adopted) and same for (12).
- Lemma 3.2 does not use the normalization (33); the hypothesis was dropped. Its generic `α² ≥ λ`
  premise is discharged in the heat model: for temperate pairs, (32) `1 ≤ C α²` (`C ≥ C_P`) follows from
  the Poincaré inequality on `𝒜`, and Lemma 3.2 holds with the bound `C χ` (`λ = 1/C ≤ λ₁`).
- Several statements were strengthened at integration by dropping unused hypotheses: (33) in
  Lemma 3.2, `hg` in (32), `hνU`/`hU` in the gradient-domain bridge. The `p₁` bound assumes `0 ≤ K`
  for convenience; Codex noted it is redundant (in dimension `0` the other hypotheses force `f = 0`).
- Batches whose first frozen statements could not be stated in the needed context were re-frozen
  without mathematical change (`Q-Temperate.frozen2.lean`: an extra import; `K-Spectral.frozen2.lean`:
  `include m` for the Haar measure of the closed gradient).
- The classical-to-`L²` bridge (temperate `f` lies in the generator domain, `A[f] = [−ℒf]`) identifies
  the centered operator-domain inverse with any centered temperate solution; the existence of such a
  solution for `g ∈ 𝒜₀` (the regularity part of Lemma 2.1) remains open.
- Production uses the Luna proofs for three statements where both Luna and Codex passed the gates
  (EN6, EN8, RG2); provenance is in `accepted-statements.csv`.
- Within the block no commit, push, tag, remote CI, Prove2Me action, Slack message or memory update
  was made; the commit and push followed afterwards at the owner's request, without remote CI.
