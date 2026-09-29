# Borell Density Representation: Proofs of Five Obligations and Certificate Registration

Date: 2026-09-07 (Asia/Shanghai). Baseline: uncommitted working tree atop `0451f2e`, starting at
[statement draft and semantic alignment record](2026-09-07-borell-density-statements.md). Lean/Mathlib is v4.33.0,
Mathlib commit `db584cd6d46c92f209a44c0f1c829460d327499d`. User instruction: "By the way, fix that sorry too".
This decision does not involve commit, push, remote CI, or Pages deployment.

During this period, another session relocated the module to `KLS/LogConcave/`, and `BorellRepresentation.lean` moved with it, see the [migration record](../explorations/2026-09-07-logconcave-module-layout.md). The decision completes the proof on the new path; the old path referenced in the statement record was the fact at the time and is not rewritten.

## Overview of Results

| goal | before | now |
| --- | --- | --- |
| `LogConcave.exists_isBorellDensity` | `sorry` | proved |
| `IsBorellDensity.pos_of_mem_interior_support` | `sorry` | proved |
| `IsBorellDensity.exists_bounds_of_isCompact` | `sorry` | proved |
| `LogConcave.intrinsic_integrable_exp_norm` | `sorry` | proved |
| `LogConcave.intrinsic_integrable_norm_pow` | `sorry` | proved |
| ledger `thm:borell-logconcave-density` | `drafted / null` | `proved / lean` |
| `check_blueprint.CERTIFICATES` | eleven mappings | twelve mappings |
| Blueprint this node | three anchors, no `leanok` | nine anchors, both declared and proved `leanok` |

The signatures of the five statements are identical to those in the statement record; no changes have been made to any premises, conclusions, or quantifiers.
`Solutions.ThmBorellLogconcaveDensity.certificate` is the only certification, providing a single bundle for existence, positivity, compactness bound,
closed convex hull identity, zero measure of interior complements, exponential moments and all-order moments; the certification file adds standard axiomatic guards to both the certification and the nine library-level statements.

## Proof path

Three sections are added to the module, all within the `FunctionalInequalities.KLS` namespace.

**Representative property (`IsBorellDensity.*`).** `convex_pos`: The positive set is convex under real power log-concavity.
`concaveOn_log`: `log ρ` is concave on the positive set. `measure_compl_pos`: `ν` is zero on the complement of the positive set.
`interior_support_subset`: If the interior of the positive set is empty, then it lies in a proper affine subspace, Haar null (`Measure.addHaar_affineSubspace`), hence `ν = 0`, a contradiction; thus the support is contained in the closure of the positive set, and by `Convex.interior_closure_eq_interior_of_nonempty_interior` we obtain
`interior supp ⊆ interior {ρ > 0}`. Positivity is a consequence. Upper bound on compact sets comes from
`UpperSemicontinuousOn.bddAbove_of_isCompact`; lower bound comes from Mathlib's
`ConcaveOn.continuousOn_interior`: `log ρ` is continuous on the interior of the positive set, `ρ = exp ∘ log ρ` attains a positive minimum value on compact sets.

**Moments (`BorelLogConcave.*`).** `measure_norm_ge_le`: Borell's lemma. Take `t = 2/(k+1)`,
`B₀ = {‖v‖ ≥ kR}`, `B₁ = ball 0 R`, their combination lies within `(closedBall 0 R)ᶜ`; expressed using previously proven Borel sets
(`LogConcave.borel_iff`) and `innerMeasure_le` yield `ν(B₀)^t · (3/4) ≤ 1/4`, then take the `1/t`th root to get
`ν(B₀) ≤ 3^{(1-k)/2}` (when `k < 2` holds with `ν ≤ 1`). `exists_integrable_exp_norm`: By exhaustion by balls,
Integer radius `R ≥ 1` ensures `ν(ball 0 R) ≥ 3/4`; take `t₀ = log 3 / (4R)`, using
`exp(t₀‖v‖) ≤ Σ_k exp(t₀(k+1)R)·1_{‖v‖ ≥ kR}` Pointwise control (`k = ⌊‖v‖/R⌋`), `lintegral_tsum`
After exchange, each term equals `3^{(k+1)/4} · 3^{(1-k)/2} = 3^{3/4}·(3^{-1/4})^k`, and the geometric series is summable,
`ENNReal.ofReal_tsum_of_nonneg` Give finiteness. `integrable_norm_pow_of_integrable_exp_norm`:
`exp(-t‖v‖) ≤ 1` integrable, Mathlib `integrable_pow_abs_of_integrable_exp_mul` gives all moments.

**Construction (`BorellRepresentation.*`, `LogConcave.exists_isBorellDensity_of_interior_support_nonempty`).**
`radius n = 1/(n+1)`; `ballRatio n x = ν(closedBall x rₙ)/m(closedBall 0 rₙ)`, measurability is given by
`measurable_measure_prodMk_left`; `lowerDensity = liminf ballRatio`. Three properties:
Bounded, by `LogConcave.exists_eventually_closedBall_le` along `rₙ → 0⁺`; a.e. equal to
`ν.rnDeriv m`, by `Besicovitch.ae_tendsto_rnDeriv` and `Measure.addHaar_closedBall_center`;
log-concave, by `LogConcave.closedBall_mul_le` (log-concavity of masses of balls of equal radii)
`liminf_eq_iSup_iInf_of_nat`, `ENNReal.orderIsoRpow` and `ENNReal.iSup_mul` pass to the lower limit.
`envelope x = ⨅ n, ⨆ y ∈ ball x rₙ, lowerDensity y`: not less than `lowerDensity`, bounded, upper semicontinuous
(using ball inclusions with halved radii), log-concave (combined points remain in balls of the same radius; compare for each `n`, then take the infimum), and equal to
`lowerDensity` Equal everywhere outside the boundary of the convex positivity set: zero outside the closure; inside, `log` finite concave thus continuous
(`concaveOn_log_toReal_of_logConcave`), the envelope value does not increase. The boundary of a convex set has Haar measure zero.
(`Convex.addHaar_frontier`), hence `withDensity` is the same, and then by `withDensity_rnDeriv_eq` we obtain `ν`.
Final `ρ = (envelope ·).toReal`: measurable (upper semicontinuous), non-negative, upper semicontinuous, log-concave (`toReal` monotonic transitive).

The intrinsic version is directly instantiated by `hμ.intrinsicMeasure`, `interior_intrinsic_support_nonempty`, `intrinsic_absolutelyContinuous`, and `borel_iff`. No special treatment is needed for the zero-dimensional direction space.

## Metadata Synchronization

- ledger: node updated to `proved / lean`, statement restated as the seven conclusions of certificate packing, source appended with this record.
- `check_blueprint.CERTIFICATES`: new mapping added; Blueprint theorem block anchors five theorems, predicates, two identities, and a certificate, declares and proves marked `leanok`, proof text updated to actual argument.
- tasks.json: infrastructure changed to `available`, gaps cleared, evidence added `Borel.lean`, Mathlib `Besicovitch.lean`, and `Convex/Continuous.lean`, and all hashes refreshed.
- Current guide (HANDOFF, README, `verification.md`, `solutions/README.md`, `formalization/README.md`, `KLS/README.md`, `KLS/LogConcave/README.md`) updates drafted descriptions to proved, certificate count changed to twelve. HANDOFF's "unverified statements" list removes the Borell representation item; corresponding item in subsequent workflow is rewritten.
- statement golden, `STATEMENT_CHECKS`, `FoundationAxiomAudit`, and route configuration remain unchanged.

## Evidence Boundary

The certificate proves the statement and the three stronger forms indicated in the statement record; it does not claim Cheeger,
Dirichlet, spectral gap, affine whitening or KLS. Borell (1974) original PDF has not yet been read; local proof starts from the compact set convention
Independent argument, not dependent on word-for-word correspondence with the original. Final verification receipt issued by `python3 research/verify.py` for this decision and all guidelines
Generated after editing, its source code SHA is recorded in the receipt itself, not written back to this file. Local kernel replay trusts third-party compiled imports;
No isolation reconstruction, remote CI, or release.
