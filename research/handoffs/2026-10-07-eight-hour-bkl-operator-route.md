# Eight-hour goal: BKL Theorem 3.1 through the operator domain

Owner goal, 2026-10-07: continue the operator route to the **exact statement** of
Bizeul–Klartag–Lehec Theorem 3.1, starting from the completed step 1. This instruction authorizes
local proof implementation, integration, model collaboration and verification; begin the work
rather than returning only a proposal.

## Baseline and precheck

Read `AGENTS.md`, `HANDOFF.md`, `research/workflow.md`, `research/naming.md` and the route record
`research/decisions/2026-10-07-bkl-operator-route.md` (the approximate-eigenfunction argument with
explicit errors, the step-1 results and the reassessed plan). Read the step-1 modules
`Analysis/Semigroup/Generated/ApproximateEigenvector.lean` and
`KLS/LogConcave/HeatSemigroup/{ApproximateEigenfunction,Hessian,Tilt,Inverse,Temperate}.lean`, the
`𝒜`-versions in `Analysis/BakryEmery/TensorEnergy.lean`, `Analysis/Tensor/*` (Lemma 2.2,
coefficient arrays) and the audit clients `research/audits/BKL*.lean`.

Verified before this goal: local `main` HEAD `b401a9f` (step 1; not pushed, `origin/main` =
`ca59365`), full local receipt `build/verification/20261007T104117.847445Z/report.json`. The
untracked `research/decisions/2026-10-07-three-paper-formalization-comparison.md` belongs to
another session: leave it untouched and unstaged. Save a fresh recoverable baseline at actual
start; do not reset, clean, discard, stage over or rewrite existing work.

Pinned source: arXiv:2610.05474v1, local PDF
`/Users/lyuyuwei/Documents/ChatGPT/KLS-paper-sources/2026-10-07/2610.05474v1.pdf`, SHA-256
`86824722318f2213daf5ae624391b41f76bb4d41118b1657db9ab00d2d1bb0db`. Keep the hypotheses, the
probability normalization, the tensor slot conventions (a derivative adds a new **first** index,
Taylor indices precede tensor indices) and Hilbert–Schmidt norms. The only sanctioned deviation is
the one recorded in the route record: an approximate eigenfunction with `‖Af − λf‖ ≤ ελ`,
`ε = 1/10`, replaces (19), so `α_i² ≤ 3λ` replaces (54) and the universal constant is enlarged.

## Targets in priority order

### 1. The iterates in `D(A)` and Lemmas 3.2, 3.4, Corollary 3.5 for them

Represent a tensor-valued `L²` field with `k` indices by its component family over
`Fin k → Fin n` (`n = finrank ℝ V`, the fixed `stdOrthonormalBasis`), each component in
`L²(ν)`; its norm is the Hilbert–Schmidt `L²` norm `(Σ_I ‖u_I‖²)^{1/2}`. Define, without new
conclusion-bearing structures:

- the centered gradient `∇₀h` of a family in `D(T̄)` (new first index `Fin.cons j I`, component
  `L2.center ⟪e_j, T̄ h_I⟫`), and the componentwise centered inverse of `A` (from
  `existsUnique_centered_adjointComp_eq`);
- `α_{i+1}` by (31), with `α_{i+1} = 0` and `h_{i+1} = 0` when `∇₀h_i = 0` (the source's
  linear case), and the recursion (30) from a supplied centered unit `h₁ = f ∈ D(A)`;
- `v_i`, `p_i`, `χ_i` by (34), (35), (37), with `∇²h_i` the weak Hessian of
  `HeatSemigroup/Hessian.lean`.

Prove for every `i`: components in `D(A)` and centered; (33); (35)–(36); `α_{i+1}² ≥ λ` when
`α_{i+1} > 0` (32) for `λ = 1/C`, `C_P ≤ C`; Lemma 3.2 with bound `χ_i/λ`; (39), (46)–(47) derived,
not assumed; Lemma 3.4 `‖Lh_i‖² ≥ ‖Lh_{i+1}‖² + χ_i + a v_i` under `∇²U ≥ a` (from
`sum_norm_sq_closedWeightedOperator_add_le`); Corollary 3.5 `v_N → 0` and the summed bounds
`Σχ_i ≤ ‖Lh₁‖²`. Handle the zero cases. These replace the "supplied iterates" hypotheses of the
`𝒜`-versions; keep those older results unchanged.

### 2. Lemma 3.3 for every `q`, and Corollary 3.7 on `D(A)`

Independent; run in parallel with the second half of target 1 once its definitions are frozen.

- Lemma 3.3: for `2 ≤ q ≤ i` and `0 < α_j² ≤ βλ` on `i − q + 2 ≤ j ≤ i`, bound
  `‖∇₀h_i − S_q∇₀h_i‖²` by an explicit `c(q, β)/λ · Σ_{j=i−q+1}^{i−1} χ_j` of the form `C^q` for
  fixed `β` (the source has `β = 2`; the route needs `β = 3`). Prove the commutation (42) of the
  transposition `τ_ℓ` with `α_j ∇₀(−L)⁻¹` from the componentwise definitions, the operator bound
  through (24), the telescoping (44) and `m ≤ q²` (or any explicit decomposition of permutations
  into adjacent transpositions with a stated length bound).
- Corollary 3.7: `S_{d+1}T_d(∇₀h_{i+1}) = T_{d+1}(−Lh_{i+1}) = α_{i+1}T_{d+1}(∇₀h_i)` for the
  iterates, componentwise from `taylorTensor_adjointComp_eq`, centering and linearity of `T_d`.

### 3. Lemma 3.8 and Lemma 3.9

Lemma 3.8 with `(βλ)^d` in (57), through `coordTensor` arrays, `symmetrize` and the proved
Lemma 2.2 (`norm_le_four_pow_mul_norm_symmetrize`), with hypothesis (29) applied componentwise in
the Hilbert–Schmidt norm. Lemma 3.9 in the route form
`Σ_{i≤N} p_i ≤ (1+ε)²λ² + βλ Σ_{i<N}|T₁(∇₀h_i)|²`, including the `p₁` bound through linear
functions and `Cov μ ≤ Id` (the scalar step `norm_sq_integral_gradient_le_of_eigen` exists for
an exact eigenfunction; prove the approximate version).

### 4. Stretch: the statement and proof of Theorem 3.1

Freeze the exact Lean statement first and obtain independent review before proving it: there is
a universal constant `C` such that for every `n`, every regular potential `V` on
`EuclideanSpace ℝ (Fin n)` (`KLS.RegularPotential V a b`) whose law is centered with
`Cov ≤ Id`, and every `R ≥ 1` with `‖T_d f‖_HS ≤ R^d ‖f‖₂` for all `f ∈ L²` and `d ≥ 1`, the
literature Poincaré constant satisfies `C_P ≤ C R²`. Prove it by the final argument of the route
record (minimal `N` with `v_{N+1} < λ/2`, the dyadic summation of (63), the contradiction).
Dimension `0` and `C_P = 0` are separate trivial cases. Register a certificate only for the
faithful statement with complete verification; a conditional or heat-model-only form stays a
supporting result.

If a target stalls on a missing general fact, isolate it as a named lemma with its own route
statement and continue the next ready target; do not leave the block surveying.

## Placement (refine and record before editing)

Iterate definitions and target 1 in `KLS/LogConcave/HeatSemigroup/Iterates.lean`; Lemma 3.3 and
Corollary 3.7 in `HeatSemigroup/IterateSymmetry.lean`; Lemmas 3.8, 3.9 and the heat-model
criterion in `HeatSemigroup/TaylorCriterion.lean`; the source statement for regular laws through
`KLS/LogConcave/Regular.lean` or a new `KLS/LogConcave/TaylorCriterion.lean`. Generic
permutation/tensor tools belong in `Analysis/Tensor/`. Write route statements first in
`research/audits/BKLIterateRouteStatements.lean` (`#check` propositions only), then one audit
client per proved group restating its propositions verbatim.

## Roles, models and resources

Same arrangement as the 2026-10-07 four-hour block: Claude owns exact statements, decomposition,
placement, acceptance, production edits and integration (one editor per production file);
parallel proof workers take frozen statements in new files only, compile with
`lake env lean -DwarningAsError=true`, never run `lake build`, `verify.py` or state-changing git;
the owner's existing Luna API configuration and signed-in Codex are used as authorized there, with
Codex for hard strategy and independent semantic/axiom review. Do not change credentials,
providers or authentication; never log secrets. Record provenance for accepted statements.

## Eight-hour window

Record actual `T0` and deadlines (Asia/Shanghai) in
`build/reviews/2026-10-07-bkl-operator-route/execution.json`.

| Elapsed time | Action |
| --- | --- |
| 0:00-0:30 | Fresh baseline; freeze iterate definitions and route statements for targets 1–2. |
| 0:30-3:30 | Target 1; target 2 in parallel once definitions compile. |
| 3:30-5:30 | Target 3; freeze and review the Theorem 3.1 statement. |
| 5:30-6:30 | Target 4 if ready; otherwise the strongest coherent endpoint and independent review. |
| 6:30 | Stop opening new targets; bound outstanding proof searches. |
| 7:00 | Freeze source and metadata; start the final full local verifier. |
| 8:00 | Hard stop; end this block's workers, preserve evidence and hand off. |

Use a local deadline supervisor independent of model responses; control only this task's
children. Checkpoint accepted proofs and the queue so compaction resumes this goal. Do not restart
the clock or extend beyond eight hours.

## Verification and delivery

Follow `research/workflow.md` and `research/naming.md`. No wrappers, placeholders, empty modules,
nonstandard axioms, suppressed warnings or weakened source targets; only `propext`,
`Classical.choice`, `Quot.sound`. Every accepted endpoint needs strict compilation, a real consumer,
elaborated-type review and `#print axioms`. Update the BKL lemma map (`✓`/`⇑`/`◐`/`○`), Blueprint,
`nodes.json`, evidence hashes and live progress only for accepted results; Lemma 2.1 on `𝒜` and
(19) stay partial. Regenerate views from the staged canonical records, run
`python3 research/verify.py` on the frozen tree and report its exact receipt.

No commit, push, tag, remote CI, memory update or credential change without a separate owner
instruction. Save `WORKLOG.md`, `accepted-statements.csv`, provenance, reviews, the receipt
pointer and `FINAL.md` under `build/reviews/2026-10-07-bkl-operator-route/`. End with a concise
Chinese account of the proved statements and their exact scope, the unchanged gaps, model use,
actual execution times, verification, and the next three proof tasks.
