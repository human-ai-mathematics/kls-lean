# Codex Handoff — Issue #2 Lean Linear-Test Poincaré Bound

**Status:** complete; semantic alignment and ledger binding recorded
**Repository:** `numina-functional-inequalities/kls-lean`  
**Working branch:** `codex/migrate-existing-work` during migration
**Destination base commit:** `40b07fdb49dd33fc55222458cad6827e509ff575`  
**Upstream synchronized through:** `cd4a89416562b1120ba9fa9526a5d6fe2ab3b7db`
**Primary orchestrator / ledger writer:** `lyw-ops`  
**Last updated:** 2026-08-31 (Asia/Shanghai)

This file is the mutable handoff for the Lean workstream. It records the current state and the
next exact action. Historical attempts, including dead ends, belong in new append-only files under
`research/explorations/`; do not use this file as a substitute for the required exploration log.

## 1. Required read order

Before changing anything, read:

1. `AGENTS.md` / `CLAUDE.md` — normative repository rules;
2. this file — current branch state and session protocol;
3. `formalization/README.md` — Lean architecture, pins, and planned module boundary;
4. `solutions/README.md` — proof certification conventions;
5. `research/README.md`, `research/ledger-schema.md`, `research/check_ledger.py`, and relevant
   tests;
6. the `research/a-series/ledger.yaml` entry `lem:linear-test-lower` and
   `solutions/glm-linear-baselines.tex`.

If this file conflicts with `AGENTS.md`, `AGENTS.md` wins.

## 2. Exact target

Bootstrap the repository's first reproducible Lean/mathlib project and machine-certify the ledger
node `lem:linear-test-lower`:

\[
C_P(\mu) \geq \lambda_{\max}(\operatorname{Cov}_\mu).
\]

The intended proof uses the linear test function

\[
f_v(x)=\langle v,x\rangle,
\qquad
\operatorname{Var}_\mu(f_v)=v^\top\operatorname{Cov}_\mu v,
\qquad
\nabla f_v=v.
\]

Thus a Poincaré inequality with constant `C` implies

\[
\operatorname{Var}_\mu\langle v,X\rangle \leq C\lVert v\rVert^2,
\]

then the Rayleigh variational bound gives
`lambdaMaxCovariance μ ≤ C`, and taking the optimal admissible constant gives the ledger theorem.

### Terminology

| 中文 | English |
|---|---|
| 庞加莱不等式 | Poincaré inequality |
| 狄利克雷能量 | Dirichlet energy |
| 协方差算子／协方差矩阵 | covariance operator / covariance matrix |
| 瑞利商 | Rayleigh quotient |
| 最优庞加莱常数 | optimal Poincaré constant |
| 弗雷歇导数 | Fréchet derivative |
| 有限二阶矩 | finite second moment |

## 3. Non-negotiable constraints

- **R1 never validates R2.** Numerical experiments may guide research but cannot certify this
  theorem.
- `checked_by: lean` is permitted only after the complete ledger statement, with all hypotheses,
  is compiled and semantically audited. A weaker Rayleigh-style lemma is not enough.
- The natural-language dossier `solutions/glm-linear-baselines.tex` must remain intact.
- `research/explorations/` is append-only: add dated files; never rewrite old attempts.
- The ledgers are single-writer files. Codex must not edit `research/a-series/ledger.yaml` or
  `research/kls/ledger.yaml` unless the
  current task explicitly identifies it as the orchestrator step. The default is **do not edit the
  ledger**.
- Protect existing work. Never run `git reset --hard`, `git clean -fd`, force-push, or overwrite
  uncommitted user changes.
- Do not expand this issue into Gaussian Poincaré, tensorization, LSI, Bakry–Émery,
  Otto–Villani, or the KLS proof backbone.

## 4. Current repository state

- The organization migration branch contains the complete Issue #2 work and includes the legacy
  source through `cd4a894` via merge commit `e78f707`. After the migration is merged, future work
  should branch from the organization repository's `main`; the former personal fork and upstream
  remain configured as recoverable legacy remotes.
- `formalization/` is pinned to Lean/mathlib `v4.33.0`. Its default `lake build` target compiles
  the reusable library, project theorem, and root-level node certificate.
- `FunctionalInequalities.Poincare` contains the complete fixed-constant linear-test proof,
  extended Rayleigh quotient, centered covariance operator, unit-sphere/eigenvalue bridge, and
  optimal-constant theorem.
- `solutions/LemLinearTestLower.lean` is the complete node-specific certificate for
  `lem:linear-test-lower`.
- The ledger node is `status: proved`, retains the natural-language dossier, and is now bound to
  the compiled node certificate through `checked_by: lean` and
  `lean_solution: solutions/LemLinearTestLower.lean`.
- The checker, schema, tests, solution conventions, formalization README, and `LEAN_DESIGN.md`
  now support explicit node-specific `lean_solution:` artifacts.

## 5. Planned implementation sequence

### Phase A — repository and Mathlib audit

- Inspect the exact ledger node, checker schema, tests, and proof dossier.
- Audit current Mathlib APIs for probability measures, variance, `MemLp`, finite-dimensional real
  inner-product spaces, Fréchet derivatives/gradients, covariance, quadratic forms, and spectral
  or Rayleigh bounds.
- Record concrete imports, declaration names, rejected approaches, and gaps in a new exploration
  log.

### Phase B — reproducible Lean bootstrap

Create a pinned project under `formalization/` such that a clean checkout supports:

```bash
cd formalization
lake build
```

The build must eventually include the node-specific certificate, not only the reusable library.
Document Lean/mathlib pins and dependency-update instructions.

### Phase C — reusable functional-inequality vocabulary

Introduce a minimal API for:

- variance and admissible test functions;
- Dirichlet energy;
- a predicate such as `HasPoincare μ C`;
- the optimal Poincaré constant;
- the finite-dimensional covariance/Rayleigh object required by the theorem.

Do not hard-code definitions solely for `lem:linear-test-lower`.

### Phase D — fixed-constant linear test

Prove that `HasPoincare μ C` implies, for every vector `v`,

\[
\operatorname{Var}_\mu\langle v,X\rangle \leq C\lVert v\rVert^2.
\]

All measurability, integrability, differentiability, finite-dimensionality, probability-measure,
and second-moment assumptions must be explicit or derived from explicit hypotheses.

### Phase E — covariance maximum and optimal constant

- Derive `lambdaMaxCovariance μ ≤ C` from the fixed-constant theorem.
- Connect this to the infimum/optimal Poincaré constant without reversing the `sInf` inequality.
- Handle the no-finite-constant / `+∞` case if the selected constant type permits it.
- Document whether the formal object is a covariance operator, a matrix, or a Rayleigh supremum,
  and justify that it matches the ledger's `λmax(Cov_μ)`.

### Phase F — certification and repository integration

- Add a thin node certificate such as `solutions/lem-linear-test-lower.lean`.
- Ensure `lake build` actually compiles that certificate.
- Extend `research/check_ledger.py` and its regression tests for the `lean_solution:` convention.
- Update `solutions/README.md` and `formalization/README.md`.
- Run the complete validation suite and persist a dated exploration log.
- Only then may the orchestrator update the ledger to `checked_by: lean`.

## 6. Resolved and open design questions

Decisions must follow a Mathlib audit and be recorded in an append-only exploration file.

1. **Resolved:** finite candidate constants use `ℝ`; the optimal constant uses `ENNReal` and is an
   `iInf` over valid `NNReal` constants, so absence of a finite constant is `⊤`.
2. **Resolved:** the manuscript-facing energy uses Mathlib's canonical `gradient` on a complete
   real inner-product space. `toDual_gradient` and the Riesz isometry prove equality with the
   Fréchet-derivative operator norm.
3. **Resolved:** the centered covariance object is the Riesz operator of Mathlib's
   `covarianceBilin`; its real Rayleigh supremum is mapped faithfully to `ENNReal`.
4. **Resolved:** the `Issue2Solutions` Lake library uses `srcDir = ".."`, so the default build
   compiles `solutions/LemLinearTestLower.lean`.
5. **Resolved:** the empty nonzero-vector/unit-sphere supremum in dimension zero is `0`.
6. **Resolved for this node:** `MemLp id 2 μ` and continuous-linear-map composition put every
   linear projection in `L²`; the project theorem exposes this moment hypothesis explicitly.
7. **Open beyond this node:** equivalence of the selected smooth finite-energy core with a closed
   Sobolev-domain or spectral-gap definition.

## 7. Session start protocol

Run and inspect, rather than assuming the worktree is clean:

```bash
git fetch origin
git switch main
git pull --ff-only origin main
git status --short --branch
cat AGENTS.md
cat CODEX_HANDOFF.md
```

Then:

- identify the current `HEAD` and the previous session's last pushed commit;
- inspect every pre-existing uncommitted change before editing;
- state one bounded session goal;
- do not edit the ledger unless explicitly acting as the sole orchestrator.

## 8. Session close protocol — commit and push are part of the task

A work session is not handed off until the organization repository contains its recoverable
branch state.

1. Run all validations relevant to the files changed. Record exact commands and whether each
   passed, failed, or was not run.
2. Update the **Current handoff** section below with the last commit, completed work, failures,
   blockers, and the next exact action.
3. For technical investigation or proof work, add a new dated append-only file under
   `research/explorations/`. Include dead ends and exact Mathlib declarations/imports discovered.
4. Inspect `git diff`, run `git diff --check`, and ensure no secret, build artifact, or unrelated
   user file is staged.
5. Commit the coherent session state. Incomplete but useful work may use a clearly labeled `wip:`
   commit only when the handoff states what fails. Never use a WIP commit to claim Lean
   certification.
6. Push the current topic branch to the organization repository and open a pull request:

```bash
git push -u origin HEAD
```

7. Verify that the push succeeded. Report the pushed commit SHA and validation results. Never say
   that work was uploaded merely because a local commit exists.

If the branch has diverged, stop and inspect; do not force-push. If credentials prevent a push,
leave the local commit intact and report that precise blocker.

## 9. Commit-message convention

Preferred examples:

```text
docs: initialize Issue 2 handoff
build(lean): bootstrap pinned formalization project
feat(lean): define reusable Poincare vocabulary
proof(lean): prove fixed-constant linear test bound
proof(lean): derive covariance Rayleigh lower bound
test(ledger): validate Lean solution artifacts
docs: record Lean API decisions and validation
wip(lean): record blocked covariance operator approach
```

Keep commits scoped and reviewable. Do not squash away failed approaches that the exploration log
must preserve.

## 10. Required validation commands at completion

```bash
python3 research/check_ledger.py
python3 -m unittest discover -s research/tests -p 'test_*.py'
cd formalization && lake build
```

Also run `git diff --check`. Additional targeted Lean or Python tests should be recorded in the
handoff and exploration log.

## 11. Current handoff

- **Last pushed branch state at session start:** `52726e12f4cb9073ba5a050bdcffbbefbf4a4e87`.
- **Coherent implementation commit:** `785e32461d2c73ee119532a41f83915a08e7e330`.
- **Semantic-alignment commit:** `6f6b33a1c1dd4df6055daa7379b5fbafdcf21d39` repairs every natural-language surface identified by
  the independent HOLD audit, records the cold follow-up PASS, and attaches the Lean certificate
  in the production ledger.
- **Fork main publication:** fork `main` was fast-forwarded and pushed to
  `4a765f925e0852b701c34b9ff2702b9b6841afb6`; remote verification returned the same SHA.
- **Upstream integration:** fetched both remotes and merged `upstream/main` through `cd4a894` in
  local merge commit `e78f707`; the merge was clean. The upstream Issue #2 branch still points to
  the old bootstrap base and contains no competing Lean implementation.
- **Semantic result:** `poincareRayleighQuotient` is defined directly in `ℝ≥0∞`, so positive
  variance over zero energy is `⊤` and every admissible test is covered. The positive-energy real
  quotient is a proved specialization. This repairs the ambiguity in the natural-language phrase
  “admissible nonconstant.”
- **Covariance result:** `centeredCovarianceOperator` is the Riesz operator of centered
  `covarianceBilin`, not Mathlib's uncentered second-moment operator. Its quadratic form equals
  linear-test variance under `MemLp id 2 μ`. `covarianceRayleighMax` equals the unit-sphere
  covariance supremum, is nonnegative, and is an actual eigenvalue in nontrivial finite dimension;
  `lambdaMaxCovariance.toReal` is exactly that value. Dimension zero is handled as `0`.
- **Certificate:** `FunctionalInequalities.Project.linearTestLowerCertificate` and
  `solutions/LemLinearTestLower.lean` cover both clauses of the ledger sentence: the extended
  Rayleigh bound for every admissible test and
  `lambdaMaxCovariance μ ≤ optimalPoincareConstant μ` on finite-dimensional Euclidean space with
  explicit probability and second-moment assumptions.
- **Repository integration:** the default Lake targets include the root certificate. The checker
  accepts explicit `lean_solution:` paths under `solutions/`, validates type/suffix/path/existence
  and node header, and preserves the adjacent-file fallback. Documentation and the append-only
  exploration/decision records are current.
- **Validation:** the working checkout's `lake build` passed all 2,946 jobs. A fresh local clone of
  implementation commit `785e324`, with no `.lake/`, downloaded the exact manifest revisions and
  completed a from-scratch `lake build` of 2,953 jobs, including the root node certificate. All 44
  checker tests passed; the production checker reported 2 ledgers, 195 nodes, 675 labels, and 0
  errors; the axiom audit found only `propext`, `Classical.choice`, and `Quot.sound`; no `sorry`,
  `admit`, or custom `axiom` was found; and `git diff --check` passed. The synchronized `main.tex`
  compiled to `output/pdf/main.pdf` (161 pages, 1,339,663 bytes); existing layout/destination
  warnings remain nonfatal.
- **Environment note:** macOS system Python 3.9 has PyYAML but lacks `tomllib`, while Homebrew
  Python 3.14 has `tomllib` but lacks PyYAML. The combined agent and unit checks therefore ran in
  an isolated `uv --with pyyaml` environment; no global package was installed.
- **Scoped change:** only the `lem:linear-test-lower` statement/certification fields in the
  A-series ledger changed. Its manuscript remark and the lemma/provenance portion of the shared
  `solutions/glm-linear-baselines.tex` dossier were aligned; the separate `thm:glm-fi` theorem and
  active agent certification were preserved. The KLS ledger is untouched. The pre-existing
  untracked `.DS_Store`, `output/` Finder metadata, and `ISSUE_2_CONTEXT_FOR_CHATGPT.md` were
  preserved and are excluded from this workstream change.
- **Semantic alignment:** the term-by-term comparison is persisted in
  `research/reviews/2026-08-29-lean-linear-test-semantic-followup.md`. An initial independent HOLD
  exposed missing natural-language hypotheses and boundary conventions; after repair, the cold
  follow-up found no residual mismatch in the node's finite-dimensional, finite-second-moment
  scope and explicitly excludes a smooth-core versus closed-Sobolev/spectral-gap equivalence.
- **Ledger transition:** the sole orchestrator retained
  `solution: solutions/glm-linear-baselines.tex`, set `checked_by: lean`, and added
  `lean_solution: solutions/LemLinearTestLower.lean`.
- **Organization migration:** the committed working tree is staged on
  `codex/migrate-existing-work`, based on the organization repository's initial `main`. `origin`
  now names `numina-functional-inequalities/kls-lean`; the previous personal fork and source
  repository remain available as `legacy-fork` and `legacy-upstream`.
- **Post-transition validation:** `lake build` completed 2,946 jobs; the production checker
  reported 2 ledgers, 195 nodes, 675 labels, and 0 errors; all 44 control-plane tests passed; and
  `git diff --check` passed. The repaired standalone dossier compiled to 2 pages and the complete
  manuscript compiled to 161 pages.
- **Next exact action:** no Issue #2 proof work remains. Future formalization of a closed Sobolev
  domain or spectral-gap equivalence must be a separate target and must not be inferred from this
  certificate.
