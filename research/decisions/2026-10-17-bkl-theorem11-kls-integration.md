# BKL Theorem 1.1 and the KLS target: source scope review and integration

Date: 2026-10-17. Goal: BKL roadmap stage 4 ([Goal record](../handoffs/2026-10-17-bkl-step4-kls.md)). Stages 1–3 are
accepted. This record is the `target_review` of BKL2026 in `research/progress/literature.json`. It supersedes the
2026-09-19 rule ([target-theorem decision](2026-09-19-kls-target-theorem.md)) that kept `KLS.kls` as a deliberate `sorry` target.
That rule's record is unchanged.

## Pinned source

Bizeul–Klartag–Lehec, *Presenting a proof of the Kannan–Lovász–Simonovits conjecture*, arXiv:2610.05474v1, PDF SHA-256
`86824722318f2213daf5ae624391b41f76bb4d41118b1657db9ab00d2d1bb0db`. Codex retained extracted printed pages 2 and 30 in the ignored
Goal control directory (`codex-source-review/PINNED-SOURCE.json`).

- **Theorem 1.1, p. 2.** There is a universal constant C > 0 such that, for any dimension n ≥ 1 and any isotropic log-concave
  probability measure μ on ℝⁿ, C_P(μ) ≤ C.
  - **C_P.** It is the least constant in (5): Var_μ f ≤ C_P ∫|∇f|² dμ for locally Lipschitz f ∈ L²(μ).
  - **Equivalent form (6).** ‖Cov μ‖_op ≤ C_P(μ) ≤ C‖Cov μ‖_op for every log-concave μ. The right-hand inequality follows by an
    affine change of variables.
- **Proof, p. 30.**
  1. By the approximation of Section 2, μ may be taken regular.
  2. Theorem 4.1 and Proposition 7.1 with b = K^d(d!)² give |T_d f|² ≤ 2K^d‖f‖₂² ≤ (2K)^d‖f‖₂² for d ≥ 2.
  3. Isotropy gives |T_1 f| ≤ ‖f‖₂.
  4. Theorem 3.1 applies with R = √(2K), so C_P(μ) ≤ 2CK.

## Lean statements

**Certificate.** `Solutions.ThmBklPoincare.certificate` (`solutions/ThmBklPoincare.lean`, ledger and Blueprint
`thm:bkl-poincare`) is the literal source form:

`∃ C : NNReal, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∀ μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)), LogConcave μ → Isotropic μ →
Poincare.LocalSlope.Intrinsic.constant μ ≤ C`.

- **Order of quantifiers.** One positive constant is chosen before every dimension and law.
- **Premises.** There is no compactness, regularity or moment premise beyond isotropy.
- **C_P.** It is the literature local-slope constant `Intrinsic.constant`. For log-concave laws the local slope agrees with
  ‖∇f‖ almost everywhere (`def:literature-poincare-constant`, `thm:klartag-density-frontend-identification`).
- **`bound`.** It is `KLS.IsotropicBound.{0} C`, the same bound on every finite-dimensional real inner product space.

**Producer.** `FunctionalInequalities.KLS.BKL.Localization.theorem11 : ∃ C : NNReal, 0 < C ∧ KLS.IsotropicBound.{u} C` in
`formalization/FunctionalInequalities/KLS/BKL/Theorem41.lean`. Its proof:
- `localSlope_le_of_cumulantBound_all` fixes C_{3.1} before K and covers the regular reduction and Section 2;
- `theorem41 letwinCompactBound` supplies K ≥ 1;
- the result is C = 2·C_{3.1}·K.

**Project target, unchanged.**
- **`KLS.Conjecture`** (`KLS/Statement.lean`): one `C : NNReal` before every dimension and every log-concave law with
  finite second moment, with `Intrinsic.constant μ ≤ C · ‖Cov μ‖_op`. Dimension 0 and singular or affine supports are
  included.
- **`FunctionalInequalities.KLS.kls : Conjecture`** (`KLS/Target.lean`) is now `KLS.BKL.Localization.conjecture`, which
  is `conjecture_of_letwinCompact letwinCompactBound`. The latter applies `conjecture_of_cumulantBound` and the affine
  bridge `affineBound_of_isotropicBound`, `conjecture_of_affineBound` (`thm:affine-isotropic-reduction`) with the same
  constant. The audit client checks `KLS.Conjecture = ExpectedKls` by `rfl`.
- **(6), left-hand inequality.** It is the separate `lambdaMax_le_constant` (`Poincare/SmoothTest/Linear.lean`, linear tests) and is not part of the target.

**Names and imports.**
- `Theorem41.lean` gains `import FunctionalInequalities.KLS.Letwin.CompactBound` and the closed producers `theorem11` and
  `conjecture`. The conditional `lemma51Bound`, `theorem41Compact`, `theorem41` and `conjecture_of_letwinCompact` are
  unchanged.
- `Target.lean` imports `KLS.BKL.Theorem41` and remains the final leaf: only the aggregate root imports it.
- The certificate imports `Theorem41` only. The client `research/audits/BKL/KlsAudit.lean` imports the certificate and
  `KLS.Target`.

## Relation choice

The certificate states Theorem 1.1 itself. The BKL map nevertheless records the main item T11 as `alternative`, not `same`,
for the same reason as T41:
- the proof goes through the owner-selected cutoff stochastic-localization route (stage 2) and the compact-to-general
  passage, not the source's uncut Eldan process;
- `bound` also extends harmlessly to every finite-dimensional inner product space.

`same` is reserved for a source statement proved along the source's own route. Coverage is decided only by the registered
paper-target certificate, so the paper is covered in the exact sense of its main Theorem 1.1. Intermediate source
statements keep their own recorded scopes, and none is promoted:
- T41 stays alternative;
- L42, E95, L43, L51 and L52 stay partial;
- the uncut identities stay pending.

## Accepted source and evidence

**Accepted bytes.** Codex's source acceptance `codex-source-review/ACCEPTANCE.json` (`33c19016…`) accepts these SHA-256s:

| File | SHA-256 |
| --- | --- |
| `Theorem41.lean` | `0d95f363…` |
| `Target.lean` | `56c02254…` |
| `solutions/ThmBklPoincare.lean` | `aa06b7cf…` |
| `research/audits/BKL/KlsAudit.lean` | `8605bc4f…` |
| `research/verify.py` | `4c317de8…` |
| `research/tests/test_verify.py` | `ceba336f…` |

Both are in the ignored Goal control directory `build/reviews/2026-10-17-bkl-step4-kls-goal/`.

**Scratch candidate.** `candidate01/RESULT.json` (`1345f088…`) strictly compiles (warnings as errors) and kernel-replays the
four modules against a copy of the stage-3 receipt's complete 915-part registered view:
- strict logs: `307c5f6a…`, `28c46bab…`, `6ebd4de2…`, `8019c558…`;
- kernel logs: `920c50b1…`, `034af2ff…`, `635eb448…`, `b492679d…`.

**Codex's independent check.** `codex-source-review/candidate-review01/RESULT.json` (`c0cf6851…`) repeats this in its own
fresh complete view (10 strict and kernel checks).
- **Standard axioms only.** `KLS.kls`, `theorem11`, `conjecture`, `bound` and `certificate`, and the independent clients for:
  - the literal source theorem;
  - the original covariance target;
  - one positive constant for all dimensions;
  - singular covariance;
  - zero covariance.
- **Scope.** Kernel replay covers local modules with pinned compiled Mathlib imports. It is not a fresh reconstruction of
  every dependency.

## Verifier migration

The declaration audit no longer excludes `FunctionalInequalities.KLS.kls`. Every project-local declaration, the target
included, must use only `propext`, `Classical.choice` and `Quot.sound`, and `excluded_open_targets` is empty.

**Regressions.** The Python regressions reject:
- a `sorry` named `KLS.kls`;
- a wrapper of such a hole;

and accept a proved `KLS.kls` with standard axioms. Codex reviewed five direct positive and negative probes
(`codex-source-review/migration02/RESULT.json`, `a2fff724…`).

**Unchanged.** The vendor gate's exact list of five upstream `sorry` declarations stays isolated.

## Not claimed

- the uncut Eldan process (strong solution, uniqueness, non-explosion) and the literal stochastic identities (68)–(73);
- the infinite-horizon (95);
- Lemmas 4.3, 5.1 and 5.2 along the uncut process;
- Lemma 4.2 for every isotropic law with its own hypothesis;
- Letwin's noncompact Theorem 1.2 and Letwin's paper;
- the four exploratory routes of `route-composition.yaml`. They keep their open gates, and their any_of/all_of expressions
  are unchanged.

## Registration

- **Ledger and certificate map.** One proved `lemma` ledger node `thm:bkl-poincare`, one `CERTIFICATES` entry and one
  Solutions root. No second mapping for `conj:kls` is needed, and a duplicate mapping of the same ledger node would be
  rejected.
- **`conj:kls` claim.** The route claim is `proved` with local provenance (Blueprint chapter 00). Its local Lean evidence
  names `thm:bkl-poincare` and the actual declaration `FunctionalInequalities.KLS.kls`. The pinned upstream record of the
  node is not promoted.
- **Blueprint.** The block names `KLS.Conjecture` and `KLS.kls` with `\leanok`. Its proof uses `thm:bkl-poincare` and the
  affine/isotropic bridge.
- **Tasks.** The `conj:kls` task is `local_argument` with pinned infrastructure evidence.
- **Progress diagram.** A completed BKL literature route (T31, T41, Proposition 7.1 and the regular approximation → BKL
  Theorem 1.1, then AND with the affine/isotropic reduction → KLS) is shown separately. It is not a fifth exploratory
  route.
- **`Reduction.lean`.** It receives four documentation-only substitutions pointing to the closed producers; imports,
  declarations, types and proofs are unchanged.

## Acceptance

The milestone is accepted only with:
- a passed full local verification report (`python3 research/verify.py`) for the exact integrated source/meta snapshot;
- its independent acceptance.

The result is recorded in the Goal checkpoint (`STATE.json` of the ignored Goal control
directory). Each earlier report applies only to its recorded snapshot.
