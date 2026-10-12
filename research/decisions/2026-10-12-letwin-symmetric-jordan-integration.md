# Letwin Theorem 2.5 matrix support: symmetric Jordan decomposition and trace energy

Date: 2026-10-12. Controller: Codex; integrator: the sole reviewed Claude conversation. Source: Letwin,
arXiv:2607.24164v1, Theorem 2.5 (the extension from positive semidefinite to all symmetric `B`, constant 2). This record
covers only generic real matrix algebra; Theorem 2.5 is not proved.

## Accepted input

The candidate `api-symmetric-compiler-patch-v3/candidate.lean` (SHA-256 `e735387e…`) in
`build/reviews/2026-10-12-bkl-letwin-t25-continuation/`:
- **Provenance.** The strong-API model gpt-6-astra (high) wrote the complete source and four literal compiler fixes;
  the controller changed no proof body.
- **Acceptance gates.** Strict compile, standard axioms for all 12 owned constants, candidate kernel replay, and an
  independent semantic review.

## Statements and placement

| Declaration | Owner | Scope |
| --- | --- | --- |
| `cfc_posSemidef_of_nonneg` | `Analysis/Matrix/Trace.lean` | a nonnegative real function of a symmetric matrix is positive semidefinite (through `cfc_eq_mul_diagonal_mul`) |
| `trace_cross_nonneg` | `Analysis/Matrix/Trace.lean` | `tr(P H N H) ≥ 0` for positive semidefinite `P`, `N` and symmetric `H` |
| `trace_energy_nonneg` | `Analysis/Matrix/Trace.lean` | `tr(B H B H) ≥ 0` for symmetric `B` and positive semidefinite `H` |
| `jordan_trace_domination` | `Analysis/Matrix/Trace.lean` | `tr((P − N) H (P − N) H) ≤ tr(P H P H) + tr(N H N H)`, no commutation |
| `symmetric_jordan_decomposition` | `Analysis/Matrix/Sign.lean` | derived positive semidefinite `P`, `N` with `B = P − N`, `P N = N P = 0`, `tr B² = tr P² + tr N²` |
| `symmetric_jordan_trace_support` | `Analysis/Matrix/Sign.lean` | the decomposition together with the domination |

All statements are for real matrices over any finite index type `ι` with decidable equality (the empty type included).

**Placement:**
- **Trace.lean** keeps the spectral positive-semidefinite helper next to the representation it uses. The two one-use
  helpers are private: `diagonal_posSemidef` and `real_posSemidef_isSymm`.
- **Sign.lean** holds the spectral Jordan parts. It now imports `Matrix/Trace.lean`; there is no cycle, since Trace
  imports only Mathlib.
- **Trace's new imports:** `Mathlib.Analysis.Matrix.Order` and `Mathlib.Tactic.NoncommRing`.
- **The new section's namespace block is reopened**, so its `ι : Type*` takes the universe `u_1` exactly as in the
  candidate. The file's earlier namespace-level `variable {n : Type*}` would otherwise shift it.
- **Names and bodies.** Public names are unchanged; the namespace is the existing `FunctionalInequalities.Analysis`.
  Proof bodies are verbatim, and there are no aliases.
- **Client.** The real indefinite, noncommuting `Fin 2` client is `research/audits/BKL/LetwinSymmetricJordanAudit.lean`.

## Comparison with the accepted candidate

All 12 candidate constants were mapped explicitly: 9 public, 1 private and 2 generated `_abel_1_1`. Kinds and ordered
universe parameters are equal. Every type is equal after replacing only the module component of compiler hygiene labels.
Ten values are equal under the same map. The two exceptions:
- **`symmetric_jordan_decomposition`.** Its proof term contains a different but equally typed instance proof for
  `T5Space ℝ`. The candidate, which imports all of Mathlib, has `T6Space.toT5Space`; canonical has
  `OrderTopology.t5Space ℝ`.
- **The audit client.** Its labels differ in macro-scope counters only.

Details and logs: `claude-y-jordan-trace-integration-v1/` in the same review directory.

## Open

The positive semidefinite integral bound, its measure extension, the moment map, Brascamp–Lieb, (2.12) for the
inverse-Hessian contractions, Letwin Theorems 2.5 and 1.2, BKL Lemma 4.2 without its hypothesis, BKL Theorems 4.1 and
1.1, and `KLS.kls`.
