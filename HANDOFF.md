# Current KLS handoff

Updated 2026-10-15 for the documentation and accepted-proof checkpoint. The previous handoff is
preserved in [the dated archive](research/decisions/2026-10-15-pre-publication-handoff.md).
Use the [proof path](research/progress/PROOF-PATH.md) for source-to-Lean navigation and the
[paper register](research/progress/LITERATURE.md) for exact scope and coverage.

## Target and current boundary

The four-stage main line is **Letwin constant 8 → stochastic localization → BKL Theorem 4.1 → KLS**.
The selected target is stage 1, `KLS.LogConcave.Suspension.LetwinCompactBound`: Letwin
arXiv:2607.24164v1, Theorem 1.2 through Theorem 2.5, as used by BKL arXiv:2610.05474v1, Lemma 4.2.
It requires the exact constant 8 for every n > 0, every compactly supported isotropic log-concave
probability law and every self-adjoint real quadratic form, including singular and indefinite ones.

**This bound and dimension-free KLS remain open.** The regular-class bound is still an input to
`letwinCompactBound_of_regularClass`; BKL `theorem41` and `conjecture_of_letwinCompact` retain
`LetwinCompactBound` as a hypothesis. `KLS.kls` is the intentional hole outside certificate closures.
Stages 2–4 are queued for source/evidence review; their conditional assembly already exists.

## Accepted canonical frontier

The actual regular source law now produces a C¹ moment potential with Lipschitz gradient, every
original R0 field, and an actual weak third-derivative tensor T, L² on compact sets. Canonical
supports include the N10b generator identities (2.2), the N11b Hessian-increment estimate, weak
product and matrix-polynomial calculus, and the determinant/Jacobi identification.

`Analysis.exists_regular_moment_weak_first_derivative` retains the same u, L, LF and T and all R0
fields. It adds a globally Lipschitz exp(−u + W(∇u)), the weak determinant density det(H) tr(H⁻¹ T_k)
with compact-local L² control, the weak log-det derivative, and a.e.
tr(H⁻¹ T_k) = −∂_k u + Σ_a H_ka ∂_aW(∇u): the first weak Monge–Ampère identity (2.4).
See the [declarations and owners](research/progress/PROOF-PATH.md#stage-1-letwins-constant-8).
These are supports; Lemma 2.4's second evolution identity, Theorem 2.5 and compact constant 8 are open.
The 30 ledger certificates and paper coverage are unchanged.

## Evidence and unintegrated work

- The accepted canonical source/meta snapshot before this documentation cleanup is `d7503d7e…`,
  full receipt `build/verification/20261015T004538.149290Z/report.json`: 287 passing gates,
  273 research clients, 9,633 local declarations audited and 812 local modules replayed.
  `EX-first-MA-integration/canonical-independent/ACCEPTANCE.json` records independent acceptance,
  complete interface/proof comparison, standard axioms, strict clients and local kernel replay.
  Both paths are local artifacts under the ignored Goal control directory or verifier directory.
- Documentation edits change the full snapshot. This checkpoint needs a fresh full receipt;
  `build/verification/latest.json` identifies the latest attempt, which must pass and match the
  current content. See [receipt scope](research/verification.md#receipts-and-trust-scope).
- E3, the local weak derivative of exp(−F) for globally Lipschitz F, has independent scratch
  acceptance (`independent/E3/ACCEPTANCE.json`). It is not canonical or part of this commit.
- E4, the product rule with compact-local L∞ factors and compact-local L² derivatives, has an
  interface/client preflight only. No candidate run or accepted proof exists. No proof worker or
  KLS build is running at this checkpoint. Scratch status does not advance paper coverage.

## Next obligations and coordination

First finish the genuinely missing weak inverse/coefficient interfaces and bounded H¹ testing.
Then handle actual C¹/Lipschitz-gradient height cutoffs (A.4/A.5), the second evolution identity
and integrated energy comparison (2.14), E tr(BHBH) ≥ 2 E G₁. Actual weak Brascamp–Lieb (A.6) and
mean-Hessian (Lemma 2.3) consumers are then needed for the Theorem 2.5 upper bound
E tr(BHBH) ≤ 2 tr(B²), followed by Stein/H⁻¹ and the spectral/regular-class/compact-8 assembly.
Local L² of T gives only local L¹ of T²; no C² upgrade or global weighted T² estimate is available.
The smooth A.4 and old N13c local-L² right-hand-side interface do not close the weak-source gap.

Codex freezes sources, statements, dependencies and placement, then independently accepts.
The authorized existing Claude session runs one unchanged gpt-6-astra/high API loop at a time
(max_rounds 4, max_queries 6) and integrates accepted proof packages after placement review.
The old large loops and other roadmap stages stay stopped. The current user authorization covers
one commit and push of this documentation plus already accepted canonical proofs; it does not
publish scratch candidates or authorize a milestone tag or remote CI. Proof work is held during
this checkpoint. The [Goal record](research/handoffs/2026-10-14-bkl-step1-letwin-constant-eight.md)
retains the endpoint and acceptance protocol; historical queues do not override this handoff.
