# Current KLS handoff

Updated 2026-10-16 at the weak trace, Theorem 2.5 and source Stein integration. The previous handoff is preserved
byte for byte in [the dated archive](research/decisions/2026-10-16-pre-weak-trace-t25-stein-handoff.md).
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

The actual regular source law produces a C¹ moment potential u with Lipschitz gradient from the
original R0 hypotheses, with every R0 field and an actual weak third-derivative tensor T, L² on
compact sets. Canonical supports include:
- the N10b generator identities (2.2) and the N11b Hessian-increment estimate;
- weak product and matrix-polynomial calculus and the determinant/Jacobi identification;
- the first weak Monge–Ampère identity (2.4) and the weak inverse formula (2.5);
- the rough compact curl identity, the C¹ unprimed generator identity and the actual mean Hessian Id;
- the weighted weak second Hessian evolution (2.6) and its bounded H¹ tests ψ·H_lk
  ([weak evolution record](research/decisions/2026-10-16-weak-hessian-evolution-h1-integration.md));
- the C¹ weak inverse-Hessian height cutoffs with C/R generator defect, also at the actual source witness
  ([weak cutoff record](research/decisions/2026-10-16-weak-inverse-hessian-cutoff-integration.md)).

See the [declarations and owners](research/progress/PROOF-PATH.md#stage-1-letwins-constant-8).

The weak trace, Theorem 2.5 and source Stein package is now canonical
([record](research/decisions/2026-10-16-weak-trace-t25-stein-integration.md)):
- **Generic tools** (every finite dimension unless stated):
  - the compact flux identity against globally bounded weak tests;
  - bounded weak trace-quadratic and matrix-product data, and rough tests against the C¹ cutoff generator;
  - the weak trace contraction (2.8)/(2.10) for arbitrary rough fields, its pointwise positivity and the trace-Gram
    comparison (2.12): 0 ≤ D and 4D ≤ g + 2 tr(BHBH);
  - the weighted-Laplacian pairing, C^{1,1} ordinary-diffusion coercivity and the weak finite-energy Brascamp–Lieb
    inequality (A.6) for a given C¹ globally Lipschitz potential with Lipschitz gradient;
  - matrix product/trace and variance identities, and the given-potential weak Theorem 2.5 bound
    `KLS.LogConcave.integral_trace_quadratic_le_two_mul_trace_sq` for positive semidefinite B, whose mean-Hessian,
    integrable-D and half-energy inputs remain hypotheses;
  - the almost-everywhere PSD symmetric trace extension;
  - zero integral of integrable weak derivatives, tilted integration by parts for bounded Lipschitz tests, the C¹
    gradient chain and the latent source Stein identity for a C¹ globally Lipschitz u with Lipschitz gradient;
  - the compact dual Cauchy–Schwarz bound from a latent source identity, and the Gaussian directional identity.
- **Actual source:** `Analysis.exists_regular_moment_bounded_weak_cutoff_testing` (rough cutoff testing at the same
  witness) and `Analysis.exists_regular_moment_weak_stein_coupling`: from the original R0 hypotheses, ONE u, L, LF and T
  with the whole earlier payload, A.5 conservativity ∫ g dν = 0 and the half energy for every PSD B, and
  E_ν tr(B∇²u B∇²u) ≤ 2 tr(B²) for every real symmetric B (exact constant 2, weak C^{1,1} form), with the
  bounded-Lipschitz weighted integration by parts and the coordinate source Stein identity. The audit
  `research/audits/BKL/WeakHessianTraceAudit.lean` projects every earlier public contract from this witness.

This is a weak C^{1,1} counterpart at the actual regular source witness, not the smooth moment map of Lemma 2.2 and not
the paper's Theorem 2.5 as stated; T25 stays partial. No Stein kernel or Gaussian product coupling is constructed.
Theorem 1.2, the compact constant 8 and KLS are open. The 30 ledger certificates and paper coverage are unchanged.

## Evidence

- The canonical source snapshot `3af79a97…` (25 files) is a byte-exact copy of the independently accepted prototype
  (strict production 98 and audits 62 with warnings as errors, complete ModuleData semantics, 392 axiom reports all
  standard, kernel replay 98). Codex accepted the source copy
  (`weak-trace-theorem25-stein-integration/canonical-phase1/CODEX-CANONICAL-SOURCE-ACCEPTANCE.json` in the ignored Goal
  control directory).
- The earlier full receipts (latest `5c139a30…`, snapshot `ef51…`) do not cover this source or this metadata. A fresh
  full local verification of the current source/meta snapshot is pending; no current-full claim is made before an exact
  report. See [receipt scope](research/verification.md#receipts-and-trust-scope).

## API status

The S3 Gaussian product source-pairing task ran once with the unchanged loop (gpt-6-astra/high, max_rounds 4,
max_queries 6). It exited naturally after 4 rounds and 1 executed query with no accepted proof; the 939-file run is
sealed and independently failure-reviewed. Rounds 1–3 compiled the unchanged frozen statement, because the fixed loop
executes a query block only when a response contains no Lean block. No equivalent resend, failed-body repair or
parser/controller change is authorized. The API is idle.

Scratch build evidence (the S2 continuity / Lemma A.2 work, the directional and affine helpers, the Gaussian L4
prototype and the S3 Expected preflight) is separate and not part of this formal status.

## Next obligations and coordination

1. The Gaussian product coupling of the actual source law: product integrability, the translated Gaussian and
   Fubini, by fresh reuse of the canonical closed supports.
2. The compact dual Cauchy–Schwarz bound from the latent source identity.
3. The H⁻¹ variance inequality (HminusOne) on the actual C² convex Gaussian-smoothed law.
4. The spectral/invertible constant-8 assembly and the noise removal.
5. The singular-matrix extension (Lemma A.2).
6. The regular-class/Lemma A.1 compact constant-8 bound.

A target Stein kernel or inverse transport of the coupling is an optional alternate support route, not a required
prerequisite: the genuine latent source identity supplies the compact dual bound directly.

The Goal is coordinated by the current Codex chat (`01a13ea4-f340-73b1-bbe8-af9381f33679`) and the
original Claude session. Codex freezes sources, statements, dependencies and placement, then
independently accepts. Claude runs one unchanged gpt-6-astra/high API loop at a time
(max_rounds 4, max_queries 6) and is the sole canonical integrator after placement review. No
commit, push, tag, remote CI or publication is authorized. The old large loops and other roadmap
stages stay stopped. The [Goal record](research/handoffs/2026-10-14-bkl-step1-letwin-constant-eight.md)
retains the endpoint and acceptance protocol; historical queues do not override this handoff.
