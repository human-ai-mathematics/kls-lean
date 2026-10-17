# Current KLS handoff

Updated 2026-10-15 at the weak inverse (2.5) integration. The previous handoff is preserved byte
for byte in [the dated archive](research/decisions/2026-10-15-pre-weak-inverse-handoff.md).
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

The weak inverse formula (2.5) is now canonical
([weak inverse record](research/decisions/2026-10-15-weak-inverse-integration.md)).
`Analysis.exists_regular_moment_weak_inverse` starts from the original R0 hypotheses and retains
the same u, L, LF and T, every R0 field and every first-weak-Monge–Ampère field. For all k, i, j it
adds the weak derivative −(H⁻¹ T_k H⁻¹)_ij of (H⁻¹)_ij, L² on compact sets, and compact-local
essential bounds on (H⁻¹)_ij. No global inverse bound is claimed, and no inverse formula, C²
regularity or evolution identity is assumed as an input. The supports are the scalar rules
`hasWeakDerivAlong_exp_neg_of_lipschitz` (weak exp(−F) for globally Lipschitz F) and
`HasWeakDerivAlong.mul_of_locally_bounded` (products of compact-locally bounded factors), the matrix
identification `ae_weak_matrix_inverse_derivative` (a.e. DR = −R·DA·R from R·A = Id), the Piola
adjugate bound and weak adjugate derivative, and the intrinsic assembly
`hasWeakDerivAlong_inverse_hessian_of_logdet`. E3, E4 and E5 are now canonical supports.

These are supports; Lemma 2.4's second evolution identity (2.6), Theorem 2.5 and compact constant 8
are open. The 30 ledger certificates and paper coverage are unchanged.

## Evidence

- The previous full receipt `build/verification/20261015T015709.906783Z/report.json` passed for the
  published snapshot `a3805d3d…` (HEAD `2c3e369`). It covers only that baseline, not the weak
  inverse sources or this metadata.
- The six weak inverse source files passed local canonical checks: strict owners, aggregate and
  actual-source audit; 124 complete records equal to the reviewed prototype; 124 standard-axiom
  reports; 6 local kernel replays. Codex accepted the sources
  (`weak-inverse-integration/CODEX-SOURCE-ACCEPTANCE.json` in the ignored Goal control directory).
- Final acceptance requires a passing full receipt matching the current source/meta snapshot,
  bound in the ignored `weak-inverse-integration/` final acceptance/completion records; inspect
  `build/verification/latest.json` and the exact report. See
  [receipt scope](research/verification.md#receipts-and-trust-scope).

## Next obligations and coordination

1. Genuinely missing weak coefficient and curl testing interfaces, and bounded H¹ testing. A
   read-only gap review proposes a commutation (curl) identity tested against a compact rough H¹
   coefficient; it is not frozen, proved or dispatched.
2. Actual C¹/Lipschitz-gradient source-height cutoffs A.4/A.5, with locally L² flux and locally L¹
   right-hand sides.
3. The weak second evolution identity (2.6) and integrated energy comparison (2.14),
   E tr(BHBH) ≥ 2 E G₁.
4. Actual weak Brascamp–Lieb (A.6) and mean-Hessian (Lemma 2.3) consumers, then the Theorem 2.5 upper
   bound E tr(BHBH) ≤ 2 tr(B²).
5. Stein/H⁻¹, spectral, regular-class and compact constant-8 assembly.

Local L² of T gives only local L¹ of T². No C² upgrade, global inverse bound, global weighted
tensor-square estimate or assumed energy bound is available. The smooth A.4 and old N13c
local-L² right-hand-side interface do not close the weak-source gap.

The Goal is coordinated by the current Codex chat (`01a13ea4-f340-73b1-bbe8-af9381f33679`) and the
original Claude session. Codex freezes sources, statements, dependencies and placement, then
independently accepts. Claude runs one unchanged gpt-6-astra/high API loop at a time
(max_rounds 4, max_queries 6) and integrates accepted proof packages after placement review.
The earlier documentation/accepted-proof publication checkpoint is complete and proof work has
resumed; no further commit, push, tag, remote CI or publication is authorized. The old large
loops and other roadmap stages stay stopped. The
[Goal record](research/handoffs/2026-10-14-bkl-step1-letwin-constant-eight.md) retains the endpoint
and acceptance protocol; historical queues do not override this handoff.
