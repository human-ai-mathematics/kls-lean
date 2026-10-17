# Current KLS handoff

Updated 2026-10-15 at the curl and mean-Hessian support integration. The previous handoff is
preserved byte for byte in [the dated archive](research/decisions/2026-10-15-pre-curl-mean-support-handoff.md).
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
compact sets. Canonical supports include the N10b generator identities (2.2), the N11b
Hessian-increment estimate, weak product and matrix-polynomial calculus, the determinant/Jacobi
identification, the first weak Monge–Ampère identity (2.4) and the weak inverse formula (2.5)
(`exists_regular_moment_weak_inverse`: weak derivative −(H⁻¹ T_k H⁻¹)_ij, L² on compact sets, and
compact-local essential inverse bounds). See the
[declarations and owners](research/progress/PROOF-PATH.md#stage-1-letwins-constant-8).

The curl and mean-Hessian supports are now canonical
([curl/mean support record](research/decisions/2026-10-15-curl-mean-support-integration.md)):
- `Analysis.exists_contDiff_compact_weak_deriv_approximation` (H1b): a compactly supported rough η
  whose weak derivatives a, b along v, w are compactly supported and globally L² admits smooth θ_m
  with one common compact support whose two directional derivatives converge to a and b in global L².
- `Analysis.integral_weakDeriv_mul_eq_swap` (H1c, the original H1a statement): if p and q are weak
  derivatives of the same f along v and w, L² on compact sets, then ∫ p·b = ∫ q·a for every such η.
  Every finite dimension and both directions, zero included; no C¹ η or global L² p, q.
- `Analysis.integral_mul_generator_eq_neg_energy_of_contDiff_one`: the unprimed weak generator
  identity (2.2) for C¹ compactly supported multipliers η; the primed form still uses C² η.
- `Analysis.exists_regular_moment_weak_inverse_mean_hessian`: from the original R0 hypotheses, with the
  same u, L, LF and T and every inverse and first-weak-Monge–Ampère field, the actual Hessian entries
  are integrable for ν = e^{−u} dx and have mean Id (Lemma 2.3 for the actual R0 source potential). It reuses
  the existing C¹,¹ mean-Hessian identity and isotropy; no analytic premise is added.

These are supports. The weak second evolution identity (2.6), Theorem 2.5 and compact constant 8 are
open. The actual source mean is proved under C¹/Lipschitz-gradient hypotheses; the full smoothness and
diffeomorphism properties of the paper's Lemma 2.2 are not asserted. The 30 ledger certificates and
paper coverage are unchanged.

## Evidence

- The full receipt `build/verification/20261015T085050.186417Z/report.json`, with Codex canonical
  acceptance of the weak inverse package, covers only the snapshot `d99c763b…`, not the curl/mean
  sources or this metadata.
- The four curl/mean source files passed local canonical checks: strict owners, aggregate and
  actual-source audit; 86 complete records (77 old ones unchanged) equal to the accepted production
  prototype; 86 standard-axiom reports; 4 local kernel replays. Codex accepted the sources
  (`curl-mean-support-integration/CODEX-SOURCE-ACCEPTANCE.json` in the ignored Goal control directory).
- Final acceptance requires a passing full receipt matching the current source/meta snapshot, bound
  in the ignored `curl-mean-support-integration/` final acceptance/completion records; inspect
  `build/verification/latest.json` and the exact report. See
  [receipt scope](research/verification.md#receipts-and-trust-scope).

## Next obligations and coordination

1. The actual weak second Monge–Ampère identity (2.6): produce the weak derivative of the
   right-hand side q_i, identify the Piola divergence of R = H⁻¹, and consume the proved rough curl.
2. Bounded H¹ testing with locally L¹ forcing, and the actual C¹/Lipschitz-gradient source-height
   cutoffs A.4/A.5 with locally L² flux, leading to the integrated energy comparison (2.14),
   E tr(BHBH) ≥ 2 E G₁.
3. The actual weak Brascamp–Lieb (A.6) consumer and the Theorem 2.5 upper bound
   E tr(BHBH) ≤ 2 tr(B²). The actual mean Hessian Id is already a source field.
4. Stein/H⁻¹, spectral, regular-class and compact constant-8 assembly.

Local L² of T gives only local L¹ of T². No C² upgrade, global inverse bound, global weighted
tensor-square estimate or assumed energy bound is available. The smooth A.4 and the old N13c
local-L² right-hand-side interface do not close the weak-source gap; the C¹ generator identity is
readiness support, not an actual height-cutoff construction.

The Goal is coordinated by the current Codex chat (`01a13ea4-f340-73b1-bbe8-af9381f33679`) and the
original Claude session. Codex freezes sources, statements, dependencies and placement, then
independently accepts. Claude runs one unchanged gpt-6-astra/high API loop at a time
(max_rounds 4, max_queries 6) and is the sole canonical integrator after placement review. No
commit, push, tag, remote CI or publication is authorized. The old large loops and other roadmap
stages stay stopped. The [Goal record](research/handoffs/2026-10-14-bkl-step1-letwin-constant-eight.md)
retains the endpoint and acceptance protocol; historical queues do not override this handoff.
