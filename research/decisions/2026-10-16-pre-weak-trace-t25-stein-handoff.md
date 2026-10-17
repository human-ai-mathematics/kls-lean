# Current KLS handoff

Updated 2026-10-16 at the weak inverse-Hessian cutoff integration. The previous handoff is preserved byte for
byte in [the dated archive](research/decisions/2026-10-16-pre-weak-cutoff-handoff.md).
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
  ([weak evolution record](research/decisions/2026-10-16-weak-hessian-evolution-h1-integration.md)).

See the [declarations and owners](research/progress/PROOF-PATH.md#stage-1-letwins-constant-8).

The C¹ weak inverse-Hessian height cutoffs are now canonical
([weak cutoff record](research/decisions/2026-10-16-weak-inverse-hessian-cutoff-integration.md)):
- `Analysis.exists_scaled_weak_inverse_hessian_cutoffs` (every real R ≥ 1) and `Analysis.exists_weak_inverse_hessian_cutoffs`
  (R = m + 1), for a convex, normalized, Lipschitz C¹ u with Lipschitz gradient, a C¹ V, a Lipschitz exponent and
  det ∇²u = exp(−u + V(∇u)) with ∇²u positive definite a.e.; every finite dimension including zero. One shift c and one constant
  C give χ_R = smoothTransition(2 − (u − c)/R) with:
  - C¹ regularity, compact support, Lipschitz gradient and values in [0, 1];
  - monotonicity in R and pointwise limit 1;
  - a literal generator L χ_R that is integrable for ν = e^{−u} dx, with ∫ |L χ_R| dν ≤ C/R → 0.

  The drift bound, coercivity, majorant and defect bound are derived, not assumed.
- `Analysis.exists_regular_moment_weak_cutoffs`: from the original R0 hypotheses, the same u, L, LF and T with the whole bounded
  weak-Hessian-testing payload (every R0, tensor, inverse, mean, first Monge–Ampère, (2.6) and ψ·H field), plus one common c and C
  with that family. The audit proves the χ_R·H_lk weak (2.6) tests at this witness for every R ≥ 1 and all indices.

This is the C¹/Lipschitz-gradient counterpart of Lemma A.4 for the actual weak source. The classical smooth A.4 keeps its
reviewed stronger scope, and the new family is not a C^∞ cutoff family or the smooth moment map of Lemma 2.2.
No C² regularity of u, global inverse bound, global L² of T or energy bound is assumed as an input.
Lemma 2.4 stays partial (a reviewed weak route; the positivity of the weak right-hand matrices is not
stated). A.5 consumption, the weak trace contraction, the energy comparison (2.14), Theorem 2.5 and compact
constant 8 are open. The 30 ledger certificates and paper coverage are unchanged.

## Evidence

- The full receipt `build/verification/20261016T033139.894094Z/report.json`, with Codex acceptance of the weak
  evolution package, covers only the snapshot `3a87e101…`. It does not cover the cutoff sources or this metadata.
- The four cutoff source files passed:
  - a scratch production prototype with independent Codex acceptance: strict compilation, 42 complete
    records with the old declarations unchanged, standard axioms and kernel replay;
  - a canonical source-only check: all 900 production artifact parts and the audit part are byte-identical
    to the accepted prototype view (`weak-cutoff-integration/canonical-phase1/CODEX-CANONICAL-SOURCE-ACCEPTANCE.json`
    in the ignored Goal control directory).
- Final acceptance requires a passing full receipt matching the current source/meta snapshot, bound in the
  ignored `weak-cutoff-integration/` final acceptance/completion records; inspect `build/verification/latest.json`
  and the exact report. See [receipt scope](research/verification.md#receipts-and-trust-scope).

## Next obligations and coordination

1. The finite contraction of the actual χ·H weak (2.6) tests to the distributional trace-quadratic density
   (2.8)/(2.10), its positivity, and the actual A.5 consumption with the canonical cutoffs. Reviewed scratch
   packets for bounded weak cutoff testing and trace data are not canonical.
2. The integrated energy comparison (2.14), E tr(BHBH) ≥ 2 E G₁.
3. The actual weak Brascamp–Lieb (A.6) consumer and the Theorem 2.5 upper bound
   E tr(BHBH) ≤ 2 tr(B²). The actual mean Hessian Id is already a source field.
4. Stein/H⁻¹, spectral, regular-class and compact constant-8 assembly.

Local L² of T gives only local L¹ of T². No C² upgrade, global inverse bound, global weighted
tensor-square estimate or assumed energy bound is available.

The Goal is coordinated by the current Codex chat (`01a13ea4-f340-73b1-bbe8-af9381f33679`) and the
original Claude session. Codex freezes sources, statements, dependencies and placement, then
independently accepts. Claude runs one unchanged gpt-6-astra/high API loop at a time
(max_rounds 4, max_queries 6) and is the sole canonical integrator after placement review. No
commit, push, tag, remote CI or publication is authorized. The old large loops and other roadmap
stages stay stopped. The [Goal record](research/handoffs/2026-10-14-bkl-step1-letwin-constant-eight.md)
retains the endpoint and acceptance protocol; historical queues do not override this handoff.
