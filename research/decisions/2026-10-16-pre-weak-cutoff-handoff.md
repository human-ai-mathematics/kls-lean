# Current KLS handoff

Updated 2026-10-16 at the weak Hessian evolution and bounded H¹ testing integration. The previous handoff is
preserved byte for byte in [the dated archive](research/decisions/2026-10-16-pre-weak-evolution-h1-handoff.md).
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
- the rough compact curl identity, the C¹ unprimed generator identity and the actual mean Hessian Id.

See the [declarations and owners](research/progress/PROOF-PATH.md#stage-1-letwins-constant-8).

The weighted weak second Hessian evolution and bounded H¹ testing are now canonical
([weak evolution record](research/decisions/2026-10-16-weak-hessian-evolution-h1-integration.md)):
- `Analysis.exists_regular_moment_weak_hessian_evolution`.
  - From the original R0 hypotheses, with the same u, L, LF and T and every R0, tensor,
    first-weak-Monge–Ampère, inverse and mean field.
  - Adds the weak derivative of tr(H⁻¹T_i) along every coordinate and the unweighted flux identity.
  - Adds the weighted weak (2.6): ∫ e^{−u} Σₐ J_ija ∂ₐψ = −∫ e^{−u} E_ij ψ for every compactly supported C¹ ψ, where
    - J_ija = Σ_b (H⁻¹)_ba T_bij is L² on compact sets;
    - E_ij = −H_ij + (H ∇²W(∇u) H)_ij + tr(H⁻¹T_iH⁻¹T_j), with E and e^{−u}E locally integrable.
- `Analysis.exists_regular_moment_bounded_weak_hessian_testing`: the same witness and every field above,
  plus the identity tested against the bounded H¹ tests ψ·H_lk, with both sides integrable.
- Generic supports, every finite dimension including zero:
  - B1 `exists_contDiff_compact_bounded_all_weak_deriv_approximation`, for bounded compact locally integrable η
    with compact global-L² coordinate weak derivatives. It gives one smooth sequence with:
    - common compact support and the uniform bound 3C;
    - L² convergence of every coordinate derivative;
    - full-sequence a.e. convergence.
    The two-direction approximation is unchanged.
  - H2 `integral_flux_eq_neg_forcing_of_bounded_weak_test`: extends compact C¹ test identities with compact-local L²
    flux and locally integrable forcing to such bounded tests.
  - The weak Piola row divergence of H⁻¹, `ae_inverse_hessian_row_divergence_of_weak_derivative`.
  - The intrinsic leaf `Analysis/BakryEmery/IntegrationByParts/WeakHessianEvolution.lean`: the first-RHS weak derivative,
    local flux and forcing, the unweighted and weighted identities, and the bounded test extension.

No C² regularity of u, global inverse bound, global L² of T or energy bound is assumed as an input.
Lemma 2.4 stays partial (a reviewed weak route; the positivity of the weak right-hand matrices is not
stated). The energy comparison (2.14), Theorem 2.5 and compact constant 8 are open. The 30 ledger
certificates and paper coverage are unchanged.

## Evidence

- The full receipt `build/verification/20261015T121010.942278Z/report.json`, with Codex canonical
  acceptance of the curl/mean package, covers only the snapshot `464d989a…`. It does not cover the weak
  evolution sources or this metadata.
- The six weak evolution source files passed:
  - a scratch production prototype with independent Codex acceptance: strict closure and audit compilation,
    134 complete records with the old declarations unchanged, standard axioms and kernel replay;
  - a canonical source-only check: all 900 compiled artifact parts are byte-identical to the accepted
    prototype view (`weak-evolution-H1-integration/canonical-phase1/CODEX-CANONICAL-SOURCE-ACCEPTANCE.json`
    in the ignored Goal control directory).
- Final acceptance requires a passing full receipt matching the current source/meta snapshot, bound
  in the ignored `weak-evolution-H1-integration/` final acceptance/completion records; inspect
  `build/verification/latest.json` and the exact report. See
  [receipt scope](research/verification.md#receipts-and-trust-scope).

## Next obligations and coordination

1. The actual C¹/Lipschitz-gradient source-height cutoffs (Letwin A.4), with an integrable generator
   defect bounded by C/R, and their A.5 consumption. Reviewed supports for the actual height family
   exist only as scratch prototypes outside the canonical tree; they are not canonical and do not
   complete A.4.
2. The integrated energy comparison (2.14), E tr(BHBH) ≥ 2 E G₁, from the bounded weak (2.6).
3. The actual weak Brascamp–Lieb (A.6) consumer and the Theorem 2.5 upper bound
   E tr(BHBH) ≤ 2 tr(B²). The actual mean Hessian Id is already a source field.
4. Stein/H⁻¹, spectral, regular-class and compact constant-8 assembly.

Local L² of T gives only local L¹ of T². No C² upgrade, global inverse bound, global weighted
tensor-square estimate or assumed energy bound is available. The smooth A.4 and the old N13c
local-L² right-hand-side interface do not close the weak-source gap.

The Goal is coordinated by the current Codex chat (`01a13ea4-f340-73b1-bbe8-af9381f33679`) and the
original Claude session. Codex freezes sources, statements, dependencies and placement, then
independently accepts. Claude runs one unchanged gpt-6-astra/high API loop at a time
(max_rounds 4, max_queries 6) and is the sole canonical integrator after placement review. No
commit, push, tag, remote CI or publication is authorized. The old large loops and other roadmap
stages stay stopped. The [Goal record](research/handoffs/2026-10-14-bkl-step1-letwin-constant-eight.md)
retains the endpoint and acceptance protocol; historical queues do not override this handoff.
