# Current KLS handoff

Updated 2026-10-17 at the exact compact Letwin constant-8 integration. The previous handoff is preserved byte for
byte in [the dated archive](research/decisions/2026-10-16-pre-letwin-compact8-completion-handoff.md).
Use the [proof path](research/progress/PROOF-PATH.md) for source-to-Lean navigation and the
[paper register](research/progress/LITERATURE.md) for exact scope and coverage.

## Target and current boundary

The four-stage main line is **Letwin constant 8 → stochastic localization → BKL Theorem 4.1 → KLS**.

**Stage 1 is proved in its compact form.** `KLS.LogConcave.Suspension.letwinCompactBound : LetwinCompactBound`
(`formalization/FunctionalInequalities/KLS/Letwin/CompactBound.lean`) gives, for every n > 0, every compactly supported
isotropic log-concave probability law on `EuclideanSpace ℝ (Fin n)` and every self-adjoint real operator (singular and
indefinite included), `Var_μ ⟨M X, X⟩ ≤ 8 ∑ᵢⱼ ⟨M eᵢ, eⱼ⟩²` in the standard orthonormal basis. It is certified in source
form as `thm:letwin-compact-quadratic-bound` (`solutions/ThmLetwinCompactQuadraticBound.lean`; Letwin arXiv:2607.24164v1,
Theorem 1.2, compact counterpart; the input of BKL arXiv:2610.05474v1, Lemma 4.2). The noncompact Theorem 1.2 (every
isotropic log-concave law, through the full Lemma A.1), Letwin's Theorem 1.1, the smooth source Lemma 2.2/Theorem 2.5 and
the target Stein kernel of Lemma 2.7 are not formalized; Letwin's paper is not covered.

**Stages 2–4 are not completed.** BKL `theorem41` and `conjecture_of_letwinCompact` keep `LetwinCompactBound` as an explicit
hypothesis. Composing them with `letwinCompactBound` would type-check, but that composition is not added and is not
claimed: the stochastic-localization chain and the Theorem 4.1 assembly must first be re-reviewed against BKL's source.
`KLS.kls` remains the intentional hole outside certificate closures; dimension-free KLS is open.

## Accepted canonical frontier

The proof of the regular-class bound `regularClass_matrix_variance_le_eight` (`KLS/Letwin/RegularClass.lean`, exact R0
hypotheses: n > 0, isotropic `1_K e^{-W} dx`, K compact convex with nonempty interior, W smooth and κ-uniformly convex):
- takes the weak Stein witness u of `exists_regular_moment_weak_stein_coupling` once, with its exact-2 trace bound
  E_ν tr(B∇²u B∇²u) ≤ 2 tr(B²) for every symmetric B ([weak trace record](research/decisions/2026-10-16-weak-trace-t25-stein-integration.md));
- shows that the original regular input law μ is log-concave (`logConcave_of_eq_regularClass`), has full affine
  support (`affineSupport μ = ⊤`, by isotropy) and has a finite fourth moment (the bounded gradient ∇u pushes the
  normalized witness law ρ = e^{−u} dx to μ);
- reduces to invertible symmetric M by the singular extension (Lemma A.2, stronger form);
- conjugates by S = √|M| and Q = sign M, compares the variance of ⟨Q x, x⟩ under η = S_#μ with its value under the
  Gaussian smoothing of η, bounds the smoothed variance by 4 times the latent product energy (Gaussian product coupling, compact dual bound, H⁻¹ inequality on the C² convex
  smoothed law), evaluates the energy with the spectral sign/noise identity and the trace bound, and removes the noise.

`regularClass_letwinQuadraticBound` and the existing compact reduction `letwinCompactBound_of_regularClass` then give
`letwinCompactBound`. The generic supports live in their object families (matrix action and spectral identities,
quadratic-form variance, Gaussian smoothing, source Stein); see the
[integration record](research/decisions/2026-10-16-letwin-compact-eight-integration.md). No target Stein kernel or inverse
transport is constructed.

## Evidence

- Source: the 21 source files (13 replaced, 8 created) are byte-identical copies of the independently accepted
  production candidate (strict compilation, complete physical comparison of old and new declarations, standard axioms
  and local-module kernel replay; two additional files named `… 2.olean` held byte-exact old 905-part seed content and
  were retained, excluded and shown not loaded). Codex accepted
  the canonical copy (`letwin-eight-integration/codex-canonical-source/ACCEPTANCE.json` in the ignored Goal control
  directory).
- Certificate and metadata: added in this integration; the certificate is a source-form restatement of the canonical
  endpoint.
- Full verification: this milestone is accepted only with a passed full local verification report
  (`python3 research/verify.py`) for the exact current source/meta snapshot and its independent acceptance, recorded under
  `build/` without editing tracked files. The ignored Goal checkpoint records the current report and acceptance state;
  each earlier report applies only to its recorded snapshot. See
  [receipt scope](research/verification.md#receipts-and-trust-scope).

## API status

The API is idle. The sealed S3 (Gaussian product source pairing) and S4 (spectral sign/noise trace) runs exhausted their
budgets without an accepted proof and remain failures; the corresponding results were proved by independently accepted
closed assemblies instead. No resend or failed-body repair is authorized.

## Next obligations and coordination

1. Stochastic localization: a source audit of BKL arXiv:2610.05474v1, Section 5, against the existing cutoff-localization
   development (`KLS/BKL/Localization/`), identifying exact hypotheses and any missing source step.
2. BKL Theorem 4.1: a source-faithful review of `theorem41`/`theorem41Compact` and their inputs.
3. KLS: only after stages 2–3 are accepted, review the composition with `conjecture_of_letwinCompact`; `KLS.kls` stays
   open until that exact statement is proved and verified.

The noncompact Letwin Theorem 1.2 (full Lemma A.1) is not on the BKL critical path, which consumes only the compact bound.

The Goal is coordinated by the current Codex chat (`01a13ea4-f340-73b1-bbe8-af9381f33679`) and the
original Claude session. Codex freezes sources, statements, dependencies and placement, then
independently accepts. Claude runs one unchanged gpt-6-astra/high API loop at a time
(max_rounds 4, max_queries 6) and is the sole canonical integrator after placement review. No
commit, push, tag, remote CI or publication is authorized. The old large loops stay stopped. The
[Goal record](research/handoffs/2026-10-14-bkl-step1-letwin-constant-eight.md) retains the endpoint and acceptance
protocol; historical queues do not override this handoff.
