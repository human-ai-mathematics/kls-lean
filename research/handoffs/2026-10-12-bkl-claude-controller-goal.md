# BKL Theorem 1.1 goal: Claude controller

Created 2026-10-12 by the owner's decision in the Claude session of 2026-10-12. Status: active;
checkpoints 1–4 below decided by the owner on 2026-10-12, checkpoint 5 open. Current milestone: G0.

## Controller and roles

- Controller and sole canonical integrator: this Claude session. The Codex thread
  `01a12de4-2412-7082-ae33-15b1c3502420` stopped on 2026-10-12 (last request
  `api-trace-cutoff-consumption-compiler-v5`, completed 22:22, not integrated); its goal record
  [2026-10-12 Letwin Theorem 2.5 goal](2026-10-12-bkl-letwin-t25-goal.md) is historical.
- Proof construction: the owner's GPT API (`~/.config/kls/gpt.env`), `gpt-6-astra` with high
  reasoning (`gpt-6.1-sol` when available); no automatic weaker fallback, no blind retry of a
  consumed request, no usage cap. Each request is sealed under `build/reviews/2026-10-12-bkl-claude-goal/`.
- The owner reviews mathematics and assumptions at the checkpoints marked (C).
- Local commits are allowed for snapshots that pass the full `research/verify.py`; push, tags and
  remote CI need the owner's confirmation.

## Exact objective

Bizeul–Klartag–Lehec, arXiv:2610.05474v1 (pinned PDF SHA-256 `86824722…`), Theorem 1.1, without
hypotheses, in the source normalization, with its certificate and a matching full receipt. The
assembly is already proved conditionally: `KLS.conjecture_of_cumulantBound`
(`KLS/BKL/Reduction.lean`) derives the exact `KLS.Conjecture` from
`∃ K ≥ 1, ∀ d ≥ 2, CumulantBound d ((d!)²·K^d)` through the certified Theorem 3.1, the
certified conditional Proposition 7.1 and the Section 2 reductions. The remaining obligations are
exactly BKL Theorem 4.1 for m ≥ 3 and its Letwin input (Lemma 4.2 via Letwin Theorem 1.2).
Closing `KLS.kls` from Theorem 1.1 changes `KLS/Target.lean` imports: a separate (C) at the end.

## Execution protocol (per task)

1. Freeze the exact Lean statement (with `sorry`, outside production) and its Blueprint node.
2. Sealed request to GPT: statement, source locator, minimal context modules, compiler protocol.
3. Compile the candidate in an isolated `/private/tmp` worktree (symlinked `.lake/packages`);
   return compiler diagnostics to GPT for further rounds.
4. Review: statement unchanged, no `sorry`/axiom/option escapes, standard axiom closure,
   meaningful client; then integrate canonically and record the mapping.
5. Full `research/verify.py` at each milestone; local commit when it passes.

Task state for resumption (also by a new Fable window when Opus quota runs out, owner 2026-10-13):
`build/reviews/2026-10-12-bkl-claude-goal/BOARD.md` (regenerate with `tools/board.py`), with the
GPT ⇄ Lean loop `tools/gpt_lean_loop.py` (frozen statement, query protocol, strict compile,
signature and axiom probes) and `tools/restart_task.sh`. Tasks that stall in the GPT loop may be
given to a Fable worker under the same acceptance checks.

## Milestones

**G0 — setup and definition audit (first).** Freeze statement names and Blueprint nodes for:
`Theorem41Compact`, generator forms of Lemma 4.3 and Lemma 5.1, a Dynkin interface, Lemma 5.2,
the compact approximation, the Letwin regular class and the moment-map contract. Audit the
definitions for the later constructions (risks below). Triage the stopped Codex v5 candidate (A.5
for the trace test). Fix the drifts found on 2026-10-12: the P71 lemma-map note, HANDOFF vendoring
status.

**Stream S — Theorem 4.1 (stochastic localization).**
- S1 [D] Parameter-space calculus: ψ(c,Q) = log Z jointly smooth, κ_m = D_c^m ψ, D_c κ_m =
  κ_{m+1}, the generator 𝓛, (71) as 𝓛Λ = −½⟨v, A⁻¹v⟩, Lemma 4.3 as 𝓛κ_m = −(mκ_m + L_m) via the
  proved grouped (74), 𝓛a = 0, 𝓛A = −A.
- S2 [D] Standardization: cumulants under affine maps; ν_p isotropic, log-concave, compact for
  symmetric PSD Q; (77)–(79) conditional on compact Letwin; a-priori bound C(n,m).
- S3 [D] Lemma 5.1 as a generator inequality on symmetric PSD Q with an explicit universal C,
  (81)–(91) on coordinate tensors.
- S4 [D] Section 6 pointwise bounds (98)–(104).
- S5 [S] The Eldan SDE (67) with cutoff coefficients on the vendored LevyStochCalc: adapters to
  `Fin N → ℝ`, existence, Q symmetric PSD, the log-det non-explosion estimate uniform in the cutoff.
- S6 [S] Dynkin identity E F(X_T) − F(p₀) = E∫γ²𝓛F for C² F, limits in the cutoff.
- S7 Lemma 5.2 and the induction (95)–(106) ⇒ `Theorem41Compact` (conditional on compact Letwin).
- S8 Compact approximation with cumulant convergence ⇒ `CumulantBound d ((d!)²K^d)` for every
  isotropic log-concave law ⇒ conditional Theorem 1.1 with Letwin as the only hypothesis.

**Stream L — Letwin Theorem 1.2 for compactly supported isotropic log-concave laws.**
- L1 Theorem 2.5 for a given potential: tensor comparison (2.12), A.4/A.5 for Tr(BHBH) and
  (2.11), A.6 for F_ij with (2.15)–(2.17), assembly.
- L2 Theorem 1.2 for a given potential: Proposition 2.8, linear Stein push-forward and (2.21),
  Lemma A.2.
- L3 Moment-map existence and push-forward for bounded isotropic sources (Euler–Lagrange from the
  proved bounded primal and Legendre variation).
- L4 Regularity sufficient for L1–L2 (route (C) below).
- L5 Lemma A.1 approximation, restricted to what the BKL consumer needs.

**F — completion.** Unconditional Theorem 4.1 and BKL Theorem 1.1, certificate, register entries,
full receipt; then (C) closing `KLS.kls`.

Parallel from the start: S1, S2, S4, S5, S8-approximation, L1, L2, L3.

## Definition-audit risks (G0)

Cumulant junk values outside the exponential-moment neighbourhood; non-symmetric Q in the
parameter space; L²-only Itô theory (state stochastic lemmas for cutoff processes); missing
pathwise uniqueness (`Ito/PicardWellPosed` not vendored); measurability for Fubini in Lemma 5.2;
`Fin N → ℝ` sup norm versus Euclidean state; avoid the five upstream `sorry` declarations; one
principal square root throughout; compact laws versus all laws (approximation mandatory);
dimension 0; basis mismatch between the Stein API (`Fin n`) and the BakryEmery API
(`Fin (finrank)`); A.5 needs a global bound on the test function.

## Owner checkpoints (C)

1. Route for Letwin regularity (L4): decided 2026-10-12 (owner): the weak route. Moment-map
   C^{1,1} regularity for uniformly convex targets (penalized finite differences and a maximum
   principle) and the trace evolution with the a.e. Hessian, in this project's dimension-generic
   API; the mathematical route of KLS500 may be consulted, its code style is not adopted. The
   statements of Letwin Theorem 1.2 (constant 8) and of BKL Lemma 4.2 are unchanged; internal
   Theorem 2.5 steps take `⇑`. Smooth Monge–Ampère regularity (Lemma 2.2, Klartag's Hessian
   bound) is out of scope.
2. Compactly supported laws first, then approximation (S7/S8, L5): decided 2026-10-12 (owner). BKL
   itself reduces to compact laws (p. 19, end of Section 6); the final `CumulantBound` covers every
   isotropic log-concave law.
3. Lemmas 4.3 and 5.1 as deterministic generator identities/inequalities, with one Dynkin bridge
   for the cutoff processes: decided 2026-10-12 (delegated by the owner to the controller). BKL
   consumes (73) and (80) only through expectations in Lemma 5.2, where the martingale terms
   vanish; the vendored Itô integral is L²-only, so the literal differential of the uncut process
   may not be expressible. Lemma-map marks: `⇑` (different formulation) for L43 and L51.
4. Pathwise uniqueness: cutoff-only route first (limits inside the inequalities); vendoring
   `Ito/PicardWellPosed` returns to the owner if that route fails: decided 2026-10-12 (owner).
5. Closing `KLS.kls` (Target imports) once Theorem 1.1 is unconditional: open.

## Controller decisions log

- 2026-10-13: the Letwin stream runs under a Fable sub-controller (owner suggestion) that freezes statements
  and drives the GPT loop but does not touch the canonical tree; the controller integrates.
- 2026-10-13: approved the weak-route auxiliary definitions
  (`build/reviews/2026-10-12-bkl-claude-goal/routes/letwin-weak-definitions.md`): pointwise subgradient
  predicate and `subgradientImage` (Analysis/Convex/Subgradient.lean), a.e. Hessian via the existing
  `hessianOperator`/`hessianMatrix`, `HasWeakDerivAlong` with `C¹_c` tests and built-in local
  integrability (Analysis/WeakDerivative.lean), the set-wise Alexandrov identity, and touching-test
  viscosity statements. New infrastructure only; no existing definition or target statement changes.
  Open for owner review.
- 2026-10-13: a second Fable sub-controller owns the analytic core of stream S (Lemma 5.1 as a generator
  inequality, the Eldan cutoff process and its Dynkin identity, Lyapunov moments, the cutoff limit, Lemma 5.2 and
  the induction), under the same boundaries (no canonical writes; log in
  `build/reviews/2026-10-12-bkl-claude-goal/routes/s-core-subcontroller-log.md`). Tasks that exhaust the GPT loop
  are given to Fable workers under the same acceptance checks (`tools/accept_manual.py`).
- 2026-10-13 (placement): touching-test (viscosity) inequalities for convex functions get their own module
  `Analysis/Convex/Viscosity.lean` (owner family `Analysis/Convex`, scope: pointwise consequences of `C²` touching
  tests via `Probability.Stein.hessianMatrix`; imports `Probability/Stein/HessianKernel.lean`, as `Analysis/Matrix/Piola.lean`
  already does). Created rather than extending `Alexandrov.lean` because the Hessian dependency diverges; no public API
  change elsewhere; validated by build, strict compile and the full verifier.
- 2026-10-13 (placement): `Analysis/Convex/Normalization.lean` (new; family `Analysis/Convex`; maximal simplices and
  standard-simplex geometry for the affine normalisation of convex bodies; Mathlib only) and
  `KLS/BKL/Localization/LyapunovMoment.lean` (new; Gronwall moment and tail bounds along the cutoff process; imports
  Lyapunov, Process, CutoffInduction, Gronwall). Both created because no existing module owns these objects; no API change.
- 2026-10-13 (placement): `KLS/BKL/Localization/EnergyIntegral.lean` (new; Dynkin and integrated energy bound along the
  cutoff process, Lemma 5.2 cutoff form; imports CutoffInduction, EnergyConjugation, EnergyBound, CumulantDerivative,
  EnergyForm) and `Analysis/Convex/Caffarelli.lean` (new; geometric steps of Caffarelli's argument; imports Alexandrov).
  Touching-test Taylor bound goes to `Viscosity.lean` (Hessian imports), not `Alexandrov.lean`. No API change.
- 2026-10-13 (placement): `KLS/BKL/Localization/CutoffInductionStep.lean` (new; the induction step and the named hypothesis
  `Lemma51Bound`; cannot live in `CutoffInduction.lean`, which its imports `EnergyIntegral`/`LyapunovMoment` depend on) and
  `KLS/BKL/Theorem41.lean` (new; paper-level assembly of Theorem 4.1 and the conditional Theorem 1.1, after the
  `KLS/BKL/Proposition71.lean` precedent). Letwin supports: Lipschitz null images to `Analysis/Sard/Equidimensional.lean`,
  proximal/Moreau/Taylor lemmas to `Analysis/Convex/Subgradient.lean`. 2026-10-13: Fable credits exhausted; the Letwin
  sub-controller continues on Opus, the S line was finished by the main controller.
- 2026-10-13 (placement): `Analysis/Convex/SecondOrder.lean` (new; second-order differentiability of convex functions,
  Alexandrov's theorem; imports Subgradient and Sard/Equidimensional). L-T11e7 supersedes L-T11e (same statement re-proved);
  only L-T11e7 was integrated.
- 2026-10-13 (placement): `Analysis/Convex/GradientLipschitz.lean` (new; the C^{1,1} estimate for moment-map potentials;
  imports Viscosity, Alexandrov, Coercivity, SecondDifference) and `KLS/LogConcave/BallConditioning.lean` (new; regular class
  of ball-conditioned affine images; imports RegularAffine). The generic ball-conditioning limit goes to
  `Probability/Conditioning.lean` (its unused `KLS.Isotropic` import dropped).
- 2026-10-13 (owner directive): Letwin formalization is limited to what BKL needs, i.e. the critical path to
  `LetwinCompactBound`; all other Letwin work is parked, and the project sprints on BKL Theorem 1.1. The Letwin
  sub-controller writes `routes/letwin-critical-path.md` and dispatches only critical-path tasks.
- 2026-10-13 (placement): L-N11a goes to `Viscosity.lean`, not `Analysis/Matrix/LogDet.lean` (it imports Viscosity, which
  imports LogDet). L-N10a needed `_root_.add_apply`/`smul_apply`/`neg_apply` under `Piola.lean`'s `open Matrix`.

## Not claimed

This goal record proves nothing. Theorem 4.1 for m ≥ 3, Letwin Theorems 2.5 and 1.2, BKL
Theorem 1.1 without hypotheses and `KLS.kls` remain open.
