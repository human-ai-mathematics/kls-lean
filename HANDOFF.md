# Current KLS handoff

Updated 2026-10-29. This tree is the **reviewed Letwin delivery**. It is rebuilt from
`origin/main` (`0233f0b837131da5bb20420c4152d13260b8260a`), not from the unpublished local commit
`04ef79859edd554e202e914875da748d39935503`, which also contains unused auxiliary research. The user
authorized review, commit and push of the completed scope while excluding unfinished work.

## Release scope

The [delivery map](research/progress/completed-letwin-delivery-map.json) records the selection rule,
every excluded path and the original scope. In short:

- **Retained (798 library modules and the aggregate):**
  - every module and public declaration owner already published on `origin/main`, with its import closure;
  - the completed Letwin/CEK results, Proposition 2.8 for full-dimensional laws and the proved Klartag supports;
  - the two Letwin certificate registrations and the Letwin/CEK readability maintenance below.
- **Not copied:**
  - 39 library files used only by the superseded auxiliary variational route to Letwin Lemma 2.2
    (Alexandrov sections, Caffarelli W²,p, Dirichlet/Pogorelov references and CNS barriers);
  - the 55 audit clients that import them.

The 798 retained library Lean files are byte-identical to the primary checkout. The delivery review trims only an extra final blank line in `examples/EllipticDrift.lean`.
No retained statement, hypothesis,
constant, dimension or proof body changes.

The 52 Blueprint statements formalized only in the excluded files keep their text and hypotheses but no
longer carry `\leanok`. The paper register and smooth-route record no longer cite their declarations.
Their mathematical gaps remain open. They are historical records, not targets to resume.

**Review state.** Sources, interfaces and metadata of this selection are reviewed:
- a strict build and an exact-scope build;
- a strict `Expr.equal` comparison of every retained public and local declaration, with no difference and no
  owner change;
- an unchanged comparison of all 403 Blueprint statements and `\uses` edges;
- regenerated API and module indexes.

The complete verification result is decided only by
`build/history/2026-10-29-letwin-delivery-20261029T105117Z/candidate-verification.json`: the delivery is fully
verified exactly when that file reports `status: passed` for this tree's source snapshot. This handoff
asserts no full-verification result.

The primary-tree full local receipt `build/verification/20261029T095710.427667Z/report.json` (snapshot
`9ed7a254fbbe1cc574b2d63c538c149cbe59bd461563413c257b7e5796245e13`) evidences only the selected source
bytes, not this tree. Do not infer a push or remote CI result from any local receipt.

## Reviewed Letwin/CEK readability maintenance

This batch supports Letwin arXiv:2607.24164v1 Lemma 2.2, Theorem 2.5 and their source consumers, and
CEK arXiv:1304.0630v1 Theorem 2. It changes no mathematics. Only six Lean files are edited:

- **`KLS/Letwin/MomentMap.lean` and `KLS/Letwin/SteinKernel.lean`:** each gets one named section,
  `BoundedOpenConvexSource`. The Lemma 2.2 source-class hypotheses are declared there once, and each
  declaration includes them theorem-locally. Private helpers with weaker hypotheses stay outside.
- **`KLS/CEK/Uniqueness.lean`:** one context, with named finite and essentially continuous sections.
- **Two generic Hessian bridges:** they move from `KLS/Letwin/MomentCalculus.lean` to
  `Analysis/BakryEmery/Hessian/Coordinates.lean` and `Analysis/BakryEmery/MongeAmpere.lean`.
  Their full names, types and proofs are unchanged.

Public names, statements, binders, universes, hypotheses, constants, dimensions, proof bodies and all
proof and certificate states are unchanged. Namespace naming was reviewed only; no public rename is
made. The batch and its owner map are recorded in the
[source layout review](research/progress/source-layout-review.md#letwincek-readability-batch-2026-10-29)
and [its map](research/progress/2026-10-29-letwin-readability-map.json). On the primary tree it was
accepted at source/interface level and passed full local verification
(`build/history/2026-10-29-letwin-style-20261029T091203Z/verification.json`).

## Canonical mathematical scope

`FunctionalInequalities.KLS.kls : KLS.Conjecture` is unchanged. The accepted chain is:

compact Letwin constant 8 -> cutoff BKL localization -> source-form BKL Theorems 4.1 and 1.1 -> KLS.

It includes singular affine supports and zero dimension. The compact Letwin certificate remains the BKL
input. The four exploratory routes are historical records, not current formalization targets.

The [paper register](research/progress/LITERATURE.md) owns pinned versions, statements, coverage and
certificates. The [proof path](research/progress/PROOF-PATH.md) owns the accepted KLS chain. The
[root summary](README.md) states the results and remaining scope.

## Registered Letwin targets

Source: Letwin, *The KLS constant is O(log^(1/4) n)*, arXiv:2607.24164v1, 27 July 2026,
PDF SHA-256 `5dd9194cf36d91e2e4929a48564fe99d8d163a0a5ec7b31d80dc1f58a41778f1`.

- **Theorem 1.1 / paper target:** `thm:letwin-log-quarter`,
  [Solutions.ThmLetwinIsoperimetricBound.certificate](solutions/ThmLetwinIsoperimetricBound.lean).
  - Statement: one real C > 0 before every n ≥ 2 and every isotropic log-concave law; ψₙ ≤ C (log n)^(1/4),
    with the source inverse Cheeger normalization.
  - The existing proof uses the stronger BKL bound and the π Cheeger–Buser comparison.
  - The lemma-map relation remains `alternative` (⇑).
- **Theorem 1.2 / full noncompact statement:** `thm:letwin-quadratic-bound`,
  [Solutions.ThmLetwinQuadraticBound.certificate](solutions/ThmLetwinQuadraticBound.lean).
  - Statement: Var(XᵀMX) ≤ 8 tr(M²) for every n > 0, every isotropic log-concave probability law and every
    symmetric M, including singular and indefinite matrices.
  - There is no compact-support or extra moment premise.
  - The lemma-map relation remains `same`.
- **Compact supporting certificate:** `thm:letwin-compact-quadratic-bound` keeps its narrower statement and
  its BKL consumer. The noncompact theorem uses it together with a moment limit. It does not depend on
  the downstream Theorem 1.1 or on the BKL Poincaré theorem.

The [target review](research/progress/target-reviews.md) records both registrations, their exact scopes
and their proof dependencies. Registration authorization is distinct from human semantic approval; no
additional maintainer or source-author review is asserted. Paper coverage means the certified
main-theorem conclusion, not every numbered statement or the original proof route.

## Retained results and unfinished scope

- **Original Letwin Theorem 1.1 route:** the third-moment argument and the traced Klartag bound remain
  unformalized. The alternative-route certificate does not change this.
- **Proposition 2.8:** remains `partial`, for full-dimensional log-concave laws only
  (`KLS.LogConcave.variance_le_sum_dualNorm_sq`). A finite dual norm forces the zero-mean derivative
  premise. No lower-dimensional ambient-gradient extension is claimed.
- **Lemma 2.2, Theorem 2.5 and consumers:** proved for the literal bounded open convex source class and
  every convex essentially continuous moment potential. The proved conclusions are:
  - smoothness and a positive definite Hessian;
  - the gradient diffeomorphism;
  - the exact-2 trace bound;
  - the same-potential calculus and Stein results.

  Section 1 constants and Letwin Lemma 2.1 (= CEK Theorem 2) keep their proved scopes. The readability
  batch reorganizes these sources without changing any statement.
- **Superseded variational route:** its auxiliary Lean development is not in this release (see Release
  scope). The completed moment-map route does not need it. These gaps remain open mathematically:
  - W²,p and smoothness of the earlier witness `exists_moment_potential_of_bounded_open_convex`, whose
    C¹ producer is retained;
  - the contact-density estimate, Dirichlet/Pogorelov reference existence and regularity, and the
    combined CNS barrier comparison.
- **CEK arXiv:1304.0630v1:** Theorem 2 is proved, but no CEK paper-target certificate is registered.
  Open or partial supports:
  - Proposition 1 and Lemma 6;
  - the vanishing integral of Lemma 4, sharp Lemma 5, and Lemma 9 as stated;
  - Lemmas 14–15 and the concavity of I_μ (Remark 13);
  - the general-mass and non-lower-semicontinuous forms of Theorem 8 and Proposition 7.
- **Klartag arXiv:1309.2767v1:** outside the completed scope are Theorem 1.1 with constant 2R², Lemma 2.3
  in its C¹ form (only a Lipschitz version is available), the Section 4–5 diffusion, and regularity
  (1) ⇒ (2). The available maximum-principle bound is 3R². The literal moment-map theorem needs only some
  uniform Hessian bound; its constructed witness is 12R².

## Verification evidence

- **This tree:** governed by `candidate-verification.json`, as stated under Release scope. No earlier
  receipt certifies it.
- **Primary-tree evidence for the selected bytes:**
  - certificate registration: `build/history/2026-10-29-letwin-certification/verification.json`
    (receipt `build/verification/20261029T074405.813355Z`, snapshot `13aa77fc…`);
  - readability batch: `build/history/2026-10-29-letwin-style-20261029T091203Z/verification.json`;
  - final primary tree: `build/verification/20261029T095710.427667Z/report.json`;
  - the pre-registration check, `build/history/2026-10-29-letwin-independent-check/result.json`, remains
    baseline evidence.

Verification scope and third-party trust are as described in
[research/verification.md](research/verification.md#receipts-and-trust-scope). No remote result is claimed.

## Next options and preservation

Remaining options:
- the original Letwin Theorem 1.1 route;
- Klartag's sharp 2R² theorem and Lipschitz Lemma 2.3;
- the open CEK supports, or a separate CEK paper-target decision;
- a separately reviewed, declaration-by-declaration namespace migration of the moment-map producers,
  which the readability batch only reviewed.

Preserve the recorded scopes when selecting a new literature target.

Prior handoffs are preserved verbatim with hashes:
- the pre-delivery handoff of this tree, under
  `build/history/2026-10-29-letwin-delivery-20261029T105117Z/claude-delivery/baseline/`;
- the registration-task handoff and canonical records, under
  `build/history/2026-10-29-letwin-style-20261029T091203Z/baseline/` and `baseline.json`;
- earlier ones, under `build/history/2026-10-29-letwin-certification/baseline/` and `baseline.json`.

Earlier migrations, reviews and failed runs remain in their owning tracked directories or ignored
history; none is rewritten. The primary checkout keeps the unpublished commit and the excluded auxiliary
work unchanged. Preserve outside work, Section/Engulfing's source and inherited whitespace in that
checkout, and the user's notification preferences. Existing provider/model, Opus-session and heartbeat
controls are outside these tasks. No API requests, other-chat delegation, purchases or automation
changes are part of them.
