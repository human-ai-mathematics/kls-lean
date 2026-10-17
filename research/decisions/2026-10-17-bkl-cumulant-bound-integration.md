# BKL Theorem 4.1 certificate: canonical integration

Date: 2026-10-17. Active Goal: BKL roadmap stage 3 ([Goal record](../handoffs/2026-10-17-bkl-step3-theorem41.md)). Stage 2
is accepted; the owner chose the BKL-sufficient cutoff localization route, then this stage.

## Result and scope

`Solutions.ThmBklCumulantBound.certificate` (`solutions/ThmBklCumulantBound.lean`, Blueprint and ledger
`thm:bkl-cumulant-bound`) is BKL arXiv:2610.05474v1, Theorem 4.1, (65)–(66), in the source form:

`∃ K : ℝ, 1 ≤ K ∧ ∀ d ≥ 1, ∀ n (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))), Isotropic μ → LogConcave μ →
∀ u, ∑ J : Fin d → Fin n, cumulant μ (d + 1) (Fin.cons u (e ∘ J)) ^ 2 ≤ K ^ d * (d!) ^ 2 * ‖u‖ ^ 2`.

- **Index.** Here m = d + 1, so every m ≥ 2 is covered, including the base m = 2.
- **Constant.** One K (witness 153) works for all orders, dimensions, laws and directions.
- **Hypotheses.** There is no compactness, Letwin, moment, energy or induction premise.
- **Form.** The sum is the coordinate sum (65).
- **Dimension.** n = 0 is included; there the statement is trivially true.
- **Bound form.** `bound` states `∃ K ≥ 1, ∀ d ≥ 1, CumulantBound d ((d!)² K^d)`.

**Relation:** the same conclusion through a different route (the cutoff localization), not the uncut Eldan process.

**Not claimed:**
- the uncut process, its uniqueness and non-explosion;
- the literal stochastic identities (68)–(73) and the infinite-horizon (95);
- Lemma 4.2 with the exact constant 8 for every isotropic law;
- Theorem 1.1, KLS, and paper coverage.

No composition is added: `theorem41`, `theorem41Compact` and `conjecture_of_letwinCompact` keep their
`LetwinCompactBound` hypothesis, and `KLS.kls` stays open.

## Proof chain (existing canonical producers; no new library proof, no API)

1. `cutoffEnergyClaim_all` with the actual `letwinCompactBound` gives `CutoffEnergyClaim 153 d` for every d ≥ 1. It uses
   the step `cutoffEnergyClaim_succ`, Lemma 5.1 from `generator_cumulantEnergy_ge`, and the claim-to-bound passage.
   This is the closed assembly of `lem:bkl-cutoff-energy`.
2. `cumulantBoundCompact_of_cutoffEnergyClaim` and `envelope_succ_eq` give `CumulantBoundCompact d ((d!)² 153^d)`.
3. `cumulantBound_of_compact` extends the bound to every isotropic log-concave law with the same constant.

## Placement

| File | Role |
| --- | --- |
| `solutions/ThmBklCumulantBound.lean` (new) | source-form certificate (title names `thm:bkl-cumulant-bound`) in namespace `Solutions.ThmBklCumulantBound`, with `bound` and `certificate` and two axiom guards. Imports `KLS.BKL.Localization.CutoffInductionStep`, `KLS.BKL.Localization.EnergyGenerator` and `KLS.Letwin.CompactBound`; no `Theorem41` and no `KLS/Target` |
| `research/audits/BKL/CumulantBoundAudit.lean` (new) | independent client: the handwritten source-index specification `Expected` (m ≥ 2) and `expected`; the base order m = 2; the third order for an arbitrary law; base and third orders with the same certificate constant |
| `formalization/FunctionalInequalities/KLS/BKL/SecondCumulant.lean` (existing) | module documentation only. Two sentences saying the all-order Theorem 4.1 "remains open" now say that this module states the base and that the all-order source certificate is registered separately. Every import, declaration, type, proof, namespace and line count is unchanged |
| `formalization/lakefile.toml`, `research/check_blueprint.py`, `research/a-series/ledger.yaml`, `solutions/README.md` | registry data: one Solutions root, one `CERTIFICATES` entry, one proved ledger node, one README section |
| `formalization/blueprint/src/chapters/45-shared-analytic-bridges.tex` | one theorem record `thm:bkl-cumulant-bound` |
| `research/progress/nodes.json`, `research/progress/literature.json`, `research/tasks.json` | node `BCUM` in its own supporting group `BKLCUMULANT`, with the edge `BCUT → BCUM` and no edge to KLS; BKL item T41 relation `alternative` with the certificate declarations, a local result and the proof-path certificate ([previous values](2026-10-17-pre-bkl-cumulant-bound-literature-notes.md)); evidence pins of the edited chapter |

No production-family module, public API, namespace, verifier option or exclusion changes. The four exploratory routes are
unchanged.

## Validation and evidence boundary

- **Source review.** Codex accepted the final certificate and client bytes: strict compilation, the literal m ≥ 2
  specification, standard axioms and kernel replay (`codex-source-review/ACCEPTANCE-v2.json` in the ignored Goal control
  directory).
  - The final certificate differs from the run03 source only in its module title, which now names the ledger id
    `thm:bkl-cumulant-bound`, as `research/check_ledger.py` requires. This is a documentation-only correction.
  - The run03 acceptance alone does not cover the new header bytes.
  - The metadata-prototype v1/v2 failures and header diagnostics are preserved.
- **Registration and metadata.** Prepared in a shadow copy of the source snapshot and integrated after Codex's review.
- **Milestone acceptance.** A passed fresh full local verification report for the exact integrated source/meta
  snapshot, plus its independent acceptance. Earlier reports apply only to their recorded snapshots.
