# BKL cutoff energy certificate: canonical integration

Date: 2026-10-17. Active Goal: BKL roadmap stage 2, stochastic localization
([Goal record](../handoffs/2026-10-17-bkl-step2-stochastic-localization.md)). On 2026-10-17 the owner explicitly chose
the completion scope: accept the BKL-sufficient cutoff route, then continue to stage 3.

## Result and scope

`Solutions.LemBklCutoffEnergy.certificate` (`solutions/LemBklCutoffEnergy.lean`, Blueprint and ledger
`lem:bkl-cutoff-energy`) states BKL arXiv:2610.05474v1, Sections 4–6, equation (95), in finite-horizon cutoff form.
- **Statement.** For every d ≥ 1 (order m = d + 1) and every n, take any compactly supported isotropic log-concave
  probability measure μ on `EuclideanSpace ℝ (Fin n)`, unit vector u, ε > 0 and T ≥ 0. Then there is R₀ such that for
  every R ≥ R₀, every probability space with an n-dimensional Brownian motion and a usual filtration, and every cutoff
  Eldan process p with `IsEldanCutoff μ hc W ℱ hW (ballCutoff R) p`:
  `cumulantEnergy μ d u + ½ ∫ ∫_{(0,T]} ballCutoff R (p_s)² · cumulantEnergy (μ_{p_s}) (d + 1) u ≤ (d!)² 153^d + ε`.
- **The named predicate.** `bound d hd : CutoffEnergyClaim 153 d`.
- **Kept from the source:** the exact factor ½, the normalization b_m = K^{m−1}((m−1)!)² of (94), a universal K = 153
  and every dimension.
- **Different from the source:**
  - a finite horizon with tolerance ε and all sufficiently large cutoff radii, instead of ∫₀^∞;
  - the cutoff weight γ_R² inside the integral;
  - the strong solution of the cutoff equation instead of the uncut Eldan process;
  - the order range including m = 2.

**Not claimed:**
- the uncut Eldan process (strong solution, uniqueness, non-explosion);
- the literal stochastic identities (68)–(73);
- the source's infinite-horizon (95);
- BKL Theorem 4.1 (stage 3), Theorem 1.1 and KLS (stage 4).

`theorem41`, `theorem41Compact` and `conjecture_of_letwinCompact` keep `LetwinCompactBound` as a hypothesis. No
composition is added, and `KLS.kls` stays open.

## Proof chain (existing canonical declarations; no new library proof)

`bound` composes the existing cutoff induction with the actual compact constant-8 theorem `letwinCompactBound`:
- `cutoffEnergyClaim_all`, with the base case `cutoffEnergyClaim_one` and the step `cutoffEnergyClaim_succ`;
- Lemma 5.1 discharged by `generator_cumulantEnergy_ge` (C = 17);
- the claim-to-bound passage `cumulantBoundCompact_of_cutoffEnergyClaim`.

`certificate` unfolds `weightedEnergyIntegral` and `envelope_succ_eq`. The cutoff process and its inputs are:
- `exists_isEldanCutoff` and `IsEldanCutoff.dynkin` (strong solution and Dynkin's identity);
- `IsEldanCutoff.ae_Q_posSemidef` (Q positive semidefinite);
- the generators of Lemma 4.3 and (71) and the energy generator (Lemma 5.1);
- Lemma 5.2 in cutoff form (`energy_integral_le_of_generator_ge`);
- the Lyapunov moment bound and the boundary removal.

All of these were accepted in the stage-2 source audit (all 41 mapped declarations, standard axioms).

## Placement

| File | Role |
| --- | --- |
| `solutions/LemBklCutoffEnergy.lean` (new) | source-form supporting certificate, namespace `Solutions.LemBklCutoffEnergy`, `bound` and `certificate`, two axiom guards; imports `KLS.BKL.Localization.CutoffInductionStep`, `KLS.BKL.Localization.EnergyGenerator`, `KLS.Letwin.CompactBound` (no `Theorem41`, no `KLS/Target`) |
| `research/audits/BKL/CutoffEnergyAudit.lean` (new) | independent client: full handwritten specification `Expected d` matched by the certificate, an actual Brownian setup and strong cutoff process for every prior and radius, and the arbitrary-direction compact cumulant handoff with 153 and (d!)² |
| `formalization/FunctionalInequalities/Probability/Diffusion/Setup.lean` (existing) | module documentation only: the sentence "no vendored declaration depending on `sorry` is used" becomes "only vendored declarations with standard logical axioms are used", because the conservative certificate guard of `research/check_ledger.py` scans comments and this certificate is the first whose import closure reaches the module; every import, declaration, proof, API and line count is unchanged (Codex `endpoint-source-v3/ACCEPTANCE.json`) |
| `formalization/lakefile.toml`, `research/check_blueprint.py`, `research/a-series/ledger.yaml`, `solutions/README.md` | registry data: one Solutions root, one `CERTIFICATES` entry, one proved ledger node, one README section |
| `formalization/blueprint/src/chapters/45-shared-analytic-bridges.tex` | one lemma record `lem:bkl-cutoff-energy` |
| `research/progress/nodes.json`, `research/progress/literature.json`, `research/tasks.json` | node `BCUT` in its own supporting group `BKLCUTOFF` with the prerequisite edge `LCOMPACT8 → BCUT`; BKL item E95 (partial), local result, proof-path step and current notes ([previous values](2026-10-17-pre-bkl-cutoff-energy-literature-notes.md)); evidence pins of the edited chapter |

No production-family module, public API, namespace, verifier option or exclusion changes. The four exploratory routes
are unchanged, and no edge leads from `BCUT` to KLS.

## Validation and evidence boundary

- **Codex acceptance of the exact three source files** (certificate, client, `Setup.lean` documentation):
  `endpoint-source-v3/ACCEPTANCE.json` in the ignored Goal control directory. `Setup.lean`, the certificate and the
  client pass strict compilation with standard axioms and local kernel replay.
- **Registration and metadata:** prepared in a shadow copy of the source snapshot and integrated after Codex's
  independent review.
- **Final acceptance:** a passed fresh full local verification report for the exact integrated source/meta snapshot,
  plus its independent acceptance. Earlier reports apply only to their recorded snapshots.
