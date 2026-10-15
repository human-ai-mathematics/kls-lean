# Actual R0 source-law weak tensor: canonical integration

Date: 2026-10-14. Active Goal: BKL roadmap step 1, the compact Letwin constant-eight endpoint `LetwinCompactBound`
([Goal record](../handoffs/2026-10-14-bkl-step1-letwin-constant-eight.md)).

Provenance of the integrated package (paths below are in the Goal control directory):
- Codex froze two small contracts and accepted each candidate independently (`independent/N11d5`, `independent/N11d6`):
  - N11d.5 exports the existing 4/kappa centered-difference estimate of the moment potential;
  - N11d.6 is a generic Lipschitz exponent producer.
- The actual R0 tensor consumer was proved and checked as an independent client.
- The complete package passed Codex's isolated prototype (`R0-input-closure-prototype/RESULT.json`,
  CODEX_R0_SOURCE_INPUT_CLOSURE_PACKAGE_PROTOTYPE_PASS) and placement acceptance (`R0-input-closure-integration/PLACEMENT-ACCEPTANCE.json`,
  CODEX_PLACEMENT_ACCEPT).

Claude integrated the exact prototype bytes (`R0-input-closure-integration/SOURCE-MANIFEST.json`) as sole canonical writer. No commit,
push, tag, remote CI or release is authorized.

## Exact scope

- `Analysis.secondDifference_le_of_map_gradient` (`Analysis/Convex/GradientLipschitz.lean`, type hash 1782526454).
  - Hypotheses, unchanged from the existing gradient theorem:
    - u is Lipschitz, convex and C1, with the normalization ∫e^{-u} = 1;
    - the gradient pushes e^{-u}dx forward to 1_K e^{-V}dx, with K compact and convex;
    - V is C1 and V - (kappa/2)|.|^2 is convex, with kappa > 0.
  - Conclusion: u(x+h) + u(x-h) - 2u(x) <= (4/kappa)|h|^2 for all x and h, in every finite dimension including zero.
  - It assumes no difference bound.
  - The proof is the existing proof prelude of `lipschitzWith_gradient_of_map_gradient` through its internal `hsd`.
  - That theorem now consumes the exported estimate; its name, header and complete type (1958789015) are unchanged.
- `Analysis.exists_lipschitzWith_neg_add_comp_gradient` (new generic leaf `Analysis/Lipschitz/Gradient.lean`, type hash 1346594316).
  - Hypotheses:
    - u is L-Lipschitz;
    - its total gradient is G-Lipschitz;
    - V is C1.
  - It produces a constant LF with -u + V(gradient u) LF-Lipschitz, in every finite dimension including zero.
  - There is no C1 hypothesis on u, no convexity, PDE, normalization, bounded-range or derivative bound, and no exponent-Lipschitz premise.
  - The source is the independently accepted N11d.6 proof with its redundant fourth Mathlib import removed. The API answer is unchanged; the original contract rejection and the raw candidate remain in scratch history.
- `Analysis.exists_regular_moment_weak_tensor` (`KLS/CEK/MomentRegularity.lean`, type hash 3977891398).
  - Hypotheses: exactly the original R0 regular-source hypotheses:
    - n > 0;
    - K compact and convex with nonempty interior;
    - W smooth with W - (kappa/2)|.|^2 convex, kappa > 0;
    - a probability measure mu with density 1_K e^{-W};
    - isotropy.
  - It produces u, L, LF and T together with every previous R0 field:
    - convex, L-Lipschitz, normalized mass and the actual gradient pushforward to mu;
    - C1 with a 16/kappa-Lipschitz gradient;
    - a.e. positive definite Hessian, the log-det equation and the 16/kappa cap.
  - It also produces:
    - the original global centered-difference bound with coefficient 4/kappa;
    - the global Lipschitz exponent -u + W(gradient u);
    - weak derivatives T of every Hessian entry along every coordinate direction, L2 on every compact set.
  - It assumes no given centered-difference bound, exponent bound, tensor, H1, trace or main-bound premise.
  - It is the independently proved client `N11d6Client.produced_regular_moment_weak_tensor` (independent N11d6 NormalizedClient), promoted with its statement and proof body unchanged; only the name and namespace change. `exists_regular_moment_potential` (type hash 3225770193) and its proof are unchanged.

Consequences:
- The two original N11d inputs are therefore closed for this actual regular source class.
- The generic `exists_weak_third_derivative` legitimately keeps its original inputs.
- No unrestricted Monge-Ampere or gradient-only exponent result is claimed.

What this result is and is not:
- It is weak, locally L2 Hessian regularity (Hessian entries in H1_loc).
- It does not establish global C2 or smooth regularity, a gradient diffeomorphism, the integrated trace estimate, Letwin Theorems 2.5/1.2,
  compact constant 8, unconditional BKL or KLS.
- Paper coverage, the 30 ledger certificates and the covered ADM-G/BGL targets are unchanged.

## Placement and maps

| File | Change |
| --- | --- |
| `Analysis/Convex/GradientLipschitz.lean` | reviewed extraction: new public `secondDifference_le_of_map_gradient` before the unchanged-type `lipschitzWith_gradient_of_map_gradient`, which consumes it; three private helpers unchanged; module docstring extended |
| `Analysis/Lipschitz/Gradient.lean` | new leaf in the existing `Analysis/Lipschitz/` family; three Mathlib imports; public `exists_lipschitzWith_neg_add_comp_gradient` |
| `KLS/CEK/MomentRegularity.lean` | imports `Analysis.Convex.HessianRegularity` and `Analysis.Lipschitz.Gradient`; module docstring extended; promoted `exists_regular_moment_weak_tensor` appended |
| `FunctionalInequalities.lean` | one import (`Analysis.Lipschitz.Gradient`) |
| `research/audits/BKL/RegularMomentWeakTensorAudit.lean` | new audit, canonical imports only, five clients in `RegularMomentWeakTensorAudit.{Difference,Exponent,Tensor}`, ten axiom reports |

API changes:
- Three new public declarations.
- No public name, type or namespace migration of existing declarations, and no alias.
- Promotion map: `N11d6Client.produced_regular_moment_weak_tensor` -> `FunctionalInequalities.Analysis.exists_regular_moment_weak_tensor` (prototype `PROMOTION-MAP.json`).
- Import direction: KLS/CEK imports Analysis owners; no Analysis owner imports KLS.

Audit coverage:
- The audit clients consume:
  - the produced difference bound;
  - the old 16/kappa gradient through the exported estimate;
  - the produced exponent;
  - the produced tensor with canonical N11e almost-everywhere symmetry and the weak testing identity.
- The generic N11e theorem does not depend on the producer, and no such edge is drawn.

## Validation

Local canonical checks:
- `lake build` completed.
- Strict `-DwarningAsError=true` compilation of the three owners and the aggregate produced empty logs; the audit compiled
  strictly (exit 0) and its log holds exactly the ten `#print axioms` reports, all standard.
- The five complete types equal the accepted hashes: 1782526454, 1958789015, 1346594316, 3977891398, 3225770193.
- The ten axiom reports use only propext, Classical.choice and Quot.sound.
- `leanchecker` replay of the three owners passed.

Metadata updates:
- Blueprint chapter `45-shared-analytic-bridges.tex` gains three appended lemmas; the existing N11d lemma's heading and its
  closing current-state sentence are corrected to point to the source-law application (no new `\uses` edge), and the earlier
  chapter text is otherwise unchanged (pre-integration copy kept in the ignored integration directory).
- `nodes.json`, `tasks.json` (with refreshed pinned evidence hashes), `literature.json`, the proof path, `HANDOFF.md` and the root summary are synchronized.

Pending:
- At this documentation stage the final full `research/verify.py` run and Codex's independent canonical acceptance are pending.
- Their results will be recorded in the ignored `R0-input-closure-integration/` report and `STATE.json`.

## Next

1. Weak local calculus and chain rules for the produced tensor.
2. Weak Hessian evolution and the integrated PSD trace estimate.
3. Weak Brascamp-Lieb, Stein/H^-1 transport and the spectral constant-8 assembly.

No proof task is dispatched by this integration.
