# Weak scalar and Hessian product calculus: canonical integration

Date: 2026-10-15. Active Goal: BKL roadmap step 1, the compact Letwin constant-eight endpoint `LetwinCompactBound`
([Goal record](../handoffs/2026-10-14-bkl-step1-letwin-constant-eight.md)).

Two small contracts, W3p1 and W3p2, were frozen by Codex. Each candidate was independently accepted with actual source-law
clients: `independent/W3p1` and `independent/W3p2` in `build/reviews/2026-10-14-letwin-constant-eight-goal/`.

The combined placement then passed two Codex checks:
- the isolated prototype (`W3-products-prototype/RESULT.json`, CODEX_WEAK_PRODUCT_PACKAGE_PROTOTYPE_PASS);
- placement acceptance (`W3-products-integration/PLACEMENT-ACCEPTANCE.json`, CODEX_PLACEMENT_ACCEPT).

The first prototype attempt failed only because a partial compiled namespace masked the checked parent view. Its diagnostic and the
receipt-locked overlay repair are kept in the prototype directory; no proof body was repaired. Claude integrated the exact prototype bytes
(`W3-products-integration/SOURCE-MANIFEST.json`) as sole canonical writer. No commit, push, tag, remote CI or release is authorized.

## Exact scope

**Global product: `Analysis.HasWeakDerivAlong.mul_of_memLp_two` (type hash 794188879).**
- Hypotheses:
  - f has weak derivative df along v, and g has weak derivative dg along v;
  - f, df, g and dg are all in L2 of Lebesgue measure on the whole space.
- Conclusion: f*g is globally integrable and has the directional weak derivative df*g + f*dg along v. Only that one direction is
  involved: full-gradient W1,1 membership is not asserted, and no L2 claim is made for the derivative.
- Scope: every finite dimension including zero and every direction, including zero.
- The proof mollifies g with the existing `Mollification` L2 approximation and passes to the limit. It assumes no boundedness or C1/C2 regularity of the rough factors, no finite
  whole-space volume or product premise.

**Bounded local product: `Analysis.HasWeakDerivAlong.mul_of_locally_memLp_two` (type hash 1355563796).**
- Hypotheses:
  - f and g are in L-infinity;
  - their weak derivatives df and dg along the fixed direction v are in L2 on every compact set.
- Conclusion: the uncut product f*g has the weak derivative df*g + f*dg along v, and that derivative is L2 on every compact set.
- Scope: every finite dimension including zero.
- The proof cuts off by a smooth bump equal to one near the support of each test, applies the global product rule to the cutoff factors and
  removes the cutoff pointwise. Raw f, df, g and dg are never assumed globally L2, the rough factors are never assumed C1/C2, and
  whole-space volume is never treated as finite. The audit clients apply it along each coordinate direction.

**Audit clients** (`research/audits/BKL/WeakHessianProductAudit.lean`, canonical imports only). They take the actual normalized regular
moment law from `exists_regular_moment_weak_tensor`, keeping its normalization and actual gradient pushforward, and produce:
- products of cutoff Hessian entries with their global weak derivative;
- the global testing identity;
- the **uncut** product H_ij * H_ab with the compact-local L2 derivative T_kij * H_ab + H_ij * T_kab;
- the square H_ij^2 with derivative 2 * H_ij * T_kij.

Here T_kij is the weak first derivative of the Hessian entry H_ij along e_k, i.e. the potential's weak third-derivative tensor. No raw
global L2 of H or T, no C1/C2 of H and no product conclusion is assumed.

**What is not proved.** This is weak product calculus for Hessian entries. It is not determinant, cofactor or inverse calculus, weak Hessian
evolution, the integrated PSD trace estimate, weak Brascamp-Lieb, Stein/H^-1, the spectral constant-8 assembly, Letwin Theorems 2.5/1.2,
unconditional BKL or KLS. Paper coverage, the 30 ledger certificates and the four active routes are unchanged.

## Placement and maps

| File | Change |
| --- | --- |
| `formalization/FunctionalInequalities/Analysis/WeakDerivative.lean` | one added import `FunctionalInequalities.Analysis.Mollification`; one module-docstring line replaced by the product scope; new appended section `WeakProducts` with the two public theorems and the two compiler-private helpers; all original declarations and bodies unchanged |
| `research/audits/BKL/WeakHessianProductAudit.lean` | new audit; four clients in `WeakHessianProductAudit.{Global,Local}`, a private Global helper, six axiom reports |

- No new library module and no root aggregate change.
- Import direction: `Mollification` imports Calculus and Mathlib, not `WeakDerivative`, so there is no cycle. The scalar weak-calculus
  owner does not import KLS/CEK; only the audit clients consume the R0 producer.

Promotion map (prototype `PROMOTION-MAP.json`):
- **Public names:** the two public names are unchanged from the accepted candidates.
- **Audit clients:**
  - `W3p1Client.produced_normalized_cutoff_hessian_product` -> `WeakHessianProductAudit.Global.produced_normalized_cutoff_hessian_product`;
  - `W3p1Client.global_product_testing` -> `WeakHessianProductAudit.Global.global_product_testing`;
  - `W3p2Client.produced_normalized_hessian_product` -> `WeakHessianProductAudit.Local.produced_normalized_hessian_product`;
  - `W3p2Client.produced_normalized_hessian_square` -> `WeakHessianProductAudit.Local.produced_normalized_hessian_square`.
- **Private helpers:** the W3p1 pairing helper `tendsto_integral_mul_of_l2` and the W3p2 frozen cutoff helper `cutoff_memLp` are now
  compiler-private in `WeakDerivative`, with headers and bodies byte-identical. The candidates' accepted bodies appear as contiguous
  verbatim text.
- No alias, signature change or migration of existing declarations.

## Validation

Local canonical checks:
- `lake build` completed.
- Strict `-DwarningAsError=true` compilation of the owner and of the unchanged aggregate produced empty logs. The audit compiled strictly
  (exit 0) with exactly its six `#print axioms` reports, all `[propext, Classical.choice, Quot.sound]`.
- The eight existing complete types, including `HasWeakDerivAlong`, are unchanged.
- The two new public types and the four client types equal the accepted hashes.
- `leanchecker` replay of `Analysis.WeakDerivative` and of the compiled audit passed.

Blueprint, `nodes.json`, `tasks.json`, `literature.json`, the proof path, `HANDOFF.md` and the root summary are synchronized.

This package's final full verification and Codex's independent canonical acceptance are recorded in the ignored
`W3-products-integration/` directory. They must match the post-integration snapshot. The earlier receipt
`20261014T143611.827158Z` covers only the parent snapshot `7db01f58…`.

## Next

Open in order:
- the determinant/cofactor/inverse and any other genuinely missing chain interfaces for the weak Hessian;
- weak Hessian evolution and the integrated PSD trace estimate;
- weak Brascamp-Lieb, Stein/H^-1 transport and the spectral constant-8 assembly.

No proof task is dispatched by this integration.
