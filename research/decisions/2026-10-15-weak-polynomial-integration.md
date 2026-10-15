# Weak finite polynomial calculus: canonical integration

Date: 2026-10-15. Active Goal: BKL roadmap step 1, the compact Letwin constant-eight endpoint `LetwinCompactBound`
([Goal record](../handoffs/2026-10-14-bkl-step1-letwin-constant-eight.md)).

Provenance:
- Codex froze four small contracts, W3p3-W3p6, and accepted each candidate independently, together with its actual source-law clients (`independent/W3p3..6` in
  `build/reviews/2026-10-14-letwin-constant-eight-goal/`).
- The combined placement passed Codex's isolated prototype (`W3-polynomials-prototype/RESULT.json`,
  CODEX_WEAK_POLYNOMIAL_PACKAGE_PROTOTYPE_PASS) and placement acceptance (`W3-polynomials-integration/PLACEMENT-ACCEPTANCE.json`,
  CODEX_PLACEMENT_ACCEPT).
- Only exact compiler-generated anonymous binder/module-scope names had to be mapped: the W3p4 instance binder and seven client lambdas.
  The raw types, ASTs and diagnostics are retained in the prototype directory, and no statement or proof changed.
- Claude integrated the exact prototype bytes (`W3-polynomials-integration/SOURCE-MANIFEST.json`) as the sole canonical writer.
- No commit, push, tag, remote CI or release is authorized.

## Exact scope

All four theorems concern weak derivatives along ONE fixed direction v, with the given directional weak derivatives only L2 on every
compact set. Boundedness hypotheses differ by theorem:
- finite linearity takes only weak derivatives (hence local integrability) of the f_i and needs no boundedness;
- the finite-product and matrix theorems take L-infinity factors or entries.

None assumes global L2 of raw data, C1/C2 regularity of the rough data or finite whole-space volume.

- `Analysis.hasWeakDerivAlong_finsetSum_mul` (type hash 1288651072). For a finite real linear combination sum_i c_i f_i (any finite
  set, possibly empty; signed coefficients), the conclusion is the weak derivative sum_i c_i df_i, with compact-local L2 density. Here
  only the derivatives df_i are assumed L2 on compact sets; no boundedness of f_i is needed.
- `Analysis.hasWeakDerivAlong_finsetProd_of_locally_memLp_two` (type hash 608913713). For a finite product prod_i f_i of L-infinity
  factors (any finite set, the empty product included), the conclusion is the Leibniz weak derivative
  sum_i df_i prod_{j != i} f_j, with compact-local L2 density.
- `Analysis.hasWeakDerivAlong_det_of_locally_memLp_two` (type hash 3571451012). For a bounded weak matrix field A over an arbitrary
  finite index type (empty and singleton included) and an independent ambient dimension d, det A has as weak derivative the signed
  permutation polynomial sum_sigma sign(sigma) sum_i DA_{sigma i, i} prod_{j != i} A_{sigma j, j}, with compact-local L2 density. No
  symmetry, positivity or invertibility is assumed.
- `Analysis.hasWeakDerivAlong_trace_quadratic_of_locally_memLp_two` (type hash 1638840520). For an arbitrary constant real matrix B
  (no symmetry, PSD or invertibility), independent ambient and matrix dimensions and zero dimensions, tr(B A B A) has the weak derivative
  2 tr(B A B DA), with compact-local L2 density.

The audit `research/audits/BKL/WeakHessianPolynomialAudit.lean` applies these to the actual normalized regular moment law from
`exists_regular_moment_weak_tensor`, keeping normalization and the actual gradient pushforward. It covers:
- the empty product in dimension zero;
- the weak determinant of the Hessian, with its signed permutation-polynomial density;
- the weak cofactors (adjugate entries), obtained as determinants of updated-row matrices;
- a singleton cofactor;
- the weak derivative 2 tr(B H B T_k) of tr(B H B H) for every real B (this formula belongs to the trace quadratic only);
- the zero matrix size.

T_k is the produced tensor of weak derivatives of the Hessian entries along e_k.

These are first weak derivatives of finite matrix polynomials. They do NOT provide:
- global L2 of raw data, or a C1/C2/smooth Hessian;
- a second generator identity or Letwin (2.8)/(2.10);
- weak Hessian evolution, inverse or log-det calculus;
- the integrated trace estimate;
- weak Brascamp-Lieb, Stein/H^-1, the regular-class bound, compact constant 8 or KLS.

Letwin Theorems 2.5/1.2 and BKL remain partial/open. Paper coverage, the 30 ledger certificates and the four active routes are unchanged.

## Placement and maps

| File | Change |
| --- | --- |
| `formalization/FunctionalInequalities/Analysis/WeakDerivative.lean` | appended W3p3 and W3p4 sections; the pre-integration file is an exact byte prefix |
| `formalization/FunctionalInequalities/Analysis/Matrix/WeakDerivative.lean` | new module in the existing `Analysis/Matrix` family; imports only the scalar `Analysis.WeakDerivative`; three private finite matrix identities (`reverse_triple_sum`, `trace_four_eq`, `trace_product_derivative_eq`) and the public W3p5/W3p6 theorems |
| `formalization/FunctionalInequalities.lean` | one import (`Analysis.Matrix.WeakDerivative`) |
| `research/audits/BKL/WeakHessianPolynomialAudit.lean` | new audit in `WeakHessianPolynomialAudit.{Scalar,Determinant,Trace}`; the only file importing CEK; ten axiom reports |

- Import direction: matrix imports scalar. No generic owner imports KLS/CEK.
- The accepted W3p3, W3p4 and W3p5 bodies appear verbatim and contiguous. The W3p6 helpers and theorem appear verbatim as separate chunks around the W3p5 theorem.
- The public names are the accepted names. No alias, migration or change to the ten existing weak-derivative interfaces.

## Integration boundary for the next steps

Read-only source review: `SOURCE-INTEGRATION-BOUNDARY-REVIEW.md`, pinned to arXiv:2607.24164v1 in
`SOURCE-INTEGRATION-BOUNDARY-PIN.json`.

- **Height cutoffs.** The source integrates via the height cutoffs of Appendix A.4 and the generic A.5 conservation step. The existing
  smooth A.4 construction cannot be invoked for the actual C1/Lipschitz-gradient potential, so a weak counterpart must use only the actual
  regularity.
- **Evolution density.** Products of tensor entries in the evolution density are only locally L1 from the current local L2 tensor. The
  old N13c locally-L2 right-hand side does not cover that consumption, and no global weighted T^2 or C2 bound is available.

Next:
1. Identify the accepted weak determinant polynomial density with the existing pointwise Jacobi algebra, using the actual a.e. positive
   determinant and log-det equation; then the weak inverse, chain and testing interfaces.
2. Then the weak height-cutoff consumption.

## Validation

Local canonical checks:
- `lake build` completed.
- Strict `-DwarningAsError=true` compilation of the scalar and matrix owners and the aggregate produced empty logs. The audit compiled
  strictly (exit 0) with exactly its ten standard `#print axioms` reports.
- The ten existing complete types are unchanged.
- The thirteen new public, private-helper and client complete types equal the prototype hashes.
- `leanchecker` replay of both owners and the compiled audit passed.

Blueprint, `nodes.json`, `tasks.json`, `literature.json`, the proof path, `HANDOFF.md` and the root summary are synchronized.

This package's final full verification and Codex canonical acceptance are recorded in the ignored `W3-polynomials-integration/`
directory and must match the post-integration snapshot. The parent receipt `20261014T165922.947275Z` covers only `cb4d39f4…`.
