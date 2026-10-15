# Determinant polynomial density and the outer Jacobi differential: canonical integration

Date: 2026-10-15. Active Goal: BKL roadmap step 1, the compact Letwin constant-eight endpoint `LetwinCompactBound`
([Goal record](../handoffs/2026-10-14-bkl-step1-letwin-constant-eight.md)).

## History of the contract

- **J1 (`fderiv_det_eq_sum_permutation`) exhausted naturally.** Its run is `runs/J1-run01` in `build/reviews/2026-10-14-letwin-constant-eight-goal/`.
  - All four rounds failed to compile, and no candidate was accepted.
  - No complete candidate compiled. In the final attempt the scalar polynomial portion reported no error, but the complete candidate failed
    at the instance-path chain step, and an unaccepted prefix of a failed candidate is not a certified result. The reported errors were
    typeclass instance paths:
    - the matrix path carried `Matrix.Norms.Elementwise` normed instances (rounds 1-2);
    - the scalar `HasDerivAt` produced by `comp_hasDerivAt` carried `Real.normedAddCommGroup`/`RCLike` module instances instead of `Real.instAddCommGroup`/`Semiring.toModule` (rounds 3-4).
  - Codex reviewed the exhaustion. The failed history is preserved unchanged and the contract was not retried.
- **J1a: a smaller scalar contract.** `deriv_det_add_smul_zero` states that the derivative at 0 of t ↦ det(A + t N) is the signed permutation polynomial. It contains no `fderiv` and no outer chain rule.
  - It was accepted in its first round (`runs/J1a-run01`, candidate `70962ed4…`).
  - Codex accepted it independently (`independent/J1a`).
  - In that acceptance, the original full J1 statement is assembled as a genuine client from the existing Mathlib directional-derivative API `DifferentiableAt.deriv_comp_add_smul` (`Mathlib/Analysis/Calculus/TaylorIntegral`).
- **Placement.** The coherent owner prototype passed (`J1-prototype/RESULT.json`, CODEX_POINTWISE_J1_PACKAGE_PROTOTYPE_PASS), as did placement acceptance (`J1-integration/PLACEMENT-ACCEPTANCE.json`, CODEX_PLACEMENT_ACCEPT).
- **Integration.** Claude, as the sole canonical writer, integrated the exact prototype bytes listed in `J1-integration/SOURCE-MANIFEST.json`.
- No commit, push, tag, remote CI or release is authorized.

## Exact scope

The new public theorem is `Analysis.fderiv_det_eq_sum_permutation` (complete type hash 4101675772, exactly the original J1 statement). It holds for:
- every finite index type, empty and singleton included;
- arbitrary real square matrices A and N, singular or non-Hermitian.

Its statement is that the outer derivative of the determinant satisfies `fderiv ℝ det A N = Σ_σ sign σ Σ_i N_{σ i, i} Π_{j ≠ i} A_{σ j, j}`. This identifies the signed permutation-polynomial density of the accepted weak determinant rule with the existing outer differential of det. It assumes no invertibility, positivity or regularity of a rough field. The scalar J1a lemma is a private helper (type hash 2443579441, body verbatim apart from `private`).

The audit `research/audits/BKL/WeakDeterminantJacobiAudit.lean` (namespace `WeakDeterminantJacobiAudit`; map `J1Client` -> `WeakDeterminantJacobiAudit`) contains three clients:
- **Regular source law.** For the actual normalized regular moment law from `exists_regular_moment_weak_tensor`, with its normalization and actual gradient pushforward retained:
  - det H has the weak derivative given by the signed permutation polynomial in the produced tensor T_k, with compact-local L2 density;
  - almost everywhere this density equals det(H) tr(H^-1 T_k). This uses the existing Jacobi formula `fderiv_det_eq_det_mul_trace` and the actual a.e. positive definiteness produced by R0.
- **Singular singleton.** A singular 1×1 matrix has a nonzero determinant differential in a nonzero direction.
- **Empty matrix.** The empty-matrix case.

What this result is not:
- It is NOT weak log-det or inverse calculus, the exponent chain rule, the first Monge-Ampère derivative (2.4) in weak form, a PDE or evolution identity, or the trace bound.
- It is NOT source C2 or the smooth Lemma 2.2.
- It does NOT cover Letwin Theorem 2.5/1.2, compact constant 8, BKL or KLS.

Paper coverage, the 30 ledger certificates and the four active routes are unchanged.

## Placement and maps

| File | Change |
| --- | --- |
| `formalization/FunctionalInequalities/Analysis/Matrix/DeterminantDerivative.lean` | one added import `Mathlib.Analysis.Calculus.TaylorIntegral`; appended section `DeterminantPolynomialIdentification` with the private scalar helper and the public theorem; the old file is otherwise an exact line prefix |
| `research/audits/BKL/WeakDeterminantJacobiAudit.lean` | new audit; imports the owner, `Analysis.Matrix.WeakDerivative` and `KLS.CEK.MomentRegularity` |

- **Aggregate:** unchanged, because the owner is already imported.
- **Existing declarations:** the seven old declarations of the owner, including the private `detML`, keep their complete types and proof values.
- **Namespaces and imports:** no alias, no namespace migration, and no application import in the owner.
- **Imports considered:** the narrower `Comp` import path showed the same instance-path mismatch during placement review; its diagnostic is kept in the prototype directory.

## Validation

Local canonical checks:
- `lake build` passed.
- Strict `-DwarningAsError=true` compilation of the owner, the aggregate and the audit produced empty logs.
- The full structural type and value ASTs of the seven old declarations match the prototype baseline exactly.
- The full type ASTs of the original J1 and of the private helper match exactly.
- The three audit client types equal Codex's preflight types (`compareAuditTypes`).
- The structured standard-axiom audit uses `verify.axiom_audit_code` with exact environment names, including the private names. All twelve declarations use only propext, Classical.choice and Quot.sound.
- `leanchecker` replay of the owner and the compiled audit passed.

Metadata changes:
- The Blueprint gains one appended lemma. The existing Jacobi lemma `lem:letwin-monge-ampere-first` now states the nonzero-determinant
  (invertibility) hypothesis of its pointwise and composed formulas, matching the actual Lean statements; this is a documentation scope
  correction, not a proof, statement or source change.
- `nodes.json`, `tasks.json`, `literature.json`, the proof path, `HANDOFF.md` and the root summary are synchronized.

Pending at this stage:
- This package's final full verification and Codex canonical acceptance are recorded in the ignored `J1-integration/` directory.
- The parent receipt `20261014T193901.458518Z` covers only `25732189…`.

## Next

1. Derive or reuse the exponent derivative, together with a weak exp / a.e. transport consumer interface. The private `ae_fderiv_mongeAmpere_exponent` in `Analysis/BakryEmery/IntegrationByParts/WeakInverseHessian.lean` is already proved and is not to be re-proved.
2. Then weak inverse, log-det and testing interfaces.
3. Then the weak source height cutoffs (Appendix A.4/A.5). These use locally L1 right-hand sides and locally L2 flux, not the old N13c L2 right-hand side. The smooth A.4 does not apply to the actual C1 / Lipschitz-gradient potential.
4. Then evolution, the trace estimate, Brascamp-Lieb, Stein and the spectral steps.

Throughout, T is only locally L2, so T^2 is only locally L1. No global weighted T^2 bound or C2 regularity is available.
