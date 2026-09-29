# Ambient and intrinsic covariance: statement, semantic alignment, and proof

Date: 2026-09-07 (Asia/Shanghai). Baseline: uncommitted working tree on top of `0451f2e`, immediately followed
[Borell density proof record](2026-09-07-borell-density-proofs.md). Lean/Mathlib is v4.33.0. User instructions:
"Proceed according to our Blueprint, then optimize your recent findings". This decision does not involve commit, push, remote CI, or release.

## Completed Interface Optimization

The review of the previous record found that the proof text for downstream `lem:covariance-core-closure` used "ρ is continuous on Ω", a fact that only appeared internally in the proof. Now it is exported as `IsBorellDensity.continuousOn_interior_pos` (interior of the positive set) and `IsBorellDensity.continuousOn_interior_support` (interior of the support), and `exists_bounds_of_isCompact` is changed to invoke the latter; the certificate file includes the corresponding axiom guards, and the module documentation is synchronized. No changes are made to the statements of any previously proven assertions.

## Node Selection

atlas shows after Borell's theorem certification `lem:ambient-intrinsic-covariance` is the only one depending solely on previously defined statements
`inspect_infrastructure` leaf node, and it is the last unverified premise of `def:affine-poincare-constant`.
`lem:relative-perimeter-smoothing` and `lem:covariance-core-closure` involve smoothing and distributional closability,
left for future work.

## Statement Design

Module [Probability/IntrinsicCovariance.lean](../../formalization/FunctionalInequalities/Probability/IntrinsicCovariance.lean).
Type variables: `E` finite-dimensional complete real inner product space, Borel, second countable; `V := (affineSupport μ).direction`;
`ν := intrinsicMeasure μ`; premise `hμ : MemLp id 2 μ`. `Covariance.operator` is the Riesz representation in Mathlib `covarianceBilin`, already defined, unchanged.

| Statement | Content |
| --- | --- |
| `Probability.integral_id_mem_affineSupport` | The barycenter lies in the affine support |
| `Probability.intrinsicMap_ae_eq_orthogonalProjection` | Intrinsic coordinates a.e. equal to the orthogonal projection after translation to the support point |
| `Probability.memLp_id_two_intrinsicMeasure` | Intrinsic laws preserve second-order moments |
| `Covariance.operator_apply_eq_zero_of_mem_orthogonal` | Ambient covariance operator is zero on `Vᗮ` |
| `Covariance.covarianceBilin_intrinsic` | Intrinsic covariance bilinear form equals the ambient form restricted to `V` |
| `Covariance.operator_coe_intrinsic` | Ambient operator on `V` equals intrinsic operator (embedded back into `E`) |
| `Covariance.opNorm_operator_intrinsic` | The norms of the two operators are equal |
| `Covariance.intrinsic_operator_inner_self_pos` | Intrinsic covariance is positive definite |
| `Covariance.operator_eq_zero_of_direction_eq_bot` | The zero-dimensional direction yields a zero ambient operator |

The second-moment assumption must be explicit: without a second moment, Mathlib uses the convention `covarianceBilin = 0`, otherwise the statement would be hollow.
Certificate `Solutions.LemAmbientIntrinsicCovariance.certificate` packages the five conclusions together, and in the zero-dimensional case simultaneously gives the intrinsic operator as zero.

## Semantic alignment

| Blueprint clause | Lean | Conclusion |
| --- | --- | --- |
| Borel probability law μ with finite second-order moment, A = a + V affine support | `hμ : MemLp id 2 μ`, `affineSupport μ`, its `direction` | Aligned |
| Cov_{μ,V} is the covariance operator of the intrinsic law on V | `Covariance.operator (intrinsicMeasure μ)` | Aligned |
| Cov_μ annihilates V^⊥ | `operator_apply_eq_zero_of_mem_orthogonal` | Aligned |
| Cov_μ restricted to V is Cov_{μ,V} | `operator_coe_intrinsic`, alternatively with a bilinear form version | Aligned |
| Operator norms are equal | `opNorm_operator_intrinsic` | Aligned |
| Cov_{μ,V} is positive definite on V | `intrinsic_operator_inner_self_pos`: for each nonzero v, ⟪Σv, v⟫ > 0 | Aligned |
| In zero dimension, both operators and both norms are zero | `operator_eq_zero_of_direction_eq_bot` plus certificate that the intrinsic operator is zero; norm zero is a consequence | Aligned |

No weakening of Lean statements relative to Blueprint was found. The norm uses the operator norm `ContinuousLinearMap`, identical to Blueprint's ‖·‖_op; the maximum eigenvalue expression is not involved.

## Proof path

- Barycenter in A: `Convex.integral_mem`, A is closed and convex, μ a.e. falls in A. Annihilation: the integrand function
  ⟪w, z − m⟫⟪y, z − m⟫ on a.e. z is zero, since z − m ∈ V and w ∈ V^⊥.
- Intrinsic coordinates: for x ∈ A, `intrinsicMap x = ⟨x − a⟩ = P (x − a)` (`starProjection_eq_self_iff`).
  Thus ν is μ translated by `x ↦ −a + x` then pushed forward by P; `covarianceBilin_map_const_add` eliminates the translation,
  `covarianceBilin_map` and `adjoint_orthogonalProjectionOnto` replace the adjoint of P with the inclusion map.
- Operator restriction and norm: y = P y + (y − P y), the second term is nullified; the norm is used in two directions
  via `opNorm_le_bound`, `le_opNorm`, and `norm_orthogonalProjectionOnto_apply_le`.
- Positive definite: `covarianceBilin_self` reduces to variance; if the variance is zero then `evariance_eq_zero_iff` gives ⟪v,·⟫ a.e. constant;
  this constant hyperplane serves as a `AffineSubspace.mk'` closed set carrying ν, and `affineSupport_le_of_ae_mem` and
  `affineSupport_intrinsicMeasure = ⊤` force (span{v})^⊥ = ⊤, hence v = 0.
- Zero-dimensional: ⊥^⊥ = ⊤, reduces to nullification.

## Metadata and Evidence

ledger adds `proved / lean` node (thirteen proved); `check_blueprint.CERTIFICATES` adds mapping;
Blueprint lemma block anchors six statements and certificates, statements and proofs marked `leanok`, proof text updated to actual argument;
tasks.json the node infrastructure is changed to `available` and source code and Mathlib file hashes are recorded; HANDOFF, README, `verification.md`, `solutions/README.md`, `formalization/README.md` are synchronized. golden,
`STATEMENT_CHECKS`, route configuration unchanged.

`lake build` passed; certification guarded by nine library-level statements with standard axioms. Final verification receipt is generated by `python3 research/verify.py`
after this record, source code SHA is recorded within the receipt itself. Local kernel replay trusts third-party compiled imports; no isolated rebuild, remote CI, or release.
