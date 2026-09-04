# One-dimensional Gaussian Poincaré statement freeze

**Approval date:** 2026-09-04 (Asia/Shanghai).

**Node:** `lem:poincare-gaussian-one-dimensional`.

**Human reviewer/approver:** the repository user in the current Codex task. Immediately before
approval, Codex reported that the Lean statements, proof chain, normalization, zero-variance
boundary and sharpness argument were semantically and mathematically correct, and separated
proof completion from the still-draft lifecycle metadata. The user then instructed:
“按照你说的那样去做优化和修正”. This ratifies the reviewed mathematical contract and asks
for its lifecycle closeout and the listed interface/documentation cleanups. It does not backdate
a freeze to the earlier statement or proof stages.

**Recorder:** Codex. The main Codex agent performs the production certificate and library-layout
changes; this record only freezes the reviewed contract and its permitted interface refinement.

**Repository baseline:** `10e4c707491830ebe9d07f7bfc5e65efeddc7e2e` on `main`, with the
Gaussian candidate and completed proofs present as uncommitted working-tree changes. No commit,
push, issue publication or remote CI result is asserted here.

## Approved mathematical contract

The approved claim is exactly ledger node `lem:poincare-gaussian-one-dimensional`, whose
`statement` text is unchanged from the candidate package. For every `m : ℝ` and `v : NNReal`,
with `v` interpreted as variance,

```lean
theorem holds_gaussianReal (m : ℝ) (v : NNReal) :
    Holds (ProbabilityTheory.gaussianReal m v) (v : ℝ)

theorem constant_gaussianReal (m : ℝ) (v : NNReal) :
    constant (ProbabilityTheory.gaussianReal m v) = (v : ENNReal)
```

The existing `Poincare.Admissible`, `energy`, `Holds` and `constant` definitions remain
unchanged: tests are globally smooth, Gaussian-L² and have integrable squared canonical
gradient; the fixed inequality is `Var(f) ≤ C ∫ ‖gradient f‖²`; the optimal constant is the
existing `ENNReal` infimum over finite `NNReal` valid constants. On `ℝ`, the canonical gradient
is the ordinary derivative.

There is no restriction on the mean and no positive-variance premise on either main theorem.
At `v = 0`, `gaussianReal m 0 = Measure.dirac m` and both the valid and optimal constants are
zero. For arbitrary `v`, the identity test has variance `v` and energy one, giving the matching
lower bound. No extra factor of two, standard-deviation interpretation, compact-support or
decay premise, extra derivative-integrability premise, or infimum-attainment assumption is
introduced. The result concerns the current smooth finite-energy domain; it does not identify
a completed Sobolev/closed-Dirichlet domain or assert a multivariate, logarithmic-Sobolev,
transport-entropy or full KLS theorem.

## Approved public surface and refinement

The candidate's 20 public mathematical declarations are approved. Their names, propositions
and source attributions are listed in
[`2026-09-04-gaussian-poincare-candidate.md`](2026-09-04-gaussian-poincare-candidate.md).
At approval time all 20 already had completed Lean proofs. Eighteen public types remain exactly
as reviewed. The two Gaussian first-moment tail identities are intentionally generalized by
removing unused endpoint-order hypotheses:

```lean
theorem integral_Ioi_centered_gaussianPDFReal (m : ℝ) {v : NNReal} (hv : v ≠ 0)
    (t : ℝ) :
    (∫ x in Set.Ioi t, (x - m) * gaussianPDFReal m v x) =
      (v : ℝ) * gaussianPDFReal m v t

theorem integral_Iio_centered_gaussianPDFReal (m : ℝ) {v : NNReal} (hv : v ≠ 0)
    (t : ℝ) :
    (∫ x in Set.Iio t, (m - x) * gaussianPDFReal m v x) =
      (v : ℝ) * gaussianPDFReal m v t
```

Both equalities are valid for every endpoint `t`; the right/left Tonelli applications still
obtain their respective order facts from their integration regions. This is a strict interface
generalization, not a weakening or change of the ledger claim. The final structural placement is
`Gaussian.Density` (7 declarations), `Gaussian.Hardy` (9 analytic upper-bound declarations), and
`Gaussian.Real` (4 valid/sharp-constant declarations). Exporting `Gaussian.Real` from the
aggregate and renaming the default Lake target are likewise structural changes and do not change
these 20 declaration types.

The exact final 20-type output and the sole production certificate are pinned by the separate
acceptance/proof-closeout record. The unchanged ledger statement has the candidate SHA-256
`07fa78f7a1a97217da6726a4f09fe043191413447e9a01715f850d9a38625574` (UTF-8, with no
added newline).

## Certification rule

The node is promoted to `proved` / `checked_by: lean` only after the main Codex agent adds the
single named `Solutions.LemPoincareGaussianOneDimensional.certificate` and the following gates
pass on the final layout:

1. the production ledger checker, including recursive local-import proof-escape scanning;
2. all ledger regression tests;
3. the default `lake build`;
4. explicit `#print axioms` checks of the certificate and all 20 public declarations.

The proof-closeout record supplies those results. Earlier candidate, design and statement-stage
validation files remain append-only historical records and continue to describe their original
`drafted` state.
