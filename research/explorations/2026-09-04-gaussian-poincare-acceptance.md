# One-dimensional Gaussian Poincaré: proof closeout and acceptance

**Date:** 2026-09-04 (Asia/Shanghai).

**Node:** `lem:poincare-gaussian-one-dimensional`.

**Baseline:** `10e4c707491830ebe9d07f7bfc5e65efeddc7e2e` on `main`, with the accepted
work present as uncommitted working-tree changes.

## Result and chronology

The node is accepted locally as **proved / checked_by: lean**. All 20 mathematical declarations
already had completed Lean proofs before the current approval. After Codex reported that their
semantics and mathematics were correct and identified the remaining lifecycle and structural
work, the user instructed “按照你说的那样去做优化和修正”. The accompanying
[statement freeze](../decisions/2026-09-04-gaussian-poincare-freeze.md) records that approval at
the current point in time; it does not reinterpret the earlier candidate and statement-stage
records as having been proved or frozen then.

The main Codex agent added the sole production certificate
`Solutions.LemPoincareGaussianOneDimensional.certificate`, performed the final module split,
generalized the two tail interfaces by removing unused order hypotheses, exported the accepted
result from the aggregate library, and placed both the certificate and its transitive axiom guard
in the default build. No `Poincare` semantic definition or ledger statement was changed.

No commit, push, GitHub Issue, clean-checkout run or remote CI result is claimed in this record.
Those are publication gates, not prerequisites for the accurate local `proved` ledger state.

## Accepted mathematical scope

For every real mean `m` and nonnegative variance `v : NNReal`, the current globally smooth,
Gaussian-L², finite-gradient-energy test class satisfies

```text
Var_{gaussianReal m v}(f) ≤ v · ∫ ‖gradient f‖² d(gaussianReal m v),
constant (gaussianReal m v) = (v : ENNReal).
```

The constant is the variance, not the standard deviation, and the energy normalization has no
extra factor. Positive variance uses the density/Hardy argument. Zero variance uses
`gaussianReal m 0 = Measure.dirac m`. The identity test has variance `v` and energy one and gives
the matching lower bound for every finite valid constant. The `ENNReal` infimum proof does not
assume attainment. The exact domain and all exclusions remain those in the unchanged ledger
statement and freeze record.

The mathematical dependency chain is:

```text
finite-interval FTC + Cauchy--Schwarz
  -> right/left Gaussian tail identities and Tonelli triangle identities
  -> two sharp half-line estimates
  -> anchored full-line estimate
  -> variance minimization and the valid constant v
  -> identity-test lower bound
  -> exact optimal constant v.
```

The two tail identities now quantify over every endpoint `t`; their former premises `m ≤ t` and
`t ≤ m` were unused by the identities themselves. The downstream right/left arguments retain
the needed order facts from membership in their integration regions. Removing those premises is
therefore a strict API generalization with no change to the proof constant or ledger conclusion.

## Final architecture and public surface

The 20 public declarations are separated by responsibility:

```text
Gaussian/Density.lean  (7)
  Mathlib density derivative, limits, first-moment tails, density-integrability bridge
             |
             v
Gaussian/Hardy.lean    (9)
  finite-interval estimate, variance minimization, integrability,
  Tonelli triangles, half-line and full-line upper bounds
             |
             v
Gaussian/Real.lean     (4) <--- Poincare/LinearTest.lean
  zero-variance case, valid constant, identity-test lower bound, sharp constant
             |
             v
solutions/LemPoincareGaussianOneDimensional.lean
  one named certificate, all 20 interface checks, and typed boundary examples
             |
             v
solutions/GaussianAxiomAudit.lean
  default-build #guard_msgs check of the certificate's exact transitive axiom set
```

`FunctionalInequalities.lean` now exports `Gaussian.Real`, so ordinary aggregate users receive
the two main theorems. The old default-target name `Issue2Solutions` is replaced by `Solutions`;
the latter contains all four node entry points and the Gaussian axiom-audit root. The ledger
protocol, checker and tests needed no exemption or schema change.

The certificate type is:

```lean
theorem Solutions.LemPoincareGaussianOneDimensional.certificate (m : ℝ) (v : NNReal) :
    Poincare.Holds (ProbabilityTheory.gaussianReal m v) (v : ℝ) ∧
      Poincare.constant (ProbabilityTheory.gaussianReal m v) = (v : ENNReal)
```

It directly pairs the two reusable library theorems and introduces no duplicate mathematical
proof. The solution entry point also retains the 20 public-interface checks, standard/translated
Gaussian examples, the Dirac boundary examples and the exact node proposition check.

## Local verification gates

All checks below were run after the final module split, certificate, aggregate export, target
rename, ledger promotion and build-time axiom guard were present.

| Check | Result |
| --- | --- |
| `python3 research/check_ledger.py` | Passed: `1 ledger(s), 4 nodes. 0 error(s).` The Gaussian node's complete local import closure passed the proved-node guard. |
| `python3 -m unittest discover -s research/tests -p 'test_*.py'` | Passed: all 24 tests. |
| `cd formalization && lake build` | Passed: 3132 jobs, with no warning or error. This includes the aggregate library, all four certificates and `solutions.GaussianAxiomAudit`. |
| Direct solution elaboration | Passed with all 20 interface checks, seven typed applications and the exact node proposition. |
| Proof-escape audit | No occurrence of `sorry`, `admit`, `native_decide`, `axiom` or `unsafe` in the Gaussian mathematical modules or certificate; the ledger check independently traversed the certificate's local imports. |
| Explicit axiom audit | The certificate and each of the 20 public declarations depend only on `propext`, `Classical.choice` and `Quot.sound`; no project axiom or `sorryAx` appears. |
| Build-time axiom guard | `solutions/GaussianAxiomAudit.lean` uses `#guard_msgs` to require the certificate's transitive set to be exactly `[propext, Classical.choice, Quot.sound]`; a change fails the default build. |
| `git diff --check` | Passed. |

The explicit 21-declaration axiom probe imported the production solution and ran `#print axioms`
for its certificate and every Gaussian declaration. Thus the build-time certificate guard and
the one-time complete public-surface audit cover distinct layers.

## Reproducible identifiers

Run the solution directly from `formalization/` with the pinned toolchain and hash its standard
output:

```bash
lake env lean ../solutions/LemPoincareGaussianOneDimensional.lean | shasum -a 256
```

The resulting SHA-256 is
`273dc9eaa000aae30e3ece7c04e7d100c3584b7ded43b1c3c62787279c61d186`. This output contains
the unique certificate type, all final 20 public types (including the generalized tail types),
the typed applications and the exact node proposition. The printer options are fixed in the
solution file.

Final source SHA-256 values are:

```text
Gaussian/Density.lean:                         badb5d9bfda56a8d533f2d8be3064c88384af761728e9f7f95a888966556ac23
Gaussian/Hardy.lean:                           ec96d4ddcde78763d7892087c0fd0975f656164342fe9a1f16bb9e25c46239ee
Gaussian/Real.lean:                            acedaa5005f81c762c671d297371d3b914352640f86e140fd97c9148094187df
LemPoincareGaussianOneDimensional.lean:         2837a718ef113e292137f6e526b8778759ddd80d8712afd28294d2c206801491
```

The ledger `statement` string remains byte-for-byte the candidate statement, with SHA-256
`07fa78f7a1a97217da6726a4f09fe043191413447e9a01715f850d9a38625574` when encoded as UTF-8
without an added newline. Only its lifecycle changes to `proved` / `lean`; all three earlier
proved node objects retain their mathematical statements and solution references.

## Historical preservation

The earlier candidate, design, route-review, issue-draft, signature and statement-validation
records remain unchanged as append-only history. In particular, their references to 20 proof
placeholders, `drafted / null`, the two older endpoint-order premises and a future certificate
accurately describe that earlier snapshot; they are not current-status documentation. This
acceptance record and the freeze record are the authoritative dated delta from that snapshot to
the accepted local state.
