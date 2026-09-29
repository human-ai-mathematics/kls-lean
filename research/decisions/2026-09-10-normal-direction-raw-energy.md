# Normal-derivative raw-energy obstruction `obs:normal-direction-raw-energy`: statements, alignment, and proofs

Date: 2026-09-10 (Asia/Shanghai). Baseline: local `main` commit `5e5c704`, with uncommitted
Dirichlet-witness and one-dimensional `12·Var` work from the same day. The user chose to keep
pursuing coefficient 4 while waiting for a collaborator's KLS 1995 source, and meanwhile work
on an unrelated node. This is the lightest-infrastructure node in atlas `ready` unrelated to
the one-dimensional constant. The user instructed no commit or push.

## Node selection and review

`obs:normal-direction-raw-energy` (Blueprint chapter 30, "Core and coordinate comparisons")
is an obstruction node like `obs:dirac-raw-energy`: a named proved library result, without
ledger entry or certificate. Initial tasks.json status: `local_argument / unchecked`.
All required infrastructure exists: `Probability.affineSupport`, `supportPoint`,
`ae_mem_affineSupport`, `Energy.SmoothGradient.Test`/`preEnergy`,
`PreEnergy.RespectsAmbientFibers`, and Mathlib's `Submodule.orthogonal_eq_bot_iff` and
`toDual_gradient`. It moves `unchecked → available` and is proved in the same round.

## Statement design

New module [Energy/SmoothGradient/NormalDirection.lean](../../formalization/FunctionalInequalities/Energy/SmoothGradient/NormalDirection.lean),
namespace `FunctionalInequalities.Energy.SmoothGradient`:

| Declaration | Content |
| --- | --- |
| `normalCoordinate μ n x := ⟪n, x − supportPoint μ⟫` | Coordinate along `n`, based at the selected support point |
| `contDiff_normalCoordinate`, `hasFDerivAt_normalCoordinate`, `gradient_normalCoordinate` | Smoothness; gradient constantly `n` |
| `normalCoordinate_ae_eq_zero (hn : n ∈ directionᗮ)` | Zero μ-a.e. (a.e. points lie in affine support, with difference vectors in its direction space) |
| `smoothTest_energy_normalCoordinate` | `Poincare.SmoothTest.energy μ u = ‖n‖²` |
| `Test.normalCoordinate hn`, `Test.toL2_normalCoordinate`, `Test.energy_normalCoordinate` | Smooth-gradient test with L² class 0 and energy `‖n‖²` |
| `exists_unit_normal (h : direction ≠ ⊤)` | A proper direction space has a unit normal |
| `exists_test_toL2_eq_zero_energy_eq_one (h)` | Blueprint statement: a test with L² class 0 and both test/raw energies 1 |
| `not_respectsAmbientFibers (h)` | `¬ (preEnergy μ).RespectsAmbientFibers` |

**Claims:** all the declarations above for Borel probability laws on arbitrary finite-dimensional
real inner product spaces with proper affine-support direction space.
**Non-claims:** no intrinsic relaxed-energy property, no validity or failure of raw/core agreement
in intrinsic coordinates, no density claim. **Scope and dimension zero:** finite-dimensional;
no conclusion for `direction = ⊤` (full-dimensional support), nor should there be. In dimension
zero the direction space is ⊤, so the premise excludes it.

## Semantic alignment

| Blueprint clause | Lean | Assessment |
| --- | --- | --- |
| Proper affine support `A = a + V` | `(affineSupport μ).direction ≠ ⊤`, `a = supportPoint μ` | Aligned (proper affine subspace iff proper direction) |
| Unit `n ∈ V^⊥` | `n ∈ directionᗮ`, `‖n‖ = 1` from `exists_unit_normal` | Aligned |
| `u = 0` in `L²(μ)` | `(Test.normalCoordinate μ n hn).toL2 = 0` and a.e. zero | Aligned |
| `∫‖∇u‖² dμ = 1` | `Poincare.SmoothTest.energy μ u = 1` and `Test.energy = 1` | Aligned |
| "ambient raw energy depends on the extension away from A" | `not_respectsAmbientFibers` | Lean gives the stronger explicit failure of the `FormCore` predicate, as explained in the Blueprint block |

No weakening relative to Blueprint was found. `\uses` is unchanged.

## Metadata synchronization

No ledger entry or certificate for this obstruction; `check_blueprint.CERTIFICATES` is unchanged.
The Blueprint block anchors eight declarations and marks statement/proof `leanok`.
`Poincare/Foundation.lean` imports the new module (the root aggregate imports it via Foundation).
`solutions/FoundationAxiomAudit.lean` adds two axiom guards. The tasks.json node becomes
`available`, with module/dependency hashes. Synchronize HANDOFF, `formalization/README.md`,
`Energy/README.md`, `blueprint/README.md`, and `solutions/README.md`.

## Evidence boundary

Default `lake build` passes; both guards depend only on the three standard axioms. The final
receipt will be generated jointly by `python3 research/verify.py` after completing the next
node, `thm:smooth-gradient-raw-core-agreement-density`. No commit or push.
