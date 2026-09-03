# Poincaré tensorization statement freeze

**Approval date:** 2026-09-03 (Asia/Shanghai).

**Human reviewer/approver:** the repository user in Codex task
`01a065af-7638-70e0-98d1-dc77718ee3e9`, whose instruction was “同步验收” following
the report of the completed proof, semantic review, compilation, and dependency audit.
The authenticated repository account for this acceptance is `lyw-ops`.
**Recorder and technical reviewer:** Codex, with independent geometry/admissibility and
variance/tensorization reviews.

**Repository baseline:** `faf782f97eabefbd3d3f2aed50d2907d07ac7a46` on `main`.
The tensorization implementation was present as uncommitted working-tree changes at this
baseline. This record freezes the current reviewed declarations and ledger claim below;
it does not claim that the baseline commit already contains the tensorization proofs.

## Approval and chronology

The user supplied the completed candidate proofs and requested their review. After that
review passed, the user instructed Codex to synchronize acceptance. This is the human
ratification of the current candidate at acceptance time. No earlier freeze is asserted or
backdated. The existing statement-phase decisions and exploration remain historical records.
The `drafted → frozen → proved` state transition is documented here and in
[the acceptance record](../explorations/2026-09-03-tensorization-acceptance.md); the final
ledger records `proved` only after the completed proof and certificate checks pass.

The scope of approval is the two-factor upper bound on the existing globally smooth,
L², finite-gradient-energy test class. It includes arbitrary Borel probability measures
on the stated Hilbert spaces, zero-dimensional factors and extended optimal constants.
It adds no moment, density, positive-dimension, finite-constant or attainment assumption.
The definitions in `Basic.lean` and the existing linear-test/covariance API are unchanged.

## Complete public declaration types

The following is the exact output of `#check @...` under the
pinned Lean/Mathlib v4.33.0. Implicit parameters and typeclass arguments are exposed.
SHA-256 of this UTF-8 output, including its final newline: `75e576722a02a1c49588534389331ed1f493fec233ee21756e348c23f8424d0a`.

```text
@FunctionalInequalities.Poincare.Holds.prod : ∀ {E : Type u_1} {F : Type u_2} [inst : NormedAddCommGroup E]
  [inst_1 : InnerProductSpace ℝ E] [inst_2 : CompleteSpace E] [inst_3 : MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] [inst_6 : NormedAddCommGroup F] [inst_7 : InnerProductSpace ℝ F]
  [inst_8 : CompleteSpace F] [inst_9 : MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
  {μ : MeasureTheory.Measure E} {ν : MeasureTheory.Measure F} {C C' : ℝ},
  FunctionalInequalities.Poincare.Holds μ C →
    FunctionalInequalities.Poincare.Holds ν C' →
      FunctionalInequalities.Poincare.Holds (FunctionalInequalities.Poincare.prodMeasure μ ν) (max C C')
@FunctionalInequalities.Poincare.constant_prod_le : ∀ {E : Type u_1} {F : Type u_2} [inst : NormedAddCommGroup E]
  [inst_1 : InnerProductSpace ℝ E] [inst_2 : CompleteSpace E] [inst_3 : MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] [inst_6 : NormedAddCommGroup F] [inst_7 : InnerProductSpace ℝ F]
  [inst_8 : CompleteSpace F] [inst_9 : MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
  {μ : MeasureTheory.Measure E} {ν : MeasureTheory.Measure F} [MeasureTheory.IsProbabilityMeasure μ]
  [MeasureTheory.IsProbabilityMeasure ν],
  FunctionalInequalities.Poincare.constant (FunctionalInequalities.Poincare.prodMeasure μ ν) ≤
    max (FunctionalInequalities.Poincare.constant μ) (FunctionalInequalities.Poincare.constant ν)
```

Reproduce the type snapshot from `formalization/`:

```bash
cat > /tmp/kls-tensorization-signatures.lean <<'LEAN'
import FunctionalInequalities.Tensorization
#check @FunctionalInequalities.Poincare.Holds.prod
#check @FunctionalInequalities.Poincare.constant_prod_le
LEAN
lake env lean /tmp/kls-tensorization-signatures.lean
```

## Complete approved ledger statement

The `statement` field is frozen verbatim. Its SHA-256, encoded as UTF-8 without an
extra newline, is `a261a6b244ad4e7ea36dd0478f268e8f2d9fad6b5cd99e22317f36bd99075234`. Lifecycle and source metadata are not part
of this mathematical statement snapshot.

```json
{
  "id": "lem:poincare-tensorization",
  "statement": "Let E and F be real separable Hilbert spaces (complete real inner product spaces with second-countable norm topologies), each equipped with its Borel sigma algebra. For measures mu on E and nu on F, define rho = (mu.prod nu).map (WithLp.toLp 2), a measure on the Hilbert product WithLp 2 (E x F). For all real C and C', Poincare.Holds mu C and Poincare.Holds nu C' imply Poincare.Holds rho (max C C'). Holds includes probability normalization, nonnegativity of its constant, and Var(f) <= C integral ||gradient f||^2 for every globally smooth real-valued L2 test with integrable squared canonical gradient. Moreover, for every pair of Borel probability measures mu and nu, Poincare.constant rho <= max (Poincare.constant mu) (Poincare.constant nu) in ENNReal, including infinite optimal constants. No second-moment, density, positive-dimension, or finite-optimal-constant assumption is imposed."
}
```

## Preservation rule

Compare the delivered declaration-type output byte for byte against the text block above,
and compare the ledger statement string against the JSON block. Record the outcome with
the published commit in the Issue #6 acceptance evidence. Later changes to either contract
require a new exploration entry and human resolution; compilation alone does not approve them.
