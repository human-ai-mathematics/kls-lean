# CEK maximiser for a bounded source: a normalized Lipschitz primal

Date: 2026-10-12. Controller: Codex thread `01a12de4-2412-7082-ae33-15b1c3502420` (continuing the owner-authorized Goal).
Integrator: the sole reviewed Claude conversation, sequenced writer window AC (after AB).

## Integration

Inputs (strong-API candidates, gpt-6-astra, high; strict compile, complete type/universe/axiom audit, kernel replay and
independent semantic review passed):

| Candidate | SHA-256 | Constants |
| --- | --- | --- |
| `api-bounded-primal-geometry-v11` | `d77ddfc1…` | 22 |
| `api-bounded-primal-uniform-client-v1` | `da4b503c…` | 13 |

**Placement by dependency level.** All blocks are verbatim; the only declaration rename is `cap ↦ closedBallCap`
(`cap_lowerSemicontinuous ↦ closedBallCap_lowerSemicontinuous`).
- **Geometry: new `Analysis/Convex/BoundedConjugate.lean`.** It holds the cap, its lower semicontinuity, the real
  minimum, finiteness and the bound of the conjugate, and the convexity, Lipschitz property and Fenchel inequality of its
  real representative. It has no probability or CEK import.
- **Normalization: `real_legendre_normalization` in `Probability/MomentMeasure/ConjugateMass.lean`.** Conjugate mass one
  gives real `exp(−ψ)` integrability, integral `1` and a probability measure.
- **Producers: new `KLS/CEK/BoundedPrimal.lean`.** `bounded_source_cap_lsc`, `bounded_source_cap`,
  `bounded_source_finite_conjugate`, `bounded_source_lipschitz_primal` and `bounded_source_real_density_client`, for
  an isotropic probability law `μ` with `‖y‖ ≤ L` μ-a.e., in every finite dimension.
- **Client: `research/audits/BKL/LetwinBoundedPrimalAudit.lean`.** The fixed uniform law on `[-√3, √3]`. The five
  needed witness blocks of `SingletonAllocationAudit.lean` are reproduced verbatim under `LetwinBoundedPrimalWitness`.

**Comparison** (pure compiled, every constant).
- **Geometry (22).** Equal in kind, ordered universes, type and value after replacing the module component of hygiene
  labels. The renamed cap declarations also need the exact hygiene-context map `h(cap) ↦ h(closedBallCap)`.
- **Client (13).** Equal under the explicit map; 12 are RAW-equal. The candidate's `L._proof_1` (a numeral instance
  proof) is canonically the witness's `unifSym._proof_1`: Lean reuses an identical auxiliary proof already generated in
  the same module.
- **Witness blocks.** RAW-equal to the accepted copy.

**Evidence:** `build/reviews/2026-10-12-bkl-letwin-t25-continuation/claude-ac-bounded-primal-integration-v1/`.

**Not formalized:** this is a weak normalized convex Lipschitz primal linked to the source law. The Euler–Lagrange
identification, the gradient push-forward `(∇ψ)_# e^{−ψ} = μ`, source smoothness, a positive definite Hessian, the
gradient diffeomorphism and the Monge–Ampère equation remain open, as do CEK Theorem 2, Letwin Theorems 2.5 and 1.2, BKL
and KLS. No lemma-map relation, paper coverage or certificate count changes.
