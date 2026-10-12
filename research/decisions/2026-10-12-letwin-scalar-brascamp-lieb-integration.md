# Letwin Lemma A.6 for a given potential: scalar Brascamp–Lieb

Date: 2026-10-12. Controller: Codex thread `01a12de4-2412-7082-ae33-15b1c3502420` (continuing the owner-authorized Goal).
Integrator: the sole reviewed Claude conversation, sequenced writer window AD (after AC).

## Integration

Input: strong-API candidate `api-scalar-bl-extended-gaussian-v5/candidate.lean` (gpt-6-astra, high; SHA-256 `394a24b1…`;
19 constants). Strict compile, complete type/universe/axiom audit, kernel replay and independent semantic review passed.
Its scratch imports are byte copies of the adopted AB and AA candidates; canonical code uses the adopted owners
(`Analysis/BakryEmery/Curvature.lean`, `KLS/LogConcave/HeatSemigroup/Range.lean`).

**Placement:**
- **`Analysis/BakryEmery/InverseHessianEnergy.lean` (new, above `MongeAmpere.lean`).** Young's inequality for the
  Hessian operator and its ring inverse, the gradient/derivative pairing, and the coordinate form, continuity and
  nonnegativity of the energy `⟪∇f, H⁻¹∇f⟫`.
- **`KLS/LogConcave/BrascampLieb.lean` (new).**
  - **Main results.** `scalar_brascamp_lieb_finite_energy` (finite-C² scope: `U ∈ C²`, integrable energy) and
    `scalar_brascamp_lieb_extended_energy` (extended-smooth scope: `U ∈ C^∞`, right side in `[0, ∞]`, no energy
    premise), with the bounded-test form.
  - **Supporting steps.** The compact-test steps `compact_pairing_identity`, `compact_diffusion_toLp_mean_zero` and
    `compact_variational_estimate`.
  - **Private helpers.** Three one-use helpers (Hilbert closure, `L²` pairing) are private here; they are public in the
    prototype. This is an API classification choice, not a rename.
- **Audit `research/audits/BKL/LetwinScalarBrascampLiebAudit.lean`.** The standard Gaussian law on `ℝ` with `f = id`
  attains equality.

**Text changes.** All declaration blocks are verbatim with their section variable blocks. Only the open lines change
(scratch namespaces replaced by the canonical range namespace), plus the `private` keyword.

**Comparison.** Pure compiled, all 19 constants. Kinds, ordered universes, types and values are equal after replacing
only the module component of hygiene labels, under the explicit map (`EXTRA_MAP` for the five referenced support
constants).
- **Range constants.** The referenced range constants are equal to their canonical owners.
- **Coercivity.** The referenced coercivity theorem has the same type. Its proof value differs only in the
  `IsOrderedModule ℝ ℝ` instance proof already recorded in the AB integration.

**Evidence:** `build/reviews/2026-10-12-bkl-letwin-t25-continuation/claude-ad-scalar-bl-integration-v1/`.

**Not provided:** the potential is given. The source moment map (existence, Euler–Lagrange identification, push-forward,
regularity), Lemma A.6 for the source law, the trace bound of Theorem 2.5, Letwin Theorems 2.5 and 1.2, BKL and KLS remain
open. Letwin LA6 is partial; no paper coverage or certificate count changes.
