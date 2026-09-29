# Strict review after Lean foundation cleanup

Date: 2026-09-06. The user requested a strict review. This record follows
`2026-09-05-lean-foundation-cleanup.md` without rewriting earlier records.

Conclusion: no proof error, strengthened assumption, deleted declaration, or additional axiom
dependency caused by the Lean refactoring was found. The review identified and corrected two
insufficiently explicit Blueprint definitions. The foundations can support subsequent KLS
statement work; this review does not promote unformalized constant comparisons, whitening,
or route conclusions to Lean proofs.

## Findings and corrections

### Finite test domain and infinite literature constant

`def:literature-poincare-constant` previously said “least C in [0, infinity]” and described
tests by a “finite right-hand side”. This did not distinguish finite energy from finiteness
after multiplication by the candidate constant, and did not adequately specify the case with
no valid finite constant.

This boundary matters: for `μ = (δ₋₁ + δ₁)/2`, take a globally Lipschitz function constant zero
near one atom and one near the other. Its variance is `1/4` and local-slope energy zero, so
no finite constant is valid. Treating infinity directly as a valid multiplier also encounters
Lean `ENNReal` multiplication `∞ * 0 = 0`.

The definition now first fixes locally Lipschitz `L²` tests of finite slope energy, defines
validity for finite `C ≥ 0`, then takes the infimum of valid finite constants, with empty
infimum infinity. Zero-energy tests are explicitly retained. The repeated formulation in
`thm:klartag-density-frontend-identification` is updated too. This agrees with the local
`TestFamily` optimizer and legacy constant, without assuming densities for general Borel measures.

### Joint measurability and exceptional conditional fibers

`def:conditional-fiber-form` previously only specified disintegration along each direction,
without a jointly measurable version for the outer directional integral. It now disintegrates
`T = ⟨x, θ⟩` by `(θ, P_{θ⊥} x)` under the joint law from `ρ ⊗ μ`. Standard Borel carriers
allow a jointly selected conditional kernel; for fixed `ρ`, uniqueness is needed only a.e.
under the joint base measure.

The definition assigns zero contribution to exceptional fibers, zero-variance fibers, and
fibers of infinite conditional second moment, noting that finite second moment makes the last
class null. The form value is independent of the conditional-kernel version and Borel
representative of the `L²` element. Test functions do not participate in selecting the kernel.

The local form remains defined for arbitrary Borel probability laws with finite second moment.
The factor-four theorem retains its full-dimensional log-concave scope with density; the
general-measure definition is not treated as a proof of every structural theorem.

## Lean baseline and internal declaration comparison

Starting HEAD remains `70ca1c19c4d207a31716c2e589c0b096521a5490`. Source saved before the previous
cleanup was used to create an independent temporary Lake package, sharing only pinned external
dependencies and rebuilding local modules and four certificates. The baseline build passed
with 3230 jobs; the current default build passed with 3234 jobs.

Import both library aggregates and four certificates separately and enumerate project-namespace
and private declarations. Compare `reprStr ci.type`, universe parameters, and internal
`ci.value?` expressions, without relying on a pretty-printer that hides implicit arguments or
notation. Proof bodies may change through refactoring; current-source checking and transitive
axiom audits verify them. Reducible definition bodies are compared directly.

| Item | Result |
| --- | --- |
| Existing declarations | 689: 665 public namespace declarations and 24 private declarations |
| Deleted declarations | 0 |
| Internal type changes | 0 |
| Universe parameter changes | 0 |
| Reducible definition bodies | 175, all identical |
| Added declarations | Only the two documented approximation lemmas; total 691 |
| Additional transitive axioms | 0; only `propext`, `Classical.choice`, `Quot.sound` |
| unsafe / partial declarations | 0 |

The comparator requires at least 650 nonempty records and unique names to prevent false passes
from empty parsing. This strict-review round made no further Lean-source changes.

Additionally, `lake env lean -DwarningAsError=true` was run file by file: all 49 library,
certificate, audit, and example files elaborated successfully, rather than merely reading
cached `lake build` success. These include 12 usage examples, eight foundation axiom guards,
and the Gaussian audit.

## Mathematical scope and source review

- Checked extracted lemmas, finite/infinite recovery branches, lower semicontinuity, and quadratic-closure consumers individually. Pseudometric assumptions, finite-energy conditions, and density needed for infinite-energy recovery are retained.
- The conditional-fiber direction is `D ≤ 4 * gradientEnergy`, so a form gap yields `C_P ≤ 4C`. One finite constant applies to all positive dimensions and eligible laws, followed by a test-independent frame chosen for each measure. Dimension zero uses zero variance; extension to proper affine support explicitly depends on the affine/isotropic bridge.
- Reread `modules/kls/45-conditional-fiber-frame.tex` and `solutions/conditional-fiber-frame-structure.tex` at upstream commit `8185e46ffb040e04fea076953e5bcaeb4157d71a`, checking the definition, maximal form domain, jointly measurable version, factor four, and exceptional-fiber conventions. Upstream agent review remains source provenance only.
- All `leanok` and `notready` markers are unchanged by node against the pre-cleanup snapshot. No ledger node was added, and Blueprint compilation is not treated as mathematical or Lean certification.

## Final verification

- Ledger: 4 nodes, 0 errors.
- Blueprint: 73 labels, 4 active routes, 0 errors.
- Python tests: all 63 passed.
- Blueprint PDF, web, and `checkdecls`: all succeeded.
- Final PDF: 27 pages; physical pages 5, 17, 24, 25 rerendered and inspected, without clipping, overlap, or unresolved references. No overfull boxes, undefined references/citations, or duplicate labels in the final log; 8 underfull notices remain.
- Compared all 130 pre-cleanup source files: 109 byte-identical, 21 containing the two rounds' documented changes, none deleted. The four certificates, ledger, version pins, historical records, and unrelated ` 2` copies are preserved.
- `git diff --check` passed. All work remains local and uncommitted; no push or remote CI.

Temporary baseline, internal declaration snapshots, per-file checks, and rendering evidence:

```text
/var/folders/6l/9qg2d8995s55q_4r1pfg83940000gn/T/kls-strict-review-20260906-0pxohkh8/
```

`raw-comparison.json` records internal comparisons, `strict-all-lean.json` per-file return
codes, and `sha256.json` evidence hashes. Type-snapshot SHA-256 values:

```text
before 528310b7388c53c97badb28ddfa33cff72fb6db2e1067f3361a54abfb1424ad2
after  7529da49f7077cd088b1842a6b291327862da074f3b1cac1a7294b651f06398e
```

This review did not complete the Lean statement of the main KLS proposition or its analytic
bridges, nor independently prove the entire upstream route. Identified literature debt remains,
including the original KLS reference for the one-dimensional log-concave factor four and the
precise source for Cheeger-frontend regularization.
