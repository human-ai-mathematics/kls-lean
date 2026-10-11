# BKL/Letwin Stage 1 integration (2026-10-10)

Stage 1 of the [staged goals](../handoffs/2026-10-10-bkl-staged-goals.md): the grouping of Bizeul–Klartag–Lehec
arXiv:2610.05474v1 (74) with (72), and the covariance step of the proof of Letwin arXiv:2607.24164v1 Theorem 1.2. All
three proofs were constructed by Astra API requests and independently accepted by Codex; the isolated combined candidate
`build/reviews/2026-10-10-bkl-staged-orchestration/claude-stage1-combined/` (maps, checks, patch) was root-reviewed
before adoption. Deterministic supports only: no stochastic statement, certificate or paper coverage.

## Source locators (pinned versions; Codex source review with page images)

- BKL pp. 20–21: (74) is the deterministic raw spatial expansion of `∇^m⟨v_t, A_t⁻¹ v_t⟩(0)`; its `2m` singleton
  allocations and complementary pairs give `2m κ_m + 2 L_m`, where (72) defines `L_m` (sum over `J ∋ 1`,
  `2 ≤ |J| ≤ m − 2`). (73) (Lemma 4.3) is stochastic and remains open.
- Letwin p. 14: `Cov_{Z∼η}(Z) = |M|` with `Z = |M|^{1/2} X` is the UNNUMBERED display of the proof of Theorem 1.2
  immediately before (2.21); (2.21) on p. 15 is the Stein-kernel Hilbert–Schmidt trace identity (not formalized).
  Earlier working records that called the covariance identity "(2.21)" keep their wording; current prose uses this
  locator.

## Placement (owner, scope, destination, imports, decision, API impact, validation)

| Result | Owner and placement | Imports | API impact |
| --- | --- | --- | --- |
| `selected_mask_partition` (four ordered-mask facts) | `Analysis/IteratedDerivative/Bilinear.lean` (owner of `selected`), generic `Type*`; extend, same namespace closed and reopened after all old declarations (a section/universe-scope placement adjustment, not a migration) | unchanged | one new theorem |
| `iteratedFDeriv_inner_centeredGradient_zero_grouped_of_compact` | `Analysis/BakryEmery/CumulantLeibniz.lean` (owner of the raw expansion); extend inside the existing namespace and identical variable scope; binder `mu` preserved | unchanged | one new theorem |
| `Isotropic.covarianceBilin_map_sqrt_abs_matrix` | `KLS/Isotropic.lean` (owner of `Isotropic`); extend | `Analysis.Matrix.Sign` | one new theorem |
| `symmetric_matrix_sqrt_real_cfc_bridge`, `symmetric_matrix_sign_factorization` | new `Analysis/Matrix/Sign.lean` with exactly their accepted imports (extending `Positivity` changed a value) | Mathlib only | new module |
| Matrix family | `Analysis/Matrix{Trace,Positivity,DeterminantDerivative}.lean` → `Analysis/Matrix/` byte-identically ([decision](2026-10-10-analysis-matrix-family.md), [map](../api-migration/2026-10-10-analysis-matrix-family-map.json)) | consumers re-pointed | module paths only; no alias or wrapper |

Validation (candidate): 71/71 strict compilations (43 modules, 28 audits), 814 axiom reports, all standard; exact frozen types/universes, accepted proof values, old interfaces, axiom closure and fresh kernel replay as recorded in the candidate (`CHECKS.json`, `INTERFACE.json`).

## Status levels

Exact completed local interfaces are `\leanok` Blueprint nodes (`lem:bkl-grouped-drift-expansion`,
`lem:letwin-mapped-covariance`, the partition in `lem:iterated-derivative-symmetry-leibniz`). In `literature.json`,
BKL E7274 ((72), (74)) and Letwin CZ14 (p. 14 covariance step) are `stronger` (⇑: any representative slot; every
symmetric matrix, singular, indefinite and dimension zero). BKL L43 (Lemma 4.3) and Letwin T12 (Theorem 1.2) are
`partial`, naming the missing stochastic and Stein pieces; BKL Theorems 4.1 and 1.1, Letwin Theorem 1.2 and `KLS.kls`
remain open.

## Superseded handoff wording (verbatim)

Each block below is replaced in the named current file; claims are unchanged here.

`HANDOFF.md`:

```text
earlier versions are preserved in the
[2026-10-08 handoff history]
```

`HANDOFF.md`:

```text
It covers everything above, including the adopted CEK Proposition 12 batch
  (below). Post-receipt changes are documentation only: this handoff file, the receipt history and the 2026-10-10
  handoff history (verified Lean snapshot ≠ final whole tree).
```

`HANDOFF.md`:

```text
## Uncommitted (2026-10-07–09, continuous BKL goal)
```

`HANDOFF.md`:

```text
(placement and metadata).

- **CEK Proposition 12 (adopted 2026-10-10):**
```

`HANDOFF.md`:

```text
the supports of the grouping. The grouping
  (72)–(73) for `M = A⁻¹` itself and the stochastic (71)/(73) are not formalized.
```

`HANDOFF.md`:

```text
(BKL2026 P71 `same`, T11/T41/L42/E67 partial; Letwin2026 L23/LA3/T25/D26/L27/L29/LA7/E23 partial)
```

`HANDOFF.md`:

```text
Stage 1 is active in the current controller chat and covers the BKL (72)--(74) grouping and
Letwin (2.21) mapped covariance, with independent acceptance and reviewed integration.
```

`HANDOFF.md`:

```text
1. **Owner decision:** commit the uncommitted work (and optionally dispatch remote Lean certification
   or push a `milestone/**` tag for the new certificate).
2. **Current focus: BKL Theorem 1.1.**
```

`HANDOFF.md`:

```text
   the latest full receipt named under "State"; owner publication decisions (commit, push, remote certification)
   are separate and listed first above.
3. New BKL modules go
```

`HANDOFF.md`:

```text
   are kept.

## Open owner decisions
```

`research/handoffs/2026-10-10-bkl-staged-goals.md`:

```text
Letwin (2.21) mapped covariance -> Theorem 1.2 -> BKL Lemma 4.2
```

`research/handoffs/2026-10-10-bkl-primary-scope.md`:

```text
The mapped-covariance interface has an explicit chain through Letwin (2.21) to Theorem 1.2
```

`research/handoffs/2026-10-10-bkl-staged-goals.md`:

```text
The original full grouped formula is now assigned to the sealed Astra-high
  `api-grouped-cumulant-v5` typed-feedback packet, with the accepted partition proof as a verbatim immutable
  prefix. Its full type/universes equal the original target.
```

`research/handoffs/2026-10-10-bkl-staged-goals.md`:

```text
Canonical adoption of
  the partition and the complete grouped proof remains pending.
```

`research/handoffs/2026-10-10-bkl-staged-goals.md`:

```text
Their placement is reviewed, but their covariance placeholder is not a proof and the patch
  has not been adopted.
```

`research/handoffs/2026-10-10-bkl-staged-goals.md`:

```text
Claude is checking its
  hole-free canonical candidate and clients under `claude-covariance-accepted-v5/`, including
```

`research/handoffs/2026-10-10-bkl-staged-goals.md`:

```text
This is not production adoption, a full
  project receipt, or paper coverage.
```
