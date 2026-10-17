# Classical KLS specification: persisted sources and gate

Date: 2026-10-17. This record makes the second independent review's Mathlib-only specification part of the reviewed tree
([gate guide](../audits/KLS/Classical/README.md)). It follows the article-standard audit finding that the strongest
classical clients lived only in ignored local evidence.

## Source and statements

**Source.** Bizeul–Klartag–Lehec, arXiv:2610.05474v1 (PDF SHA-256
`86824722318f2213daf5ae624391b41f76bb4d41118b1657db9ab00d2d1bb0db`):
- pp. 1–2: the convex-body Poincaré formulation (3) and the equivalence of formulations;
- p. 2: the locally Lipschitz constant (5), Theorem 1.1 and the covariance normalization (6).

**Formulations.** The specification (SHA-256 `f52663e2398d7eb45433dbad4edd808ae02a03fb8167467f937a9e12205a8d0f`) imports
Mathlib only. It states three formulations, each with one positive constant chosen before every dimension, law and test
function:
- **`CovarianceNormalizedSmoothKls`.**
  - Log-concavity is the compact-set Borell inequality.
  - Smooth `L²` tests with integrable squared gradient.
  - Mathlib's covariance Riesz operator norm.
  - No moment, compactness, regularity, isotropy or invertibility premise.
- **`IsotropicLocallyLipschitzKls`.**
  - Raw mean-zero and identity second-moment equations.
  - Every locally Lipschitz `L²` function.
  - Extended variance and energy, so the gradient energy may be infinite.
- **`UniformConvexBodyKls`.** The normalized Lebesgue law of every compact convex body of positive volume, with the density
  written literally, under the same raw isotropy equations (mean zero and identity second moments), and the same locally
  Lipschitz inequality.

## Client

The client (SHA-256 `d7e762f9ddd616d37a98d5e80f8fea40b5972507b76989dad8b4a12055b8f864`) proves all three from the library:
- the definition bridge `RawLogConcave ↔ KLS.LogConcave` holds by `Iff.rfl`;
- isotropy comes from the raw moments;
- finite second moments come from log-concavity rather than being supplied;
- `KLS.kls` gives the covariance form, including singular laws, with no inverse covariance;
- `theorem11` gives the locally Lipschitz form, and the infinite-energy case uses the positive constant;
- the uniform law is proved log-concave.

The four printed axiom reports use only `propext`, `Classical.choice` and `Quot.sound`.

## Review evidence (ignored local records, unchanged)

`build/reviews/2026-10-17-kls-second-independent-review/`:

| Record | SHA-256 | Content |
| --- | --- | --- |
| `REVIEW.json` | `739c5341570990ccb57880885ee5bc01ad8f6c5e264aeefe541db8404cfc64aa` | Full verification `43cdae73364dc2b76507f9952883a6a9abe9c2cad8014c3e66a61a2a105b8831` of snapshot `e94fd052ade8e51dc84d5a231afe24505fb1dc638ee6c49d071855f789dc0d01` |
| `SEMANTIC-REVIEW.json` | `1674dad332443c93b7435a4921d3591b8075302c738f2262df4bba360521fe09` | Definition review: log-concavity, Poincaré constant, energy, covariance, quantifiers, singular support, totalized integrals |
| `PROOF-CLOSURE.json` | `40652124ad036d46c43566dd2add615211180c82e6bdaa2c748165027b8560ba` | 88360 transitive constants, standard axioms, no `unsafe` or `partial` |
| `STRICT-RECOMPILE.json` | `d0a85a8ad979be4b621e75ca4438bf70f64fdcbca28e55c35cf3338411844a6b` | 7 fresh modules, replayed |

The article-standard audit recompiled both sources on the organization snapshot
(`build/reviews/2026-10-17-article-standard-audit/fresh-specs.json`, `5a4b19e5b29f2ce5468e05f260e74e01f958cbff15f0224ad7b2775d05db7612`).

These ignored records are history, not runtime inputs. The tracked templates are byte copies, and the gate compiles them
freshly on every run.

## Gate and trust boundary

**The `classical-kls` gate** of `research/verify.py`, in both modes:
- checks the pins and the import and token guards;
- compiles both templates strictly;
- requires the four standard-axiom reports;
- replays both runtime modules;
- requires three false-statement mutations of the specification to be rejected by their configured client elaboration
  errors. The kinds were calibrated from the first preserved Lean run:
  - dropped log-concavity gives `Application type mismatch`, together with an `introN` failure;
  - dropped gradient energy gives `Type mismatch`;
  - a strict inequality gives a `change` that is not definitionally equal to the target.

The pins change only with a reviewed source change; the driver never refreshes them.

**Trust boundary.** This is source compilation and client consumption with Lean, its local kernel replay and the pinned
compiled Mathlib imports. It is not an independent kernel, not a rebuild of Mathlib or every dependency, and not an
automatic certification of the English reading, which rests on the semantic review above.
