# Frontend style review (2026-11-02)

Scope: the KLS density frontend in [`integrations/openai/KLSOpenAI`](../../integrations/openai/KLSOpenAI)
and its copies in the [Palomar challenge](../../integrations/palomar/Challenge.lean) and the
[Formal Conjectures correspondence client](../../integrations/palomar/formal-conjectures/StatementCorrespondence.lean.in).
The owner is the KLSOpenAI integration boundary for the density formulation of
Bizeul–Klartag–Lehec, arXiv:2610.05474v1, Theorem 1.1. No statement, constant, quantifier,
dimension, public name, binder or proof status changes. The OpenAI model, its `UPSTREAM.json`,
`formalization/` and the Formal Conjectures file are unchanged. This review is agent-assisted;
it is not personal expert review.

## Findings and corrections

| Finding | Location | Correction |
| --- | --- | --- |
| The definition named a generated auxiliary proof (`OAI.LeanBlast.KLS.dirichletEnergy._proof_1`) and disabled `linter.auxLemma`. | `LocallyLipschitzBound` | The new theorem `completeSpace_space` supplies the `CompleteSpace` argument through `letI`; the formula keeps the ordinary `gradient f x`. |
| `of_conjecture` and `locallyLipschitz_of_conjecture` repeated the same covariance-to-smooth step. | `Bridge.lean`, `LocallyLipschitz.lean` | Both now use `smoothTest_holds_of_localSlope_le_covariance`. Each endpoint still moves to `C + 1` itself. |
| `n` and `ρ` were rebound in every density lemma header. | `Bridge.lean` | One `variable {n : ℕ} {ρ : Space n → ℝ}`. |
| The proof facts had short names, and the private helper had no docstring. | `locallyLipschitz_of_conjecture`, `locallyLipschitz_of_smooth` | The proof now reads smooth bound (`hsmooth`) → locally Lipschitz bound (`hlocal`) → variance identification (`hvariance`). The helper has a docstring. |
| The Palomar Lake comment counted one deliberate `sorry`. | `integrations/palomar/lakefile.toml` | The comment now counts two (comment only). |

Why the carrier theorem is needed: Lean moves a compound proof argument inside a definition
body into a generated auxiliary theorem. Such proofs are reused within a module by type. In the
challenge, the definition follows the inlined OpenAI block, so its `CompleteSpace` proof reused
`dirichletEnergy._proof_1`; the separately compiled solution module generated a differently named
proof, and Comparator rejected the definition. An application `completeSpace_space n` has only an
atomic argument and is not abstracted, so both modules elaborate to the same term. It is a
theorem, not an instance, so it adds nothing to typeclass search.

A remaining generated proof, `LocallyLipschitzBound._proof_1 : Nat.AtLeastTwo (1 + 1)`, comes
from the numeral `2 : ℝ≥0∞` in `MemLp f 2 μ`. Source never names it, and both modules derive
the same name from the declaration.

## Public additions

| Declaration | Reason | Consumers |
| --- | --- | --- |
| [`KLSOpenAI.completeSpace_space`](../../integrations/openai/KLSOpenAI/LocallyLipschitz.lean#L35) `(n : ℕ) : CompleteSpace (Space n)` | Gives the `CompleteSpace` argument a stable, nameable term, as explained above | `LocallyLipschitzBound` in the solution, the Palomar challenge and the correspondence client |
| [`KLSOpenAI.smoothTest_holds_of_localSlope_le_covariance`](../../integrations/openai/KLSOpenAI/Bridge.lean#L137) | Shared conversion: at an OpenAI isotropic log-concave density, `C_P^lit ≤ C ‖Cov‖` gives the smooth-test bound with constant `C`, in every dimension including zero | `of_conjecture` (same module); `locallyLipschitz_of_conjecture` (another module, hence public) |

Neither declaration is an alias of an old name, and no declaration was removed or renamed.

## Variables and placement

`Bridge.lean` owns the shared density/isotropy conversion. Its section variables are only the
carrier dimension and density, which appear in every density lemma. Premises stay in headers,
with no `include` and no linter suppression.

`LocallyLipschitz.lean` keeps self-contained headers. Its definitions are copied byte for byte
into the Lean v4.35.0 challenge and the Lean v4.33.1 correspondence client, and identical text
keeps that copy reviewable. Its private helper takes a `ProbabilityMeasure`, unlike the
definition's `Measure`, so a shared `μ` variable would not apply. Closed endpoints stay in
`Target.lean`. Conditional modules still do not import the closed KLS proof, and no module was
added, moved or split.

## Interface and evidence checks

- Pre-existing declarations keep their exact elaborated types: every public and private
  `KLSOpenAI` declaration, compared in serialized `pp.all` form, including binder names,
  implicitness and order.
- The only changed definition body is the `CompleteSpace` argument of `LocallyLipschitzBound`.
- Clients built in this round:
  - a natural-gradient statement proved by `Iff.rfl`;
  - direct use of the existing public declarations with named arguments;
  - a zero-dimensional call of the shared conversion.
- Copied blocks are byte-identical between the challenge and the correspondence client.
- The Formal Conjectures patch is unchanged.
- Strict package builds, boundary and all-declaration axiom audits, the development Comparator
  for both endpoints and the same-pin correspondence ran on the edited source. Their receipts
  under ignored `build/` bind those snapshots only.
- The official full preflight at `ed8da44` is historical. It does not cover this source.
