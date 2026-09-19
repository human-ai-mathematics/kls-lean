import FunctionalInequalities.KLS.Statement

/-!
# The KLS conjecture as an open target

This module states the KLS conjecture as a **theorem with an explicit `sorry`**. It is the one
deliberate hole of the library, and it exists so that the final goal of the repository is visible
in Lean itself, not only in the Blueprint: `#print axioms FunctionalInequalities.KLS.kls` reports
`sorryAx`, by design, until a proof is found.

`KLS.Conjecture` (`KLS/Statement.lean`) is a `def … : Prop`: it *names* the sentence and asserts
nothing. The reductions proved elsewhere, such as `KLS.conjecture_of_affineBound`, conclude that
proposition and are unconditional theorems; they hold whether or not KLS is true. This file is the
place where those reductions would be assembled into a proof.

Rule recorded in `research/decisions/2026-09-19-kls-target-theorem.md`: an unproved **claim** is
written as a `theorem` with `sorry`, never left implicit in a `def : Prop`; a `def : Prop` is
only a name for a sentence, used by results that have it as hypothesis or conclusion.

## Gate constraints, and why this file is a leaf

* `research/check_ledger.py` forbids `sorry` in the import closure of every certificate, so no
  certificate and no library module may import this file. It is imported only by the aggregate
  root `FunctionalInequalities.lean`.
* `research/verify.py` audits the axioms of every declaration named in a Blueprint `\lean{…}`
  tag and rejects `sorryAx`, so `conj:kls` keeps `\lean{FunctionalInequalities.KLS.Conjecture}`
  and refers to `kls` in prose only.
* The direct-hole count of the library is therefore **1**, this declaration, and audits must
  treat that as the baseline rather than as a regression.
-/

namespace FunctionalInequalities.KLS

/-- **The KLS conjecture**, covariance-normalized literature form (Blueprint `conj:kls`): there is
a universal `C < ∞` such that every log-concave probability law with finite second moment on every
finite-dimensional Euclidean space satisfies `C_P^lit(μ) ≤ C ‖Cov_μ‖_op`.

**Open.** The `sorry` is the intentional target hole of the repository; see the module docstring.
`KLS.conjecture_of_affineBound` reduces it to the isotropic bound `KLS.AffineBound K` for some
finite `K`, which is where a proof would enter. -/
theorem kls : Conjecture := by
  sorry

end FunctionalInequalities.KLS
