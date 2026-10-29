import FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.InverseHessian.Cutoff
import FunctionalInequalities.Analysis.BakryEmery.UniformIntervalPotential
import FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.UniformIntervalClient

/-!
# Audit: Letwin Lemmas A.4 and A.5 for the uniform-interval source law

Source: Letwin, arXiv:2607.24164v1, Lemma A.4 (p. 17) and Lemma A.5 (p. 18). Axiom reports for
the source construction of the cutoffs (real parameter and natural index), Lemma A.5 for given
cutoffs, the source-class facts of the explicit moment potential
`φ(y) = 2 log cosh(√3 y / 2) + log(4 / √3)` of the uniform law on `K = (−√3, √3)` (`V ≡ log(2√3)`)
and the facts of the nonconstant test function `f = tanh²(√3 y / 2)`. Dependency checks, enforced
at elaboration:
* the natural-index cutoffs are obtained by calling the real-parameter construction itself;
* every constant (public, private and generated) of the three modules depends only on the standard
  axioms;
* the client `uniformInterval_tanhSq_integrable_and_integral_hessianInverseOperator_eq_zero` calls
  the source package, the natural-index cutoffs, Lemma A.5 and the test-function facts; no
  integral-zero statement for `f` is used (none is defined: the checked names below are absent).
-/

open Lean Elab Command

namespace LetwinUniformIntervalAudit

/-- The constants of module `m` whose transitive axioms are not among `propext`, `Classical.choice`, `Quot.sound`. -/
def nonstandard (m : Name) : CommandElabM (Array Name) := do
  let env ← getEnv
  let some idx := env.getModuleIdx? m | throwError "module {m} not imported"
  let mut bad := #[]
  for c in env.header.moduleData[idx.toNat]!.constNames do
    let ax ← liftCoreM (collectAxioms c)
    unless ax.all (fun a => a == ``propext || a == ``Classical.choice || a == ``Quot.sound) do bad := bad.push c
  return bad

/-- The constants occurring in the value of `c` or of its own auxiliary constants (names extending `c`, such as
abstracted `_proof_n` terms), followed transitively. -/
partial def usedInValue (c : Name) : CommandElabM (Array Name) := do
  let env ← getEnv
  let rec go (todo : List Name) (seen : NameSet) (acc : Array Name) : CommandElabM (Array Name) := do
    match todo with
    | [] => return acc
    | n :: rest =>
      if seen.contains n then go rest seen acc else
      let some ci := env.find? n | throwError "{n} not found"
      let some v := ci.value? (allowOpaque := true) | throwError "{n} has no value"
      let us := v.getUsedConstants
      go (rest ++ (us.filter (fun u => c.isPrefixOf u)).toList) (seen.insert n) (acc ++ us)
  go [c] {} #[]

end LetwinUniformIntervalAudit

open LetwinUniformIntervalAudit in
run_cmd do
  for m in [`FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.InverseHessian.Cutoff,
            `FunctionalInequalities.Analysis.BakryEmery.UniformIntervalPotential] do
    let bad ← nonstandard m
    unless bad.isEmpty do throwError "nonstandard axioms in {m}: {bad}"
  let used ← usedInValue `FunctionalInequalities.Analysis.BakryEmery.exists_cutoffs_hessianInverseOperator
  unless used.contains `FunctionalInequalities.Analysis.BakryEmery.exists_scaled_cutoffs_hessianInverseOperator do
    throwError "the natural-index cutoffs do not call the real-parameter construction"
  for n in [`FunctionalInequalities.Analysis.BakryEmery.uniformInterval_tanhSq_integral_crossCheck,
            `FunctionalInequalities.Analysis.BakryEmery.uniformInterval_tanhSq_client_facts,
            `FunctionalInequalities.Analysis.BakryEmery.uniformInterval_momentPotential_map] do
    if (← getEnv).contains n then throwError "unexpected integral-zero or pushforward statement {n}"

open LetwinUniformIntervalAudit in
run_cmd do
  let bad ← nonstandard `FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.UniformIntervalClient
  unless bad.isEmpty do throwError "nonstandard axioms in the final client: {bad}"
  let used ← usedInValue
    `FunctionalInequalities.Analysis.BakryEmery.uniformInterval_tanhSq_integrable_and_integral_hessianInverseOperator_eq_zero
  for n in [`FunctionalInequalities.Analysis.BakryEmery.uniformInterval_momentPotential_source_hypotheses,
            `FunctionalInequalities.Analysis.BakryEmery.uniformInterval_tanhSq_nonconstant_facts,
            `FunctionalInequalities.Analysis.BakryEmery.exists_cutoffs_hessianInverseOperator,
            `FunctionalInequalities.Analysis.BakryEmery.integrable_and_integral_hessianInverseOperator_eq_zero_of_cutoffs] do
    unless used.contains n do throwError "the final client does not call {n}"

#print axioms FunctionalInequalities.Analysis.BakryEmery.exists_scaled_cutoffs_hessianInverseOperator
#print axioms FunctionalInequalities.Analysis.BakryEmery.exists_cutoffs_hessianInverseOperator
#print axioms FunctionalInequalities.Analysis.BakryEmery.integrable_and_integral_hessianInverseOperator_eq_zero_of_cutoffs
#print axioms FunctionalInequalities.Analysis.BakryEmery.uniformInterval_momentPotential_gradient
#print axioms FunctionalInequalities.Analysis.BakryEmery.uniformInterval_momentPotential_contDiff_convexOn
#print axioms FunctionalInequalities.Analysis.BakryEmery.uniformInterval_momentPotential_bilinearIteratedFDerivTwo
#print axioms FunctionalInequalities.Analysis.BakryEmery.uniformInterval_momentPotential_logDetHessian
#print axioms FunctionalInequalities.Analysis.BakryEmery.uniformInterval_momentPotential_integral_exp_neg
#print axioms FunctionalInequalities.Analysis.BakryEmery.uniformInterval_momentPotential_source_hypotheses
#print axioms FunctionalInequalities.Analysis.BakryEmery.uniformInterval_tanhSq_nonconstant_facts
#print axioms FunctionalInequalities.Analysis.BakryEmery.uniformInterval_tanhSq_integrable_and_integral_hessianInverseOperator_eq_zero
