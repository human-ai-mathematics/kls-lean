import Check
import KLSOpenAI
import KLSOpenAI.Bridge
import KLSOpenAI.Target
import Lean
import OAI.Analysis.KLS.Model
run_cmd do
  let env ← Lean.getEnv
  let modules : Array String := #["OAI.Analysis.KLS.Model", "KLSOpenAI.Bridge", "KLSOpenAI.Target", "KLSOpenAI", "Check"]
  let allowed : Array Lean.Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    let localDecl := match env.getModuleIdxFor? name with
      | some idx => modules.contains env.header.moduleNames[idx.toNat]!.toString
      | none => (`FunctionalInequalities).isPrefixOf name ||
          (`solutions).isPrefixOf name || (`examples).isPrefixOf name
    if !localDecl then continue
    count := count + 1
    let axioms ← Lean.collectAxioms name
    let rendered := String.intercalate ", " (axioms.toList.map Lean.Name.toString)
    let report := Lean.Json.mkObj [("name", Lean.Json.str name.toString),
      ("axioms", Lean.toJson (axioms.toList.map Lean.Name.toString))]
    Lean.logInfo m!"AXIOM_REPORT {report.compress}"
    unless axioms.all (allowed.contains ·) do
      throwError "{name}: unexpected axioms [{rendered}]"
  if count == 0 then throwError "No local declarations audited"
  Lean.logInfo m!"Audited {count} local declarations."

#print KLSOpenAI.of_conjecture
#print axioms KLSOpenAI.of_conjecture
#print axioms KLSOpenAI.kls
