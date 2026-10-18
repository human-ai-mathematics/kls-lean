import Lean

/-! Compiler observation for the generated public API directory. The Python producer supplies every library import; this is repository tooling. -/

open Lean Elab Command Meta

namespace RepositoryAPIIndex

private def declarationKind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

set_option maxHeartbeats 0 in
run_cmd do
  let outputPath ← liftIO <| IO.getEnv "KLS_API_INDEX_OUTPUT"
  let some outputPath := outputPath | throwError "Set KLS_API_INDEX_OUTPUT to an explicit output file"
  let rows ← liftTermElabM do
    let env ← getEnv
    let mut rows : Array Json := #[]
    for (name, info) in env.constants.toList do
      if isPrivateName name || name.isInternalDetail then continue
      let some moduleIdx := env.getModuleIdxFor? name | continue
      let owner := env.header.moduleNames[moduleIdx.toNat]!.toString
      unless owner == "FunctionalInequalities" || owner.startsWith "FunctionalInequalities." do continue
      let type ← withOptions (fun o => (o.setBool `pp.universes true).setBool `pp.fullNames true) do
        return (← ppExpr info.type).pretty
      let ranges ← findDeclarationRanges? name
      let doc ← liftM <| findDocString? env name
      rows := rows.push <| Json.mkObj [
        ("name", toJson name.toString), ("kind", toJson (declarationKind info)),
        ("module", toJson owner), ("type", toJson type),
        ("universes", toJson (info.levelParams.map Name.toString)),
        ("unsafe", toJson info.isUnsafe), ("partial", toJson info.isPartial),
        ("source_line", toJson (ranges.map (·.selectionRange.pos.line))),
        ("source_end_line", toJson (ranges.map (·.range.endPos.line))),
        ("docstring", toJson doc)]
    let modules := env.header.moduleNames.toList.filter fun m =>
      m.toString == "FunctionalInequalities" || m.toString.startsWith "FunctionalInequalities."
    return Json.mkObj [("modules", toJson (modules.map Name.toString)), ("declarations", toJson rows)]
  liftIO <| IO.FS.writeFile outputPath rows.pretty

end RepositoryAPIIndex
