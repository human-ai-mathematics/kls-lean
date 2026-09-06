import Lean

/-!
Elaborated statement snapshots. Traverse local declaration types and definition bodies,
including structure constructors. Theorem bodies are omitted; their types are retained.
Imported non-project declarations are explicit trust-boundary leaves. This command is
inspection tooling, not a proof checker or a test of mathematical equivalence.
-/

open Lean Elab Command Meta

set_option pp.maxSteps 1000000

namespace StatementSnapshot

private def localDeclaration (env : Environment) (name : Name) : Bool :=
  match env.getModuleIdxFor? name with
  | some idx => (`FunctionalInequalities).isPrefixOf env.header.moduleNames[idx.toNat]!
  | none => (`FunctionalInequalities).isPrefixOf name

private def kind : ConstantInfo → String
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem_type"
  | .opaqueInfo _ => "opaque"
  | .axiomInfo _ => "axiom"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"
  | .quotInfo _ => "quotient"

private def body (info : ConstantInfo) : Option Expr :=
  if info.isTheorem then none else info.value? (allowOpaque := true)

private def related (info : ConstantInfo) : Array Name :=
  match info with
  | .inductInfo v => v.ctors.toArray ++ v.all.toArray
  | .ctorInfo v => #[v.induct]
  | .recInfo v => v.all.toArray
  | _ => #[]

private def render (e : Expr) : MetaM String := do
  let text := (← ppExpr e).pretty 100
  if text.contains '⋯' then
    throwError "Statement snapshot printing was truncated"
  return text

private def snapshot (roots : Array Name) : MetaM Json := do
  let env ← getEnv
  let mut pending := roots
  let mut visited : NameSet := {}
  let mut records : Array (Name × Json) := #[]
  let mut external : NameSet := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if visited.contains name then continue
    visited := visited.insert name
    let some info := env.find? name | throwError "Snapshot declaration not found: {name}"
    if !localDeclaration env name then
      external := external.insert name
      continue
    if info.isUnsafe || info.isPartial || info.isAxiom then
      throwError "Unsupported statement dependency: {name}"
    let value := body info
    let deps := info.type.getUsedConstants ++
      (value.map Expr.getUsedConstants).getD #[] ++ related info
    pending := pending ++ deps
    let moduleName := (env.getModuleIdxFor? name).map fun idx =>
      env.header.moduleNames[idx.toNat]!.toString
    records := records.push (name, Json.mkObj [
      ("name", toJson name.toString), ("kind", toJson (kind info)),
      ("module", toJson moduleName),
      ("levels", toJson (info.levelParams.map Name.toString)),
      ("type", toJson (← render info.type)),
      ("value", toJson (← value.mapM render)),
      ("dependencies", toJson ((deps.toList.map Name.toString).mergeSort (· ≤ ·)).eraseDups)])
  let sorted := records.toList.mergeSort fun a b => a.1.toString ≤ b.1.toString
  return Json.mkObj [
    ("roots", toJson (roots.map Name.toString)),
    ("declarations", toJson (sorted.map Prod.snd)),
    ("external", toJson ((external.toList.map Name.toString).mergeSort (· ≤ ·)))]

elab "#statement_snapshot " names:ident+ : command => do
  let result ← liftTermElabM do
    let roots ← names.mapM fun name => realizeGlobalConstNoOverloadWithInfo name
    withOptions (fun o => (o.setBool `pp.all true).setBool `pp.proofs true) do
      snapshot roots
  liftIO <| IO.println result.compress

end StatementSnapshot
