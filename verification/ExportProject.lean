import Export

/- Enumerate the compiled public mathematical API, then use upstream lean4export
to serialize it. No theorem names are inferred from source-text patterns. -/
open Lean

private def publicProjectDeclaration (env : Environment) (info : ConstantInfo) : Bool :=
  match env.getModuleIdxFor? info.name with
  | none => false
  | some index =>
    (`DistributedSynthesis).isPrefixOf env.header.moduleNames[index.toNat]! &&
      !isPrivateName info.name && !info.name.isInternal && !info.isUnsafe && !info.isPartial

def main (args : List String) : IO Unit := do
  let [module, primitiveFile, manifestFile] := args
    | throw <| IO.userError "Expected MODULE PRIMITIVES.json MANIFEST.json"
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := module.toName }] {}
  let constants := env.constants.toList.filterMap fun (_, info) =>
    if publicProjectDeclaration env info then some info else none
  let constants := constants.toArray.qsort (fun a b => a.name.toString < b.name.toString)
  let theorems := constants.filterMap fun info =>
    if info.isTheorem then some info.name.toString else none
  let rigid := constants.filterMap fun info =>
    if info.isTheorem then none else some info.name.toString
  let modules := env.header.moduleNames.filter ((`DistributedSynthesis.Results).isPrefixOf ·)
    |>.map Name.toString |>.qsort (· < ·)
  let manifest := Json.mkObj [
    ("format", toJson (1 : Nat)), ("module", toJson module),
    ("result_modules", toJson modules), ("theorem_names", toJson theorems),
    ("rigid_names", toJson rigid)]
  IO.FS.writeFile manifestFile (Json.pretty manifest)
  let primitives : Array String ← IO.ofExcept <| fromJson? <|
    ← IO.ofExcept <| Json.parse <| ← IO.FS.readFile primitiveFile
  M.run env do
    let _ ← initState env []
    dumpMetadata
    for name in constants.map (·.name) ++ primitives.map String.toName do
      modify (fun state => { state with noMDataExprs := {} })
      dumpConstant name
