import Main

/- Use the pinned Comparator's own primitive list, including quotient constants. -/
#eval do
  let cfg : Comparator.Config ← IO.ofExcept <| Lean.fromJson? <|
    ← IO.ofExcept <| Lean.Json.parse <| ← IO.FS.readFile "/opt/audit/targets.json"
  let names ← Comparator.M.run (do
    return (← Comparator.builtinTargets) ++ (← Comparator.getTheoremNames) ++
      (← Comparator.getLegalAxioms) ++ (← Comparator.primitiveTargets)) cfg
  IO.println <| Lean.Json.compress <| Lean.toJson <| names.map Lean.Name.toString
