import Main

/- Only the trusted checker is elaborated here. Candidate input is serialized
declaration data; candidate source files and oleans are absent from this container.
When selected, Nanoda runs separately, before this file, and must also succeed. -/
#eval do
  let cfg : Comparator.Config ← IO.ofExcept <| Lean.fromJson? <|
    ← IO.ofExcept <| Lean.Json.parse <| ← IO.FS.readFile "/work/comparator.json"
  let rigid : Array String ← IO.ofExcept <| Lean.fromJson? <|
    ← IO.ofExcept <| Lean.Json.parse <| ← IO.FS.readFile "/work/rigid.json"
  let reference ← IO.FS.readFile "/work/reference.ndjson"
  let solution ← IO.FS.readFile "/work/solution.ndjson"
  Comparator.M.run (do
    let challenge ← Export.parseStream (← Comparator.stringStream reference)
    let candidate ← Export.parseStream (← Comparator.stringStream solution)
    let theorems ← Comparator.getTheoremNames
    let legal ← Comparator.getLegalAxioms
    let rigid := rigid.map String.toName
    IO.ofExcept <| Comparator.compareAt challenge candidate (theorems ++ legal) #[]
      (← Comparator.primitiveTargets)
    -- Public definitions, types, and constructors must match exactly. These
    -- are fixed declarations, not Comparator definition holes.
    IO.ofExcept <| (Comparator.Compare.loop.run {
      challenge, solution := candidate, definitionTargets := {},
      theoremTargets := Std.HashSet.ofArray theorems
    }).run' { worklist := rigid, checked := {} }
    -- Check every public root, including definitions unused by any theorem.
    for name in rigid do
      if let some (.axiomInfo info) := candidate.constMap[name]? then
        unless legal.contains info.name do
          throw <| IO.userError s!"Illegal public axiom: '{name}'"
    IO.ofExcept <| (Comparator.Axioms.loop.run {
      solution := candidate, legalAxioms := Std.HashSet.ofArray legal
    }).run' { worklist := theorems ++ rigid, checked := {} }
    if let some error ← Comparator.runBuiltinKernel candidate then
      throw <| IO.userError error
  ) cfg
  IO.println "Comparator: public statements, fixed definitions, axiom allowlist, and Lean kernel replay passed."
