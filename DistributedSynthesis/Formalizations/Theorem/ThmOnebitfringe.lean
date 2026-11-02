/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemJointviewsdeterminehistory

/-!
# One-bit graph fringe

This file formalizes `thm:onebitfringe` from `paper.tex`: for each process,
a current full view is compatible with at most two graph sequences, and the
two possible sequences differ only at the last receive round.
-/

set_option linter.style.longLine false

namespace DistributedSynthesis

universe u v x y

/--
Process `1` graph candidates either are unique or differ only by replacing the
last incoming edge with `both`.
-/
def ProcOneGraphFringeShape (candidates : List (List Graph)) : Prop :=
  (∃ graphs, candidates = [graphs]) ∨
    ∃ pre post,
      candidates = [pre ++ [.left] ++ post, pre ++ [.both] ++ post]

/--
Process `2` graph candidates either are unique or differ only by replacing the
last incoming edge with `both`.
-/
def ProcTwoGraphFringeShape (candidates : List (List Graph)) : Prop :=
  (∃ graphs, candidates = [graphs]) ∨
    ∃ pre post,
      candidates = [pre ++ [.right] ++ post, pre ++ [.both] ++ post]

/-- Candidate graph sequences compatible with a process-`1` full view. -/
def procOneGraphCandidates
    {In₁ : Type u} {In₂ : Type v} :
    View In₁ In₂ Proc.one -> Option (List (List Graph))
  | .empty _ => some [[]]
  | .noRecv prev (.inl _) =>
      Option.map (List.map fun graphs => graphs ++ [.right]) (procOneGraphCandidates prev)
  | .recv prevOne (.inl _) prevTwo (.inr _) =>
      Option.map
        (fun decoded => [decoded.1 ++ [.left], decoded.1 ++ [.both]])
        (decodeJointViews prevOne prevTwo)
  | _ => none

/-- Candidate graph sequences compatible with a process-`2` full view. -/
def procTwoGraphCandidates
    {In₁ : Type u} {In₂ : Type v} :
    View In₁ In₂ Proc.two -> Option (List (List Graph))
  | .empty _ => some [[]]
  | .noRecv prev (.inr _) =>
      Option.map (List.map fun graphs => graphs ++ [.left]) (procTwoGraphCandidates prev)
  | .recv prevTwo (.inr _) prevOne (.inl _) =>
      Option.map
        (fun decoded => [decoded.1 ++ [.right], decoded.1 ++ [.both]])
        (decodeJointViews prevOne prevTwo)
  | _ => none

/-- The process-`1` candidate decoder always has the one-bit-fringe shape. -/
theorem procOneGraphCandidates_shape
    {In₁ : Type u} {In₂ : Type v}
    : (view : View In₁ In₂ Proc.one) ->
      (candidates : List (List Graph)) ->
      procOneGraphCandidates view = some candidates ->
        ProcOneGraphFringeShape candidates
  | .empty _, candidates, hcandidates => by
      have hEq : candidates = [[]] := (Option.some.inj (by
        simpa [procOneGraphCandidates] using hcandidates)).symm
      subst candidates
      exact Or.inl ⟨[], rfl⟩
  | .noRecv prev (.inl _), candidates, hcandidates => by
      cases hprev : procOneGraphCandidates prev with
      | none =>
          simp [procOneGraphCandidates, hprev] at hcandidates
      | some previous =>
          have hEq : candidates = previous.map (fun graphs => graphs ++ [.right]) :=
            (Option.some.inj (by
              simpa [procOneGraphCandidates, hprev] using hcandidates)).symm
          subst candidates
          rcases procOneGraphCandidates_shape prev previous hprev with
            ⟨graphs, hgraphs⟩ | ⟨pre, post, hshape⟩
          · subst previous
            exact Or.inl ⟨graphs ++ [.right], rfl⟩
          · subst previous
            exact Or.inr ⟨pre, post ++ [.right], by simp [List.append_assoc]⟩
  | .noRecv _ (.inr _), candidates, hcandidates => by
      simp [procOneGraphCandidates] at hcandidates
  | .recv prevOne (.inl _) prevTwo (.inr _), candidates, hcandidates => by
      cases hdecode : decodeJointViews prevOne prevTwo with
      | none =>
          simp [procOneGraphCandidates, hdecode] at hcandidates
      | some decoded =>
          have hEq :
              candidates = [decoded.1 ++ [.left], decoded.1 ++ [.both]] :=
            (Option.some.inj (by
              simpa [procOneGraphCandidates, hdecode] using hcandidates)).symm
          subst candidates
          exact Or.inr ⟨decoded.1, [], by simp⟩
  | .recv _ (.inl _) _ (.inl _), candidates, hcandidates => by
      simp [procOneGraphCandidates] at hcandidates
  | .recv _ (.inr _) _ _, candidates, hcandidates => by
      simp [procOneGraphCandidates] at hcandidates

/-- The process-`2` candidate decoder always has the one-bit-fringe shape. -/
theorem procTwoGraphCandidates_shape
    {In₁ : Type u} {In₂ : Type v}
    : (view : View In₁ In₂ Proc.two) ->
      (candidates : List (List Graph)) ->
      procTwoGraphCandidates view = some candidates ->
        ProcTwoGraphFringeShape candidates
  | .empty _, candidates, hcandidates => by
      have hEq : candidates = [[]] := (Option.some.inj (by
        simpa [procTwoGraphCandidates] using hcandidates)).symm
      subst candidates
      exact Or.inl ⟨[], rfl⟩
  | .noRecv _ (.inl _), candidates, hcandidates => by
      simp [procTwoGraphCandidates] at hcandidates
  | .noRecv prev (.inr _), candidates, hcandidates => by
      cases hprev : procTwoGraphCandidates prev with
      | none =>
          simp [procTwoGraphCandidates, hprev] at hcandidates
      | some previous =>
          have hEq : candidates = previous.map (fun graphs => graphs ++ [.left]) :=
            (Option.some.inj (by
              simpa [procTwoGraphCandidates, hprev] using hcandidates)).symm
          subst candidates
          rcases procTwoGraphCandidates_shape prev previous hprev with
            ⟨graphs, hgraphs⟩ | ⟨pre, post, hshape⟩
          · subst previous
            exact Or.inl ⟨graphs ++ [.left], rfl⟩
          · subst previous
            exact Or.inr ⟨pre, post ++ [.left], by simp [List.append_assoc]⟩
  | .recv prevTwo (.inr _) prevOne (.inl _), candidates, hcandidates => by
      cases hdecode : decodeJointViews prevOne prevTwo with
      | none =>
          simp [procTwoGraphCandidates, hdecode] at hcandidates
      | some decoded =>
          have hEq :
              candidates = [decoded.1 ++ [.right], decoded.1 ++ [.both]] :=
            (Option.some.inj (by
              simpa [procTwoGraphCandidates, hdecode] using hcandidates)).symm
          subst candidates
          exact Or.inr ⟨decoded.1, [], by simp⟩
  | .recv _ (.inl _) _ _, candidates, hcandidates => by
      simp [procTwoGraphCandidates] at hcandidates
  | .recv _ (.inr _) _ (.inr _), candidates, hcandidates => by
      simp [procTwoGraphCandidates] at hcandidates

/-- Process `1`'s actual graph sequence belongs to the candidate set of its current view. -/
theorem procOneGraphCandidates_current
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (h : History In₁ In₂ Graph Out₁ Out₂) :
    ∃ candidates,
      procOneGraphCandidates (currentView Proc.one h) = some candidates ∧
      History.graphSequence h ∈ candidates ∧
      candidates.length ≤ 2 := by
  induction h using List.reverseRecOn with
  | nil =>
      refine ⟨[[]], ?_, ?_, by simp⟩
      · simp [procOneGraphCandidates, currentView, viewPair]
      · simp [History.graphSequence]
  | append_singleton h r ih =>
      obtain ⟨candidates, hcandidates, hmem, hlen⟩ := ih
      cases hGraph : r.graph with
      | left =>
          refine ⟨[History.graphSequence h ++ [.left], History.graphSequence h ++ [.both]], ?_, ?_, by simp⟩
          · change procOneGraphCandidates (currentView Proc.one (History.append h r)) = _
            rw [currentView_one_append]
            simp [procOneGraphCandidates, decodeJointViews_current, History.graphSequence, hGraph]
          · simp [History.graphSequence, hGraph]
      | right =>
          refine ⟨candidates.map (fun graphs => graphs ++ [.right]), ?_, ?_, ?_⟩
          · change procOneGraphCandidates (currentView Proc.one (History.append h r)) = _
            rw [currentView_one_append]
            simp [procOneGraphCandidates, hGraph, hcandidates]
          · simpa [History.graphSequence, hGraph] using
              (List.mem_map.2 ⟨History.graphSequence h, hmem, rfl⟩ :
                History.graphSequence h ++ [Graph.right] ∈
                  candidates.map (fun graphs => graphs ++ [Graph.right]))
          · simpa using hlen
      | both =>
          refine ⟨[History.graphSequence h ++ [.left], History.graphSequence h ++ [.both]], ?_, ?_, by simp⟩
          · change procOneGraphCandidates (currentView Proc.one (History.append h r)) = _
            rw [currentView_one_append]
            simp [procOneGraphCandidates, decodeJointViews_current, History.graphSequence, hGraph]
          · simp [History.graphSequence, hGraph]

/-- Process `2`'s actual graph sequence belongs to the candidate set of its current view. -/
theorem procTwoGraphCandidates_current
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (h : History In₁ In₂ Graph Out₁ Out₂) :
    ∃ candidates,
      procTwoGraphCandidates (currentView Proc.two h) = some candidates ∧
      History.graphSequence h ∈ candidates ∧
      candidates.length ≤ 2 := by
  induction h using List.reverseRecOn with
  | nil =>
      refine ⟨[[]], ?_, ?_, by simp⟩
      · simp [procTwoGraphCandidates, currentView, viewPair]
      · simp [History.graphSequence]
  | append_singleton h r ih =>
      obtain ⟨candidates, hcandidates, hmem, hlen⟩ := ih
      cases hGraph : r.graph with
      | left =>
          refine ⟨candidates.map (fun graphs => graphs ++ [.left]), ?_, ?_, ?_⟩
          · change procTwoGraphCandidates (currentView Proc.two (History.append h r)) = _
            rw [currentView_two_append]
            simp [procTwoGraphCandidates, hGraph, hcandidates]
          · simpa [History.graphSequence, hGraph] using
              (List.mem_map.2 ⟨History.graphSequence h, hmem, rfl⟩ :
                History.graphSequence h ++ [Graph.left] ∈
                  candidates.map (fun graphs => graphs ++ [Graph.left]))
          · simpa using hlen
      | right =>
          refine ⟨[History.graphSequence h ++ [.right], History.graphSequence h ++ [.both]], ?_, ?_, by simp⟩
          · change procTwoGraphCandidates (currentView Proc.two (History.append h r)) = _
            rw [currentView_two_append]
            simp [procTwoGraphCandidates, decodeJointViews_current, History.graphSequence, hGraph]
          · simp [History.graphSequence, hGraph]
      | both =>
          refine ⟨[History.graphSequence h ++ [.right], History.graphSequence h ++ [.both]], ?_, ?_, by simp⟩
          · change procTwoGraphCandidates (currentView Proc.two (History.append h r)) = _
            rw [currentView_two_append]
            simp [procTwoGraphCandidates, decodeJointViews_current, History.graphSequence, hGraph]
          · simp [History.graphSequence, hGraph]

/--
At a process-`1` receive round with a one-way incoming edge, the two compatible
graph histories differ exactly on the counterpart receipt bit: `.left` versus
`.both`.
-/
theorem procOneGraphCandidates_current_left
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (r : RoundRecord In₁ In₂ Graph Out₁ Out₂)
    (hGraph : r.graph = .left) :
    procOneGraphCandidates (currentView Proc.one (History.append h r)) =
      some [History.graphSequence h ++ [.left], History.graphSequence h ++ [.both]] := by
  rw [currentView_one_append]
  simp [procOneGraphCandidates, decodeJointViews_current, History.graphSequence, hGraph]

/--
At a process-`1` receive round with a bidirectional edge, the same one-bit
counterpart-receipt ambiguity is represented by `.left` versus `.both`.
-/
theorem procOneGraphCandidates_current_both
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (r : RoundRecord In₁ In₂ Graph Out₁ Out₂)
    (hGraph : r.graph = .both) :
    procOneGraphCandidates (currentView Proc.one (History.append h r)) =
      some [History.graphSequence h ++ [.left], History.graphSequence h ++ [.both]] := by
  rw [currentView_one_append]
  simp [procOneGraphCandidates, decodeJointViews_current, History.graphSequence, hGraph]

/--
At a process-`2` receive round with a one-way incoming edge, the two compatible
graph histories differ exactly on the counterpart receipt bit: `.right` versus
`.both`.
-/
theorem procTwoGraphCandidates_current_right
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (r : RoundRecord In₁ In₂ Graph Out₁ Out₂)
    (hGraph : r.graph = .right) :
    procTwoGraphCandidates (currentView Proc.two (History.append h r)) =
      some [History.graphSequence h ++ [.right], History.graphSequence h ++ [.both]] := by
  rw [currentView_two_append]
  simp [procTwoGraphCandidates, decodeJointViews_current, History.graphSequence, hGraph]

/--
At a process-`2` receive round with a bidirectional edge, the same one-bit
counterpart-receipt ambiguity is represented by `.right` versus `.both`.
-/
theorem procTwoGraphCandidates_current_both
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (r : RoundRecord In₁ In₂ Graph Out₁ Out₂)
    (hGraph : r.graph = .both) :
    procTwoGraphCandidates (currentView Proc.two (History.append h r)) =
      some [History.graphSequence h ++ [.right], History.graphSequence h ++ [.both]] := by
  rw [currentView_two_append]
  simp [procTwoGraphCandidates, decodeJointViews_current, History.graphSequence, hGraph]

/-- Any history compatible with process `1`'s current view uses one of at most two graph sequences. -/
theorem onebitfringe_procOne
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (h : History In₁ In₂ Graph Out₁ Out₂) :
    ∃ candidates : List (List Graph),
      candidates.length ≤ 2 ∧
      History.graphSequence h ∈ candidates ∧
      ∀ h' : History In₁ In₂ Graph Out₁ Out₂,
        currentView Proc.one h' = currentView Proc.one h ->
        History.graphSequence h' ∈ candidates := by
  obtain ⟨candidates, hcandidates, hmem, hlen⟩ := procOneGraphCandidates_current h
  refine ⟨candidates, hlen, hmem, ?_⟩
  intro h' hview
  obtain ⟨candidates', hcandidates', hmem', _⟩ := procOneGraphCandidates_current h'
  rw [hview, hcandidates] at hcandidates'
  injection hcandidates' with hEq
  simpa [hEq] using hmem'

/--
Precise process-`1` form of `thm:onebitfringe`: the compatible graph
sequences are either unique or share a common prefix and suffix, differing only
between `left` and `both`.
-/
theorem onebitfringe_procOne_precise
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (h : History In₁ In₂ Graph Out₁ Out₂) :
    ∃ candidates : List (List Graph),
      ProcOneGraphFringeShape candidates ∧
      candidates.length ≤ 2 ∧
      History.graphSequence h ∈ candidates ∧
      ∀ h' : History In₁ In₂ Graph Out₁ Out₂,
        currentView Proc.one h' = currentView Proc.one h ->
        History.graphSequence h' ∈ candidates := by
  obtain ⟨candidates, hcandidates, hmem, hlen⟩ := procOneGraphCandidates_current h
  refine ⟨candidates, procOneGraphCandidates_shape (currentView Proc.one h) candidates hcandidates,
    hlen, hmem, ?_⟩
  intro h' hview
  obtain ⟨candidates', hcandidates', hmem', _⟩ := procOneGraphCandidates_current h'
  rw [hview, hcandidates] at hcandidates'
  injection hcandidates' with hEq
  simpa [hEq] using hmem'

/-- Any history compatible with process `2`'s current view uses one of at most two graph sequences. -/
theorem onebitfringe_procTwo
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (h : History In₁ In₂ Graph Out₁ Out₂) :
    ∃ candidates : List (List Graph),
      candidates.length ≤ 2 ∧
      History.graphSequence h ∈ candidates ∧
      ∀ h' : History In₁ In₂ Graph Out₁ Out₂,
        currentView Proc.two h' = currentView Proc.two h ->
        History.graphSequence h' ∈ candidates := by
  obtain ⟨candidates, hcandidates, hmem, hlen⟩ := procTwoGraphCandidates_current h
  refine ⟨candidates, hlen, hmem, ?_⟩
  intro h' hview
  obtain ⟨candidates', hcandidates', hmem', _⟩ := procTwoGraphCandidates_current h'
  rw [hview, hcandidates] at hcandidates'
  injection hcandidates' with hEq
  simpa [hEq] using hmem'

/--
Precise process-`2` form of `thm:onebitfringe`: the compatible graph
sequences are either unique or share a common prefix and suffix, differing only
between `right` and `both`.
-/
theorem onebitfringe_procTwo_precise
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (h : History In₁ In₂ Graph Out₁ Out₂) :
    ∃ candidates : List (List Graph),
      ProcTwoGraphFringeShape candidates ∧
      candidates.length ≤ 2 ∧
      History.graphSequence h ∈ candidates ∧
      ∀ h' : History In₁ In₂ Graph Out₁ Out₂,
        currentView Proc.two h' = currentView Proc.two h ->
        History.graphSequence h' ∈ candidates := by
  obtain ⟨candidates, hcandidates, hmem, hlen⟩ := procTwoGraphCandidates_current h
  refine ⟨candidates, procTwoGraphCandidates_shape (currentView Proc.two h) candidates hcandidates,
    hlen, hmem, ?_⟩
  intro h' hview
  obtain ⟨candidates', hcandidates', hmem', _⟩ := procTwoGraphCandidates_current h'
  rw [hview, hcandidates] at hcandidates'
  injection hcandidates' with hEq
  simpa [hEq] using hmem'

/-- At most two graph sequences are compatible with a current full view. -/
theorem onebitfringe
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (p : Proc)
    (h : History In₁ In₂ Graph Out₁ Out₂) :
    ∃ candidates : List (List Graph),
      candidates.length ≤ 2 ∧
      History.graphSequence h ∈ candidates ∧
      ∀ h' : History In₁ In₂ Graph Out₁ Out₂,
        currentView p h' = currentView p h ->
        History.graphSequence h' ∈ candidates := by
  cases p with
  | one => simpa using onebitfringe_procOne h
  | two => simpa using onebitfringe_procTwo h

/--
Paper-facing precise form of `thm:onebitfringe`: the candidates have the
one-bit graph-fringe shape for the chosen process.
-/
theorem onebitfringe_precise
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (p : Proc)
    (h : History In₁ In₂ Graph Out₁ Out₂) :
    ∃ candidates : List (List Graph),
      (match p with
        | .one => ProcOneGraphFringeShape candidates
        | .two => ProcTwoGraphFringeShape candidates) ∧
      candidates.length ≤ 2 ∧
      History.graphSequence h ∈ candidates ∧
      ∀ h' : History In₁ In₂ Graph Out₁ Out₂,
        currentView p h' = currentView p h ->
        History.graphSequence h' ∈ candidates := by
  cases p with
  | one => simpa using onebitfringe_procOne_precise h
  | two => simpa using onebitfringe_procTwo_precise h

end DistributedSynthesis
