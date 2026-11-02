/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Definition.DefSynthesisProblem

/-!
# Input-knowledge hierarchy

This file formalizes the nonempty-history core of `thm:inputhierarchy`.
For a history decomposed as a prefix followed by its last round, the two
processes' compatible global input-pair sequences are comparable, with the
orientation determined by the last communication graph.
-/

namespace DistributedSynthesis

universe u v x y

/-- The global sequence of input pairs in a finite history. -/
def inputPairSequence
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (h : History In₁ In₂ Graph Out₁ Out₂) :
    List (In₁ × In₂) :=
  h.map fun round => (round.inputOne, round.inputTwo)

@[simp]
theorem inputPairSequence_empty
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y} :
    inputPairSequence ([] : History In₁ In₂ Graph Out₁ Out₂) = [] :=
  rfl

@[simp]
theorem inputPairSequence_append
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (r : RoundRecord In₁ In₂ Graph Out₁ Out₂) :
    inputPairSequence (History.append h r) =
      inputPairSequence h ++ [(r.inputOne, r.inputTwo)] := by
  simp [inputPairSequence, History.append]

/--
Definition `def:inputknowledge`: global input-pair sequences compatible with
process `p`'s current local view, at the same history length.
-/
def InputKnowledge
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (p : Proc)
    (h : History In₁ In₂ Graph Out₁ Out₂) :
    Set (List (In₁ × In₂)) :=
  { inputPairs |
    ∃ h' : History In₁ In₂ Graph Out₁ Out₂,
      History.length h' = History.length h ∧
        currentView p h' = currentView p h ∧
          inputPairSequence h' = inputPairs }

/--
Input knowledge for histories written as `prefix + last round`. This is the
nonempty form used in the paper proof of `thm:inputhierarchy`.
-/
def InputKnowledgeAfterRound
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (p : Proc)
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (r : RoundRecord In₁ In₂ Graph Out₁ Out₂) :
    Set (List (In₁ × In₂)) :=
  { inputPairs |
    ∃ h' : History In₁ In₂ Graph Out₁ Out₂,
      ∃ r' : RoundRecord In₁ In₂ Graph Out₁ Out₂,
        inputPairSequence (History.append h' r') = inputPairs ∧
          currentView p (History.append h' r') =
            currentView p (History.append h r) }

/-- If the last graph is left, process `1`'s input knowledge is included in process `2`'s. -/
theorem input_knowledge_after_left_subset
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (r : RoundRecord In₁ In₂ Graph Out₁ Out₂)
    (hr : r.graph = .left) :
    InputKnowledgeAfterRound Proc.one h r ⊆
      InputKnowledgeAfterRound Proc.two h r := by
  intro inputPairs hmem
  rcases hmem with ⟨h', r', hinput, hview⟩
  refine ⟨h', { r' with graph := .left }, ?_, ?_⟩
  · simpa [inputPairSequence, History.append] using hinput
  · cases hgraph : r'.graph <;>
      simp [currentView_one_append, currentView_two_append, hr, hgraph] at hview ⊢
    · exact ⟨hview.2.2.1, hview.2.2.2⟩
    · exact ⟨hview.2.2.1, hview.2.2.2⟩

/-- If the last graph is right, process `2`'s input knowledge is included in process `1`'s. -/
theorem input_knowledge_after_right_subset
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (r : RoundRecord In₁ In₂ Graph Out₁ Out₂)
    (hr : r.graph = .right) :
    InputKnowledgeAfterRound Proc.two h r ⊆
      InputKnowledgeAfterRound Proc.one h r := by
  intro inputPairs hmem
  rcases hmem with ⟨h', r', hinput, hview⟩
  refine ⟨h', { r' with graph := .right }, ?_, ?_⟩
  · simpa [inputPairSequence, History.append] using hinput
  · cases hgraph : r'.graph <;>
      simp [currentView_one_append, currentView_two_append, hr, hgraph] at hview ⊢
    · exact ⟨hview.2.2.1, hview.2.2.2⟩
    · exact ⟨hview.2.2.1, hview.2.2.2⟩

/-- If the last graph is both, the two input-knowledge sets are equal. -/
theorem input_knowledge_after_both_eq
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (r : RoundRecord In₁ In₂ Graph Out₁ Out₂)
    (hr : r.graph = .both) :
    InputKnowledgeAfterRound Proc.one h r =
      InputKnowledgeAfterRound Proc.two h r := by
  apply Set.Subset.antisymm
  · intro inputPairs hmem
    rcases hmem with ⟨h', r', hinput, hview⟩
    refine ⟨h', { r' with graph := .both }, ?_, ?_⟩
    · simpa [inputPairSequence, History.append] using hinput
    · cases hgraph : r'.graph <;>
        simp [currentView_one_append, currentView_two_append, hr, hgraph] at hview ⊢
      · exact ⟨hview.2.2.1, hview.2.2.2, hview.1, hview.2.1⟩
      · exact ⟨hview.2.2.1, hview.2.2.2, hview.1, hview.2.1⟩
  · intro inputPairs hmem
    rcases hmem with ⟨h', r', hinput, hview⟩
    refine ⟨h', { r' with graph := .both }, ?_, ?_⟩
    · simpa [inputPairSequence, History.append] using hinput
    · cases hgraph : r'.graph <;>
        simp [currentView_one_append, currentView_two_append, hr, hgraph] at hview ⊢
      · exact ⟨hview.2.2.1, hview.2.2.2, hview.1, hview.2.1⟩
      · exact ⟨hview.2.2.1, hview.2.2.2, hview.1, hview.2.1⟩

/--
Theorem `thm:inputhierarchy`, nonempty append form: the last graph determines
which process has the smaller compatible set of global input sequences.
-/
theorem input_knowledge_hierarchy_after_round
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (r : RoundRecord In₁ In₂ Graph Out₁ Out₂) :
    match r.graph with
    | .left =>
        InputKnowledgeAfterRound Proc.one h r ⊆
          InputKnowledgeAfterRound Proc.two h r
    | .right =>
        InputKnowledgeAfterRound Proc.two h r ⊆
          InputKnowledgeAfterRound Proc.one h r
    | .both =>
        InputKnowledgeAfterRound Proc.one h r =
          InputKnowledgeAfterRound Proc.two h r := by
  cases hgraph : r.graph with
  | left => exact input_knowledge_after_left_subset h r hgraph
  | right => exact input_knowledge_after_right_subset h r hgraph
  | both => exact input_knowledge_after_both_eq h r hgraph

end DistributedSynthesis
