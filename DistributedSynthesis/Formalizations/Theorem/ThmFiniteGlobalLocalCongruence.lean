/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmFiniteGlobalBeliefSummary

/-!
# Finite local congruences imply belief uniformity

The dangerous belief-uniformity induction is generic.  A relation for each
process equates global controls with the same local future behavior.  It is
closed under that process's hidden-input no-receive update, and under both
graphs compatible with a receive when the two source controls are related for
both processes.  These four finite one-step laws imply that every reachable
belief is relation-homogeneous and therefore output-uniform.
-/

namespace DistributedSynthesis

universe u v w x y

namespace FiniteGlobalRoundMachine

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable [Fintype In₁] [Fintype In₂]
variable (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
variable (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)

/-- A pair of finite-state behavioral relations sufficient for localizing a
global round machine. -/
structure LocalCongruence where
  EqOne : G.State → G.State → Prop
  EqTwo : G.State → G.State → Prop
  reflOne : ∀ state, EqOne state state
  reflTwo : ∀ state, EqTwo state state
  outputOne_eq : ∀ {left right}, EqOne left right →
    outputOne left = outputOne right
  outputTwo_eq : ∀ {left right}, EqTwo left right →
    outputTwo left = outputTwo right
  noRecvOne : ∀ {left right}, EqOne left right →
    ∀ (inputOne : In₁) (leftHidden rightHidden : In₂),
      EqOne
        (G.step left
          { inputOne := inputOne, inputTwo := leftHidden, graph := .right })
        (G.step right
          { inputOne := inputOne, inputTwo := rightHidden, graph := .right })
  noRecvTwo : ∀ {left right}, EqTwo left right →
    ∀ (inputTwo : In₂) (leftHidden rightHidden : In₁),
      EqTwo
        (G.step left
          { inputOne := leftHidden, inputTwo := inputTwo, graph := .left })
        (G.step right
          { inputOne := rightHidden, inputTwo := inputTwo, graph := .left })
  recvOne : ∀ {left right}, EqOne left right → EqTwo left right →
    ∀ (inputOne : In₁) (inputTwo : In₂) (leftGraph rightGraph : Graph),
      (leftGraph = .left ∨ leftGraph = .both) →
      (rightGraph = .left ∨ rightGraph = .both) →
      EqOne
        (G.step left
          { inputOne := inputOne, inputTwo := inputTwo, graph := leftGraph })
        (G.step right
          { inputOne := inputOne, inputTwo := inputTwo, graph := rightGraph })
  recvTwo : ∀ {left right}, EqOne left right → EqTwo left right →
    ∀ (inputOne : In₁) (inputTwo : In₂) (leftGraph rightGraph : Graph),
      (leftGraph = .right ∨ leftGraph = .both) →
      (rightGraph = .right ∨ rightGraph = .both) →
      EqTwo
        (G.step left
          { inputOne := inputOne, inputTwo := inputTwo, graph := leftGraph })
        (G.step right
          { inputOne := inputOne, inputTwo := inputTwo, graph := rightGraph })

/-- All elements of a finite belief are pairwise related. -/
def BeliefRelated (R : G.State → G.State → Prop)
    (K : Finset G.State) : Prop :=
  ∀ left ∈ K, ∀ right ∈ K, R left right

variable (C : G.LocalCongruence outputOne outputTwo)

theorem beliefAdvance_related
    (pair : Finset G.State × Finset G.State)
    (hOne : G.BeliefRelated C.EqOne pair.1)
    (hTwo : G.BeliefRelated C.EqTwo pair.2)
    (round : EnvironmentRound In₁ In₂) :
    G.BeliefRelated C.EqOne (G.beliefAdvance pair round).1 ∧
      G.BeliefRelated C.EqTwo (G.beliefAdvance pair round).2 := by
  classical
  rcases round with ⟨inputOne, inputTwo, graph⟩
  cases graph with
  | left =>
      constructor
      · intro nextLeft hnextLeft nextRight hnextRight
        simp only [beliefAdvance, beliefRecvOne, Finset.mem_filter,
          Finset.mem_univ, true_and] at hnextLeft hnextRight
        rcases hnextLeft with ⟨sourceLeft, hselfLeft, hotherLeft, hgraphLeft⟩
        rcases hnextRight with
          ⟨sourceRight, hselfRight, hotherRight, hgraphRight⟩
        rcases hgraphLeft with hleft | hleft <;>
          rcases hgraphRight with hright | hright <;>
          subst nextLeft <;> subst nextRight
        all_goals
          exact C.recvOne (hOne sourceLeft hselfLeft sourceRight hselfRight)
            (hTwo sourceLeft hotherLeft sourceRight hotherRight)
            inputOne inputTwo _ _ (by simp) (by simp)
      · intro nextLeft hnextLeft nextRight hnextRight
        simp only [beliefAdvance, beliefNoRecvTwo, Finset.mem_filter,
          Finset.mem_univ, true_and] at hnextLeft hnextRight
        rcases hnextLeft with ⟨sourceLeft, hsourceLeft, hiddenLeft, rfl⟩
        rcases hnextRight with ⟨sourceRight, hsourceRight, hiddenRight, rfl⟩
        exact C.noRecvTwo
          (hTwo sourceLeft hsourceLeft sourceRight hsourceRight)
          inputTwo hiddenLeft hiddenRight
  | right =>
      constructor
      · intro nextLeft hnextLeft nextRight hnextRight
        simp only [beliefAdvance, beliefNoRecvOne, Finset.mem_filter,
          Finset.mem_univ, true_and] at hnextLeft hnextRight
        rcases hnextLeft with ⟨sourceLeft, hsourceLeft, hiddenLeft, rfl⟩
        rcases hnextRight with ⟨sourceRight, hsourceRight, hiddenRight, rfl⟩
        exact C.noRecvOne
          (hOne sourceLeft hsourceLeft sourceRight hsourceRight)
          inputOne hiddenLeft hiddenRight
      · intro nextLeft hnextLeft nextRight hnextRight
        simp only [beliefAdvance, beliefRecvTwo, Finset.mem_filter,
          Finset.mem_univ, true_and] at hnextLeft hnextRight
        rcases hnextLeft with ⟨sourceLeft, hselfLeft, hotherLeft, hgraphLeft⟩
        rcases hnextRight with
          ⟨sourceRight, hselfRight, hotherRight, hgraphRight⟩
        rcases hgraphLeft with hleft | hleft <;>
          rcases hgraphRight with hright | hright <;>
          subst nextLeft <;> subst nextRight
        all_goals
          exact C.recvTwo (hOne sourceLeft hotherLeft sourceRight hotherRight)
            (hTwo sourceLeft hselfLeft sourceRight hselfRight)
            inputOne inputTwo _ _ (by simp) (by simp)
  | both =>
      constructor
      · intro nextLeft hnextLeft nextRight hnextRight
        simp only [beliefAdvance, beliefRecvOne, Finset.mem_filter,
          Finset.mem_univ, true_and] at hnextLeft hnextRight
        rcases hnextLeft with ⟨sourceLeft, hselfLeft, hotherLeft, hgraphLeft⟩
        rcases hnextRight with
          ⟨sourceRight, hselfRight, hotherRight, hgraphRight⟩
        rcases hgraphLeft with hleft | hleft <;>
          rcases hgraphRight with hright | hright <;>
          subst nextLeft <;> subst nextRight
        all_goals
          exact C.recvOne (hOne sourceLeft hselfLeft sourceRight hselfRight)
            (hTwo sourceLeft hotherLeft sourceRight hotherRight)
            inputOne inputTwo _ _ (by simp) (by simp)
      · intro nextLeft hnextLeft nextRight hnextRight
        simp only [beliefAdvance, beliefRecvTwo, Finset.mem_filter,
          Finset.mem_univ, true_and] at hnextLeft hnextRight
        rcases hnextLeft with ⟨sourceLeft, hselfLeft, hotherLeft, hgraphLeft⟩
        rcases hnextRight with
          ⟨sourceRight, hselfRight, hotherRight, hgraphRight⟩
        rcases hgraphLeft with hleft | hleft <;>
          rcases hgraphRight with hright | hright <;>
          subst nextLeft <;> subst nextRight
        all_goals
          exact C.recvTwo (hOne sourceLeft hotherLeft sourceRight hotherRight)
            (hTwo sourceLeft hselfLeft sourceRight hselfRight)
            inputOne inputTwo _ _ (by simp) (by simp)

/-- Every reachable pair of beliefs is homogeneous for the two local
congruences. -/
theorem beliefsAfter_related
    (rounds : List (EnvironmentRound In₁ In₂)) :
    G.BeliefRelated C.EqOne (G.beliefsAfter rounds).1 ∧
      G.BeliefRelated C.EqTwo (G.beliefsAfter rounds).2 := by
  induction rounds using List.reverseRecOn with
  | nil =>
      constructor <;>
        intro left hleft right hright <;>
        simp [beliefsAfter] at hleft hright <;>
        subst left <;> subst right
      · exact C.reflOne _
      · exact C.reflTwo _
  | append_singleton rounds round ih =>
      simp only [beliefsAfter, List.foldl_append, List.foldl_cons,
        List.foldl_nil]
      exact G.beliefAdvance_related outputOne outputTwo C
        (G.beliefsAfter rounds) ih.1 ih.2 round

/-- A finite local congruence discharges the dangerous reachable-belief
uniformity predicate. -/
theorem reachableBeliefsUniform_of_localCongruence :
    (C : G.LocalCongruence outputOne outputTwo) →
    G.ReachableBeliefsUniform outputOne outputTwo := by
  intro C rounds
  have hrelated := G.beliefsAfter_related outputOne outputTwo C rounds
  constructor
  · intro left hleft right hright
    exact C.outputOne_eq (hrelated.1 left hleft right hright)
  · intro left hleft right hright
    exact C.outputTwo_eq (hrelated.2 left hleft right hright)

end FiniteGlobalRoundMachine

end DistributedSynthesis
