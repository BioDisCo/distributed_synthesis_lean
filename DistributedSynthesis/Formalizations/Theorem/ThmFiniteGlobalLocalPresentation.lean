/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmFiniteGlobalBeliefSummary

/-!
# Presenting finite global beliefs by genuinely local controls

A fixed relation on global states is unnecessarily strong for overlap
constructions: the local meaning of a hidden global state depends on the
finite overlap control currently carried by the process.  This file gives the
history-indexed formulation.

Two finite local controls evolve by local no-receive tables and a joint
receive table.  `RepOne c s` and `RepTwo c s` say that the global state `s` is
represented by the current local control.  Four one-round simulation laws
imply that every state in each reachable global belief is represented by the
corresponding local control.  Since representation fixes the Moore output,
reachable beliefs are output-uniform.
-/

namespace DistributedSynthesis

universe u v w x y a b

namespace FiniteGlobalRoundMachine

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable [Fintype In₁] [Fintype In₂]
variable (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
variable (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)

/-- A genuinely local presentation of a finite global round machine.  The
receive table sees both delivered local controls and both current inputs, but
neither table sees the current graph. -/
structure LocalPresentation where
  ControlOne : Type a
  ControlTwo : Type b
  initialOne : ControlOne
  initialTwo : ControlTwo
  localOutputOne : ControlOne → Out₁
  localOutputTwo : ControlTwo → Out₂
  noRecvOne : ControlOne → In₁ → ControlOne
  noRecvTwo : ControlTwo → In₂ → ControlTwo
  recv : ControlOne → ControlTwo → In₁ → In₂ → ControlOne × ControlTwo
  RepOne : ControlOne → G.State → Prop
  RepTwo : ControlTwo → G.State → Prop
  initialRepOne : RepOne initialOne G.initial
  initialRepTwo : RepTwo initialTwo G.initial
  outputOne_eq : ∀ {control state}, RepOne control state →
    outputOne state = localOutputOne control
  outputTwo_eq : ∀ {control state}, RepTwo control state →
    outputTwo state = localOutputTwo control
  noRecvOne_rep : ∀ {control state}, RepOne control state →
    ∀ (inputOne : In₁) (hidden : In₂),
      RepOne (noRecvOne control inputOne)
        (G.step state
          { inputOne := inputOne, inputTwo := hidden, graph := .right })
  noRecvTwo_rep : ∀ {control state}, RepTwo control state →
    ∀ (inputTwo : In₂) (hidden : In₁),
      RepTwo (noRecvTwo control inputTwo)
        (G.step state
          { inputOne := hidden, inputTwo := inputTwo, graph := .left })
  recvOne_rep : ∀ {one two state}, RepOne one state → RepTwo two state →
    ∀ (inputOne : In₁) (inputTwo : In₂) (graph : Graph),
      (graph = .left ∨ graph = .both) →
      RepOne (recv one two inputOne inputTwo).1
        (G.step state
          { inputOne := inputOne, inputTwo := inputTwo, graph := graph })
  recvTwo_rep : ∀ {one two state}, RepOne one state → RepTwo two state →
    ∀ (inputOne : In₁) (inputTwo : In₂) (graph : Graph),
      (graph = .right ∨ graph = .both) →
      RepTwo (recv one two inputOne inputTwo).2
        (G.step state
          { inputOne := inputOne, inputTwo := inputTwo, graph := graph })

namespace LocalPresentation

variable (P : G.LocalPresentation outputOne outputTwo)

/-- The two local controls after one real environment round. -/
def advance (pair : P.ControlOne × P.ControlTwo)
    (round : EnvironmentRound In₁ In₂) : P.ControlOne × P.ControlTwo :=
  match round.graph with
  | .left =>
      ((P.recv pair.1 pair.2 round.inputOne round.inputTwo).1,
        P.noRecvTwo pair.2 round.inputTwo)
  | .right =>
      (P.noRecvOne pair.1 round.inputOne,
        (P.recv pair.1 pair.2 round.inputOne round.inputTwo).2)
  | .both => P.recv pair.1 pair.2 round.inputOne round.inputTwo

/-- Local controls reached after a finite real environment prefix. -/
def controlsAfter (rounds : List (EnvironmentRound In₁ In₂)) :
    P.ControlOne × P.ControlTwo :=
  rounds.foldl P.advance (P.initialOne, P.initialTwo)

/-- Every state in the two current beliefs is represented by the respective
current local control. -/
theorem controlsAfter_represent_beliefs
    (rounds : List (EnvironmentRound In₁ In₂)) :
    (∀ state ∈ (G.beliefsAfter rounds).1,
      P.RepOne
        (LocalPresentation.controlsAfter G outputOne outputTwo P rounds).1
        state) ∧
    (∀ state ∈ (G.beliefsAfter rounds).2,
      P.RepTwo
        (LocalPresentation.controlsAfter G outputOne outputTwo P rounds).2
        state) := by
  classical
  induction rounds using List.reverseRecOn with
  | nil =>
      constructor
      · intro state hstate
        simp [FiniteGlobalRoundMachine.beliefsAfter] at hstate
        subst state
        simpa [LocalPresentation.controlsAfter] using P.initialRepOne
      · intro state hstate
        simp [FiniteGlobalRoundMachine.beliefsAfter] at hstate
        subst state
        simpa [LocalPresentation.controlsAfter] using P.initialRepTwo
  | append_singleton rounds round ih =>
      rcases round with ⟨inputOne, inputTwo, graph⟩
      cases graph with
      | left =>
          constructor
          · intro state hstate
            simp only [FiniteGlobalRoundMachine.beliefsAfter,
              List.foldl_append, List.foldl_cons, List.foldl_nil,
              LocalPresentation.controlsAfter, LocalPresentation.advance,
              FiniteGlobalRoundMachine.beliefAdvance,
              FiniteGlobalRoundMachine.beliefRecvOne, Finset.mem_filter,
              Finset.mem_univ, true_and] at hstate ⊢
            rcases hstate with ⟨source, hself, hother, hgraph⟩
            rcases hgraph with rfl | rfl
            · exact P.recvOne_rep (ih.1 source hself) (ih.2 source hother)
                inputOne inputTwo .left (Or.inl rfl)
            · exact P.recvOne_rep (ih.1 source hself) (ih.2 source hother)
                inputOne inputTwo .both (Or.inr rfl)
          · intro state hstate
            simp only [FiniteGlobalRoundMachine.beliefsAfter,
              List.foldl_append, List.foldl_cons, List.foldl_nil,
              LocalPresentation.controlsAfter, LocalPresentation.advance,
              FiniteGlobalRoundMachine.beliefAdvance,
              FiniteGlobalRoundMachine.beliefNoRecvTwo, Finset.mem_filter,
              Finset.mem_univ, true_and] at hstate ⊢
            rcases hstate with ⟨source, hsource, hidden, rfl⟩
            exact P.noRecvTwo_rep (ih.2 source hsource) inputTwo hidden
      | right =>
          constructor
          · intro state hstate
            simp only [FiniteGlobalRoundMachine.beliefsAfter,
              List.foldl_append, List.foldl_cons, List.foldl_nil,
              LocalPresentation.controlsAfter, LocalPresentation.advance,
              FiniteGlobalRoundMachine.beliefAdvance,
              FiniteGlobalRoundMachine.beliefNoRecvOne, Finset.mem_filter,
              Finset.mem_univ, true_and] at hstate ⊢
            rcases hstate with ⟨source, hsource, hidden, rfl⟩
            exact P.noRecvOne_rep (ih.1 source hsource) inputOne hidden
          · intro state hstate
            simp only [FiniteGlobalRoundMachine.beliefsAfter,
              List.foldl_append, List.foldl_cons, List.foldl_nil,
              LocalPresentation.controlsAfter, LocalPresentation.advance,
              FiniteGlobalRoundMachine.beliefAdvance,
              FiniteGlobalRoundMachine.beliefRecvTwo, Finset.mem_filter,
              Finset.mem_univ, true_and] at hstate ⊢
            rcases hstate with ⟨source, hself, hother, hgraph⟩
            rcases hgraph with rfl | rfl
            · exact P.recvTwo_rep (ih.1 source hother) (ih.2 source hself)
                inputOne inputTwo .right (Or.inl rfl)
            · exact P.recvTwo_rep (ih.1 source hother) (ih.2 source hself)
                inputOne inputTwo .both (Or.inr rfl)
      | both =>
          constructor
          · intro state hstate
            simp only [FiniteGlobalRoundMachine.beliefsAfter,
              List.foldl_append, List.foldl_cons, List.foldl_nil,
              LocalPresentation.controlsAfter, LocalPresentation.advance,
              FiniteGlobalRoundMachine.beliefAdvance,
              FiniteGlobalRoundMachine.beliefRecvOne, Finset.mem_filter,
              Finset.mem_univ, true_and] at hstate ⊢
            rcases hstate with ⟨source, hself, hother, hgraph⟩
            rcases hgraph with rfl | rfl
            · exact P.recvOne_rep (ih.1 source hself) (ih.2 source hother)
                inputOne inputTwo .left (Or.inl rfl)
            · exact P.recvOne_rep (ih.1 source hself) (ih.2 source hother)
                inputOne inputTwo .both (Or.inr rfl)
          · intro state hstate
            simp only [FiniteGlobalRoundMachine.beliefsAfter,
              List.foldl_append, List.foldl_cons, List.foldl_nil,
              LocalPresentation.controlsAfter, LocalPresentation.advance,
              FiniteGlobalRoundMachine.beliefAdvance,
              FiniteGlobalRoundMachine.beliefRecvTwo, Finset.mem_filter,
              Finset.mem_univ, true_and] at hstate ⊢
            rcases hstate with ⟨source, hself, hother, hgraph⟩
            rcases hgraph with rfl | rfl
            · exact P.recvTwo_rep (ih.1 source hother) (ih.2 source hself)
                inputOne inputTwo .right (Or.inl rfl)
            · exact P.recvTwo_rep (ih.1 source hother) (ih.2 source hself)
                inputOne inputTwo .both (Or.inr rfl)

/-- A local presentation closes the reachable-belief uniformity gate. -/
theorem reachableBeliefsUniform :
    (P : G.LocalPresentation outputOne outputTwo) →
    G.ReachableBeliefsUniform outputOne outputTwo := by
  intro P rounds
  have hrep := LocalPresentation.controlsAfter_represent_beliefs
    G outputOne outputTwo P rounds
  constructor
  · intro left hleft right hright
    exact (P.outputOne_eq (hrep.1 left hleft)).trans
      (P.outputOne_eq (hrep.1 right hright)).symm
  · intro left hleft right hright
    exact (P.outputTwo_eq (hrep.2 left hleft)).trans
      (P.outputTwo_eq (hrep.2 right hright)).symm

end LocalPresentation

end FiniteGlobalRoundMachine

end DistributedSynthesis
