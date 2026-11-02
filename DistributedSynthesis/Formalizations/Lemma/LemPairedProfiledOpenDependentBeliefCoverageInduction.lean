/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenDependentBeliefPresentation

/-!
# Inductive coverage of dependent physical candidates

`profiledOpen_reachableBeliefsUniform_of_dependentCandidateCoverage` reduces
output uniformity to two coverage statements over `beliefsAfter`.  This file
gives the honest one-round induction interface for proving exactly those
statements.

The frame used after the actual finite history is proof-side data.  A blind
transition must cover every hidden partner input in that one common frame.  A
receive transition must cover both graphs compatible with the receiver's
local event (`left`/`both` for process one and `right`/`both` for process
two).  Thus no field chooses an orientation, leader, hidden input, row,
member, or root.

The model-specific content is now four one-step representation laws.  In
particular, if one local belief can contain outputs arising from different
current descriptors, the relevant law must prove that all of them are
represented by candidates of the single next frame.  The same-current pair
theorem does not silently discharge that cross-current obligation.
-/

namespace DistributedSynthesis

universe i u v w x y s

namespace DetParityAutomaton

variable {I : Type i}
variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Fintype I] [Inhabited I]
variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
  [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

variable (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
variable (hwin : ∀ env : EnvironmentSequence In₁ In₂,
  A.Accepts (execution strategy env))
variable (basis : ∀ state : PairedProfiledTreeState A,
  (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
variable (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))

private abbrev BeliefFrame :=
  ProfiledOpenWitnessedBeliefFrame A initialCode

private abbrev BeliefCandidate :=
  ProfiledOpenWitnessedBeliefCandidate A strategy hwin basis initialCode

/-- A small parser-stable constructor used in the dependent recurrence
fields below. -/
private def beliefRound (inputOne : In₁) (inputTwo : In₂) (graph : Graph) :
    EnvironmentRound In₁ In₂ :=
  { inputOne := inputOne
    inputTwo := inputTwo
    graph := graph }

/-- Induction data for representing every state in both local beliefs by a
retained dependent physical candidate.

`RepresentedOne` and `RepresentedTwo` may contain arbitrary proof-side
semantic invariants in addition to output equality.  This is necessary for
induction: output equality alone carries no successor provenance. -/
structure ProfiledOpenDependentCandidateCoverageRecurrence
    (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂) where
  frameOne : List (EnvironmentRound In₁ In₂) →
    BeliefFrame A initialCode
  frameTwo : List (EnvironmentRound In₁ In₂) →
    BeliefFrame A initialCode
  RepresentedOne : List (EnvironmentRound In₁ In₂) →
    G.State → BeliefCandidate A strategy hwin basis initialCode → Prop
  RepresentedTwo : List (EnvironmentRound In₁ In₂) →
    G.State → BeliefCandidate A strategy hwin basis initialCode → Prop
  initialOne : ∃ candidate ∈
      profiledOpenWitnessedBeliefCandidates A strategy hwin basis initialCode
        (frameOne []),
    RepresentedOne [] G.initial candidate
  initialTwo : ∃ candidate ∈
      profiledOpenWitnessedBeliefCandidates A strategy hwin basis initialCode
        (frameTwo []),
    RepresentedTwo [] G.initial candidate
  /-- Process one does not receive: the next common frame covers every
  partner input hidden behind the actual strict-right observation. -/
  noRecvOne : ∀ rounds source sourceCandidate,
    RepresentedOne rounds source sourceCandidate →
      ∀ (inputOne : In₁) (actualInputTwo hiddenInputTwo : In₂),
        ∃ target ∈
            profiledOpenWitnessedBeliefCandidates A strategy hwin basis
              initialCode
              (frameOne (rounds ++
                [beliefRound inputOne actualInputTwo .right])),
          RepresentedOne
            (rounds ++
              [beliefRound inputOne actualInputTwo .right])
            (G.step source
              (beliefRound inputOne hiddenInputTwo .right)) target
  /-- Process two blind-step mirror. -/
  noRecvTwo : ∀ rounds source sourceCandidate,
    RepresentedTwo rounds source sourceCandidate →
      ∀ (actualInputOne hiddenInputOne : In₁) (inputTwo : In₂),
        ∃ target ∈
            profiledOpenWitnessedBeliefCandidates A strategy hwin basis
              initialCode
              (frameTwo (rounds ++
                [beliefRound actualInputOne inputTwo .left])),
          RepresentedTwo
            (rounds ++
              [beliefRound actualInputOne inputTwo .left])
            (G.step source
              (beliefRound hiddenInputOne inputTwo .left)) target
  /-- Process one receives.  `actualGraph` selects only the proof frame;
  `compatibleGraph` ranges over both locally indistinguishable receive
  graphs. -/
  recvOne : ∀ rounds source oneCandidate twoCandidate,
    RepresentedOne rounds source oneCandidate →
      RepresentedTwo rounds source twoCandidate →
      ∀ (inputOne : In₁) (inputTwo : In₂)
        (actualGraph compatibleGraph : Graph),
        (actualGraph = .left ∨ actualGraph = .both) →
        (compatibleGraph = .left ∨ compatibleGraph = .both) →
          ∃ target ∈
              profiledOpenWitnessedBeliefCandidates A strategy hwin basis
                initialCode
                (frameOne (rounds ++
                  [beliefRound inputOne inputTwo actualGraph])),
            RepresentedOne
              (rounds ++
                [beliefRound inputOne inputTwo actualGraph])
              (G.step source
                (beliefRound inputOne inputTwo compatibleGraph)) target
  /-- Process-two receive mirror. -/
  recvTwo : ∀ rounds source oneCandidate twoCandidate,
    RepresentedOne rounds source oneCandidate →
      RepresentedTwo rounds source twoCandidate →
      ∀ (inputOne : In₁) (inputTwo : In₂)
        (actualGraph compatibleGraph : Graph),
        (actualGraph = .right ∨ actualGraph = .both) →
        (compatibleGraph = .right ∨ compatibleGraph = .both) →
          ∃ target ∈
              profiledOpenWitnessedBeliefCandidates A strategy hwin basis
                initialCode
                (frameTwo (rounds ++
                  [beliefRound inputOne inputTwo actualGraph])),
            RepresentedTwo
              (rounds ++
                [beliefRound inputOne inputTwo actualGraph])
              (G.step source
                (beliefRound inputOne inputTwo compatibleGraph)) target
  outputOne_eq : ∀ {rounds state candidate},
    RepresentedOne rounds state candidate →
      outputOne state =
        (profiledOpenWitnessedBeliefCandidateOutput A strategy hwin basis
          initialCode candidate).1
  outputTwo_eq : ∀ {rounds state candidate},
    RepresentedTwo rounds state candidate →
      outputTwo state =
        (profiledOpenWitnessedBeliefCandidateOutput A strategy hwin basis
          initialCode candidate).2

namespace ProfiledOpenDependentCandidateCoverageRecurrence

variable {G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂}
variable {outputOne : G.State → Out₁} {outputTwo : G.State → Out₂}

/-- The six honest one-round laws imply simultaneous candidate coverage of
both complete reachable local beliefs after every finite history. -/
theorem represented_beliefs
    (R : ProfiledOpenDependentCandidateCoverageRecurrence A strategy hwin
      basis initialCode G outputOne outputTwo)
    (rounds : List (EnvironmentRound In₁ In₂)) :
    (∀ state ∈ (G.beliefsAfter rounds).1,
      ∃ candidate ∈
          profiledOpenWitnessedBeliefCandidates A strategy hwin basis
            initialCode (R.frameOne rounds),
        R.RepresentedOne rounds state candidate) ∧
    (∀ state ∈ (G.beliefsAfter rounds).2,
      ∃ candidate ∈
          profiledOpenWitnessedBeliefCandidates A strategy hwin basis
            initialCode (R.frameTwo rounds),
        R.RepresentedTwo rounds state candidate) := by
  classical
  induction rounds using List.reverseRecOn with
  | nil =>
      constructor
      · intro state hstate
        simp [FiniteGlobalRoundMachine.beliefsAfter] at hstate
        subst state
        exact R.initialOne
      · intro state hstate
        simp [FiniteGlobalRoundMachine.beliefsAfter] at hstate
        subst state
        exact R.initialTwo
  | append_singleton rounds round ih =>
      rcases round with ⟨inputOne, inputTwo, graph⟩
      cases graph with
      | left =>
          constructor
          · intro target htarget
            simp only [FiniteGlobalRoundMachine.beliefsAfter,
              List.foldl_append, List.foldl_cons, List.foldl_nil,
              FiniteGlobalRoundMachine.beliefAdvance,
              FiniteGlobalRoundMachine.beliefRecvOne, Finset.mem_filter,
              Finset.mem_univ, true_and] at htarget
            rcases htarget with ⟨source, hself, hother, hstep⟩
            rcases ih.1 source hself with
              ⟨oneCandidate, _honeMem, honeRep⟩
            rcases ih.2 source hother with
              ⟨twoCandidate, _htwoMem, htwoRep⟩
            rcases hstep with rfl | rfl
            · exact R.recvOne rounds source oneCandidate twoCandidate honeRep
                htwoRep inputOne inputTwo .left .left (Or.inl rfl)
                  (Or.inl rfl)
            · exact R.recvOne rounds source oneCandidate twoCandidate honeRep
                htwoRep inputOne inputTwo .left .both (Or.inl rfl)
                  (Or.inr rfl)
          · intro target htarget
            simp only [FiniteGlobalRoundMachine.beliefsAfter,
              List.foldl_append, List.foldl_cons, List.foldl_nil,
              FiniteGlobalRoundMachine.beliefAdvance,
              FiniteGlobalRoundMachine.beliefNoRecvTwo, Finset.mem_filter,
              Finset.mem_univ, true_and] at htarget
            rcases htarget with ⟨source, hsource, hiddenInputOne, rfl⟩
            rcases ih.2 source hsource with
              ⟨sourceCandidate, _hsourceMem, hsourceRep⟩
            exact R.noRecvTwo rounds source sourceCandidate hsourceRep inputOne
              hiddenInputOne inputTwo
      | right =>
          constructor
          · intro target htarget
            simp only [FiniteGlobalRoundMachine.beliefsAfter,
              List.foldl_append, List.foldl_cons, List.foldl_nil,
              FiniteGlobalRoundMachine.beliefAdvance,
              FiniteGlobalRoundMachine.beliefNoRecvOne, Finset.mem_filter,
              Finset.mem_univ, true_and] at htarget
            rcases htarget with ⟨source, hsource, hiddenInputTwo, rfl⟩
            rcases ih.1 source hsource with
              ⟨sourceCandidate, _hsourceMem, hsourceRep⟩
            exact R.noRecvOne rounds source sourceCandidate hsourceRep inputOne
              inputTwo hiddenInputTwo
          · intro target htarget
            simp only [FiniteGlobalRoundMachine.beliefsAfter,
              List.foldl_append, List.foldl_cons, List.foldl_nil,
              FiniteGlobalRoundMachine.beliefAdvance,
              FiniteGlobalRoundMachine.beliefRecvTwo, Finset.mem_filter,
              Finset.mem_univ, true_and] at htarget
            rcases htarget with ⟨source, hself, hother, hstep⟩
            rcases ih.1 source hother with
              ⟨oneCandidate, _honeMem, honeRep⟩
            rcases ih.2 source hself with
              ⟨twoCandidate, _htwoMem, htwoRep⟩
            rcases hstep with rfl | rfl
            · exact R.recvTwo rounds source oneCandidate twoCandidate honeRep
                htwoRep inputOne inputTwo .right .right (Or.inl rfl)
                  (Or.inl rfl)
            · exact R.recvTwo rounds source oneCandidate twoCandidate honeRep
                htwoRep inputOne inputTwo .right .both (Or.inl rfl)
                  (Or.inr rfl)
      | both =>
          constructor
          · intro target htarget
            simp only [FiniteGlobalRoundMachine.beliefsAfter,
              List.foldl_append, List.foldl_cons, List.foldl_nil,
              FiniteGlobalRoundMachine.beliefAdvance,
              FiniteGlobalRoundMachine.beliefRecvOne, Finset.mem_filter,
              Finset.mem_univ, true_and] at htarget
            rcases htarget with ⟨source, hself, hother, hstep⟩
            rcases ih.1 source hself with
              ⟨oneCandidate, _honeMem, honeRep⟩
            rcases ih.2 source hother with
              ⟨twoCandidate, _htwoMem, htwoRep⟩
            rcases hstep with rfl | rfl
            · exact R.recvOne rounds source oneCandidate twoCandidate honeRep
                htwoRep inputOne inputTwo .both .left (Or.inr rfl)
                  (Or.inl rfl)
            · exact R.recvOne rounds source oneCandidate twoCandidate honeRep
                htwoRep inputOne inputTwo .both .both (Or.inr rfl)
                  (Or.inr rfl)
          · intro target htarget
            simp only [FiniteGlobalRoundMachine.beliefsAfter,
              List.foldl_append, List.foldl_cons, List.foldl_nil,
              FiniteGlobalRoundMachine.beliefAdvance,
              FiniteGlobalRoundMachine.beliefRecvTwo, Finset.mem_filter,
              Finset.mem_univ, true_and] at htarget
            rcases htarget with ⟨source, hself, hother, hstep⟩
            rcases ih.1 source hother with
              ⟨oneCandidate, _honeMem, honeRep⟩
            rcases ih.2 source hself with
              ⟨twoCandidate, _htwoMem, htwoRep⟩
            rcases hstep with rfl | rfl
            · exact R.recvTwo rounds source oneCandidate twoCandidate honeRep
                htwoRep inputOne inputTwo .both .right (Or.inr rfl)
                  (Or.inl rfl)
            · exact R.recvTwo rounds source oneCandidate twoCandidate honeRep
                htwoRep inputOne inputTwo .both .both (Or.inr rfl)
                  (Or.inr rfl)

/-- The inductive representation immediately supplies the two exact coverage
hypotheses consumed by the dependent candidate presentation. -/
theorem output_coverage
    (R : ProfiledOpenDependentCandidateCoverageRecurrence A strategy hwin
      basis initialCode G outputOne outputTwo) :
    (∀ rounds state, state ∈ (G.beliefsAfter rounds).1 →
      ∃ candidate ∈
          profiledOpenWitnessedBeliefCandidates A strategy hwin basis
            initialCode (R.frameOne rounds),
        outputOne state =
          (profiledOpenWitnessedBeliefCandidateOutput A strategy hwin basis
            initialCode candidate).1) ∧
    (∀ rounds state, state ∈ (G.beliefsAfter rounds).2 →
      ∃ candidate ∈
          profiledOpenWitnessedBeliefCandidates A strategy hwin basis
            initialCode (R.frameTwo rounds),
        outputTwo state =
          (profiledOpenWitnessedBeliefCandidateOutput A strategy hwin basis
            initialCode candidate).2) := by
  constructor
  · intro rounds state hstate
    rcases (R.represented_beliefs A strategy hwin basis initialCode rounds).1
        state hstate with ⟨candidate, hmem, hrep⟩
    exact ⟨candidate, hmem, R.outputOne_eq hrep⟩
  · intro rounds state hstate
    rcases (R.represented_beliefs A strategy hwin basis initialCode rounds).2
        state hstate with ⟨candidate, hmem, hrep⟩
    exact ⟨candidate, hmem, R.outputTwo_eq hrep⟩

/-- One-arrow closure of reachable-belief uniformity from the induction
interface. -/
theorem reachableBeliefsUniform
    (R : ProfiledOpenDependentCandidateCoverageRecurrence A strategy hwin
      basis initialCode G outputOne outputTwo) :
    G.ReachableBeliefsUniform outputOne outputTwo := by
  rcases R.output_coverage A strategy hwin basis initialCode with
    ⟨hcoverOne, hcoverTwo⟩
  exact profiledOpen_reachableBeliefsUniform_of_dependentCandidateCoverage A
    strategy hwin basis initialCode G outputOne outputTwo R.frameOne R.frameTwo
      hcoverOne hcoverTwo

end ProfiledOpenDependentCandidateCoverageRecurrence

end

end DetParityAutomaton

end DistributedSynthesis
