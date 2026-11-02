/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmDynamicHierarchyFiniteState

/-!
# Information-rank signals for two-player dynamic hierarchy

This is the first constructive component of Berwanger--Mathew--van den
Bogaard, Theorem 10 (Lemma 11 in the cited paper).  For two players, rank zero
is the most-informed role; ties are broken in favour of player one.  We prove
that each player's rank is determined by that player's own perfect-recall
observation history.  The subsequent file will implement these signals by a
finite automaton.
-/

namespace DistributedSynthesis

universe u

noncomputable section

namespace FiniteConcurrentGame

variable (G : FiniteConcurrentGame.{u})

/-- `OneDeterminesTwoAt` depends only on player one's information class. -/
theorem oneDeterminesTwoAt_congr_observations1
    (history alternative : G.PlayHistory)
    (heq : history.observations1 = alternative.observations1) :
    G.OneDeterminesTwoAt history ↔ G.OneDeterminesTwoAt alternative := by
  constructor
  · intro hdet candidate hcand
    have hAltTwo : alternative.observations2 = history.observations2 :=
      hdet alternative heq.symm
    have hCandidateTwo : candidate.observations2 = history.observations2 :=
      hdet candidate (hcand.trans heq.symm)
    exact hCandidateTwo.trans hAltTwo.symm
  · intro hdet candidate hcand
    have hHistoryTwo : history.observations2 = alternative.observations2 :=
      hdet history heq
    have hCandidateTwo : candidate.observations2 = alternative.observations2 :=
      hdet candidate (hcand.trans heq)
    exact hCandidateTwo.trans hHistoryTwo.symm

/-- `TwoDeterminesOneAt` depends only on player two's information class. -/
theorem twoDeterminesOneAt_congr_observations2
    (history alternative : G.PlayHistory)
    (heq : history.observations2 = alternative.observations2) :
    G.TwoDeterminesOneAt history ↔ G.TwoDeterminesOneAt alternative := by
  constructor
  · intro hdet candidate hcand
    have hAltOne : alternative.observations1 = history.observations1 :=
      hdet alternative heq.symm
    have hCandidateOne : candidate.observations1 = history.observations1 :=
      hdet candidate (hcand.trans heq.symm)
    exact hCandidateOne.trans hAltOne.symm
  · intro hdet candidate hcand
    have hHistoryOne : history.observations1 = alternative.observations1 :=
      hdet history heq
    have hCandidateOne : candidate.observations1 = alternative.observations1 :=
      hdet candidate (hcand.trans heq)
    exact hCandidateOne.trans hHistoryOne.symm

/-- Under dynamic hierarchy, player one's determining status is also stable
inside a player-two information class.  If player two determines player one,
equal player-two histories first imply equal player-one histories; otherwise
dynamic hierarchy forces player one to determine player two on both sides. -/
theorem oneDeterminesTwoAt_congr_observations2_of_dynamic
    (hhier : G.DynamicHierarchy)
    (history alternative : G.PlayHistory)
    (heq : history.observations2 = alternative.observations2) :
    G.OneDeterminesTwoAt history ↔ G.OneDeterminesTwoAt alternative := by
  have htwo :=
    G.twoDeterminesOneAt_congr_observations2 history alternative heq
  by_cases hdetTwo : G.TwoDeterminesOneAt history
  · have hobsOne : history.observations1 = alternative.observations1 :=
      (hdetTwo alternative heq.symm).symm
    exact G.oneDeterminesTwoAt_congr_observations1 history alternative hobsOne
  · have hdetTwoAlt : ¬ G.TwoDeterminesOneAt alternative := by
      rwa [← htwo]
    have hone : G.OneDeterminesTwoAt history :=
      (hhier history).resolve_right hdetTwo
    have honeAlt : G.OneDeterminesTwoAt alternative :=
      (hhier alternative).resolve_right hdetTwoAlt
    exact ⟨fun _ => honeAlt, fun _ => hone⟩

/-- Rank of player one: most informed (`0`) whenever player one determines
player two; ties are therefore awarded to player one. -/
noncomputable def informationRankOne (history : G.PlayHistory) : Fin 2 :=
  by
    classical
    exact if G.OneDeterminesTwoAt history then 0 else 1

/-- Rank of player two, complementary to the tie-broken rank of player one. -/
noncomputable def informationRankTwo (history : G.PlayHistory) : Fin 2 :=
  by
    classical
    exact if G.OneDeterminesTwoAt history then 1 else 0

/-- Player one's rank signal is information-consistent to player one. -/
theorem informationRankOne_consistent
    (history alternative : G.PlayHistory)
    (heq : history.observations1 = alternative.observations1) :
    G.informationRankOne history = G.informationRankOne alternative := by
  unfold informationRankOne
  rw [G.oneDeterminesTwoAt_congr_observations1 history alternative heq]

/-- Under dynamic hierarchy, player two's rank signal is
information-consistent to player two. -/
theorem informationRankTwo_consistent
    (hhier : G.DynamicHierarchy)
    (history alternative : G.PlayHistory)
    (heq : history.observations2 = alternative.observations2) :
    G.informationRankTwo history = G.informationRankTwo alternative := by
  unfold informationRankTwo
  rw [G.oneDeterminesTwoAt_congr_observations2_of_dynamic
    hhier history alternative heq]

/-- The two tie-broken ranks always form the permutation `(0,1)` or `(1,0)`. -/
theorem informationRank_complementary (history : G.PlayHistory) :
    (G.informationRankOne history = 0 ∧ G.informationRankTwo history = 1) ∨
      (G.informationRankOne history = 1 ∧ G.informationRankTwo history = 0) := by
  unfold informationRankOne informationRankTwo
  by_cases h : G.OneDeterminesTwoAt history <;> simp [h]

end FiniteConcurrentGame

end

end DistributedSynthesis
