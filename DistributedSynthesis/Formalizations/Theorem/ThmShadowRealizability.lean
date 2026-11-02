/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmTwoPlayerShadowGame
import DistributedSynthesis.Formalizations.Theorem.ThmCommonSignalRealizability

/-!
# Realizability transfer across the rank-permuted shadow reduction

The generic layer of the shadow-game transfer: whenever a base strategy pair
and a shadow strategy pair agree along shadow lifts (the shadow pair plays the
rank-correct permutation of the base pair's actions), the shadow play under any
Nature is the `shadowLift` of the base play, round for round -- same clock, no
time dilation -- so priorities coincide and wins transfer in both directions.
The invalid-action sink is handled separately: a shadow pair that ever breaks
the action shape along its own play loses outright (the sink is absorbing with
odd priority), so a *winning* shadow pair always respects shapes.

The information-theoretic strategy constructions (building the shadow pair from
a base pair and conversely, and the Moore back-transfer) are specific to the
common-signal arena and live in the follow-up sections.
-/

namespace DistributedSynthesis

universe u

namespace FiniteConcurrentGame

variable (G : FiniteConcurrentGame.{u})

attribute [instance] FiniteConcurrentGame.stateFinite
  FiniteConcurrentGame.action1Finite FiniteConcurrentGame.action2Finite
  FiniteConcurrentGame.natureFinite FiniteConcurrentGame.observation1Finite
  FiniteConcurrentGame.observation2Finite

/-- **The shadow play correspondence.**  If the shadow pair plays exactly the
rank-correct permutation of the base pair's actions along lifted views, the
shadow play is the `shadowLift` of the base play -- as full histories. -/
theorem shadow_play_correspondence (leaderOne : G.ShadowLeaderSignal)
    (σ : G.HistoryProductStrategy)
    (τ : (G.twoPlayerShadowGame leaderOne).HistoryProductStrategy)
    (hagree : ∀ h : G.PlayHistory,
      (τ.1 (G.shadowView1 leaderOne h), τ.2 (G.shadowView2 leaderOne h)) =
        G.shadowActionProfile leaderOne h.lastState
          (σ.1 h.observations1) (σ.2 h.observations2))
    (nature : Nat -> G.Nature) (n : Nat) :
    (G.twoPlayerShadowGame leaderOne).playHistory τ nature n =
      G.shadowLift leaderOne (G.playHistory σ nature n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hstep : G.playHistory σ nature (n + 1) =
          (G.playHistory σ nature n).step
            (σ.1 (G.playHistory σ nature n).observations1)
            (σ.2 (G.playHistory σ nature n).observations2) (nature n) := by
        rw [playHistory, G.playHistory_observations1 σ nature n,
          G.playHistory_observations2 σ nature n]
      have hview1 : ((G.twoPlayerShadowGame leaderOne).strategyState τ nature
            n).2.1 = G.shadowView1 leaderOne (G.playHistory σ nature n) := by
        rw [← (G.twoPlayerShadowGame leaderOne).playHistory_observations1
          τ nature n, ih, G.shadowLift_observations1]
      have hview2 : ((G.twoPlayerShadowGame leaderOne).strategyState τ nature
            n).2.2 = G.shadowView2 leaderOne (G.playHistory σ nature n) := by
        rw [← (G.twoPlayerShadowGame leaderOne).playHistory_observations2
          τ nature n, ih, G.shadowLift_observations2]
      show ((G.twoPlayerShadowGame leaderOne).playHistory τ nature n).step
          (τ.1 ((G.twoPlayerShadowGame leaderOne).strategyState τ nature n).2.1)
          (τ.2 ((G.twoPlayerShadowGame leaderOne).strategyState τ nature n).2.2)
          (nature n) = _
      rw [ih, hview1, hview2, hstep, shadowLift]
      have h1 := congrArg Prod.fst (hagree (G.playHistory σ nature n))
      have h2 := congrArg Prod.snd (hagree (G.playHistory σ nature n))
      dsimp only at h1 h2
      rw [h1, h2]

/-- Priorities along corresponding plays coincide. -/
theorem shadow_priority_correspondence (leaderOne : G.ShadowLeaderSignal)
    (σ : G.HistoryProductStrategy)
    (τ : (G.twoPlayerShadowGame leaderOne).HistoryProductStrategy)
    (hagree : ∀ h : G.PlayHistory,
      (τ.1 (G.shadowView1 leaderOne h), τ.2 (G.shadowView2 leaderOne h)) =
        G.shadowActionProfile leaderOne h.lastState
          (σ.1 h.observations1) (σ.2 h.observations2))
    (nature : Nat -> G.Nature) (n : Nat) :
    (G.twoPlayerShadowGame leaderOne).priority
        ((G.twoPlayerShadowGame leaderOne).strategyState τ nature n).1 =
      G.priority (G.strategyState σ nature n).1 := by
  rw [← (G.twoPlayerShadowGame leaderOne).playHistory_lastState τ nature n,
    G.shadow_play_correspondence leaderOne σ τ hagree nature n,
    ← G.playHistory_lastState σ nature n, G.shadowLift_priority]

/-- **Wins transfer along the shadow correspondence, both directions.** -/
theorem shadow_wins_iff_of_agree (leaderOne : G.ShadowLeaderSignal)
    (σ : G.HistoryProductStrategy)
    (τ : (G.twoPlayerShadowGame leaderOne).HistoryProductStrategy)
    (hagree : ∀ h : G.PlayHistory,
      (τ.1 (G.shadowView1 leaderOne h), τ.2 (G.shadowView2 leaderOne h)) =
        G.shadowActionProfile leaderOne h.lastState
          (σ.1 h.observations1) (σ.2 h.observations2)) :
    (G.twoPlayerShadowGame leaderOne).HistoryStrategyWins τ ↔
      G.HistoryStrategyWins σ := by
  have hpri : ∀ nature : Nat -> G.Nature,
      (fun n => (G.twoPlayerShadowGame leaderOne).priority
        ((G.twoPlayerShadowGame leaderOne).strategyState τ nature n).1) =
      (fun n => G.priority (G.strategyState σ nature n).1) := fun nature =>
    funext (G.shadow_priority_correspondence leaderOne σ τ hagree nature)
  constructor
  · intro hwin nature
    have h := hwin nature
    rwa [hpri nature] at h
  · intro hwin nature
    rw [hpri nature]
    exact hwin nature

/-! ### Agreement lemmas at the common-signal arena

The four view-determination facts that make the shadow strategy extraction
well-defined on the actual players' knowledge sets.  Shadow one's view is
determined by either player's view *at histories where that player currently
leads* (the current determination supplies the missing full list); shadow two's
view is determined by either player's view *unconditionally in the current
signal*, prefix-wise (at every prefix the then-leader's data determines the
then-follower's letter). -/

/-- Both views together determine shadow one's view: the mirror of
`commonSignalShadowView2_eq_of_both`. -/
theorem commonSignalShadowView1_eq_of_both
    (left right : G.commonSignalCrossingEliminationGame.PlayHistory)
    (hone : left.observations1 = right.observations1)
    (htwo : left.observations2 = right.observations2) :
    G.commonSignalCrossingEliminationGame.shadowView1
        G.commonSignalLeaderOne left =
      G.commonSignalCrossingEliminationGame.shadowView1
        G.commonSignalLeaderOne right := by
  induction left generalizing right with
  | initial =>
      cases right with
      | initial => rfl
      | step previous actionOne actionTwo nature =>
          have hlength := congrArg List.length hone
          rw [PlayHistory.observations1_step] at hlength
          have hpos :=
            G.commonSignalCrossingEliminationGame.observations1_length_pos previous
          simp only [PlayHistory.observations1_initial, List.length_singleton,
            List.length_append] at hlength
          omega
  | step leftPrevious leftActionOne leftActionTwo leftNature ih =>
      cases right with
      | initial =>
          have hlength := congrArg List.length hone
          rw [PlayHistory.observations1_step] at hlength
          have hpos :=
            G.commonSignalCrossingEliminationGame.observations1_length_pos leftPrevious
          simp only [PlayHistory.observations1_initial, List.length_singleton,
            List.length_append] at hlength
          omega
      | step rightPrevious rightActionOne rightActionTwo rightNature =>
          rw [PlayHistory.observations1_step,
            PlayHistory.observations1_step] at hone
          rw [PlayHistory.observations2_step,
            PlayHistory.observations2_step] at htwo
          obtain ⟨honePrefix, honeLastList⟩ :=
            List.append_inj' hone (by simp)
          obtain ⟨htwoPrefix, htwoLastList⟩ :=
            List.append_inj' htwo (by simp)
          have honeLast := List.singleton_inj.mp honeLastList
          have htwoLast := List.singleton_inj.mp htwoLastList
          have hprefix := ih rightPrevious honePrefix htwoPrefix
          let leftTarget := G.commonSignalCrossingEliminationGame.next
            leftPrevious.lastState leftActionOne leftActionTwo leftNature
          let rightTarget := G.commonSignalCrossingEliminationGame.next
            rightPrevious.lastState rightActionOne rightActionTwo rightNature
          have hleader : G.commonSignalLeaderOne leftTarget =
              G.commonSignalLeaderOne rightTarget :=
            G.commonSignalLeaderOne_eq_of_observe1_eq leftTarget rightTarget
              honeLast
          rw [shadowView1, shadowView1]
          refine congrArg₂ (fun xs x => xs ++ [x]) hprefix ?_
          change
            (G.commonSignalCrossingEliminationGame.twoPlayerShadowGame
              G.commonSignalLeaderOne).observe1 (some leftTarget) =
            (G.commonSignalCrossingEliminationGame.twoPlayerShadowGame
              G.commonSignalLeaderOne).observe1 (some rightTarget)
          cases hleft : G.commonSignalLeaderOne leftTarget
          · have hright : G.commonSignalLeaderOne rightTarget = false := by
              rw [← hleader, hleft]
            simp [twoPlayerShadowGame, hleft, hright]
            exact htwoLast
          · have hright : G.commonSignalLeaderOne rightTarget = true := by
              rw [← hleader, hleft]
            simp [twoPlayerShadowGame, hleft, hright]
            exact honeLast

/-- **A1.**  At a history whose current signal selects player one, player one's
view determines shadow one's view: the current determination supplies the full
second view. -/
theorem commonSignalShadowView1_eq_of_observations1_eq_of_leader
    (hhier : G.DynamicHierarchy)
    (left right : G.commonSignalCrossingEliminationGame.PlayHistory)
    (hsig : G.commonSignalLeaderOne left.lastState = true)
    (heq : left.observations1 = right.observations1) :
    G.commonSignalCrossingEliminationGame.shadowView1
        G.commonSignalLeaderOne left =
      G.commonSignalCrossingEliminationGame.shadowView1
        G.commonSignalLeaderOne right := by
  have hdet := G.commonSignal_selectedDetermines hhier left
  rw [hsig, if_pos rfl] at hdet
  exact G.commonSignalShadowView1_eq_of_both left right heq
    (hdet right heq.symm).symm

/-- **A4.**  At a history whose current signal selects player two, player two's
view determines shadow one's view. -/
theorem commonSignalShadowView1_eq_of_observations2_eq_of_follower
    (hhier : G.DynamicHierarchy)
    (left right : G.commonSignalCrossingEliminationGame.PlayHistory)
    (hsig : G.commonSignalLeaderOne left.lastState = false)
    (heq : left.observations2 = right.observations2) :
    G.commonSignalCrossingEliminationGame.shadowView1
        G.commonSignalLeaderOne left =
      G.commonSignalCrossingEliminationGame.shadowView1
        G.commonSignalLeaderOne right := by
  have hdet := G.commonSignal_selectedDetermines hhier left
  rw [hsig] at hdet
  simp only [Bool.false_eq_true, if_false] at hdet
  exact G.commonSignalShadowView1_eq_of_both left right
    (hdet right heq.symm).symm heq

/-- **A2.**  Player one's view determines shadow two's view, prefix-wise: at
every one-led prefix the current determination supplies the follower letter,
and at two-led prefixes the letter is player one's own observation. -/
theorem commonSignalShadowView2_eq_of_observations1_eq
    (hhier : G.DynamicHierarchy)
    (left right : G.commonSignalCrossingEliminationGame.PlayHistory)
    (hone : left.observations1 = right.observations1) :
    G.commonSignalCrossingEliminationGame.shadowView2
        G.commonSignalLeaderOne left =
      G.commonSignalCrossingEliminationGame.shadowView2
        G.commonSignalLeaderOne right := by
  induction left generalizing right with
  | initial =>
      cases right with
      | initial => rfl
      | step previous actionOne actionTwo nature =>
          have hlength := congrArg List.length hone
          rw [PlayHistory.observations1_step] at hlength
          have hpos :=
            G.commonSignalCrossingEliminationGame.observations1_length_pos previous
          simp only [PlayHistory.observations1_initial, List.length_singleton,
            List.length_append] at hlength
          omega
  | step leftPrevious leftActionOne leftActionTwo leftNature ih =>
      cases right with
      | initial =>
          have hlength := congrArg List.length hone
          rw [PlayHistory.observations1_step] at hlength
          have hpos :=
            G.commonSignalCrossingEliminationGame.observations1_length_pos leftPrevious
          simp only [PlayHistory.observations1_initial, List.length_singleton,
            List.length_append] at hlength
          omega
      | step rightPrevious rightActionOne rightActionTwo rightNature =>
          have honeFull := hone
          rw [PlayHistory.observations1_step,
            PlayHistory.observations1_step] at hone
          obtain ⟨honePrefix, honeLastList⟩ :=
            List.append_inj' hone (by simp)
          have honeLast := List.singleton_inj.mp honeLastList
          have hprefix := ih rightPrevious honePrefix
          let leftTarget := G.commonSignalCrossingEliminationGame.next
            leftPrevious.lastState leftActionOne leftActionTwo leftNature
          let rightTarget := G.commonSignalCrossingEliminationGame.next
            rightPrevious.lastState rightActionOne rightActionTwo rightNature
          have hleader : G.commonSignalLeaderOne leftTarget =
              G.commonSignalLeaderOne rightTarget :=
            G.commonSignalLeaderOne_eq_of_observe1_eq leftTarget rightTarget
              honeLast
          rw [shadowView2, shadowView2]
          refine congrArg₂ (fun xs x => xs ++ [x]) hprefix ?_
          change
            (G.commonSignalCrossingEliminationGame.twoPlayerShadowGame
              G.commonSignalLeaderOne).observe2 (some leftTarget) =
            (G.commonSignalCrossingEliminationGame.twoPlayerShadowGame
              G.commonSignalLeaderOne).observe2 (some rightTarget)
          cases hleft : G.commonSignalLeaderOne leftTarget
          · have hright : G.commonSignalLeaderOne rightTarget = false := by
              rw [← hleader, hleft]
            simp [twoPlayerShadowGame, hleft, hright]
            exact honeLast
          · have hright : G.commonSignalLeaderOne rightTarget = true := by
              rw [← hleader, hleft]
            have hdet := G.commonSignal_selectedDetermines hhier
              (leftPrevious.step leftActionOne leftActionTwo leftNature)
            have hsigStep : G.commonSignalLeaderOne
                (leftPrevious.step leftActionOne leftActionTwo
                  leftNature).lastState = true := hleft
            rw [hsigStep, if_pos rfl] at hdet
            have htwoStep := hdet
              (rightPrevious.step rightActionOne rightActionTwo rightNature)
              honeFull.symm
            have htwoLast := congrArg List.getLast? htwoStep
            rw [PlayHistory.observations2_getLast?_last,
              PlayHistory.observations2_getLast?_last] at htwoLast
            have htwoTargets := Option.some.inj htwoLast
            simp [twoPlayerShadowGame, hleft, hright]
            exact htwoTargets.symm

/-- **The signal is a function of player two's view.**  Under the hierarchy,
two doubled histories with equal player-two views carry the same rank signal at
their last states.  Rep-normalization: at bridge phases the common letter's
shape encodes the signal outright; at original phases the projected base views
determine the rank through the hierarchy dichotomy. -/
theorem commonSignalLeaderOne_eq_of_observations2_eq
    (hhier : G.DynamicHierarchy)
    (left right : G.commonSignalCrossingEliminationGame.PlayHistory)
    (heq : left.observations2 = right.observations2) :
    G.commonSignalLeaderOne left.lastState =
      G.commonSignalLeaderOne right.lastState := by
  obtain ⟨phaseL, hL, repL⟩ := G.exists_commonSignalRep left
  obtain ⟨phaseR, hR, repR⟩ := G.exists_commonSignalRep right
  have hobsL := G.commonSignalRep_observation_normal repL
  have hobsR := G.commonSignalRep_observation_normal repR
  cases phaseL with
  | false =>
      cases phaseR with
      | false =>
          simp only [CommonSignalObservationNormal, Bool.false_eq_true,
            if_false] at hobsL hobsR
          have hcanon : (G.commonSignalLift hL).observations2 =
              (G.commonSignalLift hR).observations2 := by
            rw [← hobsL.2, ← hobsR.2]
            exact heq
          have hbase : hL.observations2 = hR.observations2 :=
            G.commonSignalLift_observations2_injective hhier hL hR hcanon
          have hiff : G.OneDeterminesTwoAt hL ↔ G.OneDeterminesTwoAt hR := by
            constructor
            · intro honeL
              by_contra honeR
              have hone1 : hL.observations1 = hR.observations1 :=
                ((hhier hR).resolve_left honeR) hL hbase
              exact honeR (fun alt halt => by
                rw [← hone1] at halt
                rw [← hbase]
                exact honeL alt halt)
            · intro honeR
              by_contra honeL
              have hone1 : hR.observations1 = hL.observations1 :=
                ((hhier hL).resolve_left honeL) hR hbase.symm
              exact honeL (fun alt halt => by
                rw [← hone1] at halt
                rw [hbase]
                exact honeR alt halt)
          have hstateL : left.lastState = (G.commonSignalLift hL).lastState := by
            rw [G.commonSignalRep_lastState repL, G.commonSignalLift_lastState]
          have hstateR : right.lastState = (G.commonSignalLift hR).lastState := by
            rw [G.commonSignalRep_lastState repR, G.commonSignalLift_lastState]
          rw [hstateL, hstateR]
          cases hl : G.commonSignalLeaderOne (G.commonSignalLift hL).lastState with
          | true =>
              have honeR := hiff.mp
                ((G.commonSignalLeaderOne_lift_iff hL).mp hl)
              exact ((G.commonSignalLeaderOne_lift_iff hR).mpr honeR).symm
          | false =>
              cases hr : G.commonSignalLeaderOne
                  (G.commonSignalLift hR).lastState with
              | false => rfl
              | true =>
                  have honeL := hiff.mpr
                    ((G.commonSignalLeaderOne_lift_iff hR).mp hr)
                  rw [(G.commonSignalLeaderOne_lift_iff hL).mpr honeL] at hl
                  exact hl.symm
      | true =>
          exfalso
          simp only [CommonSignalObservationNormal, Bool.false_eq_true,
            if_false, if_true] at hobsL hobsR
          obtain ⟨pR, aR, bR, cR, hhR, hobs1R, hobs2R⟩ := hobsR
          have hviews : (G.commonSignalLift hL).observations2 =
              (G.commonSignalBridgeLift pR aR bR cR).observations2 := by
            rw [← hobsL.2, ← hobs2R]
            exact heq
          have hlast := congrArg List.getLast? hviews
          rw [PlayHistory.observations2_getLast?_last,
            PlayHistory.observations2_getLast?_last] at hlast
          have hletters := Option.some.inj hlast
          rw [G.commonSignalBridgeLift_observe2] at hletters
          rw [G.commonSignalLift_observe2 hhier] at hletters
          simp at hletters
  | true =>
      cases phaseR with
      | false =>
          exfalso
          simp only [CommonSignalObservationNormal, Bool.false_eq_true,
            if_false, if_true] at hobsL hobsR
          obtain ⟨pL, aL, bL, cL, hhL, hobs1L, hobs2L⟩ := hobsL
          have hviews : (G.commonSignalBridgeLift pL aL bL cL).observations2 =
              (G.commonSignalLift hR).observations2 := by
            rw [← hobs2L, ← hobsR.2]
            exact heq
          have hlast := congrArg List.getLast? hviews
          rw [PlayHistory.observations2_getLast?_last,
            PlayHistory.observations2_getLast?_last] at hlast
          have hletters := Option.some.inj hlast
          rw [G.commonSignalBridgeLift_observe2] at hletters
          rw [G.commonSignalLift_observe2 hhier] at hletters
          simp at hletters
      | true =>
          simp only [CommonSignalObservationNormal, if_true] at hobsL hobsR
          obtain ⟨pL, aL, bL, cL, hhL, hobs1L, hobs2L⟩ := hobsL
          obtain ⟨pR, aR, bR, cR, hhR, hobs1R, hobs2R⟩ := hobsR
          have hviews : (G.commonSignalBridgeLift pL aL bL cL).observations2 =
              (G.commonSignalBridgeLift pR aR bR cR).observations2 := by
            rw [← hobs2L, ← hobs2R]
            exact heq
          have hlast := congrArg List.getLast? hviews
          rw [PlayHistory.observations2_getLast?_last,
            PlayHistory.observations2_getLast?_last] at hlast
          have hletters := Option.some.inj hlast
          rw [G.commonSignalBridgeLift_observe2,
            G.commonSignalBridgeLift_observe2] at hletters
          have hcommon : G.commonBridgeSignalAt (pL.step aL bL cL) =
              G.commonBridgeSignalAt (pR.step aR bR cR) :=
            Sum.inr.inj hletters
          have hziff : (G.informationRankOne (pL.step aL bL cL) = 0) ↔
              (G.informationRankOne (pR.step aR bR cR) = 0) := by
            unfold commonBridgeSignalAt at hcommon
            by_cases hzL : G.informationRankOne (pL.step aL bL cL) = 0 <;>
              by_cases hzR : G.informationRankOne (pR.step aR bR cR) = 0 <;>
                simp [hzL, hzR] at hcommon ⊢
          have hstateL : left.lastState =
              (G.commonSignalBridgeLift pL aL bL cL).lastState := by
            rw [G.commonSignalRep_lastState repL, hhL,
              G.commonSignalBridgeLift_lastState]
          have hstateR : right.lastState =
              (G.commonSignalBridgeLift pR aR bR cR).lastState := by
            rw [G.commonSignalRep_lastState repR, hhR,
              G.commonSignalBridgeLift_lastState]
          rw [hstateL, hstateR]
          have hiff : G.OneDeterminesTwoAt (pL.step aL bL cL) ↔
              G.OneDeterminesTwoAt (pR.step aR bR cR) := by
            rw [← G.informationRankOne_eq_zero_iff,
              ← G.informationRankOne_eq_zero_iff]
            exact hziff
          cases hl : G.commonSignalLeaderOne
              (G.commonSignalBridgeLift pL aL bL cL).lastState with
          | true =>
              have honeR := hiff.mp
                ((G.commonSignalLeaderOne_bridge_iff pL aL bL cL).mp hl)
              exact ((G.commonSignalLeaderOne_bridge_iff pR aR bR cR).mpr
                honeR).symm
          | false =>
              cases hr : G.commonSignalLeaderOne
                  (G.commonSignalBridgeLift pR aR bR cR).lastState with
              | false => rfl
              | true =>
                  have honeL := hiff.mpr
                    ((G.commonSignalLeaderOne_bridge_iff pR aR bR cR).mp hr)
                  rw [(G.commonSignalLeaderOne_bridge_iff pL aL bL cL).mpr
                    honeL] at hl
                  exact hl.symm

/-- **A3.**  Player two's view determines shadow two's view, prefix-wise. -/
theorem commonSignalShadowView2_eq_of_observations2_eq
    (hhier : G.DynamicHierarchy)
    (left right : G.commonSignalCrossingEliminationGame.PlayHistory)
    (htwo : left.observations2 = right.observations2) :
    G.commonSignalCrossingEliminationGame.shadowView2
        G.commonSignalLeaderOne left =
      G.commonSignalCrossingEliminationGame.shadowView2
        G.commonSignalLeaderOne right := by
  induction left generalizing right with
  | initial =>
      cases right with
      | initial => rfl
      | step previous actionOne actionTwo nature =>
          have hlength := congrArg List.length htwo
          rw [PlayHistory.observations2_step] at hlength
          have hpos :=
            G.commonSignalCrossingEliminationGame.observations1_length_pos previous
          rw [G.commonSignalCrossingEliminationGame.observations_length_eq] at hpos
          simp only [PlayHistory.observations2_initial, List.length_singleton,
            List.length_append] at hlength
          omega
  | step leftPrevious leftActionOne leftActionTwo leftNature ih =>
      cases right with
      | initial =>
          have hlength := congrArg List.length htwo
          rw [PlayHistory.observations2_step] at hlength
          have hpos :=
            G.commonSignalCrossingEliminationGame.observations1_length_pos leftPrevious
          rw [G.commonSignalCrossingEliminationGame.observations_length_eq] at hpos
          simp only [PlayHistory.observations2_initial, List.length_singleton,
            List.length_append] at hlength
          omega
      | step rightPrevious rightActionOne rightActionTwo rightNature =>
          have htwoFull := htwo
          rw [PlayHistory.observations2_step,
            PlayHistory.observations2_step] at htwo
          obtain ⟨htwoPrefix, htwoLastList⟩ :=
            List.append_inj' htwo (by simp)
          have htwoLast := List.singleton_inj.mp htwoLastList
          have hprefix := ih rightPrevious htwoPrefix
          let leftTarget := G.commonSignalCrossingEliminationGame.next
            leftPrevious.lastState leftActionOne leftActionTwo leftNature
          let rightTarget := G.commonSignalCrossingEliminationGame.next
            rightPrevious.lastState rightActionOne rightActionTwo rightNature
          have hleader : G.commonSignalLeaderOne leftTarget =
              G.commonSignalLeaderOne rightTarget :=
            G.commonSignalLeaderOne_eq_of_observations2_eq hhier
              (leftPrevious.step leftActionOne leftActionTwo leftNature)
              (rightPrevious.step rightActionOne rightActionTwo rightNature)
              htwoFull
          rw [shadowView2, shadowView2]
          refine congrArg₂ (fun xs x => xs ++ [x]) hprefix ?_
          change
            (G.commonSignalCrossingEliminationGame.twoPlayerShadowGame
              G.commonSignalLeaderOne).observe2 (some leftTarget) =
            (G.commonSignalCrossingEliminationGame.twoPlayerShadowGame
              G.commonSignalLeaderOne).observe2 (some rightTarget)
          cases hleft : G.commonSignalLeaderOne leftTarget
          · have hright : G.commonSignalLeaderOne rightTarget = false := by
              rw [← hleader, hleft]
            have hdet := G.commonSignal_selectedDetermines hhier
              (leftPrevious.step leftActionOne leftActionTwo leftNature)
            have hsigStep : G.commonSignalLeaderOne
                (leftPrevious.step leftActionOne leftActionTwo
                  leftNature).lastState = false := hleft
            rw [hsigStep] at hdet
            simp only [Bool.false_eq_true, if_false] at hdet
            have honeStep := hdet
              (rightPrevious.step rightActionOne rightActionTwo rightNature)
              htwoFull.symm
            have honeLastEq := congrArg List.getLast? honeStep
            rw [PlayHistory.observations1_getLast?_last,
              PlayHistory.observations1_getLast?_last] at honeLastEq
            have honeTargets := Option.some.inj honeLastEq
            simp [twoPlayerShadowGame, hleft, hright]
            exact honeTargets.symm
          · have hright : G.commonSignalLeaderOne rightTarget = true := by
              rw [← hleader, hleft]
            simp [twoPlayerShadowGame, hleft, hright]
            exact htwoLast

/-! ### The Moore back-transfer

A winning shadow Moore pair reads back to a winning pair for the common-signal
arena.  Each actual player tracks the subset of shadow threads consistent with
its own view; a thread carries a candidate arena state together with *its own*
copies of both shadow controllers' memories, advanced thread-locally along the
candidate's shadow letters.  At output time the player extracts the action of
whichever shadow currently plays its role, with agreement across threads
supplied by the four view-determination lemmas above. -/

section MooreBackTransfer

variable
  (C1 : MooreController.{u, u, u} G.commonSignalShadowGame.Observation1
    G.commonSignalShadowGame.Action1)
  (C2 : MooreController.{u, u, u} G.commonSignalShadowGame.Observation2
    G.commonSignalShadowGame.Action2)

/-- The shadow-thread data of an arena history: its last state and the two
shadow controllers' memories along its shadow views. -/
noncomputable def shadowDataOf
    (h : G.commonSignalCrossingEliminationGame.PlayHistory) :
    G.commonSignalCrossingEliminationGame.State × C1.Memory × C2.Memory :=
  (h.lastState,
    C1.run (G.commonSignalCrossingEliminationGame.shadowView1
      G.commonSignalLeaderOne h),
    C2.run (G.commonSignalCrossingEliminationGame.shadowView2
      G.commonSignalLeaderOne h))

open Classical in
/-- One shadow-thread step for player one. -/
noncomputable def shadowThreadStep1
    (K : Finset (G.commonSignalCrossingEliminationGame.State ×
      C1.Memory × C2.Memory))
    (o1 : G.commonSignalCrossingEliminationGame.Observation1) :
    Finset (G.commonSignalCrossingEliminationGame.State ×
      C1.Memory × C2.Memory) :=
  Finset.univ.filter fun t =>
    (∃ p ∈ K, ∃ (a : G.commonSignalCrossingEliminationGame.Action1)
      (b : G.commonSignalCrossingEliminationGame.Action2)
      (env : G.commonSignalCrossingEliminationGame.Nature),
      t.1 = G.commonSignalCrossingEliminationGame.next p.1 a b env ∧
        t.2.1 = C1.update p.2.1 (G.commonSignalShadowGame.observe1 (some t.1)) ∧
        t.2.2 = C2.update p.2.2 (G.commonSignalShadowGame.observe2 (some t.1))) ∧
      G.commonSignalCrossingEliminationGame.observe1 t.1 = o1

theorem mem_shadowThreadStep1
    (K : Finset (G.commonSignalCrossingEliminationGame.State ×
      C1.Memory × C2.Memory))
    (o1 : G.commonSignalCrossingEliminationGame.Observation1)
    (t : G.commonSignalCrossingEliminationGame.State ×
      C1.Memory × C2.Memory) :
    t ∈ G.shadowThreadStep1 C1 C2 K o1 ↔
      ((∃ p ∈ K, ∃ (a : G.commonSignalCrossingEliminationGame.Action1)
        (b : G.commonSignalCrossingEliminationGame.Action2)
        (env : G.commonSignalCrossingEliminationGame.Nature),
        t.1 = G.commonSignalCrossingEliminationGame.next p.1 a b env ∧
          t.2.1 = C1.update p.2.1
            (G.commonSignalShadowGame.observe1 (some t.1)) ∧
          t.2.2 = C2.update p.2.2
            (G.commonSignalShadowGame.observe2 (some t.1))) ∧
        G.commonSignalCrossingEliminationGame.observe1 t.1 = o1) := by
  simp [shadowThreadStep1]

/-- Player one's shadow-thread set along its arena view. -/
noncomputable def shadowThreads1
    (obs : List G.commonSignalCrossingEliminationGame.Observation1) :
    Finset (G.commonSignalCrossingEliminationGame.State ×
      C1.Memory × C2.Memory) :=
  obs.tail.foldl (G.shadowThreadStep1 C1 C2)
    {G.shadowDataOf C1 C2 PlayHistory.initial}

theorem shadowThreads1_append
    (l : List G.commonSignalCrossingEliminationGame.Observation1)
    (o1 : G.commonSignalCrossingEliminationGame.Observation1) (hl : l ≠ []) :
    G.shadowThreads1 C1 C2 (l ++ [o1]) =
      G.shadowThreadStep1 C1 C2 (G.shadowThreads1 C1 C2 l) o1 := by
  obtain ⟨a, l', rfl⟩ := List.exists_cons_of_ne_nil hl
  simp only [shadowThreads1, List.cons_append, List.tail_cons,
    List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- The shadow views advance by the target's shadow letters. -/
theorem shadowView1_step (h : G.commonSignalCrossingEliminationGame.PlayHistory)
    (a : G.commonSignalCrossingEliminationGame.Action1)
    (b : G.commonSignalCrossingEliminationGame.Action2)
    (env : G.commonSignalCrossingEliminationGame.Nature) :
    G.commonSignalCrossingEliminationGame.shadowView1 G.commonSignalLeaderOne
        (h.step a b env) =
      G.commonSignalCrossingEliminationGame.shadowView1 G.commonSignalLeaderOne
        h ++
        [G.commonSignalShadowGame.observe1
          (some (h.step a b env).lastState)] := rfl

theorem shadowView2_step (h : G.commonSignalCrossingEliminationGame.PlayHistory)
    (a : G.commonSignalCrossingEliminationGame.Action1)
    (b : G.commonSignalCrossingEliminationGame.Action2)
    (env : G.commonSignalCrossingEliminationGame.Nature) :
    G.commonSignalCrossingEliminationGame.shadowView2 G.commonSignalLeaderOne
        (h.step a b env) =
      G.commonSignalCrossingEliminationGame.shadowView2 G.commonSignalLeaderOne
        h ++
        [G.commonSignalShadowGame.observe2
          (some (h.step a b env).lastState)] := rfl

/-- **Real-thread membership** for player one. -/
theorem shadowDataOf_mem_shadowThreads1
    (h : G.commonSignalCrossingEliminationGame.PlayHistory) :
    G.shadowDataOf C1 C2 h ∈
      G.shadowThreads1 C1 C2 h.observations1 := by
  induction h with
  | initial => simp [shadowThreads1]
  | step h a b c ih =>
      obtain ⟨rest, hrest⟩ :=
        G.commonSignalCrossingEliminationGame.observations1_head h
      rw [PlayHistory.observations1_step,
        G.shadowThreads1_append C1 C2 _ _ (by rw [hrest]; simp),
        mem_shadowThreadStep1]
      refine ⟨⟨G.shadowDataOf C1 C2 h, ih, a, b, c, rfl, ?_, ?_⟩, rfl⟩
      · show C1.run (G.commonSignalCrossingEliminationGame.shadowView1
            G.commonSignalLeaderOne (h.step a b c)) = _
        rw [G.shadowView1_step h a b c, MooreController.run_append_singleton]
        rfl
      · show C2.run (G.commonSignalCrossingEliminationGame.shadowView2
            G.commonSignalLeaderOne (h.step a b c)) = _
        rw [G.shadowView2_step h a b c, MooreController.run_append_singleton]
        rfl

/-- **Witnessing histories** for player one's shadow threads. -/
theorem exists_history_of_mem_shadowThreads1Fold
    (l : List G.commonSignalCrossingEliminationGame.Observation1) :
    ∀ t, t ∈ l.foldl (G.shadowThreadStep1 C1 C2)
        {G.shadowDataOf C1 C2 PlayHistory.initial} →
      ∃ h : G.commonSignalCrossingEliminationGame.PlayHistory,
        h.observations1 =
          G.commonSignalCrossingEliminationGame.observe1
            G.commonSignalCrossingEliminationGame.initial :: l ∧
          t = G.shadowDataOf C1 C2 h := by
  induction l using List.reverseRecOn with
  | nil =>
      intro t ht
      rw [List.foldl_nil, Finset.mem_singleton] at ht
      subst ht
      exact ⟨.initial, rfl, rfl⟩
  | append_singleton l' o ih =>
      intro t ht
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil,
        mem_shadowThreadStep1] at ht
      obtain ⟨⟨p, hp, a, b, env, hnext, hm1, hm2⟩, hobs⟩ := ht
      obtain ⟨h, hh1, hpdata⟩ := ih p hp
      have hlast : (h.step a b env).lastState = t.1 := by
        rw [hnext, hpdata]
        rfl
      refine ⟨h.step a b env, ?_, ?_⟩
      · rw [PlayHistory.observations1_step, hh1,
          show G.commonSignalCrossingEliminationGame.observe1
              (G.commonSignalCrossingEliminationGame.next h.lastState a b env) =
            G.commonSignalCrossingEliminationGame.observe1
              (h.step a b env).lastState from rfl, hlast, hobs]
        simp
      · refine Prod.ext ?_ (Prod.ext ?_ ?_)
        · exact hlast.symm
        · show t.2.1 = C1.run
            (G.commonSignalCrossingEliminationGame.shadowView1
              G.commonSignalLeaderOne (h.step a b env))
          rw [G.shadowView1_step h a b env,
            MooreController.run_append_singleton, hm1, hpdata, hlast]
          rfl
        · show t.2.2 = C2.run
            (G.commonSignalCrossingEliminationGame.shadowView2
              G.commonSignalLeaderOne (h.step a b env))
          rw [G.shadowView2_step h a b env,
            MooreController.run_append_singleton, hm2, hpdata, hlast]
          rfl

theorem exists_history_of_mem_shadowThreads1
    (h : G.commonSignalCrossingEliminationGame.PlayHistory)
    (t : G.commonSignalCrossingEliminationGame.State × C1.Memory × C2.Memory)
    (ht : t ∈ G.shadowThreads1 C1 C2 h.observations1) :
    ∃ h' : G.commonSignalCrossingEliminationGame.PlayHistory,
      h'.observations1 = h.observations1 ∧ t = G.shadowDataOf C1 C2 h' := by
  obtain ⟨rest, hrest⟩ :=
    G.commonSignalCrossingEliminationGame.observations1_head h
  rw [hrest] at ht
  obtain ⟨h', hh', hdata⟩ :=
    G.exists_history_of_mem_shadowThreads1Fold C1 C2 rest t ht
  exact ⟨h', by rw [hh', hrest], hdata⟩

open Classical in
/-- One shadow-thread step for player two. -/
noncomputable def shadowThreadStep2
    (K : Finset (G.commonSignalCrossingEliminationGame.State ×
      C1.Memory × C2.Memory))
    (o2 : G.commonSignalCrossingEliminationGame.Observation2) :
    Finset (G.commonSignalCrossingEliminationGame.State ×
      C1.Memory × C2.Memory) :=
  Finset.univ.filter fun t =>
    (∃ p ∈ K, ∃ (a : G.commonSignalCrossingEliminationGame.Action1)
      (b : G.commonSignalCrossingEliminationGame.Action2)
      (env : G.commonSignalCrossingEliminationGame.Nature),
      t.1 = G.commonSignalCrossingEliminationGame.next p.1 a b env ∧
        t.2.1 = C1.update p.2.1 (G.commonSignalShadowGame.observe1 (some t.1)) ∧
        t.2.2 = C2.update p.2.2 (G.commonSignalShadowGame.observe2 (some t.1))) ∧
      G.commonSignalCrossingEliminationGame.observe2 t.1 = o2

theorem mem_shadowThreadStep2
    (K : Finset (G.commonSignalCrossingEliminationGame.State ×
      C1.Memory × C2.Memory))
    (o2 : G.commonSignalCrossingEliminationGame.Observation2)
    (t : G.commonSignalCrossingEliminationGame.State ×
      C1.Memory × C2.Memory) :
    t ∈ G.shadowThreadStep2 C1 C2 K o2 ↔
      ((∃ p ∈ K, ∃ (a : G.commonSignalCrossingEliminationGame.Action1)
        (b : G.commonSignalCrossingEliminationGame.Action2)
        (env : G.commonSignalCrossingEliminationGame.Nature),
        t.1 = G.commonSignalCrossingEliminationGame.next p.1 a b env ∧
          t.2.1 = C1.update p.2.1
            (G.commonSignalShadowGame.observe1 (some t.1)) ∧
          t.2.2 = C2.update p.2.2
            (G.commonSignalShadowGame.observe2 (some t.1))) ∧
        G.commonSignalCrossingEliminationGame.observe2 t.1 = o2) := by
  simp [shadowThreadStep2]

/-- Player two's shadow-thread set along its arena view. -/
noncomputable def shadowThreads2
    (obs : List G.commonSignalCrossingEliminationGame.Observation2) :
    Finset (G.commonSignalCrossingEliminationGame.State ×
      C1.Memory × C2.Memory) :=
  obs.tail.foldl (G.shadowThreadStep2 C1 C2)
    {G.shadowDataOf C1 C2 PlayHistory.initial}

theorem shadowThreads2_append
    (l : List G.commonSignalCrossingEliminationGame.Observation2)
    (o2 : G.commonSignalCrossingEliminationGame.Observation2) (hl : l ≠ []) :
    G.shadowThreads2 C1 C2 (l ++ [o2]) =
      G.shadowThreadStep2 C1 C2 (G.shadowThreads2 C1 C2 l) o2 := by
  obtain ⟨a, l', rfl⟩ := List.exists_cons_of_ne_nil hl
  simp only [shadowThreads2, List.cons_append, List.tail_cons,
    List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem shadowDataOf_mem_shadowThreads2
    (h : G.commonSignalCrossingEliminationGame.PlayHistory) :
    G.shadowDataOf C1 C2 h ∈
      G.shadowThreads2 C1 C2 h.observations2 := by
  induction h with
  | initial => simp [shadowThreads2]
  | step h a b c ih =>
      obtain ⟨rest, hrest⟩ :=
        G.commonSignalCrossingEliminationGame.observations2_head h
      rw [PlayHistory.observations2_step,
        G.shadowThreads2_append C1 C2 _ _ (by rw [hrest]; simp),
        mem_shadowThreadStep2]
      refine ⟨⟨G.shadowDataOf C1 C2 h, ih, a, b, c, rfl, ?_, ?_⟩, rfl⟩
      · show C1.run (G.commonSignalCrossingEliminationGame.shadowView1
            G.commonSignalLeaderOne (h.step a b c)) = _
        rw [G.shadowView1_step h a b c, MooreController.run_append_singleton]
        rfl
      · show C2.run (G.commonSignalCrossingEliminationGame.shadowView2
            G.commonSignalLeaderOne (h.step a b c)) = _
        rw [G.shadowView2_step h a b c, MooreController.run_append_singleton]
        rfl

theorem exists_history_of_mem_shadowThreads2Fold
    (l : List G.commonSignalCrossingEliminationGame.Observation2) :
    ∀ t, t ∈ l.foldl (G.shadowThreadStep2 C1 C2)
        {G.shadowDataOf C1 C2 PlayHistory.initial} →
      ∃ h : G.commonSignalCrossingEliminationGame.PlayHistory,
        h.observations2 =
          G.commonSignalCrossingEliminationGame.observe2
            G.commonSignalCrossingEliminationGame.initial :: l ∧
          t = G.shadowDataOf C1 C2 h := by
  induction l using List.reverseRecOn with
  | nil =>
      intro t ht
      rw [List.foldl_nil, Finset.mem_singleton] at ht
      subst ht
      exact ⟨.initial, rfl, rfl⟩
  | append_singleton l' o ih =>
      intro t ht
      rw [List.foldl_append, List.foldl_cons, List.foldl_nil,
        mem_shadowThreadStep2] at ht
      obtain ⟨⟨p, hp, a, b, env, hnext, hm1, hm2⟩, hobs⟩ := ht
      obtain ⟨h, hh2, hpdata⟩ := ih p hp
      have hlast : (h.step a b env).lastState = t.1 := by
        rw [hnext, hpdata]
        rfl
      refine ⟨h.step a b env, ?_, ?_⟩
      · rw [PlayHistory.observations2_step, hh2,
          show G.commonSignalCrossingEliminationGame.observe2
              (G.commonSignalCrossingEliminationGame.next h.lastState a b env) =
            G.commonSignalCrossingEliminationGame.observe2
              (h.step a b env).lastState from rfl, hlast, hobs]
        simp
      · refine Prod.ext ?_ (Prod.ext ?_ ?_)
        · exact hlast.symm
        · show t.2.1 = C1.run
            (G.commonSignalCrossingEliminationGame.shadowView1
              G.commonSignalLeaderOne (h.step a b env))
          rw [G.shadowView1_step h a b env,
            MooreController.run_append_singleton, hm1, hpdata, hlast]
          rfl
        · show t.2.2 = C2.run
            (G.commonSignalCrossingEliminationGame.shadowView2
              G.commonSignalLeaderOne (h.step a b env))
          rw [G.shadowView2_step h a b env,
            MooreController.run_append_singleton, hm2, hpdata, hlast]
          rfl

theorem exists_history_of_mem_shadowThreads2
    (h : G.commonSignalCrossingEliminationGame.PlayHistory)
    (t : G.commonSignalCrossingEliminationGame.State × C1.Memory × C2.Memory)
    (ht : t ∈ G.shadowThreads2 C1 C2 h.observations2) :
    ∃ h' : G.commonSignalCrossingEliminationGame.PlayHistory,
      h'.observations2 = h.observations2 ∧ t = G.shadowDataOf C1 C2 h' := by
  obtain ⟨rest, hrest⟩ :=
    G.commonSignalCrossingEliminationGame.observations2_head h
  rw [hrest] at ht
  obtain ⟨h', hh', hdata⟩ :=
    G.exists_history_of_mem_shadowThreads2Fold C1 C2 rest t ht
  exact ⟨h', by rw [hh', hrest], hdata⟩

variable [Inhabited G.Action1] [Inhabited G.Action2]

/-- The player-one component of a shadow action. -/
def shadowActFst : Sum G.Action1 G.Action2 -> G.Action1
  | .inl a => a
  | .inr _ => default

/-- The player-two component of a shadow action. -/
def shadowActSnd : Sum G.Action1 G.Action2 -> G.Action2
  | .inl _ => default
  | .inr b => b

open Classical in
/-- Player one's extracted action: the player-one component of whichever
shadow currently plays its role, read from a representative thread. -/
noncomputable def shadowExtractAct1
    (K : Finset (G.commonSignalCrossingEliminationGame.State ×
      C1.Memory × C2.Memory)) : G.Action1 :=
  if hK : K.Nonempty then
    if G.commonSignalLeaderOne hK.choose.1 then
      G.shadowActFst (C1.output hK.choose.2.1)
    else
      G.shadowActFst (C2.output hK.choose.2.2)
  else default

open Classical in
/-- Player two's extracted action. -/
noncomputable def shadowExtractAct2
    (K : Finset (G.commonSignalCrossingEliminationGame.State ×
      C1.Memory × C2.Memory)) : G.Action2 :=
  if hK : K.Nonempty then
    if G.commonSignalLeaderOne hK.choose.1 then
      G.shadowActSnd (C2.output hK.choose.2.2)
    else
      G.shadowActSnd (C1.output hK.choose.2.1)
  else default

omit [Inhabited G.Action2] in
/-- **Extraction agreement, player one.**  On the thread set of a real view the
extracted action reads the true thread's controller memory. -/
theorem shadowExtractAct1_eq (hhier : G.DynamicHierarchy)
    (h : G.commonSignalCrossingEliminationGame.PlayHistory) :
    G.shadowExtractAct1 C1 C2
        (G.shadowThreads1 C1 C2 h.observations1) =
      if G.commonSignalLeaderOne h.lastState then
        G.shadowActFst (C1.output (C1.run
          (G.commonSignalCrossingEliminationGame.shadowView1
            G.commonSignalLeaderOne h)))
      else
        G.shadowActFst (C2.output (C2.run
          (G.commonSignalCrossingEliminationGame.shadowView2
            G.commonSignalLeaderOne h))) := by
  have hne : (G.shadowThreads1 C1 C2 h.observations1).Nonempty :=
    ⟨G.shadowDataOf C1 C2 h, G.shadowDataOf_mem_shadowThreads1 C1 C2 h⟩
  obtain ⟨h', hobs, hdata⟩ :=
    G.exists_history_of_mem_shadowThreads1 C1 C2 h hne.choose hne.choose_spec
  have hlastObs : G.commonSignalCrossingEliminationGame.observe1 h'.lastState =
      G.commonSignalCrossingEliminationGame.observe1 h.lastState := by
    have hlast := congrArg List.getLast? hobs
    rw [PlayHistory.observations1_getLast?_last,
      PlayHistory.observations1_getLast?_last] at hlast
    exact Option.some.inj hlast
  have hsig : G.commonSignalLeaderOne hne.choose.1 =
      G.commonSignalLeaderOne h.lastState := by
    rw [hdata]
    exact G.commonSignalLeaderOne_eq_of_observe1_eq _ _ hlastObs
  rw [shadowExtractAct1, dif_pos hne, hsig, hdata]
  cases hl : G.commonSignalLeaderOne h.lastState with
  | true =>
      have hview := G.commonSignalShadowView1_eq_of_observations1_eq_of_leader
        hhier h' h (by rw [show h'.lastState = hne.choose.1 by rw [hdata]; rfl,
          hsig, hl]) hobs
      show G.shadowActFst (C1.output (C1.run
        (G.commonSignalCrossingEliminationGame.shadowView1
          G.commonSignalLeaderOne h'))) = _
      rw [hview, if_pos rfl]
  | false =>
      have hview := G.commonSignalShadowView2_eq_of_observations1_eq
        hhier h' h hobs
      show G.shadowActFst (C2.output (C2.run
        (G.commonSignalCrossingEliminationGame.shadowView2
          G.commonSignalLeaderOne h'))) = _
      rw [hview, if_neg (by simp)]

omit [Inhabited G.Action1] in
/-- **Extraction agreement, player two.** -/
theorem shadowExtractAct2_eq (hhier : G.DynamicHierarchy)
    (h : G.commonSignalCrossingEliminationGame.PlayHistory) :
    G.shadowExtractAct2 C1 C2
        (G.shadowThreads2 C1 C2 h.observations2) =
      if G.commonSignalLeaderOne h.lastState then
        G.shadowActSnd (C2.output (C2.run
          (G.commonSignalCrossingEliminationGame.shadowView2
            G.commonSignalLeaderOne h)))
      else
        G.shadowActSnd (C1.output (C1.run
          (G.commonSignalCrossingEliminationGame.shadowView1
            G.commonSignalLeaderOne h))) := by
  have hne : (G.shadowThreads2 C1 C2 h.observations2).Nonempty :=
    ⟨G.shadowDataOf C1 C2 h, G.shadowDataOf_mem_shadowThreads2 C1 C2 h⟩
  obtain ⟨h', hobs, hdata⟩ :=
    G.exists_history_of_mem_shadowThreads2 C1 C2 h hne.choose hne.choose_spec
  have hsig : G.commonSignalLeaderOne hne.choose.1 =
      G.commonSignalLeaderOne h.lastState := by
    rw [hdata]
    exact G.commonSignalLeaderOne_eq_of_observations2_eq hhier h' h hobs
  rw [shadowExtractAct2, dif_pos hne, hsig, hdata]
  cases hl : G.commonSignalLeaderOne h.lastState with
  | true =>
      have hview := G.commonSignalShadowView2_eq_of_observations2_eq
        hhier h' h hobs
      show G.shadowActSnd (C2.output (C2.run
        (G.commonSignalCrossingEliminationGame.shadowView2
          G.commonSignalLeaderOne h'))) = _
      rw [hview, if_pos rfl]
  | false =>
      have hview := G.commonSignalShadowView1_eq_of_observations2_eq_of_follower
        hhier h' h (by rw [show h'.lastState = hne.choose.1 by rw [hdata]; rfl,
          hsig, hl]) hobs
      show G.shadowActSnd (C1.output (C1.run
        (G.commonSignalCrossingEliminationGame.shadowView1
          G.commonSignalLeaderOne h'))) = _
      rw [hview, if_neg (by simp)]

/-- Player one's pullback Moore controller. -/
noncomputable def shadowPullbackController1 :
    MooreController.{u, u, u}
      G.commonSignalCrossingEliminationGame.Observation1 G.Action1 where
  Memory := Option (Finset (G.commonSignalCrossingEliminationGame.State ×
    C1.Memory × C2.Memory))
  memoryFinite := by classical infer_instance
  initial := none
  update m o1 :=
    match m with
    | none => some {G.shadowDataOf C1 C2 PlayHistory.initial}
    | some K => some (G.shadowThreadStep1 C1 C2 K o1)
  output m :=
    match m with
    | none => default
    | some K => G.shadowExtractAct1 C1 C2 K

/-- Player two's pullback Moore controller. -/
noncomputable def shadowPullbackController2 :
    MooreController.{u, u, u}
      G.commonSignalCrossingEliminationGame.Observation2 G.Action2 where
  Memory := Option (Finset (G.commonSignalCrossingEliminationGame.State ×
    C1.Memory × C2.Memory))
  memoryFinite := by classical infer_instance
  initial := none
  update m o2 :=
    match m with
    | none => some {G.shadowDataOf C1 C2 PlayHistory.initial}
    | some K => some (G.shadowThreadStep2 C1 C2 K o2)
  output m :=
    match m with
    | none => default
    | some K => G.shadowExtractAct2 C1 C2 K

omit [Inhabited G.Action2] in
theorem shadowPullbackController1_run
    (h : G.commonSignalCrossingEliminationGame.PlayHistory) :
    (G.shadowPullbackController1 C1 C2).run h.observations1 =
      some (G.shadowThreads1 C1 C2 h.observations1) := by
  induction h with
  | initial => rfl
  | step h a b c ih =>
      obtain ⟨rest, hrest⟩ :=
        G.commonSignalCrossingEliminationGame.observations1_head h
      rw [PlayHistory.observations1_step, MooreController.run_append_singleton,
        ih]
      show some (G.shadowThreadStep1 C1 C2
        (G.shadowThreads1 C1 C2 h.observations1) _) = _
      rw [G.shadowThreads1_append C1 C2 _ _ (by rw [hrest]; simp)]

omit [Inhabited G.Action1] in
theorem shadowPullbackController2_run
    (h : G.commonSignalCrossingEliminationGame.PlayHistory) :
    (G.shadowPullbackController2 C1 C2).run h.observations2 =
      some (G.shadowThreads2 C1 C2 h.observations2) := by
  induction h with
  | initial => rfl
  | step h a b c ih =>
      obtain ⟨rest, hrest⟩ :=
        G.commonSignalCrossingEliminationGame.observations2_head h
      rw [PlayHistory.observations2_step, MooreController.run_append_singleton,
        ih]
      show some (G.shadowThreadStep2 C1 C2
        (G.shadowThreads2 C1 C2 h.observations2) _) = _
      rw [G.shadowThreads2_append C1 C2 _ _ (by rw [hrest]; simp)]

omit [Inhabited G.Action2] in
/-- The pullback strategies read the extractions along real views. -/
theorem shadowPullback1_strategy
    (h : G.commonSignalCrossingEliminationGame.PlayHistory) :
    (G.shadowPullbackController1 C1 C2).strategy h.observations1 =
      G.shadowExtractAct1 C1 C2 (G.shadowThreads1 C1 C2 h.observations1) := by
  rw [MooreController.strategy, G.shadowPullbackController1_run]
  rfl

omit [Inhabited G.Action1] in
theorem shadowPullback2_strategy
    (h : G.commonSignalCrossingEliminationGame.PlayHistory) :
    (G.shadowPullbackController2 C1 C2).strategy h.observations2 =
      G.shadowExtractAct2 C1 C2 (G.shadowThreads2 C1 C2 h.observations2) := by
  rw [MooreController.strategy, G.shadowPullbackController2_run]
  rfl

/-- Priority sequences that are eventually constantly `1` are not accepted. -/
theorem not_parityAccepts_of_eventually_one (p : Nat -> Nat) (N : Nat)
    (hp : ∀ k, N ≤ k -> p k = 1) : ¬ ParityAccepts p := by
  rintro ⟨q, hqeven, hqinf, hqmin⟩
  have hone : PriorityInfinitelyOften p 1 := fun n =>
    ⟨max n N, le_max_left n N, hp _ (le_max_right n N)⟩
  have hq1 : q ≤ 1 := hqmin 1 hone
  have hq0 : q = 0 := by omega
  obtain ⟨k, hk, hpk⟩ := hqinf N
  rw [hq0] at hpk
  rw [hp k hk] at hpk
  exact absurd hpk (by omega)

/-- **The pullback correspondence.**  Against any Nature, the shadow play of a
*winning* shadow Moore pair is the `shadowLift` of the pullback pair's arena
play: the winning hypothesis rules out ever entering the invalid-action sink. -/
theorem shadowPullback_correspondence (hhier : G.DynamicHierarchy)
    (hwin : G.commonSignalShadowGame.HistoryStrategyWins
      (C1.strategy, C2.strategy))
    (nature : Nat -> G.commonSignalCrossingEliminationGame.Nature) (n : Nat) :
    G.commonSignalShadowGame.playHistory (C1.strategy, C2.strategy) nature n =
      G.commonSignalCrossingEliminationGame.shadowLift G.commonSignalLeaderOne
        (G.commonSignalCrossingEliminationGame.playHistory
          ((G.shadowPullbackController1 C1 C2).strategy,
            (G.shadowPullbackController2 C1 C2).strategy) nature n) := by
  set σ : G.commonSignalCrossingEliminationGame.HistoryProductStrategy :=
    ((G.shadowPullbackController1 C1 C2).strategy,
      (G.shadowPullbackController2 C1 C2).strategy) with hσ
  induction n with
  | zero => rfl
  | succ n ih =>
      set h_n := G.commonSignalCrossingEliminationGame.playHistory σ nature n
        with hh
      have hview1 : (G.commonSignalShadowGame.strategyState
            (C1.strategy, C2.strategy) nature n).2.1 =
          G.commonSignalCrossingEliminationGame.shadowView1
            G.commonSignalLeaderOne h_n := by
        rw [← G.commonSignalShadowGame.playHistory_observations1
          (C1.strategy, C2.strategy) nature n, ih,
          G.commonSignalCrossingEliminationGame.shadowLift_observations1]
      have hview2 : (G.commonSignalShadowGame.strategyState
            (C1.strategy, C2.strategy) nature n).2.2 =
          G.commonSignalCrossingEliminationGame.shadowView2
            G.commonSignalLeaderOne h_n := by
        rw [← G.commonSignalShadowGame.playHistory_observations2
          (C1.strategy, C2.strategy) nature n, ih,
          G.commonSignalCrossingEliminationGame.shadowLift_observations2]
      have hstep : G.commonSignalCrossingEliminationGame.playHistory σ nature
            (n + 1) =
          h_n.step (σ.1 h_n.observations1) (σ.2 h_n.observations2)
            (nature n) := by
        rw [playHistory,
          G.commonSignalCrossingEliminationGame.playHistory_observations1
            σ nature n,
          G.commonSignalCrossingEliminationGame.playHistory_observations2
            σ nature n]
      have hσ1 : σ.1 h_n.observations1 =
          if G.commonSignalLeaderOne h_n.lastState then
            G.shadowActFst (C1.output (C1.run
              (G.commonSignalCrossingEliminationGame.shadowView1
                G.commonSignalLeaderOne h_n)))
          else
            G.shadowActFst (C2.output (C2.run
              (G.commonSignalCrossingEliminationGame.shadowView2
                G.commonSignalLeaderOne h_n))) := by
        show (G.shadowPullbackController1 C1 C2).strategy h_n.observations1 = _
        rw [G.shadowPullback1_strategy C1 C2 h_n,
          G.shadowExtractAct1_eq C1 C2 hhier h_n]
      have hσ2 : σ.2 h_n.observations2 =
          if G.commonSignalLeaderOne h_n.lastState then
            G.shadowActSnd (C2.output (C2.run
              (G.commonSignalCrossingEliminationGame.shadowView2
                G.commonSignalLeaderOne h_n)))
          else
            G.shadowActSnd (C1.output (C1.run
              (G.commonSignalCrossingEliminationGame.shadowView1
                G.commonSignalLeaderOne h_n))) := by
        show (G.shadowPullbackController2 C1 C2).strategy h_n.observations2 = _
        rw [G.shadowPullback2_strategy C1 C2 h_n,
          G.shadowExtractAct2_eq C1 C2 hhier h_n]
      show (G.commonSignalShadowGame.playHistory
          (C1.strategy, C2.strategy) nature n).step
          ((C1.strategy, C2.strategy).1
            (G.commonSignalShadowGame.strategyState
              (C1.strategy, C2.strategy) nature n).2.1)
          ((C1.strategy, C2.strategy).2
            (G.commonSignalShadowGame.strategyState
              (C1.strategy, C2.strategy) nature n).2.2)
          (nature n) = _
      rw [ih, hview1, hview2, hstep, shadowLift]
      show (G.commonSignalCrossingEliminationGame.shadowLift
          G.commonSignalLeaderOne h_n).step
          (C1.strategy (G.commonSignalCrossingEliminationGame.shadowView1
            G.commonSignalLeaderOne h_n))
          (C2.strategy (G.commonSignalCrossingEliminationGame.shadowView2
            G.commonSignalLeaderOne h_n)) (nature n) = _
      -- Sink exclusion and shape analysis.
      have hsinkFalse : ∀ (m : Nat),
          (G.commonSignalShadowGame.playHistory (C1.strategy, C2.strategy)
            nature (n + 1)).lastState = none -> False := by
        intro m hsink
        have habs : ∀ k, (G.commonSignalShadowGame.playHistory
            (C1.strategy, C2.strategy) nature (n + 1 + k)).lastState =
            none := by
          intro k
          induction k with
          | zero => exact hsink
          | succ k ihk =>
              show G.commonSignalShadowGame.next
                (G.commonSignalShadowGame.playHistory
                  (C1.strategy, C2.strategy) nature (n + 1 + k)).lastState
                _ _ (nature (n + 1 + k)) = none
              rw [ihk]
              rfl
        have hpk : ∀ m', n + 1 ≤ m' ->
            G.commonSignalShadowGame.priority
              (G.commonSignalShadowGame.strategyState
                (C1.strategy, C2.strategy) nature m').1 = 1 := by
          intro m' hm'
          rw [← G.commonSignalShadowGame.playHistory_lastState
            (C1.strategy, C2.strategy) nature m']
          have := habs (m' - (n + 1))
          rw [show n + 1 + (m' - (n + 1)) = m' by omega] at this
          rw [this]
          rfl
        exact not_parityAccepts_of_eventually_one _ (n + 1) hpk (hwin nature)
      cases hl : G.commonSignalLeaderOne h_n.lastState with
      | true =>
          cases hc1 : C1.output (C1.run
              (G.commonSignalCrossingEliminationGame.shadowView1
                G.commonSignalLeaderOne h_n)) with
          | inl a1 =>
              cases hc2 : C2.output (C2.run
                  (G.commonSignalCrossingEliminationGame.shadowView2
                    G.commonSignalLeaderOne h_n)) with
              | inr b2 =>
                  have hs1 : σ.1 h_n.observations1 = a1 := by
                    rw [hσ1, if_pos hl, hc1]
                    rfl
                  have hs2 : σ.2 h_n.observations2 = b2 := by
                    rw [hσ2, if_pos hl, hc2]
                    rfl
                  rw [hs1, hs2, shadowActionProfile, if_pos hl]
                  rw [show C1.strategy
                      (G.commonSignalCrossingEliminationGame.shadowView1
                        G.commonSignalLeaderOne h_n) = Sum.inl a1 from hc1,
                    show C2.strategy
                      (G.commonSignalCrossingEliminationGame.shadowView2
                        G.commonSignalLeaderOne h_n) = Sum.inr b2 from hc2]
              | inl b2' =>
                  exact False.elim (hsinkFalse 0 (by
                    show G.commonSignalShadowGame.next
                      (G.commonSignalShadowGame.playHistory
                        (C1.strategy, C2.strategy) nature n).lastState
                      _ _ (nature n) = none
                    rw [ih,
                      G.commonSignalCrossingEliminationGame.shadowLift_lastState,
                      hview1, hview2]
                    show G.commonSignalShadowGame.next (some h_n.lastState)
                      (C1.strategy _) (C2.strategy _) (nature n) = none
                    rw [show C1.strategy
                        (G.commonSignalCrossingEliminationGame.shadowView1
                          G.commonSignalLeaderOne h_n) = _ from hc1,
                      show C2.strategy
                        (G.commonSignalCrossingEliminationGame.shadowView2
                          G.commonSignalLeaderOne h_n) = _ from hc2]
                    simp [commonSignalShadowGame, twoPlayerShadowGame, hl]))
          | inr a1' =>
              exact False.elim (hsinkFalse 0 (by
                show G.commonSignalShadowGame.next
                  (G.commonSignalShadowGame.playHistory
                    (C1.strategy, C2.strategy) nature n).lastState
                  _ _ (nature n) = none
                rw [ih,
                  G.commonSignalCrossingEliminationGame.shadowLift_lastState,
                  hview1, hview2]
                show G.commonSignalShadowGame.next (some h_n.lastState)
                  (C1.strategy _) (C2.strategy _) (nature n) = none
                rw [show C1.strategy
                    (G.commonSignalCrossingEliminationGame.shadowView1
                      G.commonSignalLeaderOne h_n) = _ from hc1]
                cases C2.strategy (G.commonSignalCrossingEliminationGame.shadowView2
                  G.commonSignalLeaderOne h_n) <;>
                  simp [commonSignalShadowGame, twoPlayerShadowGame, hl]))
      | false =>
          cases hc1 : C1.output (C1.run
              (G.commonSignalCrossingEliminationGame.shadowView1
                G.commonSignalLeaderOne h_n)) with
          | inr b2 =>
              cases hc2 : C2.output (C2.run
                  (G.commonSignalCrossingEliminationGame.shadowView2
                    G.commonSignalLeaderOne h_n)) with
              | inl a1 =>
                  have hs1 : σ.1 h_n.observations1 = a1 := by
                    rw [hσ1, if_neg (by rw [hl]; simp), hc2]
                    rfl
                  have hs2 : σ.2 h_n.observations2 = b2 := by
                    rw [hσ2, if_neg (by rw [hl]; simp), hc1]
                    rfl
                  rw [hs1, hs2, shadowActionProfile,
                    if_neg (by rw [hl]; simp)]
                  rw [show C1.strategy
                      (G.commonSignalCrossingEliminationGame.shadowView1
                        G.commonSignalLeaderOne h_n) = Sum.inr b2 from hc1,
                    show C2.strategy
                      (G.commonSignalCrossingEliminationGame.shadowView2
                        G.commonSignalLeaderOne h_n) = Sum.inl a1 from hc2]
              | inr a1' =>
                  exact False.elim (hsinkFalse 0 (by
                    show G.commonSignalShadowGame.next
                      (G.commonSignalShadowGame.playHistory
                        (C1.strategy, C2.strategy) nature n).lastState
                      _ _ (nature n) = none
                    rw [ih,
                      G.commonSignalCrossingEliminationGame.shadowLift_lastState,
                      hview1, hview2]
                    show G.commonSignalShadowGame.next (some h_n.lastState)
                      (C1.strategy _) (C2.strategy _) (nature n) = none
                    rw [show C1.strategy
                        (G.commonSignalCrossingEliminationGame.shadowView1
                          G.commonSignalLeaderOne h_n) = _ from hc1,
                      show C2.strategy
                        (G.commonSignalCrossingEliminationGame.shadowView2
                          G.commonSignalLeaderOne h_n) = _ from hc2]
                    simp [commonSignalShadowGame, twoPlayerShadowGame, hl]))
          | inl b2' =>
              exact False.elim (hsinkFalse 0 (by
                show G.commonSignalShadowGame.next
                  (G.commonSignalShadowGame.playHistory
                    (C1.strategy, C2.strategy) nature n).lastState
                  _ _ (nature n) = none
                rw [ih,
                  G.commonSignalCrossingEliminationGame.shadowLift_lastState,
                  hview1, hview2]
                show G.commonSignalShadowGame.next (some h_n.lastState)
                  (C1.strategy _) (C2.strategy _) (nature n) = none
                rw [show C1.strategy
                    (G.commonSignalCrossingEliminationGame.shadowView1
                      G.commonSignalLeaderOne h_n) = _ from hc1]
                cases C2.strategy (G.commonSignalCrossingEliminationGame.shadowView2
                  G.commonSignalLeaderOne h_n) <;>
                  simp [commonSignalShadowGame, twoPlayerShadowGame, hl]))

/-- **The shadow Moore back-transfer.**  A winning shadow Moore pair pulls back
to a winning Moore pair for the common-signal arena. -/
theorem finiteStateRealizable_of_commonSignalShadow (hhier : G.DynamicHierarchy)
    (hS : G.commonSignalShadowGame.FiniteStateRealizable) :
    G.commonSignalCrossingEliminationGame.FiniteStateRealizable := by
  obtain ⟨ctrl, hctrl⟩ := hS
  refine ⟨⟨G.shadowPullbackController1 ctrl.one ctrl.two,
    G.shadowPullbackController2 ctrl.one ctrl.two⟩, ?_⟩
  intro nature
  have hwin : G.commonSignalShadowGame.HistoryStrategyWins
      (ctrl.one.strategy, ctrl.two.strategy) := hctrl
  have hpri : ∀ n,
      G.commonSignalCrossingEliminationGame.priority
        (G.commonSignalCrossingEliminationGame.strategyState
          ((G.shadowPullbackController1 ctrl.one ctrl.two).strategy,
            (G.shadowPullbackController2 ctrl.one ctrl.two).strategy)
          nature n).1 =
      G.commonSignalShadowGame.priority
        (G.commonSignalShadowGame.strategyState
          (ctrl.one.strategy, ctrl.two.strategy) nature n).1 := by
    intro n
    rw [← G.commonSignalShadowGame.playHistory_lastState
      (ctrl.one.strategy, ctrl.two.strategy) nature n,
      G.shadowPullback_correspondence ctrl.one ctrl.two hhier hwin nature n,
      ← G.commonSignalCrossingEliminationGame.playHistory_lastState _ nature n,
      G.commonSignalCrossingEliminationGame.shadowLift_priority]
  have hfun : (fun n => G.commonSignalCrossingEliminationGame.priority
      (G.commonSignalCrossingEliminationGame.strategyState
        ((G.shadowPullbackController1 ctrl.one ctrl.two).strategy,
          (G.shadowPullbackController2 ctrl.one ctrl.two).strategy)
        nature n).1) =
      (fun n => G.commonSignalShadowGame.priority
        (G.commonSignalShadowGame.strategyState
          (ctrl.one.strategy, ctrl.two.strategy) nature n).1) := funext hpri
  show ParityAccepts (fun n =>
    G.commonSignalCrossingEliminationGame.priority
      (G.commonSignalCrossingEliminationGame.strategyState
        ((G.shadowPullbackController1 ctrl.one ctrl.two).strategy,
          (G.shadowPullbackController2 ctrl.one ctrl.two).strategy)
        nature n).1)
  rw [hfun]
  exact hwin nature

end MooreBackTransfer

/-! ### The certificate composition

The endpoint of the transport: a finite-state synthesis certificate for any
game with dynamic hierarchical information, conditional on exactly two named
classical imports stated at the composed reduction -- the Reif completeness in
its Berwanger--Mathew--van den Bogaard shape (a distributed winner yields an
Even winner of the shadow game's leader knowledge arena) and finite-parity-game
solvability.  Everything else is proved: the shadow game's static hierarchy,
the static engine's soundness readback, and the two Moore back-transfers. -/

section CertificateComposition

variable [Inhabited G.Action1] [Inhabited G.Action2]
  [Inhabited G.Observation1] [Inhabited G.Observation2]

instance : Inhabited (Sum G.Action1 G.Action2) := ⟨Sum.inl default⟩

instance : Inhabited G.commonSignalCrossingEliminationGame.Action1 :=
  ⟨(default : G.Action1)⟩

instance : Inhabited G.commonSignalCrossingEliminationGame.Action2 :=
  ⟨(default : G.Action2)⟩

instance : Inhabited G.commonSignalShadowGame.Action1 := ⟨Sum.inl default⟩

instance : Inhabited G.commonSignalShadowGame.Action2 := ⟨Sum.inl default⟩

instance : Inhabited G.commonSignalShadowGame.Observation1 := ⟨none⟩

instance : Inhabited G.commonSignalShadowGame.Observation2 := ⟨none⟩

omit [Inhabited G.Action1] [Inhabited G.Action2] [Inhabited G.Observation1]
    [Inhabited G.Observation2] in
/-- The shadow game satisfies the static hierarchy: sol's fixed-hierarchy
theorem, packaged for the static engine. -/
theorem commonSignalShadowGame_staticHierarchy (hhier : G.DynamicHierarchy) :
    G.commonSignalShadowGame.StaticHierarchy := fun history =>
  G.commonSignalShadowGame_oneDeterminesTwoAt hhier history

/-- **The composed Reif certificate** (classical import; the
Berwanger--Mathew--van den Bogaard Lemma 12 + Theorem 10 shape).  A distributed
winner of the base game yields a follower belief table and an Even positional
winner of the shadow game's leader knowledge arena. -/
def ShadowLeaderArenaComplete : Prop :=
  G.HistoryRealizable ->
    ∃ (f2 : G.commonSignalShadowGame.Belief -> G.commonSignalShadowGame.Action2)
      (τ : (G.commonSignalShadowGame.leaderArena f2).PositionalStrategy
        ParityPlayer.even),
      CountableParityGame.PositionalStrategy.WinningFrom
        (G := G.commonSignalShadowGame.leaderArena f2) τ
        (G.commonSignalShadowGame.leaderArenaInitial f2)

/-- **The proven half of the composition**: a shadow arena winner reads back to
a base finite-state winner, through the static engine's soundness and the two
Moore back-transfers. -/
theorem finiteStateRealizable_of_shadowArenaWinner (hhier : G.DynamicHierarchy)
    (f2 : G.commonSignalShadowGame.Belief -> G.commonSignalShadowGame.Action2)
    (τ : (G.commonSignalShadowGame.leaderArena f2).PositionalStrategy
      ParityPlayer.even)
    (hτ : CountableParityGame.PositionalStrategy.WinningFrom
      (G := G.commonSignalShadowGame.leaderArena f2) τ
      (G.commonSignalShadowGame.leaderArenaInitial f2)) :
    G.FiniteStateRealizable :=
  G.finiteStateRealizable_of_commonSignal hhier
    (G.finiteStateRealizable_of_commonSignalShadow hhier
      (G.commonSignalShadowGame.finiteStateRealizable_of_leaderArena_winner
        (G.commonSignalShadowGame_staticHierarchy hhier) f2 τ hτ))

/-- Realizability of the base game is exactly winnability of some shadow leader
arena. -/
theorem historyRealizable_iff_shadowArenaWin (hhier : G.DynamicHierarchy)
    (hc : G.ShadowLeaderArenaComplete) :
    G.HistoryRealizable ↔
      ∃ f2 : G.commonSignalShadowGame.Belief -> G.commonSignalShadowGame.Action2,
        G.commonSignalShadowGame.leaderArenaInitial f2 ∈
          (G.commonSignalShadowGame.leaderArena f2).PositionalWinningRegion
            ParityPlayer.even := by
  constructor
  · intro hreal
    obtain ⟨f2, τ, hτ⟩ := hc hreal
    exact ⟨f2, τ, hτ⟩
  · rintro ⟨f2, τ, hτ⟩
    exact G.historyRealizable_of_finiteStateRealizable
      (G.finiteStateRealizable_of_shadowArenaWinner hhier f2 τ hτ)

/-- **The transported certificate.**  Under dynamic hierarchy, the two named
classical imports produce the full finite-state synthesis certificate for the
base game. -/
noncomputable def finiteStateSynthesisCertificate_of_shadowCerts
    (hhier : G.DynamicHierarchy) (hc : G.ShadowLeaderArenaComplete)
    (hd : G.commonSignalShadowGame.LeaderArenaWinDecidable) :
    G.FiniteStateSynthesisCertificate where
  complete hreal := by
    obtain ⟨f2, τ, hτ⟩ := hc hreal
    exact G.finiteStateRealizable_of_shadowArenaWinner hhier f2 τ hτ
  decision := by
    classical
    haveI : DecidablePred (fun f2 : G.commonSignalShadowGame.Belief ->
        G.commonSignalShadowGame.Action2 =>
        G.commonSignalShadowGame.leaderArenaInitial f2 ∈
          (G.commonSignalShadowGame.leaderArena f2).PositionalWinningRegion
            ParityPlayer.even) := hd
    haveI : Decidable (∃ f2 : G.commonSignalShadowGame.Belief ->
        G.commonSignalShadowGame.Action2,
        G.commonSignalShadowGame.leaderArenaInitial f2 ∈
          (G.commonSignalShadowGame.leaderArena f2).PositionalWinningRegion
            ParityPlayer.even) := Fintype.decidableExistsFintype
    exact decidable_of_iff _
      (G.historyRealizable_iff_shadowArenaWin hhier hc).symm

/-- **The dynamic-hierarchy synthesis theorem, transported** -- the per-game
form of `DynamicHierarchyFiniteStateSolvable`: every finite game with dynamic
hierarchical information has a finite-state synthesis certificate, conditional
on exactly the composed Reif completeness certificate and finite-parity-game
solvability at its shadow arena. -/
theorem dynamicHierarchy_finiteStateSolvable_of_shadowCerts
    (hhier : G.DynamicHierarchy) (hc : G.ShadowLeaderArenaComplete)
    (hd : G.commonSignalShadowGame.LeaderArenaWinDecidable) :
    Nonempty G.FiniteStateSynthesisCertificate :=
  ⟨G.finiteStateSynthesisCertificate_of_shadowCerts hhier hc hd⟩

omit [Inhabited G.Action2] [Inhabited G.Observation1] [Inhabited G.Observation2] in
/--
**The composed completeness certificate decomposes along the literature
seams.**  `ShadowLeaderArenaComplete` follows from (i) the forward
realizability transfer of the shadow construction (the completeness half of
the Berwanger--Mathew--van den Bogaard shadow argument, internal to their
Theorem 10 proof) and (ii) the development's concrete Reif-shaped
belief-sufficiency statement at the shadow game, whose static-hierarchy
premise is discharged by the proven
`commonSignalShadowGame_staticHierarchy`.  The crossing-elimination transfer
is the proven `commonSignal_historyRealizable_iff`.  A future internal
mechanization must prove the specialization in (ii); the preferred
literature-relative endpoint instead imports the higher-level
dynamic-hierarchy theorem directly.
-/
theorem shadowLeaderArenaComplete_of_forwardTransfer_and_reif
    (hhier : G.DynamicHierarchy)
    (hfwd :
      G.commonSignalCrossingEliminationGame.HistoryRealizable ->
        G.commonSignalShadowGame.HistoryRealizable)
    (hreif : G.commonSignalShadowGame.FollowerBeliefSufficiency) :
    G.ShadowLeaderArenaComplete := fun hreal =>
  G.commonSignalShadowGame.leaderArenaComplete_of_followerBeliefSufficiency
    hreif (G.commonSignalShadowGame_staticHierarchy hhier)
    (hfwd ((G.commonSignal_historyRealizable_iff hhier).mpr hreal))

omit [Inhabited G.Action2] [Inhabited G.Observation1] [Inhabited G.Observation2] in
/--
**The converse reduction: the forward shadow transfer is no weaker than the
composed certificate.**  Given `ShadowLeaderArenaComplete`, the proven
soundness readback at the (statically hierarchical) shadow game turns the
arena winner into shadow realizability.  Together with
`shadowLeaderArenaComplete_of_forwardTransfer_and_reif` this shows the
forward shadow transfer and the composed certificate are interderivable
modulo proven glue and the textbook Reif statement: the transfer is NOT a
lighter obligation, and a strategy-translation proof of it cannot exist
(shadow seat two lacks the current follower's leader-phase history).
-/
theorem forwardTransfer_of_shadowLeaderArenaComplete
    (hhier : G.DynamicHierarchy) (hc : G.ShadowLeaderArenaComplete)
    (hreal : G.commonSignalCrossingEliminationGame.HistoryRealizable) :
    G.commonSignalShadowGame.HistoryRealizable := by
  obtain ⟨f2, τ, hτ⟩ :=
    hc ((G.commonSignal_historyRealizable_iff hhier).mp hreal)
  exact G.commonSignalShadowGame.historyRealizable_of_finiteStateRealizable
    (G.commonSignalShadowGame.finiteStateRealizable_of_leaderArena_winner
      (G.commonSignalShadowGame_staticHierarchy hhier) f2 τ hτ)

end CertificateComposition

end FiniteConcurrentGame

end DistributedSynthesis
