/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmCommonSignalCrossingElimination

/-!
# The two-player rank-permuted shadow arena

This is the second phase of Berwanger--Mathew--van den Bogaard Theorem 10,
specialized to two players.  Shadow player one always occupies the currently
most-informed role and shadow player two the other role.  A finite positional
Boolean signal selects the permutation.  Invalidly tagged shadow action
profiles enter a public odd sink.

The information-theoretic theorem -- that, after crossing elimination, each
actual player has the same perfect-recall information set as its current
shadow -- is developed after the operational construction below.
-/

namespace DistributedSynthesis

universe u

namespace FiniteConcurrentGame

variable (G : FiniteConcurrentGame.{u})

attribute [instance] FiniteConcurrentGame.stateFinite
  FiniteConcurrentGame.action1Finite FiniteConcurrentGame.action2Finite
  FiniteConcurrentGame.natureFinite FiniteConcurrentGame.observation1Finite
  FiniteConcurrentGame.observation2Finite

/-- Player one occupies the first (more-informed) shadow role at `state`. -/
abbrev ShadowLeaderSignal := G.State → Bool

/-- Both shadows use the disjoint union of the actual action alphabets. -/
abbrev ShadowAction := Sum G.Action1 G.Action2

/-- Both shadows use the disjoint union of actual observations, with an outer
`Option` reserving `none` for the public invalid-action sink. -/
abbrev ShadowObservation := Option (Sum G.Observation1 G.Observation2)

/-- Rank-permuted two-player shadow arena. -/
noncomputable def twoPlayerShadowGame
    (leaderOne : G.ShadowLeaderSignal) : FiniteConcurrentGame where
  State := Option G.State
  Action1 := G.ShadowAction
  Action2 := G.ShadowAction
  Nature := G.Nature
  Observation1 := G.ShadowObservation
  Observation2 := G.ShadowObservation
  stateFinite := by infer_instance
  action1Finite := by infer_instance
  action2Finite := by infer_instance
  natureFinite := G.natureFinite
  observation1Finite := by infer_instance
  observation2Finite := by infer_instance
  initial := some G.initial
  next state shadowOne shadowTwo nature :=
    match state with
    | none => none
    | some current =>
        if leaderOne current then
          match shadowOne, shadowTwo with
          | Sum.inl actionOne, Sum.inr actionTwo =>
              some (G.next current actionOne actionTwo nature)
          | _, _ => none
        else
          match shadowOne, shadowTwo with
          | Sum.inr actionTwo, Sum.inl actionOne =>
              some (G.next current actionOne actionTwo nature)
          | _, _ => none
  observe1 state :=
    match state with
    | none => none
    | some current =>
        if leaderOne current then some (Sum.inl (G.observe1 current))
        else some (Sum.inr (G.observe2 current))
  observe2 state :=
    match state with
    | none => none
    | some current =>
        if leaderOne current then some (Sum.inr (G.observe2 current))
        else some (Sum.inl (G.observe1 current))
  priority state :=
    match state with
    | none => 1
    | some current => G.priority current

@[simp]
theorem twoPlayerShadowGame_initial
    (leaderOne : G.ShadowLeaderSignal) :
    (G.twoPlayerShadowGame leaderOne).initial = some G.initial := rfl

@[simp]
theorem twoPlayerShadowGame_next_sink
    (leaderOne : G.ShadowLeaderSignal)
    (shadowOne shadowTwo : G.ShadowAction) (nature : G.Nature) :
    (G.twoPlayerShadowGame leaderOne).next none shadowOne shadowTwo nature =
      none := rfl

@[simp]
theorem twoPlayerShadowGame_next_leaderOne
    (leaderOne : G.ShadowLeaderSignal) (state : G.State)
    (hleader : leaderOne state = true)
    (actionOne : G.Action1) (actionTwo : G.Action2) (nature : G.Nature) :
    (G.twoPlayerShadowGame leaderOne).next (some state)
        (Sum.inl actionOne) (Sum.inr actionTwo) nature =
      some (G.next state actionOne actionTwo nature) := by
  simp [twoPlayerShadowGame, hleader]

@[simp]
theorem twoPlayerShadowGame_next_leaderTwo
    (leaderOne : G.ShadowLeaderSignal) (state : G.State)
    (hleader : leaderOne state = false)
    (actionOne : G.Action1) (actionTwo : G.Action2) (nature : G.Nature) :
    (G.twoPlayerShadowGame leaderOne).next (some state)
        (Sum.inr actionTwo) (Sum.inl actionOne) nature =
      some (G.next state actionOne actionTwo nature) := by
  simp [twoPlayerShadowGame, hleader]

@[simp]
theorem twoPlayerShadowGame_observe_leaderOne
    (leaderOne : G.ShadowLeaderSignal) (state : G.State)
    (hleader : leaderOne state = true) :
    (G.twoPlayerShadowGame leaderOne).observe1 (some state) =
        some (Sum.inl (G.observe1 state)) ∧
      (G.twoPlayerShadowGame leaderOne).observe2 (some state) =
        some (Sum.inr (G.observe2 state)) := by
  simp [twoPlayerShadowGame, hleader]

@[simp]
theorem twoPlayerShadowGame_observe_leaderTwo
    (leaderOne : G.ShadowLeaderSignal) (state : G.State)
    (hleader : leaderOne state = false) :
    (G.twoPlayerShadowGame leaderOne).observe1 (some state) =
        some (Sum.inr (G.observe2 state)) ∧
      (G.twoPlayerShadowGame leaderOne).observe2 (some state) =
        some (Sum.inl (G.observe1 state)) := by
  simp [twoPlayerShadowGame, hleader]

@[simp]
theorem twoPlayerShadowGame_priority_some
    (leaderOne : G.ShadowLeaderSignal) (state : G.State) :
    (G.twoPlayerShadowGame leaderOne).priority (some state) =
      G.priority state := rfl

@[simp]
theorem twoPlayerShadowGame_priority_sink
    (leaderOne : G.ShadowLeaderSignal) :
    (G.twoPlayerShadowGame leaderOne).priority none = 1 := rfl

/-- The rank-correct permutation of one actual action profile. -/
def shadowActionProfile (leaderOne : G.ShadowLeaderSignal) (state : G.State)
    (actionOne : G.Action1) (actionTwo : G.Action2) :
    G.ShadowAction × G.ShadowAction :=
  if leaderOne state then
    (Sum.inl actionOne, Sum.inr actionTwo)
  else
    (Sum.inr actionTwo, Sum.inl actionOne)

theorem twoPlayerShadowGame_next_shadowActionProfile
    (leaderOne : G.ShadowLeaderSignal) (state : G.State)
    (actionOne : G.Action1) (actionTwo : G.Action2) (nature : G.Nature) :
    let profile := G.shadowActionProfile leaderOne state actionOne actionTwo
    (G.twoPlayerShadowGame leaderOne).next (some state)
        profile.1 profile.2 nature =
      some (G.next state actionOne actionTwo nature) := by
  dsimp only
  cases hleader : leaderOne state <;>
    simp [shadowActionProfile, hleader, twoPlayerShadowGame]

/-- Canonical history translation using the rank-correct action permutation. -/
noncomputable def shadowLift (leaderOne : G.ShadowLeaderSignal) :
    G.PlayHistory → (G.twoPlayerShadowGame leaderOne).PlayHistory
  | .initial => .initial
  | .step previous actionOne actionTwo nature =>
      let profile := G.shadowActionProfile leaderOne previous.lastState
        actionOne actionTwo
      (shadowLift leaderOne previous).step profile.1 profile.2 nature

theorem shadowLift_lastState (leaderOne : G.ShadowLeaderSignal)
    (history : G.PlayHistory) :
    (G.shadowLift leaderOne history).lastState = some history.lastState := by
  induction history with
  | initial => rfl
  | step previous actionOne actionTwo nature ih =>
      rw [shadowLift]
      change (G.twoPlayerShadowGame leaderOne).next
        (G.shadowLift leaderOne previous).lastState _ _ nature = _
      rw [ih]
      exact G.twoPlayerShadowGame_next_shadowActionProfile leaderOne
        previous.lastState actionOne actionTwo nature

theorem shadowLift_priority (leaderOne : G.ShadowLeaderSignal)
    (history : G.PlayHistory) :
    (G.twoPlayerShadowGame leaderOne).priority
        (G.shadowLift leaderOne history).lastState =
      G.priority history.lastState := by
  rw [G.shadowLift_lastState]
  rfl

/-- Every shadow history that has not entered the invalid-action sink is the
canonical rank-permuted lift of an actual history. -/
theorem exists_eq_shadowLift_of_lastState_eq_some
    (leaderOne : G.ShadowLeaderSignal)
    (shadow : (G.twoPlayerShadowGame leaderOne).PlayHistory)
    (state : G.State) (hlast : shadow.lastState = some state) :
    ∃ actual : G.PlayHistory, shadow = G.shadowLift leaderOne actual := by
  induction shadow generalizing state with
  | initial =>
      exact ⟨PlayHistory.initial, rfl⟩
  | step previous shadowOne shadowTwo nature ih =>
      change (G.twoPlayerShadowGame leaderOne).next previous.lastState
        shadowOne shadowTwo nature = some state at hlast
      cases hprevious : previous.lastState with
      | none =>
          rw [hprevious, G.twoPlayerShadowGame_next_sink] at hlast
          contradiction
      | some previousState =>
          obtain ⟨actual, hactual⟩ := ih previousState hprevious
          subst previous
          have hstate : actual.lastState = previousState := by
            have h := G.shadowLift_lastState leaderOne actual
            rw [hprevious] at h
            exact Option.some.inj h.symm
          subst previousState
          rw [G.shadowLift_lastState] at hlast
          cases hleader : leaderOne actual.lastState <;>
            cases shadowOne <;> cases shadowTwo <;>
              simp [twoPlayerShadowGame, hleader] at hlast
          · rename_i actionTwo actionOne
            refine ⟨actual.step actionOne actionTwo nature, ?_⟩
            simp [shadowLift, shadowActionProfile, hleader]
          · rename_i actionOne actionTwo
            refine ⟨actual.step actionOne actionTwo nature, ?_⟩
            simp [shadowLift, shadowActionProfile, hleader]

/-- The shadow-one perfect-recall view induced by rank permutation along an
actual history. -/
noncomputable def shadowView1 (leaderOne : G.ShadowLeaderSignal) :
    G.PlayHistory → List (G.twoPlayerShadowGame leaderOne).Observation1
  | .initial =>
      [(G.twoPlayerShadowGame leaderOne).observe1 (some G.initial)]
  | .step previous actionOne actionTwo nature =>
      shadowView1 leaderOne previous ++
        [(G.twoPlayerShadowGame leaderOne).observe1
          (some (G.next previous.lastState actionOne actionTwo nature))]

/-- Shadow two's induced perfect-recall view. -/
noncomputable def shadowView2 (leaderOne : G.ShadowLeaderSignal) :
    G.PlayHistory → List (G.twoPlayerShadowGame leaderOne).Observation2
  | .initial =>
      [(G.twoPlayerShadowGame leaderOne).observe2 (some G.initial)]
  | .step previous actionOne actionTwo nature =>
      shadowView2 leaderOne previous ++
        [(G.twoPlayerShadowGame leaderOne).observe2
          (some (G.next previous.lastState actionOne actionTwo nature))]

theorem shadowLift_observations1 (leaderOne : G.ShadowLeaderSignal)
    (history : G.PlayHistory) :
    (G.shadowLift leaderOne history).observations1 =
      G.shadowView1 leaderOne history := by
  induction history with
  | initial => rfl
  | step previous actionOne actionTwo nature ih =>
      rw [shadowLift, PlayHistory.observations1_step, ih]
      rw [G.shadowLift_lastState]
      rw [G.twoPlayerShadowGame_next_shadowActionProfile]
      rw [shadowView1]

theorem shadowLift_observations2 (leaderOne : G.ShadowLeaderSignal)
    (history : G.PlayHistory) :
    (G.shadowLift leaderOne history).observations2 =
      G.shadowView2 leaderOne history := by
  induction history with
  | initial => rfl
  | step previous actionOne actionTwo nature ih =>
      rw [shadowLift, PlayHistory.observations2_step, ih]
      rw [G.shadowLift_lastState]
      rw [G.twoPlayerShadowGame_next_shadowActionProfile]
      rw [shadowView2]

theorem shadowView1_length (leaderOne : G.ShadowLeaderSignal)
    (history : G.PlayHistory) :
    (G.shadowView1 leaderOne history).length = history.observations1.length := by
  induction history with
  | initial => rfl
  | step previous actionOne actionTwo nature ih =>
      simp [shadowView1, PlayHistory.observations1_step, ih]

theorem shadowView2_length (leaderOne : G.ShadowLeaderSignal)
    (history : G.PlayHistory) :
    (G.shadowView2 leaderOne history).length = history.observations2.length := by
  induction history with
  | initial => rfl
  | step previous actionOne actionTwo nature ih =>
      simp [shadowView2, PlayHistory.observations2_step, ih]

/-! ## Rank signal supplied by the common-signal arena -/

/-- The original rank monitor stored in a common-signal state, read as the
Boolean permutation signal used by the shadows. -/
noncomputable def commonSignalLeaderOne :
    G.commonSignalCrossingEliminationGame.ShadowLeaderSignal :=
  fun state => decide (G.rankOneMachine.output state.2.2.1 = 0)

/-- The concrete two-player shadow arena associated with the corrected
crossing-free common-signal arena. -/
noncomputable abbrev commonSignalShadowGame : FiniteConcurrentGame :=
  G.commonSignalCrossingEliminationGame.twoPlayerShadowGame
    G.commonSignalLeaderOne

/-- The rank permutation is publicly recoverable from player one's current
common-signal observation. -/
theorem commonSignalLeaderOne_eq_of_observe1_eq
    (left right : G.commonSignalCrossingEliminationGame.State)
    (heq : G.commonSignalCrossingEliminationGame.observe1 left =
      G.commonSignalCrossingEliminationGame.observe1 right) :
    G.commonSignalLeaderOne left = G.commonSignalLeaderOne right := by
  rcases left with ⟨leftPhase, leftState, leftRankOne, leftRankTwo⟩
  rcases right with ⟨rightPhase, rightState, rightRankOne, rightRankTwo⟩
  cases leftPhase <;> cases rightPhase <;>
    simp_all [commonSignalCrossingEliminationGame, commonSignalLeaderOne]
  by_cases hleft : G.rankOneMachine.output leftRankOne = 0 <;>
    by_cases hright : G.rankOneMachine.output rightRankOne = 0 <;>
      simp_all

theorem commonSignalLeaderOne_lift_iff
    (history : G.PlayHistory) :
    G.commonSignalLeaderOne (G.commonSignalLift history).lastState = true ↔
      G.OneDeterminesTwoAt history := by
  rw [G.commonSignalLift_lastState]
  simp only [commonSignalLeaderOne, decide_eq_true_eq]
  rw [G.rankOneMachine_output_run, G.informationRankOne_eq_zero_iff]

theorem commonSignalLeaderOne_bridge_iff
    (history : G.PlayHistory) (actionOne : G.Action1)
    (actionTwo : G.Action2) (nature : G.Nature) :
    G.commonSignalLeaderOne
        (G.commonSignalBridgeLift history actionOne actionTwo nature).lastState = true ↔
      G.OneDeterminesTwoAt (history.step actionOne actionTwo nature) := by
  rw [G.commonSignalBridgeLift_lastState]
  simp only [commonSignalLeaderOne, decide_eq_true_eq]
  rw [G.rankOneMachine_output_run, G.informationRankOne_eq_zero_iff]

/-- At a canonical original-phase position, the player selected for shadow
role one determines the other player. -/
theorem commonSignalLift_selectedDetermines
    (hhier : G.DynamicHierarchy) (history : G.PlayHistory) :
    if G.commonSignalLeaderOne (G.commonSignalLift history).lastState then
      G.commonSignalCrossingEliminationGame.OneDeterminesTwoAt
        (G.commonSignalLift history)
    else
      G.commonSignalCrossingEliminationGame.TwoDeterminesOneAt
        (G.commonSignalLift history) := by
  cases hleader : G.commonSignalLeaderOne
      (G.commonSignalLift history).lastState with
  | true =>
      simp only [hleader, if_true]
      apply (G.commonSignalLift_oneDeterminesTwoAt_iff hhier history).mpr
      exact (G.commonSignalLeaderOne_lift_iff history).mp hleader
  | false =>
      apply (G.commonSignalLift_twoDeterminesOneAt_iff hhier history).mpr
      have hnotOne : ¬ G.OneDeterminesTwoAt history := by
        intro hone
        have : G.commonSignalLeaderOne
            (G.commonSignalLift history).lastState = true :=
          (G.commonSignalLeaderOne_lift_iff history).mpr hone
        rw [hleader] at this
        contradiction
      exact (hhier history).resolve_left hnotOne

/-- At a canonical bridge position, the player selected by the *target* rank
determines the other.  If the selected rank differs from the source rank, the
strengthened rank-switch bridge theorem supplies a full tie. -/
theorem commonSignalBridge_selectedDetermines
    (hhier : G.DynamicHierarchy) (history : G.PlayHistory)
    (actionOne : G.Action1) (actionTwo : G.Action2) (nature : G.Nature) :
    if G.commonSignalLeaderOne
        (G.commonSignalBridgeLift history actionOne actionTwo nature).lastState then
      G.commonSignalCrossingEliminationGame.OneDeterminesTwoAt
        (G.commonSignalBridgeLift history actionOne actionTwo nature)
    else
      G.commonSignalCrossingEliminationGame.TwoDeterminesOneAt
        (G.commonSignalBridgeLift history actionOne actionTwo nature) := by
  let target := history.step actionOne actionTwo nature
  cases hleader : G.commonSignalLeaderOne
      (G.commonSignalBridgeLift history actionOne actionTwo nature).lastState with
  | true =>
      simp only [hleader, if_true]
      have htargetOne : G.OneDeterminesTwoAt target :=
        (G.commonSignalLeaderOne_bridge_iff history actionOne actionTwo nature).mp
          hleader
      by_cases hsourceOne : G.OneDeterminesTwoAt history
      · exact G.commonSignalBridge_oneDeterminesTwoAt_of_source hhier history
          actionOne actionTwo nature hsourceOne
      · have hsourceTwo : G.TwoDeterminesOneAt history :=
          (hhier history).resolve_left hsourceOne
        exact (G.commonSignalBridge_tie_two_to_one hhier history actionOne
          actionTwo nature ⟨hsourceTwo, hsourceOne⟩ htargetOne).1
  | false =>
      have htargetNotOne : ¬ G.OneDeterminesTwoAt target := by
        intro htargetOne
        have : G.commonSignalLeaderOne
            (G.commonSignalBridgeLift history actionOne actionTwo nature).lastState =
              true :=
          (G.commonSignalLeaderOne_bridge_iff history actionOne actionTwo nature).mpr
            htargetOne
        rw [hleader] at this
        contradiction
      have htargetTwo : G.TwoDeterminesOneAt target :=
        (hhier target).resolve_left htargetNotOne
      by_cases hsourceOne : G.OneDeterminesTwoAt history
      · exact (G.commonSignalBridge_tie_one_to_two hhier history actionOne
          actionTwo nature hsourceOne ⟨htargetTwo, htargetNotOne⟩).2
      · exact G.commonSignalBridge_twoDeterminesOneAt_of_source hhier history
          actionOne actionTwo nature ((hhier history).resolve_left hsourceOne)

/-- The rank-selected player determines the other at every history of the
common-signal arena, including histories that are not definitionally one of
the canonical lifts.  Arbitrary doubled histories have the same two views as
a canonical lift or bridge, and determination depends only on those views. -/
theorem commonSignal_selectedDetermines
    (hhier : G.DynamicHierarchy)
    (doubled : G.commonSignalCrossingEliminationGame.PlayHistory) :
    if G.commonSignalLeaderOne doubled.lastState then
      G.commonSignalCrossingEliminationGame.OneDeterminesTwoAt doubled
    else
      G.commonSignalCrossingEliminationGame.TwoDeterminesOneAt doubled := by
  obtain ⟨phase, history, rep⟩ := G.exists_commonSignalRep doubled
  cases phase with
  | false =>
      have hobs := G.commonSignalRep_observation_normal rep
      simp only [CommonSignalObservationNormal, Bool.false_eq_true, if_false]
        at hobs
      have hstate : doubled.lastState = (G.commonSignalLift history).lastState := by
        rw [G.commonSignalRep_lastState rep, G.commonSignalLift_lastState]
      have hcanonical := G.commonSignalLift_selectedDetermines hhier history
      rw [hstate]
      cases hleader : G.commonSignalLeaderOne
          (G.commonSignalLift history).lastState with
      | false =>
          simp only [hleader, Bool.false_eq_true, if_false] at hcanonical ⊢
          exact (twoDeterminesOneAt_congr hobs.1 hobs.2).mpr hcanonical
      | true =>
          simp only [hleader, if_true] at hcanonical ⊢
          exact (oneDeterminesTwoAt_congr hobs.1 hobs.2).mpr hcanonical
  | true =>
      have hobs := G.commonSignalRep_observation_normal rep
      simp only [CommonSignalObservationNormal, if_true] at hobs
      obtain ⟨previous, actionOne, actionTwo, nature, hhistory, hobsOne,
        hobsTwo⟩ := hobs
      subst history
      have hstate : doubled.lastState =
          (G.commonSignalBridgeLift previous actionOne actionTwo nature).lastState := by
        rw [G.commonSignalRep_lastState rep, G.commonSignalBridgeLift_lastState]
      have hcanonical := G.commonSignalBridge_selectedDetermines hhier previous
        actionOne actionTwo nature
      rw [hstate]
      cases hleader : G.commonSignalLeaderOne
          (G.commonSignalBridgeLift previous actionOne actionTwo nature).lastState with
      | false =>
          simp only [hleader, Bool.false_eq_true, if_false] at hcanonical ⊢
          exact (twoDeterminesOneAt_congr hobsOne hobsTwo).mpr hcanonical
      | true =>
          simp only [hleader, if_true] at hcanonical ⊢
          exact (oneDeterminesTwoAt_congr hobsOne hobsTwo).mpr hcanonical

/-! ## Perfect-recall information carried by the leading shadow -/

/-- Shadow one sees exactly the joint perfect-recall information of the two
actual players.  The forward direction uses the determining player selected
at every prefix; the reverse direction uses that the rank permutation is
recoverable from player one's current common-signal observation. -/
theorem commonSignalShadowView1_eq_iff
    (hhier : G.DynamicHierarchy)
    (left right : G.commonSignalCrossingEliminationGame.PlayHistory) :
    G.commonSignalCrossingEliminationGame.shadowView1
        G.commonSignalLeaderOne left =
      G.commonSignalCrossingEliminationGame.shadowView1
        G.commonSignalLeaderOne right ↔
      left.observations1 = right.observations1 ∧
        left.observations2 = right.observations2 := by
  induction left generalizing right with
  | initial =>
      cases right with
      | initial => simp [shadowView1]
      | step previous actionOne actionTwo nature =>
          constructor
          · intro hshadow
            have hlength := congrArg List.length hshadow
            rw [G.commonSignalCrossingEliminationGame.shadowView1_length,
              G.commonSignalCrossingEliminationGame.shadowView1_length] at hlength
            rw [PlayHistory.observations1_step] at hlength
            have hpos :=
              G.commonSignalCrossingEliminationGame.observations1_length_pos previous
            simp only [PlayHistory.observations1_initial, List.length_singleton,
              List.length_append] at hlength
            omega
          · rintro ⟨hone, _⟩
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
          constructor
          · intro hshadow
            have hlength := congrArg List.length hshadow
            rw [G.commonSignalCrossingEliminationGame.shadowView1_length,
              G.commonSignalCrossingEliminationGame.shadowView1_length] at hlength
            rw [PlayHistory.observations1_step] at hlength
            have hpos :=
              G.commonSignalCrossingEliminationGame.observations1_length_pos leftPrevious
            simp only [PlayHistory.observations1_initial, List.length_singleton,
              List.length_append] at hlength
            omega
          · rintro ⟨hone, _⟩
            have hlength := congrArg List.length hone
            rw [PlayHistory.observations1_step] at hlength
            have hpos :=
              G.commonSignalCrossingEliminationGame.observations1_length_pos leftPrevious
            simp only [PlayHistory.observations1_initial, List.length_singleton,
              List.length_append] at hlength
            omega
      | step rightPrevious rightActionOne rightActionTwo rightNature =>
          let leftTarget := G.commonSignalCrossingEliminationGame.next
            leftPrevious.lastState leftActionOne leftActionTwo leftNature
          let rightTarget := G.commonSignalCrossingEliminationGame.next
            rightPrevious.lastState rightActionOne rightActionTwo rightNature
          constructor
          · intro hshadow
            rw [shadowView1, shadowView1] at hshadow
            obtain ⟨hprefixShadow, hlastList⟩ :=
              List.append_inj' hshadow (by simp)
            have hprefix := (ih rightPrevious).mp hprefixShadow
            have hlast := List.singleton_inj.mp hlastList
            change
              (G.commonSignalCrossingEliminationGame.twoPlayerShadowGame
                G.commonSignalLeaderOne).observe1 (some leftTarget) =
              (G.commonSignalCrossingEliminationGame.twoPlayerShadowGame
                G.commonSignalLeaderOne).observe1 (some rightTarget) at hlast
            cases hleft : G.commonSignalLeaderOne leftTarget <;>
              cases hright : G.commonSignalLeaderOne rightTarget
            · simp [twoPlayerShadowGame, hleft, hright] at hlast
              have htwo :
                  (leftPrevious.step leftActionOne leftActionTwo leftNature).observations2 =
                    (rightPrevious.step rightActionOne rightActionTwo
                      rightNature).observations2 := by
                rw [PlayHistory.observations2_step,
                  PlayHistory.observations2_step]
                exact congrArg₂ (fun xs x => xs ++ [x])
                  hprefix.2 hlast
              have hdetermines := G.commonSignal_selectedDetermines hhier
                (leftPrevious.step leftActionOne leftActionTwo leftNature)
              change (if G.commonSignalLeaderOne leftTarget then
                G.commonSignalCrossingEliminationGame.OneDeterminesTwoAt
                  (leftPrevious.step leftActionOne leftActionTwo leftNature)
              else
                G.commonSignalCrossingEliminationGame.TwoDeterminesOneAt
                  (leftPrevious.step leftActionOne leftActionTwo leftNature))
                at hdetermines
              simp only [hleft, Bool.false_eq_true, if_false] at hdetermines
              exact ⟨(hdetermines _ htwo.symm).symm, htwo⟩
            · simp [twoPlayerShadowGame, hleft, hright] at hlast
            · simp [twoPlayerShadowGame, hleft, hright] at hlast
            · simp [twoPlayerShadowGame, hleft, hright] at hlast
              have hone :
                  (leftPrevious.step leftActionOne leftActionTwo leftNature).observations1 =
                    (rightPrevious.step rightActionOne rightActionTwo
                      rightNature).observations1 := by
                rw [PlayHistory.observations1_step,
                  PlayHistory.observations1_step]
                exact congrArg₂ (fun xs x => xs ++ [x])
                  hprefix.1 hlast
              have hdetermines := G.commonSignal_selectedDetermines hhier
                (leftPrevious.step leftActionOne leftActionTwo leftNature)
              change (if G.commonSignalLeaderOne leftTarget then
                G.commonSignalCrossingEliminationGame.OneDeterminesTwoAt
                  (leftPrevious.step leftActionOne leftActionTwo leftNature)
              else
                G.commonSignalCrossingEliminationGame.TwoDeterminesOneAt
                  (leftPrevious.step leftActionOne leftActionTwo leftNature))
                at hdetermines
              simp only [hleft, if_true] at hdetermines
              exact ⟨hone, (hdetermines _ hone.symm).symm⟩
          · rintro ⟨hone, htwo⟩
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
            have hprefixShadow :=
              (ih rightPrevious).mpr ⟨honePrefix, htwoPrefix⟩
            have hleader : G.commonSignalLeaderOne leftTarget =
                G.commonSignalLeaderOne rightTarget :=
              G.commonSignalLeaderOne_eq_of_observe1_eq leftTarget rightTarget
                honeLast
            rw [shadowView1, shadowView1]
            refine congrArg₂ (fun xs x => xs ++ [x])
              hprefixShadow ?_
            change
              (G.commonSignalCrossingEliminationGame.twoPlayerShadowGame
                G.commonSignalLeaderOne).observe1 (some leftTarget) =
              (G.commonSignalCrossingEliminationGame.twoPlayerShadowGame
                G.commonSignalLeaderOne).observe1 (some rightTarget)
            cases hleft : G.commonSignalLeaderOne leftTarget
            · have hright : G.commonSignalLeaderOne rightTarget = false := by
                rw [← hleader, hleft]
              simp [twoPlayerShadowGame, hleft, hright, htwoLast]
              exact htwoLast
            · have hright : G.commonSignalLeaderOne rightTarget = true := by
                rw [← hleader, hleft]
              simp [twoPlayerShadowGame, hleft, hright, honeLast]
              exact honeLast

theorem commonSignalShadowView2_eq_of_both
    (left right : G.commonSignalCrossingEliminationGame.PlayHistory)
    (hone : left.observations1 = right.observations1)
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
            simp [twoPlayerShadowGame, hleft, hright]
            exact htwoLast

/-- On two nonsink shadow histories, equality of the leading-shadow view
forces equality of the second-shadow view. -/
theorem commonSignalShadow_observations2_eq_of_observations1_eq_of_some
    (hhier : G.DynamicHierarchy)
    (left right : G.commonSignalShadowGame.PlayHistory)
    (leftState rightState : G.commonSignalCrossingEliminationGame.State)
    (hleft : left.lastState = some leftState)
    (hright : right.lastState = some rightState)
    (heq : left.observations1 = right.observations1) :
    left.observations2 = right.observations2 := by
  obtain ⟨leftActual, rfl⟩ :=
    G.commonSignalCrossingEliminationGame.exists_eq_shadowLift_of_lastState_eq_some
      G.commonSignalLeaderOne left leftState hleft
  obtain ⟨rightActual, rfl⟩ :=
    G.commonSignalCrossingEliminationGame.exists_eq_shadowLift_of_lastState_eq_some
      G.commonSignalLeaderOne right rightState hright
  rw [G.commonSignalCrossingEliminationGame.shadowLift_observations1,
    G.commonSignalCrossingEliminationGame.shadowLift_observations1] at heq
  have hjoint := (G.commonSignalShadowView1_eq_iff hhier
    leftActual rightActual).mp heq
  rw [G.commonSignalCrossingEliminationGame.shadowLift_observations2,
    G.commonSignalCrossingEliminationGame.shadowLift_observations2]
  exact G.commonSignalShadowView2_eq_of_both leftActual rightActual
    hjoint.1 hjoint.2

/-- The rank-permuted shadow arena has a fixed information hierarchy: shadow
one determines shadow two at every history, including histories in the public
invalid-action sink. -/
theorem commonSignalShadowGame_oneDeterminesTwoAt
    (hhier : G.DynamicHierarchy)
    (history : G.commonSignalShadowGame.PlayHistory) :
    G.commonSignalShadowGame.OneDeterminesTwoAt history := by
  induction history with
  | initial =>
      intro alternative heq
      have hlastObs := congrArg List.getLast? heq
      rw [PlayHistory.observations1_getLast?_last,
        PlayHistory.observations1_getLast?_last] at hlastObs
      have hlastObs := Option.some.inj hlastObs
      cases hstate : alternative.lastState with
      | none =>
          rw [hstate] at hlastObs
          cases hleader : G.commonSignalLeaderOne
              G.commonSignalCrossingEliminationGame.initial <;>
            simp [commonSignalShadowGame, twoPlayerShadowGame, hleader,
              PlayHistory.lastState]
              at hlastObs
      | some state =>
          exact G.commonSignalShadow_observations2_eq_of_observations1_eq_of_some
            hhier alternative PlayHistory.initial
            state G.commonSignalCrossingEliminationGame.initial hstate rfl heq
  | step previous shadowOne shadowTwo nature ih =>
      intro alternative heq
      cases hcurrent :
          (previous.step shadowOne shadowTwo nature).lastState with
      | some state =>
          have hlastObs := congrArg List.getLast? heq
          rw [PlayHistory.observations1_getLast?_last,
            PlayHistory.observations1_getLast?_last] at hlastObs
          have hlastObs := Option.some.inj hlastObs
          cases halternative : alternative.lastState with
          | none =>
              rw [halternative, hcurrent] at hlastObs
              cases hleader : G.commonSignalLeaderOne state <;>
                simp [commonSignalShadowGame, twoPlayerShadowGame, hleader]
                  at hlastObs
          | some alternativeState =>
              exact G.commonSignalShadow_observations2_eq_of_observations1_eq_of_some
                hhier alternative (previous.step shadowOne shadowTwo nature)
                alternativeState state halternative hcurrent heq
      | none =>
          cases alternative with
          | initial =>
              have hlastObs := congrArg List.getLast? heq
              rw [PlayHistory.observations1_getLast?_last,
                PlayHistory.observations1_getLast?_last] at hlastObs
              have hlastObs := Option.some.inj hlastObs
              rw [hcurrent] at hlastObs
              cases hleader : G.commonSignalLeaderOne
                  G.commonSignalCrossingEliminationGame.initial <;>
                simp [commonSignalShadowGame, twoPlayerShadowGame, hleader,
                  PlayHistory.lastState]
                  at hlastObs
          | step alternativePrevious alternativeOne alternativeTwo
              alternativeNature =>
              rw [PlayHistory.observations1_step,
                PlayHistory.observations1_step] at heq
              obtain ⟨hprefix, hlastList⟩ :=
                List.append_inj' heq (by simp)
              have hprefixTwo := ih alternativePrevious hprefix
              have hlastObs := List.singleton_inj.mp hlastList
              have halternative :
                  (alternativePrevious.step alternativeOne alternativeTwo
                    alternativeNature).lastState = none := by
                cases hstate :
                    (alternativePrevious.step alternativeOne alternativeTwo
                      alternativeNature).lastState with
                | none => rfl
                | some state =>
                    change G.commonSignalShadowGame.next
                      alternativePrevious.lastState alternativeOne alternativeTwo
                        alternativeNature = some state at hstate
                    change G.commonSignalShadowGame.next previous.lastState
                      shadowOne shadowTwo nature = none at hcurrent
                    rw [hstate, hcurrent] at hlastObs
                    cases hleader : G.commonSignalLeaderOne state <;>
                      simp [commonSignalShadowGame, twoPlayerShadowGame,
                        hleader] at hlastObs
              rw [PlayHistory.observations2_step,
                PlayHistory.observations2_step]
              refine congrArg₂ (fun xs x => xs ++ [x]) hprefixTwo ?_
              change G.commonSignalShadowGame.next
                alternativePrevious.lastState alternativeOne alternativeTwo
                  alternativeNature = none at halternative
              change G.commonSignalShadowGame.next previous.lastState
                shadowOne shadowTwo nature = none at hcurrent
              rw [halternative, hcurrent]

theorem commonSignalShadowGame_dynamicHierarchy
    (hhier : G.DynamicHierarchy) :
    G.commonSignalShadowGame.DynamicHierarchy := by
  intro history
  exact Or.inl (G.commonSignalShadowGame_oneDeterminesTwoAt hhier history)

end FiniteConcurrentGame

end DistributedSynthesis
