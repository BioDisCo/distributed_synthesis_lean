/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedPhysicalCompatiblePolicyBankLocalPhaseLiveOwnerFibreRelation

/-!
# Blind-output laws for the owner-fibre recurrent carrier

The operational relation proves that one mutually selected pair of underlying
controls remains semantically valid.  The acknowledged exact-closing wrapper
also stores unresolved open/closed forks.  This file proves that every such
fork emits one local no-receive output and remains blind-related until it is
resolved.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
  [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

variable
  (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
  (hwin : ∀ env : EnvironmentSequence In₁ In₂,
    A.Accepts (execution strategy env))

/-! ## Endpoint-local blind relations -/

inductive ProfiledRawJointRecurrentOwnerFibreBoundaryOneBlind :
    ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin →
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin →
        Prop
  | bridge {left right leftCoordinates rightCoordinates}
      (hblind : ProfiledRawJointRecurrentLeftToRightBridgeBlind A strategy hwin
        left right) :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneBlind
        (.inl left, leftCoordinates) (.inl right, rightCoordinates)
  | fibre {left right leftCoordinates rightCoordinates}
      (hblind : FiniteAcknowledgedDelayedCarrier.DeferredMemberBlind left
        right) :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneBlind
        (.inr left, leftCoordinates) (.inr right, rightCoordinates)

inductive ProfiledRawJointRecurrentOwnerFibreBoundaryTwoBlind :
    ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin →
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin →
        Prop
  | bridge {left right leftCoordinates rightCoordinates}
      (hblind : ProfiledRawJointRecurrentRightToLeftBridgeBlind A strategy hwin
        left right) :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoBlind
        (.inl left, leftCoordinates) (.inl right, rightCoordinates)
  | fibre {left right leftCoordinates rightCoordinates}
      (hblind : FiniteAcknowledgedDelayedCarrier.DeferredMemberBlind left
        right) :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoBlind
        (.inr left, leftCoordinates) (.inr right, rightCoordinates)

theorem profiledRawJointRecurrentOwnerFibreBoundaryOneBlind_noRecv
    (left right :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin)
    (input : In₁)
    (hblind :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneBlind A strategy hwin left
        right) :
    (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvOne A strategy hwin left
        input).2 =
        (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvOne A strategy hwin
          right input).2 ∧
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneBlind A strategy hwin
        (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvOne A strategy hwin
          left input).1
        (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvOne A strategy hwin
          right input).1 := by
  cases hblind with
  | bridge hblind =>
      obtain ⟨hout, hnext⟩ :=
        profiledRawJointRecurrentLeftToRightBridgeBlind_noRecv A strategy hwin
          _ _ input hblind
      exact ⟨hout, .bridge hnext⟩
  | fibre hblind =>
      obtain ⟨hout, hnext⟩ :=
        profiledRawJointRecurrentRightToLeftOwnerFibre_blind_noRecv A strategy
          hwin _ _ input hblind
      exact ⟨hout, .fibre hnext⟩

theorem profiledRawJointRecurrentOwnerFibreBoundaryTwoBlind_noRecv
    (left right :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin)
    (input : In₂)
    (hblind :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoBlind A strategy hwin left
        right) :
    (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvTwo A strategy hwin left
        input).2 =
        (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvTwo A strategy hwin
          right input).2 ∧
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoBlind A strategy hwin
        (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvTwo A strategy hwin
          left input).1
        (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvTwo A strategy hwin
          right input).1 := by
  cases hblind with
  | bridge hblind =>
      obtain ⟨hout, hnext⟩ :=
        profiledRawJointRecurrentRightToLeftBridgeBlind_noRecv A strategy hwin
          _ _ input hblind
      exact ⟨hout, .bridge hnext⟩
  | fibre hblind =>
      obtain ⟨hout, hnext⟩ :=
        profiledRawJointRecurrentLeftToRightOwnerFibre_blind_noRecv A strategy
          hwin _ _ input hblind
      exact ⟨hout, .fibre hnext⟩

noncomputable def
    profiledRawJointRecurrentOwnerFibreBoundaryBlindNoRecvLaws :
    FiniteAcknowledgedDelayedCarrier.BlindNoRecvLaws
      (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvOne A strategy hwin)
      (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvTwo A strategy hwin)
      (ProfiledRawJointRecurrentOwnerFibreBoundaryOneBlind A strategy hwin)
      (ProfiledRawJointRecurrentOwnerFibreBoundaryTwoBlind A strategy hwin)
    where
  one :=
    profiledRawJointRecurrentOwnerFibreBoundaryOneBlind_noRecv A strategy hwin
  two :=
    profiledRawJointRecurrentOwnerFibreBoundaryTwoBlind_noRecv A strategy hwin

/-! ## Receive-created blind forks -/

theorem
    ProfiledRawJointRecurrentRightPhaseLiveBoundaryData.ownerFibreReceive_blind_one
    (phaseData :
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryData A strategy hwin)
    (input : In₁ × In₂) :
    let result := phaseData.ownerFibreReceive A strategy hwin input
    ProfiledRawJointRecurrentOwnerFibreBoundaryOneBlind A strategy hwin
      result.1.1.openControl result.1.1.closedControl := by
  dsimp only [ProfiledRawJointRecurrentRightPhaseLiveBoundaryData.ownerFibreReceive,
    ProfiledRawJointRecurrentRightBoundaryData.ownerFibreReceive]
  apply ProfiledRawJointRecurrentOwnerFibreBoundaryOneBlind.fibre
  exact FiniteAcknowledgedDelayedCarrier.deferredMemberFork_blind _ _

theorem
    ProfiledRawJointRecurrentRightPhaseLiveBoundaryData.ownerFibreReceive_blind_two
    (phaseData :
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryData A strategy hwin)
    (hinvariant :
      ProfiledRawJointRecurrentRightBoundaryInvariant A strategy hwin
        phaseData.1)
    (input : In₁ × In₂) :
    let result := phaseData.ownerFibreReceive A strategy hwin input
    ProfiledRawJointRecurrentOwnerFibreBoundaryTwoBlind A strategy hwin
      result.2.1.openControl result.2.1.closedControl := by
  obtain ⟨hrealizes, root, hroot⟩ :=
    (profiledRawJointRecurrentRightBoundaryInvariant_ready A strategy hwin
      phaseData.1 hinvariant) input
  dsimp only [ProfiledRawJointRecurrentRightPhaseLiveBoundaryData.ownerFibreReceive]
  apply ProfiledRawJointRecurrentOwnerFibreBoundaryTwoBlind.bridge
  exact
    profiledRawJointRecurrentPhaseRightToLeftBridgeForkTwo_blind A strategy
      hwin phaseData.1.1 (phaseData.1.receiver A strategy hwin)
        (phaseData.1.owner A strategy hwin) (input.2, input.1) _ rfl hrealizes
          root hroot

theorem
    ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData.ownerFibreReceive_blind_one
    (phaseData :
      ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData A strategy hwin)
    (hinvariant :
      ProfiledRawJointRecurrentLeftBoundaryInvariant A strategy hwin
        phaseData.1)
    (input : In₁ × In₂) :
    let result := phaseData.ownerFibreReceive A strategy hwin input
    ProfiledRawJointRecurrentOwnerFibreBoundaryOneBlind A strategy hwin
      result.1.1.openControl result.1.1.closedControl := by
  obtain ⟨hrealizes, root, hroot⟩ :=
    (profiledRawJointRecurrentLeftBoundaryInvariant_ready A strategy hwin
      phaseData.1 hinvariant) input
  dsimp only [ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData.ownerFibreReceive]
  apply ProfiledRawJointRecurrentOwnerFibreBoundaryOneBlind.bridge
  exact
    profiledRawJointRecurrentPhaseLeftToRightBridgeForkOne_blind A strategy
      hwin phaseData.1.1 (phaseData.1.receiver A strategy hwin)
        (phaseData.1.owner A strategy hwin) input _ rfl hrealizes root hroot

theorem
    ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData.ownerFibreReceive_blind_two
    (phaseData :
      ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData A strategy hwin)
    (input : In₁ × In₂) :
    let result := phaseData.ownerFibreReceive A strategy hwin input
    ProfiledRawJointRecurrentOwnerFibreBoundaryTwoBlind A strategy hwin
      result.2.1.openControl result.2.1.closedControl := by
  dsimp only [ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData.ownerFibreReceive,
    ProfiledRawJointRecurrentLeftBoundaryData.ownerFibreReceive]
  apply ProfiledRawJointRecurrentOwnerFibreBoundaryTwoBlind.fibre
  exact FiniteAcknowledgedDelayedCarrier.deferredMemberFork_blind _ _

theorem profiledRawJointRecurrentOwnerFibreBoundaryReceive?_of_right
    (one :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin)
    (two :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin)
    (phaseData :
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryData A strategy hwin)
    (hdata :
      profiledRawJointRecurrentOwnerFibreRightBoundaryData? A strategy hwin
        one two = some phaseData)
    (input : In₁ × In₂) :
    profiledRawJointRecurrentOwnerFibreBoundaryReceive? A strategy hwin one two
        input =
      some (phaseData.ownerFibreReceive A strategy hwin input) := by
  simp [profiledRawJointRecurrentOwnerFibreBoundaryReceive?, hdata]

theorem profiledRawJointRecurrentOwnerFibreBoundaryReceive?_of_left
    (one :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin)
    (two :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin)
    (phaseData :
      ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData A strategy hwin)
    (hright :
      profiledRawJointRecurrentOwnerFibreRightBoundaryData? A strategy hwin
        one two = none)
    (hdata :
      profiledRawJointRecurrentOwnerFibreLeftBoundaryData? A strategy hwin
        one two = some phaseData)
    (input : In₁ × In₂) :
    profiledRawJointRecurrentOwnerFibreBoundaryReceive? A strategy hwin one two
        input =
      some (phaseData.ownerFibreReceive A strategy hwin input) := by
  simp [profiledRawJointRecurrentOwnerFibreBoundaryReceive?, hright, hdata]

/-- Every receive-created owner-fibre fork satisfies the endpoint-local blind
relations.  The semantic operational relation is used only through its
selected decoder and the active matched-prefix certificate. -/
noncomputable def
    profiledRawJointRecurrentOwnerFibreBoundaryBlindReceiveLaws :
    FiniteAcknowledgedDelayedCarrier.ExactClosingBlindReceiveLaws
      (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne A strategy hwin)
      (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo A strategy hwin)
      (profiledRawJointRecurrentOwnerFibreBoundaryClose A strategy hwin)
      (ProfiledRawJointRecurrentOwnerFibreBoundaryOperational A strategy hwin)
      (ProfiledRawJointRecurrentOwnerFibreBoundaryOneBlind A strategy hwin)
      (ProfiledRawJointRecurrentOwnerFibreBoundaryTwoBlind A strategy hwin)
    where
  one := by
    intro one inputOne two inputTwo hoperational
    cases hoperational.selected with
    | right phaseData hdata hinvariant =>
        have hreceive :=
          profiledRawJointRecurrentOwnerFibreBoundaryReceive?_of_right A
            strategy hwin one two phaseData hdata (inputOne, inputTwo)
        simp only [profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne,
          profiledRawJointRecurrentOwnerFibreBoundaryClose, hreceive]
        exact phaseData.ownerFibreReceive_blind_one A strategy hwin
          (inputOne, inputTwo)
    | left phaseData hright hdata hinvariant =>
        have hreceive :=
          profiledRawJointRecurrentOwnerFibreBoundaryReceive?_of_left A
            strategy hwin one two phaseData hright hdata (inputOne, inputTwo)
        simp only [profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne,
          profiledRawJointRecurrentOwnerFibreBoundaryClose, hreceive]
        exact phaseData.ownerFibreReceive_blind_one A strategy hwin
          hinvariant.1 (inputOne, inputTwo)
  two := by
    intro one inputOne two inputTwo hoperational
    cases hoperational.selected with
    | right phaseData hdata hinvariant =>
        have hreceive :=
          profiledRawJointRecurrentOwnerFibreBoundaryReceive?_of_right A
            strategy hwin one two phaseData hdata (inputOne, inputTwo)
        simp only [profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo,
          profiledRawJointRecurrentOwnerFibreBoundaryClose, hreceive]
        exact phaseData.ownerFibreReceive_blind_two A strategy hwin
          hinvariant.1 (inputOne, inputTwo)
    | left phaseData hright hdata hinvariant =>
        have hreceive :=
          profiledRawJointRecurrentOwnerFibreBoundaryReceive?_of_left A
            strategy hwin one two phaseData hright hdata (inputOne, inputTwo)
        simp only [profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo,
          profiledRawJointRecurrentOwnerFibreBoundaryClose, hreceive]
        exact phaseData.ownerFibreReceive_blind_two A strategy hwin
          (inputOne, inputTwo)

/-! ## Complete acknowledged-kernel laws -/

/-- A certified recurrent entry pair supplies the full model-facing law
bundle: selected-pair closure, blind no-receive preservation, and
receive-created fork coherence. -/
noncomputable def
    profiledRawJointRecurrentOwnerFibreBoundaryBlindForkLaws
    (initialOne :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin)
    (initialTwo :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin)
    (hinitial :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOperational A strategy hwin
        initialOne initialTwo) :
    FiniteAcknowledgedDelayedCarrier.ExactClosingBlindForkLaws
      initialOne initialTwo
      (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvOne A strategy hwin)
      (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvTwo A strategy hwin)
      (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne A strategy hwin)
      (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo A strategy hwin)
      (profiledRawJointRecurrentOwnerFibreBoundaryClose A strategy hwin)
      (ProfiledRawJointRecurrentOwnerFibreBoundaryOperational A strategy hwin)
      (ProfiledRawJointRecurrentOwnerFibreBoundaryOneBlind A strategy hwin)
      (ProfiledRawJointRecurrentOwnerFibreBoundaryTwoBlind A strategy hwin)
    where
  relation :=
    profiledRawJointRecurrentOwnerFibreBoundaryRelationLaws A strategy hwin
      initialOne initialTwo hinitial
  noRecv :=
    profiledRawJointRecurrentOwnerFibreBoundaryBlindNoRecvLaws A strategy hwin
  receive :=
    profiledRawJointRecurrentOwnerFibreBoundaryBlindReceiveLaws A strategy hwin

end

end DetParityAutomaton

end DistributedSynthesis
