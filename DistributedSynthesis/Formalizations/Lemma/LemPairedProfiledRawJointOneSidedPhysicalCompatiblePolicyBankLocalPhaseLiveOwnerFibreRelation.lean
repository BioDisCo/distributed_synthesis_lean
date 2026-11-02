/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedPhysicalCompatiblePolicyBankLocalPhaseLiveOwnerFibreOperational

/-!
# Operational relation for the owner-fibre boundary carrier

Decoder success is not by itself an inductive invariant.  A dormant fibre
must carry a genuine reachable-owner certificate, and a staged control must
retain the bank coordinate that becomes live if the next strict round has the
opposite direction.  Complete equality of the two coordinate registers is
neither needed nor preserved.

This file isolates those two bookkeeping conditions.  Their preservation is
independent of the remaining semantic strict-round case split.
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

private abbrev BankControl :=
  ProfiledRawJointOneSidedPhysicalCompatibleBankControl A strategy hwin

/-- Every pending first-endpoint payload carries a valid right owner fibre. -/
def ProfiledRawJointRecurrentOwnerFibreBoundaryOneValid
    (one :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin) :
    Prop :=
  match one.1 with
  | .inl _ => True
  | .inr pending =>
      ProfiledRawJointRecurrentRightToLeftOwnerFibreValid A strategy hwin
        pending

/-- Every pending second-endpoint payload carries a valid left owner fibre. -/
def ProfiledRawJointRecurrentOwnerFibreBoundaryTwoValid
    (two :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin) :
    Prop :=
  match two.1 with
  | .inl _ => True
  | .inr pending =>
      ProfiledRawJointRecurrentLeftToRightOwnerFibreValid A strategy hwin
        pending

/-- A staged left receiver at process one retains its active left bank state
in the second coordinate. -/
def ProfiledRawJointRecurrentOwnerFibreBoundaryOneStagedAnchor
    (one :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin) :
    Prop :=
  ∀ staged, one.1 = .inl (.inl staged) → one.2.2 = staged.1

/-- A staged right receiver at process two retains its active right bank
state in the first coordinate. -/
def ProfiledRawJointRecurrentOwnerFibreBoundaryTwoStagedAnchor
    (two :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin) :
    Prop :=
  ∀ staged, two.1 = .inl (.inl staged) → two.2.1 = staged.1

/-- Only staged receivers need latent coordinate constraints.  The two
implications are kept independently; in particular, the definition does not
silently discard one constraint if both endpoints are staged. -/
def ProfiledRawJointRecurrentOwnerFibreBoundaryStagedAnchor
    (one :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin)
    (two :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin) :
    Prop :=
  ProfiledRawJointRecurrentOwnerFibreBoundaryOneStagedAnchor A strategy hwin
      one ∧
    ProfiledRawJointRecurrentOwnerFibreBoundaryTwoStagedAnchor A strategy hwin
      two

/-- The proposed recurrent operational relation.  It keeps exactly the
semantic selected pair, fibre validity, and the latent staged coordinate
needed by an opposite-direction strict round. -/
structure ProfiledRawJointRecurrentOwnerFibreBoundaryOperational
    (one :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin)
    (two :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin) :
    Prop where
  selected :
    ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin one two
  oneValid :
    ProfiledRawJointRecurrentOwnerFibreBoundaryOneValid A strategy hwin one
  twoValid :
    ProfiledRawJointRecurrentOwnerFibreBoundaryTwoValid A strategy hwin two
  stagedAnchor :
    ProfiledRawJointRecurrentOwnerFibreBoundaryStagedAnchor A strategy hwin
      one two

/-! ## Fibre-certificate preservation -/

theorem ProfiledRawJointRecurrentOwnerFibreBoundaryOneValid.noRecv
    (one :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin)
    (hvalid :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneValid A strategy hwin one)
    (inputOne : In₁) :
    ProfiledRawJointRecurrentOwnerFibreBoundaryOneValid A strategy hwin
      (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvOne A strategy hwin
        one inputOne).1 := by
  rcases one with ⟨base, coordinates⟩
  cases base with
  | inl bridge => trivial
  | inr pending =>
      simpa [ProfiledRawJointRecurrentOwnerFibreBoundaryOneValid,
        profiledRawJointRecurrentOwnerFibreBoundaryNoRecvOne] using
          ProfiledRawJointRecurrentRightToLeftOwnerFibreValid.noRecv A strategy
            hwin pending hvalid inputOne

theorem ProfiledRawJointRecurrentOwnerFibreBoundaryTwoValid.noRecv
    (two :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin)
    (hvalid :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoValid A strategy hwin two)
    (inputTwo : In₂) :
    ProfiledRawJointRecurrentOwnerFibreBoundaryTwoValid A strategy hwin
      (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvTwo A strategy hwin
        two inputTwo).1 := by
  rcases two with ⟨base, coordinates⟩
  cases base with
  | inl bridge => trivial
  | inr pending =>
      simpa [ProfiledRawJointRecurrentOwnerFibreBoundaryTwoValid,
        profiledRawJointRecurrentOwnerFibreBoundaryNoRecvTwo] using
          ProfiledRawJointRecurrentLeftToRightOwnerFibreValid.noRecv A strategy
            hwin pending hvalid inputTwo

theorem profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne_valid
    (one :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin)
    (two :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin)
    (hselected :
      ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin
        one two)
    (inputOne : In₁) (inputTwo : In₂) :
    ProfiledRawJointRecurrentOwnerFibreBoundaryOneValid A strategy hwin
      (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne A strategy hwin
        one inputOne two inputTwo).1 := by
  cases hselected with
  | right phaseData hright hinvariant =>
      have hreceive :
          profiledRawJointRecurrentOwnerFibreBoundaryReceive? A strategy hwin
              one two (inputOne, inputTwo) =
            some
              (phaseData.ownerFibreReceive A strategy hwin
                (inputOne, inputTwo)) := by
        simp [profiledRawJointRecurrentOwnerFibreBoundaryReceive?, hright]
      rw [profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne, hreceive]
      have hvalid :=
        hinvariant.1.ownerFibreReceive_valid A strategy hwin phaseData.1
          phaseData.2.1 phaseData.2.2 (inputOne, inputTwo)
      simpa [ProfiledRawJointRecurrentOwnerFibreBoundaryOneValid,
        ProfiledRawJointRecurrentRightPhaseLiveBoundaryData.ownerFibreReceive]
        using hvalid.1
  | left phaseData hright hleft hinvariant =>
      have hreceive :
          profiledRawJointRecurrentOwnerFibreBoundaryReceive? A strategy hwin
              one two (inputOne, inputTwo) =
            some
              (phaseData.ownerFibreReceive A strategy hwin
                (inputOne, inputTwo)) := by
        simp [profiledRawJointRecurrentOwnerFibreBoundaryReceive?, hright,
          hleft]
      rw [profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne, hreceive]
      simp [ProfiledRawJointRecurrentOwnerFibreBoundaryOneValid,
        ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData.ownerFibreReceive]

theorem profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo_valid
    (one :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin)
    (two :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin)
    (hselected :
      ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin
        one two)
    (inputOne : In₁) (inputTwo : In₂) :
    ProfiledRawJointRecurrentOwnerFibreBoundaryTwoValid A strategy hwin
      (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo A strategy hwin
        two inputTwo one inputOne).1 := by
  cases hselected with
  | right phaseData hright hinvariant =>
      have hreceive :
          profiledRawJointRecurrentOwnerFibreBoundaryReceive? A strategy hwin
              one two (inputOne, inputTwo) =
            some
              (phaseData.ownerFibreReceive A strategy hwin
                (inputOne, inputTwo)) := by
        simp [profiledRawJointRecurrentOwnerFibreBoundaryReceive?, hright]
      rw [profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo, hreceive]
      simp [ProfiledRawJointRecurrentOwnerFibreBoundaryTwoValid,
        ProfiledRawJointRecurrentRightPhaseLiveBoundaryData.ownerFibreReceive]
  | left phaseData hright hleft hinvariant =>
      have hreceive :
          profiledRawJointRecurrentOwnerFibreBoundaryReceive? A strategy hwin
              one two (inputOne, inputTwo) =
            some
              (phaseData.ownerFibreReceive A strategy hwin
                (inputOne, inputTwo)) := by
        simp [profiledRawJointRecurrentOwnerFibreBoundaryReceive?, hright,
          hleft]
      rw [profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo, hreceive]
      have hvalid :=
        hinvariant.1.ownerFibreReceive_valid A strategy hwin phaseData.1
          phaseData.2.1 phaseData.2.2 (inputOne, inputTwo)
      simpa [ProfiledRawJointRecurrentOwnerFibreBoundaryTwoValid,
        ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData.ownerFibreReceive]
        using hvalid.1

/-! ## Staged-anchor preservation -/

theorem ProfiledRawJointRecurrentOwnerFibreBoundaryOneStagedAnchor.noRecv
    (one :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin)
    (hanchor :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneStagedAnchor A strategy
        hwin one)
    (inputOne : In₁) :
    ProfiledRawJointRecurrentOwnerFibreBoundaryOneStagedAnchor A strategy hwin
      (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvOne A strategy hwin
        one inputOne).1 := by
  rcases one with ⟨base, coordinates⟩
  cases base with
  | inl bridge =>
      cases bridge with
      | inl staged =>
          rcases staged with ⟨state, receiver, packet⟩
          have hsource : coordinates.2 = state := hanchor _ rfl
          cases packet with
          | none =>
              intro next hnext
              simp only [profiledRawJointRecurrentOwnerFibreBoundaryNoRecvOne,
                profiledRawJointRecurrentLeftToRightBridgeNoRecv] at hnext
              cases hnext
              exact hsource
          | some packet =>
              cases hmove : packet.successor.2.1.2.1 with
              | none =>
                  intro next hnext
                  simp only [
                    profiledRawJointRecurrentOwnerFibreBoundaryNoRecvOne,
                    profiledRawJointRecurrentLeftToRightBridgeNoRecv,
                    hmove] at hnext
                  cases hnext
                  exact hsource
              | some move =>
                  intro next hnext
                  simp [profiledRawJointRecurrentOwnerFibreBoundaryNoRecvOne,
                    profiledRawJointRecurrentLeftToRightBridgeNoRecv,
                    hmove] at hnext
      | inr installed =>
          intro staged hstaged
          simp [profiledRawJointRecurrentOwnerFibreBoundaryNoRecvOne,
            profiledRawJointRecurrentLeftToRightBridgeNoRecv] at hstaged
  | inr pending =>
      intro staged hstaged
      simp [profiledRawJointRecurrentOwnerFibreBoundaryNoRecvOne] at hstaged

theorem ProfiledRawJointRecurrentOwnerFibreBoundaryTwoStagedAnchor.noRecv
    (two :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin)
    (hanchor :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoStagedAnchor A strategy
        hwin two)
    (inputTwo : In₂) :
    ProfiledRawJointRecurrentOwnerFibreBoundaryTwoStagedAnchor A strategy hwin
      (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvTwo A strategy hwin
        two inputTwo).1 := by
  rcases two with ⟨base, coordinates⟩
  cases base with
  | inl bridge =>
      cases bridge with
      | inl staged =>
          rcases staged with ⟨state, receiver, packet⟩
          have hsource : coordinates.1 = state := hanchor _ rfl
          cases packet with
          | none =>
              intro next hnext
              simp only [profiledRawJointRecurrentOwnerFibreBoundaryNoRecvTwo,
                profiledRawJointRecurrentRightToLeftBridgeNoRecv] at hnext
              cases hnext
              exact hsource
          | some packet =>
              cases hmove : packet.successor.2.1.2.2 with
              | none =>
                  intro next hnext
                  simp only [
                    profiledRawJointRecurrentOwnerFibreBoundaryNoRecvTwo,
                    profiledRawJointRecurrentRightToLeftBridgeNoRecv,
                    hmove] at hnext
                  cases hnext
                  exact hsource
              | some move =>
                  intro next hnext
                  simp [profiledRawJointRecurrentOwnerFibreBoundaryNoRecvTwo,
                    profiledRawJointRecurrentRightToLeftBridgeNoRecv,
                    hmove] at hnext
      | inr installed =>
          intro staged hstaged
          simp [profiledRawJointRecurrentOwnerFibreBoundaryNoRecvTwo,
            profiledRawJointRecurrentRightToLeftBridgeNoRecv] at hstaged
  | inr pending =>
      intro staged hstaged
      simp [profiledRawJointRecurrentOwnerFibreBoundaryNoRecvTwo] at hstaged

theorem profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo_stagedAnchor
    (one :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin)
    (two :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin)
    (hselected :
      ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin
        one two)
    (inputOne : In₁) (inputTwo : In₂) :
    ProfiledRawJointRecurrentOwnerFibreBoundaryTwoStagedAnchor A strategy hwin
      (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo A strategy hwin
        two inputTwo one inputOne).1 := by
  cases hselected with
  | right phaseData hright hinvariant =>
      have hreceive :
          profiledRawJointRecurrentOwnerFibreBoundaryReceive? A strategy hwin
              one two (inputOne, inputTwo) =
            some
              (phaseData.ownerFibreReceive A strategy hwin
                (inputOne, inputTwo)) := by
        simp [profiledRawJointRecurrentOwnerFibreBoundaryReceive?, hright]
      rw [profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo, hreceive]
      rcases phaseData with ⟨data, oldState, oldOwner⟩
      rcases data with ⟨state, ⟨receiver, owner⟩, oldReceiver⟩
      intro staged hstaged
      dsimp [ProfiledRawJointRecurrentRightPhaseLiveBoundaryData.ownerFibreReceive,
        profiledRawJointRecurrentPhaseRightToLeftBridgeForkTwo,
        profiledRawJointRecurrentRightReceiveFor,
        ProfiledRawJointRecurrentRightBoundaryData.receiver,
        ProfiledRawJointRecurrentRightBoundaryData.owner,
        ProfiledRawJointRecurrentRightBoundaryData.target] at hstaged ⊢
      split at * <;> cases hstaged <;> rfl
  | left phaseData hright hleft hinvariant =>
      have hreceive :
          profiledRawJointRecurrentOwnerFibreBoundaryReceive? A strategy hwin
              one two (inputOne, inputTwo) =
            some
              (phaseData.ownerFibreReceive A strategy hwin
                (inputOne, inputTwo)) := by
        simp [profiledRawJointRecurrentOwnerFibreBoundaryReceive?, hright,
          hleft]
      rw [profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo, hreceive]
      intro staged hstaged
      simp [ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData.ownerFibreReceive]
        at hstaged

theorem profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne_stagedAnchor
    (one :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin)
    (two :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin)
    (hselected :
      ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin
        one two)
    (inputOne : In₁) (inputTwo : In₂) :
    ProfiledRawJointRecurrentOwnerFibreBoundaryOneStagedAnchor A strategy hwin
      (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne A strategy hwin
        one inputOne two inputTwo).1 := by
  cases hselected with
  | right phaseData hright hinvariant =>
      have hreceive :
          profiledRawJointRecurrentOwnerFibreBoundaryReceive? A strategy hwin
              one two (inputOne, inputTwo) =
            some
              (phaseData.ownerFibreReceive A strategy hwin
                (inputOne, inputTwo)) := by
        simp [profiledRawJointRecurrentOwnerFibreBoundaryReceive?, hright]
      rw [profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne, hreceive]
      intro staged hstaged
      simp [ProfiledRawJointRecurrentRightPhaseLiveBoundaryData.ownerFibreReceive]
        at hstaged
  | left phaseData hright hleft hinvariant =>
      have hreceive :
          profiledRawJointRecurrentOwnerFibreBoundaryReceive? A strategy hwin
              one two (inputOne, inputTwo) =
            some
              (phaseData.ownerFibreReceive A strategy hwin
                (inputOne, inputTwo)) := by
        simp [profiledRawJointRecurrentOwnerFibreBoundaryReceive?, hright,
          hleft]
      rw [profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne, hreceive]
      rcases phaseData with ⟨data, oldState, oldOwner⟩
      rcases data with ⟨state, ⟨receiver, owner⟩, oldReceiver⟩
      intro staged hstaged
      dsimp [ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData.ownerFibreReceive,
        profiledRawJointRecurrentPhaseLeftToRightBridgeForkOne,
        profiledRawJointRecurrentLeftReceiveFor,
        ProfiledRawJointRecurrentLeftBoundaryData.receiver,
        ProfiledRawJointRecurrentLeftBoundaryData.owner,
        ProfiledRawJointRecurrentLeftBoundaryData.target] at hstaged ⊢
      split at * <;> cases hstaged <;> rfl

theorem profiledRawJointRecurrentOwnerFibreBoundaryStagedAnchor_strictRight
    (one :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin)
    (two :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin)
    (hselected :
      ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin
        one two)
    (hanchor :
      ProfiledRawJointRecurrentOwnerFibreBoundaryStagedAnchor A strategy hwin
        one two)
    (inputOne : In₁) (inputTwo : In₂) :
    ProfiledRawJointRecurrentOwnerFibreBoundaryStagedAnchor A strategy hwin
      (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvOne A strategy hwin
        one inputOne).1
      (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo A strategy hwin
        two inputTwo one inputOne).1 := by
  exact ⟨hanchor.1.noRecv A strategy hwin one inputOne,
    profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo_stagedAnchor A
      strategy hwin one two hselected inputOne inputTwo⟩

theorem profiledRawJointRecurrentOwnerFibreBoundaryStagedAnchor_strictLeft
    (one :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin)
    (two :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin)
    (hselected :
      ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin
        one two)
    (hanchor :
      ProfiledRawJointRecurrentOwnerFibreBoundaryStagedAnchor A strategy hwin
        one two)
    (inputOne : In₁) (inputTwo : In₂) :
    ProfiledRawJointRecurrentOwnerFibreBoundaryStagedAnchor A strategy hwin
      (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne A strategy hwin
        one inputOne two inputTwo).1
      (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvTwo A strategy hwin
        two inputTwo).1 := by
  exact
    ⟨profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne_stagedAnchor A
        strategy hwin one two hselected inputOne inputTwo,
      hanchor.2.noRecv A strategy hwin two inputTwo⟩

/-! ## Decoder-driven bridge/bridge closure -/

/-- Coordinate-general same-direction closure of the installed/staged
branch.  Decoder inversion supplies the canonical semantic data; the local
transition theorem itself does not require the two dormant coordinate
registers to agree. -/
theorem
    ProfiledRawJointRecurrentOwnerFibreBoundarySelected.strictRight_installedStaged
    (installed :
      ProfiledRawJointRecurrentLeftToRightInstalledOwner A strategy hwin)
    (staged :
      ProfiledRawJointRecurrentRightToLeftStagedReceiver A strategy hwin)
    (oneCoordinates twoCoordinates :
      ProfiledRawJointRecurrentBoundaryBankCoordinates A strategy hwin)
    (hselected :
      ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin
        (.inl (.inr installed), oneCoordinates)
        (.inl (.inl staged), twoCoordinates))
    (inputOne : In₁) (inputTwo : In₂) :
    ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin
      (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvOne A strategy hwin
        (.inl (.inr installed), oneCoordinates) inputOne).1
      (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo A strategy hwin
        (.inl (.inl staged), twoCoordinates) inputTwo
        (.inl (.inr installed), oneCoordinates) inputOne).1 := by
  cases hselected with
  | right phaseData hdecode hinvariant =>
      obtain ⟨rightState, rightReceiver, rightOwner, leftTemplate, packet,
          leftMove, rfl, rfl, hleftMove, rfl⟩ :=
        profiledRawJointRecurrentOwnerFibreRightBoundaryData?_installedStaged_inv
          A strategy hwin installed staged oneCoordinates twoCoordinates
            phaseData hdecode
      exact
        (profiledRawJointRecurrentOwnerFibreBoundarySelected_strictRight_installedStaged
          A strategy hwin rightState rightReceiver rightOwner leftTemplate
            packet leftMove hleftMove hinvariant oneCoordinates twoCoordinates
              inputOne inputTwo).2
  | left phaseData hright hleft hinvariant =>
      simp [profiledRawJointRecurrentOwnerFibreLeftBoundaryData?] at hleft

/-- Mirrored coordinate-general same-direction closure of staged/installed. -/
theorem
    ProfiledRawJointRecurrentOwnerFibreBoundarySelected.strictLeft_stagedInstalled
    (staged :
      ProfiledRawJointRecurrentLeftToRightStagedReceiver A strategy hwin)
    (installed :
      ProfiledRawJointRecurrentRightToLeftInstalledOwner A strategy hwin)
    (oneCoordinates twoCoordinates :
      ProfiledRawJointRecurrentBoundaryBankCoordinates A strategy hwin)
    (hselected :
      ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin
        (.inl (.inl staged), oneCoordinates)
        (.inl (.inr installed), twoCoordinates))
    (inputOne : In₁) (inputTwo : In₂) :
    ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin
      (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne A strategy hwin
        (.inl (.inl staged), oneCoordinates) inputOne
        (.inl (.inr installed), twoCoordinates) inputTwo).1
      (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvTwo A strategy hwin
        (.inl (.inr installed), twoCoordinates) inputTwo).1 := by
  cases hselected with
  | right phaseData hdecode hinvariant =>
      simp [profiledRawJointRecurrentOwnerFibreRightBoundaryData?] at hdecode
  | left phaseData hright hdecode hinvariant =>
      obtain ⟨leftState, leftReceiver, leftOwner, rightTemplate, packet,
          rightMove, rfl, rfl, hrightMove, rfl⟩ :=
        profiledRawJointRecurrentOwnerFibreLeftBoundaryData?_stagedInstalled_inv
          A strategy hwin staged installed oneCoordinates twoCoordinates
            phaseData hdecode
      exact
        (profiledRawJointRecurrentOwnerFibreBoundarySelected_strictLeft_stagedInstalled
          A strategy hwin leftState leftReceiver leftOwner rightTemplate
            packet rightMove hrightMove hinvariant oneCoordinates
              twoCoordinates inputOne inputTwo).2

/-- Opposite-direction exit from staged/installed.  The sole coordinate
hypothesis required by the semantic transition is exactly the process-one
staged anchor. -/
theorem
    ProfiledRawJointRecurrentOwnerFibreBoundarySelected.strictRight_stagedInstalled
    (staged :
      ProfiledRawJointRecurrentLeftToRightStagedReceiver A strategy hwin)
    (installed :
      ProfiledRawJointRecurrentRightToLeftInstalledOwner A strategy hwin)
    (oneCoordinates twoCoordinates :
      ProfiledRawJointRecurrentBoundaryBankCoordinates A strategy hwin)
    (hselected :
      ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin
        (.inl (.inl staged), oneCoordinates)
        (.inl (.inr installed), twoCoordinates))
    (hanchor :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneStagedAnchor A strategy
        hwin (.inl (.inl staged), oneCoordinates))
    (inputOne : In₁) (inputTwo : In₂) :
    ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin
      (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvOne A strategy hwin
        (.inl (.inl staged), oneCoordinates) inputOne).1
      (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo A strategy hwin
        (.inl (.inr installed), twoCoordinates) inputTwo
        (.inl (.inl staged), oneCoordinates) inputOne).1 := by
  cases hselected with
  | right phaseData hdecode hinvariant =>
      simp [profiledRawJointRecurrentOwnerFibreRightBoundaryData?] at hdecode
  | left phaseData hright hdecode hinvariant =>
      have honeLeftState := hanchor staged rfl
      obtain ⟨leftState, leftReceiver, leftOwner, rightTemplate, packet,
          rightMove, rfl, rfl, hrightMove, rfl⟩ :=
        profiledRawJointRecurrentOwnerFibreLeftBoundaryData?_stagedInstalled_inv
          A strategy hwin staged installed oneCoordinates twoCoordinates
            phaseData hdecode
      exact
        (profiledRawJointRecurrentOwnerFibreBoundarySelected_strictRight_stagedInstalled
          A strategy hwin leftState leftReceiver leftOwner rightTemplate
            packet rightMove hrightMove hinvariant oneCoordinates
              twoCoordinates honeLeftState inputOne inputTwo).2

/-- Opposite-direction exit from installed/staged under strict-left.  The
process-two staged anchor is exactly the coordinate equality required when
the staged endpoint becomes installed. -/
theorem
    ProfiledRawJointRecurrentOwnerFibreBoundarySelected.strictLeft_installedStaged
    (installed :
      ProfiledRawJointRecurrentLeftToRightInstalledOwner A strategy hwin)
    (staged :
      ProfiledRawJointRecurrentRightToLeftStagedReceiver A strategy hwin)
    (oneCoordinates twoCoordinates :
      ProfiledRawJointRecurrentBoundaryBankCoordinates A strategy hwin)
    (hselected :
      ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin
        (.inl (.inr installed), oneCoordinates)
        (.inl (.inl staged), twoCoordinates))
    (hanchor :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoStagedAnchor A strategy
        hwin (.inl (.inl staged), twoCoordinates))
    (inputOne : In₁) (inputTwo : In₂) :
    ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin
      (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne A strategy hwin
        (.inl (.inr installed), oneCoordinates) inputOne
        (.inl (.inl staged), twoCoordinates) inputTwo).1
      (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvTwo A strategy hwin
        (.inl (.inl staged), twoCoordinates) inputTwo).1 := by
  have htwoRightState := hanchor staged rfl
  cases hselected with
  | right phaseData hdecode hinvariant =>
      obtain ⟨rightState, rightReceiver, rightOwner, leftTemplate, packet,
          leftMove, rfl, rfl, hleftMove, rfl⟩ :=
        profiledRawJointRecurrentOwnerFibreRightBoundaryData?_installedStaged_inv
          A strategy hwin installed staged oneCoordinates twoCoordinates
            phaseData hdecode
      exact
        (profiledRawJointRecurrentOwnerFibreBoundarySelected_strictLeft_installedStaged
          A strategy hwin rightState rightReceiver rightOwner leftTemplate
            packet leftMove hleftMove oneCoordinates twoCoordinates
              htwoRightState hinvariant inputOne inputTwo).2
  | left phaseData hright hdecode hinvariant =>
      simp [profiledRawJointRecurrentOwnerFibreLeftBoundaryData?] at hdecode

/-- The complete bridge/bridge quadrant is closed under a strict-right
round.  Two of the four tag combinations are decoder-impossible; the other
two are the same-direction and reversal lemmas above. -/
theorem
    ProfiledRawJointRecurrentOwnerFibreBoundarySelected.strictRight_bridgeBridge
    (oneBridge :
      ProfiledRawJointRecurrentLeftToRightBridgeControl A strategy hwin)
    (twoBridge :
      ProfiledRawJointRecurrentRightToLeftBridgeControl A strategy hwin)
    (oneCoordinates twoCoordinates :
      ProfiledRawJointRecurrentBoundaryBankCoordinates A strategy hwin)
    (hselected :
      ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin
        (.inl oneBridge, oneCoordinates) (.inl twoBridge, twoCoordinates))
    (hanchor :
      ProfiledRawJointRecurrentOwnerFibreBoundaryStagedAnchor A strategy hwin
        (.inl oneBridge, oneCoordinates) (.inl twoBridge, twoCoordinates))
    (inputOne : In₁) (inputTwo : In₂) :
    ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin
      (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvOne A strategy hwin
        (.inl oneBridge, oneCoordinates) inputOne).1
      (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo A strategy hwin
        (.inl twoBridge, twoCoordinates) inputTwo
        (.inl oneBridge, oneCoordinates) inputOne).1 := by
  cases oneBridge with
  | inl oneStaged =>
      cases twoBridge with
      | inl twoStaged =>
          cases hselected with
          | right phaseData hdecode hinvariant =>
              simp [profiledRawJointRecurrentOwnerFibreRightBoundaryData?]
                at hdecode
          | left phaseData hright hdecode hinvariant =>
              simp [profiledRawJointRecurrentOwnerFibreLeftBoundaryData?]
                at hdecode
      | inr twoInstalled =>
          exact hselected.strictRight_stagedInstalled A strategy hwin
            oneStaged twoInstalled oneCoordinates twoCoordinates hanchor.1
              inputOne inputTwo
  | inr oneInstalled =>
      cases twoBridge with
      | inl twoStaged =>
          exact hselected.strictRight_installedStaged A strategy hwin
            oneInstalled twoStaged oneCoordinates twoCoordinates inputOne
              inputTwo
      | inr twoInstalled =>
          cases hselected with
          | right phaseData hdecode hinvariant =>
              simp [profiledRawJointRecurrentOwnerFibreRightBoundaryData?]
                at hdecode
          | left phaseData hright hdecode hinvariant =>
              simp [profiledRawJointRecurrentOwnerFibreLeftBoundaryData?]
                at hdecode

/-- The complete bridge/bridge quadrant is closed under a strict-left round.
The staged/installed branch is same-direction; the installed/staged branch
uses only the process-two staged anchor.  The remaining two tag combinations
cannot be selected by either decoder. -/
theorem
    ProfiledRawJointRecurrentOwnerFibreBoundarySelected.strictLeft_bridgeBridge
    (oneBridge :
      ProfiledRawJointRecurrentLeftToRightBridgeControl A strategy hwin)
    (twoBridge :
      ProfiledRawJointRecurrentRightToLeftBridgeControl A strategy hwin)
    (oneCoordinates twoCoordinates :
      ProfiledRawJointRecurrentBoundaryBankCoordinates A strategy hwin)
    (hselected :
      ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin
        (.inl oneBridge, oneCoordinates) (.inl twoBridge, twoCoordinates))
    (hanchor :
      ProfiledRawJointRecurrentOwnerFibreBoundaryStagedAnchor A strategy hwin
        (.inl oneBridge, oneCoordinates) (.inl twoBridge, twoCoordinates))
    (inputOne : In₁) (inputTwo : In₂) :
    ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin
      (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne A strategy hwin
        (.inl oneBridge, oneCoordinates) inputOne
        (.inl twoBridge, twoCoordinates) inputTwo).1
      (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvTwo A strategy hwin
        (.inl twoBridge, twoCoordinates) inputTwo).1 := by
  cases oneBridge with
  | inl oneStaged =>
      cases twoBridge with
      | inl twoStaged =>
          cases hselected with
          | right phaseData hdecode hinvariant =>
              simp [profiledRawJointRecurrentOwnerFibreRightBoundaryData?]
                at hdecode
          | left phaseData hright hdecode hinvariant =>
              simp [profiledRawJointRecurrentOwnerFibreLeftBoundaryData?]
                at hdecode
      | inr twoInstalled =>
          exact hselected.strictLeft_stagedInstalled A strategy hwin
            oneStaged twoInstalled oneCoordinates twoCoordinates inputOne
              inputTwo
  | inr oneInstalled =>
      cases twoBridge with
      | inl twoStaged =>
          exact hselected.strictLeft_installedStaged A strategy hwin
            oneInstalled twoStaged oneCoordinates twoCoordinates hanchor.2
              inputOne inputTwo
      | inr twoInstalled =>
          cases hselected with
          | right phaseData hdecode hinvariant =>
              simp [profiledRawJointRecurrentOwnerFibreRightBoundaryData?]
                at hdecode
          | left phaseData hright hdecode hinvariant =>
              simp [profiledRawJointRecurrentOwnerFibreLeftBoundaryData?]
                at hdecode

/-- Coordinate-general strict-right closure of installed/fibre.  The decoder
inversion theorem recovers the installed active state; the operational
transition lemma already covers both pending member bits. -/
theorem
    ProfiledRawJointRecurrentOwnerFibreBoundarySelected.strictRight_installedFibre
    (installed :
      ProfiledRawJointRecurrentLeftToRightInstalledOwner A strategy hwin)
    (pendingTwo :
      ProfiledRawJointRecurrentLeftToRightOwnerFibrePending A strategy hwin)
    (oneCoordinates twoCoordinates :
      ProfiledRawJointRecurrentBoundaryBankCoordinates A strategy hwin)
    (hselected :
      ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin
        (.inl (.inr installed), oneCoordinates)
        (.inr pendingTwo, twoCoordinates))
    (inputOne : In₁) (inputTwo : In₂) :
    ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin
      (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvOne A strategy hwin
        (.inl (.inr installed), oneCoordinates) inputOne).1
      (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo A strategy hwin
        (.inr pendingTwo, twoCoordinates) inputTwo
        (.inl (.inr installed), oneCoordinates) inputOne).1 := by
  cases hselected with
  | right phaseData hdecode hinvariant =>
      let rightReceiver :=
        profiledRawJointRecurrentLeftToRightOwnerFibreReceiver A strategy hwin
          pendingTwo
      let leftFibre := pendingTwo.2.1.1
      obtain ⟨rightOwner, leftTemplate, rfl, rfl⟩ :=
        profiledRawJointRecurrentOwnerFibreRightBoundaryData?_installedFibre_inv
          A strategy hwin installed pendingTwo oneCoordinates twoCoordinates
            phaseData hdecode
      exact
        profiledRawJointRecurrentOwnerFibreBoundarySelected_strictRight_installedFibre_toStaged
          A strategy hwin rightReceiver.1 oneCoordinates.2 rightReceiver.2
            rightOwner leftTemplate (leftFibre.receiverAt A leftTemplate)
              leftFibre.2.1 pendingTwo oneCoordinates twoCoordinates hdecode
                hinvariant inputOne inputTwo
  | left phaseData hright hdecode hinvariant =>
      simp [profiledRawJointRecurrentOwnerFibreLeftBoundaryData?] at hdecode

/-- Coordinate-general strict-left closure of installed/fibre.  Decoder
inversion identifies the selected right receiver.  The pending member bit
then distinguishes the open/open target from the left-priority
`(false,true)` target, and the dormant invariant supplies the retained left
bank certificate in both cases. -/
theorem
    ProfiledRawJointRecurrentOwnerFibreBoundarySelected.strictLeft_installedFibre
    (installed :
      ProfiledRawJointRecurrentLeftToRightInstalledOwner A strategy hwin)
    (pendingTwo :
      ProfiledRawJointRecurrentLeftToRightOwnerFibrePending A strategy hwin)
    (oneCoordinates twoCoordinates :
      ProfiledRawJointRecurrentBoundaryBankCoordinates A strategy hwin)
    (hselected :
      ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin
        (.inl (.inr installed), oneCoordinates)
        (.inr pendingTwo, twoCoordinates))
    (hvalid :
      ProfiledRawJointRecurrentLeftToRightOwnerFibreValid A strategy hwin
        pendingTwo)
    (inputOne : In₁) (inputTwo : In₂) :
    ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin
      (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne A strategy hwin
        (.inl (.inr installed), oneCoordinates) inputOne
        (.inr pendingTwo, twoCoordinates) inputTwo).1
      (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvTwo A strategy hwin
        (.inr pendingTwo, twoCoordinates) inputTwo).1 := by
  cases hselected with
  | right phaseData hdecode hinvariant =>
      rcases pendingTwo with
        ⟨member, ⟨⟨leftFibre, receiverFork⟩, unitValue⟩⟩
      rcases unitValue with ⟨⟩
      rcases receiverFork with ⟨openReceiver, closedReceiver⟩
      cases member
      · rcases openReceiver with ⟨rightState, rightReceiver⟩
        obtain ⟨rightOwner, leftTemplate, rfl, rfl⟩ :=
          profiledRawJointRecurrentOwnerFibreRightBoundaryData?_installedFibre_inv
            A strategy hwin installed
              (false,
                (leftFibre, ⟨(rightState, rightReceiver), closedReceiver⟩),
                ())
              oneCoordinates twoCoordinates phaseData hdecode
        have hleftInvariant := hinvariant.2
        change
          ProfiledRawJointRecurrentLeftBoundaryInvariant A strategy hwin
            (oneCoordinates.2,
              ⟨leftFibre.receiverAt A leftTemplate, leftFibre.2.1⟩,
              rightReceiver) at hleftInvariant
        dsimp only [ProfiledRawJointRecurrentLeftBoundaryInvariant,
          ProfiledRawJointLeftOwnerFibreControl.receiverAt] at hleftInvariant
        rcases hleftInvariant with
          ⟨leftCode, leftRoot, _past, hleftState, hleftCode,
            hleftRoot, hleftMove, _hleftOwner, _hleftMonitor⟩
        exact
          (profiledRawJointRecurrentOwnerFibreBoundarySelected_strictLeft_installedOpenFibre
            A strategy hwin rightState oneCoordinates.2 rightReceiver
              rightOwner leftTemplate leftFibre closedReceiver oneCoordinates
                twoCoordinates rfl hinvariant.1 hvalid hleftState leftCode
                  hleftCode leftRoot hleftRoot hleftMove inputOne inputTwo).2
      · rcases closedReceiver with ⟨rightState, rightReceiver⟩
        obtain ⟨rightOwner, leftTemplate, rfl, rfl⟩ :=
          profiledRawJointRecurrentOwnerFibreRightBoundaryData?_installedFibre_inv
            A strategy hwin installed
              (true,
                (leftFibre, ⟨openReceiver, (rightState, rightReceiver)⟩),
                ())
              oneCoordinates twoCoordinates phaseData hdecode
        have hleftInvariant := hinvariant.2
        change
          ProfiledRawJointRecurrentLeftBoundaryInvariant A strategy hwin
            (oneCoordinates.2,
              ⟨leftFibre.receiverAt A leftTemplate, leftFibre.2.1⟩,
              rightReceiver) at hleftInvariant
        dsimp only [ProfiledRawJointRecurrentLeftBoundaryInvariant,
          ProfiledRawJointLeftOwnerFibreControl.receiverAt] at hleftInvariant
        rcases hleftInvariant with
          ⟨leftCode, leftRoot, _past, hleftState, hleftCode,
            hleftRoot, hleftMove, _hleftOwner, _hleftMonitor⟩
        exact
          (profiledRawJointRecurrentOwnerFibreBoundarySelected_strictLeft_installedClosedFibre
            A strategy hwin rightState oneCoordinates.2 rightReceiver
              rightOwner leftTemplate leftFibre openReceiver oneCoordinates
                twoCoordinates rfl hinvariant.1 hvalid hleftState leftCode
                  hleftCode leftRoot hleftRoot hleftMove inputOne inputTwo).2
  | left phaseData hright hdecode hinvariant =>
      simp [profiledRawJointRecurrentOwnerFibreLeftBoundaryData?] at hdecode

/-- Coordinate-general strict-right closure of fibre/installed.  Decoder
inversion identifies the installed left state and selected receiver.  The
pending member bit then determines whether the first endpoint preserves the
open or closed arm of its fork; both reachable cases are covered. -/
theorem
    ProfiledRawJointRecurrentOwnerFibreBoundarySelected.strictRight_fibreInstalled
    (pendingOne :
      ProfiledRawJointRecurrentRightToLeftOwnerFibrePending A strategy hwin)
    (installed :
      ProfiledRawJointRecurrentRightToLeftInstalledOwner A strategy hwin)
    (oneCoordinates twoCoordinates :
      ProfiledRawJointRecurrentBoundaryBankCoordinates A strategy hwin)
    (hselected :
      ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin
        (.inr pendingOne, oneCoordinates)
        (.inl (.inr installed), twoCoordinates))
    (hvalid :
      ProfiledRawJointRecurrentRightToLeftOwnerFibreValid A strategy hwin
        pendingOne)
    (inputOne : In₁) (inputTwo : In₂) :
    ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin
      (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvOne A strategy hwin
        (.inr pendingOne, oneCoordinates) inputOne).1
      (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo A strategy hwin
        (.inl (.inr installed), twoCoordinates) inputTwo
        (.inr pendingOne, oneCoordinates) inputOne).1 := by
  cases hselected with
  | right phaseData hdecode hinvariant =>
      simp [profiledRawJointRecurrentOwnerFibreRightBoundaryData?] at hdecode
  | left phaseData hright hdecode hinvariant =>
      rcases pendingOne with
        ⟨member, ⟨⟨rightFibre, receiverFork⟩, unitValue⟩⟩
      rcases unitValue with ⟨⟩
      rcases receiverFork with ⟨openReceiver, closedReceiver⟩
      cases member
      · rcases openReceiver with ⟨leftState, leftReceiver⟩
        obtain ⟨leftOwner, rightTemplate, rfl, rfl⟩ :=
          profiledRawJointRecurrentOwnerFibreLeftBoundaryData?_fibreInstalled_inv
            A strategy hwin
              (false,
                (rightFibre, ⟨(leftState, leftReceiver), closedReceiver⟩),
                ())
              installed oneCoordinates twoCoordinates phaseData hdecode
        have hrightInvariant := hinvariant.2
        change
          ProfiledRawJointRecurrentRightBoundaryInvariant A strategy hwin
            (twoCoordinates.1,
              ⟨rightFibre.receiverAt A rightTemplate, rightFibre.2.1⟩,
              leftReceiver) at hrightInvariant
        dsimp only [ProfiledRawJointRecurrentRightBoundaryInvariant,
          ProfiledRawJointRightOwnerFibreControl.receiverAt] at hrightInvariant
        rcases hrightInvariant with
          ⟨rightCode, rightRoot, _past, hrightState, hrightCode,
            hrightRoot, hrightMove, _hrightOwner, _hrightMonitor⟩
        exact
          (profiledRawJointRecurrentOwnerFibreBoundarySelected_strictRight_openFibreInstalled
            A strategy hwin leftState twoCoordinates.1 leftReceiver leftOwner
              rightTemplate rightFibre closedReceiver oneCoordinates
                twoCoordinates rfl hinvariant.1 hvalid hrightState rightCode
                  hrightCode rightRoot hrightRoot hrightMove inputOne
                    inputTwo).2
      · rcases closedReceiver with ⟨leftState, leftReceiver⟩
        obtain ⟨leftOwner, rightTemplate, rfl, rfl⟩ :=
          profiledRawJointRecurrentOwnerFibreLeftBoundaryData?_fibreInstalled_inv
            A strategy hwin
              (true,
                (rightFibre, ⟨openReceiver, (leftState, leftReceiver)⟩),
                ())
              installed oneCoordinates twoCoordinates phaseData hdecode
        have hrightInvariant := hinvariant.2
        change
          ProfiledRawJointRecurrentRightBoundaryInvariant A strategy hwin
            (twoCoordinates.1,
              ⟨rightFibre.receiverAt A rightTemplate, rightFibre.2.1⟩,
              leftReceiver) at hrightInvariant
        dsimp only [ProfiledRawJointRecurrentRightBoundaryInvariant,
          ProfiledRawJointRightOwnerFibreControl.receiverAt] at hrightInvariant
        rcases hrightInvariant with
          ⟨rightCode, rightRoot, _past, hrightState, hrightCode,
            hrightRoot, hrightMove, _hrightOwner, _hrightMonitor⟩
        exact
          (profiledRawJointRecurrentOwnerFibreBoundarySelected_strictRight_closedFibreInstalled
            A strategy hwin leftState twoCoordinates.1 leftReceiver leftOwner
              rightTemplate rightFibre openReceiver oneCoordinates
                twoCoordinates rfl hinvariant.1 hvalid hrightState rightCode
                  hrightCode rightRoot hrightRoot hrightMove inputOne
                    inputTwo).2

/-- Coordinate-general strict-left closure of fibre/installed.  The local
transition is already uniform in the pending member bit, so decoder inversion
alone exposes the installed active state and the selected dormant right
receiver needed by that transition. -/
theorem
    ProfiledRawJointRecurrentOwnerFibreBoundarySelected.strictLeft_fibreInstalled
    (pendingOne :
      ProfiledRawJointRecurrentRightToLeftOwnerFibrePending A strategy hwin)
    (installed :
      ProfiledRawJointRecurrentRightToLeftInstalledOwner A strategy hwin)
    (oneCoordinates twoCoordinates :
      ProfiledRawJointRecurrentBoundaryBankCoordinates A strategy hwin)
    (hselected :
      ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin
        (.inr pendingOne, oneCoordinates)
        (.inl (.inr installed), twoCoordinates))
    (inputOne : In₁) (inputTwo : In₂) :
    ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin
      (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne A strategy hwin
        (.inr pendingOne, oneCoordinates) inputOne
        (.inl (.inr installed), twoCoordinates) inputTwo).1
      (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvTwo A strategy hwin
        (.inl (.inr installed), twoCoordinates) inputTwo).1 := by
  cases hselected with
  | right phaseData hdecode hinvariant =>
      simp [profiledRawJointRecurrentOwnerFibreRightBoundaryData?] at hdecode
  | left phaseData hright hdecode hinvariant =>
      let leftReceiver :=
        profiledRawJointRecurrentRightToLeftOwnerFibreReceiver A strategy hwin
          pendingOne
      let rightFibre := pendingOne.2.1.1
      obtain ⟨leftOwner, rightTemplate, rfl, rfl⟩ :=
        profiledRawJointRecurrentOwnerFibreLeftBoundaryData?_fibreInstalled_inv
          A strategy hwin pendingOne installed oneCoordinates twoCoordinates
            phaseData hdecode
      exact
        profiledRawJointRecurrentOwnerFibreBoundarySelected_strictLeft_fibreInstalled_toStaged
          A strategy hwin twoCoordinates.1 leftReceiver.1 leftReceiver.2
            leftOwner rightTemplate (rightFibre.receiverAt A rightTemplate)
              rightFibre.2.1 pendingOne oneCoordinates twoCoordinates hright
                hdecode hinvariant inputOne inputTwo

/-- Coordinate-general same-direction closure of fibre/staged.  Once decoder
success rules out a missing packet and a missing dormant-left move, the
canonical transition is independent of both coordinate registers. -/
theorem
    ProfiledRawJointRecurrentOwnerFibreBoundarySelected.strictRight_fibreStaged
    (pendingOne :
      ProfiledRawJointRecurrentRightToLeftOwnerFibrePending A strategy hwin)
    (staged :
      ProfiledRawJointRecurrentRightToLeftStagedReceiver A strategy hwin)
    (oneCoordinates twoCoordinates :
      ProfiledRawJointRecurrentBoundaryBankCoordinates A strategy hwin)
    (hselected :
      ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin
        (.inr pendingOne, oneCoordinates)
        (.inl (.inl staged), twoCoordinates))
    (hvalid :
      ProfiledRawJointRecurrentRightToLeftOwnerFibreValid A strategy hwin
        pendingOne)
    (inputOne : In₁) (inputTwo : In₂) :
    ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin
      (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvOne A strategy hwin
        (.inr pendingOne, oneCoordinates) inputOne).1
      (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo A strategy hwin
        (.inl (.inl staged), twoCoordinates) inputTwo
        (.inr pendingOne, oneCoordinates) inputOne).1 := by
  cases hselected with
  | right phaseData hdecode hinvariant =>
      rcases pendingOne with
        ⟨member, ⟨⟨rightFibre, receiverFork⟩, unitValue⟩⟩
      rcases unitValue with ⟨⟩
      rcases receiverFork with ⟨oldLeft, newLeft⟩
      rcases staged with ⟨rightState, rightReceiver, packet⟩
      cases packet with
      | none =>
          simp [profiledRawJointRecurrentOwnerFibreRightBoundaryData?]
            at hdecode
      | some oldPacket =>
          cases hleftMove : oldPacket.successor.2.1.2.2 with
          | none =>
              simp [profiledRawJointRecurrentOwnerFibreRightBoundaryData?,
                hleftMove] at hdecode
          | some oldLeftMove =>
              have hcanonical :=
                profiledRawJointRecurrentOwnerFibreRightBoundaryData?_fibreStaged
                  A strategy hwin rightState rightReceiver rightFibre oldLeft
                    newLeft oldPacket oldLeftMove hleftMove oneCoordinates
                      twoCoordinates
              have hphaseOption := hcanonical.symm.trans hdecode
              injection hphaseOption with hphase
              subst phaseData
              exact
                (profiledRawJointRecurrentOwnerFibreBoundarySelected_strictRight_fibreStaged
                  A strategy hwin member rightState rightReceiver rightFibre
                    oldLeft newLeft oldPacket oldLeftMove hleftMove
                      oneCoordinates twoCoordinates hvalid hinvariant inputOne
                        inputTwo).2
  | left phaseData hright hdecode hinvariant =>
      simp [profiledRawJointRecurrentOwnerFibreLeftBoundaryData?] at hdecode

/-- Coordinate-general opposite-direction strict-left closure of
fibre/staged.  The process-two staged anchor supplies exactly the right bank
coordinate used when the nonreceiving staged endpoint becomes installed;
the pending member bit and obsolete fork arms do not affect the semantic
receive. -/
theorem
    ProfiledRawJointRecurrentOwnerFibreBoundarySelected.strictLeft_fibreStaged
    (pendingOne :
      ProfiledRawJointRecurrentRightToLeftOwnerFibrePending A strategy hwin)
    (staged :
      ProfiledRawJointRecurrentRightToLeftStagedReceiver A strategy hwin)
    (oneCoordinates twoCoordinates :
      ProfiledRawJointRecurrentBoundaryBankCoordinates A strategy hwin)
    (hselected :
      ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin
        (.inr pendingOne, oneCoordinates)
        (.inl (.inl staged), twoCoordinates))
    (hvalid :
      ProfiledRawJointRecurrentRightToLeftOwnerFibreValid A strategy hwin
        pendingOne)
    (hanchor :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoStagedAnchor A strategy
        hwin (.inl (.inl staged), twoCoordinates))
    (inputOne : In₁) (inputTwo : In₂) :
    ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin
      (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne A strategy hwin
        (.inr pendingOne, oneCoordinates) inputOne
        (.inl (.inl staged), twoCoordinates) inputTwo).1
      (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvTwo A strategy hwin
        (.inl (.inl staged), twoCoordinates) inputTwo).1 := by
  have htwoRightState := hanchor staged rfl
  cases hselected with
  | right phaseData hdecode hinvariant =>
      rcases pendingOne with
        ⟨member, ⟨⟨rightFibre, receiverFork⟩, unitValue⟩⟩
      rcases unitValue with ⟨⟩
      rcases receiverFork with ⟨oldLeft, newLeft⟩
      rcases staged with ⟨rightState, rightReceiver, packet⟩
      cases packet with
      | none =>
          simp [profiledRawJointRecurrentOwnerFibreRightBoundaryData?]
            at hdecode
      | some oldPacket =>
          cases hleftMove : oldPacket.successor.2.1.2.2 with
          | none =>
              simp [profiledRawJointRecurrentOwnerFibreRightBoundaryData?,
                hleftMove] at hdecode
          | some leftMove =>
              have hcanonical :=
                profiledRawJointRecurrentOwnerFibreRightBoundaryData?_fibreStaged
                  A strategy hwin rightState rightReceiver rightFibre oldLeft
                    newLeft oldPacket leftMove hleftMove oneCoordinates
                      twoCoordinates
              have hphaseOption := hcanonical.symm.trans hdecode
              injection hphaseOption with hphase
              subst phaseData
              exact
                (profiledRawJointRecurrentOwnerFibreBoundarySelected_strictLeft_fibreStaged_member
                  A strategy hwin member rightState rightReceiver rightFibre
                    oldLeft newLeft oldPacket leftMove hleftMove oneCoordinates
                      twoCoordinates htwoRightState hvalid hinvariant inputOne
                        inputTwo).2
  | left phaseData hright hdecode hinvariant =>
      simp [profiledRawJointRecurrentOwnerFibreLeftBoundaryData?] at hdecode

/-- Coordinate-general opposite-direction closure of staged/fibre.  Decoder
success forces the pending endpoint to be closed and exposes the staged
packet's right move; the process-one staged anchor supplies the only dormant
coordinate equality needed by the target decoder. -/
theorem
    ProfiledRawJointRecurrentOwnerFibreBoundarySelected.strictRight_stagedFibre
    (staged :
      ProfiledRawJointRecurrentLeftToRightStagedReceiver A strategy hwin)
    (pendingTwo :
      ProfiledRawJointRecurrentLeftToRightOwnerFibrePending A strategy hwin)
    (oneCoordinates twoCoordinates :
      ProfiledRawJointRecurrentBoundaryBankCoordinates A strategy hwin)
    (hselected :
      ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin
        (.inl (.inl staged), oneCoordinates)
        (.inr pendingTwo, twoCoordinates))
    (hvalid :
      ProfiledRawJointRecurrentLeftToRightOwnerFibreValid A strategy hwin
        pendingTwo)
    (hanchor :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneStagedAnchor A strategy
        hwin (.inl (.inl staged), oneCoordinates))
    (inputOne : In₁) (inputTwo : In₂) :
    ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin
      (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvOne A strategy hwin
        (.inl (.inl staged), oneCoordinates) inputOne).1
      (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo A strategy hwin
        (.inr pendingTwo, twoCoordinates) inputTwo
        (.inl (.inl staged), oneCoordinates) inputOne).1 := by
  have honeLeftState := hanchor staged rfl
  cases hselected with
  | right phaseData hdecode hinvariant =>
      simp [profiledRawJointRecurrentOwnerFibreRightBoundaryData?] at hdecode
  | left phaseData hright hdecode hinvariant =>
      rcases pendingTwo with
        ⟨member, ⟨⟨leftFibre, receiverFork⟩, unitValue⟩⟩
      rcases unitValue with ⟨⟩
      rcases receiverFork with ⟨oldRight, newRight⟩
      cases member
      · simp [profiledRawJointRecurrentOwnerFibreLeftBoundaryData?] at hdecode
      · rcases staged with ⟨leftState, leftReceiver, packet⟩
        cases packet with
        | none =>
            simp [profiledRawJointRecurrentOwnerFibreLeftBoundaryData?]
              at hdecode
        | some oldPacket =>
            cases hrightMove : oldPacket.successor.2.1.2.1 with
            | none =>
                simp [profiledRawJointRecurrentOwnerFibreLeftBoundaryData?,
                  hrightMove] at hdecode
            | some rightMove =>
                have hcanonical :=
                  profiledRawJointRecurrentOwnerFibreLeftBoundaryData?_stagedFibre
                    A strategy hwin leftState leftReceiver leftFibre oldRight
                      newRight oldPacket rightMove hrightMove oneCoordinates
                        twoCoordinates
                have hphaseOption := hcanonical.symm.trans hdecode
                injection hphaseOption with hphase
                subst phaseData
                exact
                  (profiledRawJointRecurrentOwnerFibreBoundarySelected_strictRight_stagedFibre
                    A strategy hwin leftState leftReceiver leftFibre oldRight
                      newRight oldPacket rightMove hrightMove oneCoordinates
                        twoCoordinates honeLeftState hvalid hinvariant inputOne
                          inputTwo).2

/-- Coordinate-general same-direction strict-left closure of staged/fibre.
Decoder success forces the second pending endpoint to be closed and the
staged packet to contain a usable right move.  No coordinate anchor is needed
because both the source and target staged/fibre decoders ignore the dormant
coordinate registers. -/
theorem
    ProfiledRawJointRecurrentOwnerFibreBoundarySelected.strictLeft_stagedFibre
    (staged :
      ProfiledRawJointRecurrentLeftToRightStagedReceiver A strategy hwin)
    (pendingTwo :
      ProfiledRawJointRecurrentLeftToRightOwnerFibrePending A strategy hwin)
    (oneCoordinates twoCoordinates :
      ProfiledRawJointRecurrentBoundaryBankCoordinates A strategy hwin)
    (hselected :
      ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin
        (.inl (.inl staged), oneCoordinates)
        (.inr pendingTwo, twoCoordinates))
    (hvalid :
      ProfiledRawJointRecurrentLeftToRightOwnerFibreValid A strategy hwin
        pendingTwo)
    (inputOne : In₁) (inputTwo : In₂) :
    ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin
      (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne A strategy hwin
        (.inl (.inl staged), oneCoordinates) inputOne
        (.inr pendingTwo, twoCoordinates) inputTwo).1
      (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvTwo A strategy hwin
        (.inr pendingTwo, twoCoordinates) inputTwo).1 := by
  cases hselected with
  | right phaseData hdecode hinvariant =>
      simp [profiledRawJointRecurrentOwnerFibreRightBoundaryData?] at hdecode
  | left phaseData hright hdecode hinvariant =>
      rcases pendingTwo with
        ⟨member, ⟨⟨leftFibre, receiverFork⟩, unitValue⟩⟩
      rcases unitValue with ⟨⟩
      rcases receiverFork with ⟨oldRight, newRight⟩
      cases member
      · simp [profiledRawJointRecurrentOwnerFibreLeftBoundaryData?] at hdecode
      · rcases staged with ⟨leftState, leftReceiver, packet⟩
        cases packet with
        | none =>
            simp [profiledRawJointRecurrentOwnerFibreLeftBoundaryData?]
              at hdecode
        | some oldPacket =>
            cases hrightMove : oldPacket.successor.2.1.2.1 with
            | none =>
                simp [profiledRawJointRecurrentOwnerFibreLeftBoundaryData?,
                  hrightMove] at hdecode
            | some rightMove =>
                have hcanonical :=
                  profiledRawJointRecurrentOwnerFibreLeftBoundaryData?_stagedFibre
                    A strategy hwin leftState leftReceiver leftFibre oldRight
                      newRight oldPacket rightMove hrightMove oneCoordinates
                        twoCoordinates
                have hphaseOption := hcanonical.symm.trans hdecode
                injection hphaseOption with hphase
                subst phaseData
                exact
                  (profiledRawJointRecurrentOwnerFibreBoundarySelected_strictLeft_stagedFibre_loop
                    A strategy hwin leftState leftReceiver leftFibre oldRight
                      newRight oldPacket rightMove hrightMove oneCoordinates
                        twoCoordinates hvalid hinvariant inputOne inputTwo).2

/-- Coordinate-general strict-right closure of the complete pending/pending
quadrant.  The four member pairs are dispatched according to the decoder's
priority rule: `00`, `10`, and `11` use the right phase, while `01` uses the
left phase. -/
theorem
    ProfiledRawJointRecurrentOwnerFibreBoundarySelected.strictRight_fibreFibre
    (pendingOne :
      ProfiledRawJointRecurrentRightToLeftOwnerFibrePending A strategy hwin)
    (pendingTwo :
      ProfiledRawJointRecurrentLeftToRightOwnerFibrePending A strategy hwin)
    (oneCoordinates twoCoordinates :
      ProfiledRawJointRecurrentBoundaryBankCoordinates A strategy hwin)
    (hselected :
      ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin
        (.inr pendingOne, oneCoordinates) (.inr pendingTwo, twoCoordinates))
    (honeValid :
      ProfiledRawJointRecurrentRightToLeftOwnerFibreValid A strategy hwin
        pendingOne)
    (htwoValid :
      ProfiledRawJointRecurrentLeftToRightOwnerFibreValid A strategy hwin
        pendingTwo)
    (inputOne : In₁) (inputTwo : In₂) :
    ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin
      (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvOne A strategy hwin
        (.inr pendingOne, oneCoordinates) inputOne).1
      (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo A strategy hwin
        (.inr pendingTwo, twoCoordinates) inputTwo
        (.inr pendingOne, oneCoordinates) inputOne).1 := by
  rcases pendingOne with
    ⟨memberOne, ⟨⟨rightFibre, forkOne⟩, unitOne⟩⟩
  rcases unitOne with ⟨⟩
  rcases forkOne with ⟨openLeft, closedLeft⟩
  rcases pendingTwo with
    ⟨memberTwo, ⟨⟨leftFibre, forkTwo⟩, unitTwo⟩⟩
  rcases unitTwo with ⟨⟩
  rcases forkTwo with ⟨openRight, closedRight⟩
  cases memberOne <;> cases memberTwo
  · rcases openLeft with ⟨leftState, leftTemplate⟩
    rcases openRight with ⟨rightState, rightTemplate⟩
    cases hselected with
    | right phaseData hdecode hinvariant =>
        have hcanonical :=
          profiledRawJointRecurrentOwnerFibreRightBoundaryData?_openOpen A
            strategy hwin rightState leftState rightTemplate leftTemplate
              rightFibre leftFibre closedLeft closedRight oneCoordinates
                twoCoordinates
        have hphaseOption := hcanonical.symm.trans hdecode
        injection hphaseOption with hphase
        subst phaseData
        have hrightInvariant := hinvariant.1
        dsimp only [ProfiledRawJointRecurrentRightBoundaryInvariant,
          ProfiledRawJointRightOwnerFibreControl.receiverAt] at hrightInvariant
        rcases hrightInvariant with
          ⟨rightCode, rightRoot, _rightPast, hrightState, hrightCode,
            hrightRoot, hrightMove, _rightOwner, _rightMonitor⟩
        have hleftInvariant := hinvariant.2
        dsimp only [
          ProfiledRawJointRecurrentRightPhaseLiveBoundaryData.dormantLeftData,
          ProfiledRawJointRecurrentLeftBoundaryInvariant,
          ProfiledRawJointLeftOwnerFibreControl.receiverAt,
          ProfiledRawJointRightOwnerFibreControl.receiverAt] at hleftInvariant
        rcases hleftInvariant with
          ⟨leftCode, leftRoot, _leftPast, hleftState, hleftCode, hleftRoot,
            hleftMove, _leftOwner, _leftMonitor⟩
        exact
          (profiledRawJointRecurrentOwnerFibreBoundarySelected_strictRight_openOpen
            A strategy hwin rightState leftState rightTemplate leftTemplate
              rightFibre leftFibre closedLeft closedRight oneCoordinates
                twoCoordinates honeValid htwoValid hrightState rightCode
                  hrightCode rightRoot hrightRoot hrightMove hleftState
                    leftCode hleftCode leftRoot hleftRoot hleftMove inputOne
                      inputTwo).2
    | left phaseData hright hdecode hinvariant =>
        simp [profiledRawJointRecurrentOwnerFibreLeftBoundaryData?] at hdecode
  · rcases openLeft with ⟨leftState, leftTemplate⟩
    rcases closedRight with ⟨rightState, rightTemplate⟩
    cases hselected with
    | right phaseData hdecode hinvariant =>
        simp [profiledRawJointRecurrentOwnerFibreRightBoundaryData?] at hdecode
    | left phaseData hright hdecode hinvariant =>
        have hcanonical :=
          profiledRawJointRecurrentOwnerFibreLeftBoundaryData?_fibreFibre A
            strategy hwin rightState leftState rightTemplate leftTemplate
              rightFibre leftFibre closedLeft openRight oneCoordinates
                twoCoordinates
        have hphaseOption := hcanonical.symm.trans hdecode
        injection hphaseOption with hphase
        subst phaseData
        have hleftInvariant := hinvariant.1
        dsimp only [ProfiledRawJointRecurrentLeftBoundaryInvariant,
          ProfiledRawJointLeftOwnerFibreControl.receiverAt] at hleftInvariant
        rcases hleftInvariant with
          ⟨leftCode, leftRoot, _leftPast, hleftState, hleftCode, hleftRoot,
            hleftMove, _leftOwner, _leftMonitor⟩
        have hrightInvariant := hinvariant.2
        dsimp only [
          ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData.dormantRightData,
          ProfiledRawJointRecurrentRightBoundaryInvariant,
          ProfiledRawJointRightOwnerFibreControl.receiverAt,
          ProfiledRawJointLeftOwnerFibreControl.receiverAt] at hrightInvariant
        rcases hrightInvariant with
          ⟨rightCode, rightRoot, _rightPast, hrightState, hrightCode,
            hrightRoot, hrightMove, _rightOwner, _rightMonitor⟩
        exact
          (profiledRawJointRecurrentOwnerFibreBoundarySelected_strictRight_leftFibreFibre
            A strategy hwin rightState leftState rightTemplate leftTemplate
              rightFibre leftFibre closedLeft openRight oneCoordinates
                twoCoordinates honeValid htwoValid hrightState rightCode
                  hrightCode rightRoot hrightRoot hrightMove hleftState
                    leftCode hleftCode leftRoot hleftRoot hleftMove inputOne
                      inputTwo).2
  · rcases closedLeft with ⟨leftState, leftTemplate⟩
    rcases openRight with ⟨rightState, rightTemplate⟩
    cases hselected with
    | right phaseData hdecode hinvariant =>
        have hcanonical :=
          profiledRawJointRecurrentOwnerFibreRightBoundaryData?_fibreFibre A
            strategy hwin rightState leftState rightTemplate leftTemplate
              rightFibre leftFibre openLeft closedRight oneCoordinates
                twoCoordinates
        have hphaseOption := hcanonical.symm.trans hdecode
        injection hphaseOption with hphase
        subst phaseData
        have hrightInvariant := hinvariant.1
        dsimp only [ProfiledRawJointRecurrentRightBoundaryInvariant,
          ProfiledRawJointRightOwnerFibreControl.receiverAt] at hrightInvariant
        rcases hrightInvariant with
          ⟨rightCode, rightRoot, _rightPast, hrightState, hrightCode,
            hrightRoot, hrightMove, _rightOwner, _rightMonitor⟩
        have hleftInvariant := hinvariant.2
        dsimp only [
          ProfiledRawJointRecurrentRightPhaseLiveBoundaryData.dormantLeftData,
          ProfiledRawJointRecurrentLeftBoundaryInvariant,
          ProfiledRawJointLeftOwnerFibreControl.receiverAt,
          ProfiledRawJointRightOwnerFibreControl.receiverAt] at hleftInvariant
        rcases hleftInvariant with
          ⟨leftCode, leftRoot, _leftPast, hleftState, hleftCode, hleftRoot,
            hleftMove, _leftOwner, _leftMonitor⟩
        exact
          (profiledRawJointRecurrentOwnerFibreBoundarySelected_strictRight_fibreFibre
            A strategy hwin rightState leftState rightTemplate leftTemplate
              rightFibre leftFibre openLeft closedRight oneCoordinates
                twoCoordinates honeValid htwoValid hrightState rightCode
                  hrightCode rightRoot hrightRoot hrightMove hleftState
                    leftCode hleftCode leftRoot hleftRoot hleftMove inputOne
                      inputTwo).2
    | left phaseData hright hdecode hinvariant =>
        simp [profiledRawJointRecurrentOwnerFibreLeftBoundaryData?] at hdecode
  · rcases closedLeft with ⟨leftState, leftTemplate⟩
    rcases closedRight with ⟨rightState, rightTemplate⟩
    cases hselected with
    | right phaseData hdecode hinvariant =>
        have hcanonical :=
          profiledRawJointRecurrentOwnerFibreRightBoundaryData?_closedClosed A
            strategy hwin rightState leftState rightTemplate leftTemplate
              rightFibre leftFibre openLeft openRight oneCoordinates
                twoCoordinates
        have hphaseOption := hcanonical.symm.trans hdecode
        injection hphaseOption with hphase
        subst phaseData
        have hrightInvariant := hinvariant.1
        dsimp only [ProfiledRawJointRecurrentRightBoundaryInvariant,
          ProfiledRawJointRightOwnerFibreControl.receiverAt] at hrightInvariant
        rcases hrightInvariant with
          ⟨rightCode, rightRoot, _rightPast, hrightState, hrightCode,
            hrightRoot, hrightMove, _rightOwner, _rightMonitor⟩
        have hleftInvariant := hinvariant.2
        dsimp only [
          ProfiledRawJointRecurrentRightPhaseLiveBoundaryData.dormantLeftData,
          ProfiledRawJointRecurrentLeftBoundaryInvariant,
          ProfiledRawJointLeftOwnerFibreControl.receiverAt,
          ProfiledRawJointRightOwnerFibreControl.receiverAt] at hleftInvariant
        rcases hleftInvariant with
          ⟨leftCode, leftRoot, _leftPast, hleftState, hleftCode, hleftRoot,
            hleftMove, _leftOwner, _leftMonitor⟩
        exact
          (profiledRawJointRecurrentOwnerFibreBoundarySelected_strictRight_closedClosed
            A strategy hwin rightState leftState rightTemplate leftTemplate
              rightFibre leftFibre openLeft openRight oneCoordinates
                twoCoordinates honeValid htwoValid hrightState rightCode
                  hrightCode rightRoot hrightRoot hrightMove hleftState
                    leftCode hleftCode leftRoot hleftRoot hleftMove inputOne
                      inputTwo).2
    | left phaseData hright hdecode hinvariant =>
        simp [profiledRawJointRecurrentOwnerFibreLeftBoundaryData?] at hdecode

/-- Coordinate-general strict-left closure of the complete pending/pending
quadrant.  The same decoder priority table determines the source phase;
opening the first endpoint sends `00` and `10` to `00`, and sends `01` and
`11` to the left-priority `01` state. -/
theorem
    ProfiledRawJointRecurrentOwnerFibreBoundarySelected.strictLeft_fibreFibre
    (pendingOne :
      ProfiledRawJointRecurrentRightToLeftOwnerFibrePending A strategy hwin)
    (pendingTwo :
      ProfiledRawJointRecurrentLeftToRightOwnerFibrePending A strategy hwin)
    (oneCoordinates twoCoordinates :
      ProfiledRawJointRecurrentBoundaryBankCoordinates A strategy hwin)
    (hselected :
      ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin
        (.inr pendingOne, oneCoordinates) (.inr pendingTwo, twoCoordinates))
    (honeValid :
      ProfiledRawJointRecurrentRightToLeftOwnerFibreValid A strategy hwin
        pendingOne)
    (htwoValid :
      ProfiledRawJointRecurrentLeftToRightOwnerFibreValid A strategy hwin
        pendingTwo)
    (inputOne : In₁) (inputTwo : In₂) :
    ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin
      (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne A strategy hwin
        (.inr pendingOne, oneCoordinates) inputOne
        (.inr pendingTwo, twoCoordinates) inputTwo).1
      (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvTwo A strategy hwin
        (.inr pendingTwo, twoCoordinates) inputTwo).1 := by
  rcases pendingOne with
    ⟨memberOne, ⟨⟨rightFibre, forkOne⟩, unitOne⟩⟩
  rcases unitOne with ⟨⟩
  rcases forkOne with ⟨openLeft, closedLeft⟩
  rcases pendingTwo with
    ⟨memberTwo, ⟨⟨leftFibre, forkTwo⟩, unitTwo⟩⟩
  rcases unitTwo with ⟨⟩
  rcases forkTwo with ⟨openRight, closedRight⟩
  cases memberOne <;> cases memberTwo
  · rcases openLeft with ⟨leftState, leftTemplate⟩
    rcases openRight with ⟨rightState, rightTemplate⟩
    cases hselected with
    | right phaseData hdecode hinvariant =>
        have hcanonical :=
          profiledRawJointRecurrentOwnerFibreRightBoundaryData?_openOpen A
            strategy hwin rightState leftState rightTemplate leftTemplate
              rightFibre leftFibre closedLeft closedRight oneCoordinates
                twoCoordinates
        have hphaseOption := hcanonical.symm.trans hdecode
        injection hphaseOption with hphase
        subst phaseData
        have hrightInvariant := hinvariant.1
        dsimp only [ProfiledRawJointRecurrentRightBoundaryInvariant,
          ProfiledRawJointRightOwnerFibreControl.receiverAt] at hrightInvariant
        rcases hrightInvariant with
          ⟨rightCode, rightRoot, _rightPast, hrightState, hrightCode,
            hrightRoot, hrightMove, _rightOwner, _rightMonitor⟩
        have hleftInvariant := hinvariant.2
        dsimp only [
          ProfiledRawJointRecurrentRightPhaseLiveBoundaryData.dormantLeftData,
          ProfiledRawJointRecurrentLeftBoundaryInvariant,
          ProfiledRawJointLeftOwnerFibreControl.receiverAt,
          ProfiledRawJointRightOwnerFibreControl.receiverAt] at hleftInvariant
        rcases hleftInvariant with
          ⟨leftCode, leftRoot, _leftPast, hleftState, hleftCode, hleftRoot,
            hleftMove, _leftOwner, _leftMonitor⟩
        exact
          (profiledRawJointRecurrentOwnerFibreBoundarySelected_strictLeft_openOpen
            A strategy hwin rightState leftState rightTemplate leftTemplate
              rightFibre leftFibre closedLeft closedRight oneCoordinates
                twoCoordinates honeValid htwoValid hrightState rightCode
                  hrightCode rightRoot hrightRoot hrightMove hleftState
                    leftCode hleftCode leftRoot hleftRoot hleftMove inputOne
                      inputTwo).2
    | left phaseData hright hdecode hinvariant =>
        simp [profiledRawJointRecurrentOwnerFibreLeftBoundaryData?] at hdecode
  · rcases openLeft with ⟨leftState, leftTemplate⟩
    rcases closedRight with ⟨rightState, rightTemplate⟩
    cases hselected with
    | right phaseData hdecode hinvariant =>
        simp [profiledRawJointRecurrentOwnerFibreRightBoundaryData?] at hdecode
    | left phaseData hright hdecode hinvariant =>
        have hcanonical :=
          profiledRawJointRecurrentOwnerFibreLeftBoundaryData?_fibreFibre A
            strategy hwin rightState leftState rightTemplate leftTemplate
              rightFibre leftFibre closedLeft openRight oneCoordinates
                twoCoordinates
        have hphaseOption := hcanonical.symm.trans hdecode
        injection hphaseOption with hphase
        subst phaseData
        have hleftInvariant := hinvariant.1
        dsimp only [ProfiledRawJointRecurrentLeftBoundaryInvariant,
          ProfiledRawJointLeftOwnerFibreControl.receiverAt] at hleftInvariant
        rcases hleftInvariant with
          ⟨leftCode, leftRoot, _leftPast, hleftState, hleftCode, hleftRoot,
            hleftMove, _leftOwner, _leftMonitor⟩
        have hrightInvariant := hinvariant.2
        dsimp only [
          ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData.dormantRightData,
          ProfiledRawJointRecurrentRightBoundaryInvariant,
          ProfiledRawJointRightOwnerFibreControl.receiverAt,
          ProfiledRawJointLeftOwnerFibreControl.receiverAt] at hrightInvariant
        rcases hrightInvariant with
          ⟨rightCode, rightRoot, _rightPast, hrightState, hrightCode,
            hrightRoot, hrightMove, _rightOwner, _rightMonitor⟩
        exact
          (profiledRawJointRecurrentOwnerFibreBoundarySelected_strictLeft_leftFibreFibre
            A strategy hwin rightState leftState rightTemplate leftTemplate
              rightFibre leftFibre closedLeft openRight oneCoordinates
                twoCoordinates honeValid htwoValid hrightState rightCode
                  hrightCode rightRoot hrightRoot hrightMove hleftState
                    leftCode hleftCode leftRoot hleftRoot hleftMove inputOne
                      inputTwo).2
  · rcases closedLeft with ⟨leftState, leftTemplate⟩
    rcases openRight with ⟨rightState, rightTemplate⟩
    cases hselected with
    | right phaseData hdecode hinvariant =>
        have hcanonical :=
          profiledRawJointRecurrentOwnerFibreRightBoundaryData?_fibreFibre A
            strategy hwin rightState leftState rightTemplate leftTemplate
              rightFibre leftFibre openLeft closedRight oneCoordinates
                twoCoordinates
        have hphaseOption := hcanonical.symm.trans hdecode
        injection hphaseOption with hphase
        subst phaseData
        have hrightInvariant := hinvariant.1
        dsimp only [ProfiledRawJointRecurrentRightBoundaryInvariant,
          ProfiledRawJointRightOwnerFibreControl.receiverAt] at hrightInvariant
        rcases hrightInvariant with
          ⟨rightCode, rightRoot, _rightPast, hrightState, hrightCode,
            hrightRoot, hrightMove, _rightOwner, _rightMonitor⟩
        have hleftInvariant := hinvariant.2
        dsimp only [
          ProfiledRawJointRecurrentRightPhaseLiveBoundaryData.dormantLeftData,
          ProfiledRawJointRecurrentLeftBoundaryInvariant,
          ProfiledRawJointLeftOwnerFibreControl.receiverAt,
          ProfiledRawJointRightOwnerFibreControl.receiverAt] at hleftInvariant
        rcases hleftInvariant with
          ⟨leftCode, leftRoot, _leftPast, hleftState, hleftCode, hleftRoot,
            hleftMove, _leftOwner, _leftMonitor⟩
        exact
          (profiledRawJointRecurrentOwnerFibreBoundarySelected_strictLeft_fibreFibre
            A strategy hwin rightState leftState rightTemplate leftTemplate
              rightFibre leftFibre openLeft closedRight oneCoordinates
                twoCoordinates honeValid htwoValid hrightState rightCode
                  hrightCode rightRoot hrightRoot hrightMove hleftState
                    leftCode hleftCode leftRoot hleftRoot hleftMove inputOne
                      inputTwo).2
    | left phaseData hright hdecode hinvariant =>
        simp [profiledRawJointRecurrentOwnerFibreLeftBoundaryData?] at hdecode
  · rcases closedLeft with ⟨leftState, leftTemplate⟩
    rcases closedRight with ⟨rightState, rightTemplate⟩
    cases hselected with
    | right phaseData hdecode hinvariant =>
        have hcanonical :=
          profiledRawJointRecurrentOwnerFibreRightBoundaryData?_closedClosed A
            strategy hwin rightState leftState rightTemplate leftTemplate
              rightFibre leftFibre openLeft openRight oneCoordinates
                twoCoordinates
        have hphaseOption := hcanonical.symm.trans hdecode
        injection hphaseOption with hphase
        subst phaseData
        have hrightInvariant := hinvariant.1
        dsimp only [ProfiledRawJointRecurrentRightBoundaryInvariant,
          ProfiledRawJointRightOwnerFibreControl.receiverAt] at hrightInvariant
        rcases hrightInvariant with
          ⟨rightCode, rightRoot, _rightPast, hrightState, hrightCode,
            hrightRoot, hrightMove, _rightOwner, _rightMonitor⟩
        have hleftInvariant := hinvariant.2
        dsimp only [
          ProfiledRawJointRecurrentRightPhaseLiveBoundaryData.dormantLeftData,
          ProfiledRawJointRecurrentLeftBoundaryInvariant,
          ProfiledRawJointLeftOwnerFibreControl.receiverAt,
          ProfiledRawJointRightOwnerFibreControl.receiverAt] at hleftInvariant
        rcases hleftInvariant with
          ⟨leftCode, leftRoot, _leftPast, hleftState, hleftCode, hleftRoot,
            hleftMove, _leftOwner, _leftMonitor⟩
        exact
          (profiledRawJointRecurrentOwnerFibreBoundarySelected_strictLeft_closedClosed
            A strategy hwin rightState leftState rightTemplate leftTemplate
              rightFibre leftFibre openLeft openRight oneCoordinates
                twoCoordinates honeValid htwoValid hrightState rightCode
                  hrightCode rightRoot hrightRoot hrightMove hleftState
                    leftCode hleftCode leftRoot hleftRoot hleftMove inputOne
                      inputTwo).2
    | left phaseData hright hdecode hinvariant =>
        simp [profiledRawJointRecurrentOwnerFibreLeftBoundaryData?] at hdecode

/-! ## Complete strict-right closure -/

/-- The compact operational relation is closed under every strict-right
round.  The proof is an exhaustive split over the two endpoint summands;
each reachable quadrant is discharged by the corresponding decoder-driven
lemma above. -/
theorem ProfiledRawJointRecurrentOwnerFibreBoundaryOperational.strictRight
    (one :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin)
    (two :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin)
    (hoperational :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOperational A strategy hwin
        one two)
    (inputOne : In₁) (inputTwo : In₂) :
    ProfiledRawJointRecurrentOwnerFibreBoundaryOperational A strategy hwin
      (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvOne A strategy hwin
        one inputOne).1
      (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo A strategy hwin
        two inputTwo one inputOne).1 := by
  rcases one with ⟨oneBase, oneCoordinates⟩
  rcases two with ⟨twoBase, twoCoordinates⟩
  have hselected :
      ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin
        (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvOne A strategy hwin
          (oneBase, oneCoordinates) inputOne).1
        (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo A strategy hwin
          (twoBase, twoCoordinates) inputTwo (oneBase, oneCoordinates)
            inputOne).1 := by
    cases oneBase with
    | inl oneBridge =>
        cases twoBase with
        | inl twoBridge =>
            exact hoperational.selected.strictRight_bridgeBridge A strategy
              hwin oneBridge twoBridge oneCoordinates twoCoordinates
                hoperational.stagedAnchor inputOne inputTwo
        | inr pendingTwo =>
            cases oneBridge with
            | inl staged =>
                have htwoValid :
                    ProfiledRawJointRecurrentLeftToRightOwnerFibreValid A
                      strategy hwin pendingTwo := by
                  simpa [ProfiledRawJointRecurrentOwnerFibreBoundaryTwoValid]
                    using hoperational.twoValid
                exact hoperational.selected.strictRight_stagedFibre A strategy
                  hwin staged pendingTwo oneCoordinates twoCoordinates
                    htwoValid hoperational.stagedAnchor.1 inputOne inputTwo
            | inr installed =>
                exact hoperational.selected.strictRight_installedFibre A
                  strategy hwin installed pendingTwo oneCoordinates
                    twoCoordinates inputOne inputTwo
    | inr pendingOne =>
        have honeValid :
            ProfiledRawJointRecurrentRightToLeftOwnerFibreValid A strategy
              hwin pendingOne := by
          simpa [ProfiledRawJointRecurrentOwnerFibreBoundaryOneValid] using
            hoperational.oneValid
        cases twoBase with
        | inl twoBridge =>
            cases twoBridge with
            | inl staged =>
                exact hoperational.selected.strictRight_fibreStaged A strategy
                  hwin pendingOne staged oneCoordinates twoCoordinates
                    honeValid inputOne inputTwo
            | inr installed =>
                exact
                  hoperational.selected.strictRight_fibreInstalled A strategy
                    hwin pendingOne installed oneCoordinates twoCoordinates
                      honeValid inputOne inputTwo
        | inr pendingTwo =>
            have htwoValid :
                ProfiledRawJointRecurrentLeftToRightOwnerFibreValid A strategy
                  hwin pendingTwo := by
              simpa [ProfiledRawJointRecurrentOwnerFibreBoundaryTwoValid] using
                hoperational.twoValid
            exact hoperational.selected.strictRight_fibreFibre A strategy hwin
              pendingOne pendingTwo oneCoordinates twoCoordinates honeValid
                htwoValid inputOne inputTwo
  exact
    { selected := hselected
      oneValid :=
        hoperational.oneValid.noRecv A strategy hwin
          (oneBase, oneCoordinates) inputOne
      twoValid :=
        profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo_valid A
          strategy hwin (oneBase, oneCoordinates) (twoBase, twoCoordinates)
            hoperational.selected inputOne inputTwo
      stagedAnchor :=
        profiledRawJointRecurrentOwnerFibreBoundaryStagedAnchor_strictRight A
          strategy hwin (oneBase, oneCoordinates) (twoBase, twoCoordinates)
            hoperational.selected hoperational.stagedAnchor inputOne inputTwo }

/-- The compact operational relation is closed under every strict-left
round.  This is the exhaustive mirror of `strictRight`; its two
opposite-direction staged branches consume exactly the corresponding staged
anchor component. -/
theorem ProfiledRawJointRecurrentOwnerFibreBoundaryOperational.strictLeft
    (one :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin)
    (two :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin)
    (hoperational :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOperational A strategy hwin
        one two)
    (inputOne : In₁) (inputTwo : In₂) :
    ProfiledRawJointRecurrentOwnerFibreBoundaryOperational A strategy hwin
      (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne A strategy hwin
        one inputOne two inputTwo).1
      (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvTwo A strategy hwin
        two inputTwo).1 := by
  rcases one with ⟨oneBase, oneCoordinates⟩
  rcases two with ⟨twoBase, twoCoordinates⟩
  have hselected :
      ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin
        (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne A strategy
          hwin (oneBase, oneCoordinates) inputOne (twoBase, twoCoordinates)
            inputTwo).1
        (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvTwo A strategy hwin
          (twoBase, twoCoordinates) inputTwo).1 := by
    cases oneBase with
    | inl oneBridge =>
        cases twoBase with
        | inl twoBridge =>
            exact hoperational.selected.strictLeft_bridgeBridge A strategy
              hwin oneBridge twoBridge oneCoordinates twoCoordinates
                hoperational.stagedAnchor inputOne inputTwo
        | inr pendingTwo =>
            have htwoValid :
                ProfiledRawJointRecurrentLeftToRightOwnerFibreValid A strategy
                  hwin pendingTwo := by
              simpa [ProfiledRawJointRecurrentOwnerFibreBoundaryTwoValid] using
                hoperational.twoValid
            cases oneBridge with
            | inl staged =>
                exact hoperational.selected.strictLeft_stagedFibre A strategy
                  hwin staged pendingTwo oneCoordinates twoCoordinates
                    htwoValid inputOne inputTwo
            | inr installed =>
                exact hoperational.selected.strictLeft_installedFibre A
                  strategy hwin installed pendingTwo oneCoordinates
                    twoCoordinates htwoValid inputOne inputTwo
    | inr pendingOne =>
        cases twoBase with
        | inl twoBridge =>
            cases twoBridge with
            | inl staged =>
                have honeValid :
                    ProfiledRawJointRecurrentRightToLeftOwnerFibreValid A
                      strategy hwin pendingOne := by
                  simpa [ProfiledRawJointRecurrentOwnerFibreBoundaryOneValid]
                    using hoperational.oneValid
                exact hoperational.selected.strictLeft_fibreStaged A strategy
                  hwin pendingOne staged oneCoordinates twoCoordinates
                    honeValid hoperational.stagedAnchor.2 inputOne inputTwo
            | inr installed =>
                exact
                  hoperational.selected.strictLeft_fibreInstalled A strategy
                    hwin pendingOne installed oneCoordinates twoCoordinates
                      inputOne inputTwo
        | inr pendingTwo =>
            have honeValid :
                ProfiledRawJointRecurrentRightToLeftOwnerFibreValid A strategy
                  hwin pendingOne := by
              simpa [ProfiledRawJointRecurrentOwnerFibreBoundaryOneValid] using
                hoperational.oneValid
            have htwoValid :
                ProfiledRawJointRecurrentLeftToRightOwnerFibreValid A strategy
                  hwin pendingTwo := by
              simpa [ProfiledRawJointRecurrentOwnerFibreBoundaryTwoValid] using
                hoperational.twoValid
            exact hoperational.selected.strictLeft_fibreFibre A strategy hwin
              pendingOne pendingTwo oneCoordinates twoCoordinates honeValid
                htwoValid inputOne inputTwo
  exact
    { selected := hselected
      oneValid :=
        profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne_valid A
          strategy hwin (oneBase, oneCoordinates) (twoBase, twoCoordinates)
            hoperational.selected inputOne inputTwo
      twoValid :=
        hoperational.twoValid.noRecv A strategy hwin
          (twoBase, twoCoordinates) inputTwo
      stagedAnchor :=
        profiledRawJointRecurrentOwnerFibreBoundaryStagedAnchor_strictLeft A
          strategy hwin (oneBase, oneCoordinates) (twoBase, twoCoordinates)
            hoperational.selected hoperational.stagedAnchor inputOne inputTwo }

/-! ## Closure packaging -/

theorem profiledRawJointRecurrentOwnerFibreBoundaryClose_oneValid
    (one :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin)
    (two :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin)
    (hselected :
      ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin
        one two)
    (inputOne : In₁) (inputTwo : In₂) :
    ProfiledRawJointRecurrentOwnerFibreBoundaryOneValid A strategy hwin
      (profiledRawJointRecurrentOwnerFibreBoundaryClose A strategy hwin one
        inputOne two inputTwo).1 := by
  cases hselected with
  | right phaseData hright hinvariant =>
      have hreceive :
          profiledRawJointRecurrentOwnerFibreBoundaryReceive? A strategy hwin
              one two (inputOne, inputTwo) =
            some
              (phaseData.ownerFibreReceive A strategy hwin
                (inputOne, inputTwo)) := by
        simp [profiledRawJointRecurrentOwnerFibreBoundaryReceive?, hright]
      rw [profiledRawJointRecurrentOwnerFibreBoundaryClose, hreceive]
      have hvalid :=
        hinvariant.1.ownerFibreReceive_valid A strategy hwin phaseData.1
          phaseData.2.1 phaseData.2.2 (inputOne, inputTwo)
      simpa [ProfiledRawJointRecurrentOwnerFibreBoundaryOneValid,
        ProfiledRawJointRecurrentRightPhaseLiveBoundaryData.ownerFibreReceive]
        using hvalid.2
  | left phaseData hright hleft hinvariant =>
      have hreceive :
          profiledRawJointRecurrentOwnerFibreBoundaryReceive? A strategy hwin
              one two (inputOne, inputTwo) =
            some
              (phaseData.ownerFibreReceive A strategy hwin
                (inputOne, inputTwo)) := by
        simp [profiledRawJointRecurrentOwnerFibreBoundaryReceive?, hright,
          hleft]
      rw [profiledRawJointRecurrentOwnerFibreBoundaryClose, hreceive]
      simp [ProfiledRawJointRecurrentOwnerFibreBoundaryOneValid,
        ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData.ownerFibreReceive]

theorem profiledRawJointRecurrentOwnerFibreBoundaryClose_twoValid
    (one :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin)
    (two :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin)
    (hselected :
      ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin
        one two)
    (inputOne : In₁) (inputTwo : In₂) :
    ProfiledRawJointRecurrentOwnerFibreBoundaryTwoValid A strategy hwin
      (profiledRawJointRecurrentOwnerFibreBoundaryClose A strategy hwin one
        inputOne two inputTwo).2 := by
  cases hselected with
  | right phaseData hright hinvariant =>
      have hreceive :
          profiledRawJointRecurrentOwnerFibreBoundaryReceive? A strategy hwin
              one two (inputOne, inputTwo) =
            some
              (phaseData.ownerFibreReceive A strategy hwin
                (inputOne, inputTwo)) := by
        simp [profiledRawJointRecurrentOwnerFibreBoundaryReceive?, hright]
      rw [profiledRawJointRecurrentOwnerFibreBoundaryClose, hreceive]
      simp [ProfiledRawJointRecurrentOwnerFibreBoundaryTwoValid,
        ProfiledRawJointRecurrentRightPhaseLiveBoundaryData.ownerFibreReceive]
  | left phaseData hright hleft hinvariant =>
      have hreceive :
          profiledRawJointRecurrentOwnerFibreBoundaryReceive? A strategy hwin
              one two (inputOne, inputTwo) =
            some
              (phaseData.ownerFibreReceive A strategy hwin
                (inputOne, inputTwo)) := by
        simp [profiledRawJointRecurrentOwnerFibreBoundaryReceive?, hright,
          hleft]
      rw [profiledRawJointRecurrentOwnerFibreBoundaryClose, hreceive]
      have hvalid :=
        hinvariant.1.ownerFibreReceive_valid A strategy hwin phaseData.1
          phaseData.2.1 phaseData.2.2 (inputOne, inputTwo)
      simpa [ProfiledRawJointRecurrentOwnerFibreBoundaryTwoValid,
        ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData.ownerFibreReceive]
        using hvalid.2

theorem profiledRawJointRecurrentOwnerFibreBoundaryClose_stagedAnchor
    (one :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin)
    (two :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin)
    (hselected :
      ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin
        one two)
    (inputOne : In₁) (inputTwo : In₂) :
    let result :=
      profiledRawJointRecurrentOwnerFibreBoundaryClose A strategy hwin one
        inputOne two inputTwo
    ProfiledRawJointRecurrentOwnerFibreBoundaryStagedAnchor A strategy hwin
      result.1 result.2 := by
  cases hselected with
  | right phaseData hright hinvariant =>
      have hreceive :
          profiledRawJointRecurrentOwnerFibreBoundaryReceive? A strategy hwin
              one two (inputOne, inputTwo) =
            some
              (phaseData.ownerFibreReceive A strategy hwin
                (inputOne, inputTwo)) := by
        simp [profiledRawJointRecurrentOwnerFibreBoundaryReceive?, hright]
      rw [profiledRawJointRecurrentOwnerFibreBoundaryClose, hreceive]
      constructor
      · intro staged hstaged
        simp [ProfiledRawJointRecurrentRightPhaseLiveBoundaryData.ownerFibreReceive]
          at hstaged
      · rcases phaseData with ⟨data, oldState, oldOwner⟩
        rcases data with ⟨state, ⟨receiver, owner⟩, oldReceiver⟩
        intro staged hstaged
        dsimp [
          ProfiledRawJointRecurrentRightPhaseLiveBoundaryData.ownerFibreReceive,
          profiledRawJointRecurrentPhaseRightToLeftBridgeForkTwo,
          profiledRawJointRecurrentRightReceiveFor,
          ProfiledRawJointRecurrentRightBoundaryData.receiver,
          ProfiledRawJointRecurrentRightBoundaryData.owner,
          ProfiledRawJointRecurrentRightBoundaryData.target] at hstaged ⊢
        split at * <;> cases hstaged
        all_goals rfl
  | left phaseData hright hleft hinvariant =>
      have hreceive :
          profiledRawJointRecurrentOwnerFibreBoundaryReceive? A strategy hwin
              one two (inputOne, inputTwo) =
            some
              (phaseData.ownerFibreReceive A strategy hwin
                (inputOne, inputTwo)) := by
        simp [profiledRawJointRecurrentOwnerFibreBoundaryReceive?, hright,
          hleft]
      rw [profiledRawJointRecurrentOwnerFibreBoundaryClose, hreceive]
      constructor
      · rcases phaseData with ⟨data, oldState, oldOwner⟩
        rcases data with ⟨state, ⟨receiver, owner⟩, oldReceiver⟩
        intro staged hstaged
        dsimp [
          ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData.ownerFibreReceive,
          profiledRawJointRecurrentPhaseLeftToRightBridgeForkOne,
          profiledRawJointRecurrentLeftReceiveFor,
          ProfiledRawJointRecurrentLeftBoundaryData.receiver,
          ProfiledRawJointRecurrentLeftBoundaryData.owner,
          ProfiledRawJointRecurrentLeftBoundaryData.target] at hstaged ⊢
        split at * <;> cases hstaged
        all_goals rfl
      · intro staged hstaged
        simp [ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData.ownerFibreReceive]
          at hstaged

/-- The compact operational relation is closed under a simultaneous close. -/
theorem ProfiledRawJointRecurrentOwnerFibreBoundaryOperational.both
    (one :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin)
    (two :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin)
    (hoperational :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOperational A strategy hwin
        one two)
    (inputOne : In₁) (inputTwo : In₂) :
    let result :=
      profiledRawJointRecurrentOwnerFibreBoundaryClose A strategy hwin one
        inputOne two inputTwo
    ProfiledRawJointRecurrentOwnerFibreBoundaryOperational A strategy hwin
      result.1 result.2 := by
  dsimp only
  exact
    { selected :=
        profiledRawJointRecurrentOwnerFibreBoundarySelected_both A strategy
          hwin one two hoperational.selected inputOne inputTwo
      oneValid :=
        profiledRawJointRecurrentOwnerFibreBoundaryClose_oneValid A strategy
          hwin one two hoperational.selected inputOne inputTwo
      twoValid :=
        profiledRawJointRecurrentOwnerFibreBoundaryClose_twoValid A strategy
          hwin one two hoperational.selected inputOne inputTwo
      stagedAnchor :=
        profiledRawJointRecurrentOwnerFibreBoundaryClose_stagedAnchor A
          strategy hwin one two hoperational.selected inputOne inputTwo }

/-- Once semantic selection for a strict-right target is known, fibre
validity and the staged anchor are automatic. -/
theorem ProfiledRawJointRecurrentOwnerFibreBoundaryOperational.strictRight_of_selected
    (one :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin)
    (two :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin)
    (hoperational :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOperational A strategy hwin
        one two)
    (inputOne : In₁) (inputTwo : In₂)
    (hselected :
      ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin
        (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvOne A strategy hwin
          one inputOne).1
        (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo A strategy hwin
          two inputTwo one inputOne).1) :
    ProfiledRawJointRecurrentOwnerFibreBoundaryOperational A strategy hwin
      (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvOne A strategy hwin
        one inputOne).1
      (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo A strategy hwin
        two inputTwo one inputOne).1 where
  selected := hselected
  oneValid := hoperational.oneValid.noRecv A strategy hwin one inputOne
  twoValid :=
    profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo_valid A strategy
      hwin one two hoperational.selected inputOne inputTwo
  stagedAnchor :=
    profiledRawJointRecurrentOwnerFibreBoundaryStagedAnchor_strictRight A
      strategy hwin one two hoperational.selected hoperational.stagedAnchor
        inputOne inputTwo

/-- Strict-left mirror of `strictRight_of_selected`. -/
theorem ProfiledRawJointRecurrentOwnerFibreBoundaryOperational.strictLeft_of_selected
    (one :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin)
    (two :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin)
    (hoperational :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOperational A strategy hwin
        one two)
    (inputOne : In₁) (inputTwo : In₂)
    (hselected :
      ProfiledRawJointRecurrentOwnerFibreBoundarySelected A strategy hwin
        (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne A strategy hwin
          one inputOne two inputTwo).1
        (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvTwo A strategy hwin
          two inputTwo).1) :
    ProfiledRawJointRecurrentOwnerFibreBoundaryOperational A strategy hwin
      (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne A strategy hwin
        one inputOne two inputTwo).1
      (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvTwo A strategy hwin
        two inputTwo).1 where
  selected := hselected
  oneValid :=
    profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne_valid A strategy
      hwin one two hoperational.selected inputOne inputTwo
  twoValid := hoperational.twoValid.noRecv A strategy hwin two inputTwo
  stagedAnchor :=
    profiledRawJointRecurrentOwnerFibreBoundaryStagedAnchor_strictLeft A
      strategy hwin one two hoperational.selected hoperational.stagedAnchor
        inputOne inputTwo

/-! ## Generic exact-closing interface -/

/-! ### Canonical recurrent entry pairs -/

/-- Process one's half of a fresh right-oriented recurrent entry.  The
installed right owner and the staged right receiver share `rightState`; the
second coordinate retains the freshly resolved dormant-left bank state. -/
noncomputable def profiledRawJointRecurrentOwnerFibreRightEntryOne
    (rightState : BankControl A strategy hwin)
    (rightReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (rightOwner : (rightReceiver.1.memberController A false).Control)
    (leftTemplate : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (packet :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin) :
    ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin :=
  (.inl
    (.inr (rightState, ⟨rightReceiver.1, rightOwner⟩, leftTemplate)),
    (rightState, packet.successor))

/-- Process-two half of `profiledRawJointRecurrentOwnerFibreRightEntryOne`.
Its first bank coordinate is definitionally the state of the staged right
receiver. -/
noncomputable def profiledRawJointRecurrentOwnerFibreRightEntryTwo
    (rightState : BankControl A strategy hwin)
    (rightReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (packet :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin) :
    ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin :=
  (.inl (.inl (rightState, rightReceiver, some packet)),
    (rightState, packet.successor))

/-- A fresh right-oriented bridge pair satisfies the complete operational
relation whenever its decoded active/dormant phase has the dual matched-prefix
certificate. -/
theorem profiledRawJointRecurrentOwnerFibreRightEntry_operational
    (rightState : BankControl A strategy hwin)
    (rightReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (rightOwner : (rightReceiver.1.memberController A false).Control)
    (leftTemplate : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (packet :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin)
    (leftMove : ProfiledRawJointLeftPhysicalSiblingMove A)
    (hleftMove : packet.successor.2.1.2.2 = some leftMove)
    (hinvariant :
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryInvariant A strategy hwin
        ⟨(rightState, ⟨rightReceiver, rightOwner⟩,
            initialProfiledRawJointLeftPhysicalSiblingReceiver A leftMove
              .first),
          packet.successor,
          (leftMove.memberController A false).initial⟩) :
    ProfiledRawJointRecurrentOwnerFibreBoundaryOperational A strategy hwin
      (profiledRawJointRecurrentOwnerFibreRightEntryOne A strategy hwin
        rightState rightReceiver rightOwner leftTemplate packet)
      (profiledRawJointRecurrentOwnerFibreRightEntryTwo A strategy hwin
        rightState rightReceiver packet) := by
  let phaseData :
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryData A strategy hwin :=
    ⟨(rightState, ⟨rightReceiver, rightOwner⟩,
        initialProfiledRawJointLeftPhysicalSiblingReceiver A leftMove .first),
      packet.successor,
      (leftMove.memberController A false).initial⟩
  refine
    { selected := .right phaseData ?_ ?_
      oneValid := ?_
      twoValid := ?_
      stagedAnchor := ?_ }
  · simpa only [phaseData,
      profiledRawJointRecurrentOwnerFibreRightEntryOne,
      profiledRawJointRecurrentOwnerFibreRightEntryTwo] using
        profiledRawJointRecurrentOwnerFibreRightBoundaryData?_installedStaged
          A strategy hwin rightState rightReceiver rightOwner leftTemplate
            packet leftMove hleftMove (rightState, packet.successor)
              (rightState, packet.successor)
  · simpa only [phaseData] using hinvariant
  · trivial
  · trivial
  · constructor
    · intro staged hstaged
      simp [profiledRawJointRecurrentOwnerFibreRightEntryOne] at hstaged
    · intro staged hstaged
      simp [profiledRawJointRecurrentOwnerFibreRightEntryTwo] at hstaged
      subst staged
      rfl

/-- One reachable right-oriented boundary is sufficient to construct a
certified recurrent entry.  The bank successor supplies the fresh dormant
left move and its matched-prefix certificate; no extra dual invariant has to
be provided by the finite front. -/
theorem
    profiledRawJointRecurrentOwnerFibreRightEntry_operational_of_boundary
    (data : ProfiledRawJointRecurrentRightBoundaryData A strategy hwin)
    (hinvariant :
      ProfiledRawJointRecurrentRightBoundaryInvariant A strategy hwin data)
    (input : In₁ × In₂)
    (leftTemplate : ProfiledRawJointLeftPhysicalSiblingReceiver A) :
    let packet :=
      profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket A strategy
        hwin data.1 (data.target A strategy hwin input)
    ∃ leftMove : ProfiledRawJointLeftPhysicalSiblingMove A,
      packet.successor.2.1.2.2 = some leftMove ∧
        ProfiledRawJointRecurrentOwnerFibreBoundaryOperational A strategy hwin
          (profiledRawJointRecurrentOwnerFibreRightEntryOne A strategy hwin
            data.1 (data.receiver A strategy hwin)
              (data.owner A strategy hwin) leftTemplate packet)
          (profiledRawJointRecurrentOwnerFibreRightEntryTwo A strategy hwin
            data.1 (data.receiver A strategy hwin) packet) := by
  dsimp only
  obtain ⟨leftMove, hleftMove, hleftInvariant⟩ :=
    hinvariant.exists_freshLeft A strategy hwin data input
  let packet :=
    profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket A strategy
      hwin data.1 (data.target A strategy hwin input)
  have hpacketSuccessor :
      packet.successor = data.successor A strategy hwin input := by
    rfl
  have hpacketMove : packet.successor.2.1.2.2 = some leftMove := by
    rw [hpacketSuccessor]
    exact hleftMove
  have hactive :
      ProfiledRawJointRecurrentRightBoundaryInvariant A strategy hwin
        (data.1, data.2.1, leftTemplate) :=
    hinvariant.replaceOldReceiver A strategy hwin data leftTemplate
  have hdormant :
      ProfiledRawJointRecurrentLeftBoundaryInvariant A strategy hwin
        (packet.successor,
          ⟨initialProfiledRawJointLeftPhysicalSiblingReceiver A leftMove
              .first,
            (leftMove.memberController A false).initial⟩,
          data.receiver A strategy hwin) := by
    rw [hpacketSuccessor]
    exact
      hleftInvariant.replaceOldReceiver A strategy hwin
        (data.freshLeftData A strategy hwin input leftMove)
        (data.receiver A strategy hwin)
  have hphase :
      ProfiledRawJointRecurrentRightPhaseLiveBoundaryInvariant A strategy hwin
        ⟨(data.1,
            ⟨data.receiver A strategy hwin, data.owner A strategy hwin⟩,
            initialProfiledRawJointLeftPhysicalSiblingReceiver A leftMove
              .first),
          packet.successor,
          (leftMove.memberController A false).initial⟩ := by
    exact ⟨hactive, hdormant⟩
  refine ⟨leftMove, hpacketMove, ?_⟩
  exact
    profiledRawJointRecurrentOwnerFibreRightEntry_operational A strategy hwin
      data.1 (data.receiver A strategy hwin) (data.owner A strategy hwin)
        leftTemplate packet leftMove hpacketMove hphase

/-- Process-one half of the mirrored fresh left-oriented recurrent entry. -/
noncomputable def profiledRawJointRecurrentOwnerFibreLeftEntryOne
    (leftState : BankControl A strategy hwin)
    (leftReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (packet :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin) :
    ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin :=
  (.inl (.inl (leftState, leftReceiver, some packet)),
    (packet.successor, leftState))

/-- Process-two half of the mirrored fresh left-oriented recurrent entry. -/
noncomputable def profiledRawJointRecurrentOwnerFibreLeftEntryTwo
    (leftState : BankControl A strategy hwin)
    (leftReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (leftOwner : (leftReceiver.1.memberController A false).Control)
    (rightTemplate : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (packet :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin) :
    ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin :=
  (.inl
    (.inr (leftState, ⟨leftReceiver.1, leftOwner⟩, rightTemplate)),
    (packet.successor, leftState))

/-- Mirrored operational entry theorem. -/
theorem profiledRawJointRecurrentOwnerFibreLeftEntry_operational
    (leftState : BankControl A strategy hwin)
    (leftReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (leftOwner : (leftReceiver.1.memberController A false).Control)
    (rightTemplate : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (packet :
      ProfiledRawJointOneSidedPhysicalCompatibleBankResolvedTarget A strategy
        hwin)
    (rightMove : ProfiledRawJointRightPhysicalSiblingMove A)
    (hrightMove : packet.successor.2.1.2.1 = some rightMove)
    (hinvariant :
      ProfiledRawJointRecurrentLeftPhaseLiveBoundaryInvariant A strategy hwin
        ⟨(leftState, ⟨leftReceiver, leftOwner⟩,
            initialProfiledRawJointRightPhysicalSiblingReceiver A rightMove
              .first),
          packet.successor,
          (rightMove.memberController A false).initial⟩) :
    ProfiledRawJointRecurrentOwnerFibreBoundaryOperational A strategy hwin
      (profiledRawJointRecurrentOwnerFibreLeftEntryOne A strategy hwin
        leftState leftReceiver packet)
      (profiledRawJointRecurrentOwnerFibreLeftEntryTwo A strategy hwin
        leftState leftReceiver leftOwner rightTemplate packet) := by
  let phaseData :
      ProfiledRawJointRecurrentLeftPhaseLiveBoundaryData A strategy hwin :=
    ⟨(leftState, ⟨leftReceiver, leftOwner⟩,
        initialProfiledRawJointRightPhysicalSiblingReceiver A rightMove
          .first),
      packet.successor,
      (rightMove.memberController A false).initial⟩
  refine
    { selected := .left phaseData ?_ ?_ ?_
      oneValid := ?_
      twoValid := ?_
      stagedAnchor := ?_ }
  · rfl
  · simpa only [phaseData,
      profiledRawJointRecurrentOwnerFibreLeftEntryOne,
      profiledRawJointRecurrentOwnerFibreLeftEntryTwo] using
        profiledRawJointRecurrentOwnerFibreLeftBoundaryData?_stagedInstalled A
          strategy hwin leftState leftReceiver leftOwner rightTemplate packet
            rightMove hrightMove (packet.successor, leftState)
              (packet.successor, leftState)
  · simpa only [phaseData] using hinvariant
  · trivial
  · trivial
  · constructor
    · intro staged hstaged
      simp [profiledRawJointRecurrentOwnerFibreLeftEntryOne] at hstaged
      subst staged
      rfl
    · intro staged hstaged
      simp [profiledRawJointRecurrentOwnerFibreLeftEntryTwo] at hstaged

/-- Mirrored reduction from one reachable left-oriented boundary to a
certified recurrent entry. -/
theorem
    profiledRawJointRecurrentOwnerFibreLeftEntry_operational_of_boundary
    (data : ProfiledRawJointRecurrentLeftBoundaryData A strategy hwin)
    (hinvariant :
      ProfiledRawJointRecurrentLeftBoundaryInvariant A strategy hwin data)
    (input : In₁ × In₂)
    (rightTemplate : ProfiledRawJointRightPhysicalSiblingReceiver A) :
    let packet :=
      profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket A strategy
        hwin data.1 (data.target A strategy hwin input)
    ∃ rightMove : ProfiledRawJointRightPhysicalSiblingMove A,
      packet.successor.2.1.2.1 = some rightMove ∧
        ProfiledRawJointRecurrentOwnerFibreBoundaryOperational A strategy hwin
          (profiledRawJointRecurrentOwnerFibreLeftEntryOne A strategy hwin
            data.1 (data.receiver A strategy hwin) packet)
          (profiledRawJointRecurrentOwnerFibreLeftEntryTwo A strategy hwin
            data.1 (data.receiver A strategy hwin)
              (data.owner A strategy hwin) rightTemplate packet) := by
  dsimp only
  obtain ⟨rightMove, hrightMove, hrightInvariant⟩ :=
    hinvariant.exists_freshRight A strategy hwin data input
  let packet :=
    profiledRawJointOneSidedPhysicalCompatibleBankResolvePacket A strategy
      hwin data.1 (data.target A strategy hwin input)
  have hpacketSuccessor :
      packet.successor = data.successor A strategy hwin input := by
    rfl
  have hpacketMove : packet.successor.2.1.2.1 = some rightMove := by
    rw [hpacketSuccessor]
    exact hrightMove
  have hactive :
      ProfiledRawJointRecurrentLeftBoundaryInvariant A strategy hwin
        (data.1, data.2.1, rightTemplate) :=
    hinvariant.replaceOldReceiver A strategy hwin data rightTemplate
  have hdormant :
      ProfiledRawJointRecurrentRightBoundaryInvariant A strategy hwin
        (packet.successor,
          ⟨initialProfiledRawJointRightPhysicalSiblingReceiver A rightMove
              .first,
            (rightMove.memberController A false).initial⟩,
          data.receiver A strategy hwin) := by
    rw [hpacketSuccessor]
    exact
      hrightInvariant.replaceOldReceiver A strategy hwin
        (data.freshRightData A strategy hwin input rightMove)
        (data.receiver A strategy hwin)
  have hphase :
      ProfiledRawJointRecurrentLeftPhaseLiveBoundaryInvariant A strategy hwin
        ⟨(data.1,
            ⟨data.receiver A strategy hwin, data.owner A strategy hwin⟩,
            initialProfiledRawJointRightPhysicalSiblingReceiver A rightMove
              .first),
          packet.successor,
          (rightMove.memberController A false).initial⟩ := by
    exact ⟨hactive, hdormant⟩
  refine ⟨rightMove, hpacketMove, ?_⟩
  exact
    profiledRawJointRecurrentOwnerFibreLeftEntry_operational A strategy hwin
      data.1 (data.receiver A strategy hwin) (data.owner A strategy hwin)
        rightTemplate packet rightMove hpacketMove hphase

/-- Any certified entry pair for the recurrent owner-fibre carrier generates
the four relation laws required by the generic acknowledged exact-closing
wrapper.  The entry pair is kept explicit because this carrier is entered
after the finite front phase; it has no distinguished time-zero state of its
own. -/
noncomputable def profiledRawJointRecurrentOwnerFibreBoundaryRelationLaws
    (initialOne :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOneControl A strategy hwin)
    (initialTwo :
      ProfiledRawJointRecurrentOwnerFibreBoundaryTwoControl A strategy hwin)
    (hinitial :
      ProfiledRawJointRecurrentOwnerFibreBoundaryOperational A strategy hwin
        initialOne initialTwo) :
    FiniteAcknowledgedDelayedCarrier.ExactClosingRelationLaws
      initialOne initialTwo
      (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvOne A strategy hwin)
      (profiledRawJointRecurrentOwnerFibreBoundaryNoRecvTwo A strategy hwin)
      (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvOne A strategy hwin)
      (profiledRawJointRecurrentOwnerFibreBoundaryOpenRecvTwo A strategy hwin)
      (profiledRawJointRecurrentOwnerFibreBoundaryClose A strategy hwin)
      (ProfiledRawJointRecurrentOwnerFibreBoundaryOperational A strategy
        hwin) where
  initial := hinitial
  strictRight := by
    intro one inputOne two inputTwo hoperational
    exact
      ProfiledRawJointRecurrentOwnerFibreBoundaryOperational.strictRight A
        strategy hwin one two hoperational inputOne inputTwo
  strictLeft := by
    intro one inputOne two inputTwo hoperational
    exact
      ProfiledRawJointRecurrentOwnerFibreBoundaryOperational.strictLeft A
        strategy hwin one two hoperational inputOne inputTwo
  both := by
    intro one inputOne two inputTwo hoperational
    exact
      ProfiledRawJointRecurrentOwnerFibreBoundaryOperational.both A strategy
        hwin one two hoperational inputOne inputTwo

end

end DetParityAutomaton

end DistributedSynthesis
