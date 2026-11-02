/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyBankLocalInformedBridge
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyBankLocalPhaseLiveOwnerFibre
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedPhysicalCompatiblePolicyBankLocalPhaseLiveOwnerFibrePhase

/-!
# Finite-memory owner-fibre endpoint controls and decoder

The two endpoints retain separate augmented bank coordinates for the right
and left orientations.  Each endpoint is either in its informed bridge or in
the opposite orientation's fibre-backed pending state.  The decoder checks
the dependent move equalities before reconstructing an executable boundary.

Returning `none` is intentional on malformed control pairs.  Later runtime
invariants must prove that every reachable pair decodes in its active
orientation; `none` must not be confused with emptiness of the later parity
tree automaton.
-/

namespace DistributedSynthesis

universe u v x y s m

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable {Memory : Type m}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
  [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]
variable [Fintype Memory]

variable
  (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
  (hwin : ∀ env : EnvironmentSequence In₁ In₂,
    A.Accepts (execution strategy env))

private abbrev BankControl :=
  ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryBankControl
    (Memory := Memory) A strategy

local instance finiteMemoryEndpointDecidableEqBankControl :
    DecidableEq (BankControl (Memory := Memory) A strategy) :=
  Classical.decEq _

/-! ## Aligned boundary data -/

noncomputable abbrev ProfiledRawJointRecurrentFiniteMemoryRightBoundaryData :=
  BankControl (Memory := Memory) A strategy ×
    (Sigma fun receiver : ProfiledRawJointRightPhysicalSiblingReceiver A ↦
      (receiver.1.memberController A false).Control) ×
    ProfiledRawJointLeftPhysicalSiblingReceiver A

noncomputable abbrev ProfiledRawJointRecurrentFiniteMemoryLeftBoundaryData :=
  BankControl (Memory := Memory) A strategy ×
    (Sigma fun receiver : ProfiledRawJointLeftPhysicalSiblingReceiver A ↦
      (receiver.1.memberController A false).Control) ×
    ProfiledRawJointRightPhysicalSiblingReceiver A

noncomputable def ProfiledRawJointRecurrentFiniteMemoryRightBoundaryData.receiver
    (data : ProfiledRawJointRecurrentFiniteMemoryRightBoundaryData
      (Memory := Memory) A strategy) :
    ProfiledRawJointRightPhysicalSiblingReceiver A :=
  data.2.1.1

noncomputable def ProfiledRawJointRecurrentFiniteMemoryRightBoundaryData.owner
    (data : ProfiledRawJointRecurrentFiniteMemoryRightBoundaryData
      (Memory := Memory) A strategy) :
    ((data.receiver A strategy).1.memberController A false).Control :=
  data.2.1.2

noncomputable def ProfiledRawJointRecurrentFiniteMemoryLeftBoundaryData.receiver
    (data : ProfiledRawJointRecurrentFiniteMemoryLeftBoundaryData
      (Memory := Memory) A strategy) :
    ProfiledRawJointLeftPhysicalSiblingReceiver A :=
  data.2.1.1

noncomputable def ProfiledRawJointRecurrentFiniteMemoryLeftBoundaryData.owner
    (data : ProfiledRawJointRecurrentFiniteMemoryLeftBoundaryData
      (Memory := Memory) A strategy) :
    ((data.receiver A strategy).1.memberController A false).Control :=
  data.2.1.2

/-- A decoded right boundary plus the augmented coordinate and matching owner
of its dormant left receiver. -/
noncomputable abbrev
    ProfiledRawJointRecurrentFiniteMemoryRightPhaseLiveBoundaryData :=
  Sigma fun data :
      ProfiledRawJointRecurrentFiniteMemoryRightBoundaryData
        (Memory := Memory) A strategy ↦
    BankControl (Memory := Memory) A strategy ×
      (data.2.2.1.memberController A false).Control

noncomputable abbrev
    ProfiledRawJointRecurrentFiniteMemoryLeftPhaseLiveBoundaryData :=
  Sigma fun data :
      ProfiledRawJointRecurrentFiniteMemoryLeftBoundaryData
        (Memory := Memory) A strategy ↦
    BankControl (Memory := Memory) A strategy ×
      (data.2.2.1.memberController A false).Control

noncomputable instance :
    Fintype
      (ProfiledRawJointRecurrentFiniteMemoryRightPhaseLiveBoundaryData
        (Memory := Memory) A strategy) := by
  classical
  infer_instance

noncomputable instance :
    Fintype
      (ProfiledRawJointRecurrentFiniteMemoryLeftPhaseLiveBoundaryData
        (Memory := Memory) A strategy) := by
  classical
  infer_instance

/-! ## Endpoint state spaces -/

abbrev ProfiledRawJointRecurrentFiniteMemoryBoundaryBankCoordinates :=
  BankControl (Memory := Memory) A strategy ×
    BankControl (Memory := Memory) A strategy

abbrev ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryOneBase :=
  ProfiledRawJointRecurrentFiniteMemoryLeftToRightBridgeControl
      (Memory := Memory) A strategy ⊕
    ProfiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibrePending
      (Memory := Memory) A strategy

abbrev ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryTwoBase :=
  ProfiledRawJointRecurrentFiniteMemoryRightToLeftBridgeControl
      (Memory := Memory) A strategy ⊕
    ProfiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibrePending
      (Memory := Memory) A strategy

abbrev ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryOneControl :=
  ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryOneBase
      (Memory := Memory) A strategy ×
    ProfiledRawJointRecurrentFiniteMemoryBoundaryBankCoordinates
      (Memory := Memory) A strategy

abbrev ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryTwoControl :=
  ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryTwoBase
      (Memory := Memory) A strategy ×
    ProfiledRawJointRecurrentFiniteMemoryBoundaryBankCoordinates
      (Memory := Memory) A strategy

noncomputable instance :
    Fintype
      (ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryOneControl
        (Memory := Memory) A strategy) := by
  classical
  infer_instance

noncomputable instance :
    Fintype
      (ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryTwoControl
        (Memory := Memory) A strategy) := by
  classical
  infer_instance

/-! ## Fibre-aligned receiver templates -/

noncomputable def ProfiledRawJointRightOwnerFibreControl.finiteMemoryReceiverAt
    (control : ProfiledRawJointRightOwnerFibreControl A)
    (template : ProfiledRawJointRightPhysicalSiblingReceiver A) :
    ProfiledRawJointRightPhysicalSiblingReceiver A :=
  ⟨control.1, template.2.1, control.2.2, none⟩

noncomputable def ProfiledRawJointLeftOwnerFibreControl.finiteMemoryReceiverAt
    (control : ProfiledRawJointLeftOwnerFibreControl A)
    (template : ProfiledRawJointLeftPhysicalSiblingReceiver A) :
    ProfiledRawJointLeftPhysicalSiblingReceiver A :=
  ⟨control.1, template.2.1, control.2.2, none⟩

/-! ## Checked dependent constructors -/

private noncomputable def
    profiledRawJointRecurrentFiniteMemoryOwnerFibreMakeRight?
    (state : BankControl (Memory := Memory) A strategy)
    (rightOwner : ProfiledRawJointRightPhysicalSiblingExceptional A)
    (rightReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (leftState : BankControl (Memory := Memory) A strategy)
    (leftOwner : ProfiledRawJointLeftPhysicalSiblingExceptional A)
    (leftReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A) :
    Option
      (ProfiledRawJointRecurrentFiniteMemoryRightPhaseLiveBoundaryData
        (Memory := Memory) A strategy) := by
  classical
  rcases rightOwner with ⟨rightOwnerMove, rightOwnerControl⟩
  rcases rightReceiver with
    ⟨rightReceiverMove, rightRow, rightReceiverState, rightTarget⟩
  by_cases hright : rightOwnerMove = rightReceiverMove
  · subst rightReceiverMove
    let data :
        ProfiledRawJointRecurrentFiniteMemoryRightBoundaryData
          (Memory := Memory) A strategy :=
      (state,
        ⟨⟨rightOwnerMove, rightRow, rightReceiverState, rightTarget⟩,
          rightOwnerControl⟩,
        leftReceiver)
    rcases leftOwner with ⟨leftOwnerMove, leftOwnerControl⟩
    by_cases hleft : leftOwnerMove = leftReceiver.1
    · subst leftOwnerMove
      exact some ⟨data, leftState, leftOwnerControl⟩
    · exact none
  · exact none

private noncomputable def
    profiledRawJointRecurrentFiniteMemoryOwnerFibreMakeLeft?
    (state : BankControl (Memory := Memory) A strategy)
    (leftOwner : ProfiledRawJointLeftPhysicalSiblingExceptional A)
    (leftReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (rightState : BankControl (Memory := Memory) A strategy)
    (rightOwner : ProfiledRawJointRightPhysicalSiblingExceptional A)
    (rightReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A) :
    Option
      (ProfiledRawJointRecurrentFiniteMemoryLeftPhaseLiveBoundaryData
        (Memory := Memory) A strategy) := by
  classical
  rcases leftOwner with ⟨leftOwnerMove, leftOwnerControl⟩
  rcases leftReceiver with
    ⟨leftReceiverMove, leftRow, leftReceiverState, leftTarget⟩
  by_cases hleft : leftOwnerMove = leftReceiverMove
  · subst leftReceiverMove
    let data :
        ProfiledRawJointRecurrentFiniteMemoryLeftBoundaryData
          (Memory := Memory) A strategy :=
      (state,
        ⟨⟨leftOwnerMove, leftRow, leftReceiverState, leftTarget⟩,
          leftOwnerControl⟩,
        rightReceiver)
    rcases rightOwner with ⟨rightOwnerMove, rightOwnerControl⟩
    by_cases hright : rightOwnerMove = rightReceiver.1
    · subst rightOwnerMove
      exact some ⟨data, rightState, rightOwnerControl⟩
    · exact none
  · exact none

omit [Fintype Memory] [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledRawJointRecurrentFiniteMemoryOwnerFibreMakeRight?_states
    (state : BankControl (Memory := Memory) A strategy)
    (rightOwner : ProfiledRawJointRightPhysicalSiblingExceptional A)
    (rightReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (leftState : BankControl (Memory := Memory) A strategy)
    (leftOwner : ProfiledRawJointLeftPhysicalSiblingExceptional A)
    (leftReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (data :
      ProfiledRawJointRecurrentFiniteMemoryRightPhaseLiveBoundaryData
        (Memory := Memory) A strategy)
    (hmake :
      profiledRawJointRecurrentFiniteMemoryOwnerFibreMakeRight?
        (Memory := Memory) A strategy state rightOwner rightReceiver leftState
          leftOwner leftReceiver = some data) :
    data.1.1 = state ∧ data.2.1 = leftState := by
  classical
  rcases rightOwner with ⟨rightOwnerMove, rightOwnerControl⟩
  rcases rightReceiver with
    ⟨rightReceiverMove, rightRow, rightReceiverState, rightTarget⟩
  unfold profiledRawJointRecurrentFiniteMemoryOwnerFibreMakeRight? at hmake
  simp only [Sigma.casesOn, Prod.casesOn] at hmake
  split at hmake
  · subst rightReceiverMove
    rcases leftOwner with ⟨leftOwnerMove, leftOwnerControl⟩
    split at hmake
    · rename_i hleft
      change leftOwnerMove = leftReceiver.1 at hleft
      subst leftOwnerMove
      have heq := Option.some.inj hmake
      rw [← heq]
      exact ⟨rfl, rfl⟩
    · simp at hmake
  · simp at hmake

omit [Fintype Memory] [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledRawJointRecurrentFiniteMemoryOwnerFibreMakeLeft?_states
    (state : BankControl (Memory := Memory) A strategy)
    (leftOwner : ProfiledRawJointLeftPhysicalSiblingExceptional A)
    (leftReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (rightState : BankControl (Memory := Memory) A strategy)
    (rightOwner : ProfiledRawJointRightPhysicalSiblingExceptional A)
    (rightReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (data :
      ProfiledRawJointRecurrentFiniteMemoryLeftPhaseLiveBoundaryData
        (Memory := Memory) A strategy)
    (hmake :
      profiledRawJointRecurrentFiniteMemoryOwnerFibreMakeLeft?
        (Memory := Memory) A strategy state leftOwner leftReceiver rightState
          rightOwner rightReceiver = some data) :
    data.1.1 = state ∧ data.2.1 = rightState := by
  classical
  rcases leftOwner with ⟨leftOwnerMove, leftOwnerControl⟩
  rcases leftReceiver with
    ⟨leftReceiverMove, leftRow, leftReceiverState, leftTarget⟩
  unfold profiledRawJointRecurrentFiniteMemoryOwnerFibreMakeLeft? at hmake
  simp only [Sigma.casesOn, Prod.casesOn] at hmake
  split at hmake
  · subst leftReceiverMove
    rcases rightOwner with ⟨rightOwnerMove, rightOwnerControl⟩
    split at hmake
    · rename_i hright
      change rightOwnerMove = rightReceiver.1 at hright
      subst rightOwnerMove
      have heq := Option.some.inj hmake
      rw [← heq]
      exact ⟨rfl, rfl⟩
    · simp at hmake
  · simp at hmake

/-! ## Eight-shape endpoint decoder -/

noncomputable def
    profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?
    (one :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryOneControl
        (Memory := Memory) A strategy)
    (two :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryTwoControl
        (Memory := Memory) A strategy) :
    Option
      (ProfiledRawJointRecurrentFiniteMemoryRightPhaseLiveBoundaryData
        (Memory := Memory) A strategy) :=
  match one.1, two.1 with
  | .inl (.inr installed), .inl (.inl staged) =>
      if installed.1 = staged.1 then
        match staged.2.2 with
        | none => none
        | some packet =>
            match packet.successor.2.1.1.2.2 with
            | none => none
            | some move =>
                let leftReceiver :=
                  initialProfiledRawJointLeftPhysicalSiblingReceiver A move
                    .first
                profiledRawJointRecurrentFiniteMemoryOwnerFibreMakeRight?
                  (Memory := Memory) A strategy installed.1 installed.2.1
                    staged.2.1 packet.successor
                    ⟨move, (move.memberController A false).initial⟩ leftReceiver
      else none
  | .inl (.inr installed), .inr pendingTwo =>
      let rightReceiver :=
        profiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibreReceiver
          (Memory := Memory) A strategy pendingTwo
      let leftFibre := pendingTwo.2.1.1
      let leftReceiver :=
        leftFibre.finiteMemoryReceiverAt A installed.2.2
      if installed.1 = rightReceiver.1 then
        profiledRawJointRecurrentFiniteMemoryOwnerFibreMakeRight?
          (Memory := Memory) A strategy installed.1 installed.2.1
            rightReceiver.2 one.2.2
            (profiledRawJointLeftOwnerFibreExceptional A leftFibre)
            leftReceiver
      else none
  | .inr pendingOne, .inr pendingTwo =>
      if pendingOne.1 || !pendingTwo.1 then
        let rightTemplate :=
          (profiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibreReceiver
            (Memory := Memory) A strategy pendingTwo).2
        let leftTemplate :=
          (profiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibreReceiver
            (Memory := Memory) A strategy pendingOne).2
        let rightFibre := pendingOne.2.1.1
        let leftFibre := pendingTwo.2.1.1
        profiledRawJointRecurrentFiniteMemoryOwnerFibreMakeRight?
          (Memory := Memory) A strategy
          (profiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibreReceiver
            (Memory := Memory) A strategy pendingTwo).1
          (profiledRawJointRightOwnerFibreExceptional A rightFibre)
          (rightFibre.finiteMemoryReceiverAt A rightTemplate)
          (profiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibreReceiver
            (Memory := Memory) A strategy pendingOne).1
          (profiledRawJointLeftOwnerFibreExceptional A leftFibre)
          (leftFibre.finiteMemoryReceiverAt A leftTemplate)
      else none
  | .inr pendingOne, .inl (.inl staged) =>
      match staged.2.2 with
      | none => none
      | some packet =>
          match packet.successor.2.1.1.2.2 with
          | none => none
          | some move =>
              let rightFibre := pendingOne.2.1.1
              let leftReceiver :=
                initialProfiledRawJointLeftPhysicalSiblingReceiver A move
                  .first
              profiledRawJointRecurrentFiniteMemoryOwnerFibreMakeRight?
                (Memory := Memory) A strategy staged.1
                (profiledRawJointRightOwnerFibreExceptional A rightFibre)
                (rightFibre.finiteMemoryReceiverAt A staged.2.1)
                packet.successor
                ⟨move, (move.memberController A false).initial⟩ leftReceiver
  | _, _ => none

noncomputable def
    profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData?
    (one :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryOneControl
        (Memory := Memory) A strategy)
    (two :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryTwoControl
        (Memory := Memory) A strategy) :
    Option
      (ProfiledRawJointRecurrentFiniteMemoryLeftPhaseLiveBoundaryData
        (Memory := Memory) A strategy) :=
  match one.1, two.1 with
  | .inl (.inl staged), .inl (.inr installed) =>
      if installed.1 = staged.1 then
        match staged.2.2 with
        | none => none
        | some packet =>
            match packet.successor.2.1.1.2.1 with
            | none => none
            | some move =>
                let rightReceiver :=
                  initialProfiledRawJointRightPhysicalSiblingReceiver A move
                    .first
                profiledRawJointRecurrentFiniteMemoryOwnerFibreMakeLeft?
                  (Memory := Memory) A strategy installed.1 installed.2.1
                    staged.2.1 packet.successor
                    ⟨move, (move.memberController A false).initial⟩
                    rightReceiver
      else none
  | .inr pendingOne, .inl (.inr installed) =>
      let leftReceiver :=
        profiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibreReceiver
          (Memory := Memory) A strategy pendingOne
      let rightFibre := pendingOne.2.1.1
      let rightReceiver :=
        rightFibre.finiteMemoryReceiverAt A installed.2.2
      if installed.1 = leftReceiver.1 then
        profiledRawJointRecurrentFiniteMemoryOwnerFibreMakeLeft?
          (Memory := Memory) A strategy installed.1 installed.2.1
            leftReceiver.2 two.2.1
            (profiledRawJointRightOwnerFibreExceptional A rightFibre)
            rightReceiver
      else none
  | .inr pendingOne, .inr pendingTwo =>
      if !pendingOne.1 && pendingTwo.1 then
        let leftTemplate :=
          (profiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibreReceiver
            (Memory := Memory) A strategy pendingOne).2
        let rightTemplate :=
          (profiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibreReceiver
            (Memory := Memory) A strategy pendingTwo).2
        let rightFibre := pendingOne.2.1.1
        let leftFibre := pendingTwo.2.1.1
        profiledRawJointRecurrentFiniteMemoryOwnerFibreMakeLeft?
          (Memory := Memory) A strategy
          (profiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibreReceiver
            (Memory := Memory) A strategy pendingOne).1
          (profiledRawJointLeftOwnerFibreExceptional A leftFibre)
          (leftFibre.finiteMemoryReceiverAt A leftTemplate)
          (profiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibreReceiver
            (Memory := Memory) A strategy pendingTwo).1
          (profiledRawJointRightOwnerFibreExceptional A rightFibre)
          (rightFibre.finiteMemoryReceiverAt A rightTemplate)
      else none
  | .inl (.inl staged), .inr pendingTwo =>
      if pendingTwo.1 then
        match staged.2.2 with
        | none => none
        | some packet =>
            match packet.successor.2.1.1.2.1 with
            | none => none
            | some move =>
                let leftFibre := pendingTwo.2.1.1
                let rightReceiver :=
                  initialProfiledRawJointRightPhysicalSiblingReceiver A move
                    .first
                profiledRawJointRecurrentFiniteMemoryOwnerFibreMakeLeft?
                  (Memory := Memory) A strategy staged.1
                  (profiledRawJointLeftOwnerFibreExceptional A leftFibre)
                  (leftFibre.finiteMemoryReceiverAt A staged.2.1)
                  packet.successor
                  ⟨move, (move.memberController A false).initial⟩ rightReceiver
      else none
  | _, _ => none

/-! ## Decoder disjointness and completeness diagnostics -/

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype Memory] in
/-- The right and left deferred/deferred orientation tags are disjoint. -/
@[simp] theorem
    profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData?_rightTags
    (pendingOne :
      ProfiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibrePending
        (Memory := Memory) A strategy)
    (pendingTwo :
      ProfiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibrePending
        (Memory := Memory) A strategy)
    (rightStateOne leftStateOne rightStateTwo leftStateTwo :
      BankControl (Memory := Memory) A strategy)
    (hone : pendingOne.1 = true)
    (htwo : pendingTwo.1 = false) :
    profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData?
      (Memory := Memory) A strategy
      ((.inr pendingOne, rightStateOne, leftStateOne))
      ((.inr pendingTwo, rightStateTwo, leftStateTwo)) = none := by
  simp [profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData?,
    hone, htwo]

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype Memory] in
/-- Mirrored tag disjointness. -/
@[simp] theorem
    profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?_leftTags
    (pendingOne :
      ProfiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibrePending
        (Memory := Memory) A strategy)
    (pendingTwo :
      ProfiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibrePending
        (Memory := Memory) A strategy)
    (rightStateOne leftStateOne rightStateTwo leftStateTwo :
      BankControl (Memory := Memory) A strategy)
    (hone : pendingOne.1 = false)
    (htwo : pendingTwo.1 = true) :
    profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?
      (Memory := Memory) A strategy
      ((.inr pendingOne, rightStateOne, leftStateOne))
      ((.inr pendingTwo, rightStateTwo, leftStateTwo)) = none := by
  simp [profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?,
    hone, htwo]

/-- Explicitly records the runtime obligation generated by the option-valued
decoder.  A reachable control pair must inhabit one of these two alternatives;
otherwise the total kernel can only take its malformed-state fallback. -/
def ProfiledRawJointRecurrentFiniteMemoryOwnerFibreDecodes
    (one :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryOneControl
        (Memory := Memory) A strategy)
    (two :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryTwoControl
        (Memory := Memory) A strategy) : Prop :=
  (∃ data,
      profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?
        (Memory := Memory) A strategy one two = some data) ∨
    (∃ data,
      profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData?
        (Memory := Memory) A strategy one two = some data)

section
omit [Fintype Memory] [Inhabited Out₁] [Inhabited Out₂]

/-- The installed-right/staged-right entry shape decodes whenever the packet
successor contains its advertised fresh left move. -/
theorem
    profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?_entry
    (rightState : BankControl (Memory := Memory) A strategy)
    (rightReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (rightOwner : (rightReceiver.1.memberController A false).Control)
    (leftTemplate : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (packet :
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryBankResolvedTarget
        (Memory := Memory) A strategy)
    (leftMove : ProfiledRawJointLeftPhysicalSiblingMove A)
    (hmove : packet.successor.2.1.1.2.2 = some leftMove) :
    ProfiledRawJointRecurrentFiniteMemoryOwnerFibreDecodes
      (Memory := Memory) A strategy
      ((.inl
          (.inr
            (rightState, ⟨rightReceiver.1, rightOwner⟩, leftTemplate)),
        (rightState, packet.successor)))
      ((.inl (.inl (rightState, rightReceiver, some packet)),
        (rightState, packet.successor))) := by
  left
  let leftReceiver :=
    initialProfiledRawJointLeftPhysicalSiblingReceiver A leftMove .first
  let data :
      ProfiledRawJointRecurrentFiniteMemoryRightBoundaryData
        (Memory := Memory) A strategy :=
    (rightState, ⟨rightReceiver, rightOwner⟩, leftReceiver)
  refine
    ⟨⟨data, packet.successor,
        (leftMove.memberController A false).initial⟩, ?_⟩
  simp [profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?,
    profiledRawJointRecurrentFiniteMemoryOwnerFibreMakeRight?, hmove,
    initialProfiledRawJointLeftPhysicalSiblingReceiver, leftReceiver, data]

/-- Mirrored installed-left/staged-left entry decoder law. -/
theorem
    profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData?_entry
    (leftState : BankControl (Memory := Memory) A strategy)
    (leftReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (leftOwner : (leftReceiver.1.memberController A false).Control)
    (rightTemplate : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (packet :
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryBankResolvedTarget
        (Memory := Memory) A strategy)
    (rightMove : ProfiledRawJointRightPhysicalSiblingMove A)
    (hmove : packet.successor.2.1.1.2.1 = some rightMove) :
    ProfiledRawJointRecurrentFiniteMemoryOwnerFibreDecodes
      (Memory := Memory) A strategy
      ((.inl (.inl (leftState, leftReceiver, some packet)),
        (packet.successor, leftState)))
      ((.inl
          (.inr
            (leftState, ⟨leftReceiver.1, leftOwner⟩, rightTemplate)),
        (packet.successor, leftState))) := by
  right
  let rightReceiver :=
    initialProfiledRawJointRightPhysicalSiblingReceiver A rightMove .first
  let data :
      ProfiledRawJointRecurrentFiniteMemoryLeftBoundaryData
        (Memory := Memory) A strategy :=
    (leftState, ⟨leftReceiver, leftOwner⟩, rightReceiver)
  refine
    ⟨⟨data, packet.successor,
        (rightMove.memberController A false).initial⟩, ?_⟩
  simp [profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData?,
    profiledRawJointRecurrentFiniteMemoryOwnerFibreMakeLeft?, hmove,
    initialProfiledRawJointRightPhysicalSiblingReceiver, rightReceiver, data]

/-- Exact decoded phase behind the right-oriented entry existence theorem. -/
@[simp] theorem
    profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?_entry_exact
    (rightState : BankControl (Memory := Memory) A strategy)
    (rightReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (rightOwner : (rightReceiver.1.memberController A false).Control)
    (leftTemplate : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (packet :
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryBankResolvedTarget
        (Memory := Memory) A strategy)
    (leftMove : ProfiledRawJointLeftPhysicalSiblingMove A)
    (hmove : packet.successor.2.1.1.2.2 = some leftMove) :
    profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?
        (Memory := Memory) A strategy
        ((.inl
            (.inr
              (rightState, ⟨rightReceiver.1, rightOwner⟩, leftTemplate)),
          (rightState, packet.successor)))
        ((.inl (.inl (rightState, rightReceiver, some packet)),
          (rightState, packet.successor))) =
      some
        ⟨(rightState, ⟨rightReceiver, rightOwner⟩,
            initialProfiledRawJointLeftPhysicalSiblingReceiver A leftMove
              .first),
          packet.successor, (leftMove.memberController A false).initial⟩ := by
  let leftReceiver :=
    initialProfiledRawJointLeftPhysicalSiblingReceiver A leftMove .first
  let data :
      ProfiledRawJointRecurrentFiniteMemoryRightBoundaryData
        (Memory := Memory) A strategy :=
    (rightState, ⟨rightReceiver, rightOwner⟩, leftReceiver)
  simp [profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?,
    profiledRawJointRecurrentFiniteMemoryOwnerFibreMakeRight?, hmove,
    initialProfiledRawJointLeftPhysicalSiblingReceiver, leftReceiver, data]

/-- Exact decoded phase behind the left-oriented entry existence theorem. -/
@[simp] theorem
    profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData?_entry_exact
    (leftState : BankControl (Memory := Memory) A strategy)
    (leftReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (leftOwner : (leftReceiver.1.memberController A false).Control)
    (rightTemplate : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (packet :
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryBankResolvedTarget
        (Memory := Memory) A strategy)
    (rightMove : ProfiledRawJointRightPhysicalSiblingMove A)
    (hmove : packet.successor.2.1.1.2.1 = some rightMove) :
    profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData?
        (Memory := Memory) A strategy
        ((.inl (.inl (leftState, leftReceiver, some packet)),
          (packet.successor, leftState)))
        ((.inl
            (.inr
              (leftState, ⟨leftReceiver.1, leftOwner⟩, rightTemplate)),
          (packet.successor, leftState))) =
      some
        ⟨(leftState, ⟨leftReceiver, leftOwner⟩,
            initialProfiledRawJointRightPhysicalSiblingReceiver A rightMove
              .first),
          packet.successor, (rightMove.memberController A false).initial⟩ := by
  let rightReceiver :=
    initialProfiledRawJointRightPhysicalSiblingReceiver A rightMove .first
  let data :
      ProfiledRawJointRecurrentFiniteMemoryLeftBoundaryData
        (Memory := Memory) A strategy :=
    (leftState, ⟨leftReceiver, leftOwner⟩, rightReceiver)
  simp [profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData?,
    profiledRawJointRecurrentFiniteMemoryOwnerFibreMakeLeft?, hmove,
    initialProfiledRawJointRightPhysicalSiblingReceiver, rightReceiver, data]

/-- Coordinate-general installed/staged decoder equation. -/
@[simp] theorem
    profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?_installedStaged
    (rightState : BankControl (Memory := Memory) A strategy)
    (rightReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (rightOwner : (rightReceiver.1.memberController A false).Control)
    (leftTemplate : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (packet :
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryBankResolvedTarget
        (Memory := Memory) A strategy)
    (leftMove : ProfiledRawJointLeftPhysicalSiblingMove A)
    (hleftMove : packet.successor.2.1.1.2.2 = some leftMove)
    (oneCoordinates twoCoordinates :
      ProfiledRawJointRecurrentFiniteMemoryBoundaryBankCoordinates
        (Memory := Memory) A strategy) :
    profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?
        (Memory := Memory) A strategy
        (.inl
          (.inr
            (rightState, ⟨rightReceiver.1, rightOwner⟩, leftTemplate)),
          oneCoordinates)
        (.inl (.inl (rightState, rightReceiver, some packet)),
          twoCoordinates) =
      some
        ⟨(rightState, ⟨rightReceiver, rightOwner⟩,
            initialProfiledRawJointLeftPhysicalSiblingReceiver A leftMove
              .first),
          packet.successor, (leftMove.memberController A false).initial⟩ := by
  rcases rightReceiver with
    ⟨rightMove, rightRow, rightReceiverState, rightTarget⟩
  simp [profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?,
    profiledRawJointRecurrentFiniteMemoryOwnerFibreMakeRight?, hleftMove,
    initialProfiledRawJointLeftPhysicalSiblingReceiver]

/-- Coordinate-general staged/installed decoder equation. -/
@[simp] theorem
    profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData?_stagedInstalled
    (leftState : BankControl (Memory := Memory) A strategy)
    (leftReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (leftOwner : (leftReceiver.1.memberController A false).Control)
    (rightTemplate : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (packet :
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryBankResolvedTarget
        (Memory := Memory) A strategy)
    (rightMove : ProfiledRawJointRightPhysicalSiblingMove A)
    (hrightMove : packet.successor.2.1.1.2.1 = some rightMove)
    (oneCoordinates twoCoordinates :
      ProfiledRawJointRecurrentFiniteMemoryBoundaryBankCoordinates
        (Memory := Memory) A strategy) :
    profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData?
        (Memory := Memory) A strategy
        (.inl (.inl (leftState, leftReceiver, some packet)), oneCoordinates)
        (.inl
          (.inr
            (leftState, ⟨leftReceiver.1, leftOwner⟩, rightTemplate)),
          twoCoordinates) =
      some
        ⟨(leftState, ⟨leftReceiver, leftOwner⟩,
            initialProfiledRawJointRightPhysicalSiblingReceiver A rightMove
              .first),
          packet.successor, (rightMove.memberController A false).initial⟩ := by
  rcases leftReceiver with
    ⟨leftMove, leftRow, leftReceiverState, leftTarget⟩
  simp [profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData?,
    profiledRawJointRecurrentFiniteMemoryOwnerFibreMakeLeft?, hrightMove,
    initialProfiledRawJointRightPhysicalSiblingReceiver]

/-- Inversion of successful finite installed/staged decoding. -/
theorem
    profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?_installedStaged_inv
    (installed :
      ProfiledRawJointRecurrentFiniteMemoryLeftToRightInstalledOwner
        (Memory := Memory) A strategy)
    (staged :
      ProfiledRawJointRecurrentFiniteMemoryRightToLeftStagedReceiver
        (Memory := Memory) A strategy)
    (oneCoordinates twoCoordinates :
      ProfiledRawJointRecurrentFiniteMemoryBoundaryBankCoordinates
        (Memory := Memory) A strategy)
    (phaseData :
      ProfiledRawJointRecurrentFiniteMemoryRightPhaseLiveBoundaryData
        (Memory := Memory) A strategy)
    (hdecode :
      profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?
          (Memory := Memory) A strategy
          (.inl (.inr installed), oneCoordinates)
          (.inl (.inl staged), twoCoordinates) = some phaseData) :
    ∃ (rightState : BankControl (Memory := Memory) A strategy)
      (rightReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
      (rightOwner : (rightReceiver.1.memberController A false).Control)
      (leftTemplate : ProfiledRawJointLeftPhysicalSiblingReceiver A)
      (packet :
        ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryBankResolvedTarget
          (Memory := Memory) A strategy)
      (leftMove : ProfiledRawJointLeftPhysicalSiblingMove A),
      installed =
          (rightState, ⟨rightReceiver.1, rightOwner⟩, leftTemplate) ∧
        staged = (rightState, rightReceiver, some packet) ∧
        packet.successor.2.1.1.2.2 = some leftMove ∧
        phaseData =
          ⟨(rightState, ⟨rightReceiver, rightOwner⟩,
              initialProfiledRawJointLeftPhysicalSiblingReceiver A leftMove
                .first),
            packet.successor,
            (leftMove.memberController A false).initial⟩ := by
  rcases installed with ⟨rightState, rightExceptional, leftTemplate⟩
  rcases rightExceptional with ⟨rightMove, rightOwner⟩
  rcases staged with ⟨stagedState, rightReceiver, packet⟩
  rcases rightReceiver with
    ⟨receiverMove, rightRow, rightReceiverState, rightTarget⟩
  cases packet with
  | none =>
      simp [profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?]
        at hdecode
  | some packet =>
      cases hleftMove : packet.successor.2.1.1.2.2 with
      | none =>
          simp [
            profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?,
            hleftMove] at hdecode
      | some leftMove =>
          simp [
            profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?,
            profiledRawJointRecurrentFiniteMemoryOwnerFibreMakeRight?,
            hleftMove] at hdecode
          rcases hdecode with ⟨hstate, ⟨hreceiverMove, hdecode⟩⟩
          subst stagedState
          subst receiverMove
          simp [initialProfiledRawJointLeftPhysicalSiblingReceiver] at hdecode
          subst phaseData
          exact ⟨rightState,
            ⟨rightMove, rightRow, rightReceiverState, rightTarget⟩,
            rightOwner, leftTemplate, packet, leftMove, rfl, rfl,
            hleftMove, rfl⟩

/-- Mirrored inversion of successful finite staged/installed decoding. -/
theorem
    profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData?_stagedInstalled_inv
    (staged :
      ProfiledRawJointRecurrentFiniteMemoryLeftToRightStagedReceiver
        (Memory := Memory) A strategy)
    (installed :
      ProfiledRawJointRecurrentFiniteMemoryRightToLeftInstalledOwner
        (Memory := Memory) A strategy)
    (oneCoordinates twoCoordinates :
      ProfiledRawJointRecurrentFiniteMemoryBoundaryBankCoordinates
        (Memory := Memory) A strategy)
    (phaseData :
      ProfiledRawJointRecurrentFiniteMemoryLeftPhaseLiveBoundaryData
        (Memory := Memory) A strategy)
    (hdecode :
      profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData?
          (Memory := Memory) A strategy
          (.inl (.inl staged), oneCoordinates)
          (.inl (.inr installed), twoCoordinates) = some phaseData) :
    ∃ (leftState : BankControl (Memory := Memory) A strategy)
      (leftReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
      (leftOwner : (leftReceiver.1.memberController A false).Control)
      (rightTemplate : ProfiledRawJointRightPhysicalSiblingReceiver A)
      (packet :
        ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryBankResolvedTarget
          (Memory := Memory) A strategy)
      (rightMove : ProfiledRawJointRightPhysicalSiblingMove A),
      staged = (leftState, leftReceiver, some packet) ∧
        installed =
          (leftState, ⟨leftReceiver.1, leftOwner⟩, rightTemplate) ∧
        packet.successor.2.1.1.2.1 = some rightMove ∧
        phaseData =
          ⟨(leftState, ⟨leftReceiver, leftOwner⟩,
              initialProfiledRawJointRightPhysicalSiblingReceiver A rightMove
                .first),
            packet.successor,
            (rightMove.memberController A false).initial⟩ := by
  rcases staged with ⟨stagedState, leftReceiver, packet⟩
  rcases leftReceiver with
    ⟨receiverMove, leftRow, leftReceiverState, leftTarget⟩
  rcases installed with ⟨leftState, leftExceptional, rightTemplate⟩
  rcases leftExceptional with ⟨leftMove, leftOwner⟩
  cases packet with
  | none =>
      simp [profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData?]
        at hdecode
  | some packet =>
      cases hrightMove : packet.successor.2.1.1.2.1 with
      | none =>
          simp [
            profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData?,
            hrightMove] at hdecode
      | some rightMove =>
          simp [
            profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData?,
            profiledRawJointRecurrentFiniteMemoryOwnerFibreMakeLeft?,
            hrightMove] at hdecode
          rcases hdecode with ⟨hstate, ⟨hreceiverMove, hdecode⟩⟩
          subst stagedState
          subst receiverMove
          simp [initialProfiledRawJointRightPhysicalSiblingReceiver] at hdecode
          subst phaseData
          exact ⟨leftState,
            ⟨leftMove, leftRow, leftReceiverState, leftTarget⟩,
            leftOwner, rightTemplate, packet, rightMove, rfl, rfl,
            hrightMove, rfl⟩

end

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype Memory] in
/-- The immediate right-oriented pending/pending reversal shape really
decodes.  In particular, the option-valued decoder is not empty on this
runtime shape. -/
theorem
    profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?_pendingPending
    (rightFibre : ProfiledRawJointRightOwnerFibreControl A)
    (oldLeft newLeft :
      ProfiledRawJointRecurrentFiniteMemoryBankedLeftReceiver
        (Memory := Memory) A strategy)
    (leftFibre : ProfiledRawJointLeftOwnerFibreControl A)
    (oldRight newRight :
      ProfiledRawJointRecurrentFiniteMemoryBankedRightReceiver
        (Memory := Memory) A strategy)
    (coordinatesOne coordinatesTwo :
      ProfiledRawJointRecurrentFiniteMemoryBoundaryBankCoordinates
        (Memory := Memory) A strategy) :
    ∃ data,
      profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?
        (Memory := Memory) A strategy
        ((.inr (true, (rightFibre, ⟨oldLeft, newLeft⟩), ()),
          coordinatesOne))
        ((.inr (false, (leftFibre, ⟨oldRight, newRight⟩), ()),
          coordinatesTwo)) = some data := by
  let rightReceiver := rightFibre.finiteMemoryReceiverAt A oldRight.2
  let leftReceiver := leftFibre.finiteMemoryReceiverAt A newLeft.2
  let data :
      ProfiledRawJointRecurrentFiniteMemoryRightBoundaryData
        (Memory := Memory) A strategy :=
    (oldRight.1, ⟨rightReceiver, rightFibre.2.1⟩, leftReceiver)
  refine ⟨⟨data, newLeft.1, leftFibre.2.1⟩, ?_⟩
  simp [
    profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?,
    profiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibreReceiver,
    profiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibreReceiver,
    profiledRawJointRecurrentFiniteMemoryOwnerFibreMakeRight?,
    ProfiledRawJointRightOwnerFibreControl.finiteMemoryReceiverAt,
    ProfiledRawJointLeftOwnerFibreControl.finiteMemoryReceiverAt,
    profiledRawJointRightOwnerFibreExceptional,
    profiledRawJointLeftOwnerFibreExceptional, rightReceiver, leftReceiver,
    data]

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype Memory] in
/-- Mirrored nonempty pending/pending decoder shape. -/
theorem
    profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData?_pendingPending
    (rightFibre : ProfiledRawJointRightOwnerFibreControl A)
    (oldLeft newLeft :
      ProfiledRawJointRecurrentFiniteMemoryBankedLeftReceiver
        (Memory := Memory) A strategy)
    (leftFibre : ProfiledRawJointLeftOwnerFibreControl A)
    (oldRight newRight :
      ProfiledRawJointRecurrentFiniteMemoryBankedRightReceiver
        (Memory := Memory) A strategy)
    (coordinatesOne coordinatesTwo :
      ProfiledRawJointRecurrentFiniteMemoryBoundaryBankCoordinates
        (Memory := Memory) A strategy) :
    ∃ data,
      profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData?
        (Memory := Memory) A strategy
        ((.inr (false, (rightFibre, ⟨oldLeft, newLeft⟩), ()),
          coordinatesOne))
        ((.inr (true, (leftFibre, ⟨oldRight, newRight⟩), ()),
          coordinatesTwo)) = some data := by
  let leftReceiver := leftFibre.finiteMemoryReceiverAt A oldLeft.2
  let rightReceiver := rightFibre.finiteMemoryReceiverAt A newRight.2
  let data :
      ProfiledRawJointRecurrentFiniteMemoryLeftBoundaryData
        (Memory := Memory) A strategy :=
    (oldLeft.1, ⟨leftReceiver, leftFibre.2.1⟩, rightReceiver)
  refine ⟨⟨data, newRight.1, rightFibre.2.1⟩, ?_⟩
  simp [
    profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData?,
    profiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibreReceiver,
    profiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibreReceiver,
    profiledRawJointRecurrentFiniteMemoryOwnerFibreMakeLeft?,
    ProfiledRawJointRightOwnerFibreControl.finiteMemoryReceiverAt,
    ProfiledRawJointLeftOwnerFibreControl.finiteMemoryReceiverAt,
    profiledRawJointRightOwnerFibreExceptional,
    profiledRawJointLeftOwnerFibreExceptional, leftReceiver, rightReceiver,
    data]

section
omit [Fintype Memory] [Inhabited Out₁] [Inhabited Out₂]

/-- Exact right-oriented decoder equation for the deferred/deferred shape.
The member bits select the right fibre's old-left arm and the left fibre's
new-right arm. -/
@[simp] theorem
    profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?_fibreFibre
    (rightState leftState : BankControl (Memory := Memory) A strategy)
    (rightTemplate : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (leftTemplate : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (rightFibre : ProfiledRawJointRightOwnerFibreControl A)
    (leftFibre : ProfiledRawJointLeftOwnerFibreControl A)
    (oldLeft :
      ProfiledRawJointRecurrentFiniteMemoryBankedLeftReceiver
        (Memory := Memory) A strategy)
    (newRight :
      ProfiledRawJointRecurrentFiniteMemoryBankedRightReceiver
        (Memory := Memory) A strategy)
    (oneCoordinates twoCoordinates :
      ProfiledRawJointRecurrentFiniteMemoryBoundaryBankCoordinates
        (Memory := Memory) A strategy) :
    let pendingOne :
        ProfiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibrePending
          (Memory := Memory) A strategy :=
      (true, (rightFibre, ⟨oldLeft, (leftState, leftTemplate)⟩), ())
    let pendingTwo :
        ProfiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibrePending
          (Memory := Memory) A strategy :=
      (false, (leftFibre, ⟨(rightState, rightTemplate), newRight⟩), ())
    profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?
        (Memory := Memory) A strategy
        (.inr pendingOne, oneCoordinates)
        (.inr pendingTwo, twoCoordinates) =
      some
        ⟨(rightState,
            ⟨rightFibre.finiteMemoryReceiverAt A rightTemplate,
              rightFibre.2.1⟩,
            leftFibre.finiteMemoryReceiverAt A leftTemplate),
          leftState, leftFibre.2.1⟩ := by
  rcases rightTemplate with
    ⟨rightMove, rightRow, rightReceiverState, rightTarget⟩
  rcases leftTemplate with
    ⟨leftMove, leftRow, leftReceiverState, leftTarget⟩
  rcases rightFibre with ⟨rightFibreMove, rightOwner, rightMonitor⟩
  rcases leftFibre with ⟨leftFibreMove, leftOwner, leftMonitor⟩
  simp [profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?,
    profiledRawJointRecurrentFiniteMemoryOwnerFibreMakeRight?,
    profiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibreReceiver,
    profiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibreReceiver,
    ProfiledRawJointRightOwnerFibreControl.finiteMemoryReceiverAt,
    ProfiledRawJointLeftOwnerFibreControl.finiteMemoryReceiverAt,
    profiledRawJointRightOwnerFibreExceptional,
    profiledRawJointLeftOwnerFibreExceptional]

/-- Mirrored exact deferred/deferred decoder equation. -/
@[simp] theorem
    profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData?_fibreFibre
    (rightState leftState : BankControl (Memory := Memory) A strategy)
    (rightTemplate : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (leftTemplate : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (rightFibre : ProfiledRawJointRightOwnerFibreControl A)
    (leftFibre : ProfiledRawJointLeftOwnerFibreControl A)
    (oldLeft :
      ProfiledRawJointRecurrentFiniteMemoryBankedLeftReceiver
        (Memory := Memory) A strategy)
    (newRight :
      ProfiledRawJointRecurrentFiniteMemoryBankedRightReceiver
        (Memory := Memory) A strategy)
    (oneCoordinates twoCoordinates :
      ProfiledRawJointRecurrentFiniteMemoryBoundaryBankCoordinates
        (Memory := Memory) A strategy) :
    let pendingOne :
        ProfiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibrePending
          (Memory := Memory) A strategy :=
      (false, (rightFibre, ⟨(leftState, leftTemplate), oldLeft⟩), ())
    let pendingTwo :
        ProfiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibrePending
          (Memory := Memory) A strategy :=
      (true, (leftFibre, ⟨newRight, (rightState, rightTemplate)⟩), ())
    profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData?
        (Memory := Memory) A strategy
        (.inr pendingOne, oneCoordinates)
        (.inr pendingTwo, twoCoordinates) =
      some
        ⟨(leftState,
            ⟨leftFibre.finiteMemoryReceiverAt A leftTemplate,
              leftFibre.2.1⟩,
            rightFibre.finiteMemoryReceiverAt A rightTemplate),
          rightState, rightFibre.2.1⟩ := by
  rcases rightTemplate with
    ⟨rightMove, rightRow, rightReceiverState, rightTarget⟩
  rcases leftTemplate with
    ⟨leftMove, leftRow, leftReceiverState, leftTarget⟩
  rcases rightFibre with ⟨rightFibreMove, rightOwner, rightMonitor⟩
  rcases leftFibre with ⟨leftFibreMove, leftOwner, leftMonitor⟩
  simp [profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData?,
    profiledRawJointRecurrentFiniteMemoryOwnerFibreMakeLeft?,
    profiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibreReceiver,
    profiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibreReceiver,
    ProfiledRawJointRightOwnerFibreControl.finiteMemoryReceiverAt,
    ProfiledRawJointLeftOwnerFibreControl.finiteMemoryReceiverAt,
    profiledRawJointRightOwnerFibreExceptional,
    profiledRawJointLeftOwnerFibreExceptional]

/-- When both delivered fibres select their open arms, the right-priority
decoder assigns the equal-bit state `(false,false)` to the right orientation.
The unused arms may carry different augmented bank states. -/
@[simp] theorem
    profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?_openOpen
    (rightState leftState : BankControl (Memory := Memory) A strategy)
    (rightTemplate : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (leftTemplate : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (rightFibre : ProfiledRawJointRightOwnerFibreControl A)
    (leftFibre : ProfiledRawJointLeftOwnerFibreControl A)
    (newLeft :
      ProfiledRawJointRecurrentFiniteMemoryBankedLeftReceiver
        (Memory := Memory) A strategy)
    (newRight :
      ProfiledRawJointRecurrentFiniteMemoryBankedRightReceiver
        (Memory := Memory) A strategy)
    (oneCoordinates twoCoordinates :
      ProfiledRawJointRecurrentFiniteMemoryBoundaryBankCoordinates
        (Memory := Memory) A strategy) :
    let pendingOne :
        ProfiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibrePending
          (Memory := Memory) A strategy :=
      (false, (rightFibre, ⟨(leftState, leftTemplate), newLeft⟩), ())
    let pendingTwo :
        ProfiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibrePending
          (Memory := Memory) A strategy :=
      (false, (leftFibre, ⟨(rightState, rightTemplate), newRight⟩), ())
    profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?
        (Memory := Memory) A strategy
        (.inr pendingOne, oneCoordinates)
        (.inr pendingTwo, twoCoordinates) =
      some
        ⟨(rightState,
            ⟨rightFibre.finiteMemoryReceiverAt A rightTemplate,
              rightFibre.2.1⟩,
            leftFibre.finiteMemoryReceiverAt A leftTemplate),
          leftState, leftFibre.2.1⟩ := by
  rcases rightTemplate with
    ⟨rightMove, rightRow, rightReceiverState, rightTarget⟩
  rcases leftTemplate with
    ⟨leftMove, leftRow, leftReceiverState, leftTarget⟩
  rcases rightFibre with ⟨rightFibreMove, rightOwner, rightMonitor⟩
  rcases leftFibre with ⟨leftFibreMove, leftOwner, leftMonitor⟩
  simp [profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?,
    profiledRawJointRecurrentFiniteMemoryOwnerFibreMakeRight?,
    profiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibreReceiver,
    profiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibreReceiver,
    ProfiledRawJointRightOwnerFibreControl.finiteMemoryReceiverAt,
    ProfiledRawJointLeftOwnerFibreControl.finiteMemoryReceiverAt,
    profiledRawJointRightOwnerFibreExceptional,
    profiledRawJointLeftOwnerFibreExceptional]

/-- The right-priority decoder also assigns the equal-bit state `(true,true)`
to the right orientation.  This is the closed-arm counterpart of the open
equal-bit equation. -/
@[simp] theorem
    profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?_closedClosed
    (rightState leftState : BankControl (Memory := Memory) A strategy)
    (rightTemplate : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (leftTemplate : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (rightFibre : ProfiledRawJointRightOwnerFibreControl A)
    (leftFibre : ProfiledRawJointLeftOwnerFibreControl A)
    (oldLeft :
      ProfiledRawJointRecurrentFiniteMemoryBankedLeftReceiver
        (Memory := Memory) A strategy)
    (oldRight :
      ProfiledRawJointRecurrentFiniteMemoryBankedRightReceiver
        (Memory := Memory) A strategy)
    (oneCoordinates twoCoordinates :
      ProfiledRawJointRecurrentFiniteMemoryBoundaryBankCoordinates
        (Memory := Memory) A strategy) :
    let pendingOne :
        ProfiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibrePending
          (Memory := Memory) A strategy :=
      (true, (rightFibre, ⟨oldLeft, (leftState, leftTemplate)⟩), ())
    let pendingTwo :
        ProfiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibrePending
          (Memory := Memory) A strategy :=
      (true, (leftFibre, ⟨oldRight, (rightState, rightTemplate)⟩), ())
    profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?
        (Memory := Memory) A strategy
        (.inr pendingOne, oneCoordinates)
        (.inr pendingTwo, twoCoordinates) =
      some
        ⟨(rightState,
            ⟨rightFibre.finiteMemoryReceiverAt A rightTemplate,
              rightFibre.2.1⟩,
            leftFibre.finiteMemoryReceiverAt A leftTemplate),
          leftState, leftFibre.2.1⟩ := by
  rcases rightTemplate with
    ⟨rightMove, rightRow, rightReceiverState, rightTarget⟩
  rcases leftTemplate with
    ⟨leftMove, leftRow, leftReceiverState, leftTarget⟩
  rcases rightFibre with ⟨rightFibreMove, rightOwner, rightMonitor⟩
  rcases leftFibre with ⟨leftFibreMove, leftOwner, leftMonitor⟩
  simp [profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?,
    profiledRawJointRecurrentFiniteMemoryOwnerFibreMakeRight?,
    profiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibreReceiver,
    profiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibreReceiver,
    ProfiledRawJointRightOwnerFibreControl.finiteMemoryReceiverAt,
    ProfiledRawJointLeftOwnerFibreControl.finiteMemoryReceiverAt,
    profiledRawJointRightOwnerFibreExceptional,
    profiledRawJointLeftOwnerFibreExceptional]

/-- A right fibre paired with an informed staged receiver decodes without
consulting the unused receiver arm carried beside the fibre. -/
@[simp] theorem
    profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?_fibreStaged
    (rightState : BankControl (Memory := Memory) A strategy)
    (rightReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (rightFibre : ProfiledRawJointRightOwnerFibreControl A)
    (oldLeft newLeft :
      ProfiledRawJointRecurrentFiniteMemoryBankedLeftReceiver
        (Memory := Memory) A strategy)
    (packet :
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryBankResolvedTarget
        (Memory := Memory) A strategy)
    (leftMove : ProfiledRawJointLeftPhysicalSiblingMove A)
    (hleftMove : packet.successor.2.1.1.2.2 = some leftMove)
    (oneCoordinates twoCoordinates :
      ProfiledRawJointRecurrentFiniteMemoryBoundaryBankCoordinates
        (Memory := Memory) A strategy) :
    let pendingOne :
        ProfiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibrePending
          (Memory := Memory) A strategy :=
      (false, (rightFibre, ⟨oldLeft, newLeft⟩), ())
    let staged :
        ProfiledRawJointRecurrentFiniteMemoryRightToLeftStagedReceiver
          (Memory := Memory) A strategy :=
      (rightState, rightReceiver, some packet)
    profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?
        (Memory := Memory) A strategy
        (.inr pendingOne, oneCoordinates)
        (.inl (.inl staged), twoCoordinates) =
      some
        ⟨(rightState,
            ⟨rightFibre.finiteMemoryReceiverAt A rightReceiver,
              rightFibre.2.1⟩,
            initialProfiledRawJointLeftPhysicalSiblingReceiver A leftMove
              .first),
          packet.successor,
          (leftMove.memberController A false).initial⟩ := by
  rcases rightReceiver with
    ⟨rightMove, rightRow, rightReceiverState, rightTarget⟩
  rcases rightFibre with
    ⟨rightFibreMove, rightOwner, rightMonitor⟩
  simp [profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?,
    profiledRawJointRecurrentFiniteMemoryOwnerFibreMakeRight?,
    ProfiledRawJointRightOwnerFibreControl.finiteMemoryReceiverAt, hleftMove,
    initialProfiledRawJointLeftPhysicalSiblingReceiver,
    profiledRawJointRightOwnerFibreExceptional]

/-- Mirrored staged/fibre decoder seam. -/
@[simp] theorem
    profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData?_stagedFibre
    (leftState : BankControl (Memory := Memory) A strategy)
    (leftReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (leftFibre : ProfiledRawJointLeftOwnerFibreControl A)
    (oldRight newRight :
      ProfiledRawJointRecurrentFiniteMemoryBankedRightReceiver
        (Memory := Memory) A strategy)
    (packet :
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryBankResolvedTarget
        (Memory := Memory) A strategy)
    (rightMove : ProfiledRawJointRightPhysicalSiblingMove A)
    (hrightMove : packet.successor.2.1.1.2.1 = some rightMove)
    (oneCoordinates twoCoordinates :
      ProfiledRawJointRecurrentFiniteMemoryBoundaryBankCoordinates
        (Memory := Memory) A strategy) :
    let staged :
        ProfiledRawJointRecurrentFiniteMemoryLeftToRightStagedReceiver
          (Memory := Memory) A strategy :=
      (leftState, leftReceiver, some packet)
    let pendingTwo :
        ProfiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibrePending
          (Memory := Memory) A strategy :=
      (true, (leftFibre, ⟨oldRight, newRight⟩), ())
    profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData?
        (Memory := Memory) A strategy
        (.inl (.inl staged), oneCoordinates)
        (.inr pendingTwo, twoCoordinates) =
      some
        ⟨(leftState,
            ⟨leftFibre.finiteMemoryReceiverAt A leftReceiver,
              leftFibre.2.1⟩,
            initialProfiledRawJointRightPhysicalSiblingReceiver A rightMove
              .first),
          packet.successor,
          (rightMove.memberController A false).initial⟩ := by
  rcases leftReceiver with
    ⟨leftMove, leftRow, leftReceiverState, leftTarget⟩
  rcases leftFibre with
    ⟨leftFibreMove, leftOwner, leftMonitor⟩
  simp [profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData?,
    profiledRawJointRecurrentFiniteMemoryOwnerFibreMakeLeft?,
    ProfiledRawJointLeftOwnerFibreControl.finiteMemoryReceiverAt, hrightMove,
    initialProfiledRawJointRightPhysicalSiblingReceiver,
    profiledRawJointLeftOwnerFibreExceptional]

/-- Open-member installed/fibre right decoder seam.  The open arm selects
the first retained right receiver; the installed endpoint supplies the
matching owner. -/
@[simp] theorem
    profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?_openInstalledFibre
    (rightState : BankControl (Memory := Memory) A strategy)
    (rightReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (rightOwner : (rightReceiver.1.memberController A false).Control)
    (leftTemplate : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (leftFibre : ProfiledRawJointLeftOwnerFibreControl A)
    (newRight :
      ProfiledRawJointRecurrentFiniteMemoryBankedRightReceiver
        (Memory := Memory) A strategy)
    (oneCoordinates twoCoordinates :
      ProfiledRawJointRecurrentFiniteMemoryBoundaryBankCoordinates
        (Memory := Memory) A strategy) :
    let pendingTwo :
        ProfiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibrePending
          (Memory := Memory) A strategy :=
      (false,
        (leftFibre, ⟨(rightState, rightReceiver), newRight⟩), ())
    profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?
        (Memory := Memory) A strategy
        (.inl
          (.inr
            (rightState, ⟨rightReceiver.1, rightOwner⟩, leftTemplate)),
          oneCoordinates)
        (.inr pendingTwo, twoCoordinates) =
      some
        ⟨(rightState, ⟨rightReceiver, rightOwner⟩,
            leftFibre.finiteMemoryReceiverAt A leftTemplate),
          oneCoordinates.2, leftFibre.2.1⟩ := by
  rcases rightReceiver with
    ⟨rightMove, rightRow, rightReceiverState, rightTarget⟩
  rcases leftTemplate with
    ⟨leftMove, leftRow, leftReceiverState, leftTarget⟩
  rcases leftFibre with ⟨leftFibreMove, leftOwner, leftMonitor⟩
  simp [profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?,
    profiledRawJointRecurrentFiniteMemoryOwnerFibreMakeRight?,
    profiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibreReceiver,
    ProfiledRawJointLeftOwnerFibreControl.finiteMemoryReceiverAt,
    profiledRawJointLeftOwnerFibreExceptional]

/-- Closed-member installed/fibre right decoder seam.  The dormant left row
comes from the installed template, while its move, owner, and monitor come
from the delivered left fibre. -/
@[simp] theorem
    profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?_installedFibreClosed
    (rightState : BankControl (Memory := Memory) A strategy)
    (rightReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (rightOwner : (rightReceiver.1.memberController A false).Control)
    (leftTemplate : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (leftFibre : ProfiledRawJointLeftOwnerFibreControl A)
    (oldRight :
      ProfiledRawJointRecurrentFiniteMemoryBankedRightReceiver
        (Memory := Memory) A strategy)
    (oneCoordinates twoCoordinates :
      ProfiledRawJointRecurrentFiniteMemoryBoundaryBankCoordinates
        (Memory := Memory) A strategy) :
    let pendingTwo :
        ProfiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibrePending
          (Memory := Memory) A strategy :=
      (true,
        (leftFibre, ⟨oldRight, (rightState, rightReceiver)⟩), ())
    profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?
        (Memory := Memory) A strategy
        (.inl
          (.inr
            (rightState, ⟨rightReceiver.1, rightOwner⟩, leftTemplate)),
          oneCoordinates)
        (.inr pendingTwo, twoCoordinates) =
      some
        ⟨(rightState, ⟨rightReceiver, rightOwner⟩,
            leftFibre.finiteMemoryReceiverAt A leftTemplate),
          oneCoordinates.2, leftFibre.2.1⟩ := by
  rcases rightReceiver with
    ⟨rightMove, rightRow, rightReceiverState, rightTarget⟩
  rcases leftTemplate with
    ⟨leftMove, leftRow, leftReceiverState, leftTarget⟩
  rcases leftFibre with ⟨leftFibreMove, leftOwner, leftMonitor⟩
  simp [profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?,
    profiledRawJointRecurrentFiniteMemoryOwnerFibreMakeRight?,
    profiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibreReceiver,
    ProfiledRawJointLeftOwnerFibreControl.finiteMemoryReceiverAt,
    profiledRawJointLeftOwnerFibreExceptional]

/-- Mirrored closed-member fibre/installed left decoder seam. -/
@[simp] theorem
    profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData?_fibreInstalled
    (leftState : BankControl (Memory := Memory) A strategy)
    (leftReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (leftOwner : (leftReceiver.1.memberController A false).Control)
    (rightTemplate : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (rightFibre : ProfiledRawJointRightOwnerFibreControl A)
    (oldLeft :
      ProfiledRawJointRecurrentFiniteMemoryBankedLeftReceiver
        (Memory := Memory) A strategy)
    (oneCoordinates twoCoordinates :
      ProfiledRawJointRecurrentFiniteMemoryBoundaryBankCoordinates
        (Memory := Memory) A strategy) :
    let pendingOne :
        ProfiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibrePending
          (Memory := Memory) A strategy :=
      (true,
        (rightFibre, ⟨oldLeft, (leftState, leftReceiver)⟩), ())
    profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData?
        (Memory := Memory) A strategy
        (.inr pendingOne, oneCoordinates)
        (.inl
          (.inr
            (leftState, ⟨leftReceiver.1, leftOwner⟩, rightTemplate)),
          twoCoordinates) =
      some
        ⟨(leftState, ⟨leftReceiver, leftOwner⟩,
            rightFibre.finiteMemoryReceiverAt A rightTemplate),
          twoCoordinates.1, rightFibre.2.1⟩ := by
  rcases leftReceiver with
    ⟨leftMove, leftRow, leftReceiverState, leftTarget⟩
  rcases rightTemplate with
    ⟨rightMove, rightRow, rightReceiverState, rightTarget⟩
  rcases rightFibre with ⟨rightFibreMove, rightOwner, rightMonitor⟩
  simp [profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData?,
    profiledRawJointRecurrentFiniteMemoryOwnerFibreMakeLeft?,
    profiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibreReceiver,
    ProfiledRawJointRightOwnerFibreControl.finiteMemoryReceiverAt,
    profiledRawJointRightOwnerFibreExceptional]

/-- Open-member fibre/installed left decoder seam.  This is the shape
produced when a right-oriented fibre/staged state takes a strict-left step:
the open arm of the pending control supplies the newly advanced left
receiver, while the installed endpoint supplies its owner. -/
@[simp] theorem
    profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData?_openFibreInstalled
    (leftState : BankControl (Memory := Memory) A strategy)
    (leftReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (leftOwner : (leftReceiver.1.memberController A false).Control)
    (rightTemplate : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (rightFibre : ProfiledRawJointRightOwnerFibreControl A)
    (newLeft :
      ProfiledRawJointRecurrentFiniteMemoryBankedLeftReceiver
        (Memory := Memory) A strategy)
    (oneCoordinates twoCoordinates :
      ProfiledRawJointRecurrentFiniteMemoryBoundaryBankCoordinates
        (Memory := Memory) A strategy) :
    let pendingOne :
        ProfiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibrePending
          (Memory := Memory) A strategy :=
      (false,
        (rightFibre, ⟨(leftState, leftReceiver), newLeft⟩), ())
    profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData?
        (Memory := Memory) A strategy
        (.inr pendingOne, oneCoordinates)
        (.inl
          (.inr
            (leftState, ⟨leftReceiver.1, leftOwner⟩, rightTemplate)),
          twoCoordinates) =
      some
        ⟨(leftState, ⟨leftReceiver, leftOwner⟩,
            rightFibre.finiteMemoryReceiverAt A rightTemplate),
          twoCoordinates.1, rightFibre.2.1⟩ := by
  rcases leftReceiver with
    ⟨leftMove, leftRow, leftReceiverState, leftTarget⟩
  rcases rightTemplate with
    ⟨rightMove, rightRow, rightReceiverState, rightTarget⟩
  rcases rightFibre with ⟨rightFibreMove, rightOwner, rightMonitor⟩
  simp [profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData?,
    profiledRawJointRecurrentFiniteMemoryOwnerFibreMakeLeft?,
    profiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibreReceiver,
    ProfiledRawJointRightOwnerFibreControl.finiteMemoryReceiverAt,
    profiledRawJointRightOwnerFibreExceptional]

/-- The closed fibre/installed shape is left-oriented.  Its outer sum tags
alone force the right decoder to reject, independently of the stored finite
memory and of every dependent payload. -/
@[simp] theorem
    profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?_reject_fibreInstalled
    (pendingOne :
      ProfiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibrePending
        (Memory := Memory) A strategy)
    (installed :
      ProfiledRawJointRecurrentFiniteMemoryRightToLeftInstalledOwner
        (Memory := Memory) A strategy)
    (oneCoordinates twoCoordinates :
      ProfiledRawJointRecurrentFiniteMemoryBoundaryBankCoordinates
        (Memory := Memory) A strategy) :
    profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?
        (Memory := Memory) A strategy
        (.inr pendingOne, oneCoordinates)
        (.inl (.inr installed), twoCoordinates) = none := by
  rfl

/-- Mirrored tag-disjointness: the installed/fibre shape is right-oriented
and is rejected by the left decoder before its payload is inspected. -/
@[simp] theorem
    profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData?_reject_installedFibre
    (installed :
      ProfiledRawJointRecurrentFiniteMemoryLeftToRightInstalledOwner
        (Memory := Memory) A strategy)
    (pendingTwo :
      ProfiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibrePending
        (Memory := Memory) A strategy)
    (oneCoordinates twoCoordinates :
      ProfiledRawJointRecurrentFiniteMemoryBoundaryBankCoordinates
        (Memory := Memory) A strategy) :
    profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData?
        (Memory := Memory) A strategy
        (.inl (.inr installed), oneCoordinates)
        (.inr pendingTwo, twoCoordinates) = none := by
  rfl

/-- The two oriented decoders are disjoint.  This is the global form of the
tag checks above: every shape accepted by the left decoder is rejected by the
right-priority decoder. -/
theorem
    profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?_none_of_left_some
    (one :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryOneControl
        (Memory := Memory) A strategy)
    (two :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryTwoControl
        (Memory := Memory) A strategy)
    (data :
      ProfiledRawJointRecurrentFiniteMemoryLeftPhaseLiveBoundaryData
        (Memory := Memory) A strategy)
    (hleft :
      profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData?
          (Memory := Memory) A strategy one two = some data) :
    profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?
        (Memory := Memory) A strategy one two = none := by
  rcases one with ⟨one, oneCoordinates⟩
  rcases two with ⟨two, twoCoordinates⟩
  rcases one with bridgeOne | pendingOne
  · rcases bridgeOne with stagedOne | installedOne
    · rcases two with bridgeTwo | pendingTwo
      · rcases bridgeTwo with stagedTwo | installedTwo
        · simp [profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData?]
            at hleft
        · rfl
      · rfl
    · simp [profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData?]
        at hleft
  · rcases two with bridgeTwo | pendingTwo
    · rcases bridgeTwo with stagedTwo | installedTwo
      · simp [profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData?]
          at hleft
      · rfl
    · cases hpendingOne : pendingOne.1 <;>
        cases hpendingTwo : pendingTwo.1 <;>
          simp [profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData?,
            profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?,
            hpendingOne, hpendingTwo] at hleft ⊢

end

/-! ## Endpoint-local no-receive transitions -/

noncomputable def
    profiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryNoRecvOne
    (control :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryOneControl
        (Memory := Memory) A strategy)
    (input : In₁) :
    ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryOneControl
        (Memory := Memory) A strategy × Out₁ :=
  match control.1 with
  | .inl bridge =>
      let next :=
        profiledRawJointRecurrentFiniteMemoryLeftToRightBridgeNoRecv
          (Memory := Memory) A strategy bridge input
      ((.inl next.1, control.2), next.2)
  | .inr pending =>
      let next :=
        profiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibreNoRecv
          (Memory := Memory) A strategy pending input
      ((.inr next.1, control.2), next.2)

noncomputable def
    profiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryNoRecvTwo
    (control :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryTwoControl
        (Memory := Memory) A strategy)
    (input : In₂) :
    ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryTwoControl
        (Memory := Memory) A strategy × Out₂ :=
  match control.1 with
  | .inl bridge =>
      let next :=
        profiledRawJointRecurrentFiniteMemoryRightToLeftBridgeNoRecv
          (Memory := Memory) A strategy bridge input
      ((.inl next.1, control.2), next.2)
  | .inr pending =>
      let next :=
        profiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibreNoRecv
          (Memory := Memory) A strategy pending input
      ((.inr next.1, control.2), next.2)

omit [Inhabited Out₂] [Fintype Memory] in
@[simp] theorem
    profiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryNoRecvOne_coordinates
    (control :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryOneControl
        (Memory := Memory) A strategy)
    (input : In₁) :
    (profiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryNoRecvOne
      (Memory := Memory) A strategy control input).1.2 = control.2 := by
  rcases control with ⟨base, coordinates⟩
  cases base <;> rfl

omit [Inhabited Out₁] [Fintype Memory] in
@[simp] theorem
    profiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryNoRecvTwo_coordinates
    (control :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryTwoControl
        (Memory := Memory) A strategy)
    (input : In₂) :
    (profiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryNoRecvTwo
      (Memory := Memory) A strategy control input).1.2 = control.2 := by
  rcases control with ⟨base, coordinates⟩
  cases base <;> rfl

/-- Endpoint-local blind relation.  Outer coordinates are allowed to differ:
they are not consulted by a no-receive step. -/
inductive ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryOneBlind :
    ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryOneControl
        (Memory := Memory) A strategy →
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryOneControl
        (Memory := Memory) A strategy → Prop
  | bridge {left right leftCoordinates rightCoordinates}
      (hblind :
        ProfiledRawJointRecurrentFiniteMemoryLeftToRightBridgeBlind
          (Memory := Memory) A strategy left right) :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryOneBlind
        (.inl left, leftCoordinates) (.inl right, rightCoordinates)
  | fibre {left right leftCoordinates rightCoordinates}
      (hblind :
        FiniteAcknowledgedDelayedCarrier.DeferredMemberBlind left right) :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryOneBlind
        (.inr left, leftCoordinates) (.inr right, rightCoordinates)

inductive ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryTwoBlind :
    ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryTwoControl
        (Memory := Memory) A strategy →
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryTwoControl
        (Memory := Memory) A strategy → Prop
  | bridge {left right leftCoordinates rightCoordinates}
      (hblind :
        ProfiledRawJointRecurrentFiniteMemoryRightToLeftBridgeBlind
          (Memory := Memory) A strategy left right) :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryTwoBlind
        (.inl left, leftCoordinates) (.inl right, rightCoordinates)
  | fibre {left right leftCoordinates rightCoordinates}
      (hblind :
        FiniteAcknowledgedDelayedCarrier.DeferredMemberBlind left right) :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryTwoBlind
        (.inr left, leftCoordinates) (.inr right, rightCoordinates)

omit [Inhabited Out₂] [Fintype Memory] in
theorem
    profiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryOneBlind_noRecv
    (left right :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryOneControl
        (Memory := Memory) A strategy)
    (input : In₁)
    (hblind :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryOneBlind
        (Memory := Memory) A strategy left right) :
    (profiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryNoRecvOne
        (Memory := Memory) A strategy left input).2 =
        (profiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryNoRecvOne
          (Memory := Memory) A strategy right input).2 ∧
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryOneBlind
        (Memory := Memory) A strategy
        (profiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryNoRecvOne
          (Memory := Memory) A strategy left input).1
        (profiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryNoRecvOne
          (Memory := Memory) A strategy right input).1 := by
  cases hblind with
  | bridge hblind =>
      obtain ⟨hout, hnext⟩ :=
        profiledRawJointRecurrentFiniteMemoryLeftToRightBridgeBlind_noRecv
          (Memory := Memory) A strategy _ _ input hblind
      exact ⟨hout, .bridge hnext⟩
  | fibre hblind =>
      obtain ⟨hout, hnext⟩ :=
        profiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibre_blind_noRecv
          (Memory := Memory) A strategy _ _ input hblind
      exact ⟨hout, .fibre hnext⟩

omit [Inhabited Out₁] [Fintype Memory] in
theorem
    profiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryTwoBlind_noRecv
    (left right :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryTwoControl
        (Memory := Memory) A strategy)
    (input : In₂)
    (hblind :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryTwoBlind
        (Memory := Memory) A strategy left right) :
    (profiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryNoRecvTwo
        (Memory := Memory) A strategy left input).2 =
        (profiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryNoRecvTwo
          (Memory := Memory) A strategy right input).2 ∧
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryTwoBlind
        (Memory := Memory) A strategy
        (profiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryNoRecvTwo
          (Memory := Memory) A strategy left input).1
        (profiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryNoRecvTwo
          (Memory := Memory) A strategy right input).1 := by
  cases hblind with
  | bridge hblind =>
      obtain ⟨hout, hnext⟩ :=
        profiledRawJointRecurrentFiniteMemoryRightToLeftBridgeBlind_noRecv
          (Memory := Memory) A strategy _ _ input hblind
      exact ⟨hout, .bridge hnext⟩
  | fibre hblind =>
      obtain ⟨hout, hnext⟩ :=
        profiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibre_blind_noRecv
          (Memory := Memory) A strategy _ _ input hblind
      exact ⟨hout, .fibre hnext⟩

noncomputable def
    profiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryBlindNoRecvLaws :
    FiniteAcknowledgedDelayedCarrier.BlindNoRecvLaws
      (profiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryNoRecvOne
        (Memory := Memory) A strategy)
      (profiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryNoRecvTwo
        (Memory := Memory) A strategy)
      (ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryOneBlind
        (Memory := Memory) A strategy)
      (ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryTwoBlind
        (Memory := Memory) A strategy) where
  one :=
    profiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryOneBlind_noRecv
      (Memory := Memory) A strategy
  two :=
    profiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryTwoBlind_noRecv
      (Memory := Memory) A strategy

end

end DetParityAutomaton

end DistributedSynthesis
