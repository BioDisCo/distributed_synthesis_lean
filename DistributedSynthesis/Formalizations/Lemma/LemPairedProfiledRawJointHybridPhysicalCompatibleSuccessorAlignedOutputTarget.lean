/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleSuccessorLocalReachability

/-!
# Locally aligned emitted outputs install compatible successor targets

The local receiver state and the blind owner control are folds of the same
finite table prefix.  Therefore the receiver output emitted by the concrete
`ReceiverStepFor` is a letter of the checked physical table play.  This file
uses that alignment to recover the target's allowedness and crossed live slot,
then feeds the already decorated key to `SuccessorTargetAt`.

All orientation, row, and liveness data below is proof-side.  Neither local
transition receives a graph, hierarchy side, leader bit, or strict-leader bit.
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

private abbrev CompatiblePolicy
    (initial : ProfiledRawJointCommonBaseWorld A strategy) :=
  ProfiledRawJointHybridPhysicalCompatibleRationalPolicy A strategy hwin
    initial

private abbrev CompatibleState
    (initial : ProfiledRawJointCommonBaseWorld A strategy) :=
  ProfiledRawJointHybridPhysicalCompatiblePolicyState A strategy hwin initial

/-! ## Right-table output -/

/-- A locally aligned concrete right receiver step emits an allowed bare
target with a live crossed left slot. -/
theorem
    profiledRawJointHybridPhysicalCompatibleRightReceiverStepFor_targetSafe
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial)
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (owner : (move.memberController A false).Control)
    (monitorState :
      (profiledRawJointHybridPhysicalCompatibleSuccessorRightMonitor A strategy
        hwin (initial := initial) move false).State)
    (hlocal :
      ProfiledRawJointHybridPhysicalCompatibleRightLocallyReachable A strategy
        hwin policy state move owner monitorState)
    (row : PairedEntryRow) (input : In₂ × In₁) :
    let output :=
      (profiledRawJointHybridPhysicalCompatibleRightReceiverStepFor A strategy
        hwin policy state move owner row monitorState input).1
    profiledRawJointRightPhysicalSiblingAllowed A move.1
        (output.target row).1.1 ∧
      ∃ slot : ProfiledRawLeftSlot A,
        (output.target row).1.1.family.left () = some slot := by
  dsimp only
  obtain ⟨past, _, _, houtput⟩ :=
    hlocal.exists_output_eq_play A strategy hwin false row input
  let env : Nat → In₂ × In₁ := omegaOfList (past ++ [input])
  let play :=
    profiledRawJointHybridPhysicalCompatibleRightPhysicalPlay A strategy hwin
      policy state move false env
  have hsafe :=
    profiledRawJointTargetRight_targetsSafe_of_wins A
      (profiledRawJointUnitRightTargetProjection A)
      (profiledRawJointRightPhysicalSiblingAllowed A move.1)
      move.1.source play
      (profiledRawJointHybridPhysicalCompatibleRightPhysicalPlay_wins A
        strategy hwin policy state move false env)
      past.length row
  have hprojection :
      profiledRawJointHybridPhysicalCompatibleSuccessorRightReceiverProjection
          A strategy hwin
          (profiledRawJointHybridPhysicalCompatibleRightReceiverStepFor A
            strategy hwin policy state move owner row monitorState input).1 =
        (play past.length).2.1 := by
    rw [houtput]
    rfl
  have htarget :
      ((profiledRawJointHybridPhysicalCompatibleRightReceiverStepFor A strategy
        hwin policy state move owner row monitorState input).1.target row).1.1 =
        ((play past.length).2.1.target row) := by
    exact congrArg (fun output ↦ output.target row) hprojection
  rw [htarget]
  refine ⟨hsafe.2, ?_⟩
  exact exists_profiledRawJointLeftSlot_of_rightPhysicalTargetSafe A
    ((play past.length).2.1.target row)
    (((profiledRawJointRightPhysicalSiblingMonitor A move.1 false).run play
      past.length).2.1)
    row (profiledRawJointTargetRightPhysicalLetter A (play past.length))
    hsafe.1

/-- The exact decorated output of a locally aligned right receiver step
installs a same-policy successor target, for either fresh acknowledgement. -/
theorem
    exists_profiledRawJointHybridPhysicalCompatibleRightReceiverStepFor_targetAt
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial)
    (hreachable : ProfiledRawJointHybridPhysicalCompatibleReachable A strategy
      hwin initial policy state)
    (currentCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (current_code : state.1.1 = .oneSided currentCode)
    (currentRoot : ProfiledRawJointThreadRoot A)
    (current_live :
      profiledRawJointHybridCurrentSlots A .right state.1.1 () =
        some currentRoot)
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (move_eq : state.1.2.1 = some move)
    (owner : (move.memberController A false).Control)
    (monitorState :
      (profiledRawJointHybridPhysicalCompatibleSuccessorRightMonitor A strategy
        hwin (initial := initial) move false).State)
    (hlocal :
      ProfiledRawJointHybridPhysicalCompatibleRightLocallyReachable A strategy
        hwin policy state move owner monitorState)
    (row : PairedEntryRow) (input : In₂ × In₁) (closeMember : Bool) :
    let output :=
      (profiledRawJointHybridPhysicalCompatibleRightReceiverStepFor A strategy
        hwin policy state move owner row monitorState input).1
    let payload :=
      profiledRawJointHybridPhysicalCompatibleRightPendingPayloadOfOutput A
        strategy hwin output row
    let target :=
      profiledRawJointHybridPhysicalCompatibleRightPendingPayloadTarget A
        strategy hwin payload closeMember
    ∃ slot : ProfiledRawLeftSlot A,
      ProfiledRawJointHybridPhysicalCompatibleRootAlignedSuccessorTargetAt A
        strategy hwin policy state target .left (.inr slot) := by
  dsimp only
  let raw :=
    profiledRawJointHybridPhysicalCompatibleSuccessorRightReceiverProjection A
      strategy hwin
      (profiledRawJointHybridPhysicalCompatibleRightReceiverStepFor A strategy
        hwin policy state move owner row monitorState input).1
  have hsafe :=
    profiledRawJointHybridPhysicalCompatibleRightReceiverStepFor_targetSafe A
      strategy hwin policy state move owner monitorState hlocal row input
  obtain ⟨slot, hlive⟩ := hsafe.2
  have hdecorated :
      profiledRawJointHybridPhysicalCompatibleDecorateRightReceiverOutput A
          strategy hwin policy state raw =
        (profiledRawJointHybridPhysicalCompatibleRightReceiverStepFor A
          strategy hwin policy state move owner row monitorState input).1 := by
    rfl
  have htarget :=
    exists_profiledRawJointHybridPhysicalCompatibleRightPendingPayloadOfDecoratedOutput_targetAt
      A strategy hwin policy state hreachable currentCode current_code
        currentRoot current_live move move_eq raw row closeMember hsafe.1 slot
        hlive
  rw [hdecorated] at htarget
  exact htarget

/-! ## Left-table output -/

/-- Left mirror of the locally aligned target-safety theorem. -/
theorem
    profiledRawJointHybridPhysicalCompatibleLeftReceiverStepFor_targetSafe
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (owner : (move.memberController A false).Control)
    (monitorState :
      (profiledRawJointHybridPhysicalCompatibleSuccessorLeftMonitor A strategy
        hwin (initial := initial) move false).State)
    (hlocal :
      ProfiledRawJointHybridPhysicalCompatibleLeftLocallyReachable A strategy
        hwin policy state move owner monitorState)
    (row : PairedEntryRow) (input : In₁ × In₂) :
    let output :=
      (profiledRawJointHybridPhysicalCompatibleLeftReceiverStepFor A strategy
        hwin policy state move owner row monitorState input).1
    profiledRawJointLeftPhysicalSiblingAllowed A move.1
        (output.target row).1.1 ∧
      ∃ slot : ProfiledRawRightSlot A,
        (output.target row).1.1.family.right () = some slot := by
  dsimp only
  obtain ⟨past, _, _, houtput⟩ :=
    hlocal.exists_output_eq_play A strategy hwin false row input
  let env : Nat → In₁ × In₂ := omegaOfList (past ++ [input])
  let play :=
    profiledRawJointHybridPhysicalCompatibleLeftPhysicalPlay A strategy hwin
      policy state move false env
  have hsafe :=
    profiledRawJointTargetLeft_targetsSafe_of_wins A
      (profiledRawJointUnitLeftTargetProjection A)
      (profiledRawJointLeftPhysicalSiblingAllowed A move.1)
      move.1.source play
      (profiledRawJointHybridPhysicalCompatibleLeftPhysicalPlay_wins A
        strategy hwin policy state move false env)
      past.length row
  have hprojection :
      profiledRawJointHybridPhysicalCompatibleSuccessorLeftReceiverProjection
          A strategy hwin
          (profiledRawJointHybridPhysicalCompatibleLeftReceiverStepFor A
            strategy hwin policy state move owner row monitorState input).1 =
        (play past.length).2.1 := by
    rw [houtput]
    rfl
  have htarget :
      ((profiledRawJointHybridPhysicalCompatibleLeftReceiverStepFor A strategy
        hwin policy state move owner row monitorState input).1.target row).1.1 =
        ((play past.length).2.1.target row) := by
    exact congrArg (fun output ↦ output.target row) hprojection
  rw [htarget]
  refine ⟨hsafe.2, ?_⟩
  exact exists_profiledRawJointRightSlot_of_leftPhysicalTargetSafe A
    ((play past.length).2.1.target row)
    (((profiledRawJointLeftPhysicalSiblingMonitor A move.1 false).run play
      past.length).2.1)
    row (profiledRawJointTargetLeftPhysicalLetter A (play past.length))
    hsafe.1

/-- The exact decorated output of a locally aligned left receiver step
installs a same-policy successor target, for either fresh acknowledgement. -/
theorem
    exists_profiledRawJointHybridPhysicalCompatibleLeftReceiverStepFor_targetAt
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial)
    (hreachable : ProfiledRawJointHybridPhysicalCompatibleReachable A strategy
      hwin initial policy state)
    (currentCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (current_code : state.1.1 = .oneSided currentCode)
    (currentRoot : ProfiledRawJointThreadRoot A)
    (current_live :
      profiledRawJointHybridCurrentSlots A .left state.1.1 () =
        some currentRoot)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (move_eq : state.1.2.2 = some move)
    (owner : (move.memberController A false).Control)
    (monitorState :
      (profiledRawJointHybridPhysicalCompatibleSuccessorLeftMonitor A strategy
        hwin (initial := initial) move false).State)
    (hlocal :
      ProfiledRawJointHybridPhysicalCompatibleLeftLocallyReachable A strategy
        hwin policy state move owner monitorState)
    (row : PairedEntryRow) (input : In₁ × In₂) (closeMember : Bool) :
    let output :=
      (profiledRawJointHybridPhysicalCompatibleLeftReceiverStepFor A strategy
        hwin policy state move owner row monitorState input).1
    let payload :=
      profiledRawJointHybridPhysicalCompatibleLeftPendingPayloadOfOutput A
        strategy hwin output row
    let target :=
      profiledRawJointHybridPhysicalCompatibleLeftPendingPayloadTarget A
        strategy hwin payload closeMember
    ∃ slot : ProfiledRawRightSlot A,
      ProfiledRawJointHybridPhysicalCompatibleRootAlignedSuccessorTargetAt A
        strategy hwin policy state target .right (.inl slot) := by
  dsimp only
  let raw :=
    profiledRawJointHybridPhysicalCompatibleSuccessorLeftReceiverProjection A
      strategy hwin
      (profiledRawJointHybridPhysicalCompatibleLeftReceiverStepFor A strategy
        hwin policy state move owner row monitorState input).1
  have hsafe :=
    profiledRawJointHybridPhysicalCompatibleLeftReceiverStepFor_targetSafe A
      strategy hwin policy state move owner monitorState hlocal row input
  obtain ⟨slot, hlive⟩ := hsafe.2
  have hdecorated :
      profiledRawJointHybridPhysicalCompatibleDecorateLeftReceiverOutput A
          strategy hwin policy state raw =
        (profiledRawJointHybridPhysicalCompatibleLeftReceiverStepFor A strategy
          hwin policy state move owner row monitorState input).1 := by
    rfl
  have htarget :=
    exists_profiledRawJointHybridPhysicalCompatibleLeftPendingPayloadOfDecoratedOutput_targetAt
      A strategy hwin policy state hreachable currentCode current_code
        currentRoot current_live move move_eq raw row closeMember hsafe.1 slot
        hlive
  rw [hdecorated] at htarget
  exact htarget

end

end DetParityAutomaton

end DistributedSynthesis
