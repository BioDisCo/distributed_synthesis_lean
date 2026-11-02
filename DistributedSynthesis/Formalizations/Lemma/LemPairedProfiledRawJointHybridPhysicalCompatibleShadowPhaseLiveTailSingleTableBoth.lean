/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleShadowPhaseLiveTailFibreTypes

/-!
# A recurrent simultaneous close from one live tail table

At a simultaneous receive both endpoints possess the two finite pieces of the
same live table: its owner control and its retained receiver state.  Thus both
local handlers can recompute one receiver record and project their respective
coordinates from that record.  A strict-right phase uses the right table;
strict-left uses the left table.

This is deliberately weaker than an anti-mosaic equality between an
independently selected right table and an independently selected left table:
no such equality is needed.  The definitions below receive only finite local
controls and the two current inputs.  In particular they receive no graph,
orientation, leader bit, strict-leader bit, history, or semantic view.
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

private abbrev Tag :=
  ProfiledRawJointHybridShadowPhaseLiveTag A strategy hwin

private abbrev TailState (tag : Tag A strategy hwin) :=
  ProfiledRawJointHybridShadowPhaseLiveTailState A strategy hwin tag

private abbrev RightOutput (tag : Tag A strategy hwin) :=
  ProfiledRawJointHybridShadowPhaseLiveTailRightReceiverOutput A strategy hwin
    tag

private abbrev LeftOutput (tag : Tag A strategy hwin) :=
  ProfiledRawJointHybridShadowPhaseLiveTailLeftReceiverOutput A strategy hwin
    tag

private abbrev RightOwner (tag : Tag A strategy hwin) :=
  ProfiledRawJointHybridShadowPhaseLiveTailFrontierOneShared A strategy hwin
    tag

private abbrev LeftOwner (tag : Tag A strategy hwin) :=
  ProfiledRawJointHybridShadowPhaseLiveTailFrontierTwoShared A strategy hwin
    tag

private abbrev RightReceiver (tag : Tag A strategy hwin) :=
  ProfiledRawJointHybridShadowPhaseLiveTailRightReceiver A strategy hwin tag

private abbrev LeftReceiver (tag : Tag A strategy hwin) :=
  ProfiledRawJointHybridShadowPhaseLiveTailLeftReceiver A strategy hwin tag

/-! ## One exact tail-relative receiver calculation -/

/-- Advance a right receiver using the owner control stored at the same tail
key.  The decorated output retains the exact next key of this tag fibre. -/
noncomputable def profiledRawJointHybridShadowPhaseLiveTailRightReceiverStepFor
    (tag : Tag A strategy hwin) (state : TailState A strategy hwin tag)
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (owner : (move.memberController A false).Control)
    (row : PairedEntryRow)
    (monitorState :
      (profiledRawJointHybridShadowPhaseLiveTailSuccessorRightMonitor A
        strategy hwin (tag := tag) move false).State)
    (input : In₂ × In₁) :
    RightOutput A strategy hwin tag × RightReceiver A strategy hwin tag :=
  let monitor :=
    profiledRawJointHybridShadowPhaseLiveTailSuccessorRightMonitor A strategy
      hwin (tag := tag) move false
  let controller :=
    profiledRawJointHybridShadowPhaseLiveTailDecoratedRightMemberController A
      strategy hwin state move false
  let label := controller.labelOf owner
  let output := label.2 monitorState input
  let nextState := monitor.step monitorState
    (input, output, label.1 input.2)
  (output, ⟨state, some ⟨move, row, nextState, some output⟩⟩)

/-- Left-table mirror. -/
noncomputable def profiledRawJointHybridShadowPhaseLiveTailLeftReceiverStepFor
    (tag : Tag A strategy hwin) (state : TailState A strategy hwin tag)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (owner : (move.memberController A false).Control)
    (row : PairedEntryRow)
    (monitorState :
      (profiledRawJointHybridShadowPhaseLiveTailSuccessorLeftMonitor A strategy
        hwin (tag := tag) move false).State)
    (input : In₁ × In₂) :
    LeftOutput A strategy hwin tag × LeftReceiver A strategy hwin tag :=
  let monitor :=
    profiledRawJointHybridShadowPhaseLiveTailSuccessorLeftMonitor A strategy
      hwin (tag := tag) move false
  let controller :=
    profiledRawJointHybridShadowPhaseLiveTailDecoratedLeftMemberController A
      strategy hwin state move false
  let label := controller.labelOf owner
  let output := label.2 monitorState input
  let nextState := monitor.step monitorState
    (input, output, label.1 input.2)
  (output, ⟨state, some ⟨move, row, nextState, some output⟩⟩)

/-! ## The exact local owner/receiver alignment -/

/-- Process one's stored right owner and process two's retained right receiver
name the same tail key, move, and finite table prefix. -/
def ProfiledRawJointHybridShadowPhaseLiveTailRightSingleTableAligned
    (tag : Tag A strategy hwin) (owner : RightOwner A strategy hwin tag)
    (receiver : RightReceiver A strategy hwin tag) : Prop :=
  ∃ (state : TailState A strategy hwin tag)
      (move : ProfiledRawJointRightPhysicalSiblingMove A)
      (ownerControl : (move.memberController A false).Control)
      (row : PairedEntryRow)
      (monitorState :
        (profiledRawJointHybridShadowPhaseLiveTailSuccessorRightMonitor A
          strategy hwin (tag := tag) move false).State)
      (staged : Option (RightOutput A strategy hwin tag)),
    owner = ⟨state, .inr ⟨move, ownerControl⟩⟩ ∧
      receiver = ⟨state, some ⟨move, row, monitorState, staged⟩⟩

/-- Process-two stored left owner and process one's retained left receiver
mirror the same exact alignment. -/
def ProfiledRawJointHybridShadowPhaseLiveTailLeftSingleTableAligned
    (tag : Tag A strategy hwin) (owner : LeftOwner A strategy hwin tag)
    (receiver : LeftReceiver A strategy hwin tag) : Prop :=
  ∃ (state : TailState A strategy hwin tag)
      (move : ProfiledRawJointLeftPhysicalSiblingMove A)
      (ownerControl : (move.memberController A false).Control)
      (row : PairedEntryRow)
      (monitorState :
        (profiledRawJointHybridShadowPhaseLiveTailSuccessorLeftMonitor A
          strategy hwin (tag := tag) move false).State)
      (staged : Option (LeftOutput A strategy hwin tag)),
    owner = ⟨state, .inr ⟨move, ownerControl⟩⟩ ∧
      receiver = ⟨state, some ⟨move, row, monitorState, staged⟩⟩

/-! ## Total local lookup from the two delivered finite controls -/

/-- Recompute the unique right record when the controls match; the fallback
totalizes unreachable malformed pairs. -/
noncomputable def profiledRawJointHybridShadowPhaseLiveTailRightSingleTableRecord
    (tag : Tag A strategy hwin) (fallback : RightOutput A strategy hwin tag)
    (owner : RightOwner A strategy hwin tag)
    (receiver : RightReceiver A strategy hwin tag) (input : In₂ × In₁) :
    RightOutput A strategy hwin tag := by
  classical
  rcases owner with ⟨ownerState, ownerShared⟩
  rcases receiver with ⟨receiverState, receiverPayload⟩
  by_cases hstate : receiverState = ownerState
  · subst receiverState
    cases ownerShared with
    | inl _ => exact fallback
    | inr installed =>
        rcases installed with ⟨ownerMove, ownerControl⟩
        cases receiverPayload with
        | none => exact fallback
        | some retained =>
            rcases retained with
              ⟨receiverMove, row, monitorState, staged⟩
            by_cases hmove : receiverMove = ownerMove
            · subst receiverMove
              exact
                (profiledRawJointHybridShadowPhaseLiveTailRightReceiverStepFor
                  A strategy hwin tag ownerState ownerMove ownerControl row
                    monitorState input).1
            · exact fallback
  · exact fallback

/-- Left-table mirror. -/
noncomputable def profiledRawJointHybridShadowPhaseLiveTailLeftSingleTableRecord
    (tag : Tag A strategy hwin) (fallback : LeftOutput A strategy hwin tag)
    (owner : LeftOwner A strategy hwin tag)
    (receiver : LeftReceiver A strategy hwin tag) (input : In₁ × In₂) :
    LeftOutput A strategy hwin tag := by
  classical
  rcases owner with ⟨ownerState, ownerShared⟩
  rcases receiver with ⟨receiverState, receiverPayload⟩
  by_cases hstate : receiverState = ownerState
  · subst receiverState
    cases ownerShared with
    | inl _ => exact fallback
    | inr installed =>
        rcases installed with ⟨ownerMove, ownerControl⟩
        cases receiverPayload with
        | none => exact fallback
        | some retained =>
            rcases retained with
              ⟨receiverMove, row, monitorState, staged⟩
            by_cases hmove : receiverMove = ownerMove
            · subst receiverMove
              exact
                (profiledRawJointHybridShadowPhaseLiveTailLeftReceiverStepFor A
                  strategy hwin tag ownerState ownerMove ownerControl row
                    monitorState input).1
            · exact fallback
  · exact fallback

@[simp] theorem
    profiledRawJointHybridShadowPhaseLiveTailRightSingleTableRecord_live
    (tag : Tag A strategy hwin) (fallback : RightOutput A strategy hwin tag)
    (state : TailState A strategy hwin tag)
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (ownerControl : (move.memberController A false).Control)
    (row : PairedEntryRow)
    (monitorState :
      (profiledRawJointHybridShadowPhaseLiveTailSuccessorRightMonitor A
        strategy hwin (tag := tag) move false).State)
    (staged : Option (RightOutput A strategy hwin tag)) (input : In₂ × In₁) :
    profiledRawJointHybridShadowPhaseLiveTailRightSingleTableRecord A strategy
        hwin tag fallback ⟨state, .inr ⟨move, ownerControl⟩⟩
          ⟨state, some ⟨move, row, monitorState, staged⟩⟩ input =
      (profiledRawJointHybridShadowPhaseLiveTailRightReceiverStepFor A strategy
        hwin tag state move ownerControl row monitorState input).1 := by
  simp [profiledRawJointHybridShadowPhaseLiveTailRightSingleTableRecord]

@[simp] theorem
    profiledRawJointHybridShadowPhaseLiveTailLeftSingleTableRecord_live
    (tag : Tag A strategy hwin) (fallback : LeftOutput A strategy hwin tag)
    (state : TailState A strategy hwin tag)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (ownerControl : (move.memberController A false).Control)
    (row : PairedEntryRow)
    (monitorState :
      (profiledRawJointHybridShadowPhaseLiveTailSuccessorLeftMonitor A strategy
        hwin (tag := tag) move false).State)
    (staged : Option (LeftOutput A strategy hwin tag)) (input : In₁ × In₂) :
    profiledRawJointHybridShadowPhaseLiveTailLeftSingleTableRecord A strategy
        hwin tag fallback ⟨state, .inr ⟨move, ownerControl⟩⟩
          ⟨state, some ⟨move, row, monitorState, staged⟩⟩ input =
      (profiledRawJointHybridShadowPhaseLiveTailLeftReceiverStepFor A strategy
        hwin tag state move ownerControl row monitorState input).1 := by
  simp [profiledRawJointHybridShadowPhaseLiveTailLeftSingleTableRecord]

/-- Alignment exposes the exact state and control used by the total right
lookup.  Thus the fallback branch cannot be taken on an aligned pair. -/
theorem
    ProfiledRawJointHybridShadowPhaseLiveTailRightSingleTableAligned.record_eq
    (tag : Tag A strategy hwin) (fallback : RightOutput A strategy hwin tag)
    (owner : RightOwner A strategy hwin tag)
    (receiver : RightReceiver A strategy hwin tag)
    (haligned :
      ProfiledRawJointHybridShadowPhaseLiveTailRightSingleTableAligned A
        strategy hwin tag owner receiver)
    (input : In₂ × In₁) :
    ∃ (state : TailState A strategy hwin tag)
        (move : ProfiledRawJointRightPhysicalSiblingMove A)
        (ownerControl : (move.memberController A false).Control)
        (row : PairedEntryRow)
        (monitorState :
          (profiledRawJointHybridShadowPhaseLiveTailSuccessorRightMonitor A
            strategy hwin (tag := tag) move false).State)
        (staged : Option (RightOutput A strategy hwin tag)),
      owner = ⟨state, .inr ⟨move, ownerControl⟩⟩ ∧
        receiver = ⟨state, some ⟨move, row, monitorState, staged⟩⟩ ∧
        profiledRawJointHybridShadowPhaseLiveTailRightSingleTableRecord A
            strategy hwin tag fallback owner receiver input =
          (profiledRawJointHybridShadowPhaseLiveTailRightReceiverStepFor A
            strategy hwin tag state move ownerControl row monitorState input).1 := by
  rcases haligned with
    ⟨state, move, ownerControl, row, monitorState, staged, rfl, rfl⟩
  exact ⟨state, move, ownerControl, row, monitorState, staged, rfl, rfl, by
    simp⟩

/-- Left alignment exposes the same exact finite data. -/
theorem
    ProfiledRawJointHybridShadowPhaseLiveTailLeftSingleTableAligned.record_eq
    (tag : Tag A strategy hwin) (fallback : LeftOutput A strategy hwin tag)
    (owner : LeftOwner A strategy hwin tag)
    (receiver : LeftReceiver A strategy hwin tag)
    (haligned :
      ProfiledRawJointHybridShadowPhaseLiveTailLeftSingleTableAligned A strategy
        hwin tag owner receiver)
    (input : In₁ × In₂) :
    ∃ (state : TailState A strategy hwin tag)
        (move : ProfiledRawJointLeftPhysicalSiblingMove A)
        (ownerControl : (move.memberController A false).Control)
        (row : PairedEntryRow)
        (monitorState :
          (profiledRawJointHybridShadowPhaseLiveTailSuccessorLeftMonitor A
            strategy hwin (tag := tag) move false).State)
        (staged : Option (LeftOutput A strategy hwin tag)),
      owner = ⟨state, .inr ⟨move, ownerControl⟩⟩ ∧
        receiver = ⟨state, some ⟨move, row, monitorState, staged⟩⟩ ∧
        profiledRawJointHybridShadowPhaseLiveTailLeftSingleTableRecord A
            strategy hwin tag fallback owner receiver input =
          (profiledRawJointHybridShadowPhaseLiveTailLeftReceiverStepFor A
            strategy hwin tag state move ownerControl row monitorState input).1 := by
  rcases haligned with
    ⟨state, move, ownerControl, row, monitorState, staged, rfl, rfl⟩
  exact ⟨state, move, ownerControl, row, monitorState, staged, rfl, rfl, by
    simp⟩

/-! ## The two local simultaneous outputs are one record -/

noncomputable def
    profiledRawJointHybridShadowPhaseLiveTailRightSingleTableBothOutputOne
    (tag : Tag A strategy hwin) (fallback : RightOutput A strategy hwin tag)
    (owner : RightOwner A strategy hwin tag)
    (receiver : RightReceiver A strategy hwin tag) (input : In₁ × In₂) :
    Out₁ :=
  let record :=
    profiledRawJointHybridShadowPhaseLiveTailRightSingleTableRecord A strategy
      hwin tag fallback owner receiver (input.2, input.1)
  pairedRightClosingForRow .both record.physical

noncomputable def
    profiledRawJointHybridShadowPhaseLiveTailRightSingleTableBothOutputTwo
    (tag : Tag A strategy hwin) (fallback : RightOutput A strategy hwin tag)
    (receiver : RightReceiver A strategy hwin tag)
    (owner : RightOwner A strategy hwin tag) (input : In₁ × In₂) : Out₂ :=
  let record :=
    profiledRawJointHybridShadowPhaseLiveTailRightSingleTableRecord A strategy
      hwin tag fallback owner receiver (input.2, input.1)
  pairedRightInformedForRow .both record.physical

noncomputable def
    profiledRawJointHybridShadowPhaseLiveTailLeftSingleTableBothOutputOne
    (tag : Tag A strategy hwin) (fallback : LeftOutput A strategy hwin tag)
    (receiver : LeftReceiver A strategy hwin tag)
    (owner : LeftOwner A strategy hwin tag) (input : In₁ × In₂) : Out₁ :=
  let record :=
    profiledRawJointHybridShadowPhaseLiveTailLeftSingleTableRecord A strategy
      hwin tag fallback owner receiver input
  pairedLeftInformedForRow .both record.physical

noncomputable def
    profiledRawJointHybridShadowPhaseLiveTailLeftSingleTableBothOutputTwo
    (tag : Tag A strategy hwin) (fallback : LeftOutput A strategy hwin tag)
    (owner : LeftOwner A strategy hwin tag)
    (receiver : LeftReceiver A strategy hwin tag) (input : In₁ × In₂) : Out₂ :=
  let record :=
    profiledRawJointHybridShadowPhaseLiveTailLeftSingleTableRecord A strategy
      hwin tag fallback owner receiver input
  pairedLeftClosingForRow .both record.physical

/-- In a right-live phase the two endpoint-local maps are definitionally the
two physical coordinates of one checked receiver record. -/
theorem
    ProfiledRawJointHybridShadowPhaseLiveTailRightSingleTableAligned.bothOutputs_eq_closingRecord
    (tag : Tag A strategy hwin) (fallback : RightOutput A strategy hwin tag)
    (owner : RightOwner A strategy hwin tag)
    (receiver : RightReceiver A strategy hwin tag)
    (_haligned :
      ProfiledRawJointHybridShadowPhaseLiveTailRightSingleTableAligned A
        strategy hwin tag owner receiver)
    (input : In₁ × In₂) :
    (profiledRawJointHybridShadowPhaseLiveTailRightSingleTableBothOutputOne A
        strategy hwin tag fallback owner receiver input,
      profiledRawJointHybridShadowPhaseLiveTailRightSingleTableBothOutputTwo A
        strategy hwin tag fallback receiver owner input) =
      let record :=
        profiledRawJointHybridShadowPhaseLiveTailRightSingleTableRecord A
          strategy hwin tag fallback owner receiver (input.2, input.1)
      (pairedRightClosingForRow .both record.physical,
        pairedRightInformedForRow .both record.physical) := by
  rfl

/-- Left-live mirror. -/
theorem
    ProfiledRawJointHybridShadowPhaseLiveTailLeftSingleTableAligned.bothOutputs_eq_closingRecord
    (tag : Tag A strategy hwin) (fallback : LeftOutput A strategy hwin tag)
    (owner : LeftOwner A strategy hwin tag)
    (receiver : LeftReceiver A strategy hwin tag)
    (_haligned :
      ProfiledRawJointHybridShadowPhaseLiveTailLeftSingleTableAligned A strategy
        hwin tag owner receiver)
    (input : In₁ × In₂) :
    (profiledRawJointHybridShadowPhaseLiveTailLeftSingleTableBothOutputOne A
        strategy hwin tag fallback receiver owner input,
      profiledRawJointHybridShadowPhaseLiveTailLeftSingleTableBothOutputTwo A
        strategy hwin tag fallback owner receiver input) =
      let record :=
        profiledRawJointHybridShadowPhaseLiveTailLeftSingleTableRecord A strategy
          hwin tag fallback owner receiver input
      (pairedLeftInformedForRow .both record.physical,
        pairedLeftClosingForRow .both record.physical) := by
  rfl

end

end DetParityAutomaton

end DistributedSynthesis
