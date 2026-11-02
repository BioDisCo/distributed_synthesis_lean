/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenWitnessedSemanticControlBridge
import DistributedSynthesis.Formalizations.Theorem.ThmPairedEntryBranchFlatten

/-!
# One policy-aligned epoch has the advertised root priority

The rational code policy proves parity for a persistent hidden lineage, while
the round implementation evaluates one witnessed re-anchored row at a time.
This file isolates the exact pointwise bridge between the two descriptions.

If a root occurs in the target code on the side opposite the completed
physical query, then that root is represented by a literal survivor of the
re-anchored semantic step.  The survivor supplies an actual source memory,
an actual target memory, and one genuine `PairedEntryDirection` between them.
The root priority is exactly both the target-memory priority and the minimum
original-DPA priority of that finite block.

All sides, roots, survivors, and semantic memories below are proof data.  No
side, orientation, strict-leader flag, lineage, or hidden bit is exposed to a
process.
-/

namespace DistributedSynthesis

universe i u v x y s

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

/-! ## A branch-free block-minimum identity -/

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- The successor priority/minimum calculation used by branch flattening is
already pointwise.  This form removes the irrelevant surrounding infinite
branch and retains only direction compatibility at the current memory. -/
theorem pairedEntryPriority_step_eq_selectedBlockMin
    (memory : PairedStrategyMemory A strategy)
    (direction : PairedEntryDirection (In₁ := In₁) (In₂ := In₂))
    (hcompatible :
      PairedStrategyMemory.DirectionCompatible (A := A) memory direction) :
    pairedEntryPriority A
        ((memory.step (A := A) direction).toTreeState) =
      A.priority
        (blockMinState A
          (entryState (A := A)
            (PairedStrategyMemory.selectedHistory memory direction))
          (PairedStrategyMemory.selectedBlockWord memory direction)) := by
  cases hmemory : memory with
  | sink =>
      simp [PairedStrategyMemory.DirectionCompatible, hmemory] at hcompatible
  | processOne entry minimum =>
      cases hdirection : direction with
      | fromTwo row past move =>
          simp [PairedStrategyMemory.DirectionCompatible, hmemory,
            hdirection] at hcompatible
      | fromOne row past move =>
          cases row <;>
            simp [PairedStrategyMemory.step, PairedStrategyMemory.toTreeState,
              pairedEntryPriority, PairedStrategyMemory.selectedHistory,
              PairedStrategyMemory.selectedBlockWord,
              ProcOnePairedEntryRep.code]
  | processTwo entry minimum =>
      cases hdirection : direction with
      | fromOne row past move =>
          simp [PairedStrategyMemory.DirectionCompatible, hmemory,
            hdirection] at hcompatible
      | fromTwo row past move =>
          cases row <;>
            simp [PairedStrategyMemory.step, PairedStrategyMemory.toTreeState,
              pairedEntryPriority, PairedStrategyMemory.selectedHistory,
              PairedStrategyMemory.selectedBlockWord,
              ProcTwoPairedEntryRep.code]

/-! ## The witnessed target-slot bridge -/

private abbrev EpochFamily :=
  ProfiledOpenWitnessedTableFamily A initialCode

private abbrev EpochDescriptor :=
  ProfiledOpenWitnessedTableBaseDescriptor A initialCode

private abbrev EpochBank :=
  ProfiledOpenWitnessedTableBank A initialCode

private abbrev EpochQuery :=
  ProfiledOpenWitnessedTableQuery A initialCode

omit [Inhabited I] in
/-- One target slot on the physical side of a witnessed re-anchored edge is
an actual strategy block.  Besides the literal memory step, the conclusion
records the two equalities needed by the acceptance handoff: target priority
equals hidden-root priority, and finite-block minimum equals that same root
priority. -/
theorem exists_profiledOpenWitnessedEpochMemoryStep_of_targetSlot
    {sourceFamily : EpochFamily A initialCode}
    {source : EpochDescriptor A initialCode}
    {bank : EpochBank A initialCode}
    {query : EpochQuery A initialCode}
    {targetFamily : EpochFamily A initialCode}
    {target : EpochDescriptor A initialCode}
    (hedge : ProfiledOpenFixedSidewiseWitnessedReanchoredExactEdge A strategy
      hwin basis initialCode sourceFamily source bank query targetFamily
        target)
    (side : IndexedLineageSide) (lineage : I)
    (root : ProfiledOpenClassifiedAnchor A)
    (hside : side = query.1.1.1.other)
    (hslot : profiledOpenIndexedBiBeliefCurrentSlots A side target.code
      lineage = some root) :
    ∃ sourceMemory targetMemory : PairedStrategyMemory A strategy,
      ∃ direction : PairedEntryDirection (In₁ := In₁) (In₂ := In₂),
        PairedStrategyMemory.DirectionCompatible (A := A) sourceMemory
            direction ∧
          targetMemory = sourceMemory.step (A := A) direction ∧
          pairedEntryPriority A targetMemory.toTreeState =
              profiledOpenIndexedRootPriority A root ∧
          A.priority
              (blockMinState A
                (entryState (A := A)
                  (PairedStrategyMemory.selectedHistory sourceMemory
                    direction))
                (PairedStrategyMemory.selectedBlockWord sourceMemory
                  direction)) =
            profiledOpenIndexedRootPriority A root := by
  classical
  rcases hedge with
    ⟨sourceState, stepState, _hsource, _hsourceFamily, _hsourceTag,
      _hvalid, _hstep, _hstepSource, _htargetFamily, htarget,
      _htargetTag⟩
  let raw := profiledOpenIndexedRawDirectionOfFiniteTag A
    (stepState.1.state.code A strategy hwin basis)
    (stepState.1.state.move A strategy hwin basis) query.1.2
  let semantic := stepState.1.state
  let child := profiledOpenFixedSidewiseSemanticNext A strategy hwin basis
    initialCode stepState query.1
  have hchildCode :
      (profiledOpenIndexedCorrelatedSemanticNext A strategy hwin basis
          semantic raw).code A strategy hwin basis = target.code := by
    have hcode := congrArg
      (fun descriptor : EpochDescriptor A initialCode ↦ descriptor.code)
      htarget
    change
      (profiledOpenIndexedOptionalControlledSemanticNext A strategy hwin
          basis initialCode stepState query.1.2).1.state.code A strategy hwin
            basis = target.code at hcode
    change
      (profiledOpenIndexedCorrelatedSemanticNext A strategy hwin basis
          semantic raw).code A strategy hwin basis = target.code at hcode
    exact hcode
  cases hquerySide : query.1.1.1 with
  | right =>
      have hside' : side = .left := by simpa [hquerySide] using hside
      have hrawSlot :
          (profiledOpenIndexedRightChildCode A
            (semantic.code A strategy hwin basis)
            (semantic.move A strategy hwin basis) raw).rootSlots lineage =
              some root := by
        have hslot' := hslot
        rw [hside', profiledOpenIndexedBiBeliefCurrentSlots_left] at hslot'
        rw [← hchildCode] at hslot'
        simpa only [semantic,
          ProfiledOpenIndexedCorrelatedSemanticState.code,
          profiledOpenIndexedCorrelatedSemanticNext,
          profiledOpenIndexedCorrelatedNextLeft_slots] using hslot'
      rw [IndexedLineageChildCode.rootSlots_eq_some_iff] at hrawSlot
      rcases hrawSlot with ⟨row, hrawSlot⟩
      let survivor :
          (profiledOpenIndexedRightRawChildCode A
            (semantic.code A strategy hwin basis)
            (semantic.move A strategy hwin basis) raw).RootSurvivor :=
        ⟨(lineage, (row, root)), hrawSlot⟩
      let handoff := profiledOpenIndexedRightToLeftHandoffOfSurvivor A strategy
        hwin basis semantic raw survivor
      let lane := profiledOpenIndexedRightLaneOfSurvivor A strategy hwin basis
        semantic raw (⟨survivor⟩ : Nonempty _)
      let sourceMemory : PairedStrategyMemory A strategy :=
        .processOne
          (lane.realization.entry (handoff.sourceMember survivor))
          (lane.realization.minimum (handoff.sourceMember survivor))
      let targetMemory : PairedStrategyMemory A strategy :=
        .processTwo
          (handoff.child.realization.entry (handoff.childMember survivor))
          (handoff.child.realization.minimum (handoff.childMember survivor))
      let direction : PairedEntryDirection (In₁ := In₁) (In₂ := In₂) :=
        .fromOne survivor.row handoff.semanticPast raw.rightInput
      let pointed : ProfiledOpenPointedSemanticState A strategy hwin basis :=
        .left {
          realization := handoff.child.realization
          selected := handoff.childMember survivor
          actualEntry := handoff.child.realization.entry
            (handoff.childMember survivor)
          actualMinimum := handoff.child.realization.minimum
            (handoff.childMember survivor)
          entry_selected := rfl
          minimum_selected := rfl }
      have hmemory : targetMemory =
          sourceMemory.step (A := A) direction := by
        exact (handoff.memory_step survivor).symm
      have hpriorityPoint : pointed.priority A =
          profiledOpenIndexedRootPriority A root := by
        have hanchor :=
          profiledOpenIndexedRightToLeftHandoffOfSurvivor_child_anchor A
            strategy hwin basis semantic raw survivor
        simp only [pointed, ProfiledOpenPointedSemanticState.priority,
          ProfiledOpenPointedSemanticState.anchor,
          profiledOpenIndexedRootPriority]
        exact congrArg (profiledOpenClassifiedAnchorPriority A) hanchor
      have htargetPriority : pairedEntryPriority A targetMemory.toTreeState =
          profiledOpenIndexedRootPriority A root := by
        calc
          pairedEntryPriority A targetMemory.toTreeState = pointed.priority A :=
            (ProfiledOpenPointedSemanticState.priority_eq_memory A
              pointed).symm
          _ = profiledOpenIndexedRootPriority A root := hpriorityPoint
      have hcompatible :
          PairedStrategyMemory.DirectionCompatible (A := A) sourceMemory
            direction := by trivial
      refine ⟨sourceMemory, targetMemory, direction, hcompatible, hmemory,
        htargetPriority, ?_⟩
      rw [← htargetPriority, hmemory]
      exact (pairedEntryPriority_step_eq_selectedBlockMin A strategy
        sourceMemory direction hcompatible).symm
  | left =>
      have hside' : side = .right := by simpa [hquerySide] using hside
      have hrawSlot :
          (profiledOpenIndexedLeftChildCode A
            (semantic.code A strategy hwin basis)
            (semantic.move A strategy hwin basis) raw).rootSlots lineage =
              some root := by
        have hslot' := hslot
        rw [hside', profiledOpenIndexedBiBeliefCurrentSlots_right] at hslot'
        rw [← hchildCode] at hslot'
        simpa only [semantic,
          ProfiledOpenIndexedCorrelatedSemanticState.code,
          profiledOpenIndexedCorrelatedSemanticNext,
          profiledOpenIndexedCorrelatedNextRight_slots] using hslot'
      rw [IndexedLineageChildCode.rootSlots_eq_some_iff] at hrawSlot
      rcases hrawSlot with ⟨row, hrawSlot⟩
      let survivor :
          (profiledOpenIndexedLeftRawChildCode A
            (semantic.code A strategy hwin basis)
            (semantic.move A strategy hwin basis) raw).RootSurvivor :=
        ⟨(lineage, (row, root)), hrawSlot⟩
      let handoff := profiledOpenIndexedLeftToRightHandoffOfSurvivor A strategy
        hwin basis semantic raw survivor
      let lane := profiledOpenIndexedLeftLaneOfSurvivor A strategy hwin basis
        semantic raw (⟨survivor⟩ : Nonempty _)
      let sourceMemory : PairedStrategyMemory A strategy :=
        .processTwo
          (lane.realization.entry (handoff.sourceMember survivor))
          (lane.realization.minimum (handoff.sourceMember survivor))
      let targetMemory : PairedStrategyMemory A strategy :=
        .processOne
          (handoff.child.realization.entry (handoff.childMember survivor))
          (handoff.child.realization.minimum (handoff.childMember survivor))
      let direction : PairedEntryDirection (In₁ := In₁) (In₂ := In₂) :=
        .fromTwo survivor.row handoff.semanticPast raw.leftInput
      let pointed : ProfiledOpenPointedSemanticState A strategy hwin basis :=
        .right {
          realization := handoff.child.realization
          selected := handoff.childMember survivor
          actualEntry := handoff.child.realization.entry
            (handoff.childMember survivor)
          actualMinimum := handoff.child.realization.minimum
            (handoff.childMember survivor)
          entry_selected := rfl
          minimum_selected := rfl }
      have hmemory : targetMemory =
          sourceMemory.step (A := A) direction := by
        exact (handoff.memory_step survivor).symm
      have hpriorityPoint : pointed.priority A =
          profiledOpenIndexedRootPriority A root := by
        have hanchor :=
          profiledOpenIndexedLeftToRightHandoffOfSurvivor_child_anchor A
            strategy hwin basis semantic raw survivor
        simp only [pointed, ProfiledOpenPointedSemanticState.priority,
          ProfiledOpenPointedSemanticState.anchor,
          profiledOpenIndexedRootPriority]
        exact congrArg (profiledOpenClassifiedAnchorPriority A) hanchor
      have htargetPriority : pairedEntryPriority A targetMemory.toTreeState =
          profiledOpenIndexedRootPriority A root := by
        calc
          pairedEntryPriority A targetMemory.toTreeState = pointed.priority A :=
            (ProfiledOpenPointedSemanticState.priority_eq_memory A
              pointed).symm
          _ = profiledOpenIndexedRootPriority A root := hpriorityPoint
      have hcompatible :
          PairedStrategyMemory.DirectionCompatible (A := A) sourceMemory
            direction := by trivial
      refine ⟨sourceMemory, targetMemory, direction, hcompatible, hmemory,
        htargetPriority, ?_⟩
      rw [← htargetPriority, hmemory]
      exact (pairedEntryPriority_step_eq_selectedBlockMin A strategy
        sourceMemory direction hcompatible).symm

end

end DetParityAutomaton

end DistributedSynthesis
