/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledOpenIndexedCorrelatedSemanticStep
import DistributedSynthesis.Formalizations.Lemma.LemCodedAlternatingIndexedLineageCodeLiveness
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledOpenIndexedBeliefThreadFlattening
import DistributedSynthesis.Formalizations.Lemma.LemSourceFreeBeliefCodeParityRationalization

/-!
# Parity of the recursive correlated semantic tree

A never-dead code-only lineage run determines one normalized literal survivor
at every depth.  Those survivors select the exact handoff members constructed
by the correlated semantic successor.  Consecutive members are stitched by
their common lane/lineage slot, yielding a genuine pointed semantic chain of
the original winning strategy.
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

variable [Fintype I]
variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
  [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

variable (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
variable (hwin : ∀ env : EnvironmentSequence In₁ In₂,
  A.Accepts (execution strategy env))
variable (basis : ∀ state : PairedProfiledTreeState A,
  (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)

/-- Semantic state at one branch depth. -/
noncomputable def profiledOpenIndexedCorrelatedBranchState
    (initial : ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin
      basis (I := I))
    (branch : Nat → ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)) (n : Nat) :=
  (profiledOpenIndexedCorrelatedSemanticTree A strategy hwin basis initial)
    |>.stateAt (branchNode branch n)

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Along the semantic tree, the child-code word is exactly the public
source-free successor at the preceding depth. -/
theorem profiledOpenIndexedCorrelated_childCodeWord_eq_next
    (initial : ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin
      basis (I := I))
    (branch : Nat → ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)) (n : Nat) :
    let raw := profiledOpenIndexedCorrelatedSemanticTree A strategy hwin basis
      initial
    raw.childCodeWord branch n =
      profiledOpenIndexedBiBeliefNext A
        ((profiledOpenIndexedCorrelatedBranchState A strategy hwin basis
          initial branch n).code A strategy hwin basis)
        ((profiledOpenIndexedCorrelatedBranchState A strategy hwin basis
          initial branch n).move A strategy hwin basis)
        (branch n) := by
  let raw := profiledOpenIndexedCorrelatedSemanticTree A strategy hwin basis
    initial
  change raw.code (raw.stateAt (branchNode branch (n + 1))) = _
  rw [show branchNode branch (n + 1) =
      branchNode branch n ++ [branch n] from rfl,
    raw.stateAt_append]
  exact profiledOpenIndexedCorrelatedSemanticNext_code A strategy hwin basis
    (profiledOpenIndexedCorrelatedBranchState A strategy hwin basis initial
      branch n) (branch n)

/-- The chosen positive-time live trace of one never-dead code-only hidden
lineage. -/
noncomputable def profiledOpenIndexedCorrelatedBranchLiveAt
    (initial : ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin
      basis (I := I))
    (branch : Nat → ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (initialSide : IndexedLineageSide) (lineage : I)
    (hnever : ∀ n,
      (codedAlternatingIndexedLineageCodeRun
        (initial.code A strategy hwin basis)
        (profiledOpenIndexedBiBeliefCurrentSlots A)
        ((profiledOpenIndexedCorrelatedSemanticTree A strategy hwin basis
          initial).childCodeWord branch) initialSide lineage (n + 1)).2 ≠
        .dead)
    (n : Nat) :=
  codedAlternatingIndexedLineageCodeLiveAtOfNeverDead
    (initial.code A strategy hwin basis)
    (profiledOpenIndexedBiBeliefCurrentSlots A)
    ((profiledOpenIndexedCorrelatedSemanticTree A strategy hwin basis initial)
      |>.childCodeWord branch)
    initialSide lineage hnever n

/-- One orientation-indexed literal survivor, including its exact persistent
lineage and monitored root. -/
inductive ProfiledOpenIndexedCorrelatedBranchSurvivorPackage
    (initial : ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin
      basis (I := I))
    (branch : Nat → ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (initialSide : IndexedLineageSide) (lineage : I)
    (hnever : ∀ n,
      (codedAlternatingIndexedLineageCodeRun
        (initial.code A strategy hwin basis)
        (profiledOpenIndexedBiBeliefCurrentSlots A)
        ((profiledOpenIndexedCorrelatedSemanticTree A strategy hwin basis
          initial).childCodeWord branch) initialSide lineage (n + 1)).2 ≠
        .dead)
    (n : Nat) : Type _ where
  | right
      (hside : (profiledOpenIndexedCorrelatedBranchLiveAt A strategy hwin
        basis initial branch initialSide lineage hnever n).side = .right)
      (survivor :
        (profiledOpenIndexedLeftRawChildCode A
          ((profiledOpenIndexedCorrelatedBranchState A strategy hwin basis
            initial branch n).code A strategy hwin basis)
          ((profiledOpenIndexedCorrelatedBranchState A strategy hwin basis
            initial branch n).move A strategy hwin basis)
          (branch n)).RootSurvivor)
      (lineage_eq : survivor.lineage = lineage)
      (root_eq : survivor.root =
        (profiledOpenIndexedCorrelatedBranchLiveAt A strategy hwin basis
          initial branch initialSide lineage hnever n).root)
  | left
      (hside : (profiledOpenIndexedCorrelatedBranchLiveAt A strategy hwin
        basis initial branch initialSide lineage hnever n).side = .left)
      (survivor :
        (profiledOpenIndexedRightRawChildCode A
          ((profiledOpenIndexedCorrelatedBranchState A strategy hwin basis
            initial branch n).code A strategy hwin basis)
          ((profiledOpenIndexedCorrelatedBranchState A strategy hwin basis
            initial branch n).move A strategy hwin basis)
          (branch n)).RootSurvivor)
      (lineage_eq : survivor.lineage = lineage)
      (root_eq : survivor.root =
        (profiledOpenIndexedCorrelatedBranchLiveAt A strategy hwin basis
          initial branch initialSide lineage hnever n).root)

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Every live code-only point materializes one normalized literal semantic
survivor with exactly the monitored root. -/
theorem exists_profiledOpenIndexedCorrelatedBranchSurvivor
    (initial : ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin
      basis (I := I))
    (branch : Nat → ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (initialSide : IndexedLineageSide) (lineage : I)
    (hnever : ∀ n,
      (codedAlternatingIndexedLineageCodeRun
        (initial.code A strategy hwin basis)
        (profiledOpenIndexedBiBeliefCurrentSlots A)
        ((profiledOpenIndexedCorrelatedSemanticTree A strategy hwin basis
          initial).childCodeWord branch) initialSide lineage (n + 1)).2 ≠
        .dead)
    (n : Nat) :
    Nonempty (ProfiledOpenIndexedCorrelatedBranchSurvivorPackage A strategy
      hwin basis initial branch initialSide lineage hnever n) := by
  classical
  let state := profiledOpenIndexedCorrelatedBranchState A strategy hwin basis
    initial branch n
  let live := profiledOpenIndexedCorrelatedBranchLiveAt A strategy hwin basis
    initial branch initialSide lineage hnever n
  have hnext := profiledOpenIndexedCorrelated_childCodeWord_eq_next A strategy
    hwin basis initial branch n
  cases hside : live.side with
  | right =>
      have hslot := live.slot
      rw [hside] at hslot
      simp only [profiledOpenIndexedBiBeliefCurrentSlots_right] at hslot
      rw [hnext] at hslot
      change (profiledOpenIndexedLeftChildCode A
          (state.code A strategy hwin basis)
          (state.move A strategy hwin basis) (branch n)).rootSlots lineage =
        some live.root at hslot
      rw [IndexedLineageChildCode.rootSlots_eq_some_iff] at hslot
      rcases hslot with ⟨row, hcode⟩
      let survivor :
          (profiledOpenIndexedLeftRawChildCode A
            (state.code A strategy hwin basis)
            (state.move A strategy hwin basis) (branch n)).RootSurvivor :=
        ⟨(lineage, (row, live.root)), hcode⟩
      exact ⟨ProfiledOpenIndexedCorrelatedBranchSurvivorPackage.right
        (A := A) hside survivor rfl rfl⟩
  | left =>
      have hslot := live.slot
      rw [hside] at hslot
      simp only [profiledOpenIndexedBiBeliefCurrentSlots_left] at hslot
      rw [hnext] at hslot
      change (profiledOpenIndexedRightChildCode A
          (state.code A strategy hwin basis)
          (state.move A strategy hwin basis) (branch n)).rootSlots lineage =
        some live.root at hslot
      rw [IndexedLineageChildCode.rootSlots_eq_some_iff] at hslot
      rcases hslot with ⟨row, hcode⟩
      let survivor :
          (profiledOpenIndexedRightRawChildCode A
            (state.code A strategy hwin basis)
            (state.move A strategy hwin basis) (branch n)).RootSurvivor :=
        ⟨(lineage, (row, live.root)), hcode⟩
      exact ⟨ProfiledOpenIndexedCorrelatedBranchSurvivorPackage.left
        (A := A) hside survivor rfl rfl⟩

/-- Canonically choose the literal survivor package at one live depth. -/
noncomputable def profiledOpenIndexedCorrelatedBranchSurvivorPackage
    (initial : ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin
      basis (I := I))
    (branch : Nat → ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (initialSide : IndexedLineageSide) (lineage : I)
    (hnever : ∀ n,
      (codedAlternatingIndexedLineageCodeRun
        (initial.code A strategy hwin basis)
        (profiledOpenIndexedBiBeliefCurrentSlots A)
        ((profiledOpenIndexedCorrelatedSemanticTree A strategy hwin basis
          initial).childCodeWord branch) initialSide lineage (n + 1)).2 ≠
        .dead)
    (n : Nat) :
    ProfiledOpenIndexedCorrelatedBranchSurvivorPackage A strategy hwin basis
      initial branch initialSide lineage hnever n :=
  Classical.choice (exists_profiledOpenIndexedCorrelatedBranchSurvivor A
    strategy hwin basis initial branch initialSide lineage hnever n)

/-- Literal pointed semantic memory selected at positive monitor depth
`n + 1`. -/
noncomputable def profiledOpenIndexedCorrelatedBranchPointedState
    (initial : ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin
      basis (I := I))
    (branch : Nat → ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (initialSide : IndexedLineageSide) (lineage : I)
    (hnever : ∀ n,
      (codedAlternatingIndexedLineageCodeRun
        (initial.code A strategy hwin basis)
        (profiledOpenIndexedBiBeliefCurrentSlots A)
        ((profiledOpenIndexedCorrelatedSemanticTree A strategy hwin basis
          initial).childCodeWord branch) initialSide lineage (n + 1)).2 ≠
        .dead)
    (n : Nat) : ProfiledOpenPointedSemanticState A strategy hwin basis :=
  match profiledOpenIndexedCorrelatedBranchSurvivorPackage A strategy hwin
      basis initial branch initialSide lineage hnever n with
  | .right _ survivor _ _ =>
      let state := profiledOpenIndexedCorrelatedBranchState A strategy hwin
        basis initial branch n
      let handoff := profiledOpenIndexedLeftToRightHandoffOfSurvivor A strategy
        hwin basis state (branch n) survivor
      .right {
        realization := handoff.child.realization
        selected := handoff.childMember survivor
        actualEntry := handoff.child.realization.entry
          (handoff.childMember survivor)
        actualMinimum := handoff.child.realization.minimum
          (handoff.childMember survivor)
        entry_selected := rfl
        minimum_selected := rfl }
  | .left _ survivor _ _ =>
      let state := profiledOpenIndexedCorrelatedBranchState A strategy hwin
        basis initial branch n
      let handoff := profiledOpenIndexedRightToLeftHandoffOfSurvivor A strategy
        hwin basis state (branch n) survivor
      .left {
        realization := handoff.child.realization
        selected := handoff.childMember survivor
        actualEntry := handoff.child.realization.entry
          (handoff.childMember survivor)
        actualMinimum := handoff.child.realization.minimum
          (handoff.childMember survivor)
        entry_selected := rfl
        minimum_selected := rfl }

/-- The raw operational direction joining pointed depths `n` and `n + 1` is
the literal recovered direction of the latter handoff. -/
noncomputable def profiledOpenIndexedCorrelatedBranchRecoveredDirection
    (initial : ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin
      basis (I := I))
    (branch : Nat → ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (initialSide : IndexedLineageSide) (lineage : I)
    (hnever : ∀ n,
      (codedAlternatingIndexedLineageCodeRun
        (initial.code A strategy hwin basis)
        (profiledOpenIndexedBiBeliefCurrentSlots A)
        ((profiledOpenIndexedCorrelatedSemanticTree A strategy hwin basis
          initial).childCodeWord branch) initialSide lineage (n + 1)).2 ≠
        .dead)
    (n : Nat) : PairedEntryDirection (In₁ := In₁) (In₂ := In₂) :=
  match profiledOpenIndexedCorrelatedBranchSurvivorPackage A strategy hwin
      basis initial branch initialSide lineage hnever (n + 1) with
  | .right _ survivor _ _ =>
      let state := profiledOpenIndexedCorrelatedBranchState A strategy hwin
        basis initial branch (n + 1)
      let handoff := profiledOpenIndexedLeftToRightHandoffOfSurvivor A strategy
        hwin basis state (branch (n + 1)) survivor
      .fromTwo survivor.row handoff.semanticPast (branch (n + 1)).leftInput
  | .left _ survivor _ _ =>
      let state := profiledOpenIndexedCorrelatedBranchState A strategy hwin
        basis initial branch (n + 1)
      let handoff := profiledOpenIndexedRightToLeftHandoffOfSurvivor A strategy
        hwin basis state (branch (n + 1)) survivor
      .fromOne survivor.row handoff.semanticPast (branch (n + 1)).rightInput

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Branch semantic states recurse by the total correlated successor. -/
theorem profiledOpenIndexedCorrelatedBranchState_succ
    (initial : ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin
      basis (I := I))
    (branch : Nat → ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)) (n : Nat) :
    profiledOpenIndexedCorrelatedBranchState A strategy hwin basis initial
        branch (n + 1) =
      profiledOpenIndexedCorrelatedSemanticNext A strategy hwin basis
        (profiledOpenIndexedCorrelatedBranchState A strategy hwin basis
          initial branch n) (branch n) := by
  unfold profiledOpenIndexedCorrelatedBranchState
  rw [show branchNode branch (n + 1) =
      branchNode branch n ++ [branch n] from rfl]
  exact SourceFreeBeliefSemanticTree.stateAt_append _ _ _

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- The pointed semantic priority is exactly the finite root priority read by
the never-dead code-only monitor. -/
theorem profiledOpenIndexedCorrelatedBranchPointedState_priority
    (initial : ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin
      basis (I := I))
    (branch : Nat → ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (initialSide : IndexedLineageSide) (lineage : I)
    (hnever : ∀ n,
      (codedAlternatingIndexedLineageCodeRun
        (initial.code A strategy hwin basis)
        (profiledOpenIndexedBiBeliefCurrentSlots A)
        ((profiledOpenIndexedCorrelatedSemanticTree A strategy hwin basis
          initial).childCodeWord branch) initialSide lineage (n + 1)).2 ≠
        .dead)
    (n : Nat) :
    (profiledOpenIndexedCorrelatedBranchPointedState A strategy hwin basis
      initial branch initialSide lineage hnever n).priority A =
      profiledOpenIndexedRootPriority A
        (profiledOpenIndexedCorrelatedBranchLiveAt A strategy hwin basis
          initial branch initialSide lineage hnever n).root := by
  classical
  cases hpackage :
      profiledOpenIndexedCorrelatedBranchSurvivorPackage A strategy hwin basis
        initial branch initialSide lineage hnever n with
  | right hside survivor hlineage hroot =>
      let state := profiledOpenIndexedCorrelatedBranchState A strategy hwin
        basis initial branch n
      let handoff := profiledOpenIndexedLeftToRightHandoffOfSurvivor A strategy
        hwin basis state (branch n) survivor
      have hanchor :=
        profiledOpenIndexedLeftToRightHandoffOfSurvivor_child_anchor A strategy
          hwin basis state (branch n) survivor
      simp only [profiledOpenIndexedCorrelatedBranchPointedState, hpackage,
        ProfiledOpenPointedSemanticState.priority,
        ProfiledOpenPointedSemanticState.anchor,
        profiledOpenIndexedRootPriority]
      exact congrArg (profiledOpenClassifiedAnchorPriority A)
        (hanchor.trans hroot)
  | left hside survivor hlineage hroot =>
      let state := profiledOpenIndexedCorrelatedBranchState A strategy hwin
        basis initial branch n
      let handoff := profiledOpenIndexedRightToLeftHandoffOfSurvivor A strategy
        hwin basis state (branch n) survivor
      have hanchor :=
        profiledOpenIndexedRightToLeftHandoffOfSurvivor_child_anchor A strategy
          hwin basis state (branch n) survivor
      simp only [profiledOpenIndexedCorrelatedBranchPointedState, hpackage,
        ProfiledOpenPointedSemanticState.priority,
        ProfiledOpenPointedSemanticState.anchor,
        profiledOpenIndexedRootPriority]
      exact congrArg (profiledOpenClassifiedAnchorPriority A)
        (hanchor.trans hroot)

omit [Fintype I] [Inhabited Out₁] [Inhabited Out₂] in
/-- Transport a selected process-one memory across equality of two semantic
right lanes, using the common persistent-lineage slot. -/
theorem profiledOpenIndexedRightLane_memory_eq_of_memberAt
    (left right : ProfiledOpenIndexedRightSemanticLane A strategy hwin basis
      (I := I))
    (hLane : left = right) (lineage : I)
    (leftMember : {root // root ∈ left.source.1})
    (rightMember : {root // root ∈ right.source.1})
    (hleft : left.memberAt lineage = some leftMember)
    (hright : right.memberAt lineage = some rightMember) :
    PairedStrategyMemory.processOne
        (left.realization.entry leftMember)
        (left.realization.minimum leftMember) =
      PairedStrategyMemory.processOne
        (right.realization.entry rightMember)
        (right.realization.minimum rightMember) := by
  cases hLane
  have hMember : leftMember = rightMember :=
    Option.some.inj (hleft.symm.trans hright)
  cases hMember
  rfl

omit [Fintype I] [Inhabited Out₁] [Inhabited Out₂] in
/-- Process-two mirror of selected-lane memory transport. -/
theorem profiledOpenIndexedLeftLane_memory_eq_of_memberAt
    (left right : ProfiledOpenIndexedLeftSemanticLane A strategy hwin basis
      (I := I))
    (hLane : left = right) (lineage : I)
    (leftMember : {root // root ∈ left.source.1})
    (rightMember : {root // root ∈ right.source.1})
    (hleft : left.memberAt lineage = some leftMember)
    (hright : right.memberAt lineage = some rightMember) :
    PairedStrategyMemory.processTwo
        (left.realization.entry leftMember)
        (left.realization.minimum leftMember) =
      PairedStrategyMemory.processTwo
        (right.realization.entry rightMember)
        (right.realization.minimum rightMember) := by
  cases hLane
  have hMember : leftMember = rightMember :=
    Option.some.inj (hleft.symm.trans hright)
  cases hMember
  rfl

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Consecutive survivor-selected pointed states are literal operational
successors.  The proof identifies the previous handoff's child member with
the next handoff's source member through their common lane and persistent
lineage; no equal-root representative is reselected. -/
theorem profiledOpenIndexedCorrelatedBranchPointedState_memory_step
    (initial : ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin
      basis (I := I))
    (branch : Nat → ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (initialSide : IndexedLineageSide) (lineage : I)
    (hnever : ∀ n,
      (codedAlternatingIndexedLineageCodeRun
        (initial.code A strategy hwin basis)
        (profiledOpenIndexedBiBeliefCurrentSlots A)
        ((profiledOpenIndexedCorrelatedSemanticTree A strategy hwin basis
          initial).childCodeWord branch) initialSide lineage (n + 1)).2 ≠
        .dead)
    (n : Nat) :
    (profiledOpenIndexedCorrelatedBranchPointedState A strategy hwin basis
      initial branch initialSide lineage hnever (n + 1)).memory A =
      PairedStrategyMemory.step (A := A)
        ((profiledOpenIndexedCorrelatedBranchPointedState A strategy hwin
          basis initial branch initialSide lineage hnever n).memory A)
        (profiledOpenIndexedCorrelatedBranchRecoveredDirection A strategy hwin
          basis initial branch initialSide lineage hnever n) := by
  classical
  have hflip :=
    codedAlternatingIndexedLineageCodeLiveAtOfNeverDead_side_succ
      (initial.code A strategy hwin basis)
      (profiledOpenIndexedBiBeliefCurrentSlots A)
      ((profiledOpenIndexedCorrelatedSemanticTree A strategy hwin basis
        initial).childCodeWord branch)
      initialSide lineage hnever n
  change
    (profiledOpenIndexedCorrelatedBranchLiveAt A strategy hwin basis initial
      branch initialSide lineage hnever (n + 1)).side =
      (profiledOpenIndexedCorrelatedBranchLiveAt A strategy hwin basis initial
        branch initialSide lineage hnever n).side.other at hflip
  cases hpkg :
      profiledOpenIndexedCorrelatedBranchSurvivorPackage A strategy hwin basis
        initial branch initialSide lineage hnever n with
  | right hpSide pSurvivor hpLine hpRoot =>
      cases qpkg :
          profiledOpenIndexedCorrelatedBranchSurvivorPackage A strategy hwin
            basis initial branch initialSide lineage hnever (n + 1) with
      | right hqSide qSurvivor hqLine hqRoot =>
          rw [hpSide, hqSide] at hflip
          cases hflip
      | left hqSide qSurvivor hqLine hqRoot =>
          let pState := profiledOpenIndexedCorrelatedBranchState A strategy
            hwin basis initial branch n
          let pHandoff :=
            profiledOpenIndexedLeftToRightHandoffOfSurvivor A strategy hwin
              basis pState (branch n) pSurvivor
          let qState := profiledOpenIndexedCorrelatedBranchState A strategy
            hwin basis initial branch (n + 1)
          let qNonempty : Nonempty
              (profiledOpenIndexedRightRawChildCode A
                (qState.code A strategy hwin basis)
                (qState.move A strategy hwin basis)
                (branch (n + 1))).RootSurvivor := ⟨qSurvivor⟩
          let qLane := profiledOpenIndexedRightLaneOfSurvivor A strategy hwin
            basis qState (branch (n + 1)) qNonempty
          have hpChild : qState.right = some pHandoff.child := by
            dsimp only [qState]
            rw [profiledOpenIndexedCorrelatedBranchState_succ A strategy hwin
              basis initial branch n]
            simpa only [pState] using
              profiledOpenIndexedCorrelatedSemanticNext_right_eq_child A
                strategy hwin basis pState (branch n) pSurvivor
          have hqSource : qState.right = some qLane := by
            exact profiledOpenIndexedRightLaneOfSurvivor_spec A strategy hwin
              basis qState (branch (n + 1)) qNonempty
          have hLane : pHandoff.child = qLane :=
            Option.some.inj (hpChild.symm.trans hqSource)
          let qHandoff :=
            profiledOpenIndexedRightToLeftHandoffOfSurvivor A strategy hwin
              basis qState (branch (n + 1)) qSurvivor
          have hpAt : pHandoff.child.memberAt lineage =
              some (pHandoff.childMember pSurvivor) := by
            rw [← hpLine]
            exact pHandoff.childMember_at pSurvivor
          have hqAt : qLane.memberAt lineage =
              some (qHandoff.sourceMember qSurvivor) := by
            rw [← hqLine]
            exact qHandoff.sourceMember_at qSurvivor
          have hMemory :=
            profiledOpenIndexedRightLane_memory_eq_of_memberAt A strategy hwin
              basis pHandoff.child qLane hLane lineage
              (pHandoff.childMember pSurvivor)
              (qHandoff.sourceMember qSurvivor) hpAt hqAt
          have hstep := qHandoff.memory_step qSurvivor
          simp only [profiledOpenIndexedCorrelatedBranchPointedState, hpkg,
            qpkg, profiledOpenIndexedCorrelatedBranchRecoveredDirection,
            ProfiledOpenPointedSemanticState.memory]
          rw [hMemory]
          exact hstep.symm
  | left hpSide pSurvivor hpLine hpRoot =>
      cases qpkg :
          profiledOpenIndexedCorrelatedBranchSurvivorPackage A strategy hwin
            basis initial branch initialSide lineage hnever (n + 1) with
      | left hqSide qSurvivor hqLine hqRoot =>
          rw [hpSide, hqSide] at hflip
          cases hflip
      | right hqSide qSurvivor hqLine hqRoot =>
          let pState := profiledOpenIndexedCorrelatedBranchState A strategy
            hwin basis initial branch n
          let pHandoff :=
            profiledOpenIndexedRightToLeftHandoffOfSurvivor A strategy hwin
              basis pState (branch n) pSurvivor
          let qState := profiledOpenIndexedCorrelatedBranchState A strategy
            hwin basis initial branch (n + 1)
          let qNonempty : Nonempty
              (profiledOpenIndexedLeftRawChildCode A
                (qState.code A strategy hwin basis)
                (qState.move A strategy hwin basis)
                (branch (n + 1))).RootSurvivor := ⟨qSurvivor⟩
          let qLane := profiledOpenIndexedLeftLaneOfSurvivor A strategy hwin
            basis qState (branch (n + 1)) qNonempty
          have hpChild : qState.left = some pHandoff.child := by
            dsimp only [qState]
            rw [profiledOpenIndexedCorrelatedBranchState_succ A strategy hwin
              basis initial branch n]
            simpa only [pState] using
              profiledOpenIndexedCorrelatedSemanticNext_left_eq_child A
                strategy hwin basis pState (branch n) pSurvivor
          have hqSource : qState.left = some qLane := by
            exact profiledOpenIndexedLeftLaneOfSurvivor_spec A strategy hwin
              basis qState (branch (n + 1)) qNonempty
          have hLane : pHandoff.child = qLane :=
            Option.some.inj (hpChild.symm.trans hqSource)
          let qHandoff :=
            profiledOpenIndexedLeftToRightHandoffOfSurvivor A strategy hwin
              basis qState (branch (n + 1)) qSurvivor
          have hpAt : pHandoff.child.memberAt lineage =
              some (pHandoff.childMember pSurvivor) := by
            rw [← hpLine]
            exact pHandoff.childMember_at pSurvivor
          have hqAt : qLane.memberAt lineage =
              some (qHandoff.sourceMember qSurvivor) := by
            rw [← hqLine]
            exact qHandoff.sourceMember_at qSurvivor
          have hMemory :=
            profiledOpenIndexedLeftLane_memory_eq_of_memberAt A strategy hwin
              basis pHandoff.child qLane hLane lineage
              (pHandoff.childMember pSurvivor)
              (qHandoff.sourceMember qSurvivor) hpAt hqAt
          have hstep := qHandoff.memory_step qSurvivor
          simp only [profiledOpenIndexedCorrelatedBranchPointedState, hpkg,
            qpkg, profiledOpenIndexedCorrelatedBranchRecoveredDirection,
            ProfiledOpenPointedSemanticState.memory]
          rw [hMemory]
          exact hstep.symm

/-- The complete literal pointed chain selected by a never-dead code-only
lineage. -/
noncomputable def profiledOpenIndexedCorrelatedBranchSemanticChain
    (initial : ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin
      basis (I := I))
    (branch : Nat → ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (initialSide : IndexedLineageSide) (lineage : I)
    (hnever : ∀ n,
      (codedAlternatingIndexedLineageCodeRun
        (initial.code A strategy hwin basis)
        (profiledOpenIndexedBiBeliefCurrentSlots A)
        ((profiledOpenIndexedCorrelatedSemanticTree A strategy hwin basis
          initial).childCodeWord branch) initialSide lineage (n + 1)).2 ≠
        .dead) :
    ProfiledOpenPointedSemanticChain A strategy hwin basis where
  state := profiledOpenIndexedCorrelatedBranchPointedState A strategy hwin
    basis initial branch initialSide lineage hnever
  direction := profiledOpenIndexedCorrelatedBranchRecoveredDirection A
    strategy hwin basis initial branch initialSide lineage hnever
  memory_step := profiledOpenIndexedCorrelatedBranchPointedState_memory_step A
    strategy hwin basis initial branch initialSide lineage hnever

section
omit [Inhabited Out₁] [Inhabited Out₂]

/-- At every positive time of a never-dead code-only run, the monitor
priority is exactly the pointed-chain priority. -/
theorem profiledOpenIndexedCorrelatedBranch_live_priority
    (initial : ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin
      basis (I := I))
    (branch : Nat → ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂))
    (initialSide : IndexedLineageSide) (lineage : I)
    (hnever : ∀ n,
      (codedAlternatingIndexedLineageCodeRun
        (initial.code A strategy hwin basis)
        (profiledOpenIndexedBiBeliefCurrentSlots A)
        ((profiledOpenIndexedCorrelatedSemanticTree A strategy hwin basis
          initial).childCodeWord branch) initialSide lineage (n + 1)).2 ≠
        .dead)
    (n : Nat) :
    (codedAlternatingIndexedLineageCodeThreadSystem
        (initial.code A strategy hwin basis)
        (profiledOpenIndexedBiBeliefCurrentSlots A)
        (profiledOpenIndexedRootPriority A)).priority
      (codedAlternatingIndexedLineageCodeRun
        (initial.code A strategy hwin basis)
        (profiledOpenIndexedBiBeliefCurrentSlots A)
        ((profiledOpenIndexedCorrelatedSemanticTree A strategy hwin basis
          initial).childCodeWord branch) initialSide lineage (n + 1)) =
      ((profiledOpenIndexedCorrelatedBranchSemanticChain A strategy hwin basis
        initial branch initialSide lineage hnever).state n).priority A := by
  let live := profiledOpenIndexedCorrelatedBranchLiveAt A strategy hwin basis
    initial branch initialSide lineage hnever n
  rw [live.run_eq]
  change profiledOpenIndexedRootPriority A live.root = _
  exact (profiledOpenIndexedCorrelatedBranchPointedState_priority A strategy
    hwin basis initial branch initialSide lineage hnever n).symm

/-- Every branch of the recursive correlated semantic tree is accepted by
the finite child-code parity monitor. -/
theorem profiledOpenIndexedCorrelatedSemanticTree_codeDPA_accepts
    (initial : ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin
      basis (I := I))
    (branch : Nat → ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)) :
    (codedAlternatingIndexedLineageCodeDPA
        (initial.code A strategy hwin basis)
        (profiledOpenIndexedBiBeliefCurrentSlots A)
        (profiledOpenIndexedRootPriority A)).Accepts
      ((profiledOpenIndexedCorrelatedSemanticTree A strategy hwin basis
        initial).childCodeWord branch) := by
  classical
  let word :=
    (profiledOpenIndexedCorrelatedSemanticTree A strategy hwin basis initial)
      |>.childCodeWord branch
  rw [codedAlternatingIndexedLineageCodeDPA_accepts_iff]
  intro initialSide lineage
  by_cases hdead : ∃ n,
      (codedAlternatingIndexedLineageCodeRun
        (initial.code A strategy hwin basis)
        (profiledOpenIndexedBiBeliefCurrentSlots A) word initialSide lineage
        n).2 = .dead
  · rcases hdead with ⟨n, hdead⟩
    have hparity := codedAlternatingIndexedLineageRun_minEven_of_eventually_dead
      (initial.code A strategy hwin basis)
      (fun _ (_ : Unit) childCode => childCode)
      (profiledOpenIndexedBiBeliefCurrentSlots A)
      (codedAlternatingIndexedLineageCodeChild
        (profiledOpenIndexedBiBeliefCurrentSlots A))
      (profiledOpenIndexedRootPriority A)
      (fun k => (Unit.unit, word k)) initialSide lineage hdead
    simpa [codedAlternatingIndexedLineageCodeThreadSystem,
      codedAlternatingIndexedLineageCodeRun] using hparity
  · have hnever : ∀ n,
        (codedAlternatingIndexedLineageCodeRun
          (initial.code A strategy hwin basis)
          (profiledOpenIndexedBiBeliefCurrentSlots A) word initialSide lineage
          (n + 1)).2 ≠ .dead := by
      intro n hnow
      exact hdead ⟨n + 1, hnow⟩
    let priorities := fun n =>
      (codedAlternatingIndexedLineageCodeThreadSystem
          (initial.code A strategy hwin basis)
          (profiledOpenIndexedBiBeliefCurrentSlots A)
          (profiledOpenIndexedRootPriority A)).priority
        (codedAlternatingIndexedLineageCodeRun
          (initial.code A strategy hwin basis)
          (profiledOpenIndexedBiBeliefCurrentSlots A) word initialSide lineage
          n)
    let chain := profiledOpenIndexedCorrelatedBranchSemanticChain A strategy
      hwin basis initial branch initialSide lineage hnever
    have hsemantic := chain.minEven A hwin basis
    have htail : NatSeqMinEvenParity (fun n => priorities (1 + n)) := by
      convert hsemantic using 1
      funext n
      simpa [priorities, chain, word, Nat.add_comm] using
        profiledOpenIndexedCorrelatedBranch_live_priority A strategy hwin basis
          initial branch initialSide lineage hnever n
    exact (natSeqMinEvenParity_shift priorities 1).mp htail

/-- The complete unconditional child-code parity certificate for the
recursive correlated semantic tree. -/
theorem profiledOpenIndexedCorrelatedSemanticTree_codeParityCertificate
    (initial : ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin
      basis (I := I)) :
    let raw := profiledOpenIndexedCorrelatedSemanticTree A strategy hwin basis
      initial
    SourceFreeBeliefCodeParityCertificate
      (codedAlternatingIndexedLineageCodeDPA
        (initial.code A strategy hwin basis)
        (profiledOpenIndexedBiBeliefCurrentSlots A)
        (profiledOpenIndexedRootPriority A))
      (initial.code A strategy hwin basis)
      (ProfiledOpenIndexedBiBeliefValid A)
      (profiledOpenIndexedBiBeliefNext A) raw := by
  let raw := profiledOpenIndexedCorrelatedSemanticTree A strategy hwin basis
    initial
  refine {
    initial_code := rfl
    valid := ?_
    next_code := ?_
    accepts := ?_ }
  · intro node
    exact profiledOpenIndexedCorrelatedSemanticTree_valid A strategy hwin basis
      initial node
  · intro node direction
    exact profiledOpenIndexedCorrelatedSemanticTree_next_code A strategy hwin
      basis initial node direction
  · intro branch
    exact profiledOpenIndexedCorrelatedSemanticTree_codeDPA_accepts A strategy
      hwin basis initial branch

/-- Applying the repository's arbitrary-direction rational-run interface to
the now complete correlated certificate yields one finite code-observable
transition policy.  The basis is kept explicit because the raw direction
contains unbounded tagged-past lists; the finite-direction specialization is
therefore not applicable at this presentation layer. -/
theorem nonempty_profiledOpenIndexedCorrelatedCodeParityRationalPolicy
    (initial : ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin
      basis (I := I))
    (rationalBasis :
      (sourceFreeBeliefCodeParityRunAutomaton
        (codedAlternatingIndexedLineageCodeDPA
          (initial.code A strategy hwin basis)
          (profiledOpenIndexedBiBeliefCurrentSlots A)
          (profiledOpenIndexedRootPriority A))
        (initial.code A strategy hwin basis)
        (ProfiledOpenIndexedBiBeliefValid A)
        (profiledOpenIndexedBiBeliefNext A)).RationalRunBasis) :
    Nonempty (SourceFreeBeliefCodeParityRationalPolicy
      (codedAlternatingIndexedLineageCodeDPA
        (initial.code A strategy hwin basis)
        (profiledOpenIndexedBiBeliefCurrentSlots A)
        (profiledOpenIndexedRootPriority A))
      (initial.code A strategy hwin basis)
      (ProfiledOpenIndexedBiBeliefValid A)
      (profiledOpenIndexedBiBeliefNext A)) := by
  let raw := profiledOpenIndexedCorrelatedSemanticTree A strategy hwin basis
    initial
  exact SourceFreeBeliefCodeParityCertificate.nonempty_rationalPolicy
    (codedAlternatingIndexedLineageCodeDPA
      (initial.code A strategy hwin basis)
      (profiledOpenIndexedBiBeliefCurrentSlots A)
      (profiledOpenIndexedRootPriority A))
    (initial.code A strategy hwin basis)
    (ProfiledOpenIndexedBiBeliefValid A)
    (profiledOpenIndexedBiBeliefNext A) raw
    (profiledOpenIndexedCorrelatedSemanticTree_codeParityCertificate A
      strategy hwin basis initial)
    rationalBasis

end

end

end DetParityAutomaton

end DistributedSynthesis
