/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralBranchAwareStageLiveness

/-!
# Physical priority retained by a branch-aware literal stage

The heterogeneous seam receiver selects one of its two finite table members
using the member bit already stored in the table state.  Both members carry a
live target slot whose thread priority is the minimum priority of that same
member's literal physical prefix.  This file transports the active slot
through `StageOfChild`: the finite stage retained by the receiver has the same
slot, and hence the same physical block priority.

All case splits below are proof-side splits on the stored member.  No
executable transition receives a graph, orientation, leader bit, hierarchy
side, history, or semantic view.
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

private abbrev CommonPoint :=
  ProfiledRawJointGuardedCommonSemanticPoint A strategy

private abbrev CrossValid :=
  ProfiledRawJointGuardedCommonLiteralCrossExtraValid A strategy hwin

namespace ProfiledRawJointGuardedCommonDecoratedPolicyPackage

variable {initial : CommonPoint A strategy}

private abbrev Package :=
  ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy hwin initial
    (CrossValid A strategy hwin)

/-- The literal block priority named by the internally selected member of a
right-seam table. -/
def literalRightSeamSelectedTableBlockPriority
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (anchor : Bool) (env : Nat → In₁ × In₂) (n : Nat)
    (row : PairedEntryRow) : Nat :=
  if anchor then
    A.priority
      (blockMinState A
        (pairedCodeStateForRow A row
          (installed.world.procTwoSlot A).1.1)
        (profiledRawJointGuardedFirstLeftPhysicalPrefixRecords A row
          (omegaPrefix
            (profiledRawJointLiteralRightBothExactTruePlay A strategy hwin
              installed env) n)))
  else
    A.priority
      (blockMinState A
        (pairedCodeStateForRow A row
          (profiledRawJointHybridExactLeftUniformDescriptor A strategy hwin
            installed).source.1.1)
        (profiledRawJointTargetLeftPhysicalPrefixRecords A row
          (omegaPrefix
            (profiledRawJointLiteralRightBothExactFalsePlay A strategy hwin
              installed env) n)))

/-- Mirror selected-member block priority. -/
def literalLeftSeamSelectedTableBlockPriority
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (anchor : Bool) (env : Nat → In₂ × In₁) (n : Nat)
    (row : PairedEntryRow) : Nat :=
  if anchor then
    A.priority
      (blockMinState A
        (pairedCodeStateForRow A row
          (installed.world.procOneSlot A).1.1)
        (profiledRawJointGuardedFirstRightPhysicalPrefixRecords A row
          (omegaPrefix
            (profiledRawJointLiteralLeftBothExactTruePlay A strategy hwin
              installed env) n)))
  else
    A.priority
      (blockMinState A
        (pairedCodeStateForRow A row
          (profiledRawJointHybridExactRightUniformDescriptor A strategy hwin
            installed).source.1.1)
        (profiledRawJointTargetRightPhysicalPrefixRecords A row
          (omegaPrefix
            (profiledRawJointLiteralLeftBothExactFalsePlay A strategy hwin
              installed env) n)))

/-- Target incidence code at one row of the selected right-table member. -/
def literalRightSeamSelectedTableTargetCode
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (anchor : Bool) (env : Nat → In₁ × In₂) (n : Nat)
    (row : PairedEntryRow) : ProfiledRawJointIncidenceCode A (I := Unit) :=
  if anchor then
    ((profiledRawJointLiteralRightBothExactTruePlay A strategy hwin installed
      env n).2.1.target row).1
  else
    (profiledRawJointLiteralRightBothExactFalsePlay A strategy hwin installed
      env n).2.1.target row

/-- Mirror target incidence code. -/
def literalLeftSeamSelectedTableTargetCode
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (anchor : Bool) (env : Nat → In₂ × In₁) (n : Nat)
    (row : PairedEntryRow) : ProfiledRawJointIncidenceCode A (I := Unit) :=
  if anchor then
    ((profiledRawJointLiteralLeftBothExactTruePlay A strategy hwin installed
      env n).2.1.target row).1
  else
    (profiledRawJointLiteralLeftBothExactFalsePlay A strategy hwin installed
      env n).2.1.target row

/-- Receiver-only proof-side reachability for the mirror table. -/
def LiteralLeftSeamReceiverTableLocallyReachable
    (package : Package A strategy hwin (initial := initial))
    (receiver :
      ProfiledRawJointGuardedCommonLiteralLeftSeamStagedReceiverState A
        strategy hwin package) : Prop :=
  ∃ sender : ProfiledRawJointLiteralLeftBothExactSenderState A strategy hwin
      (package.literalLeftSeamInstalled A strategy hwin receiver.1),
    FiniteCrossAnchorLocallyReachable
      (profiledRawJointLiteralLeftBothExactHeterogeneousRightTable A strategy
        hwin (package.literalLeftSeamInstalled A strategy hwin receiver.1))
      sender receiver.2.2.1

/-! ## Direct `.both` targets of the physical table members -/

/-- Every selected right-table member carries a live `.both` target whose
thread priority is the minimum of that member's `.both` physical prefix.
This is the parity-facing fact used by the phase-live controller: its actual
receiver output always reads `informedBoth`, even when the stored member (and
the retained stage row) is `false`/`.first`. -/
theorem exists_literalRightSeamSelectedTable_bothTargetPriority_eq_blockMin
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (anchor : Bool) (env : Nat → In₁ × In₂) (n : Nat) :
    ∃ slot : ProfiledRawRightSlot A,
      (literalRightSeamSelectedTableTargetCode A strategy hwin installed
        anchor env n .both).family.right () = some slot ∧
      profiledRawJointThreadRootPriority A (.inl slot) =
        literalRightSeamSelectedTableBlockPriority A strategy hwin installed
          anchor env n .both := by
  cases hanchor : anchor
  · obtain ⟨slot, hslot, hpriority⟩ :=
      exists_profiledRawJointLiteralRightBothExactFalsePlay_targetThreadPriority_eq_blockMin
        A strategy hwin installed env n .both
    refine ⟨slot, ?_, ?_⟩
    · simpa [literalRightSeamSelectedTableTargetCode, hanchor] using hslot
    · simpa [literalRightSeamSelectedTableBlockPriority, hanchor] using
        hpriority
  · obtain ⟨slot, hslot, hpriority⟩ :=
      exists_profiledRawJointLiteralRightBothExactTruePlay_targetThreadPriority_eq_blockMin
        A strategy hwin installed env n .both
    refine ⟨slot, ?_, ?_⟩
    · simpa [literalRightSeamSelectedTableTargetCode, hanchor] using hslot
    · simpa [literalRightSeamSelectedTableBlockPriority, hanchor] using
        hpriority

/-- Mirror direct `.both` target law. -/
theorem exists_literalLeftSeamSelectedTable_bothTargetPriority_eq_blockMin
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (anchor : Bool) (env : Nat → In₂ × In₁) (n : Nat) :
    ∃ slot : ProfiledRawLeftSlot A,
      (literalLeftSeamSelectedTableTargetCode A strategy hwin installed anchor
        env n .both).family.left () = some slot ∧
      profiledRawJointThreadRootPriority A (.inr slot) =
        literalLeftSeamSelectedTableBlockPriority A strategy hwin installed
          anchor env n .both := by
  cases hanchor : anchor
  · obtain ⟨slot, hslot, hpriority⟩ :=
      exists_profiledRawJointLiteralLeftBothExactFalsePlay_targetThreadPriority_eq_blockMin
        A strategy hwin installed env n .both
    refine ⟨slot, ?_, ?_⟩
    · simpa [literalLeftSeamSelectedTableTargetCode, hanchor] using hslot
    · simpa [literalLeftSeamSelectedTableBlockPriority, hanchor] using
        hpriority
  · obtain ⟨slot, hslot, hpriority⟩ :=
      exists_profiledRawJointLiteralLeftBothExactTruePlay_targetThreadPriority_eq_blockMin
        A strategy hwin installed env n .both
    refine ⟨slot, ?_, ?_⟩
    · simpa [literalLeftSeamSelectedTableTargetCode, hanchor] using hslot
    · simpa [literalLeftSeamSelectedTableBlockPriority, hanchor] using
        hpriority

/-! ## `StageOfChild` preserves the unique live slot -/

/-- The right stage reconstructed from a live child retains that child's
unique live slot. -/
theorem literalRightSeamStageOfChild_root_slot_eq
    (package : Package A strategy hwin (initial := initial))
    (row : PairedEntryRow)
    (child :
      ProfiledRawJointGuardedCommonLiteralRightSeamTaggedChildCode A strategy
        hwin package)
    (stage : ProfiledRawJointGuardedCommonLiteralRightSeamStage A strategy
      hwin package)
    (hstage : package.literalRightSeamStageOfChild A strategy hwin row child =
      some stage)
    (slot : ProfiledRawRightSlot A)
    (hlive : child.2.1.family.right () = some slot) :
    stage.root.slot = slot := by
  classical
  simp only [literalRightSeamStageOfChild] at hstage
  split at hstage
  · rename_i hex
    have hchosen := Classical.choose_spec hex
    have hslot : Classical.choose hex = slot :=
      Option.some.inj (hchosen.symm.trans hlive)
    have hstageEq := Option.some.inj hstage
    rw [← hstageEq]
    exact hslot
  · contradiction

/-- Mirror slot preservation for a retained left stage. -/
theorem literalLeftSeamStageOfChild_root_slot_eq
    (package : Package A strategy hwin (initial := initial))
    (row : PairedEntryRow)
    (child :
      ProfiledRawJointGuardedCommonLiteralLeftSeamTaggedChildCode A strategy
        hwin package)
    (stage : ProfiledRawJointGuardedCommonLiteralLeftSeamStage A strategy
      hwin package)
    (hstage : package.literalLeftSeamStageOfChild A strategy hwin row child =
      some stage)
    (slot : ProfiledRawLeftSlot A)
    (hlive : child.2.1.family.left () = some slot) :
    stage.root.slot = slot := by
  classical
  simp only [literalLeftSeamStageOfChild] at hstage
  split at hstage
  · rename_i hex
    have hchosen := Classical.choose_spec hex
    have hslot : Classical.choose hex = slot :=
      Option.some.inj (hchosen.symm.trans hlive)
    have hstageEq := Option.some.inj hstage
    rw [← hstageEq]
    exact hslot
  · contradiction

/-- The total inverse on the mirror seam recovers every represented
incidence code. -/
theorem literalLeftSeamTaggedChildOfCode_code_of_exists
    (package : Package A strategy hwin (initial := initial))
    (key : ProfiledRawJointGuardedCommonLiteralLeftSeamKey A strategy hwin
      package)
    (code : ProfiledRawJointIncidenceCode A (I := Unit))
    (hex : ∃ child : ProfiledRawJointOneSidedLiteralChildCode A strategy
          (ProfiledRawJointGuardedCommonLiteralLeftSeamSelectedSource A
            strategy hwin package key),
        child.1 = code) :
    (package.literalLeftSeamTaggedChildOfCode A strategy hwin key code).2.1 =
      code := by
  classical
  unfold literalLeftSeamTaggedChildOfCode
  rw [dif_pos hex]
  exact Classical.choose_spec hex

/-- A live mirror lane makes the left stage inspection succeed. -/
theorem exists_literalLeftSeamStageOfChild_of_live
    (package : Package A strategy hwin (initial := initial))
    (row : PairedEntryRow)
    (child :
      ProfiledRawJointGuardedCommonLiteralLeftSeamTaggedChildCode A strategy
        hwin package)
    (slot : ProfiledRawLeftSlot A)
    (hlive : child.2.1.family.left () = some slot) :
    ∃ stage : ProfiledRawJointGuardedCommonLiteralLeftSeamStage A strategy
        hwin package,
      package.literalLeftSeamStageOfChild A strategy hwin row child =
        some stage := by
  classical
  simp only [literalLeftSeamStageOfChild]
  split
  · exact ⟨_, rfl⟩
  · rename_i hnot
    exact False.elim (hnot ⟨slot, hlive⟩)

/-- An allowed target of the mirror exact-right uniform descriptor is
represented by a tagged child with a live left lane. -/
theorem exists_literalLeftSeamChild_live_of_exactRightAllowed
    (package : Package A strategy hwin (initial := initial))
    (key : ProfiledRawJointGuardedCommonLiteralLeftSeamKey A strategy hwin
      package)
    (code : ProfiledRawJointIncidenceCode A (I := Unit))
    (hallowed : profiledRawJointRightPhysicalSiblingAllowed A
      (profiledRawJointHybridExactRightUniformDescriptor A strategy hwin
        (package.literalLeftSeamInstalled A strategy hwin key)) code) :
    ∃ child : ProfiledRawJointOneSidedLiteralChildCode A strategy
        (ProfiledRawJointGuardedCommonLiteralLeftSeamSelectedSource A strategy
          hwin package key),
      child.1 = code ∧
        ∃ slot : ProfiledRawLeftSlot A,
          child.1.family.left () = some slot := by
  classical
  let installed := package.literalLeftSeamInstalled A strategy hwin key
  change decide (∃ row past input,
    (profiledRawJointGuardedFirstRightTarget A strategy
      (installed.world.oneSidedState A .right)
      (profiledRawJointHybridExactRightRootPredicate A installed)
      (profiledRawJointHybridExactRightPolicy A hwin installed)
      row past input).1 = code) = true at hallowed
  obtain ⟨row, past, input, hcode⟩ := of_decide_eq_true hallowed
  let child := profiledRawJointGuardedFirstRightTarget A strategy
    (installed.world.oneSidedState A .right)
    (profiledRawJointHybridExactRightRootPredicate A installed)
    (profiledRawJointHybridExactRightPolicy A hwin installed) row past input
  let activation := profiledRawJointHybridExactRightActivation A hwin installed
  let slot := profiledRawRightChildSlot A (installed.world.procOneSlot A)
    activation.lambda row past input
  refine ⟨child, hcode, slot, ?_⟩
  simpa [child, activation] using
    activation.target_active_slot row past input

/-! ## Predicate-valued branch transfer -/

/-- Any property of the active right slot transfers through the branch-aware
stage refresh.  On the false member the premise includes exact
representability by a tagged child; on the true member the dependent target
is already a tagged child. -/
theorem exists_literalRightSeamBranchStagedReceiverRecv_stage_root_of_active
    (package : Package A strategy hwin (initial := initial))
    (state :
      ProfiledRawJointGuardedCommonLiteralRightSeamStagedReceiverState A
        strategy hwin package)
    (own : In₁) (delivered : In₂) (P : ProfiledRawRightSlot A → Prop)
    (hfalse : state.2.2.1.1 = false →
      ∃ child : ProfiledRawJointOneSidedLiteralChildCode A strategy
          (ProfiledRawJointGuardedCommonLiteralRightSeamSelectedSource A
            strategy hwin package state.1),
        child.1 =
            (package.literalRightSeamBranchStagedReceiverRecv A strategy hwin
              state own delivered).1.2.1.target state.2.1 ∧
          ∃ slot : ProfiledRawRightSlot A,
            child.1.family.right () = some slot ∧ P slot)
    (htrue : state.2.2.1.1 = true →
      ∃ slot : ProfiledRawRightSlot A,
        ((package.literalRightSeamBranchStagedReceiverRecv A strategy hwin
          state own delivered).1.2.2.target state.2.1).1.family.right () =
            some slot ∧ P slot) :
    ∃ stage : ProfiledRawJointGuardedCommonLiteralRightSeamStage A strategy
        hwin package,
      (package.literalRightSeamBranchStagedReceiverRecv A strategy hwin state
        own delivered).2.2.2.2 = some stage ∧ P stage.root.slot := by
  classical
  let result := package.literalRightSeamBranchStagedReceiverRecv A strategy
    hwin state own delivered
  cases hanchor : state.2.2.1.1
  · obtain ⟨represented, hrepresented, slot, hlive, hP⟩ := hfalse hanchor
    let code : ProfiledRawJointIncidenceCode A (I := Unit) :=
      result.1.2.1.target state.2.1
    let child := package.literalRightSeamTaggedChildOfCode A strategy hwin
      state.1 code
    have hex : ∃ candidate : ProfiledRawJointOneSidedLiteralChildCode A
        strategy
          (ProfiledRawJointGuardedCommonLiteralRightSeamSelectedSource A
            strategy hwin package state.1), candidate.1 = code := by
      exact ⟨represented, hrepresented⟩
    have hcode : child.2.1 = code :=
      package.literalRightSeamTaggedChildOfCode_code_of_exists A strategy hwin
        state.1 code hex
    have hrepresentedCode : represented.1 = code := by
      simpa [code, result] using hrepresented
    have hchildLive : child.2.1.family.right () = some slot := by
      rw [hcode, ← hrepresentedCode]
      exact hlive
    obtain ⟨stage, hstage⟩ :=
      package.exists_literalRightSeamStageOfChild_of_live A strategy hwin
        state.2.1 child slot hchildLive
    refine ⟨stage, ?_, ?_⟩
    · rw [package.literalRightSeamBranchStagedReceiverRecv_stage A strategy
        hwin]
      rw [package.literalRightSeamBranchChild_false A strategy hwin _ _
        hanchor]
      exact hstage
    · rw [package.literalRightSeamStageOfChild_root_slot_eq A strategy hwin
        state.2.1 child stage hstage slot hchildLive]
      exact hP
  · obtain ⟨slot, hlive, hP⟩ := htrue hanchor
    let child :
        ProfiledRawJointGuardedCommonLiteralRightSeamTaggedChildCode A
          strategy hwin package :=
      ⟨state.1, result.1.2.2.target state.2.1⟩
    have hchildLive : child.2.1.family.right () = some slot := hlive
    obtain ⟨stage, hstage⟩ :=
      package.exists_literalRightSeamStageOfChild_of_live A strategy hwin
        state.2.1 child slot hchildLive
    refine ⟨stage, ?_, ?_⟩
    · rw [package.literalRightSeamBranchStagedReceiverRecv_stage A strategy
        hwin]
      rw [package.literalRightSeamBranchChild_true A strategy hwin _ _
        hanchor]
      exact hstage
    · rw [package.literalRightSeamStageOfChild_root_slot_eq A strategy hwin
        state.2.1 child stage hstage slot hchildLive]
      exact hP

/-- Mirror predicate transfer through the left branch-aware stage refresh. -/
theorem exists_literalLeftSeamBranchStagedReceiverRecv_stage_root_of_active
    (package : Package A strategy hwin (initial := initial))
    (state :
      ProfiledRawJointGuardedCommonLiteralLeftSeamStagedReceiverState A
        strategy hwin package)
    (own : In₂) (delivered : In₁) (P : ProfiledRawLeftSlot A → Prop)
    (hfalse : state.2.2.1.1 = false →
      ∃ child : ProfiledRawJointOneSidedLiteralChildCode A strategy
          (ProfiledRawJointGuardedCommonLiteralLeftSeamSelectedSource A
            strategy hwin package state.1),
        child.1 =
            (package.literalLeftSeamBranchStagedReceiverRecv A strategy hwin
              state own delivered).1.2.1.target state.2.1 ∧
          ∃ slot : ProfiledRawLeftSlot A,
            child.1.family.left () = some slot ∧ P slot)
    (htrue : state.2.2.1.1 = true →
      ∃ slot : ProfiledRawLeftSlot A,
        ((package.literalLeftSeamBranchStagedReceiverRecv A strategy hwin
          state own delivered).1.2.2.target state.2.1).1.family.left () =
            some slot ∧ P slot) :
    ∃ stage : ProfiledRawJointGuardedCommonLiteralLeftSeamStage A strategy
        hwin package,
      (package.literalLeftSeamBranchStagedReceiverRecv A strategy hwin state
        own delivered).2.2.2.2 = some stage ∧ P stage.root.slot := by
  classical
  let result := package.literalLeftSeamBranchStagedReceiverRecv A strategy
    hwin state own delivered
  cases hanchor : state.2.2.1.1
  · obtain ⟨represented, hrepresented, slot, hlive, hP⟩ := hfalse hanchor
    let code : ProfiledRawJointIncidenceCode A (I := Unit) :=
      result.1.2.1.target state.2.1
    let child := package.literalLeftSeamTaggedChildOfCode A strategy hwin
      state.1 code
    have hex : ∃ candidate : ProfiledRawJointOneSidedLiteralChildCode A
        strategy
          (ProfiledRawJointGuardedCommonLiteralLeftSeamSelectedSource A
            strategy hwin package state.1), candidate.1 = code := by
      exact ⟨represented, hrepresented⟩
    have hcode : child.2.1 = code :=
      package.literalLeftSeamTaggedChildOfCode_code_of_exists A strategy hwin
        state.1 code hex
    have hrepresentedCode : represented.1 = code := by
      simpa [code, result] using hrepresented
    have hchildLive : child.2.1.family.left () = some slot := by
      rw [hcode, ← hrepresentedCode]
      exact hlive
    obtain ⟨stage, hstage⟩ :=
      package.exists_literalLeftSeamStageOfChild_of_live A strategy hwin
        state.2.1 child slot hchildLive
    refine ⟨stage, ?_, ?_⟩
    · rw [package.literalLeftSeamBranchStagedReceiverRecv_stage A strategy
        hwin]
      rw [package.literalLeftSeamBranchChild_false A strategy hwin _ _
        hanchor]
      exact hstage
    · rw [package.literalLeftSeamStageOfChild_root_slot_eq A strategy hwin
        state.2.1 child stage hstage slot hchildLive]
      exact hP
  · obtain ⟨slot, hlive, hP⟩ := htrue hanchor
    let child :
        ProfiledRawJointGuardedCommonLiteralLeftSeamTaggedChildCode A strategy
          hwin package :=
      ⟨state.1, result.1.2.2.target state.2.1⟩
    have hchildLive : child.2.1.family.left () = some slot := hlive
    obtain ⟨stage, hstage⟩ :=
      package.exists_literalLeftSeamStageOfChild_of_live A strategy hwin
        state.2.1 child slot hchildLive
    refine ⟨stage, ?_, ?_⟩
    · rw [package.literalLeftSeamBranchStagedReceiverRecv_stage A strategy
        hwin]
      rw [package.literalLeftSeamBranchChild_true A strategy hwin _ _
        hanchor]
      exact hstage
    · rw [package.literalLeftSeamStageOfChild_root_slot_eq A strategy hwin
        state.2.1 child stage hstage slot hchildLive]
      exact hP

/-! ## Reachable table rounds retain the physical block priority -/

/-- At every locally reachable right-table round, the refreshed stage exists
and its root priority is the minimum of the literal prefix of the selected
member play.  The witnessed finite input prefix is proof-side only. -/
theorem
    exists_literalRightSeamBranchStagedReceiverRecv_stage_priority_of_tableReachable
    (package : Package A strategy hwin (initial := initial))
    (state :
      ProfiledRawJointGuardedCommonLiteralRightSeamStagedReceiverState A
        strategy hwin package)
    (own : In₁) (delivered : In₂)
    (hreach : package.LiteralRightSeamReceiverTableLocallyReachable A strategy
      hwin state) :
    ∃ past : List (In₁ × In₂),
      ∃ stage :
          ProfiledRawJointGuardedCommonLiteralRightSeamStage A strategy hwin
            package,
        (package.literalRightSeamBranchStagedReceiverRecv A strategy hwin
          state own delivered).2.2.2.2 = some stage ∧
          profiledRawJointThreadRootPriority A (.inl stage.root.slot) =
            literalRightSeamSelectedTableBlockPriority A strategy hwin
              (package.literalRightSeamInstalled A strategy hwin state.1)
              state.2.2.1.1 (omegaOfList (past ++ [(own, delivered)]))
                past.length state.2.1 := by
  classical
  let installed := package.literalRightSeamInstalled A strategy hwin state.1
  let table :=
    profiledRawJointLiteralRightBothExactHeterogeneousLeftTable A strategy hwin
      installed
  obtain ⟨sender, hlocal⟩ := hreach
  obtain ⟨past, _hsender, _hreceiver, hround⟩ :=
    hlocal.exists_localRound_eq_treePlay table (own, delivered)
  let env : Nat → In₁ × In₂ := omegaOfList (past ++ [(own, delivered)])
  let P : ProfiledRawRightSlot A → Prop := fun slot ↦
    profiledRawJointThreadRootPriority A (.inl slot) =
      literalRightSeamSelectedTableBlockPriority A strategy hwin
        installed state.2.2.1.1 env past.length state.2.1
  refine ⟨past, ?_⟩
  apply package.exists_literalRightSeamBranchStagedReceiverRecv_stage_root_of_active
    A strategy hwin state own delivered P
  · intro hanchor
    let play := profiledRawJointLiteralRightBothExactFalsePlay A strategy hwin
      installed env
    have htarget :
        (package.literalRightSeamBranchStagedReceiverRecv A strategy hwin state
          own delivered).1.2.1.target state.2.1 =
          (play past.length).2.1.target state.2.1 := by
      have hat := congrArg
        (fun record ↦ record.2.1.1.target state.2.1) hround
      rw [hanchor] at hat
      simpa [literalRightSeamBranchStagedReceiverRecv,
        profiledRawJointLiteralRightBothExactReceiverRecv,
        profiledRawJointLiteralRightBothExactFalsePlay,
        BlockRecordMonitor.projectReceiverPlay, play, table, installed,
        hanchor, env] using hat
    let descriptor :=
      profiledRawJointHybridExactLeftUniformDescriptor A strategy hwin installed
    have hwins :=
      profiledRawJointLiteralRightBothExactFalsePlay_wins A strategy hwin
        installed env
    have hsafe := profiledRawJointTargetLeft_targetsSafe_of_wins A
      (profiledRawJointUnitLeftTargetProjection A)
      (profiledRawJointLeftPhysicalSiblingAllowed A descriptor)
      descriptor.source play hwins past.length state.2.1
    have hallowed : profiledRawJointLeftPhysicalSiblingAllowed A descriptor
        ((package.literalRightSeamBranchStagedReceiverRecv A strategy hwin
          state own delivered).1.2.1.target state.2.1) := by
      rw [htarget]
      exact hsafe.2
    obtain ⟨child, hchild, _liveSlot, _hchildLive⟩ :=
      package.exists_literalRightSeamChild_live_of_exactLeftAllowed A strategy
        hwin state.1 _ (by simpa [descriptor, installed] using hallowed)
    obtain ⟨slot, hslot, hpriority⟩ :=
      exists_profiledRawJointLiteralRightBothExactFalsePlay_targetThreadPriority_eq_blockMin
        A strategy hwin installed env past.length state.2.1
    refine ⟨child, hchild, slot, ?_, ?_⟩
    · rw [hchild, htarget]
      exact hslot
    · simpa [P, literalRightSeamSelectedTableBlockPriority, hanchor, play,
        installed, descriptor] using hpriority
  · intro hanchor
    let play := profiledRawJointLiteralRightBothExactTruePlay A strategy hwin
      installed env
    have htarget :
        ((package.literalRightSeamBranchStagedReceiverRecv A strategy hwin
          state own delivered).1.2.2.target state.2.1).1 =
          ((play past.length).2.1.target state.2.1).1 := by
      have hat := congrArg
        (fun record ↦ (record.2.1.2.target state.2.1).1) hround
      rw [hanchor] at hat
      simpa [literalRightSeamBranchStagedReceiverRecv,
        profiledRawJointLiteralRightBothExactReceiverRecv,
        profiledRawJointLiteralRightBothExactTruePlay,
        BlockRecordMonitor.projectReceiverPlay, play, table, installed,
        hanchor, env] using hat
    obtain ⟨slot, hslot, hpriority⟩ :=
      exists_profiledRawJointLiteralRightBothExactTruePlay_targetThreadPriority_eq_blockMin
        A strategy hwin installed env past.length state.2.1
    refine ⟨slot, ?_, ?_⟩
    · rw [htarget]
      exact hslot
    · simpa [P, literalRightSeamSelectedTableBlockPriority, hanchor, play,
        installed] using hpriority

/-- Mirror locally reachable table round: the refreshed left-stage root
priority is the minimum of the selected mirror-member physical prefix. -/
theorem
    exists_literalLeftSeamBranchStagedReceiverRecv_stage_priority_of_tableReachable
    (package : Package A strategy hwin (initial := initial))
    (state :
      ProfiledRawJointGuardedCommonLiteralLeftSeamStagedReceiverState A
        strategy hwin package)
    (own : In₂) (delivered : In₁)
    (hreach : package.LiteralLeftSeamReceiverTableLocallyReachable A strategy
      hwin state) :
    ∃ past : List (In₂ × In₁),
      ∃ stage :
          ProfiledRawJointGuardedCommonLiteralLeftSeamStage A strategy hwin
            package,
        (package.literalLeftSeamBranchStagedReceiverRecv A strategy hwin state
          own delivered).2.2.2.2 = some stage ∧
          profiledRawJointThreadRootPriority A (.inr stage.root.slot) =
            literalLeftSeamSelectedTableBlockPriority A strategy hwin
              (package.literalLeftSeamInstalled A strategy hwin state.1)
              state.2.2.1.1 (omegaOfList (past ++ [(own, delivered)]))
                past.length state.2.1 := by
  classical
  let installed := package.literalLeftSeamInstalled A strategy hwin state.1
  let table :=
    profiledRawJointLiteralLeftBothExactHeterogeneousRightTable A strategy hwin
      installed
  obtain ⟨sender, hlocal⟩ := hreach
  obtain ⟨past, _hsender, _hreceiver, hround⟩ :=
    hlocal.exists_localRound_eq_treePlay table (own, delivered)
  let env : Nat → In₂ × In₁ := omegaOfList (past ++ [(own, delivered)])
  let P : ProfiledRawLeftSlot A → Prop := fun slot ↦
    profiledRawJointThreadRootPriority A (.inr slot) =
      literalLeftSeamSelectedTableBlockPriority A strategy hwin installed
        state.2.2.1.1 env past.length state.2.1
  refine ⟨past, ?_⟩
  apply package.exists_literalLeftSeamBranchStagedReceiverRecv_stage_root_of_active
    A strategy hwin state own delivered P
  · intro hanchor
    let play := profiledRawJointLiteralLeftBothExactFalsePlay A strategy hwin
      installed env
    have htarget :
        (package.literalLeftSeamBranchStagedReceiverRecv A strategy hwin state
          own delivered).1.2.1.target state.2.1 =
          (play past.length).2.1.target state.2.1 := by
      have hat := congrArg
        (fun record ↦ record.2.1.1.target state.2.1) hround
      rw [hanchor] at hat
      simpa [literalLeftSeamBranchStagedReceiverRecv,
        profiledRawJointLiteralLeftBothExactReceiverRecv,
        profiledRawJointLiteralLeftBothExactFalsePlay,
        BlockRecordMonitor.projectReceiverPlay, play, table, installed,
        hanchor, env] using hat
    let descriptor :=
      profiledRawJointHybridExactRightUniformDescriptor A strategy hwin
        installed
    have hwins :=
      profiledRawJointLiteralLeftBothExactFalsePlay_wins A strategy hwin
        installed env
    have hsafe := profiledRawJointTargetRight_targetsSafe_of_wins A
      (profiledRawJointUnitRightTargetProjection A)
      (profiledRawJointRightPhysicalSiblingAllowed A descriptor)
      descriptor.source play hwins past.length state.2.1
    have hallowed : profiledRawJointRightPhysicalSiblingAllowed A descriptor
        ((package.literalLeftSeamBranchStagedReceiverRecv A strategy hwin state
          own delivered).1.2.1.target state.2.1) := by
      rw [htarget]
      exact hsafe.2
    obtain ⟨child, hchild, _liveSlot, _hchildLive⟩ :=
      package.exists_literalLeftSeamChild_live_of_exactRightAllowed A strategy
        hwin state.1 _ (by simpa [descriptor, installed] using hallowed)
    obtain ⟨slot, hslot, hpriority⟩ :=
      exists_profiledRawJointLiteralLeftBothExactFalsePlay_targetThreadPriority_eq_blockMin
        A strategy hwin installed env past.length state.2.1
    refine ⟨child, hchild, slot, ?_, ?_⟩
    · rw [hchild, htarget]
      exact hslot
    · simpa [P, literalLeftSeamSelectedTableBlockPriority, hanchor, play,
        installed, descriptor] using hpriority
  · intro hanchor
    let play := profiledRawJointLiteralLeftBothExactTruePlay A strategy hwin
      installed env
    have htarget :
        ((package.literalLeftSeamBranchStagedReceiverRecv A strategy hwin state
          own delivered).1.2.2.target state.2.1).1 =
          ((play past.length).2.1.target state.2.1).1 := by
      have hat := congrArg
        (fun record ↦ (record.2.1.2.target state.2.1).1) hround
      rw [hanchor] at hat
      simpa [literalLeftSeamBranchStagedReceiverRecv,
        profiledRawJointLiteralLeftBothExactReceiverRecv,
        profiledRawJointLiteralLeftBothExactTruePlay,
        BlockRecordMonitor.projectReceiverPlay, play, table, installed,
        hanchor, env] using hat
    obtain ⟨slot, hslot, hpriority⟩ :=
      exists_profiledRawJointLiteralLeftBothExactTruePlay_targetThreadPriority_eq_blockMin
        A strategy hwin installed env past.length state.2.1
    refine ⟨slot, ?_, ?_⟩
    · rw [htarget]
      exact hslot
    · simpa [P, literalLeftSeamSelectedTableBlockPriority, hanchor, play,
        installed] using hpriority

end ProfiledRawJointGuardedCommonDecoratedPolicyPackage

end

end DetParityAutomaton

end DistributedSynthesis
