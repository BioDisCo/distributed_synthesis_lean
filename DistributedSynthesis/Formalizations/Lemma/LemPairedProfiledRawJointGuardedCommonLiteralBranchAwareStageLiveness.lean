/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralBranchAwareStagedFront
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralHeterogeneousTailAcceptance
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralExactTablePhysicalPriority
import DistributedSynthesis.Formalizations.Lemma.LemFiniteCrossAnchorLocalCarrierReachability

/-!
# Live-stage extraction for the branch-aware literal seam

The branch-aware receiver refreshes its retained stage from the product
coordinate selected by the receiver's internal table member.  This file
isolates the finite local fact needed by the phase activation controller:
whenever that active target code has a live right lane, the refreshed stage
is `some`.  No orientation or leader bit is supplied to an executable map.
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

private abbrev RightReceiver (package : Package A strategy hwin
    (initial := initial)) :=
  ProfiledRawJointGuardedCommonLiteralRightSeamStagedReceiverState A strategy
    hwin package

private abbrev RightSender (package : Package A strategy hwin
    (initial := initial)) :=
  ProfiledRawJointGuardedCommonLiteralRightSeamStagedSenderState A strategy
    hwin package

/-- Proof-side reachability of the table receiver from its selected member
root.  The sender witness is not stored in an executable receiver; it merely
lets the generic local-carrier theorem identify the next record with the
selected member's tree play. -/
def LiteralRightSeamReceiverTableLocallyReachable
    (package : Package A strategy hwin (initial := initial))
    (receiver : RightReceiver A strategy hwin package) : Prop :=
  ∃ sender : ProfiledRawJointLiteralRightBothExactSenderState A strategy hwin
      (package.literalRightSeamInstalled A strategy hwin receiver.1),
    FiniteCrossAnchorLocallyReachable
      (profiledRawJointLiteralRightBothExactHeterogeneousLeftTable A strategy
      hwin (package.literalRightSeamInstalled A strategy hwin receiver.1))
      sender receiver.2.2.1

/-- Every freshly installed right receiver is at its selected table root. -/
theorem literalRightSeamReceiverTableLocallyReachable_initial
    (package : Package A strategy hwin (initial := initial))
    (key : ProfiledRawJointGuardedCommonLiteralRightSeamKey A strategy hwin
      package)
    (row : PairedEntryRow) (anchor : Bool) :
    package.LiteralRightSeamReceiverTableLocallyReachable A strategy hwin
      (package.literalRightSeamStagedReceiverInitial A strategy hwin key row
        anchor) := by
  let installed := package.literalRightSeamInstalled A strategy hwin key
  let table :=
    profiledRawJointLiteralRightBothExactHeterogeneousLeftTable A strategy hwin
      installed
  refine ⟨profiledRawJointLiteralRightBothExactSenderInitial A strategy hwin
    installed, ?_⟩
  exact finiteCrossAnchorLocallyReachable_initial table anchor

/-- One branch-aware homogeneous receive preserves receiver-table
reachability.  The sender used in the proof is existential and is never added
to the executable receiver state. -/
theorem LiteralRightSeamReceiverTableLocallyReachable.step
    (package : Package A strategy hwin (initial := initial))
    {receiver : RightReceiver A strategy hwin package}
    (hreach : package.LiteralRightSeamReceiverTableLocallyReachable A strategy
      hwin receiver)
    (input : In₁ × In₂) :
    package.LiteralRightSeamReceiverTableLocallyReachable A strategy hwin
      (package.literalRightSeamBranchStagedReceiverRecv A strategy hwin
        receiver input.1 input.2).2 := by
  let installed := package.literalRightSeamInstalled A strategy hwin receiver.1
  let table :=
    profiledRawJointLiteralRightBothExactHeterogeneousLeftTable A strategy hwin
      installed
  obtain ⟨sender, hlocal⟩ := hreach
  refine ⟨(profiledRawJointLiteralRightBothExactSenderNoRecv A strategy hwin
    installed sender input.2).2, ?_⟩
  simpa [LiteralRightSeamReceiverTableLocallyReachable,
    literalRightSeamBranchStagedReceiverRecv, installed, table] using
    hlocal.step table input

/-! ## Total-inverse and stage-existence laws -/

/-- The total inverse recovers every incidence code represented by a literal
child.  The fallback branch is therefore unreachable on represented codes. -/
theorem literalRightSeamTaggedChildOfCode_code_of_exists
    (package : Package A strategy hwin (initial := initial))
    (key : ProfiledRawJointGuardedCommonLiteralRightSeamKey A strategy hwin
      package)
    (code : ProfiledRawJointIncidenceCode A (I := Unit))
  (hex : ∃ child : ProfiledRawJointOneSidedLiteralChildCode A strategy
        (ProfiledRawJointGuardedCommonLiteralRightSeamSelectedSource A
          strategy hwin package key),
      child.1 = code) :
    (package.literalRightSeamTaggedChildOfCode A strategy hwin key code).2.1 =
      code := by
  classical
  unfold literalRightSeamTaggedChildOfCode
  rw [dif_pos hex]
  exact Classical.choose_spec hex

/-- A live right lane makes the stage inspection succeed. -/
theorem exists_literalRightSeamStageOfChild_of_live
    (package : Package A strategy hwin (initial := initial))
    (row : PairedEntryRow)
    (child :
      ProfiledRawJointGuardedCommonLiteralRightSeamTaggedChildCode A strategy
        hwin package)
    (slot : ProfiledRawRightSlot A)
    (hlive : child.2.1.family.right () = some slot) :
    ∃ stage : ProfiledRawJointGuardedCommonLiteralRightSeamStage A strategy
        hwin package,
      package.literalRightSeamStageOfChild A strategy hwin row child =
        some stage := by
  classical
  simp only [literalRightSeamStageOfChild]
  split
  · rename_i hex
    exact ⟨_, rfl⟩
  · rename_i hnot
    exact False.elim (hnot ⟨slot, hlive⟩)

/-- An allowed target of the exact-left uniform descriptor is represented by
an exact literal child, and that child has the live right lane required by
the stage constructor. -/
theorem exists_literalRightSeamChild_live_of_exactLeftAllowed
    (package : Package A strategy hwin (initial := initial))
    (key : ProfiledRawJointGuardedCommonLiteralRightSeamKey A strategy hwin
      package)
    (code : ProfiledRawJointIncidenceCode A (I := Unit))
    (hallowed : profiledRawJointLeftPhysicalSiblingAllowed A
      (profiledRawJointHybridExactLeftUniformDescriptor A strategy hwin
        (package.literalRightSeamInstalled A strategy hwin key)) code) :
    ∃ child : ProfiledRawJointOneSidedLiteralChildCode A strategy
        (ProfiledRawJointGuardedCommonLiteralRightSeamSelectedSource A
          strategy hwin package key),
      child.1 = code ∧
        ∃ slot : ProfiledRawRightSlot A,
          child.1.family.right () = some slot := by
  classical
  let installed := package.literalRightSeamInstalled A strategy hwin key
  change decide (∃ row past input,
    (profiledRawJointGuardedFirstLeftTarget A strategy
      (installed.world.oneSidedState A .left)
      (profiledRawJointHybridExactLeftRootPredicate A installed)
      (profiledRawJointHybridExactLeftPolicy A hwin installed)
      row past input).1 = code) = true at hallowed
  obtain ⟨row, past, input, hcode⟩ := of_decide_eq_true hallowed
  let child := profiledRawJointGuardedFirstLeftTarget A strategy
    (installed.world.oneSidedState A .left)
    (profiledRawJointHybridExactLeftRootPredicate A installed)
    (profiledRawJointHybridExactLeftPolicy A hwin installed) row past input
  let activation := profiledRawJointHybridExactLeftActivation A hwin installed
  let slot := profiledRawLeftChildSlot A (installed.world.procTwoSlot A)
    activation.lambda row past input
  refine ⟨child, hcode, slot, ?_⟩
  simpa [child, activation] using
    activation.target_active_slot row past input

/-! ## Active-coordinate liveness -/

/-- If the target selected by the receiver's internal member has a live right
lane, the branch-aware receive retains a live stage.  The proof splits only
on the receiver's stored finite member bit; this bit is not a graph input. -/
theorem exists_literalRightSeamBranchStagedReceiverRecv_stage_of_active_live
    (package : Package A strategy hwin (initial := initial))
    (state : RightReceiver A strategy hwin package)
    (own : In₁) (delivered : In₂)
    (hfalse : state.2.2.1.1 = false →
      ∃ child : ProfiledRawJointOneSidedLiteralChildCode A strategy
          (ProfiledRawJointGuardedCommonLiteralRightSeamSelectedSource A
            strategy hwin package state.1),
        child.1 =
            (package.literalRightSeamBranchStagedReceiverRecv A strategy hwin
              state own delivered).1.2.1.target state.2.1 ∧
          ∃ slot : ProfiledRawRightSlot A,
            child.1.family.right () = some slot)
    (htrue : state.2.2.1.1 = true →
      ∃ slot : ProfiledRawRightSlot A,
        ((package.literalRightSeamBranchStagedReceiverRecv A strategy hwin
          state own delivered).1.2.2.target state.2.1).1.family.right () =
            some slot) :
    ∃ stage : ProfiledRawJointGuardedCommonLiteralRightSeamStage A strategy
        hwin package,
      (package.literalRightSeamBranchStagedReceiverRecv A strategy hwin state
        own delivered).2.2.2.2 = some stage := by
  classical
  cases hanchor : state.2.2.1.1
  · obtain ⟨child, hchild, slot, hlive⟩ := hfalse hanchor
    rw [package.literalRightSeamBranchStagedReceiverRecv_stage A strategy hwin]
    rw [package.literalRightSeamBranchChild_false A strategy hwin _ _ hanchor]
    let code : ProfiledRawJointIncidenceCode A (I := Unit) :=
      (package.literalRightSeamBranchStagedReceiverRecv A strategy hwin state
        own delivered).1.2.1.target state.2.1
    have hex : ∃ child : ProfiledRawJointOneSidedLiteralChildCode A strategy
        (ProfiledRawJointGuardedCommonLiteralRightSeamSelectedSource A
          strategy hwin package state.1), child.1 = code := by
      exact ⟨child, hchild⟩
    have hcode := package.literalRightSeamTaggedChildOfCode_code_of_exists
      A strategy hwin state.1 code hex
    apply package.exists_literalRightSeamStageOfChild_of_live A strategy hwin
      state.2.1 _ slot
    rw [hcode]
    simpa [code, hchild] using hlive
  · obtain ⟨slot, hlive⟩ := htrue hanchor
    rw [package.literalRightSeamBranchStagedReceiverRecv_stage A strategy hwin]
    rw [package.literalRightSeamBranchChild_true A strategy hwin _ _ hanchor]
    exact package.exists_literalRightSeamStageOfChild_of_live A strategy hwin
      state.2.1 _ slot hlive

/-! ## Arbitrary-depth table-reachable liveness -/

/-- Every honest next round of a table-reachable right seam refreshes a live
stage.  For the `false` member, monitor target-safety says the active code is
one of the exact-left literal children; for the `true` member, the exact table
priority theorem supplies the live lane directly.  The proof follows the
receiver's stored member and never asks an endpoint which side is informed. -/
theorem exists_literalRightSeamBranchStagedReceiverRecv_stage_of_tableReachable
    (package : Package A strategy hwin (initial := initial))
    (state : RightReceiver A strategy hwin package)
    (own : In₁) (delivered : In₂)
    (hreach : package.LiteralRightSeamReceiverTableLocallyReachable A strategy
      hwin state) :
    ∃ stage : ProfiledRawJointGuardedCommonLiteralRightSeamStage A strategy
        hwin package,
      (package.literalRightSeamBranchStagedReceiverRecv A strategy hwin state
        own delivered).2.2.2.2 = some stage := by
  classical
  let installed := package.literalRightSeamInstalled A strategy hwin state.1
  let table :=
    profiledRawJointLiteralRightBothExactHeterogeneousLeftTable A strategy hwin
      installed
  obtain ⟨sender, hlocal⟩ := hreach
  obtain ⟨past, hsender, hreceiver, hround⟩ :=
    hlocal.exists_localRound_eq_treePlay table (own, delivered)
  let env : Nat → In₁ × In₂ := omegaOfList (past ++ [(own, delivered)])
  apply package.exists_literalRightSeamBranchStagedReceiverRecv_stage_of_active_live
    A strategy hwin state own delivered
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
    have hwins :=
      profiledRawJointLiteralRightBothExactFalsePlay_wins A strategy hwin
        installed env
    let descriptor :=
      profiledRawJointHybridExactLeftUniformDescriptor A strategy hwin installed
    have hsafe := profiledRawJointTargetLeft_targetsSafe_of_wins A
      (profiledRawJointUnitLeftTargetProjection A)
      (profiledRawJointLeftPhysicalSiblingAllowed A descriptor)
      descriptor.source play hwins past.length state.2.1
    have hallowed : profiledRawJointLeftPhysicalSiblingAllowed A descriptor
        ((package.literalRightSeamBranchStagedReceiverRecv A strategy hwin
          state own delivered).1.2.1.target state.2.1) := by
      rw [htarget]
      exact hsafe.2
    exact package.exists_literalRightSeamChild_live_of_exactLeftAllowed A
      strategy hwin state.1 _ (by simpa [descriptor, installed] using hallowed)
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
    obtain ⟨slot, hlive, _⟩ :=
      exists_profiledRawJointLiteralRightBothExactTruePlay_targetThreadPriority_eq_blockMin
        A strategy hwin installed env past.length state.2.1
    refine ⟨slot, ?_⟩
    rw [htarget]
    exact hlive

end ProfiledRawJointGuardedCommonDecoratedPolicyPackage

end

end DetParityAutomaton

end DistributedSynthesis
