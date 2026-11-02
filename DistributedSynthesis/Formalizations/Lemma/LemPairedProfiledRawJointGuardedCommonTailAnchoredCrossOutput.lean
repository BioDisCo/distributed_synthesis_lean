/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonTailCoreStrictTrace
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonTailPendingRebase

/-!
# The first pending cross-anchor output test

The genuinely dangerous cross-anchor round occurs before the resolved
anchored mixed phase.  After a first strict-right round, process one retains
the old right owner while process two carries the current common shadow.  If
the next graph is simultaneous, process one must rebase from that current
shadow, whereas process two still resolves the old right table.  The two
independent local outputs must nevertheless form the current strict-left root
record.  The left-pending statement is the mirror.

Both statements below are restricted to the pending states constructed by a
literal finite prefix.  No arbitrary-state coherence is assumed.
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
  (initialBank : ProfiledRawJointInitialControllerBank A strategy)

private abbrev CommonControl :=
  ProfiledRawJointGuardedInitialCommonControl A strategy hwin

/-! ## Delayed overlap of a winning guarded controller -/

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- The base monitor hidden below the first-letter guard enforces its pending
right action profile on the next concrete narrowed-controller record. -/
theorem
    ProfiledRawJointGuardedRightPhysicalSiblingMove.memberController_overlap
    (move : ProfiledRawJointGuardedRightPhysicalSiblingMove A)
    (member : Bool) (env : Nat → In₂ × In₁) (n : Nat)
    (row : PairedEntryRow)
    (expected : LeftInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁))
    (hpending :
      let base := profiledRawJointRightPhysicalSiblingMonitor A move.1.base
        false
      let monitor := profiledRawJointGuardedRightPhysicalSiblingMonitor A
        move.1 member
      let controller := move.memberController A member
      let play := treePlay
        (narrowedInducedTree monitor controller.labeledTree) env
      (base.run play n).2.2.1 row = some expected) :
    let monitor := profiledRawJointGuardedRightPhysicalSiblingMonitor A move.1
      member
    let controller := move.memberController A member
    let play := treePlay
      (narrowedInducedTree monitor controller.labeledTree) env
    pairedRightClosingForRow row
        (profiledRawJointTargetRightPhysicalLetter A (play n)).2.1 =
      expected ((play n).1.2, (play n).1.1) := by
  dsimp only at hpending ⊢
  let base := profiledRawJointRightPhysicalSiblingMonitor A move.1.base false
  let monitor := profiledRawJointGuardedRightPhysicalSiblingMonitor A move.1
    member
  let controller := move.memberController A member
  let tree := narrowedInducedTree monitor controller.labeledTree
  let play := treePlay tree env
  have htree : monitor.lift.WinningTree tree :=
    narrowedInducedTree_winningTree_of_allThreadsWin monitor
      (move.memberController_wins A member)
  have hguard : monitor.WinsPlay play :=
    (monitor.lift_winningTree_iff tree).mp htree env
  have hbase : base.WinsPlay play :=
    BlockRecordMonitor.firstLetterGuard_base_wins_of_wins base
      move.1.firstAllowed play hguard
  have hsafe := profiledRawJointTargetRightBlockMonitor_safe_of_wins A
    (profiledRawJointUnitRightTargetProjection A)
    (profiledRawJointRightPhysicalSiblingAllowed A move.1.base)
    move.1.base.source play hbase (n + 1)
  rw [BlockRecordMonitor.run] at hsafe
  simp only [profiledRawJointTargetRightBlockMonitor, Bool.and_eq_true,
    decide_eq_true_eq] at hsafe
  exact hsafe.1.2 row expected hpending

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Left guarded-controller mirror. -/
theorem
    ProfiledRawJointGuardedLeftPhysicalSiblingMove.memberController_overlap
    (move : ProfiledRawJointGuardedLeftPhysicalSiblingMove A)
    (member : Bool) (env : Nat → In₁ × In₂) (n : Nat)
    (row : PairedEntryRow)
    (expected : RightInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂))
    (hpending :
      let base := profiledRawJointLeftPhysicalSiblingMonitor A move.1.base false
      let monitor := profiledRawJointGuardedLeftPhysicalSiblingMonitor A
        move.1 member
      let controller := move.memberController A member
      let play := treePlay
        (narrowedInducedTree monitor controller.labeledTree) env
      (base.run play n).2.2.1 row = some expected) :
    let monitor := profiledRawJointGuardedLeftPhysicalSiblingMonitor A move.1
      member
    let controller := move.memberController A member
    let play := treePlay
      (narrowedInducedTree monitor controller.labeledTree) env
    pairedLeftClosingForRow row
        (profiledRawJointTargetLeftPhysicalLetter A (play n)).2.1 =
      expected ((play n).1.2, (play n).1.1) := by
  dsimp only at hpending ⊢
  let base := profiledRawJointLeftPhysicalSiblingMonitor A move.1.base false
  let monitor := profiledRawJointGuardedLeftPhysicalSiblingMonitor A move.1
    member
  let controller := move.memberController A member
  let tree := narrowedInducedTree monitor controller.labeledTree
  let play := treePlay tree env
  have htree : monitor.lift.WinningTree tree :=
    narrowedInducedTree_winningTree_of_allThreadsWin monitor
      (move.memberController_wins A member)
  have hguard : monitor.WinsPlay play :=
    (monitor.lift_winningTree_iff tree).mp htree env
  have hbase : base.WinsPlay play :=
    BlockRecordMonitor.firstLetterGuard_base_wins_of_wins base
      move.1.firstAllowed play hguard
  have hsafe := profiledRawJointTargetLeftBlockMonitor_safe_of_wins A
    (profiledRawJointUnitLeftTargetProjection A)
    (profiledRawJointLeftPhysicalSiblingAllowed A move.1.base)
    move.1.base.source play hbase (n + 1)
  rw [BlockRecordMonitor.run] at hsafe
  simp only [profiledRawJointTargetLeftBlockMonitor, Bool.and_eq_true,
    decide_eq_true_eq] at hsafe
  exact hsafe.1.2 row expected hpending

/-- The single output equality hidden inside the right-pending pair test: the
old right receiver must agree with the process-two coordinate of the current
common occurrence.  This is deliberately a named proposition: the existing
first-letter guard fixes the old table's root record, but does not by itself
fix this second record. -/
def profiledRawJointGuardedCommonTailInitialRightPendingOldEqCurrent
    (root : CommonControl A strategy hwin) (first : In₂ × In₁)
    (next : In₁ × In₂) : Prop :=
    let pending :=
      profiledRawJointGuardedCommonTailInitialRightPending A strategy hwin root
        first
    (profiledRawJointGuardedCommonTailResolveRightTwo A strategy hwin
        initialBank pending.receiver pending.owner next.2 next.1).1 =
      let pair := profiledRawJointGuardedInitialCommonControlPair A strategy
        hwin pending.receiver.control
      (pair.leftRootRecord A strategy hwin next).2.1.physical.closingBoth

/-- Left-pending mirror. -/
def profiledRawJointGuardedCommonTailInitialLeftPendingOldEqCurrent
    (root : CommonControl A strategy hwin) (first next : In₁ × In₂) : Prop :=
    let pending :=
      profiledRawJointGuardedCommonTailInitialLeftPending A strategy hwin root
        first
    (profiledRawJointGuardedCommonTailResolveLeftOne A strategy hwin
        initialBank pending.receiver pending.owner next.1 next.2).1 =
      let pair := profiledRawJointGuardedInitialCommonControlPair A strategy
        hwin pending.receiver.control
      (pair.rightRootRecord A strategy hwin next).2.1.physical.closingBoth

/-- Reachable right-pending cross-anchor test.  The first coordinate rebases
from the current common shadow; the second resolves the old right table. -/
def profiledRawJointGuardedCommonTailInitialRightPendingCrossOutput
    (root : CommonControl A strategy hwin) (first : In₂ × In₁)
    (next : In₁ × In₂) : Prop :=
    let pending :=
      profiledRawJointGuardedCommonTailInitialRightPending A strategy hwin root
        first
    ((profiledRawJointGuardedCommonTailRightPendingRebaseOne A strategy hwin
        initialBank pending.owner pending.receiver next.1 next.2).1,
      (profiledRawJointGuardedCommonTailResolveRightTwo A strategy hwin
        initialBank pending.receiver pending.owner next.2 next.1).1) =
      profiledRawJointGuardedCommonPairBothOutput A strategy hwin
        (profiledRawJointGuardedInitialCommonControlPair A strategy hwin
          pending.receiver.control) next

/-- At a reachable right-pending cross anchor, the complete output-pair law
is equivalent to its one genuinely new process-two equality.  The process-one
coordinate follows unconditionally from the already proved rebase law. -/
theorem
    profiledRawJointGuardedCommonTailInitialRightPendingCrossOutput_iff
    (root : CommonControl A strategy hwin) (first : In₂ × In₁)
    (next : In₁ × In₂) :
    profiledRawJointGuardedCommonTailInitialRightPendingCrossOutput A strategy
        hwin initialBank root first next ↔
      profiledRawJointGuardedCommonTailInitialRightPendingOldEqCurrent A
        strategy hwin initialBank root first next := by
  constructor
  · intro h
    exact congrArg Prod.snd h
  · intro hold
    dsimp only
    apply Prod.ext
    · have hrebase := congrArg Prod.fst
        (profiledRawJointGuardedCommonTailRightPendingRebase_strictLeft_outputs
          A strategy hwin initialBank
          (profiledRawJointGuardedCommonTailInitialRightPending A strategy hwin
            root first).owner
          (profiledRawJointGuardedCommonTailInitialRightPending A strategy hwin
            root first).receiver next)
      rw [show
      (profiledRawJointGuardedCommonPairBothOutput A strategy hwin
        (profiledRawJointGuardedInitialCommonControlPair A strategy hwin
          (profiledRawJointGuardedCommonTailInitialRightPending A strategy hwin
            root first).receiver.control) next).1 =
        ((profiledRawJointGuardedInitialCommonControlPair A strategy hwin
          (profiledRawJointGuardedCommonTailInitialRightPending A strategy hwin
            root first).receiver.control).rightRootRecord A strategy hwin
              next).2.1.physical.closingBoth by rfl]
      rw [(profiledRawJointGuardedInitialCommonControlPair A strategy hwin
      (profiledRawJointGuardedCommonTailInitialRightPending A strategy hwin
        root first).receiver.control).root_outputOne A strategy hwin next]
      exact hrebase
    · exact hold

/-- Reachable left-pending mirror. -/
def profiledRawJointGuardedCommonTailInitialLeftPendingCrossOutput
    (root : CommonControl A strategy hwin) (first next : In₁ × In₂) : Prop :=
    let pending :=
      profiledRawJointGuardedCommonTailInitialLeftPending A strategy hwin root
        first
    ((profiledRawJointGuardedCommonTailResolveLeftOne A strategy hwin
        initialBank pending.receiver pending.owner next.1 next.2).1,
      (profiledRawJointGuardedCommonTailLeftPendingRebaseTwo A strategy hwin
        initialBank pending.owner pending.receiver next.2 next.1).1) =
      profiledRawJointGuardedCommonPairBothOutput A strategy hwin
        (profiledRawJointGuardedInitialCommonControlPair A strategy hwin
          pending.receiver.control) next

/-- Left-pending mirror of the exact reduction above. -/
theorem profiledRawJointGuardedCommonTailInitialLeftPendingCrossOutput_iff
    (root : CommonControl A strategy hwin) (first next : In₁ × In₂) :
    profiledRawJointGuardedCommonTailInitialLeftPendingCrossOutput A strategy
        hwin initialBank root first next ↔
      profiledRawJointGuardedCommonTailInitialLeftPendingOldEqCurrent A
        strategy hwin initialBank root first next := by
  constructor
  · intro h
    exact congrArg Prod.fst h
  · intro hold
    dsimp only
    apply Prod.ext
    · exact hold
    · have hrebase := congrArg Prod.snd
        (profiledRawJointGuardedCommonTailLeftPendingRebase_strictRight_outputs
          A strategy hwin initialBank
          (profiledRawJointGuardedCommonTailInitialLeftPending A strategy hwin
            root first).receiver
          (profiledRawJointGuardedCommonTailInitialLeftPending A strategy hwin
            root first).owner next)
      rw [show
      (profiledRawJointGuardedCommonPairBothOutput A strategy hwin
        (profiledRawJointGuardedInitialCommonControlPair A strategy hwin
          (profiledRawJointGuardedCommonTailInitialLeftPending A strategy hwin
            root first).receiver.control) next).2 =
        ((profiledRawJointGuardedInitialCommonControlPair A strategy hwin
          (profiledRawJointGuardedCommonTailInitialLeftPending A strategy hwin
            root first).receiver.control).leftRootRecord A strategy hwin
              next).2.1.physical.closingBoth by rfl]
      rw [(profiledRawJointGuardedInitialCommonControlPair A strategy hwin
      (profiledRawJointGuardedCommonTailInitialLeftPending A strategy hwin
        root first).receiver.control).root_outputTwo A strategy hwin next]
      exact hrebase

end

end DetParityAutomaton

end DistributedSynthesis
