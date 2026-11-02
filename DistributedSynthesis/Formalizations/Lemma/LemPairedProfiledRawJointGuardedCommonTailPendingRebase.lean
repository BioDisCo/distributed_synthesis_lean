/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonTailCoreAdapter

/-!
# Local rebasing at an unresolved guarded-common strict exit

After one strict round, the blind owner and the receiving common shadow are
locally ambiguous with a simultaneous round.  If the owner receives that
shadow on the next round, it can resume the occurrence-sensitive common
policy from the control carried by the delivered shadow.  Dually, a resolved
guarded receiver that later receives a common state can resume from the
delivered common control.

These maps are genuinely local: the unused old owner/receiver argument is
only the process's stored phase tag.  The new common control is read from the
delivered finite state.  The strict-reversal pair equations below show that
this rebasing agrees with the other process's local non-receive map.

No definition takes a graph, orientation, hierarchy side, leader bit,
semantic world, or history.
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

private abbrev CommonOne :=
  ProfiledRawJointGuardedInitialCommonOneState A strategy hwin

private abbrev CommonTwo :=
  ProfiledRawJointGuardedInitialCommonTwoState A strategy hwin

private abbrev InitialOne :=
  ProfiledRawJointGuardedCommonTailInitialOne A strategy hwin

private abbrev InitialTwo :=
  ProfiledRawJointGuardedCommonTailInitialTwo A strategy hwin

private abbrev ExceptionalOne :=
  ProfiledRawJointGuardedCommonTailExceptionalOne A strategy hwin

private abbrev ExceptionalTwo :=
  ProfiledRawJointGuardedCommonTailExceptionalTwo A strategy hwin

private abbrev OneControl :=
  ProfiledRawJointGuardedHybridCombinedOneControl A strategy hwin initialBank
    (InitialOne A strategy hwin) (ExceptionalOne A strategy hwin)

private abbrev TwoControl :=
  ProfiledRawJointGuardedHybridCombinedTwoControl A strategy hwin initialBank
    (InitialTwo A strategy hwin) (ExceptionalTwo A strategy hwin)

/-! ## Rebase from a pending blind owner -/

/-- Process one has the old strict-right owner, receives the process-two
common shadow, and resumes from the occurrence control carried by that
shadow. -/
noncomputable def profiledRawJointGuardedCommonTailRightPendingRebaseOne
    (_owner : ProfiledRawJointGuardedCommonRightOwner A strategy hwin)
    (two : CommonTwo A strategy hwin)
    (own : In₁) (delivered : In₂) :
    Out₁ × OneControl A strategy hwin initialBank :=
  profiledRawJointGuardedCommonTailInitialRecvOne A strategy hwin initialBank
    two.control own delivered

/-- Process-two mirror after a pending strict-left owner is delivered to
process two. -/
noncomputable def profiledRawJointGuardedCommonTailLeftPendingRebaseTwo
    (_owner : ProfiledRawJointGuardedCommonLeftOwner A strategy hwin)
    (one : CommonOne A strategy hwin)
    (own : In₂) (delivered : In₁) :
    Out₂ × TwoControl A strategy hwin initialBank :=
  profiledRawJointGuardedCommonTailInitialRecvTwo A strategy hwin initialBank
    one.control own delivered

/-! ## Rebase from an obsolete resolved receiver -/

/-- If a resolved strict-left receiver is delivered a current process-two
common state, the delivered occurrence control is sufficient to resume the
common process-one branch. -/
noncomputable def profiledRawJointGuardedCommonTailLeftReceiverRebaseOne
    (_receiver : ProfiledRawJointGuardedCommonTailLeftReceiver A strategy hwin)
    (two : CommonTwo A strategy hwin)
    (own : In₁) (delivered : In₂) :
    Out₁ × OneControl A strategy hwin initialBank :=
  profiledRawJointGuardedCommonTailInitialRecvOne A strategy hwin initialBank
    two.control own delivered

/-- Resolved strict-right mirror. -/
noncomputable def profiledRawJointGuardedCommonTailRightReceiverRebaseTwo
    (_receiver : ProfiledRawJointGuardedCommonTailRightReceiver A strategy hwin)
    (one : CommonOne A strategy hwin)
    (own : In₂) (delivered : In₁) :
    Out₂ × TwoControl A strategy hwin initialBank :=
  profiledRawJointGuardedCommonTailInitialRecvTwo A strategy hwin initialBank
    one.control own delivered

/-! ## Local strict-reversal pair equations -/

/-- A pending strict-right branch followed by an honest strict-left round
uses exactly the strict-left root record selected by the delivered common
occurrence. -/
theorem profiledRawJointGuardedCommonTailRightPendingRebase_strictLeft_outputs
    (owner : ProfiledRawJointGuardedCommonRightOwner A strategy hwin)
    (two : CommonTwo A strategy hwin) (input : In₁ × In₂) :
    ((profiledRawJointGuardedCommonTailRightPendingRebaseOne A strategy hwin
        initialBank owner two input.1 input.2).1,
      (profiledRawJointGuardedCommonTailCommonNoRecvTwo A strategy hwin
        initialBank two input.2).1) =
      let pair := profiledRawJointGuardedInitialCommonControlPair A strategy
        hwin two.control
      (pairedLeftInformedForRow .both
          (pair.leftRootRecord A strategy hwin input).2.1.physical,
        (pair.leftRootRecord A strategy hwin input).2.2) := by
  unfold profiledRawJointGuardedCommonTailRightPendingRebaseOne
    profiledRawJointGuardedCommonTailCommonNoRecvTwo
    profiledRawJointGuardedInitialCommonTwoNoRecv
    profiledRawJointGuardedCommonTwoShadowNoRecv
  rw [two.common_eq]
  exact profiledRawJointGuardedCommonTailInitialStrictLeft_outputs A strategy
    hwin initialBank two.control input

/-- Pending strict-left followed by strict-right. -/
theorem profiledRawJointGuardedCommonTailLeftPendingRebase_strictRight_outputs
    (one : CommonOne A strategy hwin)
    (owner : ProfiledRawJointGuardedCommonLeftOwner A strategy hwin)
    (input : In₁ × In₂) :
    ((profiledRawJointGuardedCommonTailCommonNoRecvOne A strategy hwin
        initialBank one input.1).1,
      (profiledRawJointGuardedCommonTailLeftPendingRebaseTwo A strategy hwin
        initialBank owner one input.2 input.1).1) =
      let pair := profiledRawJointGuardedInitialCommonControlPair A strategy
        hwin one.control
      ((pair.rightRootRecord A strategy hwin input).2.2,
        pairedRightInformedForRow .both
          (pair.rightRootRecord A strategy hwin input).2.1.physical) := by
  unfold profiledRawJointGuardedCommonTailLeftPendingRebaseTwo
    profiledRawJointGuardedCommonTailCommonNoRecvOne
    profiledRawJointGuardedInitialCommonOneNoRecv
    profiledRawJointGuardedCommonOneShadowNoRecv
  rw [one.common_eq]
  exact profiledRawJointGuardedCommonTailInitialStrictRight_outputs A strategy
    hwin initialBank one.control input

/-- The same equation applies when the obsolete local half was already a
resolved strict-right receiver. -/
theorem profiledRawJointGuardedCommonTailRightReceiverRebase_strictRight_outputs
    (one : CommonOne A strategy hwin)
    (receiver : ProfiledRawJointGuardedCommonTailRightReceiver A strategy hwin)
    (input : In₁ × In₂) :
    ((profiledRawJointGuardedCommonTailCommonNoRecvOne A strategy hwin
        initialBank one input.1).1,
      (profiledRawJointGuardedCommonTailRightReceiverRebaseTwo A strategy hwin
        initialBank receiver one input.2 input.1).1) =
      let pair := profiledRawJointGuardedInitialCommonControlPair A strategy
        hwin one.control
      ((pair.rightRootRecord A strategy hwin input).2.2,
        pairedRightInformedForRow .both
          (pair.rightRootRecord A strategy hwin input).2.1.physical) := by
  unfold profiledRawJointGuardedCommonTailRightReceiverRebaseTwo
    profiledRawJointGuardedCommonTailCommonNoRecvOne
    profiledRawJointGuardedInitialCommonOneNoRecv
    profiledRawJointGuardedCommonOneShadowNoRecv
  rw [one.common_eq]
  exact profiledRawJointGuardedCommonTailInitialStrictRight_outputs A strategy
    hwin initialBank one.control input

/-- Resolved strict-left mirror. -/
theorem profiledRawJointGuardedCommonTailLeftReceiverRebase_strictLeft_outputs
    (receiver : ProfiledRawJointGuardedCommonTailLeftReceiver A strategy hwin)
    (two : CommonTwo A strategy hwin) (input : In₁ × In₂) :
    ((profiledRawJointGuardedCommonTailLeftReceiverRebaseOne A strategy hwin
        initialBank receiver two input.1 input.2).1,
      (profiledRawJointGuardedCommonTailCommonNoRecvTwo A strategy hwin
        initialBank two input.2).1) =
      let pair := profiledRawJointGuardedInitialCommonControlPair A strategy
        hwin two.control
      (pairedLeftInformedForRow .both
          (pair.leftRootRecord A strategy hwin input).2.1.physical,
        (pair.leftRootRecord A strategy hwin input).2.2) := by
  unfold profiledRawJointGuardedCommonTailLeftReceiverRebaseOne
    profiledRawJointGuardedCommonTailCommonNoRecvTwo
    profiledRawJointGuardedInitialCommonTwoNoRecv
    profiledRawJointGuardedCommonTwoShadowNoRecv
  rw [two.common_eq]
  exact profiledRawJointGuardedCommonTailInitialStrictLeft_outputs A strategy
    hwin initialBank two.control input

end

end DetParityAutomaton

end DistributedSynthesis
