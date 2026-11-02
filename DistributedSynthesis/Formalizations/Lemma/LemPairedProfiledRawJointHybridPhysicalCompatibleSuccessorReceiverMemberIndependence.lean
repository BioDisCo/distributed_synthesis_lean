/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleSuccessorOperationalClose

/-!
# Full receiver-table independence of the old pending member

The physical sibling move ignores its proof-side member definitionally, not
only in the sender projection: `memberController_eq` identifies the complete
finite controller, including its receiver table.  The successor decoration
and its comapped monitor inherit that same equality.

The two regression theorems below compare the canonical receiver step, whose
implementation uses the `false` representative, with the complete decorated
label for an arbitrary already acknowledged `tableMember`.  They identify the
whole row-exact output (hence every target-table cell), the retained old row,
the next receiver-monitor state, and the staged output.  Consequently no
member-indexed receiver-state or payload transport is required.
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

/-! ## Successor-decorated full-controller equalities -/

/-- The complete successor monitor is independent of the member. -/
theorem profiledRawJointHybridPhysicalCompatibleSuccessorRightMonitor_eq
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (left right : Bool) :
    profiledRawJointHybridPhysicalCompatibleSuccessorRightMonitor A strategy
        hwin (initial := initial) move left =
      profiledRawJointHybridPhysicalCompatibleSuccessorRightMonitor A strategy
        hwin (initial := initial) move right :=
  rfl

/-- Right successor decoration preserves equality of the *whole* member
controller, including its receiver-output table. -/
theorem
    profiledRawJointHybridPhysicalCompatibleDecoratedRightMemberController_eq
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial)
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (left right : Bool) :
    profiledRawJointHybridPhysicalCompatibleDecoratedRightMemberController A
        strategy hwin policy state move left =
      profiledRawJointHybridPhysicalCompatibleDecoratedRightMemberController A
        strategy hwin policy state move right :=
  rfl

theorem profiledRawJointHybridPhysicalCompatibleSuccessorLeftMonitor_eq
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (left right : Bool) :
    profiledRawJointHybridPhysicalCompatibleSuccessorLeftMonitor A strategy
        hwin (initial := initial) move left =
      profiledRawJointHybridPhysicalCompatibleSuccessorLeftMonitor A strategy
        hwin (initial := initial) move right :=
  rfl

theorem
    profiledRawJointHybridPhysicalCompatibleDecoratedLeftMemberController_eq
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (left right : Bool) :
    profiledRawJointHybridPhysicalCompatibleDecoratedLeftMemberController A
        strategy hwin policy state move left =
      profiledRawJointHybridPhysicalCompatibleDecoratedLeftMemberController A
        strategy hwin policy state move right :=
  rfl

/-! ## Canonical-false receiver-step regressions -/

/-- The canonical right receiver step computes exactly the full label of any
old table member.  In particular its row-exact target table is not merely
sender-output coherent: it is definitionally the same table. -/
theorem
    profiledRawJointHybridPhysicalCompatibleRightReceiverStepFor_eq_member
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial)
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (tableMember : Bool)
    (owner : (move.memberController A false).Control)
    (row : PairedEntryRow)
    (monitorState :
      (profiledRawJointHybridPhysicalCompatibleSuccessorRightMonitor A
        strategy hwin (initial := initial) move false).State)
    (input : In₂ × In₁) :
    let monitor :=
      profiledRawJointHybridPhysicalCompatibleSuccessorRightMonitor A strategy
        hwin (initial := initial) move tableMember
    let controller :=
      profiledRawJointHybridPhysicalCompatibleDecoratedRightMemberController A
        strategy hwin policy state move tableMember
    let output := (controller.labelOf owner).2 monitorState input
    let result :=
      profiledRawJointHybridPhysicalCompatibleRightReceiverStepFor A strategy
        hwin policy state move owner row monitorState input
    result.1 = output ∧
      result.2.2.1 = row ∧
      result.2.2.2.1 = monitor.step monitorState
        (input, output, (controller.labelOf owner).1 input.2) ∧
      result.2.2.2.2 = some output := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Left mirror. -/
theorem
    profiledRawJointHybridPhysicalCompatibleLeftReceiverStepFor_eq_member
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (tableMember : Bool)
    (owner : (move.memberController A false).Control)
    (row : PairedEntryRow)
    (monitorState :
      (profiledRawJointHybridPhysicalCompatibleSuccessorLeftMonitor A strategy
        hwin (initial := initial) move false).State)
    (input : In₁ × In₂) :
    let monitor :=
      profiledRawJointHybridPhysicalCompatibleSuccessorLeftMonitor A strategy
        hwin (initial := initial) move tableMember
    let controller :=
      profiledRawJointHybridPhysicalCompatibleDecoratedLeftMemberController A
        strategy hwin policy state move tableMember
    let output := (controller.labelOf owner).2 monitorState input
    let result :=
      profiledRawJointHybridPhysicalCompatibleLeftReceiverStepFor A strategy
        hwin policy state move owner row monitorState input
    result.1 = output ∧
      result.2.2.1 = row ∧
      result.2.2.2.1 = monitor.step monitorState
        (input, output, (controller.labelOf owner).1 input.2) ∧
      result.2.2.2.2 = some output := by
  exact ⟨rfl, rfl, rfl, rfl⟩

end

end DetParityAutomaton

end DistributedSynthesis
