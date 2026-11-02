/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointFinitePhysicalSiblingMove
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointSiblingHiddenThreadContinuation
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridRootPinnedCommonBackbone

/-!
# A coupled sibling table at every recurrent common control

The initial sibling construction is not enough for a run containing an
arbitrary finite prefix of simultaneous rounds.  At every reachable finite
common control, a further simultaneous round and either strict interpretation
are still children of one literal semantic family.  This file performs the
finite sibling extraction at that point, before the common and strict children
can select independent policy moves.

The resulting right and left tables are indexed only by the finite common
control and current input pair.  Their Boolean member is proof-side only; both
members use definitionally the same complete controller.  No executable map
accepts a graph, orientation, strict-leader bit, or semantic history.
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

private abbrev CommonControl :=
  ProfiledRawJointHybridRootPinnedCommonControl A strategy hwin

/-! ## Literal sibling source at an arbitrary common control -/

/-- The semantic family installed at a reachable finite common control. -/
noncomputable def profiledRawJointHybridCommonSiblingParentFamily
    (control : CommonControl A strategy hwin) :
    ProfiledRawJointSemanticFamily A strategy (I := Unit) :=
  profiledRawJointCommonWorldFamily A
    (profiledRawJointHybridRootPinnedCommonInstalled A strategy hwin control
      ).world

/-- The literal common world reached by the current simultaneous input. -/
noncomputable def profiledRawJointHybridCommonSiblingWorld
    (control : CommonControl A strategy hwin) (current : In₁ × In₂) :
    ProfiledRawJointCommonBaseWorld A strategy :=
  profiledRawJointCommonWorldAfterBoth A
    (profiledRawJointHybridRootPinnedCommonInstalled A strategy hwin control
      ).world current

section
omit [DecidableEq In₁] [DecidableEq In₂] [Inhabited Out₁] [Inhabited Out₂]

/-- The common semantic child is exactly the next literal common world. -/
theorem profiledRawJointHybridCommonSibling_semanticChild_eq_world
    (control : CommonControl A strategy hwin) (current : In₁ × In₂) :
    (profiledRawJointHybridCommonSiblingParentFamily A strategy hwin control
      ).semanticChild A (profiledRawJointBothRestartDirection current) =
      profiledRawJointCommonWorldFamily A
        (profiledRawJointHybridCommonSiblingWorld A strategy hwin control
          current) := by
  exact profiledRawJointCommonWorld_semanticChild_eq_bothRestart A
    (profiledRawJointHybridRootPinnedCommonInstalled A strategy hwin control
      ).world current

/-- The complete process-one entry shared by the common and strict-left
interpretations. -/
@[simp] theorem profiledRawJointHybridCommonSibling_right
    (control : CommonControl A strategy hwin) (current : In₁ × In₂) :
    ((profiledRawJointHybridCommonSiblingParentFamily A strategy hwin control
      ).semanticChild A (profiledRawJointBothRestartDirection current)).right
        () =
      some ((profiledRawJointHybridCommonSiblingWorld A strategy hwin control
        current).procOneMember A) := by
  rw [profiledRawJointHybridCommonSibling_semanticChild_eq_world]
  rfl

/-- Process-two mirror. -/
@[simp] theorem profiledRawJointHybridCommonSibling_left
    (control : CommonControl A strategy hwin) (current : In₁ × In₂) :
    ((profiledRawJointHybridCommonSiblingParentFamily A strategy hwin control
      ).semanticChild A (profiledRawJointBothRestartDirection current)).left
        () =
      some ((profiledRawJointHybridCommonSiblingWorld A strategy hwin control
        current).procTwoMember A) := by
  rw [profiledRawJointHybridCommonSibling_semanticChild_eq_world]
  rfl

end

/-! ## One finite table for each common/strict sibling pair -/

/-- The right/common--strict-left table selected before either child chooses
an independent policy move. -/
noncomputable def profiledRawJointHybridCommonRightPhysicalSiblingMove
    (control : CommonControl A strategy hwin) (current : In₁ × In₂) :
    ProfiledRawJointRightPhysicalSiblingMove A :=
  profiledRawJointRightPhysicalSiblingMoveOf A hwin
    (profiledRawJointHybridCommonSiblingParentFamily A strategy hwin control)
    (profiledRawJointBothRestartDirection current)
    ((profiledRawJointHybridCommonSiblingWorld A strategy hwin control current
      ).procOneMember A)
    (profiledRawJointHybridCommonSibling_right A strategy hwin control current)

/-- The complete right controller is independent of the hidden common/strict
explanation. -/
theorem profiledRawJointHybridCommonRightPhysicalSiblingMove_controller_eq
    (control : CommonControl A strategy hwin) (current : In₁ × In₂)
    (left right : Bool) :
    (profiledRawJointHybridCommonRightPhysicalSiblingMove A strategy hwin
      control current).memberController A left =
    (profiledRawJointHybridCommonRightPhysicalSiblingMove A strategy hwin
      control current).memberController A right :=
  rfl

/-- Left/common--strict-right mirror. -/
noncomputable def profiledRawJointHybridCommonLeftPhysicalSiblingMove
    (control : CommonControl A strategy hwin) (current : In₁ × In₂) :
    ProfiledRawJointLeftPhysicalSiblingMove A :=
  profiledRawJointLeftPhysicalSiblingMoveOf A hwin
    (profiledRawJointHybridCommonSiblingParentFamily A strategy hwin control)
    (profiledRawJointBothRestartDirection current)
    ((profiledRawJointHybridCommonSiblingWorld A strategy hwin control current
      ).procTwoMember A)
    (profiledRawJointHybridCommonSibling_left A strategy hwin control current)

theorem profiledRawJointHybridCommonLeftPhysicalSiblingMove_controller_eq
    (control : CommonControl A strategy hwin) (current : In₁ × In₂)
    (left right : Bool) :
    (profiledRawJointHybridCommonLeftPhysicalSiblingMove A strategy hwin
      control current).memberController A left =
    (profiledRawJointHybridCommonLeftPhysicalSiblingMove A strategy hwin
      control current).memberController A right :=
  rfl

/-! ## Every emitted target starts the unconditional recurrent policy -/

theorem nonempty_profiledRawJointHybridCommonRightTargetPolicy
    (control : CommonControl A strategy hwin) (current : In₁ × In₂)
    (member : Bool) (env : Nat → In₂ × In₁) (n : Nat)
    (row : PairedEntryRow) :
    let family :=
      profiledRawJointHybridCommonSiblingParentFamily A strategy hwin control
    let direction := profiledRawJointBothRestartDirection current
    let move := profiledRawJointHybridCommonRightPhysicalSiblingMove A strategy
      hwin control current
    let monitor := profiledRawJointRightPhysicalSiblingMonitor A move.1 member
    let controller := move.memberController A member
    let play := treePlay
      (narrowedInducedTree monitor controller.labeledTree) env
    Nonempty (ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      ((play n).2.1.target row)) := by
  dsimp only
  let family :=
    profiledRawJointHybridCommonSiblingParentFamily A strategy hwin control
  let direction := profiledRawJointBothRestartDirection current
  let semanticMember :=
    (profiledRawJointHybridCommonSiblingWorld A strategy hwin control current
      ).procOneMember A
  have htarget :=
    profiledRawJointRightPhysicalSiblingMoveOf_targetSafe_shared A hwin family
      direction semanticMember
      (profiledRawJointHybridCommonSibling_right A strategy hwin control
        current) member env n row
  exact nonempty_profiledRawJointRightSiblingTargetRationalPolicy A hwin family
    direction _ htarget.2

theorem nonempty_profiledRawJointHybridCommonLeftTargetPolicy
    (control : CommonControl A strategy hwin) (current : In₁ × In₂)
    (member : Bool) (env : Nat → In₁ × In₂) (n : Nat)
    (row : PairedEntryRow) :
    let family :=
      profiledRawJointHybridCommonSiblingParentFamily A strategy hwin control
    let direction := profiledRawJointBothRestartDirection current
    let move := profiledRawJointHybridCommonLeftPhysicalSiblingMove A strategy
      hwin control current
    let monitor := profiledRawJointLeftPhysicalSiblingMonitor A move.1 member
    let controller := move.memberController A member
    let play := treePlay
      (narrowedInducedTree monitor controller.labeledTree) env
    Nonempty (ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      ((play n).2.1.target row)) := by
  dsimp only
  let family :=
    profiledRawJointHybridCommonSiblingParentFamily A strategy hwin control
  let direction := profiledRawJointBothRestartDirection current
  let semanticMember :=
    (profiledRawJointHybridCommonSiblingWorld A strategy hwin control current
      ).procTwoMember A
  have htarget :=
    profiledRawJointLeftPhysicalSiblingMoveOf_targetSafe_shared A hwin family
      direction semanticMember
      (profiledRawJointHybridCommonSibling_left A strategy hwin control current)
      member env n row
  exact nonempty_profiledRawJointLeftSiblingTargetRationalPolicy A hwin family
    direction _ htarget.2

end

end DetParityAutomaton

end DistributedSynthesis
