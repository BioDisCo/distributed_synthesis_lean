/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointFinitePhysicalSiblingMove
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointSiblingHiddenThreadContinuation
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridSiblingCoupledRationalization

/-!
# The initial hidden switch as one finite sibling move

This file instantiates the finite physical sibling alphabet at the first
common/strict ambiguity of the hybrid construction.  The simultaneous child
and its strict-left sibling use the two projections of one right move; the
simultaneous child and its strict-right sibling use the projections of one
left move.

The member Boolean below is proof-side only.  The two projections have the
same sender control and output, so neither process is told the graph,
orientation, or strict leader.  Every target emitted by either projection is
a shared semantic successor and therefore starts an unconditional finite
one-sided target policy.
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

/-! ## Right/common--strict-left projection -/

/-- The actual initial process-one sibling pair as one member of the fixed
finite physical move alphabet. -/
noncomputable def profiledRawJointHybridInitialRightPhysicalSiblingMove
    (first current : In₁ × In₂) :
    ProfiledRawJointRightPhysicalSiblingMove A :=
  profiledRawJointRightPhysicalSiblingMoveOf A hwin
    (profiledRawJointHybridInitialSiblingParentFamily A strategy first)
    (profiledRawJointHybridInitialSiblingDirection current)
    ((profiledRawJointHybridInitialSiblingWorld A strategy first current
      ).procOneMember A)
    (profiledRawJointHybridInitialCommonSemanticSibling_right A strategy
      first current)

/-- The common (`false`) and strict-left (`true`) interpretations have
literally the same process-one blind control. -/
theorem profiledRawJointHybridInitialRightPhysicalSiblingMove_control_eq
    (first current : In₁ × In₂) (word : List In₁) :
    ((profiledRawJointHybridInitialRightPhysicalSiblingMove A strategy hwin
      first current).memberController A false).controlAt word =
    ((profiledRawJointHybridInitialRightPhysicalSiblingMove A strategy hwin
      first current).memberController A true).controlAt word := by
  exact (profiledRawJointHybridInitialRightPhysicalSiblingMove A strategy hwin
    first current).memberController_control_eq A false true word

/-- In particular, the two hidden interpretations emit the same blind
process-one output at every local input word. -/
theorem profiledRawJointHybridInitialRightPhysicalSiblingMove_sender_eq
    (first current : In₁ × In₂) (word : List In₁) :
    (((profiledRawJointHybridInitialRightPhysicalSiblingMove A strategy hwin
      first current).memberController A false).labeledTree word).1 =
    (((profiledRawJointHybridInitialRightPhysicalSiblingMove A strategy hwin
      first current).memberController A true).labeledTree word).1 := by
  exact (profiledRawJointHybridInitialRightPhysicalSiblingMove A strategy hwin
    first current).memberController_sender_eq A false true word

/-- Every target actually emitted by either initial right projection starts
an unconditional finite recurrent policy. -/
theorem nonempty_profiledRawJointHybridInitialRightTargetPolicy
    (first current : In₁ × In₂) (member : Bool)
    (env : Nat → In₂ × In₁) (n : Nat) (row : PairedEntryRow) :
    let family :=
      profiledRawJointHybridInitialSiblingParentFamily A strategy first
    let direction := profiledRawJointHybridInitialSiblingDirection current
    let semanticMember :=
      (profiledRawJointHybridInitialSiblingWorld A strategy first current
        ).procOneMember A
    let move := profiledRawJointHybridInitialRightPhysicalSiblingMove A
      strategy hwin first current
    let monitor := profiledRawJointRightPhysicalSiblingMonitor A move.1 member
    let controller := move.memberController A member
    let play := treePlay
      (narrowedInducedTree monitor controller.labeledTree) env
    Nonempty (ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      ((play n).2.1.target row)) := by
  dsimp only
  let family :=
    profiledRawJointHybridInitialSiblingParentFamily A strategy first
  let direction := profiledRawJointHybridInitialSiblingDirection current
  let semanticMember :=
    (profiledRawJointHybridInitialSiblingWorld A strategy first current
      ).procOneMember A
  have htarget :=
    profiledRawJointRightPhysicalSiblingMoveOf_targetSafe_shared A hwin
      family direction semanticMember
      (profiledRawJointHybridInitialCommonSemanticSibling_right A strategy
        first current) member env n row
  exact nonempty_profiledRawJointRightSiblingTargetRationalPolicy A hwin
    family direction _ htarget.2

/-! ## Left/common--strict-right projection -/

noncomputable def profiledRawJointHybridInitialLeftPhysicalSiblingMove
    (first current : In₁ × In₂) :
    ProfiledRawJointLeftPhysicalSiblingMove A :=
  profiledRawJointLeftPhysicalSiblingMoveOf A hwin
    (profiledRawJointHybridInitialSiblingParentFamily A strategy first)
    (profiledRawJointHybridInitialSiblingDirection current)
    ((profiledRawJointHybridInitialSiblingWorld A strategy first current
      ).procTwoMember A)
    (profiledRawJointHybridInitialCommonSemanticSibling_left A strategy
      first current)

/-- Process-two common/strict-right control equality. -/
theorem profiledRawJointHybridInitialLeftPhysicalSiblingMove_control_eq
    (first current : In₁ × In₂) (word : List In₂) :
    ((profiledRawJointHybridInitialLeftPhysicalSiblingMove A strategy hwin
      first current).memberController A false).controlAt word =
    ((profiledRawJointHybridInitialLeftPhysicalSiblingMove A strategy hwin
      first current).memberController A true).controlAt word := by
  exact (profiledRawJointHybridInitialLeftPhysicalSiblingMove A strategy hwin
    first current).memberController_control_eq A false true word

theorem profiledRawJointHybridInitialLeftPhysicalSiblingMove_sender_eq
    (first current : In₁ × In₂) (word : List In₂) :
    (((profiledRawJointHybridInitialLeftPhysicalSiblingMove A strategy hwin
      first current).memberController A false).labeledTree word).1 =
    (((profiledRawJointHybridInitialLeftPhysicalSiblingMove A strategy hwin
      first current).memberController A true).labeledTree word).1 := by
  exact (profiledRawJointHybridInitialLeftPhysicalSiblingMove A strategy hwin
    first current).memberController_sender_eq A false true word

/-- Every target emitted by either initial left projection starts the finite
recurrent policy below that target. -/
theorem nonempty_profiledRawJointHybridInitialLeftTargetPolicy
    (first current : In₁ × In₂) (member : Bool)
    (env : Nat → In₁ × In₂) (n : Nat) (row : PairedEntryRow) :
    let family :=
      profiledRawJointHybridInitialSiblingParentFamily A strategy first
    let direction := profiledRawJointHybridInitialSiblingDirection current
    let semanticMember :=
      (profiledRawJointHybridInitialSiblingWorld A strategy first current
        ).procTwoMember A
    let move := profiledRawJointHybridInitialLeftPhysicalSiblingMove A
      strategy hwin first current
    let monitor := profiledRawJointLeftPhysicalSiblingMonitor A move.1 member
    let controller := move.memberController A member
    let play := treePlay
      (narrowedInducedTree monitor controller.labeledTree) env
    Nonempty (ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      ((play n).2.1.target row)) := by
  dsimp only
  let family :=
    profiledRawJointHybridInitialSiblingParentFamily A strategy first
  let direction := profiledRawJointHybridInitialSiblingDirection current
  let semanticMember :=
    (profiledRawJointHybridInitialSiblingWorld A strategy first current
      ).procTwoMember A
  have htarget :=
    profiledRawJointLeftPhysicalSiblingMoveOf_targetSafe_shared A hwin family
      direction semanticMember
      (profiledRawJointHybridInitialCommonSemanticSibling_left A strategy
        first current) member env n row
  exact nonempty_profiledRawJointLeftSiblingTargetRationalPolicy A hwin family
    direction _ htarget.2

end

end DetParityAutomaton

end DistributedSynthesis
