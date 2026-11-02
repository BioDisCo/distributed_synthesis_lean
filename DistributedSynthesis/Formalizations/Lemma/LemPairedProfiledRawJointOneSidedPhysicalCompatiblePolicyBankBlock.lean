/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedPhysicalCompatiblePolicyBank

/-!
# Physical-block closure of the recurrent one-sided policy bank

This file connects the abstract recurrent bank transition to the executable
finite physical sibling tables stored in its current annotation.  At an
arbitrary depth of either narrowed block controller, every emitted row target
is allowed by the installed table.  The bank's total finite resolver lifts
that bare target to a literal linked child of the same selected policy.

The lifted child retains the bank index, is reachable in that policy, and
carries the annotation installed by the same semantic step that produces the
bare target.  Thus recurrence does not select a new code-equal representative
or a new accepting policy at a block boundary.
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

private abbrev OneSidedState :=
  ProfiledRawJointOneSidedSemanticState A strategy (I := Unit)

private abbrev LinkedCode :=
  SourceFreeBeliefParentLinkedCode
    (BeliefCode := ProfiledRawJointIncidenceCode A (I := Unit))
    (Annotation := ProfiledRawJointHybridPhysicalEdgeAnnotation A)

/-! ## Right physical blocks -/

/-- Every row target of an arbitrarily advanced installed right table makes
one deterministic, semantically linked transition in the same recurrent
bank component. -/
theorem
    profiledRawJointOneSidedPhysicalCompatibleBankRightBlock_target
    (state : ProfiledRawJointOneSidedPhysicalCompatibleBankControl A strategy
      hwin)
    (hreachable :
      ProfiledRawJointOneSidedPhysicalCompatibleBankReachable A strategy hwin
        state)
    (currentCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (hcurrentCode : state.2.1.1 = currentCode)
    (root : ProfiledRawJointThreadRoot A)
    (hroot : profiledRawJointOneSidedCurrentSlots A .right currentCode () =
      some root)
    (phaseMove : ProfiledRawJointRightPhysicalSiblingMove A)
    (hphaseMove : state.2.1.2.1 = some phaseMove)
    (member : Bool) (env : Nat → In₂ × In₁) (n : Nat)
    (row : PairedEntryRow) :
    let monitor :=
      profiledRawJointRightPhysicalSiblingMonitor A phaseMove.1 member
    let controller := phaseMove.memberController A member
    let play := treePlay
      (narrowedInducedTree monitor controller.labeledTree) env
    let target := (play n).2.1.target row
    let childCode :=
      profiledRawJointOneSidedPhysicalCompatibleBankResolveTarget A strategy
        hwin state target
    childCode.1 = target ∧
      ProfiledRawJointOneSidedPhysicalCompatibleBankChildRealizes A strategy
        hwin state target childCode ∧
      (profiledRawJointOneSidedPhysicalCompatibleBankSuccessor A strategy hwin
        state childCode).1 = state.1 ∧
      ProfiledRawJointOneSidedPhysicalCompatibleBankReachable A strategy hwin
        (profiledRawJointOneSidedPhysicalCompatibleBankSuccessor A strategy
          hwin state childCode) ∧
      ∃ source : OneSidedState A strategy,
        ∃ actual : ProfiledRawJointActualDirection
            (I := Unit) (In₁ := In₁) (In₂ := In₂),
          (source.step A actual).code A = target ∧
            childCode.2 =
              profiledRawJointOneSidedPhysicalAnnotationAdvance A strategy
                hwin source state.2.1.2 actual ∧
            ProfiledRawJointOneSidedPhysicalAnnotationCompatible A strategy
              (source.step A actual) childCode.2 := by
  dsimp only
  have hsafe := phaseMove.memberController_targetSafe A member env n row
  have hresolve :=
    profiledRawJointOneSidedPhysicalCompatibleBankResolveRightTarget_spec A
      strategy hwin state hreachable currentCode hcurrentCode root hroot
        phaseMove hphaseMove _ hsafe.2
  refine ⟨hresolve.1, hresolve.2.1, hresolve.2.2.1,
    hresolve.2.2.2, ?_⟩
  exact
    ProfiledRawJointOneSidedPhysicalCompatibleBankChildRealizes.exists_child
      A strategy hwin state _ _ hresolve.2.1

/-! ## Left physical blocks -/

/-- Left-orientation mirror of arbitrary-depth recurrent block closure. -/
theorem
    profiledRawJointOneSidedPhysicalCompatibleBankLeftBlock_target
    (state : ProfiledRawJointOneSidedPhysicalCompatibleBankControl A strategy
      hwin)
    (hreachable :
      ProfiledRawJointOneSidedPhysicalCompatibleBankReachable A strategy hwin
        state)
    (currentCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (hcurrentCode : state.2.1.1 = currentCode)
    (root : ProfiledRawJointThreadRoot A)
    (hroot : profiledRawJointOneSidedCurrentSlots A .left currentCode () =
      some root)
    (phaseMove : ProfiledRawJointLeftPhysicalSiblingMove A)
    (hphaseMove : state.2.1.2.2 = some phaseMove)
    (member : Bool) (env : Nat → In₁ × In₂) (n : Nat)
    (row : PairedEntryRow) :
    let monitor :=
      profiledRawJointLeftPhysicalSiblingMonitor A phaseMove.1 member
    let controller := phaseMove.memberController A member
    let play := treePlay
      (narrowedInducedTree monitor controller.labeledTree) env
    let target := (play n).2.1.target row
    let childCode :=
      profiledRawJointOneSidedPhysicalCompatibleBankResolveTarget A strategy
        hwin state target
    childCode.1 = target ∧
      ProfiledRawJointOneSidedPhysicalCompatibleBankChildRealizes A strategy
        hwin state target childCode ∧
      (profiledRawJointOneSidedPhysicalCompatibleBankSuccessor A strategy hwin
        state childCode).1 = state.1 ∧
      ProfiledRawJointOneSidedPhysicalCompatibleBankReachable A strategy hwin
        (profiledRawJointOneSidedPhysicalCompatibleBankSuccessor A strategy
          hwin state childCode) ∧
      ∃ source : OneSidedState A strategy,
        ∃ actual : ProfiledRawJointActualDirection
            (I := Unit) (In₁ := In₁) (In₂ := In₂),
          (source.step A actual).code A = target ∧
            childCode.2 =
              profiledRawJointOneSidedPhysicalAnnotationAdvance A strategy
                hwin source state.2.1.2 actual ∧
            ProfiledRawJointOneSidedPhysicalAnnotationCompatible A strategy
              (source.step A actual) childCode.2 := by
  dsimp only
  have hsafe := phaseMove.memberController_targetSafe A member env n row
  have hresolve :=
    profiledRawJointOneSidedPhysicalCompatibleBankResolveLeftTarget_spec A
      strategy hwin state hreachable currentCode hcurrentCode root hroot
        phaseMove hphaseMove _ hsafe.2
  refine ⟨hresolve.1, hresolve.2.1, hresolve.2.2.1,
    hresolve.2.2.2, ?_⟩
  exact
    ProfiledRawJointOneSidedPhysicalCompatibleBankChildRealizes.exists_child
      A strategy hwin state _ _ hresolve.2.1

end

end DetParityAutomaton

end DistributedSynthesis
