/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatiblePolicy
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridCommonMoveData
import DistributedSynthesis.Formalizations.Lemma.LemSourceFreeBeliefRootPinnedTailAcceptance

/-!
# One-shot root pinning with the physical compatibility invariant

The common/shadow front has already selected one literal common move before a
strict block starts.  An independently rationalized compatible policy need
not select that move at its root.  This file removes that mismatch at the
correct granularity: the root guard pins the parent-linked move once, while
the ordinary tail keeps the strengthened current-source/table compatibility
predicate at every later node.

The guard is proof memory in the input-free tree automaton.  It is not a
controller bit and does not tell either endpoint which process is informed.
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

private abbrev HybridDirection :=
  ProfiledRawJointHybridDirection (In₁ := In₁) (In₂ := In₂)

private abbrev PhysicalAnnotation :=
  ProfiledRawJointHybridPhysicalEdgeAnnotation A

private abbrev LinkedCode :=
  SourceFreeBeliefParentLinkedCode
    (BeliefCode := ProfiledRawJointHybridCode A)
    (Annotation := PhysicalAnnotation A)

private abbrev LinkedMove :=
  SourceFreeBeliefParentLinkedMove
    (Direction := HybridDirection (In₁ := In₁) (In₂ := In₂))
    (Move := ProfiledRawJointHybridMove A)
    (Annotation := PhysicalAnnotation A)

/-- The physical-compatible parent-linked policy with a predicate checked
only at its fresh common root. -/
noncomputable abbrev
    ProfiledRawJointHybridPhysicalCompatibleRootPinnedPolicy
    (initial : ProfiledRawJointCommonBaseWorld A strategy)
    (RootPred : LinkedMove A → Prop) :=
  SourceFreeBeliefFiniteCodeRootPinnedPolicy
    (sourceFreeBeliefParentLinkedCodeParityDPA
      (Annotation := PhysicalAnnotation A)
      (profiledRawJointHybridCodeParityDPA A
        (.common ((profiledRawJointCommonWorldFamily A initial).incidenceCode
          A))))
    ((.common ((profiledRawJointCommonWorldFamily A initial).incidenceCode A)),
      profiledRawJointHybridInitialPhysicalAnnotation A)
    (sourceFreeBeliefParentLinkedValid
      (ProfiledRawJointHybridProvenanceValid A strategy)
      (ProfiledRawJointHybridPhysicalCompatibleParentLinkValid A strategy
        hwin))
    (sourceFreeBeliefParentLinkedNext (profiledRawJointHybridNext A))
    RootPred

/-- The literal parent-linked move at the carried common root. -/
noncomputable def
    profiledRawJointHybridLiteralPhysicalRootMove
    (initial : ProfiledRawJointCommonBaseWorld A strategy) : LinkedMove A :=
  let raw := profiledRawJointHybridSemanticTree A initial
  let carried := raw.carryFiniteAnnotation
    (profiledRawJointHybridInitialPhysicalAnnotation A)
    (profiledRawJointHybridPhysicalAnnotationAdvance A strategy hwin)
  let linked := carried.parentLinkFiniteAnnotation Prod.snd
  linked.move linked.initial

/-- Any one-shot predicate true of the literal carried root move can be
retained unconditionally by finite-code root-pinned rationalization. -/
theorem
    nonempty_profiledRawJointHybridPhysicalCompatibleRootPinnedPolicy
    (initial : ProfiledRawJointCommonBaseWorld A strategy)
    (RootPred : LinkedMove A → Prop)
    (hroot : RootPred
      (profiledRawJointHybridLiteralPhysicalRootMove A strategy hwin initial)) :
    Nonempty
      (ProfiledRawJointHybridPhysicalCompatibleRootPinnedPolicy A strategy hwin
        initial RootPred) := by
  let raw := profiledRawJointHybridSemanticTree A initial
  let initialAnnotation := profiledRawJointHybridInitialPhysicalAnnotation A
  let advance :=
    profiledRawJointHybridPhysicalAnnotationAdvance A strategy hwin
  let carried := raw.carryFiniteAnnotation initialAnnotation advance
  let initialCode : ProfiledRawJointHybridCode A :=
    .common ((profiledRawJointCommonWorldFamily A initial).incidenceCode A)
  let certificate :=
    profiledRawJointHybridSemanticTree_codeParityCertificate A strategy hwin
      initial
  let carriedCertificate :=
    certificate.carryFiniteAnnotation
      (profiledRawJointHybridCodeParityDPA A initialCode)
      initialCode
      (ProfiledRawJointHybridProvenanceValid A strategy)
      (profiledRawJointHybridNext A)
      raw initialAnnotation advance
  let linked := carried.parentLinkFiniteAnnotation Prod.snd
  let linkedCertificate := carriedCertificate.parentLinkFiniteAnnotation
    (profiledRawJointHybridCodeParityDPA A initialCode)
    initialCode
    (ProfiledRawJointHybridProvenanceValid A strategy)
    (profiledRawJointHybridNext A)
    carried Prod.snd
    (ProfiledRawJointHybridPhysicalCompatibleParentLinkValid A strategy hwin)
    (fun node ↦ by
      let state := carried.stateAt node
      exact
        profiledRawJointHybridPhysicalCompatibleParentLinkValid_of_semantic A
          strategy hwin state.1 state.2
            (profiledRawJointHybridPhysicalCarriedTree_currentCompatible A
              strategy hwin initial node))
  exact
    linkedCertificate.nonempty_finiteCodeDirectionRootPinnedRationalPolicy
      (sourceFreeBeliefParentLinkedCodeParityDPA
        (Annotation := PhysicalAnnotation A)
        (profiledRawJointHybridCodeParityDPA A initialCode))
      (initialCode, initialAnnotation)
      (sourceFreeBeliefParentLinkedValid
        (ProfiledRawJointHybridProvenanceValid A strategy)
        (ProfiledRawJointHybridPhysicalCompatibleParentLinkValid A strategy
          hwin))
      (sourceFreeBeliefParentLinkedNext (profiledRawJointHybridNext A))
      linked RootPred (by
        simpa [profiledRawJointHybridLiteralPhysicalRootMove, raw, carried,
          linked] using hroot)

/-- Pin exactly the public raw move already installed by the common/shadow
front.  The child-annotation component remains free only in syntax; the
strengthened parent-link predicate ties it to the same literal source. -/
def profiledRawJointHybridPhysicalCompatibleInstalledRootPred
    (installed : ProfiledRawJointHybridCommonMoveData A strategy) :
    LinkedMove A → Prop :=
  fun move ↦ move.1 = some installed.rawMove

/-- The literal carried root satisfies the installed-move predicate. -/
theorem
    profiledRawJointHybridPhysicalCompatibleInstalledRootPred_literal
    (installed : ProfiledRawJointHybridCommonMoveData A strategy) :
    profiledRawJointHybridPhysicalCompatibleInstalledRootPred A strategy
      installed
      (profiledRawJointHybridLiteralPhysicalRootMove A strategy hwin
        installed.world) := by
  change
    some ((profiledRawJointCommonWorldFamily A installed.world).move A) =
      some installed.rawMove
  rw [installed.move_eq]

/-- Therefore every finite installed common/shadow move has a guarded
physical-compatible rational continuation fixed before the environment. -/
theorem
    nonempty_profiledRawJointHybridPhysicalCompatibleInstalledRootPinnedPolicy
    (installed : ProfiledRawJointHybridCommonMoveData A strategy) :
    Nonempty
      (ProfiledRawJointHybridPhysicalCompatibleRootPinnedPolicy A strategy hwin
        installed.world
        (profiledRawJointHybridPhysicalCompatibleInstalledRootPred A strategy
          installed)) := by
  exact
    nonempty_profiledRawJointHybridPhysicalCompatibleRootPinnedPolicy A
      strategy hwin installed.world
      (profiledRawJointHybridPhysicalCompatibleInstalledRootPred A strategy
        installed)
      (profiledRawJointHybridPhysicalCompatibleInstalledRootPred_literal A
        strategy hwin installed)

/-- Select the root-pinned continuation once for this finite installed move. -/
noncomputable def
    profiledRawJointHybridPhysicalCompatibleInstalledRootPinnedPolicy
    (installed : ProfiledRawJointHybridCommonMoveData A strategy) :
    ProfiledRawJointHybridPhysicalCompatibleRootPinnedPolicy A strategy hwin
      installed.world
      (profiledRawJointHybridPhysicalCompatibleInstalledRootPred A strategy
        installed) :=
  Classical.choice
    (nonempty_profiledRawJointHybridPhysicalCompatibleInstalledRootPinnedPolicy
      A strategy hwin installed)

/-- The selected guarded policy's root move is literally the installed raw
move.  This is the alignment that an arbitrary compatible policy lacked. -/
theorem
    profiledRawJointHybridPhysicalCompatibleInstalledRootPinnedPolicy_move
    (installed : ProfiledRawJointHybridCommonMoveData A strategy) :
    (profiledRawJointHybridPhysicalCompatibleInstalledRootPinnedPolicy A
      strategy hwin installed).rootMove.1 = some installed.rawMove := by
  exact
    (profiledRawJointHybridPhysicalCompatibleInstalledRootPinnedPolicy A
      strategy hwin installed).rootMove_realizes.2.1

end

end DetParityAutomaton

end DistributedSynthesis
