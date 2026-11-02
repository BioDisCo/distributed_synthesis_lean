/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatiblePolicy
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleShadowPhaseLiveOccurrenceAnnotation

/-!
# Physical-compatible hybrid policies with one jointly rationalized extra

The live-tail switch cannot safely combine the physical-compatible policy
with a table selected by a second rationalization.  Even if both objects have
the same public incidence code, their semantic representatives -- and hence
their DPA entry states -- need not have a common origin.

This file gives the minimal carrier for the positive construction.  An
arbitrary finite `Extra` is carried *in the same parent-linked annotation* as
the physical sibling moves.  One reachable-policy inversion therefore
returns one semantic source which simultaneously explains

* the current public code and raw move;
* compatibility of the current physical sibling moves;
* every physical child annotation; and
* every extra child payload.

The intended concrete `Extra` is the uniform, type-erased ID of the
heterogeneous staged seam (including the controls needed at a later
reversal).  This module deliberately does not pretend that the older staged
seam, indexed by a separately rationalized guarded-common package, has that
type: no sound cast from those old controls to the re-rooted tail policy is
available.

`extraAdvance` is proof-tree data used while extracting the one finite
policy.  It is never supplied to an executable endpoint, and no definition
below gives an endpoint a graph, hierarchy side, leader bit, strict-leader
bit, semantic history, or view.
-/

namespace DistributedSynthesis

universe u v x y s b

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

variable (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
variable
  (hwin : ∀ env : EnvironmentSequence In₁ In₂,
    A.Accepts (execution strategy env))

variable {Extra : Type b} [Fintype Extra]

private abbrev HybridState :=
  ProfiledRawJointHybridSemanticState A strategy

private abbrev HybridDirection :=
  ProfiledRawJointHybridDirection (In₁ := In₁) (In₂ := In₂)

private abbrev PhysicalAnnotation :=
  ProfiledRawJointHybridPhysicalEdgeAnnotation A

/-! ## The combined finite annotation -/

/-- The existing physical payload and one additional payload selected at the
same semantic edge and retained by the same rational policy. -/
abbrev ProfiledRawJointHybridPhysicalCompatibleExtraAnnotation
    (Extra : Type b) :=
  PhysicalAnnotation A × Extra

instance [Fintype Extra] :
    Fintype (ProfiledRawJointHybridPhysicalCompatibleExtraAnnotation A Extra) :=
  inferInstance

def profiledRawJointHybridPhysicalCompatibleExtraInitial
    (initialExtra : Extra) :
    ProfiledRawJointHybridPhysicalCompatibleExtraAnnotation A Extra :=
  (profiledRawJointHybridInitialPhysicalAnnotation A, initialExtra)

/-- Both components are updated from the same literal source and whole-block
direction.  The preceding extra is available for genuinely staged
replace/update semantics; it is not reconstructed from the public code. -/
def profiledRawJointHybridPhysicalCompatibleExtraAdvance
    (extraAdvance : HybridState A strategy → Extra →
      HybridDirection (In₁ := In₁) (In₂ := In₂) → Extra)
    (source : HybridState A strategy)
    (current : ProfiledRawJointHybridPhysicalCompatibleExtraAnnotation A
      Extra)
    (direction : HybridDirection (In₁ := In₁) (In₂ := In₂)) :
    ProfiledRawJointHybridPhysicalCompatibleExtraAnnotation A Extra :=
  (profiledRawJointHybridPhysicalAnnotationAdvance A strategy hwin source
      current.1 direction,
    extraAdvance source current.2 direction)

omit [Fintype Extra] in
@[simp] theorem
    profiledRawJointHybridPhysicalCompatibleExtraAdvance_fst
    (extraAdvance : HybridState A strategy → Extra →
      HybridDirection (In₁ := In₁) (In₂ := In₂) → Extra)
    (source : HybridState A strategy)
    (current : ProfiledRawJointHybridPhysicalCompatibleExtraAnnotation A
      Extra)
    (direction : HybridDirection (In₁ := In₁) (In₂ := In₂)) :
    (profiledRawJointHybridPhysicalCompatibleExtraAdvance A strategy hwin
      extraAdvance source current direction).1 =
      profiledRawJointHybridPhysicalAnnotationAdvance A strategy hwin source
        current.1 direction :=
  rfl

omit [Fintype Extra] in
@[simp] theorem
    profiledRawJointHybridPhysicalCompatibleExtraAdvance_snd
    (extraAdvance : HybridState A strategy → Extra →
      HybridDirection (In₁ := In₁) (In₂ := In₂) → Extra)
    (source : HybridState A strategy)
    (current : ProfiledRawJointHybridPhysicalCompatibleExtraAnnotation A
      Extra)
    (direction : HybridDirection (In₁ := In₁) (In₂ := In₂)) :
    (profiledRawJointHybridPhysicalCompatibleExtraAdvance A strategy hwin
      extraAdvance source current direction).2 =
      extraAdvance source current.2 direction :=
  rfl

/-! ## One source explains both components -/

/-- The strengthened parent link.  Notice that compatibility is about the
physical component already stored in `current`; the extra and every child
annotation are then tied to the very same source. -/
def ProfiledRawJointHybridPhysicalCompatibleExtraParentLinkValid
    (extraAdvance : HybridState A strategy → Extra →
      HybridDirection (In₁ := In₁) (In₂ := In₂) → Extra)
    (code : ProfiledRawJointHybridCode A)
    (current : ProfiledRawJointHybridPhysicalCompatibleExtraAnnotation A
      Extra)
    (move : ProfiledRawJointHybridMove A)
    (children : HybridDirection (In₁ := In₁) (In₂ := In₂) →
      ProfiledRawJointHybridPhysicalCompatibleExtraAnnotation A Extra) : Prop :=
  ∃ source : HybridState A strategy,
    source.code A = code ∧
      source.move A = move ∧
      ProfiledRawJointHybridPhysicalCurrentCompatible A strategy source
        current.1 ∧
      ∀ direction,
        profiledRawJointHybridPhysicalCompatibleExtraAdvance A strategy hwin
            extraAdvance source current direction =
          children direction

omit [Fintype Extra] in
/-- Along the literal product-carried tree, the physical projection remains
compatible with the literal current source. -/
theorem profiledRawJointHybridPhysicalCompatibleExtraCarriedTree_current
    (initial : ProfiledRawJointCommonBaseWorld A strategy)
    (initialExtra : Extra)
    (extraAdvance : HybridState A strategy → Extra →
      HybridDirection (In₁ := In₁) (In₂ := In₂) → Extra)
    (node : TreeNode (HybridDirection (In₁ := In₁) (In₂ := In₂))) :
    let carried :=
      (profiledRawJointHybridSemanticTree A initial).carryFiniteAnnotation
        (profiledRawJointHybridPhysicalCompatibleExtraInitial A initialExtra)
        (profiledRawJointHybridPhysicalCompatibleExtraAdvance A strategy hwin
          extraAdvance)
    ProfiledRawJointHybridPhysicalCurrentCompatible A strategy
      (carried.stateAt node).1 (carried.stateAt node).2.1 := by
  let raw := profiledRawJointHybridSemanticTree A initial
  exact raw.carryFiniteAnnotation_invariant
    (profiledRawJointHybridPhysicalCompatibleExtraInitial A initialExtra)
    (profiledRawJointHybridPhysicalCompatibleExtraAdvance A strategy hwin
      extraAdvance)
    (fun source annotation ↦
      ProfiledRawJointHybridPhysicalCurrentCompatible A strategy source
        annotation.1)
    (by trivial)
    (fun source current direction _ ↦
      profiledRawJointHybridPhysicalAnnotationAdvance_compatible A strategy
        hwin source current.1 direction)
    node

omit [Fintype Extra] in
/-- The literal product-carried node satisfies the strengthened link without
any extra premise. -/
theorem
    profiledRawJointHybridPhysicalCompatibleExtraParentLinkValid_of_semantic
    (extraAdvance : HybridState A strategy → Extra →
      HybridDirection (In₁ := In₁) (In₂ := In₂) → Extra)
    (source : HybridState A strategy)
    (current : ProfiledRawJointHybridPhysicalCompatibleExtraAnnotation A
      Extra)
    (hcompatible : ProfiledRawJointHybridPhysicalCurrentCompatible A strategy
      source current.1) :
    ProfiledRawJointHybridPhysicalCompatibleExtraParentLinkValid A strategy
      hwin extraAdvance (source.code A) current (source.move A)
        (fun direction ↦
          profiledRawJointHybridPhysicalCompatibleExtraAdvance A strategy hwin
            extraAdvance source current direction) := by
  exact ⟨source, rfl, rfl, hcompatible, fun _ ↦ rfl⟩

/-! ## The one jointly rationalized policy -/

noncomputable abbrev
    ProfiledRawJointHybridPhysicalCompatibleExtraRationalPolicy
    (initial : ProfiledRawJointCommonBaseWorld A strategy)
    (initialExtra : Extra)
    (extraAdvance : HybridState A strategy → Extra →
      HybridDirection (In₁ := In₁) (In₂ := In₂) → Extra) :=
  SourceFreeBeliefCodeParityRationalPolicy
    (sourceFreeBeliefParentLinkedCodeParityDPA
      (Annotation :=
        ProfiledRawJointHybridPhysicalCompatibleExtraAnnotation A Extra)
      (profiledRawJointHybridCodeParityDPA A
        (.common ((profiledRawJointCommonWorldFamily A initial).incidenceCode
          A))))
    ((.common ((profiledRawJointCommonWorldFamily A initial).incidenceCode A)),
      profiledRawJointHybridPhysicalCompatibleExtraInitial A initialExtra)
    (sourceFreeBeliefParentLinkedValid
      (ProfiledRawJointHybridProvenanceValid A strategy)
      (ProfiledRawJointHybridPhysicalCompatibleExtraParentLinkValid A strategy
        hwin extraAdvance))
    (sourceFreeBeliefFiniteCodeNext
      (sourceFreeBeliefParentLinkedNext (profiledRawJointHybridNext A)))

noncomputable abbrev
    ProfiledRawJointHybridPhysicalCompatibleExtraPolicyState
    (initial : ProfiledRawJointCommonBaseWorld A strategy)
    (initialExtra : Extra)
    (extraAdvance : HybridState A strategy → Extra →
      HybridDirection (In₁ := In₁) (In₂ := In₂) → Extra) :=
  (sourceFreeBeliefCodeParityRunAutomaton
    (sourceFreeBeliefParentLinkedCodeParityDPA
      (Annotation :=
        ProfiledRawJointHybridPhysicalCompatibleExtraAnnotation A Extra)
      (profiledRawJointHybridCodeParityDPA A
        (.common ((profiledRawJointCommonWorldFamily A initial).incidenceCode
          A))))
    ((.common ((profiledRawJointCommonWorldFamily A initial).incidenceCode A)),
      profiledRawJointHybridPhysicalCompatibleExtraInitial A initialExtra)
    (sourceFreeBeliefParentLinkedValid
      (ProfiledRawJointHybridProvenanceValid A strategy)
      (ProfiledRawJointHybridPhysicalCompatibleExtraParentLinkValid A strategy
        hwin extraAdvance))
    (sourceFreeBeliefFiniteCodeNext
      (sourceFreeBeliefParentLinkedNext (profiledRawJointHybridNext A)))).State

/-! ## Erasing only the extra payload -/

/-- Forget the extra component of a linked child code while retaining the
bare hybrid code and the physical annotation literally. -/
def profiledRawJointHybridPhysicalCompatibleExtraEraseLinkedCode
    (code : SourceFreeBeliefParentLinkedCode
      (BeliefCode := ProfiledRawJointHybridCode A)
      (Annotation :=
        ProfiledRawJointHybridPhysicalCompatibleExtraAnnotation A Extra)) :
    SourceFreeBeliefParentLinkedCode
      (BeliefCode := ProfiledRawJointHybridCode A)
      (Annotation := PhysicalAnnotation A) :=
  (code.1, code.2.1)

/-- The run-DPA state does not mention annotations (the linked DPA is a
`Prod.fst` comap), so a state of the joint policy has a literal physical-only
projection.  This is a state *carrier* projection; it does not manufacture a
second rational policy. -/
def profiledRawJointHybridPhysicalCompatibleExtraEraseState
    (initial : ProfiledRawJointCommonBaseWorld A strategy)
    (initialExtra : Extra)
    (extraAdvance : HybridState A strategy → Extra →
      HybridDirection (In₁ := In₁) (In₂ := In₂) → Extra)
    (state : ProfiledRawJointHybridPhysicalCompatibleExtraPolicyState A
      strategy hwin initial initialExtra extraAdvance) :
    ProfiledRawJointHybridPhysicalCompatiblePolicyState A strategy hwin
      initial :=
  ((state.1.1, state.1.2.1), state.2)

@[simp] theorem
    profiledRawJointHybridPhysicalCompatibleExtraEraseState_code
    (initial : ProfiledRawJointCommonBaseWorld A strategy)
    (initialExtra : Extra)
    (extraAdvance : HybridState A strategy → Extra →
      HybridDirection (In₁ := In₁) (In₂ := In₂) → Extra)
    (state : ProfiledRawJointHybridPhysicalCompatibleExtraPolicyState A
      strategy hwin initial initialExtra extraAdvance) :
    (profiledRawJointHybridPhysicalCompatibleExtraEraseState A strategy hwin
      initial initialExtra extraAdvance state).1.1 = state.1.1 :=
  rfl

@[simp] theorem
    profiledRawJointHybridPhysicalCompatibleExtraEraseState_annotation
    (initial : ProfiledRawJointCommonBaseWorld A strategy)
    (initialExtra : Extra)
    (extraAdvance : HybridState A strategy → Extra →
      HybridDirection (In₁ := In₁) (In₂ := In₂) → Extra)
    (state : ProfiledRawJointHybridPhysicalCompatibleExtraPolicyState A
      strategy hwin initial initialExtra extraAdvance) :
    (profiledRawJointHybridPhysicalCompatibleExtraEraseState A strategy hwin
      initial initialExtra extraAdvance state).1.2 = state.1.2.1 :=
  rfl

@[simp] theorem
    profiledRawJointHybridPhysicalCompatibleExtraEraseState_dpa
    (initial : ProfiledRawJointCommonBaseWorld A strategy)
    (initialExtra : Extra)
    (extraAdvance : HybridState A strategy → Extra →
      HybridDirection (In₁ := In₁) (In₂ := In₂) → Extra)
    (state : ProfiledRawJointHybridPhysicalCompatibleExtraPolicyState A
      strategy hwin initial initialExtra extraAdvance) :
    (profiledRawJointHybridPhysicalCompatibleExtraEraseState A strategy hwin
      initial initialExtra extraAdvance state).2 = state.2 :=
  rfl

abbrev ProfiledRawJointHybridPhysicalCompatibleExtraReachable
    (initial : ProfiledRawJointCommonBaseWorld A strategy)
    (initialExtra : Extra)
    (extraAdvance : HybridState A strategy → Extra →
      HybridDirection (In₁ := In₁) (In₂ := In₂) → Extra)
    (policy : ProfiledRawJointHybridPhysicalCompatibleExtraRationalPolicy A
      strategy hwin initial initialExtra extraAdvance)
    (state : ProfiledRawJointHybridPhysicalCompatibleExtraPolicyState A
      strategy hwin initial initialExtra extraAdvance) : Prop :=
  SourceFreeBeliefCodeParityRationalPolicy.Reachable
    (sourceFreeBeliefParentLinkedCodeParityDPA
      (Annotation :=
        ProfiledRawJointHybridPhysicalCompatibleExtraAnnotation A Extra)
      (profiledRawJointHybridCodeParityDPA A
        (.common ((profiledRawJointCommonWorldFamily A initial).incidenceCode
          A))))
    ((.common ((profiledRawJointCommonWorldFamily A initial).incidenceCode A)),
      profiledRawJointHybridPhysicalCompatibleExtraInitial A initialExtra)
    (sourceFreeBeliefParentLinkedValid
      (ProfiledRawJointHybridProvenanceValid A strategy)
      (ProfiledRawJointHybridPhysicalCompatibleExtraParentLinkValid A strategy
        hwin extraAdvance))
    (sourceFreeBeliefFiniteCodeNext
      (sourceFreeBeliefParentLinkedNext (profiledRawJointHybridNext A)))
    policy state

/-- Any finite edge payload can be included without adding an existence
premise.  In particular, once the uniform staged-seam ID and its semantic
edge constructor are defined, there is no second rationalization step. -/
theorem
    nonempty_profiledRawJointHybridPhysicalCompatibleExtraRationalPolicy
    (initial : ProfiledRawJointCommonBaseWorld A strategy)
    (initialExtra : Extra)
    (extraAdvance : HybridState A strategy → Extra →
      HybridDirection (In₁ := In₁) (In₂ := In₂) → Extra) :
    Nonempty
      (ProfiledRawJointHybridPhysicalCompatibleExtraRationalPolicy A strategy
        hwin initial initialExtra extraAdvance) := by
  let raw := profiledRawJointHybridSemanticTree A initial
  let initialAnnotation :=
    profiledRawJointHybridPhysicalCompatibleExtraInitial A initialExtra
  let advance :=
    profiledRawJointHybridPhysicalCompatibleExtraAdvance A strategy hwin
      extraAdvance
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
  exact carriedCertificate.nonempty_parentLinkedFiniteCodeDirectionRationalPolicy
    (profiledRawJointHybridCodeParityDPA A initialCode)
    initialCode
    (ProfiledRawJointHybridProvenanceValid A strategy)
    (profiledRawJointHybridNext A)
    carried Prod.snd
    (ProfiledRawJointHybridPhysicalCompatibleExtraParentLinkValid A strategy
      hwin extraAdvance)
    (fun node ↦ by
      let state := carried.stateAt node
      exact
        profiledRawJointHybridPhysicalCompatibleExtraParentLinkValid_of_semantic
          A strategy hwin extraAdvance state.1 state.2
            (profiledRawJointHybridPhysicalCompatibleExtraCarriedTree_current
              A strategy hwin initial initialExtra extraAdvance node))

/-! ## Reachable inversion: the shared-origin guarantee -/

/-- At a reachable state, one source explains the current physical payload,
the extra payload, and their entire joint successor table.  This is the exact
fact unavailable when the old literal package and the hybrid policy are
rationalized independently. -/
theorem
    exists_profiledRawJointHybridPhysicalCompatibleExtraSemanticSource
    (initial : ProfiledRawJointCommonBaseWorld A strategy)
    (initialExtra : Extra)
    (extraAdvance : HybridState A strategy → Extra →
      HybridDirection (In₁ := In₁) (In₂ := In₂) → Extra)
    (policy : ProfiledRawJointHybridPhysicalCompatibleExtraRationalPolicy A
      strategy hwin initial initialExtra extraAdvance)
    (state : ProfiledRawJointHybridPhysicalCompatibleExtraPolicyState A
      strategy hwin initial initialExtra extraAdvance)
    (hreachable :
      ProfiledRawJointHybridPhysicalCompatibleExtraReachable A strategy hwin
        initial initialExtra extraAdvance policy state) :
    ∃ move : SourceFreeBeliefParentLinkedMove
        (Direction := HybridDirection (In₁ := In₁) (In₂ := In₂))
        (Move := ProfiledRawJointHybridMove A)
        (Annotation :=
          ProfiledRawJointHybridPhysicalCompatibleExtraAnnotation A Extra),
      ∃ source : HybridState A strategy,
        source.code A = state.1.1 ∧
          source.move A = move.1 ∧
          ProfiledRawJointHybridPhysicalCurrentCompatible A strategy source
            state.1.2.1 ∧
          (∀ direction,
            profiledRawJointHybridPhysicalCompatibleExtraAdvance A strategy
                hwin extraAdvance source state.1.2 direction =
              move.2 direction) ∧
          ∀ direction : HybridDirection (In₁ := In₁) (In₂ := In₂),
            policy.successor state
                (sourceFreeBeliefParentLinkedNext
                  (profiledRawJointHybridNext A) state.1 move direction) =
              let childCode := sourceFreeBeliefParentLinkedNext
                (profiledRawJointHybridNext A) state.1 move direction
              (childCode,
                (sourceFreeBeliefParentLinkedCodeParityDPA
                  (Annotation :=
                    ProfiledRawJointHybridPhysicalCompatibleExtraAnnotation A
                      Extra)
                  (profiledRawJointHybridCodeParityDPA A
                    (.common ((profiledRawJointCommonWorldFamily A initial
                      ).incidenceCode A)))).step state.2 childCode) := by
  rcases
      SourceFreeBeliefCodeParityRationalPolicy.exists_parentLinkedMove_finiteCodeDirection
        (profiledRawJointHybridCodeParityDPA A
          (.common ((profiledRawJointCommonWorldFamily A initial).incidenceCode
            A)))
        (.common ((profiledRawJointCommonWorldFamily A initial).incidenceCode
          A))
        (profiledRawJointHybridPhysicalCompatibleExtraInitial A initialExtra)
        (ProfiledRawJointHybridProvenanceValid A strategy)
        (ProfiledRawJointHybridPhysicalCompatibleExtraParentLinkValid A
          strategy hwin extraAdvance)
        (profiledRawJointHybridNext A)
        policy state hreachable with
    ⟨move, _hvalid, hlink, hsuccessor⟩
  rcases hlink with
    ⟨source, hcode, hmove, hcompatible, hchildren⟩
  exact ⟨move, source, hcode, hmove, hcompatible, hchildren, hsuccessor⟩

/-- Complete one-step form used by the eventual staged-tail controller.  The
successor's bare code, physical annotation, and extra payload are all the
literal children of one source occurrence.  In particular the last two
equalities cannot be witnessed by independently chosen representatives. -/
theorem
    exists_profiledRawJointHybridPhysicalCompatibleExtraSuccessorSemantics
    (initial : ProfiledRawJointCommonBaseWorld A strategy)
    (initialExtra : Extra)
    (extraAdvance : HybridState A strategy → Extra →
      HybridDirection (In₁ := In₁) (In₂ := In₂) → Extra)
    (policy : ProfiledRawJointHybridPhysicalCompatibleExtraRationalPolicy A
      strategy hwin initial initialExtra extraAdvance)
    (state : ProfiledRawJointHybridPhysicalCompatibleExtraPolicyState A
      strategy hwin initial initialExtra extraAdvance)
    (hreachable :
      ProfiledRawJointHybridPhysicalCompatibleExtraReachable A strategy hwin
        initial initialExtra extraAdvance policy state) :
    ∃ move : SourceFreeBeliefParentLinkedMove
        (Direction := HybridDirection (In₁ := In₁) (In₂ := In₂))
        (Move := ProfiledRawJointHybridMove A)
        (Annotation :=
          ProfiledRawJointHybridPhysicalCompatibleExtraAnnotation A Extra),
      ∃ source : HybridState A strategy,
        source.code A = state.1.1 ∧
          source.move A = move.1 ∧
          ProfiledRawJointHybridPhysicalCurrentCompatible A strategy source
            state.1.2.1 ∧
          ∀ direction : HybridDirection (In₁ := In₁) (In₂ := In₂),
            let childCode := sourceFreeBeliefParentLinkedNext
              (profiledRawJointHybridNext A) state.1 move direction
            let target := policy.successor state childCode
            target.1.1 = (source.step A direction).code A ∧
              target.1.2.1 =
                profiledRawJointHybridPhysicalAnnotationAdvance A strategy
                  hwin source state.1.2.1 direction ∧
              target.1.2.2 =
                extraAdvance source state.1.2.2 direction := by
  rcases
      exists_profiledRawJointHybridPhysicalCompatibleExtraSemanticSource A
        strategy hwin initial initialExtra extraAdvance policy state hreachable
      with
    ⟨move, source, hcode, hmove, hcompatible, hchildren, hsuccessor⟩
  refine ⟨move, source, hcode, hmove, hcompatible, ?_⟩
  intro direction
  simp only
  rw [hsuccessor direction]
  have hchild := (hchildren direction).symm
  constructor
  · change profiledRawJointHybridNext A state.1.1 move.1 direction =
      (source.step A direction).code A
    rw [← hcode, ← hmove]
    exact (source.step_code A direction).symm
  · constructor
    · exact congrArg Prod.fst hchild
    · exact congrArg Prod.snd hchild

/-! ## Generic installation and persistence adapters -/

/-- If the extra update has a prescribed value on one fixed outgoing
direction of a common source, then a reachable rational-policy successor
installs that value together with the literal physical child and the exact
linked-DPA step.  This is the reusable adapter for any uniform staged-table
payload; the table constructor itself remains outside the executable
endpoint. -/
theorem
    exists_profiledRawJointHybridPhysicalCompatibleExtraCommonSuccessor_of_advance
    (initial : ProfiledRawJointCommonBaseWorld A strategy)
    (initialExtra : Extra)
    (extraAdvance : HybridState A strategy → Extra →
      HybridDirection (In₁ := In₁) (In₂ := In₂) → Extra)
    (policy : ProfiledRawJointHybridPhysicalCompatibleExtraRationalPolicy A
      strategy hwin initial initialExtra extraAdvance)
    (state : ProfiledRawJointHybridPhysicalCompatibleExtraPolicyState A
      strategy hwin initial initialExtra extraAdvance)
    (hreachable :
      ProfiledRawJointHybridPhysicalCompatibleExtraReachable A strategy hwin
        initial initialExtra extraAdvance policy state)
    (code : ProfiledRawJointIncidenceCode A (I := Unit))
    (hcode : state.1.1 = .common code)
    (direction : HybridDirection (In₁ := In₁) (In₂ := In₂))
    (expected : ProfiledRawJointCommonBaseWorld A strategy → Extra)
    (hadvance : ∀ world current,
      extraAdvance (.common world) current direction = expected world) :
    ∃ move : SourceFreeBeliefParentLinkedMove
        (Direction := HybridDirection (In₁ := In₁) (In₂ := In₂))
        (Move := ProfiledRawJointHybridMove A)
        (Annotation :=
          ProfiledRawJointHybridPhysicalCompatibleExtraAnnotation A Extra),
      ∃ world : ProfiledRawJointCommonBaseWorld A strategy,
        (ProfiledRawJointHybridSemanticState.common world).code A =
            state.1.1 ∧
          (ProfiledRawJointHybridSemanticState.common world).move A = move.1 ∧
          ProfiledRawJointHybridPhysicalCurrentCompatible A strategy
            (.common world) state.1.2.1 ∧
          let childCode := sourceFreeBeliefParentLinkedNext
            (profiledRawJointHybridNext A) state.1 move direction
          let target := policy.successor state childCode
          target.1.1 = ((ProfiledRawJointHybridSemanticState.common world).step
              A direction).code A ∧
            target.1.2.1 =
              profiledRawJointHybridPhysicalAnnotationAdvance A strategy hwin
                (.common world) state.1.2.1 direction ∧
            target.1.2.2 = expected world ∧
            target.2 =
              (sourceFreeBeliefParentLinkedCodeParityDPA
                (Annotation :=
                  ProfiledRawJointHybridPhysicalCompatibleExtraAnnotation A
                    Extra)
                (profiledRawJointHybridCodeParityDPA A
                  (.common ((profiledRawJointCommonWorldFamily A initial
                    ).incidenceCode A)))).step state.2 childCode := by
  rcases
      exists_profiledRawJointHybridPhysicalCompatibleExtraSemanticSource A
        strategy hwin initial initialExtra extraAdvance policy state hreachable
      with
    ⟨move, source, hsourceCode, hsourceMove, hcompatible, hchildren,
      hsuccessor⟩
  have hsourceCommon : source.code A = .common code :=
    hsourceCode.trans hcode
  cases source with
  | dead =>
      simp [ProfiledRawJointHybridSemanticState.code] at hsourceCommon
  | oneSided source =>
      simp [ProfiledRawJointHybridSemanticState.code] at hsourceCommon
  | common world =>
      refine ⟨move, world, hsourceCode, hsourceMove, hcompatible, ?_⟩
      dsimp only
      rw [hsuccessor direction]
      have hchild := (hchildren direction).symm
      constructor
      · change profiledRawJointHybridNext A state.1.1 move.1 direction =
            ((ProfiledRawJointHybridSemanticState.common world).step A
              direction).code A
        rw [← hsourceCode, ← hsourceMove]
        exact
          ((ProfiledRawJointHybridSemanticState.common world).step_code A
            direction).symm
      · constructor
        · exact congrArg (fun annotation ↦ annotation.1) hchild
        · constructor
          · have hextra := congrArg (fun annotation ↦ annotation.2) hchild
            change (move.2 direction).2 = expected world
            calc
              (move.2 direction).2 =
                  extraAdvance (.common world) state.1.2.2 direction := by
                exact hextra
              _ = expected world := hadvance world state.1.2.2
          · rfl

/-- The one-sided analogue of the common installation adapter.  It identifies
the payload installed by an arbitrary strict edge while retaining the
physical successor and linked-DPA equations. -/
theorem
    exists_profiledRawJointHybridPhysicalCompatibleExtraOneSidedSuccessor_of_advance
    (initial : ProfiledRawJointCommonBaseWorld A strategy)
    (initialExtra : Extra)
    (extraAdvance : HybridState A strategy → Extra →
      HybridDirection (In₁ := In₁) (In₂ := In₂) → Extra)
    (policy : ProfiledRawJointHybridPhysicalCompatibleExtraRationalPolicy A
      strategy hwin initial initialExtra extraAdvance)
    (state : ProfiledRawJointHybridPhysicalCompatibleExtraPolicyState A
      strategy hwin initial initialExtra extraAdvance)
    (hreachable :
      ProfiledRawJointHybridPhysicalCompatibleExtraReachable A strategy hwin
        initial initialExtra extraAdvance policy state)
    (code : ProfiledRawJointIncidenceCode A (I := Unit))
    (hcode : state.1.1 = .oneSided code)
    (actual : ProfiledRawJointActualDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (expected :
      ProfiledRawJointOneSidedSemanticState A strategy (I := Unit) → Extra)
    (hadvance : ∀ source current,
      extraAdvance (.oneSided source) current (.strict actual) =
        expected source) :
    ∃ move : SourceFreeBeliefParentLinkedMove
        (Direction := HybridDirection (In₁ := In₁) (In₂ := In₂))
        (Move := ProfiledRawJointHybridMove A)
        (Annotation :=
          ProfiledRawJointHybridPhysicalCompatibleExtraAnnotation A Extra),
      ∃ source : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit),
        (ProfiledRawJointHybridSemanticState.oneSided source).code A =
            state.1.1 ∧
          (ProfiledRawJointHybridSemanticState.oneSided source).move A = move.1 ∧
          ProfiledRawJointHybridPhysicalCurrentCompatible A strategy
            (.oneSided source) state.1.2.1 ∧
          let direction : HybridDirection (In₁ := In₁) (In₂ := In₂) :=
            .strict actual
          let childCode := sourceFreeBeliefParentLinkedNext
            (profiledRawJointHybridNext A) state.1 move direction
          let target := policy.successor state childCode
          target.1.1 = ((ProfiledRawJointHybridSemanticState.oneSided source).step
              A direction).code A ∧
            target.1.2.1 =
              profiledRawJointHybridPhysicalAnnotationAdvance A strategy hwin
                (.oneSided source) state.1.2.1 direction ∧
            target.1.2.2 = expected source ∧
            target.2 =
              (sourceFreeBeliefParentLinkedCodeParityDPA
                (Annotation :=
                  ProfiledRawJointHybridPhysicalCompatibleExtraAnnotation A
                    Extra)
                (profiledRawJointHybridCodeParityDPA A
                  (.common ((profiledRawJointCommonWorldFamily A initial
                    ).incidenceCode A)))).step state.2 childCode := by
  rcases
      exists_profiledRawJointHybridPhysicalCompatibleExtraSemanticSource A
        strategy hwin initial initialExtra extraAdvance policy state hreachable
      with
    ⟨move, semantic, hsourceCode, hsourceMove, hcompatible, hchildren,
      hsuccessor⟩
  have hsourceOneSided : semantic.code A = .oneSided code :=
    hsourceCode.trans hcode
  cases semantic with
  | dead =>
      simp [ProfiledRawJointHybridSemanticState.code] at hsourceOneSided
  | common world =>
      simp [ProfiledRawJointHybridSemanticState.code] at hsourceOneSided
  | oneSided source =>
      refine ⟨move, source, hsourceCode, hsourceMove, hcompatible, ?_⟩
      dsimp only
      rw [hsuccessor (.strict actual)]
      have hchild := (hchildren (.strict actual)).symm
      constructor
      · change profiledRawJointHybridNext A state.1.1 move.1
            (.strict actual) =
          ((ProfiledRawJointHybridSemanticState.oneSided source).step A
            (.strict actual)).code A
        rw [← hsourceCode, ← hsourceMove]
        exact
          ((ProfiledRawJointHybridSemanticState.oneSided source).step_code A
            (.strict actual)).symm
      · constructor
        · exact congrArg (fun annotation ↦ annotation.1) hchild
        · constructor
          · have hextra := congrArg (fun annotation ↦ annotation.2) hchild
            change (move.2 (.strict actual)).2 = expected source
            calc
              (move.2 (.strict actual)).2 =
                  extraAdvance (.oneSided source) state.1.2.2
                    (.strict actual) := by
                exact hextra
              _ = expected source := hadvance source state.1.2.2
          · rfl

/-! ## Concrete smallest existing extra: guarded occurrence roots -/

/-- The smallest already available uniform payload which is genuinely
occurrence-sensitive.  It carries the two optional guarded physical moves
selected at one hybrid edge, but no arbitrary-depth table controls. -/
abbrev ProfiledRawJointHybridPhysicalCompatibleGuardedOccurrenceAnnotation :=
  ProfiledRawJointHybridPhysicalCompatibleExtraAnnotation A
    (ProfiledRawJointHybridGuardedOccurrenceAnnotation A)

noncomputable abbrev
    ProfiledRawJointHybridPhysicalCompatibleGuardedOccurrenceRationalPolicy
    (initial : ProfiledRawJointCommonBaseWorld A strategy) :=
  ProfiledRawJointHybridPhysicalCompatibleExtraRationalPolicy A strategy hwin
    initial (profiledRawJointHybridInitialGuardedOccurrenceAnnotation A)
      (profiledRawJointHybridGuardedOccurrenceAnnotationAdvance A strategy
        hwin)

noncomputable abbrev
    ProfiledRawJointHybridPhysicalCompatibleGuardedOccurrencePolicyState
    (initial : ProfiledRawJointCommonBaseWorld A strategy) :=
  ProfiledRawJointHybridPhysicalCompatibleExtraPolicyState A strategy hwin
    initial (profiledRawJointHybridInitialGuardedOccurrenceAnnotation A)
      (profiledRawJointHybridGuardedOccurrenceAnnotationAdvance A strategy
        hwin)

abbrev ProfiledRawJointHybridPhysicalCompatibleGuardedOccurrenceReachable
    (initial : ProfiledRawJointCommonBaseWorld A strategy)
    (policy :
      ProfiledRawJointHybridPhysicalCompatibleGuardedOccurrenceRationalPolicy
        A strategy hwin initial)
    (state :
      ProfiledRawJointHybridPhysicalCompatibleGuardedOccurrencePolicyState A
        strategy hwin initial) : Prop :=
  ProfiledRawJointHybridPhysicalCompatibleExtraReachable A strategy hwin
    initial (profiledRawJointHybridInitialGuardedOccurrenceAnnotation A)
      (profiledRawJointHybridGuardedOccurrenceAnnotationAdvance A strategy
        hwin) policy state

theorem
    nonempty_profiledRawJointHybridPhysicalCompatibleGuardedOccurrenceRationalPolicy
    (initial : ProfiledRawJointCommonBaseWorld A strategy) :
    Nonempty
      (ProfiledRawJointHybridPhysicalCompatibleGuardedOccurrenceRationalPolicy
        A strategy hwin initial) :=
  nonempty_profiledRawJointHybridPhysicalCompatibleExtraRationalPolicy A
    strategy hwin initial
      (profiledRawJointHybridInitialGuardedOccurrenceAnnotation A)
      (profiledRawJointHybridGuardedOccurrenceAnnotationAdvance A strategy
        hwin)

/-- At a literal common-to-common edge, the concrete extra is exactly the two
guarded moves of one represented common pair.  Thus the extra already gives
the two coherent physical roots at depth zero. -/
theorem profiledRawJointHybridGuardedOccurrenceAnnotationOf_common_eq_pair
    (world : ProfiledRawJointCommonBaseWorld A strategy)
    (input : In₁ × In₂) :
    let pair :=
      profiledRawJointGuardedCommonPairOfWorld A strategy hwin world input
    profiledRawJointHybridGuardedOccurrenceAnnotationOf A strategy hwin
        (profiledRawJointCommonWorldFamily A world)
        (profiledRawJointBothRestartDirection input) =
      (some pair.1.1, some pair.1.2) := by
  dsimp only
  apply Prod.ext
  · unfold profiledRawJointGuardedCommonPairOfWorld
      profiledRawJointGuardedCommonRightMoveOfWorld
      profiledRawJointHybridGuardedOccurrenceAnnotationOf
    apply profiledRawJointGuardedRightPhysicalSiblingMoveOption_eq_some
  · unfold profiledRawJointGuardedCommonPairOfWorld
      profiledRawJointGuardedCommonLeftMoveOfWorld
      profiledRawJointHybridGuardedOccurrenceAnnotationOf
    apply profiledRawJointGuardedLeftPhysicalSiblingMoveOption_eq_some

/-- Concrete same-source successor theorem at a reachable common state.  The
full target is the successor of the *joint* policy; its physical annotation
and both guarded roots are selected by the same `world,input` occurrence, and
its run-DPA component is the literal linked-DPA step at that target key.

This is the strongest root theorem supplied by the existing uniform
`GuardedOccurrenceAnnotation`.  It is intentionally a depth-zero theorem:
the payload contains move IDs but no sender/receiver table controls, so it
cannot by itself state `TailNextMatchesLiteralCrossRoots` after a nonempty
homogeneous block. -/
theorem
    exists_profiledRawJointHybridPhysicalCompatibleGuardedOccurrenceCommonSuccessor
    (initial : ProfiledRawJointCommonBaseWorld A strategy)
    (policy :
      ProfiledRawJointHybridPhysicalCompatibleGuardedOccurrenceRationalPolicy
        A strategy hwin initial)
    (state :
      ProfiledRawJointHybridPhysicalCompatibleGuardedOccurrencePolicyState A
        strategy hwin initial)
    (hreachable :
      ProfiledRawJointHybridPhysicalCompatibleGuardedOccurrenceReachable A
        strategy hwin initial policy state)
    (code : ProfiledRawJointIncidenceCode A (I := Unit))
    (hcode : state.1.1 = .common code)
    (input : In₁ × In₂) :
    ∃ move : SourceFreeBeliefParentLinkedMove
        (Direction := HybridDirection (In₁ := In₁) (In₂ := In₂))
        (Move := ProfiledRawJointHybridMove A)
        (Annotation :=
          ProfiledRawJointHybridPhysicalCompatibleGuardedOccurrenceAnnotation
            A),
      ∃ world : ProfiledRawJointCommonBaseWorld A strategy,
        (ProfiledRawJointHybridSemanticState.common world).code A =
            state.1.1 ∧
          (ProfiledRawJointHybridSemanticState.common world).move A = move.1 ∧
          ProfiledRawJointHybridPhysicalCurrentCompatible A strategy
            (.common world) state.1.2.1 ∧
          let direction : HybridDirection (In₁ := In₁) (In₂ := In₂) :=
            .simultaneous input
          let childCode := sourceFreeBeliefParentLinkedNext
            (profiledRawJointHybridNext A) state.1 move direction
          let target := policy.successor state childCode
          let pair :=
            profiledRawJointGuardedCommonPairOfWorld A strategy hwin world input
          target.1.1 = ((ProfiledRawJointHybridSemanticState.common world).step
              A direction).code A ∧
            target.1.2.1 =
              profiledRawJointHybridPhysicalAnnotationOf A strategy hwin
                (profiledRawJointCommonWorldFamily A world)
                (profiledRawJointBothRestartDirection input) ∧
            target.1.2.2 = (some pair.1.1, some pair.1.2) ∧
            target.2 =
              (sourceFreeBeliefParentLinkedCodeParityDPA
                (Annotation :=
                  ProfiledRawJointHybridPhysicalCompatibleGuardedOccurrenceAnnotation
                    A)
                (profiledRawJointHybridCodeParityDPA A
                  (.common ((profiledRawJointCommonWorldFamily A initial
                    ).incidenceCode A)))).step state.2 childCode := by
  rcases
      exists_profiledRawJointHybridPhysicalCompatibleExtraSemanticSource A
        strategy hwin initial
        (profiledRawJointHybridInitialGuardedOccurrenceAnnotation A)
        (profiledRawJointHybridGuardedOccurrenceAnnotationAdvance A strategy
          hwin) policy state hreachable with
    ⟨move, source, hsourceCode, hsourceMove, hcompatible, hchildren,
      hsuccessor⟩
  have hsourceCommon : source.code A = .common code :=
    hsourceCode.trans hcode
  cases source with
  | dead =>
      simp [ProfiledRawJointHybridSemanticState.code] at hsourceCommon
  | oneSided source =>
      simp [ProfiledRawJointHybridSemanticState.code] at hsourceCommon
  | common world =>
      refine ⟨move, world, hsourceCode, hsourceMove, hcompatible, ?_⟩
      dsimp only
      rw [hsuccessor (.simultaneous input)]
      have hchild := (hchildren (.simultaneous input)).symm
      constructor
      · change profiledRawJointHybridNext A state.1.1 move.1
            (.simultaneous input) =
          ((ProfiledRawJointHybridSemanticState.common world).step A
            (.simultaneous input)).code A
        rw [← hsourceCode, ← hsourceMove]
        exact
          ((ProfiledRawJointHybridSemanticState.common world).step_code A
            (.simultaneous input)).symm
      · constructor
        · have hphysical := congrArg (fun annotation ↦ annotation.1) hchild
          exact hphysical
        · constructor
          · have hextra := congrArg (fun annotation ↦ annotation.2) hchild
            change (move.2 (.simultaneous input)).2 = _
            calc
              (move.2 (.simultaneous input)).2 =
                  profiledRawJointHybridGuardedOccurrenceAnnotationAdvance A
                    strategy hwin (.common world) state.1.2.2
                      (.simultaneous input) := by
                exact hextra
              _ = profiledRawJointHybridGuardedOccurrenceAnnotationOf A
                    strategy hwin (profiledRawJointCommonWorldFamily A world)
                      (profiledRawJointBothRestartDirection input) := rfl
              _ = _ :=
                profiledRawJointHybridGuardedOccurrenceAnnotationOf_common_eq_pair
                  A strategy hwin world input
          · rfl

end

end DetParityAutomaton

end DistributedSynthesis
