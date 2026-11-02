/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleExtraAnnotation

/-!
# Current-valid extras in one physical-compatible hybrid policy

The generic jointly annotated policy records how a semantic source computes
all *child* extras.  That is not enough when an executable controller consumes
the extra already stored at the current state: after finite-code
rationalization, a representative explaining the current move need not be the
representative which installed that extra.

This file strengthens the parent link by an arbitrary semantic invariant
`ExtraValid source extra`.  The invariant is established on the literal
carried tree before rationalization and is then returned by every reachable
inversion.  Thus one semantic source simultaneously explains the current
physical annotation, the current extra, all children, and the retained DPA
control.

No endpoint receives a semantic source, graph, hierarchy side, leader bit, or
strict-leader bit.  `ExtraValid` is a proof-only extraction relation.
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

private abbrev JointAnnotation :=
  ProfiledRawJointHybridPhysicalCompatibleExtraAnnotation A Extra

/-! ## Strengthened parent link -/

/-- A single semantic representative explains both current annotations and
the complete child assignment. -/
def ProfiledRawJointHybridPhysicalCompatibleValidatedExtraParentLinkValid
    (ExtraValid : HybridState A strategy → Extra → Prop)
    (extraAdvance : HybridState A strategy → Extra →
      HybridDirection (In₁ := In₁) (In₂ := In₂) → Extra)
    (code : ProfiledRawJointHybridCode A)
    (current : JointAnnotation A (Extra := Extra))
    (move : ProfiledRawJointHybridMove A)
    (children : HybridDirection (In₁ := In₁) (In₂ := In₂) →
      JointAnnotation A (Extra := Extra)) : Prop :=
  ∃ source : HybridState A strategy,
    source.code A = code ∧
      source.move A = move ∧
      ProfiledRawJointHybridPhysicalCurrentCompatible A strategy source
        current.1 ∧
      ExtraValid source current.2 ∧
      ∀ direction,
        profiledRawJointHybridPhysicalCompatibleExtraAdvance A strategy hwin
            extraAdvance source current direction =
          children direction

omit [Fintype Extra] in
/-- A literal carried node satisfies the strengthened link whenever its
current joint annotation satisfies both component invariants. -/
theorem
    profiledRawJointHybridPhysicalCompatibleValidatedExtraParentLinkValid_of_semantic
    (ExtraValid : HybridState A strategy → Extra → Prop)
    (extraAdvance : HybridState A strategy → Extra →
      HybridDirection (In₁ := In₁) (In₂ := In₂) → Extra)
    (source : HybridState A strategy)
    (current : JointAnnotation A (Extra := Extra))
    (hphysical : ProfiledRawJointHybridPhysicalCurrentCompatible A strategy
      source current.1)
    (hextra : ExtraValid source current.2) :
    ProfiledRawJointHybridPhysicalCompatibleValidatedExtraParentLinkValid A
      strategy hwin ExtraValid extraAdvance (source.code A) current
        (source.move A)
        (fun direction ↦
          profiledRawJointHybridPhysicalCompatibleExtraAdvance A strategy hwin
            extraAdvance source current direction) := by
  exact ⟨source, rfl, rfl, hphysical, hextra, fun _ ↦ rfl⟩

/-! ## Literal carried invariant -/

omit [Fintype Extra] in
/-- Both current-component invariants hold throughout the literal annotated
semantic tree. -/
theorem
    profiledRawJointHybridPhysicalCompatibleValidatedExtraCarriedTree_current
    (initial : ProfiledRawJointCommonBaseWorld A strategy)
    (initialExtra : Extra)
    (extraAdvance : HybridState A strategy → Extra →
      HybridDirection (In₁ := In₁) (In₂ := In₂) → Extra)
    (ExtraValid : HybridState A strategy → Extra → Prop)
    (hinitial : ExtraValid (.common initial) initialExtra)
    (hstep : ∀ source current direction,
      ExtraValid source current →
        ExtraValid (source.step A direction)
          (extraAdvance source current direction))
    (node : TreeNode (HybridDirection (In₁ := In₁) (In₂ := In₂))) :
    let carried :=
      (profiledRawJointHybridSemanticTree A initial).carryFiniteAnnotation
        (profiledRawJointHybridPhysicalCompatibleExtraInitial A initialExtra)
        (profiledRawJointHybridPhysicalCompatibleExtraAdvance A strategy hwin
          extraAdvance)
    ProfiledRawJointHybridPhysicalCurrentCompatible A strategy
        (carried.stateAt node).1 (carried.stateAt node).2.1 ∧
      ExtraValid (carried.stateAt node).1 (carried.stateAt node).2.2 := by
  let raw := profiledRawJointHybridSemanticTree A initial
  exact raw.carryFiniteAnnotation_invariant
    (profiledRawJointHybridPhysicalCompatibleExtraInitial A initialExtra)
    (profiledRawJointHybridPhysicalCompatibleExtraAdvance A strategy hwin
      extraAdvance)
    (fun source annotation ↦
      ProfiledRawJointHybridPhysicalCurrentCompatible A strategy source
          annotation.1 ∧
        ExtraValid source annotation.2)
    ⟨by trivial, hinitial⟩
    (fun source current direction hcurrent ↦
      ⟨profiledRawJointHybridPhysicalAnnotationAdvance_compatible A strategy
          hwin source current.1 direction,
        hstep source current.2 direction hcurrent.2⟩)
    node

/-! ## One finite rational policy retaining the invariant -/

noncomputable abbrev
    ProfiledRawJointHybridPhysicalCompatibleValidatedExtraRationalPolicy
    (initial : ProfiledRawJointCommonBaseWorld A strategy)
    (initialExtra : Extra)
    (ExtraValid : HybridState A strategy → Extra → Prop)
    (extraAdvance : HybridState A strategy → Extra →
      HybridDirection (In₁ := In₁) (In₂ := In₂) → Extra) :=
  SourceFreeBeliefCodeParityRationalPolicy
    (sourceFreeBeliefParentLinkedCodeParityDPA
      (Annotation := JointAnnotation A (Extra := Extra))
      (profiledRawJointHybridCodeParityDPA A
        (.common ((profiledRawJointCommonWorldFamily A initial).incidenceCode
          A))))
    ((.common ((profiledRawJointCommonWorldFamily A initial).incidenceCode A)),
      profiledRawJointHybridPhysicalCompatibleExtraInitial A initialExtra)
    (sourceFreeBeliefParentLinkedValid
      (ProfiledRawJointHybridProvenanceValid A strategy)
      (ProfiledRawJointHybridPhysicalCompatibleValidatedExtraParentLinkValid A
        strategy hwin ExtraValid extraAdvance))
    (sourceFreeBeliefFiniteCodeNext
      (sourceFreeBeliefParentLinkedNext (profiledRawJointHybridNext A)))

noncomputable abbrev
    ProfiledRawJointHybridPhysicalCompatibleValidatedExtraPolicyState
    (initial : ProfiledRawJointCommonBaseWorld A strategy)
    (initialExtra : Extra)
    (ExtraValid : HybridState A strategy → Extra → Prop)
    (extraAdvance : HybridState A strategy → Extra →
      HybridDirection (In₁ := In₁) (In₂ := In₂) → Extra) :=
  (sourceFreeBeliefCodeParityRunAutomaton
    (sourceFreeBeliefParentLinkedCodeParityDPA
      (Annotation := JointAnnotation A (Extra := Extra))
      (profiledRawJointHybridCodeParityDPA A
        (.common ((profiledRawJointCommonWorldFamily A initial).incidenceCode
          A))))
    ((.common ((profiledRawJointCommonWorldFamily A initial).incidenceCode A)),
      profiledRawJointHybridPhysicalCompatibleExtraInitial A initialExtra)
    (sourceFreeBeliefParentLinkedValid
      (ProfiledRawJointHybridProvenanceValid A strategy)
      (ProfiledRawJointHybridPhysicalCompatibleValidatedExtraParentLinkValid A
        strategy hwin ExtraValid extraAdvance))
    (sourceFreeBeliefFiniteCodeNext
      (sourceFreeBeliefParentLinkedNext (profiledRawJointHybridNext A)))).State

abbrev ProfiledRawJointHybridPhysicalCompatibleValidatedExtraReachable
    (initial : ProfiledRawJointCommonBaseWorld A strategy)
    (initialExtra : Extra)
    (ExtraValid : HybridState A strategy → Extra → Prop)
    (extraAdvance : HybridState A strategy → Extra →
      HybridDirection (In₁ := In₁) (In₂ := In₂) → Extra)
    (policy :
      ProfiledRawJointHybridPhysicalCompatibleValidatedExtraRationalPolicy A
        strategy hwin initial initialExtra ExtraValid extraAdvance)
    (state :
      ProfiledRawJointHybridPhysicalCompatibleValidatedExtraPolicyState A
        strategy hwin initial initialExtra ExtraValid extraAdvance) : Prop :=
  SourceFreeBeliefCodeParityRationalPolicy.Reachable
    (sourceFreeBeliefParentLinkedCodeParityDPA
      (Annotation := JointAnnotation A (Extra := Extra))
      (profiledRawJointHybridCodeParityDPA A
        (.common ((profiledRawJointCommonWorldFamily A initial).incidenceCode
          A))))
    ((.common ((profiledRawJointCommonWorldFamily A initial).incidenceCode A)),
      profiledRawJointHybridPhysicalCompatibleExtraInitial A initialExtra)
    (sourceFreeBeliefParentLinkedValid
      (ProfiledRawJointHybridProvenanceValid A strategy)
      (ProfiledRawJointHybridPhysicalCompatibleValidatedExtraParentLinkValid A
        strategy hwin ExtraValid extraAdvance))
    (sourceFreeBeliefFiniteCodeNext
      (sourceFreeBeliefParentLinkedNext (profiledRawJointHybridNext A)))
    policy state

/-- The invariant-aware rational policy exists without an additional finite
summary hypothesis. -/
theorem
    nonempty_profiledRawJointHybridPhysicalCompatibleValidatedExtraRationalPolicy
    (initial : ProfiledRawJointCommonBaseWorld A strategy)
    (initialExtra : Extra)
    (ExtraValid : HybridState A strategy → Extra → Prop)
    (extraAdvance : HybridState A strategy → Extra →
      HybridDirection (In₁ := In₁) (In₂ := In₂) → Extra)
    (hinitial : ExtraValid (.common initial) initialExtra)
    (hstep : ∀ source current direction,
      ExtraValid source current →
        ExtraValid (source.step A direction)
          (extraAdvance source current direction)) :
    Nonempty
      (ProfiledRawJointHybridPhysicalCompatibleValidatedExtraRationalPolicy A
        strategy hwin initial initialExtra ExtraValid extraAdvance) := by
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
    (ProfiledRawJointHybridPhysicalCompatibleValidatedExtraParentLinkValid A
      strategy hwin ExtraValid extraAdvance)
    (fun node ↦ by
      let state := carried.stateAt node
      have hcurrent :=
        profiledRawJointHybridPhysicalCompatibleValidatedExtraCarriedTree_current
          A strategy hwin initial initialExtra extraAdvance ExtraValid hinitial
            hstep node
      exact
        profiledRawJointHybridPhysicalCompatibleValidatedExtraParentLinkValid_of_semantic
          A strategy hwin ExtraValid extraAdvance state.1 state.2 hcurrent.1
            hcurrent.2)

/-! ## Reachable inversion -/

/-- A reachable state has one representative explaining the current physical
annotation, the current extra, all child annotations, and every policy
successor. -/
theorem
    exists_profiledRawJointHybridPhysicalCompatibleValidatedExtraSemanticSource
    (initial : ProfiledRawJointCommonBaseWorld A strategy)
    (initialExtra : Extra)
    (ExtraValid : HybridState A strategy → Extra → Prop)
    (extraAdvance : HybridState A strategy → Extra →
      HybridDirection (In₁ := In₁) (In₂ := In₂) → Extra)
    (policy :
      ProfiledRawJointHybridPhysicalCompatibleValidatedExtraRationalPolicy A
        strategy hwin initial initialExtra ExtraValid extraAdvance)
    (state :
      ProfiledRawJointHybridPhysicalCompatibleValidatedExtraPolicyState A
        strategy hwin initial initialExtra ExtraValid extraAdvance)
    (hreachable :
      ProfiledRawJointHybridPhysicalCompatibleValidatedExtraReachable A
        strategy hwin initial initialExtra ExtraValid extraAdvance policy
          state) :
    ∃ move : SourceFreeBeliefParentLinkedMove
        (Direction := HybridDirection (In₁ := In₁) (In₂ := In₂))
        (Move := ProfiledRawJointHybridMove A)
        (Annotation := JointAnnotation A (Extra := Extra)),
      ∃ source : HybridState A strategy,
        source.code A = state.1.1 ∧
          source.move A = move.1 ∧
          ProfiledRawJointHybridPhysicalCurrentCompatible A strategy source
            state.1.2.1 ∧
          ExtraValid source state.1.2.2 ∧
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
                  (Annotation := JointAnnotation A (Extra := Extra))
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
        (ProfiledRawJointHybridPhysicalCompatibleValidatedExtraParentLinkValid
          A strategy hwin ExtraValid extraAdvance)
        (profiledRawJointHybridNext A)
        policy state hreachable with
    ⟨move, _hvalid, hlink, hsuccessor⟩
  rcases hlink with
    ⟨source, hcode, hmove, hphysical, hextra, hchildren⟩
  exact ⟨move, source, hcode, hmove, hphysical, hextra, hchildren, hsuccessor⟩

end

end DetParityAutomaton

end DistributedSynthesis
