/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleValidatedExtraAnnotation
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleLiteralPrefixCurrent

/-!
# The validated current literal-prefix policy

This module instantiates the generic validated-extra rationalization with the
input-independent literal seed and the concrete current-table provenance
relation.  It is the finite-policy endpoint of that construction:

* the root carries the exact right/left tables selected at the initial common
  occurrence, before any future strict input;
* replacement along every semantic edge establishes provenance at the exact
  child; and
* reachable inversion returns one source explaining the current physical
  annotation, the current literal tables, the complete child assignment, and
  the linked DPA successor.

The runtime policy stores only finite codes and tables.  The semantic source,
parent, and incoming-edge witnesses occur only in proofs.
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

private abbrev HybridState :=
  ProfiledRawJointHybridSemanticState A strategy

private abbrev HybridDirection :=
  ProfiledRawJointHybridDirection (In₁ := In₁) (In₂ := In₂)

private abbrev LiteralAnnotation :=
  ProfiledRawJointHybridLiteralPrefixEdgeAnnotation A

/-! ## Concrete finite policy -/

/-- One jointly rationalized policy carrying the physical annotation and a
literal table pair whose provenance is valid at the current semantic source. -/
noncomputable abbrev
    ProfiledRawJointHybridPhysicalCompatibleValidatedLiteralPrefixPolicy
    (initial : ProfiledRawJointCommonBaseWorld A strategy) :=
  ProfiledRawJointHybridPhysicalCompatibleValidatedExtraRationalPolicy A
    strategy hwin initial
      (profiledRawJointHybridLiteralPrefixSeedAnnotation A strategy hwin
        initial)
      (ProfiledRawJointHybridLiteralPrefixCurrentCompatible A strategy hwin
        initial)
      (profiledRawJointHybridLiteralPrefixAnnotationAdvance A strategy hwin)

noncomputable abbrev
    ProfiledRawJointHybridPhysicalCompatibleValidatedLiteralPrefixPolicyState
    (initial : ProfiledRawJointCommonBaseWorld A strategy) :=
  ProfiledRawJointHybridPhysicalCompatibleValidatedExtraPolicyState A strategy
    hwin initial
      (profiledRawJointHybridLiteralPrefixSeedAnnotation A strategy hwin
        initial)
      (ProfiledRawJointHybridLiteralPrefixCurrentCompatible A strategy hwin
        initial)
      (profiledRawJointHybridLiteralPrefixAnnotationAdvance A strategy hwin)

abbrev
    ProfiledRawJointHybridPhysicalCompatibleValidatedLiteralPrefixReachable
    (initial : ProfiledRawJointCommonBaseWorld A strategy)
    (policy :
      ProfiledRawJointHybridPhysicalCompatibleValidatedLiteralPrefixPolicy A
        strategy hwin initial)
    (state :
      ProfiledRawJointHybridPhysicalCompatibleValidatedLiteralPrefixPolicyState
        A strategy hwin initial) : Prop :=
  ProfiledRawJointHybridPhysicalCompatibleValidatedExtraReachable A strategy
    hwin initial
      (profiledRawJointHybridLiteralPrefixSeedAnnotation A strategy hwin
        initial)
      (ProfiledRawJointHybridLiteralPrefixCurrentCompatible A strategy hwin
        initial)
      (profiledRawJointHybridLiteralPrefixAnnotationAdvance A strategy hwin)
      policy state

/-- The concrete validated current-table policy exists for every winning
strategy.  Preservation is unconditional because the annotation update is
replace-only and records its actual incoming semantic edge. -/
theorem
    nonempty_profiledRawJointHybridPhysicalCompatibleValidatedLiteralPrefixPolicy
    (initial : ProfiledRawJointCommonBaseWorld A strategy) :
    Nonempty
      (ProfiledRawJointHybridPhysicalCompatibleValidatedLiteralPrefixPolicy A
        strategy hwin initial) := by
  exact
    nonempty_profiledRawJointHybridPhysicalCompatibleValidatedExtraRationalPolicy
      A strategy hwin initial
        (profiledRawJointHybridLiteralPrefixSeedAnnotation A strategy hwin
          initial)
        (ProfiledRawJointHybridLiteralPrefixCurrentCompatible A strategy hwin
          initial)
        (profiledRawJointHybridLiteralPrefixAnnotationAdvance A strategy hwin)
        (profiledRawJointHybridLiteralPrefixCurrentCompatible_initial A
          strategy hwin initial)
        (fun source current direction _ ↦
          profiledRawJointHybridLiteralPrefixCurrentCompatible_advance A
            strategy hwin initial source current direction)

/-! ## Reachable same-source inversion -/

/-- A reachable finite-policy state has one semantic source which validates
both current annotations and explains the complete executable successor map. -/
theorem
    exists_profiledRawJointHybridPhysicalCompatibleValidatedLiteralPrefixSemanticSource
    (initial : ProfiledRawJointCommonBaseWorld A strategy)
    (policy :
      ProfiledRawJointHybridPhysicalCompatibleValidatedLiteralPrefixPolicy A
        strategy hwin initial)
    (state :
      ProfiledRawJointHybridPhysicalCompatibleValidatedLiteralPrefixPolicyState
        A strategy hwin initial)
    (hreachable :
      ProfiledRawJointHybridPhysicalCompatibleValidatedLiteralPrefixReachable
        A strategy hwin initial policy state) :
    ∃ move : SourceFreeBeliefParentLinkedMove
        (Direction := HybridDirection (In₁ := In₁) (In₂ := In₂))
        (Move := ProfiledRawJointHybridMove A)
        (Annotation :=
          ProfiledRawJointHybridPhysicalCompatibleExtraAnnotation A
            (LiteralAnnotation A)),
      ∃ source : HybridState A strategy,
        source.code A = state.1.1 ∧
          source.move A = move.1 ∧
          ProfiledRawJointHybridPhysicalCurrentCompatible A strategy source
            state.1.2.1 ∧
          ProfiledRawJointHybridLiteralPrefixCurrentCompatible A strategy hwin
            initial source state.1.2.2 ∧
          (∀ direction,
            profiledRawJointHybridPhysicalCompatibleExtraAdvance A strategy
                hwin
                (profiledRawJointHybridLiteralPrefixAnnotationAdvance A
                  strategy hwin)
                source state.1.2 direction =
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
                      (LiteralAnnotation A))
                  (profiledRawJointHybridCodeParityDPA A
                    (.common ((profiledRawJointCommonWorldFamily A initial
                      ).incidenceCode A)))).step state.2 childCode) := by
  exact
    exists_profiledRawJointHybridPhysicalCompatibleValidatedExtraSemanticSource
      A strategy hwin initial
        (profiledRawJointHybridLiteralPrefixSeedAnnotation A strategy hwin
          initial)
        (ProfiledRawJointHybridLiteralPrefixCurrentCompatible A strategy hwin
          initial)
        (profiledRawJointHybridLiteralPrefixAnnotationAdvance A strategy hwin)
        policy state hreachable

/-- Complete one-step form.  The target's current-table invariant is proved
for the exact semantic child whose code, physical payload, literal payload,
and linked-DPA state occur in that same executable successor. -/
theorem
    exists_profiledRawJointHybridPhysicalCompatibleValidatedLiteralPrefixSuccessorSemantics
    (initial : ProfiledRawJointCommonBaseWorld A strategy)
    (policy :
      ProfiledRawJointHybridPhysicalCompatibleValidatedLiteralPrefixPolicy A
        strategy hwin initial)
    (state :
      ProfiledRawJointHybridPhysicalCompatibleValidatedLiteralPrefixPolicyState
        A strategy hwin initial)
    (hreachable :
      ProfiledRawJointHybridPhysicalCompatibleValidatedLiteralPrefixReachable
        A strategy hwin initial policy state) :
    ∃ move : SourceFreeBeliefParentLinkedMove
        (Direction := HybridDirection (In₁ := In₁) (In₂ := In₂))
        (Move := ProfiledRawJointHybridMove A)
        (Annotation :=
          ProfiledRawJointHybridPhysicalCompatibleExtraAnnotation A
            (LiteralAnnotation A)),
      ∃ source : HybridState A strategy,
        source.code A = state.1.1 ∧
          source.move A = move.1 ∧
          ProfiledRawJointHybridPhysicalCurrentCompatible A strategy source
            state.1.2.1 ∧
          ProfiledRawJointHybridLiteralPrefixCurrentCompatible A strategy hwin
            initial source state.1.2.2 ∧
          ∀ direction : HybridDirection (In₁ := In₁) (In₂ := In₂),
            let childCode := sourceFreeBeliefParentLinkedNext
              (profiledRawJointHybridNext A) state.1 move direction
            let target := policy.successor state childCode
            target.1.1 = (source.step A direction).code A ∧
              target.1.2.1 =
                profiledRawJointHybridPhysicalAnnotationAdvance A strategy
                  hwin source state.1.2.1 direction ∧
              target.1.2.2 =
                profiledRawJointHybridLiteralPrefixAnnotationAdvance A
                  strategy hwin source state.1.2.2 direction ∧
              ProfiledRawJointHybridLiteralPrefixCurrentCompatible A strategy
                hwin initial (source.step A direction) target.1.2.2 ∧
              target.2 =
                (sourceFreeBeliefParentLinkedCodeParityDPA
                  (Annotation :=
                    ProfiledRawJointHybridPhysicalCompatibleExtraAnnotation A
                      (LiteralAnnotation A))
                  (profiledRawJointHybridCodeParityDPA A
                    (.common ((profiledRawJointCommonWorldFamily A initial
                      ).incidenceCode A)))).step state.2 childCode := by
  rcases
      exists_profiledRawJointHybridPhysicalCompatibleValidatedLiteralPrefixSemanticSource
        A strategy hwin initial policy state hreachable with
    ⟨move, source, hcode, hmove, hphysical, hextra, hchildren,
      hsuccessor⟩
  refine ⟨move, source, hcode, hmove, hphysical, hextra, ?_⟩
  intro direction
  simp only
  rw [hsuccessor direction]
  have hchild := (hchildren direction).symm
  have hphysicalChild := congrArg (fun annotation ↦ annotation.1) hchild
  have hextraChild := congrArg (fun annotation ↦ annotation.2) hchild
  change (move.2 direction).1 =
      profiledRawJointHybridPhysicalAnnotationAdvance A strategy hwin source
        state.1.2.1 direction at hphysicalChild
  change (move.2 direction).2 =
      profiledRawJointHybridLiteralPrefixAnnotationAdvance A strategy hwin
        source state.1.2.2 direction at hextraChild
  constructor
  · change profiledRawJointHybridNext A state.1.1 move.1 direction =
      (source.step A direction).code A
    rw [← hcode, ← hmove]
    exact (source.step_code A direction).symm
  · constructor
    · exact hphysicalChild
    · constructor
      · exact hextraChild
      · constructor
        · change ProfiledRawJointHybridLiteralPrefixCurrentCompatible A
            strategy hwin initial (source.step A direction)
              (move.2 direction).2
          rw [hextraChild]
          exact
            profiledRawJointHybridLiteralPrefixCurrentCompatible_advance A
              strategy hwin initial source state.1.2.2 direction
        · rfl

end

end DetParityAutomaton

end DistributedSynthesis
