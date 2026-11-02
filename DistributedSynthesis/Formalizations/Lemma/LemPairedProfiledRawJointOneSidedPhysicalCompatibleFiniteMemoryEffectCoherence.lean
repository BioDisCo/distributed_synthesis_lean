/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedAutomaton

/-!
# Finite-effect coherence for the enriched table verifier

Equality of complete raw lambda moves is a sound way to prevent semantic
mosaics, but it is stronger than the finite controller observes.  This file
isolates the weaker condition needed to certify the table's forward policy:
all exact histories represented by a table cell have the same finite public
successor signature.

The main theorem below reconstructs a legal raw witness from any exact member
of the nonempty canonical cell.  Signature coherence then proves that this
witness realizes the whole stored public successor row.  Thus equality of the
generally infinite raw moves is not needed for downstream table certification.
It remains a separate question whether finite-effect coherence is sufficient
to transfer `hwin` to the literal owner-fibre safety check.
-/

namespace DistributedSynthesis

universe u v x y s m

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable {Memory : Type m}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
  [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]
variable [Fintype Memory]

variable
  (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
  (hwin : ∀ env : EnvironmentSequence In₁ In₂,
    A.Accepts (execution strategy env))

private abbrev RootKey :=
  ProfiledRawJointOneSidedPhysicalCompatibleRootKey A strategy

private abbrev PhysicalAnnotation :=
  ProfiledRawJointHybridPhysicalEdgeAnnotation A

private abbrev LinkedCode :=
  SourceFreeBeliefParentLinkedCode
    (BeliefCode := ProfiledRawJointIncidenceCode A (I := Unit))
    (Annotation := PhysicalAnnotation A)

private abbrev ActualDirection :=
  ProfiledRawJointActualDirection (I := Unit) (In₁ := In₁) (In₂ := In₂)

private abbrev LinkedMove :=
  SourceFreeBeliefParentLinkedMove
    (Direction := ActualDirection (In₁ := In₁) (In₂ := In₂))
    (Move := ProfiledRawJointLambdaFamilyMove A (I := Unit))
    (Annotation := PhysicalAnnotation A)

private abbrev PolicyDPA
    (initialCode : ProfiledRawJointIncidenceCode A (I := Unit)) :=
  sourceFreeBeliefParentLinkedCodeParityDPA
    (Annotation := PhysicalAnnotation A)
    (profiledRawJointOneSidedCodeParityDPA A initialCode)

private abbrev PolicyValid :=
  sourceFreeBeliefParentLinkedValid
    (ProfiledRawJointOneSidedProvenanceValid A strategy)
    (ProfiledRawJointOneSidedPhysicalCompatibleParentLinkValid A strategy hwin)

private noncomputable abbrev PolicyNext :
    LinkedCode A →
      LinkedMove A (In₁ := In₁) (In₂ := In₂) →
        LinkedCode A → LinkedCode A :=
  sourceFreeBeliefFiniteCodeNext
    (sourceFreeBeliefParentLinkedNext (profiledRawJointOneSidedNext A))

private abbrev FixedTable (key : RootKey A strategy) :=
  ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTable
    (Memory := Memory) A strategy key

private abbrev PolicyState (key : RootKey A strategy) :=
  ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyState
    (Memory := Memory) A key.1.1

namespace
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTable

variable
  (initialMemory : RootKey A strategy → Memory)
  (key : RootKey A strategy)
  (table : FixedTable (Memory := Memory) A strategy key)

/-- Effect-level local coherence: the canonical cell is nonempty and every
exact history in it induces the one finite public successor row stored by the
table.  No equality between complete raw moves is required. -/
def EffectLocallyValid
    (state : PolicyState (Memory := Memory) A strategy key) : Prop :=
  table.CanonicalBeliefAt A strategy hwin initialMemory key state ∧
    table.CanonicalPublicSuccessorCoherent A strategy hwin initialMemory key
      state

omit [Fintype Memory] in
/-- One exact member of an effect-coherent cell supplies a legal raw move
which realizes the complete stored public successor row. -/
theorem EffectLocallyValid.toTransitionTableValid
    (state : PolicyState (Memory := Memory) A strategy key)
    (hvalid :
      table.EffectLocallyValid A strategy hwin initialMemory key state) :
    ∃ move : LinkedMove A (In₁ := In₁) (In₂ := In₂),
      PolicyValid A strategy hwin state.1.1 move ∧
        ∀ childCode,
          (table.successor state childCode).1 =
            sourceFreeBeliefCodeParityControllerNext
              (PolicyDPA A key.1.1) state.1 move
              (PolicyNext A (In₁ := In₁) (In₂ := In₂)
                state.1.1 move childCode) := by
  rcases hvalid.1.1 with ⟨exact, hexact⟩
  have hpublic := hvalid.1.2 exact hexact
  let move : LinkedMove A (In₁ := In₁) (In₂ := In₂) :=
    profiledRawJointOneSidedSemanticLinkedMove A strategy hwin exact.1.1
      exact.1.2
  refine ⟨move, ?_, ?_⟩
  · constructor
    · constructor
      · rw [← hpublic.1]
        simpa [move, profiledRawJointOneSidedSemanticLinkedMove] using
          ProfiledRawJointOneSidedSemanticState.move_valid_of_winning A hwin
            exact.1.1
      · exact ⟨exact.1.1, hpublic.1, by simp [move,
          profiledRawJointOneSidedSemanticLinkedMove]⟩
    · have hcompatible :
          ProfiledRawJointOneSidedPhysicalAnnotationCompatible A strategy
            exact.1.1 state.1.1.2 := by
        rw [← hpublic.2]
        exact exact.2
      rw [← hpublic.1]
      simpa [move, profiledRawJointOneSidedSemanticLinkedMove, hpublic.2]
        using
          (profiledRawJointOneSidedPhysicalCompatibleParentLinkValid_of_semantic
            A strategy hwin exact.1.1 state.1.1.2 hcompatible)
  · intro childCode
    have hsignature := congrFun (hvalid.2 exact hexact) childCode
    exact hsignature.symm

/-- Effect-level coherence at every state reachable in the table fold. -/
def EffectEnrichedValidAt : Prop :=
  ∀ node : TreeNode (LinkedCode A),
    let state :=
      sourceFreeBeliefCodeParityFiniteMemoryTransitionStateAt
        (PolicyDPA A key.1.1) key.1 (initialMemory key) table node
    table.EffectLocallyValid A strategy hwin initialMemory key state

/-- The weaker finite-effect checker retains the same forward and literal
owner-fibre parity obligations. -/
def EffectEnrichedChecks : Prop :=
  table.EffectEnrichedValidAt A strategy hwin initialMemory key ∧
    table.EnrichedForwardAccepts A strategy initialMemory key ∧
    table.EnrichedOwnerSafe A strategy hwin initialMemory key

omit [Fintype Memory] in
/-- Reachable effect coherence is sufficient for ordinary table validity. -/
theorem EffectEnrichedValidAt.toTransitionTableValidAt
    (hvalid :
      table.EffectEnrichedValidAt A strategy hwin initialMemory key) :
    table.ValidAt (PolicyDPA A key.1.1) key.1 (initialMemory key)
      (PolicyValid A strategy hwin)
      (PolicyNext A (In₁ := In₁) (In₂ := In₂)) := by
  intro node
  exact
    (hvalid node).toTransitionTableValid A strategy hwin initialMemory key
      table _

omit [Fintype Memory] in
/-- The original complete-raw-move condition implies the weaker finite-effect
condition at every reachable table state. -/
theorem EnrichedValidAt.toEffectEnrichedValidAt
    (hvalid : table.EnrichedValidAt A strategy hwin initialMemory key) :
    table.EffectEnrichedValidAt A strategy hwin initialMemory key := by
  intro node
  have hlocal := hvalid node
  exact ⟨hlocal.1,
    hlocal.canonicalPublicSuccessorCoherent A strategy hwin initialMemory key
      table⟩

/-- Strong enriched checks imply the effect-level checks; owner safety and
both parity obligations are unchanged. -/
theorem EnrichedChecks.toEffectEnrichedChecks
    (hchecks : table.EnrichedChecks A strategy hwin initialMemory key) :
    table.EffectEnrichedChecks A strategy hwin initialMemory key :=
  ⟨hchecks.1.toEffectEnrichedValidAt A strategy hwin initialMemory key table,
    hchecks.2⟩

/-- Effect-level checks already certify the augmented forward policy.  Thus
complete raw-move equality is not a downstream requirement of policy
extraction. -/
def EffectEnrichedChecks.toFiniteMemoryPolicy
    (hchecks : table.EffectEnrichedChecks A strategy hwin initialMemory key) :
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicy
      (Memory := Memory) A strategy hwin (initialMemory key) key.1.1 key.1.2 :=
  SourceFreeBeliefCodeParityFiniteMemoryTransitionTable.toFiniteMemoryPolicy
    (PolicyDPA A key.1.1) key.1 (initialMemory key)
    (PolicyValid A strategy hwin)
    (PolicyNext A (In₁ := In₁) (In₂ := In₂))
    table
    (hchecks.1.toTransitionTableValidAt A strategy hwin initialMemory key
      table)
    hchecks.2.1

end
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTable

end

end DetParityAutomaton

end DistributedSynthesis
