/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenOptionalFixedPinnedFamily
import DistributedSynthesis.Formalizations.Lemma.LemFiniteRootFamilyPinnedProvenance

/-!
# Semantic provenance on the canonical fixed pinned controller

A weak fixed-family move cannot inherit semantic provenance merely because a
separate source-fibre controller has it: two independent rational
extractions need not choose the same controller.  This file performs one
strong extraction directly over the canonical hidden-descriptor roots and
then weakens the table predicate on the *same* labeled tree.  Its weak
projection is therefore an ordinary value of the fixed pinned alphabet, while
the package still exposes arbitrary-node literal semantic provenance.

No lane, orientation, selected descriptor, or strict-leader bit is added to
the sender control.  All canonical root transports remain proof-side.
-/

namespace DistributedSynthesis

universe i u v x y s

namespace DetParityAutomaton

variable {I : Type i}
variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Fintype I]
variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
  [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

variable (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
variable (hwin : ∀ env : EnvironmentSequence In₁ In₂,
  A.Accepts (execution strategy env))
variable (basis : ∀ state : PairedProfiledTreeState A,
  (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)

variable (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))

noncomputable local instance fixedPinnedProvenanceDescriptorDecidableEq :
    DecidableEq
      (ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I) initialCode) :=
  Classical.decEq _

/-! ## Two-live right side -/

variable (control : ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis
    (I := I) →
  (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode).State)

/-- Literal semantic table provenance, transported from each realized source
root to its canonical hidden-descriptor root. -/
def profiledOpenFixedPinnedRightSemanticAllowed
    (source : ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis
      (I := I))
    (descriptor : ProfiledOpenHiddenDescriptorRightCarrier A
      (profiledOpenFixedPinnedFamilyCode A strategy hwin basis initialCode
        control source))
    (responses :
      ((ProfiledOpenHiddenDescriptorRightRoot A descriptor.1 × In₂) ×
        In₁) → ProfiledOpenRightClassifiedOutput A) : Prop :=
  let point := profiledOpenFixedPinnedRightPoint A strategy hwin basis
    initialCode control source descriptor
  let table := ((point.rightLane.realization.coherentTable A).table
    |>.toClassified A point.rightLane.source)
  let hmove := profiledOpenFixedPinnedRightPoint_moveIdentity A strategy hwin
    basis initialCode control source descriptor
  ProfiledOpenRightSemanticTableAllowed A point.rightLane.source strategy hwin
    point.rightLane.realization.entry basis (fun input ↦
      responses
        ((profiledOpenHiddenDescriptorRightRootOfEq A descriptor.1
            point.rightLane.source table hmove input.1.1,
          input.1.2), input.2))

omit [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledOpenFixedPinnedRightSemanticAllowed_implies_weak
    (source : ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis
      (I := I))
    (descriptor : ProfiledOpenHiddenDescriptorRightCarrier A
      (profiledOpenFixedPinnedFamilyCode A strategy hwin basis initialCode
        control source))
    (responses :
      ((ProfiledOpenHiddenDescriptorRightRoot A descriptor.1 × In₂) ×
        In₁) → ProfiledOpenRightClassifiedOutput A)
    (hsemantic : profiledOpenFixedPinnedRightSemanticAllowed A strategy hwin
      basis initialCode control source descriptor responses) :
    ProfiledOpenHiddenDescriptorRightWeakAllowed A descriptor.1 responses := by
  let point := profiledOpenFixedPinnedRightPoint A strategy hwin basis
    initialCode control source descriptor
  let table := ((point.rightLane.realization.coherentTable A).table
    |>.toClassified A point.rightLane.source)
  let hmove := profiledOpenFixedPinnedRightPoint_moveIdentity A strategy hwin
    basis initialCode control source descriptor
  apply profiledOpenHiddenDescriptorRightWeakAllowed_ofEq A descriptor.1
    point.rightLane.source table hmove
  rcases hsemantic with ⟨past, hpast⟩
  rw [hpast]
  exact profiledOpenRightSemanticClassifiedFamilyReceiver_allowed A
    point.rightLane.source strategy hwin point.rightLane.realization.entry
    point.rightLane.realization.minimum basis past

/-- Canonical right fixed move with the strong law retained on its literal
underlying controller. -/
noncomputable abbrev ProfiledOpenFixedPinnedRightProvenanceMove
    (source : ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis
      (I := I)) :=
  FiniteDescriptorFamilyPinnedProvenanceMove
    (fun descriptor : ProfiledOpenHiddenDescriptorRightCarrier A
      (profiledOpenFixedPinnedFamilyCode A strategy hwin basis initialCode
        control source) ↦
      ProfiledOpenHiddenDescriptorRightRoot A descriptor.1)
    (fun descriptor root ↦
      profiledOpenHiddenDescriptorRightMonitor A descriptor.1 root)
    (profiledOpenFixedPinnedRightSemanticAllowed A strategy hwin basis
      initialCode control source)
    (fun descriptor responses ↦
      ProfiledOpenHiddenDescriptorRightWeakAllowed A descriptor.1 responses)
    (profiledOpenFixedPinnedRightExpected A strategy hwin basis initialCode
      control source)

noncomputable def profiledOpenFixedPinnedRightProvenanceMoveOfWinning
    (source : ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis
      (I := I)) :
    ProfiledOpenFixedPinnedRightProvenanceMove A strategy hwin basis
      initialCode control source := by
  classical
  let family := profiledOpenFixedPinnedFamilyCode A strategy hwin basis
    initialCode control source
  let Root := fun descriptor : ProfiledOpenHiddenDescriptorRightCarrier A
      family ↦ ProfiledOpenHiddenDescriptorRightRoot A descriptor.1
  let baseM : ∀ descriptor, Root descriptor →
      BlockRecordMonitor In₂ In₁ (ProfiledOpenRightClassifiedOutput A) Out₁ :=
    fun descriptor root ↦
      profiledOpenHiddenDescriptorRightMonitor A descriptor.1 root
  let expected := profiledOpenFixedPinnedRightExpected A strategy hwin basis
    initialCode control source
  let Strong := profiledOpenFixedPinnedRightSemanticAllowed A strategy hwin
    basis initialCode control source
  let Weak : ∀ descriptor,
      (((Root descriptor × In₂) × In₁) →
        ProfiledOpenRightClassifiedOutput A) → Prop :=
    fun descriptor responses ↦
      ProfiledOpenHiddenDescriptorRightWeakAllowed A descriptor.1 responses
  let receiver := profiledOpenFixedPinnedRightReceiver A strategy hwin basis
    initialCode control source
  let sender := profiledOpenFixedPinnedRightSender A strategy hwin basis source
  letI : Inhabited (Sigma Root) :=
    ⟨profiledOpenFixedPinnedRightDefaultMember A strategy hwin basis
      initialCode control source⟩
  letI : Inhabited (ProfiledOpenRightClassifiedOutput A) :=
    ⟨profiledOpenOptionalDefaultRightClassifiedOutput A strategy hwin basis⟩
  have hstrong : ∀ past,
      DescriptorRootUnionAllowed Root Strong
        (finiteRootFamilyReceiver receiver past) := by
    intro past descriptor
    let point := profiledOpenFixedPinnedRightPoint A strategy hwin basis
      initialCode control source descriptor
    let table := ((point.rightLane.realization.coherentTable A).table
      |>.toClassified A point.rightLane.source)
    let hmove := profiledOpenFixedPinnedRightPoint_moveIdentity A strategy hwin
      basis initialCode control source descriptor
    refine ⟨past.map (fun old ↦
      ((point.rightLane.realization.pivot, old.1.2), old.2)), ?_⟩
    funext input
    simp [Strong, profiledOpenFixedPinnedRightSemanticAllowed,
      profiledOpenRightSemanticClassifiedFamilyReceiver, receiver,
      profiledOpenFixedPinnedRightReceiver,
      profiledOpenFixedPinnedRightRoot, finiteRootFamilyReceiver,
      List.map_map, Function.comp_def, point, table, hmove,
      profiledOpenHiddenDescriptorRightRootToEq_rootOfEq]
  apply finiteDescriptorFamilyPinnedProvenanceMoveOfStrategies Root baseM
    Strong Weak expected
    (fun descriptor responses hsemantic ↦
      profiledOpenFixedPinnedRightSemanticAllowed_implies_weak A strategy hwin
        basis initialCode control source descriptor responses hsemantic)
    (finiteRootFamilyReceiver receiver []) (hstrong []) receiver sender
  · exact profiledOpenFixedPinnedRight_memberWins A strategy hwin basis
      initialCode control source
  · intro member input
    rfl
  · exact hstrong

/-- Weak fixed-alphabet projection of the same controller. -/
noncomputable def ProfiledOpenFixedPinnedRightProvenanceMove.toPinnedMove
    (source : ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis
      (I := I))
    (move : ProfiledOpenFixedPinnedRightProvenanceMove A strategy hwin basis
      initialCode control source) :
    ProfiledOpenHiddenDescriptorRightPinnedFamilyMove A
      (profiledOpenFixedPinnedFamilyCode A strategy hwin basis initialCode
        control source)
      (profiledOpenFixedPinnedRightExpected A strategy hwin basis initialCode
        control source) :=
  FiniteDescriptorFamilyPinnedProvenanceMove.toPinnedMove
    (fun descriptor : ProfiledOpenHiddenDescriptorRightCarrier A
      (profiledOpenFixedPinnedFamilyCode A strategy hwin basis initialCode
        control source) ↦
      ProfiledOpenHiddenDescriptorRightRoot A descriptor.1)
    (fun descriptor root ↦
      profiledOpenHiddenDescriptorRightMonitor A descriptor.1 root)
    (profiledOpenFixedPinnedRightSemanticAllowed A strategy hwin basis
      initialCode control source)
    (fun descriptor responses ↦
      ProfiledOpenHiddenDescriptorRightWeakAllowed A descriptor.1 responses)
    (profiledOpenFixedPinnedRightExpected A strategy hwin basis initialCode
      control source) move

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Arbitrary-node provenance on the literal controller returned to the fixed
alphabet. -/
theorem ProfiledOpenFixedPinnedRightProvenanceMove.controllerFor_semantic
    (source : ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis
      (I := I))
    (move : ProfiledOpenFixedPinnedRightProvenanceMove A strategy hwin basis
      initialCode control source)
    (descriptor : ProfiledOpenHiddenDescriptorRightCarrier A
      (profiledOpenFixedPinnedFamilyCode A strategy hwin basis initialCode
        control source)) :
    NarrowedTablesAllowed
      (finiteRootFamilyMonitor
        (descriptorRootPinnedMonitor
          (fun descriptor : ProfiledOpenHiddenDescriptorRightCarrier A
            (profiledOpenFixedPinnedFamilyCode A strategy hwin basis
              initialCode control source) ↦
            ProfiledOpenHiddenDescriptorRightRoot A descriptor.1)
          (fun descriptor root ↦
            profiledOpenHiddenDescriptorRightMonitor A descriptor.1 root)
          (profiledOpenFixedPinnedRightExpected A strategy hwin basis
            initialCode control source) descriptor))
      (profiledOpenFixedPinnedRightSemanticAllowed A strategy hwin basis
        initialCode control source descriptor)
      ((ProfiledOpenFixedPinnedRightProvenanceMove.toPinnedMove A strategy hwin
        basis initialCode control source move).controllerFor
          (fun descriptor : ProfiledOpenHiddenDescriptorRightCarrier A
            (profiledOpenFixedPinnedFamilyCode A strategy hwin basis
              initialCode control source) ↦
            ProfiledOpenHiddenDescriptorRightRoot A descriptor.1)
          (descriptorRootPinnedMonitor
            (fun descriptor : ProfiledOpenHiddenDescriptorRightCarrier A
              (profiledOpenFixedPinnedFamilyCode A strategy hwin basis
                initialCode control source) ↦
              ProfiledOpenHiddenDescriptorRightRoot A descriptor.1)
            (fun descriptor root ↦
              profiledOpenHiddenDescriptorRightMonitor A descriptor.1 root)
            (profiledOpenFixedPinnedRightExpected A strategy hwin basis
              initialCode control source))
          (fun descriptor responses ↦
            ProfiledOpenHiddenDescriptorRightWeakAllowed A descriptor.1
              responses)
          descriptor |>.labeledTree) := by
  exact FiniteDescriptorFamilyPinnedProvenanceMove.controllerFor_strongAllowed
    (fun descriptor : ProfiledOpenHiddenDescriptorRightCarrier A
      (profiledOpenFixedPinnedFamilyCode A strategy hwin basis initialCode
        control source) ↦ ProfiledOpenHiddenDescriptorRightRoot A descriptor.1)
    (fun descriptor root ↦
      profiledOpenHiddenDescriptorRightMonitor A descriptor.1 root)
    (profiledOpenFixedPinnedRightSemanticAllowed A strategy hwin basis
      initialCode control source)
    (fun descriptor responses ↦
      ProfiledOpenHiddenDescriptorRightWeakAllowed A descriptor.1 responses)
    (profiledOpenFixedPinnedRightExpected A strategy hwin basis initialCode
      control source) move descriptor

/-! ## Two-live left side -/

/-- Literal left semantic table provenance, transported from each realized
source root to its canonical hidden-descriptor root. -/
def profiledOpenFixedPinnedLeftSemanticAllowed
    (source : ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis
      (I := I))
    (descriptor : ProfiledOpenHiddenDescriptorLeftCarrier A
      (profiledOpenFixedPinnedFamilyCode A strategy hwin basis initialCode
        control source))
    (responses :
      ((ProfiledOpenHiddenDescriptorLeftRoot A descriptor.1 × In₁) ×
        In₂) → ProfiledOpenLeftClassifiedOutput A) : Prop :=
  let point := profiledOpenFixedPinnedLeftPoint A strategy hwin basis
    initialCode control source descriptor
  let table := ((point.leftLane.realization.coherentTable A).table
    |>.toClassified A point.leftLane.source)
  let hmove := profiledOpenFixedPinnedLeftPoint_moveIdentity A strategy hwin
    basis initialCode control source descriptor
  ProfiledOpenLeftSemanticTableAllowed A point.leftLane.source strategy hwin
    point.leftLane.realization.entry basis (fun input ↦
      responses
        ((profiledOpenHiddenDescriptorLeftRootOfEq A descriptor.1
            point.leftLane.source table hmove input.1.1,
          input.1.2), input.2))

omit [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledOpenFixedPinnedLeftSemanticAllowed_implies_weak
    (source : ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis
      (I := I))
    (descriptor : ProfiledOpenHiddenDescriptorLeftCarrier A
      (profiledOpenFixedPinnedFamilyCode A strategy hwin basis initialCode
        control source))
    (responses :
      ((ProfiledOpenHiddenDescriptorLeftRoot A descriptor.1 × In₁) ×
        In₂) → ProfiledOpenLeftClassifiedOutput A)
    (hsemantic : profiledOpenFixedPinnedLeftSemanticAllowed A strategy hwin
      basis initialCode control source descriptor responses) :
    ProfiledOpenHiddenDescriptorLeftWeakAllowed A descriptor.1 responses := by
  let point := profiledOpenFixedPinnedLeftPoint A strategy hwin basis
    initialCode control source descriptor
  let table := ((point.leftLane.realization.coherentTable A).table
    |>.toClassified A point.leftLane.source)
  let hmove := profiledOpenFixedPinnedLeftPoint_moveIdentity A strategy hwin
    basis initialCode control source descriptor
  apply profiledOpenHiddenDescriptorLeftWeakAllowed_ofEq A descriptor.1
    point.leftLane.source table hmove
  rcases hsemantic with ⟨past, hpast⟩
  rw [hpast]
  exact profiledOpenLeftSemanticClassifiedFamilyReceiver_allowed A
    point.leftLane.source strategy hwin point.leftLane.realization.entry
    point.leftLane.realization.minimum basis past

/-- Canonical left fixed move with the strong law retained on its literal
underlying controller. -/
noncomputable abbrev ProfiledOpenFixedPinnedLeftProvenanceMove
    (source : ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis
      (I := I)) :=
  FiniteDescriptorFamilyPinnedProvenanceMove
    (fun descriptor : ProfiledOpenHiddenDescriptorLeftCarrier A
      (profiledOpenFixedPinnedFamilyCode A strategy hwin basis initialCode
        control source) ↦
      ProfiledOpenHiddenDescriptorLeftRoot A descriptor.1)
    (fun descriptor root ↦
      profiledOpenHiddenDescriptorLeftMonitor A descriptor.1 root)
    (profiledOpenFixedPinnedLeftSemanticAllowed A strategy hwin basis
      initialCode control source)
    (fun descriptor responses ↦
      ProfiledOpenHiddenDescriptorLeftWeakAllowed A descriptor.1 responses)
    (profiledOpenFixedPinnedLeftExpected A strategy hwin basis initialCode
      control source)

noncomputable def profiledOpenFixedPinnedLeftProvenanceMoveOfWinning
    (source : ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis
      (I := I)) :
    ProfiledOpenFixedPinnedLeftProvenanceMove A strategy hwin basis
      initialCode control source := by
  classical
  let family := profiledOpenFixedPinnedFamilyCode A strategy hwin basis
    initialCode control source
  let Root := fun descriptor : ProfiledOpenHiddenDescriptorLeftCarrier A
      family ↦ ProfiledOpenHiddenDescriptorLeftRoot A descriptor.1
  let baseM : ∀ descriptor, Root descriptor →
      BlockRecordMonitor In₁ In₂ (ProfiledOpenLeftClassifiedOutput A) Out₂ :=
    fun descriptor root ↦
      profiledOpenHiddenDescriptorLeftMonitor A descriptor.1 root
  let expected := profiledOpenFixedPinnedLeftExpected A strategy hwin basis
    initialCode control source
  let Strong := profiledOpenFixedPinnedLeftSemanticAllowed A strategy hwin
    basis initialCode control source
  let Weak : ∀ descriptor,
      (((Root descriptor × In₁) × In₂) →
        ProfiledOpenLeftClassifiedOutput A) → Prop :=
    fun descriptor responses ↦
      ProfiledOpenHiddenDescriptorLeftWeakAllowed A descriptor.1 responses
  let receiver := profiledOpenFixedPinnedLeftReceiver A strategy hwin basis
    initialCode control source
  let sender := profiledOpenFixedPinnedLeftSender A strategy hwin basis source
  letI : Inhabited (Sigma Root) :=
    ⟨profiledOpenFixedPinnedLeftDefaultMember A strategy hwin basis
      initialCode control source⟩
  letI : Inhabited (ProfiledOpenLeftClassifiedOutput A) :=
    ⟨profiledOpenOptionalDefaultLeftClassifiedOutput A strategy hwin basis⟩
  have hstrong : ∀ past,
      DescriptorRootUnionAllowed Root Strong
        (finiteRootFamilyReceiver receiver past) := by
    intro past descriptor
    let point := profiledOpenFixedPinnedLeftPoint A strategy hwin basis
      initialCode control source descriptor
    let table := ((point.leftLane.realization.coherentTable A).table
      |>.toClassified A point.leftLane.source)
    let hmove := profiledOpenFixedPinnedLeftPoint_moveIdentity A strategy hwin
      basis initialCode control source descriptor
    refine ⟨past.map (fun old ↦
      ((point.leftLane.realization.pivot, old.1.2), old.2)), ?_⟩
    funext input
    simp [Strong, profiledOpenFixedPinnedLeftSemanticAllowed,
      profiledOpenLeftSemanticClassifiedFamilyReceiver, receiver,
      profiledOpenFixedPinnedLeftReceiver,
      profiledOpenFixedPinnedLeftRoot, finiteRootFamilyReceiver,
      List.map_map, Function.comp_def, point, table, hmove,
      profiledOpenHiddenDescriptorLeftRootToEq_rootOfEq]
  apply finiteDescriptorFamilyPinnedProvenanceMoveOfStrategies Root baseM
    Strong Weak expected
    (fun descriptor responses hsemantic ↦
      profiledOpenFixedPinnedLeftSemanticAllowed_implies_weak A strategy hwin
        basis initialCode control source descriptor responses hsemantic)
    (finiteRootFamilyReceiver receiver []) (hstrong []) receiver sender
  · exact profiledOpenFixedPinnedLeft_memberWins A strategy hwin basis
      initialCode control source
  · intro member input
    rfl
  · exact hstrong

/-- Weak left fixed-alphabet projection of the same controller. -/
noncomputable def ProfiledOpenFixedPinnedLeftProvenanceMove.toPinnedMove
    (source : ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis
      (I := I))
    (move : ProfiledOpenFixedPinnedLeftProvenanceMove A strategy hwin basis
      initialCode control source) :
    ProfiledOpenHiddenDescriptorLeftPinnedFamilyMove A
      (profiledOpenFixedPinnedFamilyCode A strategy hwin basis initialCode
        control source)
      (profiledOpenFixedPinnedLeftExpected A strategy hwin basis initialCode
        control source) :=
  FiniteDescriptorFamilyPinnedProvenanceMove.toPinnedMove
    (fun descriptor : ProfiledOpenHiddenDescriptorLeftCarrier A
      (profiledOpenFixedPinnedFamilyCode A strategy hwin basis initialCode
        control source) ↦
      ProfiledOpenHiddenDescriptorLeftRoot A descriptor.1)
    (fun descriptor root ↦
      profiledOpenHiddenDescriptorLeftMonitor A descriptor.1 root)
    (profiledOpenFixedPinnedLeftSemanticAllowed A strategy hwin basis
      initialCode control source)
    (fun descriptor responses ↦
      ProfiledOpenHiddenDescriptorLeftWeakAllowed A descriptor.1 responses)
    (profiledOpenFixedPinnedLeftExpected A strategy hwin basis initialCode
      control source) move

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Arbitrary-node left provenance on the literal fixed controller. -/
theorem ProfiledOpenFixedPinnedLeftProvenanceMove.controllerFor_semantic
    (source : ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis
      (I := I))
    (move : ProfiledOpenFixedPinnedLeftProvenanceMove A strategy hwin basis
      initialCode control source)
    (descriptor : ProfiledOpenHiddenDescriptorLeftCarrier A
      (profiledOpenFixedPinnedFamilyCode A strategy hwin basis initialCode
        control source)) :
    NarrowedTablesAllowed
      (finiteRootFamilyMonitor
        (descriptorRootPinnedMonitor
          (fun descriptor : ProfiledOpenHiddenDescriptorLeftCarrier A
            (profiledOpenFixedPinnedFamilyCode A strategy hwin basis
              initialCode control source) ↦
            ProfiledOpenHiddenDescriptorLeftRoot A descriptor.1)
          (fun descriptor root ↦
            profiledOpenHiddenDescriptorLeftMonitor A descriptor.1 root)
          (profiledOpenFixedPinnedLeftExpected A strategy hwin basis
            initialCode control source) descriptor))
      (profiledOpenFixedPinnedLeftSemanticAllowed A strategy hwin basis
        initialCode control source descriptor)
      ((ProfiledOpenFixedPinnedLeftProvenanceMove.toPinnedMove A strategy hwin
        basis initialCode control source move).controllerFor
          (fun descriptor : ProfiledOpenHiddenDescriptorLeftCarrier A
            (profiledOpenFixedPinnedFamilyCode A strategy hwin basis
              initialCode control source) ↦
            ProfiledOpenHiddenDescriptorLeftRoot A descriptor.1)
          (descriptorRootPinnedMonitor
            (fun descriptor : ProfiledOpenHiddenDescriptorLeftCarrier A
              (profiledOpenFixedPinnedFamilyCode A strategy hwin basis
                initialCode control source) ↦
              ProfiledOpenHiddenDescriptorLeftRoot A descriptor.1)
            (fun descriptor root ↦
              profiledOpenHiddenDescriptorLeftMonitor A descriptor.1 root)
            (profiledOpenFixedPinnedLeftExpected A strategy hwin basis
              initialCode control source))
          (fun descriptor responses ↦
            ProfiledOpenHiddenDescriptorLeftWeakAllowed A descriptor.1
              responses)
          descriptor |>.labeledTree) := by
  exact FiniteDescriptorFamilyPinnedProvenanceMove.controllerFor_strongAllowed
    (fun descriptor : ProfiledOpenHiddenDescriptorLeftCarrier A
      (profiledOpenFixedPinnedFamilyCode A strategy hwin basis initialCode
        control source) ↦ ProfiledOpenHiddenDescriptorLeftRoot A descriptor.1)
    (fun descriptor root ↦
      profiledOpenHiddenDescriptorLeftMonitor A descriptor.1 root)
    (profiledOpenFixedPinnedLeftSemanticAllowed A strategy hwin basis
      initialCode control source)
    (fun descriptor responses ↦
      ProfiledOpenHiddenDescriptorLeftWeakAllowed A descriptor.1 responses)
    (profiledOpenFixedPinnedLeftExpected A strategy hwin basis initialCode
      control source) move descriptor

/-! ## Right-only canonical provenance -/

variable (optionalControl :
  ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin basis (I := I) →
    (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode).State)

/-- The right-only strong law uses the same semantic receiver as the source
lane, transported only along the proof-side canonical-root equality. -/
def profiledOpenOptionalRightOnlySemanticAllowed
    (source : ProfiledOpenIndexedRightOnlyFreshSemanticPoint A strategy hwin
      basis (I := I))
    (descriptor : ProfiledOpenHiddenDescriptorRightCarrier A
      (profiledOpenOptionalRightOnlyFamilyCode A strategy hwin basis
        initialCode optionalControl source))
    (responses :
      ((ProfiledOpenHiddenDescriptorRightRoot A descriptor.1 × In₂) ×
        In₁) → ProfiledOpenRightClassifiedOutput A) : Prop :=
  let point := profiledOpenOptionalRightOnlyPoint A strategy hwin basis
    initialCode optionalControl source descriptor
  let table := ((point.lane.realization.coherentTable A).table
    |>.toClassified A point.lane.source)
  let hmove := profiledOpenOptionalRightOnlyPoint_moveIdentity A strategy hwin
    basis initialCode optionalControl source descriptor
  ProfiledOpenRightSemanticTableAllowed A point.lane.source strategy hwin
    point.lane.realization.entry basis (fun input ↦
      responses
        ((profiledOpenHiddenDescriptorRightRootOfEq A descriptor.1
            point.lane.source table hmove input.1.1,
          input.1.2), input.2))

omit [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledOpenOptionalRightOnlySemanticAllowed_implies_weak
    (source : ProfiledOpenIndexedRightOnlyFreshSemanticPoint A strategy hwin
      basis (I := I))
    (descriptor : ProfiledOpenHiddenDescriptorRightCarrier A
      (profiledOpenOptionalRightOnlyFamilyCode A strategy hwin basis
        initialCode optionalControl source))
    (responses :
      ((ProfiledOpenHiddenDescriptorRightRoot A descriptor.1 × In₂) ×
        In₁) → ProfiledOpenRightClassifiedOutput A)
    (hsemantic : profiledOpenOptionalRightOnlySemanticAllowed A strategy hwin
      basis initialCode optionalControl source descriptor responses) :
    ProfiledOpenHiddenDescriptorRightWeakAllowed A descriptor.1 responses := by
  let point := profiledOpenOptionalRightOnlyPoint A strategy hwin basis
    initialCode optionalControl source descriptor
  let table := ((point.lane.realization.coherentTable A).table
    |>.toClassified A point.lane.source)
  let hmove := profiledOpenOptionalRightOnlyPoint_moveIdentity A strategy hwin
    basis initialCode optionalControl source descriptor
  apply profiledOpenHiddenDescriptorRightWeakAllowed_ofEq A descriptor.1
    point.lane.source table hmove
  rcases hsemantic with ⟨past, hpast⟩
  rw [hpast]
  exact profiledOpenRightSemanticClassifiedFamilyReceiver_allowed A
    point.lane.source strategy hwin point.lane.realization.entry
    point.lane.realization.minimum basis past

noncomputable abbrev ProfiledOpenOptionalRightOnlyPinnedProvenanceMove
    (source : ProfiledOpenIndexedRightOnlyFreshSemanticPoint A strategy hwin
      basis (I := I)) :=
  FiniteDescriptorFamilyPinnedProvenanceMove
    (fun descriptor : ProfiledOpenHiddenDescriptorRightCarrier A
      (profiledOpenOptionalRightOnlyFamilyCode A strategy hwin basis
        initialCode optionalControl source) ↦
      ProfiledOpenHiddenDescriptorRightRoot A descriptor.1)
    (fun descriptor root ↦
      profiledOpenHiddenDescriptorRightMonitor A descriptor.1 root)
    (profiledOpenOptionalRightOnlySemanticAllowed A strategy hwin basis
      initialCode optionalControl source)
    (fun descriptor responses ↦
      ProfiledOpenHiddenDescriptorRightWeakAllowed A descriptor.1 responses)
    (profiledOpenOptionalRightOnlyExpected A strategy hwin basis initialCode
      optionalControl source)

/-- One strong extraction on the literal canonical right-only carrier. -/
noncomputable def profiledOpenOptionalRightOnlyPinnedProvenanceMoveOfWinning
    (source : ProfiledOpenIndexedRightOnlyFreshSemanticPoint A strategy hwin
      basis (I := I)) :
    ProfiledOpenOptionalRightOnlyPinnedProvenanceMove A strategy hwin basis
      initialCode optionalControl source := by
  classical
  let family := profiledOpenOptionalRightOnlyFamilyCode A strategy hwin basis
    initialCode optionalControl source
  let Root := fun descriptor : ProfiledOpenHiddenDescriptorRightCarrier A
      family ↦ ProfiledOpenHiddenDescriptorRightRoot A descriptor.1
  let baseM : ∀ descriptor, Root descriptor →
      BlockRecordMonitor In₂ In₁ (ProfiledOpenRightClassifiedOutput A) Out₁ :=
    fun descriptor root ↦
      profiledOpenHiddenDescriptorRightMonitor A descriptor.1 root
  let expected := profiledOpenOptionalRightOnlyExpected A strategy hwin basis
    initialCode optionalControl source
  let Strong := profiledOpenOptionalRightOnlySemanticAllowed A strategy hwin
    basis initialCode optionalControl source
  let Weak : ∀ descriptor,
      (((Root descriptor × In₂) × In₁) →
        ProfiledOpenRightClassifiedOutput A) → Prop :=
    fun descriptor responses ↦
      ProfiledOpenHiddenDescriptorRightWeakAllowed A descriptor.1 responses
  let receiver := profiledOpenOptionalRightOnlyReceiver A strategy hwin basis
    initialCode optionalControl source
  let sender := profiledOpenOptionalRightOnlySender A strategy hwin basis source
  letI : Inhabited (Sigma Root) :=
    ⟨profiledOpenOptionalRightOnlyDefaultMember A strategy hwin basis
      initialCode optionalControl source⟩
  letI : Inhabited (ProfiledOpenRightClassifiedOutput A) :=
    ⟨profiledOpenOptionalDefaultRightClassifiedOutput A strategy hwin basis⟩
  have hstrong : ∀ past,
      DescriptorRootUnionAllowed Root Strong
        (finiteRootFamilyReceiver receiver past) := by
    intro past descriptor
    let point := profiledOpenOptionalRightOnlyPoint A strategy hwin basis
      initialCode optionalControl source descriptor
    let table := ((point.lane.realization.coherentTable A).table
      |>.toClassified A point.lane.source)
    let hmove := profiledOpenOptionalRightOnlyPoint_moveIdentity A strategy hwin
      basis initialCode optionalControl source descriptor
    refine ⟨past.map (fun old ↦
      ((point.lane.realization.pivot, old.1.2), old.2)), ?_⟩
    funext input
    simp [Strong, profiledOpenOptionalRightOnlySemanticAllowed,
      profiledOpenRightSemanticClassifiedFamilyReceiver, receiver,
      profiledOpenOptionalRightOnlyReceiver,
      profiledOpenOptionalRightOnlyRoot, finiteRootFamilyReceiver,
      List.map_map, Function.comp_def, point, table, hmove,
      profiledOpenHiddenDescriptorRightRootToEq_rootOfEq]
  apply finiteDescriptorFamilyPinnedProvenanceMoveOfStrategies Root baseM
    Strong Weak expected
    (fun descriptor responses hsemantic ↦
      profiledOpenOptionalRightOnlySemanticAllowed_implies_weak A strategy hwin
        basis initialCode optionalControl source descriptor responses hsemantic)
    (finiteRootFamilyReceiver receiver []) (hstrong []) receiver sender
  · exact profiledOpenOptionalRightOnly_memberWins A strategy hwin basis
      initialCode optionalControl source
  · intro member input
    rfl
  · exact hstrong

noncomputable def
    ProfiledOpenOptionalRightOnlyPinnedProvenanceMove.toPinnedMove
    (source : ProfiledOpenIndexedRightOnlyFreshSemanticPoint A strategy hwin
      basis (I := I))
    (move : ProfiledOpenOptionalRightOnlyPinnedProvenanceMove A strategy hwin
      basis initialCode optionalControl source) :
    ProfiledOpenHiddenDescriptorRightPinnedFamilyMove A
      (profiledOpenOptionalRightOnlyFamilyCode A strategy hwin basis
        initialCode optionalControl source)
      (profiledOpenOptionalRightOnlyExpected A strategy hwin basis initialCode
        optionalControl source) :=
  FiniteDescriptorFamilyPinnedProvenanceMove.toPinnedMove
    (fun descriptor : ProfiledOpenHiddenDescriptorRightCarrier A
      (profiledOpenOptionalRightOnlyFamilyCode A strategy hwin basis
        initialCode optionalControl source) ↦
      ProfiledOpenHiddenDescriptorRightRoot A descriptor.1)
    (fun descriptor root ↦
      profiledOpenHiddenDescriptorRightMonitor A descriptor.1 root)
    (profiledOpenOptionalRightOnlySemanticAllowed A strategy hwin basis
      initialCode optionalControl source)
    (fun descriptor responses ↦
      ProfiledOpenHiddenDescriptorRightWeakAllowed A descriptor.1 responses)
    (profiledOpenOptionalRightOnlyExpected A strategy hwin basis initialCode
      optionalControl source) move

omit [Inhabited Out₁] [Inhabited Out₂] in
theorem
    ProfiledOpenOptionalRightOnlyPinnedProvenanceMove.controllerFor_semantic
    (source : ProfiledOpenIndexedRightOnlyFreshSemanticPoint A strategy hwin
      basis (I := I))
    (move : ProfiledOpenOptionalRightOnlyPinnedProvenanceMove A strategy hwin
      basis initialCode optionalControl source)
    (descriptor : ProfiledOpenHiddenDescriptorRightCarrier A
      (profiledOpenOptionalRightOnlyFamilyCode A strategy hwin basis
        initialCode optionalControl source)) :
    NarrowedTablesAllowed
      (finiteRootFamilyMonitor
        (descriptorRootPinnedMonitor
          (fun descriptor : ProfiledOpenHiddenDescriptorRightCarrier A
            (profiledOpenOptionalRightOnlyFamilyCode A strategy hwin basis
              initialCode optionalControl source) ↦
            ProfiledOpenHiddenDescriptorRightRoot A descriptor.1)
          (fun descriptor root ↦
            profiledOpenHiddenDescriptorRightMonitor A descriptor.1 root)
          (profiledOpenOptionalRightOnlyExpected A strategy hwin basis
            initialCode optionalControl source) descriptor))
      (profiledOpenOptionalRightOnlySemanticAllowed A strategy hwin basis
        initialCode optionalControl source descriptor)
      ((move.toPinnedMove A strategy hwin basis initialCode optionalControl
        source).controllerFor
          (fun descriptor : ProfiledOpenHiddenDescriptorRightCarrier A
            (profiledOpenOptionalRightOnlyFamilyCode A strategy hwin basis
              initialCode optionalControl source) ↦
            ProfiledOpenHiddenDescriptorRightRoot A descriptor.1)
          (descriptorRootPinnedMonitor
            (fun descriptor : ProfiledOpenHiddenDescriptorRightCarrier A
              (profiledOpenOptionalRightOnlyFamilyCode A strategy hwin basis
                initialCode optionalControl source) ↦
              ProfiledOpenHiddenDescriptorRightRoot A descriptor.1)
            (fun descriptor root ↦
              profiledOpenHiddenDescriptorRightMonitor A descriptor.1 root)
            (profiledOpenOptionalRightOnlyExpected A strategy hwin basis
              initialCode optionalControl source))
          (fun descriptor responses ↦
            ProfiledOpenHiddenDescriptorRightWeakAllowed A descriptor.1
              responses)
          descriptor |>.labeledTree) := by
  exact FiniteDescriptorFamilyPinnedProvenanceMove.controllerFor_strongAllowed
    (fun descriptor : ProfiledOpenHiddenDescriptorRightCarrier A
      (profiledOpenOptionalRightOnlyFamilyCode A strategy hwin basis
        initialCode optionalControl source) ↦
      ProfiledOpenHiddenDescriptorRightRoot A descriptor.1)
    (fun descriptor root ↦
      profiledOpenHiddenDescriptorRightMonitor A descriptor.1 root)
    (profiledOpenOptionalRightOnlySemanticAllowed A strategy hwin basis
      initialCode optionalControl source)
    (fun descriptor responses ↦
      ProfiledOpenHiddenDescriptorRightWeakAllowed A descriptor.1 responses)
    (profiledOpenOptionalRightOnlyExpected A strategy hwin basis initialCode
      optionalControl source) move descriptor

/-! ## Left-only canonical provenance -/

/-- The left-only strong law uses the same semantic receiver as the source
lane, transported only along the proof-side canonical-root equality. -/
def profiledOpenOptionalLeftOnlySemanticAllowed
    (source : ProfiledOpenIndexedLeftOnlyFreshSemanticPoint A strategy hwin
      basis (I := I))
    (descriptor : ProfiledOpenHiddenDescriptorLeftCarrier A
      (profiledOpenOptionalLeftOnlyFamilyCode A strategy hwin basis
        initialCode optionalControl source))
    (responses :
      ((ProfiledOpenHiddenDescriptorLeftRoot A descriptor.1 × In₁) ×
        In₂) → ProfiledOpenLeftClassifiedOutput A) : Prop :=
  let point := profiledOpenOptionalLeftOnlyPoint A strategy hwin basis
    initialCode optionalControl source descriptor
  let table := ((point.lane.realization.coherentTable A).table
    |>.toClassified A point.lane.source)
  let hmove := profiledOpenOptionalLeftOnlyPoint_moveIdentity A strategy hwin
    basis initialCode optionalControl source descriptor
  ProfiledOpenLeftSemanticTableAllowed A point.lane.source strategy hwin
    point.lane.realization.entry basis (fun input ↦
      responses
        ((profiledOpenHiddenDescriptorLeftRootOfEq A descriptor.1
            point.lane.source table hmove input.1.1,
          input.1.2), input.2))

omit [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledOpenOptionalLeftOnlySemanticAllowed_implies_weak
    (source : ProfiledOpenIndexedLeftOnlyFreshSemanticPoint A strategy hwin
      basis (I := I))
    (descriptor : ProfiledOpenHiddenDescriptorLeftCarrier A
      (profiledOpenOptionalLeftOnlyFamilyCode A strategy hwin basis
        initialCode optionalControl source))
    (responses :
      ((ProfiledOpenHiddenDescriptorLeftRoot A descriptor.1 × In₁) ×
        In₂) → ProfiledOpenLeftClassifiedOutput A)
    (hsemantic : profiledOpenOptionalLeftOnlySemanticAllowed A strategy hwin
      basis initialCode optionalControl source descriptor responses) :
    ProfiledOpenHiddenDescriptorLeftWeakAllowed A descriptor.1 responses := by
  let point := profiledOpenOptionalLeftOnlyPoint A strategy hwin basis
    initialCode optionalControl source descriptor
  let table := ((point.lane.realization.coherentTable A).table
    |>.toClassified A point.lane.source)
  let hmove := profiledOpenOptionalLeftOnlyPoint_moveIdentity A strategy hwin
    basis initialCode optionalControl source descriptor
  apply profiledOpenHiddenDescriptorLeftWeakAllowed_ofEq A descriptor.1
    point.lane.source table hmove
  rcases hsemantic with ⟨past, hpast⟩
  rw [hpast]
  exact profiledOpenLeftSemanticClassifiedFamilyReceiver_allowed A
    point.lane.source strategy hwin point.lane.realization.entry
    point.lane.realization.minimum basis past

noncomputable abbrev ProfiledOpenOptionalLeftOnlyPinnedProvenanceMove
    (source : ProfiledOpenIndexedLeftOnlyFreshSemanticPoint A strategy hwin
      basis (I := I)) :=
  FiniteDescriptorFamilyPinnedProvenanceMove
    (fun descriptor : ProfiledOpenHiddenDescriptorLeftCarrier A
      (profiledOpenOptionalLeftOnlyFamilyCode A strategy hwin basis
        initialCode optionalControl source) ↦
      ProfiledOpenHiddenDescriptorLeftRoot A descriptor.1)
    (fun descriptor root ↦
      profiledOpenHiddenDescriptorLeftMonitor A descriptor.1 root)
    (profiledOpenOptionalLeftOnlySemanticAllowed A strategy hwin basis
      initialCode optionalControl source)
    (fun descriptor responses ↦
      ProfiledOpenHiddenDescriptorLeftWeakAllowed A descriptor.1 responses)
    (profiledOpenOptionalLeftOnlyExpected A strategy hwin basis initialCode
      optionalControl source)

/-- One strong extraction on the literal canonical left-only carrier. -/
noncomputable def profiledOpenOptionalLeftOnlyPinnedProvenanceMoveOfWinning
    (source : ProfiledOpenIndexedLeftOnlyFreshSemanticPoint A strategy hwin
      basis (I := I)) :
    ProfiledOpenOptionalLeftOnlyPinnedProvenanceMove A strategy hwin basis
      initialCode optionalControl source := by
  classical
  let family := profiledOpenOptionalLeftOnlyFamilyCode A strategy hwin basis
    initialCode optionalControl source
  let Root := fun descriptor : ProfiledOpenHiddenDescriptorLeftCarrier A
      family ↦ ProfiledOpenHiddenDescriptorLeftRoot A descriptor.1
  let baseM : ∀ descriptor, Root descriptor →
      BlockRecordMonitor In₁ In₂ (ProfiledOpenLeftClassifiedOutput A) Out₂ :=
    fun descriptor root ↦
      profiledOpenHiddenDescriptorLeftMonitor A descriptor.1 root
  let expected := profiledOpenOptionalLeftOnlyExpected A strategy hwin basis
    initialCode optionalControl source
  let Strong := profiledOpenOptionalLeftOnlySemanticAllowed A strategy hwin
    basis initialCode optionalControl source
  let Weak : ∀ descriptor,
      (((Root descriptor × In₁) × In₂) →
        ProfiledOpenLeftClassifiedOutput A) → Prop :=
    fun descriptor responses ↦
      ProfiledOpenHiddenDescriptorLeftWeakAllowed A descriptor.1 responses
  let receiver := profiledOpenOptionalLeftOnlyReceiver A strategy hwin basis
    initialCode optionalControl source
  let sender := profiledOpenOptionalLeftOnlySender A strategy hwin basis source
  letI : Inhabited (Sigma Root) :=
    ⟨profiledOpenOptionalLeftOnlyDefaultMember A strategy hwin basis
      initialCode optionalControl source⟩
  letI : Inhabited (ProfiledOpenLeftClassifiedOutput A) :=
    ⟨profiledOpenOptionalDefaultLeftClassifiedOutput A strategy hwin basis⟩
  have hstrong : ∀ past,
      DescriptorRootUnionAllowed Root Strong
        (finiteRootFamilyReceiver receiver past) := by
    intro past descriptor
    let point := profiledOpenOptionalLeftOnlyPoint A strategy hwin basis
      initialCode optionalControl source descriptor
    let table := ((point.lane.realization.coherentTable A).table
      |>.toClassified A point.lane.source)
    let hmove := profiledOpenOptionalLeftOnlyPoint_moveIdentity A strategy hwin
      basis initialCode optionalControl source descriptor
    refine ⟨past.map (fun old ↦
      ((point.lane.realization.pivot, old.1.2), old.2)), ?_⟩
    funext input
    simp [Strong, profiledOpenOptionalLeftOnlySemanticAllowed,
      profiledOpenLeftSemanticClassifiedFamilyReceiver, receiver,
      profiledOpenOptionalLeftOnlyReceiver,
      profiledOpenOptionalLeftOnlyRoot, finiteRootFamilyReceiver,
      List.map_map, Function.comp_def, point, table, hmove,
      profiledOpenHiddenDescriptorLeftRootToEq_rootOfEq]
  apply finiteDescriptorFamilyPinnedProvenanceMoveOfStrategies Root baseM
    Strong Weak expected
    (fun descriptor responses hsemantic ↦
      profiledOpenOptionalLeftOnlySemanticAllowed_implies_weak A strategy hwin
        basis initialCode optionalControl source descriptor responses hsemantic)
    (finiteRootFamilyReceiver receiver []) (hstrong []) receiver sender
  · exact profiledOpenOptionalLeftOnly_memberWins A strategy hwin basis
      initialCode optionalControl source
  · intro member input
    rfl
  · exact hstrong

noncomputable def
    ProfiledOpenOptionalLeftOnlyPinnedProvenanceMove.toPinnedMove
    (source : ProfiledOpenIndexedLeftOnlyFreshSemanticPoint A strategy hwin
      basis (I := I))
    (move : ProfiledOpenOptionalLeftOnlyPinnedProvenanceMove A strategy hwin
      basis initialCode optionalControl source) :
    ProfiledOpenHiddenDescriptorLeftPinnedFamilyMove A
      (profiledOpenOptionalLeftOnlyFamilyCode A strategy hwin basis
        initialCode optionalControl source)
      (profiledOpenOptionalLeftOnlyExpected A strategy hwin basis initialCode
        optionalControl source) :=
  FiniteDescriptorFamilyPinnedProvenanceMove.toPinnedMove
    (fun descriptor : ProfiledOpenHiddenDescriptorLeftCarrier A
      (profiledOpenOptionalLeftOnlyFamilyCode A strategy hwin basis
        initialCode optionalControl source) ↦
      ProfiledOpenHiddenDescriptorLeftRoot A descriptor.1)
    (fun descriptor root ↦
      profiledOpenHiddenDescriptorLeftMonitor A descriptor.1 root)
    (profiledOpenOptionalLeftOnlySemanticAllowed A strategy hwin basis
      initialCode optionalControl source)
    (fun descriptor responses ↦
      ProfiledOpenHiddenDescriptorLeftWeakAllowed A descriptor.1 responses)
    (profiledOpenOptionalLeftOnlyExpected A strategy hwin basis initialCode
      optionalControl source) move

omit [Inhabited Out₁] [Inhabited Out₂] in
theorem
    ProfiledOpenOptionalLeftOnlyPinnedProvenanceMove.controllerFor_semantic
    (source : ProfiledOpenIndexedLeftOnlyFreshSemanticPoint A strategy hwin
      basis (I := I))
    (move : ProfiledOpenOptionalLeftOnlyPinnedProvenanceMove A strategy hwin
      basis initialCode optionalControl source)
    (descriptor : ProfiledOpenHiddenDescriptorLeftCarrier A
      (profiledOpenOptionalLeftOnlyFamilyCode A strategy hwin basis
        initialCode optionalControl source)) :
    NarrowedTablesAllowed
      (finiteRootFamilyMonitor
        (descriptorRootPinnedMonitor
          (fun descriptor : ProfiledOpenHiddenDescriptorLeftCarrier A
            (profiledOpenOptionalLeftOnlyFamilyCode A strategy hwin basis
              initialCode optionalControl source) ↦
            ProfiledOpenHiddenDescriptorLeftRoot A descriptor.1)
          (fun descriptor root ↦
            profiledOpenHiddenDescriptorLeftMonitor A descriptor.1 root)
          (profiledOpenOptionalLeftOnlyExpected A strategy hwin basis
            initialCode optionalControl source) descriptor))
      (profiledOpenOptionalLeftOnlySemanticAllowed A strategy hwin basis
        initialCode optionalControl source descriptor)
      ((move.toPinnedMove A strategy hwin basis initialCode optionalControl
        source).controllerFor
          (fun descriptor : ProfiledOpenHiddenDescriptorLeftCarrier A
            (profiledOpenOptionalLeftOnlyFamilyCode A strategy hwin basis
              initialCode optionalControl source) ↦
            ProfiledOpenHiddenDescriptorLeftRoot A descriptor.1)
          (descriptorRootPinnedMonitor
            (fun descriptor : ProfiledOpenHiddenDescriptorLeftCarrier A
              (profiledOpenOptionalLeftOnlyFamilyCode A strategy hwin basis
                initialCode optionalControl source) ↦
              ProfiledOpenHiddenDescriptorLeftRoot A descriptor.1)
            (fun descriptor root ↦
              profiledOpenHiddenDescriptorLeftMonitor A descriptor.1 root)
            (profiledOpenOptionalLeftOnlyExpected A strategy hwin basis
              initialCode optionalControl source))
          (fun descriptor responses ↦
            ProfiledOpenHiddenDescriptorLeftWeakAllowed A descriptor.1
              responses)
          descriptor |>.labeledTree) := by
  exact FiniteDescriptorFamilyPinnedProvenanceMove.controllerFor_strongAllowed
    (fun descriptor : ProfiledOpenHiddenDescriptorLeftCarrier A
      (profiledOpenOptionalLeftOnlyFamilyCode A strategy hwin basis
        initialCode optionalControl source) ↦
      ProfiledOpenHiddenDescriptorLeftRoot A descriptor.1)
    (fun descriptor root ↦
      profiledOpenHiddenDescriptorLeftMonitor A descriptor.1 root)
    (profiledOpenOptionalLeftOnlySemanticAllowed A strategy hwin basis
      initialCode optionalControl source)
    (fun descriptor responses ↦
      ProfiledOpenHiddenDescriptorLeftWeakAllowed A descriptor.1 responses)
    (profiledOpenOptionalLeftOnlyExpected A strategy hwin basis initialCode
      optionalControl source) move descriptor

/-! ## Total optional-lane projection -/

/-- Right-only fixed move-at built by weakening the one canonical strong
controller. -/
noncomputable def profiledOpenOptionalRightOnlyPinnedSemanticMoveAtOfWinning
    (source : ProfiledOpenIndexedRightOnlyFreshSemanticPoint A strategy hwin
      basis (I := I)) :
    ProfiledOpenHiddenDescriptorPairedPinnedFamilyMoveAt A
      (profiledOpenOptionalRightOnlyFamilyCode A strategy hwin basis
        initialCode optionalControl source) :=
  ⟨profiledOpenOptionalRightOnlyExpected A strategy hwin basis initialCode
      optionalControl source,
    profiledOpenOptionalRightOnlyLeftExpected A strategy hwin basis
      initialCode optionalControl source,
    (profiledOpenOptionalRightOnlyPinnedProvenanceMoveOfWinning A strategy hwin
      basis initialCode optionalControl source).toPinnedMove A strategy hwin
        basis initialCode optionalControl source,
    profiledOpenOptionalRightOnlyEmptyLeftMove A strategy hwin basis
      initialCode optionalControl source⟩

/-- Left-only mirror. -/
noncomputable def profiledOpenOptionalLeftOnlyPinnedSemanticMoveAtOfWinning
    (source : ProfiledOpenIndexedLeftOnlyFreshSemanticPoint A strategy hwin
      basis (I := I)) :
    ProfiledOpenHiddenDescriptorPairedPinnedFamilyMoveAt A
      (profiledOpenOptionalLeftOnlyFamilyCode A strategy hwin basis
        initialCode optionalControl source) :=
  ⟨profiledOpenOptionalLeftOnlyRightExpected A strategy hwin basis
      initialCode optionalControl source,
    profiledOpenOptionalLeftOnlyExpected A strategy hwin basis initialCode
      optionalControl source,
    profiledOpenOptionalLeftOnlyEmptyRightMove A strategy hwin basis
      initialCode optionalControl source,
    (profiledOpenOptionalLeftOnlyPinnedProvenanceMoveOfWinning A strategy hwin
      basis initialCode optionalControl source).toPinnedMove A strategy hwin
        basis initialCode optionalControl source⟩

/-- Two-live move-at, with both weak projections taken from their respective
literal strong controllers. -/
noncomputable def profiledOpenFixedPinnedPairedProvenanceMoveAtOfWinning
    (source : ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis
      (I := I)) :
    ProfiledOpenHiddenDescriptorPairedPinnedFamilyMoveAt A
      (profiledOpenFixedPinnedFamilyCode A strategy hwin basis initialCode
        control source) :=
  ⟨profiledOpenFixedPinnedRightExpected A strategy hwin basis initialCode
      control source,
    profiledOpenFixedPinnedLeftExpected A strategy hwin basis initialCode
      control source,
    (profiledOpenFixedPinnedRightProvenanceMoveOfWinning A strategy hwin basis
      initialCode control source).toPinnedMove A strategy hwin basis initialCode
        control source,
    (profiledOpenFixedPinnedLeftProvenanceMoveOfWinning A strategy hwin basis
      initialCode control source).toPinnedMove A strategy hwin basis initialCode
        control source⟩

@[simp] theorem
    profiledOpenOptionalRightOnlyPinnedSemanticMoveAtOfWinning_rightMove
    (source : ProfiledOpenIndexedRightOnlyFreshSemanticPoint A strategy hwin
      basis (I := I)) :
    (profiledOpenOptionalRightOnlyPinnedSemanticMoveAtOfWinning A strategy
      hwin basis initialCode optionalControl source).2.2.1 =
      (profiledOpenOptionalRightOnlyPinnedProvenanceMoveOfWinning A strategy
        hwin basis initialCode optionalControl source).toPinnedMove A strategy
          hwin basis initialCode optionalControl source :=
  rfl

@[simp] theorem
    profiledOpenOptionalLeftOnlyPinnedSemanticMoveAtOfWinning_leftMove
    (source : ProfiledOpenIndexedLeftOnlyFreshSemanticPoint A strategy hwin
      basis (I := I)) :
    (profiledOpenOptionalLeftOnlyPinnedSemanticMoveAtOfWinning A strategy
      hwin basis initialCode optionalControl source).2.2.2 =
      (profiledOpenOptionalLeftOnlyPinnedProvenanceMoveOfWinning A strategy
        hwin basis initialCode optionalControl source).toPinnedMove A strategy
          hwin basis initialCode optionalControl source :=
  rfl

@[simp] theorem
    profiledOpenFixedPinnedPairedProvenanceMoveAtOfWinning_rightMove
    (source : ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis
      (I := I)) :
    (profiledOpenFixedPinnedPairedProvenanceMoveAtOfWinning A strategy hwin
      basis initialCode control source).2.2.1 =
      (profiledOpenFixedPinnedRightProvenanceMoveOfWinning A strategy hwin
        basis initialCode control source).toPinnedMove A strategy hwin basis
          initialCode control source :=
  rfl

@[simp] theorem
    profiledOpenFixedPinnedPairedProvenanceMoveAtOfWinning_leftMove
    (source : ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis
      (I := I)) :
    (profiledOpenFixedPinnedPairedProvenanceMoveAtOfWinning A strategy hwin
      basis initialCode control source).2.2.2 =
      (profiledOpenFixedPinnedLeftProvenanceMoveOfWinning A strategy hwin
        basis initialCode control source).toPinnedMove A strategy hwin basis
          initialCode control source :=
  rfl

/-- Total fixed-alphabet dispatcher.  Its case split is proof-side only; no
lane, orientation, or leader flag enters either controller. -/
noncomputable def profiledOpenOptionalFixedPinnedSemanticMoveOfBank
    (point : ProfiledOpenIndexedOptionalFreshSemanticPoint A strategy hwin
      basis (I := I))
    (bank : ProfiledOpenIndexedOptionalSourceFibreProvenanceBank A strategy
      hwin basis
      (profiledOpenOptionalFixedSemanticDescriptor A strategy hwin basis
        initialCode optionalControl) point) :
    ProfiledOpenHiddenDescriptorPairedPinnedFamilyMove A initialCode :=
  match bank with
  | .sink _ _ =>
      ⟨profiledOpenOptionalSinkFamilyCode A (I := I) initialCode,
        profiledOpenOptionalSinkPinnedMoveAt A strategy hwin basis
          initialCode⟩
  | .rightOnly lane hright hleft _ =>
      let source := point.toRightOnly A strategy hwin basis lane hright hleft
      ⟨profiledOpenOptionalRightOnlyFamilyCode A strategy hwin basis
          initialCode optionalControl source,
        profiledOpenOptionalRightOnlyPinnedSemanticMoveAtOfWinning A strategy
          hwin basis initialCode optionalControl source⟩
  | .leftOnly lane hright hleft _ =>
      let source := point.toLeftOnly A strategy hwin basis lane hright hleft
      ⟨profiledOpenOptionalLeftOnlyFamilyCode A strategy hwin basis
          initialCode optionalControl source,
        profiledOpenOptionalLeftOnlyPinnedSemanticMoveAtOfWinning A strategy
          hwin basis initialCode optionalControl source⟩
  | .both rightLane leftLane hright hleft _ =>
      let source := point.toLiveFresh A strategy hwin basis rightLane leftLane
        hright hleft
      let liveControl := fun live ↦ optionalControl live.state
      ⟨profiledOpenFixedPinnedFamilyCode A strategy hwin basis initialCode
          liveControl source,
        profiledOpenFixedPinnedPairedProvenanceMoveAtOfWinning A strategy hwin
          basis initialCode liveControl source⟩

/-- The strong dispatcher has exactly the same four-way public-family shape
as the weak dispatcher, now proved directly on the literal provenance bank.
No equality between the two independently extracted controller coordinates
is used. -/
theorem profiledOpenOptionalFixedPinnedSemanticMoveOfBank_shape
    (point : ProfiledOpenIndexedOptionalFreshSemanticPoint A strategy hwin
      basis (I := I))
    (bank : ProfiledOpenIndexedOptionalSourceFibreProvenanceBank A strategy
      hwin basis
      (profiledOpenOptionalFixedSemanticDescriptor A strategy hwin basis
        initialCode optionalControl) point) :
    let move := profiledOpenOptionalFixedPinnedSemanticMoveOfBank A strategy
      hwin basis initialCode optionalControl point bank
    let descriptor := profiledOpenOptionalFixedSemanticDescriptor A strategy
      hwin basis initialCode optionalControl point.state
    move.1 = (∅, ∅) ∨
      (descriptor ∈ move.1.1 ∧ move.1.2 = ∅) ∨
      (move.1.1 = ∅ ∧ descriptor ∈ move.1.2) ∨
      (descriptor ∈ move.1.1 ∧ descriptor ∈ move.1.2) := by
  classical
  cases bank with
  | sink hright hleft =>
      exact Or.inl rfl
  | rightOnly lane hright hleft bankMove =>
      apply Or.inr
      apply Or.inl
      exact profiledOpenRightOnlyDescriptor_mem_family A strategy hwin basis
        (profiledOpenOptionalFixedSemanticDescriptor A strategy hwin basis
          initialCode optionalControl)
        (point.toRightOnly A strategy hwin basis lane hright hleft)
  | leftOnly lane hright hleft bankMove =>
      apply Or.inr
      apply Or.inr
      apply Or.inl
      exact profiledOpenLeftOnlyDescriptor_mem_family A strategy hwin basis
        (profiledOpenOptionalFixedSemanticDescriptor A strategy hwin basis
          initialCode optionalControl)
        (point.toLeftOnly A strategy hwin basis lane hright hleft)
  | both rightLane leftLane hright hleft bankMove =>
      apply Or.inr
      apply Or.inr
      apply Or.inr
      let source := point.toLiveFresh A strategy hwin basis rightLane leftLane
        hright hleft
      exact profiledOpenSourceFibreCurrent_mem_both A strategy hwin basis
        (profiledOpenFixedPinnedSemanticDescriptor A strategy hwin basis
          initialCode (fun live ↦ optionalControl live.state)) source

/-- Winning semantics supplies the total provenance-preserving fixed move. -/
noncomputable def profiledOpenOptionalFixedPinnedSemanticMoveOfWinning
    (point : ProfiledOpenIndexedOptionalFreshSemanticPoint A strategy hwin
      basis (I := I)) :
    ProfiledOpenHiddenDescriptorPairedPinnedFamilyMove A initialCode :=
  profiledOpenOptionalFixedPinnedSemanticMoveOfBank A strategy hwin basis
    initialCode optionalControl point
    (profiledOpenIndexedOptionalSourceFibreProvenanceBankOfWinning A strategy
      hwin basis
      (profiledOpenOptionalFixedSemanticDescriptor A strategy hwin basis
        initialCode optionalControl) point)

end

end DetParityAutomaton

end DistributedSynthesis
