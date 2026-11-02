/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleLiteralPrefixExtra
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCrossLocalCarrier

/-!
# Semantic readback of recurring literal-prefix edge tables

The recurring literal-prefix annotation is selected before the hybrid tree is
rationalized.  This file proves that the first two receiver records read from
each selected finite table are the literal records of the very semantic edge
which selected it.  These are full receiver-output equalities; the physical
record equalities needed by the Tail are immediate projections.

Together with the joint-policy successor theorems, this prevents a mosaic:
the public code, physical sibling annotation, literal-prefix table, and DPA
successor key all come from one semantic source occurrence.
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

/-! ## Joint-policy provenance -/

/-- The recurring literal-prefix update is replace-only: its result depends
on the literal source edge, never on a previously stored table. -/
theorem profiledRawJointHybridLiteralPrefixAnnotationAdvance_current_irrel
    (source : ProfiledRawJointHybridSemanticState A strategy)
    (left right : ProfiledRawJointHybridLiteralPrefixEdgeAnnotation A)
    (direction : ProfiledRawJointHybridDirection
      (In₁ := In₁) (In₂ := In₂)) :
    profiledRawJointHybridLiteralPrefixAnnotationAdvance A strategy hwin
        source left direction =
      profiledRawJointHybridLiteralPrefixAnnotationAdvance A strategy hwin
        source right direction := by
  cases source <;> cases direction <;> rfl

/-- Reachable readback for the concrete recurring payload.  One semantic
source simultaneously explains the bare child code, the physical table, the
literal-prefix table, and the exact successor state of the linked DPA.  The
canonical right-hand payload uses the fixed initial marker only to erase the
irrelevant previous annotation.

This is a same-occurrence theorem, not yet the visible-anchor locality
theorem: it deliberately makes no claim that independently selected hidden
input siblings use one shared heterogeneous table. -/
theorem
    exists_profiledRawJointHybridPhysicalCompatibleLiteralPrefixSuccessorSemantics
    (initial : ProfiledRawJointCommonBaseWorld A strategy)
    (policy :
      ProfiledRawJointHybridPhysicalCompatibleLiteralPrefixRationalPolicy A
        strategy hwin initial)
    (state :
      ProfiledRawJointHybridPhysicalCompatibleLiteralPrefixPolicyState A
        strategy hwin initial)
    (hreachable :
      ProfiledRawJointHybridPhysicalCompatibleLiteralPrefixReachable A
        strategy hwin initial policy state) :
    ∃ move : SourceFreeBeliefParentLinkedMove
        (Direction := ProfiledRawJointHybridDirection
          (In₁ := In₁) (In₂ := In₂))
        (Move := ProfiledRawJointHybridMove A)
        (Annotation :=
          ProfiledRawJointHybridPhysicalCompatibleExtraAnnotation A
            (ProfiledRawJointHybridLiteralPrefixEdgeAnnotation A)),
      ∃ source : ProfiledRawJointHybridSemanticState A strategy,
        source.code A = state.1.1 ∧
          source.move A = move.1 ∧
          ProfiledRawJointHybridPhysicalCurrentCompatible A strategy source
            state.1.2.1 ∧
          ∀ direction : ProfiledRawJointHybridDirection
              (In₁ := In₁) (In₂ := In₂),
            let childCode := sourceFreeBeliefParentLinkedNext
              (profiledRawJointHybridNext A) state.1 move direction
            let target := policy.successor state childCode
            target.1.1 = (source.step A direction).code A ∧
              target.1.2.1 =
                profiledRawJointHybridPhysicalAnnotationAdvance A strategy
                  hwin source state.1.2.1 direction ∧
              target.1.2.2 =
                profiledRawJointHybridLiteralPrefixAnnotationAdvance A
                  strategy hwin source
                    (profiledRawJointHybridInitialLiteralPrefixAnnotation A)
                      direction ∧
              target.2 =
                (sourceFreeBeliefParentLinkedCodeParityDPA
                  (Annotation :=
                    ProfiledRawJointHybridPhysicalCompatibleExtraAnnotation A
                      (ProfiledRawJointHybridLiteralPrefixEdgeAnnotation A))
                  (profiledRawJointHybridCodeParityDPA A
                    (.common ((profiledRawJointCommonWorldFamily A initial
                      ).incidenceCode A)))).step state.2 childCode := by
  rcases
      exists_profiledRawJointHybridPhysicalCompatibleExtraSemanticSource A
        strategy hwin initial
          (profiledRawJointHybridInitialLiteralPrefixAnnotation A)
          (profiledRawJointHybridLiteralPrefixAnnotationAdvance A strategy
            hwin) policy state hreachable with
    ⟨move, source, hsourceCode, hsourceMove, hcompatible, hchildren,
      hsuccessor⟩
  refine ⟨move, source, hsourceCode, hsourceMove, hcompatible, ?_⟩
  intro direction
  dsimp only
  rw [hsuccessor direction]
  have hchild := (hchildren direction).symm
  constructor
  · change profiledRawJointHybridNext A state.1.1 move.1 direction =
      (source.step A direction).code A
    rw [← hsourceCode, ← hsourceMove]
    exact (source.step_code A direction).symm
  · constructor
    · exact congrArg (fun annotation ↦ annotation.1) hchild
    · constructor
      · have hextra := congrArg (fun annotation ↦ annotation.2) hchild
        change (move.2 direction).2 = _
        calc
          (move.2 direction).2 =
              profiledRawJointHybridLiteralPrefixAnnotationAdvance A strategy
                hwin source state.1.2.2 direction := by
            exact hextra
          _ = profiledRawJointHybridLiteralPrefixAnnotationAdvance A strategy
                hwin source
                  (profiledRawJointHybridInitialLiteralPrefixAnnotation A)
                    direction :=
            profiledRawJointHybridLiteralPrefixAnnotationAdvance_current_irrel
              A strategy hwin source _ _ direction
      · rfl

/-! ## Descriptor agreement with the physical annotation -/

/-- The guarded prefix table and the unguarded physical table extracted from
the same right semantic member have literally the same finite base
descriptor.  Their rationalized tables need not, and are not claimed to, be
equal. -/
@[simp] theorem profiledRawJointRightLiteralPrefixMoveOf_descriptor
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcOnePairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).right () =
      some semanticMember)
    (anchor : Bool) :
    ((profiledRawJointRightLiteralPrefixMoveOf A strategy hwin family direction
        semanticMember hmember).1.descriptor anchor).base =
      (profiledRawJointRightPhysicalSiblingMoveOf A hwin family direction
        semanticMember hmember).1 := by
  rfl

/-- Left mirror of descriptor agreement. -/
@[simp] theorem profiledRawJointLeftLiteralPrefixMoveOf_descriptor
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcTwoPairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).left () =
      some semanticMember)
    (anchor : Bool) :
    ((profiledRawJointLeftLiteralPrefixMoveOf A strategy hwin family direction
        semanticMember hmember).1.descriptor anchor).base =
      (profiledRawJointLeftPhysicalSiblingMoveOf A hwin family direction
        semanticMember hmember).1 := by
  rfl

/-- Provenance-stable right descriptor agreement after both optional moves
have been read from the two components of one joint semantic-edge
annotation. -/
theorem profiledRawJointHybridLiteralPrefixAnnotationOf_right_descriptor_eq
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (physicalMove : ProfiledRawJointRightPhysicalSiblingMove A)
    (literalMove : ProfiledRawJointGuardedCommonRightLiteralCrossMove A)
    (hphysical :
      (profiledRawJointHybridPhysicalAnnotationOf A strategy hwin family
        direction).1 = some physicalMove)
    (hliteral :
      (profiledRawJointHybridLiteralPrefixAnnotationOf A strategy hwin family
        direction).1 = some literalMove)
    (anchor : Bool) :
    (literalMove.1.descriptor anchor).base = physicalMove.1 := by
  obtain ⟨physicalMember, hphysicalMember, hphysicalMove⟩ :=
    profiledRawJointRightPhysicalSiblingMoveOption_spec A strategy hwin family
      direction physicalMove (by
        simpa [profiledRawJointHybridPhysicalAnnotationOf] using hphysical)
  obtain ⟨literalMember, hliteralMember, hliteralMove⟩ :=
    profiledRawJointRightLiteralPrefixMoveOption_spec A strategy hwin family
      direction literalMove (by
        simpa [profiledRawJointHybridLiteralPrefixAnnotationOf] using hliteral)
  have hmember : physicalMember = literalMember := by
    exact Option.some.inj (hphysicalMember.symm.trans hliteralMember)
  subst literalMember
  subst physicalMove
  subst literalMove
  exact profiledRawJointRightLiteralPrefixMoveOf_descriptor A strategy hwin
    family direction physicalMember hphysicalMember anchor

/-- Left mirror at the annotation interface. -/
theorem profiledRawJointHybridLiteralPrefixAnnotationOf_left_descriptor_eq
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (physicalMove : ProfiledRawJointLeftPhysicalSiblingMove A)
    (literalMove : ProfiledRawJointGuardedCommonLeftLiteralCrossMove A)
    (hphysical :
      (profiledRawJointHybridPhysicalAnnotationOf A strategy hwin family
        direction).2 = some physicalMove)
    (hliteral :
      (profiledRawJointHybridLiteralPrefixAnnotationOf A strategy hwin family
        direction).2 = some literalMove)
    (anchor : Bool) :
    (literalMove.1.descriptor anchor).base = physicalMove.1 := by
  obtain ⟨physicalMember, hphysicalMember, hphysicalMove⟩ :=
    profiledRawJointLeftPhysicalSiblingMoveOption_spec A strategy hwin family
      direction physicalMove (by
        simpa [profiledRawJointHybridPhysicalAnnotationOf] using hphysical)
  obtain ⟨literalMember, hliteralMember, hliteralMove⟩ :=
    profiledRawJointLeftLiteralPrefixMoveOption_spec A strategy hwin family
      direction literalMove (by
        simpa [profiledRawJointHybridLiteralPrefixAnnotationOf] using hliteral)
  have hmember : physicalMember = literalMember := by
    exact Option.some.inj (hphysicalMember.symm.trans hliteralMember)
  subst literalMember
  subst physicalMove
  subst literalMove
  exact profiledRawJointLeftLiteralPrefixMoveOf_descriptor A strategy hwin
    family direction physicalMember hphysicalMember anchor

/-! ## Right-oriented literal records -/

/-- The first receiver output of a recurring right literal-prefix move is
the complete literal receiver output of its selecting semantic edge. -/
theorem profiledRawJointRightLiteralPrefixMoveOf_firstReceiver
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcOnePairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).right () =
      some semanticMember)
    (anchor : Bool) (input : In₂ × In₁) :
    let move := profiledRawJointRightLiteralPrefixMoveOf A strategy hwin family
      direction semanticMember hmember
    let receiver :=
      profiledRawJointGuardedCommonRightLiteralCrossReceiverInitial A move
        anchor
    (profiledRawJointGuardedCommonRightLiteralCrossReceiverRecv A receiver
      input.1 input.2).1 =
        profiledRawJointRightPhysicalSiblingReceiver A hwin family direction
          semanticMember hmember anchor [] input := by
  classical
  let descriptor :=
    profiledRawJointRightPhysicalSiblingDescriptorOf A family direction
      semanticMember
  let monitor :=
    profiledRawJointRightPhysicalSiblingMonitor A descriptor false
  let receiverStrategy := fun member ↦
    profiledRawJointRightPhysicalSiblingReceiver A hwin family direction
      semanticMember hmember member
  let sender := profiledRawJointRightSiblingSender A semanticMember
  letI : Inhabited (ProfiledRawJointUnitTarget A) :=
    ⟨family.incidenceCode A⟩
  let move := profiledRawJointRightLiteralPrefixMoveOf A strategy hwin family
    direction semanticMember hmember
  let monitorFamily :=
    fun descriptor : ProfiledRawJointRightPhysicalSiblingDescriptor A ↦
      profiledRawJointRightPhysicalSiblingMonitor A descriptor false
  let literalMonitor := finiteCrossAnchorLiteralPrefixMonitor monitorFamily
  let firstAllowed := finiteCrossAnchorLiteralPrefixFirstAllowed monitorFamily
  let secondAllowed :=
    finiteCrossAnchorLiteralPrefixSecondAllowed monitorFamily
  let guard := finiteCrossAnchorFirstTwoGuardFamily
    (fun member ↦ literalMonitor (move.1.descriptor member)) move.1.start
    (firstAllowed move.1) (secondAllowed move.1) anchor
  let controller := move.memberController literalMonitor anchor
  let firstRecord := narrowedRecord guard (controller.labeledTree [])
    guard.initial input
  have hallowed :=
    move.memberController_records_allowed literalMonitor anchor input default
  have hfirst : finiteCrossAnchorLiteralFirstAllowed
      (receiverStrategy anchor) sender firstRecord = true := by
    simpa [move, guard, controller, firstRecord, literalMonitor, firstAllowed,
      secondAllowed, monitorFamily,
      profiledRawJointRightLiteralPrefixMoveOf,
      finiteCrossAnchorLiteralPrefixMove, descriptor, monitor,
      receiverStrategy, sender] using hallowed.1
  have hrecord : firstRecord =
      (input, receiverStrategy anchor [] input, sender [] input.2) := by
    exact of_decide_eq_true hfirst
  change firstRecord.2.1 = _
  rw [hrecord]

/-- The second receiver output is likewise pinned, now with the first input
as its one-letter literal past. -/
theorem profiledRawJointRightLiteralPrefixMoveOf_secondReceiver
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcOnePairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).right () =
      some semanticMember)
    (anchor : Bool) (first second : In₂ × In₁) :
    let move := profiledRawJointRightLiteralPrefixMoveOf A strategy hwin family
      direction semanticMember hmember
    let receiverRoot :=
      profiledRawJointGuardedCommonRightLiteralCrossReceiverInitial A move
        anchor
    let receiverAfterFirst :=
      (profiledRawJointGuardedCommonRightLiteralCrossReceiverRecv A
        receiverRoot first.1 first.2).2
    (profiledRawJointGuardedCommonRightLiteralCrossReceiverRecv A
      receiverAfterFirst second.1 second.2).1 =
        profiledRawJointRightPhysicalSiblingReceiver A hwin family direction
          semanticMember hmember anchor [first] second := by
  classical
  let descriptor :=
    profiledRawJointRightPhysicalSiblingDescriptorOf A family direction
      semanticMember
  let monitor :=
    profiledRawJointRightPhysicalSiblingMonitor A descriptor false
  let receiverStrategy := fun member ↦
    profiledRawJointRightPhysicalSiblingReceiver A hwin family direction
      semanticMember hmember member
  let sender := profiledRawJointRightSiblingSender A semanticMember
  letI : Inhabited (ProfiledRawJointUnitTarget A) :=
    ⟨family.incidenceCode A⟩
  let move := profiledRawJointRightLiteralPrefixMoveOf A strategy hwin family
    direction semanticMember hmember
  let monitorFamily :=
    fun descriptor : ProfiledRawJointRightPhysicalSiblingDescriptor A ↦
      profiledRawJointRightPhysicalSiblingMonitor A descriptor false
  let literalMonitor := finiteCrossAnchorLiteralPrefixMonitor monitorFamily
  let firstAllowed := finiteCrossAnchorLiteralPrefixFirstAllowed monitorFamily
  let secondAllowed :=
    finiteCrossAnchorLiteralPrefixSecondAllowed monitorFamily
  let guard := finiteCrossAnchorFirstTwoGuardFamily
    (fun member ↦ literalMonitor (move.1.descriptor member)) move.1.start
    (firstAllowed move.1) (secondAllowed move.1) anchor
  let controller := move.memberController literalMonitor anchor
  let firstRecord := narrowedRecord guard (controller.labeledTree [])
    guard.initial first
  let secondRecord := narrowedRecord guard
    (controller.labeledTree [first.2])
    (guard.step guard.initial firstRecord) second
  have hallowed :=
    move.memberController_records_allowed literalMonitor anchor first second
  have hsecond : finiteCrossAnchorLiteralSecondAllowed
      (receiverStrategy anchor) sender firstRecord secondRecord = true := by
    simpa [move, guard, controller, firstRecord, secondRecord, literalMonitor,
      firstAllowed, secondAllowed, monitorFamily,
      profiledRawJointRightLiteralPrefixMoveOf,
      finiteCrossAnchorLiteralPrefixMove, descriptor, monitor,
      receiverStrategy, sender] using hallowed.2
  have hrecord : secondRecord =
      (second, receiverStrategy anchor [first] second,
        sender [first.2] second.2) := by
    simpa [finiteCrossAnchorLiteralSecondAllowed, firstRecord] using
      (of_decide_eq_true hsecond)
  change secondRecord.2.1 = _
  rw [hrecord]

/-! ## Left-oriented literal records -/

/-- Left mirror of the first-record equality. -/
theorem profiledRawJointLeftLiteralPrefixMoveOf_firstReceiver
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcTwoPairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).left () =
      some semanticMember)
    (anchor : Bool) (input : In₁ × In₂) :
    let move := profiledRawJointLeftLiteralPrefixMoveOf A strategy hwin family
      direction semanticMember hmember
    let receiver :=
      profiledRawJointGuardedCommonLeftLiteralCrossReceiverInitial A move anchor
    (profiledRawJointGuardedCommonLeftLiteralCrossReceiverRecv A receiver
      input.1 input.2).1 =
        profiledRawJointLeftPhysicalSiblingReceiver A hwin family direction
          semanticMember hmember anchor [] input := by
  classical
  let descriptor :=
    profiledRawJointLeftPhysicalSiblingDescriptorOf A family direction
      semanticMember
  let baseMonitor :=
    profiledRawJointLeftPhysicalSiblingMonitor A descriptor false
  let monitorFamily :=
    fun descriptor : ProfiledRawJointLeftPhysicalSiblingDescriptor A ↦
      profiledRawJointGuardedCommonLeftLiteralCrossMonitor A descriptor
  let literalMonitor := finiteCrossAnchorLiteralPrefixMonitor monitorFamily
  let receiverStrategy := fun member ↦
    profiledRawJointLeftPhysicalSiblingReceiver A hwin family direction
      semanticMember hmember member
  let sender := profiledRawJointLeftSiblingSender A semanticMember
  letI : Inhabited (ProfiledRawJointUnitTarget A) :=
    ⟨family.incidenceCode A⟩
  let move := profiledRawJointLeftLiteralPrefixMoveOf A strategy hwin family
    direction semanticMember hmember
  let firstAllowed := finiteCrossAnchorLiteralPrefixFirstAllowed monitorFamily
  let secondAllowed :=
    finiteCrossAnchorLiteralPrefixSecondAllowed monitorFamily
  let guard := finiteCrossAnchorFirstTwoGuardFamily
    (fun member ↦ literalMonitor (move.1.descriptor member)) move.1.start
    (firstAllowed move.1) (secondAllowed move.1) anchor
  let controller := move.memberController literalMonitor anchor
  let firstRecord := narrowedRecord guard (controller.labeledTree [])
    guard.initial input
  have hallowed :=
    move.memberController_records_allowed literalMonitor anchor input default
  have hfirst : finiteCrossAnchorLiteralFirstAllowed
      (receiverStrategy anchor) sender firstRecord = true := by
    simpa [move, guard, controller, firstRecord, literalMonitor, firstAllowed,
      secondAllowed, monitorFamily,
      profiledRawJointLeftLiteralPrefixMoveOf,
      finiteCrossAnchorLiteralPrefixMove, descriptor, baseMonitor,
      profiledRawJointGuardedCommonLeftLiteralCrossMonitor,
      receiverStrategy, sender] using hallowed.1
  have hrecord : firstRecord =
      (input, receiverStrategy anchor [] input, sender [] input.2) := by
    exact of_decide_eq_true hfirst
  change firstRecord.2.1 = _
  rw [hrecord]

/-- Left mirror of the second-record equality. -/
theorem profiledRawJointLeftLiteralPrefixMoveOf_secondReceiver
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcTwoPairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).left () =
      some semanticMember)
    (anchor : Bool) (first second : In₁ × In₂) :
    let move := profiledRawJointLeftLiteralPrefixMoveOf A strategy hwin family
      direction semanticMember hmember
    let receiverRoot :=
      profiledRawJointGuardedCommonLeftLiteralCrossReceiverInitial A move anchor
    let receiverAfterFirst :=
      (profiledRawJointGuardedCommonLeftLiteralCrossReceiverRecv A receiverRoot
        first.1 first.2).2
    (profiledRawJointGuardedCommonLeftLiteralCrossReceiverRecv A
      receiverAfterFirst second.1 second.2).1 =
        profiledRawJointLeftPhysicalSiblingReceiver A hwin family direction
          semanticMember hmember anchor [first] second := by
  classical
  let descriptor :=
    profiledRawJointLeftPhysicalSiblingDescriptorOf A family direction
      semanticMember
  let baseMonitor :=
    profiledRawJointLeftPhysicalSiblingMonitor A descriptor false
  let monitorFamily :=
    fun descriptor : ProfiledRawJointLeftPhysicalSiblingDescriptor A ↦
      profiledRawJointGuardedCommonLeftLiteralCrossMonitor A descriptor
  let literalMonitor := finiteCrossAnchorLiteralPrefixMonitor monitorFamily
  let receiverStrategy := fun member ↦
    profiledRawJointLeftPhysicalSiblingReceiver A hwin family direction
      semanticMember hmember member
  let sender := profiledRawJointLeftSiblingSender A semanticMember
  letI : Inhabited (ProfiledRawJointUnitTarget A) :=
    ⟨family.incidenceCode A⟩
  let move := profiledRawJointLeftLiteralPrefixMoveOf A strategy hwin family
    direction semanticMember hmember
  let firstAllowed := finiteCrossAnchorLiteralPrefixFirstAllowed monitorFamily
  let secondAllowed :=
    finiteCrossAnchorLiteralPrefixSecondAllowed monitorFamily
  let guard := finiteCrossAnchorFirstTwoGuardFamily
    (fun member ↦ literalMonitor (move.1.descriptor member)) move.1.start
    (firstAllowed move.1) (secondAllowed move.1) anchor
  let controller := move.memberController literalMonitor anchor
  let firstRecord := narrowedRecord guard (controller.labeledTree [])
    guard.initial first
  let secondRecord := narrowedRecord guard
    (controller.labeledTree [first.2])
    (guard.step guard.initial firstRecord) second
  have hallowed :=
    move.memberController_records_allowed literalMonitor anchor first second
  have hsecond : finiteCrossAnchorLiteralSecondAllowed
      (receiverStrategy anchor) sender firstRecord secondRecord = true := by
    simpa [move, guard, controller, firstRecord, secondRecord, literalMonitor,
      firstAllowed, secondAllowed, monitorFamily,
      profiledRawJointLeftLiteralPrefixMoveOf,
      finiteCrossAnchorLiteralPrefixMove, descriptor, baseMonitor,
      profiledRawJointGuardedCommonLeftLiteralCrossMonitor,
      receiverStrategy, sender] using hallowed.2
  have hrecord : secondRecord =
      (second, receiverStrategy anchor [first] second,
        sender [first.2] second.2) := by
    simpa [finiteCrossAnchorLiteralSecondAllowed, firstRecord] using
      (of_decide_eq_true hsecond)
  change secondRecord.2.1 = _
  rw [hrecord]

end

end DetParityAutomaton

end DistributedSynthesis
