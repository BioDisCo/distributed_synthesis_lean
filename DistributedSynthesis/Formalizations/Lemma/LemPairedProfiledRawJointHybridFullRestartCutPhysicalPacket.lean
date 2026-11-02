/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridFullRestartSeparateOccurrenceAudit
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridFinitePayloadLinkedPhysicalPriority
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankDirectionChildRunAlignment

/-!
# Physical monitor packets at FullRestart cuts

Every operational cut of the repaired controller starts at a fresh linked
occurrence.  This file identifies the complete concrete block with that
occurrence's physical monitor block.  The generic target-monitor theorem can
therefore propagate the actual DPA state and expose the exact block-minimum
priority at the following cut.
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

private abbrev BankControl :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl A strategy hwin

private abbrev RetainedTag :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A strategy
    hwin

/-! ## Current literal-table source alignment -/

/-- A left literal table carried by a one-sided semantic source stores
exactly that source's live left slot. -/
private theorem leftLiteralPrefixCurrent_descriptor_source_eq
    (initial : ProfiledRawJointCommonBaseWorld A strategy)
    (source : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (extra : ProfiledRawJointHybridLiteralPrefixEdgeAnnotation A)
    (hcurrent :
      ProfiledRawJointHybridLiteralPrefixCurrentCompatible A strategy hwin
        initial (.oneSided source) extra)
    (semanticMember : ProcTwoPairedEntryRep strategy × A.State)
    (hmember : source.family.left () = some semanticMember)
    (move : ProfiledRawJointGuardedCommonLeftLiteralCrossMove A)
    (hmove : extra.2 = some move) (anchor : Bool) :
    (move.1.descriptor anchor).base.source =
      profiledRawLeftSlotOfSemanticPair A semanticMember := by
  rcases hcurrent with hroot |
    ⟨parent, old, rawDirection, hsource, hextra⟩
  · cases hroot.1
  · cases parent with
    | common world =>
        cases rawDirection with
        | simultaneous input =>
            simp [ProfiledRawJointHybridSemanticState.step] at hsource
        | strict actual =>
            cases hside : actual.side with
            | right =>
                have hfamily := congrArg
                  ProfiledRawJointOneSidedSemanticState.family
                  (ProfiledRawJointHybridSemanticState.oneSided.inj hsource)
                simp [profiledRawJointCommonExitState, hside] at hfamily
                have hsemantic :
                    ((profiledRawJointCommonWorldFamily A world).semanticChild A
                      (profiledRawJointCommonActualDirection actual).direction
                      ).left () = some semanticMember := by
                  have hlive' :
                      ((profiledRawJointCommonWorldFamily A world
                        ).rightActualChild A
                          (profiledRawJointCommonActualDirection actual).direction
                        ).left () = some semanticMember := by
                    rw [hfamily]
                    exact hmember
                  simpa only [
                    ProfiledRawJointSemanticFamily.semanticChild_left,
                    ProfiledRawJointSemanticFamily.rightActualChild_left]
                    using hlive'
                have hoption :
                    (profiledRawJointHybridLiteralPrefixAnnotationOf A strategy
                      hwin (profiledRawJointCommonWorldFamily A world)
                        (profiledRawJointCommonActualDirection actual).direction
                      ).2 = some move := by
                  rw [← hextra] at hmove
                  simpa [
                    profiledRawJointHybridLiteralPrefixAnnotationAdvance]
                    using hmove
                obtain ⟨member, hmember', hmoveEq⟩ :=
                  profiledRawJointLeftLiteralPrefixMoveOption_spec A strategy
                    hwin (profiledRawJointCommonWorldFamily A world)
                      (profiledRawJointCommonActualDirection actual).direction
                    move (by
                      simpa [profiledRawJointHybridLiteralPrefixAnnotationOf]
                        using hoption)
                rw [hsemantic] at hmember'
                have heq : semanticMember = member :=
                  Option.some.inj hmember'
                subst member
                rw [hmoveEq]
                calc
                  _ =
                      (profiledRawJointLeftPhysicalSiblingMoveOf A hwin
                        (profiledRawJointCommonWorldFamily A world)
                        (profiledRawJointCommonActualDirection actual).direction
                        semanticMember hsemantic).1.source :=
                    congrArg (fun descriptor ↦ descriptor.source)
                      (profiledRawJointLeftLiteralPrefixMoveOf_descriptor A
                        strategy hwin
                        (profiledRawJointCommonWorldFamily A world)
                        (profiledRawJointCommonActualDirection actual).direction
                        semanticMember hsemantic anchor)
                  _ = profiledRawLeftSlotOfSemanticPair A semanticMember := rfl
            | left =>
                have hfamily := congrArg
                  ProfiledRawJointOneSidedSemanticState.family
                  (ProfiledRawJointHybridSemanticState.oneSided.inj hsource)
                simp [profiledRawJointCommonExitState, hside] at hfamily
                rw [← hfamily] at hmember
                simp at hmember
    | oneSided parentSource =>
        cases rawDirection with
        | simultaneous input =>
            simp [ProfiledRawJointHybridSemanticState.step] at hsource
        | strict actual =>
            cases hside : actual.side with
            | right =>
                have hfamily := congrArg
                  ProfiledRawJointOneSidedSemanticState.family
                  (ProfiledRawJointHybridSemanticState.oneSided.inj hsource)
                simp [ProfiledRawJointOneSidedSemanticState.step, hside]
                  at hfamily
                have hsemantic :
                    (parentSource.family.semanticChild A actual.direction).left
                        () = some semanticMember := by
                  have hlive' :
                      (parentSource.family.rightActualChild A actual.direction
                        ).left () = some semanticMember := by
                    rw [hfamily]
                    exact hmember
                  simpa only [
                    ProfiledRawJointSemanticFamily.semanticChild_left,
                    ProfiledRawJointSemanticFamily.rightActualChild_left]
                    using hlive'
                have hoption :
                    (profiledRawJointHybridLiteralPrefixAnnotationOf A strategy
                      hwin parentSource.family actual.direction).2 =
                        some move := by
                  rw [← hextra] at hmove
                  simpa [
                    profiledRawJointHybridLiteralPrefixAnnotationAdvance]
                    using hmove
                obtain ⟨member, hmember', hmoveEq⟩ :=
                  profiledRawJointLeftLiteralPrefixMoveOption_spec A strategy
                    hwin parentSource.family actual.direction move (by
                      simpa [profiledRawJointHybridLiteralPrefixAnnotationOf]
                        using hoption)
                rw [hsemantic] at hmember'
                have heq : semanticMember = member :=
                  Option.some.inj hmember'
                subst member
                rw [hmoveEq]
                calc
                  _ =
                      (profiledRawJointLeftPhysicalSiblingMoveOf A hwin
                        parentSource.family actual.direction semanticMember
                          hsemantic).1.source :=
                    congrArg (fun descriptor ↦ descriptor.source)
                      (profiledRawJointLeftLiteralPrefixMoveOf_descriptor A
                        strategy hwin parentSource.family actual.direction
                          semanticMember hsemantic anchor)
                  _ = profiledRawLeftSlotOfSemanticPair A semanticMember := rfl
            | left =>
                have hfamily := congrArg
                  ProfiledRawJointOneSidedSemanticState.family
                  (ProfiledRawJointHybridSemanticState.oneSided.inj hsource)
                simp [ProfiledRawJointOneSidedSemanticState.step, hside]
                  at hfamily
                rw [← hfamily] at hmember
                simp at hmember
    | dead =>
        cases rawDirection <;>
          simp [ProfiledRawJointHybridSemanticState.step] at hsource

/-- Right-lane mirror of current literal-table source alignment. -/
private theorem rightLiteralPrefixCurrent_descriptor_source_eq
    (initial : ProfiledRawJointCommonBaseWorld A strategy)
    (source : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (extra : ProfiledRawJointHybridLiteralPrefixEdgeAnnotation A)
    (hcurrent :
      ProfiledRawJointHybridLiteralPrefixCurrentCompatible A strategy hwin
        initial (.oneSided source) extra)
    (semanticMember : ProcOnePairedEntryRep strategy × A.State)
    (hmember : source.family.right () = some semanticMember)
    (move : ProfiledRawJointGuardedCommonRightLiteralCrossMove A)
    (hmove : extra.1 = some move) (anchor : Bool) :
    (move.1.descriptor anchor).base.source =
      profiledRawRightSlotOfSemanticPair A semanticMember := by
  rcases hcurrent with hroot |
    ⟨parent, old, rawDirection, hsource, hextra⟩
  · cases hroot.1
  · cases parent with
    | common world =>
        cases rawDirection with
        | simultaneous input =>
            simp [ProfiledRawJointHybridSemanticState.step] at hsource
        | strict actual =>
            cases hside : actual.side with
            | right =>
                have hfamily := congrArg
                  ProfiledRawJointOneSidedSemanticState.family
                  (ProfiledRawJointHybridSemanticState.oneSided.inj hsource)
                simp [profiledRawJointCommonExitState, hside] at hfamily
                rw [← hfamily] at hmember
                simp at hmember
            | left =>
                have hfamily := congrArg
                  ProfiledRawJointOneSidedSemanticState.family
                  (ProfiledRawJointHybridSemanticState.oneSided.inj hsource)
                simp [profiledRawJointCommonExitState, hside] at hfamily
                have hsemantic :
                    ((profiledRawJointCommonWorldFamily A world).semanticChild A
                      (profiledRawJointCommonActualDirection actual).direction
                      ).right () = some semanticMember := by
                  have hlive' :
                      ((profiledRawJointCommonWorldFamily A world
                        ).leftActualChild A
                          (profiledRawJointCommonActualDirection actual).direction
                        ).right () = some semanticMember := by
                    rw [hfamily]
                    exact hmember
                  simpa only [
                    ProfiledRawJointSemanticFamily.semanticChild_right,
                    ProfiledRawJointSemanticFamily.leftActualChild_right]
                    using hlive'
                have hoption :
                    (profiledRawJointHybridLiteralPrefixAnnotationOf A strategy
                      hwin (profiledRawJointCommonWorldFamily A world)
                        (profiledRawJointCommonActualDirection actual).direction
                      ).1 = some move := by
                  rw [← hextra] at hmove
                  simpa [
                    profiledRawJointHybridLiteralPrefixAnnotationAdvance]
                    using hmove
                obtain ⟨member, hmember', hmoveEq⟩ :=
                  profiledRawJointRightLiteralPrefixMoveOption_spec A strategy
                    hwin (profiledRawJointCommonWorldFamily A world)
                      (profiledRawJointCommonActualDirection actual).direction
                    move (by
                      simpa [profiledRawJointHybridLiteralPrefixAnnotationOf]
                        using hoption)
                rw [hsemantic] at hmember'
                have heq : semanticMember = member :=
                  Option.some.inj hmember'
                subst member
                rw [hmoveEq]
                calc
                  _ =
                      (profiledRawJointRightPhysicalSiblingMoveOf A hwin
                        (profiledRawJointCommonWorldFamily A world)
                        (profiledRawJointCommonActualDirection actual).direction
                        semanticMember hsemantic).1.source :=
                    congrArg (fun descriptor ↦ descriptor.source)
                      (profiledRawJointRightLiteralPrefixMoveOf_descriptor A
                        strategy hwin
                        (profiledRawJointCommonWorldFamily A world)
                        (profiledRawJointCommonActualDirection actual).direction
                        semanticMember hsemantic anchor)
                  _ = profiledRawRightSlotOfSemanticPair A semanticMember := rfl
    | oneSided parentSource =>
        cases rawDirection with
        | simultaneous input =>
            simp [ProfiledRawJointHybridSemanticState.step] at hsource
        | strict actual =>
            cases hside : actual.side with
            | right =>
                have hfamily := congrArg
                  ProfiledRawJointOneSidedSemanticState.family
                  (ProfiledRawJointHybridSemanticState.oneSided.inj hsource)
                simp [ProfiledRawJointOneSidedSemanticState.step, hside]
                  at hfamily
                rw [← hfamily] at hmember
                simp at hmember
            | left =>
                have hfamily := congrArg
                  ProfiledRawJointOneSidedSemanticState.family
                  (ProfiledRawJointHybridSemanticState.oneSided.inj hsource)
                simp [ProfiledRawJointOneSidedSemanticState.step, hside]
                  at hfamily
                have hsemantic :
                    (parentSource.family.semanticChild A actual.direction
                      ).right () = some semanticMember := by
                  have hlive' :
                      (parentSource.family.leftActualChild A actual.direction
                        ).right () = some semanticMember := by
                    rw [hfamily]
                    exact hmember
                  simpa only [
                    ProfiledRawJointSemanticFamily.semanticChild_right,
                    ProfiledRawJointSemanticFamily.leftActualChild_right]
                    using hlive'
                have hoption :
                    (profiledRawJointHybridLiteralPrefixAnnotationOf A strategy
                      hwin parentSource.family actual.direction).1 =
                        some move := by
                  rw [← hextra] at hmove
                  simpa [
                    profiledRawJointHybridLiteralPrefixAnnotationAdvance]
                    using hmove
                obtain ⟨member, hmember', hmoveEq⟩ :=
                  profiledRawJointRightLiteralPrefixMoveOption_spec A strategy
                    hwin parentSource.family actual.direction move (by
                      simpa [profiledRawJointHybridLiteralPrefixAnnotationOf]
                        using hoption)
                rw [hsemantic] at hmember'
                have heq : semanticMember = member :=
                  Option.some.inj hmember'
                subst member
                rw [hmoveEq]
                calc
                  _ =
                      (profiledRawJointRightPhysicalSiblingMoveOf A hwin
                        parentSource.family actual.direction semanticMember
                          hsemantic).1.source :=
                    congrArg (fun descriptor ↦ descriptor.source)
                      (profiledRawJointRightLiteralPrefixMoveOf_descriptor A
                        strategy hwin parentSource.family actual.direction
                          semanticMember hsemantic anchor)
                  _ = profiledRawRightSlotOfSemanticPair A semanticMember := rfl
    | dead =>
        cases rawDirection <;>
          simp [ProfiledRawJointHybridSemanticState.step] at hsource

/-- The live slot certified by a ready left root is exactly the source stored
in the executable left sender installed by the restart relay. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_leftReady_restartRelay_senderSource
    (state : BankControl A strategy hwin)
    (hready :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftRootReady
        A strategy hwin state)
    (rightAnchor leftAnchor : Bool) :
    ∃ code : ProfiledRawJointIncidenceCode A (I := Unit),
      ∃ slot : ProfiledRawLeftSlot A,
        state.2.1.1 = .oneSided code ∧
          code.family.left () = some slot ∧
          profiledRawJointLeftFinitePayloadLiteralPrefixSenderSource
              A strategy hwin
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRestartRelay
                A strategy hwin state rightAnchor leftAnchor).2.1 false =
            slot := by
  rcases hready with ⟨code, slot, hreachable, hcode, hlive⟩
  obtain ⟨oldMove, hmove, hrebuild⟩ :=
    exists_profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMove_of_liveLane
      A strategy hwin hreachable code hcode slot hlive
  rcases hrebuild with
    ⟨_hmarker, _hreachable', parent, old, rawDirection, family, direction,
      semanticMember, hmember, hsource, hannotation, _haligned, hold,
        hlinked⟩
  let packet :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankFiniteStep A strategy
      hwin state.1 state.2 hreachable
  obtain ⟨source, hpacketSource, hsourceCode⟩ :=
    ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankFiniteStep.source_oneSided_of_code
      A strategy hwin hreachable code hcode
  have hslot :
      profiledRawJointOneSidedCurrentSlots A .left (source.code A) () =
        some (.inr slot) := by
    rw [hsourceCode]
    simp [profiledRawJointOneSidedCurrentSlots, hlive]
  obtain ⟨currentMember, hcurrentMember, hcurrentSlot, _⟩ :=
    source.exists_left_member_of_currentSlot A () (.inr slot) hslot
  have hcurrentSlot' :
      profiledRawLeftSlotOfSemanticPair A currentMember = slot := by
    exact (Sum.inr.inj hcurrentSlot).symm
  have hcurrent :=
    profiledRawJointHybridLiteralPrefixCurrentCompatible_of_marked A strategy
      hwin
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankInstalled A
        strategy hwin state.1).world packet.source state.2.1.2.2
          packet.marked_current
  rw [hpacketSource] at hcurrent
  have hOldSource : (oldMove.1.descriptor false).base.source = slot :=
    (leftLiteralPrefixCurrent_descriptor_source_eq A strategy hwin
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankInstalled A
        strategy hwin state.1).world source state.2.1.2.2.2 hcurrent
          currentMember hcurrentMember oldMove hmove false).trans hcurrentSlot'
  have hLiteralSource :
      ((profiledRawJointLeftLiteralPrefixMoveOf A strategy hwin family
        direction semanticMember hmember).1.descriptor false).base.source =
          profiledRawLeftSlotOfSemanticPair A semanticMember := by
    have hdescriptor := congrArg (fun descriptor ↦ descriptor.source)
      (profiledRawJointLeftLiteralPrefixMoveOf_descriptor A strategy hwin
        family direction semanticMember hmember false)
    exact hdescriptor.trans rfl
  have holdSource :
      (oldMove.1.descriptor false).base.source =
        profiledRawLeftSlotOfSemanticPair A semanticMember :=
    (congrArg
      (fun candidate : ProfiledRawJointGuardedCommonLeftLiteralCrossMove A ↦
        (candidate.1.descriptor false).base.source) hold).trans hLiteralSource
  refine ⟨code, slot, hcode, hlive, ?_⟩
  change
    profiledRawJointLeftFinitePayloadLiteralPrefixSenderSource A strategy hwin
        (profiledRawJointLeftFinitePayloadLiteralPrefixSenderInitial A
          (state.linkedLeftMove A strategy hwin)) false = slot
  rw [hlinked]
  change
    profiledRawJointLeftFinitePayloadLiteralPrefixSenderSource A strategy hwin
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftSenderAtPrefix
        A strategy hwin state family direction semanticMember hmember [])
          false = slot
  rw [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftSenderAtPrefix_source]
  exact holdSource.symm.trans hOldSource

/-- Ready right-root mirror of executable restart-source readback. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_rightReady_restartRelay_senderSource
    (state : BankControl A strategy hwin)
    (hready :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightRootReady
        A strategy hwin state)
    (rightAnchor leftAnchor : Bool) :
    ∃ code : ProfiledRawJointIncidenceCode A (I := Unit),
      ∃ slot : ProfiledRawRightSlot A,
        state.2.1.1 = .oneSided code ∧
          code.family.right () = some slot ∧
          profiledRawJointRightFinitePayloadLiteralPrefixSenderSource
              A strategy hwin
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRestartRelay
                A strategy hwin state rightAnchor leftAnchor).1.1 false =
            slot := by
  rcases hready with ⟨code, slot, hreachable, hcode, hlive⟩
  obtain ⟨oldMove, hmove, hrebuild⟩ :=
    exists_profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMove_of_liveLane
      A strategy hwin hreachable code hcode slot hlive
  rcases hrebuild with
    ⟨_hmarker, _hreachable', parent, old, rawDirection, family, direction,
      semanticMember, hmember, hsource, hannotation, _haligned, hold,
        hlinked⟩
  let packet :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankFiniteStep A strategy
      hwin state.1 state.2 hreachable
  obtain ⟨source, hpacketSource, hsourceCode⟩ :=
    ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankFiniteStep.source_oneSided_of_code
      A strategy hwin hreachable code hcode
  have hslot :
      profiledRawJointOneSidedCurrentSlots A .right (source.code A) () =
        some (.inl slot) := by
    rw [hsourceCode]
    simp [profiledRawJointOneSidedCurrentSlots, hlive]
  obtain ⟨currentMember, hcurrentMember, hcurrentSlot, _⟩ :=
    source.exists_right_member_of_currentSlot A () (.inl slot) hslot
  have hcurrentSlot' :
      profiledRawRightSlotOfSemanticPair A currentMember = slot := by
    exact (Sum.inl.inj hcurrentSlot).symm
  have hcurrent :=
    profiledRawJointHybridLiteralPrefixCurrentCompatible_of_marked A strategy
      hwin
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankInstalled A
        strategy hwin state.1).world packet.source state.2.1.2.2
          packet.marked_current
  rw [hpacketSource] at hcurrent
  have hOldSource : (oldMove.1.descriptor false).base.source = slot :=
    (rightLiteralPrefixCurrent_descriptor_source_eq A strategy hwin
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankInstalled A
        strategy hwin state.1).world source state.2.1.2.2.2 hcurrent
          currentMember hcurrentMember oldMove hmove false).trans hcurrentSlot'
  have hLiteralSource :
      ((profiledRawJointRightLiteralPrefixMoveOf A strategy hwin family
        direction semanticMember hmember).1.descriptor false).base.source =
          profiledRawRightSlotOfSemanticPair A semanticMember := by
    have hdescriptor := congrArg (fun descriptor ↦ descriptor.source)
      (profiledRawJointRightLiteralPrefixMoveOf_descriptor A strategy hwin
        family direction semanticMember hmember false)
    exact hdescriptor.trans rfl
  have holdSource :
      (oldMove.1.descriptor false).base.source =
        profiledRawRightSlotOfSemanticPair A semanticMember :=
    (congrArg
      (fun candidate : ProfiledRawJointGuardedCommonRightLiteralCrossMove A ↦
        (candidate.1.descriptor false).base.source) hold).trans hLiteralSource
  refine ⟨code, slot, hcode, hlive, ?_⟩
  change
    profiledRawJointRightFinitePayloadLiteralPrefixSenderSource A strategy hwin
        (profiledRawJointRightFinitePayloadLiteralPrefixSenderInitial A
          (state.linkedRightMove A strategy hwin)) false = slot
  rw [hlinked]
  change
    profiledRawJointRightFinitePayloadLiteralPrefixSenderSource A strategy hwin
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightSenderAtPrefix
        A strategy hwin state family direction semanticMember hmember [])
          false = slot
  rw [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightSenderAtPrefix_source]
  exact holdSource.symm.trans hOldSource

/-- A ready right cut exposes the exact rebuilt semantic occurrence together
with the public-code equation linking each represented target to the concrete
marked-bank child. -/
private theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_rightCut_freshAlignedOccurrence
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (cuts : OperationalCloseCutPackage (fun n ↦ (env n).graph))
    (hnoBoth : ∀ n : Nat, (env n).graph ≠ .both)
    (k : Nat) (hgraph : (env (cuts.cuts k)).graph = .right)
    (hready :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightRootReady
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartParentAt
            A strategy hwin initialTag env (cuts.cuts k))) :
    let root :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartParentAt
        A strategy hwin initialTag env (cuts.cuts k)
    let base :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBaseAt
        A strategy hwin initialTag env (cuts.cuts k)
    ∃ (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
        (direction : ProfiledRawJointFamilyDirection
          (I := Unit) (In₁ := In₁) (In₂ := In₂))
        (semanticMember : ProcOnePairedEntryRep strategy × A.State),
      ∃ hmember : (family.semanticChild A direction).right () =
          some semanticMember,
        base.1.1 =
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightSenderAtPrefix
              A strategy hwin root family direction semanticMember hmember [] ∧
          base.1.2 =
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightReceiverAtPrefix
              A strategy hwin root family direction semanticMember hmember false
                [] ∧
          ∀ (row : PairedEntryRow) (past : List (In₂ × In₁))
              (input : In₂ × In₁),
            (root.childCode A strategy hwin
                (.strict
                  (profiledRawJointUnitRightActualDirection
                    (In₁ := In₁) (In₂ := In₂) row past input))).1 =
              .oneSided
                ((profiledRawJointHybridValidatedMarkedLiteralPrefixBankRightActivations
                  A strategy hwin family direction semanticMember hmember false
                    ).target row past input) := by
  dsimp only
  let root :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartParentAt
      A strategy hwin initialTag env (cuts.cuts k)
  let base :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBaseAt
      A strategy hwin initialTag env (cuts.cuts k)
  have hbase :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBaseAt_cut_eq_restartRelay
      A strategy hwin initialTag env cuts hnoBoth k hgraph
  change base =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRestartRelay
        A strategy hwin root false false at hbase
  change
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightRootReady
      A strategy hwin root at hready
  rcases hready with ⟨code, slot, hreachable, hcode, hlive⟩
  obtain ⟨oldMove, hmove, hrebuild⟩ :=
    exists_profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMove_of_liveLane
      A strategy hwin hreachable code hcode slot hlive
  rcases hrebuild with
    ⟨_hmarker, hreachable', parent, old, rawDirection, family, direction,
      semanticMember, hmember, _hsource, _hannotation, haligned, _hold,
        hlinked⟩
  let packet :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankFiniteStep A strategy
      hwin root.1 root.2 hreachable
  obtain ⟨source, hpacketSource, hsourceCode⟩ :=
    ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankFiniteStep.source_oneSided_of_code
      A strategy hwin hreachable code hcode
  have hslot :
      profiledRawJointOneSidedCurrentSlots A .right (source.code A) () =
        some (.inl slot) := by
    rw [hsourceCode]
    simp [profiledRawJointOneSidedCurrentSlots, hlive]
  obtain ⟨currentMember, hcurrentMember, _hcurrentSlot, _⟩ :=
    source.exists_right_member_of_currentSlot A () (.inl slot) hslot
  have hpacketSource' :
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankFiniteStep A
          strategy hwin root.1 root.2 hreachable').source =
        .oneSided source := by
    simpa only using hpacketSource
  have hpacketMove : packet.move.1 = some (source.move A) := by
    rw [← packet.source_move, hpacketSource]
    rfl
  letI : Inhabited
      (ProfiledRawJointHybridFinitePayloadRowExactRightReceiverOutput A
        (BankControl A strategy hwin)) :=
    ⟨profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightReceiver
      A strategy hwin root
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRightActivations
          A strategy hwin family direction semanticMember hmember false)
        [] default⟩
  refine ⟨family, direction, semanticMember, hmember, ?_, ?_, ?_⟩
  · change base.1.1 =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightSenderAtPrefix
        A strategy hwin root family direction semanticMember hmember []
    rw [hbase]
    change
      profiledRawJointRightFinitePayloadLiteralPrefixSenderInitial A
          (root.linkedRightMove A strategy hwin) =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightSenderAtPrefix
          A strategy hwin root family direction semanticMember hmember []
    rw [hlinked]
    change
      finiteCrossAnchorDescriptorFirstTwoSenderInitial _ _ _
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOf
            A strategy hwin root family direction semanticMember hmember) =
        ⟨_, finiteCrossAnchorSenderAtPrefix
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOf
            A strategy hwin root family direction semanticMember hmember).2 []⟩
    rw [finiteCrossAnchorSenderAtPrefix_nil]
    rfl
  · change base.1.2 =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightReceiverAtPrefix
        A strategy hwin root family direction semanticMember hmember false []
    rw [hbase]
    change
      profiledRawJointRightFinitePayloadLiteralPrefixReceiverInitial A
          (root.linkedRightMove A strategy hwin) false =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightReceiverAtPrefix
          A strategy hwin root family direction semanticMember hmember false []
    rw [hlinked]
    change
      finiteCrossAnchorDescriptorFirstTwoReceiverInitial _ _ _
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOf
            A strategy hwin root family direction semanticMember hmember) false =
        ⟨_, finiteCrossAnchorReceiverAtPrefix
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOf
            A strategy hwin root family direction semanticMember hmember).2 false []⟩
    rw [finiteCrossAnchorReceiverAtPrefix_nil]
    rfl
  · intro row past input
    let actual := profiledRawJointUnitRightActualDirection
      (In₁ := In₁) (In₂ := In₂) row past input
    let activation :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankRightActivations
        A strategy hwin family direction semanticMember hmember false
    have htarget :=
      haligned source hpacketSource' currentMember hcurrentMember row past input
    rw [
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl.childCode,
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl.move_eq_of_reachable
        A strategy hwin root hreachable,
      sourceFreeBeliefParentLinkedNext_fst]
    change
      profiledRawJointHybridNext A root.2.1.1 packet.move.1
          (.strict actual) =
        .oneSided (activation.target row past input)
    rw [hcode, hpacketMove]
    apply congrArg ProfiledRawJointHybridCode.oneSided
    calc
      profiledRawJointOneSidedNext A code (source.move A) actual =
          (source.step A actual).code A := by
        rw [← hsourceCode]
        exact (ProfiledRawJointOneSidedSemanticState.step_code A source actual).symm
      _ = activation.target row past input := by
        simpa [activation,
          profiledRawJointHybridValidatedMarkedLiteralPrefixBankRightActivations,
          profiledRawJointRightPhysicalSiblingActivation,
          profiledRawJointRightSiblingActivation, actual] using htarget

/-- Left-cut mirror of the aligned fresh-occurrence extraction. -/
private theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_leftCut_freshAlignedOccurrence
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (cuts : OperationalCloseCutPackage (fun n ↦ (env n).graph))
    (hnoBoth : ∀ n : Nat, (env n).graph ≠ .both)
    (k : Nat) (hgraph : (env (cuts.cuts k)).graph = .left)
    (hready :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftRootReady
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartParentAt
            A strategy hwin initialTag env (cuts.cuts k))) :
    let root :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartParentAt
        A strategy hwin initialTag env (cuts.cuts k)
    let base :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBaseAt
        A strategy hwin initialTag env (cuts.cuts k)
    ∃ (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
        (direction : ProfiledRawJointFamilyDirection
          (I := Unit) (In₁ := In₁) (In₂ := In₂))
        (semanticMember : ProcTwoPairedEntryRep strategy × A.State),
      ∃ hmember : (family.semanticChild A direction).left () =
          some semanticMember,
        base.2.1 =
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftSenderAtPrefix
              A strategy hwin root family direction semanticMember hmember [] ∧
          base.2.2 =
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftReceiverAtPrefix
              A strategy hwin root family direction semanticMember hmember false
                [] ∧
          ∀ (row : PairedEntryRow) (past : List (In₁ × In₂))
              (input : In₁ × In₂),
            (root.childCode A strategy hwin
                (.strict
                  (profiledRawJointUnitLeftActualDirection
                    (In₁ := In₁) (In₂ := In₂) row past input))).1 =
              .oneSided
                ((profiledRawJointHybridValidatedMarkedLiteralPrefixBankLeftActivations
                  A strategy hwin family direction semanticMember hmember false
                    ).target row past input) := by
  dsimp only
  let root :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartParentAt
      A strategy hwin initialTag env (cuts.cuts k)
  let base :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBaseAt
      A strategy hwin initialTag env (cuts.cuts k)
  have hbase :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBaseAt_cut_eq_restartRelay
      A strategy hwin initialTag env cuts hnoBoth k hgraph
  change base =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredRestartRelay
        A strategy hwin root false false at hbase
  change
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftRootReady
      A strategy hwin root at hready
  rcases hready with ⟨code, slot, hreachable, hcode, hlive⟩
  obtain ⟨oldMove, hmove, hrebuild⟩ :=
    exists_profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMove_of_liveLane
      A strategy hwin hreachable code hcode slot hlive
  rcases hrebuild with
    ⟨_hmarker, hreachable', parent, old, rawDirection, family, direction,
      semanticMember, hmember, _hsource, _hannotation, haligned, _hold,
        hlinked⟩
  let packet :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankFiniteStep A strategy
      hwin root.1 root.2 hreachable
  obtain ⟨source, hpacketSource, hsourceCode⟩ :=
    ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankFiniteStep.source_oneSided_of_code
      A strategy hwin hreachable code hcode
  have hslot :
      profiledRawJointOneSidedCurrentSlots A .left (source.code A) () =
        some (.inr slot) := by
    rw [hsourceCode]
    simp [profiledRawJointOneSidedCurrentSlots, hlive]
  obtain ⟨currentMember, hcurrentMember, _hcurrentSlot, _⟩ :=
    source.exists_left_member_of_currentSlot A () (.inr slot) hslot
  have hpacketSource' :
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankFiniteStep A
          strategy hwin root.1 root.2 hreachable').source =
        .oneSided source := by
    simpa only using hpacketSource
  have hpacketMove : packet.move.1 = some (source.move A) := by
    rw [← packet.source_move, hpacketSource]
    rfl
  letI : Inhabited
      (ProfiledRawJointHybridFinitePayloadRowExactLeftReceiverOutput A
        (BankControl A strategy hwin)) :=
    ⟨profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftReceiver
      A strategy hwin root
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLeftActivations
          A strategy hwin family direction semanticMember hmember false)
        [] default⟩
  refine ⟨family, direction, semanticMember, hmember, ?_, ?_, ?_⟩
  · change base.2.1 =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftSenderAtPrefix
        A strategy hwin root family direction semanticMember hmember []
    rw [hbase]
    change
      profiledRawJointLeftFinitePayloadLiteralPrefixSenderInitial A
          (root.linkedLeftMove A strategy hwin) =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftSenderAtPrefix
          A strategy hwin root family direction semanticMember hmember []
    rw [hlinked]
    change
      finiteCrossAnchorDescriptorFirstTwoSenderInitial _ _ _
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOf
            A strategy hwin root family direction semanticMember hmember) =
        ⟨_, finiteCrossAnchorSenderAtPrefix
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOf
            A strategy hwin root family direction semanticMember hmember).2 []⟩
    rw [finiteCrossAnchorSenderAtPrefix_nil]
    rfl
  · change base.2.2 =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftReceiverAtPrefix
        A strategy hwin root family direction semanticMember hmember false []
    rw [hbase]
    change
      profiledRawJointLeftFinitePayloadLiteralPrefixReceiverInitial A
          (root.linkedLeftMove A strategy hwin) false =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftReceiverAtPrefix
          A strategy hwin root family direction semanticMember hmember false []
    rw [hlinked]
    change
      finiteCrossAnchorDescriptorFirstTwoReceiverInitial _ _ _
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOf
            A strategy hwin root family direction semanticMember hmember) false =
        ⟨_, finiteCrossAnchorReceiverAtPrefix
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOf
            A strategy hwin root family direction semanticMember hmember).2 false []⟩
    rw [finiteCrossAnchorReceiverAtPrefix_nil]
    rfl
  · intro row past input
    let actual := profiledRawJointUnitLeftActualDirection
      (In₁ := In₁) (In₂ := In₂) row past input
    let activation :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLeftActivations
        A strategy hwin family direction semanticMember hmember false
    have htarget :=
      haligned source hpacketSource' currentMember hcurrentMember row past input
    rw [
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl.childCode,
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl.move_eq_of_reachable
        A strategy hwin root hreachable,
      sourceFreeBeliefParentLinkedNext_fst]
    change
      profiledRawJointHybridNext A root.2.1.1 packet.move.1
          (.strict actual) =
        .oneSided (activation.target row past input)
    rw [hcode, hpacketMove]
    apply congrArg ProfiledRawJointHybridCode.oneSided
    calc
      profiledRawJointOneSidedNext A code (source.move A) actual =
          (source.step A actual).code A := by
        rw [← hsourceCode]
        exact (ProfiledRawJointOneSidedSemanticState.step_code A source actual).symm
      _ = activation.target row past input := by
        simpa [activation,
          profiledRawJointHybridValidatedMarkedLiteralPrefixBankLeftActivations,
          profiledRawJointLeftPhysicalSiblingActivation,
          profiledRawJointLeftSiblingActivation, actual] using htarget

/-! ## Pointwise physical reification of a cut block -/

/-- Every round of a strict-right operational block, including its closing
round, is literally the corresponding round of the fresh linked physical
word. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_rightCut_round_eq_linkedPhysicalWord
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (cuts : OperationalCloseCutPackage (fun n ↦ (env n).graph))
    (hnoBoth : ∀ n : Nat, (env n).graph ≠ .both)
    (k : Nat) (hgraph : (env (cuts.cuts k)).graph = .right)
    (root : BankControl A strategy hwin)
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcOnePairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).right () =
      some semanticMember)
    (hsender :
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBaseAt
          A strategy hwin initialTag env (cuts.cuts k)).1.1 =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightSenderAtPrefix
          A strategy hwin root family direction semanticMember hmember [])
    (hreceiver :
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBaseAt
          A strategy hwin initialTag env (cuts.cuts k)).1.2 =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightReceiverAtPrefix
          A strategy hwin root family direction semanticMember hmember false [])
    (j : Nat) (hj : j ≤ cuts.openLength k) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartWord
        A strategy hwin initialTag env (cuts.cuts k + j) =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPhysicalWord
        A strategy hwin root family direction semanticMember hmember false
          .first
          (fun t ↦
            ((env (cuts.cuts k + t)).inputTwo,
              (env (cuts.cuts k + t)).inputOne)) j := by
  let inputs : Nat → In₁ × In₂ := fun t ↦
    ((env (cuts.cuts k + t)).inputOne,
      (env (cuts.cuts k + t)).inputTwo)
  have hcurrent : (env (cuts.cuts k + j)).graph = .right := by
    by_cases hclose : j = cuts.openLength k
    · rw [hclose]
      have hclosing := cuts.closing_graph_eq k
      have hindex : cuts.cuts (k + 1) - 1 =
          cuts.cuts k + cuts.openLength k := by
        rw [cuts.step_eq]
        omega
      rw [hindex, hgraph] at hclosing
      exact hclosing
    · have hjOpen : j < cuts.openLength k := by omega
      exact (cuts.homogeneous k j hjOpen).trans hgraph
  have hout :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartReferenceOutputAt_rightCut_add_eq_pairOutput_frozenFirst
      A strategy hwin initialTag env cuts hnoBoth k j hgraph hj
  have hphysical :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPairOutput_eq_physicalWord
      A strategy hwin root family direction semanticMember hmember false []
        .first inputs j
  dsimp only at hout
  rw [hsender, hreceiver] at hout
  rw [hphysical] at hout
  have htrace :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartTraceWord_eq_referenceWord
      A strategy hwin initialTag env
  apply RoundRecord.eq_of_environment_eq_of_outputPair_eq
  · rw [profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartWord]
    rw [htrace]
    apply EnvironmentRound.eq_of_components
    · simp [
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPhysicalWord,
        pairedRightOmegaWord, rightRoundRecord, RoundRecord.environment,
        FinitePairedPhysicalController.LiteralCrossGraphTraceInvariant.referenceWord]
    · simp [
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPhysicalWord,
        pairedRightOmegaWord, rightRoundRecord, RoundRecord.environment,
        FinitePairedPhysicalController.LiteralCrossGraphTraceInvariant.referenceWord]
    · simp [
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPhysicalWord,
        pairedRightOmegaWord, rightRoundRecord, RoundRecord.environment]
      simpa [
        FinitePairedPhysicalController.LiteralCrossGraphTraceInvariant.referenceWord]
        using hcurrent
  · rw [profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartWord]
    rw [htrace]
    simpa [
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartReferenceOutputAt,
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPhysicalWord,
      inputs] using hout

/-- Strict-left mirror of pointwise cut-block reification. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_leftCut_round_eq_linkedPhysicalWord
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (cuts : OperationalCloseCutPackage (fun n ↦ (env n).graph))
    (hnoBoth : ∀ n : Nat, (env n).graph ≠ .both)
    (k : Nat) (hgraph : (env (cuts.cuts k)).graph = .left)
    (root : BankControl A strategy hwin)
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcTwoPairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).left () =
      some semanticMember)
    (hsender :
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBaseAt
          A strategy hwin initialTag env (cuts.cuts k)).2.1 =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftSenderAtPrefix
          A strategy hwin root family direction semanticMember hmember [])
    (hreceiver :
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBaseAt
          A strategy hwin initialTag env (cuts.cuts k)).2.2 =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftReceiverAtPrefix
          A strategy hwin root family direction semanticMember hmember false [])
    (j : Nat) (hj : j ≤ cuts.openLength k) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartWord
        A strategy hwin initialTag env (cuts.cuts k + j) =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPhysicalWord
        A strategy hwin root family direction semanticMember hmember false
          .first
          (fun t ↦
            ((env (cuts.cuts k + t)).inputOne,
              (env (cuts.cuts k + t)).inputTwo)) j := by
  let inputs : Nat → In₁ × In₂ := fun t ↦
    ((env (cuts.cuts k + t)).inputOne,
      (env (cuts.cuts k + t)).inputTwo)
  have hcurrent : (env (cuts.cuts k + j)).graph = .left := by
    by_cases hclose : j = cuts.openLength k
    · rw [hclose]
      have hclosing := cuts.closing_graph_eq k
      have hindex : cuts.cuts (k + 1) - 1 =
          cuts.cuts k + cuts.openLength k := by
        rw [cuts.step_eq]
        omega
      rw [hindex, hgraph] at hclosing
      exact hclosing
    · have hjOpen : j < cuts.openLength k := by omega
      exact (cuts.homogeneous k j hjOpen).trans hgraph
  have hout :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartReferenceOutputAt_leftCut_add_eq_pairOutput_frozenFirst
      A strategy hwin initialTag env cuts hnoBoth k j hgraph hj
  have hphysical :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPairOutput_eq_physicalWord
      A strategy hwin root family direction semanticMember hmember false []
        .first inputs j
  dsimp only at hout
  rw [hsender, hreceiver] at hout
  rw [hphysical] at hout
  have htrace :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartTraceWord_eq_referenceWord
      A strategy hwin initialTag env
  apply RoundRecord.eq_of_environment_eq_of_outputPair_eq
  · rw [profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartWord]
    rw [htrace]
    apply EnvironmentRound.eq_of_components
    · simp [
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPhysicalWord,
        pairedLeftOmegaWord, leftRoundRecord, RoundRecord.environment,
        FinitePairedPhysicalController.LiteralCrossGraphTraceInvariant.referenceWord]
    · simp [
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPhysicalWord,
        pairedLeftOmegaWord, leftRoundRecord, RoundRecord.environment,
        FinitePairedPhysicalController.LiteralCrossGraphTraceInvariant.referenceWord]
    · simp [
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPhysicalWord,
        pairedLeftOmegaWord, leftRoundRecord, RoundRecord.environment]
      simpa [
        FinitePairedPhysicalController.LiteralCrossGraphTraceInvariant.referenceWord]
        using hcurrent
  · rw [profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartWord]
    rw [htrace]
    simpa [
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartReferenceOutputAt,
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPhysicalWord,
      inputs] using hout

/-! ## Reification in the generic target-monitor vocabulary -/

/-- Right-cut rounds stated as the records consumed by the generic physical
target monitor. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_rightCut_round_eq_projectedPlayRecord
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (cuts : OperationalCloseCutPackage (fun n ↦ (env n).graph))
    (hnoBoth : ∀ n : Nat, (env n).graph ≠ .both)
    (k : Nat) (hgraph : (env (cuts.cuts k)).graph = .right)
    (root : BankControl A strategy hwin)
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcOnePairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).right () =
      some semanticMember)
    (hsender :
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBaseAt
          A strategy hwin initialTag env (cuts.cuts k)).1.1 =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightSenderAtPrefix
          A strategy hwin root family direction semanticMember hmember [])
    (hreceiver :
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBaseAt
          A strategy hwin initialTag env (cuts.cuts k)).1.2 =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightReceiverAtPrefix
          A strategy hwin root family direction semanticMember hmember false [])
    (j : Nat) (hj : j ≤ cuts.openLength k) :
    let tableEnv : Nat → In₂ × In₁ := fun t ↦
      ((env (cuts.cuts k + t)).inputTwo,
        (env (cuts.cuts k + t)).inputOne)
    let linkedPlay :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOfPlay
        A strategy hwin root family direction semanticMember hmember false
          tableEnv
    let play := BlockRecordMonitor.projectReceiverPlay
      (profiledRawJointHybridFinitePayloadRowExactRightReceiverProjection A)
        linkedPlay
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartWord
        A strategy hwin initialTag env (cuts.cuts k + j) =
      pairedRightRecordForRow .first
        (profiledRawJointTargetRightPhysicalLetter A (play j)) := by
  dsimp only
  rw [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_rightCut_round_eq_linkedPhysicalWord
      A strategy hwin initialTag env cuts hnoBoth k hgraph root family
        direction semanticMember hmember hsender hreceiver j hj]
  rw [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPhysicalLambda_blockWord
      A strategy hwin root family direction semanticMember hmember false
        (fun t ↦
          ((env (cuts.cuts k + t)).inputTwo,
            (env (cuts.cuts k + t)).inputOne)) j]
  rfl

/-- Left-cut mirror in target-monitor vocabulary. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_leftCut_round_eq_projectedPlayRecord
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (cuts : OperationalCloseCutPackage (fun n ↦ (env n).graph))
    (hnoBoth : ∀ n : Nat, (env n).graph ≠ .both)
    (k : Nat) (hgraph : (env (cuts.cuts k)).graph = .left)
    (root : BankControl A strategy hwin)
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcTwoPairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).left () =
      some semanticMember)
    (hsender :
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBaseAt
          A strategy hwin initialTag env (cuts.cuts k)).2.1 =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftSenderAtPrefix
          A strategy hwin root family direction semanticMember hmember [])
    (hreceiver :
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBaseAt
          A strategy hwin initialTag env (cuts.cuts k)).2.2 =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftReceiverAtPrefix
          A strategy hwin root family direction semanticMember hmember false [])
    (j : Nat) (hj : j ≤ cuts.openLength k) :
    let tableEnv : Nat → In₁ × In₂ := fun t ↦
      ((env (cuts.cuts k + t)).inputOne,
        (env (cuts.cuts k + t)).inputTwo)
    let linkedPlay :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOfPlay
        A strategy hwin root family direction semanticMember hmember false
          tableEnv
    let play := BlockRecordMonitor.projectReceiverPlay
      (profiledRawJointHybridFinitePayloadRowExactLeftReceiverProjection A)
        linkedPlay
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartWord
        A strategy hwin initialTag env (cuts.cuts k + j) =
      pairedLeftRecordForRow .first
        (profiledRawJointTargetLeftPhysicalLetter A (play j)) := by
  dsimp only
  rw [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_leftCut_round_eq_linkedPhysicalWord
      A strategy hwin initialTag env cuts hnoBoth k hgraph root family
        direction semanticMember hmember hsender hreceiver j hj]
  rw [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPhysicalLambda_blockWord
      A strategy hwin root family direction semanticMember hmember false
        (fun t ↦
          ((env (cuts.cuts k + t)).inputOne,
            (env (cuts.cuts k + t)).inputTwo)) j]
  rfl

/-! ## Exact physical slices and closing rounds -/

/-- The open prefix and closing round of a right operational block are the
literal prefix and close consumed by the projected target monitor. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_rightCut_slice_and_closing
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (cuts : OperationalCloseCutPackage (fun n ↦ (env n).graph))
    (hnoBoth : ∀ n : Nat, (env n).graph ≠ .both)
    (k : Nat) (hgraph : (env (cuts.cuts k)).graph = .right)
    (root : BankControl A strategy hwin)
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcOnePairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).right () =
      some semanticMember)
    (hsender :
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBaseAt
          A strategy hwin initialTag env (cuts.cuts k)).1.1 =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightSenderAtPrefix
          A strategy hwin root family direction semanticMember hmember [])
    (hreceiver :
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBaseAt
          A strategy hwin initialTag env (cuts.cuts k)).1.2 =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightReceiverAtPrefix
          A strategy hwin root family direction semanticMember hmember false []) :
    let tableEnv : Nat → In₂ × In₁ := fun t ↦
      ((env (cuts.cuts k + t)).inputTwo,
        (env (cuts.cuts k + t)).inputOne)
    let linkedPlay :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOfPlay
        A strategy hwin root family direction semanticMember hmember false
          tableEnv
    let play := BlockRecordMonitor.projectReceiverPlay
      (profiledRawJointHybridFinitePayloadRowExactRightReceiverProjection A)
        linkedPlay
    let block := profiledRawJointTargetRightPhysicalPrefixRecords A .first
      (omegaPrefix play (cuts.openLength k))
    omegaPrefix
          (OmegaWord.drop
            (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartWord
              A strategy hwin initialTag env) (cuts.cuts k)) block.length =
        block ∧
      OmegaWord.drop
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartWord
            A strategy hwin initialTag env) (cuts.cuts k) block.length =
        pairedRightRecordForRow .first
          (profiledRawJointTargetRightPhysicalLetter A
            (play (cuts.openLength k))) := by
  dsimp only
  constructor
  · apply List.ext_get
    · simp [profiledRawJointTargetRightPhysicalPrefixRecords, omegaPrefix]
    · intro j hjLeft hjRight
      rw [List.get_eq_getElem, List.get_eq_getElem]
      simp only [omegaPrefix, List.getElem_ofFn, OmegaWord.drop_apply,
        profiledRawJointTargetRightPhysicalPrefixRecords,
        List.getElem_map]
      exact
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_rightCut_round_eq_projectedPlayRecord
          A strategy hwin initialTag env cuts hnoBoth k hgraph root family
            direction semanticMember hmember hsender hreceiver j
              (by
                have hj : j < cuts.openLength k := by
                  simpa [profiledRawJointTargetRightPhysicalPrefixRecords,
                    omegaPrefix] using hjRight
                omega)
  · simp only [profiledRawJointTargetRightPhysicalPrefixRecords,
      List.length_map, omegaPrefix, List.length_ofFn, OmegaWord.drop_apply]
    exact
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_rightCut_round_eq_projectedPlayRecord
        A strategy hwin initialTag env cuts hnoBoth k hgraph root family
          direction semanticMember hmember hsender hreceiver
            (cuts.openLength k) (Nat.le_refl _)

/-- Left operational-block mirror. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_leftCut_slice_and_closing
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (cuts : OperationalCloseCutPackage (fun n ↦ (env n).graph))
    (hnoBoth : ∀ n : Nat, (env n).graph ≠ .both)
    (k : Nat) (hgraph : (env (cuts.cuts k)).graph = .left)
    (root : BankControl A strategy hwin)
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcTwoPairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).left () =
      some semanticMember)
    (hsender :
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBaseAt
          A strategy hwin initialTag env (cuts.cuts k)).2.1 =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftSenderAtPrefix
          A strategy hwin root family direction semanticMember hmember [])
    (hreceiver :
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBaseAt
          A strategy hwin initialTag env (cuts.cuts k)).2.2 =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftReceiverAtPrefix
          A strategy hwin root family direction semanticMember hmember false []) :
    let tableEnv : Nat → In₁ × In₂ := fun t ↦
      ((env (cuts.cuts k + t)).inputOne,
        (env (cuts.cuts k + t)).inputTwo)
    let linkedPlay :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOfPlay
        A strategy hwin root family direction semanticMember hmember false
          tableEnv
    let play := BlockRecordMonitor.projectReceiverPlay
      (profiledRawJointHybridFinitePayloadRowExactLeftReceiverProjection A)
        linkedPlay
    let block := profiledRawJointTargetLeftPhysicalPrefixRecords A .first
      (omegaPrefix play (cuts.openLength k))
    omegaPrefix
          (OmegaWord.drop
            (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartWord
              A strategy hwin initialTag env) (cuts.cuts k)) block.length =
        block ∧
      OmegaWord.drop
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartWord
            A strategy hwin initialTag env) (cuts.cuts k) block.length =
        pairedLeftRecordForRow .first
          (profiledRawJointTargetLeftPhysicalLetter A
            (play (cuts.openLength k))) := by
  dsimp only
  constructor
  · apply List.ext_get
    · simp [profiledRawJointTargetLeftPhysicalPrefixRecords, omegaPrefix]
    · intro j hjLeft hjRight
      rw [List.get_eq_getElem, List.get_eq_getElem]
      simp only [omegaPrefix, List.getElem_ofFn, OmegaWord.drop_apply,
        profiledRawJointTargetLeftPhysicalPrefixRecords,
        List.getElem_map]
      exact
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_leftCut_round_eq_projectedPlayRecord
          A strategy hwin initialTag env cuts hnoBoth k hgraph root family
            direction semanticMember hmember hsender hreceiver j
              (by
                have hj : j < cuts.openLength k := by
                  simpa [profiledRawJointTargetLeftPhysicalPrefixRecords,
                    omegaPrefix] using hjRight
                omega)
  · simp only [profiledRawJointTargetLeftPhysicalPrefixRecords,
      List.length_map, omegaPrefix, List.length_ofFn, OmegaWord.drop_apply]
    exact
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_leftCut_round_eq_projectedPlayRecord
        A strategy hwin initialTag env cuts hnoBoth k hgraph root family
          direction semanticMember hmember hsender hreceiver
            (cuts.openLength k) (Nat.le_refl _)

/-! ## State-and-priority packets -/

/-- Every checked target of a linked right play projects to a live left
slot.  This small extraction turns the target-parametric packet into an
existential cut packet. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOfPlay_targetSlot_exists
    (root : BankControl A strategy hwin)
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcOnePairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).right () =
      some semanticMember)
    (anchor : Bool) (tableEnv : Nat → In₂ × In₁)
    (n : Nat) (row : PairedEntryRow) :
    let linkedPlay :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOfPlay
        A strategy hwin root family direction semanticMember hmember anchor
          tableEnv
    let play := BlockRecordMonitor.projectReceiverPlay
      (profiledRawJointHybridFinitePayloadRowExactRightReceiverProjection A)
        linkedPlay
    ∃ slot : ProfiledRawLeftSlot A,
      profiledRawJointHybridFinitePayloadLinkedRightTargetProjection A
          ((play n).2.1.target row) = .inr (.inr slot) := by
  dsimp only
  let activation :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRightActivations
      A strategy hwin family direction semanticMember hmember anchor
  let descriptor :=
    profiledRawJointRightFinitePayloadLinkedSiblingDescriptorOf A activation
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
        strategy hwin root)
  let linkedPlay :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOfPlay
      A strategy hwin root family direction semanticMember hmember anchor
        tableEnv
  let play := BlockRecordMonitor.projectReceiverPlay
    (profiledRawJointHybridFinitePayloadRowExactRightReceiverProjection A)
      linkedPlay
  have hlinked :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOfPlay_wins
      A strategy hwin root family direction semanticMember hmember anchor
        tableEnv
  have hprojected :
      (profiledRawJointTargetRightBlockMonitor A
        (ProfiledRawJointHybridFinitePayloadLinkedTarget A
          (BankControl A strategy hwin))
        (profiledRawJointHybridFinitePayloadLinkedRightTargetProjection A)
        (profiledRawJointRightFinitePayloadLinkedSiblingAllowed A descriptor)
        descriptor.source).WinsPlay play := by
    exact
      (BlockRecordMonitor.comapReceiverOutput_wins_iff
        (profiledRawJointTargetRightBlockMonitor A
          (ProfiledRawJointHybridFinitePayloadLinkedTarget A
            (BankControl A strategy hwin))
          (profiledRawJointHybridFinitePayloadLinkedRightTargetProjection A)
          (profiledRawJointRightFinitePayloadLinkedSiblingAllowed A descriptor)
          descriptor.source)
        (profiledRawJointHybridFinitePayloadRowExactRightReceiverProjection A)
        linkedPlay).mp hlinked
  have hsafe := profiledRawJointTargetRight_targetsSafe_of_wins A
    (profiledRawJointHybridFinitePayloadLinkedRightTargetProjection A)
    (profiledRawJointRightFinitePayloadLinkedSiblingAllowed A descriptor)
    descriptor.source play hprojected n row
  let target :=
    profiledRawJointHybridFinitePayloadLinkedRightTargetProjection A
      ((play n).2.1.target row)
  have hexact := hsafe.1
  change erasePairedProfiledState A target = _ at hexact
  cases htarget : target with
  | inl sink =>
      simp [htarget, erasePairedProfiledState, pairedRightCloseTarget] at hexact
  | inr side =>
      cases side with
      | inl rightSlot =>
          simp [htarget, erasePairedProfiledState, pairedRightCloseTarget] at hexact
      | inr slot =>
          exact ⟨slot, by simpa [target] using htarget⟩

/-- Checked linked left targets project to live right slots. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOfPlay_targetSlot_exists
    (root : BankControl A strategy hwin)
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcTwoPairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).left () =
      some semanticMember)
    (anchor : Bool) (tableEnv : Nat → In₁ × In₂)
    (n : Nat) (row : PairedEntryRow) :
    let linkedPlay :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOfPlay
        A strategy hwin root family direction semanticMember hmember anchor
          tableEnv
    let play := BlockRecordMonitor.projectReceiverPlay
      (profiledRawJointHybridFinitePayloadRowExactLeftReceiverProjection A)
        linkedPlay
    ∃ slot : ProfiledRawRightSlot A,
      profiledRawJointHybridFinitePayloadLinkedLeftTargetProjection A
          ((play n).2.1.target row) = .inr (.inl slot) := by
  dsimp only
  let activation :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLeftActivations
      A strategy hwin family direction semanticMember hmember anchor
  let descriptor :=
    profiledRawJointLeftFinitePayloadLinkedSiblingDescriptorOf A activation
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
        strategy hwin root)
  let linkedPlay :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOfPlay
      A strategy hwin root family direction semanticMember hmember anchor
        tableEnv
  let play := BlockRecordMonitor.projectReceiverPlay
    (profiledRawJointHybridFinitePayloadRowExactLeftReceiverProjection A)
      linkedPlay
  have hlinked :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOfPlay_wins
      A strategy hwin root family direction semanticMember hmember anchor
        tableEnv
  have hprojected :
      (profiledRawJointTargetLeftBlockMonitor A
        (ProfiledRawJointHybridFinitePayloadLinkedTarget A
          (BankControl A strategy hwin))
        (profiledRawJointHybridFinitePayloadLinkedLeftTargetProjection A)
        (profiledRawJointLeftFinitePayloadLinkedSiblingAllowed A descriptor)
        descriptor.source).WinsPlay play := by
    exact
      (BlockRecordMonitor.comapReceiverOutput_wins_iff
        (profiledRawJointTargetLeftBlockMonitor A
          (ProfiledRawJointHybridFinitePayloadLinkedTarget A
            (BankControl A strategy hwin))
          (profiledRawJointHybridFinitePayloadLinkedLeftTargetProjection A)
          (profiledRawJointLeftFinitePayloadLinkedSiblingAllowed A descriptor)
          descriptor.source)
        (profiledRawJointHybridFinitePayloadRowExactLeftReceiverProjection A)
        linkedPlay).mp hlinked
  have hsafe := profiledRawJointTargetLeft_targetsSafe_of_wins A
    (profiledRawJointHybridFinitePayloadLinkedLeftTargetProjection A)
    (profiledRawJointLeftFinitePayloadLinkedSiblingAllowed A descriptor)
    descriptor.source play hprojected n row
  let target :=
    profiledRawJointHybridFinitePayloadLinkedLeftTargetProjection A
      ((play n).2.1.target row)
  have hexact := hsafe.1
  change erasePairedProfiledState A target = _ at hexact
  cases htarget : target with
  | inl sink =>
      simp [htarget, erasePairedProfiledState, pairedLeftCloseTarget] at hexact
  | inr side =>
      cases side with
      | inl slot =>
          exact ⟨slot, by simpa [target] using htarget⟩
      | inr leftSlot =>
          simp [htarget, erasePairedProfiledState, pairedLeftCloseTarget] at hexact

/-- A checked right target retains one exact semantic direction together
with its corresponding marked-bank payload. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOfPlay_targetRepresentation_exists
    (root : BankControl A strategy hwin)
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcOnePairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).right () =
      some semanticMember)
    (anchor : Bool) (tableEnv : Nat → In₂ × In₁)
    (n : Nat) (row : PairedEntryRow) :
    let activation :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankRightActivations
        A strategy hwin family direction semanticMember hmember anchor
    let linkedPlay :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOfPlay
        A strategy hwin root family direction semanticMember hmember anchor
          tableEnv
    let play := BlockRecordMonitor.projectReceiverPlay
      (profiledRawJointHybridFinitePayloadRowExactRightReceiverProjection A)
        linkedPlay
    ∃ past input,
      (play n).2.1.target row =
        (activation.target row past input,
          (row,
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
              strategy hwin root
                (.strict
                  (profiledRawJointUnitRightActualDirection
                    (In₁ := In₁) (In₂ := In₂) row past input)))) := by
  dsimp only
  let activation :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRightActivations
      A strategy hwin family direction semanticMember hmember anchor
  let descriptor :=
    profiledRawJointRightFinitePayloadLinkedSiblingDescriptorOf A activation
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
        strategy hwin root)
  let linkedPlay :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOfPlay
      A strategy hwin root family direction semanticMember hmember anchor
        tableEnv
  let play := BlockRecordMonitor.projectReceiverPlay
    (profiledRawJointHybridFinitePayloadRowExactRightReceiverProjection A)
      linkedPlay
  have hlinked :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOfPlay_wins
      A strategy hwin root family direction semanticMember hmember anchor
        tableEnv
  have hprojected :
      (profiledRawJointTargetRightBlockMonitor A
        (ProfiledRawJointHybridFinitePayloadLinkedTarget A
          (BankControl A strategy hwin))
        (profiledRawJointHybridFinitePayloadLinkedRightTargetProjection A)
        (profiledRawJointRightFinitePayloadLinkedSiblingAllowed A descriptor)
        descriptor.source).WinsPlay play := by
    exact
      (BlockRecordMonitor.comapReceiverOutput_wins_iff
        (profiledRawJointTargetRightBlockMonitor A
          (ProfiledRawJointHybridFinitePayloadLinkedTarget A
            (BankControl A strategy hwin))
          (profiledRawJointHybridFinitePayloadLinkedRightTargetProjection A)
          (profiledRawJointRightFinitePayloadLinkedSiblingAllowed A descriptor)
          descriptor.source)
        (profiledRawJointHybridFinitePayloadRowExactRightReceiverProjection A)
        linkedPlay).mp hlinked
  have hsafe := profiledRawJointTargetRight_targetsSafe_of_wins A
    (profiledRawJointHybridFinitePayloadLinkedRightTargetProjection A)
    (profiledRawJointRightFinitePayloadLinkedSiblingAllowed A descriptor)
    descriptor.source play hprojected n row
  have himage :
      ProfiledRawJointRightFinitePayloadLinkedTargetAllowed A activation
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
          strategy hwin root)
        ((play n).2.1.target row) :=
    (profiledRawJointRightFinitePayloadLinkedSiblingDescriptorOf_allowed_iff A
      activation
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
        strategy hwin root) _).mp hsafe.2
  rcases himage with ⟨witnessRow, past, input, htarget⟩
  have hrow :=
    profiledRawJointHybridFinitePayloadRowExactRightTarget_row A
      (linkedPlay n).2.1 row
  change profiledRawJointHybridFinitePayloadLinkedTargetRow A
      ((play n).2.1.target row) = row at hrow
  rw [htarget] at hrow
  change witnessRow = row at hrow
  subst witnessRow
  exact ⟨past, input, htarget⟩

/-- Left checked-target representation mirror. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOfPlay_targetRepresentation_exists
    (root : BankControl A strategy hwin)
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcTwoPairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).left () =
      some semanticMember)
    (anchor : Bool) (tableEnv : Nat → In₁ × In₂)
    (n : Nat) (row : PairedEntryRow) :
    let activation :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLeftActivations
        A strategy hwin family direction semanticMember hmember anchor
    let linkedPlay :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOfPlay
        A strategy hwin root family direction semanticMember hmember anchor
          tableEnv
    let play := BlockRecordMonitor.projectReceiverPlay
      (profiledRawJointHybridFinitePayloadRowExactLeftReceiverProjection A)
        linkedPlay
    ∃ past input,
      (play n).2.1.target row =
        (activation.target row past input,
          (row,
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
              strategy hwin root
                (.strict
                  (profiledRawJointUnitLeftActualDirection
                    (In₁ := In₁) (In₂ := In₂) row past input)))) := by
  dsimp only
  let activation :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLeftActivations
      A strategy hwin family direction semanticMember hmember anchor
  let descriptor :=
    profiledRawJointLeftFinitePayloadLinkedSiblingDescriptorOf A activation
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
        strategy hwin root)
  let linkedPlay :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOfPlay
      A strategy hwin root family direction semanticMember hmember anchor
        tableEnv
  let play := BlockRecordMonitor.projectReceiverPlay
    (profiledRawJointHybridFinitePayloadRowExactLeftReceiverProjection A)
      linkedPlay
  have hlinked :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOfPlay_wins
      A strategy hwin root family direction semanticMember hmember anchor
        tableEnv
  have hprojected :
      (profiledRawJointTargetLeftBlockMonitor A
        (ProfiledRawJointHybridFinitePayloadLinkedTarget A
          (BankControl A strategy hwin))
        (profiledRawJointHybridFinitePayloadLinkedLeftTargetProjection A)
        (profiledRawJointLeftFinitePayloadLinkedSiblingAllowed A descriptor)
        descriptor.source).WinsPlay play := by
    exact
      (BlockRecordMonitor.comapReceiverOutput_wins_iff
        (profiledRawJointTargetLeftBlockMonitor A
          (ProfiledRawJointHybridFinitePayloadLinkedTarget A
            (BankControl A strategy hwin))
          (profiledRawJointHybridFinitePayloadLinkedLeftTargetProjection A)
          (profiledRawJointLeftFinitePayloadLinkedSiblingAllowed A descriptor)
          descriptor.source)
        (profiledRawJointHybridFinitePayloadRowExactLeftReceiverProjection A)
        linkedPlay).mp hlinked
  have hsafe := profiledRawJointTargetLeft_targetsSafe_of_wins A
    (profiledRawJointHybridFinitePayloadLinkedLeftTargetProjection A)
    (profiledRawJointLeftFinitePayloadLinkedSiblingAllowed A descriptor)
    descriptor.source play hprojected n row
  have himage :
      ProfiledRawJointLeftFinitePayloadLinkedTargetAllowed A activation
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
          strategy hwin root)
        ((play n).2.1.target row) :=
    (profiledRawJointLeftFinitePayloadLinkedSiblingDescriptorOf_allowed_iff A
      activation
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
        strategy hwin root) _).mp hsafe.2
  rcases himage with ⟨witnessRow, past, input, htarget⟩
  have hrow :=
    profiledRawJointHybridFinitePayloadRowExactLeftTarget_row A
      (linkedPlay n).2.1 row
  change profiledRawJointHybridFinitePayloadLinkedTargetRow A
      ((play n).2.1.target row) = row at hrow
  rw [htarget] at hrow
  change witnessRow = row at hrow
  subst witnessRow
  exact ⟨past, input, htarget⟩

/-- A represented fresh right cut transports an aligned physical DPA state
to its fresh left target and charges the block with that target's root
priority. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_rightCut_physicalPacket
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (cuts : OperationalCloseCutPackage (fun n ↦ (env n).graph))
    (hnoBoth : ∀ n : Nat, (env n).graph ≠ .both)
    (k : Nat) (hgraph : (env (cuts.cuts k)).graph = .right)
    (root : BankControl A strategy hwin)
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcOnePairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).right () =
      some semanticMember)
    (hsender :
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBaseAt
          A strategy hwin initialTag env (cuts.cuts k)).1.1 =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightSenderAtPrefix
          A strategy hwin root family direction semanticMember hmember [])
    (hreceiver :
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBaseAt
          A strategy hwin initialTag env (cuts.cuts k)).1.2 =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightReceiverAtPrefix
          A strategy hwin root family direction semanticMember hmember false [])
    (physicalState : A.State) :
    let activation :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankRightActivations
        A strategy hwin family direction semanticMember hmember false
    let descriptor :=
      profiledRawJointRightFinitePayloadLinkedSiblingDescriptorOf A activation
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
          strategy hwin root)
    let tableEnv : Nat → In₂ × In₁ := fun t ↦
      ((env (cuts.cuts k + t)).inputTwo,
        (env (cuts.cuts k + t)).inputOne)
    let linkedPlay :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOfPlay
        A strategy hwin root family direction semanticMember hmember false
          tableEnv
    let play := BlockRecordMonitor.projectReceiverPlay
      (profiledRawJointHybridFinitePayloadRowExactRightReceiverProjection A)
        linkedPlay
    let word :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartWord
        A strategy hwin initialTag env
    A.runFrom physicalState word (cuts.cuts k) =
        pairedCodeStateForRow A .first descriptor.source.1.1 →
      ∀ slot : ProfiledRawLeftSlot A,
        profiledRawJointHybridFinitePayloadLinkedRightTargetProjection A
            ((play (cuts.openLength k)).2.1.target .first) =
          .inr (.inr slot) →
        cutBlockMin
              (fun j ↦ A.priority (A.runFrom physicalState word j))
              cuts.cuts k =
            profiledRawJointThreadRootPriority A (.inr slot) ∧
          A.runFrom physicalState word (cuts.cuts (k + 1)) =
            pairedCodeStateForRow A .first slot.1.1 := by
  dsimp only
  intro hstate slot htarget
  let activation :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRightActivations
      A strategy hwin family direction semanticMember hmember false
  let descriptor :=
    profiledRawJointRightFinitePayloadLinkedSiblingDescriptorOf A activation
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
        strategy hwin root)
  let tableEnv : Nat → In₂ × In₁ := fun t ↦
    ((env (cuts.cuts k + t)).inputTwo,
      (env (cuts.cuts k + t)).inputOne)
  let linkedPlay :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOfPlay
      A strategy hwin root family direction semanticMember hmember false
        tableEnv
  let play := BlockRecordMonitor.projectReceiverPlay
    (profiledRawJointHybridFinitePayloadRowExactRightReceiverProjection A)
      linkedPlay
  let word :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartWord
      A strategy hwin initialTag env
  have hlinked :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOfPlay_wins
      A strategy hwin root family direction semanticMember hmember false
        tableEnv
  have hprojected :
      (profiledRawJointTargetRightBlockMonitor A
        (ProfiledRawJointHybridFinitePayloadLinkedTarget A
          (BankControl A strategy hwin))
        (profiledRawJointHybridFinitePayloadLinkedRightTargetProjection A)
        (profiledRawJointRightFinitePayloadLinkedSiblingAllowed A descriptor)
        descriptor.source).WinsPlay play := by
    exact
      (BlockRecordMonitor.comapReceiverOutput_wins_iff
        (profiledRawJointTargetRightBlockMonitor A
          (ProfiledRawJointHybridFinitePayloadLinkedTarget A
            (BankControl A strategy hwin))
          (profiledRawJointHybridFinitePayloadLinkedRightTargetProjection A)
          (profiledRawJointRightFinitePayloadLinkedSiblingAllowed A descriptor)
          descriptor.source)
        (profiledRawJointHybridFinitePayloadRowExactRightReceiverProjection A)
        linkedPlay).mp hlinked
  have halign :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_rightCut_slice_and_closing
      A strategy hwin initialTag env cuts hnoBoth k hgraph root family
        direction semanticMember hmember hsender hreceiver
  have hlength :
      (profiledRawJointTargetRightPhysicalPrefixRecords A .first
        (omegaPrefix play (cuts.openLength k))).length =
          cuts.cuts (k + 1) - cuts.cuts k - 1 := by
    simp only [profiledRawJointTargetRightPhysicalPrefixRecords,
      List.length_map, omegaPrefix, List.length_ofFn]
    rw [cuts.step_eq]
    omega
  apply
    profiledRawJointTargetRight_memberCutPacket_of_wins A
      (profiledRawJointHybridFinitePayloadLinkedRightTargetProjection A)
      (profiledRawJointRightFinitePayloadLinkedSiblingAllowed A descriptor)
      descriptor.source play hprojected (cuts.openLength k) .first slot
        htarget false physicalState word cuts.cuts k
  · exact cuts.cuts_strictMono (Nat.lt_succ_self k)
  · simpa [descriptor, activation, word] using hstate
  · exact hlength
  · simpa [play, linkedPlay, word] using halign.1
  · simpa [play, linkedPlay, word] using halign.2

/-- Fresh left-cut mirror of the physical state-and-priority packet. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_leftCut_physicalPacket
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (cuts : OperationalCloseCutPackage (fun n ↦ (env n).graph))
    (hnoBoth : ∀ n : Nat, (env n).graph ≠ .both)
    (k : Nat) (hgraph : (env (cuts.cuts k)).graph = .left)
    (root : BankControl A strategy hwin)
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcTwoPairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).left () =
      some semanticMember)
    (hsender :
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBaseAt
          A strategy hwin initialTag env (cuts.cuts k)).2.1 =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftSenderAtPrefix
          A strategy hwin root family direction semanticMember hmember [])
    (hreceiver :
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBaseAt
          A strategy hwin initialTag env (cuts.cuts k)).2.2 =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftReceiverAtPrefix
          A strategy hwin root family direction semanticMember hmember false [])
    (physicalState : A.State) :
    let activation :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLeftActivations
        A strategy hwin family direction semanticMember hmember false
    let descriptor :=
      profiledRawJointLeftFinitePayloadLinkedSiblingDescriptorOf A activation
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
          strategy hwin root)
    let tableEnv : Nat → In₁ × In₂ := fun t ↦
      ((env (cuts.cuts k + t)).inputOne,
        (env (cuts.cuts k + t)).inputTwo)
    let linkedPlay :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOfPlay
        A strategy hwin root family direction semanticMember hmember false
          tableEnv
    let play := BlockRecordMonitor.projectReceiverPlay
      (profiledRawJointHybridFinitePayloadRowExactLeftReceiverProjection A)
        linkedPlay
    let word :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartWord
        A strategy hwin initialTag env
    A.runFrom physicalState word (cuts.cuts k) =
        pairedCodeStateForRow A .first descriptor.source.1.1 →
      ∀ slot : ProfiledRawRightSlot A,
        profiledRawJointHybridFinitePayloadLinkedLeftTargetProjection A
            ((play (cuts.openLength k)).2.1.target .first) =
          .inr (.inl slot) →
        cutBlockMin
              (fun j ↦ A.priority (A.runFrom physicalState word j))
              cuts.cuts k =
            profiledRawJointThreadRootPriority A (.inl slot) ∧
          A.runFrom physicalState word (cuts.cuts (k + 1)) =
            pairedCodeStateForRow A .first slot.1.1 := by
  dsimp only
  intro hstate slot htarget
  let activation :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLeftActivations
      A strategy hwin family direction semanticMember hmember false
  let descriptor :=
    profiledRawJointLeftFinitePayloadLinkedSiblingDescriptorOf A activation
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
        strategy hwin root)
  let tableEnv : Nat → In₁ × In₂ := fun t ↦
    ((env (cuts.cuts k + t)).inputOne,
      (env (cuts.cuts k + t)).inputTwo)
  let linkedPlay :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOfPlay
      A strategy hwin root family direction semanticMember hmember false
        tableEnv
  let play := BlockRecordMonitor.projectReceiverPlay
    (profiledRawJointHybridFinitePayloadRowExactLeftReceiverProjection A)
      linkedPlay
  let word :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartWord
      A strategy hwin initialTag env
  have hlinked :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOfPlay_wins
      A strategy hwin root family direction semanticMember hmember false
        tableEnv
  have hprojected :
      (profiledRawJointTargetLeftBlockMonitor A
        (ProfiledRawJointHybridFinitePayloadLinkedTarget A
          (BankControl A strategy hwin))
        (profiledRawJointHybridFinitePayloadLinkedLeftTargetProjection A)
        (profiledRawJointLeftFinitePayloadLinkedSiblingAllowed A descriptor)
        descriptor.source).WinsPlay play := by
    exact
      (BlockRecordMonitor.comapReceiverOutput_wins_iff
        (profiledRawJointTargetLeftBlockMonitor A
          (ProfiledRawJointHybridFinitePayloadLinkedTarget A
            (BankControl A strategy hwin))
          (profiledRawJointHybridFinitePayloadLinkedLeftTargetProjection A)
          (profiledRawJointLeftFinitePayloadLinkedSiblingAllowed A descriptor)
          descriptor.source)
        (profiledRawJointHybridFinitePayloadRowExactLeftReceiverProjection A)
        linkedPlay).mp hlinked
  have halign :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_leftCut_slice_and_closing
      A strategy hwin initialTag env cuts hnoBoth k hgraph root family
        direction semanticMember hmember hsender hreceiver
  have hlength :
      (profiledRawJointTargetLeftPhysicalPrefixRecords A .first
        (omegaPrefix play (cuts.openLength k))).length =
          cuts.cuts (k + 1) - cuts.cuts k - 1 := by
    simp only [profiledRawJointTargetLeftPhysicalPrefixRecords,
      List.length_map, omegaPrefix, List.length_ofFn]
    rw [cuts.step_eq]
    omega
  apply
    profiledRawJointTargetLeft_memberCutPacket_of_wins A
      (profiledRawJointHybridFinitePayloadLinkedLeftTargetProjection A)
      (profiledRawJointLeftFinitePayloadLinkedSiblingAllowed A descriptor)
      descriptor.source play hprojected (cuts.openLength k) .first slot
        htarget false physicalState word cuts.cuts k
  · exact cuts.cuts_strictMono (Nat.lt_succ_self k)
  · simpa [descriptor, activation, word] using hstate
  · exact hlength
  · simpa [play, linkedPlay, word] using halign.1
  · simpa [play, linkedPlay, word] using halign.2

/-! ## Exact payload handoff at the following cut -/

/-- The payload carried by the closing target of a strict-right cut is
literally the authoritative parent installed at the following operational
cut. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_rightCut_targetPayload_eq_nextParent
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (cuts : OperationalCloseCutPackage (fun n ↦ (env n).graph))
    (hnoBoth : ∀ n : Nat, (env n).graph ≠ .both)
    (k : Nat) (hgraph : (env (cuts.cuts k)).graph = .right)
    (root : BankControl A strategy hwin)
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcOnePairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).right () =
      some semanticMember)
    (hsender :
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBaseAt
          A strategy hwin initialTag env (cuts.cuts k)).1.1 =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightSenderAtPrefix
          A strategy hwin root family direction semanticMember hmember [])
    (hreceiver :
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBaseAt
          A strategy hwin initialTag env (cuts.cuts k)).1.2 =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightReceiverAtPrefix
          A strategy hwin root family direction semanticMember hmember false []) :
    let tableEnv : Nat → In₂ × In₁ := fun t ↦
      ((env (cuts.cuts k + t)).inputTwo,
        (env (cuts.cuts k + t)).inputOne)
    let linkedPlay :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOfPlay
        A strategy hwin root family direction semanticMember hmember false
          tableEnv
    let play := BlockRecordMonitor.projectReceiverPlay
      (profiledRawJointHybridFinitePayloadRowExactRightReceiverProjection A)
        linkedPlay
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartParentAt
        A strategy hwin initialTag env (cuts.cuts (k + 1)) =
      profiledRawJointHybridFinitePayloadLinkedTargetPayload A
        ((play (cuts.openLength k)).2.1.target .first) := by
  dsimp only
  let start := cuts.cuts k
  let n := cuts.openLength k
  let inputs : Nat → In₁ × In₂ := fun t ↦
    ((env (start + t)).inputOne, (env (start + t)).inputTwo)
  let tableEnv : Nat → In₂ × In₁ := fun t ↦
    ((env (start + t)).inputTwo, (env (start + t)).inputOne)
  let linkedPlay :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOfPlay
      A strategy hwin root family direction semanticMember hmember false
        tableEnv
  let play := BlockRecordMonitor.projectReceiverPlay
    (profiledRawJointHybridFinitePayloadRowExactRightReceiverProjection A)
      linkedPlay
  have hhomogeneous : ∀ t : Nat, t < n →
      (env (start + t)).graph = .right := by
    intro t ht
    exact (cuts.homogeneous k t ht).trans hgraph
  have hstart :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBlindBaseAt_cut_sender
      A strategy hwin initialTag env cuts hnoBoth k hgraph
  change
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBlindBaseAt
        A strategy hwin initialTag env start).1.1 =
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBaseAt
        A strategy hwin initialTag env start).1.1 at hstart
  have hrun :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightPairRun_eq_operational
      A strategy hwin initialTag env hnoBoth start n hstart hhomogeneous
  dsimp only at hrun
  rw [hsender, hreceiver,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPairRun_eq_atPrefix]
      at hrun
  simp only [List.nil_append] at hrun
  have hreceiverClosing := congrArg Prod.snd hrun
  have hbridge :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightReceiverAtPrefix_payload_eq_moveOfPlay
      A strategy hwin root family direction semanticMember hmember false
        (omegaPrefix tableEnv n) (tableEnv n) tableEnv
        (by simp [omegaPrefix]) (by simp [omegaPrefix]) .first
  have hactualPayload :
      profiledRawJointHybridFinitePayloadLinkedTargetPayload A
          (((profiledRawJointRightFinitePayloadLiteralPrefixReceiverRecv A
            (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBaseAt
              A strategy hwin initialTag env (start + n)).1.2
            (env (start + n)).inputTwo
            (env (start + n)).inputOne).1.target .first).1) =
        profiledRawJointHybridFinitePayloadLinkedTargetPayload A
          ((play n).2.1.target .first) := by
    rw [hreceiverClosing]
    simpa [tableEnv, linkedPlay, play, omegaPrefix] using hbridge
  have hclosingGraph : (env (start + n)).graph = .right := by
    have hclosing := cuts.closing_graph_eq k
    have hindex : cuts.cuts (k + 1) - 1 = start + n := by
      dsimp only [start, n]
      rw [cuts.step_eq]
      omega
    rw [hindex, hgraph] at hclosing
    exact hclosing
  let fallback :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
      A strategy hwin initialTag
  let pair :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt
      A strategy hwin initialTag env (start + n)
  let selectedOne :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
      A strategy hwin fallback.1 pair.1
  let selectedTwo :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
      A strategy hwin fallback.2 pair.2
  let base :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRightBase
      A strategy hwin selectedOne selectedTwo
  rw [cuts.step_eq]
  rw [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartParentAt_succ_of_right
      A strategy hwin initialTag env (start + n) hclosingGraph]
  change
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartReceivedTwo
      A strategy hwin fallback pair.2 (env (start + n)).inputTwo pair.1
        (env (start + n)).inputOne).child A strategy hwin = _
  simpa only [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartReceivedTwo,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRetainedRecvTwo,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSelectedTwoAt,
    selectedTwo, selectedOne, base, start, n] using hactualPayload

/-- Strict-left mirror of the exact closing-target payload handoff. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_leftCut_targetPayload_eq_nextParent
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (cuts : OperationalCloseCutPackage (fun n ↦ (env n).graph))
    (hnoBoth : ∀ n : Nat, (env n).graph ≠ .both)
    (k : Nat) (hgraph : (env (cuts.cuts k)).graph = .left)
    (root : BankControl A strategy hwin)
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcTwoPairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).left () =
      some semanticMember)
    (hsender :
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBaseAt
          A strategy hwin initialTag env (cuts.cuts k)).2.1 =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftSenderAtPrefix
          A strategy hwin root family direction semanticMember hmember [])
    (hreceiver :
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBaseAt
          A strategy hwin initialTag env (cuts.cuts k)).2.2 =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftReceiverAtPrefix
          A strategy hwin root family direction semanticMember hmember false []) :
    let tableEnv : Nat → In₁ × In₂ := fun t ↦
      ((env (cuts.cuts k + t)).inputOne,
        (env (cuts.cuts k + t)).inputTwo)
    let linkedPlay :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOfPlay
        A strategy hwin root family direction semanticMember hmember false
          tableEnv
    let play := BlockRecordMonitor.projectReceiverPlay
      (profiledRawJointHybridFinitePayloadRowExactLeftReceiverProjection A)
        linkedPlay
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartParentAt
        A strategy hwin initialTag env (cuts.cuts (k + 1)) =
      profiledRawJointHybridFinitePayloadLinkedTargetPayload A
        ((play (cuts.openLength k)).2.1.target .first) := by
  dsimp only
  let start := cuts.cuts k
  let n := cuts.openLength k
  let inputs : Nat → In₁ × In₂ := fun t ↦
    ((env (start + t)).inputOne, (env (start + t)).inputTwo)
  let tableEnv : Nat → In₁ × In₂ := fun t ↦
    ((env (start + t)).inputOne, (env (start + t)).inputTwo)
  let linkedPlay :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOfPlay
      A strategy hwin root family direction semanticMember hmember false
        tableEnv
  let play := BlockRecordMonitor.projectReceiverPlay
    (profiledRawJointHybridFinitePayloadRowExactLeftReceiverProjection A)
      linkedPlay
  have hhomogeneous : ∀ t : Nat, t < n →
      (env (start + t)).graph = .left := by
    intro t ht
    exact (cuts.homogeneous k t ht).trans hgraph
  have hstart :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBlindBaseAt_cut_sender
      A strategy hwin initialTag env cuts hnoBoth k hgraph
  change
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBlindBaseAt
        A strategy hwin initialTag env start).2.1 =
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBaseAt
        A strategy hwin initialTag env start).2.1 at hstart
  have hrun :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftPairRun_eq_operational
      A strategy hwin initialTag env hnoBoth start n hstart hhomogeneous
  dsimp only at hrun
  rw [hsender, hreceiver,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPairRun_eq_atPrefix]
      at hrun
  simp only [List.nil_append] at hrun
  have hreceiverClosing := congrArg Prod.snd hrun
  have hbridge :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftReceiverAtPrefix_payload_eq_moveOfPlay
      A strategy hwin root family direction semanticMember hmember false
        (omegaPrefix tableEnv n) (tableEnv n) tableEnv
        (by simp [omegaPrefix]) (by simp [omegaPrefix]) .first
  have hactualPayload :
      profiledRawJointHybridFinitePayloadLinkedTargetPayload A
          (((profiledRawJointLeftFinitePayloadLiteralPrefixReceiverRecv A
            (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBaseAt
              A strategy hwin initialTag env (start + n)).2.2
            (env (start + n)).inputOne
            (env (start + n)).inputTwo).1.target .first).1) =
        profiledRawJointHybridFinitePayloadLinkedTargetPayload A
          ((play n).2.1.target .first) := by
    rw [hreceiverClosing]
    simpa [tableEnv, linkedPlay, play, omegaPrefix] using hbridge
  have hclosingGraph : (env (start + n)).graph = .left := by
    have hclosing := cuts.closing_graph_eq k
    have hindex : cuts.cuts (k + 1) - 1 = start + n := by
      dsimp only [start, n]
      rw [cuts.step_eq]
      omega
    rw [hindex, hgraph] at hclosing
    exact hclosing
  let fallback :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
      A strategy hwin initialTag
  let pair :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt
      A strategy hwin initialTag env (start + n)
  let selectedOne :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne
      A strategy hwin fallback.1 pair.1
  let selectedTwo :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo
      A strategy hwin fallback.2 pair.2
  let base :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartLeftBase
      A strategy hwin selectedOne selectedTwo
  rw [cuts.step_eq]
  rw [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartParentAt_succ_of_left
      A strategy hwin initialTag env (start + n) hclosingGraph]
  change
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartReceivedOne
      A strategy hwin fallback pair.1 (env (start + n)).inputOne pair.2
        (env (start + n)).inputTwo).child A strategy hwin = _
  simpa only [
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartReceivedOne,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartRetainedRecvOne,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSelectedOneAt,
    selectedTwo, selectedOne, base, start, n] using hactualPayload

/-! ## Fresh operational-cut wrappers -/

/-- At a ready strict-right cut, alignment with the source stored by the
executable sender is enough to obtain an existential next-cut packet.  No
semantic representative, target slot, or physical slice is supplied by the
caller. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_rightCut_freshPhysicalPacket
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (cuts : OperationalCloseCutPackage (fun n ↦ (env n).graph))
    (hnoBoth : ∀ n : Nat, (env n).graph ≠ .both)
    (k : Nat) (hgraph : (env (cuts.cuts k)).graph = .right)
    (hready :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightRootReady
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartParentAt
            A strategy hwin initialTag env (cuts.cuts k)))
    (physicalState : A.State)
    (hstate :
      A.runFrom physicalState
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartWord
            A strategy hwin initialTag env) (cuts.cuts k) =
        pairedCodeStateForRow A .first
          (profiledRawJointRightFinitePayloadLiteralPrefixSenderSource
            A strategy hwin
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBaseAt
                A strategy hwin initialTag env (cuts.cuts k)).1.1 false).1.1) :
    ∃ slot : ProfiledRawLeftSlot A,
      cutBlockMin
            (fun j ↦ A.priority
              (A.runFrom physicalState
                (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartWord
                  A strategy hwin initialTag env) j))
            cuts.cuts k =
          profiledRawJointThreadRootPriority A (.inr slot) ∧
        A.runFrom physicalState
            (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartWord
              A strategy hwin initialTag env) (cuts.cuts (k + 1)) =
          pairedCodeStateForRow A .first slot.1.1 := by
  let root :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartParentAt
      A strategy hwin initialTag env (cuts.cuts k)
  rcases
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightCut_freshOccurrence
        A strategy hwin initialTag env cuts hnoBoth k hgraph hready with
    ⟨family, direction, semanticMember, hmember, hsender, hreceiver⟩
  let activation :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRightActivations
      A strategy hwin family direction semanticMember hmember false
  let descriptor :=
    profiledRawJointRightFinitePayloadLinkedSiblingDescriptorOf A activation
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
        strategy hwin root)
  let tableEnv : Nat → In₂ × In₁ := fun t ↦
    ((env (cuts.cuts k + t)).inputTwo,
      (env (cuts.cuts k + t)).inputOne)
  have hsource :
      descriptor.source =
        profiledRawJointRightFinitePayloadLiteralPrefixSenderSource
          A strategy hwin
            (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBaseAt
              A strategy hwin initialTag env (cuts.cuts k)).1.1 false := by
    rw [hsender]
    simp [descriptor, activation,
      profiledRawJointRightFinitePayloadLinkedSiblingDescriptorOf]
  have hstate' :
      A.runFrom physicalState
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartWord
            A strategy hwin initialTag env) (cuts.cuts k) =
        pairedCodeStateForRow A .first descriptor.source.1.1 := by
    rw [hsource]
    exact hstate
  obtain ⟨slot, htarget⟩ :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOfPlay_targetSlot_exists
      A strategy hwin root family direction semanticMember hmember false
        tableEnv (cuts.openLength k) .first
  refine ⟨slot, ?_⟩
  exact
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_rightCut_physicalPacket
      A strategy hwin initialTag env cuts hnoBoth k hgraph root family
        direction semanticMember hmember hsender hreceiver physicalState
          hstate' slot htarget

/-- Ready strict-left mirror. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_leftCut_freshPhysicalPacket
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (cuts : OperationalCloseCutPackage (fun n ↦ (env n).graph))
    (hnoBoth : ∀ n : Nat, (env n).graph ≠ .both)
    (k : Nat) (hgraph : (env (cuts.cuts k)).graph = .left)
    (hready :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftRootReady
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartParentAt
            A strategy hwin initialTag env (cuts.cuts k)))
    (physicalState : A.State)
    (hstate :
      A.runFrom physicalState
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartWord
            A strategy hwin initialTag env) (cuts.cuts k) =
        pairedCodeStateForRow A .first
          (profiledRawJointLeftFinitePayloadLiteralPrefixSenderSource
            A strategy hwin
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBaseAt
                A strategy hwin initialTag env (cuts.cuts k)).2.1 false).1.1) :
    ∃ slot : ProfiledRawRightSlot A,
      cutBlockMin
            (fun j ↦ A.priority
              (A.runFrom physicalState
                (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartWord
                  A strategy hwin initialTag env) j))
            cuts.cuts k =
          profiledRawJointThreadRootPriority A (.inl slot) ∧
        A.runFrom physicalState
            (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartWord
              A strategy hwin initialTag env) (cuts.cuts (k + 1)) =
          pairedCodeStateForRow A .first slot.1.1 := by
  let root :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartParentAt
      A strategy hwin initialTag env (cuts.cuts k)
  rcases
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftCut_freshOccurrence
        A strategy hwin initialTag env cuts hnoBoth k hgraph hready with
    ⟨family, direction, semanticMember, hmember, hsender, hreceiver⟩
  let activation :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLeftActivations
      A strategy hwin family direction semanticMember hmember false
  let descriptor :=
    profiledRawJointLeftFinitePayloadLinkedSiblingDescriptorOf A activation
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
        strategy hwin root)
  let tableEnv : Nat → In₁ × In₂ := fun t ↦
    ((env (cuts.cuts k + t)).inputOne,
      (env (cuts.cuts k + t)).inputTwo)
  have hsource :
      descriptor.source =
        profiledRawJointLeftFinitePayloadLiteralPrefixSenderSource
          A strategy hwin
            (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBaseAt
              A strategy hwin initialTag env (cuts.cuts k)).2.1 false := by
    rw [hsender]
    simp [descriptor, activation,
      profiledRawJointLeftFinitePayloadLinkedSiblingDescriptorOf]
  have hstate' :
      A.runFrom physicalState
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartWord
            A strategy hwin initialTag env) (cuts.cuts k) =
        pairedCodeStateForRow A .first descriptor.source.1.1 := by
    rw [hsource]
    exact hstate
  obtain ⟨slot, htarget⟩ :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOfPlay_targetSlot_exists
      A strategy hwin root family direction semanticMember hmember false
        tableEnv (cuts.openLength k) .first
  refine ⟨slot, ?_⟩
  exact
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_leftCut_physicalPacket
      A strategy hwin initialTag env cuts hnoBoth k hgraph root family
        direction semanticMember hmember hsender hreceiver physicalState
          hstate' slot htarget

/-! ## Complete local handoff packages -/

/-- A ready right cut exposes one concrete checked target which simultaneously
determines the next authoritative bank parent, the exact block priority, the
next physical DPA state, and a ready left root. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_rightCut_freshPhysicalHandoff
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (cuts : OperationalCloseCutPackage (fun n ↦ (env n).graph))
    (hnoBoth : ∀ n : Nat, (env n).graph ≠ .both)
    (k : Nat) (hgraph : (env (cuts.cuts k)).graph = .right)
    (hready :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightRootReady
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartParentAt
            A strategy hwin initialTag env (cuts.cuts k)))
    (physicalState : A.State)
    (hstate :
      A.runFrom physicalState
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartWord
            A strategy hwin initialTag env) (cuts.cuts k) =
        pairedCodeStateForRow A .first
          (profiledRawJointRightFinitePayloadLiteralPrefixSenderSource
            A strategy hwin
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBaseAt
                A strategy hwin initialTag env (cuts.cuts k)).1.1 false).1.1) :
    ∃ target : ProfiledRawJointHybridFinitePayloadLinkedTarget A
        (BankControl A strategy hwin),
      ∃ slot : ProfiledRawLeftSlot A,
        profiledRawJointHybridFinitePayloadLinkedRightTargetProjection A
            target = .inr (.inr slot) ∧
          profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartParentAt
              A strategy hwin initialTag env (cuts.cuts (k + 1)) =
            profiledRawJointHybridFinitePayloadLinkedTargetPayload A target ∧
          cutBlockMin
                (fun j ↦ A.priority
                  (A.runFrom physicalState
                    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartWord
                      A strategy hwin initialTag env) j))
                cuts.cuts k =
              profiledRawJointThreadRootPriority A (.inr slot) ∧
          A.runFrom physicalState
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartWord
                A strategy hwin initialTag env) (cuts.cuts (k + 1)) =
            pairedCodeStateForRow A .first slot.1.1 ∧
          ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftRootReady
            A strategy hwin
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartParentAt
                A strategy hwin initialTag env (cuts.cuts (k + 1))) ∧
          profiledRawJointLeftFinitePayloadLiteralPrefixSenderSource
              A strategy hwin
                (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBaseAt
                  A strategy hwin initialTag env (cuts.cuts (k + 1))).2.1
              false = slot := by
  let root :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartParentAt
      A strategy hwin initialTag env (cuts.cuts k)
  rcases
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_rightCut_freshAlignedOccurrence
        A strategy hwin initialTag env cuts hnoBoth k hgraph hready with
    ⟨family, direction, semanticMember, hmember, hsender, hreceiver,
      hchildAligned⟩
  let activation :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRightActivations
      A strategy hwin family direction semanticMember hmember false
  let descriptor :=
    profiledRawJointRightFinitePayloadLinkedSiblingDescriptorOf A activation
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
        strategy hwin root)
  let tableEnv : Nat → In₂ × In₁ := fun t ↦
    ((env (cuts.cuts k + t)).inputTwo,
      (env (cuts.cuts k + t)).inputOne)
  let linkedPlay :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOfPlay
      A strategy hwin root family direction semanticMember hmember false
        tableEnv
  let play := BlockRecordMonitor.projectReceiverPlay
    (profiledRawJointHybridFinitePayloadRowExactRightReceiverProjection A)
      linkedPlay
  let target := ((play (cuts.openLength k)).2.1.target .first)
  obtain ⟨past, input, htargetRepresentation⟩ :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOfPlay_targetRepresentation_exists
      A strategy hwin root family direction semanticMember hmember false
        tableEnv (cuts.openLength k) .first
  have htargetRepresentation' :
      target =
        (activation.target .first past input,
          (.first,
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
              strategy hwin root
                (.strict
                  (profiledRawJointUnitRightActualDirection
                    (In₁ := In₁) (In₂ := In₂) .first past input)))) := by
    simpa [target, play, linkedPlay, activation] using htargetRepresentation
  obtain ⟨slot, htarget⟩ :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOfPlay_targetSlot_exists
      A strategy hwin root family direction semanticMember hmember false
        tableEnv (cuts.openLength k) .first
  have hsource :
      descriptor.source =
        profiledRawJointRightFinitePayloadLiteralPrefixSenderSource
          A strategy hwin
            (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBaseAt
              A strategy hwin initialTag env (cuts.cuts k)).1.1 false := by
    rw [hsender]
    simp [descriptor, activation,
      profiledRawJointRightFinitePayloadLinkedSiblingDescriptorOf]
  have hstate' :
      A.runFrom physicalState
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartWord
            A strategy hwin initialTag env) (cuts.cuts k) =
        pairedCodeStateForRow A .first descriptor.source.1.1 := by
    rw [hsource]
    exact hstate
  have hpacket :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_rightCut_physicalPacket
      A strategy hwin initialTag env cuts hnoBoth k hgraph root family
        direction semanticMember hmember hsender hreceiver physicalState
          hstate' slot htarget
  have hparent :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_rightCut_targetPayload_eq_nextParent
      A strategy hwin initialTag env cuts hnoBoth k hgraph root family
        direction semanticMember hmember hsender hreceiver
  have hpair :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightPairRootedAt
        A strategy hwin root initialTag env (cuts.cuts k) := by
    exact ⟨family, direction, semanticMember, hmember, false, [], hsender,
      hreceiver⟩
  have hnext :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_rightCut_step
      A strategy hwin initialTag env cuts hnoBoth k hgraph hready hpair
  have htarget' :
      profiledRawJointHybridFinitePayloadLinkedRightTargetProjection A target =
        .inr (.inr slot) := by
    simpa [target, play, linkedPlay] using htarget
  have htargetLive : target.1.family.left () = some slot := by
    change profiledRawJointUnitRightTargetProjection A target.1 =
      .inr (.inr slot) at htarget'
    cases hliveTarget : target.1.family.left () with
    | none =>
        simp [profiledRawJointUnitRightTargetProjection, hliveTarget] at htarget'
    | some targetSlot =>
        have hslotTarget : targetSlot = slot := by
          simpa [profiledRawJointUnitRightTargetProjection, hliveTarget]
            using htarget'
        subst targetSlot
        rfl
  rcases hready with
    ⟨rootCode, rootSlot, hreachable, hrootCode, hrootLive⟩
  have htargetCode :
      (profiledRawJointHybridFinitePayloadLinkedTargetPayload A target).2.1.1 =
        .oneSided target.1 := by
    rw [htargetRepresentation']
    have hfull :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren_code A
        strategy hwin root hreachable
          (.strict
            (profiledRawJointUnitRightActualDirection
              (In₁ := In₁) (In₂ := In₂) .first past input))
    exact (congrArg Prod.fst hfull).trans
      (hchildAligned .first past input)
  have hparent' :
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartParentAt
          A strategy hwin initialTag env (cuts.cuts (k + 1)) =
        profiledRawJointHybridFinitePayloadLinkedTargetPayload A target := by
    simpa [target, play, linkedPlay, tableEnv] using hparent
  obtain ⟨nextCode, nextSlot, hnextCode, hnextLive, hnextSenderRelay⟩ :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_leftReady_restartRelay_senderSource
      A strategy hwin
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartParentAt
          A strategy hwin initialTag env (cuts.cuts (k + 1)))
        hnext.2.1 false false
  have hnextTargetCode :
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartParentAt
          A strategy hwin initialTag env (cuts.cuts (k + 1))).2.1.1 =
        .oneSided target.1 := by
    rw [hparent']
    exact htargetCode
  have hnextCodeEq : nextCode = target.1 :=
    ProfiledRawJointHybridCode.oneSided.inj
      (hnextCode.symm.trans hnextTargetCode)
  have hnextSlotEq : nextSlot = slot := by
    rw [hnextCodeEq] at hnextLive
    exact Option.some.inj (hnextLive.symm.trans htargetLive)
  have hnextSender :
      profiledRawJointLeftFinitePayloadLiteralPrefixSenderSource
          A strategy hwin
            (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBaseAt
              A strategy hwin initialTag env (cuts.cuts (k + 1))).2.1
          false = slot := by
    rw [
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBaseAt_cut_eq_restartRelay
        A strategy hwin initialTag env cuts hnoBoth (k + 1) hnext.1]
    exact hnextSenderRelay.trans hnextSlotEq
  exact ⟨target, slot, htarget', hparent', hpacket.1, hpacket.2,
    hnext.2.1, hnextSender⟩

/-- Ready left-cut mirror of the complete local handoff package. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_leftCut_freshPhysicalHandoff
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (cuts : OperationalCloseCutPackage (fun n ↦ (env n).graph))
    (hnoBoth : ∀ n : Nat, (env n).graph ≠ .both)
    (k : Nat) (hgraph : (env (cuts.cuts k)).graph = .left)
    (hready :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftRootReady
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartParentAt
            A strategy hwin initialTag env (cuts.cuts k)))
    (physicalState : A.State)
    (hstate :
      A.runFrom physicalState
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartWord
            A strategy hwin initialTag env) (cuts.cuts k) =
        pairedCodeStateForRow A .first
          (profiledRawJointLeftFinitePayloadLiteralPrefixSenderSource
            A strategy hwin
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBaseAt
                A strategy hwin initialTag env (cuts.cuts k)).2.1 false).1.1) :
    ∃ target : ProfiledRawJointHybridFinitePayloadLinkedTarget A
        (BankControl A strategy hwin),
      ∃ slot : ProfiledRawRightSlot A,
        profiledRawJointHybridFinitePayloadLinkedLeftTargetProjection A
            target = .inr (.inl slot) ∧
          profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartParentAt
              A strategy hwin initialTag env (cuts.cuts (k + 1)) =
            profiledRawJointHybridFinitePayloadLinkedTargetPayload A target ∧
          cutBlockMin
                (fun j ↦ A.priority
                  (A.runFrom physicalState
                    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartWord
                      A strategy hwin initialTag env) j))
                cuts.cuts k =
              profiledRawJointThreadRootPriority A (.inl slot) ∧
          A.runFrom physicalState
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartWord
                A strategy hwin initialTag env) (cuts.cuts (k + 1)) =
            pairedCodeStateForRow A .first slot.1.1 ∧
          ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightRootReady
            A strategy hwin
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartParentAt
                A strategy hwin initialTag env (cuts.cuts (k + 1))) ∧
          profiledRawJointRightFinitePayloadLiteralPrefixSenderSource
              A strategy hwin
                (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBaseAt
                  A strategy hwin initialTag env (cuts.cuts (k + 1))).1.1
              false = slot := by
  let root :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartParentAt
      A strategy hwin initialTag env (cuts.cuts k)
  rcases
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_leftCut_freshAlignedOccurrence
        A strategy hwin initialTag env cuts hnoBoth k hgraph hready with
    ⟨family, direction, semanticMember, hmember, hsender, hreceiver,
      hchildAligned⟩
  let activation :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLeftActivations
      A strategy hwin family direction semanticMember hmember false
  let descriptor :=
    profiledRawJointLeftFinitePayloadLinkedSiblingDescriptorOf A activation
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
        strategy hwin root)
  let tableEnv : Nat → In₁ × In₂ := fun t ↦
    ((env (cuts.cuts k + t)).inputOne,
      (env (cuts.cuts k + t)).inputTwo)
  let linkedPlay :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOfPlay
      A strategy hwin root family direction semanticMember hmember false
        tableEnv
  let play := BlockRecordMonitor.projectReceiverPlay
    (profiledRawJointHybridFinitePayloadRowExactLeftReceiverProjection A)
      linkedPlay
  let target := ((play (cuts.openLength k)).2.1.target .first)
  obtain ⟨past, input, htargetRepresentation⟩ :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOfPlay_targetRepresentation_exists
      A strategy hwin root family direction semanticMember hmember false
        tableEnv (cuts.openLength k) .first
  have htargetRepresentation' :
      target =
        (activation.target .first past input,
          (.first,
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
              strategy hwin root
                (.strict
                  (profiledRawJointUnitLeftActualDirection
                    (In₁ := In₁) (In₂ := In₂) .first past input)))) := by
    simpa [target, play, linkedPlay, activation] using htargetRepresentation
  obtain ⟨slot, htarget⟩ :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOfPlay_targetSlot_exists
      A strategy hwin root family direction semanticMember hmember false
        tableEnv (cuts.openLength k) .first
  have hsource :
      descriptor.source =
        profiledRawJointLeftFinitePayloadLiteralPrefixSenderSource
          A strategy hwin
            (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBaseAt
              A strategy hwin initialTag env (cuts.cuts k)).2.1 false := by
    rw [hsender]
    simp [descriptor, activation,
      profiledRawJointLeftFinitePayloadLinkedSiblingDescriptorOf]
  have hstate' :
      A.runFrom physicalState
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartWord
            A strategy hwin initialTag env) (cuts.cuts k) =
        pairedCodeStateForRow A .first descriptor.source.1.1 := by
    rw [hsource]
    exact hstate
  have hpacket :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_leftCut_physicalPacket
      A strategy hwin initialTag env cuts hnoBoth k hgraph root family
        direction semanticMember hmember hsender hreceiver physicalState
          hstate' slot htarget
  have hparent :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_leftCut_targetPayload_eq_nextParent
      A strategy hwin initialTag env cuts hnoBoth k hgraph root family
        direction semanticMember hmember hsender hreceiver
  have hpair :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftPairRootedAt
        A strategy hwin root initialTag env (cuts.cuts k) := by
    exact ⟨family, direction, semanticMember, hmember, false, [], hsender,
      hreceiver⟩
  have hnext :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_leftCut_step
      A strategy hwin initialTag env cuts hnoBoth k hgraph hready hpair
  have htarget' :
      profiledRawJointHybridFinitePayloadLinkedLeftTargetProjection A target =
        .inr (.inl slot) := by
    simpa [target, play, linkedPlay] using htarget
  have htargetLive : target.1.family.right () = some slot := by
    change profiledRawJointUnitLeftTargetProjection A target.1 =
      .inr (.inl slot) at htarget'
    cases hliveTarget : target.1.family.right () with
    | none =>
        simp [profiledRawJointUnitLeftTargetProjection, hliveTarget] at htarget'
    | some targetSlot =>
        have hslotTarget : targetSlot = slot := by
          simpa [profiledRawJointUnitLeftTargetProjection, hliveTarget]
            using htarget'
        subst targetSlot
        rfl
  rcases hready with
    ⟨rootCode, rootSlot, hreachable, hrootCode, hrootLive⟩
  have htargetCode :
      (profiledRawJointHybridFinitePayloadLinkedTargetPayload A target).2.1.1 =
        .oneSided target.1 := by
    rw [htargetRepresentation']
    have hfull :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren_code A
        strategy hwin root hreachable
          (.strict
            (profiledRawJointUnitLeftActualDirection
              (In₁ := In₁) (In₂ := In₂) .first past input))
    exact (congrArg Prod.fst hfull).trans
      (hchildAligned .first past input)
  have hparent' :
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartParentAt
          A strategy hwin initialTag env (cuts.cuts (k + 1)) =
        profiledRawJointHybridFinitePayloadLinkedTargetPayload A target := by
    simpa [target, play, linkedPlay, tableEnv] using hparent
  obtain ⟨nextCode, nextSlot, hnextCode, hnextLive, hnextSenderRelay⟩ :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_rightReady_restartRelay_senderSource
      A strategy hwin
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartParentAt
          A strategy hwin initialTag env (cuts.cuts (k + 1)))
        hnext.2.1 false false
  have hnextTargetCode :
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartParentAt
          A strategy hwin initialTag env (cuts.cuts (k + 1))).2.1.1 =
        .oneSided target.1 := by
    rw [hparent']
    exact htargetCode
  have hnextCodeEq : nextCode = target.1 :=
    ProfiledRawJointHybridCode.oneSided.inj
      (hnextCode.symm.trans hnextTargetCode)
  have hnextSlotEq : nextSlot = slot := by
    rw [hnextCodeEq] at hnextLive
    exact Option.some.inj (hnextLive.symm.trans htargetLive)
  have hnextSender :
      profiledRawJointRightFinitePayloadLiteralPrefixSenderSource
          A strategy hwin
            (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBaseAt
              A strategy hwin initialTag env (cuts.cuts (k + 1))).1.1
          false = slot := by
    rw [
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBaseAt_cut_eq_restartRelay
        A strategy hwin initialTag env cuts hnoBoth (k + 1) hnext.1]
    exact hnextSenderRelay.trans hnextSlotEq
  exact ⟨target, slot, htarget', hparent', hpacket.1, hpacket.2,
    hnext.2.1, hnextSender⟩

/-! ## Global cut-state induction -/

/-- At each operational cut, the actual physical DPA state is anchored at
the executable sender source selected by the graph side of that cut. -/
def
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartPhysicalStateAlignedAtCut
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (cuts : OperationalCloseCutPackage (fun n ↦ (env n).graph))
    (physicalState : A.State) (k : Nat) : Prop :=
  match (env (cuts.cuts k)).graph with
  | .right =>
      A.runFrom physicalState
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartWord
            A strategy hwin initialTag env) (cuts.cuts k) =
        pairedCodeStateForRow A .first
          (profiledRawJointRightFinitePayloadLiteralPrefixSenderSource
            A strategy hwin
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBaseAt
                A strategy hwin initialTag env (cuts.cuts k)).1.1 false).1.1
  | .left =>
      A.runFrom physicalState
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartWord
            A strategy hwin initialTag env) (cuts.cuts k) =
        pairedCodeStateForRow A .first
          (profiledRawJointLeftFinitePayloadLiteralPrefixSenderSource
            A strategy hwin
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBaseAt
                A strategy hwin initialTag env (cuts.cuts k)).2.1 false).1.1
  | .both => False

/-- The local physical handoffs compose without any re-anchoring premise:
once the first strict cut is anchored, every later cut is anchored at its
newly installed executable sender source. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_physicalStateAlignedAtCuts
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (cuts : OperationalCloseCutPackage (fun n ↦ (env n).graph))
    (hnoBoth : ∀ n : Nat, (env n).graph ≠ .both)
    (hfirst :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartFirstStrictRootReady
        A strategy hwin initialTag env)
    (physicalState : A.State)
    (hinitial :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartPhysicalStateAlignedAtCut
        A strategy hwin initialTag env cuts physicalState 0) :
    ∀ k : Nat,
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartPhysicalStateAlignedAtCut
        A strategy hwin initialTag env cuts physicalState k := by
  intro k
  induction k with
  | zero => exact hinitial
  | succ k ih =>
      have hinvariant :=
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_cutInvariant
          A strategy hwin initialTag env cuts hnoBoth hfirst k
      cases hgraph : (env (cuts.cuts k)).graph with
      | right =>
          have hcurrent :
              ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightRootReady
                    A strategy hwin
                      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartParentAt
                        A strategy hwin initialTag env (cuts.cuts k)) ∧
                ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightPairRootedAt
                  A strategy hwin
                    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartParentAt
                      A strategy hwin initialTag env (cuts.cuts k))
                    initialTag env (cuts.cuts k) := by
            simpa [
              ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartCutInvariant,
              hgraph] using hinvariant
          have hstate :
              A.runFrom physicalState
                    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartWord
                      A strategy hwin initialTag env) (cuts.cuts k) =
                pairedCodeStateForRow A .first
                  (profiledRawJointRightFinitePayloadLiteralPrefixSenderSource
                    A strategy hwin
                      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBaseAt
                        A strategy hwin initialTag env (cuts.cuts k)).1.1
                      false).1.1 := by
            simpa [
              ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartPhysicalStateAlignedAtCut,
              hgraph] using ih
          rcases
              profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_rightCut_freshPhysicalHandoff
                A strategy hwin initialTag env cuts hnoBoth k hgraph
                  hcurrent.1 physicalState hstate
            with ⟨target, slot, htarget, hparent, hblock, hstateNext,
              hreadyNext, hsourceNext⟩
          have hnext :=
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_rightCut_step
              A strategy hwin initialTag env cuts hnoBoth k hgraph hcurrent.1
                hcurrent.2
          simp [
            ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartPhysicalStateAlignedAtCut,
            hnext.1]
          rw [hsourceNext]
          exact hstateNext
      | left =>
          have hcurrent :
              ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftRootReady
                    A strategy hwin
                      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartParentAt
                        A strategy hwin initialTag env (cuts.cuts k)) ∧
                ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftPairRootedAt
                  A strategy hwin
                    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartParentAt
                      A strategy hwin initialTag env (cuts.cuts k))
                    initialTag env (cuts.cuts k) := by
            simpa [
              ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartCutInvariant,
              hgraph] using hinvariant
          have hstate :
              A.runFrom physicalState
                    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartWord
                      A strategy hwin initialTag env) (cuts.cuts k) =
                pairedCodeStateForRow A .first
                  (profiledRawJointLeftFinitePayloadLiteralPrefixSenderSource
                    A strategy hwin
                      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBaseAt
                        A strategy hwin initialTag env (cuts.cuts k)).2.1
                      false).1.1 := by
            simpa [
              ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartPhysicalStateAlignedAtCut,
              hgraph] using ih
          rcases
              profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_leftCut_freshPhysicalHandoff
                A strategy hwin initialTag env cuts hnoBoth k hgraph
                  hcurrent.1 physicalState hstate
            with ⟨target, slot, htarget, hparent, hblock, hstateNext,
              hreadyNext, hsourceNext⟩
          have hnext :=
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_leftCut_step
              A strategy hwin initialTag env cuts hnoBoth k hgraph hcurrent.1
                hcurrent.2
          simp [
            ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartPhysicalStateAlignedAtCut,
            hnext.1]
          rw [hsourceNext]
          exact hstateNext
      | both => exact False.elim (hnoBoth (cuts.cuts k) hgraph)

/-- The positive-time bare code word of the executable child path is exactly
the public code stored by the corresponding child-run control. -/
private theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildRun_bareCodeWord_eq_controlCode
    (control : ProfiledRawJointHybridCommonControl A strategy hwin)
    (direction : Nat →
      ProfiledRawJointHybridDirection (In₁ := In₁) (In₂ := In₂))
    (n : Nat) :
    (((profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildRunPath A
        strategy hwin control direction).toExtraAllowedPath A strategy hwin
          ).bareCodeWord A strategy hwin) n =
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildRunControlAt
        A strategy hwin control direction (n + 1)).2.1.1 :=
  rfl

def profiledRawJointStrictGraphOfSide : IndexedLineageSide → Graph
  | .right => .right
  | .left => .left

private def profiledRawJointAlternatingSide
    (initial : IndexedLineageSide) : Nat → IndexedLineageSide
  | 0 => initial
  | n + 1 => (profiledRawJointAlternatingSide initial n).other

@[simp] private theorem profiledRawJointAlternatingSide_succ
    (initial : IndexedLineageSide) (n : Nat) :
    profiledRawJointAlternatingSide initial (n + 1) =
      (profiledRawJointAlternatingSide initial n).other :=
  rfl

omit [Inhabited In₁] [Inhabited In₂] [Fintype In₁] [Fintype In₂] [DecidableEq In₁]
    [DecidableEq In₂] in
/-- The maximal strict operational cuts alternate exactly with the canonical
proof-side lineage side stream. -/
private theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_graphAtCut_eq_alternatingSideOther
    (env : EnvironmentSequence In₁ In₂)
    (cuts : OperationalCloseCutPackage (fun n ↦ (env n).graph))
    (hnoBoth : ∀ n : Nat, (env n).graph ≠ .both)
    (initialSide : IndexedLineageSide)
    (hzero : (env 0).graph =
      profiledRawJointStrictGraphOfSide initialSide.other) :
    ∀ n : Nat,
      (env (cuts.cuts n)).graph =
        profiledRawJointStrictGraphOfSide
          (profiledRawJointAlternatingSide initialSide n).other := by
  intro n
  induction n with
  | zero => simpa [cuts.cuts_zero] using hzero
  | succ n ih =>
      have hstrict : (env (cuts.cuts n)).graph ≠ .both := hnoBoth _
      have hchange := cuts.maximal_of_strict n hstrict
      have hnextStrict : (env (cuts.cuts (n + 1))).graph ≠ .both := hnoBoth _
      cases hside : profiledRawJointAlternatingSide initialSide n with
      | right =>
          have hcurrent : (env (cuts.cuts n)).graph = .left := by
            simpa [profiledRawJointStrictGraphOfSide, hside] using ih
          cases hnext : (env (cuts.cuts (n + 1))).graph with
          | right =>
              simp [profiledRawJointAlternatingSide, hside,
                profiledRawJointStrictGraphOfSide]
          | left => exact False.elim (hchange (hnext.trans hcurrent.symm))
          | both => exact False.elim (hnextStrict hnext)
      | left =>
          have hcurrent : (env (cuts.cuts n)).graph = .right := by
            simpa [profiledRawJointStrictGraphOfSide, hside] using ih
          cases hnext : (env (cuts.cuts (n + 1))).graph with
          | right => exact False.elim (hchange (hnext.trans hcurrent.symm))
          | left =>
              simp [profiledRawJointAlternatingSide, hside,
                profiledRawJointStrictGraphOfSide]
          | both => exact False.elim (hnextStrict hnext)

/-- Once the front handoff identifies the retained tag with one exact bank
child, the full-restart physical priority stream inherits parity from the
accepted executable child-table run.  The root-slot hypotheses are precisely
the proof-side lineage data supplied by that front handoff. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_physicalPriorities_minEven_from_childRunRootSlots
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (cuts : OperationalCloseCutPackage (fun n ↦ (env n).graph))
    (hnoBoth : ∀ n : Nat, (env n).graph ≠ .both)
    (hfirst :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartFirstStrictRootReady
        A strategy hwin initialTag env)
    (physicalState : A.State)
    (hinitial :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartPhysicalStateAlignedAtCut
        A strategy hwin initialTag env cuts physicalState 0)
    (hclose :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartFrozenCloseWitness
        A strategy hwin initialTag env cuts)
    (control : ProfiledRawJointHybridCommonControl A strategy hwin)
    (direction : Nat → ProfiledRawJointHybridDirection
      (In₁ := In₁) (In₂ := In₂))
    (rootOffset : Nat)
    (hparentRun : ∀ n : Nat,
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartParentAt
          A strategy hwin initialTag env (cuts.cuts n) =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildRunControlAt
          A strategy hwin control direction (rootOffset + n))
    (side : Nat → IndexedLineageSide)
    (initialRoot : ProfiledRawJointThreadRoot A)
    (root : Nat → ProfiledRawJointThreadRoot A)
    (hinitialRoot :
      profiledRawJointHybridCurrentSlots A (side 0)
          (.common
            ((profiledRawJointCommonWorldFamily A
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankInstalled
                A strategy hwin control).world).incidenceCode A)) () =
        some initialRoot)
    (hroot : ∀ n : Nat,
      profiledRawJointHybridCurrentSlots A (side n).other
          ((((profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildRunPath
            A strategy hwin control direction).toExtraAllowedPath A strategy
              hwin).bareCodeWord A strategy hwin) n) () =
        some (root n))
    (halternates : ∀ n : Nat, side (n + 1) = (side n).other)
    (hside : ∀ k : Nat,
      match (env (cuts.cuts k)).graph with
      | .right => side (rootOffset + k) = .right
      | .left => side (rootOffset + k) = .left
      | .both => False) :
    NatSeqMinEvenParity
      (fun n ↦ A.priority
        (A.runFrom physicalState
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartWord
            A strategy hwin initialTag env) n)) := by
  have halignedCuts :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_physicalStateAlignedAtCuts
      A strategy hwin initialTag env cuts hnoBoth hfirst physicalState hinitial
  apply
    physicalPriorities_minEven_of_bankChildRun_rootSlots_from A strategy hwin
      control direction side initialRoot root hinitialRoot
        (rootOffset := rootOffset)
        (physicalPriorities := fun n ↦ A.priority
          (A.runFrom physicalState
            (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartWord
              A strategy hwin initialTag env) n))
        (cuts := cuts.cuts)
  · intro n
    exact hroot n
  · exact halternates
  · exact cuts.cuts_strictMono
  · exact cuts.cuts_zero
  · intro k
    have hinvariant :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_cutInvariant
        A strategy hwin initialTag env cuts hnoBoth hfirst k
    have hwordCode :
        ((((profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildRunPath
          A strategy hwin control direction).toExtraAllowedPath A strategy
            hwin).bareCodeWord A strategy hwin) (rootOffset + k)) =
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartParentAt
            A strategy hwin initialTag env (cuts.cuts (k + 1))).2.1.1 := by
      calc
        _ =
            (profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildRunControlAt
              A strategy hwin control direction ((rootOffset + k) + 1)).2.1.1 :=
          profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildRun_bareCodeWord_eq_controlCode
            A strategy hwin control direction (rootOffset + k)
        _ = _ := by
          have hoffset : (rootOffset + k) + 1 = rootOffset + (k + 1) := by
            omega
          rw [hoffset]
          exact congrArg (fun state : BankControl A strategy hwin ↦
            state.2.1.1) (hparentRun (k + 1)).symm
    cases hgraph : (env (cuts.cuts k)).graph with
    | right =>
        have hcurrent :
            ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightRootReady
                  A strategy hwin
                    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartParentAt
                      A strategy hwin initialTag env (cuts.cuts k)) ∧
              ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightPairRootedAt
                A strategy hwin
                  (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartParentAt
                    A strategy hwin initialTag env (cuts.cuts k))
                  initialTag env (cuts.cuts k) := by
          simpa [
            ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartCutInvariant,
            hgraph] using hinvariant
        have hstate :
            A.runFrom physicalState
                  (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartWord
                    A strategy hwin initialTag env) (cuts.cuts k) =
              pairedCodeStateForRow A .first
                (profiledRawJointRightFinitePayloadLiteralPrefixSenderSource
                  A strategy hwin
                    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBaseAt
                      A strategy hwin initialTag env (cuts.cuts k)).1.1
                    false).1.1 := by
          simpa [
            ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartPhysicalStateAlignedAtCut,
            hgraph] using halignedCuts k
        rcases
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_rightCut_freshPhysicalHandoff
              A strategy hwin initialTag env cuts hnoBoth k hgraph hcurrent.1
                physicalState hstate
          with ⟨target, slot, htarget, hparent, hblock, hstateNext,
            hreadyNext, hsourceNext⟩
        have hnext :=
          profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_rightCut_step
            A strategy hwin initialTag env cuts hnoBoth k hgraph hcurrent.1
              hcurrent.2
        obtain ⟨nextCode, nextSlot, hnextCode, hnextLive,
            hnextSenderRelay⟩ :=
          profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_leftReady_restartRelay_senderSource
            A strategy hwin
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartParentAt
                A strategy hwin initialTag env (cuts.cuts (k + 1)))
              hreadyNext false false
        have hnextSender :
            profiledRawJointLeftFinitePayloadLiteralPrefixSenderSource
                A strategy hwin
                  (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBaseAt
                    A strategy hwin initialTag env (cuts.cuts (k + 1))).2.1
                false = nextSlot := by
          rw [
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBaseAt_cut_eq_restartRelay
              A strategy hwin initialTag env cuts hnoBoth (k + 1) hnext.1]
          exact hnextSenderRelay
        have hnextSlotEq : nextSlot = slot :=
          hnextSender.symm.trans hsourceNext
        have hsideRight : side (rootOffset + k) = .right := by
          simpa [hgraph] using hside k
        have hrootAt := hroot (rootOffset + k)
        change
          profiledRawJointHybridCurrentSlots A (side (rootOffset + k)).other
              ((((profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildRunPath
                A strategy hwin control direction).toExtraAllowedPath A
                  strategy hwin).bareCodeWord A strategy hwin) (rootOffset + k)) () =
            some (root (rootOffset + k)) at hrootAt
        rw [hwordCode, hnextCode, hsideRight] at hrootAt
        simp [profiledRawJointHybridCurrentSlots,
          profiledRawJointOneSidedCurrentSlots, hnextLive] at hrootAt
        change some (.inr nextSlot) = some (root (rootOffset + k)) at hrootAt
        have hrootAt' := Option.some.inj hrootAt
        have hslotRoot :
            (.inr slot : ProfiledRawJointThreadRoot A) =
              root (rootOffset + k) := by
          rw [← hnextSlotEq]
          exact hrootAt'
        exact hblock.trans
          (congrArg (profiledRawJointThreadRootPriority A) hslotRoot)
    | left =>
        have hcurrent :
            ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftRootReady
                  A strategy hwin
                    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartParentAt
                      A strategy hwin initialTag env (cuts.cuts k)) ∧
              ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftPairRootedAt
                A strategy hwin
                  (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartParentAt
                    A strategy hwin initialTag env (cuts.cuts k))
                  initialTag env (cuts.cuts k) := by
          simpa [
            ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartCutInvariant,
            hgraph] using hinvariant
        have hstate :
            A.runFrom physicalState
                  (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartWord
                    A strategy hwin initialTag env) (cuts.cuts k) =
              pairedCodeStateForRow A .first
                (profiledRawJointLeftFinitePayloadLiteralPrefixSenderSource
                  A strategy hwin
                    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftBaseAt
                      A strategy hwin initialTag env (cuts.cuts k)).2.1
                    false).1.1 := by
          simpa [
            ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartPhysicalStateAlignedAtCut,
            hgraph] using halignedCuts k
        rcases
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_leftCut_freshPhysicalHandoff
              A strategy hwin initialTag env cuts hnoBoth k hgraph hcurrent.1
                physicalState hstate
          with ⟨target, slot, htarget, hparent, hblock, hstateNext,
            hreadyNext, hsourceNext⟩
        have hnext :=
          profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_leftCut_step
            A strategy hwin initialTag env cuts hnoBoth k hgraph hcurrent.1
              hcurrent.2
        obtain ⟨nextCode, nextSlot, hnextCode, hnextLive,
            hnextSenderRelay⟩ :=
          profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_rightReady_restartRelay_senderSource
            A strategy hwin
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartParentAt
                A strategy hwin initialTag env (cuts.cuts (k + 1)))
              hreadyNext false false
        have hnextSender :
            profiledRawJointRightFinitePayloadLiteralPrefixSenderSource
                A strategy hwin
                  (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBaseAt
                    A strategy hwin initialTag env (cuts.cuts (k + 1))).1.1
                false = nextSlot := by
          rw [
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightBaseAt_cut_eq_restartRelay
              A strategy hwin initialTag env cuts hnoBoth (k + 1) hnext.1]
          exact hnextSenderRelay
        have hnextSlotEq : nextSlot = slot :=
          hnextSender.symm.trans hsourceNext
        have hsideLeft : side (rootOffset + k) = .left := by
          simpa [hgraph] using hside k
        have hrootAt := hroot (rootOffset + k)
        change
          profiledRawJointHybridCurrentSlots A (side (rootOffset + k)).other
              ((((profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildRunPath
                A strategy hwin control direction).toExtraAllowedPath A
                  strategy hwin).bareCodeWord A strategy hwin) (rootOffset + k)) () =
            some (root (rootOffset + k)) at hrootAt
        rw [hwordCode, hnextCode, hsideLeft] at hrootAt
        simp [profiledRawJointHybridCurrentSlots,
          profiledRawJointOneSidedCurrentSlots, hnextLive] at hrootAt
        change some (.inl nextSlot) = some (root (rootOffset + k)) at hrootAt
        have hrootAt' := Option.some.inj hrootAt
        have hslotRoot :
            (.inl slot : ProfiledRawJointThreadRoot A) =
              root (rootOffset + k) := by
          rw [← hnextSlotEq]
          exact hrootAt'
        exact hblock.trans
          (congrArg (profiledRawJointThreadRootPriority A) hslotRoot)
    | both => exact False.elim (hnoBoth (cuts.cuts k) hgraph)

/-- The front handoff is the offset-one specialization of the arbitrary
child-run suffix theorem. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_physicalPriorities_minEven_of_childRunRootSlots
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (cuts : OperationalCloseCutPackage (fun n ↦ (env n).graph))
    (hnoBoth : ∀ n : Nat, (env n).graph ≠ .both)
    (hfirst :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartFirstStrictRootReady
        A strategy hwin initialTag env)
    (physicalState : A.State)
    (hinitial :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartPhysicalStateAlignedAtCut
        A strategy hwin initialTag env cuts physicalState 0)
    (hclose :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartFrozenCloseWitness
        A strategy hwin initialTag env cuts)
    (control : ProfiledRawJointHybridCommonControl A strategy hwin)
    (first : ProfiledRawJointHybridDirection
      (In₁ := In₁) (In₂ := In₂))
    (hfirstChild : initialTag.1 =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A strategy
        hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRoot A
            strategy hwin control) first)
    (side : Nat → IndexedLineageSide)
    (initialRoot : ProfiledRawJointThreadRoot A)
    (root : Nat → ProfiledRawJointThreadRoot A)
    (hinitialRoot :
      profiledRawJointHybridCurrentSlots A (side 0)
          (.common
            ((profiledRawJointCommonWorldFamily A
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankInstalled
                A strategy hwin control).world).incidenceCode A)) () =
        some initialRoot)
    (hroot : ∀ n : Nat,
      let direction :=
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankPrependDirection
          first
            (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartFrozenSemanticDirection
              A strategy hwin initialTag env cuts hclose)
      profiledRawJointHybridCurrentSlots A (side n).other
          ((((profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildRunPath
            A strategy hwin control direction).toExtraAllowedPath A strategy
              hwin).bareCodeWord A strategy hwin) n) () =
        some (root n))
    (halternates : ∀ n : Nat, side (n + 1) = (side n).other)
    (hside : ∀ k : Nat,
      match (env (cuts.cuts k)).graph with
      | .right => side (k + 1) = .right
      | .left => side (k + 1) = .left
      | .both => False) :
    NatSeqMinEvenParity
      (fun n ↦ A.priority
        (A.runFrom physicalState
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartWord
            A strategy hwin initialTag env) n)) := by
  let tailDirection :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartFrozenSemanticDirection
      A strategy hwin initialTag env cuts hclose
  let direction :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankPrependDirection
      first tailDirection
  have hparentRun :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartParentAtFrozenSemanticCuts_eq_childRun_prepend
      A strategy hwin initialTag env cuts hclose control first hfirstChild
  have hparentRun' : ∀ n : Nat,
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartParentAt
          A strategy hwin initialTag env (cuts.cuts n) =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildRunControlAt
          A strategy hwin control direction (1 + n) := by
    intro n
    simpa [direction, tailDirection, Nat.add_comm] using hparentRun n
  apply
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_physicalPriorities_minEven_from_childRunRootSlots
      A strategy hwin initialTag env cuts hnoBoth hfirst physicalState hinitial
        hclose control direction 1 hparentRun' side initialRoot root hinitialRoot
  · intro n
    simpa [direction, tailDirection] using hroot n
  · exact halternates
  · intro k
    simpa [Nat.add_comm] using hside k

/-- Main FullRestart acceptance endpoint.  An exact strict child delivered by
the front phase, together with the unavoidable initial physical-state anchor,
is sufficient for acceptance of the complete repaired persistent suffix.  All
later root slots and all later DPA-state anchors are constructed internally. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartWord_acceptsFrom_of_exactFirstChild
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (cuts : OperationalCloseCutPackage (fun n ↦ (env n).graph))
    (hnoBoth : ∀ n : Nat, (env n).graph ≠ .both)
    (hfirst :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartFirstStrictRootReady
        A strategy hwin initialTag env)
    (physicalState : A.State)
    (hinitial :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartPhysicalStateAlignedAtCut
        A strategy hwin initialTag env cuts physicalState 0)
    (control : ProfiledRawJointHybridCommonControl A strategy hwin)
    (actual : ProfiledRawJointActualDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (hfirstChild : initialTag.1 =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A strategy
        hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRoot A
            strategy hwin control) (.strict actual))
    (hfirstGraph : (env 0).graph =
      profiledRawJointStrictGraphOfSide actual.side.other) :
    A.AcceptsFrom physicalState
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartWord
        A strategy hwin initialTag env) := by
  let hclose :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartFrozenCloseWitness_of_firstStrictRootReady
      A strategy hwin initialTag env cuts hnoBoth hfirst
  let tailDirection :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartFrozenSemanticDirection
      A strategy hwin initialTag env cuts hclose
  let direction :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankPrependDirection
      (.strict actual) tailDirection
  let side := profiledRawJointAlternatingSide actual.side
  let world :=
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankInstalled A strategy
      hwin control).world
  let initialRoot : ProfiledRawJointThreadRoot A :=
    match actual.side with
    | .right => .inl
        (profiledRawRightSlotOfSemanticPair A (world.procOneMember A))
    | .left => .inr
        (profiledRawLeftSlotOfSemanticPair A (world.procTwoMember A))
  have hinitialRoot :
      profiledRawJointHybridCurrentSlots A (side 0)
          (.common
            ((profiledRawJointCommonWorldFamily A world).incidenceCode A)) () =
        some initialRoot := by
    cases hside : actual.side <;>
      simp [side, initialRoot, hside, world,
        profiledRawJointAlternatingSide,
        profiledRawJointHybridCurrentSlots,
        profiledRawJointOneSidedCurrentSlots,
        profiledRawJointCommonWorldFamily,
        ProfiledRawJointSemanticFamily.incidenceCode,
        ProfiledRawJointSemanticFamily.code,
        profiledRawRightSlotOfSemanticPair,
        profiledRawLeftSlotOfSemanticPair]
  have hgraphs :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_graphAtCut_eq_alternatingSideOther
      env cuts hnoBoth actual.side hfirstGraph
  have hparentRun :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartParentAtFrozenSemanticCuts_eq_childRun_prepend
      A strategy hwin initialTag env cuts hclose control (.strict actual)
        hfirstChild
  have hinvariant :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_cutInvariant
      A strategy hwin initialTag env cuts hnoBoth hfirst
  have hrootExists : ∀ n : Nat, ∃ targetRoot : ProfiledRawJointThreadRoot A,
      profiledRawJointHybridCurrentSlots A (side n).other
          ((((profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildRunPath
            A strategy hwin control direction).toExtraAllowedPath A strategy
              hwin).bareCodeWord A strategy hwin) n) () =
        some targetRoot := by
    intro n
    have hwordCode :
        ((((profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildRunPath
          A strategy hwin control direction).toExtraAllowedPath A strategy
            hwin).bareCodeWord A strategy hwin) n) =
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartParentAt
            A strategy hwin initialTag env (cuts.cuts n)).2.1.1 := by
      calc
        _ =
            (profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildRunControlAt
              A strategy hwin control direction (n + 1)).2.1.1 :=
          profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildRun_bareCodeWord_eq_controlCode
            A strategy hwin control direction n
        _ = _ := congrArg (fun state : BankControl A strategy hwin ↦
          state.2.1.1) (hparentRun n).symm
    have hgraphSide :
        (env (cuts.cuts n)).graph =
          profiledRawJointStrictGraphOfSide (side n).other := by
      simpa [side] using hgraphs n
    have hcut := hinvariant n
    cases hcurrentSide : (side n).other with
    | right =>
        have hgraph : (env (cuts.cuts n)).graph = .right := by
          simpa [profiledRawJointStrictGraphOfSide, hcurrentSide]
            using hgraphSide
        have hready :
            ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightRootReady
              A strategy hwin
                (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartParentAt
                  A strategy hwin initialTag env (cuts.cuts n)) := by
          have hcurrent :
              ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightRootReady
                    A strategy hwin
                      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartParentAt
                        A strategy hwin initialTag env (cuts.cuts n)) ∧
                ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightPairRootedAt
                  A strategy hwin
                    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartParentAt
                      A strategy hwin initialTag env (cuts.cuts n))
                    initialTag env (cuts.cuts n) := by
            simpa [
              ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartCutInvariant,
              hgraph] using hcut
          exact hcurrent.1
        rcases hready with ⟨code, slot, hreachable, hcode, hlive⟩
        refine ⟨.inl slot, ?_⟩
        rw [hwordCode, hcode]
        simp [hcurrentSide, profiledRawJointHybridCurrentSlots,
          profiledRawJointOneSidedCurrentSlots, hlive]
    | left =>
        have hgraph : (env (cuts.cuts n)).graph = .left := by
          simpa [profiledRawJointStrictGraphOfSide, hcurrentSide]
            using hgraphSide
        have hready :
            ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftRootReady
              A strategy hwin
                (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartParentAt
                  A strategy hwin initialTag env (cuts.cuts n)) := by
          have hcurrent :
              ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftRootReady
                    A strategy hwin
                      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartParentAt
                        A strategy hwin initialTag env (cuts.cuts n)) ∧
                ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftPairRootedAt
                  A strategy hwin
                    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartParentAt
                      A strategy hwin initialTag env (cuts.cuts n))
                    initialTag env (cuts.cuts n) := by
            simpa [
              ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartCutInvariant,
              hgraph] using hcut
          exact hcurrent.1
        rcases hready with ⟨code, slot, hreachable, hcode, hlive⟩
        refine ⟨.inr slot, ?_⟩
        rw [hwordCode, hcode]
        simp [hcurrentSide, profiledRawJointHybridCurrentSlots,
          profiledRawJointOneSidedCurrentSlots, hlive]
  let root : Nat → ProfiledRawJointThreadRoot A :=
    fun n ↦ Classical.choose (hrootExists n)
  have hroot : ∀ n : Nat,
      profiledRawJointHybridCurrentSlots A (side n).other
          ((((profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildRunPath
            A strategy hwin control direction).toExtraAllowedPath A strategy
              hwin).bareCodeWord A strategy hwin) n) () =
        some (root n) := fun n ↦ Classical.choose_spec (hrootExists n)
  have halternates : ∀ n : Nat, side (n + 1) = (side n).other := by
    intro n
    rfl
  have hside : ∀ k : Nat,
      match (env (cuts.cuts k)).graph with
      | .right => side (k + 1) = .right
      | .left => side (k + 1) = .left
      | .both => False := by
    intro k
    have hgraphSide :
        (env (cuts.cuts k)).graph =
          profiledRawJointStrictGraphOfSide (side k).other := by
      simpa [side] using hgraphs k
    cases hsideK : side k with
    | right =>
        have hgraph : (env (cuts.cuts k)).graph = .left := by
          simpa [profiledRawJointStrictGraphOfSide, hsideK]
            using hgraphSide
        simp only [hgraph]
        calc
          side (k + 1) = (side k).other := halternates k
          _ = .left := by rw [hsideK]; rfl
    | left =>
        have hgraph : (env (cuts.cuts k)).graph = .right := by
          simpa [profiledRawJointStrictGraphOfSide, hsideK]
            using hgraphSide
        simp only [hgraph]
        calc
          side (k + 1) = (side k).other := halternates k
          _ = .right := by rw [hsideK]; rfl
  change NatSeqMinEvenParity
    (fun n ↦ A.priority
      (A.runFrom physicalState
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartWord
          A strategy hwin initialTag env) n))
  apply
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_physicalPriorities_minEven_of_childRunRootSlots
      A strategy hwin initialTag env cuts hnoBoth hfirst physicalState hinitial
        hclose control (.strict actual) hfirstChild side initialRoot root
          hinitialRoot
  · intro n
    simpa [direction, tailDirection] using hroot n
  · exact halternates
  · exact hside

/-- Two-child form of the full-restart acceptance endpoint.  This is used
after a finite common-root block: the front phase supplied `first`, the
common-root close supplied `second`, and the canonical full-restart suffix
starts at that second child. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartWord_acceptsFrom_of_exactSecondChild
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (cuts : OperationalCloseCutPackage (fun n ↦ (env n).graph))
    (hnoBoth : ∀ n : Nat, (env n).graph ≠ .both)
    (hfirst :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartFirstStrictRootReady
        A strategy hwin initialTag env)
    (physicalState : A.State)
    (hinitial :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartPhysicalStateAlignedAtCut
        A strategy hwin initialTag env cuts physicalState 0)
    (control : ProfiledRawJointHybridCommonControl A strategy hwin)
    (first second : ProfiledRawJointActualDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (hsecondSide : second.side = first.side.other)
    (hfirstRoot : ∃ targetRoot : ProfiledRawJointThreadRoot A,
      profiledRawJointHybridCurrentSlots A first.side.other
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
            strategy hwin
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRoot A
                strategy hwin control) (.strict first)).2.1.1 () =
        some targetRoot)
    (hsecondChild : initialTag.1 =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A strategy
        hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
            strategy hwin
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRoot A
                strategy hwin control) (.strict first))
          (.strict second))
    (hfirstGraph : (env 0).graph =
      profiledRawJointStrictGraphOfSide second.side.other) :
    A.AcceptsFrom physicalState
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartWord
        A strategy hwin initialTag env) := by
  let hclose :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartFrozenCloseWitness_of_firstStrictRootReady
      A strategy hwin initialTag env cuts hnoBoth hfirst
  let tailDirection :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartFrozenSemanticDirection
      A strategy hwin initialTag env cuts hclose
  let secondAndTail :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankPrependDirection
      (.strict second) tailDirection
  let direction :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankPrependDirection
      (.strict first) secondAndTail
  let side := profiledRawJointAlternatingSide first.side
  let world :=
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankInstalled A strategy
      hwin control).world
  let initialRoot : ProfiledRawJointThreadRoot A :=
    match first.side with
    | .right => .inl
        (profiledRawRightSlotOfSemanticPair A (world.procOneMember A))
    | .left => .inr
        (profiledRawLeftSlotOfSemanticPair A (world.procTwoMember A))
  have hinitialRoot :
      profiledRawJointHybridCurrentSlots A (side 0)
          (.common
            ((profiledRawJointCommonWorldFamily A world).incidenceCode A)) () =
        some initialRoot := by
    cases hside : first.side <;>
      simp [side, initialRoot, hside, world,
        profiledRawJointAlternatingSide,
        profiledRawJointHybridCurrentSlots,
        profiledRawJointOneSidedCurrentSlots,
        profiledRawJointCommonWorldFamily,
        ProfiledRawJointSemanticFamily.incidenceCode,
        ProfiledRawJointSemanticFamily.code,
        profiledRawRightSlotOfSemanticPair,
        profiledRawLeftSlotOfSemanticPair]
  have hsideSucc : ∀ k : Nat,
      side (k + 1) = profiledRawJointAlternatingSide second.side k := by
    intro k
    induction k with
    | zero =>
        simpa [side, profiledRawJointAlternatingSide] using hsecondSide.symm
    | succ k ih =>
        change (side (k + 1)).other =
          (profiledRawJointAlternatingSide second.side k).other
        exact congrArg IndexedLineageSide.other ih
  have hgraphs :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_graphAtCut_eq_alternatingSideOther
      env cuts hnoBoth second.side hfirstGraph
  have hgraphSide : ∀ k : Nat,
      (env (cuts.cuts k)).graph =
        profiledRawJointStrictGraphOfSide (side (k + 1)).other := by
    intro k
    rw [hgraphs k, hsideSucc k]
  have hinitialRun : initialTag.1 =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildRunControlAt
        A strategy hwin control direction 2 := by
    rw [hsecondChild]
    rfl
  have hdirection : ∀ n : Nat,
      direction (2 + n) =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartFrozenSemanticDirection
          A strategy hwin initialTag env cuts hclose n := by
    intro n
    have hindex : 2 + n = Nat.succ (Nat.succ n) := by omega
    rw [hindex]
    rfl
  have hparentRun :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartParentAtFrozenSemanticCuts_eq_childRun_from
      A strategy hwin initialTag env cuts hclose control direction 2
        hinitialRun hdirection
  have hinvariant :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_cutInvariant
      A strategy hwin initialTag env cuts hnoBoth hfirst
  have hrootExists : ∀ n : Nat, ∃ targetRoot : ProfiledRawJointThreadRoot A,
      profiledRawJointHybridCurrentSlots A (side n).other
          ((((profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildRunPath
            A strategy hwin control direction).toExtraAllowedPath A strategy
              hwin).bareCodeWord A strategy hwin) n) () =
        some targetRoot := by
    intro n
    cases n with
    | zero =>
        rcases hfirstRoot with ⟨targetRoot, htargetRoot⟩
        refine ⟨targetRoot, ?_⟩
        have hwordCode :
            ((((profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildRunPath
              A strategy hwin control direction).toExtraAllowedPath A strategy
                hwin).bareCodeWord A strategy hwin) 0) =
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
                strategy hwin
                  (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRoot A
                    strategy hwin control) (.strict first)).2.1.1 := by
          rfl
        simpa [side, hwordCode] using htargetRoot
    | succ k =>
        have hwordCode :
            ((((profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildRunPath
              A strategy hwin control direction).toExtraAllowedPath A strategy
                hwin).bareCodeWord A strategy hwin) (k + 1)) =
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartParentAt
                A strategy hwin initialTag env (cuts.cuts k)).2.1.1 := by
          calc
            _ =
                (profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildRunControlAt
                  A strategy hwin control direction ((k + 1) + 1)).2.1.1 :=
              profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildRun_bareCodeWord_eq_controlCode
                A strategy hwin control direction (k + 1)
            _ = _ := by
              have hoffset : (k + 1) + 1 = 2 + k := by omega
              rw [hoffset]
              exact congrArg (fun state : BankControl A strategy hwin ↦
                state.2.1.1) (hparentRun k).symm
        have hcut := hinvariant k
        have hgraphAt := hgraphSide k
        cases hcurrentSide : (side (k + 1)).other with
        | right =>
            have hgraph : (env (cuts.cuts k)).graph = .right := by
              simpa [profiledRawJointStrictGraphOfSide, hcurrentSide]
                using hgraphAt
            have hready :
                ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightRootReady
                  A strategy hwin
                    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartParentAt
                      A strategy hwin initialTag env (cuts.cuts k)) := by
              have hcurrent :
                  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightRootReady
                        A strategy hwin
                          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartParentAt
                            A strategy hwin initialTag env (cuts.cuts k)) ∧
                    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartRightPairRootedAt
                      A strategy hwin
                        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartParentAt
                          A strategy hwin initialTag env (cuts.cuts k))
                        initialTag env (cuts.cuts k) := by
                simpa [
                  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartCutInvariant,
                  hgraph] using hcut
              exact hcurrent.1
            rcases hready with ⟨code, slot, _hreachable, hcode, hlive⟩
            refine ⟨.inl slot, ?_⟩
            rw [hwordCode, hcode]
            simp [hcurrentSide, profiledRawJointHybridCurrentSlots,
              profiledRawJointOneSidedCurrentSlots, hlive]
        | left =>
            have hgraph : (env (cuts.cuts k)).graph = .left := by
              simpa [profiledRawJointStrictGraphOfSide, hcurrentSide]
                using hgraphAt
            have hready :
                ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftRootReady
                  A strategy hwin
                    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartParentAt
                      A strategy hwin initialTag env (cuts.cuts k)) := by
              have hcurrent :
                  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftRootReady
                        A strategy hwin
                          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartParentAt
                            A strategy hwin initialTag env (cuts.cuts k)) ∧
                    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartLeftPairRootedAt
                      A strategy hwin
                        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartParentAt
                          A strategy hwin initialTag env (cuts.cuts k))
                        initialTag env (cuts.cuts k) := by
                simpa [
                  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartCutInvariant,
                  hgraph] using hcut
              exact hcurrent.1
            rcases hready with ⟨code, slot, _hreachable, hcode, hlive⟩
            refine ⟨.inr slot, ?_⟩
            rw [hwordCode, hcode]
            simp [hcurrentSide, profiledRawJointHybridCurrentSlots,
              profiledRawJointOneSidedCurrentSlots, hlive]
  let root : Nat → ProfiledRawJointThreadRoot A :=
    fun n ↦ Classical.choose (hrootExists n)
  have hroot : ∀ n : Nat,
      profiledRawJointHybridCurrentSlots A (side n).other
          ((((profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildRunPath
            A strategy hwin control direction).toExtraAllowedPath A strategy
              hwin).bareCodeWord A strategy hwin) n) () =
        some (root n) := fun n ↦ Classical.choose_spec (hrootExists n)
  have halternates : ∀ n : Nat, side (n + 1) = (side n).other := by
    intro n
    rfl
  have hside : ∀ k : Nat,
      match (env (cuts.cuts k)).graph with
      | .right => side (2 + k) = .right
      | .left => side (2 + k) = .left
      | .both => False := by
    intro k
    have hgraphAt := hgraphSide k
    have hnextSide : side (2 + k) = (side (k + 1)).other := by
      rw [show 2 + k = (k + 1) + 1 by omega, halternates]
    cases hprevSide : side (k + 1) with
    | right =>
        have hgraph : (env (cuts.cuts k)).graph = .left := by
          simpa [profiledRawJointStrictGraphOfSide, hprevSide] using hgraphAt
        simp only [hgraph]
        rw [hnextSide, hprevSide]
        rfl
    | left =>
        have hgraph : (env (cuts.cuts k)).graph = .right := by
          simpa [profiledRawJointStrictGraphOfSide, hprevSide] using hgraphAt
        simp only [hgraph]
        rw [hnextSide, hprevSide]
        rfl
  change NatSeqMinEvenParity
    (fun n ↦ A.priority
      (A.runFrom physicalState
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartWord
          A strategy hwin initialTag env) n))
  apply
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestart_physicalPriorities_minEven_from_childRunRootSlots
      A strategy hwin initialTag env cuts hnoBoth hfirst physicalState hinitial
        hclose control direction 2 hparentRun side initialRoot root hinitialRoot
  · exact hroot
  · exact halternates
  · exact hside

end

end DetParityAutomaton

end DistributedSynthesis
