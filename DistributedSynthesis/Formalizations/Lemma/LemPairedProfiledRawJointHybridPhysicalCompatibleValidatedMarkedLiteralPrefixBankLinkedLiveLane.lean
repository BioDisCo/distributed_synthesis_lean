/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankLinkedPayload

/-!
# Live marked-bank lanes never use the linked rebuild fallback

The executable payload-linked bank tables are total: an absent or unreachable
literal lane is assigned a harmless fallback value.  At a live one-sided
semantic lane, however, the current literal annotation was installed by the
same incoming edge as the current finite code.  This file makes the missing
bridge explicit.  Reachability plus a live slot in the one-sided code implies
that the corresponding literal move is present; the existing rebuild theorem
then certifies that `linkedRightMove` / `linkedLeftMove` takes its exact
same-occurrence branch.

All lane and source witnesses below are proof-side.  No executable endpoint
learns the graph direction, hierarchy side, strict leader, history, or view.
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

private abbrev BankReachable
    (state : BankControl A strategy hwin) :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankReachable A strategy
    hwin state

private abbrev RightMove :=
  ProfiledRawJointGuardedCommonRightLiteralCrossMove A

private abbrev LeftMove :=
  ProfiledRawJointGuardedCommonLeftLiteralCrossMove A

private abbrev LinkedRightMove :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMove A
    strategy hwin

private abbrev LinkedLeftMove :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMove A
    strategy hwin

private abbrev HybridState :=
  ProfiledRawJointHybridSemanticState A strategy

private abbrev LiteralAnnotation :=
  ProfiledRawJointHybridLiteralPrefixEdgeAnnotation A

/-! ## Literal options are present exactly when their semantic lane is live -/

theorem exists_profiledRawJointRightLiteralPrefixMoveOption_of_member
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcOnePairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).right () =
      some semanticMember) :
    ∃ move : RightMove A,
      profiledRawJointRightLiteralPrefixMoveOption A strategy hwin family
        direction = some move := by
  classical
  unfold profiledRawJointRightLiteralPrefixMoveOption
  split
  next hex => exact ⟨_, rfl⟩
  next hnone => exact (hnone ⟨semanticMember, hmember⟩).elim

theorem exists_profiledRawJointLeftLiteralPrefixMoveOption_of_member
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcTwoPairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).left () =
      some semanticMember) :
    ∃ move : LeftMove A,
      profiledRawJointLeftLiteralPrefixMoveOption A strategy hwin family
        direction = some move := by
  classical
  unfold profiledRawJointLeftLiteralPrefixMoveOption
  split
  next hex => exact ⟨_, rfl⟩
  next hnone => exact (hnone ⟨semanticMember, hmember⟩).elim

/-! ## Current one-sided provenance forces live literal lanes -/

/-- A live right slot in an exact one-sided current source has a present
right literal table. -/
theorem
    ProfiledRawJointHybridLiteralPrefixCurrentCompatible.exists_rightMove_of_oneSided_live
    (initial : ProfiledRawJointCommonBaseWorld A strategy)
    (source : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (extra : LiteralAnnotation A)
    (hcurrent :
      ProfiledRawJointHybridLiteralPrefixCurrentCompatible A strategy hwin
        initial (.oneSided source) extra)
    (semanticMember : ProcOnePairedEntryRep strategy × A.State)
    (hlive : source.family.right () = some semanticMember) :
    ∃ move : RightMove A, extra.1 = some move := by
  rcases hcurrent with hroot | ⟨parent, old, direction, hsource, hextra⟩
  · cases hroot.1
  · cases parent with
    | common world =>
        cases direction with
        | simultaneous input =>
            simp [ProfiledRawJointHybridSemanticState.step] at hsource
        | strict actual =>
            cases hside : actual.side with
            | right =>
                have hfamily := congrArg
                  ProfiledRawJointOneSidedSemanticState.family
                  (ProfiledRawJointHybridSemanticState.oneSided.inj hsource)
                simp [profiledRawJointCommonExitState, hside] at hfamily
                rw [← hfamily] at hlive
                simp at hlive
            | left =>
                have hfamily := congrArg
                  ProfiledRawJointOneSidedSemanticState.family
                  (ProfiledRawJointHybridSemanticState.oneSided.inj hsource)
                simp [profiledRawJointCommonExitState, hside] at hfamily
                have hsemantic :
                    ((profiledRawJointCommonWorldFamily A world).semanticChild A
                      (profiledRawJointCommonActualDirection actual).direction).right () =
                        some semanticMember := by
                  have hlive' :
                      ((profiledRawJointCommonWorldFamily A world).leftActualChild A
                        (profiledRawJointCommonActualDirection actual).direction).right () =
                          some semanticMember := by
                    rw [hfamily]
                    exact hlive
                  simpa only [
                    ProfiledRawJointSemanticFamily.semanticChild_right,
                    ProfiledRawJointSemanticFamily.leftActualChild_right] using
                      hlive'
                obtain ⟨move, hmove⟩ :=
                  exists_profiledRawJointRightLiteralPrefixMoveOption_of_member
                    A strategy hwin _ _ semanticMember hsemantic
                refine ⟨move, ?_⟩
                rw [← hextra]
                simpa [profiledRawJointHybridLiteralPrefixAnnotationAdvance,
                  profiledRawJointHybridLiteralPrefixAnnotationOf] using hmove
    | oneSided parentSource =>
        cases direction with
        | simultaneous input =>
            simp [ProfiledRawJointHybridSemanticState.step] at hsource
        | strict actual =>
            cases hside : actual.side with
            | right =>
                have hfamily := congrArg
                  ProfiledRawJointOneSidedSemanticState.family
                  (ProfiledRawJointHybridSemanticState.oneSided.inj hsource)
                simp [ProfiledRawJointOneSidedSemanticState.step, hside] at hfamily
                rw [← hfamily] at hlive
                simp at hlive
            | left =>
                have hfamily := congrArg
                  ProfiledRawJointOneSidedSemanticState.family
                  (ProfiledRawJointHybridSemanticState.oneSided.inj hsource)
                simp [ProfiledRawJointOneSidedSemanticState.step, hside] at hfamily
                have hsemantic :
                    (parentSource.family.semanticChild A actual.direction).right () =
                      some semanticMember := by
                  have hlive' :
                      (parentSource.family.leftActualChild A
                        actual.direction).right () = some semanticMember := by
                    rw [hfamily]
                    exact hlive
                  simpa only [
                    ProfiledRawJointSemanticFamily.semanticChild_right,
                    ProfiledRawJointSemanticFamily.leftActualChild_right] using
                      hlive'
                obtain ⟨move, hmove⟩ :=
                  exists_profiledRawJointRightLiteralPrefixMoveOption_of_member
                    A strategy hwin _ _ semanticMember hsemantic
                refine ⟨move, ?_⟩
                rw [← hextra]
                simpa [profiledRawJointHybridLiteralPrefixAnnotationAdvance,
                  profiledRawJointHybridLiteralPrefixAnnotationOf] using hmove
    | dead =>
        cases direction <;>
          simp [ProfiledRawJointHybridSemanticState.step] at hsource

/-- Left-lane mirror. -/
theorem
    ProfiledRawJointHybridLiteralPrefixCurrentCompatible.exists_leftMove_of_oneSided_live
    (initial : ProfiledRawJointCommonBaseWorld A strategy)
    (source : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (extra : LiteralAnnotation A)
    (hcurrent :
      ProfiledRawJointHybridLiteralPrefixCurrentCompatible A strategy hwin
        initial (.oneSided source) extra)
    (semanticMember : ProcTwoPairedEntryRep strategy × A.State)
    (hlive : source.family.left () = some semanticMember) :
    ∃ move : LeftMove A, extra.2 = some move := by
  rcases hcurrent with hroot | ⟨parent, old, direction, hsource, hextra⟩
  · cases hroot.1
  · cases parent with
    | common world =>
        cases direction with
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
                      (profiledRawJointCommonActualDirection actual).direction).left () =
                        some semanticMember := by
                  have hlive' :
                      ((profiledRawJointCommonWorldFamily A world).rightActualChild A
                        (profiledRawJointCommonActualDirection actual).direction).left () =
                          some semanticMember := by
                    rw [hfamily]
                    exact hlive
                  simpa only [
                    ProfiledRawJointSemanticFamily.semanticChild_left,
                    ProfiledRawJointSemanticFamily.rightActualChild_left] using
                      hlive'
                obtain ⟨move, hmove⟩ :=
                  exists_profiledRawJointLeftLiteralPrefixMoveOption_of_member
                    A strategy hwin _ _ semanticMember hsemantic
                refine ⟨move, ?_⟩
                rw [← hextra]
                simpa [profiledRawJointHybridLiteralPrefixAnnotationAdvance,
                  profiledRawJointHybridLiteralPrefixAnnotationOf] using hmove
            | left =>
                have hfamily := congrArg
                  ProfiledRawJointOneSidedSemanticState.family
                  (ProfiledRawJointHybridSemanticState.oneSided.inj hsource)
                simp [profiledRawJointCommonExitState, hside] at hfamily
                rw [← hfamily] at hlive
                simp at hlive
    | oneSided parentSource =>
        cases direction with
        | simultaneous input =>
            simp [ProfiledRawJointHybridSemanticState.step] at hsource
        | strict actual =>
            cases hside : actual.side with
            | right =>
                have hfamily := congrArg
                  ProfiledRawJointOneSidedSemanticState.family
                  (ProfiledRawJointHybridSemanticState.oneSided.inj hsource)
                simp [ProfiledRawJointOneSidedSemanticState.step, hside] at hfamily
                have hsemantic :
                    (parentSource.family.semanticChild A actual.direction).left () =
                      some semanticMember := by
                  have hlive' :
                      (parentSource.family.rightActualChild A
                        actual.direction).left () = some semanticMember := by
                    rw [hfamily]
                    exact hlive
                  simpa only [
                    ProfiledRawJointSemanticFamily.semanticChild_left,
                    ProfiledRawJointSemanticFamily.rightActualChild_left] using
                      hlive'
                obtain ⟨move, hmove⟩ :=
                  exists_profiledRawJointLeftLiteralPrefixMoveOption_of_member
                    A strategy hwin _ _ semanticMember hsemantic
                refine ⟨move, ?_⟩
                rw [← hextra]
                simpa [profiledRawJointHybridLiteralPrefixAnnotationAdvance,
                  profiledRawJointHybridLiteralPrefixAnnotationOf] using hmove
            | left =>
                have hfamily := congrArg
                  ProfiledRawJointOneSidedSemanticState.family
                  (ProfiledRawJointHybridSemanticState.oneSided.inj hsource)
                simp [ProfiledRawJointOneSidedSemanticState.step, hside] at hfamily
                rw [← hfamily] at hlive
                simp at hlive
    | dead =>
        cases direction <;>
          simp [ProfiledRawJointHybridSemanticState.step] at hsource

/-! ## Reachable finite bank states never fall back on a live lane -/

/-- Reachability and a live right slot in the stored one-sided public code
produce the literal table and certify the executable linked lookup as its
same-occurrence rebuild. -/
theorem
    exists_profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMove_of_liveLane
    {state : BankControl A strategy hwin}
    (hreachable : BankReachable A strategy hwin state)
    (code : ProfiledRawJointIncidenceCode A (I := Unit))
    (hcode : state.2.1.1 = .oneSided code)
    (slot : ProfiledRawRightSlot A)
    (hlive : code.family.right () = some slot) :
    ∃ oldMove : RightMove A,
      (state.literal A strategy hwin).1 = some oldMove ∧
        ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRightRebuilds A
          strategy hwin state oldMove
            (state.linkedRightMove A strategy hwin) := by
  let packet :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankFiniteStep A strategy
      hwin state.1 state.2 hreachable
  obtain ⟨source, hsource, hsourceCode⟩ :=
    ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankFiniteStep.source_oneSided_of_code
      A strategy hwin hreachable code hcode
  have hsemanticLive : ∃ semanticMember,
      source.family.right () = some semanticMember := by
    cases hmember : source.family.right () with
    | none =>
        have hprojection := congrArg
          (fun current : ProfiledRawJointIncidenceCode A (I := Unit) ↦
            current.family.right ()) hsourceCode
        simp [ProfiledRawJointOneSidedSemanticState.code,
          ProfiledRawJointSemanticFamily.incidenceCode,
          ProfiledRawJointSemanticFamily.code, hmember, hlive] at hprojection
    | some semanticMember => exact ⟨semanticMember, rfl⟩
  obtain ⟨semanticMember, hmember⟩ := hsemanticLive
  have hcurrent :=
    profiledRawJointHybridLiteralPrefixCurrentCompatible_of_marked A strategy
      hwin
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankInstalled A
        strategy hwin state.1).world
      packet.source state.2.1.2.2 packet.marked_current
  rw [hsource] at hcurrent
  obtain ⟨oldMove, hmove⟩ :=
    hcurrent.exists_rightMove_of_oneSided_live A strategy hwin _ source
      state.2.1.2.2.2 semanticMember hmember
  exact ⟨oldMove, hmove,
    state.linkedRightMove_rebuilds_of_oneSided A strategy hwin hreachable code
      hcode oldMove hmove⟩

/-- Left live-lane mirror. -/
theorem
    exists_profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMove_of_liveLane
    {state : BankControl A strategy hwin}
    (hreachable : BankReachable A strategy hwin state)
    (code : ProfiledRawJointIncidenceCode A (I := Unit))
    (hcode : state.2.1.1 = .oneSided code)
    (slot : ProfiledRawLeftSlot A)
    (hlive : code.family.left () = some slot) :
    ∃ oldMove : LeftMove A,
      (state.literal A strategy hwin).2 = some oldMove ∧
        ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLeftRebuilds A
          strategy hwin state oldMove
            (state.linkedLeftMove A strategy hwin) := by
  let packet :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankFiniteStep A strategy
      hwin state.1 state.2 hreachable
  obtain ⟨source, hsource, hsourceCode⟩ :=
    ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankFiniteStep.source_oneSided_of_code
      A strategy hwin hreachable code hcode
  have hsemanticLive : ∃ semanticMember,
      source.family.left () = some semanticMember := by
    cases hmember : source.family.left () with
    | none =>
        have hprojection := congrArg
          (fun current : ProfiledRawJointIncidenceCode A (I := Unit) ↦
            current.family.left ()) hsourceCode
        simp [ProfiledRawJointOneSidedSemanticState.code,
          ProfiledRawJointSemanticFamily.incidenceCode,
          ProfiledRawJointSemanticFamily.code, hmember, hlive] at hprojection
    | some semanticMember => exact ⟨semanticMember, rfl⟩
  obtain ⟨semanticMember, hmember⟩ := hsemanticLive
  have hcurrent :=
    profiledRawJointHybridLiteralPrefixCurrentCompatible_of_marked A strategy
      hwin
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankInstalled A
        strategy hwin state.1).world
      packet.source state.2.1.2.2 packet.marked_current
  rw [hsource] at hcurrent
  obtain ⟨oldMove, hmove⟩ :=
    hcurrent.exists_leftMove_of_oneSided_live A strategy hwin _ source
      state.2.1.2.2.2 semanticMember hmember
  exact ⟨oldMove, hmove,
    state.linkedLeftMove_rebuilds_of_oneSided A strategy hwin hreachable code
      hcode oldMove hmove⟩

/-! ## Exact strict-child corollaries -/

/-- Any exact strict child whose public code exposes a live right lane enters
the certified linked rebuild branch.  Reachability of the child is inherited
from the authoritative parent, so this statement is stable across arbitrary
deferred reinstallations. -/
theorem
    exists_profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMove_of_strictChild
    (state : BankControl A strategy hwin)
    (hreachable : BankReachable A strategy hwin state)
    (actual : ProfiledRawJointActualDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (code : ProfiledRawJointIncidenceCode A (I := Unit))
    (hpublic :
      (state.childCode A strategy hwin (.strict actual)).1 = .oneSided code)
    (slot : ProfiledRawRightSlot A)
    (hlive : code.family.right () = some slot) :
    let child :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A strategy
        hwin state (.strict actual)
    ∃ oldMove : RightMove A,
      (child.literal A strategy hwin).1 = some oldMove ∧
        ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRightRebuilds A
          strategy hwin child oldMove
            (child.linkedRightMove A strategy hwin) := by
  dsimp only
  let child :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A strategy
      hwin state (.strict actual)
  have hchildReachable : BankReachable A strategy hwin child :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren_reachable A
      strategy hwin state hreachable (.strict actual)
  have hchildCode : child.2.1.1 = .oneSided code := by
    have hfull :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren_code A
        strategy hwin state hreachable (.strict actual)
    exact (congrArg Prod.fst hfull).trans hpublic
  exact
    exists_profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMove_of_liveLane
      A strategy hwin hchildReachable code hchildCode slot hlive

/-- Left strict-child mirror. -/
theorem
    exists_profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMove_of_strictChild
    (state : BankControl A strategy hwin)
    (hreachable : BankReachable A strategy hwin state)
    (actual : ProfiledRawJointActualDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (code : ProfiledRawJointIncidenceCode A (I := Unit))
    (hpublic :
      (state.childCode A strategy hwin (.strict actual)).1 = .oneSided code)
    (slot : ProfiledRawLeftSlot A)
    (hlive : code.family.left () = some slot) :
    let child :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A strategy
        hwin state (.strict actual)
    ∃ oldMove : LeftMove A,
      (child.literal A strategy hwin).2 = some oldMove ∧
        ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLeftRebuilds A
          strategy hwin child oldMove
            (child.linkedLeftMove A strategy hwin) := by
  dsimp only
  let child :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A strategy
      hwin state (.strict actual)
  have hchildReachable : BankReachable A strategy hwin child :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren_reachable A
      strategy hwin state hreachable (.strict actual)
  have hchildCode : child.2.1.1 = .oneSided code := by
    have hfull :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren_code A
        strategy hwin state hreachable (.strict actual)
    exact (congrArg Prod.fst hfull).trans hpublic
  exact
    exists_profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMove_of_liveLane
      A strategy hwin hchildReachable code hchildCode slot hlive

end

end DetParityAutomaton

end DistributedSynthesis
