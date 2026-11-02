/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedPhysicalCompatiblePolicy
import DistributedSynthesis.Formalizations.Lemma.LemProfiledRawJointFiniteCodeFailFast

/-!
# Observation-uniform linked moves for the one-sided semantic kernel

The parent-linked legality predicate used by the recurrent policy contains an
existential semantic source.  That is enough to certify one selected policy
state, but it is not the uniformity statement needed when one finite local
memory state represents several indistinguishable semantic sources.

This file states the missing condition at its exact strength.  A public move
is the complete linked move: the raw lambda family together with the finite
annotation installed at every child.  Such a move is observation-uniform on a
semantic belief precisely when every source in the belief induces that same
linked move.  Under this hypothesis, every actual direction has a nonempty
successor belief, and every member of that belief has the public child code
and compatible installed annotation selected by the common move.

The last theorem records the remaining boundary.  The successor facts do not
by themselves make the successor belief uniform for its next move.  A finite
belief-memory construction must establish that additional inductive clause;
it cannot be recovered from the existential parent-link witness.
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

private abbrev ActualDirection :=
  ProfiledRawJointActualDirection (I := Unit) (In₁ := In₁) (In₂ := In₂)

private abbrev PhysicalAnnotation :=
  ProfiledRawJointHybridPhysicalEdgeAnnotation A

private abbrev LinkedCode :=
  SourceFreeBeliefParentLinkedCode
    (BeliefCode := ProfiledRawJointIncidenceCode A (I := Unit))
    (Annotation := PhysicalAnnotation A)

private abbrev LinkedMove :=
  SourceFreeBeliefParentLinkedMove
    (Direction := ActualDirection (In₁ := In₁) (In₂ := In₂))
    (Move := ProfiledRawJointLambdaFamilyMove A (I := Unit))
    (Annotation := PhysicalAnnotation A)

/-! ## Beliefs and their common linked action -/

/-- The complete public move induced by one exact source at the currently
installed physical annotation. -/
noncomputable def profiledRawJointOneSidedSemanticLinkedMove
    (source : OneSidedState A strategy)
    (current : PhysicalAnnotation A) :
    LinkedMove A (In₁ := In₁) (In₂ := In₂) :=
  (source.move A, fun actual ↦
    profiledRawJointOneSidedPhysicalAnnotationAdvance A strategy hwin source
      current actual)

/-- A nonempty semantic belief represented by one public code and one
installed physical annotation. -/
def ProfiledRawJointOneSidedPhysicalBeliefAt
    (belief : OneSidedState A strategy → Prop)
    (publicCode : LinkedCode A) : Prop :=
  (∃ source, belief source) ∧
    ∀ source, belief source →
      source.code A = publicCode.1 ∧
        ProfiledRawJointOneSidedPhysicalAnnotationCompatible A strategy source
          publicCode.2

/-- One complete linked move is common to every exact source represented by
the belief.  Equality includes both the raw lambda family and the full table
of child annotations. -/
def ProfiledRawJointOneSidedPhysicalBeliefCommonMove
    (belief : OneSidedState A strategy → Prop)
    (current : PhysicalAnnotation A)
    (move : LinkedMove A (In₁ := In₁) (In₂ := In₂)) : Prop :=
  ∀ source, belief source →
    profiledRawJointOneSidedSemanticLinkedMove A strategy hwin source current =
      move

/-- Exact image belief after Nature chooses one actual raw direction. -/
def profiledRawJointOneSidedPhysicalBeliefSuccessor
    (belief : OneSidedState A strategy → Prop)
    (actual : ActualDirection (In₁ := In₁) (In₂ := In₂))
    (child : OneSidedState A strategy) : Prop :=
  ∃ source, belief source ∧ child = source.step A actual

/-! ## Relation with the existing existential parent link -/

/-- Parent-linked validity says exactly that one compatible source induces
the advertised complete linked move. -/
theorem
    profiledRawJointOneSidedPhysicalCompatibleParentLinkValid_iff_exists_induces
    (publicCode : LinkedCode A)
    (move : LinkedMove A (In₁ := In₁) (In₂ := In₂)) :
    ProfiledRawJointOneSidedPhysicalCompatibleParentLinkValid A strategy hwin
        publicCode.1 publicCode.2 move.1 move.2 ↔
      ∃ source : OneSidedState A strategy,
        source.code A = publicCode.1 ∧
          ProfiledRawJointOneSidedPhysicalAnnotationCompatible A strategy
            source publicCode.2 ∧
          profiledRawJointOneSidedSemanticLinkedMove A strategy hwin source
              publicCode.2 =
            move := by
  constructor
  · rintro ⟨source, hcode, hmove, hcompatible, hchildren⟩
    refine ⟨source, hcode, hcompatible, ?_⟩
    apply Prod.ext
    · exact hmove
    · funext actual
      exact hchildren actual
  · rintro ⟨source, hcode, hcompatible, hinduced⟩
    have hmove := congrArg Prod.fst hinduced
    have hchildren := congrArg Prod.snd hinduced
    refine ⟨source, hcode, ?_, hcompatible, ?_⟩
    · exact hmove
    · intro actual
      exact congrFun hchildren actual

/-- Hence the current legality invariant always yields a uniform singleton
belief.  The singleton depends on the existential source and is not yet an
observation-based finite-memory update. -/
theorem
    ProfiledRawJointOneSidedPhysicalCompatibleParentLinkValid.exists_singleton_commonBelief
    (publicCode : LinkedCode A)
    (move : LinkedMove A (In₁ := In₁) (In₂ := In₂))
    (hvalid :
      ProfiledRawJointOneSidedPhysicalCompatibleParentLinkValid A strategy
        hwin publicCode.1 publicCode.2 move.1 move.2) :
    ∃ source : OneSidedState A strategy,
      ProfiledRawJointOneSidedPhysicalBeliefAt A strategy
          (fun candidate ↦ candidate = source) publicCode ∧
        ProfiledRawJointOneSidedPhysicalBeliefCommonMove A strategy hwin
          (fun candidate ↦ candidate = source) publicCode.2 move := by
  rw [profiledRawJointOneSidedPhysicalCompatibleParentLinkValid_iff_exists_induces]
    at hvalid
  rcases hvalid with ⟨source, hcode, hcompatible, hinduced⟩
  refine ⟨source, ?_, ?_⟩
  · constructor
    · exact ⟨source, rfl⟩
    · intro candidate hcandidate
      subst candidate
      exact ⟨hcode, hcompatible⟩
  · intro candidate hcandidate
    subst candidate
    exact hinduced

/-- Conversely, a common move on any nonempty compatible belief supplies the
existing parent-link witness. -/
theorem
    profiledRawJointOneSidedPhysicalCompatibleParentLinkValid_of_commonBelief
    (belief : OneSidedState A strategy → Prop)
    (publicCode : LinkedCode A)
    (move : LinkedMove A (In₁ := In₁) (In₂ := In₂))
    (hbelief : ProfiledRawJointOneSidedPhysicalBeliefAt A strategy belief
      publicCode)
    (hcommon : ProfiledRawJointOneSidedPhysicalBeliefCommonMove A strategy
      hwin belief publicCode.2 move) :
    ProfiledRawJointOneSidedPhysicalCompatibleParentLinkValid A strategy hwin
      publicCode.1 publicCode.2 move.1 move.2 := by
  rcases hbelief.1 with ⟨source, hsource⟩
  rw [profiledRawJointOneSidedPhysicalCompatibleParentLinkValid_iff_exists_induces]
  exact ⟨source, (hbelief.2 source hsource).1,
    (hbelief.2 source hsource).2, hcommon source hsource⟩

/-! ## Exact successor closure -/

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Every direction has an exact successor witness because the parent belief
is nonempty. -/
theorem profiledRawJointOneSidedPhysicalBeliefSuccessor_nonempty
    (belief : OneSidedState A strategy → Prop)
    (publicCode : LinkedCode A)
    (hbelief : ProfiledRawJointOneSidedPhysicalBeliefAt A strategy belief
      publicCode)
    (actual : ActualDirection (In₁ := In₁) (In₂ := In₂)) :
    ∃ child,
      profiledRawJointOneSidedPhysicalBeliefSuccessor A strategy belief actual
        child := by
  rcases hbelief.1 with ⟨source, hsource⟩
  exact ⟨source.step A actual, source, hsource, rfl⟩

/-- Under a common linked move, every exact successor has the one public
child code selected by that move. -/
theorem profiledRawJointOneSidedPhysicalBeliefSuccessor_code
    (belief : OneSidedState A strategy → Prop)
    (publicCode : LinkedCode A)
    (move : LinkedMove A (In₁ := In₁) (In₂ := In₂))
    (hbelief : ProfiledRawJointOneSidedPhysicalBeliefAt A strategy belief
      publicCode)
    (hcommon : ProfiledRawJointOneSidedPhysicalBeliefCommonMove A strategy
      hwin belief publicCode.2 move)
    (actual : ActualDirection (In₁ := In₁) (In₂ := In₂))
    (child : OneSidedState A strategy)
    (hchild : profiledRawJointOneSidedPhysicalBeliefSuccessor A strategy belief
      actual child) :
    child.code A =
      (sourceFreeBeliefParentLinkedNext
        (profiledRawJointOneSidedNext A) publicCode move actual).1 := by
  rcases hchild with ⟨source, hsource, rfl⟩
  have hinduced := hcommon source hsource
  have hmove : source.move A = move.1 := congrArg Prod.fst hinduced
  rw [ProfiledRawJointOneSidedSemanticState.step_code,
    (hbelief.2 source hsource).1, hmove]
  rfl

/-- The child annotation selected by the common move is compatible with every
exact successor source, not merely with one representative. -/
theorem profiledRawJointOneSidedPhysicalBeliefSuccessor_compatible
    (belief : OneSidedState A strategy → Prop)
    (publicCode : LinkedCode A)
    (move : LinkedMove A (In₁ := In₁) (In₂ := In₂))
    (hcommon : ProfiledRawJointOneSidedPhysicalBeliefCommonMove A strategy
      hwin belief publicCode.2 move)
    (actual : ActualDirection (In₁ := In₁) (In₂ := In₂))
    (child : OneSidedState A strategy)
    (hchild : profiledRawJointOneSidedPhysicalBeliefSuccessor A strategy belief
      actual child) :
    ProfiledRawJointOneSidedPhysicalAnnotationCompatible A strategy child
      (sourceFreeBeliefParentLinkedNext
        (profiledRawJointOneSidedNext A) publicCode move actual).2 := by
  rcases hchild with ⟨source, hsource, rfl⟩
  have hinduced := hcommon source hsource
  have hchildren := congrArg Prod.snd hinduced
  change ProfiledRawJointOneSidedPhysicalAnnotationCompatible A strategy
    (source.step A actual) (move.2 actual)
  rw [← congrFun hchildren actual]
  exact profiledRawJointOneSidedPhysicalAnnotationAdvance_compatible A strategy
    hwin source publicCode.2 actual

/-- The exact successor image is again a nonempty compatible belief at the
public child selected by the common move. -/
theorem profiledRawJointOneSidedPhysicalBeliefSuccessor_closed
    (belief : OneSidedState A strategy → Prop)
    (publicCode : LinkedCode A)
    (move : LinkedMove A (In₁ := In₁) (In₂ := In₂))
    (hbelief : ProfiledRawJointOneSidedPhysicalBeliefAt A strategy belief
      publicCode)
    (hcommon : ProfiledRawJointOneSidedPhysicalBeliefCommonMove A strategy
      hwin belief publicCode.2 move)
    (actual : ActualDirection (In₁ := In₁) (In₂ := In₂)) :
    ProfiledRawJointOneSidedPhysicalBeliefAt A strategy
      (profiledRawJointOneSidedPhysicalBeliefSuccessor A strategy belief
        actual)
      (sourceFreeBeliefParentLinkedNext
        (profiledRawJointOneSidedNext A) publicCode move actual) := by
  constructor
  · exact profiledRawJointOneSidedPhysicalBeliefSuccessor_nonempty A strategy
      belief publicCode hbelief actual
  · intro child hchild
    exact ⟨
      profiledRawJointOneSidedPhysicalBeliefSuccessor_code A strategy hwin
        belief publicCode move hbelief hcommon actual child hchild,
      profiledRawJointOneSidedPhysicalBeliefSuccessor_compatible A strategy hwin
        belief publicCode move hcommon actual child hchild⟩

/-! ## Fail-fast boundary -/

/-- Two represented sources inducing different complete linked moves rule out
an observation-uniform action on that belief. -/
theorem not_exists_profiledRawJointOneSidedPhysicalBeliefCommonMove_of_collision
    (belief : OneSidedState A strategy → Prop)
    (current : PhysicalAnnotation A)
    (left right : OneSidedState A strategy)
    (hleft : belief left)
    (hright : belief right)
    (hcollision :
      profiledRawJointOneSidedSemanticLinkedMove A strategy hwin left current ≠
        profiledRawJointOneSidedSemanticLinkedMove A strategy hwin right
          current) :
    ¬ ∃ move : LinkedMove A (In₁ := In₁) (In₂ := In₂),
      ProfiledRawJointOneSidedPhysicalBeliefCommonMove A strategy hwin belief
        current move := by
  rintro ⟨move, hcommon⟩
  exact hcollision ((hcommon left hleft).trans (hcommon right hright).symm)

/-- Successor compatibility is not the next-action uniformity premise.  The
precise additional induction obligation is that every successor belief admit
some complete common linked move at its newly installed annotation. -/
def ProfiledRawJointOneSidedPhysicalBeliefCommonMoveClosed
    (belief : OneSidedState A strategy → Prop)
    (publicCode : LinkedCode A)
    (move : LinkedMove A (In₁ := In₁) (In₂ := In₂)) : Prop :=
  ∀ actual : ActualDirection (In₁ := In₁) (In₂ := In₂),
    ∃ nextMove : LinkedMove A (In₁ := In₁) (In₂ := In₂),
      ProfiledRawJointOneSidedPhysicalBeliefCommonMove A strategy hwin
        (profiledRawJointOneSidedPhysicalBeliefSuccessor A strategy belief
          actual)
        (sourceFreeBeliefParentLinkedNext
          (profiledRawJointOneSidedNext A) publicCode move actual).2
        nextMove

/-! ## The current public code fails the strong test -/

/-- Put one of the two reachable collision entries into a literal singleton
right family. -/
def rawJointCommonActionCollisionFamily
    (entry : ProcOnePairedEntryRep rawJointCodeCollisionStrategy) :
    ProfiledRawJointSemanticFamily rawJointCodeCollisionDPA
      rawJointCodeCollisionStrategy (I := Unit) where
  right := fun _ ↦ some (entry, ())
  left := fun _ ↦ none
  right_view_shared := by
    intro leftIndex rightIndex leftMember rightMember hleft hright
    cases leftIndex
    cases rightIndex
    simp at hleft hright
    subst leftMember
    subst rightMember
    rfl
  left_view_shared := by simp

/-- The singleton family is one-sided exact because its opposite lane is
empty. -/
def rawJointCommonActionCollisionState
    (entry : ProcOnePairedEntryRep rawJointCodeCollisionStrategy) :
    ProfiledRawJointOneSidedSemanticState rawJointCodeCollisionDPA
      rawJointCodeCollisionStrategy (I := Unit) where
  family := rawJointCommonActionCollisionFamily entry
  exactFibre := by
    intro direction
    constructor
    · intro rightIndex rightMember leftPivotMember hright hleft
      simp [rawJointCommonActionCollisionFamily] at hleft
    · intro leftIndex leftMember rightPivotMember hleft hright
      simp [rawJointCommonActionCollisionFamily] at hleft

abbrev rawJointCommonActionCollisionStateZero :=
  rawJointCommonActionCollisionState rawJointCodeCollisionEntryZero

abbrev rawJointCommonActionCollisionStateOne :=
  rawJointCommonActionCollisionState rawJointCodeCollisionEntryOne

private theorem rawJointFamilyCode_eq_of_fields
    (left right : ProfiledRawJointFamilyCode rawJointCodeCollisionDPA
      (I := Unit))
    (hright : left.right = right.right)
    (hleft : left.left = right.left)
    (hrightPattern : left.rightPattern = right.rightPattern)
    (hleftPattern : left.leftPattern = right.leftPattern) :
    left = right := by
  cases left
  cases right
  simp_all

/-- The two singleton semantic families have the same complete incidence
code, including both row-equality matrices and the cross matrix. -/
theorem rawJointCommonActionCollision_sameCode :
    rawJointCommonActionCollisionStateZero.code rawJointCodeCollisionDPA =
      rawJointCommonActionCollisionStateOne.code rawJointCodeCollisionDPA := by
  apply ProfiledRawJointIncidenceCode.eq_of_fields
  · apply rawJointFamilyCode_eq_of_fields
    · funext index
      cases index
      simpa [rawJointCommonActionCollisionStateZero,
        rawJointCommonActionCollisionStateOne,
        rawJointCommonActionCollisionState,
        rawJointCommonActionCollisionFamily,
        ProfiledRawJointOneSidedSemanticState.code,
        ProfiledRawJointSemanticFamily.incidenceCode,
        ProfiledRawJointSemanticFamily.code,
        rawJointCodeCollisionSlot] using
        congrArg some rawJointCodeCollision_sameSlot
    · rfl
    · funext left right
      rcases left with ⟨leftIndex, leftRow⟩
      rcases right with ⟨rightIndex, rightRow⟩
      cases leftIndex
      cases rightIndex
      cases leftRow <;> cases rightRow <;>
        simp [rawJointCommonActionCollisionStateZero,
          rawJointCommonActionCollisionStateOne,
          rawJointCommonActionCollisionState,
          rawJointCommonActionCollisionFamily,
          ProfiledRawJointOneSidedSemanticState.code,
          ProfiledRawJointSemanticFamily.incidenceCode,
          ProfiledRawJointSemanticFamily.code,
          ProfiledRawJointSemanticFamily.rightPattern,
          profiledRawProcOneRowHistory,
          rawJointCodeCollisionEntryZero.other_view_ne,
          rawJointCodeCollisionEntryZero.other_view_ne.symm,
          rawJointCodeCollisionEntryOne.other_view_ne,
          rawJointCodeCollisionEntryOne.other_view_ne.symm]
    · rfl
  · rfl

/-- The corresponding raw family moves differ, already in the blind output
of their unique right lambda. -/
theorem rawJointCommonActionCollision_moves_ne :
    rawJointCommonActionCollisionStateZero.move rawJointCodeCollisionDPA ≠
      rawJointCommonActionCollisionStateOne.move rawJointCodeCollisionDPA := by
  intro hmoves
  have hright := congrArg
    (fun move ↦ move.rightLambda ()) hmoves
  have hlambda :
      rawJointCodeCollisionEntryZero.lambdaOfStrategy =
        rawJointCodeCollisionEntryOne.lambdaOfStrategy := by
    simpa [rawJointCommonActionCollisionStateZero,
      rawJointCommonActionCollisionStateOne,
      rawJointCommonActionCollisionState,
      rawJointCommonActionCollisionFamily,
      ProfiledRawJointOneSidedSemanticState.move,
      ProfiledRawJointSemanticFamily.move] using hright
  exact rawJointCodeCollision_incompatibleBlindLambdas
    (congrArg (fun lambda ↦ lambda.blind) hlambda)

/-- With the empty installed annotation, compatibility is vacuous for both
collision sources. -/
theorem rawJointCommonActionCollision_compatible
    (source :
      ProfiledRawJointOneSidedSemanticState rawJointCodeCollisionDPA
        rawJointCodeCollisionStrategy (I := Unit)) :
    ProfiledRawJointOneSidedPhysicalAnnotationCompatible
      rawJointCodeCollisionDPA rawJointCodeCollisionStrategy source
      (none, none) := by
  constructor <;> intro semanticMember hmember move hmove <;>
    simp at hmove

/-- The public code and installed annotation therefore support a genuine
two-source belief. -/
theorem rawJointCommonActionCollision_beliefAt :
    ProfiledRawJointOneSidedPhysicalBeliefAt rawJointCodeCollisionDPA
      rawJointCodeCollisionStrategy
      (fun source ↦ source = rawJointCommonActionCollisionStateZero ∨
        source = rawJointCommonActionCollisionStateOne)
      (rawJointCommonActionCollisionStateZero.code
          rawJointCodeCollisionDPA,
        (none, none)) := by
  constructor
  · exact ⟨rawJointCommonActionCollisionStateZero, Or.inl rfl⟩
  · intro source hsource
    rcases hsource with rfl | rfl
    · exact ⟨rfl, rawJointCommonActionCollision_compatible _⟩
    · exact ⟨rawJointCommonActionCollision_sameCode.symm,
        rawJointCommonActionCollision_compatible _⟩

/-- Thus the current public code does not determine a common literal linked
move, even for two genuine strategy-generated entries of a winning strategy.
This refutes code-only homogeneity; it does not refute a finite refinement
whose memory separates the two sources. -/
theorem rawJointCommonActionCollision_noCommonMove :
    ¬ ∃ move : SourceFreeBeliefParentLinkedMove
        (Direction := ProfiledRawJointActualDirection
          (I := Unit) (In₁ := Unit) (In₂ := Unit))
        (Move := ProfiledRawJointLambdaFamilyMove rawJointCodeCollisionDPA
          (I := Unit))
        (Annotation := ProfiledRawJointHybridPhysicalEdgeAnnotation
          rawJointCodeCollisionDPA),
      ProfiledRawJointOneSidedPhysicalBeliefCommonMove
        rawJointCodeCollisionDPA rawJointCodeCollisionStrategy
        rawJointCodeCollisionStrategy_wins
        (fun source ↦ source = rawJointCommonActionCollisionStateZero ∨
          source = rawJointCommonActionCollisionStateOne)
        (none, none) move := by
  apply
    not_exists_profiledRawJointOneSidedPhysicalBeliefCommonMove_of_collision
      rawJointCodeCollisionDPA rawJointCodeCollisionStrategy
        rawJointCodeCollisionStrategy_wins
      (fun source ↦ source = rawJointCommonActionCollisionStateZero ∨
        source = rawJointCommonActionCollisionStateOne)
      (none, none)
      rawJointCommonActionCollisionStateZero
      rawJointCommonActionCollisionStateOne
      (Or.inl rfl) (Or.inr rfl)
  intro hlinked
  apply rawJointCommonActionCollision_moves_ne
  exact congrArg Prod.fst hlinked

end

end DetParityAutomaton

end DistributedSynthesis
