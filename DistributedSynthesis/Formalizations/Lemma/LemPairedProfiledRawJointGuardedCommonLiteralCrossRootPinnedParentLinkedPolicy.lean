/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCrossRootPinnedPackage
import DistributedSynthesis.Formalizations.Lemma.LemSourceFreeBeliefParentLinkedFiniteAnnotation

/-!
# A root-pinned, parent-linked literal-cross policy

The one-shot root guard fixes the represented predecessor occurrence, but an
ordinary tail may still choose an unrelated valid move at an equal-code child.
That is insufficient for the second record of the entry bootstrap: the record
was extracted at the literal predecessor and therefore refers to its literal
child occurrence.

This file repairs that precise loss of provenance.  The public finite code is
enriched by the guarded pair and the two literal-cross table IDs selected by
the parent.  A parent-linked transition copies the exact annotation chosen for
each child into the child's finite state.  The one-shot root guard additionally
pins the complete root move, including its finite table of child annotations.
Consequently the state reached by the entry input carries the guarded pair and
cross tables of the literal entry child, and every legal move at that state is
tied to the same annotation.

The semantic point is used only to construct and verify the finite policy.
No endpoint transition receives a graph, orientation, leader bit, history, or
semantic representative.
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

private abbrev CommonPoint :=
  ProfiledRawJointGuardedCommonSemanticPoint A strategy

private abbrev CommonCode :=
  ProfiledRawJointIncidenceCode A (I := Unit)

private abbrev CommonPair :=
  ProfiledRawJointGuardedCommonPair A strategy hwin

private abbrev CrossExtra :=
  ProfiledRawJointGuardedCommonLiteralCrossExtra A

/-- The finite occurrence annotation needed at a bootstrap boundary. -/
abbrev ProfiledRawJointGuardedCommonLiteralCrossLinkedAnnotation :=
  CommonPair A strategy hwin × CrossExtra A

noncomputable instance
    profiledRawJointGuardedCommonLiteralCrossLinkedAnnotationFintype :
    Fintype
      (ProfiledRawJointGuardedCommonLiteralCrossLinkedAnnotation A strategy
        hwin) := by
  infer_instance

private abbrev Annotation :=
  ProfiledRawJointGuardedCommonLiteralCrossLinkedAnnotation A strategy hwin

/-- Exact annotation of one literal semantic occurrence. -/
noncomputable def profiledRawJointGuardedCommonLiteralCrossLinkedAnnotationOf
    (point : CommonPoint A strategy) : Annotation A strategy hwin :=
  (point.move A strategy hwin,
    profiledRawJointGuardedCommonLiteralCrossExtraOfPoint A strategy hwin
      point)

/-- One semantic occurrence simultaneously explains the current annotation,
the selected guarded pair, and every child annotation. -/
def ProfiledRawJointGuardedCommonLiteralCrossParentLinkValid
    (code : CommonCode A)
    (current : Annotation A strategy hwin)
    (move : CommonPair A strategy hwin)
    (children : (In₁ × In₂) → Annotation A strategy hwin) : Prop :=
  ∃ point : CommonPoint A strategy,
    point.code A strategy = code ∧
      profiledRawJointGuardedCommonLiteralCrossLinkedAnnotationOf A strategy
          hwin point = current ∧
        point.move A strategy hwin = move ∧
          ∀ input,
            profiledRawJointGuardedCommonLiteralCrossLinkedAnnotationOf A
                strategy hwin (point.step A strategy input) =
              children input

/-- Literal semantic nodes satisfy the parent-link law with themselves as the
single witness for all advertised fields. -/
theorem
    profiledRawJointGuardedCommonLiteralCrossParentLinkValid_of_semantic
    (point : CommonPoint A strategy) :
    ProfiledRawJointGuardedCommonLiteralCrossParentLinkValid A strategy hwin
      (point.code A strategy)
      (profiledRawJointGuardedCommonLiteralCrossLinkedAnnotationOf A strategy
        hwin point)
      (point.move A strategy hwin)
      (fun input ↦
        profiledRawJointGuardedCommonLiteralCrossLinkedAnnotationOf A strategy
          hwin (point.step A strategy input)) := by
  exact ⟨point, rfl, rfl, rfl, fun _ ↦ rfl⟩

private abbrev LinkedCode :=
  SourceFreeBeliefParentLinkedCode
    (BeliefCode := CommonCode A)
    (Annotation := Annotation A strategy hwin)

private abbrev LinkedMove :=
  SourceFreeBeliefParentLinkedMove
    (Direction := In₁ × In₂)
    (Move := CommonPair A strategy hwin)
    (Annotation := Annotation A strategy hwin)

private noncomputable abbrev LinkedDPA
    (initial : CommonPoint A strategy) :=
  sourceFreeBeliefParentLinkedCodeParityDPA
    (Annotation := Annotation A strategy hwin)
    (profiledRawJointGuardedCommonCodeParityDPA A
      (initial.code A strategy))

private abbrev LinkedValid :=
  sourceFreeBeliefParentLinkedValid
    (ProfiledRawJointGuardedCommonMoveValid A strategy hwin)
    (ProfiledRawJointGuardedCommonLiteralCrossParentLinkValid A strategy hwin)

private noncomputable abbrev LinkedNext :
    LinkedCode A strategy hwin → LinkedMove A strategy hwin →
      (In₁ × In₂) → LinkedCode A strategy hwin :=
  sourceFreeBeliefParentLinkedNext
    (Annotation := Annotation A strategy hwin)
    (profiledRawJointGuardedCommonNext A strategy hwin)

/-! Public aliases used by the finite tail-key interface.  Keeping these
aliases here prevents downstream modules from reconstructing the fairly long
generic parent-link instantiation. -/

abbrev ProfiledRawJointGuardedCommonLiteralCrossParentLinkedCode :=
  LinkedCode A strategy hwin

abbrev ProfiledRawJointGuardedCommonLiteralCrossParentLinkedMove :=
  LinkedMove A strategy hwin

noncomputable abbrev
    ProfiledRawJointGuardedCommonLiteralCrossParentLinkedDPA
    (initial : CommonPoint A strategy) :=
  LinkedDPA A strategy hwin initial

abbrev ProfiledRawJointGuardedCommonLiteralCrossParentLinkedValid :=
  LinkedValid A strategy hwin

noncomputable abbrev
    profiledRawJointGuardedCommonLiteralCrossParentLinkedNext :=
  LinkedNext A strategy hwin

/-- The root predicate fixes not only the predecessor's current annotation,
but also the complete finite child-annotation table. -/
def profiledRawJointGuardedCommonLiteralCrossParentLinkedRootPred
    (initial : CommonPoint A strategy)
    (move : LinkedMove A strategy hwin) : Prop :=
  move =
    (initial.move A strategy hwin,
      fun input ↦
        profiledRawJointGuardedCommonLiteralCrossLinkedAnnotationOf A strategy
          hwin (initial.step A strategy input))

/-- Root-pinned policy on the parent-linked finite code. -/
noncomputable abbrev
    ProfiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedPolicy
    (initial : CommonPoint A strategy) :=
  SourceFreeBeliefCodeParityRootPinnedPolicy
    (LinkedDPA A strategy hwin initial)
    ((initial.code A strategy),
      profiledRawJointGuardedCommonLiteralCrossLinkedAnnotationOf A strategy
        hwin initial)
    (LinkedValid A strategy hwin)
    (LinkedNext A strategy hwin)
    (profiledRawJointGuardedCommonLiteralCrossParentLinkedRootPred A strategy
      hwin initial)

/-- The linked semantic certificate and the finite direction alphabet give an
unconditional root-pinned parent-linked policy. -/
theorem
    nonempty_profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedPolicy
    (initial : CommonPoint A strategy) :
    Nonempty
      (ProfiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedPolicy A
        strategy hwin initial) := by
  let annotation : CommonPoint A strategy → Annotation A strategy hwin :=
    profiledRawJointGuardedCommonLiteralCrossLinkedAnnotationOf A strategy hwin
  let raw := profiledRawJointGuardedCommonSemanticTree A strategy hwin initial
  let baseCertificate :=
    profiledRawJointGuardedCommonSemanticTree_codeParityCertificate A strategy
      hwin initial
  let linked := raw.parentLinkFiniteAnnotation annotation
  let linkedCertificate := baseCertificate.parentLinkFiniteAnnotation
    (profiledRawJointGuardedCommonCodeParityDPA A
      (initial.code A strategy))
    (initial.code A strategy)
    (ProfiledRawJointGuardedCommonMoveValid A strategy hwin)
    (profiledRawJointGuardedCommonNext A strategy hwin)
    raw annotation
    (ProfiledRawJointGuardedCommonLiteralCrossParentLinkValid A strategy hwin)
    (fun node ↦
      profiledRawJointGuardedCommonLiteralCrossParentLinkValid_of_semantic A
        strategy hwin (raw.stateAt node))
  exact linkedCertificate.nonempty_rootPinnedRationalPolicy_of_finite
    (LinkedDPA A strategy hwin initial)
    ((initial.code A strategy), annotation initial)
    (LinkedValid A strategy hwin)
    (LinkedNext A strategy hwin)
    linked
    (profiledRawJointGuardedCommonLiteralCrossParentLinkedRootPred A strategy
      hwin initial)
    rfl

/-- Canonical finite package used by the executable construction. -/
noncomputable def
    profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedPolicy
    (initial : CommonPoint A strategy) :
    ProfiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedPolicy A
      strategy hwin initial :=
  Classical.choice
    (nonempty_profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedPolicy
      A strategy hwin initial)

/-- The selected root move contains the exact literal child annotation for
every possible entry input. -/
@[simp] theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedPolicy_rootMove
    (initial : CommonPoint A strategy) :
    (profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedPolicy A
      strategy hwin initial).rootMove =
      (initial.move A strategy hwin,
        fun input ↦
          profiledRawJointGuardedCommonLiteralCrossLinkedAnnotationOf A
            strategy hwin (initial.step A strategy input)) :=
  (profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedPolicy A
    strategy hwin initial).rootMove_realizes.2.1

/-- Exact child state after the entry edge.  In addition to the literal child
code, its public linked-code component contains that child's guarded pair and
literal-cross table IDs. -/
theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedPolicy_successor
    (initial : CommonPoint A strategy) (input : In₁ × In₂) :
    let package :=
      profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedPolicy A
        strategy hwin initial
    let linkedChild : LinkedCode A strategy hwin :=
      ((initial.step A strategy input).code A strategy,
        profiledRawJointGuardedCommonLiteralCrossLinkedAnnotationOf A strategy
          hwin (initial.step A strategy input))
    package.policy.successor
        (true,
          (sourceFreeBeliefCodeParityRunAutomaton
            (LinkedDPA A strategy hwin initial)
            ((initial.code A strategy),
              profiledRawJointGuardedCommonLiteralCrossLinkedAnnotationOf A
                strategy hwin initial)
            (LinkedValid A strategy hwin)
            (LinkedNext A strategy hwin)).initial)
        input =
      (false,
        (linkedChild,
          (LinkedDPA A strategy hwin initial).step
            (LinkedDPA A strategy hwin initial).initial linkedChild)) := by
  dsimp only
  have hroot :=
    (profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedPolicy A
      strategy hwin initial).rootMove_realizes.2.2 input
  rw [
    profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedPolicy_rootMove
      A strategy hwin initial] at hroot
  have hchild :
      LinkedNext A strategy hwin
          ((initial.code A strategy),
            profiledRawJointGuardedCommonLiteralCrossLinkedAnnotationOf A
              strategy hwin initial)
          (initial.move A strategy hwin,
            fun next ↦
              profiledRawJointGuardedCommonLiteralCrossLinkedAnnotationOf A
                strategy hwin (initial.step A strategy next)) input =
        ((initial.step A strategy input).code A strategy,
          profiledRawJointGuardedCommonLiteralCrossLinkedAnnotationOf A
            strategy hwin (initial.step A strategy input)) := by
    apply Prod.ext
    · exact
        (ProfiledRawJointGuardedCommonSemanticPoint.step_code A strategy hwin
          initial input).symm
    · rfl
  rw [hchild] at hroot
  exact hroot

/-! ## The exact linked entry state -/

private noncomputable abbrev LinkedRunAutomaton
    (initial : CommonPoint A strategy) :=
  sourceFreeBeliefCodeParityRunAutomaton
    (LinkedDPA A strategy hwin initial)
    ((initial.code A strategy),
      profiledRawJointGuardedCommonLiteralCrossLinkedAnnotationOf A strategy
        hwin initial)
    (LinkedValid A strategy hwin)
    (LinkedNext A strategy hwin)

/-- Ordinary finite run state below the fresh root bit. -/
noncomputable abbrev
    ProfiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedRunState
    (initial : CommonPoint A strategy) :=
  (LinkedRunAutomaton A strategy hwin initial).State

/-- Public state space of the selected one-shot parent-linked policy. -/
noncomputable abbrev
    ProfiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedState
    (initial : CommonPoint A strategy) :=
  Bool ×
    ProfiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedRunState A
      strategy hwin initial

/-- Finite guarded-policy state reached by consuming the actual entry input. -/
noncomputable def
    profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedEntryState
    (initial : CommonPoint A strategy) (input : In₁ × In₂) :
    ProfiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedState A
      strategy hwin initial :=
  (profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedPolicy A
    strategy hwin initial).policy.run [input]

/-- The entry state is not merely equal-code: its annotation is definitionally
the guarded pair and literal-cross table pair of the literal child. -/
theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedEntryState_eq
    (initial : CommonPoint A strategy) (input : In₁ × In₂) :
    profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedEntryState A
        strategy hwin initial input =
      let linkedChild : LinkedCode A strategy hwin :=
        ((initial.step A strategy input).code A strategy,
          profiledRawJointGuardedCommonLiteralCrossLinkedAnnotationOf A
            strategy hwin (initial.step A strategy input))
      (false,
        (linkedChild,
          (LinkedDPA A strategy hwin initial).step
            (LinkedDPA A strategy hwin initial).initial linkedChild)) := by
  dsimp only
  let package :=
    profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedPolicy A
      strategy hwin initial
  calc
    package.policy.run [input] =
        package.policy.successor (package.policy.run []) input := by
      simpa using (package.policy.successor_at [] input).symm
    _ = package.policy.successor
        (true, (LinkedRunAutomaton A strategy hwin initial).initial) input := by
      have hinitial : package.policy.run [] =
          (true, (LinkedRunAutomaton A strategy hwin initial).initial) :=
        package.policy.accepts.1.1
      rw [hinitial]
    _ = _ :=
      profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedPolicy_successor
        A strategy hwin initial input

/-- The guarded-pair coordinate of the entry state is the pair of the
literal simultaneous child selected by the pinned predecessor. -/
@[simp] theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedEntryState_pair
    (initial : CommonPoint A strategy) (input : In₁ × In₂) :
    (profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedEntryState A
      strategy hwin initial input).2.1.2.1 =
      (initial.step A strategy input).move A strategy hwin := by
  rw [
    profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedEntryState_eq]
  rfl

/-- The literal-cross coordinate of the same state is the table pair of that
same literal child occurrence. -/
@[simp] theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedEntryState_extra
    (initial : CommonPoint A strategy) (input : In₁ × In₂) :
    (profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedEntryState A
      strategy hwin initial input).2.1.2.2 =
      profiledRawJointGuardedCommonLiteralCrossExtraOfPoint A strategy hwin
        (initial.step A strategy input) := by
  rw [
    profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedEntryState_eq]
  rfl

/-- Legality at the entry child can no longer select a move from an unrelated
equal-code occurrence.  The selected guarded pair is forced by the annotation
that the pinned predecessor installed at this exact child. -/
theorem
    exists_profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedEntryMove
    (initial : CommonPoint A strategy) (input : In₁ × In₂) :
    ∃ move : LinkedMove A strategy hwin,
      move.1 = (initial.step A strategy input).move A strategy hwin ∧
        LinkedValid A strategy hwin
          (((initial.step A strategy input).code A strategy,
            profiledRawJointGuardedCommonLiteralCrossLinkedAnnotationOf A
              strategy hwin (initial.step A strategy input))) move := by
  let package :=
    profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedPolicy A
      strategy hwin initial
  let entryState :=
    profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedEntryState A
      strategy hwin initial input
  have hlegal := package.policy.legal_at [input]
  change (LinkedRunAutomaton A strategy hwin initial |>.rootGuarded
    (sourceFreeBeliefCodeParityRootAllowed
      (LinkedDPA A strategy hwin initial)
      ((initial.code A strategy),
        profiledRawJointGuardedCommonLiteralCrossLinkedAnnotationOf A strategy
          hwin initial)
      (LinkedValid A strategy hwin)
      (LinkedNext A strategy hwin)
      (profiledRawJointGuardedCommonLiteralCrossParentLinkedRootPred A strategy
        hwin initial))).delta entryState PUnit.unit
          (package.policy.successor entryState) at hlegal
  have hentry : entryState =
      (false,
        (((initial.step A strategy input).code A strategy,
          profiledRawJointGuardedCommonLiteralCrossLinkedAnnotationOf A
            strategy hwin (initial.step A strategy input)),
          (LinkedDPA A strategy hwin initial).step
            (LinkedDPA A strategy hwin initial).initial
            (((initial.step A strategy input).code A strategy,
              profiledRawJointGuardedCommonLiteralCrossLinkedAnnotationOf A
                strategy hwin (initial.step A strategy input))))) :=
    profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedEntryState_eq
      A strategy hwin initial input
  rw [hentry] at hlegal
  change ∃ next : (In₁ × In₂) →
      (LinkedRunAutomaton A strategy hwin initial).State,
    (∃ move : LinkedMove A strategy hwin,
      LinkedValid A strategy hwin
          (((initial.step A strategy input).code A strategy,
            profiledRawJointGuardedCommonLiteralCrossLinkedAnnotationOf A
              strategy hwin (initial.step A strategy input))) move ∧
        ∀ direction : In₁ × In₂,
          let childCode := LinkedNext A strategy hwin
            (((initial.step A strategy input).code A strategy,
              profiledRawJointGuardedCommonLiteralCrossLinkedAnnotationOf A
                strategy hwin (initial.step A strategy input))) move direction
          next direction =
            (childCode,
              (LinkedDPA A strategy hwin initial).step
                ((LinkedDPA A strategy hwin initial).step
                  (LinkedDPA A strategy hwin initial).initial
                  (((initial.step A strategy input).code A strategy,
                    profiledRawJointGuardedCommonLiteralCrossLinkedAnnotationOf
                      A strategy hwin
                        (initial.step A strategy input)))) childCode)) ∧
      package.policy.successor
          (false,
            (((initial.step A strategy input).code A strategy,
              profiledRawJointGuardedCommonLiteralCrossLinkedAnnotationOf A
                strategy hwin (initial.step A strategy input)),
              (LinkedDPA A strategy hwin initial).step
                (LinkedDPA A strategy hwin initial).initial
                (((initial.step A strategy input).code A strategy,
                  profiledRawJointGuardedCommonLiteralCrossLinkedAnnotationOf
                    A strategy hwin (initial.step A strategy input))))) =
        fun direction ↦ (false, next direction) at hlegal
  rcases hlegal with ⟨next, ⟨move, hvalid, _hnext⟩, _htable⟩
  rcases hvalid.2 with
    ⟨point, _hcode, hannotation, hmove, _hchildren⟩
  have hpair := congrArg Prod.fst hannotation
  refine ⟨move, ?_, hvalid⟩
  calc
    move.1 = point.move A strategy hwin := hmove.symm
    _ = (initial.step A strategy input).move A strategy hwin := by
      simpa [profiledRawJointGuardedCommonLiteralCrossLinkedAnnotationOf]
        using hpair

/-- Total finite lookup of the move selected by the parent-linked policy at
the exact entry child.  This is a controller-table lookup; the semantic point
is used only in the proof that the table is legal. -/
noncomputable def
    profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedEntryMoveAt
    (initial : CommonPoint A strategy) (input : In₁ × In₂) :=
  Classical.choose
    (exists_profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedEntryMove
      A strategy hwin initial input)

/-- The selected entry move has the exact guarded pair stored by the pinned
predecessor and is legal at the exact parent-linked child code. -/
theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedEntryMoveAt_realizes
    (initial : CommonPoint A strategy) (input : In₁ × In₂) :
    let move :=
      profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedEntryMoveAt
        A strategy hwin initial input
    move.1 = (initial.step A strategy input).move A strategy hwin ∧
      LinkedValid A strategy hwin
        (((initial.step A strategy input).code A strategy,
          profiledRawJointGuardedCommonLiteralCrossLinkedAnnotationOf A
            strategy hwin (initial.step A strategy input))) move :=
  Classical.choose_spec
    (exists_profiledRawJointGuardedCommonLiteralCrossRootPinnedParentLinkedEntryMove
      A strategy hwin initial input)

end

end DetParityAutomaton

end DistributedSynthesis
