/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenDependentBeliefPresentation
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenShapeFreeObservableReceiptFilter

/-!
# Output homogeneity follows the local receive event

The full physical pair need not be homogeneous across different current
descriptors.  That statement would compare the informed receiver at two
different semantic past/root arguments.  It is also stronger than locality
requires.

The honest split is instead exactly the split made by a process's local
receive event.

* On a no-receive round, process one uses the right blind sender and process
  two uses the left blind sender.  Those outputs depend only on the common
  fixed value and query, so they are definitionally equal even when the two
  retained evaluations have different current descriptors.
* On a receive round, the delivered pair supplies one common current.  Once
  both alternatives are typed over that current, the exact dependent-root
  pair theorem gives the informed receiver output.

No theorem below gives a process an orientation, leader flag, member, root,
or hidden bit.  The right/left case split is proof-side and is selected at
runtime only by the process's actual receive event.
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

variable [Fintype I] [Inhabited I]
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

/-! ## The two blind/no-receive laws -/

omit [Inhabited I] [Inhabited Out₁] [Inhabited Out₂] in
/-- Process one's right-shadow output is independent of the retained current,
member, and root.  This is the strict-right/no-receive law. -/
theorem profiledOpenWitnessedRightSenderOutput_crossCurrent
    {leftCurrent rightCurrent :
      ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I) initialCode}
    {value : ProfiledOpenFixedRightPinnedValue A initialCode}
    {query : ProfiledOpenFixedRightPinnedBlockQuery A initialCode value}
    (reachable : ProfiledOpenFixedRightQueryReachable A initialCode value
      query)
    (left : ProfiledOpenFixedRightReanchoredRowEvaluation A strategy hwin
      basis initialCode leftCurrent value query)
    (right : ProfiledOpenFixedRightReanchoredRowEvaluation A strategy hwin
      basis initialCode rightCurrent value query)
    (leftRow rightRow : PairedEntryRow) (inputOne : In₁) :
    profiledOpenWitnessedRightSenderOutput A initialCode
        (profiledOpenWitnessedRightRoundOverlayOfEvaluation A strategy hwin
          basis initialCode reachable left leftRow) inputOne =
      profiledOpenWitnessedRightSenderOutput A initialCode
        (profiledOpenWitnessedRightRoundOverlayOfEvaluation A strategy hwin
          basis initialCode reachable right rightRow) inputOne :=
  rfl

omit [Inhabited I] [Inhabited Out₁] [Inhabited Out₂] in
/-- Process-two strict-left/no-receive mirror. -/
theorem profiledOpenWitnessedLeftSenderOutput_crossCurrent
    {leftCurrent rightCurrent :
      ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I) initialCode}
    {value : ProfiledOpenFixedLeftPinnedValue A initialCode}
    {query : ProfiledOpenFixedLeftPinnedBlockQuery A initialCode value}
    (reachable : ProfiledOpenFixedLeftQueryReachable A initialCode value
      query)
    (left : ProfiledOpenFixedLeftReanchoredRowEvaluation A strategy hwin basis
      initialCode leftCurrent value query)
    (right : ProfiledOpenFixedLeftReanchoredRowEvaluation A strategy hwin basis
      initialCode rightCurrent value query)
    (leftRow rightRow : PairedEntryRow) (inputTwo : In₂) :
    profiledOpenWitnessedLeftSenderOutput A initialCode
        (profiledOpenWitnessedLeftRoundOverlayOfEvaluation A strategy hwin
          basis initialCode reachable left leftRow) inputTwo =
      profiledOpenWitnessedLeftSenderOutput A initialCode
        (profiledOpenWitnessedLeftRoundOverlayOfEvaluation A strategy hwin
          basis initialCode reachable right rightRow) inputTwo :=
  rfl

/-! ## The two informed/receive laws -/

omit [Inhabited I] [Inhabited Out₁] [Inhabited Out₂] in
/-- Process one receives on `left` or `both`.  A delivered source gives one
common current; all dependent member/root alternatives over that current
emit the same process-one receiver output. -/
theorem profiledOpenWitnessedLeftReceiverOutput_sameCurrent
    {current : ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I)
      initialCode}
    {value : ProfiledOpenFixedLeftPinnedValue A initialCode}
    {query : ProfiledOpenFixedLeftPinnedBlockQuery A initialCode value}
    (reachable : ProfiledOpenFixedLeftQueryReachable A initialCode value
      query)
    (left right : ProfiledOpenFixedLeftReanchoredRowEvaluation A strategy hwin
      basis initialCode current value query)
    (row : PairedEntryRow) (inputOne : In₁) (inputTwo : In₂) :
    profiledOpenWitnessedLeftReceiverOutput A initialCode
          (profiledOpenWitnessedLeftRoundOverlayOfEvaluation A strategy hwin
            basis initialCode reachable left row) inputOne inputTwo =
      profiledOpenWitnessedLeftReceiverOutput A initialCode
          (profiledOpenWitnessedLeftRoundOverlayOfEvaluation A strategy hwin
            basis initialCode reachable right row) inputOne inputTwo :=
  profiledOpenWitnessedLeftReceiverOutput_exactDependent_pair A strategy hwin
    basis initialCode reachable left right row inputOne inputTwo

omit [Inhabited I] [Inhabited Out₁] [Inhabited Out₂] in
/-- Process-two receive mirror, used on `right` or `both`. -/
theorem profiledOpenWitnessedRightReceiverOutput_sameCurrent
    {current : ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I)
      initialCode}
    {value : ProfiledOpenFixedRightPinnedValue A initialCode}
    {query : ProfiledOpenFixedRightPinnedBlockQuery A initialCode value}
    (reachable : ProfiledOpenFixedRightQueryReachable A initialCode value
      query)
    (left right : ProfiledOpenFixedRightReanchoredRowEvaluation A strategy
      hwin basis initialCode current value query)
    (row : PairedEntryRow) (inputOne : In₁) (inputTwo : In₂) :
    profiledOpenWitnessedRightReceiverOutput A initialCode
          (profiledOpenWitnessedRightRoundOverlayOfEvaluation A strategy hwin
            basis initialCode reachable left row) inputOne inputTwo =
      profiledOpenWitnessedRightReceiverOutput A initialCode
          (profiledOpenWitnessedRightRoundOverlayOfEvaluation A strategy hwin
            basis initialCode reachable right row) inputOne inputTwo :=
  profiledOpenWitnessedRightReceiverOutput_exactDependent_pair A strategy hwin
    basis initialCode reachable left right row inputOne inputTwo

/-! ## Why the receive law is genuinely same-current -/

omit [Inhabited I] [Inhabited Out₁] [Inhabited Out₂] in
/-- Equality of the dependent family members of evaluations over possibly
different currents already forces those currents to be equal.  Thus the old
same-member proof cannot silently be reused for a cross-current receiver
claim: a receive construction must really provide the common current. -/
theorem profiledOpenFixedRightReanchoredRowEvaluation_current_eq_of_member_eq
    {leftCurrent rightCurrent :
      ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I) initialCode}
    {value : ProfiledOpenFixedRightPinnedValue A initialCode}
    {query : ProfiledOpenFixedRightPinnedBlockQuery A initialCode value}
    (left : ProfiledOpenFixedRightReanchoredRowEvaluation A strategy hwin
      basis initialCode leftCurrent value query)
    (right : ProfiledOpenFixedRightReanchoredRowEvaluation A strategy hwin
      basis initialCode rightCurrent value query)
    (hmember : left.1.1 = right.1.1) :
    leftCurrent = rightCurrent := by
  rcases left.2 with ⟨leftWitness, hleftMember, _⟩
  rcases right.2 with ⟨rightWitness, hrightMember, _⟩
  exact leftWitness.member_eq.symm |>.trans
    ((congrArg Subtype.val hleftMember).trans
      ((congrArg Subtype.val hmember).trans
        ((congrArg Subtype.val hrightMember).symm.trans
          rightWitness.member_eq)))

omit [Inhabited I] [Inhabited Out₁] [Inhabited Out₂] in
/-- Left mirror. -/
theorem profiledOpenFixedLeftReanchoredRowEvaluation_current_eq_of_member_eq
    {leftCurrent rightCurrent :
      ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I) initialCode}
    {value : ProfiledOpenFixedLeftPinnedValue A initialCode}
    {query : ProfiledOpenFixedLeftPinnedBlockQuery A initialCode value}
    (left : ProfiledOpenFixedLeftReanchoredRowEvaluation A strategy hwin basis
      initialCode leftCurrent value query)
    (right : ProfiledOpenFixedLeftReanchoredRowEvaluation A strategy hwin basis
      initialCode rightCurrent value query)
    (hmember : left.1.1 = right.1.1) :
    leftCurrent = rightCurrent := by
  rcases left.2 with ⟨leftWitness, hleftMember, _⟩
  rcases right.2 with ⟨rightWitness, hrightMember, _⟩
  exact leftWitness.member_eq.symm |>.trans
    ((congrArg Subtype.val hleftMember).trans
      ((congrArg Subtype.val hmember).trans
        ((congrArg Subtype.val hrightMember).symm.trans
          rightWitness.member_eq)))

/-! ## Receipt equality supplies behavior, but not a false past equality -/

omit [Inhabited I] in
/-- Equal process-one observable receipts yield anchors with identical full
right behavior.  This is the strongest valid cross-current conclusion at the
anchor level; applying the receiver component still requires one common
future-history argument, supplied by a receive transition rather than by the
receipt itself. -/
theorem profiledOpenActiveLaneRightWitnessedReceipt_completeBehavior
    (left right : ProfiledOpenActiveLaneTaggedCandidate A initialCode)
    (hleftLive : ProfiledOpenActiveLaneRightWitnessedRuntimeLive A strategy
      hwin basis initialCode left.2 left.1)
    (hrightLive : ProfiledOpenActiveLaneRightWitnessedRuntimeLive A strategy
      hwin basis initialCode right.2 right.1)
    (hreceipt : left.1.1.1 = right.1.1.1) :
    ∃ leftAnchor : ProfiledOpenActiveLaneRightCandidateAnchor A strategy hwin
        basis initialCode left,
      ∃ rightAnchor : ProfiledOpenActiveLaneRightCandidateAnchor A strategy
          hwin basis initialCode right,
        ProfiledOpenIndexedActiveRightCompleteBehaviorEq A strategy hwin basis
          leftAnchor.source.1 rightAnchor.source.1 := by
  rcases profiledOpenActiveLaneRightWitnessedAnchors_of_receipt_eq A strategy
      hwin basis initialCode left right hleftLive hrightLive hreceipt with
    ⟨leftAnchor, rightAnchor, hrel⟩
  exact ⟨leftAnchor, rightAnchor,
    profiledOpenIndexedActiveRightCompleteBehaviorEq_of_decoratedRel A
      strategy hwin basis hrel⟩

omit [Inhabited I] in
/-- Process-two/left mirror. -/
theorem profiledOpenActiveLaneLeftWitnessedReceipt_completeBehavior
    (left right : ProfiledOpenActiveLaneTaggedCandidate A initialCode)
    (hleftLive : ProfiledOpenActiveLaneLeftWitnessedRuntimeLive A strategy
      hwin basis initialCode left.2 left.1)
    (hrightLive : ProfiledOpenActiveLaneLeftWitnessedRuntimeLive A strategy
      hwin basis initialCode right.2 right.1)
    (hreceipt : left.1.1.2 = right.1.1.2) :
    ∃ leftAnchor : ProfiledOpenActiveLaneLeftCandidateAnchor A strategy hwin
        basis initialCode left,
      ∃ rightAnchor : ProfiledOpenActiveLaneLeftCandidateAnchor A strategy
          hwin basis initialCode right,
        ProfiledOpenIndexedActiveLeftCompleteBehaviorEq A strategy hwin basis
          leftAnchor.source.1 rightAnchor.source.1 := by
  rcases profiledOpenActiveLaneLeftWitnessedAnchors_of_receipt_eq A strategy
      hwin basis initialCode left right hleftLive hrightLive hreceipt with
    ⟨leftAnchor, rightAnchor, hrel⟩
  exact ⟨leftAnchor, rightAnchor,
    profiledOpenIndexedActiveLeftCompleteBehaviorEq_of_decoratedRel A strategy
      hwin basis hrel⟩

end

end DetParityAutomaton

end DistributedSynthesis
