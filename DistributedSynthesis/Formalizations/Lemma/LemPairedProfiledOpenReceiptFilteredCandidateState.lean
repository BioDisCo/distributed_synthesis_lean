/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenShapeFreeObservableReceiptFilter

/-!
# Receipt-filtered witnessed candidate states

The witnessed successor relation already has an unconditional local theorem:
after fixing one finite projected receipt, every two retained live successors
belong to one exact local fibre.  This file turns that theorem into a small
finite operational carrier.

The runtime data are exactly two finite receipt coordinates and one finite
candidate set.  The proof fields only certify that every carried candidate
has those two coordinates.  They are erased and contain no semantic point.
In particular, neither receipt is an active-side, orientation, strict-leader,
or future-lineage choice.

The successor below filters the full witnessed saturation simultaneously by
the two supplied local-summary receipts.  The literal-receipt coverage lemma
shows that this intersection does not discard an actual successor when the
two supplied receipts are its own two public coordinates.  Both local-fibre
coherence laws and arbitrary-bank output homogeneity then hold without an
additional semantic premise.
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

private abbrev FilteredReceiptClass :=
  ProfiledOpenActiveLaneSideClass A initialCode

private abbrev FilteredCandidate :=
  ProfiledOpenActiveLaneTaggedCandidate A initialCode

private abbrev FilteredBank :=
  ProfiledOpenFixedSidewisePinnedBank A initialCode
    (FilteredReceiptClass A initialCode) (FilteredReceiptClass A initialCode)

private abbrev FilteredQuery :=
  ProfiledOpenFixedSidewiseReachablePointedQuery A initialCode

private abbrev FilteredControlStep :=
  ProfiledOpenFixedSidewiseControlStep A initialCode

private abbrev FilteredGood
    (source : FilteredCandidate A initialCode)
    (bank : FilteredBank A initialCode)
    (query : FilteredQuery A initialCode)
    (target : FilteredCandidate A initialCode) : Prop :=
  SourceAwareRelationalFamilyCandidateGood
    (profiledOpenActiveLaneWitnessedCandidateEdge A strategy hwin basis
      initialCode)
    (FilteredControlStep A initialCode) source bank query target

/-! ## The proof-erased finite carrier -/

/-- A candidate set filtered by both processes' finite receipt coordinates.
Only the three data fields survive at runtime. -/
structure ProfiledOpenWitnessedReceiptFilteredCandidateState where
  rightReceipt : FilteredReceiptClass A initialCode
  leftReceipt : FilteredReceiptClass A initialCode
  candidates : Finset (FilteredCandidate A initialCode)
  candidates_rightReceipt : ∀ candidate, candidate ∈ candidates →
    candidate.1.1.1 = rightReceipt
  candidates_leftReceipt : ∀ candidate, candidate ∈ candidates →
    candidate.1.1.2 = leftReceipt

/-- The carrier is finite.  Its semantic coherence witnesses are propositions
and hence do not enlarge the runtime state. -/
noncomputable instance
    profiledOpenWitnessedReceiptFilteredCandidateState_fintype :
    Fintype
      (ProfiledOpenWitnessedReceiptFilteredCandidateState A initialCode) := by
  classical
  let encode : ProfiledOpenWitnessedReceiptFilteredCandidateState A
      initialCode →
      FilteredReceiptClass A initialCode ×
        FilteredReceiptClass A initialCode ×
          Finset (FilteredCandidate A initialCode) :=
    fun state ↦ (state.rightReceipt, state.leftReceipt, state.candidates)
  exact Fintype.ofInjective encode (by
    intro left right heq
    rcases left with ⟨leftRight, leftLeft, leftCandidates, _, _⟩
    rcases right with ⟨rightRight, rightLeft, rightCandidates, _, _⟩
    simp only [encode, Prod.mk.injEq] at heq
    rcases heq with ⟨rfl, rfl, rfl⟩
    rfl)

/-- Membership is the finite possibility relation exposed to local-consumer
lemmas. -/
def profiledOpenWitnessedReceiptFilteredCandidatePossible
    (state : ProfiledOpenWitnessedReceiptFilteredCandidateState A initialCode)
    (candidate : FilteredCandidate A initialCode) : Prop :=
  candidate ∈ state.candidates

/-! ## Initialization -/

/-- A singleton starts at its literal pair of public receipts. -/
noncomputable def profiledOpenWitnessedReceiptFilteredCandidateInitial
    (candidate : FilteredCandidate A initialCode) :
    ProfiledOpenWitnessedReceiptFilteredCandidateState A initialCode :=
  { rightReceipt := candidate.1.1.1
    leftReceipt := candidate.1.1.2
    candidates := {candidate}
    candidates_rightReceipt := by
      intro other hother
      have heq : other = candidate := by
        simpa only [Finset.mem_singleton] using hother
      exact congrArg (fun value : FilteredCandidate A initialCode ↦
        value.1.1.1) heq
    candidates_leftReceipt := by
      intro other hother
      have heq : other = candidate := by
        simpa only [Finset.mem_singleton] using hother
      exact congrArg (fun value : FilteredCandidate A initialCode ↦
        value.1.1.2) heq }

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem
    profiledOpenWitnessedReceiptFilteredCandidateInitial_candidate_mem
    (candidate : FilteredCandidate A initialCode) :
    candidate ∈
      (profiledOpenWitnessedReceiptFilteredCandidateInitial A initialCode
        candidate).candidates := by
  simp [profiledOpenWitnessedReceiptFilteredCandidateInitial]

/-! ## Simultaneously receipt-filtered witnessed saturation -/

/-- All witnessed exact successors whose two literal projected classes are
the supplied finite local-summary receipts. -/
noncomputable def profiledOpenWitnessedReceiptPairFilteredSaturation
    (current : Finset (FilteredCandidate A initialCode))
    (bank : FilteredBank A initialCode)
    (query : FilteredQuery A initialCode)
    (rightReceipt leftReceipt : FilteredReceiptClass A initialCode) :
    Finset (FilteredCandidate A initialCode) := by
  classical
  exact Finset.univ.filter fun target ↦
    target.1.1.1 = rightReceipt ∧
      target.1.1.2 = leftReceipt ∧
      ∃ source ∈ current,
        FilteredGood A strategy hwin basis initialCode source bank query target

theorem mem_profiledOpenWitnessedReceiptPairFilteredSaturation_iff
    (current : Finset (FilteredCandidate A initialCode))
    (bank : FilteredBank A initialCode)
    (query : FilteredQuery A initialCode)
    (rightReceipt leftReceipt : FilteredReceiptClass A initialCode)
    (target : FilteredCandidate A initialCode) :
    target ∈
        profiledOpenWitnessedReceiptPairFilteredSaturation A strategy hwin basis
          initialCode current bank query rightReceipt leftReceipt ↔
      target.1.1.1 = rightReceipt ∧
        target.1.1.2 = leftReceipt ∧
        ∃ source ∈ current,
          FilteredGood A strategy hwin basis initialCode source bank query
            target := by
  classical
  simp [profiledOpenWitnessedReceiptPairFilteredSaturation]

/-- The total finite transition.  The two receipt arguments are public
local-summary coordinates; the transition itself performs no side, leader,
orientation, or lineage test. -/
noncomputable def ProfiledOpenWitnessedReceiptFilteredCandidateState.step
    (current : ProfiledOpenWitnessedReceiptFilteredCandidateState A initialCode)
    (bank : FilteredBank A initialCode)
    (query : FilteredQuery A initialCode)
    (rightReceipt leftReceipt : FilteredReceiptClass A initialCode) :
    ProfiledOpenWitnessedReceiptFilteredCandidateState A initialCode := by
  let candidates :=
    profiledOpenWitnessedReceiptPairFilteredSaturation A strategy hwin basis
      initialCode current.candidates bank query rightReceipt leftReceipt
  exact
    { rightReceipt := rightReceipt
      leftReceipt := leftReceipt
      candidates := candidates
      candidates_rightReceipt := by
        intro candidate hcandidate
        exact (mem_profiledOpenWitnessedReceiptPairFilteredSaturation_iff A
          strategy hwin basis initialCode current.candidates bank query
          rightReceipt leftReceipt candidate).1 hcandidate |>.1
      candidates_leftReceipt := by
        intro candidate hcandidate
        exact (mem_profiledOpenWitnessedReceiptPairFilteredSaturation_iff A
          strategy hwin basis initialCode current.candidates bank query
          rightReceipt leftReceipt candidate).1 hcandidate |>.2.1 }

/-- Simultaneous filtering cannot delete a represented exact successor when
the next receipts are the target's own literal public receipt pair. -/
theorem
    ProfiledOpenWitnessedReceiptFilteredCandidateState.target_mem_step_literalReceipts
    (current : ProfiledOpenWitnessedReceiptFilteredCandidateState A initialCode)
    (bank : FilteredBank A initialCode)
    (query : FilteredQuery A initialCode)
    (source target : FilteredCandidate A initialCode)
    (hsource : source ∈ current.candidates)
    (hgood : FilteredGood A strategy hwin basis initialCode source bank query
      target) :
    target ∈
      (current.step A strategy hwin basis initialCode bank query
        target.1.1.1 target.1.1.2).candidates := by
  apply (mem_profiledOpenWitnessedReceiptPairFilteredSaturation_iff A strategy
    hwin basis initialCode current.candidates bank query target.1.1.1
    target.1.1.2 target).2
  exact ⟨rfl, rfl, source, hsource, hgood⟩

/-! ## Unconditional local coherence -/

/-- Process-one coherence of a finite witnessed candidate set. -/
def ProfiledOpenWitnessedRightCandidateSetCoherent
    (candidates : Finset (FilteredCandidate A initialCode)) : Prop :=
  ∀ left, left ∈ candidates →
    ProfiledOpenActiveLaneRightWitnessedRuntimeLive A strategy hwin basis
        initialCode left.2 left.1 →
    ∀ right, right ∈ candidates →
      ProfiledOpenActiveLaneRightWitnessedRuntimeLive A strategy hwin basis
          initialCode right.2 right.1 →
      ∃ leftAnchor : ProfiledOpenActiveLaneRightCandidateAnchor A strategy
          hwin basis initialCode left,
        ∃ rightAnchor : ProfiledOpenActiveLaneRightCandidateAnchor A strategy
            hwin basis initialCode right,
          ProfiledOpenIndexedActiveRightControlledLocalFibreRel A strategy hwin
            basis initialCode leftAnchor.source rightAnchor.source

/-- Process-two mirror. -/
def ProfiledOpenWitnessedLeftCandidateSetCoherent
    (candidates : Finset (FilteredCandidate A initialCode)) : Prop :=
  ∀ left, left ∈ candidates →
    ProfiledOpenActiveLaneLeftWitnessedRuntimeLive A strategy hwin basis
        initialCode left.2 left.1 →
    ∀ right, right ∈ candidates →
      ProfiledOpenActiveLaneLeftWitnessedRuntimeLive A strategy hwin basis
          initialCode right.2 right.1 →
      ∃ leftAnchor : ProfiledOpenActiveLaneLeftCandidateAnchor A strategy
          hwin basis initialCode left,
        ∃ rightAnchor : ProfiledOpenActiveLaneLeftCandidateAnchor A strategy
            hwin basis initialCode right,
          ProfiledOpenIndexedActiveLeftControlledLocalFibreRel A strategy hwin
            basis initialCode leftAnchor.source rightAnchor.source

/-- Singleton initialization is coherent for process one. -/
theorem profiledOpenWitnessedReceiptFilteredCandidateInitial_rightCoherent
    (candidate : FilteredCandidate A initialCode) :
    ProfiledOpenWitnessedRightCandidateSetCoherent A strategy hwin basis
      initialCode
      (profiledOpenWitnessedReceiptFilteredCandidateInitial A initialCode
        candidate).candidates := by
  intro left hleft hleftLive right hright hrightLive
  change left ∈ ({candidate} : Finset (FilteredCandidate A initialCode)) at hleft
  change right ∈ ({candidate} : Finset (FilteredCandidate A initialCode)) at hright
  have hleftEq : left = candidate := by simpa using hleft
  have hrightEq : right = candidate := by simpa using hright
  subst left
  subst right
  exact profiledOpenActiveLaneRightWitnessedAnchors_of_receipt_eq A strategy
    hwin basis initialCode candidate candidate hleftLive hrightLive rfl

/-- Singleton initialization is coherent for process two. -/
theorem profiledOpenWitnessedReceiptFilteredCandidateInitial_leftCoherent
    (candidate : FilteredCandidate A initialCode) :
    ProfiledOpenWitnessedLeftCandidateSetCoherent A strategy hwin basis
      initialCode
      (profiledOpenWitnessedReceiptFilteredCandidateInitial A initialCode
        candidate).candidates := by
  intro left hleft hleftLive right hright hrightLive
  change left ∈ ({candidate} : Finset (FilteredCandidate A initialCode)) at hleft
  change right ∈ ({candidate} : Finset (FilteredCandidate A initialCode)) at hright
  have hleftEq : left = candidate := by simpa using hleft
  have hrightEq : right = candidate := by simpa using hright
  subst left
  subst right
  exact profiledOpenActiveLaneLeftWitnessedAnchors_of_receipt_eq A strategy
    hwin basis initialCode candidate candidate hleftLive hrightLive rfl

/-- One filtered saturation step is process-one coherent.  This is the direct
operational use of the fixed-receipt successor law. -/
theorem ProfiledOpenWitnessedReceiptFilteredCandidateState.step_rightCoherent
    (current : ProfiledOpenWitnessedReceiptFilteredCandidateState A initialCode)
    (bank : FilteredBank A initialCode)
    (query : FilteredQuery A initialCode)
    (rightReceipt leftReceipt : FilteredReceiptClass A initialCode) :
    ProfiledOpenWitnessedRightCandidateSetCoherent A strategy hwin basis
      initialCode
      (current.step A strategy hwin basis initialCode bank query rightReceipt
        leftReceipt).candidates := by
  intro left hleft hleftLive right hright hrightLive
  rcases (mem_profiledOpenWitnessedReceiptPairFilteredSaturation_iff A strategy
      hwin basis initialCode current.candidates bank query rightReceipt
      leftReceipt left).1 hleft with
    ⟨hleftReceipt, _hleftOther, leftSource, hleftSource, hleftGood⟩
  rcases (mem_profiledOpenWitnessedReceiptPairFilteredSaturation_iff A strategy
      hwin basis initialCode current.candidates bank query rightReceipt
      leftReceipt right).1 hright with
    ⟨hrightReceipt, _hrightOther, rightSource, hrightSource, hrightGood⟩
  let hstep :=
    profiledOpenActiveLaneRightWitnessedLocalReceiptSuccessorLaw_receipt A
      strategy hwin basis initialCode current.candidates bank query rightReceipt
  exact hstep leftSource left rightSource right hleftSource hleftGood
    hleftReceipt hleftLive hrightSource hrightGood hrightReceipt hrightLive

/-- Process-two one-step coherence. -/
theorem ProfiledOpenWitnessedReceiptFilteredCandidateState.step_leftCoherent
    (current : ProfiledOpenWitnessedReceiptFilteredCandidateState A initialCode)
    (bank : FilteredBank A initialCode)
    (query : FilteredQuery A initialCode)
    (rightReceipt leftReceipt : FilteredReceiptClass A initialCode) :
    ProfiledOpenWitnessedLeftCandidateSetCoherent A strategy hwin basis
      initialCode
      (current.step A strategy hwin basis initialCode bank query rightReceipt
        leftReceipt).candidates := by
  intro left hleft hleftLive right hright hrightLive
  rcases (mem_profiledOpenWitnessedReceiptPairFilteredSaturation_iff A strategy
      hwin basis initialCode current.candidates bank query rightReceipt
      leftReceipt left).1 hleft with
    ⟨_hleftOther, hleftReceipt, leftSource, hleftSource, hleftGood⟩
  rcases (mem_profiledOpenWitnessedReceiptPairFilteredSaturation_iff A strategy
      hwin basis initialCode current.candidates bank query rightReceipt
      leftReceipt right).1 hright with
    ⟨_hrightOther, hrightReceipt, rightSource, hrightSource, hrightGood⟩
  let hstep :=
    profiledOpenActiveLaneLeftWitnessedLocalReceiptSuccessorLaw_receipt A
      strategy hwin basis initialCode current.candidates bank query leftReceipt
  exact hstep leftSource left rightSource right hleftSource hleftGood
    hleftReceipt hleftLive hrightSource hrightGood hrightReceipt hrightLive

/-! ## Arbitrary-bank output homogeneity -/

/-- Every two carried candidates select literally the same process-one value
from any bank assigned to this state.  No semantic representative is chosen. -/
theorem
    ProfiledOpenWitnessedReceiptFilteredCandidateState.rightBankBehaviorHomogeneous
    (bankAt : ProfiledOpenWitnessedReceiptFilteredCandidateState A initialCode →
      FilteredBank A initialCode)
    (current : ProfiledOpenWitnessedReceiptFilteredCandidateState A initialCode) :
    SidewiseOneBankFamilyBehaviorHomogeneousAt
      (ProfiledOpenActiveLaneRightWitnessedRuntimeLive A strategy hwin basis
        initialCode)
      (profiledOpenWitnessedReceiptFilteredCandidatePossible A initialCode)
      (fun left right : ProfiledOpenFixedRightPinnedValue A initialCode ↦
        left = right)
      bankAt current := by
  intro left right hleft _hleftLive hright _hrightLive
  exact congrArg (bankAt current).1
    ((current.candidates_rightReceipt left hleft).trans
      (current.candidates_rightReceipt right hright).symm)

/-- Process-two arbitrary-bank output homogeneity. -/
theorem
    ProfiledOpenWitnessedReceiptFilteredCandidateState.leftBankBehaviorHomogeneous
    (bankAt : ProfiledOpenWitnessedReceiptFilteredCandidateState A initialCode →
      FilteredBank A initialCode)
    (current : ProfiledOpenWitnessedReceiptFilteredCandidateState A initialCode) :
    SidewiseTwoBankFamilyBehaviorHomogeneousAt
      (ProfiledOpenActiveLaneLeftWitnessedRuntimeLive A strategy hwin basis
        initialCode)
      (profiledOpenWitnessedReceiptFilteredCandidatePossible A initialCode)
      (fun left right : ProfiledOpenFixedLeftPinnedValue A initialCode ↦
        left = right)
      bankAt current := by
  intro left right hleft _hleftLive hright _hrightLive
  exact congrArg (bankAt current).2
    ((current.candidates_leftReceipt left hleft).trans
      (current.candidates_leftReceipt right hright).symm)

/-- The one-step state therefore has homogeneous process-one output for every
bank family, with no additional reachability or consistency premise. -/
theorem
    ProfiledOpenWitnessedReceiptFilteredCandidateState.step_rightBankBehaviorHomogeneous
    (bankAt : ProfiledOpenWitnessedReceiptFilteredCandidateState A initialCode →
      FilteredBank A initialCode)
    (current : ProfiledOpenWitnessedReceiptFilteredCandidateState A initialCode)
    (bank : FilteredBank A initialCode)
    (query : FilteredQuery A initialCode)
    (rightReceipt leftReceipt : FilteredReceiptClass A initialCode) :
    SidewiseOneBankFamilyBehaviorHomogeneousAt
      (ProfiledOpenActiveLaneRightWitnessedRuntimeLive A strategy hwin basis
        initialCode)
      (profiledOpenWitnessedReceiptFilteredCandidatePossible A initialCode)
      (fun left right : ProfiledOpenFixedRightPinnedValue A initialCode ↦
        left = right)
      bankAt
      (current.step A strategy hwin basis initialCode bank query rightReceipt
        leftReceipt) :=
  ProfiledOpenWitnessedReceiptFilteredCandidateState.rightBankBehaviorHomogeneous
    A strategy hwin basis initialCode bankAt _

/-- Process-two one-step output homogeneity. -/
theorem
    ProfiledOpenWitnessedReceiptFilteredCandidateState.step_leftBankBehaviorHomogeneous
    (bankAt : ProfiledOpenWitnessedReceiptFilteredCandidateState A initialCode →
      FilteredBank A initialCode)
    (current : ProfiledOpenWitnessedReceiptFilteredCandidateState A initialCode)
    (bank : FilteredBank A initialCode)
    (query : FilteredQuery A initialCode)
    (rightReceipt leftReceipt : FilteredReceiptClass A initialCode) :
    SidewiseTwoBankFamilyBehaviorHomogeneousAt
      (ProfiledOpenActiveLaneLeftWitnessedRuntimeLive A strategy hwin basis
        initialCode)
      (profiledOpenWitnessedReceiptFilteredCandidatePossible A initialCode)
      (fun left right : ProfiledOpenFixedLeftPinnedValue A initialCode ↦
        left = right)
      bankAt
      (current.step A strategy hwin basis initialCode bank query rightReceipt
        leftReceipt) :=
  ProfiledOpenWitnessedReceiptFilteredCandidateState.leftBankBehaviorHomogeneous
    A strategy hwin basis initialCode bankAt _

end

end DetParityAutomaton

end DistributedSynthesis
