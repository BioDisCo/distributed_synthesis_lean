/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemSidewiseLocalClassReadout
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenShapeFreeCandidateCommonBank

/-!
# Local consumption of a shape-free sidewise bank

A candidate table chooses one finite sidewise bank at each finite candidate
set.  The selected component is nevertheless indexed by a proof-side class.
This file gives the exact runtime criterion for erasing that hidden index.

The criterion is behavioral, not epistemic: at one process-local summary all
bank components belonging to still-possible live candidates must implement
the same local behavior.  The consumer then chooses one representative
component as a function of the finite summary alone.  It never reads a graph,
orientation, lane, strict-leader flag, hidden control, or optional shape.

For the concrete shape-free bank we prove a useful sufficient condition.  If
all active candidates possible at one finite receipt have semantic anchors in
one active-lane local fibre, then their projected classes are equal in the
safe forward direction.  Hence even an arbitrary bank has literally equal
selected components.  The same fibre relation also gives equality of the
complete physical sender and every receiver row.  In particular, the
right-only/`both` and left-only/`both` ambiguity is already absorbed.

What remains for an end-to-end local-summary automaton is stated without an
opaque theorem-shaped placeholder: its finite possibility/receipt sets must
satisfy the explicit source-fibre coherence predicates below.  The final
collision theorems refute local consumption immediately if one reachable
receipt retains two behaviorally different components.
-/

namespace DistributedSynthesis

universe oc tc f d om tm so st i u v x y s

private abbrev SidewiseCandidate
    (OneClass : Type oc) (TwoClass : Type tc) (Family : Type f)
    (Descriptor : Type d) :=
  RelationalFamilyCandidate
    (SidewiseTaggedFamily OneClass TwoClass Family) Descriptor

/-! ## A bank varying with the finite local summary -/

/-- A process-one consumer for a bank selected by the current finite summary.
The hidden candidate occurs only in the correctness statement. -/
def SidewiseOneBankFamilyLocallyConsumable
    {OneClass : Type oc} {TwoClass : Type tc} {Family : Type f}
    {Descriptor : Type d} {OneMove : Type om} {TwoMove : Type tm}
    {SummaryOne : Type so}
    (Live : Descriptor →
      SidewiseTaggedFamily OneClass TwoClass Family → Prop)
    (PossibleOne : SummaryOne →
      SidewiseCandidate OneClass TwoClass Family Descriptor → Prop)
    (EquivalentOne : OneMove → OneMove → Prop)
    (bankAt : SummaryOne →
      SidewiseMoveBank OneClass TwoClass OneMove TwoMove) : Prop :=
  ∃ consumeOne : SummaryOne → OneMove,
    ∀ summary candidate,
      PossibleOne summary candidate → Live candidate.2 candidate.1 →
        EquivalentOne
          ((bankAt summary).1 candidate.1.1.1)
          (consumeOne summary)

/-- Process-two mirror. -/
def SidewiseTwoBankFamilyLocallyConsumable
    {OneClass : Type oc} {TwoClass : Type tc} {Family : Type f}
    {Descriptor : Type d} {OneMove : Type om} {TwoMove : Type tm}
    {SummaryTwo : Type st}
    (Live : Descriptor →
      SidewiseTaggedFamily OneClass TwoClass Family → Prop)
    (PossibleTwo : SummaryTwo →
      SidewiseCandidate OneClass TwoClass Family Descriptor → Prop)
    (EquivalentTwo : TwoMove → TwoMove → Prop)
    (bankAt : SummaryTwo →
      SidewiseMoveBank OneClass TwoClass OneMove TwoMove) : Prop :=
  ∃ consumeTwo : SummaryTwo → TwoMove,
    ∀ summary candidate,
      PossibleTwo summary candidate → Live candidate.2 candidate.1 →
        EquivalentTwo
          ((bankAt summary).2 candidate.1.1.2)
          (consumeTwo summary)

/-- Exact process-one behavioral homogeneity at one summary. -/
def SidewiseOneBankFamilyBehaviorHomogeneousAt
    {OneClass : Type oc} {TwoClass : Type tc} {Family : Type f}
    {Descriptor : Type d} {OneMove : Type om} {TwoMove : Type tm}
    {SummaryOne : Type so}
    (Live : Descriptor →
      SidewiseTaggedFamily OneClass TwoClass Family → Prop)
    (PossibleOne : SummaryOne →
      SidewiseCandidate OneClass TwoClass Family Descriptor → Prop)
    (EquivalentOne : OneMove → OneMove → Prop)
    (bankAt : SummaryOne →
      SidewiseMoveBank OneClass TwoClass OneMove TwoMove)
    (summary : SummaryOne) : Prop :=
  ∀ left right,
    PossibleOne summary left → Live left.2 left.1 →
      PossibleOne summary right → Live right.2 right.1 →
        EquivalentOne
          ((bankAt summary).1 left.1.1.1)
          ((bankAt summary).1 right.1.1.1)

/-- Exact process-two behavioral homogeneity at one summary. -/
def SidewiseTwoBankFamilyBehaviorHomogeneousAt
    {OneClass : Type oc} {TwoClass : Type tc} {Family : Type f}
    {Descriptor : Type d} {OneMove : Type om} {TwoMove : Type tm}
    {SummaryTwo : Type st}
    (Live : Descriptor →
      SidewiseTaggedFamily OneClass TwoClass Family → Prop)
    (PossibleTwo : SummaryTwo →
      SidewiseCandidate OneClass TwoClass Family Descriptor → Prop)
    (EquivalentTwo : TwoMove → TwoMove → Prop)
    (bankAt : SummaryTwo →
      SidewiseMoveBank OneClass TwoClass OneMove TwoMove)
    (summary : SummaryTwo) : Prop :=
  ∀ left right,
    PossibleTwo summary left → Live left.2 left.1 →
      PossibleTwo summary right → Live right.2 right.1 →
        EquivalentTwo
          ((bankAt summary).2 left.1.1.2)
          ((bankAt summary).2 right.1.1.2)

/-- The varying-bank version of the exact criterion in
`LemSidewiseLocalClassReadout`: no class readout is required. -/
theorem sidewiseOneBankFamilyLocallyConsumable_iff_behaviorHomogeneous
    {OneClass : Type oc} {TwoClass : Type tc} {Family : Type f}
    {Descriptor : Type d} {OneMove : Type om} {TwoMove : Type tm}
    {SummaryOne : Type so} [Inhabited OneMove]
    (Live : Descriptor →
      SidewiseTaggedFamily OneClass TwoClass Family → Prop)
    (PossibleOne : SummaryOne →
      SidewiseCandidate OneClass TwoClass Family Descriptor → Prop)
    (EquivalentOne : OneMove → OneMove → Prop)
    (hsymm : Symmetric EquivalentOne)
    (htrans : IsTrans _ EquivalentOne)
    (bankAt : SummaryOne →
      SidewiseMoveBank OneClass TwoClass OneMove TwoMove) :
    SidewiseOneBankFamilyLocallyConsumable Live PossibleOne EquivalentOne
        bankAt ↔
      ∀ summary,
        SidewiseOneBankFamilyBehaviorHomogeneousAt Live PossibleOne
          EquivalentOne bankAt summary := by
  constructor
  · rintro ⟨consumeOne, hconsume⟩ summary left right hleft hleftLive
      hright hrightLive
    exact htrans.trans _ _ _
      (hconsume summary left hleft hleftLive)
      (hsymm (hconsume summary right hright hrightLive))
  · intro hhomogeneous
    classical
    have hexists : ∀ summary : SummaryOne, ∃ move : OneMove,
        ∀ candidate,
          PossibleOne summary candidate → Live candidate.2 candidate.1 →
            EquivalentOne ((bankAt summary).1 candidate.1.1.1) move := by
      intro summary
      letI : Decidable (∃ candidate,
          PossibleOne summary candidate ∧ Live candidate.2 candidate.1) :=
        Classical.propDecidable _
      by_cases hactive : ∃ candidate,
          PossibleOne summary candidate ∧ Live candidate.2 candidate.1
      · let pivot := Classical.choose hactive
        refine ⟨(bankAt summary).1 pivot.1.1.1, ?_⟩
        intro candidate hpossible hlive
        exact hhomogeneous summary candidate pivot hpossible hlive
          (Classical.choose_spec hactive).1
          (Classical.choose_spec hactive).2
      · refine ⟨default, ?_⟩
        intro candidate hpossible hlive
        exact False.elim (hactive ⟨candidate, hpossible, hlive⟩)
    exact ⟨fun summary ↦ Classical.choose (hexists summary),
      fun summary candidate hpossible hlive ↦
        Classical.choose_spec (hexists summary) candidate hpossible hlive⟩

/-- Process-two varying-bank criterion. -/
theorem sidewiseTwoBankFamilyLocallyConsumable_iff_behaviorHomogeneous
    {OneClass : Type oc} {TwoClass : Type tc} {Family : Type f}
    {Descriptor : Type d} {OneMove : Type om} {TwoMove : Type tm}
    {SummaryTwo : Type st} [Inhabited TwoMove]
    (Live : Descriptor →
      SidewiseTaggedFamily OneClass TwoClass Family → Prop)
    (PossibleTwo : SummaryTwo →
      SidewiseCandidate OneClass TwoClass Family Descriptor → Prop)
    (EquivalentTwo : TwoMove → TwoMove → Prop)
    (hsymm : Symmetric EquivalentTwo)
    (htrans : IsTrans _ EquivalentTwo)
    (bankAt : SummaryTwo →
      SidewiseMoveBank OneClass TwoClass OneMove TwoMove) :
    SidewiseTwoBankFamilyLocallyConsumable Live PossibleTwo EquivalentTwo
        bankAt ↔
      ∀ summary,
        SidewiseTwoBankFamilyBehaviorHomogeneousAt Live PossibleTwo
          EquivalentTwo bankAt summary := by
  constructor
  · rintro ⟨consumeTwo, hconsume⟩ summary left right hleft hleftLive
      hright hrightLive
    exact htrans.trans _ _ _
      (hconsume summary left hleft hleftLive)
      (hsymm (hconsume summary right hright hrightLive))
  · intro hhomogeneous
    classical
    have hexists : ∀ summary : SummaryTwo, ∃ move : TwoMove,
        ∀ candidate,
          PossibleTwo summary candidate → Live candidate.2 candidate.1 →
            EquivalentTwo ((bankAt summary).2 candidate.1.1.2) move := by
      intro summary
      letI : Decidable (∃ candidate,
          PossibleTwo summary candidate ∧ Live candidate.2 candidate.1) :=
        Classical.propDecidable _
      by_cases hactive : ∃ candidate,
          PossibleTwo summary candidate ∧ Live candidate.2 candidate.1
      · let pivot := Classical.choose hactive
        refine ⟨(bankAt summary).2 pivot.1.1.2, ?_⟩
        intro candidate hpossible hlive
        exact hhomogeneous summary candidate pivot hpossible hlive
          (Classical.choose_spec hactive).1
          (Classical.choose_spec hactive).2
      · refine ⟨default, ?_⟩
        intro candidate hpossible hlive
        exact False.elim (hactive ⟨candidate, hpossible, hlive⟩)
    exact ⟨fun summary ↦ Classical.choose (hexists summary),
      fun summary candidate hpossible hlive ↦
        Classical.choose_spec (hexists summary) candidate hpossible hlive⟩

/-! ## Honest finite possibility summaries -/

/-- The finite receipt state used below is exactly a finite set of public
candidates.  No semantic source or hidden bit occurs in the state type. -/
abbrev SidewiseFiniteCandidateSummary
    (OneClass : Type oc) (TwoClass : Type tc) (Family : Type f)
    (Descriptor : Type d) :=
  Finset (SidewiseCandidate OneClass TwoClass Family Descriptor)

/-- A public candidate remains possible precisely when the receipt is
reachable and contains it.  `Reachable` lets an automaton ignore unused
values of the ambient finite powerset type. -/
def sidewiseFiniteCandidatePossible
    {OneClass : Type oc} {TwoClass : Type tc} {Family : Type f}
    {Descriptor : Type d}
    (Reachable : SidewiseFiniteCandidateSummary OneClass TwoClass Family
      Descriptor → Prop)
    (summary : SidewiseFiniteCandidateSummary OneClass TwoClass Family
      Descriptor)
    (candidate : SidewiseCandidate OneClass TwoClass Family Descriptor) : Prop :=
  Reachable summary ∧ candidate ∈ summary

noncomputable instance
    {OneClass : Type oc} {TwoClass : Type tc} {Family : Type f}
    {Descriptor : Type d}
    [Fintype OneClass] [Fintype TwoClass] [Fintype Family]
    [Fintype Descriptor] [DecidableEq OneClass] [DecidableEq TwoClass]
    [DecidableEq Family] [DecidableEq Descriptor] :
    Fintype (SidewiseFiniteCandidateSummary OneClass TwoClass Family
      Descriptor) := by
  classical
  infer_instance

/-- One reachable receipt containing two inequivalent active components is a
kernel-level refutation of any local consumer. -/
theorem not_sidewiseOneBankFamilyLocallyConsumable_of_collision
    {OneClass : Type oc} {TwoClass : Type tc} {Family : Type f}
    {Descriptor : Type d} {OneMove : Type om} {TwoMove : Type tm}
    {SummaryOne : Type so}
    (Live : Descriptor →
      SidewiseTaggedFamily OneClass TwoClass Family → Prop)
    (PossibleOne : SummaryOne →
      SidewiseCandidate OneClass TwoClass Family Descriptor → Prop)
    (EquivalentOne : OneMove → OneMove → Prop)
    (hsymm : Symmetric EquivalentOne)
    (htrans : IsTrans _ EquivalentOne)
    (bankAt : SummaryOne →
      SidewiseMoveBank OneClass TwoClass OneMove TwoMove)
    (summary : SummaryOne)
    (left right : SidewiseCandidate OneClass TwoClass Family Descriptor)
    (hleft : PossibleOne summary left) (hleftLive : Live left.2 left.1)
    (hright : PossibleOne summary right) (hrightLive : Live right.2 right.1)
    (hne : ¬ EquivalentOne
      ((bankAt summary).1 left.1.1.1)
      ((bankAt summary).1 right.1.1.1)) :
    ¬ SidewiseOneBankFamilyLocallyConsumable Live PossibleOne EquivalentOne
      bankAt := by
  rintro ⟨consumeOne, hconsume⟩
  exact hne (htrans.trans _ _ _ (hconsume summary left hleft hleftLive)
    (hsymm (hconsume summary right hright hrightLive)))

/-- Process-two collision refutation. -/
theorem not_sidewiseTwoBankFamilyLocallyConsumable_of_collision
    {OneClass : Type oc} {TwoClass : Type tc} {Family : Type f}
    {Descriptor : Type d} {OneMove : Type om} {TwoMove : Type tm}
    {SummaryTwo : Type st}
    (Live : Descriptor →
      SidewiseTaggedFamily OneClass TwoClass Family → Prop)
    (PossibleTwo : SummaryTwo →
      SidewiseCandidate OneClass TwoClass Family Descriptor → Prop)
    (EquivalentTwo : TwoMove → TwoMove → Prop)
    (hsymm : Symmetric EquivalentTwo)
    (htrans : IsTrans _ EquivalentTwo)
    (bankAt : SummaryTwo →
      SidewiseMoveBank OneClass TwoClass OneMove TwoMove)
    (summary : SummaryTwo)
    (left right : SidewiseCandidate OneClass TwoClass Family Descriptor)
    (hleft : PossibleTwo summary left) (hleftLive : Live left.2 left.1)
    (hright : PossibleTwo summary right) (hrightLive : Live right.2 right.1)
    (hne : ¬ EquivalentTwo
      ((bankAt summary).2 left.1.1.2)
      ((bankAt summary).2 right.1.1.2)) :
    ¬ SidewiseTwoBankFamilyLocallyConsumable Live PossibleTwo EquivalentTwo
      bankAt := by
  rintro ⟨consumeTwo, hconsume⟩
  exact hne (htrans.trans _ _ _ (hconsume summary left hleft hleftLive)
    (hsymm (hconsume summary right hright hrightLive)))

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

private abbrev LocalDescriptor :=
  ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I) initialCode

private abbrev LocalFamily :=
  ProfiledOpenIndexedHiddenDescriptorFamilyCode A (I := I) initialCode

private abbrev LocalClass :=
  ProfiledOpenActiveLaneSideClass A initialCode

private abbrev LocalCandidate :=
  ProfiledOpenActiveLaneTaggedCandidate A initialCode

private abbrev LocalSummary :=
  SidewiseFiniteCandidateSummary
    (LocalClass A initialCode) (LocalClass A initialCode)
    (LocalFamily A initialCode) (LocalDescriptor A initialCode)

/-! ## Exact active-side anchors and receipt coherence -/

/-- A proof-side right anchor represents the literal descriptor and public
projected class of one active candidate. -/
structure ProfiledOpenActiveLaneRightCandidateAnchor
    (candidate : LocalCandidate A initialCode) where
  source : ProfiledOpenIndexedActiveRightControlledSemanticPoint A strategy
    hwin basis initialCode
  descriptor_eq :
    profiledOpenActiveRightControlledDescriptor A strategy hwin basis
      initialCode source = candidate.2
  class_eq :
    profiledOpenActiveRightProjectedClass A strategy hwin basis initialCode
      source = candidate.1.1.1

/-- Left anchor. -/
structure ProfiledOpenActiveLaneLeftCandidateAnchor
    (candidate : LocalCandidate A initialCode) where
  source : ProfiledOpenIndexedActiveLeftControlledSemanticPoint A strategy
    hwin basis initialCode
  descriptor_eq :
    profiledOpenActiveLeftControlledDescriptor A strategy hwin basis
      initialCode source = candidate.2
  class_eq :
    profiledOpenActiveLeftProjectedClass A strategy hwin basis initialCode
      source = candidate.1.1.2

/-- Process-one only needs a bank component when the current descriptor is
in the right coordinate. -/
def ProfiledOpenActiveLaneRightRuntimeLive
    (descriptor : LocalDescriptor A initialCode)
    (family : SidewiseTaggedFamily (LocalClass A initialCode)
      (LocalClass A initialCode) (LocalFamily A initialCode)) : Prop :=
  ProfiledOpenFixedSidewiseSemanticLive A strategy hwin basis initialCode
      (ProfiledOpenActiveLaneClassTagInvariant A strategy hwin basis
        initialCode)
      descriptor family ∧
    descriptor ∈ family.2.1

/-- Process-two active liveness. -/
def ProfiledOpenActiveLaneLeftRuntimeLive
    (descriptor : LocalDescriptor A initialCode)
    (family : SidewiseTaggedFamily (LocalClass A initialCode)
      (LocalClass A initialCode) (LocalFamily A initialCode)) : Prop :=
  ProfiledOpenFixedSidewiseSemanticLive A strategy hwin basis initialCode
      (ProfiledOpenActiveLaneClassTagInvariant A strategy hwin basis
        initialCode)
      descriptor family ∧
    descriptor ∈ family.2.2

/-- Every active right candidate has an honest attained anchor. -/
theorem exists_profiledOpenActiveLaneRightCandidateAnchor
    (candidate : LocalCandidate A initialCode)
    (hlive : ProfiledOpenActiveLaneRightRuntimeLive A strategy hwin basis
      initialCode candidate.2 candidate.1) :
    Nonempty (ProfiledOpenActiveLaneRightCandidateAnchor A strategy hwin basis
      initialCode candidate) := by
  rcases profiledOpenActiveLaneClassOf_rightAnchor A strategy hwin basis
      initialCode candidate.2 candidate.1.2 hlive.1.1 hlive.2 with
    ⟨source, hdescriptor, hclass⟩
  refine ⟨⟨source, hdescriptor, ?_⟩⟩
  exact hclass.trans (congrArg Prod.fst hlive.1.2).symm

/-- Every active left candidate has an attained anchor. -/
theorem exists_profiledOpenActiveLaneLeftCandidateAnchor
    (candidate : LocalCandidate A initialCode)
    (hlive : ProfiledOpenActiveLaneLeftRuntimeLive A strategy hwin basis
      initialCode candidate.2 candidate.1) :
    Nonempty (ProfiledOpenActiveLaneLeftCandidateAnchor A strategy hwin basis
      initialCode candidate) := by
  rcases profiledOpenActiveLaneClassOf_leftAnchor A strategy hwin basis
      initialCode candidate.2 candidate.1.2 hlive.1.1 hlive.2 with
    ⟨source, hdescriptor, hclass⟩
  refine ⟨⟨source, hdescriptor, ?_⟩⟩
  exact hclass.trans (congrArg Prod.snd hlive.1.2).symm

/-- Exact process-one receipt invariant.  Every two active possibilities at
the same reachable finite receipt have representing anchors in one literal
active-right local fibre. -/
def ProfiledOpenActiveLaneRightReceiptCoherentAt
    (Reachable : LocalSummary A initialCode → Prop)
    (summary : LocalSummary A initialCode) : Prop :=
  ∀ left right,
    sidewiseFiniteCandidatePossible Reachable summary left →
      ProfiledOpenActiveLaneRightRuntimeLive A strategy hwin basis initialCode
        left.2 left.1 →
    sidewiseFiniteCandidatePossible Reachable summary right →
      ProfiledOpenActiveLaneRightRuntimeLive A strategy hwin basis initialCode
        right.2 right.1 →
    ∃ leftAnchor : ProfiledOpenActiveLaneRightCandidateAnchor A strategy hwin
        basis initialCode left,
      ∃ rightAnchor : ProfiledOpenActiveLaneRightCandidateAnchor A strategy
        hwin basis initialCode right,
        ProfiledOpenIndexedActiveRightControlledLocalFibreRel A strategy hwin
          basis initialCode leftAnchor.source rightAnchor.source

/-- Process-two mirror. -/
def ProfiledOpenActiveLaneLeftReceiptCoherentAt
    (Reachable : LocalSummary A initialCode → Prop)
    (summary : LocalSummary A initialCode) : Prop :=
  ∀ left right,
    sidewiseFiniteCandidatePossible Reachable summary left →
      ProfiledOpenActiveLaneLeftRuntimeLive A strategy hwin basis initialCode
        left.2 left.1 →
    sidewiseFiniteCandidatePossible Reachable summary right →
      ProfiledOpenActiveLaneLeftRuntimeLive A strategy hwin basis initialCode
        right.2 right.1 →
    ∃ leftAnchor : ProfiledOpenActiveLaneLeftCandidateAnchor A strategy hwin
        basis initialCode left,
      ∃ rightAnchor : ProfiledOpenActiveLaneLeftCandidateAnchor A strategy
        hwin basis initialCode right,
        ProfiledOpenIndexedActiveLeftControlledLocalFibreRel A strategy hwin
          basis initialCode leftAnchor.source rightAnchor.source

/-! ## One fibre gives both physical behavior and bank-index uniformity -/

/-- Receipt coherence implies equality of the complete physical process-one
behavior, not only equality of a first output. -/
theorem profiledOpenActiveLaneRightReceipt_completeBehavior
    (Reachable : LocalSummary A initialCode → Prop)
    (summary : LocalSummary A initialCode)
    (hcoherent : ProfiledOpenActiveLaneRightReceiptCoherentAt A strategy hwin
      basis initialCode Reachable summary)
    (left right : LocalCandidate A initialCode)
    (hleft : sidewiseFiniteCandidatePossible Reachable summary left)
    (hleftLive : ProfiledOpenActiveLaneRightRuntimeLive A strategy hwin basis
      initialCode left.2 left.1)
    (hright : sidewiseFiniteCandidatePossible Reachable summary right)
    (hrightLive : ProfiledOpenActiveLaneRightRuntimeLive A strategy hwin basis
      initialCode right.2 right.1) :
    ∃ leftAnchor : ProfiledOpenActiveLaneRightCandidateAnchor A strategy hwin
        basis initialCode left,
      ∃ rightAnchor : ProfiledOpenActiveLaneRightCandidateAnchor A strategy
        hwin basis initialCode right,
        ProfiledOpenIndexedActiveRightCompleteBehaviorEq A strategy hwin basis
          leftAnchor.source.1 rightAnchor.source.1 := by
  rcases hcoherent left right hleft hleftLive hright hrightLive with
    ⟨leftAnchor, rightAnchor, hrel⟩
  exact ⟨leftAnchor, rightAnchor,
    profiledOpenIndexedActiveRightCompleteBehaviorEq_of_decoratedRel A
      strategy hwin basis hrel⟩

/-- Process-two complete-behavior mirror. -/
theorem profiledOpenActiveLaneLeftReceipt_completeBehavior
    (Reachable : LocalSummary A initialCode → Prop)
    (summary : LocalSummary A initialCode)
    (hcoherent : ProfiledOpenActiveLaneLeftReceiptCoherentAt A strategy hwin
      basis initialCode Reachable summary)
    (left right : LocalCandidate A initialCode)
    (hleft : sidewiseFiniteCandidatePossible Reachable summary left)
    (hleftLive : ProfiledOpenActiveLaneLeftRuntimeLive A strategy hwin basis
      initialCode left.2 left.1)
    (hright : sidewiseFiniteCandidatePossible Reachable summary right)
    (hrightLive : ProfiledOpenActiveLaneLeftRuntimeLive A strategy hwin basis
      initialCode right.2 right.1) :
    ∃ leftAnchor : ProfiledOpenActiveLaneLeftCandidateAnchor A strategy hwin
        basis initialCode left,
      ∃ rightAnchor : ProfiledOpenActiveLaneLeftCandidateAnchor A strategy
        hwin basis initialCode right,
        ProfiledOpenIndexedActiveLeftCompleteBehaviorEq A strategy hwin basis
          leftAnchor.source.1 rightAnchor.source.1 := by
  rcases hcoherent left right hleft hleftLive hright hrightLive with
    ⟨leftAnchor, rightAnchor, hrel⟩
  exact ⟨leftAnchor, rightAnchor,
    profiledOpenIndexedActiveLeftCompleteBehaviorEq_of_decoratedRel A
      strategy hwin basis hrel⟩

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Two represented right candidates in one fibre index literally the same
component of every bank. -/
theorem profiledOpenActiveLaneRightBankComponent_eq_of_anchors
    (bank : ProfiledOpenFixedSidewisePinnedBank A initialCode
      (LocalClass A initialCode) (LocalClass A initialCode))
    {left right : LocalCandidate A initialCode}
    (leftAnchor : ProfiledOpenActiveLaneRightCandidateAnchor A strategy hwin
      basis initialCode left)
    (rightAnchor : ProfiledOpenActiveLaneRightCandidateAnchor A strategy hwin
      basis initialCode right)
    (hrel : ProfiledOpenIndexedActiveRightControlledLocalFibreRel A strategy
      hwin basis initialCode leftAnchor.source rightAnchor.source) :
    bank.1 left.1.1.1 = bank.1 right.1.1.1 := by
  have hprojected := profiledOpenActiveRightProjectedClass_eq_of_rel A strategy
    hwin basis initialCode hrel
  have hclass : left.1.1.1 = right.1.1.1 :=
    leftAnchor.class_eq.symm.trans (hprojected.trans rightAnchor.class_eq)
  exact congrArg bank.1 hclass

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Left component equality. -/
theorem profiledOpenActiveLaneLeftBankComponent_eq_of_anchors
    (bank : ProfiledOpenFixedSidewisePinnedBank A initialCode
      (LocalClass A initialCode) (LocalClass A initialCode))
    {left right : LocalCandidate A initialCode}
    (leftAnchor : ProfiledOpenActiveLaneLeftCandidateAnchor A strategy hwin
      basis initialCode left)
    (rightAnchor : ProfiledOpenActiveLaneLeftCandidateAnchor A strategy hwin
      basis initialCode right)
    (hrel : ProfiledOpenIndexedActiveLeftControlledLocalFibreRel A strategy
      hwin basis initialCode leftAnchor.source rightAnchor.source) :
    bank.2 left.1.1.2 = bank.2 right.1.1.2 := by
  have hprojected := profiledOpenActiveLeftProjectedClass_eq_of_rel A strategy
    hwin basis initialCode hrel
  have hclass : left.1.1.2 = right.1.1.2 :=
    leftAnchor.class_eq.symm.trans (hprojected.trans rightAnchor.class_eq)
  exact congrArg bank.2 hclass

/-! ## The concrete finite local consumers -/

/-- On every coherent reachable receipt, *any* selected bank is process-one
behaviorally homogeneous under literal controller equality.  This is the
form consumed by a rational branch whose `moveAt` is known by common
validity, but need not be definitionally the canonical bank constructor. -/
theorem profiledOpenActiveLaneRightArbitraryBankFamily_behaviorHomogeneousAt
    (Reachable : LocalSummary A initialCode → Prop)
    (bankAt : LocalSummary A initialCode →
      ProfiledOpenFixedSidewisePinnedBank A initialCode
        (LocalClass A initialCode) (LocalClass A initialCode))
    (summary : LocalSummary A initialCode)
    (hcoherent : ProfiledOpenActiveLaneRightReceiptCoherentAt A strategy hwin
      basis initialCode Reachable summary) :
    SidewiseOneBankFamilyBehaviorHomogeneousAt
      (ProfiledOpenActiveLaneRightRuntimeLive A strategy hwin basis
        initialCode)
      (sidewiseFiniteCandidatePossible Reachable)
      (fun left right : ProfiledOpenFixedRightPinnedValue A initialCode ↦
        left = right)
      bankAt
      summary := by
  intro left right hleft hleftLive hright hrightLive
  rcases hcoherent left right hleft hleftLive hright hrightLive with
    ⟨leftAnchor, rightAnchor, hrel⟩
  exact profiledOpenActiveLaneRightBankComponent_eq_of_anchors A strategy hwin
    basis initialCode
    (bankAt summary)
    leftAnchor rightAnchor hrel

/-- Process-two arbitrary-bank behavioral homogeneity. -/
theorem profiledOpenActiveLaneLeftArbitraryBankFamily_behaviorHomogeneousAt
    (Reachable : LocalSummary A initialCode → Prop)
    (bankAt : LocalSummary A initialCode →
      ProfiledOpenFixedSidewisePinnedBank A initialCode
        (LocalClass A initialCode) (LocalClass A initialCode))
    (summary : LocalSummary A initialCode)
    (hcoherent : ProfiledOpenActiveLaneLeftReceiptCoherentAt A strategy hwin
      basis initialCode Reachable summary) :
    SidewiseTwoBankFamilyBehaviorHomogeneousAt
      (ProfiledOpenActiveLaneLeftRuntimeLive A strategy hwin basis initialCode)
      (sidewiseFiniteCandidatePossible Reachable)
      (fun left right : ProfiledOpenFixedLeftPinnedValue A initialCode ↦
        left = right)
      bankAt
      summary := by
  intro left right hleft hleftLive hright hrightLive
  rcases hcoherent left right hleft hleftLive hright hrightLive with
    ⟨leftAnchor, rightAnchor, hrel⟩
  exact profiledOpenActiveLaneLeftBankComponent_eq_of_anchors A strategy hwin
    basis initialCode
    (bankAt summary)
    leftAnchor rightAnchor hrel

/-- Canonical-bank specialization. -/
theorem profiledOpenActiveLaneRightBankFamily_behaviorHomogeneousAt
    (Reachable : LocalSummary A initialCode → Prop)
    (summary : LocalSummary A initialCode)
    (hcoherent : ProfiledOpenActiveLaneRightReceiptCoherentAt A strategy hwin
      basis initialCode Reachable summary) :
    SidewiseOneBankFamilyBehaviorHomogeneousAt
      (ProfiledOpenActiveLaneRightRuntimeLive A strategy hwin basis
        initialCode)
      (sidewiseFiniteCandidatePossible Reachable)
      (fun left right : ProfiledOpenFixedRightPinnedValue A initialCode ↦
        left = right)
      (profiledOpenActiveLaneSidewiseBank A strategy hwin basis initialCode)
      summary :=
  profiledOpenActiveLaneRightArbitraryBankFamily_behaviorHomogeneousAt A
    strategy hwin basis initialCode Reachable
    (profiledOpenActiveLaneSidewiseBank A strategy hwin basis initialCode)
    summary hcoherent

/-- Canonical process-two specialization. -/
theorem profiledOpenActiveLaneLeftBankFamily_behaviorHomogeneousAt
    (Reachable : LocalSummary A initialCode → Prop)
    (summary : LocalSummary A initialCode)
    (hcoherent : ProfiledOpenActiveLaneLeftReceiptCoherentAt A strategy hwin
      basis initialCode Reachable summary) :
    SidewiseTwoBankFamilyBehaviorHomogeneousAt
      (ProfiledOpenActiveLaneLeftRuntimeLive A strategy hwin basis initialCode)
      (sidewiseFiniteCandidatePossible Reachable)
      (fun left right : ProfiledOpenFixedLeftPinnedValue A initialCode ↦
        left = right)
      (profiledOpenActiveLaneSidewiseBank A strategy hwin basis initialCode)
      summary :=
  profiledOpenActiveLaneLeftArbitraryBankFamily_behaviorHomogeneousAt A
    strategy hwin basis initialCode Reachable
    (profiledOpenActiveLaneSidewiseBank A strategy hwin basis initialCode)
    summary hcoherent

/-- A finite process-one receipt automaton can execute an arbitrary selected
bank family without reading its hidden class whenever its reachable receipts
satisfy the explicit coherence law. -/
theorem profiledOpenActiveLaneRightArbitraryBankFamily_locallyConsumable
    (Reachable : LocalSummary A initialCode → Prop)
    (bankAt : LocalSummary A initialCode →
      ProfiledOpenFixedSidewisePinnedBank A initialCode
        (LocalClass A initialCode) (LocalClass A initialCode))
    (hcoherent : ∀ summary,
      ProfiledOpenActiveLaneRightReceiptCoherentAt A strategy hwin basis
        initialCode Reachable summary) :
    SidewiseOneBankFamilyLocallyConsumable
      (ProfiledOpenActiveLaneRightRuntimeLive A strategy hwin basis
        initialCode)
      (sidewiseFiniteCandidatePossible Reachable)
      (fun left right : ProfiledOpenFixedRightPinnedValue A initialCode ↦
        left = right)
      bankAt := by
  letI : Inhabited (ProfiledOpenFixedRightPinnedValue A initialCode) :=
    ⟨profiledOpenFixedDefaultRightPinnedValue A initialCode strategy hwin
      basis⟩
  apply (sidewiseOneBankFamilyLocallyConsumable_iff_behaviorHomogeneous
    (ProfiledOpenActiveLaneRightRuntimeLive A strategy hwin basis initialCode)
    (sidewiseFiniteCandidatePossible Reachable)
    (fun left right : ProfiledOpenFixedRightPinnedValue A initialCode ↦
      left = right)
    (fun _ _ h ↦ h.symm) ⟨fun _ _ _ h₁ h₂ ↦ h₁.trans h₂⟩
    bankAt).2
  intro summary
  exact profiledOpenActiveLaneRightArbitraryBankFamily_behaviorHomogeneousAt A
    strategy hwin basis initialCode Reachable bankAt summary
    (hcoherent summary)

/-- Process-two arbitrary-bank finite local consumer. -/
theorem profiledOpenActiveLaneLeftArbitraryBankFamily_locallyConsumable
    (Reachable : LocalSummary A initialCode → Prop)
    (bankAt : LocalSummary A initialCode →
      ProfiledOpenFixedSidewisePinnedBank A initialCode
        (LocalClass A initialCode) (LocalClass A initialCode))
    (hcoherent : ∀ summary,
      ProfiledOpenActiveLaneLeftReceiptCoherentAt A strategy hwin basis
        initialCode Reachable summary) :
    SidewiseTwoBankFamilyLocallyConsumable
      (ProfiledOpenActiveLaneLeftRuntimeLive A strategy hwin basis initialCode)
      (sidewiseFiniteCandidatePossible Reachable)
      (fun left right : ProfiledOpenFixedLeftPinnedValue A initialCode ↦
        left = right)
      bankAt := by
  letI : Inhabited (ProfiledOpenFixedLeftPinnedValue A initialCode) :=
    ⟨profiledOpenFixedDefaultLeftPinnedValue A initialCode strategy hwin
      basis⟩
  apply (sidewiseTwoBankFamilyLocallyConsumable_iff_behaviorHomogeneous
    (ProfiledOpenActiveLaneLeftRuntimeLive A strategy hwin basis initialCode)
    (sidewiseFiniteCandidatePossible Reachable)
    (fun left right : ProfiledOpenFixedLeftPinnedValue A initialCode ↦
      left = right)
    (fun _ _ h ↦ h.symm) ⟨fun _ _ _ h₁ h₂ ↦ h₁.trans h₂⟩
    bankAt).2
  intro summary
  exact profiledOpenActiveLaneLeftArbitraryBankFamily_behaviorHomogeneousAt A
    strategy hwin basis initialCode Reachable bankAt summary
    (hcoherent summary)

/-- Canonical process-one bank specialization. -/
theorem profiledOpenActiveLaneRightBankFamily_locallyConsumable
    (Reachable : LocalSummary A initialCode → Prop)
    (hcoherent : ∀ summary,
      ProfiledOpenActiveLaneRightReceiptCoherentAt A strategy hwin basis
        initialCode Reachable summary) :
    SidewiseOneBankFamilyLocallyConsumable
      (ProfiledOpenActiveLaneRightRuntimeLive A strategy hwin basis
        initialCode)
      (sidewiseFiniteCandidatePossible Reachable)
      (fun left right : ProfiledOpenFixedRightPinnedValue A initialCode ↦
        left = right)
      (profiledOpenActiveLaneSidewiseBank A strategy hwin basis
        initialCode) :=
  profiledOpenActiveLaneRightArbitraryBankFamily_locallyConsumable A strategy
    hwin basis initialCode Reachable
    (profiledOpenActiveLaneSidewiseBank A strategy hwin basis initialCode)
    hcoherent

/-- Canonical process-two bank specialization. -/
theorem profiledOpenActiveLaneLeftBankFamily_locallyConsumable
    (Reachable : LocalSummary A initialCode → Prop)
    (hcoherent : ∀ summary,
      ProfiledOpenActiveLaneLeftReceiptCoherentAt A strategy hwin basis
        initialCode Reachable summary) :
    SidewiseTwoBankFamilyLocallyConsumable
      (ProfiledOpenActiveLaneLeftRuntimeLive A strategy hwin basis initialCode)
      (sidewiseFiniteCandidatePossible Reachable)
      (fun left right : ProfiledOpenFixedLeftPinnedValue A initialCode ↦
        left = right)
      (profiledOpenActiveLaneSidewiseBank A strategy hwin basis
        initialCode) :=
  profiledOpenActiveLaneLeftArbitraryBankFamily_locallyConsumable A strategy
    hwin basis initialCode Reachable
    (profiledOpenActiveLaneSidewiseBank A strategy hwin basis initialCode)
    hcoherent

/-! ## Concrete fail-fast witnesses -/

/-- Two distinct right values selected at one reachable receipt refute the
concrete equality-based process-one consumer immediately. -/
theorem not_profiledOpenActiveLaneRightBankFamily_locallyConsumable_of_collision
    (Reachable : LocalSummary A initialCode → Prop)
    (summary : LocalSummary A initialCode)
    (left right : LocalCandidate A initialCode)
    (hleft : sidewiseFiniteCandidatePossible Reachable summary left)
    (hleftLive : ProfiledOpenActiveLaneRightRuntimeLive A strategy hwin basis
      initialCode left.2 left.1)
    (hright : sidewiseFiniteCandidatePossible Reachable summary right)
    (hrightLive : ProfiledOpenActiveLaneRightRuntimeLive A strategy hwin basis
      initialCode right.2 right.1)
    (hne :
      (profiledOpenActiveLaneSidewiseBank A strategy hwin basis initialCode
          summary).1 left.1.1.1 ≠
        (profiledOpenActiveLaneSidewiseBank A strategy hwin basis initialCode
          summary).1 right.1.1.1) :
    ¬ SidewiseOneBankFamilyLocallyConsumable
      (ProfiledOpenActiveLaneRightRuntimeLive A strategy hwin basis
        initialCode)
      (sidewiseFiniteCandidatePossible Reachable)
      (fun left right : ProfiledOpenFixedRightPinnedValue A initialCode ↦
        left = right)
      (profiledOpenActiveLaneSidewiseBank A strategy hwin basis
        initialCode) := by
  exact not_sidewiseOneBankFamilyLocallyConsumable_of_collision
    (ProfiledOpenActiveLaneRightRuntimeLive A strategy hwin basis initialCode)
    (sidewiseFiniteCandidatePossible Reachable)
    (fun left right : ProfiledOpenFixedRightPinnedValue A initialCode ↦
      left = right)
    (fun _ _ h ↦ h.symm) ⟨fun _ _ _ h₁ h₂ ↦ h₁.trans h₂⟩
    (profiledOpenActiveLaneSidewiseBank A strategy hwin basis initialCode)
    summary left right hleft hleftLive hright hrightLive hne

/-- Process-two concrete collision refutation. -/
theorem not_profiledOpenActiveLaneLeftBankFamily_locallyConsumable_of_collision
    (Reachable : LocalSummary A initialCode → Prop)
    (summary : LocalSummary A initialCode)
    (left right : LocalCandidate A initialCode)
    (hleft : sidewiseFiniteCandidatePossible Reachable summary left)
    (hleftLive : ProfiledOpenActiveLaneLeftRuntimeLive A strategy hwin basis
      initialCode left.2 left.1)
    (hright : sidewiseFiniteCandidatePossible Reachable summary right)
    (hrightLive : ProfiledOpenActiveLaneLeftRuntimeLive A strategy hwin basis
      initialCode right.2 right.1)
    (hne :
      (profiledOpenActiveLaneSidewiseBank A strategy hwin basis initialCode
          summary).2 left.1.1.2 ≠
        (profiledOpenActiveLaneSidewiseBank A strategy hwin basis initialCode
          summary).2 right.1.1.2) :
    ¬ SidewiseTwoBankFamilyLocallyConsumable
      (ProfiledOpenActiveLaneLeftRuntimeLive A strategy hwin basis initialCode)
      (sidewiseFiniteCandidatePossible Reachable)
      (fun left right : ProfiledOpenFixedLeftPinnedValue A initialCode ↦
        left = right)
      (profiledOpenActiveLaneSidewiseBank A strategy hwin basis
        initialCode) := by
  exact not_sidewiseTwoBankFamilyLocallyConsumable_of_collision
    (ProfiledOpenActiveLaneLeftRuntimeLive A strategy hwin basis initialCode)
    (sidewiseFiniteCandidatePossible Reachable)
    (fun left right : ProfiledOpenFixedLeftPinnedValue A initialCode ↦
      left = right)
    (fun _ _ h ↦ h.symm) ⟨fun _ _ _ h₁ h₂ ↦ h₁.trans h₂⟩
    (profiledOpenActiveLaneSidewiseBank A strategy hwin basis initialCode)
    summary left right hleft hleftLive hright hrightLive hne

end

end DetParityAutomaton

end DistributedSynthesis
