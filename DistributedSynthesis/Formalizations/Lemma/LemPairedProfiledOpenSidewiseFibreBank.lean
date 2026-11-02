/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenFibreProvenanceMove
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenSetValuedCommonMoveBoundary
import DistributedSynthesis.Formalizations.Lemma.LemSidewiseRelationalCandidateSuccessor

/-!
# A sidewise finite-fibre bank with sticky provenance

The complete pinned-family alphabet stores one public family in its sigma
coordinate.  `LemPairedProfiledOpenSetValuedCommonMoveBoundary` proves that a
single value of that alphabet cannot serve live candidates carrying different
family tags.

The finite-fibre construction already has the right replacement shape.  It
does not choose one global semantic representative.  It stores a right
controller for every finite process-one fibre class and, independently, a
left controller for every finite process-two fibre class.  This file packages
the provenance-preserving version of that whole bank.

Within one class, all descriptor projections use definitionally the same
blind sender controller.  At every reachable controller word and every
proof-side monitor state, each projection also retains a literal semantic
table witness.  The two sides are independent: no theorem asks their semantic
pasts, descriptors, or source witnesses to coincide.

The final tagged-atom interface records the exact operational invariant a
set-valued implementation must preserve.  Every active candidate retains its
finite side class.  Candidates in one process-local carried set must agree on
that process's active class; the process may then select its bank component
from its own finite local class.  No graph, lane, orientation, strict-leader
bit, or distinguished candidate is exposed.
-/

namespace DistributedSynthesis

universe u v x y s z p q

namespace DetParityAutomaton

/-! ## Generic finite side-class tags -/

/-- Correct enrichment of one old family tag by the two finite local-fibre
classes of its global descriptor.  The two equations are independent; they
do not assert a common semantic representative for the two fibres. -/
def ProfiledOpenSidewiseFibreTagsCorrect
    {TagGlobal TagOneClass TagTwoClass : Type q}
    (tagOneFibre : ProfiledOpenFiniteFibrePresentation
      TagGlobal TagOneClass)
    (tagTwoFibre : ProfiledOpenFiniteFibrePresentation
      TagGlobal TagTwoClass)
    {Family : Type p} (descriptor : TagGlobal)
    (family : SidewiseTaggedFamily TagOneClass TagTwoClass Family) : Prop :=
  tagOneFibre.classOf descriptor = family.1.1 ∧
    tagTwoFibre.classOf descriptor = family.1.2

/-- Semantic liveness enriched with the exact finite class tags. -/
def ProfiledOpenSidewiseFibreTaggedLive
    {TagGlobal TagOneClass TagTwoClass : Type q}
    (tagOneFibre : ProfiledOpenFiniteFibrePresentation
      TagGlobal TagOneClass)
    (tagTwoFibre : ProfiledOpenFiniteFibrePresentation
      TagGlobal TagTwoClass)
    {Family : Type p} (BaseLive : TagGlobal → Family → Prop)
    (descriptor : TagGlobal)
    (family : SidewiseTaggedFamily TagOneClass TagTwoClass Family) : Prop :=
  BaseLive descriptor family.2 ∧
    ProfiledOpenSidewiseFibreTagsCorrect tagOneFibre tagTwoFibre
      descriptor family

/-- Canonical enrichment of an old family tag.  This is the constructor the
exact successor relation must use: it records each side's finite class
directly from the actual child descriptor. -/
def profiledOpenSidewiseTaggedFamilyOf
    {TagGlobal TagOneClass TagTwoClass : Type q}
    (tagOneFibre : ProfiledOpenFiniteFibrePresentation
      TagGlobal TagOneClass)
    (tagTwoFibre : ProfiledOpenFiniteFibrePresentation
      TagGlobal TagTwoClass)
    {Family : Type p} (descriptor : TagGlobal) (family : Family) :
    SidewiseTaggedFamily TagOneClass TagTwoClass Family :=
  ((tagOneFibre.classOf descriptor, tagTwoFibre.classOf descriptor), family)

@[simp] theorem profiledOpenSidewiseTaggedFamilyOf_tagsCorrect
    {TagGlobal TagOneClass TagTwoClass : Type q}
    (tagOneFibre : ProfiledOpenFiniteFibrePresentation
      TagGlobal TagOneClass)
    (tagTwoFibre : ProfiledOpenFiniteFibrePresentation
      TagGlobal TagTwoClass)
    {Family : Type p} (descriptor : TagGlobal) (family : Family) :
    ProfiledOpenSidewiseFibreTagsCorrect tagOneFibre tagTwoFibre descriptor
      (profiledOpenSidewiseTaggedFamilyOf tagOneFibre tagTwoFibre
        descriptor family) := by
  exact ⟨rfl, rfl⟩

@[simp] theorem profiledOpenSidewiseTaggedFamilyOf_taggedLive_iff
    {TagGlobal TagOneClass TagTwoClass : Type q}
    (tagOneFibre : ProfiledOpenFiniteFibrePresentation
      TagGlobal TagOneClass)
    (tagTwoFibre : ProfiledOpenFiniteFibrePresentation
      TagGlobal TagTwoClass)
    {Family : Type p} (BaseLive : TagGlobal → Family → Prop)
    (descriptor : TagGlobal) (family : Family) :
    ProfiledOpenSidewiseFibreTaggedLive tagOneFibre tagTwoFibre BaseLive
        descriptor
        (profiledOpenSidewiseTaggedFamilyOf tagOneFibre tagTwoFibre
          descriptor family) ↔
      BaseLive descriptor family := by
  simp only [ProfiledOpenSidewiseFibreTaggedLive,
    profiledOpenSidewiseTaggedFamilyOf, ProfiledOpenSidewiseFibreTagsCorrect,
    and_true]

/-- The concrete finite-fibre invariant is exactly the generic tagged
successor invariant (up to the harmless orientation of the two equalities). -/
theorem profiledOpenSidewiseFibreTagsCorrect_iff_sidewiseTaggedFamilyCorrect
    {TagGlobal TagOneClass TagTwoClass : Type q}
    (tagOneFibre : ProfiledOpenFiniteFibrePresentation
      TagGlobal TagOneClass)
    (tagTwoFibre : ProfiledOpenFiniteFibrePresentation
      TagGlobal TagTwoClass)
    {Family : Type p} (descriptor : TagGlobal)
    (family : SidewiseTaggedFamily TagOneClass TagTwoClass Family) :
    ProfiledOpenSidewiseFibreTagsCorrect tagOneFibre tagTwoFibre
        descriptor family ↔
      SidewiseTaggedFamilyCorrect tagOneFibre.classOf tagTwoFibre.classOf
        descriptor family := by
  constructor
  · intro h
    exact ⟨h.1.symm, h.2.symm⟩
  · intro h
    exact ⟨h.1.symm, h.2.symm⟩

/-- Therefore canonical tagged successor coverage from
`LemSidewiseRelationalCandidateSuccessor` preserves precisely the invariant
consumed by the strong fibre bank. -/
theorem profiledOpenSidewiseFibreTaggedLive_iff_sidewiseTaggedLive
    {TagGlobal TagOneClass TagTwoClass : Type q}
    (tagOneFibre : ProfiledOpenFiniteFibrePresentation
      TagGlobal TagOneClass)
    (tagTwoFibre : ProfiledOpenFiniteFibrePresentation
      TagGlobal TagTwoClass)
    {Family : Type p} (BaseLive : TagGlobal → Family → Prop)
    (descriptor : TagGlobal)
    (family : SidewiseTaggedFamily TagOneClass TagTwoClass Family) :
    ProfiledOpenSidewiseFibreTaggedLive tagOneFibre tagTwoFibre BaseLive
        descriptor family ↔
      SidewiseTaggedLive tagOneFibre.classOf tagTwoFibre.classOf BaseLive
        descriptor family := by
  unfold ProfiledOpenSidewiseFibreTaggedLive SidewiseTaggedLive
  constructor
  · intro h
    exact ⟨h.1,
      (profiledOpenSidewiseFibreTagsCorrect_iff_sidewiseTaggedFamilyCorrect
        tagOneFibre tagTwoFibre descriptor family).mp h.2⟩
  · intro h
    exact ⟨h.1,
      (profiledOpenSidewiseFibreTagsCorrect_iff_sidewiseTaggedFamilyCorrect
        tagOneFibre tagTwoFibre descriptor family).mpr h.2⟩

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
  [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

variable {Global OneClass TwoClass : Type (max z u v x y s)}
variable [Fintype Global] [DecidableEq Global]
variable [Fintype OneClass] [DecidableEq OneClass]
variable [Fintype TwoClass] [DecidableEq TwoClass]

variable
  (oneFibre : ProfiledOpenFiniteFibrePresentation Global OneClass)
  (twoFibre : ProfiledOpenFiniteFibrePresentation Global TwoClass)

variable (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
variable (hwin : ∀ env : EnvironmentSequence In₁ In₂,
  A.Accepts (execution strategy env))
variable (basis : ∀ state : PairedProfiledTreeState A,
  (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)

variable
  (rightSource : Global → ProfiledOpenRightViewClass A)
  (leftSource : Global → ProfiledOpenLeftViewClass A)
  (rightRealization : ∀ descriptor,
    ProfiledOpenRightRealization A strategy hwin basis
      (rightSource descriptor))
  (leftRealization : ∀ descriptor,
    ProfiledOpenLeftRealization A strategy hwin basis
      (leftSource descriptor))

/-! ## The complete strong sidewise bank -/

/-- One finite value containing a provenance-preserving controller at every
process-one class and, independently, at every process-two class. -/
noncomputable abbrev ProfiledOpenPairedFibreProvenanceFamilyMove :=
  (∀ c : OneClass,
      ProfiledOpenRightPinnedFibreProvenanceMove A oneFibre strategy hwin
        basis rightSource rightRealization c) ×
    (∀ c : TwoClass,
      ProfiledOpenLeftPinnedFibreProvenanceMove A twoFibre strategy hwin
        basis leftSource leftRealization c)

set_option synthInstance.maxHeartbeats 400000 in
noncomputable instance : Fintype
    (ProfiledOpenPairedFibreProvenanceFamilyMove (A := A)
      (oneFibre := oneFibre) (twoFibre := twoFibre) (strategy := strategy)
      (hwin := hwin) (basis := basis) (rightSource := rightSource)
      (leftSource := leftSource) (rightRealization := rightRealization)
      (leftRealization := leftRealization)) := by
  classical
  infer_instance

/-- The two classwise common-sender certificates fill the complete strong
bank.  The certificates, and the resulting controllers, remain sidewise. -/
noncomputable def
    profiledOpenPairedFibreProvenanceFamilyMoveOfCommonSenderWins
    (hright : ProfiledOpenRightFibreCommonSenderWins A oneFibre strategy hwin
      basis rightSource rightRealization)
    (hleft : ProfiledOpenLeftFibreCommonSenderWins A twoFibre strategy hwin
      basis leftSource leftRealization) :
    ProfiledOpenPairedFibreProvenanceFamilyMove (A := A)
      (oneFibre := oneFibre) (twoFibre := twoFibre) (strategy := strategy)
      (hwin := hwin) (basis := basis) (rightSource := rightSource)
      (leftSource := leftSource) (rightRealization := rightRealization)
      (leftRealization := leftRealization) :=
  (fun c ↦
      profiledOpenRightPinnedFibreProvenanceMoveOfCommonSenderWins A oneFibre
        strategy hwin basis rightSource rightRealization hright c,
    fun c ↦
      profiledOpenLeftPinnedFibreProvenanceMoveOfCommonSenderWins A twoFibre
        strategy hwin basis leftSource leftRealization hleft c)

/-- Exact local-view agreement is one unconditional way of filling the
sidewise bank.  It is used proof-side; neither relation nor its class is a
leader signal. -/
noncomputable def profiledOpenPairedFibreProvenanceFamilyMoveOfViews
    (hright : ProfiledOpenRightFibreSenderViewsAgree A oneFibre strategy hwin
      basis rightSource rightRealization)
    (hleft : ProfiledOpenLeftFibreSenderViewsAgree A twoFibre strategy hwin
      basis leftSource leftRealization) :
    ProfiledOpenPairedFibreProvenanceFamilyMove (A := A)
      (oneFibre := oneFibre) (twoFibre := twoFibre) (strategy := strategy)
      (hwin := hwin) (basis := basis) (rightSource := rightSource)
      (leftSource := leftSource) (rightRealization := rightRealization)
      (leftRealization := leftRealization) :=
  profiledOpenPairedFibreProvenanceFamilyMoveOfCommonSenderWins A oneFibre
    twoFibre strategy hwin basis rightSource leftSource rightRealization
    leftRealization
    (profiledOpenRightFibreCommonSenderWins_of_senderStrategiesAgree A
      oneFibre strategy hwin basis rightSource rightRealization
      (profiledOpenRightFibreSenderStrategiesAgree_of_views A oneFibre
        strategy hwin basis rightSource rightRealization hright))
    (profiledOpenLeftFibreCommonSenderWins_of_senderStrategiesAgree A
      twoFibre strategy hwin basis leftSource leftRealization
      (profiledOpenLeftFibreSenderStrategiesAgree_of_views A twoFibre
        strategy hwin basis leftSource leftRealization hleft))

/-- Forget only the proof-only semantic provenance.  The literal classwise
controllers, transitions, and labels are unchanged. -/
noncomputable def ProfiledOpenPairedFibreProvenanceFamilyMove.toWeakBank
    (move : ProfiledOpenPairedFibreProvenanceFamilyMove (A := A)
      (oneFibre := oneFibre) (twoFibre := twoFibre) (strategy := strategy)
      (hwin := hwin) (basis := basis) (rightSource := rightSource)
      (leftSource := leftSource) (rightRealization := rightRealization)
      (leftRealization := leftRealization)) :
    ProfiledOpenPairedFibreFamilyMove (A := A) (oneFibre := oneFibre)
      (twoFibre := twoFibre) (strategy := strategy) (hwin := hwin)
      (basis := basis) (rightSource := rightSource)
      (leftSource := leftSource) (rightRealization := rightRealization)
      (leftRealization := leftRealization) :=
  (fun c ↦ (move.1 c).toPinnedMove A oneFibre strategy hwin basis
      rightSource rightRealization c,
    fun c ↦ (move.2 c).toPinnedMove A twoFibre strategy hwin basis
      leftSource leftRealization c)

/-! ## One whole blind sender inside each local class -/

/-- The rational process-one sender exposed by one descriptor projection of
a class bank.  The following theorem proves that the descriptor argument is
proof-only. -/
noncomputable def ProfiledOpenPairedFibreProvenanceFamilyMove.rightSenderAt
    (move : ProfiledOpenPairedFibreProvenanceFamilyMove (A := A)
      (oneFibre := oneFibre) (twoFibre := twoFibre) (strategy := strategy)
      (hwin := hwin) (basis := basis) (rightSource := rightSource)
      (leftSource := leftSource) (rightRealization := rightRealization)
      (leftRealization := leftRealization))
    (c : OneClass) (descriptor : oneFibre.Fibre c) :
    SenderBlockStrategy In₁ Out₁ :=
  fun word ↦
    ((((move.1 c).toPinnedMove A oneFibre strategy hwin basis rightSource
      rightRealization c).controllerFor
        (ProfiledOpenRightFibreRoot A oneFibre rightSource c)
        (descriptorRootPinnedMonitor
          (ProfiledOpenRightFibreRoot A oneFibre rightSource c)
          (profiledOpenRightFibreMonitor A oneFibre rightSource c)
          (profiledOpenRightFibreExpected A (oneFibre := oneFibre) strategy
            hwin basis rightSource rightRealization c))
        (profiledOpenRightFibreAllowed A oneFibre rightSource c)
        descriptor).labeledTree word).1

/-- Process-two mirror. -/
noncomputable def ProfiledOpenPairedFibreProvenanceFamilyMove.leftSenderAt
    (move : ProfiledOpenPairedFibreProvenanceFamilyMove (A := A)
      (oneFibre := oneFibre) (twoFibre := twoFibre) (strategy := strategy)
      (hwin := hwin) (basis := basis) (rightSource := rightSource)
      (leftSource := leftSource) (rightRealization := rightRealization)
      (leftRealization := leftRealization))
    (c : TwoClass) (descriptor : twoFibre.Fibre c) :
    SenderBlockStrategy In₂ Out₂ :=
  fun word ↦
    ((((move.2 c).toPinnedMove A twoFibre strategy hwin basis leftSource
      leftRealization c).controllerFor
        (ProfiledOpenLeftFibreRoot A twoFibre leftSource c)
        (descriptorRootPinnedMonitor
          (ProfiledOpenLeftFibreRoot A twoFibre leftSource c)
          (profiledOpenLeftFibreMonitor A twoFibre leftSource c)
          (profiledOpenLeftFibreExpected A (twoFibre := twoFibre) strategy
            hwin basis leftSource leftRealization c))
        (profiledOpenLeftFibreAllowed A twoFibre leftSource c)
        descriptor).labeledTree word).1

omit [Fintype OneClass] [Fintype TwoClass] [Inhabited Out₁] [Inhabited Out₂] in
/-- Every process-one descriptor projection in one finite local class exposes
the same *whole* sender strategy, not merely the same first output. -/
theorem
    ProfiledOpenPairedFibreProvenanceFamilyMove.rightSenderAt_eq
    (move : ProfiledOpenPairedFibreProvenanceFamilyMove (A := A)
      (oneFibre := oneFibre) (twoFibre := twoFibre) (strategy := strategy)
      (hwin := hwin) (basis := basis) (rightSource := rightSource)
      (leftSource := leftSource) (rightRealization := rightRealization)
      (leftRealization := leftRealization))
    (c : OneClass) (left right : oneFibre.Fibre c) :
    move.rightSenderAt A oneFibre twoFibre strategy hwin basis rightSource
        leftSource rightRealization leftRealization c left =
      move.rightSenderAt A oneFibre twoFibre strategy hwin basis rightSource
        leftSource rightRealization leftRealization c right := by
  funext word
  exact ((move.1 c).toPinnedMove A oneFibre strategy hwin basis rightSource
    rightRealization c).sender_eq
      (ProfiledOpenRightFibreRoot A oneFibre rightSource c)
      (profiledOpenRightFibreMonitor A oneFibre rightSource c)
      (profiledOpenRightFibreAllowed A oneFibre rightSource c)
      (profiledOpenRightFibreExpected A (oneFibre := oneFibre) strategy hwin
        basis rightSource rightRealization c) left right word

omit [Fintype OneClass] [Fintype TwoClass] [Inhabited Out₁] [Inhabited Out₂] in
/-- Process-two whole-sender equality inside one local class. -/
theorem
    ProfiledOpenPairedFibreProvenanceFamilyMove.leftSenderAt_eq
    (move : ProfiledOpenPairedFibreProvenanceFamilyMove (A := A)
      (oneFibre := oneFibre) (twoFibre := twoFibre) (strategy := strategy)
      (hwin := hwin) (basis := basis) (rightSource := rightSource)
      (leftSource := leftSource) (rightRealization := rightRealization)
      (leftRealization := leftRealization))
    (c : TwoClass) (left right : twoFibre.Fibre c) :
    move.leftSenderAt A oneFibre twoFibre strategy hwin basis rightSource
        leftSource rightRealization leftRealization c left =
      move.leftSenderAt A oneFibre twoFibre strategy hwin basis rightSource
        leftSource rightRealization leftRealization c right := by
  funext word
  exact ((move.2 c).toPinnedMove A twoFibre strategy hwin basis leftSource
    leftRealization c).sender_eq
      (ProfiledOpenLeftFibreRoot A twoFibre leftSource c)
      (profiledOpenLeftFibreMonitor A twoFibre leftSource c)
      (profiledOpenLeftFibreAllowed A twoFibre leftSource c)
      (profiledOpenLeftFibreExpected A (twoFibre := twoFibre) strategy hwin
        basis leftSource leftRealization c) left right word

/-! ## Arbitrary-node semantic provenance remains classwise -/

omit [Fintype TwoClass] [Inhabited Out₁] [Inhabited Out₂] [Fintype OneClass] in
/-- The right class bank retains the existing arbitrary-node semantic law for
every descriptor. -/
theorem ProfiledOpenPairedFibreProvenanceFamilyMove.right_semantic
    (move : ProfiledOpenPairedFibreProvenanceFamilyMove (A := A)
      (oneFibre := oneFibre) (twoFibre := twoFibre) (strategy := strategy)
      (hwin := hwin) (basis := basis) (rightSource := rightSource)
      (leftSource := leftSource) (rightRealization := rightRealization)
      (leftRealization := leftRealization))
    (c : OneClass) (descriptor : oneFibre.Fibre c) (word : List In₁)
    (state : (finiteRootFamilyMonitor
      (descriptorRootPinnedMonitor
        (ProfiledOpenRightFibreRoot A oneFibre rightSource c)
        (profiledOpenRightFibreMonitor A oneFibre rightSource c)
        (profiledOpenRightFibreExpected A (oneFibre := oneFibre) strategy
          hwin basis rightSource rightRealization c)
        descriptor)).State) :
    ∃ semanticPast,
      (fun input ↦
        (((((move.1 c).toPinnedMove A oneFibre strategy hwin basis rightSource
          rightRealization c).controllerFor
            (ProfiledOpenRightFibreRoot A oneFibre rightSource c)
            (descriptorRootPinnedMonitor
              (ProfiledOpenRightFibreRoot A oneFibre rightSource c)
              (profiledOpenRightFibreMonitor A oneFibre rightSource c)
              (profiledOpenRightFibreExpected A (oneFibre := oneFibre)
                strategy hwin basis rightSource rightRealization c))
            (profiledOpenRightFibreAllowed A oneFibre rightSource c)
            descriptor).labeledTree word).2 state
              ((ULift.up input.1.1, input.1.2), input.2))) =
        profiledOpenRightSemanticClassifiedFamilyReceiver A
          (rightSource descriptor.1) strategy hwin
          (rightRealization descriptor.1).entry basis semanticPast := by
  exact (move.1 c).controllerFor_semantic A oneFibre strategy hwin basis
    rightSource rightRealization c descriptor word state

omit [Fintype OneClass] [Inhabited Out₁] [Inhabited Out₂] [Fintype TwoClass] in
/-- Left classwise arbitrary-node semantic law. -/
theorem ProfiledOpenPairedFibreProvenanceFamilyMove.left_semantic
    (move : ProfiledOpenPairedFibreProvenanceFamilyMove (A := A)
      (oneFibre := oneFibre) (twoFibre := twoFibre) (strategy := strategy)
      (hwin := hwin) (basis := basis) (rightSource := rightSource)
      (leftSource := leftSource) (rightRealization := rightRealization)
      (leftRealization := leftRealization))
    (c : TwoClass) (descriptor : twoFibre.Fibre c) (word : List In₂)
    (state : (finiteRootFamilyMonitor
      (descriptorRootPinnedMonitor
        (ProfiledOpenLeftFibreRoot A twoFibre leftSource c)
        (profiledOpenLeftFibreMonitor A twoFibre leftSource c)
        (profiledOpenLeftFibreExpected A (twoFibre := twoFibre) strategy hwin
          basis leftSource leftRealization c)
        descriptor)).State) :
    ∃ semanticPast,
      (fun input ↦
        (((((move.2 c).toPinnedMove A twoFibre strategy hwin basis leftSource
          leftRealization c).controllerFor
            (ProfiledOpenLeftFibreRoot A twoFibre leftSource c)
            (descriptorRootPinnedMonitor
              (ProfiledOpenLeftFibreRoot A twoFibre leftSource c)
              (profiledOpenLeftFibreMonitor A twoFibre leftSource c)
              (profiledOpenLeftFibreExpected A (twoFibre := twoFibre)
                strategy hwin basis leftSource leftRealization c))
            (profiledOpenLeftFibreAllowed A twoFibre leftSource c)
            descriptor).labeledTree word).2 state
              ((ULift.up input.1.1, input.1.2), input.2))) =
        profiledOpenLeftSemanticClassifiedFamilyReceiver A
          (leftSource descriptor.1) strategy hwin
          (leftRealization descriptor.1).entry basis semanticPast := by
  exact (move.2 c).controllerFor_semantic A twoFibre strategy hwin basis
    leftSource leftRealization c descriptor word state

/-! ## Direct discharge of the candidate-wide common move -/

/-- Candidate validity for the strong sidewise bank.  The class equations
select well-typed projections; the bank component's type already contains
universal winning, root pinning, and arbitrary-node semantic provenance. -/
def ProfiledOpenSidewiseFibreBankCandidateValid
    {Family : Type p} (descriptor : Global)
    (family : SidewiseTaggedFamily OneClass TwoClass Family)
    (_move : ProfiledOpenPairedFibreProvenanceFamilyMove (A := A)
      (oneFibre := oneFibre) (twoFibre := twoFibre) (strategy := strategy)
      (hwin := hwin) (basis := basis) (rightSource := rightSource)
      (leftSource := leftSource) (rightRealization := rightRealization)
      (leftRealization := leftRealization)) : Prop :=
  ProfiledOpenSidewiseFibreTagsCorrect
    oneFibre twoFibre descriptor family

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype OneClass] [Fintype TwoClass] in
/-- Once exact atoms retain their two correct finite class tags, the entire
strong sidewise bank is one candidate-wide public move for *every* finite
candidate set.  Different old family tags are harmless.  This discharges the
uniform-lambda premise without recovering a hidden descriptor and without
choosing a common right/left semantic source.

The same fixed bank works for all candidate sets; the proof does not inspect
the selected live candidate. -/
theorem profiledOpenSidewiseFibreBank_commonMoveExists
    {Family : Type p} (BaseLive : Global → Family → Prop)
    (hright : ProfiledOpenRightFibreCommonSenderWins A oneFibre strategy hwin
      basis rightSource rightRealization)
    (hleft : ProfiledOpenLeftFibreCommonSenderWins A twoFibre strategy hwin
      basis leftSource leftRealization) :
    RelationalCandidateCommonMoveExists
      (Family := SidewiseTaggedFamily OneClass TwoClass Family)
      (Descriptor := Global)
      (Move := ProfiledOpenPairedFibreProvenanceFamilyMove (A := A)
        (oneFibre := oneFibre) (twoFibre := twoFibre) (strategy := strategy)
        (hwin := hwin) (basis := basis) (rightSource := rightSource)
        (leftSource := leftSource) (rightRealization := rightRealization)
        (leftRealization := leftRealization))
      (ProfiledOpenSidewiseFibreTaggedLive
        oneFibre twoFibre BaseLive)
      (ProfiledOpenSidewiseFibreBankCandidateValid
        (A := A) (oneFibre := oneFibre) (twoFibre := twoFibre)
        (strategy := strategy) (hwin := hwin) (basis := basis)
        (rightSource := rightSource) (leftSource := leftSource)
        (rightRealization := rightRealization)
        (leftRealization := leftRealization)) := by
  let bank :=
    profiledOpenPairedFibreProvenanceFamilyMoveOfCommonSenderWins A oneFibre
      twoFibre strategy hwin basis rightSource leftSource rightRealization
      leftRealization hright hleft
  intro candidates _hactive
  refine ⟨bank, ?_⟩
  intro candidate _hcandidate hlive
  exact hlive.2

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype OneClass] [Fintype TwoClass] in
/-- Exact-view agreement supplies the common-move theorem immediately.  This
is the direct concrete bridge from the existing fibre construction into the
fixed-policy relational candidate package. -/
theorem profiledOpenSidewiseFibreBank_commonMoveExists_of_views
    {Family : Type p} (BaseLive : Global → Family → Prop)
    (hright : ProfiledOpenRightFibreSenderViewsAgree A oneFibre strategy hwin
      basis rightSource rightRealization)
    (hleft : ProfiledOpenLeftFibreSenderViewsAgree A twoFibre strategy hwin
      basis leftSource leftRealization) :
    RelationalCandidateCommonMoveExists
      (Family := SidewiseTaggedFamily OneClass TwoClass Family)
      (Descriptor := Global)
      (Move := ProfiledOpenPairedFibreProvenanceFamilyMove (A := A)
        (oneFibre := oneFibre) (twoFibre := twoFibre) (strategy := strategy)
        (hwin := hwin) (basis := basis) (rightSource := rightSource)
        (leftSource := leftSource) (rightRealization := rightRealization)
        (leftRealization := leftRealization))
      (ProfiledOpenSidewiseFibreTaggedLive
        oneFibre twoFibre BaseLive)
      (ProfiledOpenSidewiseFibreBankCandidateValid
        (A := A) (oneFibre := oneFibre) (twoFibre := twoFibre)
        (strategy := strategy) (hwin := hwin) (basis := basis)
        (rightSource := rightSource) (leftSource := leftSource)
        (rightRealization := rightRealization)
        (leftRealization := leftRealization)) :=
  profiledOpenSidewiseFibreBank_commonMoveExists A oneFibre twoFibre strategy
    hwin basis rightSource leftSource rightRealization leftRealization
    BaseLive
    (profiledOpenRightFibreCommonSenderWins_of_senderStrategiesAgree A
      oneFibre strategy hwin basis rightSource rightRealization
      (profiledOpenRightFibreSenderStrategiesAgree_of_views A oneFibre
        strategy hwin basis rightSource rightRealization hright))
    (profiledOpenLeftFibreCommonSenderWins_of_senderStrategiesAgree A
      twoFibre strategy hwin basis leftSource leftRealization
      (profiledOpenLeftFibreSenderStrategiesAgree_of_views A twoFibre
        strategy hwin basis leftSource leftRealization hleft))

end

/-! ## Tagged atoms and the local-class invariant -/

section TaggedAtoms

variable {TagGlobal TagOneClass TagTwoClass : Type q}
variable {Payload : Type p}
variable
  (tagOneFibre : ProfiledOpenFiniteFibrePresentation
    TagGlobal TagOneClass)
  (tagTwoFibre : ProfiledOpenFiniteFibrePresentation
    TagGlobal TagTwoClass)

/-- A set-valued atom enriched with independent finite side classes.  An
inactive side is `none`; an active side retains a class together with its
descriptor in that exact fibre.  `payload` may contain the old family and DPA
descriptor used by the outer relational certificate. -/
structure ProfiledOpenSidewiseFibreAtom
    {FibreGlobal FibreOneClass FibreTwoClass : Type q}
    (oneFibre : ProfiledOpenFiniteFibrePresentation
      FibreGlobal FibreOneClass)
    (twoFibre : ProfiledOpenFiniteFibrePresentation
      FibreGlobal FibreTwoClass)
    (Payload : Type p) where
  payload : Payload
  right : Option (Sigma oneFibre.Fibre)
  left : Option (Sigma twoFibre.Fibre)

noncomputable instance [Fintype TagGlobal] [Fintype TagOneClass]
    [Fintype TagTwoClass] [Fintype Payload] : Fintype
    (ProfiledOpenSidewiseFibreAtom (FibreGlobal := TagGlobal)
      (FibreOneClass := TagOneClass) (FibreTwoClass := TagTwoClass)
      tagOneFibre tagTwoFibre Payload) := by
  classical
  let encode : ProfiledOpenSidewiseFibreAtom (FibreGlobal := TagGlobal)
      (FibreOneClass := TagOneClass) (FibreTwoClass := TagTwoClass)
      tagOneFibre tagTwoFibre Payload →
      Payload × Option (Sigma tagOneFibre.Fibre) ×
        Option (Sigma tagTwoFibre.Fibre) :=
    fun atom ↦ (atom.payload, atom.right, atom.left)
  exact Fintype.ofInjective encode (by
    intro left right heq
    rcases left with ⟨leftPayload, leftRight, leftLeft⟩
    rcases right with ⟨rightPayload, rightRight, rightLeft⟩
    simp only [encode, Prod.mk.injEq] at heq
    rcases heq with ⟨rfl, rfl, rfl⟩
    rfl)

/-- The active process-one class carried by an atom. -/
def ProfiledOpenSidewiseFibreAtom.rightClass?
    (atom : ProfiledOpenSidewiseFibreAtom (FibreGlobal := TagGlobal)
      (FibreOneClass := TagOneClass) (FibreTwoClass := TagTwoClass)
      tagOneFibre tagTwoFibre Payload) :
    Option TagOneClass :=
  atom.right.map Sigma.fst

/-- The active process-two class carried by an atom. -/
def ProfiledOpenSidewiseFibreAtom.leftClass?
    (atom : ProfiledOpenSidewiseFibreAtom (FibreGlobal := TagGlobal)
      (FibreOneClass := TagOneClass) (FibreTwoClass := TagTwoClass)
      tagOneFibre tagTwoFibre Payload) :
    Option TagTwoClass :=
  atom.left.map Sigma.fst

/-- All active right candidates in one process-local carried set have one
finite local class.  Inactive candidates impose no class. -/
def ProfiledOpenSidewiseRightClassCoherent
    (current : Finset
      (ProfiledOpenSidewiseFibreAtom (FibreGlobal := TagGlobal)
        (FibreOneClass := TagOneClass) (FibreTwoClass := TagTwoClass)
        tagOneFibre tagTwoFibre Payload)) : Prop :=
  ∀ left ∈ current, ∀ right ∈ current, ∀ leftClass rightClass,
    left.rightClass? (TagGlobal := TagGlobal) (TagOneClass := TagOneClass)
        (TagTwoClass := TagTwoClass) tagOneFibre tagTwoFibre =
        some leftClass →
    right.rightClass? (TagGlobal := TagGlobal) (TagOneClass := TagOneClass)
        (TagTwoClass := TagTwoClass) tagOneFibre tagTwoFibre =
        some rightClass →
    leftClass = rightClass

/-- Process-two mirror of local-class coherence. -/
def ProfiledOpenSidewiseLeftClassCoherent
    (current : Finset
      (ProfiledOpenSidewiseFibreAtom (FibreGlobal := TagGlobal)
        (FibreOneClass := TagOneClass) (FibreTwoClass := TagTwoClass)
        tagOneFibre tagTwoFibre Payload)) : Prop :=
  ∀ left ∈ current, ∀ right ∈ current, ∀ leftClass rightClass,
    left.leftClass? (TagGlobal := TagGlobal) (TagOneClass := TagOneClass)
        (TagTwoClass := TagTwoClass) tagOneFibre tagTwoFibre =
        some leftClass →
    right.leftClass? (TagGlobal := TagGlobal) (TagOneClass := TagOneClass)
        (TagTwoClass := TagTwoClass) tagOneFibre tagTwoFibre =
        some rightClass →
    leftClass = rightClass

/-- The exact sidewise invariant consumed by a graph-blind implementation.
It does not require the right and left class witnesses to arise from one
global semantic representative. -/
def ProfiledOpenSidewiseClassCoherent
    (current : Finset
      (ProfiledOpenSidewiseFibreAtom (FibreGlobal := TagGlobal)
        (FibreOneClass := TagOneClass) (FibreTwoClass := TagTwoClass)
        tagOneFibre tagTwoFibre Payload)) : Prop :=
  ProfiledOpenSidewiseRightClassCoherent tagOneFibre tagTwoFibre current ∧
    ProfiledOpenSidewiseLeftClassCoherent tagOneFibre tagTwoFibre current

end TaggedAtoms

end DetParityAutomaton

end DistributedSynthesis
