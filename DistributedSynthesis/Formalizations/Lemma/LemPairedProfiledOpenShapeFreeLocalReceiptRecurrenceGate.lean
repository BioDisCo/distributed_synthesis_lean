/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenShapeFreeObservableReceiptFilter

/-!
# The finite local recurrence gate for witnessed receipts

Fixing one projected-class receipt makes the witnessed candidate successors
locally coherent, but a distributed implementation still has to compute the
*next* receipt from finite local data.  It may not choose the receipt of the
actual hidden candidate.  In particular, one permanently unavailable bit is
not reconstructed here as a leader, direction, lane, or current-graph flag.

The local observation below has exactly the arguments of an honest local
summary transition:

* the process's current finite receipt and control, and its own input;
* on a receive only, the delivered partner receipt/control and partner input.

The proof-side compatibility relation may quantify over semantic candidates,
banks, and pointed queries.  Those objects do **not** occur in the argument of
the extracted transition.  Receipt functionality says that every witnessed
exact successor represented by one such local observation has the same own
receipt coordinate.  Under that law, arbitrary choice is harmless and gives
a finite local transition.  A concrete collision refutes functionality.

This isolates the remaining model obligation without pretending that the
current global pointed-query type is locally observable: that type contains a
proof-side active side and both query vectors.  A later adapter must construct
the compatibility relation from the actual local summary transitions and
prove coverage plus the functionality law below.
-/

namespace DistributedSynthesis

universe i u v x y s rc lc r c pr pc

/-! ## Honest finite local transition inputs -/

/-- The finite state locally retained by one process.  The receipt and the
remaining controller state are both explicit; neither is a semantic witness.
-/
abbrev ShapeFreeFiniteReceiptControlState
    (Receipt : Type r) (Control : Type c) :=
  Receipt × Control

/-- The only two locally distinguishable transition forms.  The sum tag is
`noRecv` versus `recv`, not a graph orientation.  In the receive case the
partner state is available because it is the finite payload delivered by the
model. -/
abbrev ShapeFreeFiniteLocalReceiptObservation
    (Receipt : Type r) (Control : Type c) (OwnInput : Type u)
    (PartnerReceipt : Type pr) (PartnerControl : Type pc)
    (PartnerInput : Type v) :=
  (ShapeFreeFiniteReceiptControlState Receipt Control × OwnInput) ⊕
    (ShapeFreeFiniteReceiptControlState Receipt Control × OwnInput ×
      ShapeFreeFiniteReceiptControlState PartnerReceipt PartnerControl ×
      PartnerInput)

/-- Any functional nonempty relation from a finite local observation to a
receipt induces one local receipt update.  The default branch is used only
where the relation represents no exact successor. -/
noncomputable def shapeFreeFiniteLocalNextReceipt
    {Local : Type i} {Receipt : Type r} [Inhabited Receipt]
    (Possible : Local → Receipt → Prop) (observation : Local) : Receipt := by
  classical
  exact if h : ∃ receipt, Possible observation receipt then
    Classical.choose h
  else default

/-- The abstract uniqueness law needed by the local choice above. -/
def ShapeFreeFiniteLocalReceiptFunctional
    {Local : Type i} {Receipt : Type r}
    (Possible : Local → Receipt → Prop) : Prop :=
  ∀ observation left right,
    Possible observation left → Possible observation right → left = right

/-- The local choice equals every represented possible receipt. -/
theorem shapeFreeFiniteLocalNextReceipt_eq
    {Local : Type i} {Receipt : Type r} [Inhabited Receipt]
    (Possible : Local → Receipt → Prop)
    (hfunctional : ShapeFreeFiniteLocalReceiptFunctional Possible)
    {observation : Local} {receipt : Receipt}
    (hpossible : Possible observation receipt) :
    shapeFreeFiniteLocalNextReceipt Possible observation = receipt := by
  classical
  unfold shapeFreeFiniteLocalNextReceipt
  rw [dif_pos ⟨receipt, hpossible⟩]
  exact hfunctional observation (Classical.choose ⟨receipt, hpossible⟩) receipt
    (Classical.choose_spec ⟨receipt, hpossible⟩) hpossible

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

private abbrev RecurrenceClass :=
  ProfiledOpenActiveLaneSideClass A initialCode

private abbrev RecurrenceCandidate :=
  ProfiledOpenActiveLaneTaggedCandidate A initialCode

private abbrev RecurrenceBank :=
  ProfiledOpenFixedSidewisePinnedBank A initialCode
    (RecurrenceClass A initialCode) (RecurrenceClass A initialCode)

private abbrev RecurrenceQuery :=
  ProfiledOpenFixedSidewiseReachablePointedQuery A initialCode

private abbrev RecurrenceControlStep :=
  ProfiledOpenFixedSidewiseControlStep A initialCode

/-! ## Process-local observations and proof-side compatibility -/

/-- Process one's honest local observation type.  `RightControl` and
`LeftControl` are arbitrary finite public controller carriers. -/
abbrev ProfiledOpenActiveLaneRightLocalReceiptObservation
    (RightControl : Type rc) (LeftControl : Type lc) :=
  ShapeFreeFiniteLocalReceiptObservation
    (RecurrenceClass A initialCode) RightControl In₁
    (RecurrenceClass A initialCode) LeftControl In₂

/-- Process-two mirror, with self and partner input alphabets swapped. -/
abbrev ProfiledOpenActiveLaneLeftLocalReceiptObservation
    (RightControl : Type rc) (LeftControl : Type lc) :=
  ShapeFreeFiniteLocalReceiptObservation
    (RecurrenceClass A initialCode) LeftControl In₂
    (RecurrenceClass A initialCode) RightControl In₁

/-- Proof-only interpretation of one process-one local observation.  Its
arguments after `local` are deliberately not supplied to the local update.
-/
abbrev ProfiledOpenActiveLaneRightWitnessedLocalCompatibility
    (RightControl : Type rc) (LeftControl : Type lc) :=
  ProfiledOpenActiveLaneRightLocalReceiptObservation A initialCode
      RightControl LeftControl →
    RecurrenceCandidate A initialCode →
    RecurrenceBank A initialCode →
    RecurrenceQuery A initialCode →
    RecurrenceCandidate A initialCode → Prop

/-- Process-two proof-only interpretation. -/
abbrev ProfiledOpenActiveLaneLeftWitnessedLocalCompatibility
    (RightControl : Type rc) (LeftControl : Type lc) :=
  ProfiledOpenActiveLaneLeftLocalReceiptObservation A initialCode
      RightControl LeftControl →
    RecurrenceCandidate A initialCode →
    RecurrenceBank A initialCode →
    RecurrenceQuery A initialCode →
    RecurrenceCandidate A initialCode → Prop

/-- The witnessed source-aware edge together with its descriptor-control
step.  This is the exact candidate edge consumed by the receipt-coherence
theorems, not the older canonical-target edge. -/
def ProfiledOpenActiveLaneWitnessedRecurrenceGood
    (source : RecurrenceCandidate A initialCode)
    (bank : RecurrenceBank A initialCode)
    (query : RecurrenceQuery A initialCode)
    (target : RecurrenceCandidate A initialCode) : Prop :=
  SourceAwareRelationalFamilyCandidateGood
    (profiledOpenActiveLaneWitnessedCandidateEdge A strategy hwin basis
      initialCode)
    (RecurrenceControlStep A initialCode) source bank query target

/-! ## Possible receipts represented by one local transition -/

/-- A process-one receipt is possible at `local` iff some hidden candidate
edge represented by that same local observation produces it and the target is
witnessed-live on process one's lane. -/
def ProfiledOpenActiveLaneRightWitnessedReceiptPossible
    {RightControl : Type rc} {LeftControl : Type lc}
    (Compatible : ProfiledOpenActiveLaneRightWitnessedLocalCompatibility A
      initialCode RightControl LeftControl)
    (observation : ProfiledOpenActiveLaneRightLocalReceiptObservation A initialCode
      RightControl LeftControl)
    (receipt : RecurrenceClass A initialCode) : Prop :=
  ∃ source bank query target,
    Compatible observation source bank query target ∧
      ProfiledOpenActiveLaneWitnessedRecurrenceGood A strategy hwin basis
        initialCode source bank query target ∧
      ProfiledOpenActiveLaneRightWitnessedRuntimeLive A strategy hwin basis
        initialCode target.2 target.1 ∧
      target.1.1.1 = receipt

/-- Process-two mirror. -/
def ProfiledOpenActiveLaneLeftWitnessedReceiptPossible
    {RightControl : Type rc} {LeftControl : Type lc}
    (Compatible : ProfiledOpenActiveLaneLeftWitnessedLocalCompatibility A
      initialCode RightControl LeftControl)
    (observation : ProfiledOpenActiveLaneLeftLocalReceiptObservation A initialCode
      RightControl LeftControl)
    (receipt : RecurrenceClass A initialCode) : Prop :=
  ∃ source bank query target,
    Compatible observation source bank query target ∧
      ProfiledOpenActiveLaneWitnessedRecurrenceGood A strategy hwin basis
        initialCode source bank query target ∧
      ProfiledOpenActiveLaneLeftWitnessedRuntimeLive A strategy hwin basis
        initialCode target.2 target.1 ∧
      target.1.1.2 = receipt

/-- The dangerous process-one functionality gate.  It quantifies over all
hidden exact successors compatible with one local observable transition. -/
def ProfiledOpenActiveLaneRightWitnessedReceiptFunctional
    {RightControl : Type rc} {LeftControl : Type lc}
    (Compatible : ProfiledOpenActiveLaneRightWitnessedLocalCompatibility A
      initialCode RightControl LeftControl) : Prop :=
  ShapeFreeFiniteLocalReceiptFunctional
    (ProfiledOpenActiveLaneRightWitnessedReceiptPossible A strategy hwin basis
      initialCode Compatible)

/-- Process-two dangerous functionality gate. -/
def ProfiledOpenActiveLaneLeftWitnessedReceiptFunctional
    {RightControl : Type rc} {LeftControl : Type lc}
    (Compatible : ProfiledOpenActiveLaneLeftWitnessedLocalCompatibility A
      initialCode RightControl LeftControl) : Prop :=
  ShapeFreeFiniteLocalReceiptFunctional
    (ProfiledOpenActiveLaneLeftWitnessedReceiptPossible A strategy hwin basis
      initialCode Compatible)

/-! ## Concrete fail-fast collision certificates -/

/-- A same-local-observation pair of witnessed process-one successors with
different own receipts.  Such a witness disproves every receipt update based
only on this local observation. -/
def ProfiledOpenActiveLaneRightWitnessedReceiptCollision
    {RightControl : Type rc} {LeftControl : Type lc}
    (Compatible : ProfiledOpenActiveLaneRightWitnessedLocalCompatibility A
      initialCode RightControl LeftControl) : Prop :=
  ∃ observation leftSource leftBank leftQuery leftTarget
      rightSource rightBank rightQuery rightTarget,
    Compatible observation leftSource leftBank leftQuery leftTarget ∧
      ProfiledOpenActiveLaneWitnessedRecurrenceGood A strategy hwin basis
        initialCode leftSource leftBank leftQuery leftTarget ∧
      ProfiledOpenActiveLaneRightWitnessedRuntimeLive A strategy hwin basis
        initialCode leftTarget.2 leftTarget.1 ∧
      Compatible observation rightSource rightBank rightQuery rightTarget ∧
      ProfiledOpenActiveLaneWitnessedRecurrenceGood A strategy hwin basis
        initialCode rightSource rightBank rightQuery rightTarget ∧
      ProfiledOpenActiveLaneRightWitnessedRuntimeLive A strategy hwin basis
        initialCode rightTarget.2 rightTarget.1 ∧
      leftTarget.1.1.1 ≠ rightTarget.1.1.1

/-- Process-two collision certificate. -/
def ProfiledOpenActiveLaneLeftWitnessedReceiptCollision
    {RightControl : Type rc} {LeftControl : Type lc}
    (Compatible : ProfiledOpenActiveLaneLeftWitnessedLocalCompatibility A
      initialCode RightControl LeftControl) : Prop :=
  ∃ observation leftSource leftBank leftQuery leftTarget
      rightSource rightBank rightQuery rightTarget,
    Compatible observation leftSource leftBank leftQuery leftTarget ∧
      ProfiledOpenActiveLaneWitnessedRecurrenceGood A strategy hwin basis
        initialCode leftSource leftBank leftQuery leftTarget ∧
      ProfiledOpenActiveLaneLeftWitnessedRuntimeLive A strategy hwin basis
        initialCode leftTarget.2 leftTarget.1 ∧
      Compatible observation rightSource rightBank rightQuery rightTarget ∧
      ProfiledOpenActiveLaneWitnessedRecurrenceGood A strategy hwin basis
        initialCode rightSource rightBank rightQuery rightTarget ∧
      ProfiledOpenActiveLaneLeftWitnessedRuntimeLive A strategy hwin basis
        initialCode rightTarget.2 rightTarget.1 ∧
      leftTarget.1.1.2 ≠ rightTarget.1.1.2

/-- Functionality is exactly absence of a process-one collision. -/
theorem profiledOpenActiveLaneRightWitnessedReceiptFunctional_iff_noCollision
    {RightControl : Type rc} {LeftControl : Type lc}
    (Compatible : ProfiledOpenActiveLaneRightWitnessedLocalCompatibility A
      initialCode RightControl LeftControl) :
    ProfiledOpenActiveLaneRightWitnessedReceiptFunctional A strategy hwin basis
        initialCode Compatible ↔
      ¬ ProfiledOpenActiveLaneRightWitnessedReceiptCollision A strategy hwin
        basis initialCode Compatible := by
  constructor
  · intro hfunctional hcollision
    rcases hcollision with ⟨observation, leftSource, leftBank, leftQuery,
      leftTarget, rightSource, rightBank, rightQuery, rightTarget,
      hleftCompatible, hleftGood, hleftLive, hrightCompatible, hrightGood,
      hrightLive, hne⟩
    apply hne
    exact hfunctional observation leftTarget.1.1.1 rightTarget.1.1.1
      ⟨leftSource, leftBank, leftQuery, leftTarget, hleftCompatible,
        hleftGood, hleftLive, rfl⟩
      ⟨rightSource, rightBank, rightQuery, rightTarget, hrightCompatible,
        hrightGood, hrightLive, rfl⟩
  · intro hnoCollision observation left right hleft hright
    rcases hleft with ⟨leftSource, leftBank, leftQuery, leftTarget,
      hleftCompatible, hleftGood, hleftLive, hleftReceipt⟩
    rcases hright with ⟨rightSource, rightBank, rightQuery, rightTarget,
      hrightCompatible, hrightGood, hrightLive, hrightReceipt⟩
    rw [← hleftReceipt, ← hrightReceipt]
    by_contra hne
    exact hnoCollision ⟨observation, leftSource, leftBank, leftQuery, leftTarget,
      rightSource, rightBank, rightQuery, rightTarget, hleftCompatible,
      hleftGood, hleftLive, hrightCompatible, hrightGood, hrightLive, hne⟩

/-- Functionality is exactly absence of a process-two collision. -/
theorem profiledOpenActiveLaneLeftWitnessedReceiptFunctional_iff_noCollision
    {RightControl : Type rc} {LeftControl : Type lc}
    (Compatible : ProfiledOpenActiveLaneLeftWitnessedLocalCompatibility A
      initialCode RightControl LeftControl) :
    ProfiledOpenActiveLaneLeftWitnessedReceiptFunctional A strategy hwin basis
        initialCode Compatible ↔
      ¬ ProfiledOpenActiveLaneLeftWitnessedReceiptCollision A strategy hwin
        basis initialCode Compatible := by
  constructor
  · intro hfunctional hcollision
    rcases hcollision with ⟨observation, leftSource, leftBank, leftQuery,
      leftTarget, rightSource, rightBank, rightQuery, rightTarget,
      hleftCompatible, hleftGood, hleftLive, hrightCompatible, hrightGood,
      hrightLive, hne⟩
    apply hne
    exact hfunctional observation leftTarget.1.1.2 rightTarget.1.1.2
      ⟨leftSource, leftBank, leftQuery, leftTarget, hleftCompatible,
        hleftGood, hleftLive, rfl⟩
      ⟨rightSource, rightBank, rightQuery, rightTarget, hrightCompatible,
        hrightGood, hrightLive, rfl⟩
  · intro hnoCollision observation left right hleft hright
    rcases hleft with ⟨leftSource, leftBank, leftQuery, leftTarget,
      hleftCompatible, hleftGood, hleftLive, hleftReceipt⟩
    rcases hright with ⟨rightSource, rightBank, rightQuery, rightTarget,
      hrightCompatible, hrightGood, hrightLive, hrightReceipt⟩
    rw [← hleftReceipt, ← hrightReceipt]
    by_contra hne
    exact hnoCollision ⟨observation, leftSource, leftBank, leftQuery, leftTarget,
      rightSource, rightBank, rightQuery, rightTarget, hleftCompatible,
      hleftGood, hleftLive, hrightCompatible, hrightGood, hrightLive, hne⟩

/-! ## The extracted finite local receipt updates -/

/-- Process one's next receipt.  Its only runtime argument is `local`; all
semantic objects occur under `Possible` and are erased by functionality. -/
noncomputable def profiledOpenActiveLaneRightWitnessedLocalNextReceipt
    {RightControl : Type rc} {LeftControl : Type lc}
    (Compatible : ProfiledOpenActiveLaneRightWitnessedLocalCompatibility A
      initialCode RightControl LeftControl)
    (observation : ProfiledOpenActiveLaneRightLocalReceiptObservation A initialCode
      RightControl LeftControl) : RecurrenceClass A initialCode :=
  shapeFreeFiniteLocalNextReceipt
    (ProfiledOpenActiveLaneRightWitnessedReceiptPossible A strategy hwin basis
      initialCode Compatible) observation

/-- Process-two mirror. -/
noncomputable def profiledOpenActiveLaneLeftWitnessedLocalNextReceipt
    {RightControl : Type rc} {LeftControl : Type lc}
    (Compatible : ProfiledOpenActiveLaneLeftWitnessedLocalCompatibility A
      initialCode RightControl LeftControl)
    (observation : ProfiledOpenActiveLaneLeftLocalReceiptObservation A initialCode
      RightControl LeftControl) : RecurrenceClass A initialCode :=
  shapeFreeFiniteLocalNextReceipt
    (ProfiledOpenActiveLaneLeftWitnessedReceiptPossible A strategy hwin basis
      initialCode Compatible) observation

/-- Under functionality, every compatible witnessed successor is retained by
the receipt computed from process one's finite local observation. -/
theorem profiledOpenActiveLaneRightWitnessedLocalNextReceipt_eq_target
    {RightControl : Type rc} {LeftControl : Type lc}
    (Compatible : ProfiledOpenActiveLaneRightWitnessedLocalCompatibility A
      initialCode RightControl LeftControl)
    (hfunctional :
      ProfiledOpenActiveLaneRightWitnessedReceiptFunctional A strategy hwin
        basis initialCode Compatible)
    {observation : ProfiledOpenActiveLaneRightLocalReceiptObservation A initialCode
      RightControl LeftControl}
    {source target : RecurrenceCandidate A initialCode}
    {bank : RecurrenceBank A initialCode}
    {query : RecurrenceQuery A initialCode}
    (hcompatible : Compatible observation source bank query target)
    (hgood : ProfiledOpenActiveLaneWitnessedRecurrenceGood A strategy hwin
      basis initialCode source bank query target)
    (hlive : ProfiledOpenActiveLaneRightWitnessedRuntimeLive A strategy hwin
      basis initialCode target.2 target.1) :
    profiledOpenActiveLaneRightWitnessedLocalNextReceipt A strategy hwin basis
        initialCode Compatible observation = target.1.1.1 := by
  exact shapeFreeFiniteLocalNextReceipt_eq
    (ProfiledOpenActiveLaneRightWitnessedReceiptPossible A strategy hwin basis
      initialCode Compatible) hfunctional
    ⟨source, bank, query, target, hcompatible, hgood, hlive, rfl⟩

/-- Process-two specification. -/
theorem profiledOpenActiveLaneLeftWitnessedLocalNextReceipt_eq_target
    {RightControl : Type rc} {LeftControl : Type lc}
    (Compatible : ProfiledOpenActiveLaneLeftWitnessedLocalCompatibility A
      initialCode RightControl LeftControl)
    (hfunctional :
      ProfiledOpenActiveLaneLeftWitnessedReceiptFunctional A strategy hwin
        basis initialCode Compatible)
    {observation : ProfiledOpenActiveLaneLeftLocalReceiptObservation A initialCode
      RightControl LeftControl}
    {source target : RecurrenceCandidate A initialCode}
    {bank : RecurrenceBank A initialCode}
    {query : RecurrenceQuery A initialCode}
    (hcompatible : Compatible observation source bank query target)
    (hgood : ProfiledOpenActiveLaneWitnessedRecurrenceGood A strategy hwin
      basis initialCode source bank query target)
    (hlive : ProfiledOpenActiveLaneLeftWitnessedRuntimeLive A strategy hwin
      basis initialCode target.2 target.1) :
    profiledOpenActiveLaneLeftWitnessedLocalNextReceipt A strategy hwin basis
        initialCode Compatible observation = target.1.1.2 := by
  exact shapeFreeFiniteLocalNextReceipt_eq
    (ProfiledOpenActiveLaneLeftWitnessedReceiptPossible A strategy hwin basis
      initialCode Compatible) hfunctional
    ⟨source, bank, query, target, hcompatible, hgood, hlive, rfl⟩

/-- The extracted process-one receipt is immediately accepted by the
previous witnessed pairwise coherence theorem. -/
theorem profiledOpenActiveLaneRightWitnessedLocalReceiptSuccessorLaw_next
    {RightControl : Type rc} {LeftControl : Type lc}
    (Compatible : ProfiledOpenActiveLaneRightWitnessedLocalCompatibility A
      initialCode RightControl LeftControl)
    (observation : ProfiledOpenActiveLaneRightLocalReceiptObservation A initialCode
      RightControl LeftControl)
    (current : Finset (RecurrenceCandidate A initialCode))
    (bank : RecurrenceBank A initialCode)
    (query : RecurrenceQuery A initialCode) :
    ProfiledOpenActiveLaneRightWitnessedLocalReceiptSuccessorLaw A strategy
      hwin basis initialCode current bank query
      (profiledOpenActiveLaneRightObservableReceiptKeep A initialCode
        (profiledOpenActiveLaneRightWitnessedLocalNextReceipt A strategy hwin
          basis initialCode Compatible observation)) :=
  profiledOpenActiveLaneRightWitnessedLocalReceiptSuccessorLaw_receipt A
    strategy hwin basis initialCode current bank query _

/-- Process-two connection to the witnessed pairwise coherence theorem. -/
theorem profiledOpenActiveLaneLeftWitnessedLocalReceiptSuccessorLaw_next
    {RightControl : Type rc} {LeftControl : Type lc}
    (Compatible : ProfiledOpenActiveLaneLeftWitnessedLocalCompatibility A
      initialCode RightControl LeftControl)
    (observation : ProfiledOpenActiveLaneLeftLocalReceiptObservation A initialCode
      RightControl LeftControl)
    (current : Finset (RecurrenceCandidate A initialCode))
    (bank : RecurrenceBank A initialCode)
    (query : RecurrenceQuery A initialCode) :
    ProfiledOpenActiveLaneLeftWitnessedLocalReceiptSuccessorLaw A strategy
      hwin basis initialCode current bank query
      (profiledOpenActiveLaneLeftObservableReceiptKeep A initialCode
        (profiledOpenActiveLaneLeftWitnessedLocalNextReceipt A strategy hwin
          basis initialCode Compatible observation)) :=
  profiledOpenActiveLaneLeftWitnessedLocalReceiptSuccessorLaw_receipt A
    strategy hwin basis initialCode current bank query _

end

end DetParityAutomaton

end DistributedSynthesis
