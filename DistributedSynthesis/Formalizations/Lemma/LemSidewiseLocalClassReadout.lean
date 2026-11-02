/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemSidewiseRelationalCandidateCommonMove

/-!
# The local readout boundary for a sidewise controller bank

`SidewiseCandidateValid` is a centralized proof about a hidden candidate: it
indexes the public bank by the class stored in that candidate.  A distributed
process cannot perform that lookup unless its own finite local summary
determines the same class.  This file states that missing runtime obligation
without adding a selected candidate, orientation, lane, or strict-leader bit.

There are exactly two safe implementations.

* The locally possible live candidates are class-homogeneous.  Equivalently,
  there is a class readout from the process's finite summary.
* Even if the classes differ, all corresponding bank components factor to one
  locally equivalent controller value.  The caller chooses the equivalence
  strong enough to preserve the complete local controller behavior, not just
  its first output.

The negative witness theorems make the boundary fail fast: two candidates
possible at the same local summary with different classes refute class
readout, and unequal bank components refute equality-based whole-bank
consumption.
-/

namespace DistributedSynthesis

universe oc tc f d om tm so st

private abbrev SidewiseCandidate
    (OneClass : Type oc) (TwoClass : Type tc) (Family : Type f)
    (Descriptor : Type d) :=
  RelationalFamilyCandidate
    (SidewiseTaggedFamily OneClass TwoClass Family) Descriptor

/-! ## One-process class homogeneity and readout -/

/-- At one process-one summary, all locally possible live candidates carry
the same process-one class. -/
def SidewiseOneClassHomogeneousAt
    {OneClass : Type oc} {TwoClass : Type tc} {Family : Type f}
    {Descriptor : Type d} {SummaryOne : Type so}
    (Live : Descriptor → Family → Prop)
    (PossibleOne : SummaryOne →
      SidewiseCandidate OneClass TwoClass Family Descriptor → Prop)
    (summary : SummaryOne) : Prop :=
  ∀ left right,
    PossibleOne summary left → Live left.2 left.1.2 →
      PossibleOne summary right → Live right.2 right.1.2 →
        left.1.1.1 = right.1.1.1

/-- Process-two mirror. -/
def SidewiseTwoClassHomogeneousAt
    {OneClass : Type oc} {TwoClass : Type tc} {Family : Type f}
    {Descriptor : Type d} {SummaryTwo : Type st}
    (Live : Descriptor → Family → Prop)
    (PossibleTwo : SummaryTwo →
      SidewiseCandidate OneClass TwoClass Family Descriptor → Prop)
    (summary : SummaryTwo) : Prop :=
  ∀ left right,
    PossibleTwo summary left → Live left.2 left.1.2 →
      PossibleTwo summary right → Live right.2 right.1.2 →
        left.1.1.2 = right.1.1.2

/-- A process-one class readout is correct when it agrees with every live
candidate possible at the summary from which it is computed. -/
def SidewiseOneClassReadoutCorrect
    {OneClass : Type oc} {TwoClass : Type tc} {Family : Type f}
    {Descriptor : Type d} {SummaryOne : Type so}
    (Live : Descriptor → Family → Prop)
    (PossibleOne : SummaryOne →
      SidewiseCandidate OneClass TwoClass Family Descriptor → Prop)
    (readOne : SummaryOne → OneClass) : Prop :=
  ∀ summary candidate,
    PossibleOne summary candidate → Live candidate.2 candidate.1.2 →
      candidate.1.1.1 = readOne summary

/-- Process-two readout correctness. -/
def SidewiseTwoClassReadoutCorrect
    {OneClass : Type oc} {TwoClass : Type tc} {Family : Type f}
    {Descriptor : Type d} {SummaryTwo : Type st}
    (Live : Descriptor → Family → Prop)
    (PossibleTwo : SummaryTwo →
      SidewiseCandidate OneClass TwoClass Family Descriptor → Prop)
    (readTwo : SummaryTwo → TwoClass) : Prop :=
  ∀ summary candidate,
    PossibleTwo summary candidate → Live candidate.2 candidate.1.2 →
      candidate.1.1.2 = readTwo summary

/-- With a harmless default for summaries having no live candidate, local
class homogeneity is exactly existence of a process-one readout. -/
theorem exists_sidewiseOneClassReadout_iff
    {OneClass : Type oc} {TwoClass : Type tc} {Family : Type f}
    {Descriptor : Type d} {SummaryOne : Type so} [Inhabited OneClass]
    (Live : Descriptor → Family → Prop)
    (PossibleOne : SummaryOne →
      SidewiseCandidate OneClass TwoClass Family Descriptor → Prop) :
    (∃ readOne : SummaryOne → OneClass,
        SidewiseOneClassReadoutCorrect Live PossibleOne readOne) ↔
      ∀ summary, SidewiseOneClassHomogeneousAt Live PossibleOne summary := by
  constructor
  · rintro ⟨readOne, hread⟩ summary left right hleft hleftLive hright
      hrightLive
    exact (hread summary left hleft hleftLive).trans
      (hread summary right hright hrightLive).symm
  · intro hhomogeneous
    classical
    have hexists : ∀ summary : SummaryOne, ∃ oneClass : OneClass,
        ∀ candidate, PossibleOne summary candidate →
          Live candidate.2 candidate.1.2 →
            candidate.1.1.1 = oneClass := by
      intro summary
      letI : Decidable (∃ candidate,
          PossibleOne summary candidate ∧
            Live candidate.2 candidate.1.2) :=
        Classical.propDecidable _
      by_cases hactive : ∃ candidate,
          PossibleOne summary candidate ∧
            Live candidate.2 candidate.1.2
      · let pivot := Classical.choose hactive
        refine ⟨pivot.1.1.1, ?_⟩
        intro candidate hpossible hlive
        exact hhomogeneous summary candidate pivot hpossible hlive
          (Classical.choose_spec hactive).1
          (Classical.choose_spec hactive).2
      · refine ⟨default, ?_⟩
        intro candidate hpossible hlive
        exact False.elim (hactive ⟨candidate, hpossible, hlive⟩)
    let readOne : SummaryOne → OneClass := fun summary ↦
      Classical.choose (hexists summary)
    exact ⟨readOne, fun summary candidate hpossible hlive ↦
      Classical.choose_spec (hexists summary) candidate hpossible hlive⟩

/-- Process-two form. -/
theorem exists_sidewiseTwoClassReadout_iff
    {OneClass : Type oc} {TwoClass : Type tc} {Family : Type f}
    {Descriptor : Type d} {SummaryTwo : Type st} [Inhabited TwoClass]
    (Live : Descriptor → Family → Prop)
    (PossibleTwo : SummaryTwo →
      SidewiseCandidate OneClass TwoClass Family Descriptor → Prop) :
    (∃ readTwo : SummaryTwo → TwoClass,
        SidewiseTwoClassReadoutCorrect Live PossibleTwo readTwo) ↔
      ∀ summary, SidewiseTwoClassHomogeneousAt Live PossibleTwo summary := by
  constructor
  · rintro ⟨readTwo, hread⟩ summary left right hleft hleftLive hright
      hrightLive
    exact (hread summary left hleft hleftLive).trans
      (hread summary right hright hrightLive).symm
  · intro hhomogeneous
    classical
    have hexists : ∀ summary : SummaryTwo, ∃ twoClass : TwoClass,
        ∀ candidate, PossibleTwo summary candidate →
          Live candidate.2 candidate.1.2 →
            candidate.1.1.2 = twoClass := by
      intro summary
      letI : Decidable (∃ candidate,
          PossibleTwo summary candidate ∧
            Live candidate.2 candidate.1.2) :=
        Classical.propDecidable _
      by_cases hactive : ∃ candidate,
          PossibleTwo summary candidate ∧
            Live candidate.2 candidate.1.2
      · let pivot := Classical.choose hactive
        refine ⟨pivot.1.1.2, ?_⟩
        intro candidate hpossible hlive
        exact hhomogeneous summary candidate pivot hpossible hlive
          (Classical.choose_spec hactive).1
          (Classical.choose_spec hactive).2
      · refine ⟨default, ?_⟩
        intro candidate hpossible hlive
        exact False.elim (hactive ⟨candidate, hpossible, hlive⟩)
    let readTwo : SummaryTwo → TwoClass := fun summary ↦
      Classical.choose (hexists summary)
    exact ⟨readTwo, fun summary candidate hpossible hlive ↦
      Classical.choose_spec (hexists summary) candidate hpossible hlive⟩

/-! ## Reading the component justified by centralized candidate validity -/

/-- Once the own-side class is locally readable, the process-one component
selected from the bank is valid for the actual hidden candidate. -/
theorem SidewiseCandidateValid.one_of_readout
    {OneClass : Type oc} {TwoClass : Type tc} {Family : Type f}
    {Descriptor : Type d} {OneMove : Type om} {TwoMove : Type tm}
    {SummaryOne : Type so}
    (OneValid : Descriptor → Family → OneMove → Prop)
    (TwoValid : Descriptor → Family → TwoMove → Prop)
    (Live : Descriptor → Family → Prop)
    (PossibleOne : SummaryOne →
      SidewiseCandidate OneClass TwoClass Family Descriptor → Prop)
    (readOne : SummaryOne → OneClass)
    (hread : SidewiseOneClassReadoutCorrect Live PossibleOne readOne)
    (summary : SummaryOne)
    (candidate : SidewiseCandidate OneClass TwoClass Family Descriptor)
    (bank : SidewiseMoveBank OneClass TwoClass OneMove TwoMove)
    (hvalid : SidewiseCandidateValid OneValid TwoValid candidate.2 candidate.1
      bank)
    (hpossible : PossibleOne summary candidate)
    (hlive : Live candidate.2 candidate.1.2) :
    OneValid candidate.2 candidate.1.2 (bank.1 (readOne summary)) := by
  rw [← hread summary candidate hpossible hlive]
  exact hvalid.1

/-- Process-two mirror. -/
theorem SidewiseCandidateValid.two_of_readout
    {OneClass : Type oc} {TwoClass : Type tc} {Family : Type f}
    {Descriptor : Type d} {OneMove : Type om} {TwoMove : Type tm}
    {SummaryTwo : Type st}
    (OneValid : Descriptor → Family → OneMove → Prop)
    (TwoValid : Descriptor → Family → TwoMove → Prop)
    (Live : Descriptor → Family → Prop)
    (PossibleTwo : SummaryTwo →
      SidewiseCandidate OneClass TwoClass Family Descriptor → Prop)
    (readTwo : SummaryTwo → TwoClass)
    (hread : SidewiseTwoClassReadoutCorrect Live PossibleTwo readTwo)
    (summary : SummaryTwo)
    (candidate : SidewiseCandidate OneClass TwoClass Family Descriptor)
    (bank : SidewiseMoveBank OneClass TwoClass OneMove TwoMove)
    (hvalid : SidewiseCandidateValid OneValid TwoValid candidate.2 candidate.1
      bank)
    (hpossible : PossibleTwo summary candidate)
    (hlive : Live candidate.2 candidate.1.2) :
    TwoValid candidate.2 candidate.1.2 (bank.2 (readTwo summary)) := by
  rw [← hread summary candidate hpossible hlive]
  exact hvalid.2

/-! ## The whole-bank factorization alternative -/

/-- A process-one bank is locally consumable modulo `EquivalentOne` when one
controller value computed from the local summary is equivalent to the hidden
candidate-indexed component for every locally possible live candidate. -/
def SidewiseOneBankLocallyConsumable
    {OneClass : Type oc} {TwoClass : Type tc} {Family : Type f}
    {Descriptor : Type d} {OneMove : Type om} {TwoMove : Type tm}
    {SummaryOne : Type so}
    (Live : Descriptor → Family → Prop)
    (PossibleOne : SummaryOne →
      SidewiseCandidate OneClass TwoClass Family Descriptor → Prop)
    (EquivalentOne : OneMove → OneMove → Prop)
    (bank : SidewiseMoveBank OneClass TwoClass OneMove TwoMove) : Prop :=
  ∃ consumeOne : SummaryOne → OneMove,
    ∀ summary candidate,
      PossibleOne summary candidate → Live candidate.2 candidate.1.2 →
        EquivalentOne (bank.1 candidate.1.1.1) (consumeOne summary)

/-- Process-two whole-bank consumption. -/
def SidewiseTwoBankLocallyConsumable
    {OneClass : Type oc} {TwoClass : Type tc} {Family : Type f}
    {Descriptor : Type d} {OneMove : Type om} {TwoMove : Type tm}
    {SummaryTwo : Type st}
    (Live : Descriptor → Family → Prop)
    (PossibleTwo : SummaryTwo →
      SidewiseCandidate OneClass TwoClass Family Descriptor → Prop)
    (EquivalentTwo : TwoMove → TwoMove → Prop)
    (bank : SidewiseMoveBank OneClass TwoClass OneMove TwoMove) : Prop :=
  ∃ consumeTwo : SummaryTwo → TwoMove,
    ∀ summary candidate,
      PossibleTwo summary candidate → Live candidate.2 candidate.1.2 →
        EquivalentTwo (bank.2 candidate.1.1.2) (consumeTwo summary)

/-! ## Exact behavioral criterion for consuming a hidden bank index -/

/-- At one process-one summary, every bank component justified by a locally
possible live candidate has the same behavior, modulo `EquivalentOne`.

Unlike class homogeneity, this permits distinct hidden class indices.  It is
the correct criterion at a one-way/`both` ambiguity: the process need not
recover the hidden graph bit when both possible entries implement equivalent
local behavior. -/
def SidewiseOneBankBehaviorHomogeneousAt
    {OneClass : Type oc} {TwoClass : Type tc} {Family : Type f}
    {Descriptor : Type d} {OneMove : Type om} {TwoMove : Type tm}
    {SummaryOne : Type so}
    (Live : Descriptor → Family → Prop)
    (PossibleOne : SummaryOne →
      SidewiseCandidate OneClass TwoClass Family Descriptor → Prop)
    (EquivalentOne : OneMove → OneMove → Prop)
    (bank : SidewiseMoveBank OneClass TwoClass OneMove TwoMove)
    (summary : SummaryOne) : Prop :=
  ∀ left right,
    PossibleOne summary left → Live left.2 left.1.2 →
      PossibleOne summary right → Live right.2 right.1.2 →
        EquivalentOne (bank.1 left.1.1.1) (bank.1 right.1.1.1)

/-- Process-two mirror. -/
def SidewiseTwoBankBehaviorHomogeneousAt
    {OneClass : Type oc} {TwoClass : Type tc} {Family : Type f}
    {Descriptor : Type d} {OneMove : Type om} {TwoMove : Type tm}
    {SummaryTwo : Type st}
    (Live : Descriptor → Family → Prop)
    (PossibleTwo : SummaryTwo →
      SidewiseCandidate OneClass TwoClass Family Descriptor → Prop)
    (EquivalentTwo : TwoMove → TwoMove → Prop)
    (bank : SidewiseMoveBank OneClass TwoClass OneMove TwoMove)
    (summary : SummaryTwo) : Prop :=
  ∀ left right,
    PossibleTwo summary left → Live left.2 left.1.2 →
      PossibleTwo summary right → Live right.2 right.1.2 →
        EquivalentTwo (bank.2 left.1.1.2) (bank.2 right.1.1.2)

/-- A hidden process-one bank index can be erased exactly when the entries
that may occur at each local summary are behaviorally homogeneous.  The
consumer chooses an arbitrary represented entry; summaries with no live
candidate use the harmless default.

Only symmetry and transitivity of behavioral equivalence are needed in the
forward direction.  No class readout, orientation, lane, or leader signal is
constructed. -/
theorem sidewiseOneBankLocallyConsumable_iff_behaviorHomogeneous
    {OneClass : Type oc} {TwoClass : Type tc} {Family : Type f}
    {Descriptor : Type d} {OneMove : Type om} {TwoMove : Type tm}
    {SummaryOne : Type so} [Inhabited OneMove]
    (Live : Descriptor → Family → Prop)
    (PossibleOne : SummaryOne →
      SidewiseCandidate OneClass TwoClass Family Descriptor → Prop)
    (EquivalentOne : OneMove → OneMove → Prop)
    (hsymm : Symmetric EquivalentOne)
    (htrans : IsTrans _ EquivalentOne)
    (bank : SidewiseMoveBank OneClass TwoClass OneMove TwoMove) :
    SidewiseOneBankLocallyConsumable Live PossibleOne EquivalentOne bank ↔
      ∀ summary,
        SidewiseOneBankBehaviorHomogeneousAt Live PossibleOne EquivalentOne
          bank summary := by
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
          PossibleOne summary candidate → Live candidate.2 candidate.1.2 →
            EquivalentOne (bank.1 candidate.1.1.1) move := by
      intro summary
      letI : Decidable (∃ candidate,
          PossibleOne summary candidate ∧
            Live candidate.2 candidate.1.2) :=
        Classical.propDecidable _
      by_cases hactive : ∃ candidate,
          PossibleOne summary candidate ∧
            Live candidate.2 candidate.1.2
      · let pivot := Classical.choose hactive
        refine ⟨bank.1 pivot.1.1.1, ?_⟩
        intro candidate hpossible hlive
        exact hhomogeneous summary candidate pivot hpossible hlive
          (Classical.choose_spec hactive).1
          (Classical.choose_spec hactive).2
      · refine ⟨default, ?_⟩
        intro candidate hpossible hlive
        exact False.elim (hactive ⟨candidate, hpossible, hlive⟩)
    let consumeOne : SummaryOne → OneMove := fun summary ↦
      Classical.choose (hexists summary)
    exact ⟨consumeOne, fun summary candidate hpossible hlive ↦
      Classical.choose_spec (hexists summary) candidate hpossible hlive⟩

/-- Process-two behavioral-consumption criterion. -/
theorem sidewiseTwoBankLocallyConsumable_iff_behaviorHomogeneous
    {OneClass : Type oc} {TwoClass : Type tc} {Family : Type f}
    {Descriptor : Type d} {OneMove : Type om} {TwoMove : Type tm}
    {SummaryTwo : Type st} [Inhabited TwoMove]
    (Live : Descriptor → Family → Prop)
    (PossibleTwo : SummaryTwo →
      SidewiseCandidate OneClass TwoClass Family Descriptor → Prop)
    (EquivalentTwo : TwoMove → TwoMove → Prop)
    (hsymm : Symmetric EquivalentTwo)
    (htrans : IsTrans _ EquivalentTwo)
    (bank : SidewiseMoveBank OneClass TwoClass OneMove TwoMove) :
    SidewiseTwoBankLocallyConsumable Live PossibleTwo EquivalentTwo bank ↔
      ∀ summary,
        SidewiseTwoBankBehaviorHomogeneousAt Live PossibleTwo EquivalentTwo
          bank summary := by
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
          PossibleTwo summary candidate → Live candidate.2 candidate.1.2 →
            EquivalentTwo (bank.2 candidate.1.1.2) move := by
      intro summary
      letI : Decidable (∃ candidate,
          PossibleTwo summary candidate ∧
            Live candidate.2 candidate.1.2) :=
        Classical.propDecidable _
      by_cases hactive : ∃ candidate,
          PossibleTwo summary candidate ∧
            Live candidate.2 candidate.1.2
      · let pivot := Classical.choose hactive
        refine ⟨bank.2 pivot.1.1.2, ?_⟩
        intro candidate hpossible hlive
        exact hhomogeneous summary candidate pivot hpossible hlive
          (Classical.choose_spec hactive).1
          (Classical.choose_spec hactive).2
      · refine ⟨default, ?_⟩
        intro candidate hpossible hlive
        exact False.elim (hactive ⟨candidate, hpossible, hlive⟩)
    let consumeTwo : SummaryTwo → TwoMove := fun summary ↦
      Classical.choose (hexists summary)
    exact ⟨consumeTwo, fun summary candidate hpossible hlive ↦
      Classical.choose_spec (hexists summary) candidate hpossible hlive⟩

/-- Behavioral whole-bank consumption is enough to execute process one's
component whenever validity is preserved by the chosen behavioral
equivalence.  The returned function reads only the process-local summary;
the hidden candidate appears solely in its correctness proof. -/
theorem SidewiseCandidateValid.one_of_locallyConsumable
    {OneClass : Type oc} {TwoClass : Type tc} {Family : Type f}
    {Descriptor : Type d} {OneMove : Type om} {TwoMove : Type tm}
    {SummaryOne : Type so}
    (OneValid : Descriptor → Family → OneMove → Prop)
    (TwoValid : Descriptor → Family → TwoMove → Prop)
    (Live : Descriptor → Family → Prop)
    (PossibleOne : SummaryOne →
      SidewiseCandidate OneClass TwoClass Family Descriptor → Prop)
    (EquivalentOne : OneMove → OneMove → Prop)
    (bank : SidewiseMoveBank OneClass TwoClass OneMove TwoMove)
    (hconsume : SidewiseOneBankLocallyConsumable Live PossibleOne
      EquivalentOne bank)
    (hvalidRespect : ∀ descriptor family source target,
      OneValid descriptor family source → EquivalentOne source target →
        OneValid descriptor family target) :
    ∃ consumeOne : SummaryOne → OneMove,
      ∀ summary candidate,
        PossibleOne summary candidate → Live candidate.2 candidate.1.2 →
          SidewiseCandidateValid OneValid TwoValid candidate.2 candidate.1
              bank →
            OneValid candidate.2 candidate.1.2 (consumeOne summary) := by
  rcases hconsume with ⟨consumeOne, hconsume⟩
  refine ⟨consumeOne, ?_⟩
  intro summary candidate hpossible hlive hvalid
  exact hvalidRespect candidate.2 candidate.1.2
    (bank.1 candidate.1.1.1) (consumeOne summary) hvalid.1
    (hconsume summary candidate hpossible hlive)

/-- Process-two mirror of behavioral local consumption. -/
theorem SidewiseCandidateValid.two_of_locallyConsumable
    {OneClass : Type oc} {TwoClass : Type tc} {Family : Type f}
    {Descriptor : Type d} {OneMove : Type om} {TwoMove : Type tm}
    {SummaryTwo : Type st}
    (OneValid : Descriptor → Family → OneMove → Prop)
    (TwoValid : Descriptor → Family → TwoMove → Prop)
    (Live : Descriptor → Family → Prop)
    (PossibleTwo : SummaryTwo →
      SidewiseCandidate OneClass TwoClass Family Descriptor → Prop)
    (EquivalentTwo : TwoMove → TwoMove → Prop)
    (bank : SidewiseMoveBank OneClass TwoClass OneMove TwoMove)
    (hconsume : SidewiseTwoBankLocallyConsumable Live PossibleTwo
      EquivalentTwo bank)
    (hvalidRespect : ∀ descriptor family source target,
      TwoValid descriptor family source → EquivalentTwo source target →
        TwoValid descriptor family target) :
    ∃ consumeTwo : SummaryTwo → TwoMove,
      ∀ summary candidate,
        PossibleTwo summary candidate → Live candidate.2 candidate.1.2 →
          SidewiseCandidateValid OneValid TwoValid candidate.2 candidate.1
              bank →
            TwoValid candidate.2 candidate.1.2 (consumeTwo summary) := by
  rcases hconsume with ⟨consumeTwo, hconsume⟩
  refine ⟨consumeTwo, ?_⟩
  intro summary candidate hpossible hlive hvalid
  exact hvalidRespect candidate.2 candidate.1.2
    (bank.2 candidate.1.1.2) (consumeTwo summary) hvalid.2
    (hconsume summary candidate hpossible hlive)

/-- A correct class readout makes the whole bank locally consumable for every
reflexive controller equivalence. -/
theorem sidewiseOneBankLocallyConsumable_of_readout
    {OneClass : Type oc} {TwoClass : Type tc} {Family : Type f}
    {Descriptor : Type d} {OneMove : Type om} {TwoMove : Type tm}
    {SummaryOne : Type so}
    (Live : Descriptor → Family → Prop)
    (PossibleOne : SummaryOne →
      SidewiseCandidate OneClass TwoClass Family Descriptor → Prop)
    (EquivalentOne : OneMove → OneMove → Prop)
    (hrefl : ∀ move, EquivalentOne move move)
    (bank : SidewiseMoveBank OneClass TwoClass OneMove TwoMove)
    (readOne : SummaryOne → OneClass)
    (hread : SidewiseOneClassReadoutCorrect Live PossibleOne readOne) :
    SidewiseOneBankLocallyConsumable Live PossibleOne EquivalentOne bank := by
  refine ⟨fun summary ↦ bank.1 (readOne summary), ?_⟩
  intro summary candidate hpossible hlive
  rw [hread summary candidate hpossible hlive]
  exact hrefl _

/-- Process-two mirror. -/
theorem sidewiseTwoBankLocallyConsumable_of_readout
    {OneClass : Type oc} {TwoClass : Type tc} {Family : Type f}
    {Descriptor : Type d} {OneMove : Type om} {TwoMove : Type tm}
    {SummaryTwo : Type st}
    (Live : Descriptor → Family → Prop)
    (PossibleTwo : SummaryTwo →
      SidewiseCandidate OneClass TwoClass Family Descriptor → Prop)
    (EquivalentTwo : TwoMove → TwoMove → Prop)
    (hrefl : ∀ move, EquivalentTwo move move)
    (bank : SidewiseMoveBank OneClass TwoClass OneMove TwoMove)
    (readTwo : SummaryTwo → TwoClass)
    (hread : SidewiseTwoClassReadoutCorrect Live PossibleTwo readTwo) :
    SidewiseTwoBankLocallyConsumable Live PossibleTwo EquivalentTwo bank := by
  refine ⟨fun summary ↦ bank.2 (readTwo summary), ?_⟩
  intro summary candidate hpossible hlive
  rw [hread summary candidate hpossible hlive]
  exact hrefl _

/-! ## Fail-fast witnesses -/

theorem not_exists_sidewiseOneClassReadout_of_collision
    {OneClass : Type oc} {TwoClass : Type tc} {Family : Type f}
    {Descriptor : Type d} {SummaryOne : Type so}
    (Live : Descriptor → Family → Prop)
    (PossibleOne : SummaryOne →
      SidewiseCandidate OneClass TwoClass Family Descriptor → Prop)
    (summary : SummaryOne)
    (left right : SidewiseCandidate OneClass TwoClass Family Descriptor)
    (hleft : PossibleOne summary left) (hleftLive : Live left.2 left.1.2)
    (hright : PossibleOne summary right) (hrightLive : Live right.2 right.1.2)
    (hne : left.1.1.1 ≠ right.1.1.1) :
    ¬ ∃ readOne : SummaryOne → OneClass,
      SidewiseOneClassReadoutCorrect Live PossibleOne readOne := by
  rintro ⟨readOne, hread⟩
  exact hne ((hread summary left hleft hleftLive).trans
    (hread summary right hright hrightLive).symm)

theorem not_exists_sidewiseTwoClassReadout_of_collision
    {OneClass : Type oc} {TwoClass : Type tc} {Family : Type f}
    {Descriptor : Type d} {SummaryTwo : Type st}
    (Live : Descriptor → Family → Prop)
    (PossibleTwo : SummaryTwo →
      SidewiseCandidate OneClass TwoClass Family Descriptor → Prop)
    (summary : SummaryTwo)
    (left right : SidewiseCandidate OneClass TwoClass Family Descriptor)
    (hleft : PossibleTwo summary left) (hleftLive : Live left.2 left.1.2)
    (hright : PossibleTwo summary right) (hrightLive : Live right.2 right.1.2)
    (hne : left.1.1.2 ≠ right.1.1.2) :
    ¬ ∃ readTwo : SummaryTwo → TwoClass,
      SidewiseTwoClassReadoutCorrect Live PossibleTwo readTwo := by
  rintro ⟨readTwo, hread⟩
  exact hne ((hread summary left hleft hleftLive).trans
    (hread summary right hright hrightLive).symm)

/-- If two locally possible candidates ask for literally different bank
components, the whole bank cannot be consumed as one equality-based local
controller without a class readout. -/
theorem not_sidewiseOneBankLocallyConsumable_eq_of_collision
    {OneClass : Type oc} {TwoClass : Type tc} {Family : Type f}
    {Descriptor : Type d} {OneMove : Type om} {TwoMove : Type tm}
    {SummaryOne : Type so}
    (Live : Descriptor → Family → Prop)
    (PossibleOne : SummaryOne →
      SidewiseCandidate OneClass TwoClass Family Descriptor → Prop)
    (bank : SidewiseMoveBank OneClass TwoClass OneMove TwoMove)
    (summary : SummaryOne)
    (left right : SidewiseCandidate OneClass TwoClass Family Descriptor)
    (hleft : PossibleOne summary left) (hleftLive : Live left.2 left.1.2)
    (hright : PossibleOne summary right) (hrightLive : Live right.2 right.1.2)
    (hne : bank.1 left.1.1.1 ≠ bank.1 right.1.1.1) :
    ¬ SidewiseOneBankLocallyConsumable Live PossibleOne (fun x y ↦ x = y)
      bank := by
  rintro ⟨consumeOne, hconsume⟩
  exact hne ((hconsume summary left hleft hleftLive).trans
    (hconsume summary right hright hrightLive).symm)

/-- Process-two fail-fast mirror. -/
theorem not_sidewiseTwoBankLocallyConsumable_eq_of_collision
    {OneClass : Type oc} {TwoClass : Type tc} {Family : Type f}
    {Descriptor : Type d} {OneMove : Type om} {TwoMove : Type tm}
    {SummaryTwo : Type st}
    (Live : Descriptor → Family → Prop)
    (PossibleTwo : SummaryTwo →
      SidewiseCandidate OneClass TwoClass Family Descriptor → Prop)
    (bank : SidewiseMoveBank OneClass TwoClass OneMove TwoMove)
    (summary : SummaryTwo)
    (left right : SidewiseCandidate OneClass TwoClass Family Descriptor)
    (hleft : PossibleTwo summary left) (hleftLive : Live left.2 left.1.2)
    (hright : PossibleTwo summary right) (hrightLive : Live right.2 right.1.2)
    (hne : bank.2 left.1.1.2 ≠ bank.2 right.1.1.2) :
    ¬ SidewiseTwoBankLocallyConsumable Live PossibleTwo (fun x y ↦ x = y)
      bank := by
  rintro ⟨consumeTwo, hconsume⟩
  exact hne ((hconsume summary left hleft hleftLive).trans
    (hconsume summary right hright hrightLive).symm)

end DistributedSynthesis
