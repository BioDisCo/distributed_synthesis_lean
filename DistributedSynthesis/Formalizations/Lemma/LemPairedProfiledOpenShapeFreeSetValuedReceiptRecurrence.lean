/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenShapeFreeLocalReceiptRecurrenceGate

/-!
# Set-valued local receipt recurrence

The forward exact-view facts are strong enough once their premise is
available: equal literal active views imply the same projected finite class.
An honest finite receive tuple, however, contains only the two finite local
summaries and the two current inputs.  Equality of two projected descriptor
images does not reflect to equality of the underlying exact views, and two
marginal receipt coordinates do not supply one shared paired semantic source.

Consequently this file does not assert uniqueness of the next receipt.  It
instantiates the strongest graph-blind compatibility projection already
supported by the set-valued receive construction:

* a blind step retains the current receipt;
* a receive advances every candidate in the delivered partner candidate set;
* both source classes must belong to the two carried receipt sets;
* the bank and pointed query are read from the finite receive tuple.

The next local receipt is the finite set of all projected classes of
witnessed-live exact targets.  Every actual compatible target is covered.
One bank is locally consumable from this set precisely when all values it
selects on the set are behavior-equivalent.  A named two-receipt collision is
the exact refuter.  No representative, hidden bit, graph, active side,
orientation, or strict leader is selected.
-/

namespace DistributedSynthesis

universe i u v x y s b₁ b₂

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

private abbrev SetReceiptClass :=
  ProfiledOpenActiveLaneSideClass A initialCode

private abbrev SetReceiptCandidate :=
  ProfiledOpenActiveLaneTaggedCandidate A initialCode

private abbrev SetReceiptBank :=
  ProfiledOpenFixedSidewisePinnedBank A initialCode
    (SetReceiptClass A initialCode) (SetReceiptClass A initialCode)

private abbrev SetReceiptRightValue :=
  ProfiledOpenFixedRightPinnedValue A initialCode

private abbrev SetReceiptLeftValue :=
  ProfiledOpenFixedLeftPinnedValue A initialCode

/-! ## The strongest honest finite receive carrier -/

/-- The remaining finite base control paired with the complete finite
candidate set carried by one process. -/
abbrev ProfiledOpenActiveLaneWitnessedReceiptControl (Base : Type b₁) :=
  Base × Finset (SetReceiptCandidate A initialCode)

/-- Process-one iterative local receipt state.  The receipt coordinate is the
whole finite uncertainty set, not a selected hidden member. -/
abbrev ProfiledOpenActiveLaneWitnessedRightReceiptState (Base : Type b₁) :=
  Finset (SetReceiptClass A initialCode) ×
    ProfiledOpenActiveLaneWitnessedReceiptControl A initialCode Base

/-- Process-two local receipt state. -/
abbrev ProfiledOpenActiveLaneWitnessedLeftReceiptState (Base : Type b₂) :=
  Finset (SetReceiptClass A initialCode) ×
    ProfiledOpenActiveLaneWitnessedReceiptControl A initialCode Base

/-- Honest process-one transition observation. -/
abbrev ProfiledOpenActiveLaneWitnessedRightReceiptObservation
    (BaseOne : Type b₁) (BaseTwo : Type b₂) :=
  ShapeFreeFiniteLocalReceiptObservation
    (Finset (SetReceiptClass A initialCode))
    (ProfiledOpenActiveLaneWitnessedReceiptControl A initialCode BaseOne) In₁
    (Finset (SetReceiptClass A initialCode))
    (ProfiledOpenActiveLaneWitnessedReceiptControl A initialCode BaseTwo) In₂

/-- Process-two mirror. -/
abbrev ProfiledOpenActiveLaneWitnessedLeftReceiptObservation
    (BaseOne : Type b₁) (BaseTwo : Type b₂) :=
  ShapeFreeFiniteLocalReceiptObservation
    (Finset (SetReceiptClass A initialCode))
    (ProfiledOpenActiveLaneWitnessedReceiptControl A initialCode BaseTwo) In₂
    (Finset (SetReceiptClass A initialCode))
    (ProfiledOpenActiveLaneWitnessedReceiptControl A initialCode BaseOne) In₁

/-- Proof-only interpretation of one set-valued process-one observation. -/
abbrev ProfiledOpenActiveLaneRightWitnessedSetReceiptLocalCompatibility
    (BaseOne : Type b₁) (BaseTwo : Type b₂) :=
  ProfiledOpenActiveLaneWitnessedRightReceiptObservation A initialCode
      BaseOne BaseTwo →
    SetReceiptCandidate A initialCode →
    SetReceiptBank A initialCode →
    ProfiledOpenFixedSidewiseReachablePointedQuery.{i, u, v, x, y, s,
      max i s u v x y, max i s u v x y} (I := I) A initialCode →
    SetReceiptCandidate A initialCode → Prop

/-- Process-two set-valued compatibility. -/
abbrev ProfiledOpenActiveLaneLeftWitnessedSetReceiptLocalCompatibility
    (BaseOne : Type b₁) (BaseTwo : Type b₂) :=
  ProfiledOpenActiveLaneWitnessedLeftReceiptObservation A initialCode
      BaseOne BaseTwo →
    SetReceiptCandidate A initialCode →
    SetReceiptBank A initialCode →
    ProfiledOpenFixedSidewiseReachablePointedQuery.{i, u, v, x, y, s,
      max i s u v x y, max i s u v x y} (I := I) A initialCode →
    SetReceiptCandidate A initialCode → Prop

/-- The four graph-blind finite readers used at receives.  Their arguments
are exactly the self summary/input and delivered partner summary/input in the
order supplied to a local summary automaton. -/
structure ProfiledOpenActiveLaneWitnessedReceiptReaders
    (BaseOne : Type b₁) (BaseTwo : Type b₂) where
  rightBank :
    ProfiledOpenActiveLaneWitnessedRightReceiptState A initialCode BaseOne →
      In₁ →
      ProfiledOpenActiveLaneWitnessedLeftReceiptState A initialCode BaseTwo →
      In₂ → SetReceiptBank A initialCode
  rightQuery :
    ProfiledOpenActiveLaneWitnessedRightReceiptState A initialCode BaseOne →
      In₁ →
      ProfiledOpenActiveLaneWitnessedLeftReceiptState A initialCode BaseTwo →
      In₂ →
        ProfiledOpenFixedSidewiseReachablePointedQuery.{i, u, v, x, y, s,
          max i s u v x y, max i s u v x y} (I := I) A initialCode
  leftBank :
    ProfiledOpenActiveLaneWitnessedLeftReceiptState A initialCode BaseTwo →
      In₂ →
      ProfiledOpenActiveLaneWitnessedRightReceiptState A initialCode BaseOne →
      In₁ → SetReceiptBank A initialCode
  leftQuery :
    ProfiledOpenActiveLaneWitnessedLeftReceiptState A initialCode BaseTwo →
      In₂ →
      ProfiledOpenActiveLaneWitnessedRightReceiptState A initialCode BaseOne →
      In₁ →
        ProfiledOpenFixedSidewiseReachablePointedQuery.{i, u, v, x, y, s,
          max i s u v x y, max i s u v x y} (I := I) A initialCode

/-! ## Concrete compatibility with the witnessed source-aware edge -/

/-- At a process-one receive, advance the delivered process-two candidate
set.  Both source receipt coordinates must occur in the two finite states in the
receive tuple.  A no-receive transition has no semantic candidate edge and is
handled by retention below. -/
def profiledOpenActiveLaneRightHonestReceiveCompatible
    {BaseOne : Type b₁} {BaseTwo : Type b₂}
    (readers : ProfiledOpenActiveLaneWitnessedReceiptReaders A initialCode
      BaseOne BaseTwo) :
    ProfiledOpenActiveLaneRightWitnessedSetReceiptLocalCompatibility A
      initialCode BaseOne BaseTwo
  | .inl _, _, _, _, _ => False
  | .inr (self, inputSelf, other, inputOther), source, bank, query, _ =>
      source ∈ other.2.2 ∧
        source.1.1.1 ∈ self.1 ∧
        source.1.1.2 ∈ other.1 ∧
        bank = readers.rightBank self inputSelf other inputOther ∧
        query = readers.rightQuery self inputSelf other inputOther

/-- Process-two mirror: its receive advances the delivered process-one
candidate set and checks the same two marginal receipts in global process
order. -/
def profiledOpenActiveLaneLeftHonestReceiveCompatible
    {BaseOne : Type b₁} {BaseTwo : Type b₂}
    (readers : ProfiledOpenActiveLaneWitnessedReceiptReaders A initialCode
      BaseOne BaseTwo) :
    ProfiledOpenActiveLaneLeftWitnessedSetReceiptLocalCompatibility A
      initialCode BaseOne BaseTwo
  | .inl _, _, _, _, _ => False
  | .inr (self, inputSelf, other, inputOther), source, bank, query, _ =>
      source ∈ other.2.2 ∧
        source.1.1.1 ∈ other.1 ∧
        source.1.1.2 ∈ self.1 ∧
        bank = readers.leftBank self inputSelf other inputOther ∧
        query = readers.leftQuery self inputSelf other inputOther

/-! ## Finite sets of every possible next receipt -/

/-- One process-one receipt class is possible after a set-valued local
observation when some compatible witnessed-live exact edge produces it. -/
def ProfiledOpenActiveLaneRightWitnessedSetReceiptPossible
    {BaseOne : Type b₁} {BaseTwo : Type b₂}
    (Compatible : ProfiledOpenActiveLaneRightWitnessedSetReceiptLocalCompatibility
      A initialCode BaseOne BaseTwo)
    (observation : ProfiledOpenActiveLaneWitnessedRightReceiptObservation A
      initialCode BaseOne BaseTwo)
    (receipt : SetReceiptClass A initialCode) : Prop :=
  ∃ source bank query target,
    Compatible observation source bank query target ∧
      ProfiledOpenActiveLaneWitnessedRecurrenceGood A strategy hwin basis
        initialCode source bank query target ∧
      ProfiledOpenActiveLaneRightWitnessedRuntimeLive A strategy hwin basis
        initialCode target.2 target.1 ∧
      target.1.1.1 = receipt

/-- Process-two mirror. -/
def ProfiledOpenActiveLaneLeftWitnessedSetReceiptPossible
    {BaseOne : Type b₁} {BaseTwo : Type b₂}
    (Compatible : ProfiledOpenActiveLaneLeftWitnessedSetReceiptLocalCompatibility
      A initialCode BaseOne BaseTwo)
    (observation : ProfiledOpenActiveLaneWitnessedLeftReceiptObservation A
      initialCode BaseOne BaseTwo)
    (receipt : SetReceiptClass A initialCode) : Prop :=
  ∃ source bank query target,
    Compatible observation source bank query target ∧
      ProfiledOpenActiveLaneWitnessedRecurrenceGood A strategy hwin basis
        initialCode source bank query target ∧
      ProfiledOpenActiveLaneLeftWitnessedRuntimeLive A strategy hwin basis
        initialCode target.2 target.1 ∧
      target.1.1.2 = receipt

/-- Process one retains its receipt on a blind step.  On a receive it stores
all classes of compatible witnessed-live exact targets. -/
noncomputable def profiledOpenActiveLaneRightWitnessedLocalNextReceiptSet
    {BaseOne : Type b₁} {BaseTwo : Type b₂}
    (readers : ProfiledOpenActiveLaneWitnessedReceiptReaders A initialCode
      BaseOne BaseTwo)
    (observation : ProfiledOpenActiveLaneWitnessedRightReceiptObservation A
      initialCode BaseOne BaseTwo) : Finset (SetReceiptClass A initialCode) := by
  classical
  cases observation with
  | inl blind => exact blind.1.1
  | inr receive =>
      exact Finset.univ.filter fun receipt =>
        ProfiledOpenActiveLaneRightWitnessedSetReceiptPossible A strategy hwin
          basis initialCode
          (profiledOpenActiveLaneRightHonestReceiveCompatible A initialCode
            (BaseOne := BaseOne) (BaseTwo := BaseTwo) readers)
          (.inr receive) receipt

/-- Process-two set-valued update. -/
noncomputable def profiledOpenActiveLaneLeftWitnessedLocalNextReceiptSet
    {BaseOne : Type b₁} {BaseTwo : Type b₂}
    (readers : ProfiledOpenActiveLaneWitnessedReceiptReaders A initialCode
      BaseOne BaseTwo)
    (observation : ProfiledOpenActiveLaneWitnessedLeftReceiptObservation A
      initialCode BaseOne BaseTwo) : Finset (SetReceiptClass A initialCode) := by
  classical
  cases observation with
  | inl blind => exact blind.1.1
  | inr receive =>
      exact Finset.univ.filter fun receipt =>
        ProfiledOpenActiveLaneLeftWitnessedSetReceiptPossible A strategy hwin
          basis initialCode
          (profiledOpenActiveLaneLeftHonestReceiveCompatible A initialCode
            (BaseOne := BaseOne) (BaseTwo := BaseTwo) readers)
          (.inr receive) receipt

@[simp] theorem
    profiledOpenActiveLaneRightWitnessedLocalNextReceiptSet_noRecv
    {BaseOne : Type b₁} {BaseTwo : Type b₂}
    (readers : ProfiledOpenActiveLaneWitnessedReceiptReaders A initialCode
      BaseOne BaseTwo)
    (self : ProfiledOpenActiveLaneWitnessedRightReceiptState A initialCode
      BaseOne) (inputSelf : In₁) :
    profiledOpenActiveLaneRightWitnessedLocalNextReceiptSet A strategy hwin
        basis initialCode (BaseOne := BaseOne) (BaseTwo := BaseTwo) readers
        (.inl (self, inputSelf)) =
      self.1 :=
  rfl

@[simp] theorem
    profiledOpenActiveLaneLeftWitnessedLocalNextReceiptSet_noRecv
    {BaseOne : Type b₁} {BaseTwo : Type b₂}
    (readers : ProfiledOpenActiveLaneWitnessedReceiptReaders A initialCode
      BaseOne BaseTwo)
    (self : ProfiledOpenActiveLaneWitnessedLeftReceiptState A initialCode
      BaseTwo) (inputSelf : In₂) :
    profiledOpenActiveLaneLeftWitnessedLocalNextReceiptSet A strategy hwin
        basis initialCode (BaseOne := BaseOne) (BaseTwo := BaseTwo) readers
        (.inl (self, inputSelf)) =
      self.1 :=
  rfl

/-- Every actual compatible witnessed-live process-one target is represented
in the finite next-receipt set.  The actual target is used only in this proof;
it is not an argument of the update. -/
theorem mem_profiledOpenActiveLaneRightWitnessedLocalNextReceiptSet_of_target
    {BaseOne : Type b₁} {BaseTwo : Type b₂}
    (readers : ProfiledOpenActiveLaneWitnessedReceiptReaders A initialCode
      BaseOne BaseTwo)
    {observation : ProfiledOpenActiveLaneWitnessedRightReceiptObservation A
      initialCode BaseOne BaseTwo}
    {source target : SetReceiptCandidate A initialCode}
    {bank : SetReceiptBank A initialCode}
    {query : ProfiledOpenFixedSidewiseReachablePointedQuery.{i, u, v, x, y, s,
      max i s u v x y, max i s u v x y} (I := I) A initialCode}
    (hcompatible :
      profiledOpenActiveLaneRightHonestReceiveCompatible A initialCode readers
        (BaseOne := BaseOne) (BaseTwo := BaseTwo)
        observation source bank query target)
    (hgood : ProfiledOpenActiveLaneWitnessedRecurrenceGood A strategy hwin
      basis initialCode source bank query target)
    (hlive : ProfiledOpenActiveLaneRightWitnessedRuntimeLive A strategy hwin
      basis initialCode target.2 target.1) :
    target.1.1.1 ∈
      profiledOpenActiveLaneRightWitnessedLocalNextReceiptSet A strategy hwin
        basis initialCode (BaseOne := BaseOne) (BaseTwo := BaseTwo) readers
        observation := by
  classical
  cases observation with
  | inl blind =>
      simp [profiledOpenActiveLaneRightHonestReceiveCompatible] at hcompatible
  | inr receive =>
      simp only [profiledOpenActiveLaneRightWitnessedLocalNextReceiptSet,
        Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨source, bank, query, target, hcompatible, hgood, hlive, rfl⟩

/-- Process-two actual-target coverage. -/
theorem mem_profiledOpenActiveLaneLeftWitnessedLocalNextReceiptSet_of_target
    {BaseOne : Type b₁} {BaseTwo : Type b₂}
    (readers : ProfiledOpenActiveLaneWitnessedReceiptReaders A initialCode
      BaseOne BaseTwo)
    {observation : ProfiledOpenActiveLaneWitnessedLeftReceiptObservation A
      initialCode BaseOne BaseTwo}
    {source target : SetReceiptCandidate A initialCode}
    {bank : SetReceiptBank A initialCode}
    {query : ProfiledOpenFixedSidewiseReachablePointedQuery.{i, u, v, x, y, s,
      max i s u v x y, max i s u v x y} (I := I) A initialCode}
    (hcompatible :
      profiledOpenActiveLaneLeftHonestReceiveCompatible A initialCode readers
        (BaseOne := BaseOne) (BaseTwo := BaseTwo)
        observation source bank query target)
    (hgood : ProfiledOpenActiveLaneWitnessedRecurrenceGood A strategy hwin
      basis initialCode source bank query target)
    (hlive : ProfiledOpenActiveLaneLeftWitnessedRuntimeLive A strategy hwin
      basis initialCode target.2 target.1) :
    target.1.1.2 ∈
      profiledOpenActiveLaneLeftWitnessedLocalNextReceiptSet A strategy hwin
        basis initialCode (BaseOne := BaseOne) (BaseTwo := BaseTwo) readers
        observation := by
  classical
  cases observation with
  | inl blind =>
      simp [profiledOpenActiveLaneLeftHonestReceiveCompatible] at hcompatible
  | inr receive =>
      simp only [profiledOpenActiveLaneLeftWitnessedLocalNextReceiptSet,
        Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨source, bank, query, target, hcompatible, hgood, hlive, rfl⟩

/-! ## Exact behavior-uniformity criterion for a receipt set -/

/-- All right values selected by possible receipts have equivalent observable
behavior.  `Equivalent` may forget proof fields and compare only the runtime
behavior actually consumed by process one. -/
def ProfiledOpenActiveLaneRightReceiptSetBehaviorUniform
    (Equivalent : SetReceiptRightValue A initialCode →
      SetReceiptRightValue A initialCode → Prop)
    (bank : SetReceiptBank A initialCode)
    (receipts : Finset (SetReceiptClass A initialCode)) : Prop :=
  ∀ left, left ∈ receipts → ∀ right, right ∈ receipts →
    Equivalent (bank.1 left) (bank.1 right)

/-- Left behavior-uniformity. -/
def ProfiledOpenActiveLaneLeftReceiptSetBehaviorUniform
    (Equivalent : SetReceiptLeftValue A initialCode →
      SetReceiptLeftValue A initialCode → Prop)
    (bank : SetReceiptBank A initialCode)
    (receipts : Finset (SetReceiptClass A initialCode)) : Prop :=
  ∀ left, left ∈ receipts → ∀ right, right ∈ receipts →
    Equivalent (bank.2 left) (bank.2 right)

/-- A pair of possible receipts that select behaviorally distinct process-one
values. -/
def ProfiledOpenActiveLaneRightReceiptSetBehaviorCollision
    (Equivalent : SetReceiptRightValue A initialCode →
      SetReceiptRightValue A initialCode → Prop)
    (bank : SetReceiptBank A initialCode)
    (receipts : Finset (SetReceiptClass A initialCode)) : Prop :=
  ∃ left ∈ receipts, ∃ right ∈ receipts,
    ¬ Equivalent (bank.1 left) (bank.1 right)

/-- Process-two behavior collision. -/
def ProfiledOpenActiveLaneLeftReceiptSetBehaviorCollision
    (Equivalent : SetReceiptLeftValue A initialCode →
      SetReceiptLeftValue A initialCode → Prop)
    (bank : SetReceiptBank A initialCode)
    (receipts : Finset (SetReceiptClass A initialCode)) : Prop :=
  ∃ left ∈ receipts, ∃ right ∈ receipts,
    ¬ Equivalent (bank.2 left) (bank.2 right)

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- The right set is consumable exactly when it contains no behavioral
collision. -/
theorem profiledOpenActiveLaneRightReceiptSetBehaviorUniform_iff_noCollision
    (Equivalent : SetReceiptRightValue A initialCode →
      SetReceiptRightValue A initialCode → Prop)
    (bank : SetReceiptBank A initialCode)
    (receipts : Finset (SetReceiptClass A initialCode)) :
    ProfiledOpenActiveLaneRightReceiptSetBehaviorUniform A initialCode
        Equivalent bank receipts ↔
      ¬ ProfiledOpenActiveLaneRightReceiptSetBehaviorCollision A initialCode
        Equivalent bank receipts := by
  constructor
  · intro huniform hcollision
    rcases hcollision with ⟨left, hleft, right, hright, hne⟩
    exact hne (huniform left hleft right hright)
  · intro hno left hleft right hright
    by_contra hne
    exact hno ⟨left, hleft, right, hright, hne⟩

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Process-two exact criterion. -/
theorem profiledOpenActiveLaneLeftReceiptSetBehaviorUniform_iff_noCollision
    (Equivalent : SetReceiptLeftValue A initialCode →
      SetReceiptLeftValue A initialCode → Prop)
    (bank : SetReceiptBank A initialCode)
    (receipts : Finset (SetReceiptClass A initialCode)) :
    ProfiledOpenActiveLaneLeftReceiptSetBehaviorUniform A initialCode
        Equivalent bank receipts ↔
      ¬ ProfiledOpenActiveLaneLeftReceiptSetBehaviorCollision A initialCode
        Equivalent bank receipts := by
  constructor
  · intro huniform hcollision
    rcases hcollision with ⟨left, hleft, right, hright, hne⟩
    exact hne (huniform left hleft right hright)
  · intro hno left hleft right hright
    by_contra hne
    exact hno ⟨left, hleft, right, hright, hne⟩

/-! ## Selecting behavior without selecting the actual hidden receipt -/

/-- Pick one value from the entire finite set, never from the actual hidden
candidate.  The empty fallback is the existing harmless fixed value. -/
noncomputable def profiledOpenActiveLaneRightReceiptSetSelectedValue
    (bank : SetReceiptBank A initialCode)
    (receipts : Finset (SetReceiptClass A initialCode)) :
    SetReceiptRightValue A initialCode := by
  classical
  exact if h : receipts.Nonempty then bank.1 h.choose
  else profiledOpenFixedDefaultRightPinnedValue A initialCode strategy hwin
    basis

/-- Process-two selection from the whole finite set. -/
noncomputable def profiledOpenActiveLaneLeftReceiptSetSelectedValue
    (bank : SetReceiptBank A initialCode)
    (receipts : Finset (SetReceiptClass A initialCode)) :
    SetReceiptLeftValue A initialCode := by
  classical
  exact if h : receipts.Nonempty then bank.2 h.choose
  else profiledOpenFixedDefaultLeftPinnedValue A initialCode strategy hwin basis

/-- Under behavior uniformity, the one set-selected value is equivalent to
the value indexed by every possible process-one receipt. -/
theorem profiledOpenActiveLaneRightReceiptSetSelectedValue_equivalent
    (Equivalent : SetReceiptRightValue A initialCode →
      SetReceiptRightValue A initialCode → Prop)
    (bank : SetReceiptBank A initialCode)
    (receipts : Finset (SetReceiptClass A initialCode))
    (huniform : ProfiledOpenActiveLaneRightReceiptSetBehaviorUniform A
      initialCode Equivalent bank receipts)
    {receipt : SetReceiptClass A initialCode} (hreceipt : receipt ∈ receipts) :
    Equivalent (bank.1 receipt)
      (profiledOpenActiveLaneRightReceiptSetSelectedValue A strategy hwin basis
        initialCode bank receipts) := by
  classical
  unfold profiledOpenActiveLaneRightReceiptSetSelectedValue
  rw [dif_pos ⟨receipt, hreceipt⟩]
  exact huniform receipt hreceipt
    (Classical.choose ⟨receipt, hreceipt⟩)
    (Classical.choose_spec ⟨receipt, hreceipt⟩)

/-- Process-two selected-value specification. -/
theorem profiledOpenActiveLaneLeftReceiptSetSelectedValue_equivalent
    (Equivalent : SetReceiptLeftValue A initialCode →
      SetReceiptLeftValue A initialCode → Prop)
    (bank : SetReceiptBank A initialCode)
    (receipts : Finset (SetReceiptClass A initialCode))
    (huniform : ProfiledOpenActiveLaneLeftReceiptSetBehaviorUniform A
      initialCode Equivalent bank receipts)
    {receipt : SetReceiptClass A initialCode} (hreceipt : receipt ∈ receipts) :
    Equivalent (bank.2 receipt)
      (profiledOpenActiveLaneLeftReceiptSetSelectedValue A strategy hwin basis
        initialCode bank receipts) := by
  classical
  unfold profiledOpenActiveLaneLeftReceiptSetSelectedValue
  rw [dif_pos ⟨receipt, hreceipt⟩]
  exact huniform receipt hreceipt
    (Classical.choose ⟨receipt, hreceipt⟩)
    (Classical.choose_spec ⟨receipt, hreceipt⟩)

/-! ## Bridge to the existing finite local-consumption interface -/

/-- The finite information consumed after one set-valued recurrence step:
the graph-blind bank selected from the local receive tuple and the complete
set of possible projected receipts. -/
abbrev ProfiledOpenActiveLaneWitnessedReceiptSetSummary :=
  ProfiledOpenFixedSidewisePinnedBank A initialCode
      (SetReceiptClass A initialCode) (SetReceiptClass A initialCode) ×
    Finset (SetReceiptClass A initialCode)

/-- A process-one candidate is represented by a reachable receipt-set
summary when its process-one class occurs in the carried set.  `Allowed`
lets the concrete automaton exclude unreachable summary pairs without
manufacturing behavior for them. -/
def profiledOpenActiveLaneRightReceiptSetPossible
    (Allowed : ProfiledOpenActiveLaneWitnessedReceiptSetSummary A initialCode →
      Prop)
    (summary : ProfiledOpenActiveLaneWitnessedReceiptSetSummary A initialCode)
    (candidate : SetReceiptCandidate A initialCode) : Prop :=
  Allowed summary ∧ candidate.1.1.1 ∈ summary.2

/-- Process-two mirror. -/
def profiledOpenActiveLaneLeftReceiptSetPossible
    (Allowed : ProfiledOpenActiveLaneWitnessedReceiptSetSummary A initialCode →
      Prop)
    (summary : ProfiledOpenActiveLaneWitnessedReceiptSetSummary A initialCode)
    (candidate : SetReceiptCandidate A initialCode) : Prop :=
  Allowed summary ∧ candidate.1.1.2 ∈ summary.2

/-- An actual compatible process-one target is a possible candidate of the
receipt-set summary consumed after the update. -/
theorem profiledOpenActiveLaneRightReceiptSetPossible_of_target
    {BaseOne : Type b₁} {BaseTwo : Type b₂}
    (readers : ProfiledOpenActiveLaneWitnessedReceiptReaders A initialCode
      BaseOne BaseTwo)
    (Allowed : ProfiledOpenActiveLaneWitnessedReceiptSetSummary A initialCode →
      Prop)
    {observation : ProfiledOpenActiveLaneWitnessedRightReceiptObservation A
      initialCode BaseOne BaseTwo}
    {source target : SetReceiptCandidate A initialCode}
    {bank : SetReceiptBank A initialCode}
    {query : ProfiledOpenFixedSidewiseReachablePointedQuery.{i, u, v, x, y, s,
      max i s u v x y, max i s u v x y} (I := I) A initialCode}
    (hallowed : Allowed (bank,
      profiledOpenActiveLaneRightWitnessedLocalNextReceiptSet A strategy hwin
        basis initialCode (BaseOne := BaseOne) (BaseTwo := BaseTwo) readers
        observation))
    (hcompatible :
      profiledOpenActiveLaneRightHonestReceiveCompatible A initialCode readers
        (BaseOne := BaseOne) (BaseTwo := BaseTwo)
        observation source bank query target)
    (hgood : ProfiledOpenActiveLaneWitnessedRecurrenceGood A strategy hwin
      basis initialCode source bank query target)
    (hlive : ProfiledOpenActiveLaneRightWitnessedRuntimeLive A strategy hwin
      basis initialCode target.2 target.1) :
    profiledOpenActiveLaneRightReceiptSetPossible A initialCode Allowed
      (bank,
        profiledOpenActiveLaneRightWitnessedLocalNextReceiptSet A strategy hwin
          basis initialCode (BaseOne := BaseOne) (BaseTwo := BaseTwo) readers
          observation)
      target :=
  ⟨hallowed,
    mem_profiledOpenActiveLaneRightWitnessedLocalNextReceiptSet_of_target A
      strategy hwin basis initialCode readers hcompatible hgood hlive⟩

/-- Process-two actual-target bridge. -/
theorem profiledOpenActiveLaneLeftReceiptSetPossible_of_target
    {BaseOne : Type b₁} {BaseTwo : Type b₂}
    (readers : ProfiledOpenActiveLaneWitnessedReceiptReaders A initialCode
      BaseOne BaseTwo)
    (Allowed : ProfiledOpenActiveLaneWitnessedReceiptSetSummary A initialCode →
      Prop)
    {observation : ProfiledOpenActiveLaneWitnessedLeftReceiptObservation A
      initialCode BaseOne BaseTwo}
    {source target : SetReceiptCandidate A initialCode}
    {bank : SetReceiptBank A initialCode}
    {query : ProfiledOpenFixedSidewiseReachablePointedQuery.{i, u, v, x, y, s,
      max i s u v x y, max i s u v x y} (I := I) A initialCode}
    (hallowed : Allowed (bank,
      profiledOpenActiveLaneLeftWitnessedLocalNextReceiptSet A strategy hwin
        basis initialCode (BaseOne := BaseOne) (BaseTwo := BaseTwo) readers
        observation))
    (hcompatible :
      profiledOpenActiveLaneLeftHonestReceiveCompatible A initialCode readers
        (BaseOne := BaseOne) (BaseTwo := BaseTwo)
        observation source bank query target)
    (hgood : ProfiledOpenActiveLaneWitnessedRecurrenceGood A strategy hwin
      basis initialCode source bank query target)
    (hlive : ProfiledOpenActiveLaneLeftWitnessedRuntimeLive A strategy hwin
      basis initialCode target.2 target.1) :
    profiledOpenActiveLaneLeftReceiptSetPossible A initialCode Allowed
      (bank,
        profiledOpenActiveLaneLeftWitnessedLocalNextReceiptSet A strategy hwin
          basis initialCode (BaseOne := BaseOne) (BaseTwo := BaseTwo) readers
          observation)
      target :=
  ⟨hallowed,
    mem_profiledOpenActiveLaneLeftWitnessedLocalNextReceiptSet_of_target A
      strategy hwin basis initialCode readers hcompatible hgood hlive⟩

/-- Behavior-uniform set-valued receipts are sufficient for the repository's
existing process-one local-consumption interface.  The selected move depends
only on the finite pair `(bank, receiptSet)`; the hidden actual receipt occurs
only in the correctness statement of `SidewiseOneBankFamilyLocallyConsumable`.
-/
theorem
    profiledOpenActiveLaneRightReceiptSetFamilyLocallyConsumable_of_uniform
    (Equivalent : SetReceiptRightValue A initialCode →
      SetReceiptRightValue A initialCode → Prop)
    (Allowed : ProfiledOpenActiveLaneWitnessedReceiptSetSummary A initialCode →
      Prop)
    (huniform : ∀ summary,
      Allowed summary →
        ProfiledOpenActiveLaneRightReceiptSetBehaviorUniform A initialCode
          Equivalent summary.1 summary.2) :
    SidewiseOneBankFamilyLocallyConsumable
      (ProfiledOpenActiveLaneRightWitnessedRuntimeLive A strategy hwin basis
        initialCode)
      (profiledOpenActiveLaneRightReceiptSetPossible A initialCode Allowed)
      Equivalent (fun summary ↦ summary.1) := by
  refine ⟨fun summary ↦
    profiledOpenActiveLaneRightReceiptSetSelectedValue A strategy hwin basis
      initialCode summary.1 summary.2, ?_⟩
  intro summary candidate hpossible _
  exact profiledOpenActiveLaneRightReceiptSetSelectedValue_equivalent A
    strategy hwin basis initialCode Equivalent summary.1 summary.2
    (huniform summary hpossible.1) hpossible.2

/-- Process-two local-consumption bridge. -/
theorem
    profiledOpenActiveLaneLeftReceiptSetFamilyLocallyConsumable_of_uniform
    (Equivalent : SetReceiptLeftValue A initialCode →
      SetReceiptLeftValue A initialCode → Prop)
    (Allowed : ProfiledOpenActiveLaneWitnessedReceiptSetSummary A initialCode →
      Prop)
    (huniform : ∀ summary,
      Allowed summary →
        ProfiledOpenActiveLaneLeftReceiptSetBehaviorUniform A initialCode
          Equivalent summary.1 summary.2) :
    SidewiseTwoBankFamilyLocallyConsumable
      (ProfiledOpenActiveLaneLeftWitnessedRuntimeLive A strategy hwin basis
        initialCode)
      (profiledOpenActiveLaneLeftReceiptSetPossible A initialCode Allowed)
      Equivalent (fun summary ↦ summary.1) := by
  refine ⟨fun summary ↦
    profiledOpenActiveLaneLeftReceiptSetSelectedValue A strategy hwin basis
      initialCode summary.1 summary.2, ?_⟩
  intro summary candidate hpossible _
  exact profiledOpenActiveLaneLeftReceiptSetSelectedValue_equivalent A
    strategy hwin basis initialCode Equivalent summary.1 summary.2
    (huniform summary hpossible.1) hpossible.2

end

end DetParityAutomaton

end DistributedSynthesis
