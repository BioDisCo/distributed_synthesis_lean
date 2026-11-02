/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteAcknowledgedExactClosingBlindForkInvariant

/-!
# A finite dependent bank of acknowledged exact-close components

The concrete literal construction has one finite controller fibre for every
two-round seed.  Its two symmetric seam orientations must be carried
simultaneously *inside* that fibre; an orientation is never selected as a
bank key.  The local control types are dependent on the seed-selected package,
so an ordinary product type is not an adequate outer carrier.

This module packages the fibres in dependent sums.  Every executable map
preserves its finite bank key.  Equal-key receives dispatch to the selected
member; unequal keys are totalized with that member's own initial partner and
are unreachable under the proof-side bank relation.  The exact-close laws
lift pointwise, so the acknowledgement proof never needs to inspect a seed or
an orientation.

The key is fixed construction data (in the intended instantiation, the finite
seed/package) stored in the local control.  It is not a runtime orientation or
leader signal.  No map in this file receives a graph, hierarchy side, leader
bit, history, or view.
-/

namespace DistributedSynthesis

universe u v x y k c₁ c₂

namespace FiniteAcknowledgedDelayedCarrier

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}

/-- A finite family of exact-closing controller fibres. -/
structure FiniteExactClosingFamily (Key : Type k) where
  ControlOne : Key → Type c₁
  ControlTwo : Key → Type c₂
  oneFinite : ∀ key, Fintype (ControlOne key)
  twoFinite : ∀ key, Fintype (ControlTwo key)
  initialOne : ∀ key, ControlOne key
  initialTwo : ∀ key, ControlTwo key
  noRecvOne : ∀ key, ControlOne key → In₁ → ControlOne key × Out₁
  noRecvTwo : ∀ key, ControlTwo key → In₂ → ControlTwo key × Out₂
  openRecvOne : ∀ key,
    ControlOne key → In₁ → ControlTwo key → In₂ → ControlOne key × Out₁
  openRecvTwo : ∀ key,
    ControlTwo key → In₂ → ControlOne key → In₁ → ControlTwo key × Out₂
  close : ∀ key,
    ControlOne key → In₁ → ControlTwo key → In₂ →
      ControlOne key × ControlTwo key
  Rel : ∀ key, ControlOne key → ControlTwo key → Prop
  laws : ∀ key,
    ExactClosingRelationLaws (initialOne key) (initialTwo key)
      (noRecvOne key) (noRecvTwo key) (openRecvOne key) (openRecvTwo key)
      (close key) (Rel key)

namespace FiniteExactClosingFamily

variable {Key : Type k}
variable
  (family : FiniteExactClosingFamily (In₁ := In₁) (In₂ := In₂)
    (Out₁ := Out₁) (Out₂ := Out₂) Key)

/-- Process-one controls of all dependent fibres. -/
abbrev BankOneControl := Σ key : Key, family.ControlOne key

/-- Process-two controls of all dependent fibres. -/
abbrev BankTwoControl := Σ key : Key, family.ControlTwo key

noncomputable instance bankOneFintype [Fintype Key] :
    Fintype family.BankOneControl := by
  classical
  letI (key : Key) : Fintype (family.ControlOne key) := family.oneFinite key
  infer_instance

noncomputable instance bankTwoFintype [Fintype Key] :
    Fintype family.BankTwoControl := by
  classical
  letI (key : Key) : Fintype (family.ControlTwo key) := family.twoFinite key
  infer_instance

/-- Install both endpoints in one selected fibre. -/
def bankInitialOne (key : Key) : family.BankOneControl :=
  ⟨key, family.initialOne key⟩

def bankInitialTwo (key : Key) : family.BankTwoControl :=
  ⟨key, family.initialTwo key⟩

/-- Nonreceive preserves the dependent bank key. -/
def bankNoRecvOne (state : family.BankOneControl) (input : In₁) :
    family.BankOneControl × Out₁ :=
  let next := family.noRecvOne state.1 state.2 input
  (⟨state.1, next.1⟩, next.2)

def bankNoRecvTwo (state : family.BankTwoControl) (input : In₂) :
    family.BankTwoControl × Out₂ :=
  let next := family.noRecvTwo state.1 state.2 input
  (⟨state.1, next.1⟩, next.2)

/-- Equal-key receives dispatch to that exact member.  The mismatch branch
uses the receiver's own member and its canonical initial partner solely to
make the executable map total. -/
noncomputable def bankOpenRecvOne
    (one : family.BankOneControl) (own : In₁)
    (two : family.BankTwoControl) (delivered : In₂) :
    family.BankOneControl × Out₁ := by
  classical
  rcases one with ⟨keyOne, one⟩
  rcases two with ⟨keyTwo, two⟩
  by_cases hkey : keyTwo = keyOne
  · subst keyTwo
    let next := family.openRecvOne keyOne one own two delivered
    exact (⟨keyOne, next.1⟩, next.2)
  · let next := family.openRecvOne keyOne one own
      (family.initialTwo keyOne) delivered
    exact (⟨keyOne, next.1⟩, next.2)

noncomputable def bankOpenRecvTwo
    (two : family.BankTwoControl) (own : In₂)
    (one : family.BankOneControl) (delivered : In₁) :
    family.BankTwoControl × Out₂ := by
  classical
  rcases two with ⟨keyTwo, two⟩
  rcases one with ⟨keyOne, one⟩
  by_cases hkey : keyOne = keyTwo
  · subst keyOne
    let next := family.openRecvTwo keyTwo two own one delivered
    exact (⟨keyTwo, next.1⟩, next.2)
  · let next := family.openRecvTwo keyTwo two own
      (family.initialOne keyTwo) delivered
    exact (⟨keyTwo, next.1⟩, next.2)

/-- The exact joint close also preserves the selected dependent key.  On an
unreachable mismatch it closes process one's fibre against its own canonical
process-two root, ensuring that both projections still share one key. -/
noncomputable def bankClose
    (one : family.BankOneControl) (own : In₁)
    (two : family.BankTwoControl) (delivered : In₂) :
    family.BankOneControl × family.BankTwoControl := by
  classical
  rcases one with ⟨keyOne, one⟩
  rcases two with ⟨keyTwo, two⟩
  by_cases hkey : keyTwo = keyOne
  · subst keyTwo
    let next := family.close keyOne one own two delivered
    exact (⟨keyOne, next.1⟩, ⟨keyOne, next.2⟩)
  · let next := family.close keyOne one own (family.initialTwo keyOne)
      delivered
    exact (⟨keyOne, next.1⟩, ⟨keyOne, next.2⟩)

@[simp] theorem bankOpenRecvOne_same
    (key : Key) (one : family.ControlOne key) (own : In₁)
    (two : family.ControlTwo key) (delivered : In₂) :
    family.bankOpenRecvOne ⟨key, one⟩ own ⟨key, two⟩ delivered =
      (⟨key, (family.openRecvOne key one own two delivered).1⟩,
        (family.openRecvOne key one own two delivered).2) := by
  simp [bankOpenRecvOne]

@[simp] theorem bankOpenRecvTwo_same
    (key : Key) (two : family.ControlTwo key) (own : In₂)
    (one : family.ControlOne key) (delivered : In₁) :
    family.bankOpenRecvTwo ⟨key, two⟩ own ⟨key, one⟩ delivered =
      (⟨key, (family.openRecvTwo key two own one delivered).1⟩,
        (family.openRecvTwo key two own one delivered).2) := by
  simp [bankOpenRecvTwo]

@[simp] theorem bankClose_same
    (key : Key) (one : family.ControlOne key) (own : In₁)
    (two : family.ControlTwo key) (delivered : In₂) :
    family.bankClose ⟨key, one⟩ own ⟨key, two⟩ delivered =
      (⟨key, (family.close key one own two delivered).1⟩,
        ⟨key, (family.close key one own two delivered).2⟩) := by
  simp [bankClose]

/-- Proof-side agreement of bank keys and the member relation. -/
def BankRel (one : family.BankOneControl)
    (two : family.BankTwoControl) : Prop :=
  ∃ hkey : two.1 = one.1,
    family.Rel one.1 one.2 (hkey ▸ two.2)

@[simp] theorem bankInitial_keys
    (key : Key) :
    (family.bankInitialOne key).1 = (family.bankInitialTwo key).1 :=
  rfl

theorem bankInitial_rel (key : Key) :
    family.BankRel (family.bankInitialOne key)
      (family.bankInitialTwo key) := by
  exact ⟨rfl, (family.laws key).initial⟩

@[simp] theorem bankNoRecvOne_key
    (state : family.BankOneControl) (input : In₁) :
    (family.bankNoRecvOne state input).1.1 = state.1 :=
  rfl

@[simp] theorem bankNoRecvTwo_key
    (state : family.BankTwoControl) (input : In₂) :
    (family.bankNoRecvTwo state input).1.1 = state.1 :=
  rfl

/-- The member laws lift without any cross-fibre transport. -/
theorem bank_strictRight
    (one : family.BankOneControl) (inputOne : In₁)
    (two : family.BankTwoControl) (inputTwo : In₂)
    (hrel : family.BankRel one two) :
    family.BankRel
      (family.bankNoRecvOne one inputOne).1
      (family.bankOpenRecvTwo two inputTwo one inputOne).1 := by
  rcases one with ⟨keyOne, one⟩
  rcases two with ⟨keyTwo, two⟩
  rcases hrel with ⟨hkey, hrel⟩
  change keyTwo = keyOne at hkey
  subst keyTwo
  rw [family.bankOpenRecvTwo_same]
  refine ⟨rfl, ?_⟩
  exact (family.laws keyOne).strictRight one inputOne two inputTwo hrel

theorem bank_strictLeft
    (one : family.BankOneControl) (inputOne : In₁)
    (two : family.BankTwoControl) (inputTwo : In₂)
    (hrel : family.BankRel one two) :
    family.BankRel
      (family.bankOpenRecvOne one inputOne two inputTwo).1
      (family.bankNoRecvTwo two inputTwo).1 := by
  rcases one with ⟨keyOne, one⟩
  rcases two with ⟨keyTwo, two⟩
  rcases hrel with ⟨hkey, hrel⟩
  change keyTwo = keyOne at hkey
  subst keyTwo
  rw [family.bankOpenRecvOne_same]
  refine ⟨rfl, ?_⟩
  exact (family.laws keyOne).strictLeft one inputOne two inputTwo hrel

theorem bank_both
    (one : family.BankOneControl) (inputOne : In₁)
    (two : family.BankTwoControl) (inputTwo : In₂)
    (hrel : family.BankRel one two) :
    family.BankRel
      (family.bankClose one inputOne two inputTwo).1
      (family.bankClose one inputOne two inputTwo).2 := by
  rcases one with ⟨keyOne, one⟩
  rcases two with ⟨keyTwo, two⟩
  rcases hrel with ⟨hkey, hrel⟩
  change keyTwo = keyOne at hkey
  subst keyTwo
  rw [family.bankClose_same]
  refine ⟨rfl, ?_⟩
  exact (family.laws keyOne).both one inputOne two inputTwo hrel

/-- Pointwise exact-close laws lifted to the whole finite dependent bank. -/
noncomputable def bankRelationLaws (key : Key) :
    ExactClosingRelationLaws
      (family.bankInitialOne key) (family.bankInitialTwo key)
      family.bankNoRecvOne family.bankNoRecvTwo
      family.bankOpenRecvOne family.bankOpenRecvTwo family.bankClose
      family.BankRel where
  initial := family.bankInitial_rel key
  strictRight := family.bank_strictRight
  strictLeft := family.bank_strictLeft
  both := family.bank_both

/-- The complete acknowledged controller over all dependent fibres. -/
noncomputable def bankPairedMealyController [Fintype Key] (key : Key) :
    FinitePairedMealyController In₁ In₂ Out₁ Out₂ :=
  exactClosingPairedMealyController
    (family.bankInitialOne key) (family.bankInitialTwo key)
    family.bankNoRecvOne family.bankNoRecvTwo
    family.bankOpenRecvOne family.bankOpenRecvTwo family.bankClose

end FiniteExactClosingFamily

/-! ## Blind-fork bisimulation lifted through the same dependent bank -/

/-- A family whose members additionally prove arbitrary-depth equality of
the unresolved open/exact blind branches. -/
structure FiniteExactClosingBlindFamily (Key : Type k) where
  base : FiniteExactClosingFamily.{u, v, x, y, k, c₁, c₂}
    (In₁ := In₁) (In₂ := In₂)
    (Out₁ := Out₁) (Out₂ := Out₂) Key
  BlindOne : ∀ key, base.ControlOne key → base.ControlOne key → Prop
  BlindTwo : ∀ key, base.ControlTwo key → base.ControlTwo key → Prop
  noRecvLaws : ∀ key,
    BlindNoRecvLaws (base.noRecvOne key) (base.noRecvTwo key)
      (BlindOne key) (BlindTwo key)
  receiveLaws : ∀ key,
    ExactClosingBlindReceiveLaws
      (base.openRecvOne key) (base.openRecvTwo key) (base.close key)
      (base.Rel key) (BlindOne key) (BlindTwo key)

namespace FiniteExactClosingBlindFamily

variable {Key : Type k}
variable
  (family : FiniteExactClosingBlindFamily (In₁ := In₁) (In₂ := In₂)
    (Out₁ := Out₁) (Out₂ := Out₂) Key)

/-- Bank-level blind relation: equal dependent key and the member relation. -/
def BankBlindOne (left right : family.base.BankOneControl) : Prop :=
  ∃ hkey : right.1 = left.1,
    family.BlindOne left.1 left.2 (hkey ▸ right.2)

def BankBlindTwo (left right : family.base.BankTwoControl) : Prop :=
  ∃ hkey : right.1 = left.1,
    family.BlindTwo left.1 left.2 (hkey ▸ right.2)

theorem bankBlindOne_noRecv
    (left right : family.base.BankOneControl) (input : In₁)
    (hblind : family.BankBlindOne left right) :
    (family.base.bankNoRecvOne left input).2 =
        (family.base.bankNoRecvOne right input).2 ∧
      family.BankBlindOne
        (family.base.bankNoRecvOne left input).1
        (family.base.bankNoRecvOne right input).1 := by
  rcases left with ⟨leftKey, left⟩
  rcases right with ⟨rightKey, right⟩
  rcases hblind with ⟨hkey, hblind⟩
  change rightKey = leftKey at hkey
  subst rightKey
  have hstep := (family.noRecvLaws leftKey).one left right input hblind
  exact ⟨hstep.1, ⟨rfl, hstep.2⟩⟩

theorem bankBlindTwo_noRecv
    (left right : family.base.BankTwoControl) (input : In₂)
    (hblind : family.BankBlindTwo left right) :
    (family.base.bankNoRecvTwo left input).2 =
        (family.base.bankNoRecvTwo right input).2 ∧
      family.BankBlindTwo
        (family.base.bankNoRecvTwo left input).1
        (family.base.bankNoRecvTwo right input).1 := by
  rcases left with ⟨leftKey, left⟩
  rcases right with ⟨rightKey, right⟩
  rcases hblind with ⟨hkey, hblind⟩
  change rightKey = leftKey at hkey
  subst rightKey
  have hstep := (family.noRecvLaws leftKey).two left right input hblind
  exact ⟨hstep.1, ⟨rfl, hstep.2⟩⟩

/-- The open/exact receive alternatives stay in one bank fibre and inherit
the member's blind compatibility. -/
theorem bankBlindOne_receive
    (one : family.base.BankOneControl) (inputOne : In₁)
    (two : family.base.BankTwoControl) (inputTwo : In₂)
    (hrel : family.base.BankRel one two) :
    family.BankBlindOne
      (family.base.bankOpenRecvOne one inputOne two inputTwo).1
      (family.base.bankClose one inputOne two inputTwo).1 := by
  rcases one with ⟨keyOne, one⟩
  rcases two with ⟨keyTwo, two⟩
  rcases hrel with ⟨hkey, hrel⟩
  change keyTwo = keyOne at hkey
  subst keyTwo
  rw [family.base.bankOpenRecvOne_same, family.base.bankClose_same]
  exact ⟨rfl,
    (family.receiveLaws keyOne).one one inputOne two inputTwo hrel⟩

theorem bankBlindTwo_receive
    (one : family.base.BankOneControl) (inputOne : In₁)
    (two : family.base.BankTwoControl) (inputTwo : In₂)
    (hrel : family.base.BankRel one two) :
    family.BankBlindTwo
      (family.base.bankOpenRecvTwo two inputTwo one inputOne).1
      (family.base.bankClose one inputOne two inputTwo).2 := by
  rcases one with ⟨keyOne, one⟩
  rcases two with ⟨keyTwo, two⟩
  rcases hrel with ⟨hkey, hrel⟩
  change keyTwo = keyOne at hkey
  subst keyTwo
  rw [family.base.bankOpenRecvTwo_same, family.base.bankClose_same]
  exact ⟨rfl,
    (family.receiveLaws keyOne).two one inputOne two inputTwo hrel⟩

noncomputable def bankBlindNoRecvLaws :
    BlindNoRecvLaws family.base.bankNoRecvOne family.base.bankNoRecvTwo
      family.BankBlindOne family.BankBlindTwo where
  one := family.bankBlindOne_noRecv
  two := family.bankBlindTwo_noRecv

noncomputable def bankBlindReceiveLaws :
    ExactClosingBlindReceiveLaws
      family.base.bankOpenRecvOne family.base.bankOpenRecvTwo
      family.base.bankClose family.base.BankRel
      family.BankBlindOne family.BankBlindTwo where
  one := family.bankBlindOne_receive
  two := family.bankBlindTwo_receive

/-- All semantic and arbitrary-depth blind laws lifted to the whole bank. -/
noncomputable def bankBlindForkLaws (key : Key) :
    ExactClosingBlindForkLaws
      (family.base.bankInitialOne key) (family.base.bankInitialTwo key)
      family.base.bankNoRecvOne family.base.bankNoRecvTwo
      family.base.bankOpenRecvOne family.base.bankOpenRecvTwo
      family.base.bankClose family.base.BankRel
      family.BankBlindOne family.BankBlindTwo where
  relation := family.base.bankRelationLaws key
  noRecv := family.bankBlindNoRecvLaws
  receive := family.bankBlindReceiveLaws

end FiniteExactClosingBlindFamily

end FiniteAcknowledgedDelayedCarrier

end DistributedSynthesis
