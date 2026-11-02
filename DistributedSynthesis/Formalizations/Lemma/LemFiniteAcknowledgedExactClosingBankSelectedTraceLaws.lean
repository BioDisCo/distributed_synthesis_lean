/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteAcknowledgedExactClosingBankLiteralCrossTraceInvariant

/-!
# Fibrewise selected traces lift through the dependent bank

The trace adapter for an exact-closing bank is stated on dependent-sum
controls.  Concrete semantic invariants, however, are naturally proved in
one member fibre.  This file removes the resulting transport boilerplate.

`BankSelected` says that the two bank controls have one key and that their
members satisfy the selected predicate in that fibre.  Fibrewise selected
trace laws then lift to `BankSelectedTraceLaws`; all unreachable unequal-key
branches disappear from the proof after unpacking `BankRel`.

The bank key is proof-side construction data.  No executable map introduced
here receives a graph, orientation, hierarchy side, leader bit, history, or
view.
-/

namespace DistributedSynthesis

universe u v x y k c₁ c₂

namespace FiniteAcknowledgedDelayedCarrier

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}

namespace FiniteExactClosingBlindFamily

variable {Key : Type k}
variable
  (family : FiniteExactClosingBlindFamily.{u, v, x, y, k, c₁, c₂}
    (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) Key)

noncomputable section

/-- Lift a member predicate to dependent-bank controls by retaining the
common key and transporting only the second member to that fibre. -/
def BankSelected
    (Selected : ∀ key : Key,
      family.base.ControlOne key → family.base.ControlTwo key → Nat → Prop)
    (one : family.base.BankOneControl)
    (two : family.base.BankTwoControl) (n : Nat) : Prop :=
  ∃ hkey : two.1 = one.1,
    Selected one.1 one.2 (hkey ▸ two.2) n

@[simp] theorem bankSelected_same
    (Selected : ∀ key : Key,
      family.base.ControlOne key → family.base.ControlTwo key → Nat → Prop)
    (key : Key) (one : family.base.ControlOne key)
    (two : family.base.ControlTwo key) (n : Nat) :
    family.BankSelected Selected ⟨key, one⟩ ⟨key, two⟩ n ↔
      Selected key one two n := by
  constructor
  · rintro ⟨hkey, hselected⟩
    simpa using hselected
  · intro hselected
    exact ⟨rfl, hselected⟩

/-- The chosen bank root inherits the selected fact of its member fibre. -/
theorem bankSelected_initial
    (Selected : ∀ key : Key,
      family.base.ControlOne key → family.base.ControlTwo key → Nat → Prop)
    (key : Key)
    (hselected :
      Selected key (family.base.initialOne key) (family.base.initialTwo key) 0) :
    family.BankSelected Selected (family.base.bankInitialOne key)
      (family.base.bankInitialTwo key) 0 := by
  exact ⟨rfl, hselected⟩

/-! ## One fixed fibre

For final trace extraction the bank starts in one already selected package
fibre.  The following presentation stores explicit member witnesses at that
fixed key.  It is equivalent to the key-indexed predicate above on a run that
starts at `key`, but lets a caller provide laws for only that member. -/

/-- A selected bank pair represented by two members of one fixed fibre. -/
def BankSelectedAt
    (key : Key)
    (Selected : family.base.ControlOne key →
      family.base.ControlTwo key → Nat → Prop)
    (one : family.base.BankOneControl)
    (two : family.base.BankTwoControl) (n : Nat) : Prop :=
  ∃ memberOne : family.base.ControlOne key,
    ∃ memberTwo : family.base.ControlTwo key,
      one = ⟨key, memberOne⟩ ∧ two = ⟨key, memberTwo⟩ ∧
        Selected memberOne memberTwo n

@[simp] theorem bankSelectedAt_same
    (key : Key)
    (Selected : family.base.ControlOne key →
      family.base.ControlTwo key → Nat → Prop)
    (one : family.base.ControlOne key)
    (two : family.base.ControlTwo key) (n : Nat) :
    family.BankSelectedAt key Selected ⟨key, one⟩ ⟨key, two⟩ n ↔
      Selected one two n := by
  constructor
  · rintro ⟨memberOne, memberTwo, hone, htwo, hselected⟩
    cases hone
    cases htwo
    exact hselected
  · intro hselected
    exact ⟨one, two, rfl, rfl, hselected⟩

/-- Selected trace laws for one fibre lift to the whole bank initialized at
that fibre.  In particular the totalized unequal-key receive clauses are
unreachable and create no concrete proof obligation. -/
noncomputable def bankSelectedTraceLaws_of_fibre
    (key : Key)
    (Selected : family.base.ControlOne key →
      family.base.ControlTwo key → Nat → Prop)
    (env : EnvironmentSequence In₁ In₂)
    (expectedOutputOne : Nat → Out₁)
    (expectedOutputTwo : Nat → Out₂)
    (fibreLaws : ExactClosingSelectedTraceLaws
      (family.base.initialOne key) (family.base.initialTwo key)
      (family.base.noRecvOne key) (family.base.noRecvTwo key)
      (family.base.openRecvOne key) (family.base.openRecvTwo key)
      (family.base.close key) (family.base.Rel key) Selected env
      expectedOutputOne expectedOutputTwo) :
    family.BankSelectedTraceLaws key (family.BankSelectedAt key Selected) env
      expectedOutputOne expectedOutputTwo where
  initial := ⟨family.base.initialOne key, family.base.initialTwo key,
    rfl, rfl, fibreLaws.initial⟩
  strictRight := by
    intro n one two hrel hselected hgraph
    rcases hselected with ⟨memberOne, memberTwo, rfl, rfl, hselected⟩
    have hrel' : family.base.Rel key memberOne memberTwo := by
      rcases hrel with ⟨hkey, hrel⟩
      simpa using hrel
    have hnext := fibreLaws.strictRight n memberOne memberTwo hrel' hselected
      hgraph
    rw [family.base.bankOpenRecvTwo_same]
    exact ⟨
      ⟨(family.base.noRecvOne key memberOne (env n).inputOne).1,
        (family.base.openRecvTwo key memberTwo (env n).inputTwo memberOne
          (env n).inputOne).1,
        rfl, rfl, hnext.1⟩,
      hnext.2⟩
  strictLeft := by
    intro n one two hrel hselected hgraph
    rcases hselected with ⟨memberOne, memberTwo, rfl, rfl, hselected⟩
    have hrel' : family.base.Rel key memberOne memberTwo := by
      rcases hrel with ⟨hkey, hrel⟩
      simpa using hrel
    have hnext := fibreLaws.strictLeft n memberOne memberTwo hrel' hselected
      hgraph
    rw [family.base.bankOpenRecvOne_same]
    exact ⟨
      ⟨(family.base.openRecvOne key memberOne (env n).inputOne memberTwo
          (env n).inputTwo).1,
        (family.base.noRecvTwo key memberTwo (env n).inputTwo).1,
        rfl, rfl, hnext.1⟩,
      hnext.2⟩
  both := by
    intro n one two hrel hselected hgraph
    rcases hselected with ⟨memberOne, memberTwo, rfl, rfl, hselected⟩
    have hrel' : family.base.Rel key memberOne memberTwo := by
      rcases hrel with ⟨hkey, hrel⟩
      simpa using hrel
    have hnext := fibreLaws.both n memberOne memberTwo hrel' hselected hgraph
    rw [family.base.bankClose_same, family.base.bankOpenRecvOne_same,
      family.base.bankOpenRecvTwo_same]
    exact ⟨
      ⟨(family.base.close key memberOne (env n).inputOne memberTwo
          (env n).inputTwo).1,
        (family.base.close key memberOne (env n).inputOne memberTwo
          (env n).inputTwo).2,
        rfl, rfl, hnext.1⟩,
      hnext.2⟩

/-- Direct fixed-fibre Mealy endpoint.  The dependent bank, acknowledgement
relay, and arbitrary blind-depth invariant are all discharged by the two
generic adapters. -/
noncomputable def bankMealyTraceInvariant_of_fibre
    [Fintype Key]
    (key : Key)
    (Selected : family.base.ControlOne key →
      family.base.ControlTwo key → Nat → Prop)
    (env : EnvironmentSequence In₁ In₂)
    (expectedOutputOne : Nat → Out₁)
    (expectedOutputTwo : Nat → Out₂)
    (fibreLaws : ExactClosingSelectedTraceLaws
      (family.base.initialOne key) (family.base.initialTwo key)
      (family.base.noRecvOne key) (family.base.noRecvTwo key)
      (family.base.openRecvOne key) (family.base.openRecvTwo key)
      (family.base.close key) (family.base.Rel key) Selected env
      expectedOutputOne expectedOutputTwo) :
    (family.base.bankPairedMealyController key).LiteralCrossMealyTraceInvariant
      env :=
  family.bankMealyTraceInvariant key (family.BankSelectedAt key Selected) env
    expectedOutputOne expectedOutputTwo
      (family.bankSelectedTraceLaws_of_fibre key Selected env
        expectedOutputOne expectedOutputTwo fibreLaws)

/-- Pointwise selected-control laws lift through the dependent bank.  The
same environment and expected physical trace are used in every fibre; the
operational run starts in the explicitly chosen `key` and never leaves it. -/
noncomputable def bankSelectedTraceLaws_of_fibrewise
    (Selected : ∀ key : Key,
      family.base.ControlOne key → family.base.ControlTwo key → Nat → Prop)
    (env : EnvironmentSequence In₁ In₂)
    (expectedOutputOne : Nat → Out₁)
    (expectedOutputTwo : Nat → Out₂)
    (fibreLaws : ∀ key : Key,
      ExactClosingSelectedTraceLaws
        (family.base.initialOne key) (family.base.initialTwo key)
        (family.base.noRecvOne key) (family.base.noRecvTwo key)
        (family.base.openRecvOne key) (family.base.openRecvTwo key)
        (family.base.close key) (family.base.Rel key) (Selected key) env
        expectedOutputOne expectedOutputTwo)
    (key : Key) :
    family.BankSelectedTraceLaws key (family.BankSelected Selected) env
      expectedOutputOne expectedOutputTwo where
  initial := family.bankSelected_initial Selected key (fibreLaws key).initial
  strictRight := by
    intro n one two hrel hselected hgraph
    rcases one with ⟨keyOne, one⟩
    rcases two with ⟨keyTwo, two⟩
    rcases hrel with ⟨hkey, hrel⟩
    change keyTwo = keyOne at hkey
    subst keyTwo
    have hselected' : Selected keyOne one two n :=
      (family.bankSelected_same Selected keyOne one two n).1 hselected
    have hnext :=
      (fibreLaws keyOne).strictRight n one two hrel hselected' hgraph
    rw [family.base.bankOpenRecvTwo_same]
    exact ⟨⟨rfl, hnext.1⟩, hnext.2⟩
  strictLeft := by
    intro n one two hrel hselected hgraph
    rcases one with ⟨keyOne, one⟩
    rcases two with ⟨keyTwo, two⟩
    rcases hrel with ⟨hkey, hrel⟩
    change keyTwo = keyOne at hkey
    subst keyTwo
    have hselected' : Selected keyOne one two n :=
      (family.bankSelected_same Selected keyOne one two n).1 hselected
    have hnext :=
      (fibreLaws keyOne).strictLeft n one two hrel hselected' hgraph
    rw [family.base.bankOpenRecvOne_same]
    exact ⟨⟨rfl, hnext.1⟩, hnext.2⟩
  both := by
    intro n one two hrel hselected hgraph
    rcases one with ⟨keyOne, one⟩
    rcases two with ⟨keyTwo, two⟩
    rcases hrel with ⟨hkey, hrel⟩
    change keyTwo = keyOne at hkey
    subst keyTwo
    have hselected' : Selected keyOne one two n :=
      (family.bankSelected_same Selected keyOne one two n).1 hselected
    have hnext := (fibreLaws keyOne).both n one two hrel hselected' hgraph
    rw [family.base.bankClose_same, family.base.bankOpenRecvOne_same,
      family.base.bankOpenRecvTwo_same]
    exact ⟨⟨rfl, hnext.1⟩, hnext.2⟩

/-- Direct Mealy consumption: fibrewise semantic trace laws are sufficient
for the complete acknowledged dependent-bank invariant. -/
noncomputable def bankMealyTraceInvariant_of_fibrewise
    [Fintype Key]
    (Selected : ∀ key : Key,
      family.base.ControlOne key → family.base.ControlTwo key → Nat → Prop)
    (env : EnvironmentSequence In₁ In₂)
    (expectedOutputOne : Nat → Out₁)
    (expectedOutputTwo : Nat → Out₂)
    (fibreLaws : ∀ key : Key,
      ExactClosingSelectedTraceLaws
        (family.base.initialOne key) (family.base.initialTwo key)
        (family.base.noRecvOne key) (family.base.noRecvTwo key)
        (family.base.openRecvOne key) (family.base.openRecvTwo key)
        (family.base.close key) (family.base.Rel key) (Selected key) env
        expectedOutputOne expectedOutputTwo)
    (key : Key) :
    (family.base.bankPairedMealyController key).LiteralCrossMealyTraceInvariant
      env :=
  family.bankMealyTraceInvariant key (family.BankSelected Selected) env
    expectedOutputOne expectedOutputTwo
      (family.bankSelectedTraceLaws_of_fibrewise Selected env expectedOutputOne
        expectedOutputTwo fibreLaws key)

end

end FiniteExactClosingBlindFamily

end FiniteAcknowledgedDelayedCarrier

end DistributedSynthesis
