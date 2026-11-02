/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledEndToEndOperationalFamilyReceiverBankStep

/-!
# Refreshing alternating root families from the receiver banks

After a block step, each full receiver bank contains exactly the two pieces
needed at the next strict reversal: the current state of its own monitor and
the recurrent macro staged for the opposite orientation.  This file turns
those pieces back into the package-wide restart-root types.

The two refreshed source maps are indexed by the fixed family convention,
not by the current graph:

* right `false` is the current right root at the common past anchor;
* right `true` is the right root staged by the left member at the
  complementary anchor;
* left `false` is the current left root at the complementary anchor;
* left `true` is the left root staged by the right member at the anchor.

Thus the construction stores neither a current orientation nor a strict-
leader bit.  The anchor is the already synchronized provenance bit carried
by the full family receiver bundles.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

open PairedStrategyMemory
open PairedStrategyMemory.PairedInitialProfiledRationalPackage

variable (package : PairedInitialProfiledRationalPackage A)

/-! ## Exact current roots -/

/-- Repackage one member of a right receiver bank at its current monitor
state.  The stored root contributes only the monitor source; its old restart
state is replaced by the state reached by the bank. -/
def endToEndRightFamilyBankCurrentRoot
    (move : EndToEndRightFamilyPairMove A package)
    (bank : EndToEndRightFamilyReceiverBank A package move)
    (member : Bool) : EndToEndRightRestartRoot A package :=
  ⟨(move.1 member).1, (bank member).2.1⟩

/-- Left-oriented mirror. -/
def endToEndLeftFamilyBankCurrentRoot
    (move : EndToEndLeftFamilyPairMove A package)
    (bank : EndToEndLeftFamilyReceiverBank A package move)
    (member : Bool) : EndToEndLeftRestartRoot A package :=
  ⟨(move.1 member).1, (bank member).2.1⟩

section
omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]

@[simp] theorem endToEndRightFamilyBankCurrentRoot_source
    (move : EndToEndRightFamilyPairMove A package)
    (bank : EndToEndRightFamilyReceiverBank A package move)
    (member : Bool) :
    (endToEndRightFamilyBankCurrentRoot A package move bank member).1 =
      (move.1 member).1 :=
  rfl

@[simp] theorem endToEndRightFamilyBankCurrentRoot_state
    (move : EndToEndRightFamilyPairMove A package)
    (bank : EndToEndRightFamilyReceiverBank A package move)
    (member : Bool) :
    (endToEndRightFamilyBankCurrentRoot A package move bank member).2 =
      (bank member).2.1 :=
  rfl

@[simp] theorem endToEndLeftFamilyBankCurrentRoot_source
    (move : EndToEndLeftFamilyPairMove A package)
    (bank : EndToEndLeftFamilyReceiverBank A package move)
    (member : Bool) :
    (endToEndLeftFamilyBankCurrentRoot A package move bank member).1 =
      (move.1 member).1 :=
  rfl

@[simp] theorem endToEndLeftFamilyBankCurrentRoot_state
    (move : EndToEndLeftFamilyPairMove A package)
    (bank : EndToEndLeftFamilyReceiverBank A package move)
    (member : Bool) :
    (endToEndLeftFamilyBankCurrentRoot A package move bank member).2 =
      (bank member).2.1 :=
  rfl

end

/-! ## Staged opposite roots -/

/-- A recurrent right macro staged by a left receiver becomes a fresh right
restart root.  Its origin summand selects the corresponding package-wide
monitor source, and the new monitor starts at its own initial state. -/
noncomputable def endToEndRightRestartRootOfPending :
    EndToEndRecurrentRightMacro A package → EndToEndRightRestartRoot A package
  | .inl source =>
      ⟨.rightOrigin source,
        ((EndToEndRightMonitorSource.rightOrigin source).monitor A package).initial⟩
  | .inr source =>
      ⟨.leftOrigin source,
        ((EndToEndRightMonitorSource.leftOrigin source).monitor A package).initial⟩

/-- Left-oriented mirror. -/
noncomputable def endToEndLeftRestartRootOfPending :
    EndToEndRecurrentLeftMacro A package → EndToEndLeftRestartRoot A package
  | .inl source =>
      ⟨.rightOrigin source,
        ((EndToEndLeftMonitorSource.rightOrigin source).monitor A package).initial⟩
  | .inr source =>
      ⟨.leftOrigin source,
        ((EndToEndLeftMonitorSource.leftOrigin source).monitor A package).initial⟩

/-- Map the optional macro staged by a left-family receiver member to the
optional fresh right root. -/
noncomputable def endToEndRightRestartRootOfPending? :
    Option (EndToEndRecurrentRightMacro A package) →
      Option (EndToEndRightRestartRoot A package) :=
  Option.map (endToEndRightRestartRootOfPending A package)

/-- Map the optional macro staged by a right-family receiver member to the
optional fresh left root. -/
noncomputable def endToEndLeftRestartRootOfPending? :
    Option (EndToEndRecurrentLeftMacro A package) →
      Option (EndToEndLeftRestartRoot A package) :=
  Option.map (endToEndLeftRestartRootOfPending A package)

section
omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]

@[simp] theorem endToEndRightRestartRootOfPending?_none :
    endToEndRightRestartRootOfPending? A package none = none :=
  rfl

@[simp] theorem endToEndRightRestartRootOfPending?_some
    (source : EndToEndRecurrentRightMacro A package) :
    endToEndRightRestartRootOfPending? A package (some source) =
      some (endToEndRightRestartRootOfPending A package source) :=
  rfl

@[simp] theorem endToEndLeftRestartRootOfPending?_none :
    endToEndLeftRestartRootOfPending? A package none = none :=
  rfl

@[simp] theorem endToEndLeftRestartRootOfPending?_some
    (source : EndToEndRecurrentLeftMacro A package) :
    endToEndLeftRestartRootOfPending? A package (some source) =
      some (endToEndLeftRestartRootOfPending A package source) :=
  rfl

end

/-- The optional fresh left root staged by one right-family bank member. -/
noncomputable def endToEndRightFamilyBankPendingLeftRoot?
    (move : EndToEndRightFamilyPairMove A package)
    (bank : EndToEndRightFamilyReceiverBank A package move)
    (member : Bool) : Option (EndToEndLeftRestartRoot A package) :=
  endToEndLeftRestartRootOfPending? A package (bank member).2.2

/-- The optional fresh right root staged by one left-family bank member. -/
noncomputable def endToEndLeftFamilyBankPendingRightRoot?
    (move : EndToEndLeftFamilyPairMove A package)
    (bank : EndToEndLeftFamilyReceiverBank A package move)
    (member : Bool) : Option (EndToEndRightRestartRoot A package) :=
  endToEndRightRestartRootOfPending? A package (bank member).2.2

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem endToEndRightFamilyBankPendingLeftRoot?_of_pending
    (move : EndToEndRightFamilyPairMove A package)
    (bank : EndToEndRightFamilyReceiverBank A package move)
    (member : Bool) (source : EndToEndRecurrentLeftMacro A package)
    (hpending : (bank member).2.2 = some source) :
    endToEndRightFamilyBankPendingLeftRoot? A package move bank member =
      some (endToEndLeftRestartRootOfPending A package source) := by
  simp [endToEndRightFamilyBankPendingLeftRoot?, hpending]

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem endToEndLeftFamilyBankPendingRightRoot?_of_pending
    (move : EndToEndLeftFamilyPairMove A package)
    (bank : EndToEndLeftFamilyReceiverBank A package move)
    (member : Bool) (source : EndToEndRecurrentRightMacro A package)
    (hpending : (bank member).2.2 = some source) :
    endToEndLeftFamilyBankPendingRightRoot? A package move bank member =
      some (endToEndRightRestartRootOfPending A package source) := by
  simp [endToEndLeftFamilyBankPendingRightRoot?, hpending]

/-! ## The alternating refresh equations -/

/-- Refresh the two right-family roots from the post-step right and left
receiver banks.  Missing staging is represented honestly by `none`. -/
noncomputable def endToEndNextRightFamilyRoots?
    (pastAnchor : Bool)
    (rightMove : EndToEndRightFamilyPairMove A package)
    (rightBank : EndToEndRightFamilyReceiverBank A package rightMove)
    (leftMove : EndToEndLeftFamilyPairMove A package)
    (leftBank : EndToEndLeftFamilyReceiverBank A package leftMove) :
    Bool → Option (EndToEndRightRestartRoot A package)
  | false => some
      (endToEndRightFamilyBankCurrentRoot A package rightMove rightBank
        pastAnchor)
  | true => endToEndLeftFamilyBankPendingRightRoot? A package leftMove
      leftBank (!pastAnchor)

/-- Refresh the two left-family roots.  The complementary member convention
is the same one used by the physical left receiver-bank output. -/
noncomputable def endToEndNextLeftFamilyRoots?
    (pastAnchor : Bool)
    (rightMove : EndToEndRightFamilyPairMove A package)
    (rightBank : EndToEndRightFamilyReceiverBank A package rightMove)
    (leftMove : EndToEndLeftFamilyPairMove A package)
    (leftBank : EndToEndLeftFamilyReceiverBank A package leftMove) :
    Bool → Option (EndToEndLeftRestartRoot A package)
  | false => some
      (endToEndLeftFamilyBankCurrentRoot A package leftMove leftBank
        (!pastAnchor))
  | true => endToEndRightFamilyBankPendingLeftRoot? A package rightMove
      rightBank pastAnchor

section
omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]

@[simp] theorem endToEndNextRightFamilyRoots?_false
    (pastAnchor : Bool)
    (rightMove : EndToEndRightFamilyPairMove A package)
    (rightBank : EndToEndRightFamilyReceiverBank A package rightMove)
    (leftMove : EndToEndLeftFamilyPairMove A package)
    (leftBank : EndToEndLeftFamilyReceiverBank A package leftMove) :
    endToEndNextRightFamilyRoots? A package pastAnchor rightMove rightBank
        leftMove leftBank false =
      some (endToEndRightFamilyBankCurrentRoot A package rightMove rightBank
        pastAnchor) :=
  rfl

@[simp] theorem endToEndNextRightFamilyRoots?_true
    (pastAnchor : Bool)
    (rightMove : EndToEndRightFamilyPairMove A package)
    (rightBank : EndToEndRightFamilyReceiverBank A package rightMove)
    (leftMove : EndToEndLeftFamilyPairMove A package)
    (leftBank : EndToEndLeftFamilyReceiverBank A package leftMove) :
    endToEndNextRightFamilyRoots? A package pastAnchor rightMove rightBank
        leftMove leftBank true =
      endToEndLeftFamilyBankPendingRightRoot? A package leftMove leftBank
        (!pastAnchor) :=
  rfl

@[simp] theorem endToEndNextLeftFamilyRoots?_false
    (pastAnchor : Bool)
    (rightMove : EndToEndRightFamilyPairMove A package)
    (rightBank : EndToEndRightFamilyReceiverBank A package rightMove)
    (leftMove : EndToEndLeftFamilyPairMove A package)
    (leftBank : EndToEndLeftFamilyReceiverBank A package leftMove) :
    endToEndNextLeftFamilyRoots? A package pastAnchor rightMove rightBank
        leftMove leftBank false =
      some (endToEndLeftFamilyBankCurrentRoot A package leftMove leftBank
        (!pastAnchor)) :=
  rfl

@[simp] theorem endToEndNextLeftFamilyRoots?_true
    (pastAnchor : Bool)
    (rightMove : EndToEndRightFamilyPairMove A package)
    (rightBank : EndToEndRightFamilyReceiverBank A package rightMove)
    (leftMove : EndToEndLeftFamilyPairMove A package)
    (leftBank : EndToEndLeftFamilyReceiverBank A package leftMove) :
    endToEndNextLeftFamilyRoots? A package pastAnchor rightMove rightBank
        leftMove leftBank true =
      endToEndRightFamilyBankPendingLeftRoot? A package rightMove rightBank
        pastAnchor :=
  rfl

end

/-! The semantic `some` branches used at a real strict close. -/

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
theorem endToEndNextRightFamilyRoots?_true_of_pending
    (pastAnchor : Bool)
    (rightMove : EndToEndRightFamilyPairMove A package)
    (rightBank : EndToEndRightFamilyReceiverBank A package rightMove)
    (leftMove : EndToEndLeftFamilyPairMove A package)
    (leftBank : EndToEndLeftFamilyReceiverBank A package leftMove)
    (source : EndToEndRecurrentRightMacro A package)
    (hpending : (leftBank (!pastAnchor)).2.2 = some source) :
    endToEndNextRightFamilyRoots? A package pastAnchor rightMove rightBank
        leftMove leftBank true =
      some (endToEndRightRestartRootOfPending A package source) := by
  simp [hpending]

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
theorem endToEndNextLeftFamilyRoots?_true_of_pending
    (pastAnchor : Bool)
    (rightMove : EndToEndRightFamilyPairMove A package)
    (rightBank : EndToEndRightFamilyReceiverBank A package rightMove)
    (leftMove : EndToEndLeftFamilyPairMove A package)
    (leftBank : EndToEndLeftFamilyReceiverBank A package leftMove)
    (source : EndToEndRecurrentLeftMacro A package)
    (hpending : (rightBank pastAnchor).2.2 = some source) :
    endToEndNextLeftFamilyRoots? A package pastAnchor rightMove rightBank
        leftMove leftBank true =
      some (endToEndLeftRestartRootOfPending A package source) := by
  simp [hpending]

end

end DetParityAutomaton

end DistributedSynthesis
