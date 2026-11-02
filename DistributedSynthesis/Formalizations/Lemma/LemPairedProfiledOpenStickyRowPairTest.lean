/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenRowEqualityPattern
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenWitnessedReanchoredRowProjection

/-!
# Fail-fast sticky-row pair test

The two values of `PairedEntryRow` are proof-side alternatives.  A process
must never select between them by observing a strict leader or an orientation.
This file tests the only safe merge: two row alternatives may be represented
by one receiver-local state only when the literal receiver behavior agrees.

For a genuine two-member family, the existing finite cross-row matrix is not
merely a width summary.  Together with the common blind view, it implies
equality of both old local views.  Hence it forces equality of the *complete*
raw receiver strategies, including the mixed `.first`/`.both` case.  On one
lineage the two rows are never merged: `other_view_ne` makes the corresponding
matrix test false.

No leader, orientation, row uniqueness, or eventual recovery premise occurs
in these statements.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
  [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

/-! ## The matrix is the exact old receiver-view test -/

/-- The process-one-family matrix exactly decides equality of the old
process-two views, including mixed rows. -/
theorem procOneFamilyCrossRowEquivalent_iff_otherView_eq
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (entry : Bool → ProcOnePairedEntryRep strategy)
    (left right : Bool × PairedEntryRow) :
    pairedCrossRowEquivalent
          (procOneFamilyCrossRowEqualityPattern strategy entry) left right =
        true ↔
      currentView Proc.two (procOneViewClassRowHistory entry left) =
        currentView Proc.two (procOneViewClassRowHistory entry right) := by
  rcases left with ⟨leftMember, leftRow⟩
  rcases right with ⟨rightMember, rightRow⟩
  cases leftMember <;> cases rightMember <;> cases leftRow <;> cases rightRow
  <;> simp [pairedCrossRowEquivalent, procOneFamilyCrossRowEqualityPattern,
    procOneViewClassRowHistory, eq_comm, (entry false).other_view_ne,
    (entry true).other_view_ne]

/-- Process-two-family mirror. -/
theorem procTwoFamilyCrossRowEquivalent_iff_otherView_eq
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (entry : Bool → ProcTwoPairedEntryRep strategy)
    (left right : Bool × PairedEntryRow) :
    pairedCrossRowEquivalent
          (procTwoFamilyCrossRowEqualityPattern strategy entry) left right =
        true ↔
      currentView Proc.one (procTwoViewClassRowHistory entry left) =
        currentView Proc.one (procTwoViewClassRowHistory entry right) := by
  rcases left with ⟨leftMember, leftRow⟩
  rcases right with ⟨rightMember, rightRow⟩
  cases leftMember <;> cases rightMember <;> cases leftRow <;> cases rightRow
  <;> simp [pairedCrossRowEquivalent, procTwoFamilyCrossRowEqualityPattern,
    procTwoViewClassRowHistory, eq_comm, (entry false).other_view_ne,
    (entry true).other_view_ne]

/-! ## The dangerous mixed-row pair is behavior homogeneous -/

/-- If two right-block rows lie in the same finite cross-row class, their
complete process-two receiver strategies coincide.  The rows may be
`.first` and `.both`; they need not be equal. -/
theorem procOneFamily_rightReceiver_eq_of_crossRowEquivalent
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (entry : Bool → ProcOnePairedEntryRep strategy)
    (hblind : ∀ left right,
      currentView Proc.one (entry left).leftHistory =
        currentView Proc.one (entry right).leftHistory)
    (left right : Bool × PairedEntryRow)
    (hcross : pairedCrossRowEquivalent
      (procOneFamilyCrossRowEqualityPattern strategy entry) left right = true) :
    procOnePairedEntryRightReceiverForRow strategy (entry left.1) left.2 =
      procOnePairedEntryRightReceiverForRow strategy (entry right.1) right.2 := by
  have hone := procOneViewClassRowHistory_blind_eq entry hblind left right
  have htwo :=
    (procOneFamilyCrossRowEquivalent_iff_otherView_eq strategy entry left
      right).mp hcross
  have hreceiver := blockReceiverTwo_eq_of_currentViews_eq strategy
    (procOneViewClassRowHistory entry left)
    (procOneViewClassRowHistory entry right) hone htwo
  rcases left with ⟨leftMember, leftRow⟩
  rcases right with ⟨rightMember, rightRow⟩
  cases leftRow <;> cases rightRow <;>
    simpa [procOnePairedEntryRightReceiverForRow,
      procOneViewClassRowHistory] using hreceiver

/-- Left-block mirror. -/
theorem procTwoFamily_leftReceiver_eq_of_crossRowEquivalent
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (entry : Bool → ProcTwoPairedEntryRep strategy)
    (hblind : ∀ left right,
      currentView Proc.two (entry left).rightHistory =
        currentView Proc.two (entry right).rightHistory)
    (left right : Bool × PairedEntryRow)
    (hcross : pairedCrossRowEquivalent
      (procTwoFamilyCrossRowEqualityPattern strategy entry) left right = true) :
    procTwoPairedEntryLeftReceiverForRow strategy (entry left.1) left.2 =
      procTwoPairedEntryLeftReceiverForRow strategy (entry right.1) right.2 := by
  have htwo := procTwoViewClassRowHistory_blind_eq entry hblind left right
  have hone :=
    (procTwoFamilyCrossRowEquivalent_iff_otherView_eq strategy entry left
      right).mp hcross
  have hreceiver := blockReceiverOne_eq_of_currentViews_eq strategy
    (procTwoViewClassRowHistory entry left)
    (procTwoViewClassRowHistory entry right) hone htwo
  rcases left with ⟨leftMember, leftRow⟩
  rcases right with ⟨rightMember, rightRow⟩
  cases leftRow <;> cases rightRow <;>
    simpa [procTwoPairedEntryLeftReceiverForRow,
      procTwoViewClassRowHistory] using hreceiver

/-- In particular, a single process-one lineage can never put its `.first`
and `.both` rows in one receiver-view class. -/
theorem procOneFamily_first_both_not_crossRowEquivalent
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (entry : Bool → ProcOnePairedEntryRep strategy) (member : Bool) :
    pairedCrossRowEquivalent
      (procOneFamilyCrossRowEqualityPattern strategy entry)
      (member, .first) (member, .both) = false := by
  cases member <;> rfl

/-- Process-two mirror. -/
theorem procTwoFamily_first_both_not_crossRowEquivalent
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (entry : Bool → ProcTwoPairedEntryRep strategy) (member : Bool) :
    pairedCrossRowEquivalent
      (procTwoFamilyCrossRowEqualityPattern strategy entry)
      (member, .first) (member, .both) = false := by
  cases member <;> rfl

end

end DetParityAutomaton

end DistributedSynthesis
