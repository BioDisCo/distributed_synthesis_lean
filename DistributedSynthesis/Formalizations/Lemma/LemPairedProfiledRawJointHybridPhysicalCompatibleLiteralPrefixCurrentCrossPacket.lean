/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleLiteralPrefixCurrent

/-!
# Exact cross-occurrence packet for recurring literal-prefix tables

The retained coordinate of an old strict block and the initial informed
coordinate of the freshly entered block are generated from two presentations
of the same local history.  This file first records that dangerous equation
directly for the concrete semantic child used by the raw-joint transition.

The equations are strategy-level local-view identities.  They use no graph,
hierarchy, leader, or strict-leader observation and no acceptance assumption.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

section

variable [Inhabited In₁] [Inhabited In₂]

/-- The concrete right-to-left semantic child satisfies the exact boundary
profile equation.  This is the raw dangerous right/left seam. -/
theorem profiledRawRightSemanticChildPair_boundaryProfile
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (member : ProcOnePairedEntryRep strategy × A.State)
    (row : PairedEntryRow) (past : List (In₂ × In₁))
    (move : In₂ × In₁) :
    rightClosingProfile member.1.lambdaOfStrategy row past move =
      leftInitialFirstProfile
        (profiledRawRightSemanticChildPair A member row past move).1.lambdaOfStrategy := by
  simpa [profiledRawRightSemanticChildPair, procTwoViewClassChild] using
    (rightClosingProfile_lambdaOfStrategy strategy member.1 row past move)

/-- Mirror exact seam for a left block entering a fresh right block. -/
theorem profiledRawLeftSemanticChildPair_boundaryProfile
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (member : ProcTwoPairedEntryRep strategy × A.State)
    (row : PairedEntryRow) (past : List (In₁ × In₂))
    (move : In₁ × In₂) :
    leftClosingProfile member.1.lambdaOfStrategy row past move =
      rightInitialFirstProfile
        (profiledRawLeftSemanticChildPair A member row past move).1.lambdaOfStrategy := by
  simpa [profiledRawLeftSemanticChildPair, procOneViewClassChild] using
    (leftClosingProfile_lambdaOfStrategy strategy member.1 row past move)

/-! ## Exact audit of the old Tail's hard-coded `.both` projection -/

/-- Replacing the fresh `.first` profile in the right-to-left boundary law by
the fresh `.both` profile is equivalent to a new equality between the two
entry-row profiles of the child.  The boundary theorem does not supply this
extra equality. -/
theorem profiledRawRightSemanticChildPair_tailBoth_iff_rows_eq
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (member : ProcOnePairedEntryRep strategy × A.State)
    (row : PairedEntryRow) (past : List (In₂ × In₁))
    (move : In₂ × In₁) :
    let child := profiledRawRightSemanticChildPair A member row past move
    rightClosingProfile member.1.lambdaOfStrategy row past move =
        child.1.lambdaOfStrategy.informedBoth [] ↔
      leftInitialFirstProfile child.1.lambdaOfStrategy =
        child.1.lambdaOfStrategy.informedBoth [] := by
  dsimp only
  rw [profiledRawRightSemanticChildPair_boundaryProfile A strategy member row
    past move]

/-- Mirror diagnosis: the old Tail's fresh-right `.both` request needs an
additional equality between the child's `.first` and `.both` profiles. -/
theorem profiledRawLeftSemanticChildPair_tailBoth_iff_rows_eq
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (member : ProcTwoPairedEntryRep strategy × A.State)
    (row : PairedEntryRow) (past : List (In₁ × In₂))
    (move : In₁ × In₂) :
    let child := profiledRawLeftSemanticChildPair A member row past move
    leftClosingProfile member.1.lambdaOfStrategy row past move =
        child.1.lambdaOfStrategy.informedBoth [] ↔
      rightInitialFirstProfile child.1.lambdaOfStrategy =
        child.1.lambdaOfStrategy.informedBoth [] := by
  dsimp only
  rw [profiledRawLeftSemanticChildPair_boundaryProfile A strategy member row
    past move]

end

end DetParityAutomaton

end DistributedSynthesis
