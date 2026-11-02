/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteCrossAnchorPairTable

/-!
# Reachable suffixes of a finite cross-anchor table

A preselected cross-anchor member is known to win from its constructed
initial state.  The only sound state-level continuation principle is
therefore the reachable one: at a finite cut of the induced play, restart
the base monitor at the state reached by that play.  No claim is made about
an arbitrary, possibly unreachable, controller or monitor state.
-/

namespace DistributedSynthesis

universe u v x y w

noncomputable section

variable {RIn : Type u} {SIn : Type v} {ROut : Type x} {SOut : Type y}
variable [Inhabited RIn] [Inhabited SIn] [Inhabited ROut]
variable [Fintype RIn] [Fintype SIn] [Fintype ROut] [Fintype SOut]
variable [DecidableEq RIn] [DecidableEq SIn]

omit [Inhabited RIn] [Inhabited SIn] [Inhabited ROut] in
/-- Every physical continuation reached in a member of a preselected table
still wins the base monitor restarted at the state reached at the cut. -/
theorem FiniteCrossAnchorFirstTwoTable.memberController_base_wins_suffix
    {base : Bool → BlockRecordMonitor.{u, v, x, y, w}
      RIn SIn ROut SOut}
    {start : ∀ anchor, (base anchor).State}
    {firstAllowed : ∀ anchor,
      RealizedBlockRound RIn SIn ROut SOut → Bool}
    {secondAllowed : ∀ anchor,
      RealizedBlockRound RIn SIn ROut SOut →
        RealizedBlockRound RIn SIn ROut SOut → Bool}
    (table : FiniteCrossAnchorFirstTwoTable base start firstAllowed
      secondAllowed)
    (anchor : Bool) (env : Nat → RIn × SIn) (cut : Nat) :
    let restarted := finiteCrossAnchorRestartFamily base start anchor
    let guard := finiteCrossAnchorFirstTwoGuardFamily base start firstAllowed
      secondAllowed anchor
    let controller := table.memberController anchor
    let play := treePlay
      (narrowedInducedTree guard controller.labeledTree) env
    (restarted.restartAt (restarted.run play cut)).WinsPlay
      (fun k ↦ play (cut + k)) := by
  let restarted := finiteCrossAnchorRestartFamily base start anchor
  let guard := finiteCrossAnchorFirstTwoGuardFamily base start firstAllowed
    secondAllowed anchor
  let controller := table.memberController anchor
  let play := treePlay
    (narrowedInducedTree guard controller.labeledTree) env
  exact restarted.restartAt_wins_suffix play cut
    (table.memberController_base_wins anchor env)

end

end DistributedSynthesis
