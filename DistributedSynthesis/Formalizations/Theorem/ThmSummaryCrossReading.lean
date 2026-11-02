/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmThetaBar
import DistributedSynthesis.Formalizations.Theorem.ThmLocalSummaryAutomaton

/-!
# `cor:blindcrossreading` at the summary level

The θ̄-fold of `prop:starcomplete` cannot live on the arena plan family: the two
boundaries it must reconcile -- the successor `bcand = oneBothSuccessor …` and the
opening `atom` -- are *different* `A_φ` states, and θ̄ refines the `A_φ` state, so
no atom-indexed blind table can agree at both.  The agreement holds only because
process one's *view*, hence its θ̄, is identical at the two continuations
(`cor:blindcrossreading`).  The fold therefore belongs at the **summary** level,
where the blind side keys on what it computes from its own view.

A `LocalSummaryAutomaton` summary is exactly that: `read : View → Summary` folds a
process's view increments (`def:views`) into a finite state the process computes
from its own view alone.  This file is the bridge: because `read` is a function of
the view, the proved view-level `cor:blindcrossreading`
(`blindTable_crossReading_procOne`/`_procTwo`) applies verbatim with `t := M.read`,
so the summary -- and hence *any* summary-indexed blind table -- is identical
across the reversal indistinguishability (a `left`-vs-`both` pending bit `b_old`
followed by a shared run of `right` rounds in which process one only sends).  This
is the summary-level statement a θ̄(=summary)-indexed realizing fold needs at the
matched pair `(bcand, atom)`; the remaining play↔history correspondence identifies
those atoms' summaries with `read` of these two views.
-/

namespace DistributedSynthesis

universe u v x y o z

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}

namespace LocalSummaryAutomaton

/-- Process one's summary is invariant across the reversal indistinguishability:
the finite state it reads from its own view is the same whether the old block
closed (`both`) or directly reversed (`left`), followed by a shared run of `right`
rounds it only sends on.  Immediate from the view-level `cor:blindcrossreading`
(`blindTable_crossReading_procOne`) applied to `t := M.read`, since `read` is a
function of the view. -/
theorem read_crossReading_procOne
    (M : LocalSummaryAutomaton.{u, v, o} In₁ In₂)
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (rLeft rBoth : RoundRecord In₁ In₂ Graph Out₁ Out₂)
    (suffix : History In₁ In₂ Graph Out₁ Out₂)
    (hinputOne : rLeft.inputOne = rBoth.inputOne)
    (hinputTwo : rLeft.inputTwo = rBoth.inputTwo)
    (hleft : rLeft.graph = .left)
    (hboth : rBoth.graph = .both)
    (hsuffix : suffix.Forall (fun r => r.graph = .right))
    (n : Nat) :
    M.read (currentView Proc.one (History.append h rLeft ++ suffix.take n)) =
      M.read (currentView Proc.one (History.append h rBoth ++ suffix.take n)) :=
  blindTable_crossReading_procOne (fun view : View In₁ In₂ Proc.one => M.read view)
    h rLeft rBoth suffix hinputOne hinputTwo hleft hboth hsuffix n

/-- Process two's summary is invariant across the orientation-mirror reversal
indistinguishability: a `right`-vs-`both` pending bit followed by a shared run of
`left` rounds.  The mirror of `read_crossReading_procOne`. -/
theorem read_crossReading_procTwo
    (M : LocalSummaryAutomaton.{u, v, o} In₁ In₂)
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (rRight rBoth : RoundRecord In₁ In₂ Graph Out₁ Out₂)
    (suffix : History In₁ In₂ Graph Out₁ Out₂)
    (hinputOne : rRight.inputOne = rBoth.inputOne)
    (hinputTwo : rRight.inputTwo = rBoth.inputTwo)
    (hright : rRight.graph = .right)
    (hboth : rBoth.graph = .both)
    (hsuffix : suffix.Forall (fun r => r.graph = .left))
    (n : Nat) :
    M.read (currentView Proc.two (History.append h rRight ++ suffix.take n)) =
      M.read (currentView Proc.two (History.append h rBoth ++ suffix.take n)) :=
  blindTable_crossReading_procTwo (fun view : View In₁ In₂ Proc.two => M.read view)
    h rRight rBoth suffix hinputOne hinputTwo hright hboth hsuffix n

/-! ### The summary-indexed blind table agrees by construction

The impasse of the plan-family route is isolated at `foldθ_leftTrace`: its
`hagree` demands that a blind table read at the successor boundary's control and
at the opening boundary's control coincide word-for-word, and those two
plan-internal controls *differ*, so `hagree` is met only by a constant table
(the `globalFold` degeneracy).  The resolution is to index the blind table not on
the plan control but on the process's own **summary** `M.read view`: across the
reversal indistinguishability the two continuations give process one the *same*
view, hence the same summary, so *any* summary-indexed table -- constant or not --
emits the same value.  The obligation moves from "the two controls are equal"
(false) to "the two summaries are equal" (true, `read_crossReading_procOne`).
This is `cor:blindcrossreading` at the level where the realizing fold consumes it. -/

/-- A summary-indexed blind table of process one emits the same value along both
reversal continuations.  Immediate from `read_crossReading_procOne`, since the
table factors through the summary and the summary is `b_old`-invariant.  With
`Y := In₁ → Out₁` this is the `hagree`-shaped agreement a summary-indexed fold
needs, provable because it factors through the equal summary rather than through
the unequal plan controls. -/
theorem blindSummaryTable_crossReading_procOne {Y : Type z}
    (M : LocalSummaryAutomaton.{u, v, o} In₁ In₂)
    (b : M.Summary Proc.one → Y)
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (rLeft rBoth : RoundRecord In₁ In₂ Graph Out₁ Out₂)
    (suffix : History In₁ In₂ Graph Out₁ Out₂)
    (hinputOne : rLeft.inputOne = rBoth.inputOne)
    (hinputTwo : rLeft.inputTwo = rBoth.inputTwo)
    (hleft : rLeft.graph = .left)
    (hboth : rBoth.graph = .both)
    (hsuffix : suffix.Forall (fun r => r.graph = .right))
    (n : Nat) :
    b (M.read (currentView Proc.one (History.append h rLeft ++ suffix.take n))) =
      b (M.read (currentView Proc.one (History.append h rBoth ++ suffix.take n))) :=
  congrArg b
    (read_crossReading_procOne M h rLeft rBoth suffix hinputOne hinputTwo hleft hboth
      hsuffix n)

/-- The orientation mirror of `blindSummaryTable_crossReading_procOne`. -/
theorem blindSummaryTable_crossReading_procTwo {Y : Type z}
    (M : LocalSummaryAutomaton.{u, v, o} In₁ In₂)
    (b : M.Summary Proc.two → Y)
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (rRight rBoth : RoundRecord In₁ In₂ Graph Out₁ Out₂)
    (suffix : History In₁ In₂ Graph Out₁ Out₂)
    (hinputOne : rRight.inputOne = rBoth.inputOne)
    (hinputTwo : rRight.inputTwo = rBoth.inputTwo)
    (hright : rRight.graph = .right)
    (hboth : rBoth.graph = .both)
    (hsuffix : suffix.Forall (fun r => r.graph = .left))
    (n : Nat) :
    b (M.read (currentView Proc.two (History.append h rRight ++ suffix.take n))) =
      b (M.read (currentView Proc.two (History.append h rBoth ++ suffix.take n))) :=
  congrArg b
    (read_crossReading_procTwo M h rRight rBoth suffix hinputOne hinputTwo hright hboth
      hsuffix n)

end LocalSummaryAutomaton

end DistributedSynthesis
