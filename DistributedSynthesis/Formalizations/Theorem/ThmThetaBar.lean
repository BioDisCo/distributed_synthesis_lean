/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmOnebitfringe
import DistributedSynthesis.Formalizations.Definition.DefPathSummary
import DistributedSynthesis.Formalizations.Lemma.LemViewinv
import Mathlib.Data.Finset.Card

/-!
# Compatible graph sequences of a blind view

`thetaBar` is the finite set of graph sequences compatible with a
process-one view. It contains the true graph sequence and every graph
sequence of an indistinguishable history. The one-bit fringe bound gives
at most two elements, differing at the last receiving round.
The lemmas establish finiteness and invariance under equality of views.
-/

namespace DistributedSynthesis

universe u v x y s w

variable {In₁ : Type u} {In₂ : Type v}

/-- The blind side's entry-thread coordinate on a process-one view: the finite set
of graph sequences the view is compatible with (`procOneGraphCandidates`). -/
def thetaBar (view : View In₁ In₂ Proc.one) : Finset (List Graph) :=
  ((procOneGraphCandidates view).getD []).toFinset

/-- `θ̄` is finite with at most two elements: the one-bit graph fringe
(`thm:onebitfringe`). -/
theorem thetaBar_card_le_two (view : View In₁ In₂ Proc.one) :
    (thetaBar view).card ≤ 2 := by
  rw [thetaBar]
  cases hc : procOneGraphCandidates view with
  | none => simp
  | some c =>
      have hlen : c.length ≤ 2 := by
        rcases procOneGraphCandidates_shape view c hc with
          ⟨g, rfl⟩ | ⟨pre, post, rfl⟩ <;> simp
      simpa using le_trans (List.toFinset_card_le c) hlen

/-- The true graph sequence of a history lies in the `θ̄` of its process-one
view. -/
theorem graphSequence_mem_thetaBar {Out₁ : Type x} {Out₂ : Type y}
    (h : History In₁ In₂ Graph Out₁ Out₂) :
    History.graphSequence h ∈ thetaBar (currentView Proc.one h) := by
  obtain ⟨c, hc, hmem, _⟩ := procOneGraphCandidates_current h
  rw [thetaBar, hc]
  simpa using hmem

/-- `θ̄` is invariant across histories the blind side cannot distinguish: the
graph sequence of *any* view-equal history lies in the `θ̄` of the view.  This is
the sense in which `θ̄` is exactly what process one determines from its own view,
`b_old` included as the two-element ambiguity. -/
theorem graphSequence_mem_thetaBar_of_view {Out₁ : Type x} {Out₂ : Type y}
    (h h' : History In₁ In₂ Graph Out₁ Out₂)
    (hview : currentView Proc.one h' = currentView Proc.one h) :
    History.graphSequence h' ∈ thetaBar (currentView Proc.one h) := by
  rw [← hview]
  exact graphSequence_mem_thetaBar h'

/-- The process-two mirror of `thetaBar`: the finite set of graph sequences a
process-two view is compatible with (`procTwoGraphCandidates`). -/
def thetaBarTwo (view : View In₁ In₂ Proc.two) : Finset (List Graph) :=
  ((procTwoGraphCandidates view).getD []).toFinset

/-- `thetaBarTwo` is finite with at most two elements (`thm:onebitfringe`,
process two). -/
theorem thetaBarTwo_card_le_two (view : View In₁ In₂ Proc.two) :
    (thetaBarTwo view).card ≤ 2 := by
  rw [thetaBarTwo]
  cases hc : procTwoGraphCandidates view with
  | none => simp
  | some c =>
      have hlen : c.length ≤ 2 := by
        rcases procTwoGraphCandidates_shape view c hc with
          ⟨g, rfl⟩ | ⟨pre, post, rfl⟩ <;> simp
      simpa using le_trans (List.toFinset_card_le c) hlen

/-- The true graph sequence of a history lies in the `θ̄` of its process-two
view. -/
theorem graphSequence_mem_thetaBarTwo {Out₁ : Type x} {Out₂ : Type y}
    (h : History In₁ In₂ Graph Out₁ Out₂) :
    History.graphSequence h ∈ thetaBarTwo (currentView Proc.two h) := by
  obtain ⟨c, hc, hmem, _⟩ := procTwoGraphCandidates_current h
  rw [thetaBarTwo, hc]
  simpa using hmem

/-! ### `cor:blindcrossreading` at the view/θ̄ level

This is the genuine crux of the G★ construction.  Fix a round at which the blind
sender (say process one) faces a `right` round out of an old `left`-block whose
acknowledgement bit `b_old` it has not resolved.  Process one cannot distinguish
its two blind continuations:

* (a) the old block *closes* at the successor boundary and a fresh no-direct
  `right`-block opens there, process one the subordinate sender; and
* (b) the old block *directly reverses*, process one the blind sender of the
  reversed `right`-block.

The two continuations differ only in the pending graph bit at process one's last
receive round -- `left` (case a: the partner did not receive) versus `both`
(case b: it did) -- followed by a shared run of `right` rounds in which process
one only sends and never receives.  By `lem:viewinv` (`viewinv_procOne`, already
proved) process one's *view* is then literally identical along both
continuations at every later round; the graph bit that separates "closed then
reopened" from "reversed" is exactly the single pending ambiguity `b_old` of
`thm:onebitfringe`, which process one never observes.

Its `θ̄` coordinate, being a function of the view, is therefore identical, and any
`θ̄`-indexed (indeed any view-indexed) blind table reads the *same* value along
both continuations.  This is `cor:blindcrossreading`: the successor-boundary
subordinate table of case (a) and the reversed-block blind table of case (b) are
one and the same `t_{θ̄}`.  It is what forces the folded commitment to be a single
global `θ̄`-family (`rem:globalblindtable`): the paired arena atoms differ in
`A_φ` state -- the wall no plan-family fold crosses -- yet process one's *view*,
and hence its `θ̄`, does not.  The heavy content is the pre-existing view
invariance `viewinv_procOne`; here it is relocated onto the `θ̄` coordinate the
summary-level fold consumes. -/

/-- `cor:blindcrossreading`, `θ̄` level (process one): the `θ̄` coordinate is
identical across the reversal indistinguishability (the `left`-vs-`both` pending
bit followed by a shared run of `right` rounds). -/
theorem thetaBar_crossReading_procOne {Out₁ : Type x} {Out₂ : Type y}
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (rLeft rBoth : RoundRecord In₁ In₂ Graph Out₁ Out₂)
    (suffix : History In₁ In₂ Graph Out₁ Out₂)
    (hinputOne : rLeft.inputOne = rBoth.inputOne)
    (hinputTwo : rLeft.inputTwo = rBoth.inputTwo)
    (hleft : rLeft.graph = .left)
    (hboth : rBoth.graph = .both)
    (hsuffix : suffix.Forall (fun r => r.graph = .right))
    (n : Nat) :
    thetaBar (currentView Proc.one (History.append h rLeft ++ suffix.take n)) =
      thetaBar (currentView Proc.one (History.append h rBoth ++ suffix.take n)) :=
  congrArg thetaBar
    (viewinv_procOne h rLeft rBoth suffix hinputOne hinputTwo hleft hboth hsuffix n)

/-- `cor:blindcrossreading`, `θ̄` level (process two): the orientation mirror,
the `right`-vs-`both` pending bit followed by a shared run of `left` rounds. -/
theorem thetaBar_crossReading_procTwo {Out₁ : Type x} {Out₂ : Type y}
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (rRight rBoth : RoundRecord In₁ In₂ Graph Out₁ Out₂)
    (suffix : History In₁ In₂ Graph Out₁ Out₂)
    (hinputOne : rRight.inputOne = rBoth.inputOne)
    (hinputTwo : rRight.inputTwo = rBoth.inputTwo)
    (hright : rRight.graph = .right)
    (hboth : rBoth.graph = .both)
    (hsuffix : suffix.Forall (fun r => r.graph = .left))
    (n : Nat) :
    thetaBarTwo (currentView Proc.two (History.append h rRight ++ suffix.take n)) =
      thetaBarTwo (currentView Proc.two (History.append h rBoth ++ suffix.take n)) :=
  congrArg thetaBarTwo
    (viewinv_procTwo h rRight rBoth suffix hinputOne hinputTwo hright hboth hsuffix n)

/-- `cor:blindcrossreading`, table level (process one): any view-indexed (hence
`θ̄`-indexed) blind table `t` emits the *same* value along both continuations.
This is the paper's conclusion that the output process one emits is the same
`t_{θ̄}(w)` in cases (a) and (b). -/
theorem blindTable_crossReading_procOne {Out₁ : Type x} {Out₂ : Type y} {X : Type w}
    (t : View In₁ In₂ Proc.one → X)
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (rLeft rBoth : RoundRecord In₁ In₂ Graph Out₁ Out₂)
    (suffix : History In₁ In₂ Graph Out₁ Out₂)
    (hinputOne : rLeft.inputOne = rBoth.inputOne)
    (hinputTwo : rLeft.inputTwo = rBoth.inputTwo)
    (hleft : rLeft.graph = .left)
    (hboth : rBoth.graph = .both)
    (hsuffix : suffix.Forall (fun r => r.graph = .right))
    (n : Nat) :
    t (currentView Proc.one (History.append h rLeft ++ suffix.take n)) =
      t (currentView Proc.one (History.append h rBoth ++ suffix.take n)) :=
  congrArg t
    (viewinv_procOne h rLeft rBoth suffix hinputOne hinputTwo hleft hboth hsuffix n)

/-- `cor:blindcrossreading`, table level (process two): the orientation mirror. -/
theorem blindTable_crossReading_procTwo {Out₁ : Type x} {Out₂ : Type y} {X : Type w}
    (t : View In₁ In₂ Proc.two → X)
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (rRight rBoth : RoundRecord In₁ In₂ Graph Out₁ Out₂)
    (suffix : History In₁ In₂ Graph Out₁ Out₂)
    (hinputOne : rRight.inputOne = rBoth.inputOne)
    (hinputTwo : rRight.inputTwo = rBoth.inputTwo)
    (hright : rRight.graph = .right)
    (hboth : rBoth.graph = .both)
    (hsuffix : suffix.Forall (fun r => r.graph = .left))
    (n : Nat) :
    t (currentView Proc.two (History.append h rRight ++ suffix.take n)) =
      t (currentView Proc.two (History.append h rBoth ++ suffix.take n)) :=
  congrArg t
    (viewinv_procTwo h rRight rBoth suffix hinputOne hinputTwo hright hboth hsuffix n)

/-! ### The `A_φ`-entry projection

`θ̄` above is a set of graph sequences; the boundary game is coordinatized by the
`A_φ`-entry `A.State`.  Because the blind side stores inputs and receives outputs
but does not observe the graph beyond `b_old`, the entry it faces is determined by
its own input/output context together with one of the (at most two) compatible
graph sequences.  `thetaBarEntries` runs `A_φ` over that context under each
compatible graph sequence; it is the blind side's entry-state ambiguity and, by
`thm:onebitfringe`, has at most two elements.  The context is a parameter (the
entry is play-relative: the `View` carries inputs, not outputs). -/

namespace DetParityAutomaton

variable {Out₁ : Type x} {Out₂ : Type y}
variable {A :
    DetParityAutomaton.{max u v x y, s} (RoundRecord In₁ In₂ Graph Out₁ Out₂)}

/-- Run `A_φ` over a record sequence to its entry state. -/
def entryState (records : List (RoundRecord In₁ In₂ Graph Out₁ Out₂)) : A.State :=
  records.foldl A.step A.initial

/-- Rebuild a record sequence with a given graph sequence, keeping the
inputs and outputs. -/
def withGraphs (records : List (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (gs : List Graph) : List (RoundRecord In₁ In₂ Graph Out₁ Out₂) :=
  List.zipWith (fun r g => { r with graph := g }) records gs

/-- The blind side's entry-state ambiguity: `θ̄`'s graph sequences run through
`A_φ` at a fixed input/output context. -/
def thetaBarEntries [DecidableEq A.State] (view : View In₁ In₂ Proc.one)
    (records : List (RoundRecord In₁ In₂ Graph Out₁ Out₂)) : Finset A.State :=
  (thetaBar view).image (fun gs => entryState (A := A) (withGraphs records gs))

/-- The entry-state ambiguity is finite with at most two elements: the
`A_φ`-image of the one-bit graph fringe. -/
theorem thetaBarEntries_card_le_two [DecidableEq A.State]
    (view : View In₁ In₂ Proc.one)
    (records : List (RoundRecord In₁ In₂ Graph Out₁ Out₂)) :
    (thetaBarEntries (A := A) view records).card ≤ 2 :=
  le_trans (Finset.card_image_le) (thetaBar_card_le_two view)

/-- Rebuilding a history's records with its own graph sequence is the identity. -/
theorem withGraphs_graphSequence (h : History In₁ In₂ Graph Out₁ Out₂) :
    withGraphs h (History.graphSequence h) = h := by
  induction h with
  | nil => rfl
  | cons r rest ih =>
      simp only [withGraphs, History.graphSequence, List.map_cons,
        List.zipWith_cons_cons] at ih ⊢
      rw [ih]

/-- The true entry of a play lies in the blind side's `θ̄`-entry ambiguity set: the
entry process one actually faces is one of the (at most two) it cannot rule out. -/
theorem entryState_mem_thetaBarEntries [DecidableEq A.State]
    (h : History In₁ In₂ Graph Out₁ Out₂) :
    entryState (A := A) h ∈ thetaBarEntries (A := A) (currentView Proc.one h) h := by
  rw [thetaBarEntries, Finset.mem_image]
  exact ⟨History.graphSequence h, graphSequence_mem_thetaBar h,
    by rw [withGraphs_graphSequence]⟩

end DetParityAutomaton

end DistributedSynthesis
