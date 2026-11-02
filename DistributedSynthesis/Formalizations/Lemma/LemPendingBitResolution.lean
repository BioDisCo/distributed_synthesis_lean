/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemEntryThreadClass

/-!
# The pending acknowledgement bit is replaced at the next receive

`LemViewinv` proves that changing a receive round from the one-way graph to
`both` is invisible to the receiver throughout the following block in which
that process does not receive.  This file proves the complementary fact needed
by a Bérard-style overlapping-lambda decomposition: the old ambiguity is
resolved at that process's next receive.

Thus the raw local-view ambiguity is genuinely *replace-not-accumulate*.
During the intervening opposite block there are the two old variants; at its
closing receive those variants give different received partner views, so the
old bit is known before the new receive round can introduce its own fresh bit.

This is a structural theorem about full views, independent of an objective or
strategy.  It does not by itself prove that a rational journal controller
preserves local consistency; the remaining automata step is to encode the
resulting one-transition overlap in the strategy-tree label.
-/

namespace DistributedSynthesis

universe u v x y

/-- Inequality of process-two views is preserved while process two receives
through a common suffix of `right` rounds. -/
theorem procTwo_ne_preserved_by_right_suffix
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (h₁ h₂ : History In₁ In₂ Graph Out₁ Out₂)
    (hne : currentView Proc.two h₁ ≠ currentView Proc.two h₂)
    (suffix : History In₁ In₂ Graph Out₁ Out₂)
    (hsuffix : suffix.Forall (fun r => r.graph = .right)) :
    currentView Proc.two (h₁ ++ suffix) ≠
      currentView Proc.two (h₂ ++ suffix) := by
  induction suffix generalizing h₁ h₂ with
  | nil =>
      simpa using hne
  | cons r suffix ih =>
      have hsplit :
          r.graph = .right ∧ suffix.Forall (fun r => r.graph = .right) := by
        simpa using hsuffix
      have hstep :
          currentView Proc.two (History.append h₁ r) ≠
            currentView Proc.two (History.append h₂ r) := by
        simp only [currentView_two_append, hsplit.1]
        intro heq
        exact hne (View.recv.inj heq).1
      simpa [History.append, List.append_assoc] using
        ih (History.append h₁ r) (History.append h₂ r) hstep hsplit.2

/-- Inequality of process-one views is preserved while process one receives
through a common suffix of `left` rounds. -/
theorem procOne_ne_preserved_by_left_suffix
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (h₁ h₂ : History In₁ In₂ Graph Out₁ Out₂)
    (hne : currentView Proc.one h₁ ≠ currentView Proc.one h₂)
    (suffix : History In₁ In₂ Graph Out₁ Out₂)
    (hsuffix : suffix.Forall (fun r => r.graph = .left)) :
    currentView Proc.one (h₁ ++ suffix) ≠
      currentView Proc.one (h₂ ++ suffix) := by
  induction suffix generalizing h₁ h₂ with
  | nil =>
      simpa using hne
  | cons r suffix ih =>
      have hsplit :
          r.graph = .left ∧ suffix.Forall (fun r => r.graph = .left) := by
        simpa using hsuffix
      have hstep :
          currentView Proc.one (History.append h₁ r) ≠
            currentView Proc.one (History.append h₂ r) := by
        simp only [currentView_one_append, hsplit.1]
        intro heq
        exact hne (View.recv.inj heq).1
      simpa [History.append, List.append_assoc] using
        ih (History.append h₁ r) (History.append h₂ r) hstep hsplit.2

/-- A process-one pending bit (`left` versus `both`) remains hidden during a
`right` block but is resolved when process one next receives on `left`. -/
theorem procOne_left_both_resolved_at_next_left
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (rLeft rBoth : RoundRecord In₁ In₂ Graph Out₁ Out₂)
    (suffix : History In₁ In₂ Graph Out₁ Out₂)
    (next : RoundRecord In₁ In₂ Graph Out₁ Out₂)
    (hleft : rLeft.graph = .left)
    (hboth : rBoth.graph = .both)
    (hsuffix : suffix.Forall (fun r => r.graph = .right))
    (hnext : next.graph = .left) :
    currentView Proc.one
        (History.append (History.append h rLeft ++ suffix) next) ≠
      currentView Proc.one
        (History.append (History.append h rBoth ++ suffix) next) := by
  have htwo :
      currentView Proc.two (History.append h rLeft) ≠
        currentView Proc.two (History.append h rBoth) := by
    simp [currentView_two_append, hleft, hboth]
  have htwoSuffix :=
    procTwo_ne_preserved_by_right_suffix
      (History.append h rLeft) (History.append h rBoth) htwo suffix hsuffix
  simp only [currentView_one_append, hnext]
  intro heq
  exact htwoSuffix (View.recv.inj heq).2.2.1

/-- Symmetric resolution: a process-two pending bit (`right` versus `both`)
is resolved when process two next receives on `right`. -/
theorem procTwo_right_both_resolved_at_next_right
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (rRight rBoth : RoundRecord In₁ In₂ Graph Out₁ Out₂)
    (suffix : History In₁ In₂ Graph Out₁ Out₂)
    (next : RoundRecord In₁ In₂ Graph Out₁ Out₂)
    (hright : rRight.graph = .right)
    (hboth : rBoth.graph = .both)
    (hsuffix : suffix.Forall (fun r => r.graph = .left))
    (hnext : next.graph = .right) :
    currentView Proc.two
        (History.append (History.append h rRight ++ suffix) next) ≠
      currentView Proc.two
        (History.append (History.append h rBoth ++ suffix) next) := by
  have hone :
      currentView Proc.one (History.append h rRight) ≠
        currentView Proc.one (History.append h rBoth) := by
    simp [currentView_one_append, hright, hboth]
  have honeSuffix :=
    procOne_ne_preserved_by_left_suffix
      (History.append h rRight) (History.append h rBoth) hone suffix hsuffix
  simp only [currentView_two_append, hnext]
  intro heq
  exact honeSuffix (View.recv.inj heq).2.2.1

/-- Strong replace-not-accumulate form for process one.  The two old variants
remain distinguishable at the next process-one receive even if the two next
round records are themselves different (`left` versus `both` may introduce the
fresh pending bit).  Thus a fresh bit cannot mask or combine with the old one. -/
theorem procOne_old_bit_resolved_despite_fresh_receive
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (rLeft rBoth : RoundRecord In₁ In₂ Graph Out₁ Out₂)
    (suffix : History In₁ In₂ Graph Out₁ Out₂)
    (next₁ next₂ : RoundRecord In₁ In₂ Graph Out₁ Out₂)
    (hleft : rLeft.graph = .left)
    (hboth : rBoth.graph = .both)
    (hsuffix : suffix.Forall (fun r => r.graph = .right))
    (hnext₁ : next₁.graph = .left ∨ next₁.graph = .both)
    (hnext₂ : next₂.graph = .left ∨ next₂.graph = .both) :
    currentView Proc.one
        (History.append (History.append h rLeft ++ suffix) next₁) ≠
      currentView Proc.one
        (History.append (History.append h rBoth ++ suffix) next₂) := by
  have htwo :
      currentView Proc.two (History.append h rLeft) ≠
        currentView Proc.two (History.append h rBoth) := by
    simp [currentView_two_append, hleft, hboth]
  have htwoSuffix :=
    procTwo_ne_preserved_by_right_suffix
      (History.append h rLeft) (History.append h rBoth) htwo suffix hsuffix
  rw [currentView_one_append_recv _ _ hnext₁,
    currentView_one_append_recv _ _ hnext₂]
  intro heq
  exact htwoSuffix (View.recv.inj heq).2.2.1

/-- Symmetric strong replace-not-accumulate theorem for process two. -/
theorem procTwo_old_bit_resolved_despite_fresh_receive
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (rRight rBoth : RoundRecord In₁ In₂ Graph Out₁ Out₂)
    (suffix : History In₁ In₂ Graph Out₁ Out₂)
    (next₁ next₂ : RoundRecord In₁ In₂ Graph Out₁ Out₂)
    (hright : rRight.graph = .right)
    (hboth : rBoth.graph = .both)
    (hsuffix : suffix.Forall (fun r => r.graph = .left))
    (hnext₁ : next₁.graph = .right ∨ next₁.graph = .both)
    (hnext₂ : next₂.graph = .right ∨ next₂.graph = .both) :
    currentView Proc.two
        (History.append (History.append h rRight ++ suffix) next₁) ≠
      currentView Proc.two
        (History.append (History.append h rBoth ++ suffix) next₂) := by
  have hone :
      currentView Proc.one (History.append h rRight) ≠
        currentView Proc.one (History.append h rBoth) := by
    simp [currentView_one_append, hright, hboth]
  have honeSuffix :=
    procOne_ne_preserved_by_left_suffix
      (History.append h rRight) (History.append h rBoth) hone suffix hsuffix
  rw [currentView_two_append_recv _ _ hnext₁,
    currentView_two_append_recv _ _ hnext₂]
  intro heq
  exact honeSuffix (View.recv.inj heq).2.2.1

/-! ### The overlap relation for a switching strategy-tree label -/

/-- Two histories form the process-one overlap of one switching block when
they differ only in the opening `left`/`both` acknowledgement and are followed
by the same (possibly empty) `right` block.  This is the overlap that a
Bérard-style pair of adjacent lambda fragments must identify. -/
def ProcOnePendingOverlap
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (h₁ h₂ : History In₁ In₂ Graph Out₁ Out₂) : Prop :=
  ∃ (base : History In₁ In₂ Graph Out₁ Out₂)
      (rLeft rBoth : RoundRecord In₁ In₂ Graph Out₁ Out₂)
      (suffix : History In₁ In₂ Graph Out₁ Out₂),
    rLeft.inputOne = rBoth.inputOne ∧
      rLeft.inputTwo = rBoth.inputTwo ∧
      rLeft.graph = .left ∧ rBoth.graph = .both ∧
      suffix.Forall (fun r => r.graph = .right) ∧
      h₁ = History.append base rLeft ++ suffix ∧
      h₂ = History.append base rBoth ++ suffix

/-- The symmetric process-two overlap: an opening `right`/`both` ambiguity
followed by one common `left` block. -/
def ProcTwoPendingOverlap
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (h₁ h₂ : History In₁ In₂ Graph Out₁ Out₂) : Prop :=
  ∃ (base : History In₁ In₂ Graph Out₁ Out₂)
      (rRight rBoth : RoundRecord In₁ In₂ Graph Out₁ Out₂)
      (suffix : History In₁ In₂ Graph Out₁ Out₂),
    rRight.inputOne = rBoth.inputOne ∧
      rRight.inputTwo = rBoth.inputTwo ∧
      rRight.graph = .right ∧ rBoth.graph = .both ∧
      suffix.Forall (fun r => r.graph = .left) ∧
      h₁ = History.append base rRight ++ suffix ∧
      h₂ = History.append base rBoth ++ suffix

namespace ProcOnePendingOverlap

/-- The two histories in a process-one overlap really are locally
indistinguishable to process one. -/
theorem view_eq
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    {h₁ h₂ : History In₁ In₂ Graph Out₁ Out₂}
    (hoverlap : ProcOnePendingOverlap h₁ h₂) :
    currentView Proc.one h₁ = currentView Proc.one h₂ := by
  obtain ⟨base, rLeft, rBoth, suffix, hinOne, hinTwo, hleft, hboth,
    hsuffix, rfl, rfl⟩ := hoverlap
  exact viewinv_procOne_right_suffix base rLeft rBoth suffix
    hinOne hinTwo hleft hboth hsuffix

/-- Consequently every legal distributed strategy already gives the same
process-one output on the two overlapping decompositions. -/
theorem strategy_output_eq
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    {h₁ h₂ : History In₁ In₂ Graph Out₁ Out₂}
    (hoverlap : ProcOnePendingOverlap h₁ h₂)
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂) :
    strategy.one (currentView Proc.one h₁) =
      strategy.one (currentView Proc.one h₂) := by
  rw [hoverlap.view_eq]

/-- The overlap cannot persist past the next process-one receive. -/
theorem resolved_at_next_left
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    {h₁ h₂ : History In₁ In₂ Graph Out₁ Out₂}
    (hoverlap : ProcOnePendingOverlap h₁ h₂)
    (next : RoundRecord In₁ In₂ Graph Out₁ Out₂)
    (hnext : next.graph = .left) :
    currentView Proc.one (History.append h₁ next) ≠
      currentView Proc.one (History.append h₂ next) := by
  obtain ⟨base, rLeft, rBoth, suffix, _hinOne, _hinTwo, hleft, hboth,
    hsuffix, rfl, rfl⟩ := hoverlap
  exact procOne_left_both_resolved_at_next_left
    base rLeft rBoth suffix next hleft hboth hsuffix hnext

end ProcOnePendingOverlap

namespace ProcTwoPendingOverlap

/-- The process-two overlap is locally indistinguishable to process two. -/
theorem view_eq
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    {h₁ h₂ : History In₁ In₂ Graph Out₁ Out₂}
    (hoverlap : ProcTwoPendingOverlap h₁ h₂) :
    currentView Proc.two h₁ = currentView Proc.two h₂ := by
  obtain ⟨base, rRight, rBoth, suffix, hinOne, hinTwo, hright, hboth,
    hsuffix, rfl, rfl⟩ := hoverlap
  exact viewinv_procTwo_left_suffix base rRight rBoth suffix
    hinOne hinTwo hright hboth hsuffix

/-- Every distributed strategy agrees on the process-two overlap. -/
theorem strategy_output_eq
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    {h₁ h₂ : History In₁ In₂ Graph Out₁ Out₂}
    (hoverlap : ProcTwoPendingOverlap h₁ h₂)
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂) :
    strategy.two (currentView Proc.two h₁) =
      strategy.two (currentView Proc.two h₂) := by
  rw [hoverlap.view_eq]

/-- The process-two overlap ends at the next process-two receive. -/
theorem resolved_at_next_right
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    {h₁ h₂ : History In₁ In₂ Graph Out₁ Out₂}
    (hoverlap : ProcTwoPendingOverlap h₁ h₂)
    (next : RoundRecord In₁ In₂ Graph Out₁ Out₂)
    (hnext : next.graph = .right) :
    currentView Proc.two (History.append h₁ next) ≠
      currentView Proc.two (History.append h₂ next) := by
  obtain ⟨base, rRight, rBoth, suffix, _hinOne, _hinTwo, hright, hboth,
    hsuffix, rfl, rfl⟩ := hoverlap
  exact procTwo_right_both_resolved_at_next_right
    base rRight rBoth suffix next hright hboth hsuffix hnext

end ProcTwoPendingOverlap

/-! ### Completeness of the overlap at a receive boundary -/

/-- For strategy-generated histories ending in a process-one receive, equality
of the process-one view has no hidden source beyond the pending bit: the
histories are equal, or they are the two orientations of
`ProcOnePendingOverlap` (with an empty following block).

This is the receive-boundary local-consistency fact needed by a Bérard-style
strategy tree.  It strengthens the cardinality statement
`blind_receive_class_le_two_one` by identifying the two candidates. -/
theorem strategyGenerated_receive_eq_or_pendingOverlap_one
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    {h₀ h₀' : History In₁ In₂ Graph Out₁ Out₂}
    (hgen₀ : StrategyGeneratedPrefix strategy h₀)
    (hgen₀' : StrategyGeneratedPrefix strategy h₀')
    (i₁ j₁ : In₁) (i₂ j₂ : In₂) (g g' : Graph)
    (hg : g = .left ∨ g = .both)
    (hg' : g' = .left ∨ g' = .both)
    (hview :
      currentView Proc.one
          (History.append h₀' (nextRound strategy h₀' ⟨j₁, j₂, g'⟩)) =
        currentView Proc.one
          (History.append h₀ (nextRound strategy h₀ ⟨i₁, i₂, g⟩))) :
    History.append h₀' (nextRound strategy h₀' ⟨j₁, j₂, g'⟩) =
        History.append h₀ (nextRound strategy h₀ ⟨i₁, i₂, g⟩) ∨
      ProcOnePendingOverlap
        (History.append h₀' (nextRound strategy h₀' ⟨j₁, j₂, g'⟩))
        (History.append h₀ (nextRound strategy h₀ ⟨i₁, i₂, g⟩)) ∨
      ProcOnePendingOverlap
        (History.append h₀ (nextRound strategy h₀ ⟨i₁, i₂, g⟩))
        (History.append h₀' (nextRound strategy h₀' ⟨j₁, j₂, g'⟩)) := by
  obtain ⟨hbase, hinputOne, hinputTwo⟩ :=
    recv_view_determines_prefix_one strategy hgen₀ hgen₀'
      i₁ j₁ i₂ j₂ g g' hg hg' hview
  subst h₀'
  subst j₁
  subst j₂
  rcases hg with rfl | rfl <;> rcases hg' with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inr ⟨h₀,
      nextRound strategy h₀ ⟨i₁, i₂, .left⟩,
      nextRound strategy h₀ ⟨i₁, i₂, .both⟩, [], by simp [nextRound]⟩)
  · exact Or.inr (Or.inl ⟨h₀,
      nextRound strategy h₀ ⟨i₁, i₂, .left⟩,
      nextRound strategy h₀ ⟨i₁, i₂, .both⟩, [], by simp [nextRound]⟩)
  · exact Or.inl rfl

/-- Symmetric completeness of `ProcTwoPendingOverlap` at a process-two
receive boundary. -/
theorem strategyGenerated_receive_eq_or_pendingOverlap_two
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    {h₀ h₀' : History In₁ In₂ Graph Out₁ Out₂}
    (hgen₀ : StrategyGeneratedPrefix strategy h₀)
    (hgen₀' : StrategyGeneratedPrefix strategy h₀')
    (i₁ j₁ : In₁) (i₂ j₂ : In₂) (g g' : Graph)
    (hg : g = .right ∨ g = .both)
    (hg' : g' = .right ∨ g' = .both)
    (hview :
      currentView Proc.two
          (History.append h₀' (nextRound strategy h₀' ⟨j₁, j₂, g'⟩)) =
        currentView Proc.two
          (History.append h₀ (nextRound strategy h₀ ⟨i₁, i₂, g⟩))) :
    History.append h₀' (nextRound strategy h₀' ⟨j₁, j₂, g'⟩) =
        History.append h₀ (nextRound strategy h₀ ⟨i₁, i₂, g⟩) ∨
      ProcTwoPendingOverlap
        (History.append h₀' (nextRound strategy h₀' ⟨j₁, j₂, g'⟩))
        (History.append h₀ (nextRound strategy h₀ ⟨i₁, i₂, g⟩)) ∨
      ProcTwoPendingOverlap
        (History.append h₀ (nextRound strategy h₀ ⟨i₁, i₂, g⟩))
        (History.append h₀' (nextRound strategy h₀' ⟨j₁, j₂, g'⟩)) := by
  obtain ⟨hbase, hinputOne, hinputTwo⟩ :=
    recv_view_determines_prefix_two strategy hgen₀ hgen₀'
      i₁ j₁ i₂ j₂ g g' hg hg' hview
  subst h₀'
  subst j₁
  subst j₂
  rcases hg with rfl | rfl <;> rcases hg' with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inr ⟨h₀,
      nextRound strategy h₀ ⟨i₁, i₂, .right⟩,
      nextRound strategy h₀ ⟨i₁, i₂, .both⟩, [], by simp [nextRound]⟩)
  · exact Or.inr (Or.inl ⟨h₀,
      nextRound strategy h₀ ⟨i₁, i₂, .right⟩,
      nextRound strategy h₀ ⟨i₁, i₂, .both⟩, [], by simp [nextRound]⟩)
  · exact Or.inl rfl

end DistributedSynthesis
