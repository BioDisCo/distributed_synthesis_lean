/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenIndexedLineage

/-!
# Universal parity monitor for an indexed lineage

The public letter contains only two finite ordered codes: the current root
slots and the pattern-derived successor slots.  A hidden resolution chooses
one persistent lineage at the first step.  Every later step ignores the
resolution and retains that same lineage.  Missing or inconsistent slots go
to an even sink.

Thus the universal bundle checks every persistent lineage without exposing a
lineage, an orientation, or a strict-leader bit to either process.  In
particular, equal finite roots in distinct slots cannot cause the monitor to
switch lineages after a merge.
-/

namespace DistributedSynthesis

universe i r

namespace DetParityAutomaton

/-- The finite data consumed by one indexed-lineage transition. -/
structure IndexedLineageThreadLetter (I : Type i) (Root : Type r) where
  currentSlots : I → Option Root
  childCode : IndexedLineageChildCode I Root

/-- One transition of the persistent-lineage monitor.  Only the first
resolution selects a lineage; live states retain their stored index. -/
noncomputable def indexedLineageThreadStep
    {I : Type i} {Root : Type r}
    (state : IndexedLineageThreadState I Root)
    (letter : IndexedLineageThreadLetter I Root)
    (resolution : I) : IndexedLineageThreadState I Root := by
  classical
  exact match state with
    | .dead => .dead
    | .initial =>
        match letter.currentSlots resolution, letter.childCode resolution with
        | some _, some (_, next) => .live resolution next
        | _, _ => .dead
    | .live lineage root =>
        indexedLineageThreadUpdate letter.currentSlots (.live lineage root)
          letter.childCode

/-- The finite hidden-thread system checking all persistent lineages. -/
noncomputable def indexedLineageThreadSystem
    {I : Type i} {Root : Type r}
    [Fintype I] [Fintype Root]
    (rootPriority : Root → Nat) :
    FiniteThreadSystem (IndexedLineageThreadLetter I Root) where
  State := IndexedLineageThreadState I Root
  stateFinite := inferInstance
  initial := .initial
  Resolution := I
  step := indexedLineageThreadStep
  priority := fun state =>
    match state with
    | .initial | .dead => 0
    | .live _ root => rootPriority root

@[simp] theorem indexedLineageThreadStep_dead
    {I : Type i} {Root : Type r}
    (letter : IndexedLineageThreadLetter I Root) (resolution : I) :
    indexedLineageThreadStep
        (IndexedLineageThreadState.dead : IndexedLineageThreadState I Root)
        letter resolution = .dead := by
  simp [indexedLineageThreadStep]

/-- A present initial slot starts precisely the selected persistent lineage. -/
theorem indexedLineageThreadStep_initial_of
    {I : Type i} {Root : Type r}
    (letter : IndexedLineageThreadLetter I Root)
    (lineage : I) (current next : Root) (row : PairedEntryRow)
    (hcurrent : letter.currentSlots lineage = some current)
    (hchild : letter.childCode lineage = some (row, next)) :
    indexedLineageThreadStep
        (IndexedLineageThreadState.initial : IndexedLineageThreadState I Root)
        letter lineage = .live lineage next := by
  simp [indexedLineageThreadStep, hcurrent, hchild]

/-- An absent current slot makes that initial resolution harmless. -/
theorem indexedLineageThreadStep_initial_dead_of_current_none
    {I : Type i} {Root : Type r}
    (letter : IndexedLineageThreadLetter I Root) (lineage : I)
    (hcurrent : letter.currentSlots lineage = none) :
    indexedLineageThreadStep
        (IndexedLineageThreadState.initial : IndexedLineageThreadState I Root)
        letter lineage = .dead := by
  simp [indexedLineageThreadStep, hcurrent]

/-- A missing successor makes that initial resolution harmless. -/
theorem indexedLineageThreadStep_initial_dead_of_child_none
    {I : Type i} {Root : Type r}
    (letter : IndexedLineageThreadLetter I Root) (lineage : I)
    (hchild : letter.childCode lineage = none) :
    indexedLineageThreadStep
        (IndexedLineageThreadState.initial : IndexedLineageThreadState I Root)
        letter lineage = .dead := by
  simp [indexedLineageThreadStep, hchild]

/-- Once live, the external resolution cannot change the lineage. -/
theorem indexedLineageThreadStep_live_of
    {I : Type i} {Root : Type r}
    (letter : IndexedLineageThreadLetter I Root)
    (lineage resolution : I) (current next : Root)
    (row : PairedEntryRow)
    (hcurrent : letter.currentSlots lineage = some current)
    (hchild : letter.childCode lineage = some (row, next)) :
    indexedLineageThreadStep (.live lineage current) letter resolution =
      .live lineage next := by
  simp only [indexedLineageThreadStep]
  exact indexedLineageThreadUpdate_live_of letter.currentSlots
    letter.childCode lineage current next row hcurrent hchild

/-- The live-state equation is independent of the supplied resolution. -/
theorem indexedLineageThreadStep_live_resolution_irrel
    {I : Type i} {Root : Type r}
    (letter : IndexedLineageThreadLetter I Root)
    (lineage : I) (current : Root) (left right : I) :
    indexedLineageThreadStep (.live lineage current) letter left =
      indexedLineageThreadStep (.live lineage current) letter right := by
  rfl

/-- Every transition leaves the one-use initial state. -/
theorem indexedLineageThreadStep_ne_initial
    {I : Type i} {Root : Type r}
    (state : IndexedLineageThreadState I Root)
    (letter : IndexedLineageThreadLetter I Root) (resolution : I) :
    indexedLineageThreadStep state letter resolution ≠ .initial := by
  classical
  cases state with
  | initial =>
      cases hcurrent : letter.currentSlots resolution with
      | none => simp [indexedLineageThreadStep, hcurrent]
      | some current =>
          cases hchild : letter.childCode resolution with
          | none => simp [indexedLineageThreadStep, hcurrent, hchild]
          | some child =>
              rcases child with ⟨row, next⟩
              simp [indexedLineageThreadStep, hcurrent, hchild]
  | live lineage root =>
      simp only [indexedLineageThreadStep, indexedLineageThreadUpdate]
      split
      · split <;> simp
      · simp
  | dead => simp [indexedLineageThreadStep]

/-- After the initial choice, resolutions are entirely irrelevant. -/
theorem indexedLineageThreadStep_resolution_irrel_of_ne_initial
    {I : Type i} {Root : Type r}
    (state : IndexedLineageThreadState I Root)
    (letter : IndexedLineageThreadLetter I Root)
    (hne : state ≠ .initial) (left right : I) :
    indexedLineageThreadStep state letter left =
      indexedLineageThreadStep state letter right := by
  cases state with
  | initial => exact absurd rfl hne
  | live => rfl
  | dead => rfl

/-- The run obtained by selecting one lineage initially and retaining it
forever. -/
noncomputable def indexedLineageRun
    {I : Type i} {Root : Type r}
    (word : OmegaWord (IndexedLineageThreadLetter I Root))
    (lineage : I) : Nat → IndexedLineageThreadState I Root
  | 0 => .initial
  | n + 1 => indexedLineageThreadStep
      (indexedLineageRun word lineage n) (word n) lineage

@[simp] theorem indexedLineageRun_zero
    {I : Type i} {Root : Type r}
    (word : OmegaWord (IndexedLineageThreadLetter I Root))
    (lineage : I) :
    indexedLineageRun word lineage 0 = .initial :=
  rfl

@[simp] theorem indexedLineageRun_succ
    {I : Type i} {Root : Type r}
    (word : OmegaWord (IndexedLineageThreadLetter I Root))
    (lineage : I) (n : Nat) :
    indexedLineageRun word lineage (n + 1) =
      indexedLineageThreadStep (indexedLineageRun word lineage n)
        (word n) lineage :=
  rfl

theorem indexedLineageRun_succ_ne_initial
    {I : Type i} {Root : Type r}
    (word : OmegaWord (IndexedLineageThreadLetter I Root))
    (lineage : I) (n : Nat) :
    indexedLineageRun word lineage (n + 1) ≠ .initial := by
  rw [indexedLineageRun_succ]
  exact indexedLineageThreadStep_ne_initial _ _ _

/-- Every fixed-lineage evolution is a run of the finite thread system. -/
theorem indexedLineageRun_isRun
    {I : Type i} {Root : Type r}
    [Fintype I] [Fintype Root]
    (rootPriority : Root → Nat)
    (word : OmegaWord (IndexedLineageThreadLetter I Root))
    (lineage : I) :
    (indexedLineageThreadSystem rootPriority).IsRun word
      (indexedLineageRun word lineage) := by
  constructor
  · rfl
  · intro n
    exact ⟨lineage, rfl⟩

/-- Conversely, an arbitrary hidden run chooses one lineage on its first
step and thereafter is exactly that fixed-lineage run. -/
theorem indexedLineageRun_eq_of_isRun
    {I : Type i} {Root : Type r}
    [Fintype I] [Fintype Root]
    (rootPriority : Root → Nat)
    (word : OmegaWord (IndexedLineageThreadLetter I Root))
    (run : Nat → IndexedLineageThreadState I Root)
    (hrun : (indexedLineageThreadSystem rootPriority).IsRun word run) :
    ∃ lineage : I, run = indexedLineageRun word lineage := by
  rcases hrun.2 0 with ⟨lineage, hfirst⟩
  refine ⟨lineage, funext fun n => ?_⟩
  cases n with
  | zero => exact hrun.1
  | succ n =>
      induction n with
      | zero =>
          calc
            run (0 + 1) = indexedLineageThreadStep (run 0) (word 0)
                lineage := hfirst
            _ = indexedLineageThreadStep
                (indexedLineageRun word lineage 0) (word 0) lineage := by
                  rw [hrun.1, indexedLineageRun_zero]
                  rfl
      | succ n ih =>
          rcases hrun.2 (n + 1) with ⟨resolution, hnext⟩
          rw [hnext, ih]
          exact indexedLineageThreadStep_resolution_irrel_of_ne_initial
            (indexedLineageRun word lineage (n + 1)) (word (n + 1))
            (indexedLineageRun_succ_ne_initial word lineage n) resolution
            lineage

/-- Exact semantic characterization of the universal monitor: it checks all
and only the persistent lineages. -/
theorem indexedLineageThreadSystem_accepts_iff
    {I : Type i} {Root : Type r}
    [Fintype I] [Fintype Root]
    (rootPriority : Root → Nat)
    (word : OmegaWord (IndexedLineageThreadLetter I Root)) :
    (indexedLineageThreadSystem rootPriority).universalRunDPA.Accepts word ↔
      ∀ lineage : I,
        NatSeqMinEvenParity (fun n =>
          (indexedLineageThreadSystem rootPriority).priority
            (indexedLineageRun word lineage n)) := by
  rw [(indexedLineageThreadSystem rootPriority).universalRunDPA_accepts_iff]
  constructor
  · intro hall lineage
    exact hall (indexedLineageRun word lineage)
      (indexedLineageRun_isRun rootPriority word lineage)
  · intro hall run hrun
    rcases indexedLineageRun_eq_of_isRun rootPriority word run hrun with
      ⟨lineage, rfl⟩
    exact hall lineage

/-- Priorities of live states are exactly the priorities of their finite
roots; the persistent index has no effect on the parity objective. -/
@[simp] theorem indexedLineageThreadSystem_priority_live
    {I : Type i} {Root : Type r}
    [Fintype I] [Fintype Root]
    (rootPriority : Root → Nat) (lineage : I) (root : Root) :
    (indexedLineageThreadSystem rootPriority).priority (.live lineage root) =
      rootPriority root :=
  rfl

@[simp] theorem indexedLineageThreadSystem_priority_dead
    {I : Type i} {Root : Type r}
    [Fintype I] [Fintype Root]
    (rootPriority : Root → Nat) :
    (indexedLineageThreadSystem rootPriority).priority
        (IndexedLineageThreadState.dead : IndexedLineageThreadState I Root) =
      0 :=
  rfl

end DetParityAutomaton

end DistributedSynthesis
