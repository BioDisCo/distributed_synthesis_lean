/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemCodedAlternatingIndexedLineageThreadSystem

/-!
# A child-code observable alternating-lineage parity monitor

The ordinary coded alternating-lineage system receives a move and a raw
environment direction, then recomputes a child code.  For local strategy
extraction we need the equivalent finite presentation in which the objective
monitor reads only the already computed child belief code.

The current code remains in the hidden thread-system state.  A live lineage
alternates sides and reads its next root from the corresponding slot of the
child code.  The row coordinate is irrelevant to parity, so the adapter uses
the fixed row `first` internally.  The resulting deterministic parity
automaton has alphabet `Code` and therefore factors through a finite child
code by construction.
-/

namespace DistributedSynthesis

universe c i r

namespace DetParityAutomaton

/-- Reconstruct the row-decorated child-code interface from the root slots of
the next public code. -/
def codedAlternatingIndexedLineageCodeChild
    {Code : Type c} {I : Type i} {Root : Type r}
    (currentSlots : IndexedLineageSide → Code → I → Option Root)
    (side : IndexedLineageSide) (_code : Code) (_move : Unit)
    (childCode : Code) : IndexedLineageChildCode I Root :=
  fun lineage =>
    match currentSlots side.other childCode lineage with
    | none => none
    | some root => some (.first, root)

@[simp] theorem codedAlternatingIndexedLineageCodeChild_rootSlots
    {Code : Type c} {I : Type i} {Root : Type r}
    (currentSlots : IndexedLineageSide → Code → I → Option Root)
    (side : IndexedLineageSide) (code childCode : Code) (lineage : I) :
    (codedAlternatingIndexedLineageCodeChild currentSlots side code
        Unit.unit childCode).rootSlots lineage =
      currentSlots side.other childCode lineage := by
  cases hslot : currentSlots side.other childCode lineage <;>
    simp [codedAlternatingIndexedLineageCodeChild,
      IndexedLineageChildCode.rootSlots, hslot]

/-- Hidden thread system whose public letter is `(unit, childCode)`. -/
noncomputable def codedAlternatingIndexedLineageCodeThreadSystem
    {Code : Type c} {I : Type i} {Root : Type r}
    [Fintype Code] [Fintype I] [Fintype Root]
    (initialCode : Code)
    (currentSlots : IndexedLineageSide → Code → I → Option Root)
    (rootPriority : Root → Nat) : FiniteThreadSystem (Unit × Code) :=
  codedAlternatingIndexedLineageThreadSystem initialCode
    (fun _ _ childCode => childCode)
    currentSlots
    (codedAlternatingIndexedLineageCodeChild currentSlots)
    rootPriority

/-- The code-observable DPA.  Its transition alphabet is exactly the finite
child belief code. -/
noncomputable def codedAlternatingIndexedLineageCodeDPA
    {Code : Type c} {I : Type i} {Root : Type r}
    [Fintype Code] [Fintype I] [Fintype Root]
    (initialCode : Code)
    (currentSlots : IndexedLineageSide → Code → I → Option Root)
    (rootPriority : Root → Nat) : DetParityAutomaton Code :=
  (codedAlternatingIndexedLineageCodeThreadSystem initialCode currentSlots
    rootPriority).universalRunDPA.comap (fun childCode => (Unit.unit, childCode))

/-- Canonical hidden evolution for one initially selected side and lineage. -/
noncomputable def codedAlternatingIndexedLineageCodeRun
    {Code : Type c} {I : Type i} {Root : Type r}
    (initialCode : Code)
    (currentSlots : IndexedLineageSide → Code → I → Option Root)
    (word : OmegaWord Code)
    (initialSide : IndexedLineageSide) (lineage : I) :=
  codedAlternatingIndexedLineageRun initialCode
    (fun _ (_ : Unit) childCode => childCode)
    currentSlots
    (codedAlternatingIndexedLineageCodeChild currentSlots)
    (fun n => (Unit.unit, word n)) initialSide lineage

@[simp] theorem codedAlternatingIndexedLineageCodeRun_zero
    {Code : Type c} {I : Type i} {Root : Type r}
    (initialCode : Code)
    (currentSlots : IndexedLineageSide → Code → I → Option Root)
    (word : OmegaWord Code)
    (initialSide : IndexedLineageSide) (lineage : I) :
    codedAlternatingIndexedLineageCodeRun initialCode currentSlots word
        initialSide lineage 0 =
      (initialCode, .initial) :=
  rfl

/-- A present initial slot advances to the root stored in the child code on
the opposite side. -/
theorem codedAlternatingIndexedLineageCodeStep_initial_of
    {Code : Type c} {I : Type i} {Root : Type r}
    (currentSlots : IndexedLineageSide → Code → I → Option Root)
    (code childCode : Code) (side : IndexedLineageSide) (lineage : I)
    (root child : Root)
    (hcurrent : currentSlots side code lineage = some root)
    (hchild : currentSlots side.other childCode lineage = some child) :
    codedAlternatingIndexedLineageStep
        (fun _ (_ : Unit) nextCode => nextCode)
        currentSlots
        (codedAlternatingIndexedLineageCodeChild currentSlots)
        (code, .initial) (Unit.unit, childCode) (side, lineage) =
      (childCode, .live side.other lineage child) := by
  apply codedAlternatingIndexedLineageStep_initial_of
    (fun _ (_ : Unit) nextCode => nextCode)
    currentSlots
    (codedAlternatingIndexedLineageCodeChild currentSlots)
    code Unit.unit childCode side lineage root child .first hcurrent
  simp [codedAlternatingIndexedLineageCodeChild, hchild]

/-- Live code-only step; later resolutions remain ignored. -/
theorem codedAlternatingIndexedLineageCodeStep_live_of
    {Code : Type c} {I : Type i} {Root : Type r}
    (currentSlots : IndexedLineageSide → Code → I → Option Root)
    (code childCode : Code) (side : IndexedLineageSide) (lineage : I)
    (root child : Root) (resolution : IndexedLineageSide × I)
    (hcurrent : currentSlots side code lineage = some root)
    (hchild : currentSlots side.other childCode lineage = some child) :
    codedAlternatingIndexedLineageStep
        (fun _ (_ : Unit) nextCode => nextCode)
        currentSlots
        (codedAlternatingIndexedLineageCodeChild currentSlots)
        (code, .live side lineage root) (Unit.unit, childCode) resolution =
      (childCode, .live side.other lineage child) := by
  apply codedAlternatingIndexedLineageStep_live_of
    (fun _ (_ : Unit) nextCode => nextCode)
    currentSlots
    (codedAlternatingIndexedLineageCodeChild currentSlots)
    code Unit.unit childCode side lineage root child .first resolution
    hcurrent
  simp [codedAlternatingIndexedLineageCodeChild, hchild]

/-- Exact acceptance semantics: the code DPA checks every persistent
alternating side/lineage evolution. -/
theorem codedAlternatingIndexedLineageCodeDPA_accepts_iff
    {Code : Type c} {I : Type i} {Root : Type r}
    [Fintype Code] [Fintype I] [Fintype Root]
    (initialCode : Code)
    (currentSlots : IndexedLineageSide → Code → I → Option Root)
    (rootPriority : Root → Nat)
    (word : OmegaWord Code) :
    (codedAlternatingIndexedLineageCodeDPA initialCode currentSlots
        rootPriority).Accepts word ↔
      ∀ initialSide lineage,
        NatSeqMinEvenParity (fun n =>
          (codedAlternatingIndexedLineageCodeThreadSystem initialCode
              currentSlots rootPriority).priority
            (codedAlternatingIndexedLineageCodeRun initialCode currentSlots
              word initialSide lineage n)) := by
  rw [codedAlternatingIndexedLineageCodeDPA,
    DetParityAutomaton.comap_accepts_iff]
  change
    (codedAlternatingIndexedLineageCodeThreadSystem initialCode currentSlots
      rootPriority).universalRunDPA.Accepts
        (fun n => (Unit.unit, word n)) ↔ _
  exact codedAlternatingIndexedLineageThreadSystem_accepts_iff initialCode
    (fun _ (_ : Unit) childCode => childCode)
    currentSlots
    (codedAlternatingIndexedLineageCodeChild currentSlots)
    rootPriority (fun n => (Unit.unit, word n))

end DetParityAutomaton

end DistributedSynthesis
