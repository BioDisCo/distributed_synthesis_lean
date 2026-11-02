/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemCodedAlternatingIndexedLineageCodeParity

/-!
# Extracting a literal live trace from the code-only lineage monitor

If the canonical code-only lineage run never reaches `dead`, every positive
time is uniquely a live state on the original lineage.  This file packages
those states as a recursive trace, including the exact public slot and the
side-alternation equation needed by semantic memory stitching.
-/

namespace DistributedSynthesis

universe c i r

namespace DetParityAutomaton

noncomputable section

/-- Literal data at positive monitor time `n + 1`. -/
structure CodedAlternatingIndexedLineageCodeLiveAt
    {Code : Type c} {I : Type i} {Root : Type r}
    (initialCode : Code)
    (currentSlots : IndexedLineageSide → Code → I → Option Root)
    (word : OmegaWord Code) (initialSide : IndexedLineageSide)
    (lineage : I) (n : Nat) where
  side : IndexedLineageSide
  root : Root
  run_eq :
    codedAlternatingIndexedLineageCodeRun initialCode currentSlots word
        initialSide lineage (n + 1) =
      (word n, .live side lineage root)
  slot : currentSlots side (word n) lineage = some root

/-- Non-death of the first transition supplies the first live state. -/
theorem exists_codedAlternatingIndexedLineageCodeLiveAt_zero
    {Code : Type c} {I : Type i} {Root : Type r}
    (initialCode : Code)
    (currentSlots : IndexedLineageSide → Code → I → Option Root)
    (word : OmegaWord Code) (initialSide : IndexedLineageSide)
    (lineage : I)
    (hlive :
      (codedAlternatingIndexedLineageCodeRun initialCode currentSlots word
        initialSide lineage 1).2 ≠ .dead) :
    Nonempty (CodedAlternatingIndexedLineageCodeLiveAt initialCode
      currentSlots word initialSide lineage 0) := by
  classical
  cases hcurrent : currentSlots initialSide initialCode lineage with
  | none =>
      exfalso
      apply hlive
      simp [codedAlternatingIndexedLineageCodeRun,
        codedAlternatingIndexedLineageRun,
        codedAlternatingIndexedLineageStep, hcurrent]
  | some currentRoot =>
      cases hchild : currentSlots initialSide.other (word 0) lineage with
      | none =>
          exfalso
          apply hlive
          simp [codedAlternatingIndexedLineageCodeRun,
            codedAlternatingIndexedLineageRun,
            codedAlternatingIndexedLineageStep,
            codedAlternatingIndexedLineageCodeChild, hcurrent, hchild]
      | some childRoot =>
          refine ⟨{
            side := initialSide.other
            root := childRoot
            run_eq := ?_
            slot := hchild }⟩
          simp [codedAlternatingIndexedLineageCodeRun,
            codedAlternatingIndexedLineageRun,
            codedAlternatingIndexedLineageStep,
            codedAlternatingIndexedLineageCodeChild, hcurrent, hchild]

/-- One non-dead successor extends a live trace point, preserves its lineage,
and flips its hidden monitor side. -/
theorem exists_codedAlternatingIndexedLineageCodeLiveAt_succ
    {Code : Type c} {I : Type i} {Root : Type r}
    (initialCode : Code)
    (currentSlots : IndexedLineageSide → Code → I → Option Root)
    (word : OmegaWord Code) (initialSide : IndexedLineageSide)
    (lineage : I) (n : Nat)
    (current : CodedAlternatingIndexedLineageCodeLiveAt initialCode
      currentSlots word initialSide lineage n)
    (hlive :
      (codedAlternatingIndexedLineageCodeRun initialCode currentSlots word
        initialSide lineage (n + 2)).2 ≠ .dead) :
    ∃ next : CodedAlternatingIndexedLineageCodeLiveAt initialCode
        currentSlots word initialSide lineage (n + 1),
      next.side = current.side.other := by
  classical
  cases hchild : currentSlots current.side.other (word (n + 1)) lineage with
  | none =>
      exfalso
      apply hlive
      rw [show n + 2 = (n + 1) + 1 by omega]
      unfold codedAlternatingIndexedLineageCodeRun
      rw [codedAlternatingIndexedLineageRun_succ]
      change (codedAlternatingIndexedLineageCodeRun initialCode currentSlots
        word initialSide lineage (n + 1) |> fun state =>
          codedAlternatingIndexedLineageStep
            (fun _ (_ : Unit) nextCode => nextCode) currentSlots
            (codedAlternatingIndexedLineageCodeChild currentSlots) state
            (Unit.unit, word (n + 1)) (initialSide, lineage)).2 = .dead
      rw [current.run_eq]
      simp [codedAlternatingIndexedLineageStep,
        codedAlternatingIndexedLineageCodeChild, current.slot, hchild]
  | some childRoot =>
      let next : CodedAlternatingIndexedLineageCodeLiveAt initialCode
          currentSlots word initialSide lineage (n + 1) :=
        { side := current.side.other
          root := childRoot
          run_eq := by
            rw [show n + 2 = (n + 1) + 1 by omega]
            unfold codedAlternatingIndexedLineageCodeRun
            rw [codedAlternatingIndexedLineageRun_succ]
            change codedAlternatingIndexedLineageStep
                (fun _ (_ : Unit) nextCode => nextCode) currentSlots
                (codedAlternatingIndexedLineageCodeChild currentSlots)
                (codedAlternatingIndexedLineageCodeRun initialCode currentSlots
                  word initialSide lineage (n + 1))
                (Unit.unit, word (n + 1)) (initialSide, lineage) = _
            rw [current.run_eq]
            simp [codedAlternatingIndexedLineageStep,
              codedAlternatingIndexedLineageCodeChild, current.slot, hchild]
          slot := hchild }
      exact ⟨next, rfl⟩

/-- Recursively selected live point at every positive time. -/
noncomputable def codedAlternatingIndexedLineageCodeLiveAtOfNeverDead
    {Code : Type c} {I : Type i} {Root : Type r}
    (initialCode : Code)
    (currentSlots : IndexedLineageSide → Code → I → Option Root)
    (word : OmegaWord Code) (initialSide : IndexedLineageSide)
    (lineage : I)
    (hnever : ∀ n,
      (codedAlternatingIndexedLineageCodeRun initialCode currentSlots word
        initialSide lineage (n + 1)).2 ≠ .dead) :
    (n : Nat) → CodedAlternatingIndexedLineageCodeLiveAt initialCode
      currentSlots word initialSide lineage n
  | 0 => Classical.choice
      (exists_codedAlternatingIndexedLineageCodeLiveAt_zero initialCode
        currentSlots word initialSide lineage (hnever 0))
  | n + 1 => Classical.choose
      (exists_codedAlternatingIndexedLineageCodeLiveAt_succ initialCode
        currentSlots word initialSide lineage n
        (codedAlternatingIndexedLineageCodeLiveAtOfNeverDead initialCode
          currentSlots word initialSide lineage hnever n)
        (hnever (n + 1)))

@[simp] theorem codedAlternatingIndexedLineageCodeLiveAtOfNeverDead_side_succ
    {Code : Type c} {I : Type i} {Root : Type r}
    (initialCode : Code)
    (currentSlots : IndexedLineageSide → Code → I → Option Root)
    (word : OmegaWord Code) (initialSide : IndexedLineageSide)
    (lineage : I)
    (hnever : ∀ n,
      (codedAlternatingIndexedLineageCodeRun initialCode currentSlots word
        initialSide lineage (n + 1)).2 ≠ .dead)
    (n : Nat) :
    (codedAlternatingIndexedLineageCodeLiveAtOfNeverDead initialCode
      currentSlots word initialSide lineage hnever (n + 1)).side =
      (codedAlternatingIndexedLineageCodeLiveAtOfNeverDead initialCode
        currentSlots word initialSide lineage hnever n).side.other := by
  exact Classical.choose_spec
    (exists_codedAlternatingIndexedLineageCodeLiveAt_succ initialCode
      currentSlots word initialSide lineage n
      (codedAlternatingIndexedLineageCodeLiveAtOfNeverDead initialCode
        currentSlots word initialSide lineage hnever n)
      (hnever (n + 1)))

end

end DetParityAutomaton

end DistributedSynthesis
