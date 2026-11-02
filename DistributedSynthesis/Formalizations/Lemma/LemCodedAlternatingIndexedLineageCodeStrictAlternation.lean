/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemCodedAlternatingIndexedLineageCodeParity

/-!
# Reading a prescribed alternating root stream from child codes

The code-only lineage monitor flips its hidden side after every letter.  Thus,
if a proof-side stream of strict directions flips sides at the same rate and
each child code exposes the crossed root of that direction, the monitor reads
exactly that root stream.  This is a generic indexing lemma: the direction
sides and roots remain proof witnesses and are not observable controller
inputs.
-/

namespace DistributedSynthesis

universe c i r

namespace DetParityAutomaton

noncomputable section

/-- Exact live state of the code-only monitor after reading child code `n`.
The source slot is required only at time zero; every later source slot is the
preceding crossed target slot, by strict-side alternation. -/
theorem codedAlternatingIndexedLineageCodeRun_eq_live_of_strictAlternation
    {Code : Type c} {I : Type i} {Root : Type r}
    (initialCode : Code)
    (currentSlots : IndexedLineageSide → Code → I → Option Root)
    (word : OmegaWord Code)
    (side : Nat → IndexedLineageSide) (lineage : I)
    (initialRoot : Root) (root : Nat → Root)
    (hinitial :
      currentSlots (side 0) initialCode lineage = some initialRoot)
    (hroot : ∀ n : Nat,
      currentSlots (side n).other (word n) lineage = some (root n))
    (halternates : ∀ n : Nat, side (n + 1) = (side n).other) :
    ∀ n : Nat,
      codedAlternatingIndexedLineageCodeRun initialCode currentSlots word
          (side 0) lineage (n + 1) =
        (word n, .live (side n).other lineage (root n)) := by
  intro n
  induction n with
  | zero =>
      change
        codedAlternatingIndexedLineageStep
            (fun _ (_ : Unit) nextCode => nextCode)
            currentSlots
            (codedAlternatingIndexedLineageCodeChild currentSlots)
            (initialCode, .initial) (Unit.unit, word 0)
            (side 0, lineage) =
          (word 0, .live (side 0).other lineage (root 0))
      exact codedAlternatingIndexedLineageCodeStep_initial_of currentSlots
        initialCode (word 0) (side 0) lineage initialRoot (root 0)
          hinitial (hroot 0)
  | succ n ih =>
      rw [show n + 1 + 1 = (n + 1) + 1 by omega]
      unfold codedAlternatingIndexedLineageCodeRun
      rw [codedAlternatingIndexedLineageRun_succ]
      change codedAlternatingIndexedLineageStep
          (fun _ (_ : Unit) nextCode => nextCode)
          currentSlots
          (codedAlternatingIndexedLineageCodeChild currentSlots)
          (codedAlternatingIndexedLineageRun initialCode
            (fun _ (_ : Unit) nextCode => nextCode) currentSlots
            (codedAlternatingIndexedLineageCodeChild currentSlots)
            (fun k => (Unit.unit, word k)) (side 0) lineage (n + 1))
          (Unit.unit, word (n + 1)) (side 0, lineage) = _
      unfold codedAlternatingIndexedLineageCodeRun at ih
      rw [ih]
      have hnext :
          currentSlots ((side n).other).other (word (n + 1)) lineage =
            some (root (n + 1)) := by
        simpa [halternates n] using hroot (n + 1)
      simpa [halternates n] using
        (codedAlternatingIndexedLineageCodeStep_live_of currentSlots
          (word n) (word (n + 1)) (side n).other lineage (root n)
          (root (n + 1)) (side 0, lineage) (hroot n) hnext)

/-- The monitor priority at positive time `n + 1` is the priority of the
prescribed crossed root at block `n`. -/
theorem codedAlternatingIndexedLineageCodeRun_priority_eq_of_strictAlternation
    {Code : Type c} {I : Type i} {Root : Type r}
    [Fintype Code] [Fintype I] [Fintype Root]
    (initialCode : Code)
    (currentSlots : IndexedLineageSide → Code → I → Option Root)
    (rootPriority : Root → Nat) (word : OmegaWord Code)
    (side : Nat → IndexedLineageSide) (lineage : I)
    (initialRoot : Root) (root : Nat → Root)
    (hinitial :
      currentSlots (side 0) initialCode lineage = some initialRoot)
    (hroot : ∀ n : Nat,
      currentSlots (side n).other (word n) lineage = some (root n))
    (halternates : ∀ n : Nat, side (n + 1) = (side n).other)
    (n : Nat) :
    (codedAlternatingIndexedLineageCodeThreadSystem initialCode currentSlots
        rootPriority).priority
        (codedAlternatingIndexedLineageCodeRun initialCode currentSlots word
          (side 0) lineage (n + 1)) =
      rootPriority (root n) := by
  rw [codedAlternatingIndexedLineageCodeRun_eq_live_of_strictAlternation
    initialCode currentSlots word side lineage initialRoot root hinitial hroot
      halternates n]
  rfl

/-- Parity of the complete canonical monitor run therefore implies parity of
the prescribed physical/root stream.  The initial monitor state is removed
by the standard finite-prefix invariance theorem. -/
theorem natSeqMinEvenParity_roots_of_codedAlternating_strictAlternation
    {Code : Type c} {I : Type i} {Root : Type r}
    [Fintype Code] [Fintype I] [Fintype Root]
    (initialCode : Code)
    (currentSlots : IndexedLineageSide → Code → I → Option Root)
    (rootPriority : Root → Nat) (word : OmegaWord Code)
    (side : Nat → IndexedLineageSide) (lineage : I)
    (initialRoot : Root) (root : Nat → Root)
    (hinitial :
      currentSlots (side 0) initialCode lineage = some initialRoot)
    (hroot : ∀ n : Nat,
      currentSlots (side n).other (word n) lineage = some (root n))
    (halternates : ∀ n : Nat, side (n + 1) = (side n).other)
    (hparity : NatSeqMinEvenParity (fun n =>
      (codedAlternatingIndexedLineageCodeThreadSystem initialCode currentSlots
        rootPriority).priority
        (codedAlternatingIndexedLineageCodeRun initialCode currentSlots word
          (side 0) lineage n))) :
    NatSeqMinEvenParity (fun n => rootPriority (root n)) := by
  let priorities := fun n =>
    (codedAlternatingIndexedLineageCodeThreadSystem initialCode currentSlots
      rootPriority).priority
      (codedAlternatingIndexedLineageCodeRun initialCode currentSlots word
        (side 0) lineage n)
  have hshift : NatSeqMinEvenParity (fun n => priorities (1 + n)) :=
    (natSeqMinEvenParity_shift priorities 1).mpr hparity
  simpa only [priorities, Nat.one_add,
    codedAlternatingIndexedLineageCodeRun_priority_eq_of_strictAlternation
      initialCode currentSlots rootPriority word side lineage initialRoot root
        hinitial hroot halternates] using hshift

end

end DetParityAutomaton

end DistributedSynthesis
