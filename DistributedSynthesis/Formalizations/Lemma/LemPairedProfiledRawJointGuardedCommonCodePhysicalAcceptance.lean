/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonTreeRationalization

/-!
# Common-code parity transfers to a physical word

The occurrence-sensitive common-code objective already checks every hidden
alternating side.  A concrete local controller therefore does not need to
reprove parity.  It only has to identify one checked hidden-thread priority
with the original DPA priority of its physical trace, up to finite offsets.

This file packages that last handoff.  `GuardedCommonCodePhysicalCoupling`
contains only proof-side data: a side, two offsets, and the pointwise priority
equation.  It is never supplied to an executable endpoint and does not reveal
a graph, orientation, leader, strict leader, history, or semantic view.
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

private abbrev CommonCode :=
  ProfiledRawJointIncidenceCode A (I := Unit)

/-! ## The checked hidden common-code thread -/

/-- Tag a bare common-code stream for the existing hybrid hidden-thread
monitor. -/
def guardedCommonTaggedCodeWord
    (word : OmegaWord (CommonCode A)) :
    OmegaWord (ProfiledRawJointHybridCode A) :=
  OmegaWord.map ProfiledRawJointHybridCode.common word

/-- Priority sequence of one proof-side hidden thread in a common-code word. -/
noncomputable def guardedCommonCodeThreadPriorities
    (initialCode : CommonCode A)
    (word : OmegaWord (CommonCode A))
    (initialSide : IndexedLineageSide) : Nat → Nat :=
  fun n ↦
    (codedAlternatingIndexedLineageCodeThreadSystem
      (.common initialCode)
      (profiledRawJointHybridCurrentSlots A)
      (profiledRawJointThreadRootPriority A)).priority
      (codedAlternatingIndexedLineageCodeRun
        (.common initialCode)
        (profiledRawJointHybridCurrentSlots A)
        (guardedCommonTaggedCodeWord A word)
        initialSide () n)

/-! ## Exact physical coupling -/

/-- The sole concrete fact needed to transfer common-code acceptance to one
physical word.  The two offsets independently discard finite code and
physical prefixes. -/
structure GuardedCommonCodePhysicalCoupling
    (initialCode : CommonCode A)
    (codeWord : OmegaWord (CommonCode A))
    (physicalWord : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    where
  initialSide : IndexedLineageSide
  codeOffset : Nat
  physicalOffset : Nat
  priority_eq : ∀ n,
    guardedCommonCodeThreadPriorities A initialCode codeWord initialSide
        (codeOffset + n) =
      A.priority (A.run physicalWord (physicalOffset + n))

namespace GuardedCommonCodePhysicalCoupling

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Accepted common codes plus the pointwise coupling imply acceptance of the
actual original-DPA word. -/
theorem physicalWord_accepts
    {initialCode : CommonCode A}
    {codeWord : OmegaWord (CommonCode A)}
    {physicalWord :
      OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂)}
    (coupling : GuardedCommonCodePhysicalCoupling A initialCode codeWord
      physicalWord)
    (hcode :
      (profiledRawJointGuardedCommonCodeParityDPA A initialCode).Accepts
        codeWord) :
    A.Accepts physicalWord := by
  let taggedWord := guardedCommonTaggedCodeWord A codeWord
  let codePriorities := guardedCommonCodeThreadPriorities A initialCode
    codeWord coupling.initialSide
  let physicalPriorities := fun n ↦ A.priority (A.run physicalWord n)
  have htagged :
      (profiledRawJointHybridCodeParityDPA A (.common initialCode)).Accepts
        taggedWord := by
    rw [profiledRawJointGuardedCommonCodeParityDPA,
      DetParityAutomaton.comap_accepts_iff] at hcode
    simpa [taggedWord, guardedCommonTaggedCodeWord] using hcode
  have hcoded :
      (codedAlternatingIndexedLineageCodeDPA (.common initialCode)
        (profiledRawJointHybridCurrentSlots A)
        (profiledRawJointThreadRootPriority A)).Accepts taggedWord := by
    simpa [profiledRawJointHybridCodeParityDPA] using htagged
  have hall :=
    (codedAlternatingIndexedLineageCodeDPA_accepts_iff
      (.common initialCode)
      (profiledRawJointHybridCurrentSlots A)
      (profiledRawJointThreadRootPriority A) taggedWord).1 hcoded
  have hcodeParity : NatSeqMinEvenParity codePriorities := by
    simpa [codePriorities, guardedCommonCodeThreadPriorities, taggedWord]
      using hall coupling.initialSide ()
  have hcodeTail : NatSeqMinEvenParity
      (fun n ↦ codePriorities (coupling.codeOffset + n)) :=
    (natSeqMinEvenParity_shift codePriorities coupling.codeOffset).mpr
      hcodeParity
  have hphysicalTail : NatSeqMinEvenParity
      (fun n ↦ physicalPriorities (coupling.physicalOffset + n)) := by
    convert hcodeTail using 1
    funext n
    exact (coupling.priority_eq n).symm
  rw [A.accepts_iff_natSeqMinEvenParity]
  exact
    (natSeqMinEvenParity_shift physicalPriorities coupling.physicalOffset).mp
      hphysicalTail

end GuardedCommonCodePhysicalCoupling

end

end DetParityAutomaton

end DistributedSynthesis
