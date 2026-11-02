/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointUnitFixedPolicyThreadAlignment

/-!
# State-relative physical parity from one fixed-policy code lineage

The fixed-policy alternating thread already supplies an accepted code word
and identifies the live root read by the code-only lineage monitor at every
positive time.  The original endpoint pasted those priorities into a complete
physical word starting at `A.initial`.

After the activated relay flush, the checker instead starts from the exact
state reached by the finite prefix.  This file gives the corresponding
`AcceptsFrom` endpoint directly.  It compares only physical block minima with
the live code-thread roots, so it does not restart a row-dependent DPA state
and does not ask the physical controller to know or reset a proof-side row.
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

namespace ProfiledRawJointUnitFixedPolicyRoot.AlternatingThread

variable {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
variable {initialCode : ProfiledRawJointIncidenceCode A (I := Unit)}
variable (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
  initialCode)

private abbrev ThreadSystem :=
  codedAlternatingIndexedLineageCodeThreadSystem initialCode
    (profiledRawJointOneSidedCurrentSlots A)
    (profiledRawJointThreadRootPriority A)

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Every tail of the literal live-root priority sequence has min-even
parity.  This is the row-free consequence of the accepted fixed-policy code
word. -/
theorem threadRootPriorities_minEven
    (thread : ProfiledRawJointUnitFixedPolicyRoot.AlternatingThread A policy)
    (rootOffset : Nat) :
    NatSeqMinEvenParity (fun k ↦
      profiledRawJointThreadRootPriority A
        (ProfiledRawJointUnitFixedPolicyRoot.threadRoot A policy
          (thread.root (rootOffset + k + 1)))) := by
  let codeWord := fun n ↦ (thread.states A policy (n + 1)).1
  let initialSide :=
    ProfiledRawJointUnitFixedPolicyRoot.side A policy (thread.root 0)
  let priorities := fun n ↦
    (ThreadSystem (initialCode := initialCode) A).priority
      (codedAlternatingIndexedLineageCodeRun initialCode
        (profiledRawJointOneSidedCurrentSlots A) codeWord initialSide () n)
  have hcode := thread.codeWord_accepts A policy
  have hall :=
    (codedAlternatingIndexedLineageCodeDPA_accepts_iff initialCode
      (profiledRawJointOneSidedCurrentSlots A)
      (profiledRawJointThreadRootPriority A) codeWord).mp hcode
  have hparity : NatSeqMinEvenParity priorities := by
    simpa [priorities, ThreadSystem, initialSide, codeWord] using
      hall initialSide ()
  have htail :=
    (natSeqMinEvenParity_shift priorities (rootOffset + 1)).mpr hparity
  convert htail using 1
  funext k
  have halign := thread.codeRun_priority_eq_threadRoot A policy
    (rootOffset + k)
  simpa [priorities, ThreadSystem, initialSide, codeWord, Nat.add_assoc,
    Nat.add_left_comm, Nat.add_comm] using halign.symm

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- State-relative physical acceptance from exact block-minimum alignment
with the fixed policy's live code lineage. -/
theorem physicalTail_acceptsFrom_of_threadRootPriority
    (thread : ProfiledRawJointUnitFixedPolicyRoot.AlternatingThread A policy)
    (physicalState : A.State)
    (physicalTail : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (rootOffset : Nat)
    (cuts : Nat → Nat) (cuts_strictMono : StrictMono cuts)
    (cuts_zero : cuts 0 = 0)
    (blockMin_eq_threadRootPriority : ∀ k : Nat,
      cutBlockMin
          (fun n ↦ A.priority (A.runFrom physicalState physicalTail n))
          cuts k =
        profiledRawJointThreadRootPriority A
          (ProfiledRawJointUnitFixedPolicyRoot.threadRoot A policy
            (thread.root (rootOffset + k + 1)))) :
    A.AcceptsFrom physicalState physicalTail := by
  let priorities := fun n ↦
    A.priority (A.runFrom physicalState physicalTail n)
  have hroot := thread.threadRootPriorities_minEven A policy rootOffset
  have hblocks : NatSeqMinEvenParity (cutBlockMin priorities cuts) := by
    convert hroot using 1
    funext k
    exact blockMin_eq_threadRootPriority k
  change NatSeqMinEvenParity priorities
  exact (natSeqMinEvenParity_cutBlockMin priorities cuts_strictMono
    cuts_zero).mp hblocks

end ProfiledRawJointUnitFixedPolicyRoot.AlternatingThread

end

end DetParityAutomaton

end DistributedSynthesis
