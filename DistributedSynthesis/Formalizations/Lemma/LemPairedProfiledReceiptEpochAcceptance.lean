/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledReceiptOperationalSemantics
import DistributedSynthesis.Formalizations.Lemma.LemFixedPolicyRelationalCandidateTable

/-!
# The exact original-DPA acceptance boundary for a receipt trace

The fixed-policy candidate table and the executable receipt carrier provide
two different facts:

* the table has a proof-only alternating root thread with min-even epoch
  priorities;
* the receipt carrier emits one concrete word read by the original DPA.

Acceptance of the table's hidden monitor is not acceptance of that emitted
word.  The missing mathematical invariant is the usual parity-pasting
coupling: after a finite prefix, the minimum priority of the original DPA on
each concrete receipt epoch must be the priority of the corresponding root
of one alternating fixed-policy thread.  The structure and theorem below
isolate exactly that invariant.

The coupling is proof data only.  It gives neither process a root,
orientation, side, strict-leader flag, optional shape, or hidden bit.

This file also records a fail-fast fact about the present relational
candidate interface.  `RelationalFamilyCandidateGood` passes only the source
descriptor to `ExactEdge`; the source family is erased.  Consequently an old
exact edge is invariant under arbitrary replacement of the source family at
a fixed descriptor.  Such an exact thread cannot, by itself, establish the
source-family-sensitive epoch coupling below.  A concrete repair must make
the source family an argument of the exact edge (or equivalently use the
whole source candidate as its source).
-/

namespace DistributedSynthesis

universe f d m q u v x y s

/-! ## Fail-fast audit of the old exact-thread interface -/

/-- The current relational edge is definitionally blind to the source
family.  In particular, changing that family while preserving the source
descriptor preserves every advertised `Good` edge. -/
theorem relationalFamilyCandidateGood_sourceFamily_irrelevant
    {Family : Type f} {Descriptor : Type d} {Move : Type m} {Query : Type q}
    (ExactEdge : Descriptor → Move → Query → Family → Descriptor → Prop)
    (ControlStep : Descriptor → Descriptor → Prop)
    (sourceFamily sourceFamily' : Family) (source : Descriptor)
    (move : Move) (query : Query)
    (target : RelationalFamilyCandidate Family Descriptor) :
    RelationalFamilyCandidateGood ExactEdge ControlStep
        (sourceFamily, source) move query target ↔
      RelationalFamilyCandidateGood ExactEdge ControlStep
        (sourceFamily', source) move query target := by
  rfl

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
  [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

open PairedStrategyMemory
open PairedStrategyMemory.PairedInitialProfiledRationalPackage

/-! ## The physical-epoch coupling -/

/-- The weakest direct coupling between one finite receipt execution and one
proof-side alternating fixed-policy root thread.

`start` discards the exceptional finite prefix.  The cuts are relative to
that suffix.  `blockMin_eq_rootPriority` is the only semantic field: it says
that the actual original-DPA run over the outputs emitted by the receipt
carrier has exactly the stored epoch minimum at every recurrent root.

No field is executable local information.  In particular, `thread` is not
stored by either process and is not available to any output table. -/
structure EndToEndFamilyReceiptAlternatingEpochCoupling
    {initialState : PairedProfiledTreeState A}
    (policy :
      (pairedProfiledEntryRunAutomaton A initialState).RationalTransitionPolicy)
    (package : PairedInitialProfiledRationalPackage A)
    (initialOne : EndToEndFamilyReceiptOneSummary A package)
    (initialTwo : EndToEndFamilyReceiptTwoSummary A package)
    (receive : EndToEndFamilyReceiptReceivePairTable A package)
    (env : EnvironmentSequence In₁ In₂) where
  start : Nat
  cuts : Nat → Nat
  cuts_strictMono : StrictMono cuts
  cuts_zero : cuts 0 = 0
  thread : ProfiledFixedPolicyRoot.AlternatingThread A policy
  /-- The root reached *after* epoch `k` stores that epoch's minimum.  The
  initial root at index zero is the harmless compressed-tree prefix. -/
  blockMin_eq_rootPriority : ∀ k : Nat,
    cutBlockMin
        (fun n ↦ A.priority
          (A.run
            (endToEndFamilyReceiptTraceWord A package initialOne initialTwo
              receive env)
            (start + n)))
        cuts k =
      pairedProfiledEntryPriority A
        (ProfiledFixedPolicyRoot.state A policy (thread.root (k + 1)))

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- The parity-pasting coupling is sufficient for acceptance by the original
DPA.  This theorem does not use acceptance by the fixed-policy monitor: that
monitor lives over the candidate-table alphabet, whereas the conclusion is
about the concrete `RoundRecord` word emitted by the receipt carrier. -/
theorem endToEndFamilyReceiptTraceWord_accepts_of_alternatingEpochCoupling
    {initialState : PairedProfiledTreeState A}
    (policy :
      (pairedProfiledEntryRunAutomaton A initialState).RationalTransitionPolicy)
    (package : PairedInitialProfiledRationalPackage A)
    (initialOne : EndToEndFamilyReceiptOneSummary A package)
    (initialTwo : EndToEndFamilyReceiptTwoSummary A package)
    (receive : EndToEndFamilyReceiptReceivePairTable A package)
    (env : EnvironmentSequence In₁ In₂)
    (coupling : EndToEndFamilyReceiptAlternatingEpochCoupling A policy package
      initialOne initialTwo receive env) :
    A.Accepts
      (endToEndFamilyReceiptTraceWord A package initialOne initialTwo receive
        env) := by
  let word := endToEndFamilyReceiptTraceWord A package initialOne initialTwo
    receive env
  let priorities : Nat → Nat := fun n ↦ A.priority (A.run word n)
  let tailPriorities : Nat → Nat := fun n ↦ priorities (coupling.start + n)
  have hblocks :
      NatSeqMinEvenParity (cutBlockMin tailPriorities coupling.cuts) := by
    have hepoch := coupling.thread.epochParity A policy
    have hepochTail : NatSeqMinEvenParity (fun k ↦
        pairedProfiledEntryPriority A
          (ProfiledFixedPolicyRoot.state A policy
            (coupling.thread.root (1 + k)))) :=
      (natSeqMinEvenParity_shift
        (fun k ↦ pairedProfiledEntryPriority A
          (ProfiledFixedPolicyRoot.state A policy
            (coupling.thread.root k))) 1).mpr hepoch
    convert hepochTail using 1
    funext k
    dsimp only [tailPriorities, priorities, word]
    rw [Nat.add_comm 1 k]
    exact coupling.blockMin_eq_rootPriority k
  have htail : NatSeqMinEvenParity tailPriorities :=
    (natSeqMinEvenParity_cutBlockMin tailPriorities
      coupling.cuts_strictMono coupling.cuts_zero).mp hblocks
  have hall : NatSeqMinEvenParity priorities :=
    (natSeqMinEvenParity_shift priorities coupling.start).mp htail
  exact (A.accepts_iff_natSeqMinEvenParity word).mpr hall

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Execution-level form of the same endpoint. -/
theorem endToEndFamilyReceipt_execution_accepts_of_alternatingEpochCoupling
    {initialState : PairedProfiledTreeState A}
    (policy :
      (pairedProfiledEntryRunAutomaton A initialState).RationalTransitionPolicy)
    (package : PairedInitialProfiledRationalPackage A)
    (initialOne : EndToEndFamilyReceiptOneSummary A package)
    (initialTwo : EndToEndFamilyReceiptTwoSummary A package)
    (receive : EndToEndFamilyReceiptReceivePairTable A package)
    (env : EnvironmentSequence In₁ In₂)
    (coupling : EndToEndFamilyReceiptAlternatingEpochCoupling A policy package
      initialOne initialTwo receive env) :
    A.Accepts
      (execution
        (endToEndFamilyReceiptStrategy A package initialOne initialTwo receive)
        env) := by
  exact
    (endToEndFamilyReceipt_accepts_execution_iff_traceWord A package initialOne
      initialTwo receive env).mpr
      (endToEndFamilyReceiptTraceWord_accepts_of_alternatingEpochCoupling A
        policy package initialOne initialTwo receive env coupling)

end

end DetParityAutomaton

end DistributedSynthesis
