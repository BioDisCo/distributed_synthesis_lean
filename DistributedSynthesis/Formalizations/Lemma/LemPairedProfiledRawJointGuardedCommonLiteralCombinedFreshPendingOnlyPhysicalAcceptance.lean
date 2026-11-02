/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCombinedFreshPendingOnlyInitial
import DistributedSynthesis.Formalizations.Theorem.ThmParityBlockPasting

/-!
# Physical acceptance of the pending-only literal-table carrier

The recursively refreshed common-policy path already supplies one accepted
word of exact installed child codes.  The finite acknowledged controller also
already supplies its exact proof-side reference word.  This file isolates the
only semantic seam between those two completed constructions.

A coupling chooses productive proof-side cuts of the reference word and one
hidden alternating lineage of the installed-child code word.  Its sole
model-specific equation says that each original-DPA block minimum is the
priority of that lineage.  The generic parity-pasting argument below then
proves acceptance of both the reference word and the actual finite-controller
trace.

The cuts, side, offset, and lineage are proof objects.  No executable map is
given a graph, orientation, hierarchy side, leader bit, history, view, or
global branch selector.  In particular this interface does not assume an
unsound pointwise identification between a freshly installed code and the
old table that emits the current strict-round output.
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
variable [DecidableEq In₁] [DecidableEq In₂]

variable
  (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
  (hwin : ∀ env : EnvironmentSequence In₁ In₂,
    A.Accepts (execution strategy env))

private abbrev CommonPoint :=
  ProfiledRawJointGuardedCommonSemanticPoint A strategy

private abbrev CrossValid :=
  ProfiledRawJointGuardedCommonLiteralCrossExtraValid A strategy hwin

namespace ProfiledRawJointGuardedCommonDecoratedPolicyPackage

variable {initial : CommonPoint A strategy}

private abbrev Package :=
  ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy hwin initial
    (CrossValid A strategy hwin)

/-! ## The two already constructed words -/

/-- Input-pair stream seen by the common decorated policy. -/
def literalCombinedFreshPendingOnlyInputWord
    (env : EnvironmentSequence In₁ In₂) : Nat → In₁ × In₂ :=
  fun n ↦ ((env n).inputOne, (env n).inputTwo)

/-- Proof-side graph stream used only to iterate the leader-free freshness
invariant. -/
def literalCombinedFreshPendingOnlyGraphWord
    (env : EnvironmentSequence In₁ In₂) : Nat → Graph :=
  fun n ↦ (env n).graph

/-- Common installed-child codes tagged for the existing hybrid code DPA. -/
def literalCombinedFreshPendingOnlyInstalledTaggedCodeWord
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) :
    OmegaWord (ProfiledRawJointHybridCode A) :=
  fun n ↦ .common
    (package.literalCombinedFreshPendingInstalledChildCodeWord A strategy hwin
      (literalCombinedFreshPendingOnlyInputWord env)
      (literalCombinedFreshPendingOnlyGraphWord env) n)

/-- The exact proof-side physical word exposed by the pending-only trace
invariant.  The acknowledgement carrier's actual word is already proved equal
to this word in `literalCombinedFreshPendingOnlyRootTraceWord_eq_referenceWord`.
-/
def literalCombinedFreshPendingOnlyRootReferenceWord
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) :
    OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂) :=
  let controller :=
    package.literalCombinedFreshPendingOnlyRootPhysicalController A strategy
      hwin
  (package.literalCombinedFreshPendingOnlyRootTraceInvariant A strategy hwin
    env).referenceWord controller

/-! ## Exact remaining priority coupling -/

/-- The smallest physical/code coupling left after recursive code acceptance
and exact controller readback.

The `start` prefix permits the harmless arbitrary initial table.  The cuts are
relative to the remaining physical suffix.  The final field is deliberately
an equality of priorities, not an equality of semantic representatives or of
entire physical words. -/
structure LiteralCombinedFreshPendingOnlyRootPhysicalPriorityCoupling
    (package : Package A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) where
  start : Nat
  cuts : Nat → Nat
  cuts_strictMono : StrictMono cuts
  cuts_zero : cuts 0 = 0
  initialSide : IndexedLineageSide
  offset : Nat
  blockMin_eq_threadPriority : ∀ k : Nat,
    cutBlockMin
        (fun n ↦ A.priority
          (A.run
            (package.literalCombinedFreshPendingOnlyRootReferenceWord A
              strategy hwin env)
            (start + n)))
        cuts k =
      (codedAlternatingIndexedLineageCodeThreadSystem
          (.common (initial.code A strategy))
          (profiledRawJointHybridCurrentSlots A)
          (profiledRawJointThreadRootPriority A)).priority
        (codedAlternatingIndexedLineageCodeRun
          (.common (initial.code A strategy))
          (profiledRawJointHybridCurrentSlots A)
          (package.literalCombinedFreshPendingOnlyInstalledTaggedCodeWord A
            strategy hwin env)
          initialSide () (offset + k))

namespace LiteralCombinedFreshPendingOnlyRootPhysicalPriorityCoupling

/-- The accepted common-policy path is accepted after inserting the common
tag expected by the hybrid code objective. -/
theorem installedTaggedCodeWord_accepts
    {package : Package A strategy hwin (initial := initial)}
    (env : EnvironmentSequence In₁ In₂) :
    (profiledRawJointHybridCodeParityDPA A
      (.common (initial.code A strategy))).Accepts
        (package.literalCombinedFreshPendingOnlyInstalledTaggedCodeWord A
          strategy hwin env) := by
  have hcommon :=
    package.literalCombinedFreshPendingInstalledChildCodeWord_accepts A
      strategy hwin (literalCombinedFreshPendingOnlyInputWord env)
        (literalCombinedFreshPendingOnlyGraphWord env)
  change
    (profiledRawJointGuardedCommonCodeParityDPA A
      (initial.code A strategy)).Accepts _ at hcommon
  rw [profiledRawJointGuardedCommonCodeParityDPA,
    DetParityAutomaton.comap_accepts_iff] at hcommon
  simpa [literalCombinedFreshPendingOnlyInstalledTaggedCodeWord] using hcommon

/-- The priority coupling transfers the accepted hidden code lineage through
productive physical cuts to the original DPA reference word. -/
theorem referenceWord_accepts
    {package : Package A strategy hwin (initial := initial)}
    {env : EnvironmentSequence In₁ In₂}
    (coupling :
      LiteralCombinedFreshPendingOnlyRootPhysicalPriorityCoupling A strategy
        hwin package env) :
    A.Accepts
      (package.literalCombinedFreshPendingOnlyRootReferenceWord A strategy
        hwin env) := by
  let initialCode : ProfiledRawJointHybridCode A :=
    .common (initial.code A strategy)
  let codeWord :=
    package.literalCombinedFreshPendingOnlyInstalledTaggedCodeWord A strategy
      hwin env
  let codePriorities : Nat → Nat := fun n ↦
    (codedAlternatingIndexedLineageCodeThreadSystem initialCode
      (profiledRawJointHybridCurrentSlots A)
      (profiledRawJointThreadRootPriority A)).priority
      (codedAlternatingIndexedLineageCodeRun initialCode
        (profiledRawJointHybridCurrentSlots A) codeWord coupling.initialSide ()
          n)
  let word :=
    package.literalCombinedFreshPendingOnlyRootReferenceWord A strategy hwin
      env
  let priorities : Nat → Nat := fun n ↦ A.priority (A.run word n)
  let tailPriorities : Nat → Nat := fun n ↦
    priorities (coupling.start + n)
  have hcode := installedTaggedCodeWord_accepts A strategy hwin env
    (package := package)
  have hall :=
    (codedAlternatingIndexedLineageCodeDPA_accepts_iff initialCode
      (profiledRawJointHybridCurrentSlots A)
      (profiledRawJointThreadRootPriority A) codeWord).mp hcode
  have hcodeParity : NatSeqMinEvenParity codePriorities := by
    simpa [codePriorities, initialCode, codeWord] using
      hall coupling.initialSide ()
  have hcodeTail :
      NatSeqMinEvenParity (fun n ↦ codePriorities (coupling.offset + n)) :=
    (natSeqMinEvenParity_shift codePriorities coupling.offset).mpr hcodeParity
  have hblocks :
      NatSeqMinEvenParity (cutBlockMin tailPriorities coupling.cuts) := by
    convert hcodeTail using 1
    funext k
    exact coupling.blockMin_eq_threadPriority k
  have htail : NatSeqMinEvenParity tailPriorities :=
    (natSeqMinEvenParity_cutBlockMin tailPriorities
      coupling.cuts_strictMono coupling.cuts_zero).mp hblocks
  have hallPhysical : NatSeqMinEvenParity priorities :=
    (natSeqMinEvenParity_shift priorities coupling.start).mp htail
  exact (A.accepts_iff_natSeqMinEvenParity word).mpr hallPhysical

/-- Rewriting by the existing trace invariant gives acceptance of the actual
finite pending-only controller word. -/
theorem rootTraceWord_accepts
    {package : Package A strategy hwin (initial := initial)}
    {env : EnvironmentSequence In₁ In₂}
    (coupling :
      LiteralCombinedFreshPendingOnlyRootPhysicalPriorityCoupling A strategy
        hwin package env) :
    let controller :=
      package.literalCombinedFreshPendingOnlyRootPhysicalController A strategy
        hwin
    A.Accepts
      (controller.globalMachine.globalMachineTraceWord
        controller.globalOutputOne controller.globalOutputTwo env) := by
  dsimp only
  rw [package.literalCombinedFreshPendingOnlyRootTraceWord_eq_referenceWord A
    strategy hwin env]
  exact coupling.referenceWord_accepts A strategy hwin

end LiteralCombinedFreshPendingOnlyRootPhysicalPriorityCoupling

end ProfiledRawJointGuardedCommonDecoratedPolicyPackage

end

end DetParityAutomaton

end DistributedSynthesis
