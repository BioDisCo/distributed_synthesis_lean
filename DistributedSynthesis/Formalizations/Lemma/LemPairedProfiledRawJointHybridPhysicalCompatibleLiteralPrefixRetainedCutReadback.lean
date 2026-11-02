/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleLiteralPrefixRetainedCarrierTrace
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleShadowPhaseLiveTailRootAlignedCutStream

/-!
# Root-aligned cut readback for the retained literal carrier

The retained controller has an exact, row-aware reference word.  The generic
tail acceptance layer, on the other hand, consumes root-aligned packets for a
finite controller's actual trace word.  This file is the adapter between those
two interfaces.

Packet proofs below are stated directly on the retained reference word.  The
proved whole-word equality transports them to the actual finite controller,
after which the existing root-aligned cut-stream theorem supplies parity
acceptance.  In particular, this route never uses the obsolete tail output
contracts that hard-code row `.both` at every strict receive.

The remaining mathematical premise is exposed as one structure: at every cut
one must supply the exact hidden-lineage transition and identify the physical
block minimum with the priority of that same root, together with a finite-state
decoder for the cut states.  No further output or readback equation is owed.
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

private abbrev RightMove :=
  ProfiledRawJointGuardedCommonRightLiteralCrossMove A

private abbrev LeftMove :=
  ProfiledRawJointGuardedCommonLeftLiteralCrossMove A

private abbrev Controller
    (rightMove : RightMove A) (leftMove : LeftMove A)
    (rightAnchor leftAnchor : Bool) :=
  profiledRawJointHybridLiteralPrefixRetainedController A rightMove leftMove
    rightAnchor leftAnchor

private abbrev Tag :=
  ProfiledRawJointHybridShadowPhaseLiveTag A strategy hwin

private abbrev TailState (tag : Tag A strategy hwin) :=
  ProfiledRawJointHybridShadowPhaseLiveTailState A strategy hwin tag

/-- One root-aligned packet whose parity equation is stated on the exact
row-aware reference word rather than on the finite controller trace word. -/
structure
    ProfiledRawJointHybridLiteralPrefixRetainedReferenceCutPacketAt
    (rightMove : RightMove A) (leftMove : LeftMove A)
    (rightAnchor leftAnchor : Bool)
    (env : EnvironmentSequence In₁ In₂)
    (tag : Tag A strategy hwin)
    (start : Nat) (cuts : Nat → Nat)
    (initialSide : IndexedLineageSide)
    (state : Nat → TailState A strategy hwin tag) (k : Nat) where
  root : ProfiledRawJointThreadRoot A
  transition :
    ProfiledRawJointHybridShadowPhaseLiveTailRootAlignedTransitionAt A strategy
      hwin tag (state k) (state (k + 1))
        (profiledRawJointHybridPhysicalCompatibleSideAfter initialSide (k + 2))
        root
  blockMin_eq_rootPriority :
    cutBlockMin
        (fun n ↦ A.priority
          (A.run
            (profiledRawJointHybridLiteralPrefixRetainedReferenceWord A
              rightMove leftMove rightAnchor leftAnchor env)
            (start + n)))
        cuts k =
      profiledRawJointThreadRootPriority A root

namespace
  ProfiledRawJointHybridLiteralPrefixRetainedReferenceCutPacketAt

/-- Transport a reference-word packet to the actual retained finite
controller.  The transition component is unchanged; only the word occurring
in the block-minimum equation is rewritten. -/
noncomputable def toPhysical
    {rightMove : RightMove A} {leftMove : LeftMove A}
    {rightAnchor leftAnchor : Bool}
    {env : EnvironmentSequence In₁ In₂}
    {tag : Tag A strategy hwin}
    {start : Nat} {cuts : Nat → Nat}
    {initialSide : IndexedLineageSide}
    {state : Nat → TailState A strategy hwin tag} {k : Nat}
    (packet :
      ProfiledRawJointHybridLiteralPrefixRetainedReferenceCutPacketAt A
        strategy hwin rightMove leftMove rightAnchor leftAnchor env tag start
        cuts initialSide state k) :
    ProfiledRawJointHybridShadowPhaseLiveTailRootAlignedPhysicalCutPacketAt A
      strategy hwin tag
        (Controller A rightMove leftMove rightAnchor leftAnchor).globalMachine
        (Controller A rightMove leftMove rightAnchor leftAnchor).globalOutputOne
        (Controller A rightMove leftMove rightAnchor leftAnchor).globalOutputTwo
        env start cuts initialSide state k := by
  refine {
    root := packet.root
    transition := packet.transition
    blockMin_eq_rootPriority := ?_ }
  rw [profiledRawJointHybridLiteralPrefixRetained_globalMachineTraceWord_eq A
    rightMove leftMove rightAnchor leftAnchor env]
  exact packet.blockMin_eq_rootPriority

end
  ProfiledRawJointHybridLiteralPrefixRetainedReferenceCutPacketAt

/-- A complete reference-word packet stream.  The canonical lineage seed of
the delayed tag supplies its initial side and first two live roots. -/
structure ProfiledRawJointHybridLiteralPrefixRetainedReferenceCutStream
    (rightMove : RightMove A) (leftMove : LeftMove A)
    (rightAnchor leftAnchor : Bool)
    (env : EnvironmentSequence In₁ In₂)
    (tag : Tag A strategy hwin)
    (start : Nat) (cuts : Nat → Nat) where
  state : Nat → TailState A strategy hwin tag
  state_zero : state 0 = (tag.tailCodePolicy A strategy hwin).run []
  state_zero_code : (state 0).1.1 = (tag.childCode A strategy hwin).1
  packet : ∀ k : Nat,
    ProfiledRawJointHybridLiteralPrefixRetainedReferenceCutPacketAt A strategy
      hwin rightMove leftMove rightAnchor leftAnchor env tag start cuts
        (tag.lineageSeed A strategy hwin).initialSide state k

namespace ProfiledRawJointHybridLiteralPrefixRetainedReferenceCutStream

/-- Turn a packet stream on the row-aware reference word into the generic
physical packet stream for the genuine retained controller. -/
noncomputable def toPhysical
    {rightMove : RightMove A} {leftMove : LeftMove A}
    {rightAnchor leftAnchor : Bool}
    {env : EnvironmentSequence In₁ In₂}
    {tag : Tag A strategy hwin}
    {start : Nat} {cuts : Nat → Nat}
    (stream :
      ProfiledRawJointHybridLiteralPrefixRetainedReferenceCutStream A strategy
        hwin rightMove leftMove rightAnchor leftAnchor env tag start cuts) :
    ProfiledRawJointHybridShadowPhaseLiveTailRootAlignedPhysicalCutStream A
      strategy hwin tag
        (Controller A rightMove leftMove rightAnchor leftAnchor).globalMachine
        (Controller A rightMove leftMove rightAnchor leftAnchor).globalOutputOne
        (Controller A rightMove leftMove rightAnchor leftAnchor).globalOutputTwo
        env start cuts :=
  ProfiledRawJointHybridShadowPhaseLiveTailRootAlignedPhysicalCutStream.ofPackets
    A strategy hwin tag
      (Controller A rightMove leftMove rightAnchor leftAnchor).globalMachine
      (Controller A rightMove leftMove rightAnchor leftAnchor).globalOutputOne
      (Controller A rightMove leftMove rightAnchor leftAnchor).globalOutputTwo
      env start cuts stream.state stream.state_zero stream.state_zero_code
      (fun k ↦ (stream.packet k).toPhysical A strategy hwin)

end ProfiledRawJointHybridLiteralPrefixRetainedReferenceCutStream

/-- The exact residual consumed by the retained-carrier readback endpoint.
It contains only root-aligned packets, cut arithmetic, and the finite-state
decoder at cut boundaries. -/
structure ProfiledRawJointHybridLiteralPrefixRetainedCutReadback
    (rightMove : RightMove A) (leftMove : LeftMove A)
    (rightAnchor leftAnchor : Bool)
    (env : EnvironmentSequence In₁ In₂)
    (tag : Tag A strategy hwin)
    (start : Nat) (cuts : Nat → Nat) where
  stream :
    ProfiledRawJointHybridLiteralPrefixRetainedReferenceCutStream A strategy
      hwin rightMove leftMove rightAnchor leftAnchor env tag start cuts
  cuts_strictMono : StrictMono cuts
  cuts_zero : cuts 0 = 0
  closeState :
    (Controller A rightMove leftMove rightAnchor leftAnchor).globalMachine.State
      → TailState A strategy hwin tag
  closeState_eq : ∀ n : Nat,
    closeState
        ((Controller A rightMove leftMove rightAnchor leftAnchor).globalMachine
          |>.globalStateTrace env (start + cuts n)) =
      stream.state n

namespace ProfiledRawJointHybridLiteralPrefixRetainedCutReadback

/-- The retained finite controller accepts whenever the row-parametric cut
readback premise is supplied. -/
theorem controller_accepts
    {rightMove : RightMove A} {leftMove : LeftMove A}
    {rightAnchor leftAnchor : Bool}
    {env : EnvironmentSequence In₁ In₂}
    {tag : Tag A strategy hwin}
    {start : Nat} {cuts : Nat → Nat}
    (readback :
      ProfiledRawJointHybridLiteralPrefixRetainedCutReadback A strategy hwin
        rightMove leftMove rightAnchor leftAnchor env tag start cuts) :
    A.Accepts
      ((Controller A rightMove leftMove rightAnchor leftAnchor).globalMachine
        |>.globalMachineTraceWord
          (Controller A rightMove leftMove rightAnchor leftAnchor).globalOutputOne
          (Controller A rightMove leftMove rightAnchor leftAnchor).globalOutputTwo
          env) :=
  (readback.stream.toPhysical A strategy hwin).accepts A strategy hwin
    readback.cuts_strictMono readback.cuts_zero readback.closeState
    readback.closeState_eq

/-- Equivalent acceptance endpoint stated on the exact row-aware reference
word. -/
theorem referenceWord_accepts
    {rightMove : RightMove A} {leftMove : LeftMove A}
    {rightAnchor leftAnchor : Bool}
    {env : EnvironmentSequence In₁ In₂}
    {tag : Tag A strategy hwin}
    {start : Nat} {cuts : Nat → Nat}
    (readback :
      ProfiledRawJointHybridLiteralPrefixRetainedCutReadback A strategy hwin
        rightMove leftMove rightAnchor leftAnchor env tag start cuts) :
    A.Accepts
      (profiledRawJointHybridLiteralPrefixRetainedReferenceWord A rightMove
        leftMove rightAnchor leftAnchor env) := by
  rw [←
    profiledRawJointHybridLiteralPrefixRetained_globalMachineTraceWord_eq A
      rightMove leftMove rightAnchor leftAnchor env]
  exact readback.controller_accepts A strategy hwin

end ProfiledRawJointHybridLiteralPrefixRetainedCutReadback

end

end DetParityAutomaton

end DistributedSynthesis
