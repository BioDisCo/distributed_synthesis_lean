/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleShadowPhaseLiveTailRootAlignedAcceptanceBridge
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleShadowPhaseLiveTailLineageSeed

/-!
# Root-aligned physical cut streams in one delayed-tag fibre

The concrete controller induction naturally produces one packet at a time:
an exact root-aligned tail transition and the physical block minimum at that
same root.  This file packages those packets into the root-aligned path and
physical trace bookkeeping consumed by the final acceptance bridge.

All sides and roots are proof-side indices.  No executable endpoint map is
extended by them.
-/

namespace DistributedSynthesis

universe u v x y s w

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

private abbrev Tag :=
  ProfiledRawJointHybridShadowPhaseLiveTag A strategy hwin

private abbrev TailState (tag : Tag A strategy hwin) :=
  ProfiledRawJointHybridShadowPhaseLiveTailState A strategy hwin tag

/-- One controller cut already normalized to the hidden-lineage side at this
cut.  The transition and physical minimum retain literally the same root. -/
structure
    ProfiledRawJointHybridShadowPhaseLiveTailRootAlignedPhysicalCutPacketAt
    (tag : Tag A strategy hwin)
    (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (env : EnvironmentSequence In₁ In₂)
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
          (A.run (G.globalMachineTraceWord outputOne outputTwo env)
            (start + n)))
        cuts k =
      profiledRawJointThreadRootPriority A root

/-- A complete stream of root-aligned cut packets.  The finite controller
trace proof only has to instantiate this structure; path construction and
parity alignment are generic. -/
structure
    ProfiledRawJointHybridShadowPhaseLiveTailRootAlignedPhysicalCutStream
    (tag : Tag A strategy hwin)
    (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (env : EnvironmentSequence In₁ In₂)
    (start : Nat) (cuts : Nat → Nat) where
  state : Nat → TailState A strategy hwin tag
  state_zero : state 0 = (tag.tailCodePolicy A strategy hwin).run []
  state_zero_code : (state 0).1.1 = (tag.childCode A strategy hwin).1
  initialSide : IndexedLineageSide
  initialRoot : ProfiledRawJointThreadRoot A
  initial_live :
    let installed :=
      profiledRawJointHybridShadowPhaseLiveInstalled A strategy hwin tag.origin
    let initialCode : ProfiledRawJointHybridCode A :=
      .common ((profiledRawJointCommonWorldFamily A installed.world
        ).incidenceCode A)
    profiledRawJointHybridCurrentSlots A initialSide initialCode () =
      some initialRoot
  childRoot : ProfiledRawJointThreadRoot A
  child_live :
    profiledRawJointHybridCurrentSlots A
        (profiledRawJointHybridPhysicalCompatibleSideAfter initialSide 1)
        (tag.childCode A strategy hwin).1 () =
      some childRoot
  packet : ∀ k : Nat,
    ProfiledRawJointHybridShadowPhaseLiveTailRootAlignedPhysicalCutPacketAt A
      strategy hwin tag G outputOne outputTwo env start cuts initialSide state k

namespace
  ProfiledRawJointHybridShadowPhaseLiveTailRootAlignedPhysicalCutStream

/-- Canonical constructor using the unconditional proof-side lineage seed of
the delivered tag.  Concrete trace proofs supply only their tail-state stream
and one exact physical packet at every cut. -/
noncomputable def ofPackets
    (tag : Tag A strategy hwin)
    (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (env : EnvironmentSequence In₁ In₂)
    (start : Nat) (cuts : Nat → Nat)
    (state : Nat → TailState A strategy hwin tag)
    (state_zero : state 0 = (tag.tailCodePolicy A strategy hwin).run [])
    (state_zero_code : (state 0).1.1 = (tag.childCode A strategy hwin).1)
    (packet : ∀ k : Nat,
      ProfiledRawJointHybridShadowPhaseLiveTailRootAlignedPhysicalCutPacketAt A
        strategy hwin tag G outputOne outputTwo env start cuts
          (tag.lineageSeed A strategy hwin).initialSide state k) :
    ProfiledRawJointHybridShadowPhaseLiveTailRootAlignedPhysicalCutStream A
      strategy hwin tag G outputOne outputTwo env start cuts := by
  let seed := tag.lineageSeed A strategy hwin
  exact {
    state := state
    state_zero := state_zero
    state_zero_code := state_zero_code
    initialSide := seed.initialSide
    initialRoot := seed.initialRoot
    initial_live := seed.initial_live
    childRoot := seed.childRoot
    child_live := seed.child_live
    packet := packet }

/-- Forget the physical equations and retain the coherent hidden-lineage
branch. -/
noncomputable def rootAlignedPath
    {tag : Tag A strategy hwin}
    {G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂}
    {outputOne : G.State → Out₁} {outputTwo : G.State → Out₂}
    {env : EnvironmentSequence In₁ In₂}
    {start : Nat} {cuts : Nat → Nat}
    (stream :
      ProfiledRawJointHybridShadowPhaseLiveTailRootAlignedPhysicalCutStream A
        strategy hwin tag G outputOne outputTwo env start cuts) :
    ProfiledRawJointHybridShadowPhaseLiveTailRootAlignedPath A strategy hwin
      tag where
  state := stream.state
  state_zero := stream.state_zero
  state_zero_code := stream.state_zero_code
  initialSide := stream.initialSide
  initialRoot := stream.initialRoot
  initial_live := stream.initial_live
  childRoot := stream.childRoot
  child_live := stream.child_live
  rootAt := fun k ↦ (stream.packet k).root
  transition := fun k ↦ (stream.packet k).transition

/-- Add only the finite-machine cut decoding.  The packet stream supplies the
whole mathematical content of the acceptance bridge. -/
noncomputable def physicalTraceBookkeeping
    {tag : Tag A strategy hwin}
    {G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂}
    {outputOne : G.State → Out₁} {outputTwo : G.State → Out₂}
    {env : EnvironmentSequence In₁ In₂}
    {start : Nat} {cuts : Nat → Nat}
    (stream :
      ProfiledRawJointHybridShadowPhaseLiveTailRootAlignedPhysicalCutStream A
        strategy hwin tag G outputOne outputTwo env start cuts)
    (cuts_strictMono : StrictMono cuts) (cuts_zero : cuts 0 = 0)
    (closeState : G.State → TailState A strategy hwin tag)
    (closeState_eq : ∀ n : Nat,
      closeState (G.globalStateTrace env (start + cuts n)) = stream.state n) :
    ProfiledRawJointHybridShadowPhaseLiveTailRootAlignedPhysicalTraceBookkeeping
      A strategy hwin tag G outputOne outputTwo env start cuts where
  cuts_strictMono := cuts_strictMono
  cuts_zero := cuts_zero
  closeState := closeState
  path := stream.rootAlignedPath A strategy hwin
  closeState_eq_path := closeState_eq
  blockMin_eq_rootPriority := fun k ↦
    (stream.packet k).blockMin_eq_rootPriority

/-- Direct construction of the hard-regime certificate retained by the final
strategy-indexed controller bookkeeping. -/
noncomputable def physicalAcceptanceCertificate
    {tag : Tag A strategy hwin}
    {G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂}
    {outputOne : G.State → Out₁} {outputTwo : G.State → Out₂}
    {env : EnvironmentSequence In₁ In₂}
    {start : Nat} {cuts : Nat → Nat}
    (stream :
      ProfiledRawJointHybridShadowPhaseLiveTailRootAlignedPhysicalCutStream A
        strategy hwin tag G outputOne outputTwo env start cuts)
    (cuts_strictMono : StrictMono cuts) (cuts_zero : cuts 0 = 0)
    (closeState : G.State → TailState A strategy hwin tag)
    (closeState_eq : ∀ n : Nat,
      closeState (G.globalStateTrace env (start + cuts n)) = stream.state n) :
    ProfiledRawJointHybridShadowPhaseLivePhysicalAcceptanceCertificate A
      strategy hwin tag G outputOne outputTwo env start cuts :=
  (stream.physicalTraceBookkeeping A strategy hwin cuts_strictMono cuts_zero
    closeState closeState_eq).physicalAcceptanceCertificate A strategy hwin

/-- Direct acceptance endpoint for a complete packet stream. -/
theorem accepts
    {tag : Tag A strategy hwin}
    {G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂}
    {outputOne : G.State → Out₁} {outputTwo : G.State → Out₂}
    {env : EnvironmentSequence In₁ In₂}
    {start : Nat} {cuts : Nat → Nat}
    (stream :
      ProfiledRawJointHybridShadowPhaseLiveTailRootAlignedPhysicalCutStream A
        strategy hwin tag G outputOne outputTwo env start cuts)
    (cuts_strictMono : StrictMono cuts) (cuts_zero : cuts 0 = 0)
    (closeState : G.State → TailState A strategy hwin tag)
    (closeState_eq : ∀ n : Nat,
      closeState (G.globalStateTrace env (start + cuts n)) = stream.state n) :
    A.Accepts (G.globalMachineTraceWord outputOne outputTwo env) :=
  (stream.physicalAcceptanceCertificate A strategy hwin cuts_strictMono
    cuts_zero closeState closeState_eq).accepts A strategy hwin

end
  ProfiledRawJointHybridShadowPhaseLiveTailRootAlignedPhysicalCutStream

end

end DetParityAutomaton

end DistributedSynthesis
