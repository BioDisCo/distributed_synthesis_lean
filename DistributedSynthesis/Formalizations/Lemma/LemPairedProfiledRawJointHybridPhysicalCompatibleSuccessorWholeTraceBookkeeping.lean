/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleSuccessorActualHandlerCut
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleSuccessorInstalledFixedTailBookkeeping

/-!
# Whole-trace packets at the resolved-controller boundary

This file is the controller-independent last-mile adapter for the two hard
physical regimes.  A witness consists of the already checked common-root
`SuccessorInitialExit`, a strict cut schedule starting at zero, and at every
later cut either the right or left four-part transition packet.  The side is
only a proof index of the packet; it is never exposed to an endpoint.

The witness constructs a `ResolvedMemberStream` directly.  Regime-indexed
witnesses therefore supply the exact recurrent and reversal fields of
`LiteralCompatibleSuccessorResolvedControllerBookkeeping`.  Combining them
with `EventuallyInstalledFixedTailBookkeeping` closes all four physical
regimes for the same newly constructed controller word.
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

private abbrev CompatiblePolicy
    (initial : ProfiledRawJointCommonBaseWorld A strategy) :=
  ProfiledRawJointHybridPhysicalCompatibleRationalPolicy A strategy hwin
    initial

private abbrev CompatibleState
    (initial : ProfiledRawJointCommonBaseWorld A strategy) :=
  ProfiledRawJointHybridPhysicalCompatiblePolicyState A strategy hwin initial

private abbrev SuccessorTarget
    (initial : ProfiledRawJointCommonBaseWorld A strategy) :=
  ProfiledRawJointHybridPhysicalCompatibleSuccessorTarget A strategy hwin
    initial

/-! ## One orientation-indexed transition packet -/

/-- A literal later-cut packet, in either physical orientation.

The first three conjuncts are exactly what `ResolvedMemberBoundaryAt`
consumes.  The fourth is the next-cut DPA state supplied by the actual packet;
it remains available to the whole-trace induction even though the boundary
erasure itself does not need to inspect it. -/
inductive ProfiledRawJointHybridPhysicalCompatibleResolvedTransitionPacketAt
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (env : EnvironmentSequence In₁ In₂)
    (initialSide : IndexedLineageSide)
    (state : Nat → CompatibleState A strategy hwin initial)
    (start : Nat) (cuts : Nat → Nat) (n : Nat) : Type _ where
  | right
      (hside :
        profiledRawJointHybridPhysicalCompatibleSideAfter initialSide
            (n + 2) = .left)
      (member : Bool) (target : SuccessorTarget A strategy hwin initial)
      (nextRow : PairedEntryRow)
      (packet : ∃ slot : ProfiledRawLeftSlot A,
        state (n + 1) =
            profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A
              strategy hwin target ∧
          ProfiledRawJointHybridPhysicalCompatibleSuccessorTargetAt A strategy
              hwin policy (state n) target .left (.inr slot) ∧
          cutBlockMin
              (fun j ↦ A.priority
                (A.run (G.globalMachineTraceWord outputOne outputTwo env)
                  (start + j)))
              cuts (n + 1) =
            profiledRawJointThreadRootPriority A (.inr slot) ∧
          A.run (G.globalMachineTraceWord outputOne outputTwo env)
              (start + cuts (n + 2)) =
            pairedCodeStateForRow A nextRow slot.1.1) :
      ProfiledRawJointHybridPhysicalCompatibleResolvedTransitionPacketAt
        policy G outputOne outputTwo env initialSide state start cuts n
  | left
      (hside :
        profiledRawJointHybridPhysicalCompatibleSideAfter initialSide
            (n + 2) = .right)
      (member : Bool) (target : SuccessorTarget A strategy hwin initial)
      (nextRow : PairedEntryRow)
      (packet : ∃ slot : ProfiledRawRightSlot A,
        state (n + 1) =
            profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A
              strategy hwin target ∧
          ProfiledRawJointHybridPhysicalCompatibleSuccessorTargetAt A strategy
              hwin policy (state n) target .right (.inl slot) ∧
          cutBlockMin
              (fun j ↦ A.priority
                (A.run (G.globalMachineTraceWord outputOne outputTwo env)
                  (start + j)))
              cuts (n + 1) =
            profiledRawJointThreadRootPriority A (.inl slot) ∧
          A.run (G.globalMachineTraceWord outputOne outputTwo env)
              (start + cuts (n + 2)) =
            pairedCodeStateForRow A nextRow slot.1.1) :
      ProfiledRawJointHybridPhysicalCompatibleResolvedTransitionPacketAt
        policy G outputOne outputTwo env initialSide state start cuts n

namespace
    ProfiledRawJointHybridPhysicalCompatibleResolvedTransitionPacketAt

variable {initial : ProfiledRawJointCommonBaseWorld A strategy}
variable {policy : CompatiblePolicy A strategy hwin initial}
variable {G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂}
variable {outputOne : G.State → Out₁} {outputTwo : G.State → Out₂}
variable {env : EnvironmentSequence In₁ In₂}
variable {initialSide : IndexedLineageSide}
variable {state : Nat → CompatibleState A strategy hwin initial}
variable {start : Nat} {cuts : Nat → Nat} {n : Nat}

/-- Erase either concrete orientation packet to the common resolved-boundary
interface. -/
theorem nonemptyBoundary
    (packet :
      ProfiledRawJointHybridPhysicalCompatibleResolvedTransitionPacketAt A
        strategy hwin policy G outputOne outputTwo env initialSide state start
          cuts n) :
    Nonempty
      (ProfiledRawJointHybridPhysicalCompatibleResolvedMemberBoundaryAt A
        strategy hwin policy G outputOne outputTwo env initialSide state start
          cuts n) := by
  cases packet with
  | right hside member target nextRow raw =>
      have hpacket :=
        ProfiledRawJointHybridPhysicalCompatibleResolvedMemberBoundaryAt.ofRightTransitionPacket
          A strategy hwin hside member target (state (n + 1)) rfl
            (fun slot ↦
              A.run (G.globalMachineTraceWord outputOne outputTwo env)
                  (start + cuts (n + 2)) =
                pairedCodeStateForRow A nextRow slot.1.1)
            raw
      rcases hpacket with ⟨result⟩
      exact ⟨result.2.1⟩
  | left hside member target nextRow raw =>
      have hpacket :=
        ProfiledRawJointHybridPhysicalCompatibleResolvedMemberBoundaryAt.ofLeftTransitionPacket
          A strategy hwin hside member target (state (n + 1)) rfl
            (fun slot ↦
              A.run (G.globalMachineTraceWord outputOne outputTwo env)
                  (start + cuts (n + 2)) =
                pairedCodeStateForRow A nextRow slot.1.1)
            raw
      rcases hpacket with ⟨result⟩
      exact ⟨result.2.1⟩

end
  ProfiledRawJointHybridPhysicalCompatibleResolvedTransitionPacketAt

/-! ## One complete whole-trace cut witness -/

/-- Common-root exit followed by one right/left packet at every later cut. -/
structure ProfiledRawJointHybridPhysicalCompatibleWholeTraceCutWitness
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (env : EnvironmentSequence In₁ In₂) where
  start : Nat
  cuts : Nat → Nat
  cuts_strictMono : StrictMono cuts
  cuts_zero : cuts 0 = 0
  later : Nat → CompatibleState A strategy hwin initial
  exit :
    ProfiledRawJointHybridPhysicalCompatibleSuccessorInitialExit A strategy
      hwin policy G outputOne outputTwo env start cuts
  transition : ∀ n : Nat,
    ProfiledRawJointHybridPhysicalCompatibleResolvedTransitionPacketAt A
      strategy hwin policy G outputOne outputTwo env exit.initialSide
        (exit.state A strategy hwin later) start cuts n

namespace ProfiledRawJointHybridPhysicalCompatibleWholeTraceCutWitness

variable {initial : ProfiledRawJointCommonBaseWorld A strategy}
variable {policy : CompatiblePolicy A strategy hwin initial}
variable {G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂}
variable {outputOne : G.State → Out₁} {outputTwo : G.State → Out₂}
variable {env : EnvironmentSequence In₁ In₂}

/-- The checked exit and all later packets are precisely a resolved stream. -/
noncomputable def toResolvedMemberStream
    (witness :
      ProfiledRawJointHybridPhysicalCompatibleWholeTraceCutWitness A strategy
        hwin policy G outputOne outputTwo env) :
    ProfiledRawJointHybridPhysicalCompatibleResolvedMemberStream A strategy
      hwin policy G outputOne outputTwo env :=
  witness.exit.toResolvedMemberStream A strategy hwin witness.later
    witness.cuts_strictMono witness.cuts_zero
      (fun n ↦ Classical.choice (witness.transition n).nonemptyBoundary)

end ProfiledRawJointHybridPhysicalCompatibleWholeTraceCutWitness

/-! ## The two hard-regime fields and final four-regime composition -/

/-- Whole-trace cut witnesses in exactly the two regimes handled by the
resolved stream. -/
structure ProfiledRawJointHybridPhysicalCompatibleHardRegimeWholeTraceBookkeeping
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (env : EnvironmentSequence In₁ In₂) : Prop where
  recurrent : GraphBothRecurrent (fun n ↦ (env n).graph) →
    Nonempty
      (ProfiledRawJointHybridPhysicalCompatibleWholeTraceCutWitness A strategy
        hwin policy G outputOne outputTwo env)
  reversal : PersistentStrictReversalTail (fun n ↦ (env n).graph) →
    Nonempty
      (ProfiledRawJointHybridPhysicalCompatibleWholeTraceCutWitness A strategy
        hwin policy G outputOne outputTwo env)

namespace
    ProfiledRawJointHybridPhysicalCompatibleHardRegimeWholeTraceBookkeeping

variable {initial : ProfiledRawJointCommonBaseWorld A strategy}
variable {policy : CompatiblePolicy A strategy hwin initial}
variable {G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂}
variable {outputOne : G.State → Out₁} {outputTwo : G.State → Out₂}
variable {env : EnvironmentSequence In₁ In₂}

theorem recurrentStream
    (bookkeeping :
      ProfiledRawJointHybridPhysicalCompatibleHardRegimeWholeTraceBookkeeping
        A strategy hwin policy G outputOne outputTwo env)
    (hboth : GraphBothRecurrent (fun n ↦ (env n).graph)) :
    Nonempty
      (ProfiledRawJointHybridPhysicalCompatibleResolvedMemberStream A strategy
        hwin policy G outputOne outputTwo env) := by
  rcases bookkeeping.recurrent hboth with ⟨witness⟩
  exact ⟨witness.toResolvedMemberStream A strategy hwin⟩

theorem reversalStream
    (bookkeeping :
      ProfiledRawJointHybridPhysicalCompatibleHardRegimeWholeTraceBookkeeping
        A strategy hwin policy G outputOne outputTwo env)
    (hreversal :
      PersistentStrictReversalTail (fun n ↦ (env n).graph)) :
    Nonempty
      (ProfiledRawJointHybridPhysicalCompatibleResolvedMemberStream A strategy
        hwin policy G outputOne outputTwo env) := by
  rcases bookkeeping.reversal hreversal with ⟨witness⟩
  exact ⟨witness.toResolvedMemberStream A strategy hwin⟩

end
  ProfiledRawJointHybridPhysicalCompatibleHardRegimeWholeTraceBookkeeping

variable {initial : ProfiledRawJointCommonBaseWorld A strategy}
variable
  {policy : CompatiblePolicy A strategy hwin initial}
variable {controller :
  FinitePairedPhysicalController.{u, v, x, y, w, w}
    In₁ In₂ Out₁ Out₂}
variable {env : EnvironmentSequence In₁ In₂}

/-- Final downstream composition: hard-regime whole-trace packets plus the
installed homogeneous-tail alignments fill all four fields of the exact
resolved-controller bookkeeping. -/
noncomputable def
    LiteralCompatibleSuccessorResolvedControllerBookkeeping.ofWholeTraceAndInstalledFixedTails
    (hard :
      ProfiledRawJointHybridPhysicalCompatibleHardRegimeWholeTraceBookkeeping
        A strategy hwin policy controller.globalMachine
          controller.globalOutputOne controller.globalOutputTwo env)
    (fixed : EventuallyInstalledFixedTailBookkeeping A
      (controller.globalMachine.globalMachineTraceWord
        controller.globalOutputOne controller.globalOutputTwo env)
      (fun n ↦ (env n).graph)) :
    LiteralCompatibleSuccessorResolvedControllerBookkeeping A strategy hwin
      initial policy controller env :=
  LiteralCompatibleSuccessorResolvedControllerBookkeeping.ofInstalledFixedTails
    A hard.recurrentStream hard.reversalStream fixed

end

end DetParityAutomaton

end DistributedSynthesis
