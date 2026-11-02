/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleSuccessorMemberCutPacket
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleSuccessorCarrier

/-!
# Resolved-member stream adapter for compatible successor carriers

The local packet theorems expose one acknowledged physical close at a time.
This file is the controller-independent iteration adapter: it packages their
four consumed conclusions and turns a `Nat`-indexed sequence of such packets
into the existing successor-carrier cut tail.

Right and left constructors keep the physical orientation explicit.  The
lineage side, member, target, root, and installed key are proof-side audit
data.  They are not inputs to an endpoint controller and do not reveal a
strict leader or graph orientation.
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

/-! ## One resolved recurrent boundary -/

/-- The four facts about one acknowledged close which are consumed by the
carrier tail.

The packet's actual next-DPA-state equation is used by the caller to establish
the starting-state premise of the following packet.  Once that induction has
been performed, only `blockMin` is retained here; the carrier consumer does
not otherwise inspect DPA states at cuts. -/
structure
    ProfiledRawJointHybridPhysicalCompatibleResolvedMemberBoundaryAt
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (env : EnvironmentSequence In₁ In₂)
    (initialSide : IndexedLineageSide)
    (state : Nat → CompatibleState A strategy hwin initial)
    (start : Nat) (cuts : Nat → Nat) (n : Nat) where
  member : Bool
  target : SuccessorTarget A strategy hwin initial
  root : ProfiledRawJointThreadRoot A
  target_at :
    ProfiledRawJointHybridPhysicalCompatibleSuccessorTargetAt A strategy hwin
      policy (state n) target
        (profiledRawJointHybridPhysicalCompatibleSideAfter initialSide (n + 2))
        root
  next_state :
    state (n + 1) =
      profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A strategy
        hwin target
  blockMin :
    cutBlockMin
        (fun j ↦ A.priority
          (A.run (G.globalMachineTraceWord outputOne outputTwo env)
            (start + j)))
        cuts (n + 1) =
      profiledRawJointThreadRootPriority A root

namespace
    ProfiledRawJointHybridPhysicalCompatibleResolvedMemberBoundaryAt

variable {initial : ProfiledRawJointCommonBaseWorld A strategy}
variable {policy : CompatiblePolicy A strategy hwin initial}
variable {G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂}
variable {outputOne : G.State → Out₁} {outputTwo : G.State → Out₂}
variable {env : EnvironmentSequence In₁ In₂}
variable {initialSide : IndexedLineageSide}
variable {state : Nat → CompatibleState A strategy hwin initial}
variable {start : Nat} {cuts : Nat → Nat} {n : Nat}

/-- Package the conclusions of a resolved right-table close.  `installed` is
the key read from the actual crossed control; the two equalities compose to
the state equation consumed by the stream. -/
def ofRight
    (hside :
      profiledRawJointHybridPhysicalCompatibleSideAfter initialSide (n + 2) =
        .left)
    (member : Bool) (target : SuccessorTarget A strategy hwin initial)
    (slot : ProfiledRawLeftSlot A)
    (htarget :
      ProfiledRawJointHybridPhysicalCompatibleSuccessorTargetAt A strategy
        hwin policy (state n) target .left (.inr slot))
    (installed : CompatibleState A strategy hwin initial)
    (htrace : state (n + 1) = installed)
    (hinstalled : installed =
      profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A strategy
        hwin target)
    (hblock :
      cutBlockMin
          (fun j ↦ A.priority
            (A.run (G.globalMachineTraceWord outputOne outputTwo env)
              (start + j)))
          cuts (n + 1) =
        profiledRawJointThreadRootPriority A (.inr slot)) :
    ProfiledRawJointHybridPhysicalCompatibleResolvedMemberBoundaryAt A strategy
      hwin policy G outputOne outputTwo env initialSide state start cuts n where
  member := member
  target := target
  root := .inr slot
  target_at := by
    rw [hside]
    exact htarget
  next_state := htrace.trans hinstalled
  blockMin := hblock

/-- Left-table mirror. -/
def ofLeft
    (hside :
      profiledRawJointHybridPhysicalCompatibleSideAfter initialSide (n + 2) =
        .right)
    (member : Bool) (target : SuccessorTarget A strategy hwin initial)
    (slot : ProfiledRawRightSlot A)
    (htarget :
      ProfiledRawJointHybridPhysicalCompatibleSuccessorTargetAt A strategy
        hwin policy (state n) target .right (.inl slot))
    (installed : CompatibleState A strategy hwin initial)
    (htrace : state (n + 1) = installed)
    (hinstalled : installed =
      profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A strategy
        hwin target)
    (hblock :
      cutBlockMin
          (fun j ↦ A.priority
            (A.run (G.globalMachineTraceWord outputOne outputTwo env)
              (start + j)))
          cuts (n + 1) =
        profiledRawJointThreadRootPriority A (.inl slot)) :
    ProfiledRawJointHybridPhysicalCompatibleResolvedMemberBoundaryAt A strategy
      hwin policy G outputOne outputTwo env initialSide state start cuts n where
  member := member
  target := target
  root := .inl slot
  target_at := by
    rw [hside]
    exact htarget
  next_state := htrace.trans hinstalled
  blockMin := hblock

end
  ProfiledRawJointHybridPhysicalCompatibleResolvedMemberBoundaryAt

/-! ## Infinite packet stream -/

/-- Initial common-root exit plus one resolved acknowledged packet at every
later cut.  This is the smallest controller-independent invariant sufficient
to build `SuccessorCarrierCutTail`.

All physical slice/closing equations and the next-DPA-state induction live in
the proof producing `boundary`; they are not duplicated after their packet has
been checked. -/
structure ProfiledRawJointHybridPhysicalCompatibleResolvedMemberStream
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (env : EnvironmentSequence In₁ In₂) where
  initial_code :
    (policy.run []).1.1 =
      .common ((profiledRawJointCommonWorldFamily A initial).incidenceCode A)
  initialSide : IndexedLineageSide
  initialRoot : ProfiledRawJointThreadRoot A
  initial_live :
    profiledRawJointHybridCurrentSlots A initialSide (policy.run []).1.1 () =
      some initialRoot
  exitTarget : SuccessorTarget A strategy hwin initial
  exitRoot : ProfiledRawJointThreadRoot A
  exit_at :
    ProfiledRawJointHybridPhysicalCompatibleSuccessorTargetAt A strategy hwin
      policy (policy.run []) exitTarget
        (profiledRawJointHybridPhysicalCompatibleSideAfter initialSide 1)
        exitRoot
  state : Nat → CompatibleState A strategy hwin initial
  state_zero :
    state 0 =
      profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A strategy
        hwin exitTarget
  start : Nat
  cuts : Nat → Nat
  cuts_strictMono : StrictMono cuts
  cuts_zero : cuts 0 = 0
  exit_blockMin :
    cutBlockMin
        (fun j ↦ A.priority
          (A.run (G.globalMachineTraceWord outputOne outputTwo env)
            (start + j)))
        cuts 0 =
      profiledRawJointThreadRootPriority A exitRoot
  boundary : ∀ n : Nat,
    ProfiledRawJointHybridPhysicalCompatibleResolvedMemberBoundaryAt A strategy
      hwin policy G outputOne outputTwo env initialSide state start cuts n

namespace ProfiledRawJointHybridPhysicalCompatibleResolvedMemberStream

variable {initial : ProfiledRawJointCommonBaseWorld A strategy}
variable {policy : CompatiblePolicy A strategy hwin initial}
variable {G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂}
variable {outputOne : G.State → Out₁} {outputTwo : G.State → Out₂}
variable {env : EnvironmentSequence In₁ In₂}

/-- Erase the orientation-specific operational packet presentation.  `Unit`
is enough for the carrier's proof-only payload because both fork-key
projections are definitionally the retained target key. -/
noncomputable def toCarrierCutTail
    (stream :
      ProfiledRawJointHybridPhysicalCompatibleResolvedMemberStream A strategy
        hwin policy G outputOne outputTwo env) :
    ProfiledRawJointHybridPhysicalCompatibleSuccessorCarrierCutTail A strategy
      hwin policy Unit G outputOne outputTwo env where
  initial_code := stream.initial_code
  initialSide := stream.initialSide
  initialRoot := stream.initialRoot
  initial_live := stream.initial_live
  exitTarget := stream.exitTarget
  exitRoot := stream.exitRoot
  exit_at := stream.exit_at
  state := stream.state
  state_zero := stream.state_zero
  target n := (stream.boundary n).target
  rootAt n := (stream.boundary n).root
  target_at n := (stream.boundary n).target_at
  member n := (stream.boundary n).member
  payload _ := ()
  carrier_next := by
    intro n
    rw [(stream.boundary n).next_state]
    cases hside : profiledRawJointHybridPhysicalCompatibleSideAfter
        stream.initialSide (n + 2) with
    | left => simp
    | right => simp
  start := stream.start
  cuts := stream.cuts
  cuts_strictMono := stream.cuts_strictMono
  cuts_zero := stream.cuts_zero
  exit_blockMin := stream.exit_blockMin
  recurrent_blockMin n := (stream.boundary n).blockMin

/-- The resolved packet stream therefore inherits the complete physical
acceptance theorem. -/
theorem accepts
    (stream :
      ProfiledRawJointHybridPhysicalCompatibleResolvedMemberStream A strategy
        hwin policy G outputOne outputTwo env) :
    A.Accepts (G.globalMachineTraceWord outputOne outputTwo env) :=
  (stream.toCarrierCutTail A strategy hwin).accepts A strategy hwin

end ProfiledRawJointHybridPhysicalCompatibleResolvedMemberStream

end

end DetParityAutomaton

end DistributedSynthesis
