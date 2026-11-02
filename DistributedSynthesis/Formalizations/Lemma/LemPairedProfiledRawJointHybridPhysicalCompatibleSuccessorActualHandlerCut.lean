/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleSuccessorDeferredHandlers
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleSuccessorInitialExit

/-!
# Actual deferred-handler cuts for compatible successor tables

The packet theorems use the canonical decorated-table play, whereas the
executable controller calls the concrete deferred receive handler.  This file
is the downstream adapter: given the one-cut equality supplied by a local
matched-prefix invariant, it packages the actual handler result into the full
member-transition packet.

The installed table member, retained entry row, and fresh closing member stay
independent.  All are proof-side audit data; no endpoint receives a hierarchy
side or strict-leader bit.
-/

namespace DistributedSynthesis

universe u v x y s c w

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

private abbrev OneShared
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial) :=
  ProfiledRawJointHybridPhysicalCompatibleFrontierOneShared.{u, v, x, y, s,
    max u v x y s} A strategy hwin policy

private abbrev TwoShared
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial) :=
  ProfiledRawJointHybridPhysicalCompatibleFrontierTwoShared.{u, v, x, y, s,
    max u v x y s} A strategy hwin policy

private abbrev OneControl
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial) :=
  ProfiledRawJointHybridPhysicalCompatibleFrontierOneControl.{u, v, x, y, s,
    max u v x y s, 0} A strategy hwin policy

private abbrev TwoControl
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial) :=
  ProfiledRawJointHybridPhysicalCompatibleFrontierTwoControl.{u, v, x, y, s,
    max u v x y s, 0} A strategy hwin policy

private abbrev OnePayload
    (initial : ProfiledRawJointCommonBaseWorld A strategy) :=
  ProfiledRawJointHybridPhysicalCompatibleFrontierOnePayload A strategy hwin
    (initial := initial)

private abbrev TwoPayload
    (initial : ProfiledRawJointCommonBaseWorld A strategy) :=
  ProfiledRawJointHybridPhysicalCompatibleFrontierTwoPayload A strategy hwin
    (initial := initial)

private abbrev LeftOutput
    (initial : ProfiledRawJointCommonBaseWorld A strategy) :=
  ProfiledRawJointHybridPhysicalCompatibleSuccessorLeftReceiverOutput A
    strategy hwin initial

private abbrev RightOutput
    (initial : ProfiledRawJointCommonBaseWorld A strategy) :=
  ProfiledRawJointHybridPhysicalCompatibleSuccessorRightReceiverOutput A
    strategy hwin initial

/-! ## Actual handler to resolved transition packet -/

/-- The process-two handler on an installed right table supplies the complete
right member-transition packet.  `hhandler` is exactly the local
matched-prefix seam; every conclusion after it is unconditional. -/
theorem
    profiledRawJointHybridPhysicalCompatibleFrontierTwoReceiver_memberTransitionCutPacket
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (fallback : PairedEntryRow × RightOutput A strategy hwin initial)
    (two : TwoControl A strategy hwin policy) (inputTwo : In₂)
    (oldPending : FiniteAcknowledgedDelayedCarrier.DeferredMemberControl
      (OneShared A strategy hwin policy) (OnePayload A strategy hwin initial))
    (inputOne : In₁)
    (state : CompatibleState A strategy hwin initial)
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (tableMember : Bool) (entryRow : PairedEntryRow)
    (tableEnv : Nat → In₂ × In₁) (n : Nat)
    (hhandler :
      profiledRawJointHybridPhysicalCompatibleFrontierTwoReceiver A strategy
          hwin policy fallback two inputTwo (.inl oldPending) inputOne =
        (entryRow,
          (profiledRawJointHybridPhysicalCompatibleRightDecoratedPlay A
            strategy hwin policy state move tableMember tableEnv n).2.1))
    {ParentShared : Type c} (shared : ParentShared) (closeMember : Bool)
    (hkey :
      let actual :=
        profiledRawJointHybridPhysicalCompatibleFrontierTwoReceiver A strategy
          hwin policy fallback two inputTwo (.inl oldPending) inputOne
      let target := (actual.2.target actual.1).1
      ProfiledRawJointHybridPhysicalCompatibleRightSuccessorKeyAt A strategy
        hwin policy state
          (profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A
            strategy hwin target)
          target.1)
    (physicalState : A.State)
    (word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (cuts : Nat → Nat) (k : Nat)
    (hcut : cuts k < cuts (k + 1))
    (hstate : A.runFrom physicalState word (cuts k) =
      pairedCodeStateForRow A entryRow move.1.source.1.1)
    (hlength :
      (profiledRawJointTargetRightPhysicalPrefixRecords A entryRow
          (omegaPrefix
            (profiledRawJointHybridPhysicalCompatibleRightPhysicalPlay A
              strategy hwin policy state move tableMember tableEnv) n)).length =
        cuts (k + 1) - cuts k - 1)
    (hslice : omegaPrefix (OmegaWord.drop word (cuts k))
        (profiledRawJointTargetRightPhysicalPrefixRecords A entryRow
          (omegaPrefix
            (profiledRawJointHybridPhysicalCompatibleRightPhysicalPlay A
              strategy hwin policy state move tableMember tableEnv) n)).length =
      profiledRawJointTargetRightPhysicalPrefixRecords A entryRow
        (omegaPrefix
          (profiledRawJointHybridPhysicalCompatibleRightPhysicalPlay A
            strategy hwin policy state move tableMember tableEnv) n))
    (hclosing : OmegaWord.drop word (cuts k)
        (profiledRawJointTargetRightPhysicalPrefixRecords A entryRow
          (omegaPrefix
            (profiledRawJointHybridPhysicalCompatibleRightPhysicalPlay A
              strategy hwin policy state move tableMember tableEnv) n)).length =
      profiledRawJointTargetRightClosingRecordForMember closeMember entryRow
        (profiledRawJointTargetRightPhysicalLetter A
          (profiledRawJointHybridPhysicalCompatibleRightPhysicalPlay A
            strategy hwin policy state move tableMember tableEnv n))) :
    let actual :=
      profiledRawJointHybridPhysicalCompatibleFrontierTwoReceiver A strategy
        hwin policy fallback two inputTwo (.inl oldPending) inputOne
    let pending :=
      profiledRawJointHybridPhysicalCompatibleRightPendingPayloadOfOutput A
        strategy hwin actual.2 actual.1
    let target :=
      profiledRawJointHybridPhysicalCompatibleRightPendingPayloadTarget A
        strategy hwin pending closeMember
    let installed :=
      profiledRawJointHybridPhysicalCompatibleInstallLeftPendingMember.{u, v,
        x, y, s, c, max u v x y s} A strategy hwin policy
          (closeMember, shared, pending)
    ∃ slot : ProfiledRawLeftSlot A,
      installed.1.1 =
          profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A strategy
            hwin target ∧
        ProfiledRawJointHybridPhysicalCompatibleSuccessorTargetAt A strategy
          hwin policy state target .left (.inr slot) ∧
        cutBlockMin
            (fun j ↦ A.priority (A.runFrom physicalState word j)) cuts k =
          profiledRawJointThreadRootPriority A (.inr slot) ∧
        A.runFrom physicalState word (cuts (k + 1)) =
          pairedCodeStateForRow A
            (profiledRawJointCloseRowOfMember closeMember) slot.1.1 := by
  rw [hhandler] at hkey ⊢
  exact
    profiledRawJointHybridPhysicalCompatibleRight_memberTransitionCutPacket
      A strategy hwin policy state shared move tableMember entryRow closeMember
      tableEnv n hkey physicalState word cuts k hcut hstate hlength hslice
        hclosing

/-- Process-one/left-table mirror. -/
theorem
    profiledRawJointHybridPhysicalCompatibleFrontierOneReceiver_memberTransitionCutPacket
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (fallback : PairedEntryRow × LeftOutput A strategy hwin initial)
    (one : OneControl A strategy hwin policy) (inputOne : In₁)
    (oldPending : FiniteAcknowledgedDelayedCarrier.DeferredMemberControl
      (TwoShared A strategy hwin policy) (TwoPayload A strategy hwin initial))
    (inputTwo : In₂)
    (state : CompatibleState A strategy hwin initial)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (tableMember : Bool) (entryRow : PairedEntryRow)
    (tableEnv : Nat → In₁ × In₂) (n : Nat)
    (hhandler :
      profiledRawJointHybridPhysicalCompatibleFrontierOneReceiver A strategy
          hwin policy fallback one inputOne (.inl oldPending) inputTwo =
        (entryRow,
          (profiledRawJointHybridPhysicalCompatibleLeftDecoratedPlay A strategy
            hwin policy state move tableMember tableEnv n).2.1))
    {ParentShared : Type c} (shared : ParentShared) (closeMember : Bool)
    (hkey :
      let actual :=
        profiledRawJointHybridPhysicalCompatibleFrontierOneReceiver A strategy
          hwin policy fallback one inputOne (.inl oldPending) inputTwo
      let target := (actual.2.target actual.1).1
      ProfiledRawJointHybridPhysicalCompatibleLeftSuccessorKeyAt A strategy
        hwin policy state
          (profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A
            strategy hwin target)
          target.1)
    (physicalState : A.State)
    (word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (cuts : Nat → Nat) (k : Nat)
    (hcut : cuts k < cuts (k + 1))
    (hstate : A.runFrom physicalState word (cuts k) =
      pairedCodeStateForRow A entryRow move.1.source.1.1)
    (hlength :
      (profiledRawJointTargetLeftPhysicalPrefixRecords A entryRow
          (omegaPrefix
            (profiledRawJointHybridPhysicalCompatibleLeftPhysicalPlay A
              strategy hwin policy state move tableMember tableEnv) n)).length =
        cuts (k + 1) - cuts k - 1)
    (hslice : omegaPrefix (OmegaWord.drop word (cuts k))
        (profiledRawJointTargetLeftPhysicalPrefixRecords A entryRow
          (omegaPrefix
            (profiledRawJointHybridPhysicalCompatibleLeftPhysicalPlay A
              strategy hwin policy state move tableMember tableEnv) n)).length =
      profiledRawJointTargetLeftPhysicalPrefixRecords A entryRow
        (omegaPrefix
          (profiledRawJointHybridPhysicalCompatibleLeftPhysicalPlay A strategy
            hwin policy state move tableMember tableEnv) n))
    (hclosing : OmegaWord.drop word (cuts k)
        (profiledRawJointTargetLeftPhysicalPrefixRecords A entryRow
          (omegaPrefix
            (profiledRawJointHybridPhysicalCompatibleLeftPhysicalPlay A
              strategy hwin policy state move tableMember tableEnv) n)).length =
      profiledRawJointTargetLeftClosingRecordForMember closeMember entryRow
        (profiledRawJointTargetLeftPhysicalLetter A
          (profiledRawJointHybridPhysicalCompatibleLeftPhysicalPlay A strategy
            hwin policy state move tableMember tableEnv n))) :
    let actual :=
      profiledRawJointHybridPhysicalCompatibleFrontierOneReceiver A strategy
        hwin policy fallback one inputOne (.inl oldPending) inputTwo
    let pending :=
      profiledRawJointHybridPhysicalCompatibleLeftPendingPayloadOfOutput A
        strategy hwin actual.2 actual.1
    let target :=
      profiledRawJointHybridPhysicalCompatibleLeftPendingPayloadTarget A
        strategy hwin pending closeMember
    let installed :=
      profiledRawJointHybridPhysicalCompatibleInstallRightPendingMember.{u, v,
        x, y, s, c, max u v x y s} A strategy hwin policy
          (closeMember, shared, pending)
    ∃ slot : ProfiledRawRightSlot A,
      installed.1.1 =
          profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A strategy
            hwin target ∧
        ProfiledRawJointHybridPhysicalCompatibleSuccessorTargetAt A strategy
          hwin policy state target .right (.inl slot) ∧
        cutBlockMin
            (fun j ↦ A.priority (A.runFrom physicalState word j)) cuts k =
          profiledRawJointThreadRootPriority A (.inl slot) ∧
        A.runFrom physicalState word (cuts (k + 1)) =
          pairedCodeStateForRow A
            (profiledRawJointCloseRowOfMember closeMember) slot.1.1 := by
  rw [hhandler] at hkey ⊢
  exact
    profiledRawJointHybridPhysicalCompatibleLeft_memberTransitionCutPacket
      A strategy hwin policy state shared move tableMember entryRow closeMember
      tableEnv n hkey physicalState word cuts k hcut hstate hlength hslice
        hclosing

/-! ## Transition packets are exactly resolved stream boundaries -/

namespace ProfiledRawJointHybridPhysicalCompatibleResolvedMemberBoundaryAt

variable {initial : ProfiledRawJointCommonBaseWorld A strategy}
variable {policy : CompatiblePolicy A strategy hwin initial}
variable {G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂}
variable {outputOne : G.State → Out₁} {outputTwo : G.State → Out₂}
variable {env : EnvironmentSequence In₁ In₂}
variable {initialSide : IndexedLineageSide}
variable {state : Nat → CompatibleState A strategy hwin initial}
variable {start : Nat} {cuts : Nat → Nat} {n : Nat}

/-- Consume a complete right member-transition packet.  The last component is
kept abstract because callers normally use it as the starting-state premise
of the following cut. -/
theorem ofRightTransitionPacket
    (hside :
      profiledRawJointHybridPhysicalCompatibleSideAfter initialSide (n + 2) =
        .left)
    (member : Bool)
    (target : ProfiledRawJointHybridPhysicalCompatibleSuccessorTarget A
      strategy hwin initial)
    (installed : CompatibleState A strategy hwin initial)
    (htrace : state (n + 1) = installed)
    (Next : ProfiledRawLeftSlot A → Prop)
    (packet : ∃ slot : ProfiledRawLeftSlot A,
      installed =
          profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A strategy
            hwin target ∧
        ProfiledRawJointHybridPhysicalCompatibleSuccessorTargetAt A strategy
          hwin policy (state n) target .left (.inr slot) ∧
        cutBlockMin
            (fun j ↦ A.priority
              (A.run (G.globalMachineTraceWord outputOne outputTwo env)
                (start + j)))
            cuts (n + 1) =
          profiledRawJointThreadRootPriority A (.inr slot) ∧
        Next slot) :
    Nonempty (Σ slot : ProfiledRawLeftSlot A,
      ProfiledRawJointHybridPhysicalCompatibleResolvedMemberBoundaryAt A
          strategy hwin policy G outputOne outputTwo env initialSide state start
            cuts n ×
        PLift (Next slot)) := by
  obtain ⟨slot, hinstalled, htarget, hblock, hnext⟩ := packet
  exact ⟨⟨slot,
    ProfiledRawJointHybridPhysicalCompatibleResolvedMemberBoundaryAt.ofRight
      A strategy hwin hside member target slot htarget installed htrace
        hinstalled hblock,
    ⟨hnext⟩⟩⟩

/-- Left mirror. -/
theorem ofLeftTransitionPacket
    (hside :
      profiledRawJointHybridPhysicalCompatibleSideAfter initialSide (n + 2) =
        .right)
    (member : Bool)
    (target : ProfiledRawJointHybridPhysicalCompatibleSuccessorTarget A
      strategy hwin initial)
    (installed : CompatibleState A strategy hwin initial)
    (htrace : state (n + 1) = installed)
    (Next : ProfiledRawRightSlot A → Prop)
    (packet : ∃ slot : ProfiledRawRightSlot A,
      installed =
          profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A strategy
            hwin target ∧
        ProfiledRawJointHybridPhysicalCompatibleSuccessorTargetAt A strategy
          hwin policy (state n) target .right (.inl slot) ∧
        cutBlockMin
            (fun j ↦ A.priority
              (A.run (G.globalMachineTraceWord outputOne outputTwo env)
                (start + j)))
            cuts (n + 1) =
          profiledRawJointThreadRootPriority A (.inl slot) ∧
        Next slot) :
    Nonempty (Σ slot : ProfiledRawRightSlot A,
      ProfiledRawJointHybridPhysicalCompatibleResolvedMemberBoundaryAt A
          strategy hwin policy G outputOne outputTwo env initialSide state start
            cuts n ×
        PLift (Next slot)) := by
  obtain ⟨slot, hinstalled, htarget, hblock, hnext⟩ := packet
  exact ⟨⟨slot,
    ProfiledRawJointHybridPhysicalCompatibleResolvedMemberBoundaryAt.ofLeft
      A strategy hwin hside member target slot htarget installed htrace
        hinstalled hblock,
    ⟨hnext⟩⟩⟩

end ProfiledRawJointHybridPhysicalCompatibleResolvedMemberBoundaryAt

end

end DetParityAutomaton

end DistributedSynthesis
