/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteAcknowledgedExactClosingCanonicalPendingOnly
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleSuccessorDeferredFrontier
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleSuccessorMemberCutPacket

/-!
# Concrete local handlers for the compatible successor frontier

This file replaces the six abstract maps of the canonical deferred frontier by
the actual decorated-table operations.  At a receive, an endpoint performs two
independent local resolutions:

* its own acknowledged pending control supplies the next owner/shared table;
* the delivered partner pending control supplies the current receiver table,
  whose stored entry row is advanced on the current input pair.

The receiver result is returned together with that stored entry row as one
value.  Hence the subsequent pending payload cannot mix the target of one old
row with another row.  The later fresh open/close member selects only the next
receiver row through the corrected frontier API.

All mismatch and recurrent cases are explicit totalization branches.  The
canonical pending-only trace theorem proves that the recurrent branches are
unreachable.  This module is nevertheless only the one-cut controller probe:
on a repeated same-direction receive it does not retain the receiver monitor
advanced at the preceding receive.  A global trace construction must replace
the simple shared state below by the finite phase-live overlay (retained live
receiver plus dormant delivered sender) before claiming mismatch
unreachability.  The completed one-cut equations remain the interface for
that port.  No executable definition receives a graph, orientation, hierarchy
side, leader bit, strict-leader bit, history, or view.
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

private abbrev CompatiblePolicy
    (initial : ProfiledRawJointCommonBaseWorld A strategy) :=
  ProfiledRawJointHybridPhysicalCompatibleRationalPolicy A strategy hwin
    initial

private abbrev CompatibleState
    (initial : ProfiledRawJointCommonBaseWorld A strategy) :=
  ProfiledRawJointHybridPhysicalCompatiblePolicyState A strategy hwin initial

variable {initial : ProfiledRawJointCommonBaseWorld A strategy}
variable (policy : CompatiblePolicy A strategy hwin initial)

private abbrev OneShared :=
  ProfiledRawJointHybridPhysicalCompatibleFrontierOneShared.{u, v, x, y, s,
    max u v x y s} A strategy hwin policy
private abbrev TwoShared :=
  ProfiledRawJointHybridPhysicalCompatibleFrontierTwoShared.{u, v, x, y, s,
    max u v x y s} A strategy hwin policy
private abbrev OneControl :=
  ProfiledRawJointHybridPhysicalCompatibleFrontierOneControl.{u, v, x, y, s,
    max u v x y s, 0} A strategy hwin policy
private abbrev TwoControl :=
  ProfiledRawJointHybridPhysicalCompatibleFrontierTwoControl.{u, v, x, y, s,
    max u v x y s, 0} A strategy hwin policy
private abbrev OnePayload :=
  ProfiledRawJointHybridPhysicalCompatibleFrontierOnePayload A strategy hwin
    (initial := initial)
private abbrev TwoPayload :=
  ProfiledRawJointHybridPhysicalCompatibleFrontierTwoPayload A strategy hwin
    (initial := initial)
private abbrev OnePending :=
  FiniteAcknowledgedDelayedCarrier.DeferredMemberControl
    (OneShared A strategy hwin policy)
    (OnePayload A strategy hwin (initial := initial))
private abbrev TwoPending :=
  FiniteAcknowledgedDelayedCarrier.DeferredMemberControl
    (TwoShared A strategy hwin policy)
    (TwoPayload A strategy hwin (initial := initial))
private abbrev LeftOutput :=
  ProfiledRawJointHybridPhysicalCompatibleSuccessorLeftReceiverOutput A
    strategy hwin initial
private abbrev RightOutput :=
  ProfiledRawJointHybridPhysicalCompatibleSuccessorRightReceiverOutput A
    strategy hwin initial

/-! ## Fail-fast audit: the receiver's `false` index is canonical -/

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- The physical sibling construction materializes one common monitor and one
complete controller table.  Its Bool parameter is definitionally ignored, so
using the `false`-indexed receiver-state type loses no old-table-member case. -/
theorem
    profiledRawJointHybridPhysicalCompatibleRightReceiver_memberCanonical
    (move : ProfiledRawJointRightPhysicalSiblingMove A) (tableMember : Bool) :
    profiledRawJointRightPhysicalSiblingMonitor A move.1 tableMember =
        profiledRawJointRightPhysicalSiblingMonitor A move.1 false ∧
      move.memberController A tableMember = move.memberController A false :=
  ⟨rfl, rfl⟩

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Left mirror of the canonical-member audit. -/
theorem
    profiledRawJointHybridPhysicalCompatibleLeftReceiver_memberCanonical
    (move : ProfiledRawJointLeftPhysicalSiblingMove A) (tableMember : Bool) :
    profiledRawJointLeftPhysicalSiblingMonitor A move.1 tableMember =
        profiledRawJointLeftPhysicalSiblingMonitor A move.1 false ∧
      move.memberController A tableMember = move.memberController A false :=
  ⟨rfl, rfl⟩

/-! ## The selected own pending control supplies the next owner -/

/-- Process one's own pending control installs the selected right table. -/
noncomputable def
    profiledRawJointHybridPhysicalCompatibleFrontierOneSelectedOwner
    (fallback : OneShared A strategy hwin policy)
    (one : OneControl A strategy hwin policy) :
    OneShared A strategy hwin policy :=
  match one with
  | .inl pending =>
      let installed :=
        profiledRawJointHybridPhysicalCompatibleInstallRightPendingMember.{u,
          v, x, y, s, max u v x y s, max u v x y s} A
          strategy hwin policy pending
      ⟨installed.1.1, installed.1.2.2⟩
  | .inr _ => fallback

/-- Process-two mirror. -/
noncomputable def
    profiledRawJointHybridPhysicalCompatibleFrontierTwoSelectedOwner
    (fallback : TwoShared A strategy hwin policy)
    (two : TwoControl A strategy hwin policy) :
    TwoShared A strategy hwin policy :=
  match two with
  | .inl pending =>
      let installed :=
        profiledRawJointHybridPhysicalCompatibleInstallLeftPendingMember.{u,
          v, x, y, s, max u v x y s, max u v x y s} A
          strategy hwin policy pending
      ⟨installed.1.1, installed.1.2.2⟩
  | .inr _ => fallback

@[simp] theorem
    profiledRawJointHybridPhysicalCompatibleFrontierOneSelectedOwner_inl
    (fallback : OneShared A strategy hwin policy)
    (pending : FiniteAcknowledgedDelayedCarrier.DeferredMemberControl
      (OneShared A strategy hwin policy)
      (ProfiledRawJointHybridPhysicalCompatibleFrontierOnePayload A strategy
        hwin (initial := initial))) :
    profiledRawJointHybridPhysicalCompatibleFrontierOneSelectedOwner A strategy
        hwin policy fallback (.inl pending) =
      let installed :=
        profiledRawJointHybridPhysicalCompatibleInstallRightPendingMember.{u,
          v, x, y, s, max u v x y s, max u v x y s} A
          strategy hwin policy pending
      ⟨installed.1.1, installed.1.2.2⟩ :=
  rfl

/-! ## The selected delivered pending control supplies the receiver -/

private abbrev LeftInstalled :=
  ProfiledRawJointHybridPhysicalCompatibleLeftDeferredControl.{u, v, x, y, s,
    max u v x y s, max u v x y s} A strategy hwin policy
    (ProfiledRawJointHybridPhysicalCompatibleLeftPayload A strategy hwin
      (initial := initial))

private abbrev RightInstalled :=
  ProfiledRawJointHybridPhysicalCompatibleRightDeferredControl.{u, v, x, y, s,
    max u v x y s, max u v x y s} A strategy hwin policy
    (ProfiledRawJointHybridPhysicalCompatibleRightPayload A strategy hwin
      (initial := initial))

/-- Run an installed left receiver.  The fallback covers only an inert owner,
an absent receiver, or a malformed move mismatch. -/
noncomputable def
    profiledRawJointHybridPhysicalCompatibleRunInstalledLeftReceiver
    (fallback : PairedEntryRow × LeftOutput A strategy hwin (initial := initial))
    (installed : LeftInstalled A strategy hwin policy)
    (input : In₁ × In₂) :
    PairedEntryRow × LeftOutput A strategy hwin (initial := initial) := by
  classical
  rcases installed with ⟨⟨state, member, shared⟩, payload⟩
  cases shared with
  | inl _ => exact fallback
  | inr owner =>
      cases payload with
      | none => exact fallback
      | some receiver =>
          rcases owner with ⟨ownerMove, ownerControl⟩
          rcases receiver with
            ⟨receiverMove, row, monitorState, stagedOutput⟩
          by_cases hmove : receiverMove = ownerMove
          · cases hmove
            exact (row,
              (profiledRawJointHybridPhysicalCompatibleLeftReceiverStepFor A
                strategy hwin policy state ownerMove ownerControl row
                monitorState input).1)
          · exact fallback

/-- Right-installed mirror. -/
noncomputable def
    profiledRawJointHybridPhysicalCompatibleRunInstalledRightReceiver
    (fallback : PairedEntryRow × RightOutput A strategy hwin
      (initial := initial))
    (installed : RightInstalled A strategy hwin policy)
    (input : In₂ × In₁) :
    PairedEntryRow × RightOutput A strategy hwin (initial := initial) := by
  classical
  rcases installed with ⟨⟨state, member, shared⟩, payload⟩
  cases shared with
  | inl _ => exact fallback
  | inr owner =>
      cases payload with
      | none => exact fallback
      | some receiver =>
          rcases owner with ⟨ownerMove, ownerControl⟩
          rcases receiver with
            ⟨receiverMove, row, monitorState, stagedOutput⟩
          by_cases hmove : receiverMove = ownerMove
          · cases hmove
            exact (row,
              (profiledRawJointHybridPhysicalCompatibleRightReceiverStepFor A
                strategy hwin policy state ownerMove ownerControl row
                monitorState input).1)
          · exact fallback

/-- Process one resolves the delivered process-two pending control and runs
its installed left receiver on the current input pair. -/
noncomputable def
    profiledRawJointHybridPhysicalCompatibleFrontierOneReceiver
    (fallback : PairedEntryRow × LeftOutput A strategy hwin (initial := initial))
    (_one : OneControl A strategy hwin policy) (inputOne : In₁)
    (two : TwoControl A strategy hwin policy) (inputTwo : In₂) :
    PairedEntryRow × LeftOutput A strategy hwin (initial := initial) :=
  match two with
  | .inl pending =>
      let installed : LeftInstalled A strategy hwin policy :=
        profiledRawJointHybridPhysicalCompatibleInstallLeftPendingMember.{u,
          v, x, y, s, max u v x y s, max u v x y s} A
          strategy hwin policy pending
      profiledRawJointHybridPhysicalCompatibleRunInstalledLeftReceiver A
        strategy hwin policy fallback installed (inputOne, inputTwo)
  | .inr _ => fallback

/-- Process-two mirror. -/
noncomputable def
    profiledRawJointHybridPhysicalCompatibleFrontierTwoReceiver
    (fallback : PairedEntryRow × RightOutput A strategy hwin
      (initial := initial))
    (_two : TwoControl A strategy hwin policy) (inputTwo : In₂)
    (one : OneControl A strategy hwin policy) (inputOne : In₁) :
    PairedEntryRow × RightOutput A strategy hwin (initial := initial) :=
  match one with
  | .inl pending =>
      let installed : RightInstalled A strategy hwin policy :=
        profiledRawJointHybridPhysicalCompatibleInstallRightPendingMember.{u,
          v, x, y, s, max u v x y s, max u v x y s} A
          strategy hwin policy pending
      profiledRawJointHybridPhysicalCompatibleRunInstalledRightReceiver A
        strategy hwin policy fallback installed (inputTwo, inputOne)
  | .inr _ => fallback

/-! ## Exact live-branch equations -/

@[simp] theorem
    profiledRawJointHybridPhysicalCompatibleRunInstalledLeftReceiver_live
    (fallback : PairedEntryRow × LeftOutput A strategy hwin (initial := initial))
    (state : CompatibleState A strategy hwin initial) (member : Bool)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (owner : (move.memberController A false).Control)
    (row : PairedEntryRow)
    (monitorState :
      (profiledRawJointHybridPhysicalCompatibleSuccessorLeftMonitor A strategy
        hwin (initial := initial) move false).State)
    (staged : Option (LeftOutput A strategy hwin (initial := initial)))
    (input : In₁ × In₂) :
    profiledRawJointHybridPhysicalCompatibleRunInstalledLeftReceiver A strategy
        hwin policy fallback
        ((⟨state, member, .inr ⟨move, owner⟩⟩),
          some ⟨move, row, monitorState, staged⟩) input =
      (row,
        (profiledRawJointHybridPhysicalCompatibleLeftReceiverStepFor A strategy
          hwin policy state move owner row monitorState input).1) := by
  simp [profiledRawJointHybridPhysicalCompatibleRunInstalledLeftReceiver]

@[simp] theorem
    profiledRawJointHybridPhysicalCompatibleRunInstalledRightReceiver_live
    (fallback : PairedEntryRow × RightOutput A strategy hwin
      (initial := initial))
    (state : CompatibleState A strategy hwin initial) (member : Bool)
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (owner : (move.memberController A false).Control)
    (row : PairedEntryRow)
    (monitorState :
      (profiledRawJointHybridPhysicalCompatibleSuccessorRightMonitor A strategy
        hwin (initial := initial) move false).State)
    (staged : Option (RightOutput A strategy hwin (initial := initial)))
    (input : In₂ × In₁) :
    profiledRawJointHybridPhysicalCompatibleRunInstalledRightReceiver A
        strategy hwin policy fallback
        ((⟨state, member, .inr ⟨move, owner⟩⟩),
          some ⟨move, row, monitorState, staged⟩) input =
      (row,
        (profiledRawJointHybridPhysicalCompatibleRightReceiverStepFor A
          strategy hwin policy state move owner row monitorState input).1) := by
  simp [profiledRawJointHybridPhysicalCompatibleRunInstalledRightReceiver]

/-- Concrete process-one one-cut equation.  It assumes only the live shape of
the installed delivered table; no graph-side fact enters the handler. -/
theorem
    profiledRawJointHybridPhysicalCompatibleFrontierOneReceiver_of_installed
    (fallback : PairedEntryRow × LeftOutput A strategy hwin (initial := initial))
    (one : OneControl A strategy hwin policy) (inputOne : In₁)
    (pending : FiniteAcknowledgedDelayedCarrier.DeferredMemberControl
      (TwoShared A strategy hwin policy)
      (ProfiledRawJointHybridPhysicalCompatibleFrontierTwoPayload A strategy
        hwin (initial := initial)))
    (inputTwo : In₂)
    (state : CompatibleState A strategy hwin initial) (member : Bool)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (owner : (move.memberController A false).Control)
    (row : PairedEntryRow)
    (monitorState :
      (profiledRawJointHybridPhysicalCompatibleSuccessorLeftMonitor A strategy
        hwin (initial := initial) move false).State)
    (staged : Option (LeftOutput A strategy hwin (initial := initial)))
    (hinstalled :
      profiledRawJointHybridPhysicalCompatibleInstallLeftPendingMember.{u,
        v, x, y, s, max u v x y s, max u v x y s} A
          strategy hwin policy pending =
        ((⟨state, member, .inr ⟨move, owner⟩⟩),
          some ⟨move, row, monitorState, staged⟩)) :
    profiledRawJointHybridPhysicalCompatibleFrontierOneReceiver A strategy hwin
        policy fallback one inputOne (.inl pending) inputTwo =
      (row,
        (profiledRawJointHybridPhysicalCompatibleLeftReceiverStepFor A strategy
          hwin policy state move owner row monitorState
          (inputOne, inputTwo)).1) := by
  simp only
    [profiledRawJointHybridPhysicalCompatibleFrontierOneReceiver]
  calc
    profiledRawJointHybridPhysicalCompatibleRunInstalledLeftReceiver A strategy
        hwin policy fallback
        (profiledRawJointHybridPhysicalCompatibleInstallLeftPendingMember.{u,
          v, x, y, s, max u v x y s, max u v x y s} A
          strategy hwin policy pending) (inputOne, inputTwo) =
      profiledRawJointHybridPhysicalCompatibleRunInstalledLeftReceiver A
        strategy hwin policy fallback
        ((⟨state, member, .inr ⟨move, owner⟩⟩),
          some ⟨move, row, monitorState, staged⟩) (inputOne, inputTwo) :=
      congrArg
        (fun installed ↦
          profiledRawJointHybridPhysicalCompatibleRunInstalledLeftReceiver A
            strategy hwin policy fallback installed (inputOne, inputTwo))
        hinstalled
    _ = _ :=
      profiledRawJointHybridPhysicalCompatibleRunInstalledLeftReceiver_live A
        strategy hwin policy fallback state member move owner row monitorState
        staged (inputOne, inputTwo)

/-- Process-two one-cut mirror. -/
theorem
    profiledRawJointHybridPhysicalCompatibleFrontierTwoReceiver_of_installed
    (fallback : PairedEntryRow × RightOutput A strategy hwin
      (initial := initial))
    (two : TwoControl A strategy hwin policy) (inputTwo : In₂)
    (pending : FiniteAcknowledgedDelayedCarrier.DeferredMemberControl
      (OneShared A strategy hwin policy)
      (ProfiledRawJointHybridPhysicalCompatibleFrontierOnePayload A strategy
        hwin (initial := initial)))
    (inputOne : In₁)
    (state : CompatibleState A strategy hwin initial) (member : Bool)
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (owner : (move.memberController A false).Control)
    (row : PairedEntryRow)
    (monitorState :
      (profiledRawJointHybridPhysicalCompatibleSuccessorRightMonitor A strategy
        hwin (initial := initial) move false).State)
    (staged : Option (RightOutput A strategy hwin (initial := initial)))
    (hinstalled :
      profiledRawJointHybridPhysicalCompatibleInstallRightPendingMember.{u,
        v, x, y, s, max u v x y s, max u v x y s} A
          strategy hwin policy pending =
        ((⟨state, member, .inr ⟨move, owner⟩⟩),
          some ⟨move, row, monitorState, staged⟩)) :
    profiledRawJointHybridPhysicalCompatibleFrontierTwoReceiver A strategy hwin
        policy fallback two inputTwo (.inl pending) inputOne =
      (row,
        (profiledRawJointHybridPhysicalCompatibleRightReceiverStepFor A
          strategy hwin policy state move owner row monitorState
          (inputTwo, inputOne)).1) := by
  simp only
    [profiledRawJointHybridPhysicalCompatibleFrontierTwoReceiver]
  calc
    profiledRawJointHybridPhysicalCompatibleRunInstalledRightReceiver A
        strategy hwin policy fallback
        (profiledRawJointHybridPhysicalCompatibleInstallRightPendingMember.{u,
          v, x, y, s, max u v x y s, max u v x y s} A
          strategy hwin policy pending) (inputTwo, inputOne) =
      profiledRawJointHybridPhysicalCompatibleRunInstalledRightReceiver A
        strategy hwin policy fallback
        ((⟨state, member, .inr ⟨move, owner⟩⟩),
          some ⟨move, row, monitorState, staged⟩) (inputTwo, inputOne) :=
      congrArg
        (fun installed ↦
          profiledRawJointHybridPhysicalCompatibleRunInstalledRightReceiver A
            strategy hwin policy fallback installed (inputTwo, inputOne))
        hinstalled
    _ = _ :=
      profiledRawJointHybridPhysicalCompatibleRunInstalledRightReceiver_live A
        strategy hwin policy fallback state member move owner row monitorState
        staged (inputTwo, inputOne)

@[simp] theorem
    profiledRawJointHybridPhysicalCompatibleFrontierTwoSelectedOwner_inl
    (fallback : TwoShared A strategy hwin policy)
    (pending : FiniteAcknowledgedDelayedCarrier.DeferredMemberControl
      (TwoShared A strategy hwin policy)
      (ProfiledRawJointHybridPhysicalCompatibleFrontierTwoPayload A strategy
        hwin (initial := initial))) :
    profiledRawJointHybridPhysicalCompatibleFrontierTwoSelectedOwner A strategy
        hwin policy fallback (.inl pending) =
      let installed :=
        profiledRawJointHybridPhysicalCompatibleInstallLeftPendingMember.{u,
          v, x, y, s, max u v x y s, max u v x y s} A
          strategy hwin policy pending
      ⟨installed.1.1, installed.1.2.2⟩ :=
  rfl

/-! ## Physical outputs and the fully instantiated family -/

/-- Physical process-one response stored in a left receiver table at the
already selected entry row. -/
def profiledRawJointHybridPhysicalCompatibleLeftInformedOutputAtRow
    (row : PairedEntryRow)
    (output : LeftOutput A strategy hwin (initial := initial)) : Out₁ :=
  match row with
  | .first => output.physical.informedFirst
  | .both => output.physical.informedBoth

/-- Process-two mirror. -/
def profiledRawJointHybridPhysicalCompatibleRightInformedOutputAtRow
    (row : PairedEntryRow)
    (output : RightOutput A strategy hwin (initial := initial)) : Out₂ :=
  match row with
  | .first => output.physical.informedFirst
  | .both => output.physical.informedBoth

noncomputable def
    profiledRawJointHybridPhysicalCompatibleConcreteParentOne
    (fallback : OneShared A strategy hwin policy)
    (one : OneControl A strategy hwin policy) (_inputOne : In₁)
    (_two : TwoControl A strategy hwin policy) (_inputTwo : In₂) :
    OneShared A strategy hwin policy :=
  profiledRawJointHybridPhysicalCompatibleFrontierOneSelectedOwner A strategy
    hwin policy fallback one

noncomputable def
    profiledRawJointHybridPhysicalCompatibleConcreteParentTwo
    (fallback : TwoShared A strategy hwin policy)
    (two : TwoControl A strategy hwin policy) (_inputTwo : In₂)
    (_one : OneControl A strategy hwin policy) (_inputOne : In₁) :
    TwoShared A strategy hwin policy :=
  profiledRawJointHybridPhysicalCompatibleFrontierTwoSelectedOwner A strategy
    hwin policy fallback two

noncomputable def
    profiledRawJointHybridPhysicalCompatibleConcreteOutputOne
    (fallback : PairedEntryRow × LeftOutput A strategy hwin (initial := initial))
    (one : OneControl A strategy hwin policy) (inputOne : In₁)
    (two : TwoControl A strategy hwin policy) (inputTwo : In₂) : Out₁ :=
  let result :=
    profiledRawJointHybridPhysicalCompatibleFrontierOneReceiver A strategy hwin
      policy fallback one inputOne two inputTwo
  profiledRawJointHybridPhysicalCompatibleLeftInformedOutputAtRow A strategy
    hwin result.1 result.2

noncomputable def
    profiledRawJointHybridPhysicalCompatibleConcreteOutputTwo
    (fallback : PairedEntryRow × RightOutput A strategy hwin
      (initial := initial))
    (two : TwoControl A strategy hwin policy) (inputTwo : In₂)
    (one : OneControl A strategy hwin policy) (inputOne : In₁) : Out₂ :=
  let result :=
    profiledRawJointHybridPhysicalCompatibleFrontierTwoReceiver A strategy hwin
      policy fallback two inputTwo one inputOne
  profiledRawJointHybridPhysicalCompatibleRightInformedOutputAtRow A strategy
    hwin result.1 result.2

private noncomputable def concreteFreshOne
    (fallbackShared : OneShared A strategy hwin policy)
    (fallbackReceiver :
      PairedEntryRow × LeftOutput A strategy hwin (initial := initial)) :=
  profiledRawJointHybridPhysicalCompatibleFrontierFreshOne A strategy hwin
    policy
    (profiledRawJointHybridPhysicalCompatibleConcreteParentOne A strategy hwin
      policy fallbackShared)
    (profiledRawJointHybridPhysicalCompatibleFrontierOneReceiver A strategy
      hwin policy fallbackReceiver)

private noncomputable def concreteFreshTwo
    (fallbackShared : TwoShared A strategy hwin policy)
    (fallbackReceiver :
      PairedEntryRow × RightOutput A strategy hwin (initial := initial)) :=
  profiledRawJointHybridPhysicalCompatibleFrontierFreshTwo A strategy hwin
    policy
    (profiledRawJointHybridPhysicalCompatibleConcreteParentTwo A strategy hwin
      policy fallbackShared)
    (profiledRawJointHybridPhysicalCompatibleFrontierTwoReceiver A strategy
      hwin policy fallbackReceiver)

/-- The concrete finite local family.  Its ordinary `PUnit` summands are
totalization only; the pending-only theorems below show they are unreachable. -/
noncomputable def
    profiledRawJointHybridPhysicalCompatibleOperationalDeferredFamily
    (initialOne : OnePending A strategy hwin policy)
    (initialTwo : TwoPending A strategy hwin policy)
    (fallbackOneShared : OneShared A strategy hwin policy)
    (fallbackTwoShared : TwoShared A strategy hwin policy)
    (fallbackLeft :
      PairedEntryRow × LeftOutput A strategy hwin (initial := initial))
    (fallbackRight :
      PairedEntryRow × RightOutput A strategy hwin (initial := initial)) :=
  profiledRawJointHybridPhysicalCompatibleSuccessorDeferredFamily.{u, v, x, y,
      s, max u v x y s, 0, max u v x y s, 0, 0}
    A strategy hwin policy (.inl initialOne) (.inl initialTwo)
    (profiledRawJointHybridPhysicalCompatibleConcreteParentOne A strategy hwin
      policy fallbackOneShared)
    (profiledRawJointHybridPhysicalCompatibleFrontierOneReceiver A strategy
      hwin policy fallbackLeft)
    (profiledRawJointHybridPhysicalCompatibleConcreteParentTwo A strategy hwin
      policy fallbackTwoShared)
    (profiledRawJointHybridPhysicalCompatibleFrontierTwoReceiver A strategy
      hwin policy fallbackRight)
    (profiledRawJointHybridPhysicalCompatibleConcreteOutputOne A strategy hwin
      policy fallbackLeft)
    (profiledRawJointHybridPhysicalCompatibleConcreteOutputTwo A strategy hwin
      policy fallbackRight)

/-- Bank the singleton-key family and assemble its actual acknowledged finite
Mealy controller. -/
noncomputable def
    profiledRawJointHybridPhysicalCompatibleOperationalMealyController
    (initialOne : OnePending A strategy hwin policy)
    (initialTwo : TwoPending A strategy hwin policy)
    (fallbackOneShared : OneShared A strategy hwin policy)
    (fallbackTwoShared : TwoShared A strategy hwin policy)
    (fallbackLeft :
      PairedEntryRow × LeftOutput A strategy hwin (initial := initial))
    (fallbackRight :
      PairedEntryRow × RightOutput A strategy hwin (initial := initial)) :=
  let family :=
    profiledRawJointHybridPhysicalCompatibleOperationalDeferredFamily A
      strategy hwin policy initialOne initialTwo fallbackOneShared
        fallbackTwoShared fallbackLeft fallbackRight
  family.toExactClosingFamily.bankPairedMealyController PUnit.unit

/-- The probe controller's own physical Moore presentation.  Any theorem
about this machine must still supply its trace alignment explicitly; the
trace alignment must refer to this controller's own physical word. -/
noncomputable def
    profiledRawJointHybridPhysicalCompatibleOperationalPhysicalController
    (initialOne : OnePending A strategy hwin policy)
    (initialTwo : TwoPending A strategy hwin policy)
    (fallbackOneShared : OneShared A strategy hwin policy)
    (fallbackTwoShared : TwoShared A strategy hwin policy)
    (fallbackLeft :
      PairedEntryRow × LeftOutput A strategy hwin (initial := initial))
    (fallbackRight :
      PairedEntryRow × RightOutput A strategy hwin (initial := initial)) :=
  (profiledRawJointHybridPhysicalCompatibleOperationalMealyController A
    strategy hwin policy initialOne initialTwo fallbackOneShared
      fallbackTwoShared fallbackLeft fallbackRight).mooreize

/-! ## The ordinary `PUnit` branch is unreachable -/

private noncomputable def operationalSemanticTrace
    (initialOne : OnePending A strategy hwin policy)
    (initialTwo : TwoPending A strategy hwin policy)
    (fallbackOneShared : OneShared A strategy hwin policy)
    (fallbackTwoShared : TwoShared A strategy hwin policy)
    (fallbackLeft :
      PairedEntryRow × LeftOutput A strategy hwin (initial := initial))
    (fallbackRight :
      PairedEntryRow × RightOutput A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :=
  FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace
    (.inl initialOne : OneControl A strategy hwin policy)
    (.inl initialTwo : TwoControl A strategy hwin policy)
    (FiniteAcknowledgedDelayedCarrier.deferredOrRecurrentNoRecv
      (profiledRawJointHybridPhysicalCompatibleFrontierOnePendingStep A
        strategy hwin policy)
      profiledRawJointHybridPhysicalCompatibleFrontierOneRecurrentStep)
    (FiniteAcknowledgedDelayedCarrier.deferredOrRecurrentNoRecv
      (profiledRawJointHybridPhysicalCompatibleFrontierTwoPendingStep A
        strategy hwin policy)
      profiledRawJointHybridPhysicalCompatibleFrontierTwoRecurrentStep)
    (FiniteAcknowledgedDelayedCarrier.canonicalDeferredOpenRecvOne
      (concreteFreshOne A strategy hwin policy fallbackOneShared fallbackLeft)
      (profiledRawJointHybridPhysicalCompatibleConcreteOutputOne A strategy
        hwin policy fallbackLeft))
    (FiniteAcknowledgedDelayedCarrier.canonicalDeferredOpenRecvTwo
      (concreteFreshTwo A strategy hwin policy fallbackTwoShared fallbackRight)
      (profiledRawJointHybridPhysicalCompatibleConcreteOutputTwo A strategy
        hwin policy fallbackRight))
    (FiniteAcknowledgedDelayedCarrier.canonicalDeferredClose
      (concreteFreshOne A strategy hwin policy fallbackOneShared fallbackLeft)
      (concreteFreshTwo A strategy hwin policy fallbackTwoShared fallbackRight))
    env n

/-- The selected semantic execution never reaches either recurrent `PUnit`
summand. -/
theorem
    profiledRawJointHybridPhysicalCompatibleOperationalSemanticTrace_pending
    (initialOne : OnePending A strategy hwin policy)
    (initialTwo : TwoPending A strategy hwin policy)
    (fallbackOneShared : OneShared A strategy hwin policy)
    (fallbackTwoShared : TwoShared A strategy hwin policy)
    (fallbackLeft :
      PairedEntryRow × LeftOutput A strategy hwin (initial := initial))
    (fallbackRight :
      PairedEntryRow × RightOutput A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    FiniteAcknowledgedDelayedCarrier.DeferredPairIsPending
      (operationalSemanticTrace A strategy hwin policy initialOne initialTwo
        fallbackOneShared fallbackTwoShared fallbackLeft fallbackRight env n).1
      (operationalSemanticTrace A strategy hwin policy initialOne initialTwo
        fallbackOneShared fallbackTwoShared fallbackLeft fallbackRight env n).2 := by
  exact
    FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace_pending
      (profiledRawJointHybridPhysicalCompatibleFrontierOnePendingStep A
        strategy hwin policy)
      profiledRawJointHybridPhysicalCompatibleFrontierOneRecurrentStep
      (profiledRawJointHybridPhysicalCompatibleFrontierTwoPendingStep A
        strategy hwin policy)
      profiledRawJointHybridPhysicalCompatibleFrontierTwoRecurrentStep
      (concreteFreshOne A strategy hwin policy fallbackOneShared fallbackLeft)
      (concreteFreshTwo A strategy hwin policy fallbackTwoShared fallbackRight)
      (profiledRawJointHybridPhysicalCompatibleConcreteOutputOne A strategy
        hwin policy fallbackLeft)
      (profiledRawJointHybridPhysicalCompatibleConcreteOutputTwo A strategy
        hwin policy fallbackRight)
      initialOne initialTwo env n

/-! The stronger relay invariant audits every live/dormant interpretation of
the acknowledged carrier, not only the proof-side semantic selection. -/

private noncomputable def operationalRelayTrace
    (initialOne : OnePending A strategy hwin policy)
    (initialTwo : TwoPending A strategy hwin policy)
    (fallbackOneShared : OneShared A strategy hwin policy)
    (fallbackTwoShared : TwoShared A strategy hwin policy)
    (fallbackLeft :
      PairedEntryRow × LeftOutput A strategy hwin (initial := initial))
    (fallbackRight :
      PairedEntryRow × RightOutput A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :=
  FiniteAcknowledgedDelayedCarrier.canonicalDeferredRelayPairTrace
    (profiledRawJointHybridPhysicalCompatibleFrontierOnePendingStep A
      strategy hwin policy)
    profiledRawJointHybridPhysicalCompatibleFrontierOneRecurrentStep
    (profiledRawJointHybridPhysicalCompatibleFrontierTwoPendingStep A
      strategy hwin policy)
    profiledRawJointHybridPhysicalCompatibleFrontierTwoRecurrentStep
    (concreteFreshOne A strategy hwin policy fallbackOneShared fallbackLeft)
    (concreteFreshTwo A strategy hwin policy fallbackTwoShared fallbackRight)
    (profiledRawJointHybridPhysicalCompatibleConcreteOutputOne A strategy
      hwin policy fallbackLeft)
    (profiledRawJointHybridPhysicalCompatibleConcreteOutputTwo A strategy
      hwin policy fallbackRight)
    initialOne initialTwo env n

/-- Every runtime interpretation of the concrete relay stays in the pending
summands.  In particular, totalization through `PUnit` cannot affect a real
execution, independently of which old table member is acknowledged. -/
theorem
    profiledRawJointHybridPhysicalCompatibleOperationalRelayTrace_allPending
    (initialOne : OnePending A strategy hwin policy)
    (initialTwo : TwoPending A strategy hwin policy)
    (fallbackOneShared : OneShared A strategy hwin policy)
    (fallbackTwoShared : TwoShared A strategy hwin policy)
    (fallbackLeft :
      PairedEntryRow × LeftOutput A strategy hwin (initial := initial))
    (fallbackRight :
      PairedEntryRow × RightOutput A strategy hwin (initial := initial))
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    FiniteAcknowledgedDelayedCarrier.DeferredRelayPairAllPending
      (operationalRelayTrace A strategy hwin policy initialOne initialTwo
        fallbackOneShared fallbackTwoShared fallbackLeft fallbackRight env n).1
      (operationalRelayTrace A strategy hwin policy initialOne initialTwo
        fallbackOneShared fallbackTwoShared fallbackLeft fallbackRight env n).2 := by
  exact
    FiniteAcknowledgedDelayedCarrier.canonicalDeferredRelayPairTrace_allPending
      (profiledRawJointHybridPhysicalCompatibleFrontierOnePendingStep A
        strategy hwin policy)
      profiledRawJointHybridPhysicalCompatibleFrontierOneRecurrentStep
      (profiledRawJointHybridPhysicalCompatibleFrontierTwoPendingStep A
        strategy hwin policy)
      profiledRawJointHybridPhysicalCompatibleFrontierTwoRecurrentStep
      (concreteFreshOne A strategy hwin policy fallbackOneShared fallbackLeft)
      (concreteFreshTwo A strategy hwin policy fallbackTwoShared fallbackRight)
      (profiledRawJointHybridPhysicalCompatibleConcreteOutputOne A strategy
        hwin policy fallbackLeft)
      (profiledRawJointHybridPhysicalCompatibleConcreteOutputTwo A strategy
        hwin policy fallbackRight)
      initialOne initialTwo env n

end

end DetParityAutomaton

end DistributedSynthesis
