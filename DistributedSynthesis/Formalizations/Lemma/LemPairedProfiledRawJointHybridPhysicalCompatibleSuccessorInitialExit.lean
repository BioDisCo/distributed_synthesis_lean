/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleSuccessorResolvedMemberStream

/-!
# The literal common-root exit of a compatible successor stream

Successor-decorated sibling tables begin only after the compatible policy has
left its common root.  This file isolates that exceptional first close.  The
common root itself supplies its code and either initial live slot
unconditionally.  A checked physical close then owes only

* one exact same-policy decorated target transition; and
* the literal minimum-priority equation for its physical slice.

The post-exit state sequence is defined by prepending the retained target key
to an arbitrary later sequence.  Consequently its depth-zero equation is
definitional, rather than another trace invariant.

The side and roots below are proof-side lineage data.  They are not inputs to
an endpoint controller and do not reveal a graph orientation or strict
leader.
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

/-! ## The common root already supplies the first live lineage -/

/-- The selected compatible policy starts at the advertised common code. -/
theorem profiledRawJointHybridPhysicalCompatiblePolicy_initial_code
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial) :
    (policy.run []).1.1 =
      .common ((profiledRawJointCommonWorldFamily A initial).incidenceCode A) := by
  have hroot := congrArg (fun state ↦ state.1.1) policy.accepts.1.1
  simpa [sourceFreeBeliefCodeParityRunAutomaton] using hroot

/-- Choosing the process-one lineage at the common root is always live. -/
theorem profiledRawJointHybridPhysicalCompatiblePolicy_initial_right_live
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial) :
    profiledRawJointHybridCurrentSlots A .right (policy.run []).1.1 () =
      some (.inl (initial.procOneSlot A)) := by
  rw [profiledRawJointHybridPhysicalCompatiblePolicy_initial_code A strategy
    hwin policy]
  rfl

/-- Choosing the process-two lineage at the common root is always live. -/
theorem profiledRawJointHybridPhysicalCompatiblePolicy_initial_left_live
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial) :
    profiledRawJointHybridCurrentSlots A .left (policy.run []).1.1 () =
      some (.inr (initial.procTwoSlot A)) := by
  rw [profiledRawJointHybridPhysicalCompatiblePolicy_initial_code A strategy
    hwin policy]
  rfl

/-! ## One controller-independent physical exit -/

/-- The complete acceptance-facing information supplied by the first
physical close.  Unlike recurrent member packets, this packet starts at the
common policy root.

`exit_at` contains both the crossed live root of the bare target and the exact
successor transition of the unchanged compatible policy.  `exit_blockMin`
is the only physical-word field. -/
structure ProfiledRawJointHybridPhysicalCompatibleSuccessorInitialExit
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (env : EnvironmentSequence In₁ In₂)
    (start : Nat) (cuts : Nat → Nat) : Type _ where
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
  exit_blockMin :
    cutBlockMin
        (fun j ↦ A.priority
          (A.run (G.globalMachineTraceWord outputOne outputTwo env)
            (start + j)))
        cuts 0 =
      profiledRawJointThreadRootPriority A exitRoot

namespace ProfiledRawJointHybridPhysicalCompatibleSuccessorInitialExit

variable {initial : ProfiledRawJointCommonBaseWorld A strategy}
variable {policy : CompatiblePolicy A strategy hwin initial}
variable {G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂}
variable {outputOne : G.State → Out₁} {outputTwo : G.State → Out₂}
variable {env : EnvironmentSequence In₁ In₂}
variable {start : Nat} {cuts : Nat → Nat}

/-- A physical right close starts from the common right lineage and crosses
to a live left slot.  The common-root code and live premise are discharged
here, independently of the controller producing the close. -/
def ofRight
    (targetCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (row : PairedEntryRow)
    (next : CompatibleState A strategy hwin initial)
    (slot : ProfiledRawLeftSlot A)
    (target_live : targetCode.family.left () = some slot)
    (transition : Nonempty
      (ProfiledRawJointHybridPhysicalCompatibleTargetTransitionAt A strategy
        hwin policy (policy.run []) next .left (.inr slot)))
    (blockMin :
      cutBlockMin
          (fun j ↦ A.priority
            (A.run (G.globalMachineTraceWord outputOne outputTwo env)
              (start + j)))
          cuts 0 =
        profiledRawJointThreadRootPriority A (.inr slot)) :
    ProfiledRawJointHybridPhysicalCompatibleSuccessorInitialExit A strategy
      hwin policy G outputOne outputTwo env start cuts where
  initialSide := .right
  initialRoot := .inl (initial.procOneSlot A)
  initial_live :=
    profiledRawJointHybridPhysicalCompatiblePolicy_initial_right_live A
      strategy hwin policy
  exitTarget := (targetCode, (row, next))
  exitRoot := .inr slot
  exit_at := {
    root_at := .right (targetCode, (row, next)) slot target_live
    transition := transition }
  exit_blockMin := blockMin

/-- Left-close mirror. -/
def ofLeft
    (targetCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (row : PairedEntryRow)
    (next : CompatibleState A strategy hwin initial)
    (slot : ProfiledRawRightSlot A)
    (target_live : targetCode.family.right () = some slot)
    (transition : Nonempty
      (ProfiledRawJointHybridPhysicalCompatibleTargetTransitionAt A strategy
        hwin policy (policy.run []) next .right (.inl slot)))
    (blockMin :
      cutBlockMin
          (fun j ↦ A.priority
            (A.run (G.globalMachineTraceWord outputOne outputTwo env)
              (start + j)))
          cuts 0 =
        profiledRawJointThreadRootPriority A (.inl slot)) :
    ProfiledRawJointHybridPhysicalCompatibleSuccessorInitialExit A strategy
      hwin policy G outputOne outputTwo env start cuts where
  initialSide := .left
  initialRoot := .inr (initial.procTwoSlot A)
  initial_live :=
    profiledRawJointHybridPhysicalCompatiblePolicy_initial_left_live A strategy
      hwin policy
  exitTarget := (targetCode, (row, next))
  exitRoot := .inl slot
  exit_at := {
    root_at := .left (targetCode, (row, next)) slot target_live
    transition := transition }
  exit_blockMin := blockMin

/-! ## Definitional post-exit state and stream assembly -/

/-- Prepend the first retained key to the later recurrent state sequence. -/
def state
    (exit :
      ProfiledRawJointHybridPhysicalCompatibleSuccessorInitialExit A strategy
        hwin policy G outputOne outputTwo env start cuts)
    (later : Nat → CompatibleState A strategy hwin initial) :
    Nat → CompatibleState A strategy hwin initial
  | 0 =>
      profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A strategy
        hwin exit.exitTarget
  | n + 1 => later n

@[simp] theorem state_zero
    (exit :
      ProfiledRawJointHybridPhysicalCompatibleSuccessorInitialExit A strategy
        hwin policy G outputOne outputTwo env start cuts)
    (later : Nat → CompatibleState A strategy hwin initial) :
    exit.state A strategy hwin later 0 =
      profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A strategy
        hwin exit.exitTarget :=
  rfl

/-- Attach any recurrent resolved-member boundary stream to the checked
common-root exit.  All six exceptional depth-zero fields are discharged by
the exit package; the caller supplies only the ordinary cut schedule and the
later boundaries. -/
noncomputable def toResolvedMemberStream
    (exit :
      ProfiledRawJointHybridPhysicalCompatibleSuccessorInitialExit A strategy
        hwin policy G outputOne outputTwo env start cuts)
    (later : Nat → CompatibleState A strategy hwin initial)
    (cuts_strictMono : StrictMono cuts) (cuts_zero : cuts 0 = 0)
    (boundary : ∀ n : Nat,
      ProfiledRawJointHybridPhysicalCompatibleResolvedMemberBoundaryAt A
        strategy hwin policy G outputOne outputTwo env exit.initialSide
          (exit.state A strategy hwin later) start cuts n) :
    ProfiledRawJointHybridPhysicalCompatibleResolvedMemberStream A strategy
      hwin policy G outputOne outputTwo env where
  initial_code :=
    profiledRawJointHybridPhysicalCompatiblePolicy_initial_code A strategy
      hwin policy
  initialSide := exit.initialSide
  initialRoot := exit.initialRoot
  initial_live := exit.initial_live
  exitTarget := exit.exitTarget
  exitRoot := exit.exitRoot
  exit_at := exit.exit_at
  state := exit.state A strategy hwin later
  state_zero := exit.state_zero A strategy hwin later
  start := start
  cuts := cuts
  cuts_strictMono := cuts_strictMono
  cuts_zero := cuts_zero
  exit_blockMin := exit.exit_blockMin
  boundary := boundary

end ProfiledRawJointHybridPhysicalCompatibleSuccessorInitialExit

end

end DetParityAutomaton

end DistributedSynthesis
