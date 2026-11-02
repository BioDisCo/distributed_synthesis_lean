/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleSuccessorRootWholeTraceBridge
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleSuccessorLiveOverlaySchedule

/-!
# The first recurrent cut after the compatible common-root handoff

The root handoff and the recurrent phase-live proof used to meet only at the
physical word.  That is too weak: the first recurrent table must start at the
same compatible-policy key selected by the root transition, and the DPA slice
must be a suffix of the very same global-machine trace.

This file records the exact seam.  The two structures below retain one
schedule-selected orientation at cut `1`, its literal scheduled alignment,
and equality of the next abstract state with the control actually installed
at the close.  Their conversion theorems produce the existing resolved
transition packet at index `0` for the unchanged machine, word, policy, and
root exit.

The two possible target keys are never equated.  Only the member selected by
the actual close is installed.  Orientations and members are proof-side
indices; no executable transition receives a graph, hierarchy side, leader,
or strict-leader bit.
-/

namespace DistributedSynthesis

universe u v x y s w c

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

private abbrev PhysicalWord :=
  OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂)

/-! ## Exact root projections -/

namespace
    ProfiledRawJointHybridPhysicalCompatibleSuccessorRootHandoffAt

variable {initial : ProfiledRawJointCommonBaseWorld A strategy}
variable {policy : CompatiblePolicy A strategy hwin initial}
variable {G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂}
variable {outputOne : G.State → Out₁} {outputTwo : G.State → Out₂}
variable {env : EnvironmentSequence In₁ In₂}

/-- The root close crosses the lineage side exactly once.  This fact is
definitionally present in `toInitialExit`, but exporting it avoids reopening
the root target witness in every recurrent proof. -/
theorem initialSide_other_eq_exitSide
    (handoff :
      ProfiledRawJointHybridPhysicalCompatibleSuccessorRootHandoffAt A
        strategy hwin policy G outputOne outputTwo env) :
    (handoff.toInitialExit A strategy hwin).initialSide.other =
      handoff.exitSide := by
  rcases handoff with
    ⟨start, cuts, target, side, root, controllerTarget, transition,
      blockMin⟩
  cases controllerTarget <;> rfl

/-- The exit package retains literally the target selected by the root
handoff. -/
theorem toInitialExit_exitTarget
    (handoff :
      ProfiledRawJointHybridPhysicalCompatibleSuccessorRootHandoffAt A
        strategy hwin policy G outputOne outputTwo env) :
    (handoff.toInitialExit A strategy hwin).exitTarget = handoff.target := by
  rcases handoff with
    ⟨start, cuts, target, side, root, controllerTarget, transition,
      blockMin⟩
  cases controllerTarget <;> rfl

/-- Hence the abstract state at the first recurrent cut is exactly the state
stored by the canonical phase-live seed. -/
theorem state_zero_eq_phaseLiveSeed_state
    (handoff :
      ProfiledRawJointHybridPhysicalCompatibleSuccessorRootHandoffAt A
        strategy hwin policy G outputOne outputTwo env)
    (later : Nat → CompatibleState A strategy hwin initial) :
    (handoff.toInitialExit A strategy hwin).state A strategy hwin later 0 =
      (handoff.phaseLiveSeed A strategy hwin).state := by
  rw [(handoff.toInitialExit A strategy hwin).state_zero A strategy hwin later]
  rw [handoff.toInitialExit_exitTarget A strategy hwin]
  exact (handoff.phaseLiveSeed A strategy hwin).state_eq.symm

end
  ProfiledRawJointHybridPhysicalCompatibleSuccessorRootHandoffAt

/-! ## One selected right-table cut -/

/-- Literal data for a right-table block beginning at root-relative cut `1`.

The `alignment` field exposes the DPA entry state, record length, physical
slice, and closing inputs.  `later_zero_eq_installed` is the missing
control-state seam: it identifies the next abstract policy state with the
state installed by the actual acknowledgement member. -/
structure
    ProfiledRawJointHybridPhysicalCompatibleRootRightCutOneAlignment
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (env : EnvironmentSequence In₁ In₂)
    (handoff :
      ProfiledRawJointHybridPhysicalCompatibleSuccessorRootHandoffAt A
        strategy hwin policy G outputOne outputTwo env)
    (later : Nat → CompatibleState A strategy hwin initial)
    (schedule : OperationalCloseMemberSchedule
      (fun j ↦
        ((OmegaWord.drop
          (G.globalMachineTraceWord outputOne outputTwo env) handoff.start) j
          ).graph))
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (tableMember : Bool) (localEnv : Nat → In₂ × In₁) (n : Nat)
    {ParentShared : Type c} (shared : ParentShared) : Prop where
  exit_side : handoff.exitSide = .right
  cuts_eq : handoff.cuts = schedule.cutPackage.cuts
  alignment :
    ProfiledRawJointHybridPhysicalCompatibleRightScheduledAlignmentAt A
      strategy hwin policy (handoff.phaseLiveSeed A strategy hwin).state move
        tableMember handoff.target.2.1 localEnv n
        (A.run (G.globalMachineTraceWord outputOne outputTwo env) handoff.start)
        (OmegaWord.drop (G.globalMachineTraceWord outputOne outputTwo env)
          handoff.start) schedule 1
  successor_key :
    let output :=
      (profiledRawJointHybridPhysicalCompatibleRightDecoratedPlay A strategy
        hwin policy (handoff.phaseLiveSeed A strategy hwin).state move
          tableMember localEnv n).2.1
    let target := (output.target handoff.target.2.1).1
    ProfiledRawJointHybridPhysicalCompatibleRightSuccessorKeyAt A strategy
      hwin policy (handoff.phaseLiveSeed A strategy hwin).state
        (profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A strategy
          hwin target) target.1
  later_zero_eq_installed :
    let output :=
      (profiledRawJointHybridPhysicalCompatibleRightDecoratedPlay A strategy
        hwin policy (handoff.phaseLiveSeed A strategy hwin).state move
          tableMember localEnv n).2.1
    let pending :=
      profiledRawJointHybridPhysicalCompatibleRightPendingPayloadOfOutput A
        strategy hwin output handoff.target.2.1
    later 0 =
      (profiledRawJointHybridPhysicalCompatibleInstallLeftPendingMember.{u, v,
        x, y, s, c, max u v x y s} A strategy hwin policy
          (schedule.closeMember 1, shared, pending)).1.1

namespace
    ProfiledRawJointHybridPhysicalCompatibleRootRightCutOneAlignment

variable {initial : ProfiledRawJointCommonBaseWorld A strategy}
variable {policy : CompatiblePolicy A strategy hwin initial}
variable {G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂}
variable {outputOne : G.State → Out₁} {outputTwo : G.State → Out₂}
variable {env : EnvironmentSequence In₁ In₂}
variable
  {handoff :
    ProfiledRawJointHybridPhysicalCompatibleSuccessorRootHandoffAt A strategy
      hwin policy G outputOne outputTwo env}
variable {later : Nat → CompatibleState A strategy hwin initial}
variable
  {schedule : OperationalCloseMemberSchedule
    (fun j ↦
      ((OmegaWord.drop (G.globalMachineTraceWord outputOne outputTwo env)
        handoff.start) j).graph)}
variable {move : ProfiledRawJointRightPhysicalSiblingMove A}
variable {tableMember : Bool} {localEnv : Nat → In₂ × In₁} {n : Nat}
variable {ParentShared : Type c} {shared : ParentShared}

/-- The selected right cut closes directly to the resolved packet consumed by
the whole-trace theorem. -/
theorem nonempty_transitionPacket
    (cut :
      ProfiledRawJointHybridPhysicalCompatibleRootRightCutOneAlignment A
        strategy hwin policy G outputOne outputTwo env handoff later schedule
          move tableMember localEnv n shared) :
    Nonempty
      (ProfiledRawJointHybridPhysicalCompatibleResolvedTransitionPacketAt A
        strategy hwin policy G outputOne outputTwo env
          (handoff.toInitialExit A strategy hwin).initialSide
          ((handoff.toInitialExit A strategy hwin).state A strategy hwin later)
          handoff.start handoff.cuts 0) := by
  let word := G.globalMachineTraceWord outputOne outputTwo env
  let tail := OmegaWord.drop word handoff.start
  let output :=
    (profiledRawJointHybridPhysicalCompatibleRightDecoratedPlay A strategy hwin
      policy (handoff.phaseLiveSeed A strategy hwin).state move tableMember
        localEnv n).2.1
  let pending :=
    profiledRawJointHybridPhysicalCompatibleRightPendingPayloadOfOutput A
      strategy hwin output handoff.target.2.1
  let target :=
    profiledRawJointHybridPhysicalCompatibleRightPendingPayloadTarget A strategy
      hwin pending (schedule.closeMember 1)
  let installed :=
    profiledRawJointHybridPhysicalCompatibleInstallLeftPendingMember.{u, v, x,
      y, s, c, max u v x y s} A strategy hwin policy
        (schedule.closeMember 1, shared, pending)
  have hpacket := cut.alignment.transitionCutPacket A strategy hwin shared
    cut.successor_key
  change ∃ slot : ProfiledRawLeftSlot A,
      installed.1.1 =
          profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A strategy
            hwin target ∧
        ProfiledRawJointHybridPhysicalCompatibleSuccessorTargetAt A strategy
          hwin policy (handoff.phaseLiveSeed A strategy hwin).state target .left
            (.inr slot) ∧
        cutBlockMin
            (fun j ↦ A.priority
              (A.runFrom (A.run word handoff.start) tail j))
            schedule.cutPackage.cuts 1 =
          profiledRawJointThreadRootPriority A (.inr slot) ∧
        A.runFrom (A.run word handoff.start) tail
            (schedule.cutPackage.cuts 2) =
          pairedCodeStateForRow A
            (profiledRawJointCloseRowOfMember (schedule.closeMember 1))
            slot.1.1 at hpacket
  rcases hpacket with ⟨slot, hinstalled, htarget, hminimum, hnext⟩
  refine ⟨
    ProfiledRawJointHybridPhysicalCompatibleResolvedTransitionPacketAt.right
      (member := schedule.closeMember 1) (target := target)
      (nextRow := profiledRawJointCloseRowOfMember (schedule.closeMember 1))
      ?_ ?_⟩
  · have hrootSide :=
      handoff.initialSide_other_eq_exitSide A strategy hwin
    rw [cut.exit_side] at hrootSide
    cases hinitial : (handoff.toInitialExit A strategy hwin).initialSide with
    | right =>
        simp [IndexedLineageSide.other, hinitial] at hrootSide
    | left => rfl
  · refine ⟨slot, ?_, ?_, ?_, ?_⟩
    · exact cut.later_zero_eq_installed.trans hinstalled
    · rw [handoff.state_zero_eq_phaseLiveSeed_state A strategy hwin later]
      exact htarget
    · rw [cut.cuts_eq]
      exact
        (cutBlockMin_runFrom_drop_eq_shifted_run A word handoff.start
          schedule.cutPackage.cuts 1).symm.trans hminimum
    · rw [cut.cuts_eq]
      change A.runFrom A.initial word
          (handoff.start + schedule.cutPackage.cuts 2) = _
      have hshift := hnext
      change
        A.runFrom (A.runFrom A.initial word handoff.start)
            (OmegaWord.drop word handoff.start)
            (schedule.cutPackage.cuts 2) = _ at hshift
      rw [A.runFrom_drop] at hshift
      exact hshift

end
  ProfiledRawJointHybridPhysicalCompatibleRootRightCutOneAlignment

/-! ## Left-table mirror -/

structure
    ProfiledRawJointHybridPhysicalCompatibleRootLeftCutOneAlignment
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (env : EnvironmentSequence In₁ In₂)
    (handoff :
      ProfiledRawJointHybridPhysicalCompatibleSuccessorRootHandoffAt A
        strategy hwin policy G outputOne outputTwo env)
    (later : Nat → CompatibleState A strategy hwin initial)
    (schedule : OperationalCloseMemberSchedule
      (fun j ↦
        ((OmegaWord.drop
          (G.globalMachineTraceWord outputOne outputTwo env) handoff.start) j
          ).graph))
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (tableMember : Bool) (localEnv : Nat → In₁ × In₂) (n : Nat)
    {ParentShared : Type c} (shared : ParentShared) : Prop where
  exit_side : handoff.exitSide = .left
  cuts_eq : handoff.cuts = schedule.cutPackage.cuts
  alignment :
    ProfiledRawJointHybridPhysicalCompatibleLeftScheduledAlignmentAt A
      strategy hwin policy (handoff.phaseLiveSeed A strategy hwin).state move
        tableMember handoff.target.2.1 localEnv n
        (A.run (G.globalMachineTraceWord outputOne outputTwo env) handoff.start)
        (OmegaWord.drop (G.globalMachineTraceWord outputOne outputTwo env)
          handoff.start) schedule 1
  successor_key :
    let output :=
      (profiledRawJointHybridPhysicalCompatibleLeftDecoratedPlay A strategy
        hwin policy (handoff.phaseLiveSeed A strategy hwin).state move
          tableMember localEnv n).2.1
    let target := (output.target handoff.target.2.1).1
    ProfiledRawJointHybridPhysicalCompatibleLeftSuccessorKeyAt A strategy hwin
      policy (handoff.phaseLiveSeed A strategy hwin).state
        (profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A strategy
          hwin target) target.1
  later_zero_eq_installed :
    let output :=
      (profiledRawJointHybridPhysicalCompatibleLeftDecoratedPlay A strategy
        hwin policy (handoff.phaseLiveSeed A strategy hwin).state move
          tableMember localEnv n).2.1
    let pending :=
      profiledRawJointHybridPhysicalCompatibleLeftPendingPayloadOfOutput A
        strategy hwin output handoff.target.2.1
    later 0 =
      (profiledRawJointHybridPhysicalCompatibleInstallRightPendingMember.{u, v,
        x, y, s, c, max u v x y s} A strategy hwin policy
          (schedule.closeMember 1, shared, pending)).1.1

namespace
    ProfiledRawJointHybridPhysicalCompatibleRootLeftCutOneAlignment

variable {initial : ProfiledRawJointCommonBaseWorld A strategy}
variable {policy : CompatiblePolicy A strategy hwin initial}
variable {G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂}
variable {outputOne : G.State → Out₁} {outputTwo : G.State → Out₂}
variable {env : EnvironmentSequence In₁ In₂}
variable
  {handoff :
    ProfiledRawJointHybridPhysicalCompatibleSuccessorRootHandoffAt A strategy
      hwin policy G outputOne outputTwo env}
variable {later : Nat → CompatibleState A strategy hwin initial}
variable
  {schedule : OperationalCloseMemberSchedule
    (fun j ↦
      ((OmegaWord.drop (G.globalMachineTraceWord outputOne outputTwo env)
        handoff.start) j).graph)}
variable {move : ProfiledRawJointLeftPhysicalSiblingMove A}
variable {tableMember : Bool} {localEnv : Nat → In₁ × In₂} {n : Nat}
variable {ParentShared : Type c} {shared : ParentShared}

/-- Left-table conversion to the first resolved recurrent packet. -/
theorem nonempty_transitionPacket
    (cut :
      ProfiledRawJointHybridPhysicalCompatibleRootLeftCutOneAlignment A
        strategy hwin policy G outputOne outputTwo env handoff later schedule
          move tableMember localEnv n shared) :
    Nonempty
      (ProfiledRawJointHybridPhysicalCompatibleResolvedTransitionPacketAt A
        strategy hwin policy G outputOne outputTwo env
          (handoff.toInitialExit A strategy hwin).initialSide
          ((handoff.toInitialExit A strategy hwin).state A strategy hwin later)
          handoff.start handoff.cuts 0) := by
  let word := G.globalMachineTraceWord outputOne outputTwo env
  let tail := OmegaWord.drop word handoff.start
  let output :=
    (profiledRawJointHybridPhysicalCompatibleLeftDecoratedPlay A strategy hwin
      policy (handoff.phaseLiveSeed A strategy hwin).state move tableMember
        localEnv n).2.1
  let pending :=
    profiledRawJointHybridPhysicalCompatibleLeftPendingPayloadOfOutput A
      strategy hwin output handoff.target.2.1
  let target :=
    profiledRawJointHybridPhysicalCompatibleLeftPendingPayloadTarget A strategy
      hwin pending (schedule.closeMember 1)
  let installed :=
    profiledRawJointHybridPhysicalCompatibleInstallRightPendingMember.{u, v, x,
      y, s, c, max u v x y s} A strategy hwin policy
        (schedule.closeMember 1, shared, pending)
  have hpacket := cut.alignment.transitionCutPacket A strategy hwin shared
    cut.successor_key
  change ∃ slot : ProfiledRawRightSlot A,
      installed.1.1 =
          profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A strategy
            hwin target ∧
        ProfiledRawJointHybridPhysicalCompatibleSuccessorTargetAt A strategy
          hwin policy (handoff.phaseLiveSeed A strategy hwin).state target
            .right (.inl slot) ∧
        cutBlockMin
            (fun j ↦ A.priority
              (A.runFrom (A.run word handoff.start) tail j))
            schedule.cutPackage.cuts 1 =
          profiledRawJointThreadRootPriority A (.inl slot) ∧
        A.runFrom (A.run word handoff.start) tail
            (schedule.cutPackage.cuts 2) =
          pairedCodeStateForRow A
            (profiledRawJointCloseRowOfMember (schedule.closeMember 1))
            slot.1.1 at hpacket
  rcases hpacket with ⟨slot, hinstalled, htarget, hminimum, hnext⟩
  refine ⟨
    ProfiledRawJointHybridPhysicalCompatibleResolvedTransitionPacketAt.left
      (member := schedule.closeMember 1) (target := target)
      (nextRow := profiledRawJointCloseRowOfMember (schedule.closeMember 1))
      ?_ ?_⟩
  · have hrootSide :=
      handoff.initialSide_other_eq_exitSide A strategy hwin
    rw [cut.exit_side] at hrootSide
    cases hinitial : (handoff.toInitialExit A strategy hwin).initialSide with
    | right => rfl
    | left =>
        simp [IndexedLineageSide.other, hinitial] at hrootSide
  · refine ⟨slot, ?_, ?_, ?_, ?_⟩
    · exact cut.later_zero_eq_installed.trans hinstalled
    · rw [handoff.state_zero_eq_phaseLiveSeed_state A strategy hwin later]
      exact htarget
    · rw [cut.cuts_eq]
      exact
        (cutBlockMin_runFrom_drop_eq_shifted_run A word handoff.start
          schedule.cutPackage.cuts 1).symm.trans hminimum
    · rw [cut.cuts_eq]
      change A.runFrom A.initial word
          (handoff.start + schedule.cutPackage.cuts 2) = _
      have hshift := hnext
      change
        A.runFrom (A.runFrom A.initial word handoff.start)
            (OmegaWord.drop word handoff.start)
            (schedule.cutPackage.cuts 2) = _ at hshift
      rw [A.runFrom_drop] at hshift
      exact hshift

end
  ProfiledRawJointHybridPhysicalCompatibleRootLeftCutOneAlignment

end

end DetParityAutomaton

end DistributedSynthesis
