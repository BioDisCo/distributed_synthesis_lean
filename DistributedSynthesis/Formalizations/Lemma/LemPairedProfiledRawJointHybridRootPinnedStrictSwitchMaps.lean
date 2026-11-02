/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridRootPinnedStrictControlFamily

/-!
# Leader-free strict switches below the root-pinned policy

A receiver stores an optional opposite live macro staged by the checked local
handoff.  A strict switch reads that local field, restarts both roles from the
same macro, and executes the current local input.  No switch receives a graph,
an orientation, a side bit, or a leader signal.

The lookup is total only because the generic carrier is total on unreachable
states.  Its fallback is another macro extracted from the already certified
narrowed controller; it is not an identification with the canonical
`source.closeKey`.  On reachable closing runs the stored literal emitted
target is used.
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
  (first : In₁ × In₂)
  (bank : ProfiledRawJointHybridInitialRootPinnedPersistentControllerBank A
    strategy hwin first)

/-! ## Total staged-target lookup at one fixed first input -/

/-- Certified left-live fallback for an off-invariant right receiver. -/
noncomputable def
    profiledRawJointHybridInitialRootPinnedPersistentFallbackLeft
    (source :
      ProfiledRawJointHybridInitialRootPinnedPersistentRightMacro A strategy
        hwin first) :
    ProfiledRawJointHybridInitialRootPinnedPersistentLeftMacro A strategy hwin
      first :=
  Classical.choose
    (profiledRawJointHybridInitialRootPinnedPersistentRight_narrowedTargetMacro
      A strategy hwin first bank source (fun _ ↦ default) 0 .first)

/-- Certified right-live fallback for an off-invariant left receiver. -/
noncomputable def
    profiledRawJointHybridInitialRootPinnedPersistentFallbackRight
    (source :
      ProfiledRawJointHybridInitialRootPinnedPersistentLeftMacro A strategy
        hwin first) :
    ProfiledRawJointHybridInitialRootPinnedPersistentRightMacro A strategy hwin
      first :=
  Classical.choose
    (profiledRawJointHybridInitialRootPinnedPersistentLeft_narrowedTargetMacro
      A strategy hwin first bank source (fun _ ↦ default) 0 .first)

/-- The literal staged left macro, with a certified off-invariant fallback. -/
noncomputable def
    profiledRawJointHybridInitialRootPinnedPersistentRightReceiverTarget
    (receiver :
      ProfiledRawJointHybridInitialRootPinnedPersistentRightReceiverControl A
        strategy hwin first) :
    ProfiledRawJointHybridInitialRootPinnedPersistentLeftMacro A strategy hwin
      first :=
  receiver.2.2.2.getD
    (profiledRawJointHybridInitialRootPinnedPersistentFallbackLeft A strategy
      hwin first bank receiver.1)

/-- The literal staged right macro, with its mirror fallback. -/
noncomputable def
    profiledRawJointHybridInitialRootPinnedPersistentLeftReceiverTarget
    (receiver :
      ProfiledRawJointHybridInitialRootPinnedPersistentLeftReceiverControl A
        strategy hwin first) :
    ProfiledRawJointHybridInitialRootPinnedPersistentRightMacro A strategy hwin
      first :=
  receiver.2.2.2.getD
    (profiledRawJointHybridInitialRootPinnedPersistentFallbackRight A strategy
      hwin first bank receiver.1)

/-! ## Fixed-first executable switches -/

/-- Process one restarts as a left receiver from a delivered right receiver. -/
noncomputable def
    profiledRawJointHybridInitialRootPinnedPersistentStartLeftReceiver
    (receiver :
      ProfiledRawJointHybridInitialRootPinnedPersistentRightReceiverControl A
        strategy hwin first)
    (move : In₁ × In₂) :
    Out₁ ×
      ProfiledRawJointHybridInitialRootPinnedPersistentLeftReceiverControl A
        strategy hwin first :=
  let target :=
    profiledRawJointHybridInitialRootPinnedPersistentRightReceiverTarget A
      strategy hwin first bank receiver
  let restart :=
    profiledRawJointHybridInitialRootPinnedPersistentRestartLeft A strategy
      hwin first bank target receiver.2.1
  continueProfiledRawJointHybridInitialRootPinnedPersistentLeftReceiver A
    strategy hwin first bank restart.2 restart.1 move

/-- Process two locally restarts as the matching left owner. -/
noncomputable def
    profiledRawJointHybridInitialRootPinnedPersistentStartLeftOwner
    (receiver :
      ProfiledRawJointHybridInitialRootPinnedPersistentRightReceiverControl A
        strategy hwin first)
    (input : In₂) :
    Out₂ ×
      ProfiledRawJointHybridInitialRootPinnedPersistentLeftOwnerControl A
        strategy hwin first bank :=
  let target :=
    profiledRawJointHybridInitialRootPinnedPersistentRightReceiverTarget A
      strategy hwin first bank receiver
  let restart :=
    profiledRawJointHybridInitialRootPinnedPersistentRestartLeft A strategy
      hwin first bank target receiver.2.1
  stepProfiledRawJointHybridInitialRootPinnedPersistentLeftOwner A strategy
    hwin first bank restart.1 input

/-- Process two restarts as a right receiver from a delivered left receiver. -/
noncomputable def
    profiledRawJointHybridInitialRootPinnedPersistentStartRightReceiver
    (receiver :
      ProfiledRawJointHybridInitialRootPinnedPersistentLeftReceiverControl A
        strategy hwin first)
    (move : In₂ × In₁) :
    Out₂ ×
      ProfiledRawJointHybridInitialRootPinnedPersistentRightReceiverControl A
        strategy hwin first :=
  let target :=
    profiledRawJointHybridInitialRootPinnedPersistentLeftReceiverTarget A
      strategy hwin first bank receiver
  let restart :=
    profiledRawJointHybridInitialRootPinnedPersistentRestartRight A strategy
      hwin first bank target receiver.2.1
  continueProfiledRawJointHybridInitialRootPinnedPersistentRightReceiver A
    strategy hwin first bank restart.2 restart.1 move

/-- Process one locally restarts as the matching right owner. -/
noncomputable def
    profiledRawJointHybridInitialRootPinnedPersistentStartRightOwner
    (receiver :
      ProfiledRawJointHybridInitialRootPinnedPersistentLeftReceiverControl A
        strategy hwin first)
    (input : In₁) :
    Out₁ ×
      ProfiledRawJointHybridInitialRootPinnedPersistentRightOwnerControl A
        strategy hwin first bank :=
  let target :=
    profiledRawJointHybridInitialRootPinnedPersistentLeftReceiverTarget A
      strategy hwin first bank receiver
  let restart :=
    profiledRawJointHybridInitialRootPinnedPersistentRestartRight A strategy
      hwin first bank target receiver.2.1
  stepProfiledRawJointHybridInitialRootPinnedPersistentRightOwner A strategy
    hwin first bank restart.1 input

/-! ## Exact common-source laws -/

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- The independently executable left-role switches restart the same literal
macro. -/
theorem
    profiledRawJointHybridInitialRootPinnedPersistentStartLeft_commonSource
    (receiver :
      ProfiledRawJointHybridInitialRootPinnedPersistentRightReceiverControl A
        strategy hwin first)
    (move : In₁ × In₂) :
    (profiledRawJointHybridInitialRootPinnedPersistentStartLeftReceiver A
      strategy hwin first bank receiver move).2.1 =
      (profiledRawJointHybridInitialRootPinnedPersistentStartLeftOwner A
        strategy hwin first bank receiver move.2).2.1 := by
  simp [
    profiledRawJointHybridInitialRootPinnedPersistentStartLeftReceiver,
    profiledRawJointHybridInitialRootPinnedPersistentStartLeftOwner,
    continueProfiledRawJointHybridInitialRootPinnedPersistentLeftReceiver_source,
    stepProfiledRawJointHybridInitialRootPinnedPersistentLeftOwner_source]

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Right-role mirror common-source law. -/
theorem
    profiledRawJointHybridInitialRootPinnedPersistentStartRight_commonSource
    (receiver :
      ProfiledRawJointHybridInitialRootPinnedPersistentLeftReceiverControl A
        strategy hwin first)
    (move : In₂ × In₁) :
    (profiledRawJointHybridInitialRootPinnedPersistentStartRightOwner A
      strategy hwin first bank receiver move.2).2.1 =
      (profiledRawJointHybridInitialRootPinnedPersistentStartRightReceiver A
        strategy hwin first bank receiver move).2.1 := by
  simp [
    profiledRawJointHybridInitialRootPinnedPersistentStartRightReceiver,
    profiledRawJointHybridInitialRootPinnedPersistentStartRightOwner,
    continueProfiledRawJointHybridInitialRootPinnedPersistentRightReceiver_source,
    stepProfiledRawJointHybridInitialRootPinnedPersistentRightOwner_source]

end

end DetParityAutomaton

end DistributedSynthesis
