/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledRawJointUnitPolicyMatchedPhase
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointUnitPhysicalPriority

/-!
# Physical block minima at raw-joint policy handoffs

This file specializes the pointwise raw-joint priority theorem to the actual
finite-controller prefixes of the local handoff.  At every real close, the
macro literally staged for the opposite orientation carries exactly the
minimum original-DPA priority of the emitted physical block prefix.
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

/-- The literal narrowed-tree play used by one actual right-controller
prefix and its closing move. -/
noncomputable def profiledRawJointUnitRightPolicyPlay
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (initial.code A))
    (bank : ProfiledRawJointUnitPolicyControllerBank A strategy initial policy)
    (source : ProfiledRawJointUnitRightPolicyMacro A strategy (initial.code A)
      policy) (past : List (In₂ × In₁)) (move : In₂ × In₁) :
    Nat → RealizedBlockRound In₂ In₁
      (ProfiledRawJointUnitRightReceiverOutput A strategy (initial.code A))
      Out₁ :=
  let monitor := profiledRawJointUnitRightBlockMonitor.{u, v, x, y, s,
    max u v x y s} A strategy (initial.code A) policy source.state source.slot
  let controller := (bank.right source).1
  treePlay (narrowedInducedTree monitor controller.labeledTree)
    (omegaOfList (past ++ [move]))

/-- Left-controller mirror. -/
noncomputable def profiledRawJointUnitLeftPolicyPlay
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (initial.code A))
    (bank : ProfiledRawJointUnitPolicyControllerBank A strategy initial policy)
    (source : ProfiledRawJointUnitLeftPolicyMacro A strategy (initial.code A)
      policy) (past : List (In₁ × In₂)) (move : In₁ × In₂) :
    Nat → RealizedBlockRound In₁ In₂
      (ProfiledRawJointUnitLeftReceiverOutput A strategy (initial.code A))
      Out₂ :=
  let monitor := profiledRawJointUnitLeftBlockMonitor.{u, v, x, y, s,
    max u v x y s} A strategy (initial.code A) policy source.state source.slot
  let controller := (bank.left source).1
  treePlay (narrowedInducedTree monitor controller.labeledTree)
    (omegaOfList (past ++ [move]))

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- At a real right-to-left close, the exact staged left macro carries the
minimum priority of the literal physical right-block prefix. -/
theorem profiledRawJointUnitRightPolicy_real_close_priority_eq_blockMin
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (initial.code A))
    (bank : ProfiledRawJointUnitPolicyControllerBank A strategy initial policy)
    (source : ProfiledRawJointUnitRightPolicyMacro A strategy (initial.code A)
      policy) (row : PairedEntryRow)
    (past : List (In₂ × In₁)) (move : In₂ × In₁) :
    ∃ target : ProfiledRawJointUnitLeftPolicyMacro A strategy (initial.code A)
        policy,
      (stepProfiledRawJointUnitRightPolicyReceiverFor A strategy initial policy
        bank source
          (profiledRawJointUnitRightPolicyFiniteStateAfter A strategy initial
            policy bank source past).1 row
          (profiledRawJointUnitRightPolicyFiniteStateAfter A strategy initial
            policy bank source past).2 move).2.2 = some target ∧
      profiledRawJointThreadRootPriority A (.inr target.slot) =
        A.priority
          (blockMinState A
            (pairedCodeStateForRow A row source.slot.1.1)
            (profiledRawJointUnitRightPhysicalPrefixRecords A row
              (omegaPrefix
                (profiledRawJointUnitRightPolicyPlay A strategy initial policy
                  bank source past move)
                past.length))) := by
  obtain ⟨target, hstage, hstate⟩ :=
    profiledRawJointUnitRightPolicy_real_close_stages_exact A strategy initial
      policy bank source row past move
  rw [profiledRawJointUnitRightPolicyFiniteStateAfter_eq A strategy initial
    policy bank source] at hstate
  let monitor := profiledRawJointUnitRightBlockMonitor.{u, v, x, y, s,
    max u v x y s} A strategy (initial.code A) policy source.state source.slot
  let controller := (bank.right source).1
  let env : Nat → In₂ × In₁ := omegaOfList (past ++ [move])
  let tree := narrowedInducedTree monitor controller.labeledTree
  let play := treePlay tree env
  have htree := narrowedInducedTree_winningTree_of_allThreadsWin monitor
    (bank.right source).2
  have hwin : monitor.WinsPlay play :=
    (monitor.lift_winningTree_iff tree).mp htree env
  obtain ⟨slot, hslot, hpriority⟩ :=
    exists_profiledRawJointUnitRightTargetThreadPriority_eq_blockMin_of_wins
      A strategy (initial.code A) policy source play hwin past.length row
  have hat := profiledRawJointUnitRightPolicy_treePlay_at_prefix A strategy
    initial policy bank source past move
  change play past.length = _ at hat
  have hplayTarget :
      ((play past.length).2.1.target row) =
        (((controller.labelOf (controller.controlAt (senderWord past))).2
          (narrowedControl monitor controller.labeledTree past) move).target
            row) := by
    rw [hat]
    rfl
  have htargetSlot :
      ((play past.length).2.1.target row).1.family.left () =
        some target.slot := by
    rw [hplayTarget, ← hstate]
    exact target.active_slot
  have hslotEq : slot = target.slot :=
    Option.some.inj (hslot.symm.trans htargetSlot)
  subst slot
  refine ⟨target, hstage, ?_⟩
  simpa [profiledRawJointUnitRightPolicyPlay, play, tree, env, monitor,
    controller] using hpriority

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- At a real left-to-right close, the exact staged right macro carries the
minimum priority of the literal physical left-block prefix. -/
theorem profiledRawJointUnitLeftPolicy_real_close_priority_eq_blockMin
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (initial.code A))
    (bank : ProfiledRawJointUnitPolicyControllerBank A strategy initial policy)
    (source : ProfiledRawJointUnitLeftPolicyMacro A strategy (initial.code A)
      policy) (row : PairedEntryRow)
    (past : List (In₁ × In₂)) (move : In₁ × In₂) :
    ∃ target : ProfiledRawJointUnitRightPolicyMacro A strategy (initial.code A)
        policy,
      (stepProfiledRawJointUnitLeftPolicyReceiverFor A strategy initial policy
        bank source
          (profiledRawJointUnitLeftPolicyFiniteStateAfter A strategy initial
            policy bank source past).1 row
          (profiledRawJointUnitLeftPolicyFiniteStateAfter A strategy initial
            policy bank source past).2 move).2.2 = some target ∧
      profiledRawJointThreadRootPriority A (.inl target.slot) =
        A.priority
          (blockMinState A
            (pairedCodeStateForRow A row source.slot.1.1)
            (profiledRawJointUnitLeftPhysicalPrefixRecords A row
              (omegaPrefix
                (profiledRawJointUnitLeftPolicyPlay A strategy initial policy
                  bank source past move)
                past.length))) := by
  obtain ⟨target, hstage, hstate⟩ :=
    profiledRawJointUnitLeftPolicy_real_close_stages_exact A strategy initial
      policy bank source row past move
  rw [profiledRawJointUnitLeftPolicyFiniteStateAfter_eq A strategy initial
    policy bank source] at hstate
  let monitor := profiledRawJointUnitLeftBlockMonitor.{u, v, x, y, s,
    max u v x y s} A strategy (initial.code A) policy source.state source.slot
  let controller := (bank.left source).1
  let env : Nat → In₁ × In₂ := omegaOfList (past ++ [move])
  let tree := narrowedInducedTree monitor controller.labeledTree
  let play := treePlay tree env
  have htree := narrowedInducedTree_winningTree_of_allThreadsWin monitor
    (bank.left source).2
  have hwin : monitor.WinsPlay play :=
    (monitor.lift_winningTree_iff tree).mp htree env
  obtain ⟨slot, hslot, hpriority⟩ :=
    exists_profiledRawJointUnitLeftTargetThreadPriority_eq_blockMin_of_wins
      A strategy (initial.code A) policy source play hwin past.length row
  have hat := profiledRawJointUnitLeftPolicy_treePlay_at_prefix A strategy
    initial policy bank source past move
  change play past.length = _ at hat
  have hplayTarget :
      ((play past.length).2.1.target row) =
        (((controller.labelOf (controller.controlAt (senderWord past))).2
          (narrowedControl monitor controller.labeledTree past) move).target
            row) := by
    rw [hat]
    rfl
  have htargetSlot :
      ((play past.length).2.1.target row).1.family.right () =
        some target.slot := by
    rw [hplayTarget, ← hstate]
    exact target.active_slot
  have hslotEq : slot = target.slot :=
    Option.some.inj (hslot.symm.trans htargetSlot)
  subst slot
  refine ⟨target, hstage, ?_⟩
  simpa [profiledRawJointUnitLeftPolicyPlay, play, tree, env, monitor,
    controller] using hpriority

end

end DetParityAutomaton

end DistributedSynthesis
