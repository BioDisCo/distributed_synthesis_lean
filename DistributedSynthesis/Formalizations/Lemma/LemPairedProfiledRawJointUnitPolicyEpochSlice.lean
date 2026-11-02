/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledRawJointUnitPolicyPhysicalPriority
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenAutomaticRecutEpochCoupling

/-!
# Literal raw-joint controller blocks at physical epoch cuts

The local raw-joint controller already proves that the macro staged at a
checked close carries the minimum priority of its literal emitted prefix.
This file connects that pointwise fact to the generic physical cut sequence.

The only hypotheses below are the two transparent facts an operational run
must establish: the DPA state at the cut is the row-selected source state, and
the finite physical slice is literally the controller prefix.  No strategy
word, replay, or independently accepted fragment occurs in the statement.
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

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- A real right-to-left controller close, aligned with one physical cut
slice, stages an exact left macro whose root priority is the cut minimum. -/
theorem profiledRawJointUnitRightPolicy_real_close_cutBlockMin_eq_priority
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (initial.code A))
    (bank : ProfiledRawJointUnitPolicyControllerBank A strategy initial policy)
    (source : ProfiledRawJointUnitRightPolicyMacro A strategy (initial.code A)
      policy) (row : PairedEntryRow)
    (past : List (In₂ × In₁)) (move : In₂ × In₁)
    (word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (start : Nat) (cuts : Nat → Nat) (k : Nat)
    (hstate : A.run word (start + cuts k) =
      pairedCodeStateForRow A row source.slot.1.1)
    (hlength :
      (profiledRawJointUnitRightPhysicalPrefixRecords A row
          (omegaPrefix
            (profiledRawJointUnitRightPolicyPlay A strategy initial policy
              bank source past move)
            past.length)).length =
        cuts (k + 1) - cuts k - 1)
    (hslice :
      omegaPrefix (OmegaWord.drop word (start + cuts k))
          (profiledRawJointUnitRightPhysicalPrefixRecords A row
            (omegaPrefix
              (profiledRawJointUnitRightPolicyPlay A strategy initial policy
                bank source past move)
              past.length)).length =
        profiledRawJointUnitRightPhysicalPrefixRecords A row
          (omegaPrefix
            (profiledRawJointUnitRightPolicyPlay A strategy initial policy bank
              source past move)
            past.length)) :
    ∃ target : ProfiledRawJointUnitLeftPolicyMacro A strategy (initial.code A)
        policy,
      (stepProfiledRawJointUnitRightPolicyReceiverFor A strategy initial policy
        bank source
          (profiledRawJointUnitRightPolicyFiniteStateAfter A strategy initial
            policy bank source past).1 row
          (profiledRawJointUnitRightPolicyFiniteStateAfter A strategy initial
            policy bank source past).2 move).2.2 = some target ∧
      cutBlockMin (fun n ↦ A.priority (A.run word (start + n))) cuts k =
        profiledRawJointThreadRootPriority A (.inr target.slot) := by
  obtain ⟨target, hstage, hpriority⟩ :=
    profiledRawJointUnitRightPolicy_real_close_priority_eq_blockMin A strategy
      initial policy bank source row past move
  refine ⟨target, hstage, ?_⟩
  have hcut := cutBlockMin_eq_priority_blockMinState_of_slice_alignment A word
    start cuts k (pairedCodeStateForRow A row source.slot.1.1)
      (profiledRawJointUnitRightPhysicalPrefixRecords A row
        (omegaPrefix
          (profiledRawJointUnitRightPolicyPlay A strategy initial policy bank
            source past move)
          past.length)) hstate hlength hslice
  exact hcut.trans hpriority.symm

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Left-to-right mirror. -/
theorem profiledRawJointUnitLeftPolicy_real_close_cutBlockMin_eq_priority
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (initial.code A))
    (bank : ProfiledRawJointUnitPolicyControllerBank A strategy initial policy)
    (source : ProfiledRawJointUnitLeftPolicyMacro A strategy (initial.code A)
      policy) (row : PairedEntryRow)
    (past : List (In₁ × In₂)) (move : In₁ × In₂)
    (word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (start : Nat) (cuts : Nat → Nat) (k : Nat)
    (hstate : A.run word (start + cuts k) =
      pairedCodeStateForRow A row source.slot.1.1)
    (hlength :
      (profiledRawJointUnitLeftPhysicalPrefixRecords A row
          (omegaPrefix
            (profiledRawJointUnitLeftPolicyPlay A strategy initial policy bank
              source past move)
            past.length)).length =
        cuts (k + 1) - cuts k - 1)
    (hslice :
      omegaPrefix (OmegaWord.drop word (start + cuts k))
          (profiledRawJointUnitLeftPhysicalPrefixRecords A row
            (omegaPrefix
              (profiledRawJointUnitLeftPolicyPlay A strategy initial policy
                bank source past move)
              past.length)).length =
        profiledRawJointUnitLeftPhysicalPrefixRecords A row
          (omegaPrefix
            (profiledRawJointUnitLeftPolicyPlay A strategy initial policy bank
              source past move)
            past.length)) :
    ∃ target : ProfiledRawJointUnitRightPolicyMacro A strategy (initial.code A)
        policy,
      (stepProfiledRawJointUnitLeftPolicyReceiverFor A strategy initial policy
        bank source
          (profiledRawJointUnitLeftPolicyFiniteStateAfter A strategy initial
            policy bank source past).1 row
          (profiledRawJointUnitLeftPolicyFiniteStateAfter A strategy initial
            policy bank source past).2 move).2.2 = some target ∧
      cutBlockMin (fun n ↦ A.priority (A.run word (start + n))) cuts k =
        profiledRawJointThreadRootPriority A (.inl target.slot) := by
  obtain ⟨target, hstage, hpriority⟩ :=
    profiledRawJointUnitLeftPolicy_real_close_priority_eq_blockMin A strategy
      initial policy bank source row past move
  refine ⟨target, hstage, ?_⟩
  have hcut := cutBlockMin_eq_priority_blockMinState_of_slice_alignment A word
    start cuts k (pairedCodeStateForRow A row source.slot.1.1)
      (profiledRawJointUnitLeftPhysicalPrefixRecords A row
        (omegaPrefix
          (profiledRawJointUnitLeftPolicyPlay A strategy initial policy bank
            source past move)
          past.length)) hstate hlength hslice
  exact hcut.trans hpriority.symm

end

end DetParityAutomaton

end DistributedSynthesis
