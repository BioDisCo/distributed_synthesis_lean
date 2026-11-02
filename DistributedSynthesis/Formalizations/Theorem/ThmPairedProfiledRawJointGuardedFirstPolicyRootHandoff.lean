/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedFirstBlockActivation
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledRawJointUnitRightPolicyHandoff

/-!
# Root-macro handoff below the exceptional raw-joint block

Selecting an ordinary policy for a literal child is not yet the operational
handoff: the alternating controller starts from a reachable right- or
left-policy macro.  This file packages the ordinary policy's literal root
state together with the live slot already carried by the child incidence
code.

The root state is `policy.run []`, so reachability is witnessed by the empty
word.  Its code is the literal child code by the policy acceptance equation;
therefore the active-slot proof is a rewrite of the exact raw-child slot
equation.  This makes the next alternating root definitionally the state
selected by the finite child-policy bank.
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

/-! ## A root macro for any bank child with a live slot -/

/-- Package a literal child whose left lane is live as the root macro of its
selected ordinary policy. -/
noncomputable def profiledRawJointLiteralChildLeftPolicyRoot
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (bank : ProfiledRawJointOneSidedLiteralChildPolicyBank A strategy initial)
    (child : ProfiledRawJointOneSidedLiteralChildCode A strategy initial)
    (slot : ProfiledRawLeftSlot A)
    (hslot : child.1.family.left () = some slot) :
    ProfiledRawJointUnitLeftPolicyMacro A strategy child.1 (bank child) := by
  let policy := bank child
  have hrootCode : (policy.run []).1 = child.1 := by
    have hroot := congrArg Prod.fst policy.accepts.1.1
    simpa [sourceFreeBeliefCodeParityRunAutomaton] using hroot
  exact {
    state := policy.run []
    reachable := ⟨[], rfl⟩
    slot := slot
    active_slot := by
      rw [hrootCode]
      exact hslot }

/-- Right-live mirror. -/
noncomputable def profiledRawJointLiteralChildRightPolicyRoot
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (bank : ProfiledRawJointOneSidedLiteralChildPolicyBank A strategy initial)
    (child : ProfiledRawJointOneSidedLiteralChildCode A strategy initial)
    (slot : ProfiledRawRightSlot A)
    (hslot : child.1.family.right () = some slot) :
    ProfiledRawJointUnitRightPolicyMacro A strategy child.1 (bank child) := by
  let policy := bank child
  have hrootCode : (policy.run []).1 = child.1 := by
    have hroot := congrArg Prod.fst policy.accepts.1.1
    simpa [sourceFreeBeliefCodeParityRunAutomaton] using hroot
  exact {
    state := policy.run []
    reachable := ⟨[], rfl⟩
    slot := slot
    active_slot := by
      rw [hrootCode]
      exact hslot }

omit [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂] in
@[simp] theorem profiledRawJointLiteralChildLeftPolicyRoot_state
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (bank : ProfiledRawJointOneSidedLiteralChildPolicyBank A strategy initial)
    (child : ProfiledRawJointOneSidedLiteralChildCode A strategy initial)
    (slot : ProfiledRawLeftSlot A)
    (hslot : child.1.family.left () = some slot) :
    (profiledRawJointLiteralChildLeftPolicyRoot A strategy initial bank child
      slot hslot).state = (bank child).run [] :=
  rfl

omit [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂] in
@[simp] theorem profiledRawJointLiteralChildRightPolicyRoot_state
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (bank : ProfiledRawJointOneSidedLiteralChildPolicyBank A strategy initial)
    (child : ProfiledRawJointOneSidedLiteralChildCode A strategy initial)
    (slot : ProfiledRawRightSlot A)
    (hslot : child.1.family.right () = some slot) :
    (profiledRawJointLiteralChildRightPolicyRoot A strategy initial bank child
      slot hslot).state = (bank child).run [] :=
  rfl

/-! ## Exact physical specializations -/

/-- A concrete exceptional right close initializes the ordinary left-policy
macro at the exact raw child and exact physical child slot. -/
noncomputable def profiledRawJointGuardedFirstRightChildRootMacro
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (RootPred : ProfiledRawJointLambdaFamilyMove A (I := Unit) → Prop)
    (package : ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      initial RootPred)
    (source : ProfiledRawRightSlot A)
    (activation : ProfiledRawJointGuardedFirstRightBlockActivation A strategy
      initial RootPred package source)
    (row : PairedEntryRow) (past : List (In₂ × In₁))
    (input : In₂ × In₁) :
    let selected := profiledRawJointRootPinnedSelectedSource A strategy
      initial RootPred package
    let bank := profiledRawJointRootPinnedLiteralChildPolicyBank A strategy
      hwin initial RootPred package
    let child := profiledRawJointGuardedFirstRightTarget A strategy initial
      RootPred package row past input
    ProfiledRawJointUnitLeftPolicyMacro A strategy child.1 (bank child) := by
  dsimp only
  exact profiledRawJointLiteralChildLeftPolicyRoot A strategy
    (profiledRawJointRootPinnedSelectedSource A strategy initial RootPred
      package)
    (profiledRawJointRootPinnedLiteralChildPolicyBank A strategy hwin initial
      RootPred package)
    (profiledRawJointGuardedFirstRightTarget A strategy initial RootPred
      package row past input)
    (profiledRawRightChildSlot A source activation.lambda row past input)
    (activation.target_active_slot row past input)

/-- A concrete exceptional left close initializes the ordinary right-policy
macro at the exact raw child. -/
noncomputable def profiledRawJointGuardedFirstLeftChildRootMacro
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (RootPred : ProfiledRawJointLambdaFamilyMove A (I := Unit) → Prop)
    (package : ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      initial RootPred)
    (source : ProfiledRawLeftSlot A)
    (activation : ProfiledRawJointGuardedFirstLeftBlockActivation A strategy
      initial RootPred package source)
    (row : PairedEntryRow) (past : List (In₁ × In₂))
    (input : In₁ × In₂) :
    let selected := profiledRawJointRootPinnedSelectedSource A strategy
      initial RootPred package
    let bank := profiledRawJointRootPinnedLiteralChildPolicyBank A strategy
      hwin initial RootPred package
    let child := profiledRawJointGuardedFirstLeftTarget A strategy initial
      RootPred package row past input
    ProfiledRawJointUnitRightPolicyMacro A strategy child.1 (bank child) := by
  dsimp only
  exact profiledRawJointLiteralChildRightPolicyRoot A strategy
    (profiledRawJointRootPinnedSelectedSource A strategy initial RootPred
      package)
    (profiledRawJointRootPinnedLiteralChildPolicyBank A strategy hwin initial
      RootPred package)
    (profiledRawJointGuardedFirstLeftTarget A strategy initial RootPred package
      row past input)
    (profiledRawLeftChildSlot A source activation.lambda row past input)
    (activation.target_active_slot row past input)

omit [DecidableEq In₁] [DecidableEq In₂] [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem profiledRawJointGuardedFirstRightChildRootMacro_state
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (RootPred : ProfiledRawJointLambdaFamilyMove A (I := Unit) → Prop)
    (package : ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      initial RootPred)
    (source : ProfiledRawRightSlot A)
    (activation : ProfiledRawJointGuardedFirstRightBlockActivation A strategy
      initial RootPred package source)
    (row : PairedEntryRow) (past : List (In₂ × In₁))
    (input : In₂ × In₁) :
    (profiledRawJointGuardedFirstRightChildRootMacro A strategy hwin initial
      RootPred package source activation row past input).state =
      (profiledRawJointRootPinnedLiteralChildPolicyBank A strategy hwin initial
        RootPred package
        (profiledRawJointGuardedFirstRightTarget A strategy initial RootPred
          package row past input)).run [] :=
  rfl

omit [DecidableEq In₁] [DecidableEq In₂] [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem profiledRawJointGuardedFirstLeftChildRootMacro_state
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (RootPred : ProfiledRawJointLambdaFamilyMove A (I := Unit) → Prop)
    (package : ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      initial RootPred)
    (source : ProfiledRawLeftSlot A)
    (activation : ProfiledRawJointGuardedFirstLeftBlockActivation A strategy
      initial RootPred package source)
    (row : PairedEntryRow) (past : List (In₁ × In₂))
    (input : In₁ × In₂) :
    (profiledRawJointGuardedFirstLeftChildRootMacro A strategy hwin initial
      RootPred package source activation row past input).state =
      (profiledRawJointRootPinnedLiteralChildPolicyBank A strategy hwin initial
        RootPred package
        (profiledRawJointGuardedFirstLeftTarget A strategy initial RootPred
          package row past input)).run [] :=
  rfl

end


end DetParityAutomaton

end DistributedSynthesis
