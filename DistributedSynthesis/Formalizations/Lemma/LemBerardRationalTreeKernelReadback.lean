/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemBerardDirectRationalTreeReadback
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedHybridCombinedReadbackBridge

/-!
# Reading an occurrence-sensitive rational tree through a local kernel

The direct Bérard route and the guarded-common route meet at a particularly
small interface.  The Bérard object is a finite transition-rational global
action tree.  The guarded object is already an honestly local, leader-free
kernel.  It is unnecessary to reproduce the five physical acceptance proofs
when the two objects emit the same outputs at every actual occurrence:
pointwise output agreement gives equality of their complete physical words,
and universal winningness of the tree fills every proof-side graph regime.

`BerardTreeOutputAgreement` is deliberately only a proof relation.  Neither
local process receives the tree control, graph, orientation, active side, or
strict-leader bit.  The executable object remains the existing leader-free
kernel.  Thus the first concrete model fact needed by this adapter is a
literal occurrence-by-occurrence output alignment, not a new finite-summary
or post-rationalization congruence.
-/

namespace DistributedSynthesis

universe u v w x y s c i₁ i₂ e₁ e₂ k ro lr rr lo

namespace ProfiledRawJointLeaderFreeKernel

variable
  {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
  {InitialOne : Type i₁} {InitialTwo : Type i₂}
  {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
  {ChildCode : Type k}
  {RightOwner : ChildCode → Type ro}
  {LeftReceiver : ChildCode → Type lr}
  {RightReceiver : ChildCode → Type rr}
  {LeftOwner : ChildCode → Type lo}

variable (kernel : ProfiledRawJointLeaderFreeKernel In₁ In₂ Out₁ Out₂
  InitialOne InitialTwo ExceptionalOne ExceptionalTwo ChildCode RightOwner
  LeftReceiver RightReceiver LeftOwner)

variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [Fintype InitialOne] [Fintype InitialTwo]
variable [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
variable [Fintype ChildCode]
variable [∀ key, Fintype (RightOwner key)]
variable [∀ key, Fintype (LeftReceiver key)]
variable [∀ key, Fintype (RightReceiver key)]
variable [∀ key, Fintype (LeftOwner key)]

variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

/--
The local kernel and rational tree choose the same output pair at every
physical occurrence.  Inputs and the graph need not be restated: both words
copy those components from the same environment round.
-/
def BerardTreeOutputAgreement
    (tree : TransitionRationalTree.{max u v, max u v x y, c}
      (EnvironmentRound In₁ In₂)
      (DetParityAutomaton.ExactViewGlobalActionTable
        (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))) :
    Prop :=
  ∀ (env : EnvironmentSequence In₁ In₂) (n : Nat),
    (kernel.globalOutputOne
        (kernel.globalMachine.globalStateTrace env (n + 1)),
      kernel.globalOutputTwo
        (kernel.globalMachine.globalStateTrace env (n + 1))) =
      tree.labeledTree (branchNode env n) (env n)

omit [Fintype In₁] [Fintype In₂] in
/-- Pointwise output alignment identifies the complete physical omega words. -/
theorem globalMachineTraceWord_eq_berardTreeWord
    (tree : TransitionRationalTree.{max u v, max u v x y, c}
      (EnvironmentRound In₁ In₂)
      (DetParityAutomaton.ExactViewGlobalActionTable
        (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)))
    (hagrees : kernel.BerardTreeOutputAgreement tree)
    (env : EnvironmentSequence In₁ In₂) :
    kernel.globalMachine.globalMachineTraceWord
        kernel.globalOutputOne kernel.globalOutputTwo env =
      DetParityAutomaton.exactViewGlobalTreeWord tree.labeledTree env := by
  funext n
  have houtputs := hagrees env n
  have hone := congrArg Prod.fst houtputs
  have htwo := congrArg Prod.snd houtputs
  change kernel.globalOutputOne
      (kernel.globalMachine.globalStateTrace env (n + 1)) =
    (tree.labeledTree (branchNode env n) (env n)).1 at hone
  change kernel.globalOutputTwo
      (kernel.globalMachine.globalStateTrace env (n + 1)) =
    (tree.labeledTree (branchNode env n) (env n)).2 at htwo
  unfold FiniteGlobalRoundMachine.globalMachineTraceWord
    DetParityAutomaton.exactViewGlobalTreeWord
    DetParityAutomaton.exactViewGlobalTreeRound
  rw [hone, htwo]

omit [Fintype In₁] [Fintype In₂] in
/-- Universal winningness of the aligned rational tree is universal
acceptance of the already-local kernel's actual trace. -/
theorem globalMachine_accepts_of_berardTree
    (tree : TransitionRationalTree.{max u v, max u v x y, c}
      (EnvironmentRound In₁ In₂)
      (DetParityAutomaton.ExactViewGlobalActionTable
        (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)))
    (hwins : DetParityAutomaton.ExactViewGlobalTreeWinning A tree.labeledTree)
    (hagrees : kernel.BerardTreeOutputAgreement tree) :
    ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts
        (kernel.globalMachine.globalMachineTraceWord
          kernel.globalOutputOne kernel.globalOutputTwo env) := by
  intro env
  rw [kernel.globalMachineTraceWord_eq_berardTreeWord tree hagrees env]
  exact hwins env

/-- Direct acceptance fills all five carrier-facing regimes.  The graph
hypotheses are proof-only and are intentionally unused. -/
def allEnvironmentDetailedRegimeAcceptance_of_berardTree
    (tree : TransitionRationalTree.{max u v, max u v x y, c}
      (EnvironmentRound In₁ In₂)
      (DetParityAutomaton.ExactViewGlobalActionTable
        (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)))
    (hwins : DetParityAutomaton.ExactViewGlobalTreeWinning A tree.labeledTree)
    (hagrees : kernel.BerardTreeOutputAgreement tree) :
    kernel.AllEnvironmentDetailedRegimeAcceptance A := by
  intro env
  let haccepts : A.Accepts
      (kernel.globalMachine.globalMachineTraceWord
        kernel.globalOutputOne kernel.globalOutputTwo env) :=
    kernel.globalMachine_accepts_of_berardTree A tree hwins hagrees env
  exact {
    eventuallyCommon := fun _ ↦ haccepts
    recurrentBothWithStrict := fun _ _ ↦ haccepts
    alternating := fun _ ↦ haccepts
    strictRight := fun _ ↦ haccepts
    strictLeft := fun _ ↦ haccepts }

omit [Fintype In₁] [Fintype In₂] in
/-- Reusable positive endpoint: an occurrence-aligned winning rational tree
closes `ReadbackUpgrade` for any already-local leader-free kernel. -/
theorem summaryAutomaton_readbackUpgrade_of_berardTree
    (tree : TransitionRationalTree.{max u v, max u v x y, c}
      (EnvironmentRound In₁ In₂)
      (DetParityAutomaton.ExactViewGlobalActionTable
        (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)))
    (hwins : DetParityAutomaton.ExactViewGlobalTreeWinning A tree.labeledTree)
    (hagrees : kernel.BerardTreeOutputAgreement tree) :
    kernel.summaryAutomaton.ReadbackUpgrade A :=
  kernel.summaryAutomaton_readbackUpgrade_of_detailedRegimeAcceptance A
    (kernel.allEnvironmentDetailedRegimeAcceptance_of_berardTree A tree hwins
      hagrees)

end ProfiledRawJointLeaderFreeKernel

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
  (initialBank : ProfiledRawJointInitialControllerBank A strategy)

variable {InitialOne : Type i₁} {InitialTwo : Type i₂}
  {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
variable [Fintype InitialOne] [Fintype InitialTwo]
  [Fintype ExceptionalOne] [Fintype ExceptionalTwo]

/--
Construct the current combined readback completion from an aligned Bérard
rational tree.  This replaces all five separate acceptance fields; it does
not replace or strengthen the executable exceptional-front adapter.
-/
noncomputable def
    ProfiledRawJointGuardedHybridCombinedReadbackCompletion.ofBerardTree
    (adapter : ProfiledRawJointGuardedHybridCombinedExceptionalAdapter A
      strategy hwin initialBank InitialOne InitialTwo ExceptionalOne
      ExceptionalTwo)
    (tree : TransitionRationalTree.{max u v, max u v x y, c}
      (EnvironmentRound In₁ In₂)
      (ExactViewGlobalActionTable
        (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)))
    (hwins : ExactViewGlobalTreeWinning A tree.labeledTree)
    (hagrees :
      (profiledRawJointGuardedHybridCombinedLeaderFreeKernel A strategy hwin
        initialBank adapter).BerardTreeOutputAgreement tree) :
    ProfiledRawJointGuardedHybridCombinedReadbackCompletion A strategy hwin
      initialBank InitialOne InitialTwo ExceptionalOne ExceptionalTwo where
  adapter := adapter
  detailedAcceptance :=
    (profiledRawJointGuardedHybridCombinedLeaderFreeKernel A strategy hwin
      initialBank adapter
      ).allEnvironmentDetailedRegimeAcceptance_of_berardTree A tree hwins
        hagrees

/-- Direct outer-existential endpoint for the combined route from the same
occurrence-aligned rational tree. -/
theorem exists_profiledRawJointGuardedHybridCombined_readbackUpgrade_of_berardTree
    (adapter : ProfiledRawJointGuardedHybridCombinedExceptionalAdapter A
      strategy hwin initialBank InitialOne InitialTwo ExceptionalOne
      ExceptionalTwo)
    (tree : TransitionRationalTree.{max u v, max u v x y, c}
      (EnvironmentRound In₁ In₂)
      (ExactViewGlobalActionTable
        (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)))
    (hwins : ExactViewGlobalTreeWinning A tree.labeledTree)
    (hagrees :
      (profiledRawJointGuardedHybridCombinedLeaderFreeKernel A strategy hwin
        initialBank adapter).BerardTreeOutputAgreement tree) :
    ∃ M : LocalSummaryAutomaton.{u, v,
        max s u v x y i₁ i₂ e₁ e₂} In₁ In₂,
      M.ReadbackUpgrade (Out₁ := Out₁) (Out₂ := Out₂) A := by
  exact
    (ProfiledRawJointGuardedHybridCombinedReadbackCompletion.ofBerardTree
      A strategy hwin initialBank adapter tree hwins hagrees
      ).exists_readbackUpgrade A strategy hwin initialBank

end

end DetParityAutomaton

end DistributedSynthesis
