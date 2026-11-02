/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCombinedFreshPhaseActivatedInitialBank
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonTwoRoundFront

/-!
# Honest two-round entry to the phase-activated bank

This is the synchronization boundary omitted by the standalone default-root
controller.  The existing local front emits the original strategy's literal
outputs during two simultaneous seed rounds.  At the second receive, each
endpoint reconstructs the same physical seed and enters the phase-activated
member indexed by precisely that seed.
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
  (controllers : ProfiledRawJointRootCompatibleInitialControllers A strategy)

namespace ProfiledRawJointGuardedCommonDecoratedPolicyPackage

private abbrev OneSeed :=
  ProfiledRawJointGuardedCommonTwoRoundSeedOne A strategy hwin controllers

private abbrev TwoSeed :=
  ProfiledRawJointGuardedCommonTwoRoundSeedTwo A strategy hwin controllers

private abbrev BankOne :=
  ProfiledRawJointGuardedCommonLiteralPhaseActivatedBankOneControl A strategy
    hwin

private abbrev BankTwo :=
  ProfiledRawJointGuardedCommonLiteralPhaseActivatedBankTwoControl A strategy
    hwin

/-! ## Second-round local activation maps -/

/-- Process one emits the literal second common output and enters the member
selected by its retained first pair and the current receive. -/
noncomputable def literalCombinedFreshPhaseActivatedTwoRoundSecondRecvOne
    (state : OneSeed A strategy hwin controllers)
    (own : In₁) (delivered : In₂) : Out₁ × BankOne A strategy hwin :=
  let seed := (state.common.1, (own, delivered))
  (profiledRawJointInitialCommonBothOutputOneOfReceive A strategy
      state.common.1 own delivered,
    literalCombinedFreshPhaseActivatedBankActivateOne A strategy hwin seed)

/-- Process-two mirror. -/
noncomputable def literalCombinedFreshPhaseActivatedTwoRoundSecondRecvTwo
    (state : TwoSeed A strategy hwin controllers)
    (own : In₂) (delivered : In₁) : Out₂ × BankTwo A strategy hwin :=
  let seed := (state.common.1, (delivered, own))
  (profiledRawJointInitialCommonBothOutputTwoOfReceive A strategy
      state.common.1 own delivered,
    literalCombinedFreshPhaseActivatedBankActivateTwo A strategy hwin seed)

/-! ## Exact physical and dependent-package agreement -/

/-- On two actual simultaneous rounds, the output pair is the original
strategy's literal second-round output. -/
@[simp] theorem
    literalCombinedFreshPhaseActivatedTwoRoundSecondRecv_outputs_eq_literalBoth
    (first current : In₁ × In₂) :
    ((literalCombinedFreshPhaseActivatedTwoRoundSecondRecvOne A strategy hwin
        controllers
        (profiledRawJointGuardedCommonTwoRoundFirstRecvOne A strategy hwin
          controllers () first.1 first.2).2 current.1 current.2).1,
      (literalCombinedFreshPhaseActivatedTwoRoundSecondRecvTwo A strategy hwin
        controllers
        (profiledRawJointGuardedCommonTwoRoundFirstRecvTwo A strategy hwin
          controllers () first.2 first.1).2 current.2 current.1).1) =
      profiledRawJointInitialCommonBothOutput A strategy (first, current) :=
  rfl

/-- Expanded form identifying that output with `nextRound` on the literal
history selected by the first input pair. -/
theorem
    literalCombinedFreshPhaseActivatedTwoRoundSecondRecv_outputs_eq_nextRound
    (first current : In₁ × In₂) :
    ((literalCombinedFreshPhaseActivatedTwoRoundSecondRecvOne A strategy hwin
        controllers
        (profiledRawJointGuardedCommonTwoRoundFirstRecvOne A strategy hwin
          controllers () first.1 first.2).2 current.1 current.2).1,
      (literalCombinedFreshPhaseActivatedTwoRoundSecondRecvTwo A strategy hwin
        controllers
        (profiledRawJointGuardedCommonTwoRoundFirstRecvTwo A strategy hwin
          controllers () first.2 first.1).2 current.2 current.1).1) =
      let world := profiledRawJointInitialCommonBothWorld A strategy
        (first, current)
      let round := nextRound strategy (world.procOne A).bothHistory
        ⟨current.1, current.2, Graph.both⟩
      (round.outputOne, round.outputTwo) :=
  rfl

@[simp] theorem
    literalCombinedFreshPhaseActivatedTwoRoundSecondRecvOne_installs_seed
    (first current : In₁ × In₂) :
    (literalCombinedFreshPhaseActivatedTwoRoundSecondRecvOne A strategy hwin
      controllers
      (profiledRawJointGuardedCommonTwoRoundFirstRecvOne A strategy hwin
        controllers () first.1 first.2).2 current.1 current.2).2.1 =
      (first, current) :=
  rfl

@[simp] theorem
    literalCombinedFreshPhaseActivatedTwoRoundSecondRecvTwo_installs_seed
    (first current : In₁ × In₂) :
    (literalCombinedFreshPhaseActivatedTwoRoundSecondRecvTwo A strategy hwin
      controllers
      (profiledRawJointGuardedCommonTwoRoundFirstRecvTwo A strategy hwin
        controllers () first.2 first.1).2 current.2 current.1).2.1 =
      (first, current) :=
  rfl

/-- The two locally reconstructed dependent controls select the same package
member. -/
@[simp] theorem
    literalCombinedFreshPhaseActivatedTwoRoundSecondRecv_seeds_agree
    (first current : In₁ × In₂) :
    (literalCombinedFreshPhaseActivatedTwoRoundSecondRecvOne A strategy hwin
      controllers
      (profiledRawJointGuardedCommonTwoRoundFirstRecvOne A strategy hwin
        controllers () first.1 first.2).2 current.1 current.2).2.1 =
    (literalCombinedFreshPhaseActivatedTwoRoundSecondRecvTwo A strategy hwin
      controllers
      (profiledRawJointGuardedCommonTwoRoundFirstRecvTwo A strategy hwin
        controllers () first.2 first.1).2 current.2 current.1).2.1 :=
  rfl

/-- The installed package is the exact guarded semantic occurrence generated
by the two physical input pairs. -/
theorem literalCombinedFreshPhaseActivatedTwoRound_installed_point
    (first current : In₁ × In₂) :
    literalCombinedFreshPhaseActivatedPointOfSeed A strategy
        (literalCombinedFreshPhaseActivatedTwoRoundSecondRecvOne A strategy
          hwin controllers
          (profiledRawJointGuardedCommonTwoRoundFirstRecvOne A strategy hwin
            controllers () first.1 first.2).2 current.1 current.2).2.1 =
      profiledRawJointGuardedInitialCommonPoint A strategy (first, current) :=
  rfl

/-! ## Initial checker synchronization -/

omit [DecidableEq In₁] [DecidableEq In₂] [Inhabited In₁] [Inhabited Out₁] [Inhabited Out₂]
    [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂] in
/-- If the physical word begins with the two literal simultaneous seed
records, the actual DPA run after those records is exactly the `.both` entry
state stored by the selected phase-activated package.  This is the honest
base case for later table-state synchronization; no finite prefix is
discarded and no checker is restarted. -/
theorem literalCombinedFreshPhaseActivatedTwoRound_run_two_eq_installedState
    (first current : In₁ × In₂)
    (word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (hfirst : word 0 =
      nextRound strategy [] ⟨first.1, first.2, Graph.both⟩)
    (hsecond : word 1 =
      let firstRound :=
        nextRound strategy [] ⟨first.1, first.2, Graph.both⟩
      nextRound strategy [firstRound]
        ⟨current.1, current.2, Graph.both⟩) :
    A.run word 2 =
      pairedCodeStateForRow A .both
        (((literalCombinedFreshPhaseActivatedPointOfSeed A strategy
          (first, current)).world A strategy).procOneSlot A).1.1 := by
  rw [show 2 = 1 + 1 by omega, A.run_succ, A.run_succ, hfirst, hsecond]
  simp [literalCombinedFreshPhaseActivatedPointOfSeed,
    profiledRawJointGuardedInitialCommonPoint,
    ProfiledRawJointGuardedCommonSemanticPoint.world,
    profiledRawJointInitialCommonBaseWorld,
    profiledRawJointCommonWorldAfterBoth,
    profiledRawRightCommonBaseWorld,
    ProfiledRawJointCommonBaseWorld.procOneSlot,
    ProfiledRawJointCommonBaseWorld.procOneMember,
    ProfiledRawJointCommonBaseWorld.procOne,
    profiledRawRightSlotOfSemanticPair, profiledRawProcOneRowHistory,
    procOneFreshPair, ProcOnePairedEntryRep.code, pairedCodeStateForRow,
    entryState, History.append]

end ProfiledRawJointGuardedCommonDecoratedPolicyPackage

end

end DetParityAutomaton

end DistributedSynthesis
