/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridMegaLinkedDeferredTailAdapter
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridForeverCommonAcceptance

/-!
# Forever-common trace of the closed mega-linked front

The closed mega-linked adapter has an honest all-simultaneous path.  The root
round creates the two initial ambiguity shadows; the next simultaneous round
enters the stable generic shadow pair; every later simultaneous round refreshes
that pair.  This file identifies the resulting physical word with the already
verified forever-common word.
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
  (initialBank : ProfiledRawJointInitialControllerBank A strategy)

private abbrev RetainedTag :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A strategy
    hwin

private abbrev MegaPhysicalController (kernelTag : RetainedTag A strategy hwin) :=
  MegaLinkedUnconditionalPhysicalController A strategy hwin controllers
    initialBank kernelTag

/-- Input pairs viewed as an all-simultaneous environment. -/
def profiledRawJointHybridMegaLinkedAllBothEnvironment
    (inputs : Nat → In₁ × In₂) : EnvironmentSequence In₁ In₂ :=
  fun n ↦ bothEnvironment (inputs n)

@[simp] theorem profiledRawJointHybridMegaLinkedAllBothEnvironment_apply
    (inputs : Nat → In₁ × In₂) (n : Nat) :
    profiledRawJointHybridMegaLinkedAllBothEnvironment inputs n =
      bothEnvironment (inputs n) :=
  rfl

/-- Stable process-one shadow after physical round `n + 1`. -/
noncomputable def profiledRawJointHybridMegaLinkedForeverCommonShadowOne
    (inputs : Nat → In₁ × In₂) (n : Nat) :=
  (profiledRawJointHybridCommonToOneShadow A strategy hwin
    (profiledRawJointHybridForeverCommonControlTrace A strategy hwin inputs n)
      (inputs (n + 1)).1 (inputs (n + 1)).2).2

/-- Process-two mirror. -/
noncomputable def profiledRawJointHybridMegaLinkedForeverCommonShadowTwo
    (inputs : Nat → In₁ × In₂) (n : Nat) :=
  (profiledRawJointHybridCommonToTwoShadow A strategy hwin
    (profiledRawJointHybridForeverCommonControlTrace A strategy hwin inputs n)
      (inputs (n + 1)).2 (inputs (n + 1)).1).2

/-- The corresponding complete mega physical state. -/
noncomputable def profiledRawJointHybridMegaLinkedForeverCommonGlobalState
    (kernelTag : RetainedTag A strategy hwin)
    (inputs : Nat → In₁ × In₂) (n : Nat) :
    (MegaPhysicalController A strategy hwin controllers initialBank kernelTag
      ).OneControl ×
      (MegaPhysicalController A strategy hwin controllers initialBank kernelTag
        ).TwoControl :=
  let nextOne := profiledRawJointHybridCommonToOneShadow A strategy hwin
    (profiledRawJointHybridForeverCommonControlTrace A strategy hwin inputs n)
      (inputs (n + 1)).1 (inputs (n + 1)).2
  let nextTwo := profiledRawJointHybridCommonToTwoShadow A strategy hwin
    (profiledRawJointHybridForeverCommonControlTrace A strategy hwin inputs n)
      (inputs (n + 1)).2 (inputs (n + 1)).1
  ((profiledRawJointHybridMegaLinkedLiftOldOne A strategy hwin controllers
      initialBank
        (profiledRawJointHybridMegaLinkedFrontOneOfShadow A strategy hwin
          controllers initialBank nextOne.2), nextOne.1),
    (profiledRawJointHybridMegaLinkedLiftOldTwo A strategy hwin controllers
      initialBank
        (profiledRawJointHybridMegaLinkedFrontTwoOfShadow A strategy hwin
          controllers initialBank nextTwo.2), nextTwo.1))

/- At every time `n + 2`, the concrete all-`.both` run is the stable shadow
state generated from common-policy control `n`. -/
set_option maxHeartbeats 2000000 in
theorem
    profiledRawJointHybridMegaLinkedUnconditional_allBoth_globalStateTrace
    (kernelTag : RetainedTag A strategy hwin)
    (inputs : Nat → In₁ × In₂) : ∀ n : Nat,
    (MegaPhysicalController A strategy hwin controllers initialBank kernelTag
      ).globalMachine.globalStateTrace
        (profiledRawJointHybridMegaLinkedAllBothEnvironment inputs) (n + 2) =
      profiledRawJointHybridMegaLinkedForeverCommonGlobalState A strategy hwin
        controllers initialBank kernelTag inputs n := by
  unfold MegaPhysicalController
  intro n
  induction n with
  | zero =>
      rw [show 0 + 2 = (0 + 1) + 1 by omega,
        FiniteGlobalRoundMachine.globalStateTrace_succ,
        FiniteGlobalRoundMachine.globalStateTrace_succ]
      simp only [FiniteGlobalRoundMachine.globalStateTrace_zero,
        profiledRawJointHybridMegaLinkedAllBothEnvironment_apply,
        bothEnvironment,
        FinitePairedPhysicalController.globalMachine_step,
        FinitePairedPhysicalController.globalMachine_initial]
      rw [profiledRawJointHybridMegaLinkedUnconditional_root_both A strategy
        hwin controllers initialBank kernelTag]
      unfold profiledRawJointHybridMegaLinkedForeverCommonGlobalState
      dsimp only
      simpa only [profiledRawJointHybridForeverCommonControlTrace_zero,
        profiledRawJointHybridInitialRootRecvOne_common,
        profiledRawJointHybridInitialRootRecvTwo_common, Nat.zero_add] using
        (profiledRawJointHybridMegaLinkedUnconditional_initialShadows_both A
          strategy hwin controllers initialBank kernelTag
          (profiledRawJointHybridInitialRootRecvOne A strategy hwin controllers
            ((inputs 0).1, (inputs 0).2)).2
          (profiledRawJointHybridInitialRootRecvTwo A strategy hwin controllers
            ((inputs 0).1, (inputs 0).2)).2
          (profiledRawJointHybridInitialRootRecvOne A strategy hwin controllers
            ((inputs 0).1, (inputs 0).2)).1
          (profiledRawJointHybridInitialRootRecvTwo A strategy hwin controllers
            ((inputs 0).1, (inputs 0).2)).1 (inputs 1).1 (inputs 1).2)
  | succ n ih =>
      rw [show n + 1 + 2 = (n + 2) + 1 by omega,
        FiniteGlobalRoundMachine.globalStateTrace_succ, ih]
      simp only [profiledRawJointHybridMegaLinkedAllBothEnvironment_apply,
        bothEnvironment,
        FinitePairedPhysicalController.globalMachine_step]
      unfold profiledRawJointHybridMegaLinkedForeverCommonGlobalState
      dsimp only
      rw [profiledRawJointHybridMegaLinkedUnconditional_shadows_both A strategy
        hwin controllers initialBank kernelTag
        (profiledRawJointHybridCommonToOneShadow A strategy hwin
          (profiledRawJointHybridForeverCommonControlTrace A strategy hwin
            inputs n) (inputs (n + 1)).1 (inputs (n + 1)).2).2
        (profiledRawJointHybridCommonToTwoShadow A strategy hwin
          (profiledRawJointHybridForeverCommonControlTrace A strategy hwin
            inputs n) (inputs (n + 1)).2 (inputs (n + 1)).1).2
        (profiledRawJointHybridCommonToOneShadow A strategy hwin
          (profiledRawJointHybridForeverCommonControlTrace A strategy hwin
            inputs n) (inputs (n + 1)).1 (inputs (n + 1)).2).1
        (profiledRawJointHybridCommonToTwoShadow A strategy hwin
          (profiledRawJointHybridForeverCommonControlTrace A strategy hwin
            inputs n) (inputs (n + 1)).2 (inputs (n + 1)).1).1
        (inputs (n + 2)).1 (inputs (n + 2)).2]
      rw [profiledRawJointHybridForeverCommonControlTrace_succ A strategy hwin]
      rfl

/- Pointwise, the closed mega controller emits exactly the established
forever-common physical word. -/
set_option maxHeartbeats 2000000 in
theorem
    profiledRawJointHybridMegaLinkedUnconditional_allBoth_traceWord_apply
    (kernelTag : RetainedTag A strategy hwin)
    (inputs : Nat → In₁ × In₂) (n : Nat) :
    let mega := MegaPhysicalController A strategy hwin controllers initialBank
      kernelTag
    mega.globalMachine.globalMachineTraceWord mega.globalOutputOne
        mega.globalOutputTwo
        (profiledRawJointHybridMegaLinkedAllBothEnvironment inputs) n =
      profiledRawJointHybridForeverCommonPhysicalWord A strategy hwin inputs n :=
  by
    dsimp only
    unfold MegaPhysicalController
    cases n with
    | zero =>
        rw [FiniteGlobalRoundMachine.globalMachineTraceWord,
          FiniteGlobalRoundMachine.globalStateTrace_succ]
        simp only [FiniteGlobalRoundMachine.globalStateTrace_zero,
          profiledRawJointHybridMegaLinkedAllBothEnvironment_apply,
          bothEnvironment,
          FinitePairedPhysicalController.globalMachine_step,
          FinitePairedPhysicalController.globalMachine_initial]
        rw [profiledRawJointHybridMegaLinkedUnconditional_root_both A strategy
          hwin controllers initialBank kernelTag]
        change
          ({ inputOne := (inputs 0).1
             inputTwo := (inputs 0).2
             graph := Graph.both
             outputOne :=
               (profiledRawJointHybridInitialRootRecvOne A strategy hwin
                 controllers ((inputs 0).1, (inputs 0).2)).1
             outputTwo :=
               (profiledRawJointHybridInitialRootRecvTwo A strategy hwin
                 controllers ((inputs 0).1, (inputs 0).2)).1 } :
            RoundRecord In₁ In₂ Graph Out₁ Out₂) =
          nextRound strategy []
            ⟨(inputs 0).1, (inputs 0).2, Graph.both⟩
        have hout :=
          profiledRawJointHybridInitialRootRecv_outputs_eq_literalBoth A
            strategy hwin controllers ((inputs 0).1, (inputs 0).2)
        have houtOne := congrArg Prod.fst hout
        have houtTwo := congrArg Prod.snd hout
        have houtOne' :
            (profiledRawJointHybridInitialRootRecvOne A strategy hwin
              controllers ((inputs 0).1, (inputs 0).2)).1 =
              (nextRound strategy []
                ⟨(inputs 0).1, (inputs 0).2, Graph.both⟩).outputOne := by
          simpa only [Prod.fst] using houtOne
        have houtTwo' :
            (profiledRawJointHybridInitialRootRecvTwo A strategy hwin
              controllers ((inputs 0).1, (inputs 0).2)).1 =
              (nextRound strategy []
                ⟨(inputs 0).1, (inputs 0).2, Graph.both⟩).outputTwo := by
          simpa only [Prod.snd] using houtTwo
        rw [houtOne', houtTwo']
        unfold nextRound
        rfl
    | succ n =>
        rw [FiniteGlobalRoundMachine.globalMachineTraceWord]
        rw [profiledRawJointHybridMegaLinkedUnconditional_allBoth_globalStateTrace
          A strategy hwin controllers initialBank kernelTag inputs n]
        rfl

/-- Whole-word form of the trace identification. -/
theorem profiledRawJointHybridMegaLinkedUnconditional_allBoth_traceWord_eq
    (kernelTag : RetainedTag A strategy hwin)
    (inputs : Nat → In₁ × In₂) :
    let mega := MegaPhysicalController A strategy hwin controllers initialBank
      kernelTag
    mega.globalMachine.globalMachineTraceWord mega.globalOutputOne
        mega.globalOutputTwo
        (profiledRawJointHybridMegaLinkedAllBothEnvironment inputs) =
      profiledRawJointHybridForeverCommonPhysicalWord A strategy hwin inputs :=
  by
    funext n
    exact
      profiledRawJointHybridMegaLinkedUnconditional_allBoth_traceWord_apply A
        strategy hwin controllers initialBank kernelTag inputs n

/-- The repaired all-simultaneous branch of the closed mega controller is
accepted. -/
theorem profiledRawJointHybridMegaLinkedUnconditional_allBoth_accepts
    (kernelTag : RetainedTag A strategy hwin)
    (inputs : Nat → In₁ × In₂) :
    let mega := MegaPhysicalController A strategy hwin controllers initialBank
      kernelTag
    A.Accepts
      (mega.globalMachine.globalMachineTraceWord mega.globalOutputOne
        mega.globalOutputTwo
        (profiledRawJointHybridMegaLinkedAllBothEnvironment inputs)) := by
  dsimp only
  rw [profiledRawJointHybridMegaLinkedUnconditional_allBoth_traceWord_eq A
    strategy hwin controllers initialBank kernelTag inputs]
  exact profiledRawJointHybridForeverCommonPhysicalWord_accepts A strategy hwin
    inputs

end

end DetParityAutomaton

end DistributedSynthesis
