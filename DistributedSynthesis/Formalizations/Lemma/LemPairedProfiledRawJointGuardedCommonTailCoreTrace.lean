/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonTailCoreAdapter
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLocalReceiveTrace
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointLeaderFreeReadback

/-!
# The all-receive trace of the guarded-common tail kernel

On an environment consisting only of simultaneous receives, the concrete
tail-core kernel never reaches a fallback or a strict state.  After physical
tail round `n`, its two Moore controls are exactly the two local components of
`profiledRawJointGuardedCommonLocalStateTrace` at `n`, and its stored outputs
are exactly `profiledRawJointGuardedCommonLocalOutputTrace` at `n`.

This file proves only operational trace equality.  In particular, it makes no
standalone acceptance claim about a tail whose two literal seed rounds have
been removed.
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
  (initialBank : ProfiledRawJointInitialControllerBank A strategy)

private abbrev CommonControl :=
  ProfiledRawJointGuardedInitialCommonControl A strategy hwin

private abbrev CoreKernel (root : CommonControl A strategy hwin) :=
  profiledRawJointGuardedCommonTailCoreKernel A strategy hwin initialBank root

/-! ## The all-receive environment and embedded local state -/

/-- Tail inputs viewed as an environment of simultaneous receives. -/
def profiledRawJointGuardedCommonTailAllBothEnvironment
    (inputs : Nat → In₁ × In₂) : EnvironmentSequence In₁ In₂ :=
  fun n ↦ bothEnvironment (inputs n)

omit [Inhabited In₁] [Inhabited In₂] [Fintype In₁] [Fintype In₂] [DecidableEq In₁]
    [DecidableEq In₂] in
@[simp] theorem profiledRawJointGuardedCommonTailAllBothEnvironment_apply
    (inputs : Nat → In₁ × In₂) (n : Nat) :
    profiledRawJointGuardedCommonTailAllBothEnvironment inputs n =
      bothEnvironment (inputs n) :=
  rfl

/-- Embed a synchronized local common state and its freshly emitted output in
the concrete kernel's joint Moore state. -/
noncomputable def profiledRawJointGuardedCommonTailLocalGlobalState
    (root : CommonControl A strategy hwin)
    (state : ProfiledRawJointGuardedCommonLocalPairState A strategy hwin)
    (output : Out₁ × Out₂) :
    ((CoreKernel A strategy hwin initialBank root).globalMachine).State :=
  ((.exceptional
      (profiledRawJointGuardedCommonTailOneOfCommon A strategy hwin state.one),
      output.1),
    (.exceptional
      (profiledRawJointGuardedCommonTailTwoOfCommon A strategy hwin state.two),
      output.2))

/-! ## Exact global-state trace -/

/-- The first all-receive tail step enters exactly the fresh synchronized
local common state. -/
@[simp] theorem profiledRawJointGuardedCommonTailCore_globalStateTrace_one
    (root : CommonControl A strategy hwin) (inputs : Nat → In₁ × In₂) :
    ((CoreKernel A strategy hwin initialBank root).globalMachine
        ).globalStateTrace
        (profiledRawJointGuardedCommonTailAllBothEnvironment inputs) 1 =
      profiledRawJointGuardedCommonTailLocalGlobalState A strategy hwin
        (initialBank := initialBank) root
        (profiledRawJointGuardedCommonLocalStateTrace A strategy hwin root
          inputs 0)
        (profiledRawJointGuardedCommonLocalOutputTrace A strategy hwin root
          inputs 0) := by
  rfl

/-- At every positive time, the concrete global kernel state is precisely the
embedding of the independently executable synchronized local trace. -/
theorem profiledRawJointGuardedCommonTailCore_globalStateTrace_succ
    (root : CommonControl A strategy hwin) (inputs : Nat → In₁ × In₂) :
    ∀ n,
      ((CoreKernel A strategy hwin initialBank root).globalMachine
          ).globalStateTrace
          (profiledRawJointGuardedCommonTailAllBothEnvironment inputs)
          (n + 1) =
        profiledRawJointGuardedCommonTailLocalGlobalState A strategy hwin
          (initialBank := initialBank) root
          (profiledRawJointGuardedCommonLocalStateTrace A strategy hwin root
            inputs n)
          (profiledRawJointGuardedCommonLocalOutputTrace A strategy hwin root
            inputs n) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [FiniteGlobalRoundMachine.globalStateTrace_succ, ih]
      rfl

/-! ## Pointwise physical-word equality -/

/-- The guarded common tail word rooted at an arbitrary supplied bank
control.  This is the root-relative form of the tail occurring after the two
literal seed rounds in the forever-common construction. -/
noncomputable def profiledRawJointGuardedCommonTailWordFrom
    (root : CommonControl A strategy hwin) (inputs : Nat → In₁ × In₂) :
    OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂) :=
  fun n ↦
    let control :=
      profiledRawJointGuardedCommonLocalControlTrace A strategy hwin root
        inputs n
    let output := profiledRawJointGuardedCommonPairBothOutput A strategy hwin
      (profiledRawJointGuardedInitialCommonControlPair A strategy hwin control)
      (inputs n)
    bothRoundRecord (inputs n) output.1 output.2

/-- Pointwise, the concrete kernel's all-`both` physical word is the guarded
common tail word from the supplied root. -/
theorem
    profiledRawJointGuardedCommonTailCore_globalMachineTraceWord_apply
    (root : CommonControl A strategy hwin) (inputs : Nat → In₁ × In₂)
    (n : Nat) :
    let kernel := CoreKernel A strategy hwin initialBank root
    (kernel.globalMachine).globalMachineTraceWord kernel.globalOutputOne
        kernel.globalOutputTwo
        (profiledRawJointGuardedCommonTailAllBothEnvironment inputs) n =
      profiledRawJointGuardedCommonTailWordFrom A strategy hwin root inputs n :=
  by
    dsimp only
    rw [FiniteGlobalRoundMachine.globalMachineTraceWord]
    rw [profiledRawJointGuardedCommonTailCore_globalStateTrace_succ A strategy
      hwin initialBank root inputs n]
    rw [profiledRawJointGuardedCommonLocalOutputTrace_eq_pairBothOutput A
      strategy hwin root inputs n]
    rfl

/-- Whole-word extensional form of the pointwise trace theorem. -/
theorem profiledRawJointGuardedCommonTailCore_globalMachineTraceWord_eq
    (root : CommonControl A strategy hwin) (inputs : Nat → In₁ × In₂) :
    let kernel := CoreKernel A strategy hwin initialBank root
    (kernel.globalMachine).globalMachineTraceWord kernel.globalOutputOne
        kernel.globalOutputTwo
        (profiledRawJointGuardedCommonTailAllBothEnvironment inputs) =
      profiledRawJointGuardedCommonTailWordFrom A strategy hwin root inputs :=
  by
    funext n
    exact
      profiledRawJointGuardedCommonTailCore_globalMachineTraceWord_apply A
        strategy hwin initialBank root inputs n

/-! ## Identification with the established forever-common tail -/

/-- Starting the local control trace at the bank root selected by the first
two physical input pairs gives exactly the control trace used by the existing
forever-common tail. -/
theorem
    profiledRawJointGuardedCommonLocalControlTrace_from_seed_eq_forever
    (inputs : Nat → In₁ × In₂) : ∀ n,
    profiledRawJointGuardedCommonLocalControlTrace A strategy hwin
        (profiledRawJointGuardedInitialCommonControlRoot A strategy hwin
          (inputs 0, inputs 1))
        (fun k ↦ inputs (k + 2)) n =
      profiledRawJointGuardedForeverCommonControlTrace A strategy hwin inputs
        n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [profiledRawJointGuardedCommonLocalControlTrace]
      rw [profiledRawJointGuardedForeverCommonControlTrace_succ]
      rw [ih]

/-- Consequently, the root-relative word is pointwise the exact guarded
forever-common tail already used by the prefixed physical acceptance proof. -/
theorem profiledRawJointGuardedCommonTailWordFrom_seed_apply
    (inputs : Nat → In₁ × In₂) (n : Nat) :
    profiledRawJointGuardedCommonTailWordFrom A strategy hwin
        (profiledRawJointGuardedInitialCommonControlRoot A strategy hwin
          (inputs 0, inputs 1))
        (fun k ↦ inputs (k + 2)) n =
      profiledRawJointGuardedForeverCommonTailWord A strategy hwin inputs n :=
  by
    unfold profiledRawJointGuardedCommonTailWordFrom
    unfold profiledRawJointGuardedForeverCommonTailWord
    rw [profiledRawJointGuardedCommonLocalControlTrace_from_seed_eq_forever A
      strategy hwin inputs n]

/-- Extensional form of the seeded tail identification. -/
theorem profiledRawJointGuardedCommonTailWordFrom_seed_eq
    (inputs : Nat → In₁ × In₂) :
    profiledRawJointGuardedCommonTailWordFrom A strategy hwin
        (profiledRawJointGuardedInitialCommonControlRoot A strategy hwin
          (inputs 0, inputs 1))
        (fun k ↦ inputs (k + 2)) =
      profiledRawJointGuardedForeverCommonTailWord A strategy hwin inputs :=
  by
    funext n
    exact profiledRawJointGuardedCommonTailWordFrom_seed_apply A strategy hwin
      inputs n

/-- Direct pointwise specialization of the concrete kernel trace to the
established guarded common tail.  No acceptance conclusion is drawn here. -/
theorem
    profiledRawJointGuardedCommonTailCore_seed_globalMachineTraceWord_apply
    (inputs : Nat → In₁ × In₂) (n : Nat) :
    let root :=
      profiledRawJointGuardedInitialCommonControlRoot A strategy hwin
        (inputs 0, inputs 1)
    let kernel := CoreKernel A strategy hwin initialBank root
    (kernel.globalMachine).globalMachineTraceWord kernel.globalOutputOne
        kernel.globalOutputTwo
        (profiledRawJointGuardedCommonTailAllBothEnvironment
          (fun k ↦ inputs (k + 2))) n =
      profiledRawJointGuardedForeverCommonTailWord A strategy hwin inputs n :=
  by
    dsimp only
    rw [profiledRawJointGuardedCommonTailCore_globalMachineTraceWord_apply A
      strategy hwin initialBank
      (profiledRawJointGuardedInitialCommonControlRoot A strategy hwin
        (inputs 0, inputs 1))
      (fun k ↦ inputs (k + 2)) n]
    exact profiledRawJointGuardedCommonTailWordFrom_seed_apply A strategy hwin
      inputs n

/-! ## Restoring the two literal seed rounds -/

/-- The concrete tail-core word with the two literal physical seed rounds
restored in front.  Only this prefixed word is handed to the DPA acceptance
theorem. -/
noncomputable def profiledRawJointGuardedCommonTailCoreSeedPhysicalWord
    (inputs : Nat → In₁ × In₂) :
    OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂) :=
  let root :=
    profiledRawJointGuardedInitialCommonControlRoot A strategy hwin
      (inputs 0, inputs 1)
  let kernel := CoreKernel A strategy hwin initialBank root
  OmegaWord.prependList
    [profiledRawJointGuardedForeverCommonFirstRound strategy inputs,
      profiledRawJointGuardedForeverCommonSecondRound A strategy inputs]
    ((kernel.globalMachine).globalMachineTraceWord kernel.globalOutputOne
      kernel.globalOutputTwo
      (profiledRawJointGuardedCommonTailAllBothEnvironment
        (fun k ↦ inputs (k + 2))))

/-- The prefixed concrete kernel word is exactly the already verified
forever-common physical word. -/
theorem profiledRawJointGuardedCommonTailCoreSeedPhysicalWord_eq
    (inputs : Nat → In₁ × In₂) :
    profiledRawJointGuardedCommonTailCoreSeedPhysicalWord A strategy hwin
        initialBank inputs =
      profiledRawJointGuardedForeverCommonPhysicalWord A strategy hwin
        inputs := by
  unfold profiledRawJointGuardedCommonTailCoreSeedPhysicalWord
  unfold profiledRawJointGuardedForeverCommonPhysicalWord
  dsimp only
  rw [profiledRawJointGuardedCommonTailCore_globalMachineTraceWord_eq A
    strategy hwin initialBank
    (profiledRawJointGuardedInitialCommonControlRoot A strategy hwin
      (inputs 0, inputs 1))
    (fun k ↦ inputs (k + 2))]
  rw [profiledRawJointGuardedCommonTailWordFrom_seed_eq A strategy hwin
    inputs]

/-- Acceptance of the concrete all-`both` core after restoring the mandatory
two physical seed rounds.  There is deliberately no theorem asserting
acceptance of the unprefixed tail. -/
theorem profiledRawJointGuardedCommonTailCoreSeedPhysicalWord_accepts
    (inputs : Nat → In₁ × In₂) :
    A.Accepts
      (profiledRawJointGuardedCommonTailCoreSeedPhysicalWord A strategy hwin
        initialBank inputs) := by
  rw [profiledRawJointGuardedCommonTailCoreSeedPhysicalWord_eq A strategy hwin
    initialBank inputs]
  exact profiledRawJointGuardedForeverCommonPhysicalWord_accepts A strategy
    hwin inputs

end

end DetParityAutomaton

end DistributedSynthesis
