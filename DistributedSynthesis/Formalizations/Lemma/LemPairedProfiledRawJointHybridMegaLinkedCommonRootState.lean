/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridMegaLinkedFirstPersistentCut
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankLinkedRetainedCarrier

/-!
# DPA state at a common-root strict handoff

The first strict record emitted from a synchronized common root moves the
deterministic parity checker from its `both` row to the exact executable
sender source stored by the newly selected strict child.
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

theorem profiledRawJointHybridMegaLinkedCommonRootstrictRight_checker
    (control : ProfiledRawJointHybridCommonControl A strategy hwin)
    (input : In₁ × In₂) :
    let state :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankRoot A strategy hwin
        control
    let world :=
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankInstalled A
        strategy hwin control).world
    let installed :=
      profiledRawJointHybridLiteralPrefixSeedInstalled A strategy world
    let activation :=
      profiledRawJointHybridExactRightUniformActivation A strategy hwin
        installed
    let initial :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedCommonRootInitialOfState
        A strategy hwin state
    let next :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedStrictRightStep
        A strategy hwin initial input
    A.step (pairedCodeStateForRow A .both (world.procOneSlot A).1.1)
        (rightRoundRecord (input.2, input.1) next.1.1 next.2.1) =
      pairedCodeStateForRow A .first
        (profiledRawRightChildSlot A (world.procOneSlot A) activation.lambda
          .both [] (input.2, input.1)).1.1 := by
  dsimp only
  let state :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRoot A strategy hwin
      control
  let world :=
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankInstalled A
      strategy hwin control).world
  let installed :=
    profiledRawJointHybridLiteralPrefixSeedInstalled A strategy world
  let activation :=
    profiledRawJointHybridExactRightUniformActivation A strategy hwin installed
  let initial :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedCommonRootInitialOfState
      A strategy hwin state
  let next :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedStrictRightStep
      A strategy hwin initial input
  have hout :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedCommonRoot_strictRight_initial_output
      A strategy hwin control input
  change (next.1.1, next.2.1) = _ at hout
  have houtOne := congrArg Prod.fst hout
  have houtTwo := congrArg Prod.snd hout
  change next.1.1 = _ at houtOne
  change next.2.1 = _ at houtTwo
  change A.step (pairedCodeStateForRow A .both (world.procOneSlot A).1.1)
      (rightRoundRecord (input.2, input.1) next.1.1 next.2.1) = _
  rw [houtOne, houtTwo]
  simpa [activation, installed, world] using
    (profiledRawJointRight_bothRootStep_eq_childFirstState A activation
      (input.2, input.1))

theorem profiledRawJointHybridMegaLinkedCommonRootstrictRight_childSlot_eq_tagSource
    (control : ProfiledRawJointHybridCommonControl A strategy hwin)
    (input : In₁ × In₂) :
    let world :=
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankInstalled A
        strategy hwin control).world
    let installed :=
      profiledRawJointHybridLiteralPrefixSeedInstalled A strategy world
    let activation :=
      profiledRawJointHybridExactRightUniformActivation A strategy hwin
        installed
    let tag :=
      profiledRawJointHybridShadowPhaseLiveRightTag A strategy hwin control
        input
    profiledRawRightChildSlot A (world.procOneSlot A) activation.lambda .both
        [] (input.2, input.1) =
      (tag.initialLeftMove A strategy hwin).1.source := by
  dsimp only
  let bankInstalled :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankInstalled A strategy
      hwin control
  let world := bankInstalled.world
  let installed :=
    profiledRawJointHybridLiteralPrefixSeedInstalled A strategy world
  let activation :=
    profiledRawJointHybridExactRightUniformActivation A strategy hwin installed
  let tag :=
    profiledRawJointHybridShadowPhaseLiveRightTag A strategy hwin control input
  let shadowInstalled :=
    profiledRawJointHybridShadowPhaseLiveInstalled A strategy hwin control
  have htargetSeed :
      activation.target .both [] (input.2, input.1) =
        profiledRawJointOneSidedNext A installed.incidenceCode installed.rawMove
          (profiledRawJointCommonOneRoundStrictRight input) := by
    simpa [activation,
      profiledRawJointHybridExactRightUniformActivation] using
      (profiledRawJointHybridExactRightActivation_strictChild A installed
        (profiledRawJointHybridExactRightPolicy A hwin installed)
        (profiledRawJointHybridExactRightActivation A hwin installed) input)
  have hseedIncidence : installed.incidenceCode = shadowInstalled.incidenceCode :=
    installed.incidence_eq.symm.trans shadowInstalled.incidence_eq
  have hseedMove : installed.rawMove = shadowInstalled.rawMove :=
    installed.move_eq.symm.trans shadowInstalled.move_eq
  have htarget :
      activation.target .both [] (input.2, input.1) =
        tag.childIncidence A strategy hwin := by
    rw [htargetSeed, hseedIncidence, hseedMove]
    rfl
  have hlive :=
    profiledRawJointHybridShadowPhaseLiveRightTag_tailRoot_leftLive A strategy
      hwin control input
  dsimp only at hlive
  change
    profiledRawJointHybridCurrentSlots A .left
        (tag.tailRoot A strategy hwin).1.1 () =
      some (.inr (tag.initialLeftMove A strategy hwin).1.source) at hlive
  have hpublic := tag.tailRoot_publicCode A strategy hwin
  have hslot :
      (tag.childIncidence A strategy hwin).family.left () =
        some (tag.initialLeftMove A strategy hwin).1.source := by
    rw [hpublic] at hlive
    simpa [profiledRawJointHybridCurrentSlots,
      profiledRawJointOneSidedCurrentSlots] using hlive
  have hstate := activation.target_state .both [] (input.2, input.1)
  rw [htarget] at hstate
  simp [profiledRawJointUnitRightTargetProjection, hslot] at hstate
  simpa [activation, installed, world,
    profiledRawJointHybridExactRightUniformDescriptor] using hstate.symm

theorem profiledRawJointHybridMegaLinkedCommonRootstrictRight_checker_eq_tagSource
    (control : ProfiledRawJointHybridCommonControl A strategy hwin)
    (input : In₁ × In₂) :
    let state :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankRoot A strategy hwin
        control
    let world :=
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankInstalled A
        strategy hwin control).world
    let initial :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedCommonRootInitialOfState
        A strategy hwin state
    let next :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedStrictRightStep
        A strategy hwin initial input
    let tag :=
      profiledRawJointHybridShadowPhaseLiveRightTag A strategy hwin control
        input
    A.step (pairedCodeStateForRow A .both (world.procOneSlot A).1.1)
        (rightRoundRecord (input.2, input.1) next.1.1 next.2.1) =
      pairedCodeStateForRow A .first
        ((tag.initialLeftMove A strategy hwin).1.source).1.1 := by
  dsimp only
  rw [profiledRawJointHybridMegaLinkedCommonRootstrictRight_checker A strategy hwin control input]
  rw [profiledRawJointHybridMegaLinkedCommonRootstrictRight_childSlot_eq_tagSource A strategy hwin
    control input]

theorem profiledRawJointHybridMegaLinkedCommonRootstrictLeft_checker
    (control : ProfiledRawJointHybridCommonControl A strategy hwin)
    (input : In₁ × In₂) :
    let state :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankRoot A strategy hwin
        control
    let world :=
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankInstalled A
        strategy hwin control).world
    let installed :=
      profiledRawJointHybridLiteralPrefixSeedInstalled A strategy world
    let activation :=
      profiledRawJointHybridExactLeftUniformActivation A strategy hwin
        installed
    let initial :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedCommonRootInitialOfState
        A strategy hwin state
    let next :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedStrictLeftStep
        A strategy hwin initial input
    A.step (pairedCodeStateForRow A .both (world.procTwoSlot A).1.1)
        (leftRoundRecord input next.1.1 next.2.1) =
      pairedCodeStateForRow A .first
        (profiledRawLeftChildSlot A (world.procTwoSlot A) activation.lambda
          .both [] input).1.1 := by
  dsimp only
  let state :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRoot A strategy hwin
      control
  let world :=
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankInstalled A
      strategy hwin control).world
  let installed :=
    profiledRawJointHybridLiteralPrefixSeedInstalled A strategy world
  let activation :=
    profiledRawJointHybridExactLeftUniformActivation A strategy hwin installed
  let initial :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedCommonRootInitialOfState
      A strategy hwin state
  let next :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedStrictLeftStep
      A strategy hwin initial input
  have hout :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedCommonRoot_strictLeft_initial_output
      A strategy hwin control input
  change (next.1.1, next.2.1) = _ at hout
  have houtOne := congrArg Prod.fst hout
  have houtTwo := congrArg Prod.snd hout
  change next.1.1 = _ at houtOne
  change next.2.1 = _ at houtTwo
  change A.step (pairedCodeStateForRow A .both (world.procTwoSlot A).1.1)
      (leftRoundRecord input next.1.1 next.2.1) = _
  rw [houtOne, houtTwo]
  simpa [activation, installed, world] using
    (profiledRawJointLeft_bothRootStep_eq_childFirstState A activation input)

theorem profiledRawJointHybridMegaLinkedCommonRootstrictLeft_childSlot_eq_tagSource
    (control : ProfiledRawJointHybridCommonControl A strategy hwin)
    (input : In₁ × In₂) :
    let world :=
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankInstalled A
        strategy hwin control).world
    let installed :=
      profiledRawJointHybridLiteralPrefixSeedInstalled A strategy world
    let activation :=
      profiledRawJointHybridExactLeftUniformActivation A strategy hwin
        installed
    let tag :=
      profiledRawJointHybridShadowPhaseLiveLeftTag A strategy hwin control input
    profiledRawLeftChildSlot A (world.procTwoSlot A) activation.lambda .both
        [] input =
      (tag.initialRightMove A strategy hwin).1.source := by
  dsimp only
  let bankInstalled :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankInstalled A strategy
      hwin control
  let world := bankInstalled.world
  let installed :=
    profiledRawJointHybridLiteralPrefixSeedInstalled A strategy world
  let activation :=
    profiledRawJointHybridExactLeftUniformActivation A strategy hwin installed
  let tag :=
    profiledRawJointHybridShadowPhaseLiveLeftTag A strategy hwin control input
  let shadowInstalled :=
    profiledRawJointHybridShadowPhaseLiveInstalled A strategy hwin control
  have htargetSeed :
      activation.target .both [] input =
        profiledRawJointOneSidedNext A installed.incidenceCode installed.rawMove
          (profiledRawJointCommonOneRoundStrictLeft input) := by
    simpa [activation,
      profiledRawJointHybridExactLeftUniformActivation] using
      (profiledRawJointHybridExactLeftActivation_strictChild A installed
        (profiledRawJointHybridExactLeftPolicy A hwin installed)
        (profiledRawJointHybridExactLeftActivation A hwin installed) input)
  have hseedIncidence : installed.incidenceCode = shadowInstalled.incidenceCode :=
    installed.incidence_eq.symm.trans shadowInstalled.incidence_eq
  have hseedMove : installed.rawMove = shadowInstalled.rawMove :=
    installed.move_eq.symm.trans shadowInstalled.move_eq
  have htarget :
      activation.target .both [] input =
        tag.childIncidence A strategy hwin := by
    rw [htargetSeed, hseedIncidence, hseedMove]
    rfl
  have hlive :=
    profiledRawJointHybridShadowPhaseLiveLeftTag_tailRoot_rightLive A strategy
      hwin control input
  dsimp only at hlive
  change
    profiledRawJointHybridCurrentSlots A .right
        (tag.tailRoot A strategy hwin).1.1 () =
      some (.inl (tag.initialRightMove A strategy hwin).1.source) at hlive
  have hpublic := tag.tailRoot_publicCode A strategy hwin
  have hslot :
      (tag.childIncidence A strategy hwin).family.right () =
        some (tag.initialRightMove A strategy hwin).1.source := by
    rw [hpublic] at hlive
    simpa [profiledRawJointHybridCurrentSlots,
      profiledRawJointOneSidedCurrentSlots] using hlive
  have hstate := activation.target_state .both [] input
  rw [htarget] at hstate
  simp [profiledRawJointUnitLeftTargetProjection, hslot] at hstate
  simpa [activation, installed, world,
    profiledRawJointHybridExactLeftUniformDescriptor] using hstate.symm

theorem profiledRawJointHybridMegaLinkedCommonRootstrictLeft_checker_eq_tagSource
    (control : ProfiledRawJointHybridCommonControl A strategy hwin)
    (input : In₁ × In₂) :
    let state :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankRoot A strategy hwin
        control
    let world :=
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankInstalled A
        strategy hwin control).world
    let initial :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedCommonRootInitialOfState
        A strategy hwin state
    let next :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRetainedStrictLeftStep
        A strategy hwin initial input
    let tag :=
      profiledRawJointHybridShadowPhaseLiveLeftTag A strategy hwin control input
    A.step (pairedCodeStateForRow A .both (world.procTwoSlot A).1.1)
        (leftRoundRecord input next.1.1 next.2.1) =
      pairedCodeStateForRow A .first
        ((tag.initialRightMove A strategy hwin).1.source).1.1 := by
  dsimp only
  rw [profiledRawJointHybridMegaLinkedCommonRootstrictLeft_checker A strategy hwin control input]
  rw [profiledRawJointHybridMegaLinkedCommonRootstrictLeft_childSlot_eq_tagSource A strategy hwin
    control input]

end

end DetParityAutomaton

end DistributedSynthesis
