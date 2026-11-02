/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonTailCoreStrictAcceptance
import DistributedSynthesis.Formalizations.Lemma.LemFiniteGlobalMachineReroot
import DistributedSynthesis.Formalizations.Lemma.LemFiniteGlobalBeliefPhysicalAcceptanceSplit

/-!
# Eventually fixed strict tails after a guarded common cut

The fixed-tail controller proof starts at a finite common-policy occurrence.
This file transports it to an arbitrary physical prefix that reaches two
agreeing local common shadows.  The graph orientation occurs only in the
proof-side suffix hypothesis; no local transition receives an orientation,
leader bit, semantic world, or history.
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

private abbrev CommonOne :=
  ProfiledRawJointGuardedInitialCommonOneState A strategy hwin

private abbrev CommonTwo :=
  ProfiledRawJointGuardedInitialCommonTwoState A strategy hwin

private abbrev TailKernel (kernelRoot : CommonControl A strategy hwin) :=
  profiledRawJointGuardedCommonTailCoreKernel A strategy hwin initialBank
    kernelRoot

/-! ## A proof-side common cut state -/

/-- Embed two local common shadows in the concrete global Moore carrier.
The stored outputs belong to the discarded prefix and are intentionally
arbitrary. -/
noncomputable def profiledRawJointGuardedCommonTailCommonGlobalState
    (kernelRoot : CommonControl A strategy hwin)
    (one : CommonOne A strategy hwin) (two : CommonTwo A strategy hwin)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂) :
    ((TailKernel A strategy hwin initialBank kernelRoot).globalMachine).State :=
  ((.exceptional
      (profiledRawJointGuardedCommonTailOneOfCommon A strategy hwin one),
      oldOutputOne),
    (.exceptional
      (profiledRawJointGuardedCommonTailTwoOfCommon A strategy hwin two),
      oldOutputTwo))

/-- The fallback root is not inspected while a strict-right owner is pending
beside its common receiver. -/
theorem profiledRawJointGuardedCommonTail_step_rightPending_root_independent
    (firstRoot secondRoot : CommonControl A strategy hwin)
    (owner : ProfiledRawJointGuardedCommonRightOwner A strategy hwin)
    (receiver : CommonTwo A strategy hwin)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂) (input : In₂ × In₁) :
    (TailKernel A strategy hwin initialBank firstRoot).globalMachine.step
        ((.exceptional
            (profiledRawJointGuardedCommonTailOneOfRightOwner A strategy hwin
              owner), oldOutputOne),
          (.exceptional
            (profiledRawJointGuardedCommonTailTwoOfCommon A strategy hwin
              receiver), oldOutputTwo))
        { inputOne := input.2, inputTwo := input.1, graph := .right } =
      (TailKernel A strategy hwin initialBank secondRoot).globalMachine.step
        ((.exceptional
            (profiledRawJointGuardedCommonTailOneOfRightOwner A strategy hwin
              owner), oldOutputOne),
          (.exceptional
            (profiledRawJointGuardedCommonTailTwoOfCommon A strategy hwin
              receiver), oldOutputTwo))
        { inputOne := input.2, inputTwo := input.1, graph := .right } := by
  rfl

/-- Once the strict-right receiver is resolved, the fallback root likewise
remains irrelevant. -/
theorem profiledRawJointGuardedCommonTail_step_resolvedRight_root_independent
    (firstRoot secondRoot : CommonControl A strategy hwin)
    (owner : ProfiledRawJointGuardedCommonRightOwner A strategy hwin)
    (receiver : ProfiledRawJointGuardedCommonTailRightReceiver A strategy hwin)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂) (input : In₂ × In₁) :
    (TailKernel A strategy hwin initialBank firstRoot).globalMachine.step
        ((.exceptional
            (profiledRawJointGuardedCommonTailOneOfRightOwner A strategy hwin
              owner), oldOutputOne),
          (.exceptional
            (profiledRawJointGuardedCommonTailTwoOfRightReceiver A strategy
              hwin receiver), oldOutputTwo))
        { inputOne := input.2, inputTwo := input.1, graph := .right } =
      (TailKernel A strategy hwin initialBank secondRoot).globalMachine.step
        ((.exceptional
            (profiledRawJointGuardedCommonTailOneOfRightOwner A strategy hwin
              owner), oldOutputOne),
          (.exceptional
            (profiledRawJointGuardedCommonTailTwoOfRightReceiver A strategy
              hwin receiver), oldOutputTwo))
        { inputOne := input.2, inputTwo := input.1, graph := .right } := by
  rfl

/-- Strict-left pending mirror of root independence. -/
theorem profiledRawJointGuardedCommonTail_step_leftPending_root_independent
    (firstRoot secondRoot : CommonControl A strategy hwin)
    (receiver : CommonOne A strategy hwin)
    (owner : ProfiledRawJointGuardedCommonLeftOwner A strategy hwin)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂) (input : In₁ × In₂) :
    (TailKernel A strategy hwin initialBank firstRoot).globalMachine.step
        ((.exceptional
            (profiledRawJointGuardedCommonTailOneOfCommon A strategy hwin
              receiver), oldOutputOne),
          (.exceptional
            (profiledRawJointGuardedCommonTailTwoOfLeftOwner A strategy hwin
              owner), oldOutputTwo))
        { inputOne := input.1, inputTwo := input.2, graph := .left } =
      (TailKernel A strategy hwin initialBank secondRoot).globalMachine.step
        ((.exceptional
            (profiledRawJointGuardedCommonTailOneOfCommon A strategy hwin
              receiver), oldOutputOne),
          (.exceptional
            (profiledRawJointGuardedCommonTailTwoOfLeftOwner A strategy hwin
              owner), oldOutputTwo))
        { inputOne := input.1, inputTwo := input.2, graph := .left } := by
  rfl

/-- Resolved strict-left mirror. -/
theorem profiledRawJointGuardedCommonTail_step_resolvedLeft_root_independent
    (firstRoot secondRoot : CommonControl A strategy hwin)
    (receiver : ProfiledRawJointGuardedCommonTailLeftReceiver A strategy hwin)
    (owner : ProfiledRawJointGuardedCommonLeftOwner A strategy hwin)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂) (input : In₁ × In₂) :
    (TailKernel A strategy hwin initialBank firstRoot).globalMachine.step
        ((.exceptional
            (profiledRawJointGuardedCommonTailOneOfLeftReceiver A strategy
              hwin receiver), oldOutputOne),
          (.exceptional
            (profiledRawJointGuardedCommonTailTwoOfLeftOwner A strategy hwin
              owner), oldOutputTwo))
        { inputOne := input.1, inputTwo := input.2, graph := .left } =
      (TailKernel A strategy hwin initialBank secondRoot).globalMachine.step
        ((.exceptional
            (profiledRawJointGuardedCommonTailOneOfLeftReceiver A strategy
              hwin receiver), oldOutputOne),
          (.exceptional
            (profiledRawJointGuardedCommonTailTwoOfLeftOwner A strategy hwin
              owner), oldOutputTwo))
        { inputOne := input.1, inputTwo := input.2, graph := .left } := by
  rfl

/-- One strict-right step from agreeing common shadows is the same concrete
state as one strict-right step from the bare occurrence root selected by
those shadows. -/
theorem
    profiledRawJointGuardedCommonTailCommonCut_firstStrictRight_state
    (kernelRoot : CommonControl A strategy hwin)
    (one : CommonOne A strategy hwin) (two : CommonTwo A strategy hwin)
    (hagrees : ProfiledRawJointGuardedInitialCommonStatesAgree A strategy hwin
      one two)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (env : Nat → In₂ × In₁) :
    let actual := TailKernel A strategy hwin initialBank kernelRoot
    let canonical := TailKernel A strategy hwin initialBank one.control
    (actual.globalMachine.reroot
      (profiledRawJointGuardedCommonTailCommonGlobalState A strategy hwin
        initialBank kernelRoot one two oldOutputOne oldOutputTwo)
      ).globalStateTrace
        (profiledRawJointGuardedCommonTailStrictRightEnvironment env) 1 =
      canonical.globalMachine.globalStateTrace
        (profiledRawJointGuardedCommonTailStrictRightEnvironment env) 1 := by
  dsimp only
  unfold ProfiledRawJointGuardedInitialCommonStatesAgree at hagrees
  rcases one with ⟨oneControl, oneShadow, oneCommonEq⟩
  rcases two with ⟨twoControl, twoShadow, twoCommonEq⟩
  simp only at hagrees oneCommonEq twoCommonEq
  subst twoControl
  have hone :
      profiledRawJointGuardedCommonTailCommonNoRecvOne A strategy hwin
          initialBank ⟨oneControl, oneShadow, oneCommonEq⟩ (env 0).2 =
        profiledRawJointGuardedCommonTailInitialNoRecvOne A strategy hwin
          initialBank oneControl (env 0).2 := by
    simp [profiledRawJointGuardedCommonTailCommonNoRecvOne,
      profiledRawJointGuardedCommonTailInitialNoRecvOne,
      profiledRawJointGuardedInitialCommonOneNoRecv,
      profiledRawJointGuardedCommonOneShadowNoRecv, oneCommonEq]
  have htwo :
      profiledRawJointGuardedCommonTailCommonRecvTwo A strategy hwin
          initialBank ⟨oneControl, twoShadow, twoCommonEq⟩
            ⟨oneControl, oneShadow, oneCommonEq⟩ (env 0).1 (env 0).2 =
        profiledRawJointGuardedCommonTailInitialRecvTwo A strategy hwin
          initialBank oneControl (env 0).1 (env 0).2 := by
    unfold profiledRawJointGuardedCommonTailCommonRecvTwo
      profiledRawJointGuardedCommonTailInitialRecvTwo
      profiledRawJointGuardedInitialCommonTwoRecv
      profiledRawJointGuardedInitialCommonStartTwo
      profiledRawJointGuardedCommonTwoShadowRecvOneShadow
    rw [twoCommonEq]
    apply Prod.ext
    · rfl
    · congr 2
  rw [FiniteGlobalRoundMachine.globalStateTrace_succ,
    FiniteGlobalRoundMachine.globalStateTrace_succ]
  change
    (((profiledRawJointGuardedCommonTailCommonNoRecvOne A strategy hwin
          initialBank ⟨oneControl, oneShadow, oneCommonEq⟩ (env 0).2).2,
        (profiledRawJointGuardedCommonTailCommonNoRecvOne A strategy hwin
          initialBank ⟨oneControl, oneShadow, oneCommonEq⟩ (env 0).2).1),
      ((profiledRawJointGuardedCommonTailCommonRecvTwo A strategy hwin
          initialBank ⟨oneControl, twoShadow, twoCommonEq⟩
            ⟨oneControl, oneShadow, oneCommonEq⟩ (env 0).1 (env 0).2).2,
        (profiledRawJointGuardedCommonTailCommonRecvTwo A strategy hwin
          initialBank ⟨oneControl, twoShadow, twoCommonEq⟩
            ⟨oneControl, oneShadow, oneCommonEq⟩ (env 0).1
              (env 0).2).1)) =
    (((profiledRawJointGuardedCommonTailInitialNoRecvOne A strategy hwin
          initialBank oneControl (env 0).2).2,
        (profiledRawJointGuardedCommonTailInitialNoRecvOne A strategy hwin
          initialBank oneControl (env 0).2).1),
      ((profiledRawJointGuardedCommonTailInitialRecvTwo A strategy hwin
          initialBank oneControl (env 0).1 (env 0).2).2,
        (profiledRawJointGuardedCommonTailInitialRecvTwo A strategy hwin
          initialBank oneControl (env 0).1 (env 0).2).1))
  rw [hone, htwo]

/-- After the first strict-right round, the actual machine rooted at the
discarded prefix and the canonical machine rooted at the current common
occurrence have identical state traces. -/
theorem
    profiledRawJointGuardedCommonTailCommonCut_strictRight_stateTrace
    (kernelRoot : CommonControl A strategy hwin)
    (one : CommonOne A strategy hwin) (two : CommonTwo A strategy hwin)
    (hagrees : ProfiledRawJointGuardedInitialCommonStatesAgree A strategy hwin
      one two)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (env : Nat → In₂ × In₁) : ∀ n : Nat,
    let actual := TailKernel A strategy hwin initialBank kernelRoot
    let canonical := TailKernel A strategy hwin initialBank one.control
    (actual.globalMachine.reroot
      (profiledRawJointGuardedCommonTailCommonGlobalState A strategy hwin
        initialBank kernelRoot one two oldOutputOne oldOutputTwo)
      ).globalStateTrace
        (profiledRawJointGuardedCommonTailStrictRightEnvironment env) (n + 1) =
      canonical.globalMachine.globalStateTrace
        (profiledRawJointGuardedCommonTailStrictRightEnvironment env)
          (n + 1) := by
  intro n
  induction n with
  | zero =>
      simpa using
        profiledRawJointGuardedCommonTailCommonCut_firstStrictRight_state A
          strategy hwin initialBank kernelRoot one two hagrees oldOutputOne
            oldOutputTwo env
  | succ n ih =>
      dsimp only at ih ⊢
      change
        (TailKernel A strategy hwin initialBank kernelRoot).globalMachine.step
            ((((TailKernel A strategy hwin initialBank kernelRoot).globalMachine
              ).reroot
                (profiledRawJointGuardedCommonTailCommonGlobalState A strategy
                  hwin initialBank kernelRoot one two oldOutputOne oldOutputTwo)
              ).globalStateTrace
                (profiledRawJointGuardedCommonTailStrictRightEnvironment env)
                  (n + 1))
            (profiledRawJointGuardedCommonTailStrictRightEnvironment env
              (n + 1)) =
          (TailKernel A strategy hwin initialBank one.control).globalMachine.step
            (((TailKernel A strategy hwin initialBank one.control).globalMachine
              ).globalStateTrace
                (profiledRawJointGuardedCommonTailStrictRightEnvironment env)
                  (n + 1))
            (profiledRawJointGuardedCommonTailStrictRightEnvironment env
              (n + 1))
      rw [ih]
      cases n with
      | zero =>
          rw [profiledRawJointGuardedCommonTailCore_firstStrictRight A strategy
            hwin initialBank one.control env]
          let ownerStep :=
            profiledRawJointGuardedCommonTailInitialNoRecvOne A strategy hwin
              initialBank one.control (env 0).2
          let receiverStep :=
            profiledRawJointGuardedCommonTailInitialRecvTwo A strategy hwin
              initialBank one.control (env 0).1 (env 0).2
          let pending :=
            profiledRawJointGuardedCommonTailInitialRightPending A strategy
              hwin one.control (env 0)
          have hroot :=
            profiledRawJointGuardedCommonTail_step_rightPending_root_independent
              A strategy hwin initialBank kernelRoot one.control pending.owner
                pending.receiver ownerStep.1 receiverStep.1 (env 1)
          simpa [ownerStep, receiverStep, pending,
            profiledRawJointGuardedCommonTailInitialRightPending,
            profiledRawJointGuardedCommonTailInitialNoRecvOne,
            profiledRawJointGuardedCommonTailInitialRecvTwo,
            profiledRawJointGuardedCommonTailStrictRightEnvironment] using hroot
      | succ n =>
          rw [show Nat.succ n + 1 = n + 2 by omega,
            profiledRawJointGuardedCommonTailCore_globalStateTrace_add_two_right
              A strategy hwin initialBank one.control env n]
          let state :=
            profiledRawJointGuardedCommonTailStrictRightStateTrace A strategy
              hwin one.control env n
          let output :=
            profiledRawJointGuardedCommonTailStrictRightOutputTrace A strategy
              hwin one.control env n
          have hroot :=
            profiledRawJointGuardedCommonTail_step_resolvedRight_root_independent
              A strategy hwin initialBank kernelRoot one.control
                state.strict.owner state output.1 output.2 (env (n + 2))
          simpa [state, output,
            profiledRawJointGuardedCommonTailStrictRightGlobalState,
            profiledRawJointGuardedCommonTailStrictRightEnvironment] using hroot

/-! ## Exact strict-right suffix word -/

/-- Rerooting at an agreeing common-shadow cut and then staying strict-right
produces exactly the guarded member-controller word selected at that finite
common occurrence. -/
theorem
    profiledRawJointGuardedCommonTailCommonCut_strictRight_traceWord
    (kernelRoot : CommonControl A strategy hwin)
    (one : CommonOne A strategy hwin) (two : CommonTwo A strategy hwin)
    (hagrees : ProfiledRawJointGuardedInitialCommonStatesAgree A strategy hwin
      one two)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (env : Nat → In₂ × In₁) :
    let actual := TailKernel A strategy hwin initialBank kernelRoot
    (actual.globalMachine.reroot
      (profiledRawJointGuardedCommonTailCommonGlobalState A strategy hwin
        initialBank kernelRoot one two oldOutputOne oldOutputTwo)
      ).globalMachineTraceWord actual.globalOutputOne actual.globalOutputTwo
        (profiledRawJointGuardedCommonTailStrictRightEnvironment env) =
      profiledRawJointGuardedCommonTailStrictRightControllerWord A strategy
        hwin one.control env := by
  dsimp only
  funext n
  rw [FiniteGlobalRoundMachine.globalMachineTraceWord,
    profiledRawJointGuardedCommonTailCommonCut_strictRight_stateTrace A
      strategy hwin initialBank kernelRoot one two hagrees oldOutputOne
        oldOutputTwo env n]
  have hcanonical :=
    profiledRawJointGuardedCommonTailCore_globalMachineTraceWord_right_controller
      A strategy hwin initialBank one.control env
  exact congrFun hcanonical n

/-! ## Strict-left mirror -/

/-- One strict-left step from agreeing common shadows agrees with the bare
occurrence-root step. -/
theorem
    profiledRawJointGuardedCommonTailCommonCut_firstStrictLeft_state
    (kernelRoot : CommonControl A strategy hwin)
    (one : CommonOne A strategy hwin) (two : CommonTwo A strategy hwin)
    (hagrees : ProfiledRawJointGuardedInitialCommonStatesAgree A strategy hwin
      one two)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (env : Nat → In₁ × In₂) :
    let actual := TailKernel A strategy hwin initialBank kernelRoot
    let canonical := TailKernel A strategy hwin initialBank one.control
    (actual.globalMachine.reroot
      (profiledRawJointGuardedCommonTailCommonGlobalState A strategy hwin
        initialBank kernelRoot one two oldOutputOne oldOutputTwo)
      ).globalStateTrace
        (profiledRawJointGuardedCommonTailStrictLeftEnvironment env) 1 =
      canonical.globalMachine.globalStateTrace
        (profiledRawJointGuardedCommonTailStrictLeftEnvironment env) 1 := by
  dsimp only
  unfold ProfiledRawJointGuardedInitialCommonStatesAgree at hagrees
  rcases one with ⟨oneControl, oneShadow, oneCommonEq⟩
  rcases two with ⟨twoControl, twoShadow, twoCommonEq⟩
  simp only at hagrees oneCommonEq twoCommonEq
  subst twoControl
  have hone :
      profiledRawJointGuardedCommonTailCommonRecvOne A strategy hwin
          initialBank ⟨oneControl, oneShadow, oneCommonEq⟩
            ⟨oneControl, twoShadow, twoCommonEq⟩ (env 0).1 (env 0).2 =
        profiledRawJointGuardedCommonTailInitialRecvOne A strategy hwin
          initialBank oneControl (env 0).1 (env 0).2 := by
    unfold profiledRawJointGuardedCommonTailCommonRecvOne
      profiledRawJointGuardedCommonTailInitialRecvOne
      profiledRawJointGuardedInitialCommonOneRecv
      profiledRawJointGuardedInitialCommonStartOne
      profiledRawJointGuardedCommonOneShadowRecvTwoShadow
    rw [oneCommonEq]
    apply Prod.ext
    · rfl
    · congr 2
  have htwo :
      profiledRawJointGuardedCommonTailCommonNoRecvTwo A strategy hwin
          initialBank ⟨oneControl, twoShadow, twoCommonEq⟩ (env 0).2 =
        profiledRawJointGuardedCommonTailInitialNoRecvTwo A strategy hwin
          initialBank oneControl (env 0).2 := by
    simp [profiledRawJointGuardedCommonTailCommonNoRecvTwo,
      profiledRawJointGuardedCommonTailInitialNoRecvTwo,
      profiledRawJointGuardedInitialCommonTwoNoRecv,
      profiledRawJointGuardedCommonTwoShadowNoRecv, twoCommonEq]
  rw [FiniteGlobalRoundMachine.globalStateTrace_succ,
    FiniteGlobalRoundMachine.globalStateTrace_succ]
  change
    (((profiledRawJointGuardedCommonTailCommonRecvOne A strategy hwin
          initialBank ⟨oneControl, oneShadow, oneCommonEq⟩
            ⟨oneControl, twoShadow, twoCommonEq⟩ (env 0).1 (env 0).2).2,
        (profiledRawJointGuardedCommonTailCommonRecvOne A strategy hwin
          initialBank ⟨oneControl, oneShadow, oneCommonEq⟩
            ⟨oneControl, twoShadow, twoCommonEq⟩ (env 0).1
              (env 0).2).1),
      ((profiledRawJointGuardedCommonTailCommonNoRecvTwo A strategy hwin
          initialBank ⟨oneControl, twoShadow, twoCommonEq⟩ (env 0).2).2,
        (profiledRawJointGuardedCommonTailCommonNoRecvTwo A strategy hwin
          initialBank ⟨oneControl, twoShadow, twoCommonEq⟩ (env 0).2).1)) =
    (((profiledRawJointGuardedCommonTailInitialRecvOne A strategy hwin
          initialBank oneControl (env 0).1 (env 0).2).2,
        (profiledRawJointGuardedCommonTailInitialRecvOne A strategy hwin
          initialBank oneControl (env 0).1 (env 0).2).1),
      ((profiledRawJointGuardedCommonTailInitialNoRecvTwo A strategy hwin
          initialBank oneControl (env 0).2).2,
        (profiledRawJointGuardedCommonTailInitialNoRecvTwo A strategy hwin
          initialBank oneControl (env 0).2).1))
  rw [hone, htwo]

/-- Strict-left state traces coincide after the first fixed-side round. -/
theorem
    profiledRawJointGuardedCommonTailCommonCut_strictLeft_stateTrace
    (kernelRoot : CommonControl A strategy hwin)
    (one : CommonOne A strategy hwin) (two : CommonTwo A strategy hwin)
    (hagrees : ProfiledRawJointGuardedInitialCommonStatesAgree A strategy hwin
      one two)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (env : Nat → In₁ × In₂) : ∀ n : Nat,
    let actual := TailKernel A strategy hwin initialBank kernelRoot
    let canonical := TailKernel A strategy hwin initialBank one.control
    (actual.globalMachine.reroot
      (profiledRawJointGuardedCommonTailCommonGlobalState A strategy hwin
        initialBank kernelRoot one two oldOutputOne oldOutputTwo)
      ).globalStateTrace
        (profiledRawJointGuardedCommonTailStrictLeftEnvironment env) (n + 1) =
      canonical.globalMachine.globalStateTrace
        (profiledRawJointGuardedCommonTailStrictLeftEnvironment env)
          (n + 1) := by
  intro n
  induction n with
  | zero =>
      simpa using
        profiledRawJointGuardedCommonTailCommonCut_firstStrictLeft_state A
          strategy hwin initialBank kernelRoot one two hagrees oldOutputOne
            oldOutputTwo env
  | succ n ih =>
      dsimp only at ih ⊢
      change
        (TailKernel A strategy hwin initialBank kernelRoot).globalMachine.step
            ((((TailKernel A strategy hwin initialBank kernelRoot).globalMachine
              ).reroot
                (profiledRawJointGuardedCommonTailCommonGlobalState A strategy
                  hwin initialBank kernelRoot one two oldOutputOne oldOutputTwo)
              ).globalStateTrace
                (profiledRawJointGuardedCommonTailStrictLeftEnvironment env)
                  (n + 1))
            (profiledRawJointGuardedCommonTailStrictLeftEnvironment env
              (n + 1)) =
          (TailKernel A strategy hwin initialBank one.control).globalMachine.step
            (((TailKernel A strategy hwin initialBank one.control).globalMachine
              ).globalStateTrace
                (profiledRawJointGuardedCommonTailStrictLeftEnvironment env)
                  (n + 1))
            (profiledRawJointGuardedCommonTailStrictLeftEnvironment env
              (n + 1))
      rw [ih]
      cases n with
      | zero =>
          rw [profiledRawJointGuardedCommonTailCore_firstStrictLeft A strategy
            hwin initialBank one.control env]
          let receiverStep :=
            profiledRawJointGuardedCommonTailInitialRecvOne A strategy hwin
              initialBank one.control (env 0).1 (env 0).2
          let ownerStep :=
            profiledRawJointGuardedCommonTailInitialNoRecvTwo A strategy hwin
              initialBank one.control (env 0).2
          let pending :=
            profiledRawJointGuardedCommonTailInitialLeftPending A strategy
              hwin one.control (env 0)
          have hroot :=
            profiledRawJointGuardedCommonTail_step_leftPending_root_independent
              A strategy hwin initialBank kernelRoot one.control
                pending.receiver pending.owner receiverStep.1 ownerStep.1
                  (env 1)
          simpa [receiverStep, ownerStep, pending,
            profiledRawJointGuardedCommonTailInitialLeftPending,
            profiledRawJointGuardedCommonTailInitialRecvOne,
            profiledRawJointGuardedCommonTailInitialNoRecvTwo,
            profiledRawJointGuardedCommonTailStrictLeftEnvironment] using hroot
      | succ n =>
          rw [show Nat.succ n + 1 = n + 2 by omega,
            profiledRawJointGuardedCommonTailCore_globalStateTrace_add_two_left
              A strategy hwin initialBank one.control env n]
          let state :=
            profiledRawJointGuardedCommonTailStrictLeftStateTrace A strategy
              hwin one.control env n
          let output :=
            profiledRawJointGuardedCommonTailStrictLeftOutputTrace A strategy
              hwin one.control env n
          have hroot :=
            profiledRawJointGuardedCommonTail_step_resolvedLeft_root_independent
              A strategy hwin initialBank kernelRoot one.control state
                state.strict.owner output.1 output.2 (env (n + 2))
          simpa [state, output,
            profiledRawJointGuardedCommonTailStrictLeftGlobalState,
            profiledRawJointGuardedCommonTailStrictLeftEnvironment] using hroot

/-- Exact guarded finite-controller word at a synchronized common cut on an
all-left suffix. -/
theorem
    profiledRawJointGuardedCommonTailCommonCut_strictLeft_traceWord
    (kernelRoot : CommonControl A strategy hwin)
    (one : CommonOne A strategy hwin) (two : CommonTwo A strategy hwin)
    (hagrees : ProfiledRawJointGuardedInitialCommonStatesAgree A strategy hwin
      one two)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (env : Nat → In₁ × In₂) :
    let actual := TailKernel A strategy hwin initialBank kernelRoot
    (actual.globalMachine.reroot
      (profiledRawJointGuardedCommonTailCommonGlobalState A strategy hwin
        initialBank kernelRoot one two oldOutputOne oldOutputTwo)
      ).globalMachineTraceWord actual.globalOutputOne actual.globalOutputTwo
        (profiledRawJointGuardedCommonTailStrictLeftEnvironment env) =
      profiledRawJointGuardedCommonTailStrictLeftControllerWord A strategy
        hwin one.control env := by
  dsimp only
  funext n
  rw [FiniteGlobalRoundMachine.globalMachineTraceWord,
    profiledRawJointGuardedCommonTailCommonCut_strictLeft_stateTrace A
      strategy hwin initialBank kernelRoot one two hagrees oldOutputOne
        oldOutputTwo env n]
  have hcanonical :=
    profiledRawJointGuardedCommonTailCore_globalMachineTraceWord_left_controller
      A strategy hwin initialBank one.control env
  exact congrFun hcanonical n

/-! ## Transport from an actual finite prefix -/

/-- Exact dropped physical word at an actual synchronized common cut whose
suffix is all strict-right. -/
theorem profiledRawJointGuardedCommonTailCommonCut_strictRight_suffixWord
    (kernelRoot : CommonControl A strategy hwin)
    (physicalEnv : EnvironmentSequence In₁ In₂) (start : Nat)
    (one : CommonOne A strategy hwin) (two : CommonTwo A strategy hwin)
    (hagrees : ProfiledRawJointGuardedInitialCommonStatesAgree A strategy hwin
      one two)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (env : Nat → In₂ × In₁)
    (hcontrol :
      (TailKernel A strategy hwin initialBank kernelRoot).globalMachine.globalStateTrace
          physicalEnv start =
        profiledRawJointGuardedCommonTailCommonGlobalState A strategy hwin
          initialBank kernelRoot one two oldOutputOne oldOutputTwo)
    (henv : OmegaWord.drop physicalEnv start =
      profiledRawJointGuardedCommonTailStrictRightEnvironment env) :
    OmegaWord.drop
        ((TailKernel A strategy hwin initialBank kernelRoot).globalMachine.globalMachineTraceWord
            (TailKernel A strategy hwin initialBank kernelRoot).globalOutputOne
            (TailKernel A strategy hwin initialBank kernelRoot).globalOutputTwo
            physicalEnv) start =
      profiledRawJointGuardedCommonTailStrictRightControllerWord A strategy
        hwin one.control env := by
  let G := (TailKernel A strategy hwin initialBank kernelRoot).globalMachine
  have hreroot := G.reroot_globalMachineTraceWord_drop
    (TailKernel A strategy hwin initialBank kernelRoot).globalOutputOne
    (TailKernel A strategy hwin initialBank kernelRoot).globalOutputTwo
    physicalEnv start
  rw [hcontrol, henv,
    profiledRawJointGuardedCommonTailCommonCut_strictRight_traceWord A
      strategy hwin initialBank kernelRoot one two hagrees oldOutputOne
        oldOutputTwo env] at hreroot
  exact hreroot.symm

/-- Strict-left dropped-word mirror. -/
theorem profiledRawJointGuardedCommonTailCommonCut_strictLeft_suffixWord
    (kernelRoot : CommonControl A strategy hwin)
    (physicalEnv : EnvironmentSequence In₁ In₂) (start : Nat)
    (one : CommonOne A strategy hwin) (two : CommonTwo A strategy hwin)
    (hagrees : ProfiledRawJointGuardedInitialCommonStatesAgree A strategy hwin
      one two)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (env : Nat → In₁ × In₂)
    (hcontrol :
      (TailKernel A strategy hwin initialBank kernelRoot).globalMachine.globalStateTrace
          physicalEnv start =
        profiledRawJointGuardedCommonTailCommonGlobalState A strategy hwin
          initialBank kernelRoot one two oldOutputOne oldOutputTwo)
    (henv : OmegaWord.drop physicalEnv start =
      profiledRawJointGuardedCommonTailStrictLeftEnvironment env) :
    OmegaWord.drop
        ((TailKernel A strategy hwin initialBank kernelRoot).globalMachine.globalMachineTraceWord
            (TailKernel A strategy hwin initialBank kernelRoot).globalOutputOne
            (TailKernel A strategy hwin initialBank kernelRoot).globalOutputTwo
            physicalEnv) start =
      profiledRawJointGuardedCommonTailStrictLeftControllerWord A strategy hwin
        one.control env := by
  let G := (TailKernel A strategy hwin initialBank kernelRoot).globalMachine
  have hreroot := G.reroot_globalMachineTraceWord_drop
    (TailKernel A strategy hwin initialBank kernelRoot).globalOutputOne
    (TailKernel A strategy hwin initialBank kernelRoot).globalOutputTwo
    physicalEnv start
  rw [hcontrol, henv,
    profiledRawJointGuardedCommonTailCommonCut_strictLeft_traceWord A strategy
      hwin initialBank kernelRoot one two hagrees oldOutputOne oldOutputTwo env]
      at hreroot
  exact hreroot.symm

/-- The strict-right suffix is accepted from the actual post-prefix DPA
state, provided that state is the represented common occurrence's entry. -/
theorem
    profiledRawJointGuardedCommonTailCommonCut_strictRight_acceptsFrom_actual
    (kernelRoot : CommonControl A strategy hwin)
    (physicalEnv : EnvironmentSequence In₁ In₂) (start : Nat)
    (one : CommonOne A strategy hwin) (two : CommonTwo A strategy hwin)
    (hagrees : ProfiledRawJointGuardedInitialCommonStatesAgree A strategy hwin
      one two)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (env : Nat → In₂ × In₁)
    (hcontrol :
      (TailKernel A strategy hwin initialBank kernelRoot).globalMachine.globalStateTrace
          physicalEnv start =
        profiledRawJointGuardedCommonTailCommonGlobalState A strategy hwin
          initialBank kernelRoot one two oldOutputOne oldOutputTwo)
    (henv : OmegaWord.drop physicalEnv start =
      profiledRawJointGuardedCommonTailStrictRightEnvironment env)
    (hstate :
      A.run
          ((TailKernel A strategy hwin initialBank kernelRoot).globalMachine.globalMachineTraceWord
              (TailKernel A strategy hwin initialBank kernelRoot).globalOutputOne
              (TailKernel A strategy hwin initialBank kernelRoot).globalOutputTwo
              physicalEnv) start =
        (profiledRawJointGuardedInitialCommonControlPair A strategy hwin
          one.control).1.1.1.base.source.1.1.2) :
    A.AcceptsFrom
      (A.run
        ((TailKernel A strategy hwin initialBank kernelRoot).globalMachine.globalMachineTraceWord
            (TailKernel A strategy hwin initialBank kernelRoot).globalOutputOne
            (TailKernel A strategy hwin initialBank kernelRoot).globalOutputTwo
            physicalEnv) start)
      (OmegaWord.drop
        ((TailKernel A strategy hwin initialBank kernelRoot).globalMachine.globalMachineTraceWord
            (TailKernel A strategy hwin initialBank kernelRoot).globalOutputOne
            (TailKernel A strategy hwin initialBank kernelRoot).globalOutputTwo
            physicalEnv) start) := by
  rw [hstate,
    profiledRawJointGuardedCommonTailCommonCut_strictRight_suffixWord A
      strategy hwin initialBank kernelRoot physicalEnv start one two hagrees
        oldOutputOne oldOutputTwo env hcontrol henv]
  exact
    profiledRawJointGuardedCommonTailStrictRightControllerAcceptsFromEntry A
      strategy hwin one.control env

/-- Strict-left actual-state mirror. -/
theorem
    profiledRawJointGuardedCommonTailCommonCut_strictLeft_acceptsFrom_actual
    (kernelRoot : CommonControl A strategy hwin)
    (physicalEnv : EnvironmentSequence In₁ In₂) (start : Nat)
    (one : CommonOne A strategy hwin) (two : CommonTwo A strategy hwin)
    (hagrees : ProfiledRawJointGuardedInitialCommonStatesAgree A strategy hwin
      one two)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (env : Nat → In₁ × In₂)
    (hcontrol :
      (TailKernel A strategy hwin initialBank kernelRoot).globalMachine.globalStateTrace
          physicalEnv start =
        profiledRawJointGuardedCommonTailCommonGlobalState A strategy hwin
          initialBank kernelRoot one two oldOutputOne oldOutputTwo)
    (henv : OmegaWord.drop physicalEnv start =
      profiledRawJointGuardedCommonTailStrictLeftEnvironment env)
    (hstate :
      A.run
          ((TailKernel A strategy hwin initialBank kernelRoot).globalMachine.globalMachineTraceWord
              (TailKernel A strategy hwin initialBank kernelRoot).globalOutputOne
              (TailKernel A strategy hwin initialBank kernelRoot).globalOutputTwo
              physicalEnv) start =
        (profiledRawJointGuardedInitialCommonControlPair A strategy hwin
          one.control).1.2.1.base.source.1.1.2) :
    A.AcceptsFrom
      (A.run
        ((TailKernel A strategy hwin initialBank kernelRoot).globalMachine.globalMachineTraceWord
            (TailKernel A strategy hwin initialBank kernelRoot).globalOutputOne
            (TailKernel A strategy hwin initialBank kernelRoot).globalOutputTwo
            physicalEnv) start)
      (OmegaWord.drop
        ((TailKernel A strategy hwin initialBank kernelRoot).globalMachine.globalMachineTraceWord
            (TailKernel A strategy hwin initialBank kernelRoot).globalOutputOne
            (TailKernel A strategy hwin initialBank kernelRoot).globalOutputTwo
            physicalEnv) start) := by
  rw [hstate,
    profiledRawJointGuardedCommonTailCommonCut_strictLeft_suffixWord A strategy
      hwin initialBank kernelRoot physicalEnv start one two hagrees oldOutputOne
        oldOutputTwo env hcontrol henv]
  exact
    profiledRawJointGuardedCommonTailStrictLeftControllerAcceptsFromEntry A
      strategy hwin one.control env

/-- Complete physical-word acceptance after a represented strict-right common
cut.  The arbitrary finite prefix is retained in the original DPA run. -/
theorem profiledRawJointGuardedCommonTailCommonCut_strictRight_accepts
    (kernelRoot : CommonControl A strategy hwin)
    (physicalEnv : EnvironmentSequence In₁ In₂) (start : Nat)
    (one : CommonOne A strategy hwin) (two : CommonTwo A strategy hwin)
    (hagrees : ProfiledRawJointGuardedInitialCommonStatesAgree A strategy hwin
      one two)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (env : Nat → In₂ × In₁)
    (hcontrol :
      (TailKernel A strategy hwin initialBank kernelRoot).globalMachine.globalStateTrace
          physicalEnv start =
        profiledRawJointGuardedCommonTailCommonGlobalState A strategy hwin
          initialBank kernelRoot one two oldOutputOne oldOutputTwo)
    (henv : OmegaWord.drop physicalEnv start =
      profiledRawJointGuardedCommonTailStrictRightEnvironment env)
    (hstate :
      A.run
          ((TailKernel A strategy hwin initialBank kernelRoot).globalMachine.globalMachineTraceWord
              (TailKernel A strategy hwin initialBank kernelRoot).globalOutputOne
              (TailKernel A strategy hwin initialBank kernelRoot).globalOutputTwo
              physicalEnv) start =
        (profiledRawJointGuardedInitialCommonControlPair A strategy hwin
          one.control).1.1.1.base.source.1.1.2) :
    A.Accepts
      ((TailKernel A strategy hwin initialBank kernelRoot).globalMachine.globalMachineTraceWord
          (TailKernel A strategy hwin initialBank kernelRoot).globalOutputOne
          (TailKernel A strategy hwin initialBank kernelRoot).globalOutputTwo
          physicalEnv) := by
  let word :=
    (TailKernel A strategy hwin initialBank kernelRoot).globalMachine.globalMachineTraceWord
        (TailKernel A strategy hwin initialBank kernelRoot).globalOutputOne
        (TailKernel A strategy hwin initialBank kernelRoot).globalOutputTwo
        physicalEnv
  have haccepts :=
    profiledRawJointGuardedCommonTailCommonCut_strictRight_acceptsFrom_actual
      A strategy hwin initialBank kernelRoot physicalEnv start one two hagrees
        oldOutputOne oldOutputTwo env hcontrol henv hstate
  exact (A.acceptsFrom_runFrom_drop_iff A.initial word start).mp haccepts

/-- Complete strict-left mirror. -/
theorem profiledRawJointGuardedCommonTailCommonCut_strictLeft_accepts
    (kernelRoot : CommonControl A strategy hwin)
    (physicalEnv : EnvironmentSequence In₁ In₂) (start : Nat)
    (one : CommonOne A strategy hwin) (two : CommonTwo A strategy hwin)
    (hagrees : ProfiledRawJointGuardedInitialCommonStatesAgree A strategy hwin
      one two)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (env : Nat → In₁ × In₂)
    (hcontrol :
      (TailKernel A strategy hwin initialBank kernelRoot).globalMachine.globalStateTrace
          physicalEnv start =
        profiledRawJointGuardedCommonTailCommonGlobalState A strategy hwin
          initialBank kernelRoot one two oldOutputOne oldOutputTwo)
    (henv : OmegaWord.drop physicalEnv start =
      profiledRawJointGuardedCommonTailStrictLeftEnvironment env)
    (hstate :
      A.run
          ((TailKernel A strategy hwin initialBank kernelRoot).globalMachine.globalMachineTraceWord
              (TailKernel A strategy hwin initialBank kernelRoot).globalOutputOne
              (TailKernel A strategy hwin initialBank kernelRoot).globalOutputTwo
              physicalEnv) start =
        (profiledRawJointGuardedInitialCommonControlPair A strategy hwin
          one.control).1.2.1.base.source.1.1.2) :
    A.Accepts
      ((TailKernel A strategy hwin initialBank kernelRoot).globalMachine.globalMachineTraceWord
          (TailKernel A strategy hwin initialBank kernelRoot).globalOutputOne
          (TailKernel A strategy hwin initialBank kernelRoot).globalOutputTwo
          physicalEnv) := by
  let word :=
    (TailKernel A strategy hwin initialBank kernelRoot).globalMachine.globalMachineTraceWord
        (TailKernel A strategy hwin initialBank kernelRoot).globalOutputOne
        (TailKernel A strategy hwin initialBank kernelRoot).globalOutputTwo
        physicalEnv
  have haccepts :=
    profiledRawJointGuardedCommonTailCommonCut_strictLeft_acceptsFrom_actual A
      strategy hwin initialBank kernelRoot physicalEnv start one two hagrees
        oldOutputOne oldOutputTwo env hcontrol henv hstate
  exact (A.acceptsFrom_runFrom_drop_iff A.initial word start).mp haccepts

/-! ## Proof-side eventual-tail certificates -/

/-- Read the right-controller inputs from an actual environment suffix. -/
def profiledRawJointGuardedCommonTailRightInputsAfter
    (physicalEnv : EnvironmentSequence In₁ In₂) (start : Nat) :
    Nat → In₂ × In₁ :=
  fun n ↦
    ((physicalEnv (start + n)).inputTwo,
      (physicalEnv (start + n)).inputOne)

/-- Left-controller input extraction. -/
def profiledRawJointGuardedCommonTailLeftInputsAfter
    (physicalEnv : EnvironmentSequence In₁ In₂) (start : Nat) :
    Nat → In₁ × In₂ :=
  fun n ↦
    ((physicalEnv (start + n)).inputOne,
      (physicalEnv (start + n)).inputTwo)

omit [Inhabited In₁] [Inhabited In₂] [Fintype In₁] [Fintype In₂] [DecidableEq In₁]
    [DecidableEq In₂] in
/-- An eventually-right graph hypothesis identifies the literal dropped
environment with the right-controller environment. -/
theorem profiledRawJointGuardedCommonTail_drop_eq_strictRightEnvironment
    (physicalEnv : EnvironmentSequence In₁ In₂) (start : Nat)
    (hgraph : ∀ n, start ≤ n → (physicalEnv n).graph = .right) :
    OmegaWord.drop physicalEnv start =
      profiledRawJointGuardedCommonTailStrictRightEnvironment
        (profiledRawJointGuardedCommonTailRightInputsAfter physicalEnv start) := by
  funext n
  apply EnvironmentRound.equivProd.injective
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · rfl
    · simpa [OmegaWord.drop,
        profiledRawJointGuardedCommonTailStrictRightEnvironment] using
        hgraph (start + n) (by omega)

omit [Inhabited In₁] [Inhabited In₂] [Fintype In₁] [Fintype In₂] [DecidableEq In₁]
    [DecidableEq In₂] in
/-- Eventually-left mirror. -/
theorem profiledRawJointGuardedCommonTail_drop_eq_strictLeftEnvironment
    (physicalEnv : EnvironmentSequence In₁ In₂) (start : Nat)
    (hgraph : ∀ n, start ≤ n → (physicalEnv n).graph = .left) :
    OmegaWord.drop physicalEnv start =
      profiledRawJointGuardedCommonTailStrictLeftEnvironment
        (profiledRawJointGuardedCommonTailLeftInputsAfter physicalEnv start) := by
  funext n
  apply EnvironmentRound.equivProd.injective
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · rfl
    · simpa [OmegaWord.drop,
        profiledRawJointGuardedCommonTailStrictLeftEnvironment] using
        hgraph (start + n) (by omega)

/-- A proof-side cut witnessing that an actual execution has reached two
agreeing finite common shadows at the beginning of its eventual strict-right
tail.  It stores no executable orientation signal. -/
structure ProfiledRawJointGuardedCommonTailEventuallyStrictRightCut
    (kernelRoot : CommonControl A strategy hwin)
    (physicalEnv : EnvironmentSequence In₁ In₂) where
  start : Nat
  one : CommonOne A strategy hwin
  two : CommonTwo A strategy hwin
  oldOutputOne : Out₁
  oldOutputTwo : Out₂
  agrees : ProfiledRawJointGuardedInitialCommonStatesAgree A strategy hwin one
    two
  strict : ∀ n, start ≤ n → (physicalEnv n).graph = .right
  control :
    (TailKernel A strategy hwin initialBank kernelRoot).globalMachine.globalStateTrace
        physicalEnv start =
      profiledRawJointGuardedCommonTailCommonGlobalState A strategy hwin
        initialBank kernelRoot one two oldOutputOne oldOutputTwo
  entry :
    A.run
        ((TailKernel A strategy hwin initialBank kernelRoot).globalMachine.globalMachineTraceWord
          (TailKernel A strategy hwin initialBank kernelRoot).globalOutputOne
          (TailKernel A strategy hwin initialBank kernelRoot).globalOutputTwo
          physicalEnv) start =
      (profiledRawJointGuardedInitialCommonControlPair A strategy hwin
        one.control).1.1.1.base.source.1.1.2

/-- Strict-left proof-side cut. -/
structure ProfiledRawJointGuardedCommonTailEventuallyStrictLeftCut
    (kernelRoot : CommonControl A strategy hwin)
    (physicalEnv : EnvironmentSequence In₁ In₂) where
  start : Nat
  one : CommonOne A strategy hwin
  two : CommonTwo A strategy hwin
  oldOutputOne : Out₁
  oldOutputTwo : Out₂
  agrees : ProfiledRawJointGuardedInitialCommonStatesAgree A strategy hwin one
    two
  strict : ∀ n, start ≤ n → (physicalEnv n).graph = .left
  control :
    (TailKernel A strategy hwin initialBank kernelRoot).globalMachine.globalStateTrace
        physicalEnv start =
      profiledRawJointGuardedCommonTailCommonGlobalState A strategy hwin
        initialBank kernelRoot one two oldOutputOne oldOutputTwo
  entry :
    A.run
        ((TailKernel A strategy hwin initialBank kernelRoot).globalMachine.globalMachineTraceWord
          (TailKernel A strategy hwin initialBank kernelRoot).globalOutputOne
          (TailKernel A strategy hwin initialBank kernelRoot).globalOutputTwo
          physicalEnv) start =
      (profiledRawJointGuardedInitialCommonControlPair A strategy hwin
        one.control).1.2.1.base.source.1.1.2

/-- The right cut visibly entails the standard proof-side graph regime. -/
theorem
    ProfiledRawJointGuardedCommonTailEventuallyStrictRightCut.eventuallyStrict
    {kernelRoot : CommonControl A strategy hwin}
    {physicalEnv : EnvironmentSequence In₁ In₂}
    (cut : ProfiledRawJointGuardedCommonTailEventuallyStrictRightCut A strategy
      hwin initialBank kernelRoot physicalEnv) :
    EventuallyStrictRight (fun n ↦ (physicalEnv n).graph) :=
  ⟨cut.start, cut.strict⟩

/-- Left regime witness. -/
theorem
    ProfiledRawJointGuardedCommonTailEventuallyStrictLeftCut.eventuallyStrict
    {kernelRoot : CommonControl A strategy hwin}
    {physicalEnv : EnvironmentSequence In₁ In₂}
    (cut : ProfiledRawJointGuardedCommonTailEventuallyStrictLeftCut A strategy
      hwin initialBank kernelRoot physicalEnv) :
    EventuallyStrictLeft (fun n ↦ (physicalEnv n).graph) :=
  ⟨cut.start, cut.strict⟩

/-- End-to-end eventual strict-right acceptance from the reached finite cut.
The controller root is `cut.one.control`; no process is told that fact at
runtime. -/
theorem
    ProfiledRawJointGuardedCommonTailEventuallyStrictRightCut.accepts
    {kernelRoot : CommonControl A strategy hwin}
    {physicalEnv : EnvironmentSequence In₁ In₂}
    (cut : ProfiledRawJointGuardedCommonTailEventuallyStrictRightCut A strategy
      hwin initialBank kernelRoot physicalEnv) :
    A.Accepts
      ((TailKernel A strategy hwin initialBank kernelRoot).globalMachine.globalMachineTraceWord
        (TailKernel A strategy hwin initialBank kernelRoot).globalOutputOne
        (TailKernel A strategy hwin initialBank kernelRoot).globalOutputTwo
        physicalEnv) := by
  let env := profiledRawJointGuardedCommonTailRightInputsAfter physicalEnv
    cut.start
  apply profiledRawJointGuardedCommonTailCommonCut_strictRight_accepts A
    strategy hwin initialBank kernelRoot physicalEnv cut.start cut.one cut.two
      cut.agrees cut.oldOutputOne cut.oldOutputTwo env cut.control
  · exact
      profiledRawJointGuardedCommonTail_drop_eq_strictRightEnvironment
        physicalEnv cut.start cut.strict
  · exact cut.entry

/-- Eventual strict-left end-to-end acceptance. -/
theorem
    ProfiledRawJointGuardedCommonTailEventuallyStrictLeftCut.accepts
    {kernelRoot : CommonControl A strategy hwin}
    {physicalEnv : EnvironmentSequence In₁ In₂}
    (cut : ProfiledRawJointGuardedCommonTailEventuallyStrictLeftCut A strategy
      hwin initialBank kernelRoot physicalEnv) :
    A.Accepts
      ((TailKernel A strategy hwin initialBank kernelRoot).globalMachine.globalMachineTraceWord
        (TailKernel A strategy hwin initialBank kernelRoot).globalOutputOne
        (TailKernel A strategy hwin initialBank kernelRoot).globalOutputTwo
        physicalEnv) := by
  let env := profiledRawJointGuardedCommonTailLeftInputsAfter physicalEnv
    cut.start
  apply profiledRawJointGuardedCommonTailCommonCut_strictLeft_accepts A strategy
    hwin initialBank kernelRoot physicalEnv cut.start cut.one cut.two cut.agrees
      cut.oldOutputOne cut.oldOutputTwo env cut.control
  · exact
      profiledRawJointGuardedCommonTail_drop_eq_strictLeftEnvironment
        physicalEnv cut.start cut.strict
  · exact cut.entry

end

end DetParityAutomaton

end DistributedSynthesis
