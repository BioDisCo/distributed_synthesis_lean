/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankRetainedReinstallation
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleShadowPhaseLiveTagBankController

/-!
# The finite marked-bank retained suffix controller

This file installs the leader-free retained literal carrier behind one finite
marked-bank tag.  The local control alphabets contain *all* marked-bank tags;
the initial tag is only a value stored in those fixed finite alphabets.  On a
receive, an endpoint copies exactly the tag belonging to the relay selected by
its local `lastRecv` bit.  Thus tag selection and relay selection cannot drift
apart, and no transition receives a graph, hierarchy orientation, leader bit,
strict-leader bit, semantic source, history, or view.

The controller deliberately does not call `RetainedTag.advance`.  A receive is
locally unable to distinguish a strict receive from a simultaneous receive,
so advancing by a proof-side `HybridDirection` there would be an illicit graph
oracle.  Direction advancement remains a proof-side bank/path equation.  The
outer common/shadow bootstrap must carry the retained root from its common
origin until its delayed tag is resolved; restarting it only when the tag is
delivered would lose the blind prefix.

The theorems below close the reusable executable part of that composition:

* a genuine `FinitePairedPhysicalController`, fixed once its finite initial
  tag is fixed;
* exact projection of every physical step and of the whole global trace to the
  already proved retained carrier;
* preservation of equal selected bank tags through all three graph cases; and
* a cast-free adapter from the existing phase-live tag bank to the marked-bank
  root selected by the same local common control.
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

private abbrev CommonControl :=
  ProfiledRawJointHybridCommonControl A strategy hwin

private abbrev ShadowTag :=
  ProfiledRawJointHybridShadowPhaseLiveTag A strategy hwin

private abbrev ShadowBankOne :=
  ProfiledRawJointHybridShadowPhaseLiveTagBankOneControl A strategy hwin

private abbrev ShadowBankTwo :=
  ProfiledRawJointHybridShadowPhaseLiveTagBankTwoControl A strategy hwin

private abbrev RetainedTag :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A strategy
    hwin

private abbrev OneControl :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneControl A
    strategy hwin

private abbrev TwoControl :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoControl A
    strategy hwin

private abbrev RetainedOne :=
  ProfiledRawJointHybridLiteralPrefixRetainedOneControl A

private abbrev RetainedTwo :=
  ProfiledRawJointHybridLiteralPrefixRetainedTwoControl A

/-! ## Local bank transitions -/

/-- A blind process-one step retains the selected finite bank tag and advances
only the genuine retained process-one control. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedNoRecvOne
    (state : OneControl A strategy hwin) (input : In₁) :
    OneControl A strategy hwin :=
  (state.1,
    profiledRawJointHybridLiteralPrefixRetainedNoRecvOne A state.2 input)

/-- Process-two mirror. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedNoRecvTwo
    (state : TwoControl A strategy hwin) (input : In₂) :
    TwoControl A strategy hwin :=
  (state.1,
    profiledRawJointHybridLiteralPrefixRetainedNoRecvTwo A state.2 input)

/-- Process one copies the tag of exactly the relay chosen by its local
`lastRecv` rule.  The Boolean is endpoint-local memory, not an orientation
test. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedRecvOne
    (state : OneControl A strategy hwin) (own : In₁)
    (partner : TwoControl A strategy hwin) (delivered : In₂) :
    OneControl A strategy hwin :=
  let selectedTag := if state.2.2.1 then state.1 else partner.1
  (selectedTag,
    profiledRawJointHybridLiteralPrefixRetainedRecvOne A state.2 own partner.2
      delivered)

/-- Process-two mirror. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedRecvTwo
    (state : TwoControl A strategy hwin) (own : In₂)
    (partner : OneControl A strategy hwin) (delivered : In₁) :
    TwoControl A strategy hwin :=
  let selectedTag := if state.2.2.1 then state.1 else partner.1
  (selectedTag,
    profiledRawJointHybridLiteralPrefixRetainedRecvTwo A state.2 own partner.2
      delivered)

/-! ## One fixed finite physical controller -/

/-- The whole marked-bank suffix controller.  Its local alphabets range over
every finite retained tag.  `initialTag` is construction-time initial data;
later transitions only inspect local controls and locally delivered data. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedController
    (initialTag : RetainedTag A strategy hwin) :
    FinitePairedPhysicalController In₁ In₂ Out₁ Out₂ where
  OneControl := OneControl A strategy hwin
  TwoControl := TwoControl A strategy hwin
  oneFinite := inferInstance
  twoFinite := inferInstance
  initialOne :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedInstallOne A
      strategy hwin initialTag
  initialTwo :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedInstallTwo A
      strategy hwin initialTag
  noRecvOne :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedNoRecvOne A
      strategy hwin
  noRecvTwo :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedNoRecvTwo A
      strategy hwin
  recvOne :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedRecvOne A
      strategy hwin
  recvTwo :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedRecvTwo A
      strategy hwin
  outputOne := fun state ↦ state.2.1
  outputTwo := fun state ↦ state.2.1

private abbrev BankController (initialTag : RetainedTag A strategy hwin) :=
  profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedController A
    strategy hwin initialTag

/-! ## Exact erasure to the retained carrier -/

/-- Forget only the finite marked-bank tags. -/
def profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedErase
    (state : OneControl A strategy hwin × TwoControl A strategy hwin) :
    RetainedOne A × RetainedTwo A :=
  (state.1.2, state.2.2)

@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedErase_initial
    (initialTag : RetainedTag A strategy hwin) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedErase A
        strategy hwin
        ((BankController A strategy hwin initialTag).initialOne,
          (BankController A strategy hwin initialTag).initialTwo) =
      initialTag.initial A strategy hwin :=
  rfl

/-- Every dispatched physical step erases to the corresponding step of the
leader-free retained carrier. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedErase_advanceControls
    (initialTag : RetainedTag A strategy hwin)
    (state : (BankController A strategy hwin initialTag).OneControl ×
      (BankController A strategy hwin initialTag).TwoControl)
    (round : EnvironmentRound In₁ In₂) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedErase A
        strategy hwin
        ((BankController A strategy hwin initialTag).advanceControls state
          round) =
      profiledRawJointHybridLiteralPrefixRetainedGraphStep A round.graph
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedErase A
          strategy hwin state)
        (round.inputOne, round.inputTwo) := by
  cases round with
  | mk inputOne inputTwo graph =>
      cases graph <;> rfl

@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetained_outputOne
    (initialTag : RetainedTag A strategy hwin)
    (state : (BankController A strategy hwin initialTag).OneControl) :
    (BankController A strategy hwin initialTag).outputOne state = state.2.1 :=
  rfl

@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetained_outputTwo
    (initialTag : RetainedTag A strategy hwin)
    (state : (BankController A strategy hwin initialTag).TwoControl) :
    (BankController A strategy hwin initialTag).outputTwo state = state.2.1 :=
  rfl

/-! ## Bank-key synchronization -/

/-- Proof-side agreement of the two locally stored finite tags. -/
def ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedKeysAgree
    (state : OneControl A strategy hwin × TwoControl A strategy hwin) : Prop :=
  state.1.1 = state.2.1

@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedKeysAgree_initial
    (initialTag : RetainedTag A strategy hwin) :
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedKeysAgree A
      strategy hwin
      ((BankController A strategy hwin initialTag).initialOne,
        (BankController A strategy hwin initialTag).initialTwo) :=
  rfl

/-- Equal tags remain equal after every physical graph case.  This is the
finite tag analogue of retained-relay authority. -/
theorem
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedKeysAgree.step
    (initialTag : RetainedTag A strategy hwin)
    (state : (BankController A strategy hwin initialTag).OneControl ×
      (BankController A strategy hwin initialTag).TwoControl)
    (hagrees :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedKeysAgree A
        strategy hwin state)
    (round : EnvironmentRound In₁ In₂) :
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedKeysAgree A
      strategy hwin
      ((BankController A strategy hwin initialTag).advanceControls state
        round) := by
  rcases state with ⟨one, two⟩
  unfold ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedKeysAgree at hagrees
  change one.1 = two.1 at hagrees
  unfold ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedKeysAgree
  cases round with
  | mk inputOne inputTwo graph =>
      cases graph <;>
        simp [FinitePairedPhysicalController.advanceControls,
          BankController,
          profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedController,
          profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedNoRecvOne,
          profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedNoRecvTwo,
          profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedRecvOne,
          profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedRecvTwo,
          hagrees]

/-! ## Whole-trace projection -/

/-- At every physical time the tagged controller has exactly the underlying
retained-carrier state reached from the selected tag's literal tables. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetained_globalStateTrace_erase
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedErase A
        strategy hwin
        ((BankController A strategy hwin initialTag).globalMachine.globalStateTrace
          env n) =
      (profiledRawJointHybridLiteralPrefixRetainedController A
          (initialTag.1.rightMove A strategy hwin)
          (initialTag.1.leftMove A strategy hwin) initialTag.2.1 initialTag.2.2
        ).globalMachine.globalStateTrace env n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [FiniteGlobalRoundMachine.globalStateTrace_succ,
        FiniteGlobalRoundMachine.globalStateTrace_succ]
      change
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedErase A
            strategy hwin
            ((BankController A strategy hwin initialTag).advanceControls
              ((BankController A strategy hwin initialTag).globalMachine.globalStateTrace
                env n)
              (env n)) = _
      rw [profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedErase_advanceControls
        A strategy hwin initialTag]
      change
        profiledRawJointHybridLiteralPrefixRetainedGraphStep A (env n).graph
            (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedErase
              A strategy hwin
                ((BankController A strategy hwin initialTag).globalMachine.globalStateTrace
                  env n))
            ((env n).inputOne, (env n).inputTwo) = _
      rw [ih]
      rw [FinitePairedPhysicalController.globalMachine_step,
        profiledRawJointHybridLiteralPrefixRetainedController_advanceControls]

/-- The selected finite tag stays synchronized along the actual global
machine trace. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetained_globalStateTrace_keysAgree
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedKeysAgree A
      strategy hwin
      ((BankController A strategy hwin initialTag).globalMachine.globalStateTrace
        env n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [FiniteGlobalRoundMachine.globalStateTrace_succ]
      exact
        ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedKeysAgree.step
          A strategy hwin initialTag _ ih (env n)

/-- Consequently the complete Moore word is definitionally the word of the
retained carrier selected by the initial finite bank tag. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetained_globalMachineTraceWord_eq
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) :
    (BankController A strategy hwin initialTag).globalMachine.globalMachineTraceWord
        (BankController A strategy hwin initialTag).globalOutputOne
        (BankController A strategy hwin initialTag).globalOutputTwo env =
      (profiledRawJointHybridLiteralPrefixRetainedController A
          (initialTag.1.rightMove A strategy hwin)
          (initialTag.1.leftMove A strategy hwin) initialTag.2.1 initialTag.2.2
        ).globalMachine.globalMachineTraceWord
          (profiledRawJointHybridLiteralPrefixRetainedController A
            (initialTag.1.rightMove A strategy hwin)
            (initialTag.1.leftMove A strategy hwin) initialTag.2.1 initialTag.2.2
          ).globalOutputOne
          (profiledRawJointHybridLiteralPrefixRetainedController A
            (initialTag.1.rightMove A strategy hwin)
            (initialTag.1.leftMove A strategy hwin) initialTag.2.1 initialTag.2.2
          ).globalOutputTwo env := by
  funext n
  have hstate :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetained_globalStateTrace_erase
      A strategy hwin initialTag env (n + 1)
  have houtputs := congrArg (fun state ↦ (state.1.1, state.2.1)) hstate
  have hone := congrArg Prod.fst houtputs
  have htwo := congrArg Prod.snd houtputs
  have hone' :
      (BankController A strategy hwin initialTag).globalOutputOne
          ((BankController A strategy hwin initialTag).globalMachine.globalStateTrace
            env (n + 1)) =
        (profiledRawJointHybridLiteralPrefixRetainedController A
            (initialTag.1.rightMove A strategy hwin)
            (initialTag.1.leftMove A strategy hwin) initialTag.2.1
            initialTag.2.2).globalOutputOne
          ((profiledRawJointHybridLiteralPrefixRetainedController A
              (initialTag.1.rightMove A strategy hwin)
              (initialTag.1.leftMove A strategy hwin) initialTag.2.1
              initialTag.2.2).globalMachine.globalStateTrace env (n + 1)) := by
    simpa [FinitePairedPhysicalController.globalOutputOne,
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedErase,
      BankController,
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedController,
      profiledRawJointHybridLiteralPrefixRetainedController] using hone
  have htwo' :
      (BankController A strategy hwin initialTag).globalOutputTwo
          ((BankController A strategy hwin initialTag).globalMachine.globalStateTrace
            env (n + 1)) =
        (profiledRawJointHybridLiteralPrefixRetainedController A
            (initialTag.1.rightMove A strategy hwin)
            (initialTag.1.leftMove A strategy hwin) initialTag.2.1
            initialTag.2.2).globalOutputTwo
          ((profiledRawJointHybridLiteralPrefixRetainedController A
              (initialTag.1.rightMove A strategy hwin)
              (initialTag.1.leftMove A strategy hwin) initialTag.2.1
              initialTag.2.2).globalMachine.globalStateTrace env (n + 1)) := by
    simpa [FinitePairedPhysicalController.globalOutputTwo,
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedErase,
      BankController,
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedController,
      profiledRawJointHybridLiteralPrefixRetainedController] using htwo
  unfold FiniteGlobalRoundMachine.globalMachineTraceWord
  rw [hone', htwo']

/-! ## Cast-free handoff from the existing phase-live tag bank -/

/-- The marked-bank root selected by the same common-control index stored in
an already delivered phase-live tag.  Canonical `false` anchors are harmless:
the literal moves are valid for both finite anchor values. -/
noncomputable def
    ProfiledRawJointHybridShadowPhaseLiveTag.markedRetainedRootTag
    (tag : ShadowTag A strategy hwin) : RetainedTag A strategy hwin :=
  (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRoot A strategy hwin
      tag.origin,
    (false, false))

theorem
    ProfiledRawJointHybridShadowPhaseLiveTag.markedRetainedRootTag_reachable
    (tag : ShadowTag A strategy hwin) :
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankReachable A strategy
      hwin (tag.markedRetainedRootTag A strategy hwin).1 :=
  profiledRawJointHybridValidatedMarkedLiteralPrefixBankRoot_reachable A
    strategy hwin tag.origin

/-- Convert a process-one state of the existing delivered tag bank to the
canonical marked retained root selected by its finite tag key. -/
noncomputable def
    profiledRawJointHybridShadowPhaseLiveTagBankToMarkedRetainedOne
    (state : ShadowBankOne A strategy hwin) : OneControl A strategy hwin :=
  profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedInstallOne A
    strategy hwin (state.1.markedRetainedRootTag A strategy hwin)

/-- Process-two mirror. -/
noncomputable def
    profiledRawJointHybridShadowPhaseLiveTagBankToMarkedRetainedTwo
    (state : ShadowBankTwo A strategy hwin) : TwoControl A strategy hwin :=
  profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedInstallTwo A
    strategy hwin (state.1.markedRetainedRootTag A strategy hwin)

/-- Equal phase-live tag keys select equal marked-bank retained keys. -/
theorem
    profiledRawJointHybridShadowPhaseLiveTagBankToMarkedRetained_keysAgree
    (one : ShadowBankOne A strategy hwin)
    (two : ShadowBankTwo A strategy hwin) (hkey : one.1 = two.1) :
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedKeysAgree A
      strategy hwin
      (profiledRawJointHybridShadowPhaseLiveTagBankToMarkedRetainedOne A
          strategy hwin one,
        profiledRawJointHybridShadowPhaseLiveTagBankToMarkedRetainedTwo A
          strategy hwin two) := by
  rcases one with ⟨oneTag, oneControl⟩
  rcases two with ⟨twoTag, twoControl⟩
  change oneTag = twoTag at hkey
  subst twoTag
  rfl

/-- The existing left-handoff activation therefore selects one common marked
bank entry at both endpoints, with no cast and no new environment-dependent
choice. -/
theorem
    profiledRawJointHybridActivateDeliveredLeftShadowPhaseLiveBank_markedRetained_keysAgree
    (delivered :
      ProfiledRawJointHybridLeftShadowPhaseLiveHandoff A strategy hwin) :
    let bank :=
      profiledRawJointHybridActivateDeliveredLeftShadowPhaseLiveBank A strategy
        hwin delivered
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedKeysAgree A
      strategy hwin
      (profiledRawJointHybridShadowPhaseLiveTagBankToMarkedRetainedOne A
          strategy hwin bank.1,
        profiledRawJointHybridShadowPhaseLiveTagBankToMarkedRetainedTwo A
          strategy hwin bank.2) := by
  rfl

/-- Strict-right mirror. -/
theorem
    profiledRawJointHybridActivateDeliveredRightShadowPhaseLiveBank_markedRetained_keysAgree
    (delivered :
      ProfiledRawJointHybridRightShadowPhaseLiveHandoff A strategy hwin) :
    let bank :=
      profiledRawJointHybridActivateDeliveredRightShadowPhaseLiveBank A
        strategy hwin delivered
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedKeysAgree A
      strategy hwin
      (profiledRawJointHybridShadowPhaseLiveTagBankToMarkedRetainedOne A
          strategy hwin bank.1,
        profiledRawJointHybridShadowPhaseLiveTagBankToMarkedRetainedTwo A
          strategy hwin bank.2) := by
  rfl

end

end DetParityAutomaton

end DistributedSynthesis
