/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridInitialOneRoundReplacement
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointInitialCommonBothOneShot

/-!
# The second-level ambiguity below an initial simultaneous root

After the physical root was simultaneous, the next receive at process one is
locally compatible with both a strict-left round and another simultaneous
round.  Process two has the strict-right mirror ambiguity.  The two exact
one-sided controllers selected for these strict contingencies may not be
combined as a joint policy.  Only their receiver projections are used here.

The first two lemmas are the fail-fast seam: the two independently executable
receiver projections are componentwise equal to the literal common-world
output.  Thus a local state may retain one exact strict receiver together with
the single common continuation, without assuming equality of the two selected
policies and without storing a graph, orientation, or leader bit.
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

/-! ## Componentwise literal-output coherence -/

/-- The exact pinned-left receiver used by process one on its locally
ambiguous receive emits the literal common-world process-one output. -/
theorem profiledRawJointHybridInitialImmediateLeftReceiver_eq_commonOutputOne
    (first current : In₁ × In₂) :
    let shadowTwo :=
      (profiledRawJointHybridInitialRootRecvTwo A strategy hwin controllers
        first).2
    (profiledRawJointHybridInitialTwoShadowRecvOne A strategy hwin controllers
      shadowTwo .both current.1 current.2).1 =
      (profiledRawJointInitialCommonBothOutput A strategy
        (first, current)).1 := by
  dsimp only
  calc
    (profiledRawJointHybridInitialTwoShadowRecvOne A strategy hwin controllers
        (profiledRawJointHybridInitialRootRecvTwo A strategy hwin controllers
          first).2 .both current.1 current.2).1 =
        pairedLeftInformedForRow .both
          (profiledRawJointHybridInitialImmediateLeftRootRecord A strategy hwin
            first current).2.1.physical := by
      have hrecord :=
        profiledRawJointHybridInitialImmediateLeftController_rootRecord A
          strategy hwin first current
      have hout := congrArg
        (fun record ↦ pairedLeftInformedForRow .both record.2.1.physical)
        hrecord
      simpa [profiledRawJointHybridInitialTwoShadowRecvOne,
        profiledRawJointHybridInitialRootRecvTwo,
        profiledRawJointHybridInitialImmediateLeftRootStage,
        narrowedRecord, TransitionRationalTree.labeledTree,
        TransitionRationalTree.controlAt] using hout
    _ = (profiledRawJointInitialCommonBothOutput A strategy
          (first, current)).1 := by
      unfold profiledRawJointHybridInitialImmediateLeftRootRecord
      simp only [pairPlay, treePlay, treeOfPair, branchNode, blockLabelApply,
        senderWord, profiledRawJointGuardedFirstLeftReceiverStrategy,
        pairedLeftSenderStrategy]
      rw [profiledRawJointHybridInitialImmediateLeftActivation_lambda A
        strategy hwin first]
      rfl

/-- Process-two/right mirror. -/
theorem profiledRawJointHybridInitialImmediateRightReceiver_eq_commonOutputTwo
    (first current : In₁ × In₂) :
    let shadowOne :=
      (profiledRawJointHybridInitialRootRecvOne A strategy hwin controllers
        first).2
    (profiledRawJointHybridInitialOneShadowRecvTwo A strategy hwin controllers
      shadowOne .both current.2 current.1).1 =
      (profiledRawJointInitialCommonBothOutput A strategy
        (first, current)).2 := by
  dsimp only
  calc
    (profiledRawJointHybridInitialOneShadowRecvTwo A strategy hwin controllers
        (profiledRawJointHybridInitialRootRecvOne A strategy hwin controllers
          first).2 .both current.2 current.1).1 =
        pairedRightInformedForRow .both
          (profiledRawJointHybridInitialImmediateRightRootRecord A strategy hwin
            first (current.2, current.1)).2.1.physical := by
      have hrecord :=
        profiledRawJointHybridInitialImmediateRightController_rootRecord A
          strategy hwin first (current.2, current.1)
      have hout := congrArg
        (fun record ↦ pairedRightInformedForRow .both record.2.1.physical)
        hrecord
      simpa [profiledRawJointHybridInitialOneShadowRecvTwo,
        profiledRawJointHybridInitialRootRecvOne,
        profiledRawJointHybridInitialImmediateRightRootStage,
        narrowedRecord, TransitionRationalTree.labeledTree,
        TransitionRationalTree.controlAt] using hout
    _ = (profiledRawJointInitialCommonBothOutput A strategy
          (first, current)).2 := by
      unfold profiledRawJointHybridInitialImmediateRightRootRecord
      simp only [pairPlay, treePlay, treeOfPair, branchNode, blockLabelApply,
        senderWord, profiledRawJointGuardedFirstRightReceiverStrategy,
        pairedRightSenderStrategy]
      rw [profiledRawJointHybridInitialImmediateRightActivation_lambda A
        strategy hwin first]
      rfl

/-- Consequently, the two local receiver tables form the one literal common
output; no equality between their independently selected policies occurs in
the statement or proof. -/
theorem profiledRawJointHybridInitialImmediateReceivers_eq_commonOutput
    (first current : In₁ × In₂) :
    let shadowOne :=
      (profiledRawJointHybridInitialRootRecvOne A strategy hwin controllers
        first).2
    let shadowTwo :=
      (profiledRawJointHybridInitialRootRecvTwo A strategy hwin controllers
        first).2
    ((profiledRawJointHybridInitialTwoShadowRecvOne A strategy hwin controllers
        shadowTwo .both current.1 current.2).1,
      (profiledRawJointHybridInitialOneShadowRecvTwo A strategy hwin controllers
        shadowOne .both current.2 current.1).1) =
      profiledRawJointInitialCommonBothOutput A strategy (first, current) := by
  apply Prod.ext
  · exact
      profiledRawJointHybridInitialImmediateLeftReceiver_eq_commonOutputOne
        A strategy hwin controllers first current
  · exact
      profiledRawJointHybridInitialImmediateRightReceiver_eq_commonOutputTwo
        A strategy hwin controllers first current

/-! ## One finite common bank rooted below the literal second round -/

/-- The literal recursively common world after the two simultaneous rounds.
The index consists of two finite input pairs; it is not a stored view. -/
abbrev ProfiledRawJointHybridInitialSecondCommonWorld
    (key : ProfiledRawJointInitialCommonBothKey
      (In₁ := In₁) (In₂ := In₂)) :=
  profiledRawJointCommonWorldAfterBoth A
    (profiledRawJointInitialCommonBothWorld A strategy key) key.2

/-- Its finite hybrid code. -/
abbrev ProfiledRawJointHybridInitialSecondCommonCode
    (key : ProfiledRawJointInitialCommonBothKey
      (In₁ := In₁) (In₂ := In₂)) : ProfiledRawJointHybridCode A :=
  .common ((profiledRawJointCommonWorldFamily A
    (ProfiledRawJointHybridInitialSecondCommonWorld A strategy key)
    ).incidenceCode A)

/-- Select one ordinary finite policy at each of the finitely many exact
second-common roots.  Later common rounds update this one policy state; they
do not add another input-pair layer to the control type. -/
noncomputable def profiledRawJointHybridInitialSecondCommonPolicy
    (key : ProfiledRawJointInitialCommonBothKey
      (In₁ := In₁) (In₂ := In₂)) :
    ProfiledRawJointHybridProvenanceRationalPolicy A strategy
      (ProfiledRawJointHybridInitialSecondCommonCode A strategy key) :=
  Classical.choice
    (nonempty_profiledRawJointHybridProvenanceRationalPolicy A strategy hwin
      (ProfiledRawJointHybridInitialSecondCommonWorld A strategy key))

/-- Reachable root key of that fixed policy. -/
def profiledRawJointHybridInitialSecondCommonKey
    (key : ProfiledRawJointInitialCommonBothKey
      (In₁ := In₁) (In₂ := In₂)) :
    ProfiledRawJointHybridCommonPolicyKey A strategy
      (ProfiledRawJointHybridInitialSecondCommonCode A strategy key)
      (profiledRawJointHybridInitialSecondCommonPolicy A strategy hwin key)
    where
  incidenceCode :=
    (profiledRawJointCommonWorldFamily A
      (ProfiledRawJointHybridInitialSecondCommonWorld A strategy key)
      ).incidenceCode A
  state :=
    (profiledRawJointHybridInitialSecondCommonPolicy A strategy hwin key).run []
  reachable :=
    profiledRawJointHybridProvenancePolicy_initial_reachable A strategy
      (ProfiledRawJointHybridInitialSecondCommonCode A strategy key)
      (profiledRawJointHybridInitialSecondCommonPolicy A strategy hwin key)
  state_code := by
    have hroot :=
      (profiledRawJointHybridInitialSecondCommonPolicy A strategy hwin key
        ).accepts.1.1
    exact congrArg Prod.fst hroot

/-- Uniform finite alphabet for the exact common successor and every later
common state of the same selected policy. -/
abbrev ProfiledRawJointHybridInitialSecondCommonControl :=
  Σ key : ProfiledRawJointInitialCommonBothKey
      (In₁ := In₁) (In₂ := In₂),
    ProfiledRawJointHybridCommonPolicyKey A strategy
      (ProfiledRawJointHybridInitialSecondCommonCode A strategy key)
      (profiledRawJointHybridInitialSecondCommonPolicy A strategy hwin key)

noncomputable instance
    profiledRawJointHybridInitialSecondCommonControlFintype :
    Fintype (ProfiledRawJointHybridInitialSecondCommonControl A strategy hwin) :=
  by
  classical
  infer_instance

/-- Install the exact second-common root. -/
def profiledRawJointHybridInitialSecondCommonControl
    (key : ProfiledRawJointInitialCommonBothKey
      (In₁ := In₁) (In₂ := In₂)) :
    ProfiledRawJointHybridInitialSecondCommonControl A strategy hwin :=
  ⟨key, profiledRawJointHybridInitialSecondCommonKey A strategy hwin key⟩

/-- Invert the one installed move at a reachable second-common control. -/
noncomputable def profiledRawJointHybridInitialSecondCommonInstalled
    (control :
      ProfiledRawJointHybridInitialSecondCommonControl A strategy hwin) :
    ProfiledRawJointHybridCommonInstalledMove A strategy
      (ProfiledRawJointHybridInitialSecondCommonCode A strategy control.1)
      (profiledRawJointHybridInitialSecondCommonPolicy A strategy hwin
        control.1) control.2 :=
  Classical.choice
    (nonempty_profiledRawJointHybridCommonInstalledMove A strategy
      (ProfiledRawJointHybridInitialSecondCommonCode A strategy control.1)
      (profiledRawJointHybridInitialSecondCommonPolicy A strategy hwin
        control.1) control.2)

/-- A later simultaneous receive changes only the finite state of the fixed
second-common policy.  In particular the outer two-pair index is preserved. -/
noncomputable def profiledRawJointHybridInitialSecondCommonNext
    (control :
      ProfiledRawJointHybridInitialSecondCommonControl A strategy hwin)
    (input : In₁ × In₂) :
    ProfiledRawJointHybridInitialSecondCommonControl A strategy hwin :=
  ⟨control.1,
    (profiledRawJointHybridInitialSecondCommonInstalled A strategy hwin control
      ).simultaneousSuccessorKey A input⟩

omit [DecidableEq In₁] [DecidableEq In₂] [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem profiledRawJointHybridInitialSecondCommonNext_index
    (control :
      ProfiledRawJointHybridInitialSecondCommonControl A strategy hwin)
    (input : In₁ × In₂) :
    (profiledRawJointHybridInitialSecondCommonNext A strategy hwin control
      input).1 = control.1 :=
  rfl

/-! ## The two finite local ambiguity states -/

/-- Process one retains exactly the strict-left receiver contingency and the
finite key of the one common successor. -/
structure ProfiledRawJointHybridInitialSecondOneShadow where
  key : ProfiledRawJointInitialCommonBothKey
    (In₁ := In₁) (In₂ := In₂)
  strictReceiver :
    ProfiledRawJointHybridInitialImmediateLeftReceiverAt A strategy hwin key.1
  strictStage :
    ProfiledRawJointHybridInitialImmediateLeftStageAt A strategy hwin key.1

/-- Process-two mirror. -/
structure ProfiledRawJointHybridInitialSecondTwoShadow where
  key : ProfiledRawJointInitialCommonBothKey
    (In₁ := In₁) (In₂ := In₂)
  strictReceiver :
    ProfiledRawJointHybridInitialImmediateRightReceiverAt A strategy hwin key.1
  strictStage :
    ProfiledRawJointHybridInitialImmediateRightStageAt A strategy hwin key.1

noncomputable instance
    profiledRawJointHybridInitialSecondOneShadowFintype :
    Fintype
      (ProfiledRawJointHybridInitialSecondOneShadow A strategy hwin) := by
  classical
  let Rep := Σ key : ProfiledRawJointInitialCommonBothKey
      (In₁ := In₁) (In₂ := In₂),
    ProfiledRawJointHybridInitialImmediateLeftReceiverAt A strategy hwin key.1
      ×
    ProfiledRawJointHybridInitialImmediateLeftStageAt A strategy hwin key.1
  let equiv :
      ProfiledRawJointHybridInitialSecondOneShadow A strategy hwin ≃ Rep := {
    toFun := fun state ↦ ⟨state.key, state.strictReceiver, state.strictStage⟩
    invFun := fun state ↦ ⟨state.1, state.2.1, state.2.2⟩
    left_inv := by intro state; cases state; rfl
    right_inv := by intro state; rcases state with ⟨key, receiver, stage⟩; rfl }
  exact Fintype.ofEquiv Rep equiv.symm

noncomputable instance
    profiledRawJointHybridInitialSecondTwoShadowFintype :
    Fintype
      (ProfiledRawJointHybridInitialSecondTwoShadow A strategy hwin) := by
  classical
  let Rep := Σ key : ProfiledRawJointInitialCommonBothKey
      (In₁ := In₁) (In₂ := In₂),
    ProfiledRawJointHybridInitialImmediateRightReceiverAt A strategy hwin key.1
      ×
    ProfiledRawJointHybridInitialImmediateRightStageAt A strategy hwin key.1
  let equiv :
      ProfiledRawJointHybridInitialSecondTwoShadow A strategy hwin ≃ Rep := {
    toFun := fun state ↦ ⟨state.key, state.strictReceiver, state.strictStage⟩
    invFun := fun state ↦ ⟨state.1, state.2.1, state.2.2⟩
    left_inv := by intro state; cases state; rfl
    right_inv := by intro state; rcases state with ⟨key, receiver, stage⟩; rfl }
  exact Fintype.ofEquiv Rep equiv.symm

/-- The common branch retained by process one is an actual finite policy
control, derived from its finite key. -/
def ProfiledRawJointHybridInitialSecondOneShadow.common
    (shadow : ProfiledRawJointHybridInitialSecondOneShadow A strategy hwin) :
    ProfiledRawJointHybridInitialSecondCommonControl A strategy hwin :=
  profiledRawJointHybridInitialSecondCommonControl A strategy hwin shadow.key

/-- Process-two mirror. -/
def ProfiledRawJointHybridInitialSecondTwoShadow.common
    (shadow : ProfiledRawJointHybridInitialSecondTwoShadow A strategy hwin) :
    ProfiledRawJointHybridInitialSecondCommonControl A strategy hwin :=
  profiledRawJointHybridInitialSecondCommonControl A strategy hwin shadow.key

/-! ## Local construction on the second receive -/

/-- Process one's local second receive.  The delivered process-two root
shadow supplies the finite first pair; the current receive supplies the
second. -/
noncomputable def profiledRawJointHybridInitialToSecondOneShadow
    (delivered : ProfiledRawJointHybridInitialTwoShadow A strategy hwin
      controllers)
    (own : In₁) (deliveredInput : In₂) :
    Out₁ × ProfiledRawJointHybridInitialSecondOneShadow A strategy hwin :=
  let first := delivered.common.1
  let next := profiledRawJointHybridInitialTwoShadowRecvOne A strategy hwin
    controllers delivered .both own deliveredInput
  (next.1, ⟨(first, (own, deliveredInput)), next.2.receiver, next.2.stage⟩)

/-- Process-two mirror. -/
noncomputable def profiledRawJointHybridInitialToSecondTwoShadow
    (delivered : ProfiledRawJointHybridInitialOneShadow A strategy hwin
      controllers)
    (own : In₂) (deliveredInput : In₁) :
    Out₂ × ProfiledRawJointHybridInitialSecondTwoShadow A strategy hwin :=
  let first := delivered.common.1
  let next := profiledRawJointHybridInitialOneShadowRecvTwo A strategy hwin
    controllers delivered .both own deliveredInput
  (next.1, ⟨(first, (deliveredInput, own)), next.2.receiver, next.2.stage⟩)

/-- On the reachable initial simultaneous pair, the two locally constructed
shadows retain literally the same common-successor key. -/
@[simp] theorem profiledRawJointHybridInitialToSecondShadows_key_agree
    (first current : In₁ × In₂) :
    (profiledRawJointHybridInitialToSecondOneShadow A strategy hwin controllers
      (profiledRawJointHybridInitialRootRecvTwo A strategy hwin controllers
        first).2 current.1 current.2).2.key =
    (profiledRawJointHybridInitialToSecondTwoShadow A strategy hwin controllers
      (profiledRawJointHybridInitialRootRecvOne A strategy hwin controllers
        first).2 current.2 current.1).2.key :=
  rfl

/-- Their derived finite common controls therefore agree as well. -/
theorem profiledRawJointHybridInitialToSecondShadows_common_agree
    (first current : In₁ × In₂) :
    (profiledRawJointHybridInitialToSecondOneShadow A strategy hwin controllers
      (profiledRawJointHybridInitialRootRecvTwo A strategy hwin controllers
        first).2 current.1 current.2).2.common A strategy hwin =
    (profiledRawJointHybridInitialToSecondTwoShadow A strategy hwin controllers
      (profiledRawJointHybridInitialRootRecvOne A strategy hwin controllers
        first).2 current.2 current.1).2.common A strategy hwin :=
  rfl

/-- The executable construction emits the literal common output. -/
theorem profiledRawJointHybridInitialToSecondShadows_outputs
    (first current : In₁ × In₂) :
    ((profiledRawJointHybridInitialToSecondOneShadow A strategy hwin
        controllers
        (profiledRawJointHybridInitialRootRecvTwo A strategy hwin controllers
          first).2 current.1 current.2).1,
      (profiledRawJointHybridInitialToSecondTwoShadow A strategy hwin
        controllers
        (profiledRawJointHybridInitialRootRecvOne A strategy hwin controllers
          first).2 current.2 current.1).1) =
      profiledRawJointInitialCommonBothOutput A strategy (first, current) :=
  profiledRawJointHybridInitialImmediateReceivers_eq_commonOutput A strategy
    hwin controllers first current

/-- Each local output is definitionally the corresponding pinned strict
receiver output; the common equality above therefore adds no policy-coherence
premise. -/
theorem profiledRawJointHybridInitialToSecondOneShadow_strictOutput
    (delivered : ProfiledRawJointHybridInitialTwoShadow A strategy hwin
      controllers)
    (own : In₁) (deliveredInput : In₂) :
    (profiledRawJointHybridInitialToSecondOneShadow A strategy hwin controllers
      delivered own deliveredInput).1 =
    (profiledRawJointHybridInitialTwoShadowRecvOne A strategy hwin controllers
      delivered .both own deliveredInput).1 :=
  rfl

theorem profiledRawJointHybridInitialToSecondTwoShadow_strictOutput
    (delivered : ProfiledRawJointHybridInitialOneShadow A strategy hwin
      controllers)
    (own : In₂) (deliveredInput : In₁) :
    (profiledRawJointHybridInitialToSecondTwoShadow A strategy hwin controllers
      delivered own deliveredInput).1 =
    (profiledRawJointHybridInitialOneShadowRecvTwo A strategy hwin controllers
      delivered .both own deliveredInput).1 :=
  rfl

/-! ## Receive resolution into the ordinary common/strict pattern -/

/-- The policy-free common data consumed by both exact guards.  Naming this
projection once prevents dependent policy indices from being re-elaborated
through the old installed-move wrapper. -/
noncomputable def profiledRawJointHybridInitialSecondCommonMoveData
    (control :
      ProfiledRawJointHybridInitialSecondCommonControl A strategy hwin) :
    ProfiledRawJointHybridCommonMoveData A strategy :=
  (profiledRawJointHybridInitialSecondCommonInstalled A strategy hwin control
    ).toCommonMoveData A

/-- Exact left guard at a second-common control. -/
noncomputable def profiledRawJointHybridInitialSecondShadowLeftController
    (control :
      ProfiledRawJointHybridInitialSecondCommonControl A strategy hwin) :=
  profiledRawJointHybridExactLeftController A hwin
    (profiledRawJointHybridInitialSecondCommonMoveData A strategy hwin control)

/-- Right mirror. -/
noncomputable def profiledRawJointHybridInitialSecondShadowRightController
    (control :
      ProfiledRawJointHybridInitialSecondCommonControl A strategy hwin) :=
  profiledRawJointHybridExactRightController A hwin
    (profiledRawJointHybridInitialSecondCommonMoveData A strategy hwin control)

/-- The exact-left policy over the same policy-free data. -/
noncomputable def profiledRawJointHybridInitialSecondShadowLeftPolicy
    (control :
      ProfiledRawJointHybridInitialSecondCommonControl A strategy hwin) :=
  profiledRawJointHybridExactLeftPolicy A hwin
    (profiledRawJointHybridInitialSecondCommonMoveData A strategy hwin control)

/-- Right mirror. -/
noncomputable def profiledRawJointHybridInitialSecondShadowRightPolicy
    (control :
      ProfiledRawJointHybridInitialSecondCommonControl A strategy hwin) :=
  profiledRawJointHybridExactRightPolicy A hwin
    (profiledRawJointHybridInitialSecondCommonMoveData A strategy hwin control)

abbrev ProfiledRawJointHybridInitialSecondShadowLeftMonitor
    (control :
      ProfiledRawJointHybridInitialSecondCommonControl A strategy hwin) :=
  profiledRawJointHybridExactLeftMonitor.{u, v, x, y, s,
    max u v x y s} A
    (profiledRawJointHybridInitialSecondCommonMoveData A strategy hwin control)
    (profiledRawJointHybridInitialSecondShadowLeftPolicy A strategy hwin control)

abbrev ProfiledRawJointHybridInitialSecondShadowRightMonitor
    (control :
      ProfiledRawJointHybridInitialSecondCommonControl A strategy hwin) :=
  profiledRawJointHybridExactRightMonitor.{u, v, x, y, s,
    max u v x y s} A
    (profiledRawJointHybridInitialSecondCommonMoveData A strategy hwin control)
    (profiledRawJointHybridInitialSecondShadowRightPolicy A strategy hwin
      control)

/-- One root record of the exact left guard. -/
noncomputable def profiledRawJointHybridInitialSecondShadowLeftRootRecord
    (control :
      ProfiledRawJointHybridInitialSecondCommonControl A strategy hwin)
    (input : In₁ × In₂) :=
  let monitor :=
    ProfiledRawJointHybridInitialSecondShadowLeftMonitor A strategy hwin control
  let controller :=
    profiledRawJointHybridInitialSecondShadowLeftController A strategy hwin
      control
  narrowedRecord monitor (controller.labelOf controller.initial)
    monitor.initial input

/-- Right root record. -/
noncomputable def profiledRawJointHybridInitialSecondShadowRightRootRecord
    (control :
      ProfiledRawJointHybridInitialSecondCommonControl A strategy hwin)
    (input : In₁ × In₂) :=
  let monitor :=
    ProfiledRawJointHybridInitialSecondShadowRightMonitor A strategy hwin control
  let controller :=
    profiledRawJointHybridInitialSecondShadowRightController A strategy hwin
      control
  narrowedRecord monitor (controller.labelOf controller.initial)
    monitor.initial (input.2, input.1)

/-- The new left guarded root again emits the installed common output. -/
theorem profiledRawJointHybridInitialSecondShadowLeftRoot_output
    (control :
      ProfiledRawJointHybridInitialSecondCommonControl A strategy hwin)
    (input : In₁ × In₂) :
    pairedLeftInformedForRow .both
        (profiledRawJointHybridInitialSecondShadowLeftRootRecord A strategy hwin
          control input).2.1.physical =
      (profiledRawJointHybridInitialSecondCommonInstalled A strategy hwin
        control).bothOutputOne A input := by
  simpa [profiledRawJointHybridInitialSecondShadowLeftRootRecord,
    profiledRawJointHybridInitialSecondShadowLeftController,
    TransitionRationalTree.labeledTree, TransitionRationalTree.controlAt] using
    profiledRawJointHybridExactLeftController_root_output A hwin
      (profiledRawJointHybridInitialSecondCommonInstalled A strategy hwin
        control) input

/-- Right mirror. -/
theorem profiledRawJointHybridInitialSecondShadowRightRoot_output
    (control :
      ProfiledRawJointHybridInitialSecondCommonControl A strategy hwin)
    (input : In₁ × In₂) :
    pairedRightInformedForRow .both
        (profiledRawJointHybridInitialSecondShadowRightRootRecord A strategy
          hwin control input).2.1.physical =
      (profiledRawJointHybridInitialSecondCommonInstalled A strategy hwin
        control).bothOutputTwo A input := by
  simpa [profiledRawJointHybridInitialSecondShadowRightRootRecord,
    profiledRawJointHybridInitialSecondShadowRightController,
    TransitionRationalTree.labeledTree, TransitionRationalTree.controlAt] using
    profiledRawJointHybridExactRightController_root_output A hwin
      (profiledRawJointHybridInitialSecondCommonInstalled A strategy hwin
        control) (input.2, input.1)

/-- From the next receive onward, the local shadow has the stable generic
shape: one finite common origin/input and one exact strict receiver. -/
structure ProfiledRawJointHybridInitialSecondCommonOneShadow where
  origin : ProfiledRawJointHybridInitialSecondCommonControl A strategy hwin
  input : In₁ × In₂
  strictReceiver :
    (ProfiledRawJointHybridInitialSecondShadowLeftMonitor A strategy hwin
      origin).State

/-- Process-two mirror. -/
structure ProfiledRawJointHybridInitialSecondCommonTwoShadow where
  origin : ProfiledRawJointHybridInitialSecondCommonControl A strategy hwin
  input : In₁ × In₂
  strictReceiver :
    (ProfiledRawJointHybridInitialSecondShadowRightMonitor A strategy hwin
      origin).State

noncomputable instance
    profiledRawJointHybridInitialSecondCommonOneShadowFintype :
    Fintype
      (ProfiledRawJointHybridInitialSecondCommonOneShadow A strategy hwin) := by
  classical
  let Rep := Σ control :
      ProfiledRawJointHybridInitialSecondCommonControl A strategy hwin,
    (In₁ × In₂) ×
      (ProfiledRawJointHybridInitialSecondShadowLeftMonitor A strategy hwin
        control).State
  let equiv :
      ProfiledRawJointHybridInitialSecondCommonOneShadow A strategy hwin ≃
        Rep := {
    toFun := fun state ↦ ⟨state.origin, state.input, state.strictReceiver⟩
    invFun := fun state ↦ ⟨state.1, state.2.1, state.2.2⟩
    left_inv := by intro state; cases state; rfl
    right_inv := by intro state; rcases state with ⟨a, b, c⟩; rfl }
  exact Fintype.ofEquiv Rep equiv.symm

noncomputable instance
    profiledRawJointHybridInitialSecondCommonTwoShadowFintype :
    Fintype
      (ProfiledRawJointHybridInitialSecondCommonTwoShadow A strategy hwin) := by
  classical
  let Rep := Σ control :
      ProfiledRawJointHybridInitialSecondCommonControl A strategy hwin,
    (In₁ × In₂) ×
      (ProfiledRawJointHybridInitialSecondShadowRightMonitor A strategy hwin
        control).State
  let equiv :
      ProfiledRawJointHybridInitialSecondCommonTwoShadow A strategy hwin ≃
        Rep := {
    toFun := fun state ↦ ⟨state.origin, state.input, state.strictReceiver⟩
    invFun := fun state ↦ ⟨state.1, state.2.1, state.2.2⟩
    left_inv := by intro state; cases state; rfl
    right_inv := by intro state; rcases state with ⟨a, b, c⟩; rfl }
  exact Fintype.ofEquiv Rep equiv.symm

def ProfiledRawJointHybridInitialSecondCommonOneShadow.commonNext
    (shadow :
      ProfiledRawJointHybridInitialSecondCommonOneShadow A strategy hwin) :
    ProfiledRawJointHybridInitialSecondCommonControl A strategy hwin :=
  profiledRawJointHybridInitialSecondCommonNext A strategy hwin shadow.origin
    shadow.input

def ProfiledRawJointHybridInitialSecondCommonTwoShadow.commonNext
    (shadow :
      ProfiledRawJointHybridInitialSecondCommonTwoShadow A strategy hwin) :
    ProfiledRawJointHybridInitialSecondCommonControl A strategy hwin :=
  profiledRawJointHybridInitialSecondCommonNext A strategy hwin shadow.origin
    shadow.input

/-- Stable common-to-shadow transition for process one. -/
noncomputable def profiledRawJointHybridInitialSecondCommonToOneShadow
    (control :
      ProfiledRawJointHybridInitialSecondCommonControl A strategy hwin)
    (own : In₁) (delivered : In₂) :
    Out₁ ×
      ProfiledRawJointHybridInitialSecondCommonOneShadow A strategy hwin :=
  let input := (own, delivered)
  let monitor :=
    ProfiledRawJointHybridInitialSecondShadowLeftMonitor A strategy hwin control
  let record := profiledRawJointHybridInitialSecondShadowLeftRootRecord A
    strategy hwin control input
  ((profiledRawJointHybridInitialSecondCommonInstalled A strategy hwin control
    ).bothOutputOne A input,
    ⟨control, input, monitor.step monitor.initial record⟩)

/-- Stable process-two mirror. -/
noncomputable def profiledRawJointHybridInitialSecondCommonToTwoShadow
    (control :
      ProfiledRawJointHybridInitialSecondCommonControl A strategy hwin)
    (own : In₂) (delivered : In₁) :
    Out₂ ×
      ProfiledRawJointHybridInitialSecondCommonTwoShadow A strategy hwin :=
  let input := (delivered, own)
  let monitor :=
    ProfiledRawJointHybridInitialSecondShadowRightMonitor A strategy hwin
      control
  let record := profiledRawJointHybridInitialSecondShadowRightRootRecord A
    strategy hwin control input
  ((profiledRawJointHybridInitialSecondCommonInstalled A strategy hwin control
    ).bothOutputTwo A input,
    ⟨control, input, monitor.step monitor.initial record⟩)

/-- Receiving the partner's second-level ambiguity control certifies the
common predecessor branch and replaces it by the stable generic shape. -/
noncomputable def profiledRawJointHybridInitialSecondOneShadowRecvCommon
    (own : ProfiledRawJointHybridInitialSecondOneShadow A strategy hwin)
    (_delivered : ProfiledRawJointHybridInitialSecondTwoShadow A strategy hwin)
    (ownInput : In₁) (deliveredInput : In₂) :
    Out₁ ×
      ProfiledRawJointHybridInitialSecondCommonOneShadow A strategy hwin :=
  profiledRawJointHybridInitialSecondCommonToOneShadow A strategy hwin
    (own.common A strategy hwin) ownInput deliveredInput

/-- Process-two mirror. -/
noncomputable def profiledRawJointHybridInitialSecondTwoShadowRecvCommon
    (own : ProfiledRawJointHybridInitialSecondTwoShadow A strategy hwin)
    (_delivered : ProfiledRawJointHybridInitialSecondOneShadow A strategy hwin)
    (ownInput : In₂) (deliveredInput : In₁) :
    Out₂ ×
      ProfiledRawJointHybridInitialSecondCommonTwoShadow A strategy hwin :=
  profiledRawJointHybridInitialSecondCommonToTwoShadow A strategy hwin
    (own.common A strategy hwin) ownInput deliveredInput

/-- On a reachable common/common pair, the next receive emits the literal
output of the one installed common move. -/
theorem profiledRawJointHybridInitialSecondShadowRecvCommon_outputs
    (one : ProfiledRawJointHybridInitialSecondOneShadow A strategy hwin)
    (two : ProfiledRawJointHybridInitialSecondTwoShadow A strategy hwin)
    (hagrees : one.common A strategy hwin = two.common A strategy hwin)
    (input : In₁ × In₂) :
    ((profiledRawJointHybridInitialSecondOneShadowRecvCommon A strategy hwin
        one two input.1 input.2).1,
      (profiledRawJointHybridInitialSecondTwoShadowRecvCommon A strategy hwin
        two one input.2 input.1).1) =
      (profiledRawJointHybridInitialSecondCommonInstalled A strategy hwin
        (one.common A strategy hwin)).literalBothOutput A input := by
  change
    ((profiledRawJointHybridInitialSecondCommonInstalled A strategy hwin
        (one.common A strategy hwin)).bothOutputOne A input,
      (profiledRawJointHybridInitialSecondCommonInstalled A strategy hwin
        (two.common A strategy hwin)).bothOutputTwo A input) = _
  rw [← hagrees]
  exact (profiledRawJointHybridInitialSecondCommonInstalled A strategy hwin
    (one.common A strategy hwin)).bothOutputs_eq_literal A input

/-- Repeated simultaneous rounds do not create a third-level input index:
both stable shadows stay in the same second-common control alphabet. -/
theorem profiledRawJointHybridInitialSecondCommonToShadows_next_agree
    (control :
      ProfiledRawJointHybridInitialSecondCommonControl A strategy hwin)
    (input : In₁ × In₂) :
    (profiledRawJointHybridInitialSecondCommonToOneShadow A strategy hwin
      control input.1 input.2).2.commonNext A strategy hwin =
    (profiledRawJointHybridInitialSecondCommonToTwoShadow A strategy hwin
      control input.2 input.1).2.commonNext A strategy hwin :=
  rfl

/-! ## Resolution toward the pinned matched branch -/

/-- Reassemble process one's retained fields as the exact pinned-left
receiver that would have been installed on the indistinguishable strict-left
round. -/
def ProfiledRawJointHybridInitialSecondOneShadow.pinnedReceiver
    (shadow : ProfiledRawJointHybridInitialSecondOneShadow A strategy hwin) :
    ProfiledRawJointHybridInitialImmediateLeftReceiver A strategy hwin :=
  ⟨shadow.key.1, .both, shadow.strictReceiver, shadow.strictStage⟩

/-- Process-two/right mirror. -/
def ProfiledRawJointHybridInitialSecondTwoShadow.pinnedReceiver
    (shadow : ProfiledRawJointHybridInitialSecondTwoShadow A strategy hwin) :
    ProfiledRawJointHybridInitialImmediateRightReceiver A strategy hwin :=
  ⟨shadow.key.1, .both, shadow.strictReceiver, shadow.strictStage⟩

/-- If process one receives an honest pinned-left owner, the delivered control
resolves the preceding ambiguity and the existing exact matched controller
continues directly. -/
noncomputable def profiledRawJointHybridInitialSecondOneShadowRecvLeftOwner
    (shadow : ProfiledRawJointHybridInitialSecondOneShadow A strategy hwin)
    (owner : ProfiledRawJointHybridInitialImmediateLeftOwner A strategy hwin)
    (ownInput : In₁) (deliveredInput : In₂) :
    Out₁ × ProfiledRawJointHybridInitialImmediateLeftReceiver A strategy
      hwin :=
  profiledRawJointHybridInitialImmediateLeftReceiverRecvOwner A strategy hwin
    (shadow.pinnedReceiver A strategy hwin) owner ownInput deliveredInput

/-- Process-two/right mirror. -/
noncomputable def profiledRawJointHybridInitialSecondTwoShadowRecvRightOwner
    (shadow : ProfiledRawJointHybridInitialSecondTwoShadow A strategy hwin)
    (owner : ProfiledRawJointHybridInitialImmediateRightOwner A strategy hwin)
    (ownInput : In₂) (deliveredInput : In₁) :
    Out₂ × ProfiledRawJointHybridInitialImmediateRightReceiver A strategy
      hwin :=
  profiledRawJointHybridInitialImmediateRightReceiverRecvOwner A strategy hwin
    (shadow.pinnedReceiver A strategy hwin) owner ownInput deliveredInput

@[simp] theorem
    profiledRawJointHybridInitialSecondOneShadowRecvLeftOwner_first
    (shadow : ProfiledRawJointHybridInitialSecondOneShadow A strategy hwin)
    (owner : ProfiledRawJointHybridInitialImmediateLeftOwner A strategy hwin)
    (ownInput : In₁) (deliveredInput : In₂) :
    (profiledRawJointHybridInitialSecondOneShadowRecvLeftOwner A strategy hwin
      shadow owner ownInput deliveredInput).2.first = shadow.key.1 :=
  rfl

@[simp] theorem
    profiledRawJointHybridInitialSecondTwoShadowRecvRightOwner_first
    (shadow : ProfiledRawJointHybridInitialSecondTwoShadow A strategy hwin)
    (owner : ProfiledRawJointHybridInitialImmediateRightOwner A strategy hwin)
    (ownInput : In₂) (deliveredInput : In₁) :
    (profiledRawJointHybridInitialSecondTwoShadowRecvRightOwner A strategy hwin
      shadow owner ownInput deliveredInput).2.first = shadow.key.1 :=
  rfl

/-! ## Cross-handoff semantics of the staged strict child -/

/-- The exact child retained by the canonical pinned-left receiver is the
literal strict-left child of the one common move. -/
theorem profiledRawJointHybridInitialSecondOneShadow_child_eq_leftActual
    (first current : In₁ × In₂) :
    let shadow :=
      (profiledRawJointHybridInitialToSecondOneShadow A strategy hwin
        controllers
        (profiledRawJointHybridInitialRootRecvTwo A strategy hwin controllers
          first).2 current.1 current.2).2
    let family := profiledRawJointInitialCommonBothFamily A strategy
      (first, current)
    shadow.strictStage.child.1 =
      (family.leftActualChild A
        (profiledRawJointInitialCommonBothDirection (first, current)
          )).incidenceCode A := by
  dsimp only
  simp only [profiledRawJointHybridInitialToSecondOneShadow,
    profiledRawJointHybridInitialRootRecvTwo,
    profiledRawJointHybridInitialTwoShadowRecvOne]
  change
    (profiledRawJointHybridInitialImmediateLeftRootStage A strategy hwin first
      .both current).child.1 = _
  simp only [profiledRawJointHybridInitialImmediateLeftRootStage,
    profiledRawJointGuardedFirstLeftTarget_val]
  rw [profiledRawJointRootPinnedSelectedSource_code A strategy,
    profiledRawJointRootPinnedSelectedSource_move A strategy,
    profiledRawJointHybridInitialImmediateLeftPolicy_rootMove A strategy hwin]
  let world := profiledRawJointInitialCommonBothWorld A strategy
    (first, current)
  let family := profiledRawJointInitialCommonBothFamily A strategy
    (first, current)
  let direction := profiledRawJointInitialCommonBothDirection (first, current)
  let common := Classical.choice
    (nonempty_profiledRawJointCommonWorldBothRestartSource A world current)
  rw [family.leftActualChild_incidenceCode_eq A direction common]
  dsimp only [world, family, direction,
    profiledRawJointInitialCommonBothWorld,
    profiledRawJointInitialCommonBothFamily,
    ProfiledRawJointHybridInitialImmediateLeftSource]
  rw [(profiledRawJointInitialCommonBaseWorld A strategy first.1 first.2
    ).leftSingleton_code_eq_rightActual A
      ((profiledRawJointCommonWorldFamily A
        (profiledRawJointInitialCommonBaseWorld A strategy first.1 first.2)
        ).incidenceCode A) rfl]
  apply profiledRawJointLeftActualIncidenceNext_congr_active A
  · rfl
  · rfl
  · funext index
    cases index
    rfl
  · rfl
  · rfl
  · rfl

/-- Pinned-right mirror. -/
theorem profiledRawJointHybridInitialSecondTwoShadow_child_eq_rightActual
    (first current : In₁ × In₂) :
    let shadow :=
      (profiledRawJointHybridInitialToSecondTwoShadow A strategy hwin
        controllers
        (profiledRawJointHybridInitialRootRecvOne A strategy hwin controllers
          first).2 current.2 current.1).2
    let family := profiledRawJointInitialCommonBothFamily A strategy
      (first, current)
    shadow.strictStage.child.1 =
      (family.rightActualChild A
        (profiledRawJointInitialCommonBothDirection (first, current)
          )).incidenceCode A := by
  dsimp only
  simp only [profiledRawJointHybridInitialToSecondTwoShadow,
    profiledRawJointHybridInitialRootRecvOne,
    profiledRawJointHybridInitialOneShadowRecvTwo]
  change
    (profiledRawJointHybridInitialImmediateRightRootStage A strategy hwin first
      .both (current.2, current.1)).child.1 = _
  simp only [profiledRawJointHybridInitialImmediateRightRootStage,
    profiledRawJointGuardedFirstRightTarget_val]
  rw [profiledRawJointRootPinnedSelectedSource_code A strategy,
    profiledRawJointRootPinnedSelectedSource_move A strategy,
    profiledRawJointHybridInitialImmediateRightPolicy_rootMove A strategy hwin]
  let world := profiledRawJointInitialCommonBothWorld A strategy
    (first, current)
  let family := profiledRawJointInitialCommonBothFamily A strategy
    (first, current)
  let direction := profiledRawJointInitialCommonBothDirection (first, current)
  let common := Classical.choice
    (nonempty_profiledRawJointCommonWorldBothRestartSource A world current)
  rw [family.rightActualChild_incidenceCode_eq A direction common]
  dsimp only [world, family, direction,
    profiledRawJointInitialCommonBothWorld,
    profiledRawJointInitialCommonBothFamily,
    ProfiledRawJointHybridInitialImmediateRightSource]
  rw [(profiledRawJointInitialCommonBaseWorld A strategy first.1 first.2
    ).rightSingleton_code_eq_leftActual A
      ((profiledRawJointCommonWorldFamily A
        (profiledRawJointInitialCommonBaseWorld A strategy first.1 first.2)
        ).incidenceCode A) rfl]
  apply profiledRawJointRightActualIncidenceNext_congr_active A
  · rfl
  · rfl
  · funext index
    cases index
    rfl
  · rfl
  · rfl
  · rfl

/-! ## Exact live projections at the second-round boundary -/

/-- Although the process-one shadow retains the strict-left child, its live
process-two slot is exactly the slot of the literal recursively common child.
This is the only cross-branch datum needed at this boundary; it neither starts
a fresh policy nor compares children belonging to different rounds. -/
theorem profiledRawJointHybridInitialSecondOneShadow_liveRight_eq_common
    (first current : In₁ × In₂) :
    let shadow :=
      (profiledRawJointHybridInitialToSecondOneShadow A strategy hwin
        controllers
        (profiledRawJointHybridInitialRootRecvTwo A strategy hwin controllers
          first).2 current.1 current.2).2
    shadow.strictStage.child.1.family.right =
      ((profiledRawJointCommonWorldFamily A
        (ProfiledRawJointHybridInitialSecondCommonWorld A strategy
          (first, current))).incidenceCode A).family.right := by
  dsimp only
  calc
    _ = (((profiledRawJointInitialCommonBothFamily A strategy
          (first, current)).leftActualChild A
          (profiledRawJointInitialCommonBothDirection (first, current)
            )).incidenceCode A).family.right :=
      congrArg (fun code ↦ code.family.right)
        (profiledRawJointHybridInitialSecondOneShadow_child_eq_leftActual A
          strategy hwin controllers first current)
    _ = profiledRawJointInitialCommonBothOneReceiveChildControl A strategy
          first current.1 current.2 :=
      (profiledRawJointInitialCommonBoth_oneReceiveChildControl_eq_leftActual A
        strategy first current.1 current.2).symm
    _ = ((profiledRawJointCommonWorldFamily A
          (ProfiledRawJointHybridInitialSecondCommonWorld A strategy
            (first, current))).incidenceCode A).family.right := by
      dsimp only [profiledRawJointInitialCommonBothOneReceiveChildControl,
        profiledRawJointInitialCommonBothKeyOfOneReceive]
      rw [profiledRawJointInitialCommonBoth_jointChild_eq A strategy
        (first, current)]

/-- Process-two/right mirror: its retained strict-right child has the exact
live process-one slot of the same recursively common child. -/
theorem profiledRawJointHybridInitialSecondTwoShadow_liveLeft_eq_common
    (first current : In₁ × In₂) :
    let shadow :=
      (profiledRawJointHybridInitialToSecondTwoShadow A strategy hwin
        controllers
        (profiledRawJointHybridInitialRootRecvOne A strategy hwin controllers
          first).2 current.2 current.1).2
    shadow.strictStage.child.1.family.left =
      ((profiledRawJointCommonWorldFamily A
        (ProfiledRawJointHybridInitialSecondCommonWorld A strategy
          (first, current))).incidenceCode A).family.left := by
  dsimp only
  calc
    _ = (((profiledRawJointInitialCommonBothFamily A strategy
          (first, current)).rightActualChild A
          (profiledRawJointInitialCommonBothDirection (first, current)
            )).incidenceCode A).family.left :=
      congrArg (fun code ↦ code.family.left)
        (profiledRawJointHybridInitialSecondTwoShadow_child_eq_rightActual A
          strategy hwin controllers first current)
    _ = profiledRawJointInitialCommonBothTwoReceiveChildControl A strategy
          first current.2 current.1 :=
      (profiledRawJointInitialCommonBoth_twoReceiveChildControl_eq_rightActual A
        strategy first current.2 current.1).symm
    _ = ((profiledRawJointCommonWorldFamily A
          (ProfiledRawJointHybridInitialSecondCommonWorld A strategy
            (first, current))).incidenceCode A).family.left := by
      dsimp only [profiledRawJointInitialCommonBothTwoReceiveChildControl,
        profiledRawJointInitialCommonBothKeyOfTwoReceive]
      rw [profiledRawJointInitialCommonBoth_jointChild_eq A strategy
        (first, current)]

/-- The complete honest boundary certificate.  The two local shadows name
the same finite second-round key, and each strict contingency carries exactly
the live slot of the one literal common child.  Deliberately, this proposition
stops before a `recv`/`noRecv` controller is chosen: supplying that controller
requires persistence of the root-guarded policy and is the next theorem, not
an equality between a second-round and a third-round child. -/
theorem profiledRawJointHybridInitialSecond_liveProjectionCertificate
    (first current : In₁ × In₂) :
    let one :=
      (profiledRawJointHybridInitialToSecondOneShadow A strategy hwin
        controllers
        (profiledRawJointHybridInitialRootRecvTwo A strategy hwin controllers
          first).2 current.1 current.2).2
    let two :=
      (profiledRawJointHybridInitialToSecondTwoShadow A strategy hwin
        controllers
        (profiledRawJointHybridInitialRootRecvOne A strategy hwin controllers
          first).2 current.2 current.1).2
    let commonCode :=
      (profiledRawJointCommonWorldFamily A
        (ProfiledRawJointHybridInitialSecondCommonWorld A strategy
          (first, current))).incidenceCode A
    one.key = (first, current) ∧
      two.key = (first, current) ∧
      one.strictStage.child.1.family.right = commonCode.family.right ∧
      two.strictStage.child.1.family.left = commonCode.family.left := by
  dsimp only
  exact ⟨rfl, rfl,
    profiledRawJointHybridInitialSecondOneShadow_liveRight_eq_common A strategy
      hwin controllers first current,
    profiledRawJointHybridInitialSecondTwoShadow_liveLeft_eq_common A strategy
      hwin controllers first current⟩

end

end DetParityAutomaton

end DistributedSynthesis
