/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridInitialShadow
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledRawJointHybridExactRootGuard
import DistributedSynthesis.Formalizations.Theorem.ThmRootPinnedBlockNarrowing

/-!
# The exact paired phase below an ambiguous initial receive

The old exceptional controller and a generic common controller are selected
independently, so their blind labels are intentionally incomparable.  The
repair is one fresh controller indexed by the finite root input pair and
rooted at the literal one-sided lane of the post-root common world.  That
semantic lane already carries the two paired histories.  Root-pinning its
complete first record gives one blind behavior and two honest receiver rows:
`.first` for an immediate reversal after a strict root and `.both` for the
first strict block after a simultaneous root.

This is an exceptional finite phase, not the ordinary immediate-switch
policy family.  It persists through the homogeneous strict block and exposes
its own exact literal-child tag at the close.  No graph, orientation, leader
bit, or recursively nested shadow occurs in a runtime control.
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

/-! ## Literal paired sources and exact moves -/

abbrev ProfiledRawJointHybridInitialImmediateRightSource
    (first : In₁ × In₂) :=
  (profiledRawJointInitialCommonBaseWorld A strategy first.1 first.2
    ).oneSidedState A .right

abbrev ProfiledRawJointHybridInitialImmediateLeftSource
    (first : In₁ × In₂) :=
  (profiledRawJointInitialCommonBaseWorld A strategy first.1 first.2
    ).oneSidedState A .left

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
theorem profiledRawJointHybridInitialLeftBoundary_nil_eq_immediateRight
    (first : In₁ × In₂) :
    profiledRawJointInitialLeftBoundaryState A strategy [] first =
      ProfiledRawJointHybridInitialImmediateRightSource A strategy first :=
  rfl

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
theorem profiledRawJointHybridInitialRightBoundary_nil_eq_immediateLeft
    (first : In₁ × In₂) :
    profiledRawJointInitialRightBoundaryState A strategy []
        (first.2, first.1) =
      ProfiledRawJointHybridInitialImmediateLeftSource A strategy first :=
  rfl

def profiledRawJointHybridInitialImmediateRightRootPredicate
    (first : In₁ × In₂)
    (move : ProfiledRawJointLambdaFamilyMove A (I := Unit)) : Prop :=
  move =
    (ProfiledRawJointHybridInitialImmediateRightSource A strategy first).move A

def profiledRawJointHybridInitialImmediateLeftRootPredicate
    (first : In₁ × In₂)
    (move : ProfiledRawJointLambdaFamilyMove A (I := Unit)) : Prop :=
  move =
    (ProfiledRawJointHybridInitialImmediateLeftSource A strategy first).move A

omit [DecidableEq In₁] [DecidableEq In₂] [Inhabited Out₁] [Inhabited Out₂] in
theorem nonempty_profiledRawJointHybridInitialImmediateRightPolicy
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (first : In₁ × In₂) :
    Nonempty (ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      (ProfiledRawJointHybridInitialImmediateRightSource A strategy first)
      (profiledRawJointHybridInitialImmediateRightRootPredicate A strategy
        first)) :=
  nonempty_profiledRawJointOneSidedRootPinnedProvenancePolicy A strategy hwin
    (ProfiledRawJointHybridInitialImmediateRightSource A strategy first)
    (profiledRawJointHybridInitialImmediateRightRootPredicate A strategy first)
    rfl

omit [DecidableEq In₁] [DecidableEq In₂] [Inhabited Out₁] [Inhabited Out₂] in
theorem nonempty_profiledRawJointHybridInitialImmediateLeftPolicy
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (first : In₁ × In₂) :
    Nonempty (ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      (ProfiledRawJointHybridInitialImmediateLeftSource A strategy first)
      (profiledRawJointHybridInitialImmediateLeftRootPredicate A strategy
        first)) :=
  nonempty_profiledRawJointOneSidedRootPinnedProvenancePolicy A strategy hwin
    (ProfiledRawJointHybridInitialImmediateLeftSource A strategy first)
    (profiledRawJointHybridInitialImmediateLeftRootPredicate A strategy first)
    rfl

noncomputable def profiledRawJointHybridInitialImmediateRightPolicy
    (first : In₁ × In₂) :=
  Classical.choice
    (nonempty_profiledRawJointHybridInitialImmediateRightPolicy A strategy hwin
      first)

noncomputable def profiledRawJointHybridInitialImmediateLeftPolicy
    (first : In₁ × In₂) :=
  Classical.choice
    (nonempty_profiledRawJointHybridInitialImmediateLeftPolicy A strategy hwin
      first)

omit [DecidableEq In₁] [DecidableEq In₂] [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledRawJointHybridInitialImmediateRightPolicy_rootMove
    (first : In₁ × In₂) :
    (profiledRawJointHybridInitialImmediateRightPolicy A strategy hwin first
      ).rootMove =
      (ProfiledRawJointHybridInitialImmediateRightSource A strategy first
        ).move A :=
  (profiledRawJointHybridInitialImmediateRightPolicy A strategy hwin first
    ).rootMove_realizes.2.1

omit [DecidableEq In₁] [DecidableEq In₂] [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledRawJointHybridInitialImmediateLeftPolicy_rootMove
    (first : In₁ × In₂) :
    (profiledRawJointHybridInitialImmediateLeftPolicy A strategy hwin first
      ).rootMove =
      (ProfiledRawJointHybridInitialImmediateLeftSource A strategy first
        ).move A :=
  (profiledRawJointHybridInitialImmediateLeftPolicy A strategy hwin first
    ).rootMove_realizes.2.1

/-! ## Exact paired activations -/

noncomputable def profiledRawJointHybridInitialImmediateRightActivation
    (first : In₁ × In₂) :=
  Classical.choice
    (nonempty_profiledRawJointGuardedFirstRightBlockActivation A strategy
      (ProfiledRawJointHybridInitialImmediateRightSource A strategy first)
      (profiledRawJointHybridInitialImmediateRightRootPredicate A strategy
        first)
      (profiledRawJointHybridInitialImmediateRightPolicy A strategy hwin first)
      ((profiledRawJointInitialCommonBaseWorld A strategy first.1 first.2
        ).procOneSlot A) (by rfl))

noncomputable def profiledRawJointHybridInitialImmediateLeftActivation
    (first : In₁ × In₂) :=
  Classical.choice
    (nonempty_profiledRawJointGuardedFirstLeftBlockActivation A strategy
      (ProfiledRawJointHybridInitialImmediateLeftSource A strategy first)
      (profiledRawJointHybridInitialImmediateLeftRootPredicate A strategy
        first)
      (profiledRawJointHybridInitialImmediateLeftPolicy A strategy hwin first)
      ((profiledRawJointInitialCommonBaseWorld A strategy first.1 first.2
        ).procTwoSlot A) (by rfl))

omit [DecidableEq In₁] [DecidableEq In₂] [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledRawJointHybridInitialImmediateRightActivation_lambda
    (first : In₁ × In₂) :
    (profiledRawJointHybridInitialImmediateRightActivation A strategy hwin
      first).lambda =
      (profiledRawJointInitialCommonBaseWorld A strategy first.1 first.2
        |>.procOne A).lambdaOfStrategy := by
  have hselected :=
    (profiledRawJointHybridInitialImmediateRightActivation A strategy hwin
      first).lambda_selected
  rw [profiledRawJointHybridInitialImmediateRightPolicy_rootMove A strategy
    hwin first] at hselected
  exact Option.some.inj hselected.symm

omit [DecidableEq In₁] [DecidableEq In₂] [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledRawJointHybridInitialImmediateLeftActivation_lambda
    (first : In₁ × In₂) :
    (profiledRawJointHybridInitialImmediateLeftActivation A strategy hwin
      first).lambda =
      (profiledRawJointInitialCommonBaseWorld A strategy first.1 first.2
        |>.procTwo A).lambdaOfStrategy := by
  have hselected :=
    (profiledRawJointHybridInitialImmediateLeftActivation A strategy hwin
      first).lambda_selected
  rw [profiledRawJointHybridInitialImmediateLeftPolicy_rootMove A strategy
    hwin first] at hselected
  exact Option.some.inj hselected.symm

/-! ## Complete root-record pinning and finite controllers -/

abbrev ProfiledRawJointHybridInitialImmediateRightBaseMonitor
    (first : In₁ × In₂) :=
  profiledRawJointGuardedFirstRightBlockMonitor.{u, v, x, y, s,
    max u v x y s} A strategy
    (ProfiledRawJointHybridInitialImmediateRightSource A strategy first)
    (profiledRawJointHybridInitialImmediateRightRootPredicate A strategy first)
    (profiledRawJointHybridInitialImmediateRightPolicy A strategy hwin first)
    ((profiledRawJointInitialCommonBaseWorld A strategy first.1 first.2
      ).procOneSlot A)

abbrev ProfiledRawJointHybridInitialImmediateLeftBaseMonitor
    (first : In₁ × In₂) :=
  profiledRawJointGuardedFirstLeftBlockMonitor.{u, v, x, y, s,
    max u v x y s} A strategy
    (ProfiledRawJointHybridInitialImmediateLeftSource A strategy first)
    (profiledRawJointHybridInitialImmediateLeftRootPredicate A strategy first)
    (profiledRawJointHybridInitialImmediateLeftPolicy A strategy hwin first)
    ((profiledRawJointInitialCommonBaseWorld A strategy first.1 first.2
      ).procTwoSlot A)

noncomputable def profiledRawJointHybridInitialImmediateRightRootRecord
    (first : In₁ × In₂) (move : In₂ × In₁) :=
  pairPlay
    (profiledRawJointGuardedFirstRightReceiverStrategy A
      (profiledRawJointHybridInitialImmediateRightActivation A strategy hwin
        first))
    (pairedRightSenderStrategy
      (profiledRawJointHybridInitialImmediateRightActivation A strategy hwin
        first).lambda)
    (fun _ ↦ move) 0

noncomputable def profiledRawJointHybridInitialImmediateLeftRootRecord
    (first : In₁ × In₂) (move : In₁ × In₂) :=
  pairPlay
    (profiledRawJointGuardedFirstLeftReceiverStrategy A
      (profiledRawJointHybridInitialImmediateLeftActivation A strategy hwin
        first))
    (pairedLeftSenderStrategy
      (profiledRawJointHybridInitialImmediateLeftActivation A strategy hwin
        first).lambda)
    (fun _ ↦ move) 0

noncomputable def profiledRawJointHybridInitialImmediateRightMonitor
    (first : In₁ × In₂) :=
  (ProfiledRawJointHybridInitialImmediateRightBaseMonitor A strategy hwin first
    ).rootPinned
      (profiledRawJointHybridInitialImmediateRightRootRecord A strategy hwin
        first)

noncomputable def profiledRawJointHybridInitialImmediateLeftMonitor
    (first : In₁ × In₂) :=
  (ProfiledRawJointHybridInitialImmediateLeftBaseMonitor A strategy hwin first
    ).rootPinned
      (profiledRawJointHybridInitialImmediateLeftRootRecord A strategy hwin
        first)

theorem exists_profiledRawJointHybridInitialImmediateRightController
    (first : In₁ × In₂) :
    ∃ controller :
        TransitionRationalTree.{u, max u v x y s, max u v x y s} In₁
          (NarrowedBlockLabel In₂ In₁
            (ProfiledRawJointGuardedFirstRightReceiverOutput A strategy
              (ProfiledRawJointHybridInitialImmediateRightSource A strategy
                first)
              (profiledRawJointHybridInitialImmediateRightRootPredicate A
                strategy first)
              (profiledRawJointHybridInitialImmediateRightPolicy A strategy
                hwin first)) Out₁
            (profiledRawJointHybridInitialImmediateRightMonitor A strategy hwin
              first).State),
      NarrowedAllThreadsWin
        (profiledRawJointHybridInitialImmediateRightMonitor A strategy hwin
          first) controller.labeledTree := by
  let base :=
    ProfiledRawJointHybridInitialImmediateRightBaseMonitor A strategy hwin first
  let activation :=
    profiledRawJointHybridInitialImmediateRightActivation A strategy hwin first
  let receiver := profiledRawJointGuardedFirstRightReceiverStrategy A activation
  let sender := pairedRightSenderStrategy activation.lambda
  let expected :=
    profiledRawJointHybridInitialImmediateRightRootRecord A strategy hwin first
  have hbase : ∀ env : Nat → In₂ × In₁,
      base.WinsPlay (pairPlay receiver sender env) :=
    profiledRawJointGuardedFirstRightBlockMonitor_realizable A
      ((profiledRawJointInitialCommonBaseWorld A strategy first.1 first.2
        ).procOneSlot A) activation
  have hpinned : ∀ env : Nat → In₂ × In₁,
      (base.rootPinned expected).WinsPlay (pairPlay receiver sender env) :=
    base.rootPinned_realizable expected receiver sender hbase (by
      intro move
      rfl)
  exact (block_realizable_iff_implementable_controller_unconditional
    (base.rootPinned expected)).mp ⟨receiver, sender, hpinned⟩

theorem exists_profiledRawJointHybridInitialImmediateLeftController
    (first : In₁ × In₂) :
    ∃ controller :
        TransitionRationalTree.{v, max u v x y s, max u v x y s} In₂
          (NarrowedBlockLabel In₁ In₂
            (ProfiledRawJointGuardedFirstLeftReceiverOutput A strategy
              (ProfiledRawJointHybridInitialImmediateLeftSource A strategy
                first)
              (profiledRawJointHybridInitialImmediateLeftRootPredicate A
                strategy first)
              (profiledRawJointHybridInitialImmediateLeftPolicy A strategy
                hwin first)) Out₂
            (profiledRawJointHybridInitialImmediateLeftMonitor A strategy hwin
              first).State),
      NarrowedAllThreadsWin
        (profiledRawJointHybridInitialImmediateLeftMonitor A strategy hwin
          first) controller.labeledTree := by
  let base :=
    ProfiledRawJointHybridInitialImmediateLeftBaseMonitor A strategy hwin first
  let activation :=
    profiledRawJointHybridInitialImmediateLeftActivation A strategy hwin first
  let receiver := profiledRawJointGuardedFirstLeftReceiverStrategy A activation
  let sender := pairedLeftSenderStrategy activation.lambda
  let expected :=
    profiledRawJointHybridInitialImmediateLeftRootRecord A strategy hwin first
  have hbase : ∀ env : Nat → In₁ × In₂,
      base.WinsPlay (pairPlay receiver sender env) :=
    profiledRawJointGuardedFirstLeftBlockMonitor_realizable A
      ((profiledRawJointInitialCommonBaseWorld A strategy first.1 first.2
        ).procTwoSlot A) activation
  have hpinned : ∀ env : Nat → In₁ × In₂,
      (base.rootPinned expected).WinsPlay (pairPlay receiver sender env) :=
    base.rootPinned_realizable expected receiver sender hbase (by
      intro move
      rfl)
  exact (block_realizable_iff_implementable_controller_unconditional
    (base.rootPinned expected)).mp ⟨receiver, sender, hpinned⟩

noncomputable def profiledRawJointHybridInitialImmediateRightController
    (first : In₁ × In₂) :=
  Classical.choose
    (exists_profiledRawJointHybridInitialImmediateRightController A strategy
      hwin first)

noncomputable def profiledRawJointHybridInitialImmediateLeftController
    (first : In₁ × In₂) :=
  Classical.choose
    (exists_profiledRawJointHybridInitialImmediateLeftController A strategy
      hwin first)

theorem profiledRawJointHybridInitialImmediateRightController_wins
    (first : In₁ × In₂) :
    NarrowedAllThreadsWin
      (profiledRawJointHybridInitialImmediateRightMonitor A strategy hwin first)
      (profiledRawJointHybridInitialImmediateRightController A strategy hwin
        first).labeledTree :=
  Classical.choose_spec
    (exists_profiledRawJointHybridInitialImmediateRightController A strategy
      hwin first)

theorem profiledRawJointHybridInitialImmediateLeftController_wins
    (first : In₁ × In₂) :
    NarrowedAllThreadsWin
      (profiledRawJointHybridInitialImmediateLeftMonitor A strategy hwin first)
      (profiledRawJointHybridInitialImmediateLeftController A strategy hwin
        first).labeledTree :=
  Classical.choose_spec
    (exists_profiledRawJointHybridInitialImmediateLeftController A strategy
      hwin first)

theorem profiledRawJointHybridInitialImmediateRightController_rootRecord
    (first : In₁ × In₂) (move : In₂ × In₁) :
    narrowedRecord
        (profiledRawJointHybridInitialImmediateRightMonitor A strategy hwin
          first)
        ((profiledRawJointHybridInitialImmediateRightController A strategy hwin
          first).labeledTree [])
        (profiledRawJointHybridInitialImmediateRightMonitor A strategy hwin
          first).initial move =
      profiledRawJointHybridInitialImmediateRightRootRecord A strategy hwin
        first move :=
  (ProfiledRawJointHybridInitialImmediateRightBaseMonitor A strategy hwin first
    ).rootPinned_root_record
    (profiledRawJointHybridInitialImmediateRightRootRecord A strategy hwin first)
    (profiledRawJointHybridInitialImmediateRightController A strategy hwin first
      ).labeledTree
    (profiledRawJointHybridInitialImmediateRightController_wins A strategy hwin
      first) move

theorem profiledRawJointHybridInitialImmediateLeftController_rootRecord
    (first current : In₁ × In₂) :
    narrowedRecord
        (profiledRawJointHybridInitialImmediateLeftMonitor A strategy hwin first)
        ((profiledRawJointHybridInitialImmediateLeftController A strategy hwin
          first).labeledTree [])
        (profiledRawJointHybridInitialImmediateLeftMonitor A strategy hwin first
          ).initial current =
      profiledRawJointHybridInitialImmediateLeftRootRecord A strategy hwin first
        current :=
  (ProfiledRawJointHybridInitialImmediateLeftBaseMonitor A strategy hwin first
    ).rootPinned_root_record
    (profiledRawJointHybridInitialImmediateLeftRootRecord A strategy hwin first)
    (profiledRawJointHybridInitialImmediateLeftController A strategy hwin first
      ).labeledTree
    (profiledRawJointHybridInitialImmediateLeftController_wins A strategy hwin
      first) current

/-! ## Local one-round entry from the initial shadows -/

abbrev ProfiledRawJointHybridInitialImmediateRightOwnerAt
    (first : In₁ × In₂) :=
  (profiledRawJointHybridInitialImmediateRightController A strategy hwin first
    ).Control

abbrev ProfiledRawJointHybridInitialImmediateLeftOwnerAt
    (first : In₁ × In₂) :=
  (profiledRawJointHybridInitialImmediateLeftController A strategy hwin first
    ).Control

abbrev ProfiledRawJointHybridInitialImmediateRightReceiverAt
    (first : In₁ × In₂) :=
  (profiledRawJointHybridInitialImmediateRightMonitor A strategy hwin first
    ).State

abbrev ProfiledRawJointHybridInitialImmediateLeftReceiverAt
    (first : In₁ × In₂) :=
  (profiledRawJointHybridInitialImmediateLeftMonitor A strategy hwin first
    ).State

/-- The exact literal child staged by the right-block receiver after its most
recent receive.  This is dependent on the same finite root-pair index as the
controller and cannot be reconstructed from the projected monitor state. -/
abbrev ProfiledRawJointHybridInitialImmediateRightChildAt
    (first : In₁ × In₂) :=
  ProfiledRawJointOneSidedLiteralChildCode A strategy
    (profiledRawJointRootPinnedSelectedSource A strategy
      (ProfiledRawJointHybridInitialImmediateRightSource A strategy first)
      (profiledRawJointHybridInitialImmediateRightRootPredicate A strategy
        first)
      (profiledRawJointHybridInitialImmediateRightPolicy A strategy hwin first))

/-- Left-block staged-child mirror. -/
abbrev ProfiledRawJointHybridInitialImmediateLeftChildAt
    (first : In₁ × In₂) :=
  ProfiledRawJointOneSidedLiteralChildCode A strategy
    (profiledRawJointRootPinnedSelectedSource A strategy
      (ProfiledRawJointHybridInitialImmediateLeftSource A strategy first)
      (profiledRawJointHybridInitialImmediateLeftRootPredicate A strategy first)
      (profiledRawJointHybridInitialImmediateLeftPolicy A strategy hwin first))

/-- A staged right-block close retains not only the literal child code but
the live left slot needed to initialize its ordinary recurrent macro. -/
structure ProfiledRawJointHybridInitialImmediateRightStageAt
    (first : In₁ × In₂) where
  child :
    ProfiledRawJointHybridInitialImmediateRightChildAt A strategy hwin first
  slot : ProfiledRawLeftSlot A
  active_slot : child.1.family.left () = some slot

/-- Left-block mirror, whose closing recurrent macro has a live right slot. -/
structure ProfiledRawJointHybridInitialImmediateLeftStageAt
    (first : In₁ × In₂) where
  child :
    ProfiledRawJointHybridInitialImmediateLeftChildAt A strategy hwin first
  slot : ProfiledRawRightSlot A
  active_slot : child.1.family.right () = some slot

noncomputable instance
    profiledRawJointHybridInitialImmediateRightStageAtFintype
    (first : In₁ × In₂) :
    Fintype
      (ProfiledRawJointHybridInitialImmediateRightStageAt A strategy hwin
        first) := by
  classical
  let Rep := Σ child :
      ProfiledRawJointHybridInitialImmediateRightChildAt A strategy hwin first,
    { slot : ProfiledRawLeftSlot A //
      child.1.family.left () = some slot }
  let equiv :
      ProfiledRawJointHybridInitialImmediateRightStageAt A strategy hwin
          first ≃ Rep := {
    toFun := fun stage ↦ ⟨stage.child, stage.slot, stage.active_slot⟩
    invFun := fun stage ↦ ⟨stage.1, stage.2.1, stage.2.2⟩
    left_inv := by intro stage; cases stage; rfl
    right_inv := by
      intro stage
      rcases stage with ⟨child, slot, hslot⟩
      rfl }
  exact Fintype.ofEquiv Rep equiv.symm

noncomputable instance
    profiledRawJointHybridInitialImmediateLeftStageAtFintype
    (first : In₁ × In₂) :
    Fintype
      (ProfiledRawJointHybridInitialImmediateLeftStageAt A strategy hwin
        first) := by
  classical
  let Rep := Σ child :
      ProfiledRawJointHybridInitialImmediateLeftChildAt A strategy hwin first,
    { slot : ProfiledRawRightSlot A //
      child.1.family.right () = some slot }
  let equiv :
      ProfiledRawJointHybridInitialImmediateLeftStageAt A strategy hwin
          first ≃ Rep := {
    toFun := fun stage ↦ ⟨stage.child, stage.slot, stage.active_slot⟩
    invFun := fun stage ↦ ⟨stage.1, stage.2.1, stage.2.2⟩
    left_inv := by intro stage; cases stage; rfl
    right_inv := by
      intro stage
      rcases stage with ⟨child, slot, hslot⟩
      rfl }
  exact Fintype.ofEquiv Rep equiv.symm

/-- The exact stage at a semantic right root. -/
noncomputable def profiledRawJointHybridInitialImmediateRightRootStage
    (first : In₁ × In₂) (row : PairedEntryRow) (input : In₂ × In₁) :
    ProfiledRawJointHybridInitialImmediateRightStageAt A strategy hwin first :=
  let activation :=
    profiledRawJointHybridInitialImmediateRightActivation A strategy hwin first
  let child := profiledRawJointGuardedFirstRightTarget A strategy
    (ProfiledRawJointHybridInitialImmediateRightSource A strategy first)
    (profiledRawJointHybridInitialImmediateRightRootPredicate A strategy first)
    (profiledRawJointHybridInitialImmediateRightPolicy A strategy hwin first)
    row [] input
  let slot := profiledRawRightChildSlot A
    ((profiledRawJointInitialCommonBaseWorld A strategy first.1 first.2
      ).procOneSlot A) activation.lambda row [] input
  ⟨child, slot, activation.target_active_slot row [] input⟩

/-- Exact semantic left-root stage. -/
noncomputable def profiledRawJointHybridInitialImmediateLeftRootStage
    (first : In₁ × In₂) (row : PairedEntryRow) (input : In₁ × In₂) :
    ProfiledRawJointHybridInitialImmediateLeftStageAt A strategy hwin first :=
  let activation :=
    profiledRawJointHybridInitialImmediateLeftActivation A strategy hwin first
  let child := profiledRawJointGuardedFirstLeftTarget A strategy
    (ProfiledRawJointHybridInitialImmediateLeftSource A strategy first)
    (profiledRawJointHybridInitialImmediateLeftRootPredicate A strategy first)
    (profiledRawJointHybridInitialImmediateLeftPolicy A strategy hwin first)
    row [] input
  let slot := profiledRawLeftChildSlot A
    ((profiledRawJointInitialCommonBaseWorld A strategy first.1 first.2
      ).procTwoSlot A) activation.lambda row [] input
  ⟨child, slot, activation.target_active_slot row [] input⟩

/-- Totalize the stage constructor for an arbitrary controller target.  On a
live target it retains that target exactly; only an unreachable malformed
target takes the canonical exact-root fallback. -/
noncomputable def profiledRawJointHybridInitialImmediateRightStageOfChild
    (first : In₁ × In₂)
    (child : ProfiledRawJointHybridInitialImmediateRightChildAt A strategy hwin
      first) :
    ProfiledRawJointHybridInitialImmediateRightStageAt A strategy hwin first := by
  classical
  exact if h : ∃ slot : ProfiledRawLeftSlot A,
      child.1.family.left () = some slot then
    ⟨child, Classical.choose h, Classical.choose_spec h⟩
  else
    profiledRawJointHybridInitialImmediateRightRootStage A strategy hwin first
      .first (default, default)

/-- Left target totalization mirror. -/
noncomputable def profiledRawJointHybridInitialImmediateLeftStageOfChild
    (first : In₁ × In₂)
    (child : ProfiledRawJointHybridInitialImmediateLeftChildAt A strategy hwin
      first) :
    ProfiledRawJointHybridInitialImmediateLeftStageAt A strategy hwin first := by
  classical
  exact if h : ∃ slot : ProfiledRawRightSlot A,
      child.1.family.right () = some slot then
    ⟨child, Classical.choose h, Classical.choose_spec h⟩
  else
    profiledRawJointHybridInitialImmediateLeftRootStage A strategy hwin first
      .first (default, default)

omit [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem
    profiledRawJointHybridInitialImmediateRightStageOfChild_child_of_active
    (first : In₁ × In₂)
    (child : ProfiledRawJointHybridInitialImmediateRightChildAt A strategy hwin
      first)
    (h : ∃ slot : ProfiledRawLeftSlot A,
      child.1.family.left () = some slot) :
    (profiledRawJointHybridInitialImmediateRightStageOfChild A strategy hwin
      first child).child = child := by
  simp [profiledRawJointHybridInitialImmediateRightStageOfChild, h]

omit [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem
    profiledRawJointHybridInitialImmediateLeftStageOfChild_child_of_active
    (first : In₁ × In₂)
    (child : ProfiledRawJointHybridInitialImmediateLeftChildAt A strategy hwin
      first)
    (h : ∃ slot : ProfiledRawRightSlot A,
      child.1.family.right () = some slot) :
    (profiledRawJointHybridInitialImmediateLeftStageOfChild A strategy hwin
      first child).child = child := by
  simp [profiledRawJointHybridInitialImmediateLeftStageOfChild, h]

/-- Process one leaves its initial shadow for the shared exact right-block
owner. -/
structure ProfiledRawJointHybridInitialImmediateRightOwner where
  first : In₁ × In₂
  owner : ProfiledRawJointHybridInitialImmediateRightOwnerAt A strategy hwin
    first

/-- Process two's matched receiver control.  The proof-side row is part of
the ordinary paired receiver state, not a leader signal. -/
structure ProfiledRawJointHybridInitialImmediateRightReceiver where
  first : In₁ × In₂
  row : PairedEntryRow
  receiver :
    ProfiledRawJointHybridInitialImmediateRightReceiverAt A strategy hwin first
  stage :
    ProfiledRawJointHybridInitialImmediateRightStageAt A strategy hwin first

/-- Left-block owner at process two. -/
structure ProfiledRawJointHybridInitialImmediateLeftOwner where
  first : In₁ × In₂
  owner : ProfiledRawJointHybridInitialImmediateLeftOwnerAt A strategy hwin
    first

/-- Left-block receiver at process one. -/
structure ProfiledRawJointHybridInitialImmediateLeftReceiver where
  first : In₁ × In₂
  row : PairedEntryRow
  receiver :
    ProfiledRawJointHybridInitialImmediateLeftReceiverAt A strategy hwin first
  stage :
    ProfiledRawJointHybridInitialImmediateLeftStageAt A strategy hwin first

noncomputable instance
    profiledRawJointHybridInitialImmediateRightOwnerFintype :
    Fintype
      (ProfiledRawJointHybridInitialImmediateRightOwner A strategy hwin) := by
  classical
  let Rep := Σ first : In₁ × In₂,
    ProfiledRawJointHybridInitialImmediateRightOwnerAt A strategy hwin first
  let equiv :
      ProfiledRawJointHybridInitialImmediateRightOwner A strategy hwin ≃
        Rep := {
    toFun := fun state ↦ ⟨state.first, state.owner⟩
    invFun := fun state ↦ ⟨state.1, state.2⟩
    left_inv := by intro state; cases state; rfl
    right_inv := by intro state; rcases state with ⟨first, owner⟩; rfl }
  exact Fintype.ofEquiv Rep equiv.symm

noncomputable instance
    profiledRawJointHybridInitialImmediateRightReceiverFintype :
    Fintype
      (ProfiledRawJointHybridInitialImmediateRightReceiver A strategy hwin) := by
  classical
  let Rep := Σ first : In₁ × In₂, PairedEntryRow ×
    (ProfiledRawJointHybridInitialImmediateRightReceiverAt A strategy hwin first
      ×
    ProfiledRawJointHybridInitialImmediateRightStageAt A strategy hwin first)
  let equiv :
      ProfiledRawJointHybridInitialImmediateRightReceiver A strategy hwin ≃
        Rep := {
    toFun := fun state ↦
      ⟨state.first, state.row, state.receiver, state.stage⟩
    invFun := fun state ↦
      ⟨state.1, state.2.1, state.2.2.1, state.2.2.2⟩
    left_inv := by intro state; cases state; rfl
    right_inv := by
      intro state
      rcases state with ⟨first, row, receiver, stage⟩
      rfl }
  exact Fintype.ofEquiv Rep equiv.symm

noncomputable instance
    profiledRawJointHybridInitialImmediateLeftOwnerFintype :
    Fintype
      (ProfiledRawJointHybridInitialImmediateLeftOwner A strategy hwin) := by
  classical
  let Rep := Σ first : In₁ × In₂,
    ProfiledRawJointHybridInitialImmediateLeftOwnerAt A strategy hwin first
  let equiv :
      ProfiledRawJointHybridInitialImmediateLeftOwner A strategy hwin ≃ Rep := {
    toFun := fun state ↦ ⟨state.first, state.owner⟩
    invFun := fun state ↦ ⟨state.1, state.2⟩
    left_inv := by intro state; cases state; rfl
    right_inv := by intro state; rcases state with ⟨first, owner⟩; rfl }
  exact Fintype.ofEquiv Rep equiv.symm

noncomputable instance
    profiledRawJointHybridInitialImmediateLeftReceiverFintype :
    Fintype
      (ProfiledRawJointHybridInitialImmediateLeftReceiver A strategy hwin) := by
  classical
  let Rep := Σ first : In₁ × In₂, PairedEntryRow ×
    (ProfiledRawJointHybridInitialImmediateLeftReceiverAt A strategy hwin first
      ×
    ProfiledRawJointHybridInitialImmediateLeftStageAt A strategy hwin first)
  let equiv :
      ProfiledRawJointHybridInitialImmediateLeftReceiver A strategy hwin ≃
        Rep := {
    toFun := fun state ↦
      ⟨state.first, state.row, state.receiver, state.stage⟩
    invFun := fun state ↦
      ⟨state.1, state.2.1, state.2.2.1, state.2.2.2⟩
    left_inv := by intro state; cases state; rfl
    right_inv := by
      intro state
      rcases state with ⟨first, row, receiver, stage⟩
      rfl }
  exact Fintype.ofEquiv Rep equiv.symm

variable
  (controllers : ProfiledRawJointRootCompatibleInitialControllers A strategy)

/-- The ambiguous process-one `noRecv` starts and steps the one exact right
controller indexed by the root pair stored in its common candidate. -/
noncomputable def profiledRawJointHybridInitialOneShadowNoRecv
    (shadow : ProfiledRawJointHybridInitialOneShadow A strategy hwin
      controllers)
    (input : In₁) :
    Out₁ × ProfiledRawJointHybridInitialImmediateRightOwner A strategy hwin :=
  let first := shadow.common.1
  let controller :=
    profiledRawJointHybridInitialImmediateRightController A strategy hwin first
  let label := controller.labelOf controller.initial
  (label.1 input, ⟨first, controller.step controller.initial input⟩)

/-- Process two reconstructs the same exact right controller from the
delivered initial shadow and enters its paired receiver row. -/
noncomputable def profiledRawJointHybridInitialOneShadowRecvTwo
    (shadow : ProfiledRawJointHybridInitialOneShadow A strategy hwin
      controllers)
    (row : PairedEntryRow) (ownInput : In₂) (deliveredInput : In₁) :
    Out₂ ×
      ProfiledRawJointHybridInitialImmediateRightReceiver A strategy hwin :=
  let first := shadow.common.1
  let monitor :=
    profiledRawJointHybridInitialImmediateRightMonitor A strategy hwin first
  let controller :=
    profiledRawJointHybridInitialImmediateRightController A strategy hwin first
  let record := narrowedRecord monitor (controller.labeledTree [])
    monitor.initial (ownInput, deliveredInput)
  (pairedRightInformedForRow row record.2.1.physical,
    ⟨first, row, monitor.step monitor.initial record,
      profiledRawJointHybridInitialImmediateRightRootStage A strategy hwin
        first row (ownInput, deliveredInput)⟩)

/-- Process-two `noRecv` mirror. -/
noncomputable def profiledRawJointHybridInitialTwoShadowNoRecv
    (shadow : ProfiledRawJointHybridInitialTwoShadow A strategy hwin
      controllers)
    (input : In₂) :
    Out₂ × ProfiledRawJointHybridInitialImmediateLeftOwner A strategy hwin :=
  let first := shadow.common.1
  let controller :=
    profiledRawJointHybridInitialImmediateLeftController A strategy hwin first
  let label := controller.labelOf controller.initial
  (label.1 input, ⟨first, controller.step controller.initial input⟩)

/-- Process-one receiver mirror reconstructed from a delivered process-two
initial shadow. -/
noncomputable def profiledRawJointHybridInitialTwoShadowRecvOne
    (shadow : ProfiledRawJointHybridInitialTwoShadow A strategy hwin
      controllers)
    (row : PairedEntryRow) (ownInput : In₁) (deliveredInput : In₂) :
    Out₁ × ProfiledRawJointHybridInitialImmediateLeftReceiver A strategy hwin :=
  let first := shadow.common.1
  let monitor :=
    profiledRawJointHybridInitialImmediateLeftMonitor A strategy hwin first
  let controller :=
    profiledRawJointHybridInitialImmediateLeftController A strategy hwin first
  let record := narrowedRecord monitor (controller.labeledTree [])
    monitor.initial (ownInput, deliveredInput)
  (pairedLeftInformedForRow row record.2.1.physical,
    ⟨first, row, monitor.step monitor.initial record,
      profiledRawJointHybridInitialImmediateLeftRootStage A strategy hwin first
        row (ownInput, deliveredInput)⟩)

@[simp] theorem profiledRawJointHybridInitialOneShadowNoRecv_rootFirst
    (rootMove : In₁ × In₂) (input : In₁) :
    (profiledRawJointHybridInitialOneShadowNoRecv A strategy hwin controllers
      (profiledRawJointHybridInitialRootRecvOne A strategy hwin controllers
        rootMove).2 input).2.first = rootMove :=
  rfl

@[simp] theorem profiledRawJointHybridInitialTwoShadowNoRecv_rootFirst
    (rootMove : In₁ × In₂) (input : In₂) :
    (profiledRawJointHybridInitialTwoShadowNoRecv A strategy hwin controllers
      (profiledRawJointHybridInitialRootRecvTwo A strategy hwin controllers
        rootMove).2 input).2.first = rootMove :=
  rfl

/-- Both local right entries are literally the two projections of one root
record of one controller. -/
theorem profiledRawJointHybridInitialImmediateRight_localOutputs
    (shadow : ProfiledRawJointHybridInitialOneShadow A strategy hwin
      controllers)
    (row : PairedEntryRow) (current : In₁ × In₂) :
    ((profiledRawJointHybridInitialOneShadowNoRecv A strategy hwin controllers
        shadow current.1).1,
      (profiledRawJointHybridInitialOneShadowRecvTwo A strategy hwin
        controllers shadow row current.2 current.1).1) =
      let first := shadow.common.1
      let monitor :=
        profiledRawJointHybridInitialImmediateRightMonitor A strategy hwin first
      let controller :=
        profiledRawJointHybridInitialImmediateRightController A strategy hwin
          first
      let record := narrowedRecord monitor (controller.labeledTree [])
        monitor.initial (current.2, current.1)
      (record.2.2, pairedRightInformedForRow row record.2.1.physical) :=
  rfl

/-- Left local pair mirror. -/
theorem profiledRawJointHybridInitialImmediateLeft_localOutputs
    (shadow : ProfiledRawJointHybridInitialTwoShadow A strategy hwin
      controllers)
    (row : PairedEntryRow) (current : In₁ × In₂) :
    ((profiledRawJointHybridInitialTwoShadowRecvOne A strategy hwin controllers
        shadow row current.1 current.2).1,
      (profiledRawJointHybridInitialTwoShadowNoRecv A strategy hwin controllers
        shadow current.2).1) =
      let first := shadow.common.1
      let monitor :=
        profiledRawJointHybridInitialImmediateLeftMonitor A strategy hwin first
      let controller :=
        profiledRawJointHybridInitialImmediateLeftController A strategy hwin
          first
      let record := narrowedRecord monitor (controller.labeledTree [])
        monitor.initial current
      (pairedLeftInformedForRow row record.2.1.physical, record.2.2) :=
  rfl

/-- The two independently constructed right next controls retain exactly the
same finite root-pair index. -/
theorem profiledRawJointHybridInitialImmediateRight_nextFirst_agree
    (shadow : ProfiledRawJointHybridInitialOneShadow A strategy hwin
      controllers)
    (row : PairedEntryRow) (current : In₁ × In₂) :
    (profiledRawJointHybridInitialOneShadowNoRecv A strategy hwin controllers
      shadow current.1).2.first =
      (profiledRawJointHybridInitialOneShadowRecvTwo A strategy hwin
        controllers shadow row current.2 current.1).2.first :=
  rfl

/-- Left next-index agreement. -/
theorem profiledRawJointHybridInitialImmediateLeft_nextFirst_agree
    (shadow : ProfiledRawJointHybridInitialTwoShadow A strategy hwin
      controllers)
    (row : PairedEntryRow) (current : In₁ × In₂) :
    (profiledRawJointHybridInitialTwoShadowRecvOne A strategy hwin controllers
      shadow row current.1 current.2).2.first =
      (profiledRawJointHybridInitialTwoShadowNoRecv A strategy hwin controllers
        shadow current.2).2.first :=
  rfl

/-! ## Homogeneous continuation of the exact pinned block -/

/-- Align a delivered right-block owner with the receiver's finite root-pair
index.  Reachable pairs take the equality branch; the root fallback only
totalizes the local table on unreachable mismatched controls. -/
noncomputable def profiledRawJointHybridInitialImmediateRightOwnerFor
    (receiver : ProfiledRawJointHybridInitialImmediateRightReceiver A strategy
      hwin)
    (owner : ProfiledRawJointHybridInitialImmediateRightOwner A strategy hwin) :
    (profiledRawJointHybridInitialImmediateRightController A strategy hwin
      receiver.first).Control := by
  classical
  exact if h : owner.first = receiver.first then h ▸ owner.owner
    else (profiledRawJointHybridInitialImmediateRightController A strategy hwin
      receiver.first).initial

/-- Left-block owner alignment mirror. -/
noncomputable def profiledRawJointHybridInitialImmediateLeftOwnerFor
    (receiver : ProfiledRawJointHybridInitialImmediateLeftReceiver A strategy
      hwin)
    (owner : ProfiledRawJointHybridInitialImmediateLeftOwner A strategy hwin) :
    (profiledRawJointHybridInitialImmediateLeftController A strategy hwin
      receiver.first).Control := by
  classical
  exact if h : owner.first = receiver.first then h ▸ owner.owner
    else (profiledRawJointHybridInitialImmediateLeftController A strategy hwin
      receiver.first).initial

/-- Process one continues a homogeneous right block on `noRecv`. -/
noncomputable def profiledRawJointHybridInitialImmediateRightOwnerNoRecv
    (owner : ProfiledRawJointHybridInitialImmediateRightOwner A strategy hwin)
    (input : In₁) :
    Out₁ × ProfiledRawJointHybridInitialImmediateRightOwner A strategy hwin :=
  let controller :=
    profiledRawJointHybridInitialImmediateRightController A strategy hwin
      owner.first
  let label := controller.labelOf owner.owner
  (label.1 input, ⟨owner.first, controller.step owner.owner input⟩)

/-- Process two continues a homogeneous left block on `noRecv`. -/
noncomputable def profiledRawJointHybridInitialImmediateLeftOwnerNoRecv
    (owner : ProfiledRawJointHybridInitialImmediateLeftOwner A strategy hwin)
    (input : In₂) :
    Out₂ × ProfiledRawJointHybridInitialImmediateLeftOwner A strategy hwin :=
  let controller :=
    profiledRawJointHybridInitialImmediateLeftController A strategy hwin
      owner.first
  let label := controller.labelOf owner.owner
  (label.1 input, ⟨owner.first, controller.step owner.owner input⟩)

/-- Process two receives the delivered right-block owner, advances the exact
monitor, and refreshes the literal child staged for a possible close. -/
noncomputable def profiledRawJointHybridInitialImmediateRightReceiverRecvOwner
    (receiver : ProfiledRawJointHybridInitialImmediateRightReceiver A strategy
      hwin)
    (owner : ProfiledRawJointHybridInitialImmediateRightOwner A strategy hwin)
    (ownInput : In₂) (deliveredInput : In₁) :
    Out₂ ×
      ProfiledRawJointHybridInitialImmediateRightReceiver A strategy hwin :=
  let first := receiver.first
  let monitor :=
    profiledRawJointHybridInitialImmediateRightMonitor A strategy hwin first
  let controller :=
    profiledRawJointHybridInitialImmediateRightController A strategy hwin first
  let ownerControl :=
    profiledRawJointHybridInitialImmediateRightOwnerFor A strategy hwin
      receiver owner
  let label := controller.labelOf ownerControl
  let output := label.2 receiver.receiver (ownInput, deliveredInput)
  let record := ((ownInput, deliveredInput), output, label.1 deliveredInput)
  (pairedRightInformedForRow receiver.row output.physical,
    ⟨first, receiver.row, monitor.step receiver.receiver record,
      profiledRawJointHybridInitialImmediateRightStageOfChild A strategy hwin
        first (output.target receiver.row)⟩)

/-- Process-one/left-block receive mirror. -/
noncomputable def profiledRawJointHybridInitialImmediateLeftReceiverRecvOwner
    (receiver : ProfiledRawJointHybridInitialImmediateLeftReceiver A strategy
      hwin)
    (owner : ProfiledRawJointHybridInitialImmediateLeftOwner A strategy hwin)
    (ownInput : In₁) (deliveredInput : In₂) :
    Out₁ ×
      ProfiledRawJointHybridInitialImmediateLeftReceiver A strategy hwin :=
  let first := receiver.first
  let monitor :=
    profiledRawJointHybridInitialImmediateLeftMonitor A strategy hwin first
  let controller :=
    profiledRawJointHybridInitialImmediateLeftController A strategy hwin first
  let ownerControl :=
    profiledRawJointHybridInitialImmediateLeftOwnerFor A strategy hwin receiver
      owner
  let label := controller.labelOf ownerControl
  let output := label.2 receiver.receiver (ownInput, deliveredInput)
  let record := ((ownInput, deliveredInput), output, label.1 deliveredInput)
  (pairedLeftInformedForRow receiver.row output.physical,
    ⟨first, receiver.row, monitor.step receiver.receiver record,
      profiledRawJointHybridInitialImmediateLeftStageOfChild A strategy hwin
        first (output.target receiver.row)⟩)

@[simp] theorem
    profiledRawJointHybridInitialImmediateRightReceiverRecvOwner_first
    (receiver : ProfiledRawJointHybridInitialImmediateRightReceiver A strategy
      hwin)
    (owner : ProfiledRawJointHybridInitialImmediateRightOwner A strategy hwin)
    (ownInput : In₂) (deliveredInput : In₁) :
    (profiledRawJointHybridInitialImmediateRightReceiverRecvOwner A strategy
      hwin receiver owner ownInput deliveredInput).2.first = receiver.first :=
  rfl

@[simp] theorem
    profiledRawJointHybridInitialImmediateLeftReceiverRecvOwner_first
    (receiver : ProfiledRawJointHybridInitialImmediateLeftReceiver A strategy
      hwin)
    (owner : ProfiledRawJointHybridInitialImmediateLeftOwner A strategy hwin)
    (ownInput : In₁) (deliveredInput : In₂) :
    (profiledRawJointHybridInitialImmediateLeftReceiverRecvOwner A strategy
      hwin receiver owner ownInput deliveredInput).2.first = receiver.first :=
  rfl

end


end DetParityAutomaton

end DistributedSynthesis
