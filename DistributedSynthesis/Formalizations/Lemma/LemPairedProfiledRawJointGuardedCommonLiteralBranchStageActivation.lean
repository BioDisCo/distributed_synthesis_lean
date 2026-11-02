/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteCrossAnchorLocalCarrierReachability
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralBranchAwareStagedFront
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralExactTablePhysicalPriority
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralHeterogeneousTailAcceptance

/-!
# Live stages on every reachable literal-seam table receive

The branch-aware receiver inspects the target coordinate selected by its
internal finite anchor.  This file proves that the resulting stage is never
`none` on a synchronized, locally reachable table round.  The false member is
live because its physical target belongs to the exact uniform descriptor;
the true member is live by the checked guarded-first target theorem.  The
generic local-reachability witness identifies the executable receive with the
corresponding member-table play at one finite prefix.

The statement is local and orientation-free at runtime: reachability is a
proof-side prefix witness and neither executable endpoint receives a graph,
leader bit, hierarchy side, history, or semantic view.
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

private abbrev CommonPoint :=
  ProfiledRawJointGuardedCommonSemanticPoint A strategy

private abbrev CrossValid :=
  ProfiledRawJointGuardedCommonLiteralCrossExtraValid A strategy hwin

namespace ProfiledRawJointGuardedCommonDecoratedPolicyPackage

variable {initial : CommonPoint A strategy}

private abbrev Package :=
  ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy hwin initial
    (CrossValid A strategy hwin)

/-! ## Active slots in both projections of the honest table play -/

/-- Every false right-seam table record carries a live right lane. -/
theorem
    exists_profiledRawJointLiteralRightBothExactFalsePlay_target_active_slot
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (env : Nat → In₁ × In₂) (n : Nat) (row : PairedEntryRow) :
    ∃ slot : ProfiledRawRightSlot A,
      ((profiledRawJointLiteralRightBothExactFalsePlay A strategy hwin
        installed env n).2.1.target row).family.right () = some slot := by
  classical
  let descriptor :=
    profiledRawJointHybridExactLeftUniformDescriptor A strategy hwin installed
  let play := profiledRawJointLiteralRightBothExactFalsePlay A strategy hwin
    installed env
  have hbase :
      (profiledRawJointLeftPhysicalSiblingMonitor A descriptor false).WinsPlay
        play := by
    simpa [descriptor, play] using
      (profiledRawJointLiteralRightBothExactFalsePlay_wins A strategy hwin
        installed env)
  have hallowed :=
    (profiledRawJointTargetLeft_targetsSafe_of_wins A
      (profiledRawJointUnitLeftTargetProjection A)
      (profiledRawJointLeftPhysicalSiblingAllowed A descriptor)
      descriptor.source play hbase n row).2
  change decide (∃ row' past input,
    (profiledRawJointGuardedFirstLeftTarget A strategy
      (installed.world.oneSidedState A .left)
      (profiledRawJointHybridExactLeftRootPredicate A installed)
      (profiledRawJointHybridExactLeftPolicy A hwin installed)
      row' past input).1 = (play n).2.1.target row) = true at hallowed
  rcases of_decide_eq_true hallowed with ⟨row', past, input, htarget⟩
  let activation := profiledRawJointHybridExactLeftActivation A hwin installed
  refine ⟨profiledRawLeftChildSlot A descriptor.source activation.lambda row'
    past input, ?_⟩
  rw [← htarget]
  simpa [activation, descriptor] using
    (activation.target_active_slot row' past input)

/-- The checked exact right-seam projection carries a live right lane at
every depth. -/
theorem
    exists_profiledRawJointLiteralRightBothExactTruePlay_target_active_slot
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (env : Nat → In₁ × In₂) (n : Nat) (row : PairedEntryRow) :
    ∃ slot : ProfiledRawRightSlot A,
      (((profiledRawJointLiteralRightBothExactTruePlay A strategy hwin
        installed env n).2.1.target row).1.family.right ()) = some slot := by
  obtain ⟨slot, hslot, _⟩ :=
    exists_profiledRawJointLiteralRightBothExactTruePlay_targetThreadPriority_eq_blockMin
      A strategy hwin installed env n row
  exact ⟨slot, hslot⟩

/-- False mirror-table records carry a live left lane. -/
theorem
    exists_profiledRawJointLiteralLeftBothExactFalsePlay_target_active_slot
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (env : Nat → In₂ × In₁) (n : Nat) (row : PairedEntryRow) :
    ∃ slot : ProfiledRawLeftSlot A,
      ((profiledRawJointLiteralLeftBothExactFalsePlay A strategy hwin
        installed env n).2.1.target row).family.left () = some slot := by
  classical
  let descriptor :=
    profiledRawJointHybridExactRightUniformDescriptor A strategy hwin installed
  let play := profiledRawJointLiteralLeftBothExactFalsePlay A strategy hwin
    installed env
  have hbase :
      (profiledRawJointRightPhysicalSiblingMonitor A descriptor false).WinsPlay
        play := by
    simpa [descriptor, play] using
      (profiledRawJointLiteralLeftBothExactFalsePlay_wins A strategy hwin
        installed env)
  have hallowed :=
    (profiledRawJointTargetRight_targetsSafe_of_wins A
      (profiledRawJointUnitRightTargetProjection A)
      (profiledRawJointRightPhysicalSiblingAllowed A descriptor)
      descriptor.source play hbase n row).2
  change decide (∃ row' past input,
    (profiledRawJointGuardedFirstRightTarget A strategy
      (installed.world.oneSidedState A .right)
      (profiledRawJointHybridExactRightRootPredicate A installed)
      (profiledRawJointHybridExactRightPolicy A hwin installed)
      row' past input).1 = (play n).2.1.target row) = true at hallowed
  rcases of_decide_eq_true hallowed with ⟨row', past, input, htarget⟩
  let activation := profiledRawJointHybridExactRightActivation A hwin installed
  refine ⟨profiledRawRightChildSlot A descriptor.source activation.lambda row'
    past input, ?_⟩
  rw [← htarget]
  simpa [activation, descriptor] using
    (activation.target_active_slot row' past input)

/-- Exact mirror projection: live left lane at every depth. -/
theorem
    exists_profiledRawJointLiteralLeftBothExactTruePlay_target_active_slot
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (env : Nat → In₂ × In₁) (n : Nat) (row : PairedEntryRow) :
    ∃ slot : ProfiledRawLeftSlot A,
      (((profiledRawJointLiteralLeftBothExactTruePlay A strategy hwin
        installed env n).2.1.target row).1.family.left ()) = some slot := by
  obtain ⟨slot, hslot, _⟩ :=
    exists_profiledRawJointLiteralLeftBothExactTruePlay_targetThreadPriority_eq_blockMin
      A strategy hwin installed env n row
  exact ⟨slot, hslot⟩

/-! ## Exact representation of the false target codes -/

/-- The false target is not merely live: the uniform descriptor represents
it by an exact tagged child of the same installed right seam. -/
theorem
    exists_literalRightSeamFalsePlay_target_eq_taggedTarget_code
    (package : Package A strategy hwin (initial := initial))
    (key : ProfiledRawJointGuardedCommonLiteralRightSeamKey A strategy hwin
      package)
    (env : Nat → In₁ × In₂) (n : Nat) (row : PairedEntryRow) :
    ∃ row' past input,
      (profiledRawJointLiteralRightBothExactFalsePlay A strategy hwin
        (package.literalRightSeamInstalled A strategy hwin key) env n
          ).2.1.target row =
        (package.literalRightSeamTaggedTarget A strategy hwin key row' past
          input).2.1 := by
  classical
  let installed := package.literalRightSeamInstalled A strategy hwin key
  let descriptor :=
    profiledRawJointHybridExactLeftUniformDescriptor A strategy hwin installed
  let play := profiledRawJointLiteralRightBothExactFalsePlay A strategy hwin
    installed env
  have hbase :
      (profiledRawJointLeftPhysicalSiblingMonitor A descriptor false).WinsPlay
        play := by
    simpa [descriptor, play, installed] using
      (profiledRawJointLiteralRightBothExactFalsePlay_wins A strategy hwin
        installed env)
  have hallowed :=
    (profiledRawJointTargetLeft_targetsSafe_of_wins A
      (profiledRawJointUnitLeftTargetProjection A)
      (profiledRawJointLeftPhysicalSiblingAllowed A descriptor)
      descriptor.source play hbase n row).2
  change decide (∃ row' past input,
    (profiledRawJointGuardedFirstLeftTarget A strategy
      (installed.world.oneSidedState A .left)
      (profiledRawJointHybridExactLeftRootPredicate A installed)
      (profiledRawJointHybridExactLeftPolicy A hwin installed)
      row' past input).1 = (play n).2.1.target row) = true at hallowed
  rcases of_decide_eq_true hallowed with ⟨row', past, input, htarget⟩
  refine ⟨row', past, input, ?_⟩
  simpa [play, installed, literalRightSeamTaggedTarget] using htarget.symm

/-- Mirror exact representation of every false target. -/
theorem
    exists_literalLeftSeamFalsePlay_target_eq_taggedTarget_code
    (package : Package A strategy hwin (initial := initial))
    (key : ProfiledRawJointGuardedCommonLiteralLeftSeamKey A strategy hwin
      package)
    (env : Nat → In₂ × In₁) (n : Nat) (row : PairedEntryRow) :
    ∃ row' past input,
      (profiledRawJointLiteralLeftBothExactFalsePlay A strategy hwin
        (package.literalLeftSeamInstalled A strategy hwin key) env n
          ).2.1.target row =
        (package.literalLeftSeamTaggedTarget A strategy hwin key row' past
          input).2.1 := by
  classical
  let installed := package.literalLeftSeamInstalled A strategy hwin key
  let descriptor :=
    profiledRawJointHybridExactRightUniformDescriptor A strategy hwin installed
  let play := profiledRawJointLiteralLeftBothExactFalsePlay A strategy hwin
    installed env
  have hbase :
      (profiledRawJointRightPhysicalSiblingMonitor A descriptor false).WinsPlay
        play := by
    simpa [descriptor, play, installed] using
      (profiledRawJointLiteralLeftBothExactFalsePlay_wins A strategy hwin
        installed env)
  have hallowed :=
    (profiledRawJointTargetRight_targetsSafe_of_wins A
      (profiledRawJointUnitRightTargetProjection A)
      (profiledRawJointRightPhysicalSiblingAllowed A descriptor)
      descriptor.source play hbase n row).2
  change decide (∃ row' past input,
    (profiledRawJointGuardedFirstRightTarget A strategy
      (installed.world.oneSidedState A .right)
      (profiledRawJointHybridExactRightRootPredicate A installed)
      (profiledRawJointHybridExactRightPolicy A hwin installed)
      row' past input).1 = (play n).2.1.target row) = true at hallowed
  rcases of_decide_eq_true hallowed with ⟨row', past, input, htarget⟩
  refine ⟨row', past, input, ?_⟩
  simpa [play, installed, literalLeftSeamTaggedTarget] using htarget.symm

/-! ## Product plays of the internally selected member -/

/-- The honest product-valued right-seam table play. -/
noncomputable def literalRightSeamHonestProductPlay
    (package : Package A strategy hwin (initial := initial))
    (key : ProfiledRawJointGuardedCommonLiteralRightSeamKey A strategy hwin
      package)
    (anchor : Bool) (env : Nat → In₁ × In₂) :
    Nat → RealizedBlockRound In₁ In₂
      (ProfiledRawJointLiteralRightBothExactProductReceiverOutput A strategy
        hwin (package.literalRightSeamInstalled A strategy hwin key)) Out₂ :=
  let installed := package.literalRightSeamInstalled A strategy hwin key
  let table :=
    profiledRawJointLiteralRightBothExactHeterogeneousLeftTable A strategy hwin
      installed
  let controller := table.memberController anchor
  treePlay (narrowedInducedTree _ controller.labeledTree) env

/-- Honest mirror product play. -/
noncomputable def literalLeftSeamHonestProductPlay
    (package : Package A strategy hwin (initial := initial))
    (key : ProfiledRawJointGuardedCommonLiteralLeftSeamKey A strategy hwin
      package)
    (anchor : Bool) (env : Nat → In₂ × In₁) :
    Nat → RealizedBlockRound In₂ In₁
      (ProfiledRawJointLiteralLeftBothExactProductReceiverOutput A strategy
        hwin (package.literalLeftSeamInstalled A strategy hwin key)) Out₁ :=
  let installed := package.literalLeftSeamInstalled A strategy hwin key
  let table :=
    profiledRawJointLiteralLeftBothExactHeterogeneousRightTable A strategy hwin
      installed
  let controller := table.memberController anchor
  treePlay (narrowedInducedTree _ controller.labeledTree) env

@[simp] theorem literalRightSeamHonestProductPlay_false_fst
    (package : Package A strategy hwin (initial := initial))
    (key : ProfiledRawJointGuardedCommonLiteralRightSeamKey A strategy hwin
      package)
    (env : Nat → In₁ × In₂) :
    BlockRecordMonitor.projectReceiverPlay Prod.fst
        (package.literalRightSeamHonestProductPlay A strategy hwin key false
          env) =
      profiledRawJointLiteralRightBothExactFalsePlay A strategy hwin
        (package.literalRightSeamInstalled A strategy hwin key) env := by
  rfl

@[simp] theorem literalRightSeamHonestProductPlay_true_snd
    (package : Package A strategy hwin (initial := initial))
    (key : ProfiledRawJointGuardedCommonLiteralRightSeamKey A strategy hwin
      package)
    (env : Nat → In₁ × In₂) :
    BlockRecordMonitor.projectReceiverPlay Prod.snd
        (package.literalRightSeamHonestProductPlay A strategy hwin key true
          env) =
      profiledRawJointLiteralRightBothExactTruePlay A strategy hwin
        (package.literalRightSeamInstalled A strategy hwin key) env := by
  rfl

@[simp] theorem literalLeftSeamHonestProductPlay_false_fst
    (package : Package A strategy hwin (initial := initial))
    (key : ProfiledRawJointGuardedCommonLiteralLeftSeamKey A strategy hwin
      package)
    (env : Nat → In₂ × In₁) :
    BlockRecordMonitor.projectReceiverPlay Prod.fst
        (package.literalLeftSeamHonestProductPlay A strategy hwin key false
          env) =
      profiledRawJointLiteralLeftBothExactFalsePlay A strategy hwin
        (package.literalLeftSeamInstalled A strategy hwin key) env := by
  rfl

@[simp] theorem literalLeftSeamHonestProductPlay_true_snd
    (package : Package A strategy hwin (initial := initial))
    (key : ProfiledRawJointGuardedCommonLiteralLeftSeamKey A strategy hwin
      package)
    (env : Nat → In₂ × In₁) :
    BlockRecordMonitor.projectReceiverPlay Prod.snd
        (package.literalLeftSeamHonestProductPlay A strategy hwin key true
          env) =
      profiledRawJointLiteralLeftBothExactTruePlay A strategy hwin
        (package.literalLeftSeamInstalled A strategy hwin key) env := by
  rfl

end ProfiledRawJointGuardedCommonDecoratedPolicyPackage

end

end DetParityAutomaton

end DistributedSynthesis
