/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridCommonFiniteSiblingMove
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointSiblingTargetIndexedKernel

/-!
# Synchronizing a recurrent common sibling close with its target key

At every reachable root-pinned common control and current input pair, the
common/strict sibling construction selects one finite narrowed table before
the two semantic children can choose independent policies.  Every target of
that table belongs to a finite relation depending on the common control and
current pair.  This file retains those two finite indices in one global child
key and feeds it into the existing target-indexed recurrent kernel.

Thus a later strict close does not select a fresh policy from its public code.
It installs the one policy already indexed by the exact checked table target.
The owner and receiver root constructors below have definitionally the same
global key.

The only proof-side invariant used below is ordinary matched-prefix
reachability: the owner control and receiver monitor state are the two folds
of one finite input prefix.  It is not a runtime field.  In particular, none
of the executable restart maps accepts a graph, an orientation, a sibling
member, or a leader bit.
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
  ProfiledRawJointHybridRootPinnedCommonControl A strategy hwin

/-! ## Prefix-local form of the finite right sibling table -/

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- At a finite prefix, the local owner/receiver evaluation is exactly the
corresponding node of the canonical narrowed tree. -/
theorem profiledRawJointRightPhysicalSibling_treePlay_at_prefix
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (past : List (In₂ × In₁)) (input : In₂ × In₁) :
    let monitor := profiledRawJointRightPhysicalSiblingMonitor A move.1 false
    let controller := move.memberController A false
    let env := omegaOfList (past ++ [input])
    treePlay (narrowedInducedTree monitor controller.labeledTree) env
        past.length =
      narrowedRecord monitor
        (controller.labelOf (controller.controlAt (senderWord past)))
        (narrowedControl monitor controller.labeledTree past) input := by
  dsimp only
  let finiteWord := past ++ [input]
  let env : Nat → In₂ × In₁ := omegaOfList finiteWord
  have hpast : omegaPrefix env past.length = past := by
    apply List.ext_get
    · simp [omegaPrefix]
    · intro n hnLeft hnRight
      rw [List.get_eq_getElem, List.get_eq_getElem]
      simp only [omegaPrefix, List.getElem_ofFn]
      have hnPrefix : n < finiteWord.length := by simp [finiteWord]; omega
      change omegaOfList finiteWord n = past[n]
      rw [omegaOfList_eq_getElem finiteWord n hnPrefix]
      simp [finiteWord, hnRight]
  have hinput : env past.length = input := by
    have hnPrefix : past.length < finiteWord.length := by simp [finiteWord]
    change omegaOfList finiteWord past.length = input
    rw [omegaOfList_eq_getElem finiteWord past.length hnPrefix]
    simp [finiteWord]
  simp [treePlay, narrowedInducedTree, blockLabelApply, narrowedRecord,
    TransitionRationalTree.labeledTree, branchNode_eq_omegaPrefix,
    hpast, hinput, senderWord, env, finiteWord]

/-! ## Left mirror -/

omit [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledRawJointLeftPhysicalSibling_treePlay_at_prefix
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (past : List (In₁ × In₂)) (input : In₁ × In₂) :
    let monitor := profiledRawJointLeftPhysicalSiblingMonitor A move.1 false
    let controller := move.memberController A false
    let env := omegaOfList (past ++ [input])
    treePlay (narrowedInducedTree monitor controller.labeledTree) env
        past.length =
      narrowedRecord monitor
        (controller.labelOf (controller.controlAt (senderWord past)))
        (narrowedControl monitor controller.labeledTree past) input := by
  dsimp only
  let finiteWord := past ++ [input]
  let env : Nat → In₁ × In₂ := omegaOfList finiteWord
  have hpast : omegaPrefix env past.length = past := by
    apply List.ext_get
    · simp [omegaPrefix]
    · intro n hnLeft hnRight
      rw [List.get_eq_getElem, List.get_eq_getElem]
      simp only [omegaPrefix, List.getElem_ofFn]
      have hnPrefix : n < finiteWord.length := by simp [finiteWord]; omega
      change omegaOfList finiteWord n = past[n]
      rw [omegaOfList_eq_getElem finiteWord n hnPrefix]
      simp [finiteWord, hnRight]
  have hinput : env past.length = input := by
    have hnPrefix : past.length < finiteWord.length := by simp [finiteWord]
    change omegaOfList finiteWord past.length = input
    rw [omegaOfList_eq_getElem finiteWord past.length hnPrefix]
    simp [finiteWord]
  simp [treePlay, narrowedInducedTree, blockLabelApply, narrowedRecord,
    TransitionRationalTree.labeledTree, branchNode_eq_omegaPrefix,
    hpast, hinput, senderWord, env, finiteWord]

/-! ## One global finite target family over all common exits -/

/-- A checked sibling target together with the common control and current
input pair which determine its finite target relation. -/
abbrev ProfiledRawJointHybridCommonSiblingTargetKey :=
  Σ control : CommonControl A strategy hwin,
    Σ current : In₁ × In₂,
      ProfiledRawJointSiblingTargetChildCode A strategy
        (profiledRawJointHybridCommonSiblingParentFamily A strategy hwin
          control)
        (profiledRawJointBothRestartDirection current)

noncomputable instance profiledRawJointHybridCommonSiblingTargetKeyFintype :
    Fintype
      (ProfiledRawJointHybridCommonSiblingTargetKey A strategy hwin) := by
  classical
  infer_instance

noncomputable instance
    profiledRawJointHybridCommonSiblingTargetKeyDecidableEq :
    DecidableEq
      (ProfiledRawJointHybridCommonSiblingTargetKey A strategy hwin) :=
  Classical.decEq _

/-- Embed a checked right-close target in the global recurrent family. -/
def profiledRawJointHybridCommonSiblingTargetOfRight
    (control : CommonControl A strategy hwin) (current : In₁ × In₂)
    (child : ProfiledRawJointRightSiblingChildCode A
      (profiledRawJointHybridCommonSiblingParentFamily A strategy hwin
        control)
      (profiledRawJointBothRestartDirection current)) :
    ProfiledRawJointHybridCommonSiblingTargetKey A strategy hwin :=
  ⟨control, current,
    profiledRawJointSiblingTargetChildOfRight A strategy
      (profiledRawJointHybridCommonSiblingParentFamily A strategy hwin
        control)
      (profiledRawJointBothRestartDirection current) child⟩

/-- Left-close mirror. -/
def profiledRawJointHybridCommonSiblingTargetOfLeft
    (control : CommonControl A strategy hwin) (current : In₁ × In₂)
    (child : ProfiledRawJointLeftSiblingChildCode A
      (profiledRawJointHybridCommonSiblingParentFamily A strategy hwin
        control)
      (profiledRawJointBothRestartDirection current)) :
    ProfiledRawJointHybridCommonSiblingTargetKey A strategy hwin :=
  ⟨control, current,
    profiledRawJointSiblingTargetChildOfLeft A strategy
      (profiledRawJointHybridCommonSiblingParentFamily A strategy hwin
        control)
      (profiledRawJointBothRestartDirection current) child⟩

/-- Literal one-sided semantic source represented by a global checked key. -/
noncomputable def profiledRawJointHybridCommonSiblingTargetSource
    (key : ProfiledRawJointHybridCommonSiblingTargetKey A strategy hwin) :
    ProfiledRawJointOneSidedSemanticState A strategy (I := Unit) :=
  profiledRawJointSiblingTargetChildSource A strategy
    (profiledRawJointHybridCommonSiblingParentFamily A strategy hwin key.1)
    (profiledRawJointBothRestartDirection key.2.1) key.2.2

include hwin in
/-- Select one recurrent policy once for every global checked target. -/
noncomputable def profiledRawJointHybridCommonSiblingTargetPolicy
    (key : ProfiledRawJointHybridCommonSiblingTargetKey A strategy hwin) :
    ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      ((profiledRawJointHybridCommonSiblingTargetSource A strategy hwin key
        ).code A) :=
  profiledRawJointSiblingTargetChildPolicy A strategy hwin
    (profiledRawJointHybridCommonSiblingParentFamily A strategy hwin key.1)
    (profiledRawJointBothRestartDirection key.2.1) key.2.2

/-- Complete recurrent controller bank at the checked target. -/
noncomputable def profiledRawJointHybridCommonSiblingTargetControllerBank
    (key : ProfiledRawJointHybridCommonSiblingTargetKey A strategy hwin) :
    ProfiledRawJointUnitPolicyControllerBank A strategy
      (profiledRawJointHybridCommonSiblingTargetSource A strategy hwin key)
      (profiledRawJointHybridCommonSiblingTargetPolicy A strategy hwin key) :=
  profiledRawJointUnitPolicyControllerBank A strategy
    (profiledRawJointHybridCommonSiblingTargetSource A strategy hwin key)
    (profiledRawJointHybridCommonSiblingTargetPolicy A strategy hwin key)

/-! ## Indexed recurrent local controls -/

abbrev ProfiledRawJointHybridCommonSiblingTargetRightOwner
    (key : ProfiledRawJointHybridCommonSiblingTargetKey A strategy hwin) :=
  ProfiledRawJointIndexedPolicyRightOwner A strategy
    (ProfiledRawJointHybridCommonSiblingTargetKey A strategy hwin)
    (profiledRawJointHybridCommonSiblingTargetSource A strategy hwin)
    (profiledRawJointHybridCommonSiblingTargetPolicy A strategy hwin)
    (profiledRawJointHybridCommonSiblingTargetControllerBank A strategy hwin)
    key

abbrev ProfiledRawJointHybridCommonSiblingTargetLeftReceiver
    (key : ProfiledRawJointHybridCommonSiblingTargetKey A strategy hwin) :=
  ProfiledRawJointIndexedPolicyLeftReceiver A strategy
    (ProfiledRawJointHybridCommonSiblingTargetKey A strategy hwin)
    (profiledRawJointHybridCommonSiblingTargetSource A strategy hwin)
    (profiledRawJointHybridCommonSiblingTargetPolicy A strategy hwin) key

abbrev ProfiledRawJointHybridCommonSiblingTargetRightReceiver
    (key : ProfiledRawJointHybridCommonSiblingTargetKey A strategy hwin) :=
  ProfiledRawJointIndexedPolicyRightReceiver A strategy
    (ProfiledRawJointHybridCommonSiblingTargetKey A strategy hwin)
    (profiledRawJointHybridCommonSiblingTargetSource A strategy hwin)
    (profiledRawJointHybridCommonSiblingTargetPolicy A strategy hwin) key

abbrev ProfiledRawJointHybridCommonSiblingTargetLeftOwner
    (key : ProfiledRawJointHybridCommonSiblingTargetKey A strategy hwin) :=
  ProfiledRawJointIndexedPolicyLeftOwner A strategy
    (ProfiledRawJointHybridCommonSiblingTargetKey A strategy hwin)
    (profiledRawJointHybridCommonSiblingTargetSource A strategy hwin)
    (profiledRawJointHybridCommonSiblingTargetPolicy A strategy hwin)
    (profiledRawJointHybridCommonSiblingTargetControllerBank A strategy hwin)
    key

/-! ## Definitionally synchronized close roots -/

/-- A checked right close initializes the next left owner at the global key
carrying the same common control, current pair, and checked target. -/
noncomputable def
    profiledRawJointHybridCommonRightTargetInitialLeftOwner
    (control : CommonControl A strategy hwin) (current : In₁ × In₂)
    (child : ProfiledRawJointRightSiblingChildCode A
      (profiledRawJointHybridCommonSiblingParentFamily A strategy hwin
        control)
      (profiledRawJointBothRestartDirection current))
    (package : ProfiledRawJointRightSiblingTargetChildRootPackage A strategy
      hwin
      (profiledRawJointHybridCommonSiblingParentFamily A strategy hwin control)
      (profiledRawJointBothRestartDirection current) child) :
    ProfiledRawJointHybridCommonSiblingTargetLeftOwner A strategy hwin
      (profiledRawJointHybridCommonSiblingTargetOfRight A strategy hwin
        control current child) :=
  package.initialLeftOwner A strategy hwin
    (profiledRawJointHybridCommonSiblingParentFamily A strategy hwin control)
    (profiledRawJointBothRestartDirection current) child

/-- Receiver-side root at literally the same global right-close key. -/
noncomputable def
    profiledRawJointHybridCommonRightTargetInitialLeftReceiver
    (control : CommonControl A strategy hwin) (current : In₁ × In₂)
    (child : ProfiledRawJointRightSiblingChildCode A
      (profiledRawJointHybridCommonSiblingParentFamily A strategy hwin
        control)
      (profiledRawJointBothRestartDirection current))
    (package : ProfiledRawJointRightSiblingTargetChildRootPackage A strategy
      hwin
      (profiledRawJointHybridCommonSiblingParentFamily A strategy hwin control)
      (profiledRawJointBothRestartDirection current) child)
    (row : PairedEntryRow) :
    ProfiledRawJointHybridCommonSiblingTargetLeftReceiver A strategy hwin
      (profiledRawJointHybridCommonSiblingTargetOfRight A strategy hwin
        control current child) :=
  package.initialLeftReceiver A strategy hwin
    (profiledRawJointHybridCommonSiblingParentFamily A strategy hwin control)
    (profiledRawJointBothRestartDirection current) child row

/-- Checked left-close owner root. -/
noncomputable def
    profiledRawJointHybridCommonLeftTargetInitialRightOwner
    (control : CommonControl A strategy hwin) (current : In₁ × In₂)
    (child : ProfiledRawJointLeftSiblingChildCode A
      (profiledRawJointHybridCommonSiblingParentFamily A strategy hwin
        control)
      (profiledRawJointBothRestartDirection current))
    (package : ProfiledRawJointLeftSiblingTargetChildRootPackage A strategy
      hwin
      (profiledRawJointHybridCommonSiblingParentFamily A strategy hwin control)
      (profiledRawJointBothRestartDirection current) child) :
    ProfiledRawJointHybridCommonSiblingTargetRightOwner A strategy hwin
      (profiledRawJointHybridCommonSiblingTargetOfLeft A strategy hwin
        control current child) :=
  package.initialRightOwner A strategy hwin
    (profiledRawJointHybridCommonSiblingParentFamily A strategy hwin control)
    (profiledRawJointBothRestartDirection current) child

/-- Receiver-side root at the same global left-close key. -/
noncomputable def
    profiledRawJointHybridCommonLeftTargetInitialRightReceiver
    (control : CommonControl A strategy hwin) (current : In₁ × In₂)
    (child : ProfiledRawJointLeftSiblingChildCode A
      (profiledRawJointHybridCommonSiblingParentFamily A strategy hwin
        control)
      (profiledRawJointBothRestartDirection current))
    (package : ProfiledRawJointLeftSiblingTargetChildRootPackage A strategy
      hwin
      (profiledRawJointHybridCommonSiblingParentFamily A strategy hwin control)
      (profiledRawJointBothRestartDirection current) child)
    (row : PairedEntryRow) :
    ProfiledRawJointHybridCommonSiblingTargetRightReceiver A strategy hwin
      (profiledRawJointHybridCommonSiblingTargetOfLeft A strategy hwin
        control current child) :=
  package.initialRightReceiver A strategy hwin
    (profiledRawJointHybridCommonSiblingParentFamily A strategy hwin control)
    (profiledRawJointBothRestartDirection current) child row

/-! ## Every concrete finite close supplies such a synchronized root -/

/-- At a concrete prefix of the right sibling table, its emitted target is a
checked right child and supplies the orientation-refined recurrent root
package.  This is the proof-side invariant needed by a local receiver state;
the executable receiver only stores the finite target. -/
theorem
    nonempty_profiledRawJointHybridCommonRightTargetRootPackage_at_prefix
    (control : CommonControl A strategy hwin) (current : In₁ × In₂)
    (past : List (In₂ × In₁)) (input : In₂ × In₁)
    (row : PairedEntryRow) :
    let family :=
      profiledRawJointHybridCommonSiblingParentFamily A strategy hwin control
    let direction := profiledRawJointBothRestartDirection current
    let move := profiledRawJointHybridCommonRightPhysicalSiblingMove A strategy
      hwin control current
    let monitor := profiledRawJointRightPhysicalSiblingMonitor A move.1 false
    let controller := move.memberController A false
    let env : Nat → In₂ × In₁ := omegaOfList (past ++ [input])
    let play := treePlay
      (narrowedInducedTree monitor controller.labeledTree) env
    ∃ child : ProfiledRawJointRightSiblingChildCode A family direction,
      child.1 = (play past.length).2.1.target row ∧
      Nonempty
        (ProfiledRawJointRightSiblingTargetChildRootPackage A strategy hwin
          family direction child) := by
  dsimp only
  let family :=
    profiledRawJointHybridCommonSiblingParentFamily A strategy hwin control
  let direction := profiledRawJointBothRestartDirection current
  let semanticMember :=
    (profiledRawJointHybridCommonSiblingWorld A strategy hwin control current
      ).procOneMember A
  let move := profiledRawJointHybridCommonRightPhysicalSiblingMove A strategy
    hwin control current
  let monitor := profiledRawJointRightPhysicalSiblingMonitor A move.1 false
  let controller := move.memberController A false
  let env : Nat → In₂ × In₁ := omegaOfList (past ++ [input])
  let play := treePlay
    (narrowedInducedTree monitor controller.labeledTree) env
  have hsafe := move.memberController_targetSafe A false env past.length row
  dsimp only at hsafe
  let target := (play past.length).2.1.target row
  have hallowed :
      ProfiledRawJointRightSiblingSharedAllowedTarget A family direction
        target := by
    have hphysicalAllowed := hsafe.2
    change profiledRawJointRightPhysicalSiblingAllowed A
        (profiledRawJointRightPhysicalSiblingDescriptorOf A family direction
          semanticMember) target at hphysicalAllowed
    exact
      (profiledRawJointRightPhysicalSiblingDescriptorOf_allowed_iff A family
        direction semanticMember target).mp hphysicalAllowed
  let child : ProfiledRawJointRightSiblingChildCode A family direction :=
    ⟨target, hallowed⟩
  refine ⟨child, rfl, ?_⟩
  exact
    nonempty_profiledRawJointRightSiblingTargetChildRootPackage_of_close A
      strategy hwin family direction child _ row _ hsafe.1

/-- Left-close mirror. -/
theorem
    nonempty_profiledRawJointHybridCommonLeftTargetRootPackage_at_prefix
    (control : CommonControl A strategy hwin) (current : In₁ × In₂)
    (past : List (In₁ × In₂)) (input : In₁ × In₂)
    (row : PairedEntryRow) :
    let family :=
      profiledRawJointHybridCommonSiblingParentFamily A strategy hwin control
    let direction := profiledRawJointBothRestartDirection current
    let move := profiledRawJointHybridCommonLeftPhysicalSiblingMove A strategy
      hwin control current
    let monitor := profiledRawJointLeftPhysicalSiblingMonitor A move.1 false
    let controller := move.memberController A false
    let env : Nat → In₁ × In₂ := omegaOfList (past ++ [input])
    let play := treePlay
      (narrowedInducedTree monitor controller.labeledTree) env
    ∃ child : ProfiledRawJointLeftSiblingChildCode A family direction,
      child.1 = (play past.length).2.1.target row ∧
      Nonempty
        (ProfiledRawJointLeftSiblingTargetChildRootPackage A strategy hwin
          family direction child) := by
  dsimp only
  let family :=
    profiledRawJointHybridCommonSiblingParentFamily A strategy hwin control
  let direction := profiledRawJointBothRestartDirection current
  let semanticMember :=
    (profiledRawJointHybridCommonSiblingWorld A strategy hwin control current
      ).procTwoMember A
  let move := profiledRawJointHybridCommonLeftPhysicalSiblingMove A strategy
    hwin control current
  let monitor := profiledRawJointLeftPhysicalSiblingMonitor A move.1 false
  let controller := move.memberController A false
  let env : Nat → In₁ × In₂ := omegaOfList (past ++ [input])
  let play := treePlay
    (narrowedInducedTree monitor controller.labeledTree) env
  have hsafe := move.memberController_targetSafe A false env past.length row
  dsimp only at hsafe
  let target := (play past.length).2.1.target row
  have hallowed :
      ProfiledRawJointLeftSiblingSharedAllowedTarget A family direction
        target := by
    have hphysicalAllowed := hsafe.2
    change profiledRawJointLeftPhysicalSiblingAllowed A
        (profiledRawJointLeftPhysicalSiblingDescriptorOf A family direction
          semanticMember) target at hphysicalAllowed
    exact
      (profiledRawJointLeftPhysicalSiblingDescriptorOf_allowed_iff A family
        direction semanticMember target).mp hphysicalAllowed
  let child : ProfiledRawJointLeftSiblingChildCode A family direction :=
    ⟨target, hallowed⟩
  refine ⟨child, rfl, ?_⟩
  exact
    nonempty_profiledRawJointLeftSiblingTargetChildRootPackage_of_close A
      strategy hwin family direction child _ row _ hsafe.1

end

end DetParityAutomaton

end DistributedSynthesis
