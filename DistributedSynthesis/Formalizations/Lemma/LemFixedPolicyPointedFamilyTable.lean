/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPointedFamilyTreeBranch
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledFixedPolicyObservableThread

/-!
# One finite table with fixed-policy parity and genuine pointed branches

The fixed hidden-policy monitor and descriptor-pointed successor totality are
orthogonal.  The former extracts one finite public table and proves parity for
every public word.  Winning the monitor also preserves nodewise public move
validity; the latter then follows the moves literally chosen by that same
table and constructs a genuine exact descriptor branch for every direction
word.

No semantic state representing an entire two-fibre family is selected.  The
actual descriptor is a proof-side cursor only, and the public table exposes
neither it nor an orientation or strict-leader bit.
-/

namespace DistributedSynthesis

universe c q fm dir dc i₁ i₂ o₁ o₂ pa

namespace DetParityAutomaton

variable {In₁ : Type i₁} {In₂ : Type i₂} {Out₁ : Type o₁} {Out₂ : Type o₂}
variable
  (A : DetParityAutomaton.{max i₁ i₂ o₁ o₂, pa}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]
variable {initialState : PairedProfiledTreeState A}
variable (policy :
  (pairedProfiledEntryRunAutomaton A initialState).RationalTransitionPolicy)

variable {Code : Type c} {MoveIdentity : Type q}
variable (D : DetParityAutomaton.{c, dc} Code)
variable {FamilyMove : Type fm} {Direction : Type dir}
variable [Fintype Code] [Fintype MoveIdentity]
variable [Fintype FamilyMove] [Fintype Direction] [Inhabited Direction]

variable
  (Represented : HiddenCodeControlDescriptor D
      (MoveIdentity := MoveIdentity) →
    HiddenDescriptorTwoFibreFamily D (MoveIdentity := MoveIdentity) → Prop)
  (Live : HiddenCodeControlDescriptor D
      (MoveIdentity := MoveIdentity) →
    HiddenDescriptorTwoFibreFamily D (MoveIdentity := MoveIdentity) → Prop)
  (ExactEdge : HiddenCodeControlDescriptor D
      (MoveIdentity := MoveIdentity) →
    FamilyMove → Direction →
      HiddenDescriptorTwoFibreFamily D (MoveIdentity := MoveIdentity) →
    HiddenCodeControlDescriptor D (MoveIdentity := MoveIdentity) → Prop)
  (Valid : HiddenDescriptorTwoFibreFamily D
      (MoveIdentity := MoveIdentity) → FamilyMove → Prop)
  (Supported : HiddenCodeControlDescriptor D
      (MoveIdentity := MoveIdentity) →
    HiddenDescriptorTwoFibreFamily D (MoveIdentity := MoveIdentity) →
    FamilyMove → Direction →
      HiddenDescriptorTwoFibreFamily D (MoveIdentity := MoveIdentity) → Prop)

variable [DecidableRel Valid]

private abbrev FamilyCode :=
  HiddenDescriptorTwoFibreFamily D (MoveIdentity := MoveIdentity)

private abbrev Observation := HiddenDescriptorTreeObservation
  (Direction := Direction)
  (FamilyCode := FamilyCode D (MoveIdentity := MoveIdentity))

private abbrev FixedPolicyFamilyMonitor
    (initialRoot : ProfiledFixedPolicyRoot A policy)
    (initialFamily : FamilyCode D (MoveIdentity := MoveIdentity)) :=
  observableThreadTreeMonitor
    (ProfiledFixedPolicyThreadState.system A policy
      (FamilyMove × Observation D (MoveIdentity := MoveIdentity)
        (Direction := Direction)) initialRoot)
    ((default : Direction), initialFamily)
    (fun observation move ↦ Valid observation.2 move)

/-- One literal finite public table carrying both independent certificates. -/
structure FixedPolicyPointedFamilyTablePackage
    (initialRoot : ProfiledFixedPolicyRoot A policy)
    (initialDescriptor : HiddenCodeControlDescriptor D
      (MoveIdentity := MoveIdentity))
    (initialFamily : FamilyCode D (MoveIdentity := MoveIdentity)) where
  table : RunParityTreeAutomaton.StateControlledTreeTable
    (FixedPolicyFamilyMonitor A policy D Valid initialRoot initialFamily
      (FamilyMove := FamilyMove) (Direction := Direction)).toRunAutomaton
  fixedPolicyWinning :
    (FixedPolicyFamilyMonitor A policy D Valid initialRoot initialFamily
      (FamilyMove := FamilyMove) (Direction := Direction)).WinningTree
        table.toTransitionRationalTree.labeledTree
  pointed : PointedFamilyTreeBranchPackage D Represented Live ExactEdge Valid
    Supported initialDescriptor initialFamily
  pointed_tree_eq : pointed.tree =
    table.toTransitionRationalTree.labeledTree

namespace FixedPolicyPointedFamilyTablePackage

variable
  {Represented Live ExactEdge Valid Supported}
  {initialRoot : ProfiledFixedPolicyRoot A policy}
  {initialDescriptor : HiddenCodeControlDescriptor D
    (MoveIdentity := MoveIdentity)}
  {initialFamily : FamilyCode D (MoveIdentity := MoveIdentity)}

/-- Every external direction word has a genuine pointed admissibility
certificate on the same finite table that wins the hidden fixed-policy
monitor. -/
noncomputable def pointedAdmissible
    (package : FixedPolicyPointedFamilyTablePackage A policy D Represented Live
      ExactEdge Valid Supported initialRoot initialDescriptor initialFamily)
    (branch : Nat → Direction) :
    PointedHiddenDescriptorFamilyWordAdmissible D Live ExactEdge Valid Supported
      initialDescriptor initialFamily
      (package.pointed.word D initialDescriptor initialFamily branch) :=
  package.pointed.admissible D initialDescriptor initialFamily branch

section
omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]

/-- In particular, the exact hidden-descriptor thread is nonempty on every
direction word; fixed-policy acceptance cannot be witnessed only by a dead
state. -/
theorem pointedContinuityThread_nonempty
    (package : FixedPolicyPointedFamilyTablePackage A policy D Represented Live
      ExactEdge Valid Supported initialRoot initialDescriptor initialFamily)
    (branch : Nat → Direction) :
    Nonempty (HiddenDescriptorContinuityThread D initialDescriptor ExactEdge
      (package.pointed.word D initialDescriptor initialFamily branch)) :=
  package.pointed.continuityThread_nonempty D initialDescriptor initialFamily
    branch

/-- The public word of the pointed certificate is literally a branch of the
finite table from `fixedPolicyWinning`. -/
theorem pointedWord_eq_tableBranch
    (package : FixedPolicyPointedFamilyTablePackage A policy D Represented Live
      ExactEdge Valid Supported initialRoot initialDescriptor initialFamily)
    (branch : Nat → Direction) :
    package.pointed.word D initialDescriptor initialFamily branch =
      observableThreadWord package.table.toTransitionRationalTree.labeledTree
        (package.pointed.observationBranch D initialDescriptor initialFamily
          branch) := by
  rw [← package.pointed_tree_eq]
  exact package.pointed.word_eq_observableThreadWord D initialDescriptor
    initialFamily branch

/-- Fixed-policy parity holds for every public observation branch of the
finite table, independently of the pointed coupling chosen below. -/
theorem fixedPolicy_accepts_tableBranch
    (package : FixedPolicyPointedFamilyTablePackage A policy D Represented Live
      ExactEdge Valid Supported initialRoot initialDescriptor initialFamily)
    (branch : Nat → Observation D (MoveIdentity := MoveIdentity)
      (Direction := Direction)) :
    (ProfiledFixedPolicyThreadState.system A policy
      (FamilyMove × Observation D (MoveIdentity := MoveIdentity)
        (Direction := Direction)) initialRoot).universalRunDPA.Accepts
      (observableThreadWord package.table.toTransitionRationalTree.labeledTree
        branch) :=
  ((observableThreadTreeMonitor_winning_iff
    (ProfiledFixedPolicyThreadState.system A policy
      (FamilyMove × Observation D (MoveIdentity := MoveIdentity)
        (Direction := Direction)) initialRoot)
    ((default : Direction), initialFamily)
    (fun observation move ↦ Valid observation.2 move)
    package.table.toTransitionRationalTree.labeledTree).mp
      package.fixedPolicyWinning).2 branch

end

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- The fixed hidden-policy universal automaton accepts the very same public
word that carries the genuine pointed exact thread. -/
theorem fixedPolicy_accepts_pointedWord
    (package : FixedPolicyPointedFamilyTablePackage A policy D Represented Live
      ExactEdge Valid Supported initialRoot initialDescriptor initialFamily)
    (branch : Nat → Direction) :
    (ProfiledFixedPolicyThreadState.system A policy
      (FamilyMove × Observation D (MoveIdentity := MoveIdentity)
        (Direction := Direction)) initialRoot).universalRunDPA.Accepts
      (package.pointed.word D initialDescriptor initialFamily branch) := by
  rw [package.pointedWord_eq_tableBranch A policy D branch]
  exact package.fixedPolicy_accepts_tableBranch A policy D
    (package.pointed.observationBranch D initialDescriptor initialFamily
      branch)

end FixedPolicyPointedFamilyTablePackage

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Extract one finite public table from any valid source tree and equip that
same table with a genuine pointed branch at every direction word. -/
theorem exists_fixedPolicyPointedFamilyTable_of_movesValid
    (initialRoot : ProfiledFixedPolicyRoot A policy)
    (hinitial : initialRoot.state A policy = policy.run [])
    (initialDescriptor : HiddenCodeControlDescriptor D
      (MoveIdentity := MoveIdentity))
    (initialFamily : FamilyCode D (MoveIdentity := MoveIdentity))
    (totality : PointedHiddenDescriptorFamilyTotality D Represented Live
      ExactEdge Valid Supported)
    (initialLive : Live initialDescriptor initialFamily)
    (sourceTree : LabeledTree
      (Observation D (MoveIdentity := MoveIdentity) (Direction := Direction))
      FamilyMove)
    (hvalid : ObservableMovesValid ((default : Direction), initialFamily)
      (fun observation move ↦ Valid observation.2 move) sourceTree) :
    ∃ package : FixedPolicyPointedFamilyTablePackage A policy D Represented
        Live ExactEdge Valid Supported initialRoot initialDescriptor
        initialFamily,
      ∀ branch : Nat → Direction,
        Nonempty (HiddenDescriptorContinuityThread D initialDescriptor ExactEdge
          (package.pointed.word D initialDescriptor initialFamily branch)) := by
  obtain ⟨table, hwinning⟩ :=
    ProfiledFixedPolicyThreadState.exists_finite_observableTable_of_movesValid
      A policy initialRoot hinitial ((default : Direction), initialFamily)
      (fun observation move ↦ Valid observation.2 move) sourceTree hvalid
  have htableValid : ObservableMovesValid
      ((default : Direction), initialFamily)
      (fun observation move ↦ Valid observation.2 move)
      table.toTransitionRationalTree.labeledTree :=
    observableThreadTreeMonitor_valid_of_winning
      (ProfiledFixedPolicyThreadState.system A policy
        (FamilyMove × Observation D (MoveIdentity := MoveIdentity)
          (Direction := Direction)) initialRoot)
      ((default : Direction), initialFamily)
      (fun observation move ↦ Valid observation.2 move)
      table.toTransitionRationalTree.labeledTree hwinning
  let pointed : PointedFamilyTreeBranchPackage D Represented Live ExactEdge
      Valid Supported initialDescriptor initialFamily :=
    { totality := totality
      initialLive := initialLive
      tree := table.toTransitionRationalTree.labeledTree
      movesValid := htableValid }
  let package : FixedPolicyPointedFamilyTablePackage A policy D Represented Live
      ExactEdge Valid Supported initialRoot initialDescriptor initialFamily :=
    { table := table
      fixedPolicyWinning := hwinning
      pointed := pointed
      pointed_tree_eq := rfl }
  refine ⟨package, ?_⟩
  intro branch
  exact package.pointedContinuityThread_nonempty A policy D branch

end

end DetParityAutomaton


end DistributedSynthesis
