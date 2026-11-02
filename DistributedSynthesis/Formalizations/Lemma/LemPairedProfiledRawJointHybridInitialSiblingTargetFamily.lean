/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridInitialFiniteSiblingMove
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointSiblingTargetIndexedKernel

/-!
# The finite recurrent family below every initial sibling installation

An initial sibling table is selected from the two finite input pairs `first`
and `current`.  Its checked targets therefore belong to the target relation
for that same pair.  This module retains that finite provenance in the child
key and lifts the target-indexed recurrent kernel over all installations.

The pairs are ordinary inputs honestly known at installation and later
delivered with the finite control.  They are not a graph, orientation,
strict-leader, or hidden sibling tag.
-/

namespace DistributedSynthesis

universe u v x y s i₁ i₂ e₁ e₂

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

/-- A checked recurrent target together with the finite installation inputs
that determine its shared target relation. -/
abbrev ProfiledRawJointHybridInitialSiblingTargetKey :=
  Σ first : In₁ × In₂, Σ current : In₁ × In₂,
    ProfiledRawJointSiblingTargetChildCode A strategy
      (profiledRawJointHybridInitialSiblingParentFamily A strategy first)
      (profiledRawJointHybridInitialSiblingDirection current)

noncomputable instance profiledRawJointHybridInitialSiblingTargetKeyFintype :
    Fintype (ProfiledRawJointHybridInitialSiblingTargetKey A strategy) := by
  classical
  infer_instance

noncomputable instance
    profiledRawJointHybridInitialSiblingTargetKeyDecidableEq :
    DecidableEq (ProfiledRawJointHybridInitialSiblingTargetKey A strategy) :=
  Classical.decEq _

def profiledRawJointHybridInitialSiblingTargetOfRight
    (first current : In₁ × In₂)
    (child : ProfiledRawJointRightSiblingChildCode A
      (profiledRawJointHybridInitialSiblingParentFamily A strategy first)
      (profiledRawJointHybridInitialSiblingDirection current)) :
    ProfiledRawJointHybridInitialSiblingTargetKey A strategy :=
  ⟨first, current,
    profiledRawJointSiblingTargetChildOfRight A strategy
      (profiledRawJointHybridInitialSiblingParentFamily A strategy first)
      (profiledRawJointHybridInitialSiblingDirection current) child⟩

def profiledRawJointHybridInitialSiblingTargetOfLeft
    (first current : In₁ × In₂)
    (child : ProfiledRawJointLeftSiblingChildCode A
      (profiledRawJointHybridInitialSiblingParentFamily A strategy first)
      (profiledRawJointHybridInitialSiblingDirection current)) :
    ProfiledRawJointHybridInitialSiblingTargetKey A strategy :=
  ⟨first, current,
    profiledRawJointSiblingTargetChildOfLeft A strategy
      (profiledRawJointHybridInitialSiblingParentFamily A strategy first)
      (profiledRawJointHybridInitialSiblingDirection current) child⟩

/-- Exact semantic source represented by a global target key. -/
noncomputable def profiledRawJointHybridInitialSiblingTargetSource
    (key : ProfiledRawJointHybridInitialSiblingTargetKey A strategy) :
    ProfiledRawJointOneSidedSemanticState A strategy (I := Unit) :=
  profiledRawJointSiblingTargetChildSource A strategy
    (profiledRawJointHybridInitialSiblingParentFamily A strategy key.1)
    (profiledRawJointHybridInitialSiblingDirection key.2.1) key.2.2

include hwin in
/-- One fixed recurrent policy selected once for the global target key. -/
noncomputable def profiledRawJointHybridInitialSiblingTargetPolicy
    (key : ProfiledRawJointHybridInitialSiblingTargetKey A strategy) :
    ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      ((profiledRawJointHybridInitialSiblingTargetSource A strategy key).code
        A) :=
  profiledRawJointSiblingTargetChildPolicy A strategy hwin
    (profiledRawJointHybridInitialSiblingParentFamily A strategy key.1)
    (profiledRawJointHybridInitialSiblingDirection key.2.1) key.2.2

/-- Recurrent controller bank at every global target key. -/
noncomputable def profiledRawJointHybridInitialSiblingTargetControllerBank
    (key : ProfiledRawJointHybridInitialSiblingTargetKey A strategy) :
    ProfiledRawJointUnitPolicyControllerBank A strategy
      (profiledRawJointHybridInitialSiblingTargetSource A strategy key)
      (profiledRawJointHybridInitialSiblingTargetPolicy A strategy hwin key) :=
  profiledRawJointUnitPolicyControllerBank A strategy
    (profiledRawJointHybridInitialSiblingTargetSource A strategy key)
    (profiledRawJointHybridInitialSiblingTargetPolicy A strategy hwin key)

/-! ## Indexed recurrent controls and kernel -/

abbrev ProfiledRawJointHybridInitialSiblingTargetRightOwner
    (key : ProfiledRawJointHybridInitialSiblingTargetKey A strategy) :=
  ProfiledRawJointIndexedPolicyRightOwner A strategy
    (ProfiledRawJointHybridInitialSiblingTargetKey A strategy)
    (profiledRawJointHybridInitialSiblingTargetSource A strategy)
    (profiledRawJointHybridInitialSiblingTargetPolicy A strategy hwin)
    (profiledRawJointHybridInitialSiblingTargetControllerBank A strategy hwin)
    key

abbrev ProfiledRawJointHybridInitialSiblingTargetLeftReceiver
    (key : ProfiledRawJointHybridInitialSiblingTargetKey A strategy) :=
  ProfiledRawJointIndexedPolicyLeftReceiver A strategy
    (ProfiledRawJointHybridInitialSiblingTargetKey A strategy)
    (profiledRawJointHybridInitialSiblingTargetSource A strategy)
    (profiledRawJointHybridInitialSiblingTargetPolicy A strategy hwin) key

abbrev ProfiledRawJointHybridInitialSiblingTargetRightReceiver
    (key : ProfiledRawJointHybridInitialSiblingTargetKey A strategy) :=
  ProfiledRawJointIndexedPolicyRightReceiver A strategy
    (ProfiledRawJointHybridInitialSiblingTargetKey A strategy)
    (profiledRawJointHybridInitialSiblingTargetSource A strategy)
    (profiledRawJointHybridInitialSiblingTargetPolicy A strategy hwin) key

abbrev ProfiledRawJointHybridInitialSiblingTargetLeftOwner
    (key : ProfiledRawJointHybridInitialSiblingTargetKey A strategy) :=
  ProfiledRawJointIndexedPolicyLeftOwner A strategy
    (ProfiledRawJointHybridInitialSiblingTargetKey A strategy)
    (profiledRawJointHybridInitialSiblingTargetSource A strategy)
    (profiledRawJointHybridInitialSiblingTargetPolicy A strategy hwin)
    (profiledRawJointHybridInitialSiblingTargetControllerBank A strategy hwin)
    key

/-! ## Close installation in the global key family -/

/-- A checked front-right close initializes the global left owner at the key
carrying the same installation inputs and target. -/
noncomputable def profiledRawJointHybridInitialRightTargetInitialLeftOwner
    (first current : In₁ × In₂)
    (child : ProfiledRawJointRightSiblingChildCode A
      (profiledRawJointHybridInitialSiblingParentFamily A strategy first)
      (profiledRawJointHybridInitialSiblingDirection current))
    (package : ProfiledRawJointRightSiblingTargetChildRootPackage A strategy
      hwin (profiledRawJointHybridInitialSiblingParentFamily A strategy first)
        (profiledRawJointHybridInitialSiblingDirection current) child) :
    ProfiledRawJointHybridInitialSiblingTargetLeftOwner A strategy hwin
      (profiledRawJointHybridInitialSiblingTargetOfRight A strategy first
        current child) :=
  package.initialLeftOwner A strategy hwin
    (profiledRawJointHybridInitialSiblingParentFamily A strategy first)
    (profiledRawJointHybridInitialSiblingDirection current) child

/-- The receiving side installs the identical global key and row. -/
noncomputable def profiledRawJointHybridInitialRightTargetInitialLeftReceiver
    (first current : In₁ × In₂)
    (child : ProfiledRawJointRightSiblingChildCode A
      (profiledRawJointHybridInitialSiblingParentFamily A strategy first)
      (profiledRawJointHybridInitialSiblingDirection current))
    (package : ProfiledRawJointRightSiblingTargetChildRootPackage A strategy
      hwin (profiledRawJointHybridInitialSiblingParentFamily A strategy first)
        (profiledRawJointHybridInitialSiblingDirection current) child)
    (row : PairedEntryRow) :
    ProfiledRawJointHybridInitialSiblingTargetLeftReceiver A strategy hwin
      (profiledRawJointHybridInitialSiblingTargetOfRight A strategy first
        current child) :=
  package.initialLeftReceiver A strategy hwin
    (profiledRawJointHybridInitialSiblingParentFamily A strategy first)
    (profiledRawJointHybridInitialSiblingDirection current) child row

/-- Checked front-left mirror: initialize the global right owner. -/
noncomputable def profiledRawJointHybridInitialLeftTargetInitialRightOwner
    (first current : In₁ × In₂)
    (child : ProfiledRawJointLeftSiblingChildCode A
      (profiledRawJointHybridInitialSiblingParentFamily A strategy first)
      (profiledRawJointHybridInitialSiblingDirection current))
    (package : ProfiledRawJointLeftSiblingTargetChildRootPackage A strategy
      hwin (profiledRawJointHybridInitialSiblingParentFamily A strategy first)
        (profiledRawJointHybridInitialSiblingDirection current) child) :
    ProfiledRawJointHybridInitialSiblingTargetRightOwner A strategy hwin
      (profiledRawJointHybridInitialSiblingTargetOfLeft A strategy first
        current child) :=
  package.initialRightOwner A strategy hwin
    (profiledRawJointHybridInitialSiblingParentFamily A strategy first)
    (profiledRawJointHybridInitialSiblingDirection current) child

/-- Checked front-left receiving-side mirror. -/
noncomputable def profiledRawJointHybridInitialLeftTargetInitialRightReceiver
    (first current : In₁ × In₂)
    (child : ProfiledRawJointLeftSiblingChildCode A
      (profiledRawJointHybridInitialSiblingParentFamily A strategy first)
      (profiledRawJointHybridInitialSiblingDirection current))
    (package : ProfiledRawJointLeftSiblingTargetChildRootPackage A strategy
      hwin (profiledRawJointHybridInitialSiblingParentFamily A strategy first)
        (profiledRawJointHybridInitialSiblingDirection current) child)
    (row : PairedEntryRow) :
    ProfiledRawJointHybridInitialSiblingTargetRightReceiver A strategy hwin
      (profiledRawJointHybridInitialSiblingTargetOfLeft A strategy first
        current child) :=
  package.initialRightReceiver A strategy hwin
    (profiledRawJointHybridInitialSiblingParentFamily A strategy first)
    (profiledRawJointHybridInitialSiblingDirection current) child row

abbrev ProfiledRawJointHybridInitialSiblingTargetExceptionalAdapter
    (InitialOne : Type i₁) (InitialTwo : Type i₂)
    (ExceptionalOne : Type e₁) (ExceptionalTwo : Type e₂) :=
  ProfiledRawJointIndexedPolicyExceptionalAdapter A strategy
    (ProfiledRawJointHybridInitialSiblingTargetKey A strategy)
    (profiledRawJointHybridInitialSiblingTargetSource A strategy)
    (profiledRawJointHybridInitialSiblingTargetPolicy A strategy hwin)
    (profiledRawJointHybridInitialSiblingTargetControllerBank A strategy hwin)
    InitialOne InitialTwo ExceptionalOne ExceptionalTwo

/-- Complete local recurrent kernel below any finite front adapter. -/
noncomputable def profiledRawJointHybridInitialSiblingTargetLeaderFreeKernel
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    (adapter : ProfiledRawJointHybridInitialSiblingTargetExceptionalAdapter A
      strategy hwin InitialOne InitialTwo ExceptionalOne ExceptionalTwo) :
    ProfiledRawJointLeaderFreeKernel In₁ In₂ Out₁ Out₂ InitialOne
      InitialTwo ExceptionalOne ExceptionalTwo
      (ProfiledRawJointHybridInitialSiblingTargetKey A strategy)
      (ProfiledRawJointHybridInitialSiblingTargetRightOwner A strategy hwin)
      (ProfiledRawJointHybridInitialSiblingTargetLeftReceiver A strategy hwin)
      (ProfiledRawJointHybridInitialSiblingTargetRightReceiver A strategy hwin)
      (ProfiledRawJointHybridInitialSiblingTargetLeftOwner A strategy hwin) :=
  profiledRawJointIndexedPolicyLeaderFreeKernel A strategy
    (ProfiledRawJointHybridInitialSiblingTargetKey A strategy)
    (profiledRawJointHybridInitialSiblingTargetSource A strategy)
    (profiledRawJointHybridInitialSiblingTargetPolicy A strategy hwin)
    (profiledRawJointHybridInitialSiblingTargetControllerBank A strategy hwin)
    adapter

end


end DetParityAutomaton

end DistributedSynthesis
