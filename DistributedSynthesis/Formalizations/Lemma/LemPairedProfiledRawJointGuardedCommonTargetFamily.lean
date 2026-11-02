/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLocalStrictInstallation

/-!
# The recurrent target family below every guarded common pair

Every guarded common policy state chooses one finite represented pair.  A
checked strict close below that pair belongs to the finite sibling target
relation of the pair's fixed representative.  This file takes the dependent
sum over all such pairs and feeds the resulting finite target alphabet into
the existing indexed recurrent policy interface.

The pair component is finite controller provenance.  It is retained in the
handoff key; it is not a graph, orientation, strict-leader bit, or semantic
history supplied to either process.
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

private abbrev CommonPair :=
  ProfiledRawJointGuardedCommonPair A strategy hwin

/-- Public proof-side family belonging to a represented guarded pair. -/
noncomputable def profiledRawJointGuardedCommonTargetFamily
    (pair : CommonPair A strategy hwin) :
    ProfiledRawJointSemanticFamily A strategy (I := Unit) :=
  profiledRawJointCommonWorldFamily A
    (pair.representativeWorld A strategy hwin)

/-- Public proof-side incoming direction belonging to that same pair. -/
noncomputable def profiledRawJointGuardedCommonTargetDirection
    (pair : CommonPair A strategy hwin) :
    ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂) :=
  profiledRawJointBothRestartDirection
    (pair.representativeCurrent A strategy hwin)

/-- All recurrent targets below all finite guarded pairs. -/
abbrev ProfiledRawJointGuardedCommonTargetKey :=
  Σ pair : CommonPair A strategy hwin,
    ProfiledRawJointSiblingTargetChildCode A strategy
      (profiledRawJointGuardedCommonTargetFamily A strategy hwin pair)
      (profiledRawJointGuardedCommonTargetDirection A strategy hwin pair)

noncomputable instance profiledRawJointGuardedCommonTargetKeyFintype :
    Fintype (ProfiledRawJointGuardedCommonTargetKey A strategy hwin) := by
  classical
  infer_instance

noncomputable instance profiledRawJointGuardedCommonTargetKeyDecidableEq :
    DecidableEq (ProfiledRawJointGuardedCommonTargetKey A strategy hwin) :=
  Classical.decEq _

/-- Embed a checked right handoff in the global recurrent key family. -/
def profiledRawJointGuardedCommonTargetOfRight
    (handoff : ProfiledRawJointGuardedCommonRightHandoff A strategy hwin) :
    ProfiledRawJointGuardedCommonTargetKey A strategy hwin :=
  ⟨handoff.1,
    profiledRawJointSiblingTargetChildOfRight A strategy
      (profiledRawJointGuardedCommonTargetFamily A strategy hwin handoff.1)
      (profiledRawJointGuardedCommonTargetDirection A strategy hwin handoff.1)
      handoff.2⟩

/-- Left handoff embedding. -/
def profiledRawJointGuardedCommonTargetOfLeft
    (handoff : ProfiledRawJointGuardedCommonLeftHandoff A strategy hwin) :
    ProfiledRawJointGuardedCommonTargetKey A strategy hwin :=
  ⟨handoff.1,
    profiledRawJointSiblingTargetChildOfLeft A strategy
      (profiledRawJointGuardedCommonTargetFamily A strategy hwin handoff.1)
      (profiledRawJointGuardedCommonTargetDirection A strategy hwin handoff.1)
      handoff.2⟩

/-- Exact semantic source represented by one global recurrent key. -/
noncomputable def profiledRawJointGuardedCommonTargetSource
    (key : ProfiledRawJointGuardedCommonTargetKey A strategy hwin) :
    ProfiledRawJointOneSidedSemanticState A strategy (I := Unit) :=
  profiledRawJointSiblingTargetChildSource A strategy
    (profiledRawJointGuardedCommonTargetFamily A strategy hwin key.1)
    (profiledRawJointGuardedCommonTargetDirection A strategy hwin key.1)
    key.2

include hwin in
/-- One rational recurrent policy fixed once for every global target key. -/
noncomputable def profiledRawJointGuardedCommonTargetPolicy
    (key : ProfiledRawJointGuardedCommonTargetKey A strategy hwin) :
    ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      ((profiledRawJointGuardedCommonTargetSource A strategy hwin key).code
        A) :=
  profiledRawJointSiblingTargetChildPolicy A strategy hwin
    (profiledRawJointGuardedCommonTargetFamily A strategy hwin key.1)
    (profiledRawJointGuardedCommonTargetDirection A strategy hwin key.1)
    key.2

/-- Recurrent controller bank at each global target key. -/
noncomputable def profiledRawJointGuardedCommonTargetControllerBank
    (key : ProfiledRawJointGuardedCommonTargetKey A strategy hwin) :
    ProfiledRawJointUnitPolicyControllerBank A strategy
      (profiledRawJointGuardedCommonTargetSource A strategy hwin key)
      (profiledRawJointGuardedCommonTargetPolicy A strategy hwin key) :=
  profiledRawJointUnitPolicyControllerBank A strategy
    (profiledRawJointGuardedCommonTargetSource A strategy hwin key)
    (profiledRawJointGuardedCommonTargetPolicy A strategy hwin key)

/-! ## Indexed recurrent local types -/

abbrev ProfiledRawJointGuardedCommonTargetRightOwner
    (key : ProfiledRawJointGuardedCommonTargetKey A strategy hwin) :=
  ProfiledRawJointIndexedPolicyRightOwner A strategy
    (ProfiledRawJointGuardedCommonTargetKey A strategy hwin)
    (profiledRawJointGuardedCommonTargetSource A strategy hwin)
    (profiledRawJointGuardedCommonTargetPolicy A strategy hwin)
    (profiledRawJointGuardedCommonTargetControllerBank A strategy hwin) key

abbrev ProfiledRawJointGuardedCommonTargetLeftReceiver
    (key : ProfiledRawJointGuardedCommonTargetKey A strategy hwin) :=
  ProfiledRawJointIndexedPolicyLeftReceiver A strategy
    (ProfiledRawJointGuardedCommonTargetKey A strategy hwin)
    (profiledRawJointGuardedCommonTargetSource A strategy hwin)
    (profiledRawJointGuardedCommonTargetPolicy A strategy hwin) key

abbrev ProfiledRawJointGuardedCommonTargetRightReceiver
    (key : ProfiledRawJointGuardedCommonTargetKey A strategy hwin) :=
  ProfiledRawJointIndexedPolicyRightReceiver A strategy
    (ProfiledRawJointGuardedCommonTargetKey A strategy hwin)
    (profiledRawJointGuardedCommonTargetSource A strategy hwin)
    (profiledRawJointGuardedCommonTargetPolicy A strategy hwin) key

abbrev ProfiledRawJointGuardedCommonTargetLeftOwner
    (key : ProfiledRawJointGuardedCommonTargetKey A strategy hwin) :=
  ProfiledRawJointIndexedPolicyLeftOwner A strategy
    (ProfiledRawJointGuardedCommonTargetKey A strategy hwin)
    (profiledRawJointGuardedCommonTargetSource A strategy hwin)
    (profiledRawJointGuardedCommonTargetPolicy A strategy hwin)
    (profiledRawJointGuardedCommonTargetControllerBank A strategy hwin) key

/-! ## Exact close installation in the global target family -/

/-- A checked right close supplies the orientation-refined left root below
the exact guarded-pair handoff. -/
theorem
    nonempty_profiledRawJointGuardedCommonRightOrientedRootPackage_of_close
    (handoff : ProfiledRawJointGuardedCommonRightHandoff A strategy hwin)
    (scan : PairedRightScanState A) (row : PairedEntryRow)
    (physical : PairedRightBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hclose : erasePairedProfiledState A
        (profiledRawJointUnitRightTargetProjection A handoff.2.1) =
      pairedRightCloseTarget A scan row physical) :
    Nonempty
      (ProfiledRawJointRightSiblingTargetChildRootPackage A strategy hwin
        (profiledRawJointGuardedCommonTargetFamily A strategy hwin handoff.1)
        (profiledRawJointGuardedCommonTargetDirection A strategy hwin
          handoff.1) handoff.2) :=
  nonempty_profiledRawJointRightSiblingTargetChildRootPackage_of_close A
    strategy hwin
    (profiledRawJointGuardedCommonTargetFamily A strategy hwin handoff.1)
    (profiledRawJointGuardedCommonTargetDirection A strategy hwin handoff.1)
    handoff.2 scan row physical hclose

/-- Checked left-close mirror. -/
theorem
    nonempty_profiledRawJointGuardedCommonLeftOrientedRootPackage_of_close
    (handoff : ProfiledRawJointGuardedCommonLeftHandoff A strategy hwin)
    (scan : PairedLeftScanState A) (row : PairedEntryRow)
    (physical : PairedLeftBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hclose : erasePairedProfiledState A
        (profiledRawJointUnitLeftTargetProjection A handoff.2.1) =
      pairedLeftCloseTarget A scan row physical) :
    Nonempty
      (ProfiledRawJointLeftSiblingTargetChildRootPackage A strategy hwin
        (profiledRawJointGuardedCommonTargetFamily A strategy hwin handoff.1)
        (profiledRawJointGuardedCommonTargetDirection A strategy hwin
          handoff.1) handoff.2) :=
  nonempty_profiledRawJointLeftSiblingTargetChildRootPackage_of_close A
    strategy hwin
    (profiledRawJointGuardedCommonTargetFamily A strategy hwin handoff.1)
    (profiledRawJointGuardedCommonTargetDirection A strategy hwin handoff.1)
    handoff.2 scan row physical hclose

/-- Install a checked right close as the next global left owner. -/
noncomputable def profiledRawJointGuardedCommonRightTargetInitialLeftOwner
    (handoff : ProfiledRawJointGuardedCommonRightHandoff A strategy hwin)
    (package : ProfiledRawJointRightSiblingTargetChildRootPackage A strategy
      hwin
      (profiledRawJointGuardedCommonTargetFamily A strategy hwin handoff.1)
      (profiledRawJointGuardedCommonTargetDirection A strategy hwin handoff.1)
      handoff.2) :
    ProfiledRawJointGuardedCommonTargetLeftOwner A strategy hwin
      (profiledRawJointGuardedCommonTargetOfRight A strategy hwin handoff) :=
  package.initialLeftOwner A strategy hwin
    (profiledRawJointGuardedCommonTargetFamily A strategy hwin handoff.1)
    (profiledRawJointGuardedCommonTargetDirection A strategy hwin handoff.1)
    handoff.2

/-- The receiving process installs the identical global target key and row. -/
noncomputable def profiledRawJointGuardedCommonRightTargetInitialLeftReceiver
    (handoff : ProfiledRawJointGuardedCommonRightHandoff A strategy hwin)
    (package : ProfiledRawJointRightSiblingTargetChildRootPackage A strategy
      hwin
      (profiledRawJointGuardedCommonTargetFamily A strategy hwin handoff.1)
      (profiledRawJointGuardedCommonTargetDirection A strategy hwin handoff.1)
      handoff.2)
    (row : PairedEntryRow) :
    ProfiledRawJointGuardedCommonTargetLeftReceiver A strategy hwin
      (profiledRawJointGuardedCommonTargetOfRight A strategy hwin handoff) :=
  package.initialLeftReceiver A strategy hwin
    (profiledRawJointGuardedCommonTargetFamily A strategy hwin handoff.1)
    (profiledRawJointGuardedCommonTargetDirection A strategy hwin handoff.1)
    handoff.2 row

/-- Checked left close installs the next global right owner. -/
noncomputable def profiledRawJointGuardedCommonLeftTargetInitialRightOwner
    (handoff : ProfiledRawJointGuardedCommonLeftHandoff A strategy hwin)
    (package : ProfiledRawJointLeftSiblingTargetChildRootPackage A strategy
      hwin
      (profiledRawJointGuardedCommonTargetFamily A strategy hwin handoff.1)
      (profiledRawJointGuardedCommonTargetDirection A strategy hwin handoff.1)
      handoff.2) :
    ProfiledRawJointGuardedCommonTargetRightOwner A strategy hwin
      (profiledRawJointGuardedCommonTargetOfLeft A strategy hwin handoff) :=
  package.initialRightOwner A strategy hwin
    (profiledRawJointGuardedCommonTargetFamily A strategy hwin handoff.1)
    (profiledRawJointGuardedCommonTargetDirection A strategy hwin handoff.1)
    handoff.2

/-- Receiving-side mirror at a checked left close. -/
noncomputable def profiledRawJointGuardedCommonLeftTargetInitialRightReceiver
    (handoff : ProfiledRawJointGuardedCommonLeftHandoff A strategy hwin)
    (package : ProfiledRawJointLeftSiblingTargetChildRootPackage A strategy
      hwin
      (profiledRawJointGuardedCommonTargetFamily A strategy hwin handoff.1)
      (profiledRawJointGuardedCommonTargetDirection A strategy hwin handoff.1)
      handoff.2)
    (row : PairedEntryRow) :
    ProfiledRawJointGuardedCommonTargetRightReceiver A strategy hwin
      (profiledRawJointGuardedCommonTargetOfLeft A strategy hwin handoff) :=
  package.initialRightReceiver A strategy hwin
    (profiledRawJointGuardedCommonTargetFamily A strategy hwin handoff.1)
    (profiledRawJointGuardedCommonTargetDirection A strategy hwin handoff.1)
    handoff.2 row

/-! ## Indexed recurrent kernel below a finite front adapter -/

abbrev ProfiledRawJointGuardedCommonTargetExceptionalAdapter
    (InitialOne : Type i₁) (InitialTwo : Type i₂)
    (ExceptionalOne : Type e₁) (ExceptionalTwo : Type e₂) :=
  ProfiledRawJointIndexedPolicyExceptionalAdapter A strategy
    (ProfiledRawJointGuardedCommonTargetKey A strategy hwin)
    (profiledRawJointGuardedCommonTargetSource A strategy hwin)
    (profiledRawJointGuardedCommonTargetPolicy A strategy hwin)
    (profiledRawJointGuardedCommonTargetControllerBank A strategy hwin)
    InitialOne InitialTwo ExceptionalOne ExceptionalTwo

/-- Complete local recurrent kernel below any finite guarded-common front
adapter. -/
noncomputable def profiledRawJointGuardedCommonTargetLeaderFreeKernel
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    (adapter : ProfiledRawJointGuardedCommonTargetExceptionalAdapter A strategy
      hwin InitialOne InitialTwo ExceptionalOne ExceptionalTwo) :
    ProfiledRawJointLeaderFreeKernel In₁ In₂ Out₁ Out₂ InitialOne InitialTwo
      ExceptionalOne ExceptionalTwo
      (ProfiledRawJointGuardedCommonTargetKey A strategy hwin)
      (ProfiledRawJointGuardedCommonTargetRightOwner A strategy hwin)
      (ProfiledRawJointGuardedCommonTargetLeftReceiver A strategy hwin)
      (ProfiledRawJointGuardedCommonTargetRightReceiver A strategy hwin)
      (ProfiledRawJointGuardedCommonTargetLeftOwner A strategy hwin) :=
  profiledRawJointIndexedPolicyLeaderFreeKernel A strategy
    (ProfiledRawJointGuardedCommonTargetKey A strategy hwin)
    (profiledRawJointGuardedCommonTargetSource A strategy hwin)
    (profiledRawJointGuardedCommonTargetPolicy A strategy hwin)
    (profiledRawJointGuardedCommonTargetControllerBank A strategy hwin)
    adapter

end


end DetParityAutomaton

end DistributedSynthesis
