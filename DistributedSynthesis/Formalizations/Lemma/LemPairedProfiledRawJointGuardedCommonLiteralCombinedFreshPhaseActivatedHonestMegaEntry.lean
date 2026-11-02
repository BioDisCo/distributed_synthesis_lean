/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridMegaGuardedInitialCheckerAlignment
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridInitialCommonSiblingBridge
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedForeverCommonAcceptance
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCombinedFreshPhaseActivatedInitialBank
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntryBootstrapReceive
import DistributedSynthesis.Formalizations.Lemma.LemFiniteAcknowledgedExactClosingSemanticSelectionTrace

/-!
# Honest guarded-mega entry to the phase-activated carrier

The two-round seed bank is sufficient only when the execution starts with two
simultaneous rounds.  A general execution instead reaches a finite guarded
installation after an arbitrary literal prefix.  That installation already
contains one jointly represented common occurrence and is present in both
coupled endpoint controls.

This file indexes the phase-activated controller by that finite installation
together with the actual simultaneous entry input.  At a receive from
matching coupled controls, one exact close installs the member rooted at the
literal successor occurrence.  The open
branches remain the guarded strict-left and strict-right continuations.  The
generic acknowledged exact-close relay retains these alternatives until the
physical receipt pattern resolves them; no endpoint is told the graph.
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
  (initialBank : ProfiledRawJointInitialControllerBank A strategy)

namespace ProfiledRawJointGuardedCommonDecoratedPolicyPackage

private abbrev Installation :=
  ProfiledRawJointHybridGuardedSiblingInstallation A strategy hwin

private abbrev CrossValid :=
  ProfiledRawJointGuardedCommonLiteralCrossExtraValid A strategy hwin

/-! ## The literal occurrence represented by an installation -/

/-- Recover a literal common occurrence from the proof-erased finite guarded
installation.  This choice is not a code-only reanchoring: each constructor of
the installation stores a root-pinned common world and its actual incoming
simultaneous input. -/
noncomputable def literalCombinedFreshPhaseActivatedPointOfInstallation
    (installation : Installation A strategy hwin) :
    ProfiledRawJointGuardedCommonSemanticPoint A strategy :=
  match installation with
  | .inl initial =>
      ⟨ProfiledRawJointHybridInitialRootPinnedWorld A strategy
          initial.first,
        initial.current⟩
  | .inr recurrent =>
      ⟨(profiledRawJointHybridRootPinnedCommonInstalled A strategy hwin
          recurrent.1).world,
        recurrent.2⟩

/-- The recovered occurrence has exactly the guarded pair stored by the
installation. -/
theorem literalCombinedFreshPhaseActivatedPointOfInstallation_move
    (installation : Installation A strategy hwin) :
    (literalCombinedFreshPhaseActivatedPointOfInstallation A strategy hwin
      installation).move A strategy hwin =
      profiledRawJointHybridGuardedCommonPairAt A strategy hwin
        installation := by
  cases installation <;> rfl

omit [DecidableEq In₁] [DecidableEq In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- The common control prepared by an installation has the same complete
process-one slot as the semantic occurrence represented by that installation.
For a recurrent installation this is the anti-mosaic successor theorem.  For
the exceptional initial installation it follows by extracting the right slot
from the complete incidence-code equality. -/
theorem
    literalCombinedFreshPhaseActivatedInstallationCommon_procOneSlot_eq_point
    (installation : Installation A strategy hwin) :
    let common :=
      profiledRawJointHybridGuardedInstallationCommon A strategy hwin
        installation
    let installed :=
      profiledRawJointHybridRootPinnedCommonInstalled A strategy hwin common
    installed.world.procOneSlot A =
      ((literalCombinedFreshPhaseActivatedPointOfInstallation A strategy hwin
        installation).world A strategy).procOneSlot A := by
  cases installation with
  | inl initial =>
      dsimp only [profiledRawJointHybridGuardedInstallationCommon,
        literalCombinedFreshPhaseActivatedPointOfInstallation,
        ProfiledRawJointGuardedCommonSemanticPoint.world]
      let installed :=
        profiledRawJointHybridRootPinnedCommonInstalled A strategy hwin
          (profiledRawJointHybridRootPinnedInitialCommonControl A strategy
            hwin initial.first initial.current)
      have hincidence :
          (profiledRawJointCommonWorldFamily A installed.world).incidenceCode A =
            (profiledRawJointCommonWorldFamily A
              (profiledRawJointCommonWorldAfterBoth A
                (ProfiledRawJointHybridInitialRootPinnedWorld A strategy
                  initial.first)
                initial.current)).incidenceCode A := by
        calc
          _ = (profiledRawJointHybridInitialRootPinnedSimultaneousKey A
                strategy hwin initial.first initial.current).incidenceCode :=
              installed.incidence_eq
          _ = _ :=
            profiledRawJointHybridInitialRootPinnedSimultaneousKey_incidence_eq_secondCommon
              A strategy hwin initial.first initial.current
      have hright := congrArg
        (fun code : ProfiledRawJointIncidenceCode A (I := Unit) ↦
          code.family.right ()) hincidence
      exact Option.some.inj (by
        simpa [ProfiledRawJointSemanticFamily.incidenceCode,
          ProfiledRawJointSemanticFamily.code,
          profiledRawJointCommonWorldFamily,
          ProfiledRawJointCommonBaseWorld.procOneSlot,
          profiledRawRightSlotOfSemanticPair] using hright)
  | inr recurrent =>
      dsimp only [profiledRawJointHybridGuardedInstallationCommon,
        literalCombinedFreshPhaseActivatedPointOfInstallation,
        ProfiledRawJointGuardedCommonSemanticPoint.world]
      exact
        (profiledRawJointHybridRootPinnedCommonInstalled A strategy hwin
          recurrent.1).simultaneousSuccessor_procOneSlot A
            recurrent.2
            (profiledRawJointHybridRootPinnedCommonInstalled A strategy hwin
              (profiledRawJointHybridRootPinnedCommonNext A strategy hwin
                recurrent.1 recurrent.2))

/-- Checker-coordinate form of the preceding complete-slot equality. -/
theorem literalCombinedFreshPhaseActivatedInstallationCommon_source_eq_pair
    (installation : Installation A strategy hwin) :
    let pair := profiledRawJointHybridGuardedCommonPairAt A strategy hwin
      installation
    let common :=
      profiledRawJointHybridGuardedInstallationCommon A strategy hwin
        installation
    let installed :=
      profiledRawJointHybridRootPinnedCommonInstalled A strategy hwin common
    pairedCodeStateForRow A .both pair.1.1.1.base.source.1.1 =
      pairedCodeStateForRow A .both (installed.world.procOneSlot A).1.1 := by
  dsimp only
  rw [← literalCombinedFreshPhaseActivatedPointOfInstallation_move A
    strategy hwin installation]
  unfold ProfiledRawJointGuardedCommonSemanticPoint.move
    profiledRawJointGuardedCommonPairOfWorld
    profiledRawJointGuardedCommonRightMoveOfWorld
  change pairedCodeStateForRow A .both
      (((literalCombinedFreshPhaseActivatedPointOfInstallation A strategy hwin
        installation).world A strategy).procOneSlot A).1.1 = _
  exact congrArg
    (fun slot ↦ pairedCodeStateForRow A .both slot.1.1)
    (literalCombinedFreshPhaseActivatedInstallationCommon_procOneSlot_eq_point
      A strategy hwin installation).symm

/-- Finite entry key recording the exact guarded occurrence and the
simultaneous input whose literal child becomes the phase root. -/
private abbrev EntrySeed :=
  Installation A strategy hwin × (In₁ × In₂)

/-- The literal child occurrence selected at the honest entry round. -/
def literalCombinedFreshPhaseActivatedPointOfEntrySeed
    (seed : EntrySeed A strategy hwin) :
    ProfiledRawJointGuardedCommonSemanticPoint A strategy :=
  (literalCombinedFreshPhaseActivatedPointOfInstallation A strategy hwin
    seed.1).step A strategy seed.2

/-- Root-pinned decorated policy selected at the literal predecessor of an
honest entry.  Unlike `EntrySeedPackage`, its unique fresh root retains the
represented occurrence's exact guarded pair and both literal-cross table
IDs. -/
noncomputable def
    literalCombinedFreshPhaseActivatedRootPinnedPolicyOfEntrySeed
    (seed : EntrySeed A strategy hwin) :
    ProfiledRawJointGuardedCommonLiteralCrossRootPinnedPolicy A strategy hwin
      (literalCombinedFreshPhaseActivatedPointOfInstallation A strategy hwin
        seed.1) :=
  profiledRawJointGuardedCommonLiteralCrossRootPinnedPolicy A strategy hwin
    (literalCombinedFreshPhaseActivatedPointOfInstallation A strategy hwin
      seed.1)

/-- The root-pinned entry policy selects the represented literal occurrence,
not an arbitrary same-code representative. -/
@[simp] theorem
    literalCombinedFreshPhaseActivatedRootPinnedPolicyOfEntrySeed_rootMove
    (seed : EntrySeed A strategy hwin) :
    (literalCombinedFreshPhaseActivatedRootPinnedPolicyOfEntrySeed A strategy
      hwin seed).rootMove =
      ((literalCombinedFreshPhaseActivatedPointOfInstallation A strategy hwin
          seed.1).move A strategy hwin,
        profiledRawJointGuardedCommonLiteralCrossExtraOfPoint A strategy hwin
          (literalCombinedFreshPhaseActivatedPointOfInstallation A strategy
            hwin seed.1)) :=
  profiledRawJointGuardedCommonLiteralCrossRootPinnedPolicy_rootMove A strategy
    hwin
      (literalCombinedFreshPhaseActivatedPointOfInstallation A strategy hwin
        seed.1)

/-- Applying the actual entry input to the pinned root gives exactly the
public code of the literal child occurrence used by the checker handoff. -/
theorem
    literalCombinedFreshPhaseActivatedRootPinnedPolicyOfEntrySeed_childCode
    (seed : EntrySeed A strategy hwin) :
    ((literalCombinedFreshPhaseActivatedRootPinnedPolicyOfEntrySeed A strategy
        hwin seed).rootMove.1.bothNextCode A strategy hwin seed.2) =
      (literalCombinedFreshPhaseActivatedPointOfEntrySeed A strategy hwin
        seed).code A strategy := by
  rw [
    literalCombinedFreshPhaseActivatedRootPinnedPolicyOfEntrySeed_rootMove A
      strategy hwin seed]
  exact
    (ProfiledRawJointGuardedCommonSemanticPoint.step_code A strategy hwin
      (literalCombinedFreshPhaseActivatedPointOfInstallation A strategy hwin
        seed.1) seed.2).symm

/-- Exact false-bit state reached by consuming the honest entry input in the
single root-pinned policy selected at its literal predecessor. -/
noncomputable def
    literalCombinedFreshPhaseActivatedRootPinnedEntryKeyOfEntrySeed
    (seed : EntrySeed A strategy hwin) :
    ProfiledRawJointGuardedCommonLiteralCrossRootPinnedFalseKey A strategy hwin
      (literalCombinedFreshPhaseActivatedPointOfInstallation A strategy hwin
        seed.1) :=
  profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryKey A strategy hwin
    (literalCombinedFreshPhaseActivatedPointOfInstallation A strategy hwin
      seed.1) seed.2

/-- The entry seed's executable root-pinned state is the literal child named
by that same seed. -/
@[simp] theorem
    literalCombinedFreshPhaseActivatedRootPinnedEntryKeyOfEntrySeed_code
    (seed : EntrySeed A strategy hwin) :
    (literalCombinedFreshPhaseActivatedRootPinnedEntryKeyOfEntrySeed A strategy
      hwin seed).state.2.1 =
      (literalCombinedFreshPhaseActivatedPointOfEntrySeed A strategy hwin
        seed).code A strategy := by
  exact
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryKey_code A strategy
      hwin
      (literalCombinedFreshPhaseActivatedPointOfInstallation A strategy hwin
        seed.1) seed.2

/-! ## Entry-aligned blind bootstrap -/

/-- The finite table pair used by the corrected entry bootstrap is exactly
the annotation pinned at the represented predecessor occurrence.  In
particular, constructing the bootstrap does not consult the independently
rationalized Mega child policy. -/
theorem
    literalCombinedFreshPhaseActivatedEntryBootstrapExtra_eq_rootMove
    (seed : EntrySeed A strategy hwin) :
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryExtra A strategy
        hwin
        (literalCombinedFreshPhaseActivatedPointOfInstallation A strategy hwin
          seed.1) =
      (literalCombinedFreshPhaseActivatedRootPinnedPolicyOfEntrySeed A strategy
        hwin seed).rootMove.2 := by
  exact
    profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryExtra_eq_rootMove A
      strategy hwin
      (literalCombinedFreshPhaseActivatedPointOfInstallation A strategy hwin
        seed.1)

/-- Either semantic member selected from the honest entry bootstrap gives a
pair of synchronized right and left literal-table controls.  The strict
receive maps may therefore be iterated without any semantic re-selection. -/
theorem
    literalCombinedFreshPhaseActivatedEntryBootstrapInitial_aligned
    (seed : EntrySeed A strategy hwin) (member : Bool) :
    ProfiledRawJointGuardedCommonLiteralCrossRootPinnedEntryAligned A
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryOneInitial A
        strategy hwin
          (literalCombinedFreshPhaseActivatedPointOfInstallation A strategy
            hwin seed.1) seed.2 member)
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryTwoInitial A
        strategy hwin
          (literalCombinedFreshPhaseActivatedPointOfInstallation A strategy
            hwin seed.1) seed.2 member) :=
  profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryInitial_aligned A
    strategy hwin
      (literalCombinedFreshPhaseActivatedPointOfInstallation A strategy hwin
        seed.1) seed.2 member

/-- Process-one blind-output coherence at every no-receive depth reachable
from an honest entry-aligned fork. -/
theorem
    literalCombinedFreshPhaseActivatedEntryBootstrapOne_reachable_coherent
    (seed : EntrySeed A strategy hwin) (past : List In₁) (input : In₁) :
    FiniteAcknowledgedDelayedCarrier.NoRecvOutputCoherent
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryNoRecvOne A)
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryOneBlindRun A
        (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryOneFork A
          strategy hwin
          (literalCombinedFreshPhaseActivatedPointOfInstallation A strategy
            hwin seed.1) seed.2) past)
      input :=
  profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryOne_reachable_coherent
    A strategy hwin
      (literalCombinedFreshPhaseActivatedPointOfInstallation A strategy hwin
        seed.1) seed.2 past input

/-- Process-two mirror. -/
theorem
    literalCombinedFreshPhaseActivatedEntryBootstrapTwo_reachable_coherent
    (seed : EntrySeed A strategy hwin) (past : List In₂) (input : In₂) :
    FiniteAcknowledgedDelayedCarrier.NoRecvOutputCoherent
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryNoRecvTwo A)
      (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryTwoBlindRun A
        (profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryTwoFork A
          strategy hwin
          (literalCombinedFreshPhaseActivatedPointOfInstallation A strategy
            hwin seed.1) seed.2) past)
      input :=
  profiledRawJointGuardedCommonLiteralCrossRootPinnedEntryTwo_reachable_coherent
    A strategy hwin
      (literalCombinedFreshPhaseActivatedPointOfInstallation A strategy hwin
        seed.1) seed.2 past input

/-- The package selected by an arbitrary honest guarded entry seed. -/
noncomputable def literalCombinedFreshPhaseActivatedPackageOfEntrySeed
    (seed : EntrySeed A strategy hwin) :
    ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy hwin
      (literalCombinedFreshPhaseActivatedPointOfEntrySeed A strategy hwin seed)
      (CrossValid A strategy hwin) :=
  profiledRawJointGuardedCommonLiteralCrossDecoratedPolicyPackage A strategy
    hwin
      (literalCombinedFreshPhaseActivatedPointOfEntrySeed A strategy hwin seed)

private abbrev EntrySeedPackage (seed : EntrySeed A strategy hwin) :=
  literalCombinedFreshPhaseActivatedPackageOfEntrySeed A strategy hwin seed

private abbrev EntrySeedMember (seed : EntrySeed A strategy hwin) :=
  (EntrySeedPackage A strategy hwin seed
    ).literalCombinedFreshPhaseActivatedController A strategy hwin

/-! ## Finite dependent bank over all honest entry seeds -/

abbrev ProfiledRawJointGuardedCommonLiteralPhaseActivatedInstallationBankOne :=
  Σ seed : EntrySeed A strategy hwin,
    (EntrySeedMember A strategy hwin seed).OneControl

abbrev ProfiledRawJointGuardedCommonLiteralPhaseActivatedInstallationBankTwo :=
  Σ seed : EntrySeed A strategy hwin,
    (EntrySeedMember A strategy hwin seed).TwoControl

set_option synthInstance.maxHeartbeats 1000000 in
noncomputable instance
    literalCombinedFreshPhaseActivatedInstallationBankOneFintype :
    Fintype
      (ProfiledRawJointGuardedCommonLiteralPhaseActivatedInstallationBankOne
        A strategy hwin) := by
  classical
  infer_instance

set_option synthInstance.maxHeartbeats 1000000 in
noncomputable instance
    literalCombinedFreshPhaseActivatedInstallationBankTwoFintype :
    Fintype
      (ProfiledRawJointGuardedCommonLiteralPhaseActivatedInstallationBankTwo
        A strategy hwin) := by
  classical
  infer_instance

/-- Install the process-one half of the member rooted at `seed`. -/
noncomputable def literalCombinedFreshPhaseActivatedInstallationActivateOne
    (seed : EntrySeed A strategy hwin) :
    ProfiledRawJointGuardedCommonLiteralPhaseActivatedInstallationBankOne A
      strategy hwin :=
  ⟨seed, (EntrySeedMember A strategy hwin seed).initialOne⟩

/-- Process-two mirror. -/
noncomputable def literalCombinedFreshPhaseActivatedInstallationActivateTwo
    (seed : EntrySeed A strategy hwin) :
    ProfiledRawJointGuardedCommonLiteralPhaseActivatedInstallationBankTwo A
      strategy hwin :=
  ⟨seed, (EntrySeedMember A strategy hwin seed).initialTwo⟩

@[simp] theorem
    literalCombinedFreshPhaseActivatedInstallationActivateOne_installation
    (seed : EntrySeed A strategy hwin) :
    (literalCombinedFreshPhaseActivatedInstallationActivateOne A strategy hwin
      seed).1 = seed :=
  rfl

@[simp] theorem
    literalCombinedFreshPhaseActivatedInstallationActivateTwo_installation
    (seed : EntrySeed A strategy hwin) :
    (literalCombinedFreshPhaseActivatedInstallationActivateTwo A strategy hwin
      seed).1 = seed :=
  rfl

noncomputable def literalCombinedFreshPhaseActivatedInstallationNoRecvOne
    (state :
      ProfiledRawJointGuardedCommonLiteralPhaseActivatedInstallationBankOne A
        strategy hwin)
    (input : In₁) :
    ProfiledRawJointGuardedCommonLiteralPhaseActivatedInstallationBankOne A
        strategy hwin × Out₁ := by
  rcases state with ⟨seed, state⟩
  let next := (EntrySeedMember A strategy hwin seed).noRecvOne
    state input
  exact (⟨seed, next.1⟩, next.2)

noncomputable def literalCombinedFreshPhaseActivatedInstallationNoRecvTwo
    (state :
      ProfiledRawJointGuardedCommonLiteralPhaseActivatedInstallationBankTwo A
        strategy hwin)
    (input : In₂) :
    ProfiledRawJointGuardedCommonLiteralPhaseActivatedInstallationBankTwo A
        strategy hwin × Out₂ := by
  rcases state with ⟨seed, state⟩
  let next := (EntrySeedMember A strategy hwin seed).noRecvTwo
    state input
  exact (⟨seed, next.1⟩, next.2)

noncomputable def literalCombinedFreshPhaseActivatedInstallationRecvOne
    (one :
      ProfiledRawJointGuardedCommonLiteralPhaseActivatedInstallationBankOne A
        strategy hwin)
    (own : In₁)
    (two :
      ProfiledRawJointGuardedCommonLiteralPhaseActivatedInstallationBankTwo A
        strategy hwin)
    (delivered : In₂) :
    ProfiledRawJointGuardedCommonLiteralPhaseActivatedInstallationBankOne A
        strategy hwin × Out₁ := by
  rcases one with ⟨seedOne, one⟩
  rcases two with ⟨seedTwo, two⟩
  classical
  by_cases hseed : seedTwo = seedOne
  · subst seedTwo
    let next := (EntrySeedMember A strategy hwin seedOne).recvOne
      one own two delivered
    exact (⟨seedOne, next.1⟩, next.2)
  · let next := (EntrySeedMember A strategy hwin seedOne).recvOne
      one own
      (EntrySeedMember A strategy hwin seedOne).initialTwo delivered
    exact (⟨seedOne, next.1⟩, next.2)

noncomputable def literalCombinedFreshPhaseActivatedInstallationRecvTwo
    (two :
      ProfiledRawJointGuardedCommonLiteralPhaseActivatedInstallationBankTwo A
        strategy hwin)
    (own : In₂)
    (one :
      ProfiledRawJointGuardedCommonLiteralPhaseActivatedInstallationBankOne A
        strategy hwin)
    (delivered : In₁) :
    ProfiledRawJointGuardedCommonLiteralPhaseActivatedInstallationBankTwo A
        strategy hwin × Out₂ := by
  rcases two with ⟨seedTwo, two⟩
  rcases one with ⟨seedOne, one⟩
  classical
  by_cases hseed : seedOne = seedTwo
  · subst seedOne
    let next := (EntrySeedMember A strategy hwin seedTwo).recvTwo
      two own one delivered
    exact (⟨seedTwo, next.1⟩, next.2)
  · let next := (EntrySeedMember A strategy hwin seedTwo).recvTwo
      two own
      (EntrySeedMember A strategy hwin seedTwo).initialOne delivered
    exact (⟨seedTwo, next.1⟩, next.2)

/-- The occurrence-and-input-indexed bank as one key-independent Mealy tail.
Its default seed is administrative; the global controller below enters only
through the exact activation maps. -/
noncomputable def literalCombinedFreshPhaseActivatedInstallationBankController
    (fallback : Installation A strategy hwin) :
    FinitePairedMealyController In₁ In₂ Out₁ Out₂ where
  OneControl :=
    ProfiledRawJointGuardedCommonLiteralPhaseActivatedInstallationBankOne A
      strategy hwin
  TwoControl :=
    ProfiledRawJointGuardedCommonLiteralPhaseActivatedInstallationBankTwo A
      strategy hwin
  oneFinite := inferInstance
  twoFinite := inferInstance
  initialOne :=
    literalCombinedFreshPhaseActivatedInstallationActivateOne A strategy hwin
      (fallback, (default, default))
  initialTwo :=
    literalCombinedFreshPhaseActivatedInstallationActivateTwo A strategy hwin
      (fallback, (default, default))
  noRecvOne :=
    literalCombinedFreshPhaseActivatedInstallationNoRecvOne A strategy hwin
  noRecvTwo :=
    literalCombinedFreshPhaseActivatedInstallationNoRecvTwo A strategy hwin
  recvOne :=
    literalCombinedFreshPhaseActivatedInstallationRecvOne A strategy hwin
  recvTwo :=
    literalCombinedFreshPhaseActivatedInstallationRecvTwo A strategy hwin

/-! ## Exact guarded-mega splice -/

private abbrev RetainedTag :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A strategy
    hwin

private abbrev Mega (fallbackTag : RetainedTag A strategy hwin) :=
  MegaGuardedLinkedPhysicalController A strategy hwin controllers initialBank
    fallbackTag

private abbrev InstallationBank (fallback : Installation A strategy hwin) :=
  literalCombinedFreshPhaseActivatedInstallationBankController A strategy hwin
    fallback

abbrev ProfiledRawJointGuardedCommonLiteralPhaseActivatedHonestEntryOneControl
    (fallback : Installation A strategy hwin)
    (fallbackTag : RetainedTag A strategy hwin) :=
  (Mega A strategy hwin controllers initialBank fallbackTag).OneControl ⊕
    (InstallationBank A strategy hwin fallback).OneControl

abbrev ProfiledRawJointGuardedCommonLiteralPhaseActivatedHonestEntryTwoControl
    (fallback : Installation A strategy hwin)
    (fallbackTag : RetainedTag A strategy hwin) :=
  (Mega A strategy hwin controllers initialBank fallbackTag).TwoControl ⊕
    (InstallationBank A strategy hwin fallback).TwoControl

private noncomputable def literalCombinedFreshPhaseActivatedHonestEntryNoRecvOne
    (fallback : Installation A strategy hwin)
    (fallbackTag : RetainedTag A strategy hwin)
    (state :
      ProfiledRawJointGuardedCommonLiteralPhaseActivatedHonestEntryOneControl A
        strategy hwin controllers initialBank fallback fallbackTag)
    (input : In₁) :
    ProfiledRawJointGuardedCommonLiteralPhaseActivatedHonestEntryOneControl A
        strategy hwin controllers initialBank fallback fallbackTag × Out₁ :=
  match state with
  | .inl state =>
      let mega := Mega A strategy hwin controllers initialBank fallbackTag
      let next := mega.noRecvOne state input
      (.inl next, mega.outputOne next)
  | .inr state =>
      let next :=
        literalCombinedFreshPhaseActivatedInstallationNoRecvOne A strategy hwin
          state input
      (.inr next.1, next.2)

private noncomputable def literalCombinedFreshPhaseActivatedHonestEntryNoRecvTwo
    (fallback : Installation A strategy hwin)
    (fallbackTag : RetainedTag A strategy hwin)
    (state :
      ProfiledRawJointGuardedCommonLiteralPhaseActivatedHonestEntryTwoControl A
        strategy hwin controllers initialBank fallback fallbackTag)
    (input : In₂) :
    ProfiledRawJointGuardedCommonLiteralPhaseActivatedHonestEntryTwoControl A
        strategy hwin controllers initialBank fallback fallbackTag × Out₂ :=
  match state with
  | .inl state =>
      let mega := Mega A strategy hwin controllers initialBank fallbackTag
      let next := mega.noRecvTwo state input
      (.inl next, mega.outputTwo next)
  | .inr state =>
      let next :=
        literalCombinedFreshPhaseActivatedInstallationNoRecvTwo A strategy hwin
          state input
      (.inr next.1, next.2)

private noncomputable def literalCombinedFreshPhaseActivatedHonestEntryOpenRecvOne
    (fallback : Installation A strategy hwin)
    (fallbackTag : RetainedTag A strategy hwin)
    (one :
      ProfiledRawJointGuardedCommonLiteralPhaseActivatedHonestEntryOneControl A
        strategy hwin controllers initialBank fallback fallbackTag)
    (own : In₁)
    (two :
      ProfiledRawJointGuardedCommonLiteralPhaseActivatedHonestEntryTwoControl A
        strategy hwin controllers initialBank fallback fallbackTag)
    (delivered : In₂) :
    ProfiledRawJointGuardedCommonLiteralPhaseActivatedHonestEntryOneControl A
        strategy hwin controllers initialBank fallback fallbackTag × Out₁ :=
  match one, two with
  | .inl one, .inl two =>
      let mega := Mega A strategy hwin controllers initialBank fallbackTag
      let next := mega.recvOne one own two delivered
      (.inl next, mega.outputOne next)
  | .inr one, .inr two =>
      let next :=
        literalCombinedFreshPhaseActivatedInstallationRecvOne A strategy hwin
          one own two delivered
      (.inr next.1, next.2)
  | .inl one, .inr _ => (.inl one, default)
  | .inr one, .inl _ => (.inr one, default)

private noncomputable def literalCombinedFreshPhaseActivatedHonestEntryOpenRecvTwo
    (fallback : Installation A strategy hwin)
    (fallbackTag : RetainedTag A strategy hwin)
    (two :
      ProfiledRawJointGuardedCommonLiteralPhaseActivatedHonestEntryTwoControl A
        strategy hwin controllers initialBank fallback fallbackTag)
    (own : In₂)
    (one :
      ProfiledRawJointGuardedCommonLiteralPhaseActivatedHonestEntryOneControl A
        strategy hwin controllers initialBank fallback fallbackTag)
    (delivered : In₁) :
    ProfiledRawJointGuardedCommonLiteralPhaseActivatedHonestEntryTwoControl A
        strategy hwin controllers initialBank fallback fallbackTag × Out₂ :=
  match two, one with
  | .inl two, .inl one =>
      let mega := Mega A strategy hwin controllers initialBank fallbackTag
      let next := mega.recvTwo two own one delivered
      (.inl next, mega.outputTwo next)
  | .inr two, .inr one =>
      let next :=
        literalCombinedFreshPhaseActivatedInstallationRecvTwo A strategy hwin
          two own one delivered
      (.inr next.1, next.2)
  | .inl two, .inr _ => (.inl two, default)
  | .inr two, .inl _ => (.inr two, default)

private def literalCombinedFreshPhaseActivatedMegaCoupledOne?
    (fallbackTag : RetainedTag A strategy hwin)
    (state : (Mega A strategy hwin controllers initialBank
      fallbackTag).OneControl) : Option (Installation A strategy hwin) :=
  match state.1 with
  | .exceptional (.inr (.inl coupled)) => some coupled.1
  | _ => none

private def literalCombinedFreshPhaseActivatedMegaCoupledTwo?
    (fallbackTag : RetainedTag A strategy hwin)
    (state : (Mega A strategy hwin controllers initialBank
      fallbackTag).TwoControl) : Option (Installation A strategy hwin) :=
  match state.1 with
  | .exceptional (.inr (.inl coupled)) => some coupled.1
  | _ => none

@[simp] private theorem
    literalCombinedFreshPhaseActivatedMegaCoupledOne?_initial
    (fallbackTag : RetainedTag A strategy hwin) :
    literalCombinedFreshPhaseActivatedMegaCoupledOne? A strategy hwin
        controllers initialBank fallbackTag
        (Mega A strategy hwin controllers initialBank fallbackTag).initialOne =
      none :=
  rfl

@[simp] private theorem
    literalCombinedFreshPhaseActivatedMegaCoupledTwo?_initial
    (fallbackTag : RetainedTag A strategy hwin) :
    literalCombinedFreshPhaseActivatedMegaCoupledTwo? A strategy hwin
        controllers initialBank fallbackTag
        (Mega A strategy hwin controllers initialBank fallbackTag).initialTwo =
      none :=
  rfl

@[simp] private theorem
    literalCombinedFreshPhaseActivatedMegaCoupledOne?_initialShadow
    (fallbackTag : RetainedTag A strategy hwin)
    (shadow : ProfiledRawJointHybridInitialOneShadow A strategy hwin
      controllers)
    (output : Out₁) :
    literalCombinedFreshPhaseActivatedMegaCoupledOne? A strategy hwin
        controllers initialBank fallbackTag
        (profiledRawJointHybridMegaGuardedLinkedLiftFrontOne A strategy hwin
          controllers initialBank
            (.exceptional
              (profiledRawJointHybridMegaExceptionalOneOfInitialShadow A
                strategy hwin controllers initialBank shadow)), output) =
      none :=
  rfl

@[simp] private theorem
    literalCombinedFreshPhaseActivatedMegaCoupledTwo?_initialShadow
    (fallbackTag : RetainedTag A strategy hwin)
    (shadow : ProfiledRawJointHybridInitialTwoShadow A strategy hwin
      controllers)
    (output : Out₂) :
    literalCombinedFreshPhaseActivatedMegaCoupledTwo? A strategy hwin
        controllers initialBank fallbackTag
        (profiledRawJointHybridMegaGuardedLinkedLiftFrontTwo A strategy hwin
          controllers initialBank
            (.exceptional
              (profiledRawJointHybridMegaExceptionalTwoOfInitialShadow A
                strategy hwin controllers initialBank shadow)), output) =
      none :=
  rfl

/-- The guarded-Mega pair is at a genuine honest-entry seam precisely when
both finite controls expose the same guarded installation.  The graph is kept
out of this local predicate; an actual activation trigger additionally
requires a simultaneous physical round. -/
def literalCombinedFreshPhaseActivatedHonestMegaEntryEnabled
    (fallbackTag : RetainedTag A strategy hwin)
    (one : (Mega A strategy hwin controllers initialBank
      fallbackTag).OneControl)
    (two : (Mega A strategy hwin controllers initialBank
      fallbackTag).TwoControl) : Prop :=
  ∃ installation : Installation A strategy hwin,
    literalCombinedFreshPhaseActivatedMegaCoupledOne? A strategy hwin
        controllers initialBank fallbackTag one = some installation ∧
      literalCombinedFreshPhaseActivatedMegaCoupledTwo? A strategy hwin
        controllers initialBank fallbackTag two = some installation

/-- Exact simultaneous update.  Matching guarded coupled controls enter the
phase-activated member at their literal simultaneous successor.  All other
mega states retain the existing mega simultaneous transition, and states
already in the phase bank use that bank's simultaneous transition. -/
private noncomputable def literalCombinedFreshPhaseActivatedHonestEntryClose
    (fallback : Installation A strategy hwin)
    (fallbackTag : RetainedTag A strategy hwin)
    (one :
      ProfiledRawJointGuardedCommonLiteralPhaseActivatedHonestEntryOneControl A
        strategy hwin controllers initialBank fallback fallbackTag)
    (own : In₁)
    (two :
      ProfiledRawJointGuardedCommonLiteralPhaseActivatedHonestEntryTwoControl A
        strategy hwin controllers initialBank fallback fallbackTag)
    (delivered : In₂) :
    ProfiledRawJointGuardedCommonLiteralPhaseActivatedHonestEntryOneControl A
        strategy hwin controllers initialBank fallback fallbackTag ×
      ProfiledRawJointGuardedCommonLiteralPhaseActivatedHonestEntryTwoControl A
        strategy hwin controllers initialBank fallback fallbackTag := by
  classical
  exact match one, two with
  | .inl one, .inl two =>
      let mega := Mega A strategy hwin controllers initialBank fallbackTag
      match
          literalCombinedFreshPhaseActivatedMegaCoupledOne? A strategy hwin
            controllers initialBank fallbackTag one,
          literalCombinedFreshPhaseActivatedMegaCoupledTwo? A strategy hwin
            controllers initialBank fallbackTag two with
      | some installationOne, some installationTwo =>
          if hinstallation : installationTwo = installationOne then
            let entrySeed : EntrySeed A strategy hwin :=
              (installationOne, (own, delivered))
            (.inr
                (literalCombinedFreshPhaseActivatedInstallationActivateOne A
                  strategy hwin entrySeed),
              .inr
                (literalCombinedFreshPhaseActivatedInstallationActivateTwo A
                  strategy hwin entrySeed))
          else
            let next := mega.advanceControls (one, two)
              ⟨own, delivered, .both⟩
            (.inl next.1, .inl next.2)
      | _, _ =>
          let next := mega.advanceControls (one, two)
            ⟨own, delivered, .both⟩
          (.inl next.1, .inl next.2)
  | .inr one, .inr two =>
      let nextOne :=
        literalCombinedFreshPhaseActivatedInstallationRecvOne A strategy hwin
          one own two delivered
      let nextTwo :=
        literalCombinedFreshPhaseActivatedInstallationRecvTwo A strategy hwin
          two delivered one own
      (.inr nextOne.1, .inr nextTwo.1)
  | .inl one, .inr two => (.inl one, .inr two)
  | .inr one, .inl two => (.inr one, .inl two)

/-- Away from a matching coupled seam, the honest close does not enter the
phase bank: it is exactly the guarded-Mega simultaneous transition, lifted
into the left summand. -/
theorem literalCombinedFreshPhaseActivatedHonestEntryClose_mega_of_not_enabled
    (fallback : Installation A strategy hwin)
    (fallbackTag : RetainedTag A strategy hwin)
    (one : (Mega A strategy hwin controllers initialBank
      fallbackTag).OneControl)
    (two : (Mega A strategy hwin controllers initialBank
      fallbackTag).TwoControl)
    (input : In₁ × In₂)
    (hdisabled :
      ¬ literalCombinedFreshPhaseActivatedHonestMegaEntryEnabled A strategy
        hwin controllers initialBank fallbackTag one two) :
    let mega := Mega A strategy hwin controllers initialBank fallbackTag
    let next := mega.advanceControls (one, two)
      ⟨input.1, input.2, Graph.both⟩
    literalCombinedFreshPhaseActivatedHonestEntryClose A strategy hwin
        controllers initialBank fallback fallbackTag (.inl one) input.1
          (.inl two) input.2 =
      (.inl next.1, .inl next.2) := by
  unfold literalCombinedFreshPhaseActivatedHonestMegaEntryEnabled at hdisabled
  unfold literalCombinedFreshPhaseActivatedHonestEntryClose
  cases hone : literalCombinedFreshPhaseActivatedMegaCoupledOne? A strategy hwin
      controllers initialBank fallbackTag one with
  | none => simp only [hone]
  | some installationOne =>
      cases htwo : literalCombinedFreshPhaseActivatedMegaCoupledTwo? A strategy
          hwin controllers initialBank fallbackTag two with
      | none => simp only [hone, htwo]
      | some installationTwo =>
          simp only [hone, htwo]
          split
          next heq =>
            subst installationTwo
            exact False.elim (hdisabled ⟨installationOne, hone, htwo⟩)
          next hne => rfl

/-! ## The honest handoff equations -/

/-- At a matching guarded coupled state the exact close records the current
installation and simultaneous input, and installs both initial controls of
the phase member rooted at their literal child occurrence. -/
theorem literalCombinedFreshPhaseActivatedHonestEntryClose_coupled
    (fallback : Installation A strategy hwin)
    (fallbackTag : RetainedTag A strategy hwin)
    (installation : Installation A strategy hwin)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (input : In₁ × In₂) :
    let coupled :=
      profiledRawJointHybridMegaGuardedCoupledControls A strategy hwin
        controllers initialBank fallbackTag installation oldOutputOne
          oldOutputTwo
    let entrySeed : EntrySeed A strategy hwin := (installation, input)
    literalCombinedFreshPhaseActivatedHonestEntryClose A strategy hwin
        controllers initialBank fallback fallbackTag (.inl coupled.1) input.1
          (.inl coupled.2) input.2 =
      (.inr
          (literalCombinedFreshPhaseActivatedInstallationActivateOne A
            strategy hwin entrySeed),
        .inr
          (literalCombinedFreshPhaseActivatedInstallationActivateTwo A
            strategy hwin entrySeed)) := by
  dsimp only
  simp [literalCombinedFreshPhaseActivatedHonestEntryClose,
    literalCombinedFreshPhaseActivatedMegaCoupledOne?,
    literalCombinedFreshPhaseActivatedMegaCoupledTwo?,
    profiledRawJointHybridMegaGuardedCoupledControls,
    initialProfiledRawJointHybridGuardedCoupledOne,
    initialProfiledRawJointHybridGuardedCoupledTwo]

/-- Audit of the process-one blind branch created at an honest entry.  The
closed continuation does not start from the literal entry occurrence: its
first no-receive output is the left staged sender attached to the phase
member's fixed pending-only initial state.  That state uses
`literalCombinedFreshPendingOnlyInitialKey`, hence the default input pair.

This equation deliberately stops before comparing the result with the open
guarded-Mega continuation.  No theorem currently identifies these two
outputs. -/
theorem
    literalCombinedFreshPhaseActivatedHonestEntry_closedNoRecvOne_output
    (fallback : Installation A strategy hwin)
    (fallbackTag : RetainedTag A strategy hwin)
    (installation : Installation A strategy hwin)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (entryInput : In₁ × In₂) (nextInput : In₁) :
    let coupled :=
      profiledRawJointHybridMegaGuardedCoupledControls A strategy hwin
        controllers initialBank fallbackTag installation oldOutputOne
          oldOutputTwo
    let entrySeed : EntrySeed A strategy hwin := (installation, entryInput)
    let closed :=
      literalCombinedFreshPhaseActivatedHonestEntryClose A strategy hwin
        controllers initialBank fallback fallbackTag (.inl coupled.1)
          entryInput.1 (.inl coupled.2) entryInput.2
    let package := EntrySeedPackage A strategy hwin entrySeed
    (literalCombinedFreshPhaseActivatedHonestEntryNoRecvOne A strategy hwin
        controllers initialBank fallback fallbackTag closed.1 nextInput).2 =
      (package.literalLeftSeamStagedSenderNoRecv A strategy hwin
        (package.literalCombinedFreshPendingOnlyInitialOneShared A strategy
          hwin).2.1 nextInput).1 := by
  dsimp only
  rw [literalCombinedFreshPhaseActivatedHonestEntryClose_coupled A strategy
    hwin controllers initialBank fallback fallbackTag installation oldOutputOne
      oldOutputTwo entryInput]
  simp only [literalCombinedFreshPhaseActivatedHonestEntryNoRecvOne,
    literalCombinedFreshPhaseActivatedInstallationNoRecvOne,
    literalCombinedFreshPhaseActivatedInstallationActivateOne,
    EntrySeedMember, EntrySeedPackage,
    literalCombinedFreshPhaseActivatedController,
    FiniteAcknowledgedDelayedCarrier.exactClosingPairedMealyController,
    FiniteAcknowledgedDelayedCarrier.pairedMealyController,
    FiniteAcknowledgedDelayedCarrier.noRecvMealy,
    literalCombinedFreshPhaseActivatedNoRecvOne]
  have hstage :
      (literalCombinedFreshPhaseActivatedPackageOfEntrySeed A strategy hwin
          (installation, entryInput)
        |>.literalCombinedFreshOneReceiver A strategy hwin
          (literalCombinedFreshPendingOnlyInitialOne A strategy hwin
            (literalCombinedFreshPhaseActivatedPackageOfEntrySeed A strategy
              hwin (installation, entryInput))).1
          (literalCombinedFreshPendingOnlyInitialOne A strategy hwin
            (literalCombinedFreshPhaseActivatedPackageOfEntrySeed A strategy
              hwin (installation, entryInput))).2.1).2.2.2 = none := by
    rfl
  have hready :=
    (literalCombinedFreshPhaseActivatedPackageOfEntrySeed A strategy hwin
      (installation, entryInput)
      |>.literalCombinedFreshRightActivationReady_eq_false_of_no_stage A
        strategy hwin
        (literalCombinedFreshPendingOnlyInitialOne A strategy hwin
          (literalCombinedFreshPhaseActivatedPackageOfEntrySeed A strategy
            hwin (installation, entryInput)))
        (literalCombinedFreshPendingOnlyInitialTwo A strategy hwin
          (literalCombinedFreshPhaseActivatedPackageOfEntrySeed A strategy
            hwin (installation, entryInput))) hstage).1
  rw [hready]
  simp [FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv,
    literalCombinedFreshOnePendingStep,
    literalCombinedFreshPendingOnlyInitialOne,
    literalCombinedFreshPendingOnlyInitialOneShared,
    literalCrossCombinedFreshOneSharedAt]

/-- Process-two mirror of
`literalCombinedFreshPhaseActivatedHonestEntry_closedNoRecvOne_output`. -/
theorem
    literalCombinedFreshPhaseActivatedHonestEntry_closedNoRecvTwo_output
    (fallback : Installation A strategy hwin)
    (fallbackTag : RetainedTag A strategy hwin)
    (installation : Installation A strategy hwin)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (entryInput : In₁ × In₂) (nextInput : In₂) :
    let coupled :=
      profiledRawJointHybridMegaGuardedCoupledControls A strategy hwin
        controllers initialBank fallbackTag installation oldOutputOne
          oldOutputTwo
    let entrySeed : EntrySeed A strategy hwin := (installation, entryInput)
    let closed :=
      literalCombinedFreshPhaseActivatedHonestEntryClose A strategy hwin
        controllers initialBank fallback fallbackTag (.inl coupled.1)
          entryInput.1 (.inl coupled.2) entryInput.2
    let package := EntrySeedPackage A strategy hwin entrySeed
    (literalCombinedFreshPhaseActivatedHonestEntryNoRecvTwo A strategy hwin
        controllers initialBank fallback fallbackTag closed.2 nextInput).2 =
      (package.literalRightSeamStagedSenderNoRecv A strategy hwin
        (package.literalCombinedFreshPendingOnlyInitialTwoShared A strategy
          hwin).2.1 nextInput).1 := by
  dsimp only
  rw [literalCombinedFreshPhaseActivatedHonestEntryClose_coupled A strategy
    hwin controllers initialBank fallback fallbackTag installation oldOutputOne
      oldOutputTwo entryInput]
  simp [literalCombinedFreshPhaseActivatedHonestEntryNoRecvTwo,
    literalCombinedFreshPhaseActivatedInstallationNoRecvTwo,
    literalCombinedFreshPhaseActivatedInstallationActivateTwo,
    EntrySeedMember, EntrySeedPackage,
    literalCombinedFreshPhaseActivatedController,
    FiniteAcknowledgedDelayedCarrier.exactClosingPairedMealyController,
    FiniteAcknowledgedDelayedCarrier.pairedMealyController,
    FiniteAcknowledgedDelayedCarrier.noRecvMealy,
    literalCombinedFreshPhaseActivatedNoRecvTwo,
    FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv,
    literalCombinedFreshTwoPendingStep,
    literalCombinedFreshPendingOnlyInitialTwo,
    literalCombinedFreshPendingOnlyInitialTwoShared,
    literalCrossCombinedFreshTwoSharedAt]

/-- The exact process-one coherence obligation created by an honest entry.
After unfolding the acknowledged fork, coherence is equivalent to equality
between the guarded-Mega strict continuation and the default-key phase
sender displayed by
`literalCombinedFreshPhaseActivatedHonestEntry_closedNoRecvOne_output`. -/
theorem
    literalCombinedFreshPhaseActivatedHonestEntry_blindOne_coherent_iff
    (fallback : Installation A strategy hwin)
    (fallbackTag : RetainedTag A strategy hwin)
    (installation : Installation A strategy hwin)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (entryInput : In₁ × In₂) (nextInput : In₁) :
    let coupled :=
      profiledRawJointHybridMegaGuardedCoupledControls A strategy hwin
        controllers initialBank fallbackTag installation oldOutputOne
          oldOutputTwo
    let opened :=
      literalCombinedFreshPhaseActivatedHonestEntryOpenRecvOne A strategy hwin
        controllers initialBank fallback fallbackTag (.inl coupled.1)
          entryInput.1 (.inl coupled.2) entryInput.2
    let closed :=
      literalCombinedFreshPhaseActivatedHonestEntryClose A strategy hwin
        controllers initialBank fallback fallbackTag (.inl coupled.1)
          entryInput.1 (.inl coupled.2) entryInput.2
    let state :
        FiniteAcknowledgedDelayedCarrier (Fin 5)
          (ProfiledRawJointGuardedCommonLiteralPhaseActivatedHonestEntryOneControl
            A strategy hwin controllers initialBank fallback fallbackTag) :=
      ⟨.fork 0
        { openControl := opened.1, closedControl := closed.1 }, none⟩
    let package :=
      EntrySeedPackage A strategy hwin (installation, entryInput)
    let mega := Mega A strategy hwin controllers initialBank fallbackTag
    FiniteAcknowledgedDelayedCarrier.NoRecvOutputCoherent
        (literalCombinedFreshPhaseActivatedHonestEntryNoRecvOne A strategy hwin
          controllers initialBank fallback fallbackTag) state nextInput ↔
      mega.outputOne
          (mega.noRecvOne
            (mega.recvOne coupled.1 entryInput.1 coupled.2 entryInput.2)
            nextInput) =
        (package.literalLeftSeamStagedSenderNoRecv A strategy hwin
          (package.literalCombinedFreshPendingOnlyInitialOneShared A strategy
            hwin).2.1 nextInput).1 := by
  dsimp only
  simp only [FiniteAcknowledgedDelayedCarrier.NoRecvOutputCoherent,
    FiniteDelayedFork.NoRecvMealyOutputCoherent,
    FiniteDelayedFork.noRecvMealyTable, FiniteDelayedFork.candidate_false,
    FiniteDelayedFork.candidate_true]
  rw [literalCombinedFreshPhaseActivatedHonestEntry_closedNoRecvOne_output A
    strategy hwin controllers initialBank fallback fallbackTag installation
      oldOutputOne oldOutputTwo entryInput nextInput]
  rfl

/-- Process-two mirror of the exact honest-entry coherence obligation. -/
theorem
    literalCombinedFreshPhaseActivatedHonestEntry_blindTwo_coherent_iff
    (fallback : Installation A strategy hwin)
    (fallbackTag : RetainedTag A strategy hwin)
    (installation : Installation A strategy hwin)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (entryInput : In₁ × In₂) (nextInput : In₂) :
    let coupled :=
      profiledRawJointHybridMegaGuardedCoupledControls A strategy hwin
        controllers initialBank fallbackTag installation oldOutputOne
          oldOutputTwo
    let opened :=
      literalCombinedFreshPhaseActivatedHonestEntryOpenRecvTwo A strategy hwin
        controllers initialBank fallback fallbackTag (.inl coupled.2)
          entryInput.2 (.inl coupled.1) entryInput.1
    let closed :=
      literalCombinedFreshPhaseActivatedHonestEntryClose A strategy hwin
        controllers initialBank fallback fallbackTag (.inl coupled.1)
          entryInput.1 (.inl coupled.2) entryInput.2
    let state :
        FiniteAcknowledgedDelayedCarrier (Fin 5)
          (ProfiledRawJointGuardedCommonLiteralPhaseActivatedHonestEntryTwoControl
            A strategy hwin controllers initialBank fallback fallbackTag) :=
      ⟨.fork 0
        { openControl := opened.1, closedControl := closed.2 }, none⟩
    let package :=
      EntrySeedPackage A strategy hwin (installation, entryInput)
    let mega := Mega A strategy hwin controllers initialBank fallbackTag
    FiniteAcknowledgedDelayedCarrier.NoRecvOutputCoherent
        (literalCombinedFreshPhaseActivatedHonestEntryNoRecvTwo A strategy hwin
          controllers initialBank fallback fallbackTag) state nextInput ↔
      mega.outputTwo
          (mega.noRecvTwo
            (mega.recvTwo coupled.2 entryInput.2 coupled.1 entryInput.1)
            nextInput) =
        (package.literalRightSeamStagedSenderNoRecv A strategy hwin
          (package.literalCombinedFreshPendingOnlyInitialTwoShared A strategy
            hwin).2.1 nextInput).1 := by
  dsimp only
  simp only [FiniteAcknowledgedDelayedCarrier.NoRecvOutputCoherent,
    FiniteDelayedFork.NoRecvMealyOutputCoherent,
    FiniteDelayedFork.noRecvMealyTable, FiniteDelayedFork.candidate_false,
    FiniteDelayedFork.candidate_true]
  rw [literalCombinedFreshPhaseActivatedHonestEntry_closedNoRecvTwo_output A
    strategy hwin controllers initialBank fallback fallbackTag installation
      oldOutputOne oldOutputTwo entryInput nextInput]
  rfl

/-- The two open receive outputs used by the acknowledged relay are exactly
the outputs of the pre-existing guarded-mega simultaneous transition.
Consequently the splice changes only the closed continuation controls; all
literal-prefix equations already proved for the mega front remain applicable
to the entry round. -/
theorem literalCombinedFreshPhaseActivatedHonestEntryOpen_outputs_coupled
    (fallback : Installation A strategy hwin)
    (fallbackTag : RetainedTag A strategy hwin)
    (installation : Installation A strategy hwin)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (input : In₁ × In₂) :
    let coupled :=
      profiledRawJointHybridMegaGuardedCoupledControls A strategy hwin
        controllers initialBank fallbackTag installation oldOutputOne
          oldOutputTwo
    let mega := Mega A strategy hwin controllers initialBank fallbackTag
    ((literalCombinedFreshPhaseActivatedHonestEntryOpenRecvOne A strategy hwin
        controllers initialBank fallback fallbackTag (.inl coupled.1) input.1
          (.inl coupled.2) input.2).2,
      (literalCombinedFreshPhaseActivatedHonestEntryOpenRecvTwo A strategy hwin
        controllers initialBank fallback fallbackTag (.inl coupled.2) input.2
          (.inl coupled.1) input.1).2) =
      (mega.outputOne (mega.recvOne coupled.1 input.1 coupled.2 input.2),
        mega.outputTwo
          (mega.recvTwo coupled.2 input.2 coupled.1 input.1)) := by
  simp [literalCombinedFreshPhaseActivatedHonestEntryOpenRecvOne,
    literalCombinedFreshPhaseActivatedHonestEntryOpenRecvTwo,
    profiledRawJointHybridMegaGuardedCoupledControls]

/-- The two strict-receiver projections started from one guarded installation
emit the simultaneous physical output of the exact guarded pair represented
by that installation. -/
theorem
    literalCombinedFreshPhaseActivatedGuardedStartReceivers_outputs_eq_pair
    (installation : Installation A strategy hwin)
    (input : In₁ × In₂) :
    ((startProfiledRawJointHybridGuardedLeftReceiver A strategy hwin
        (initialProfiledRawJointHybridGuardedCoupledTwo A strategy hwin
          installation) input.1 input.2).1,
      (startProfiledRawJointHybridGuardedRightReceiver A strategy hwin
        (initialProfiledRawJointHybridGuardedCoupledOne A strategy hwin
          installation) input.2 input.1).1) =
      profiledRawJointGuardedCommonPairBothOutput A strategy hwin
        (profiledRawJointHybridGuardedCommonPairAt A strategy hwin
          installation) input := by
  cases installation with
  | inl initial =>
      let pair :=
        profiledRawJointHybridGuardedCommonPairAt A strategy hwin (.inl initial)
      change
        (pairedLeftInformedForRow .both
            (pair.leftRootRecord A strategy hwin input).2.1.physical,
          pairedRightInformedForRow .both
            (pair.rightRootRecord A strategy hwin input).2.1.physical) =
          ((pair.rightRootRecord A strategy hwin input).2.1.physical.closingBoth,
            (pair.leftRootRecord A strategy hwin input).2.1.physical.closingBoth)
      exact Prod.ext
        (pair.root_outputOne A strategy hwin input).symm
        (pair.root_outputTwo A strategy hwin input).symm
  | inr recurrent =>
      let pair :=
        profiledRawJointHybridGuardedCommonPairAt A strategy hwin (.inr recurrent)
      change
        (pairedLeftInformedForRow .both
            (pair.leftRootRecord A strategy hwin input).2.1.physical,
          pairedRightInformedForRow .both
            (pair.rightRootRecord A strategy hwin input).2.1.physical) =
          ((pair.rightRootRecord A strategy hwin input).2.1.physical.closingBoth,
            (pair.leftRootRecord A strategy hwin input).2.1.physical.closingBoth)
      exact Prod.ext
        (pair.root_outputOne A strategy hwin input).symm
        (pair.root_outputTwo A strategy hwin input).symm

/-- The guarded pair stored by an installation emits the literal strategy
outputs at the occurrence represented by that same installation. -/
theorem literalCombinedFreshPhaseActivatedInstallationPair_outputs_literal
    (installation : Installation A strategy hwin)
    (input : In₁ × In₂) :
    profiledRawJointGuardedCommonPairBothOutput A strategy hwin
        (profiledRawJointHybridGuardedCommonPairAt A strategy hwin
          installation) input =
      let point :=
        literalCombinedFreshPhaseActivatedPointOfInstallation A strategy hwin
          installation
      let round := nextRound strategy (point.world A strategy).procOne.bothHistory
        ⟨input.1, input.2, Graph.both⟩
      (round.outputOne, round.outputTwo) := by
  let point :=
    literalCombinedFreshPhaseActivatedPointOfInstallation A strategy hwin
      installation
  rw [← literalCombinedFreshPhaseActivatedPointOfInstallation_move A strategy
    hwin installation]
  have hclosing :
      profiledRawJointGuardedCommonPairBothOutput A strategy hwin
          (point.move A strategy hwin) input =
        (pairedLeftInformedForRow .both
            ((point.move A strategy hwin).leftRootRecord A strategy hwin input
              ).2.1.physical,
          pairedRightInformedForRow .both
            ((point.move A strategy hwin).rightRootRecord A strategy hwin input
              ).2.1.physical) := by
    apply Prod.ext
    · exact (point.move A strategy hwin).root_outputOne A strategy hwin input
    · exact (point.move A strategy hwin).root_outputTwo A strategy hwin input
  rw [hclosing]
  let family := profiledRawJointCommonWorldFamily A point.parent
  let direction := profiledRawJointBothRestartDirection point.incoming
  have hchild : family.semanticChild A direction =
      profiledRawJointCommonWorldFamily A (point.world A strategy) :=
    profiledRawJointCommonWorld_semanticChild_eq_bothRestart A point.parent
      point.incoming
  simpa [point, family, direction,
    ProfiledRawJointGuardedCommonSemanticPoint.move,
    profiledRawJointGuardedCommonPairOfWorld,
    profiledRawJointGuardedCommonRightMoveOfWorld,
    profiledRawJointGuardedCommonLeftMoveOfWorld,
    ProfiledRawJointGuardedCommonPair.rightRootRecord,
    ProfiledRawJointGuardedCommonPair.leftRootRecord] using
      (profiledRawJointGuardedSiblingControllerRootRecords_bothOutput_eq_literal
        A hwin family direction (point.world A strategy) hchild false false
          input)

/-- At a matching coupled Mega state, the two actual receive outputs are the
literal simultaneous outputs at the exact occurrence represented by the
installation.  No rationally reselected successor representative appears in
this equation. -/
theorem literalCombinedFreshPhaseActivatedMegaCoupled_outputs_literal
    (fallbackTag : RetainedTag A strategy hwin)
    (installation : Installation A strategy hwin)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (input : In₁ × In₂) :
    let coupled :=
      profiledRawJointHybridMegaGuardedCoupledControls A strategy hwin
        controllers initialBank fallbackTag installation oldOutputOne
          oldOutputTwo
    let mega := Mega A strategy hwin controllers initialBank fallbackTag
    let point :=
      literalCombinedFreshPhaseActivatedPointOfInstallation A strategy hwin
        installation
    let round := nextRound strategy (point.world A strategy).procOne.bothHistory
      ⟨input.1, input.2, Graph.both⟩
    (mega.outputOne (mega.recvOne coupled.1 input.1 coupled.2 input.2),
      mega.outputTwo (mega.recvTwo coupled.2 input.2 coupled.1 input.1)) =
      (round.outputOne, round.outputTwo) := by
  dsimp only
  change
    ((startProfiledRawJointHybridGuardedLeftReceiver A strategy hwin
        (initialProfiledRawJointHybridGuardedCoupledTwo A strategy hwin
          installation) input.1 input.2).1,
      (startProfiledRawJointHybridGuardedRightReceiver A strategy hwin
        (initialProfiledRawJointHybridGuardedCoupledOne A strategy hwin
          installation) input.2 input.1).1) = _
  rw [literalCombinedFreshPhaseActivatedGuardedStartReceivers_outputs_eq_pair
    A strategy hwin installation input]
  exact literalCombinedFreshPhaseActivatedInstallationPair_outputs_literal A
    strategy hwin installation input

omit [DecidableEq In₁] [DecidableEq In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- The literal simultaneous letter at an honest coupled entry advances the
actual checker from the represented occurrence's `.both` coordinate to the
`.both` coordinate of the package selected by `(installation,input)`.  Both
sides use the same literal world, so the equation does not identify a
reselected semantic representative with this occurrence. -/
theorem literalCombinedFreshPhaseActivatedHonestEntry_step_eq_installedState
    (installation : Installation A strategy hwin)
    (input : In₁ × In₂) :
    let point :=
      literalCombinedFreshPhaseActivatedPointOfInstallation A strategy hwin
        installation
    let round := nextRound strategy (point.world A strategy).procOne.bothHistory
      ⟨input.1, input.2, Graph.both⟩
    let entrySeed : EntrySeed A strategy hwin := (installation, input)
    A.step
        (pairedCodeStateForRow A .both
          ((point.world A strategy).procOneSlot A).1.1)
        (bothRoundRecord input round.outputOne round.outputTwo) =
      pairedCodeStateForRow A .both
        (((literalCombinedFreshPhaseActivatedPointOfEntrySeed A strategy hwin
          entrySeed).world A strategy).procOneSlot A).1.1 := by
  dsimp only
  let world :=
    (literalCombinedFreshPhaseActivatedPointOfInstallation A strategy hwin
      installation).world A strategy
  change
    A.step ((world.procOne A).code (A := A)).2
        (bothRoundRecord input
          (nextRound strategy (world.procOne A).bothHistory
            ⟨input.1, input.2, Graph.both⟩).outputOne
          (nextRound strategy (world.procOne A).bothHistory
            ⟨input.1, input.2, Graph.both⟩).outputTwo) =
      (((profiledRawJointCommonWorldAfterBoth A world input).procOne A).code
        (A := A)).2
  simp [profiledRawJointCommonWorldAfterBoth,
    profiledRawRightCommonBaseWorld,
    ProfiledRawJointCommonBaseWorld.procOneMember,
    ProfiledRawJointCommonBaseWorld.procOne,
    profiledRawProcOneRowHistory, procOneFreshPair,
    ProcOnePairedEntryRep.code,
    entryState, bothRoundRecord, nextRound, History.append,
    List.foldl_append]

/-- One finite local controller that starts in the honest guarded-mega front
and enters an occurrence-indexed phase-activated member only at a physically
resolved simultaneous coupled receive. -/
noncomputable def literalCombinedFreshPhaseActivatedHonestMegaEntryController
    (fallback : Installation A strategy hwin)
    (fallbackTag : RetainedTag A strategy hwin) :
    FinitePairedMealyController In₁ In₂ Out₁ Out₂ :=
  FiniteAcknowledgedDelayedCarrier.exactClosingPairedMealyController
    (.inl (Mega A strategy hwin controllers initialBank fallbackTag).initialOne)
    (.inl (Mega A strategy hwin controllers initialBank fallbackTag).initialTwo)
    (literalCombinedFreshPhaseActivatedHonestEntryNoRecvOne A strategy hwin
      controllers initialBank fallback fallbackTag)
    (literalCombinedFreshPhaseActivatedHonestEntryNoRecvTwo A strategy hwin
      controllers initialBank fallback fallbackTag)
    (literalCombinedFreshPhaseActivatedHonestEntryOpenRecvOne A strategy hwin
      controllers initialBank fallback fallbackTag)
    (literalCombinedFreshPhaseActivatedHonestEntryOpenRecvTwo A strategy hwin
      controllers initialBank fallback fallbackTag)
    (literalCombinedFreshPhaseActivatedHonestEntryClose A strategy hwin
      controllers initialBank fallback fallbackTag)

/-- Moore presentation consumed by the global trace and readback layers. -/
noncomputable def
    literalCombinedFreshPhaseActivatedHonestMegaEntryPhysicalController
    (fallback : Installation A strategy hwin)
    (fallbackTag : RetainedTag A strategy hwin) :
    FinitePairedPhysicalController In₁ In₂ Out₁ Out₂ :=
  (literalCombinedFreshPhaseActivatedHonestMegaEntryController A strategy hwin
    controllers initialBank fallback fallbackTag).mooreize

/-- Canonical proof-side pair of unwrapped controls before round `n` of the
honest Mega/phase splice.  This trace is used only to state which finite
control pair the acknowledged physical relays select. -/
noncomputable def
    literalCombinedFreshPhaseActivatedHonestMegaEntrySemanticTrace
    (fallback : Installation A strategy hwin)
    (fallbackTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) : Nat →
      ProfiledRawJointGuardedCommonLiteralPhaseActivatedHonestEntryOneControl
          A strategy hwin controllers initialBank fallback fallbackTag ×
        ProfiledRawJointGuardedCommonLiteralPhaseActivatedHonestEntryTwoControl
          A strategy hwin controllers initialBank fallback fallbackTag :=
  FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace
    (.inl (Mega A strategy hwin controllers initialBank fallbackTag).initialOne)
    (.inl (Mega A strategy hwin controllers initialBank fallbackTag).initialTwo)
    (literalCombinedFreshPhaseActivatedHonestEntryNoRecvOne A strategy hwin
      controllers initialBank fallback fallbackTag)
    (literalCombinedFreshPhaseActivatedHonestEntryNoRecvTwo A strategy hwin
      controllers initialBank fallback fallbackTag)
    (literalCombinedFreshPhaseActivatedHonestEntryOpenRecvOne A strategy hwin
      controllers initialBank fallback fallbackTag)
    (literalCombinedFreshPhaseActivatedHonestEntryOpenRecvTwo A strategy hwin
      controllers initialBank fallback fallbackTag)
    (literalCombinedFreshPhaseActivatedHonestEntryClose A strategy hwin
      controllers initialBank fallback fallbackTag) env

/-- At every physical time, the two acknowledged relay controls select the
canonical unwrapped controls of the honest Mega/phase splice. -/
theorem literalCombinedFreshPhaseActivatedHonestMegaEntryPhysicalTrace_pairSelects
    (fallback : Installation A strategy hwin)
    (fallbackTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    let actual :=
      literalCombinedFreshPhaseActivatedHonestMegaEntryPhysicalController A
        strategy hwin controllers initialBank fallback fallbackTag
    let state := actual.globalMachine.globalStateTrace env n
    let semantic :=
      literalCombinedFreshPhaseActivatedHonestMegaEntrySemanticTrace A strategy
        hwin controllers initialBank fallback fallbackTag env n
    FiniteAcknowledgedDelayedCarrier.PairSelects
      state.1.1 state.2.1 semantic.1 semantic.2 := by
  simpa [literalCombinedFreshPhaseActivatedHonestMegaEntryPhysicalController,
    literalCombinedFreshPhaseActivatedHonestMegaEntryController,
    literalCombinedFreshPhaseActivatedHonestMegaEntrySemanticTrace] using
    (FiniteAcknowledgedDelayedCarrier.exactClosingPairedMealyController_globalStateTrace_pairSelects
      (.inl
        (Mega A strategy hwin controllers initialBank fallbackTag).initialOne)
      (.inl
        (Mega A strategy hwin controllers initialBank fallbackTag).initialTwo)
      (literalCombinedFreshPhaseActivatedHonestEntryNoRecvOne A strategy hwin
        controllers initialBank fallback fallbackTag)
      (literalCombinedFreshPhaseActivatedHonestEntryNoRecvTwo A strategy hwin
        controllers initialBank fallback fallbackTag)
      (literalCombinedFreshPhaseActivatedHonestEntryOpenRecvOne A strategy hwin
        controllers initialBank fallback fallbackTag)
      (literalCombinedFreshPhaseActivatedHonestEntryOpenRecvTwo A strategy hwin
        controllers initialBank fallback fallbackTag)
      (literalCombinedFreshPhaseActivatedHonestEntryClose A strategy hwin
      controllers initialBank fallback fallbackTag)
      env n)

/-- The actual round word emitted by the Moore presentation of the honest
Mega/phase splice.  Its letter at time `n` uses the environment inputs and
graph at `n`, and the two Moore outputs after the physical transition of that
round. -/
noncomputable def
    literalCombinedFreshPhaseActivatedHonestMegaEntryPhysicalWord
    (fallback : Installation A strategy hwin)
    (fallbackTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) :
    OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂) :=
  let controller :=
    literalCombinedFreshPhaseActivatedHonestMegaEntryPhysicalController A
      strategy hwin controllers initialBank fallback fallbackTag
  controller.globalMachine.globalMachineTraceWord controller.globalOutputOne
    controller.globalOutputTwo env

/-- An actual pre-entry round triggers the honest phase close exactly when it
is simultaneous and the guarded-Mega trace exposes the same installation at
both endpoints. -/
def literalCombinedFreshPhaseActivatedHonestMegaEntryTrigger
    (fallbackTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) : Prop :=
  let mega := Mega A strategy hwin controllers initialBank fallbackTag
  let state := mega.globalMachine.globalStateTrace env n
  (env n).graph = .both ∧
    literalCombinedFreshPhaseActivatedHonestMegaEntryEnabled A strategy hwin
      controllers initialBank fallbackTag state.1 state.2

/-- One-step semantic preservation before the first honest-entry trigger.
Strict rounds use the open Mega transitions.  A simultaneous round uses the
Mega close because the common-installation guard is false. -/
theorem
    literalCombinedFreshPhaseActivatedHonestMegaEntrySemanticTrace_succ_mega
    (fallback : Installation A strategy hwin)
    (fallbackTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (hcurrent :
      let mega := Mega A strategy hwin controllers initialBank fallbackTag
      let state := mega.globalMachine.globalStateTrace env n
      literalCombinedFreshPhaseActivatedHonestMegaEntrySemanticTrace A strategy
        hwin controllers initialBank fallback fallbackTag env n =
          (.inl state.1, .inl state.2))
    (hnotTrigger :
      ¬ literalCombinedFreshPhaseActivatedHonestMegaEntryTrigger A strategy
        hwin controllers initialBank fallbackTag env n) :
    let mega := Mega A strategy hwin controllers initialBank fallbackTag
    let nextState := mega.globalMachine.globalStateTrace env (n + 1)
    literalCombinedFreshPhaseActivatedHonestMegaEntrySemanticTrace A strategy
        hwin controllers initialBank fallback fallbackTag env (n + 1) =
      (.inl nextState.1, .inl nextState.2) := by
  let mega := Mega A strategy hwin controllers initialBank fallbackTag
  let state := mega.globalMachine.globalStateTrace env n
  change
    literalCombinedFreshPhaseActivatedHonestMegaEntrySemanticTrace A strategy
        hwin controllers initialBank fallback fallbackTag env n =
      (.inl state.1, .inl state.2) at hcurrent
  unfold literalCombinedFreshPhaseActivatedHonestMegaEntrySemanticTrace at hcurrent
  change ¬ ((env n).graph = .both ∧
    literalCombinedFreshPhaseActivatedHonestMegaEntryEnabled A strategy hwin
      controllers initialBank fallbackTag state.1 state.2) at hnotTrigger
  dsimp only
  cases hgraph : (env n).graph with
  | right =>
      rw [literalCombinedFreshPhaseActivatedHonestMegaEntrySemanticTrace,
        FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace,
        hgraph]
      rw [hcurrent, FiniteGlobalRoundMachine.globalStateTrace_succ]
      simp only
        [literalCombinedFreshPhaseActivatedHonestEntryNoRecvOne,
          literalCombinedFreshPhaseActivatedHonestEntryOpenRecvTwo,
          FinitePairedPhysicalController.globalMachine_step,
          FinitePairedPhysicalController.advanceControls, hgraph]
      rfl
  | left =>
      rw [literalCombinedFreshPhaseActivatedHonestMegaEntrySemanticTrace,
        FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace,
        hgraph]
      rw [hcurrent, FiniteGlobalRoundMachine.globalStateTrace_succ]
      simp only
        [literalCombinedFreshPhaseActivatedHonestEntryOpenRecvOne,
          literalCombinedFreshPhaseActivatedHonestEntryNoRecvTwo,
          FinitePairedPhysicalController.globalMachine_step,
          FinitePairedPhysicalController.advanceControls, hgraph]
      rfl
  | both =>
      have hdisabled :
          ¬ literalCombinedFreshPhaseActivatedHonestMegaEntryEnabled A
            strategy hwin controllers initialBank fallbackTag state.1 state.2 :=
        fun henabled ↦ hnotTrigger ⟨hgraph, henabled⟩
      have hclose :=
        literalCombinedFreshPhaseActivatedHonestEntryClose_mega_of_not_enabled
          A strategy hwin controllers initialBank fallback fallbackTag state.1
            state.2 ((env n).inputOne, (env n).inputTwo) hdisabled
      rw [literalCombinedFreshPhaseActivatedHonestMegaEntrySemanticTrace,
        FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace,
        hgraph]
      rw [hcurrent, hclose, FiniteGlobalRoundMachine.globalStateTrace_succ]
      simp only [FinitePairedPhysicalController.globalMachine_step,
        FinitePairedPhysicalController.advanceControls, hgraph]
      rfl

/-- Before the first actual trigger, the canonical proof-side splice is not
merely in the Mega summand: it is exactly the guarded-Mega global trace on the
same environment prefix. -/
theorem
    literalCombinedFreshPhaseActivatedHonestMegaEntrySemanticTrace_eq_mega_of_noTrigger
    (fallback : Installation A strategy hwin)
    (fallbackTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (cut : Nat)
    (hnoTrigger : ∀ n : Nat, n < cut →
      ¬ literalCombinedFreshPhaseActivatedHonestMegaEntryTrigger A strategy
        hwin controllers initialBank fallbackTag env n) :
    let mega := Mega A strategy hwin controllers initialBank fallbackTag
    let state := mega.globalMachine.globalStateTrace env cut
    literalCombinedFreshPhaseActivatedHonestMegaEntrySemanticTrace A strategy
        hwin controllers initialBank fallback fallbackTag env cut =
      (.inl state.1, .inl state.2) := by
  induction cut with
  | zero => rfl
  | succ cut ih =>
      apply
        literalCombinedFreshPhaseActivatedHonestMegaEntrySemanticTrace_succ_mega
          A strategy hwin controllers initialBank fallback fallbackTag env cut
      · exact ih (fun n hn ↦ hnoTrigger n (by omega))
      · exact hnoTrigger cut (by omega)

/-- After the first initial simultaneous round, the proof-side splice is the
lift of the actual guarded-Mega state after that round. -/
theorem
    literalCombinedFreshPhaseActivatedHonestMegaEntrySemanticTrace_one
    (fallback : Installation A strategy hwin)
    (fallbackTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (first : In₁ × In₂)
    (hfirst : env 0 = ⟨first.1, first.2, Graph.both⟩) :
    let mega := Mega A strategy hwin controllers initialBank fallbackTag
    let state := mega.globalMachine.globalStateTrace env 1
    literalCombinedFreshPhaseActivatedHonestMegaEntrySemanticTrace A strategy
        hwin controllers initialBank fallback fallbackTag env 1 =
      (.inl state.1, .inl state.2) := by
  dsimp only
  rw [show 1 = 0 + 1 by omega,
    literalCombinedFreshPhaseActivatedHonestMegaEntrySemanticTrace,
    FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace, hfirst,
    FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace]
  simp only [literalCombinedFreshPhaseActivatedHonestEntryClose,
    literalCombinedFreshPhaseActivatedMegaCoupledOne?_initial,
    literalCombinedFreshPhaseActivatedMegaCoupledTwo?_initial]
  rw [FiniteGlobalRoundMachine.globalStateTrace_succ,
    FiniteGlobalRoundMachine.globalStateTrace_zero, hfirst]
  rfl

set_option maxHeartbeats 1000000 in
/-- On two initial simultaneous rounds, the proof-side splice has not yet
entered the phase bank: it reaches exactly the guarded-Mega coupled controls
indexed by the two observed input pairs. -/
theorem
    literalCombinedFreshPhaseActivatedHonestMegaEntrySemanticTrace_two
    (fallback : Installation A strategy hwin)
    (fallbackTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (first current : In₁ × In₂)
    (hfirst : env 0 = ⟨first.1, first.2, Graph.both⟩)
    (hcurrent : env 1 = ⟨current.1, current.2, Graph.both⟩) :
    let installation : Installation A strategy hwin :=
      .inl ⟨first, current⟩
    let outputs :=
      profiledRawJointInitialCommonBothOutput A strategy (first, current)
    let coupled :=
      profiledRawJointHybridMegaGuardedCoupledControls A strategy hwin
        controllers initialBank fallbackTag installation outputs.1 outputs.2
    literalCombinedFreshPhaseActivatedHonestMegaEntrySemanticTrace A strategy
        hwin controllers initialBank fallback fallbackTag env 2 =
      (.inl coupled.1, .inl coupled.2) := by
  dsimp only
  rw [show 2 = 1 + 1 by omega,
    literalCombinedFreshPhaseActivatedHonestMegaEntrySemanticTrace,
    FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace, hcurrent,
    show 1 = 0 + 1 by omega,
    FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace, hfirst,
    FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace]
  simp only
    [literalCombinedFreshPhaseActivatedHonestEntryClose,
      literalCombinedFreshPhaseActivatedMegaCoupledOne?_initial,
      literalCombinedFreshPhaseActivatedMegaCoupledTwo?_initial]
  rw [profiledRawJointHybridMegaGuardedLinked_root_both A strategy hwin
    controllers initialBank fallbackTag first.1 first.2]
  simp only
    [literalCombinedFreshPhaseActivatedMegaCoupledOne?_initialShadow,
      literalCombinedFreshPhaseActivatedMegaCoupledTwo?_initialShadow]
  rw [profiledRawJointHybridMegaGuardedLinked_initialShadows_both A strategy
    hwin controllers initialBank fallbackTag
      (profiledRawJointHybridInitialRootRecvOne A strategy hwin controllers
        first).2
      (profiledRawJointHybridInitialRootRecvTwo A strategy hwin controllers
        first).2
      (profiledRawJointHybridInitialRootRecvOne A strategy hwin controllers
        first).1
      (profiledRawJointHybridInitialRootRecvTwo A strategy hwin controllers
        first).1 current.1 current.2]
  have houtputs :=
    profiledRawJointHybridInitialToSecondShadows_outputs A strategy hwin
      controllers first current
  have hone := congrArg Prod.fst houtputs
  have htwo := congrArg Prod.snd houtputs
  dsimp only at hone htwo
  simp only [profiledRawJointHybridMegaInitialToCoupledOne,
    profiledRawJointHybridMegaInitialToCoupledTwo]
  rw [hone, htwo]
  simp [profiledRawJointHybridMegaGuardedCoupledControls,
    profiledRawJointHybridInitialToSecondOneShadow,
    profiledRawJointHybridInitialToSecondTwoShadow,
    profiledRawJointHybridInitialCommonControl]

/-- Before bank entry, simultaneous receive outputs of the acknowledged
splice are exactly those of the selected guarded-Mega controls. -/
theorem
    literalCombinedFreshPhaseActivatedHonestMegaEntry_both_outputs_mega_of_pairSelects
    (fallback : Installation A strategy hwin)
    (fallbackTag : RetainedTag A strategy hwin)
    (megaOne : (Mega A strategy hwin controllers initialBank
      fallbackTag).OneControl)
    (megaTwo : (Mega A strategy hwin controllers initialBank
      fallbackTag).TwoControl)
    (input : In₁ × In₂)
    (one :
      (literalCombinedFreshPhaseActivatedHonestMegaEntryController A strategy
        hwin controllers initialBank fallback fallbackTag).OneControl)
    (two :
      (literalCombinedFreshPhaseActivatedHonestMegaEntryController A strategy
        hwin controllers initialBank fallback fallbackTag).TwoControl)
    (hselects : FiniteAcknowledgedDelayedCarrier.PairSelects one two
      (.inl megaOne) (.inl megaTwo)) :
    let controller :=
      literalCombinedFreshPhaseActivatedHonestMegaEntryController A strategy
        hwin controllers initialBank fallback fallbackTag
    let mega := Mega A strategy hwin controllers initialBank fallbackTag
    ((controller.recvOne one input.1 two input.2).2,
      (controller.recvTwo two input.2 one input.1).2) =
      (mega.outputOne (mega.recvOne megaOne input.1 megaTwo input.2),
        mega.outputTwo (mega.recvTwo megaTwo input.2 megaOne input.1)) := by
  dsimp only at hselects ⊢
  rcases hselects with ⟨hone, htwo⟩
  change FiniteAcknowledgedDelayedCarrier.resolvedControl one two =
    .inl megaOne at hone
  change FiniteAcknowledgedDelayedCarrier.resolvedControl two one =
    .inl megaTwo at htwo
  change
    ((literalCombinedFreshPhaseActivatedHonestEntryOpenRecvOne A strategy hwin
        controllers initialBank fallback fallbackTag
          (FiniteAcknowledgedDelayedCarrier.resolvedControl one two) input.1
          (FiniteAcknowledgedDelayedCarrier.resolvedControl two one)
          input.2).2,
      (literalCombinedFreshPhaseActivatedHonestEntryOpenRecvTwo A strategy hwin
        controllers initialBank fallback fallbackTag
          (FiniteAcknowledgedDelayedCarrier.resolvedControl two one) input.2
          (FiniteAcknowledgedDelayedCarrier.resolvedControl one two)
          input.1).2) = _
  rw [hone, htwo]
  rfl

/-- Before bank entry, a strict-right round emits the selected guarded-Mega
outputs.  The receiving endpoint is unconditional; the blind process-one
endpoint needs exactly the acknowledged relay's local no-receive coherence
hypothesis.  `PairSelects` alone cannot imply this equality. -/
theorem
    literalCombinedFreshPhaseActivatedHonestMegaEntry_strictRight_outputs_mega_of_pairSelects
    (fallback : Installation A strategy hwin)
    (fallbackTag : RetainedTag A strategy hwin)
    (megaOne : (Mega A strategy hwin controllers initialBank
      fallbackTag).OneControl)
    (megaTwo : (Mega A strategy hwin controllers initialBank
      fallbackTag).TwoControl)
    (input : In₁ × In₂)
    (one :
      (literalCombinedFreshPhaseActivatedHonestMegaEntryController A strategy
        hwin controllers initialBank fallback fallbackTag).OneControl)
    (two :
      (literalCombinedFreshPhaseActivatedHonestMegaEntryController A strategy
        hwin controllers initialBank fallback fallbackTag).TwoControl)
    (hselects : FiniteAcknowledgedDelayedCarrier.PairSelects one two
      (.inl megaOne) (.inl megaTwo))
    (hcoherent :
      FiniteAcknowledgedDelayedCarrier.NoRecvOutputCoherent
        (literalCombinedFreshPhaseActivatedHonestEntryNoRecvOne A strategy hwin
          controllers initialBank fallback fallbackTag) one input.1) :
    let controller :=
      literalCombinedFreshPhaseActivatedHonestMegaEntryController A strategy
        hwin controllers initialBank fallback fallbackTag
    let mega := Mega A strategy hwin controllers initialBank fallbackTag
    ((controller.noRecvOne one input.1).2,
      (controller.recvTwo two input.2 one input.1).2) =
      (mega.outputOne (mega.noRecvOne megaOne input.1),
        mega.outputTwo (mega.recvTwo megaTwo input.2 megaOne input.1)) := by
  dsimp only at hselects ⊢
  rcases hselects with ⟨hone, htwo⟩
  change FiniteAcknowledgedDelayedCarrier.resolvedControl one two =
    .inl megaOne at hone
  change FiniteAcknowledgedDelayedCarrier.resolvedControl two one =
    .inl megaTwo at htwo
  change
    ((FiniteAcknowledgedDelayedCarrier.noRecvMealy
        (literalCombinedFreshPhaseActivatedHonestEntryNoRecvOne A strategy hwin
          controllers initialBank fallback fallbackTag) one input.1).2,
      (literalCombinedFreshPhaseActivatedHonestEntryOpenRecvTwo A strategy hwin
        controllers initialBank fallback fallbackTag
          (FiniteAcknowledgedDelayedCarrier.resolvedControl two one) input.2
          (FiniteAcknowledgedDelayedCarrier.resolvedControl one two)
          input.1).2) = _
  rw [FiniteAcknowledgedDelayedCarrier.noRecvMealy_output_eq_resolvedControl
    (literalCombinedFreshPhaseActivatedHonestEntryNoRecvOne A strategy hwin
      controllers initialBank fallback fallbackTag) one two input.1 hcoherent,
    hone, htwo]
  rfl

/-- Strict-left mirror of the preceding selected-output equation.  Here only
process two is blind, so coherence is required only for its no-receive map. -/
theorem
    literalCombinedFreshPhaseActivatedHonestMegaEntry_strictLeft_outputs_mega_of_pairSelects
    (fallback : Installation A strategy hwin)
    (fallbackTag : RetainedTag A strategy hwin)
    (megaOne : (Mega A strategy hwin controllers initialBank
      fallbackTag).OneControl)
    (megaTwo : (Mega A strategy hwin controllers initialBank
      fallbackTag).TwoControl)
    (input : In₁ × In₂)
    (one :
      (literalCombinedFreshPhaseActivatedHonestMegaEntryController A strategy
        hwin controllers initialBank fallback fallbackTag).OneControl)
    (two :
      (literalCombinedFreshPhaseActivatedHonestMegaEntryController A strategy
        hwin controllers initialBank fallback fallbackTag).TwoControl)
    (hselects : FiniteAcknowledgedDelayedCarrier.PairSelects one two
      (.inl megaOne) (.inl megaTwo))
    (hcoherent :
      FiniteAcknowledgedDelayedCarrier.NoRecvOutputCoherent
        (literalCombinedFreshPhaseActivatedHonestEntryNoRecvTwo A strategy hwin
          controllers initialBank fallback fallbackTag) two input.2) :
    let controller :=
      literalCombinedFreshPhaseActivatedHonestMegaEntryController A strategy
        hwin controllers initialBank fallback fallbackTag
    let mega := Mega A strategy hwin controllers initialBank fallbackTag
    ((controller.recvOne one input.1 two input.2).2,
      (controller.noRecvTwo two input.2).2) =
      (mega.outputOne (mega.recvOne megaOne input.1 megaTwo input.2),
        mega.outputTwo (mega.noRecvTwo megaTwo input.2)) := by
  dsimp only at hselects ⊢
  rcases hselects with ⟨hone, htwo⟩
  change FiniteAcknowledgedDelayedCarrier.resolvedControl one two =
    .inl megaOne at hone
  change FiniteAcknowledgedDelayedCarrier.resolvedControl two one =
    .inl megaTwo at htwo
  change
    ((literalCombinedFreshPhaseActivatedHonestEntryOpenRecvOne A strategy hwin
        controllers initialBank fallback fallbackTag
          (FiniteAcknowledgedDelayedCarrier.resolvedControl one two) input.1
          (FiniteAcknowledgedDelayedCarrier.resolvedControl two one)
          input.2).2,
      (FiniteAcknowledgedDelayedCarrier.noRecvMealy
        (literalCombinedFreshPhaseActivatedHonestEntryNoRecvTwo A strategy hwin
          controllers initialBank fallback fallbackTag) two input.2).2) = _
  rw [FiniteAcknowledgedDelayedCarrier.noRecvMealy_output_eq_resolvedControl
    (literalCombinedFreshPhaseActivatedHonestEntryNoRecvTwo A strategy hwin
      controllers initialBank fallback fallbackTag) two one input.2 hcoherent,
    hone, htwo]
  rfl

/-- Actual Moore output of a simultaneous pre-entry round, expressed through
the guarded-Mega controls selected by the canonical semantic trace. -/
theorem
    literalCombinedFreshPhaseActivatedHonestMegaEntryPhysicalOutput_both_mega
    (fallback : Installation A strategy hwin)
    (fallbackTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (megaOne : (Mega A strategy hwin controllers initialBank
      fallbackTag).OneControl)
    (megaTwo : (Mega A strategy hwin controllers initialBank
      fallbackTag).TwoControl)
    (hgraph : (env n).graph = .both)
    (hsemantic :
      literalCombinedFreshPhaseActivatedHonestMegaEntrySemanticTrace A strategy
        hwin controllers initialBank fallback fallbackTag env n =
          (.inl megaOne, .inl megaTwo)) :
    let physical :=
      literalCombinedFreshPhaseActivatedHonestMegaEntryPhysicalController A
        strategy hwin controllers initialBank fallback fallbackTag
    let nextState := physical.globalMachine.globalStateTrace env (n + 1)
    let mega := Mega A strategy hwin controllers initialBank fallbackTag
    (physical.globalOutputOne nextState, physical.globalOutputTwo nextState) =
      (mega.outputOne
          (mega.recvOne megaOne (env n).inputOne megaTwo (env n).inputTwo),
        mega.outputTwo
          (mega.recvTwo megaTwo (env n).inputTwo megaOne (env n).inputOne)) := by
  let mealy :=
    literalCombinedFreshPhaseActivatedHonestMegaEntryController A strategy hwin
      controllers initialBank fallback fallbackTag
  let physical := mealy.mooreize
  let state := physical.globalMachine.globalStateTrace env n
  have hselects :=
    literalCombinedFreshPhaseActivatedHonestMegaEntryPhysicalTrace_pairSelects
      A strategy hwin controllers initialBank fallback fallbackTag env n
  change FiniteAcknowledgedDelayedCarrier.PairSelects state.1.1 state.2.1
      (literalCombinedFreshPhaseActivatedHonestMegaEntrySemanticTrace A strategy
        hwin controllers initialBank fallback fallbackTag env n).1
      (literalCombinedFreshPhaseActivatedHonestMegaEntrySemanticTrace A strategy
        hwin controllers initialBank fallback fallbackTag env n).2 at hselects
  rw [hsemantic] at hselects
  have hlocal :=
    literalCombinedFreshPhaseActivatedHonestMegaEntry_both_outputs_mega_of_pairSelects
      A strategy hwin controllers initialBank fallback fallbackTag megaOne
        megaTwo ((env n).inputOne, (env n).inputTwo) state.1.1 state.2.1
          hselects
  calc
    _ =
        ((mealy.recvOne state.1.1 (env n).inputOne state.2.1
            (env n).inputTwo).2,
          (mealy.recvTwo state.2.1 (env n).inputTwo state.1.1
            (env n).inputOne).2) := by
      rw [FiniteGlobalRoundMachine.globalStateTrace_succ]
      change
        (physical.outputOne (physical.advanceControls state (env n)).1,
          physical.outputTwo (physical.advanceControls state (env n)).2) = _
      simp only [FinitePairedPhysicalController.advanceControls, hgraph]
      rw [mealy.mooreize_recvOne_output, mealy.mooreize_recvTwo_output]
    _ = _ := hlocal

/-- Actual Moore output of a strict-right pre-entry round.  The theorem makes
the sole blind-output obligation explicit at the current physical relay
state; all receive-side and mutual-selection obligations are discharged by
the acknowledged trace invariant. -/
theorem
    literalCombinedFreshPhaseActivatedHonestMegaEntryPhysicalOutput_strictRight_mega
    (fallback : Installation A strategy hwin)
    (fallbackTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (megaOne : (Mega A strategy hwin controllers initialBank
      fallbackTag).OneControl)
    (megaTwo : (Mega A strategy hwin controllers initialBank
      fallbackTag).TwoControl)
    (hgraph : (env n).graph = .right)
    (hsemantic :
      literalCombinedFreshPhaseActivatedHonestMegaEntrySemanticTrace A strategy
        hwin controllers initialBank fallback fallbackTag env n =
          (.inl megaOne, .inl megaTwo))
    (hcoherent :
      let physical :=
        literalCombinedFreshPhaseActivatedHonestMegaEntryPhysicalController A
          strategy hwin controllers initialBank fallback fallbackTag
      let state := physical.globalMachine.globalStateTrace env n
      FiniteAcknowledgedDelayedCarrier.NoRecvOutputCoherent
        (literalCombinedFreshPhaseActivatedHonestEntryNoRecvOne A strategy hwin
          controllers initialBank fallback fallbackTag) state.1.1
            (env n).inputOne) :
    let physical :=
      literalCombinedFreshPhaseActivatedHonestMegaEntryPhysicalController A
        strategy hwin controllers initialBank fallback fallbackTag
    let nextState := physical.globalMachine.globalStateTrace env (n + 1)
    let mega := Mega A strategy hwin controllers initialBank fallbackTag
    (physical.globalOutputOne nextState, physical.globalOutputTwo nextState) =
      (mega.outputOne (mega.noRecvOne megaOne (env n).inputOne),
        mega.outputTwo
          (mega.recvTwo megaTwo (env n).inputTwo megaOne (env n).inputOne)) := by
  let mealy :=
    literalCombinedFreshPhaseActivatedHonestMegaEntryController A strategy hwin
      controllers initialBank fallback fallbackTag
  let physical := mealy.mooreize
  let state := physical.globalMachine.globalStateTrace env n
  have hselects :=
    literalCombinedFreshPhaseActivatedHonestMegaEntryPhysicalTrace_pairSelects
      A strategy hwin controllers initialBank fallback fallbackTag env n
  change FiniteAcknowledgedDelayedCarrier.PairSelects state.1.1 state.2.1
      (literalCombinedFreshPhaseActivatedHonestMegaEntrySemanticTrace A strategy
        hwin controllers initialBank fallback fallbackTag env n).1
      (literalCombinedFreshPhaseActivatedHonestMegaEntrySemanticTrace A strategy
        hwin controllers initialBank fallback fallbackTag env n).2 at hselects
  rw [hsemantic] at hselects
  have hlocal :=
    literalCombinedFreshPhaseActivatedHonestMegaEntry_strictRight_outputs_mega_of_pairSelects
      A strategy hwin controllers initialBank fallback fallbackTag megaOne
        megaTwo ((env n).inputOne, (env n).inputTwo) state.1.1 state.2.1
          hselects hcoherent
  calc
    _ =
        ((mealy.noRecvOne state.1.1 (env n).inputOne).2,
          (mealy.recvTwo state.2.1 (env n).inputTwo state.1.1
            (env n).inputOne).2) := by
      rw [FiniteGlobalRoundMachine.globalStateTrace_succ]
      change
        (physical.outputOne (physical.advanceControls state (env n)).1,
          physical.outputTwo (physical.advanceControls state (env n)).2) = _
      simp only [FinitePairedPhysicalController.advanceControls, hgraph]
      rw [mealy.mooreize_noRecvOne_output, mealy.mooreize_recvTwo_output]
    _ = _ := hlocal

/-- Actual strict-left mirror.  Only process two's blind no-receive output
requires coherence at the reached relay state. -/
theorem
    literalCombinedFreshPhaseActivatedHonestMegaEntryPhysicalOutput_strictLeft_mega
    (fallback : Installation A strategy hwin)
    (fallbackTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (megaOne : (Mega A strategy hwin controllers initialBank
      fallbackTag).OneControl)
    (megaTwo : (Mega A strategy hwin controllers initialBank
      fallbackTag).TwoControl)
    (hgraph : (env n).graph = .left)
    (hsemantic :
      literalCombinedFreshPhaseActivatedHonestMegaEntrySemanticTrace A strategy
        hwin controllers initialBank fallback fallbackTag env n =
          (.inl megaOne, .inl megaTwo))
    (hcoherent :
      let physical :=
        literalCombinedFreshPhaseActivatedHonestMegaEntryPhysicalController A
          strategy hwin controllers initialBank fallback fallbackTag
      let state := physical.globalMachine.globalStateTrace env n
      FiniteAcknowledgedDelayedCarrier.NoRecvOutputCoherent
        (literalCombinedFreshPhaseActivatedHonestEntryNoRecvTwo A strategy hwin
          controllers initialBank fallback fallbackTag) state.2.1
            (env n).inputTwo) :
    let physical :=
      literalCombinedFreshPhaseActivatedHonestMegaEntryPhysicalController A
        strategy hwin controllers initialBank fallback fallbackTag
    let nextState := physical.globalMachine.globalStateTrace env (n + 1)
    let mega := Mega A strategy hwin controllers initialBank fallbackTag
    (physical.globalOutputOne nextState, physical.globalOutputTwo nextState) =
      (mega.outputOne
          (mega.recvOne megaOne (env n).inputOne megaTwo (env n).inputTwo),
        mega.outputTwo (mega.noRecvTwo megaTwo (env n).inputTwo)) := by
  let mealy :=
    literalCombinedFreshPhaseActivatedHonestMegaEntryController A strategy hwin
      controllers initialBank fallback fallbackTag
  let physical := mealy.mooreize
  let state := physical.globalMachine.globalStateTrace env n
  have hselects :=
    literalCombinedFreshPhaseActivatedHonestMegaEntryPhysicalTrace_pairSelects
      A strategy hwin controllers initialBank fallback fallbackTag env n
  change FiniteAcknowledgedDelayedCarrier.PairSelects state.1.1 state.2.1
      (literalCombinedFreshPhaseActivatedHonestMegaEntrySemanticTrace A strategy
        hwin controllers initialBank fallback fallbackTag env n).1
      (literalCombinedFreshPhaseActivatedHonestMegaEntrySemanticTrace A strategy
        hwin controllers initialBank fallback fallbackTag env n).2 at hselects
  rw [hsemantic] at hselects
  have hlocal :=
    literalCombinedFreshPhaseActivatedHonestMegaEntry_strictLeft_outputs_mega_of_pairSelects
      A strategy hwin controllers initialBank fallback fallbackTag megaOne
        megaTwo ((env n).inputOne, (env n).inputTwo) state.1.1 state.2.1
          hselects hcoherent
  calc
    _ =
        ((mealy.recvOne state.1.1 (env n).inputOne state.2.1
            (env n).inputTwo).2,
          (mealy.noRecvTwo state.2.1 (env n).inputTwo).2) := by
      rw [FiniteGlobalRoundMachine.globalStateTrace_succ]
      change
        (physical.outputOne (physical.advanceControls state (env n)).1,
          physical.outputTwo (physical.advanceControls state (env n)).2) = _
      simp only [FinitePairedPhysicalController.advanceControls, hgraph]
      rw [mealy.mooreize_recvOne_output, mealy.mooreize_noRecvTwo_output]
    _ = _ := hlocal

/-- Graph-uniform pre-entry output simulation.  The actual acknowledged
splice emits exactly the guarded-Mega Moore output whenever its canonical
semantic pair is in the Mega summand.  The hypotheses mention coherence only
in the graph case where the corresponding endpoint is blind. -/
theorem
    literalCombinedFreshPhaseActivatedHonestMegaEntryPhysicalOutput_mega
    (fallback : Installation A strategy hwin)
    (fallbackTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (megaOne : (Mega A strategy hwin controllers initialBank
      fallbackTag).OneControl)
    (megaTwo : (Mega A strategy hwin controllers initialBank
      fallbackTag).TwoControl)
    (hsemantic :
      literalCombinedFreshPhaseActivatedHonestMegaEntrySemanticTrace A strategy
        hwin controllers initialBank fallback fallbackTag env n =
          (.inl megaOne, .inl megaTwo))
    (hcoherentRight :
      (env n).graph = .right →
        let physical :=
          literalCombinedFreshPhaseActivatedHonestMegaEntryPhysicalController A
            strategy hwin controllers initialBank fallback fallbackTag
        let state := physical.globalMachine.globalStateTrace env n
        FiniteAcknowledgedDelayedCarrier.NoRecvOutputCoherent
          (literalCombinedFreshPhaseActivatedHonestEntryNoRecvOne A strategy
            hwin controllers initialBank fallback fallbackTag) state.1.1
              (env n).inputOne)
    (hcoherentLeft :
      (env n).graph = .left →
        let physical :=
          literalCombinedFreshPhaseActivatedHonestMegaEntryPhysicalController A
            strategy hwin controllers initialBank fallback fallbackTag
        let state := physical.globalMachine.globalStateTrace env n
        FiniteAcknowledgedDelayedCarrier.NoRecvOutputCoherent
          (literalCombinedFreshPhaseActivatedHonestEntryNoRecvTwo A strategy
            hwin controllers initialBank fallback fallbackTag) state.2.1
              (env n).inputTwo) :
    let physical :=
      literalCombinedFreshPhaseActivatedHonestMegaEntryPhysicalController A
        strategy hwin controllers initialBank fallback fallbackTag
    let nextState := physical.globalMachine.globalStateTrace env (n + 1)
    let mega := Mega A strategy hwin controllers initialBank fallbackTag
    let megaNext := mega.advanceControls (megaOne, megaTwo) (env n)
    (physical.globalOutputOne nextState, physical.globalOutputTwo nextState) =
      (mega.outputOne megaNext.1, mega.outputTwo megaNext.2) := by
  cases hgraph : (env n).graph with
  | right =>
      have houtput :=
        literalCombinedFreshPhaseActivatedHonestMegaEntryPhysicalOutput_strictRight_mega
          A strategy hwin controllers initialBank fallback fallbackTag env n
            megaOne megaTwo hgraph hsemantic (hcoherentRight hgraph)
      simpa only [FinitePairedPhysicalController.advanceControls, hgraph] using
        houtput
  | left =>
      have houtput :=
        literalCombinedFreshPhaseActivatedHonestMegaEntryPhysicalOutput_strictLeft_mega
          A strategy hwin controllers initialBank fallback fallbackTag env n
            megaOne megaTwo hgraph hsemantic (hcoherentLeft hgraph)
      simpa only [FinitePairedPhysicalController.advanceControls, hgraph] using
        houtput
  | both =>
      have houtput :=
        literalCombinedFreshPhaseActivatedHonestMegaEntryPhysicalOutput_both_mega
          A strategy hwin controllers initialBank fallback fallbackTag env n
            megaOne megaTwo hgraph hsemantic
      simpa only [FinitePairedPhysicalController.advanceControls, hgraph] using
        houtput

/-- Letter form of graph-uniform pre-entry simulation.  This is the precise
one-round statement needed to transfer a finite checker prefix from the Mega
front to the honest acknowledged splice. -/
theorem literalCombinedFreshPhaseActivatedHonestMegaEntryPhysicalWord_eq_mega
    (fallback : Installation A strategy hwin)
    (fallbackTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (hsemantic :
      let mega := Mega A strategy hwin controllers initialBank fallbackTag
      let state := mega.globalMachine.globalStateTrace env n
      literalCombinedFreshPhaseActivatedHonestMegaEntrySemanticTrace A strategy
        hwin controllers initialBank fallback fallbackTag env n =
          (.inl state.1, .inl state.2))
    (hcoherentRight :
      (env n).graph = .right →
        let physical :=
          literalCombinedFreshPhaseActivatedHonestMegaEntryPhysicalController A
            strategy hwin controllers initialBank fallback fallbackTag
        let state := physical.globalMachine.globalStateTrace env n
        FiniteAcknowledgedDelayedCarrier.NoRecvOutputCoherent
          (literalCombinedFreshPhaseActivatedHonestEntryNoRecvOne A strategy
            hwin controllers initialBank fallback fallbackTag) state.1.1
              (env n).inputOne)
    (hcoherentLeft :
      (env n).graph = .left →
        let physical :=
          literalCombinedFreshPhaseActivatedHonestMegaEntryPhysicalController A
            strategy hwin controllers initialBank fallback fallbackTag
        let state := physical.globalMachine.globalStateTrace env n
        FiniteAcknowledgedDelayedCarrier.NoRecvOutputCoherent
          (literalCombinedFreshPhaseActivatedHonestEntryNoRecvTwo A strategy
            hwin controllers initialBank fallback fallbackTag) state.2.1
              (env n).inputTwo) :
    literalCombinedFreshPhaseActivatedHonestMegaEntryPhysicalWord A strategy
        hwin controllers initialBank fallback fallbackTag env n =
      let mega := Mega A strategy hwin controllers initialBank fallbackTag
      mega.globalMachine.globalMachineTraceWord mega.globalOutputOne
        mega.globalOutputTwo env n := by
  let mega := Mega A strategy hwin controllers initialBank fallbackTag
  let state := mega.globalMachine.globalStateTrace env n
  have houtputs :=
    literalCombinedFreshPhaseActivatedHonestMegaEntryPhysicalOutput_mega A
      strategy hwin controllers initialBank fallback fallbackTag env n state.1
        state.2 hsemantic hcoherentRight hcoherentLeft
  have houtputs' :
      let physical :=
        literalCombinedFreshPhaseActivatedHonestMegaEntryPhysicalController A
          strategy hwin controllers initialBank fallback fallbackTag
      (physical.globalOutputOne
          (physical.globalMachine.globalStateTrace env (n + 1)),
        physical.globalOutputTwo
          (physical.globalMachine.globalStateTrace env (n + 1))) =
        (mega.globalOutputOne
            (mega.globalMachine.globalStateTrace env (n + 1)),
          mega.globalOutputTwo
            (mega.globalMachine.globalStateTrace env (n + 1))) := by
    rw [FiniteGlobalRoundMachine.globalStateTrace_succ]
    exact houtputs
  simpa only
    [literalCombinedFreshPhaseActivatedHonestMegaEntryPhysicalWord,
      FiniteGlobalRoundMachine.globalMachineTraceWord] using
    congrArg
      (fun outputs : Out₁ × Out₂ ↦
        (RoundRecord.mk (env n).inputOne (env n).inputTwo (env n).graph
          outputs.1 outputs.2 :
            RoundRecord In₁ In₂ Graph Out₁ Out₂)) houtputs'

/-- Main finite-prefix checker transport before honest phase entry.  If the
canonical semantic splice remains exactly on the guarded-Mega trace through
round `cut - 1`, and the reached blind relay is coherent in each strict
round, then the real DPA checker of the acknowledged splice equals the Mega
checker at `cut`. -/
theorem
    literalCombinedFreshPhaseActivatedHonestMegaEntry_run_eq_mega_of_prefix
    (fallback : Installation A strategy hwin)
    (fallbackTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (cut : Nat)
    (hsemantic : ∀ n : Nat, n < cut →
      let mega := Mega A strategy hwin controllers initialBank fallbackTag
      let state := mega.globalMachine.globalStateTrace env n
      literalCombinedFreshPhaseActivatedHonestMegaEntrySemanticTrace A strategy
        hwin controllers initialBank fallback fallbackTag env n =
          (.inl state.1, .inl state.2))
    (hcoherentRight : ∀ n : Nat, n < cut → (env n).graph = .right →
      let physical :=
        literalCombinedFreshPhaseActivatedHonestMegaEntryPhysicalController A
          strategy hwin controllers initialBank fallback fallbackTag
      let state := physical.globalMachine.globalStateTrace env n
      FiniteAcknowledgedDelayedCarrier.NoRecvOutputCoherent
        (literalCombinedFreshPhaseActivatedHonestEntryNoRecvOne A strategy hwin
          controllers initialBank fallback fallbackTag) state.1.1
            (env n).inputOne)
    (hcoherentLeft : ∀ n : Nat, n < cut → (env n).graph = .left →
      let physical :=
        literalCombinedFreshPhaseActivatedHonestMegaEntryPhysicalController A
          strategy hwin controllers initialBank fallback fallbackTag
      let state := physical.globalMachine.globalStateTrace env n
      FiniteAcknowledgedDelayedCarrier.NoRecvOutputCoherent
        (literalCombinedFreshPhaseActivatedHonestEntryNoRecvTwo A strategy hwin
          controllers initialBank fallback fallbackTag) state.2.1
            (env n).inputTwo) :
    A.run
        (literalCombinedFreshPhaseActivatedHonestMegaEntryPhysicalWord A
          strategy hwin controllers initialBank fallback fallbackTag env) cut =
      let mega := Mega A strategy hwin controllers initialBank fallbackTag
      A.run
        (mega.globalMachine.globalMachineTraceWord mega.globalOutputOne
          mega.globalOutputTwo env) cut := by
  induction cut with
  | zero => rfl
  | succ cut ih =>
      rw [A.run_succ, A.run_succ]
      rw [ih
        (fun n hn ↦ hsemantic n (by omega))
        (fun n hn ↦ hcoherentRight n (by omega))
        (fun n hn ↦ hcoherentLeft n (by omega))]
      rw [literalCombinedFreshPhaseActivatedHonestMegaEntryPhysicalWord_eq_mega
        A strategy hwin controllers initialBank fallback fallbackTag env cut
          (hsemantic cut (by omega))
          (hcoherentRight cut (by omega))
          (hcoherentLeft cut (by omega))]

/-- Pre-entry checker theorem stated only with operational cut conditions.
Absence of an earlier honest-entry trigger now supplies the semantic-trace
premise automatically; reachable blind-output coherence is the only remaining
relay hypothesis. -/
theorem
    literalCombinedFreshPhaseActivatedHonestMegaEntry_run_eq_mega_of_noTrigger
    (fallback : Installation A strategy hwin)
    (fallbackTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (cut : Nat)
    (hnoTrigger : ∀ n : Nat, n < cut →
      ¬ literalCombinedFreshPhaseActivatedHonestMegaEntryTrigger A strategy
        hwin controllers initialBank fallbackTag env n)
    (hcoherentRight : ∀ n : Nat, n < cut → (env n).graph = .right →
      let physical :=
        literalCombinedFreshPhaseActivatedHonestMegaEntryPhysicalController A
          strategy hwin controllers initialBank fallback fallbackTag
      let state := physical.globalMachine.globalStateTrace env n
      FiniteAcknowledgedDelayedCarrier.NoRecvOutputCoherent
        (literalCombinedFreshPhaseActivatedHonestEntryNoRecvOne A strategy hwin
          controllers initialBank fallback fallbackTag) state.1.1
            (env n).inputOne)
    (hcoherentLeft : ∀ n : Nat, n < cut → (env n).graph = .left →
      let physical :=
        literalCombinedFreshPhaseActivatedHonestMegaEntryPhysicalController A
          strategy hwin controllers initialBank fallback fallbackTag
      let state := physical.globalMachine.globalStateTrace env n
      FiniteAcknowledgedDelayedCarrier.NoRecvOutputCoherent
        (literalCombinedFreshPhaseActivatedHonestEntryNoRecvTwo A strategy hwin
          controllers initialBank fallback fallbackTag) state.2.1
            (env n).inputTwo) :
    A.run
        (literalCombinedFreshPhaseActivatedHonestMegaEntryPhysicalWord A
          strategy hwin controllers initialBank fallback fallbackTag env) cut =
      let mega := Mega A strategy hwin controllers initialBank fallbackTag
      A.run
        (mega.globalMachine.globalMachineTraceWord mega.globalOutputOne
          mega.globalOutputTwo env) cut := by
  apply
    literalCombinedFreshPhaseActivatedHonestMegaEntry_run_eq_mega_of_prefix A
      strategy hwin controllers initialBank fallback fallbackTag env cut
  · intro n hn
    exact
      literalCombinedFreshPhaseActivatedHonestMegaEntrySemanticTrace_eq_mega_of_noTrigger
        A strategy hwin controllers initialBank fallback fallbackTag env n
          (fun k hk ↦ hnoTrigger k (by omega))
  · exact hcoherentRight
  · exact hcoherentLeft

/-- The first letter of the honest splice is the literal first strategy
letter whenever the initial physical round is simultaneous. -/
theorem literalCombinedFreshPhaseActivatedHonestMegaEntryPhysicalWord_zero
    (fallback : Installation A strategy hwin)
    (fallbackTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (first : In₁ × In₂)
    (hfirst : env 0 = ⟨first.1, first.2, Graph.both⟩) :
    literalCombinedFreshPhaseActivatedHonestMegaEntryPhysicalWord A strategy
        hwin controllers initialBank fallback fallbackTag env 0 =
      nextRound strategy [] ⟨first.1, first.2, Graph.both⟩ := by
  let mega := Mega A strategy hwin controllers initialBank fallbackTag
  let physical :=
    literalCombinedFreshPhaseActivatedHonestMegaEntryPhysicalController A
      strategy hwin controllers initialBank fallback fallbackTag
  have hgraph : (env 0).graph = .both := by
    rw [hfirst]
  have hsemantic :
      literalCombinedFreshPhaseActivatedHonestMegaEntrySemanticTrace A strategy
          hwin controllers initialBank fallback fallbackTag env 0 =
        (.inl mega.initialOne, .inl mega.initialTwo) :=
    rfl
  have hactual :=
    literalCombinedFreshPhaseActivatedHonestMegaEntryPhysicalOutput_both_mega
      A strategy hwin controllers initialBank fallback fallbackTag env 0
        mega.initialOne mega.initialTwo hgraph hsemantic
  rw [hfirst] at hactual
  have hmega :=
    profiledRawJointHybridMegaGuarded_outputs_after_one A strategy hwin
      controllers initialBank fallbackTag env first hfirst
  dsimp only at hmega
  rw [FiniteGlobalRoundMachine.globalStateTrace_succ,
    FiniteGlobalRoundMachine.globalStateTrace_zero, hfirst] at hmega
  have houtputs :
      (physical.globalOutputOne
          (physical.globalMachine.globalStateTrace env 1),
        physical.globalOutputTwo
          (physical.globalMachine.globalStateTrace env 1)) =
        let round := nextRound strategy []
          ⟨first.1, first.2, Graph.both⟩
        (round.outputOne, round.outputTwo) := by
    exact hactual.trans (by
      simpa only [FinitePairedPhysicalController.globalMachine_step,
        FinitePairedPhysicalController.advanceControls] using hmega)
  have hone :
      physical.globalOutputOne
          (physical.globalMachine.globalStateTrace env 1) =
        (nextRound strategy []
          ⟨first.1, first.2, Graph.both⟩).outputOne := by
    exact congrArg Prod.fst houtputs
  have htwo :
      physical.globalOutputTwo
          (physical.globalMachine.globalStateTrace env 1) =
        (nextRound strategy []
          ⟨first.1, first.2, Graph.both⟩).outputTwo := by
    exact congrArg Prod.snd houtputs
  change
    (RoundRecord.mk (env 0).inputOne (env 0).inputTwo (env 0).graph
      (physical.globalOutputOne
        (physical.globalMachine.globalStateTrace env 1))
      (physical.globalOutputTwo
        (physical.globalMachine.globalStateTrace env 1)) :
      RoundRecord In₁ In₂ Graph Out₁ Out₂) = _
  rw [hfirst, hone, htwo]
  rfl

/-- The second letter of the honest splice is the literal second strategy
letter and leaves the proof-side front at the corresponding guarded coupled
installation. -/
theorem literalCombinedFreshPhaseActivatedHonestMegaEntryPhysicalWord_one
    (fallback : Installation A strategy hwin)
    (fallbackTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (first current : In₁ × In₂)
    (hfirst : env 0 = ⟨first.1, first.2, Graph.both⟩)
    (hcurrent : env 1 = ⟨current.1, current.2, Graph.both⟩) :
    literalCombinedFreshPhaseActivatedHonestMegaEntryPhysicalWord A strategy
        hwin controllers initialBank fallback fallbackTag env 1 =
      let firstRound := nextRound strategy []
        ⟨first.1, first.2, Graph.both⟩
      nextRound strategy [firstRound]
        ⟨current.1, current.2, Graph.both⟩ := by
  let mega := Mega A strategy hwin controllers initialBank fallbackTag
  let state := mega.globalMachine.globalStateTrace env 1
  let physical :=
    literalCombinedFreshPhaseActivatedHonestMegaEntryPhysicalController A
      strategy hwin controllers initialBank fallback fallbackTag
  have hgraph : (env 1).graph = .both := by
    rw [hcurrent]
  have hsemantic :=
    literalCombinedFreshPhaseActivatedHonestMegaEntrySemanticTrace_one A
      strategy hwin controllers initialBank fallback fallbackTag env first
        hfirst
  change
    literalCombinedFreshPhaseActivatedHonestMegaEntrySemanticTrace A strategy
        hwin controllers initialBank fallback fallbackTag env 1 =
      (.inl state.1, .inl state.2) at hsemantic
  have hactual :=
    literalCombinedFreshPhaseActivatedHonestMegaEntryPhysicalOutput_both_mega
      A strategy hwin controllers initialBank fallback fallbackTag env 1
        state.1 state.2 hgraph hsemantic
  rw [hcurrent] at hactual
  have hmega :=
    profiledRawJointHybridMegaGuarded_outputs_after_two A strategy hwin
      controllers initialBank fallbackTag env first current hfirst hcurrent
  dsimp only at hmega
  rw [show 2 = 1 + 1 by omega,
    FiniteGlobalRoundMachine.globalStateTrace_succ, hcurrent] at hmega
  rw [profiledRawJointHybridMegaGuarded_initialCommonOutput_eq_secondRound A
    strategy first current] at hmega
  have houtputs :
      (physical.globalOutputOne
          (physical.globalMachine.globalStateTrace env 2),
        physical.globalOutputTwo
          (physical.globalMachine.globalStateTrace env 2)) =
        let firstRound := nextRound strategy []
          ⟨first.1, first.2, Graph.both⟩
        let secondRound := nextRound strategy [firstRound]
          ⟨current.1, current.2, Graph.both⟩
        (secondRound.outputOne, secondRound.outputTwo) := by
    exact hactual.trans (by
      simpa only [FinitePairedPhysicalController.globalMachine_step,
        FinitePairedPhysicalController.advanceControls] using hmega)
  have hone :
      physical.globalOutputOne
          (physical.globalMachine.globalStateTrace env 2) =
        (nextRound strategy
          [nextRound strategy []
            ⟨first.1, first.2, Graph.both⟩]
          ⟨current.1, current.2, Graph.both⟩).outputOne := by
    exact congrArg Prod.fst houtputs
  have htwo :
      physical.globalOutputTwo
          (physical.globalMachine.globalStateTrace env 2) =
        (nextRound strategy
          [nextRound strategy []
            ⟨first.1, first.2, Graph.both⟩]
          ⟨current.1, current.2, Graph.both⟩).outputTwo := by
    exact congrArg Prod.snd houtputs
  change
    (RoundRecord.mk (env 1).inputOne (env 1).inputTwo (env 1).graph
      (physical.globalOutputOne
        (physical.globalMachine.globalStateTrace env 2))
      (physical.globalOutputTwo
        (physical.globalMachine.globalStateTrace env 2)) :
      RoundRecord In₁ In₂ Graph Out₁ Out₂) = _
  rw [hcurrent, hone, htwo]
  rfl

/-- The real checker of the honest splice is aligned with the guarded
installation after the two initial simultaneous rounds. -/
theorem literalCombinedFreshPhaseActivatedHonestMegaEntry_run_two
    (fallback : Installation A strategy hwin)
    (fallbackTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (first current : In₁ × In₂)
    (hfirst : env 0 = ⟨first.1, first.2, Graph.both⟩)
    (hcurrent : env 1 = ⟨current.1, current.2, Graph.both⟩) :
    let installation : Installation A strategy hwin :=
      .inl ⟨first, current⟩
    A.run
        (literalCombinedFreshPhaseActivatedHonestMegaEntryPhysicalWord A
          strategy hwin controllers initialBank fallback fallbackTag env) 2 =
      pairedCodeStateForRow A .both
        (((literalCombinedFreshPhaseActivatedPointOfInstallation A strategy
          hwin installation).world A strategy).procOneSlot A).1.1 := by
  dsimp only
  let word :=
    literalCombinedFreshPhaseActivatedHonestMegaEntryPhysicalWord A strategy
      hwin controllers initialBank fallback fallbackTag env
  have hrun :=
    literalCombinedFreshPhaseActivatedTwoRound_run_two_eq_installedState A
      strategy first current word
        (literalCombinedFreshPhaseActivatedHonestMegaEntryPhysicalWord_zero A
          strategy hwin controllers initialBank fallback fallbackTag env first
            hfirst)
        (literalCombinedFreshPhaseActivatedHonestMegaEntryPhysicalWord_one A
          strategy hwin controllers initialBank fallback fallbackTag env first
            current hfirst hcurrent)
  exact hrun

/-- Relay-independent output form of the honest entry.  Whenever the two
acknowledged endpoint states select one matching guarded-mega coupled pair,
their actual simultaneous receive outputs are exactly the pre-existing Mega
outputs.  In particular, unresolved acknowledgement identifiers do not alter
the entry letter. -/
theorem
    literalCombinedFreshPhaseActivatedHonestMegaEntry_both_outputs_of_pairSelects
    (fallback : Installation A strategy hwin)
    (fallbackTag : RetainedTag A strategy hwin)
    (installation : Installation A strategy hwin)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (input : In₁ × In₂)
    (one :
      (literalCombinedFreshPhaseActivatedHonestMegaEntryController A strategy
        hwin controllers initialBank fallback fallbackTag).OneControl)
    (two :
      (literalCombinedFreshPhaseActivatedHonestMegaEntryController A strategy
        hwin controllers initialBank fallback fallbackTag).TwoControl)
    (hselects :
      let coupled :=
        profiledRawJointHybridMegaGuardedCoupledControls A strategy hwin
          controllers initialBank fallbackTag installation oldOutputOne
            oldOutputTwo
      FiniteAcknowledgedDelayedCarrier.PairSelects one two
        (.inl coupled.1) (.inl coupled.2)) :
    let coupled :=
      profiledRawJointHybridMegaGuardedCoupledControls A strategy hwin
        controllers initialBank fallbackTag installation oldOutputOne
          oldOutputTwo
    let controller :=
      literalCombinedFreshPhaseActivatedHonestMegaEntryController A strategy
        hwin controllers initialBank fallback fallbackTag
    let mega := Mega A strategy hwin controllers initialBank fallbackTag
    ((controller.recvOne one input.1 two input.2).2,
      (controller.recvTwo two input.2 one input.1).2) =
      (mega.outputOne (mega.recvOne coupled.1 input.1 coupled.2 input.2),
        mega.outputTwo
          (mega.recvTwo coupled.2 input.2 coupled.1 input.1)) := by
  dsimp only at hselects ⊢
  rcases hselects with ⟨hone, htwo⟩
  change FiniteAcknowledgedDelayedCarrier.resolvedControl one two =
      .inl
        (profiledRawJointHybridMegaGuardedCoupledControls A strategy hwin
          controllers initialBank fallbackTag installation oldOutputOne
            oldOutputTwo).1 at hone
  change FiniteAcknowledgedDelayedCarrier.resolvedControl two one =
      .inl
        (profiledRawJointHybridMegaGuardedCoupledControls A strategy hwin
          controllers initialBank fallbackTag installation oldOutputOne
            oldOutputTwo).2 at htwo
  change
    ((literalCombinedFreshPhaseActivatedHonestEntryOpenRecvOne A strategy hwin
        controllers initialBank fallback fallbackTag
          (FiniteAcknowledgedDelayedCarrier.resolvedControl one two) input.1
          (FiniteAcknowledgedDelayedCarrier.resolvedControl two one)
          input.2).2,
      (literalCombinedFreshPhaseActivatedHonestEntryOpenRecvTwo A strategy hwin
        controllers initialBank fallback fallbackTag
          (FiniteAcknowledgedDelayedCarrier.resolvedControl two one) input.2
          (FiniteAcknowledgedDelayedCarrier.resolvedControl one two)
          input.1).2) = _
  rw [hone, htwo]
  exact
    literalCombinedFreshPhaseActivatedHonestEntryOpen_outputs_coupled A
      strategy hwin controllers initialBank fallback fallbackTag installation
        oldOutputOne oldOutputTwo input

/-- Reachable-control form of the exact entry letter.  If the two endpoint
relays select matching coupled Mega controls, their simultaneous receive
outputs are the literal strategy outputs at the represented occurrence. -/
theorem
    literalCombinedFreshPhaseActivatedHonestMegaEntry_both_outputs_literal_of_pairSelects
    (fallback : Installation A strategy hwin)
    (fallbackTag : RetainedTag A strategy hwin)
    (installation : Installation A strategy hwin)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (input : In₁ × In₂)
    (one :
      (literalCombinedFreshPhaseActivatedHonestMegaEntryController A strategy
        hwin controllers initialBank fallback fallbackTag).OneControl)
    (two :
      (literalCombinedFreshPhaseActivatedHonestMegaEntryController A strategy
        hwin controllers initialBank fallback fallbackTag).TwoControl)
    (hselects :
      let coupled :=
        profiledRawJointHybridMegaGuardedCoupledControls A strategy hwin
          controllers initialBank fallbackTag installation oldOutputOne
            oldOutputTwo
      FiniteAcknowledgedDelayedCarrier.PairSelects one two
        (.inl coupled.1) (.inl coupled.2)) :
    let controller :=
      literalCombinedFreshPhaseActivatedHonestMegaEntryController A strategy
        hwin controllers initialBank fallback fallbackTag
    let point :=
      literalCombinedFreshPhaseActivatedPointOfInstallation A strategy hwin
        installation
    let round := nextRound strategy (point.world A strategy).procOne.bothHistory
      ⟨input.1, input.2, Graph.both⟩
    ((controller.recvOne one input.1 two input.2).2,
      (controller.recvTwo two input.2 one input.1).2) =
      (round.outputOne, round.outputTwo) := by
  calc
    _ =
        let coupled :=
          profiledRawJointHybridMegaGuardedCoupledControls A strategy hwin
            controllers initialBank fallbackTag installation oldOutputOne
              oldOutputTwo
        let mega := Mega A strategy hwin controllers initialBank fallbackTag
        (mega.outputOne (mega.recvOne coupled.1 input.1 coupled.2 input.2),
          mega.outputTwo
            (mega.recvTwo coupled.2 input.2 coupled.1 input.1)) :=
      literalCombinedFreshPhaseActivatedHonestMegaEntry_both_outputs_of_pairSelects
        A strategy hwin controllers initialBank fallback fallbackTag
          installation oldOutputOne oldOutputTwo input one two hselects
    _ = _ :=
      literalCombinedFreshPhaseActivatedMegaCoupled_outputs_literal A strategy
        hwin controllers initialBank fallbackTag installation oldOutputOne
          oldOutputTwo input

/-- Relay-independent control form of the same handoff.  A simultaneous
receive from any relay pair selecting matching coupled Mega controls selects
the two initial controls of the phase member rooted at the actual occurrence
and current input. -/
theorem
    literalCombinedFreshPhaseActivatedHonestMegaEntry_both_selects_of_pairSelects
    (fallback : Installation A strategy hwin)
    (fallbackTag : RetainedTag A strategy hwin)
    (installation : Installation A strategy hwin)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (input : In₁ × In₂)
    (one :
      (literalCombinedFreshPhaseActivatedHonestMegaEntryController A strategy
        hwin controllers initialBank fallback fallbackTag).OneControl)
    (two :
      (literalCombinedFreshPhaseActivatedHonestMegaEntryController A strategy
        hwin controllers initialBank fallback fallbackTag).TwoControl)
    (hselects :
      let coupled :=
        profiledRawJointHybridMegaGuardedCoupledControls A strategy hwin
          controllers initialBank fallbackTag installation oldOutputOne
            oldOutputTwo
      FiniteAcknowledgedDelayedCarrier.PairSelects one two
        (.inl coupled.1) (.inl coupled.2)) :
    let controller :=
      literalCombinedFreshPhaseActivatedHonestMegaEntryController A strategy
        hwin controllers initialBank fallback fallbackTag
    let entrySeed : EntrySeed A strategy hwin := (installation, input)
    FiniteAcknowledgedDelayedCarrier.PairSelects
      (controller.recvOne one input.1 two input.2).1
      (controller.recvTwo two input.2 one input.1).1
      (.inr
        (literalCombinedFreshPhaseActivatedInstallationActivateOne A strategy
          hwin entrySeed))
      (.inr
        (literalCombinedFreshPhaseActivatedInstallationActivateTwo A strategy
          hwin entrySeed)) := by
  dsimp only at hselects ⊢
  rcases hselects with ⟨hone, htwo⟩
  change FiniteAcknowledgedDelayedCarrier.resolvedControl one two =
      .inl
        (profiledRawJointHybridMegaGuardedCoupledControls A strategy hwin
          controllers initialBank fallbackTag installation oldOutputOne
            oldOutputTwo).1 at hone
  change FiniteAcknowledgedDelayedCarrier.resolvedControl two one =
      .inl
        (profiledRawJointHybridMegaGuardedCoupledControls A strategy hwin
          controllers initialBank fallbackTag installation oldOutputOne
            oldOutputTwo).2 at htwo
  have hnext :=
    FiniteAcknowledgedDelayedCarrier.exactClosing_pairSelects_both
      (literalCombinedFreshPhaseActivatedHonestEntryOpenRecvOne A strategy hwin
        controllers initialBank fallback fallbackTag)
      (literalCombinedFreshPhaseActivatedHonestEntryOpenRecvTwo A strategy hwin
        controllers initialBank fallback fallbackTag)
      (literalCombinedFreshPhaseActivatedHonestEntryClose A strategy hwin
        controllers initialBank fallback fallbackTag)
      one two input.1 input.2
  rw [hone, htwo] at hnext
  dsimp only at hnext
  rw [literalCombinedFreshPhaseActivatedHonestEntryClose_coupled A strategy
    hwin controllers initialBank fallback fallbackTag installation oldOutputOne
      oldOutputTwo input] at hnext
  change FiniteAcknowledgedDelayedCarrier.PairSelects
    (FiniteAcknowledgedDelayedCarrier.refork one two
      (FiniteAcknowledgedDelayedCarrier.exactClosingRecvForkOne
        (literalCombinedFreshPhaseActivatedHonestEntryOpenRecvOne A strategy
          hwin controllers initialBank fallback fallbackTag)
        (literalCombinedFreshPhaseActivatedHonestEntryClose A strategy hwin
          controllers initialBank fallback fallbackTag)
        (FiniteAcknowledgedDelayedCarrier.resolvedControl one two) input.1
        (FiniteAcknowledgedDelayedCarrier.resolvedControl two one)
          input.2).1)
    (FiniteAcknowledgedDelayedCarrier.refork two one
      (FiniteAcknowledgedDelayedCarrier.exactClosingRecvForkTwo
        (literalCombinedFreshPhaseActivatedHonestEntryOpenRecvTwo A strategy
          hwin controllers initialBank fallback fallbackTag)
        (literalCombinedFreshPhaseActivatedHonestEntryClose A strategy hwin
          controllers initialBank fallback fallbackTag)
        (FiniteAcknowledgedDelayedCarrier.resolvedControl two one) input.2
        (FiniteAcknowledgedDelayedCarrier.resolvedControl one two)
          input.1).1) _ _
  rw [hone, htwo]
  exact hnext

/-- Complete local handoff at a reachable honest entry.  One simultaneous
physical receive has three synchronized consequences: it emits the literal
strategy letter of the represented occurrence, selects both initial controls
of the phase member rooted at its literal child, and advances the real parity
checker to that member's `.both` source state. -/
theorem
    literalCombinedFreshPhaseActivatedHonestMegaEntry_both_handoff_of_pairSelects
    (fallback : Installation A strategy hwin)
    (fallbackTag : RetainedTag A strategy hwin)
    (installation : Installation A strategy hwin)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (input : In₁ × In₂)
    (one :
      (literalCombinedFreshPhaseActivatedHonestMegaEntryController A strategy
        hwin controllers initialBank fallback fallbackTag).OneControl)
    (two :
      (literalCombinedFreshPhaseActivatedHonestMegaEntryController A strategy
        hwin controllers initialBank fallback fallbackTag).TwoControl)
    (hselects :
      let coupled :=
        profiledRawJointHybridMegaGuardedCoupledControls A strategy hwin
          controllers initialBank fallbackTag installation oldOutputOne
            oldOutputTwo
      FiniteAcknowledgedDelayedCarrier.PairSelects one two
        (.inl coupled.1) (.inl coupled.2)) :
    let controller :=
      literalCombinedFreshPhaseActivatedHonestMegaEntryController A strategy
        hwin controllers initialBank fallback fallbackTag
    let point :=
      literalCombinedFreshPhaseActivatedPointOfInstallation A strategy hwin
        installation
    let round := nextRound strategy (point.world A strategy).procOne.bothHistory
      ⟨input.1, input.2, Graph.both⟩
    let entrySeed : EntrySeed A strategy hwin := (installation, input)
    let nextOne := controller.recvOne one input.1 two input.2
    let nextTwo := controller.recvTwo two input.2 one input.1
    (nextOne.2, nextTwo.2) = (round.outputOne, round.outputTwo) ∧
      FiniteAcknowledgedDelayedCarrier.PairSelects nextOne.1 nextTwo.1
        (.inr
          (literalCombinedFreshPhaseActivatedInstallationActivateOne A
            strategy hwin entrySeed))
        (.inr
          (literalCombinedFreshPhaseActivatedInstallationActivateTwo A
            strategy hwin entrySeed)) ∧
      A.step
          (pairedCodeStateForRow A .both
            ((point.world A strategy).procOneSlot A).1.1)
          (bothRoundRecord input nextOne.2 nextTwo.2) =
        pairedCodeStateForRow A .both
          (((literalCombinedFreshPhaseActivatedPointOfEntrySeed A strategy hwin
            entrySeed).world A strategy).procOneSlot A).1.1 := by
  dsimp only
  have houtputs :=
    literalCombinedFreshPhaseActivatedHonestMegaEntry_both_outputs_literal_of_pairSelects
      A strategy hwin controllers initialBank fallback fallbackTag installation
        oldOutputOne oldOutputTwo input one two hselects
  have hnext :=
    literalCombinedFreshPhaseActivatedHonestMegaEntry_both_selects_of_pairSelects
      A strategy hwin controllers initialBank fallback fallbackTag installation
        oldOutputOne oldOutputTwo input one two hselects
  refine ⟨houtputs, hnext, ?_⟩
  have houtputOne :
      ((literalCombinedFreshPhaseActivatedHonestMegaEntryController A strategy
        hwin controllers initialBank fallback fallbackTag).recvOne
          one input.1 two input.2).2 =
        (nextRound strategy
          ((literalCombinedFreshPhaseActivatedPointOfInstallation A strategy
            hwin installation).world A strategy).procOne.bothHistory
          ⟨input.1, input.2, Graph.both⟩).outputOne := by
    exact congrArg Prod.fst houtputs
  have houtputTwo :
      ((literalCombinedFreshPhaseActivatedHonestMegaEntryController A strategy
        hwin controllers initialBank fallback fallbackTag).recvTwo
          two input.2 one input.1).2 =
        (nextRound strategy
          ((literalCombinedFreshPhaseActivatedPointOfInstallation A strategy
            hwin installation).world A strategy).procOne.bothHistory
          ⟨input.1, input.2, Graph.both⟩).outputTwo := by
    exact congrArg Prod.snd houtputs
  rw [houtputOne, houtputTwo]
  exact
    literalCombinedFreshPhaseActivatedHonestEntry_step_eq_installedState A
      strategy hwin installation input

/-! ## The handoff on the actual physical trace -/

/-- Trace-level honest entry.  Suppose that, just before a simultaneous
physical round, the canonical semantic splice is at one coupled guarded-Mega
installation, and the real parity checker is at the source represented by
that installation.  The actual physical round then emits the literal strategy
letter, both acknowledged relays select the phase member rooted at the actual
input child, and the checker reaches exactly that member's `.both` source.

The two hypotheses are prefix obligations.  Everything concerning the entry
round itself--including relay ambiguity, its two outputs, the phase key, and
the checker transition--is discharged here. -/
theorem
    literalCombinedFreshPhaseActivatedHonestMegaEntry_global_both_handoff
    (fallback : Installation A strategy hwin)
    (fallbackTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (n : Nat)
    (installation : Installation A strategy hwin)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (hgraph : (env n).graph = .both)
    (hsemantic :
      let coupled :=
        profiledRawJointHybridMegaGuardedCoupledControls A strategy hwin
          controllers initialBank fallbackTag installation oldOutputOne
            oldOutputTwo
      literalCombinedFreshPhaseActivatedHonestMegaEntrySemanticTrace A strategy
        hwin controllers initialBank fallback fallbackTag env n =
          (.inl coupled.1, .inl coupled.2))
    (hchecker :
      A.run
          (literalCombinedFreshPhaseActivatedHonestMegaEntryPhysicalWord A
            strategy hwin controllers initialBank fallback fallbackTag env) n =
        pairedCodeStateForRow A .both
          (((literalCombinedFreshPhaseActivatedPointOfInstallation A strategy
            hwin installation).world A strategy).procOneSlot A).1.1) :
    let physical :=
      literalCombinedFreshPhaseActivatedHonestMegaEntryPhysicalController A
        strategy hwin controllers initialBank fallback fallbackTag
    let nextState := physical.globalMachine.globalStateTrace env (n + 1)
    let input : In₁ × In₂ := ((env n).inputOne, (env n).inputTwo)
    let point :=
      literalCombinedFreshPhaseActivatedPointOfInstallation A strategy hwin
        installation
    let round := nextRound strategy (point.world A strategy).procOne.bothHistory
      ⟨input.1, input.2, Graph.both⟩
    let entrySeed : EntrySeed A strategy hwin := (installation, input)
    (physical.globalOutputOne nextState,
        physical.globalOutputTwo nextState) =
        (round.outputOne, round.outputTwo) ∧
      FiniteAcknowledgedDelayedCarrier.PairSelects nextState.1.1 nextState.2.1
        (.inr
          (literalCombinedFreshPhaseActivatedInstallationActivateOne A
            strategy hwin entrySeed))
        (.inr
          (literalCombinedFreshPhaseActivatedInstallationActivateTwo A
            strategy hwin entrySeed)) ∧
      A.run
          (literalCombinedFreshPhaseActivatedHonestMegaEntryPhysicalWord A
            strategy hwin controllers initialBank fallback fallbackTag env)
          (n + 1) =
        pairedCodeStateForRow A .both
          (((literalCombinedFreshPhaseActivatedPointOfEntrySeed A strategy hwin
            entrySeed).world A strategy).procOneSlot A).1.1 := by
  let mealy :=
    literalCombinedFreshPhaseActivatedHonestMegaEntryController A strategy hwin
      controllers initialBank fallback fallbackTag
  let physical := mealy.mooreize
  let state := physical.globalMachine.globalStateTrace env n
  let input : In₁ × In₂ := ((env n).inputOne, (env n).inputTwo)
  let coupled :=
    profiledRawJointHybridMegaGuardedCoupledControls A strategy hwin controllers
      initialBank fallbackTag installation oldOutputOne oldOutputTwo
  have hphysicalSelects :=
    literalCombinedFreshPhaseActivatedHonestMegaEntryPhysicalTrace_pairSelects
      A strategy hwin controllers initialBank fallback fallbackTag env n
  change FiniteAcknowledgedDelayedCarrier.PairSelects state.1.1 state.2.1
      (literalCombinedFreshPhaseActivatedHonestMegaEntrySemanticTrace A strategy
        hwin controllers initialBank fallback fallbackTag env n).1
      (literalCombinedFreshPhaseActivatedHonestMegaEntrySemanticTrace A strategy
        hwin controllers initialBank fallback fallbackTag env n).2 at hphysicalSelects
  rw [hsemantic] at hphysicalSelects
  have hlocal :=
    literalCombinedFreshPhaseActivatedHonestMegaEntry_both_handoff_of_pairSelects
      A strategy hwin controllers initialBank fallback fallbackTag installation
        oldOutputOne oldOutputTwo input state.1.1 state.2.1 hphysicalSelects
  rcases hlocal with ⟨hlocalOutputs, hlocalSelects, hlocalChecker⟩
  have hphysicalOutputs :
      (physical.globalOutputOne
          (physical.globalMachine.globalStateTrace env (n + 1)),
        physical.globalOutputTwo
          (physical.globalMachine.globalStateTrace env (n + 1))) =
        ((mealy.recvOne state.1.1 input.1 state.2.1 input.2).2,
          (mealy.recvTwo state.2.1 input.2 state.1.1 input.1).2) := by
    rw [FiniteGlobalRoundMachine.globalStateTrace_succ]
    change
      (physical.outputOne (physical.advanceControls state (env n)).1,
        physical.outputTwo (physical.advanceControls state (env n)).2) = _
    simp only [FinitePairedPhysicalController.advanceControls, hgraph]
    rw [mealy.mooreize_recvOne_output, mealy.mooreize_recvTwo_output]
  have hphysicalNext :
      FiniteAcknowledgedDelayedCarrier.PairSelects
        (physical.globalMachine.globalStateTrace env (n + 1)).1.1
        (physical.globalMachine.globalStateTrace env (n + 1)).2.1
        (.inr
          (literalCombinedFreshPhaseActivatedInstallationActivateOne A
            strategy hwin (installation, input)))
        (.inr
          (literalCombinedFreshPhaseActivatedInstallationActivateTwo A
            strategy hwin (installation, input))) := by
    rw [FiniteGlobalRoundMachine.globalStateTrace_succ]
    change FiniteAcknowledgedDelayedCarrier.PairSelects
      (physical.advanceControls state (env n)).1.1
      (physical.advanceControls state (env n)).2.1 _ _
    simp only [FinitePairedPhysicalController.advanceControls, hgraph]
    exact hlocalSelects
  have houtputs := hphysicalOutputs.trans hlocalOutputs
  have hmealyOutputOne := congrArg Prod.fst hphysicalOutputs
  have hmealyOutputTwo := congrArg Prod.snd hphysicalOutputs
  dsimp only at hmealyOutputOne hmealyOutputTwo
  have hrun :
      A.run
          (literalCombinedFreshPhaseActivatedHonestMegaEntryPhysicalWord A
            strategy hwin controllers initialBank fallback fallbackTag env)
          (n + 1) =
        pairedCodeStateForRow A .both
          (((literalCombinedFreshPhaseActivatedPointOfEntrySeed A strategy hwin
            (installation, input)).world A strategy).procOneSlot A).1.1 := by
    rw [A.run_succ, hchecker]
    change A.step
      (pairedCodeStateForRow A .both
        (((literalCombinedFreshPhaseActivatedPointOfInstallation A strategy
          hwin installation).world A strategy).procOneSlot A).1.1)
      {
        inputOne := (env n).inputOne
        inputTwo := (env n).inputTwo
        graph := (env n).graph
        outputOne := physical.globalOutputOne
          (physical.globalMachine.globalStateTrace env (n + 1))
        outputTwo := physical.globalOutputTwo
          (physical.globalMachine.globalStateTrace env (n + 1))
      } = _
    rw [hgraph, hmealyOutputOne, hmealyOutputTwo]
    exact hlocalChecker
  exact ⟨houtputs, hphysicalNext, hrun⟩

/-- Fully unconditional honest entry for the initial all-simultaneous front.
After three actual simultaneous rounds, the emitted third letter is literal,
the two physical relays select the phase member rooted at that third-round
child, and the real checker is at the member's `.both` source. -/
theorem
    literalCombinedFreshPhaseActivatedHonestMegaEntry_three_both_handoff
    (fallback : Installation A strategy hwin)
    (fallbackTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (first current next : In₁ × In₂)
    (hfirst : env 0 = ⟨first.1, first.2, Graph.both⟩)
    (hcurrent : env 1 = ⟨current.1, current.2, Graph.both⟩)
    (hnext : env 2 = ⟨next.1, next.2, Graph.both⟩) :
    let installation : Installation A strategy hwin :=
      .inl ⟨first, current⟩
    let physical :=
      literalCombinedFreshPhaseActivatedHonestMegaEntryPhysicalController A
        strategy hwin controllers initialBank fallback fallbackTag
    let nextState := physical.globalMachine.globalStateTrace env 3
    let point :=
      literalCombinedFreshPhaseActivatedPointOfInstallation A strategy hwin
        installation
    let round := nextRound strategy (point.world A strategy).procOne.bothHistory
      ⟨next.1, next.2, Graph.both⟩
    let entrySeed : EntrySeed A strategy hwin := (installation, next)
    (physical.globalOutputOne nextState,
        physical.globalOutputTwo nextState) =
        (round.outputOne, round.outputTwo) ∧
      FiniteAcknowledgedDelayedCarrier.PairSelects nextState.1.1 nextState.2.1
        (.inr
          (literalCombinedFreshPhaseActivatedInstallationActivateOne A
            strategy hwin entrySeed))
        (.inr
          (literalCombinedFreshPhaseActivatedInstallationActivateTwo A
            strategy hwin entrySeed)) ∧
      A.run
          (literalCombinedFreshPhaseActivatedHonestMegaEntryPhysicalWord A
            strategy hwin controllers initialBank fallback fallbackTag env) 3 =
        pairedCodeStateForRow A .both
          (((literalCombinedFreshPhaseActivatedPointOfEntrySeed A strategy hwin
            entrySeed).world A strategy).procOneSlot A).1.1 := by
  let installation : Installation A strategy hwin := .inl ⟨first, current⟩
  let outputs :=
    profiledRawJointInitialCommonBothOutput A strategy (first, current)
  have hgraph : (env 2).graph = .both := by
    rw [hnext]
  have hsemantic :=
    literalCombinedFreshPhaseActivatedHonestMegaEntrySemanticTrace_two A
      strategy hwin controllers initialBank fallback fallbackTag env first
        current hfirst hcurrent
  have hchecker :=
    literalCombinedFreshPhaseActivatedHonestMegaEntry_run_two A strategy hwin
      controllers initialBank fallback fallbackTag env first current hfirst
        hcurrent
  have hhandoff :=
    literalCombinedFreshPhaseActivatedHonestMegaEntry_global_both_handoff A
      strategy hwin controllers initialBank fallback fallbackTag env 2
        installation outputs.1 outputs.2 hgraph hsemantic hchecker
  simpa only [installation, outputs, hnext, show 2 + 1 = 3 by omega] using
    hhandoff

end ProfiledRawJointGuardedCommonDecoratedPolicyPackage

end

end DetParityAutomaton

end DistributedSynthesis
