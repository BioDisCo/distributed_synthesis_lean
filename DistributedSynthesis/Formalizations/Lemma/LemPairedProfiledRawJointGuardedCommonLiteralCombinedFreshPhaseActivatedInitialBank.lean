/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCombinedFreshPhaseActivatedController
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedInitialCommonPolicyBank

/-!
# A finite seed bank for the phase-activated controller

The standalone phase-activated controller is parametrized by one literal
guarded-common semantic occurrence.  It therefore cannot soundly be started
at an arbitrary default occurrence and simultaneously be identified with the
initial DPA run.

This file collects the phase-activated controller rooted at every possible
two-round simultaneous seed in one finite dependent bank.  Once two actual
simultaneous receives have revealed the same seed to both endpoints, the two
local activation maps install the corresponding member.  Every transition
preserves that seed.  Unequal-seed receive branches only totalize unreachable
mixed states and do not inspect a graph, orientation, leader, semantic world,
or history.
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

namespace ProfiledRawJointGuardedCommonDecoratedPolicyPackage

/-- The finite physical seed exposed by two simultaneous receives. -/
abbrev ProfiledRawJointGuardedCommonLiteralPhaseActivatedSeed :=
  (In₁ × In₂) × (In₁ × In₂)

private abbrev Seed :=
  ProfiledRawJointGuardedCommonLiteralPhaseActivatedSeed
    (In₁ := In₁) (In₂ := In₂)

/-- The exact occurrence selected by a revealed seed. -/
def literalCombinedFreshPhaseActivatedPointOfSeed
    (seed : Seed (In₁ := In₁) (In₂ := In₂)) :
    ProfiledRawJointGuardedCommonSemanticPoint A strategy :=
  profiledRawJointGuardedInitialCommonPoint A strategy seed

/-- The occurrence-sensitive decorated package selected for that seed. -/
noncomputable def literalCombinedFreshPhaseActivatedPackageOfSeed
    (seed : Seed (In₁ := In₁) (In₂ := In₂)) :
    ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy hwin
      (literalCombinedFreshPhaseActivatedPointOfSeed A strategy seed)
      (ProfiledRawJointGuardedCommonLiteralCrossExtraValid A strategy hwin) :=
  profiledRawJointGuardedCommonLiteralCrossDecoratedPolicyPackage A strategy
    hwin (literalCombinedFreshPhaseActivatedPointOfSeed A strategy seed)

private abbrev Package
    (seed : Seed (In₁ := In₁) (In₂ := In₂)) :=
  literalCombinedFreshPhaseActivatedPackageOfSeed A strategy hwin seed

private abbrev Member
    (seed : Seed (In₁ := In₁) (In₂ := In₂)) :=
  (Package A strategy hwin seed
    ).literalCombinedFreshPhaseActivatedController A strategy hwin

/-- Process-one controls of every seed-rooted activated member. -/
abbrev ProfiledRawJointGuardedCommonLiteralPhaseActivatedBankOneControl :=
  Σ seed : Seed (In₁ := In₁) (In₂ := In₂),
    (Member A strategy hwin seed).OneControl

/-- Process-two mirror. -/
abbrev ProfiledRawJointGuardedCommonLiteralPhaseActivatedBankTwoControl :=
  Σ seed : Seed (In₁ := In₁) (In₂ := In₂),
    (Member A strategy hwin seed).TwoControl

noncomputable instance literalCombinedFreshPhaseActivatedBankOneControlFintype :
    Fintype
      (ProfiledRawJointGuardedCommonLiteralPhaseActivatedBankOneControl A
        strategy hwin) := by
  classical
  infer_instance

noncomputable instance literalCombinedFreshPhaseActivatedBankTwoControlFintype :
    Fintype
      (ProfiledRawJointGuardedCommonLiteralPhaseActivatedBankTwoControl A
        strategy hwin) := by
  classical
  infer_instance

/-! ## Honest activation -/

/-- Install process one in the member indexed by the revealed seed. -/
def literalCombinedFreshPhaseActivatedBankActivateOne
    (seed : Seed (In₁ := In₁) (In₂ := In₂)) :
    ProfiledRawJointGuardedCommonLiteralPhaseActivatedBankOneControl A strategy
      hwin :=
  ⟨seed, (Member A strategy hwin seed).initialOne⟩

/-- Process-two mirror. -/
def literalCombinedFreshPhaseActivatedBankActivateTwo
    (seed : Seed (In₁ := In₁) (In₂ := In₂)) :
    ProfiledRawJointGuardedCommonLiteralPhaseActivatedBankTwoControl A strategy
      hwin :=
  ⟨seed, (Member A strategy hwin seed).initialTwo⟩

@[simp] theorem literalCombinedFreshPhaseActivatedBankActivateOne_seed
    (seed : Seed (In₁ := In₁) (In₂ := In₂)) :
    (literalCombinedFreshPhaseActivatedBankActivateOne A strategy hwin
      seed).1 = seed :=
  rfl

@[simp] theorem literalCombinedFreshPhaseActivatedBankActivateTwo_seed
    (seed : Seed (In₁ := In₁) (In₂ := In₂)) :
    (literalCombinedFreshPhaseActivatedBankActivateTwo A strategy hwin
      seed).1 = seed :=
  rfl

/-! ## Seed-preserving transitions -/

noncomputable def literalCombinedFreshPhaseActivatedBankNoRecvOne
    (state :
      ProfiledRawJointGuardedCommonLiteralPhaseActivatedBankOneControl A
        strategy hwin)
    (input : In₁) :
    ProfiledRawJointGuardedCommonLiteralPhaseActivatedBankOneControl A strategy
        hwin × Out₁ := by
  rcases state with ⟨seed, state⟩
  let next := (Member A strategy hwin seed).noRecvOne state input
  exact (⟨seed, next.1⟩, next.2)

noncomputable def literalCombinedFreshPhaseActivatedBankNoRecvTwo
    (state :
      ProfiledRawJointGuardedCommonLiteralPhaseActivatedBankTwoControl A
        strategy hwin)
    (input : In₂) :
    ProfiledRawJointGuardedCommonLiteralPhaseActivatedBankTwoControl A strategy
        hwin × Out₂ := by
  rcases state with ⟨seed, state⟩
  let next := (Member A strategy hwin seed).noRecvTwo state input
  exact (⟨seed, next.1⟩, next.2)

/-- Equal tags dispatch to one member.  The unequal branch uses the receiving
member's own initial partner and is unreachable after honest activation. -/
noncomputable def literalCombinedFreshPhaseActivatedBankRecvOne
    (one : ProfiledRawJointGuardedCommonLiteralPhaseActivatedBankOneControl A
      strategy hwin)
    (own : In₁)
    (two : ProfiledRawJointGuardedCommonLiteralPhaseActivatedBankTwoControl A
      strategy hwin)
    (delivered : In₂) :
    ProfiledRawJointGuardedCommonLiteralPhaseActivatedBankOneControl A strategy
        hwin × Out₁ := by
  rcases one with ⟨seedOne, one⟩
  rcases two with ⟨seedTwo, two⟩
  classical
  by_cases hseed : seedTwo = seedOne
  · subst seedTwo
    let next := (Member A strategy hwin seedOne).recvOne one own two delivered
    exact (⟨seedOne, next.1⟩, next.2)
  · let next := (Member A strategy hwin seedOne).recvOne one own
      (Member A strategy hwin seedOne).initialTwo delivered
    exact (⟨seedOne, next.1⟩, next.2)

/-- Process-two mirror. -/
noncomputable def literalCombinedFreshPhaseActivatedBankRecvTwo
    (two : ProfiledRawJointGuardedCommonLiteralPhaseActivatedBankTwoControl A
      strategy hwin)
    (own : In₂)
    (one : ProfiledRawJointGuardedCommonLiteralPhaseActivatedBankOneControl A
      strategy hwin)
    (delivered : In₁) :
    ProfiledRawJointGuardedCommonLiteralPhaseActivatedBankTwoControl A strategy
        hwin × Out₂ := by
  rcases two with ⟨seedTwo, two⟩
  rcases one with ⟨seedOne, one⟩
  classical
  by_cases hseed : seedOne = seedTwo
  · subst seedOne
    let next := (Member A strategy hwin seedTwo).recvTwo two own one delivered
    exact (⟨seedTwo, next.1⟩, next.2)
  · let next := (Member A strategy hwin seedTwo).recvTwo two own
      (Member A strategy hwin seedTwo).initialOne delivered
    exact (⟨seedTwo, next.1⟩, next.2)

@[simp] theorem literalCombinedFreshPhaseActivatedBankNoRecvOne_seed
    (state :
      ProfiledRawJointGuardedCommonLiteralPhaseActivatedBankOneControl A
        strategy hwin)
    (input : In₁) :
    (literalCombinedFreshPhaseActivatedBankNoRecvOne A strategy hwin state
      input).1.1 = state.1 := by
  rcases state with ⟨seed, state⟩
  rfl

@[simp] theorem literalCombinedFreshPhaseActivatedBankNoRecvTwo_seed
    (state :
      ProfiledRawJointGuardedCommonLiteralPhaseActivatedBankTwoControl A
        strategy hwin)
    (input : In₂) :
    (literalCombinedFreshPhaseActivatedBankNoRecvTwo A strategy hwin state
      input).1.1 = state.1 := by
  rcases state with ⟨seed, state⟩
  rfl

@[simp] theorem literalCombinedFreshPhaseActivatedBankRecvOne_seed
    (one : ProfiledRawJointGuardedCommonLiteralPhaseActivatedBankOneControl A
      strategy hwin)
    (own : In₁)
    (two : ProfiledRawJointGuardedCommonLiteralPhaseActivatedBankTwoControl A
      strategy hwin)
    (delivered : In₂) :
    (literalCombinedFreshPhaseActivatedBankRecvOne A strategy hwin one own two
      delivered).1.1 = one.1 := by
  rcases one with ⟨seedOne, one⟩
  rcases two with ⟨seedTwo, two⟩
  classical
  by_cases hseed : seedTwo = seedOne
  · subst seedTwo
    simp [literalCombinedFreshPhaseActivatedBankRecvOne]
  · simp [literalCombinedFreshPhaseActivatedBankRecvOne, hseed]

@[simp] theorem literalCombinedFreshPhaseActivatedBankRecvTwo_seed
    (two : ProfiledRawJointGuardedCommonLiteralPhaseActivatedBankTwoControl A
      strategy hwin)
    (own : In₂)
    (one : ProfiledRawJointGuardedCommonLiteralPhaseActivatedBankOneControl A
      strategy hwin)
    (delivered : In₁) :
    (literalCombinedFreshPhaseActivatedBankRecvTwo A strategy hwin two own one
      delivered).1.1 = two.1 := by
  rcases two with ⟨seedTwo, two⟩
  rcases one with ⟨seedOne, one⟩
  classical
  by_cases hseed : seedOne = seedTwo
  · subst seedOne
    simp [literalCombinedFreshPhaseActivatedBankRecvTwo]
  · simp [literalCombinedFreshPhaseActivatedBankRecvTwo, hseed]

/-! ## Total bank controller -/

/-- A finite controller containing every seed-rooted phase-activated member.
Its default initial member is only an interface totalization.  Global use must
enter through the two activation maps after the seed has been revealed. -/
noncomputable def literalCombinedFreshPhaseActivatedBankController :
    FinitePairedMealyController In₁ In₂ Out₁ Out₂ where
  OneControl :=
    ProfiledRawJointGuardedCommonLiteralPhaseActivatedBankOneControl A strategy
      hwin
  TwoControl :=
    ProfiledRawJointGuardedCommonLiteralPhaseActivatedBankTwoControl A strategy
      hwin
  oneFinite := inferInstance
  twoFinite := inferInstance
  initialOne := literalCombinedFreshPhaseActivatedBankActivateOne A strategy
    hwin ((default, default), (default, default))
  initialTwo := literalCombinedFreshPhaseActivatedBankActivateTwo A strategy
    hwin ((default, default), (default, default))
  noRecvOne := literalCombinedFreshPhaseActivatedBankNoRecvOne A strategy hwin
  noRecvTwo := literalCombinedFreshPhaseActivatedBankNoRecvTwo A strategy hwin
  recvOne := literalCombinedFreshPhaseActivatedBankRecvOne A strategy hwin
  recvTwo := literalCombinedFreshPhaseActivatedBankRecvTwo A strategy hwin

/-- Honest activation gives both endpoints definitionally equal bank tags. -/
theorem literalCombinedFreshPhaseActivatedBankActivate_seeds_agree
    (seed : Seed (In₁ := In₁) (In₂ := In₂)) :
    (literalCombinedFreshPhaseActivatedBankActivateOne A strategy hwin seed).1 =
      (literalCombinedFreshPhaseActivatedBankActivateTwo A strategy hwin
        seed).1 :=
  rfl

end ProfiledRawJointGuardedCommonDecoratedPolicyPackage

end

end DetParityAutomaton

end DistributedSynthesis
