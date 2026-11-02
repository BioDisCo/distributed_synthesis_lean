/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralProductController
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonTwoRoundFront

/-!
# A finite seed bank for the literal-product suffix controllers

The concrete literal-product controller is intentionally rooted at one
literal guarded-common semantic point.  It must therefore not be started at
an arbitrary default point before the environment has supplied the finite
two-round seed.

This file collects the controller rooted at every possible two-round seed in
one finite dependent bank.  The two local activation maps install the same
bank member once an actual pair of simultaneous receives has made the seed
available at both endpoints.  The total bank transitions preserve that seed.
Their unequal-seed branches are only an off-invariant totalization; no graph,
orientation, hierarchy side, leader bit, semantic history, or view is used.

This is an activation adapter, not by itself the complete global front.  The
strict alternatives during the two seed rounds remain in the existing hybrid
initial shadow.  In particular, the arbitrary initial value of the total bank
controller is never asserted to represent the initial DPA run.
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

/-- The finite physical information which selects one literal-product suffix
after two actual simultaneous seed rounds. -/
abbrev ProfiledRawJointGuardedCommonLiteralProductSeed :=
  (In₁ × In₂) × (In₁ × In₂)

private abbrev Seed :=
  ProfiledRawJointGuardedCommonLiteralProductSeed
    (In₁ := In₁) (In₂ := In₂)

/-- The exact literal semantic point represented by a two-round seed. -/
def literalProductPointOfSeed (seed : Seed (In₁ := In₁) (In₂ := In₂)) :
    ProfiledRawJointGuardedCommonSemanticPoint A strategy :=
  profiledRawJointGuardedInitialCommonPoint A strategy seed

/-- The occurrence-sensitive decorated package selected once for this finite
seed. -/
noncomputable def literalProductPackageOfSeed
    (seed : Seed (In₁ := In₁) (In₂ := In₂)) :
    ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy hwin
      (literalProductPointOfSeed A strategy seed)
      (ProfiledRawJointGuardedCommonLiteralCrossExtraValid A strategy hwin) :=
  profiledRawJointGuardedCommonLiteralCrossDecoratedPolicyPackage A strategy
    hwin (literalProductPointOfSeed A strategy seed)

private abbrev Member
    (initialBank : ProfiledRawJointInitialControllerBank A strategy)
    (seed : Seed (In₁ := In₁) (In₂ := In₂)) :=
  (literalProductPackageOfSeed A strategy hwin seed
    ).literalProductMealyController A strategy hwin initialBank

/-- Process-one controls of all seed-rooted product controllers, tagged by the
seed which fixes their dependent type. -/
abbrev ProfiledRawJointGuardedCommonLiteralProductBankOneControl
    (initialBank : ProfiledRawJointInitialControllerBank A strategy) :=
  Σ seed : Seed (In₁ := In₁) (In₂ := In₂),
    (Member A strategy hwin initialBank seed).OneControl

/-- Process-two mirror. -/
abbrev ProfiledRawJointGuardedCommonLiteralProductBankTwoControl
    (initialBank : ProfiledRawJointInitialControllerBank A strategy) :=
  Σ seed : Seed (In₁ := In₁) (In₂ := In₂),
    (Member A strategy hwin initialBank seed).TwoControl

noncomputable instance literalProductBankOneControlFintype
    (initialBank : ProfiledRawJointInitialControllerBank A strategy) :
    Fintype
      (ProfiledRawJointGuardedCommonLiteralProductBankOneControl A strategy
        hwin initialBank) := by
  classical
  infer_instance

noncomputable instance literalProductBankTwoControlFintype
    (initialBank : ProfiledRawJointInitialControllerBank A strategy) :
    Fintype
      (ProfiledRawJointGuardedCommonLiteralProductBankTwoControl A strategy
        hwin initialBank) := by
  classical
  infer_instance

/-! ## Honest activation at a revealed seed -/

/-- Install process one's initial relay in the member selected by the actual
two-round seed. -/
def literalProductBankActivateOne
    (initialBank : ProfiledRawJointInitialControllerBank A strategy)
    (seed : Seed (In₁ := In₁) (In₂ := In₂)) :
    ProfiledRawJointGuardedCommonLiteralProductBankOneControl A strategy hwin
      initialBank :=
  ⟨seed, (Member A strategy hwin initialBank seed).initialOne⟩

/-- Process-two mirror. -/
def literalProductBankActivateTwo
    (initialBank : ProfiledRawJointInitialControllerBank A strategy)
    (seed : Seed (In₁ := In₁) (In₂ := In₂)) :
    ProfiledRawJointGuardedCommonLiteralProductBankTwoControl A strategy hwin
      initialBank :=
  ⟨seed, (Member A strategy hwin initialBank seed).initialTwo⟩

@[simp] theorem literalProductBankActivateOne_seed
    (initialBank : ProfiledRawJointInitialControllerBank A strategy)
    (seed : Seed (In₁ := In₁) (In₂ := In₂)) :
    (literalProductBankActivateOne A strategy hwin initialBank seed).1 = seed :=
  rfl

@[simp] theorem literalProductBankActivateTwo_seed
    (initialBank : ProfiledRawJointInitialControllerBank A strategy)
    (seed : Seed (In₁ := In₁) (In₂ := In₂)) :
    (literalProductBankActivateTwo A strategy hwin initialBank seed).1 = seed :=
  rfl

/-! ## Total seed-preserving bank transitions -/

noncomputable def literalProductBankNoRecvOne
    (initialBank : ProfiledRawJointInitialControllerBank A strategy)
    (state : ProfiledRawJointGuardedCommonLiteralProductBankOneControl A
      strategy hwin initialBank) (input : In₁) :
    ProfiledRawJointGuardedCommonLiteralProductBankOneControl A strategy hwin
        initialBank × Out₁ := by
  rcases state with ⟨seed, state⟩
  let next := (Member A strategy hwin initialBank seed).noRecvOne state input
  exact (⟨seed, next.1⟩, next.2)

noncomputable def literalProductBankNoRecvTwo
    (initialBank : ProfiledRawJointInitialControllerBank A strategy)
    (state : ProfiledRawJointGuardedCommonLiteralProductBankTwoControl A
      strategy hwin initialBank) (input : In₂) :
    ProfiledRawJointGuardedCommonLiteralProductBankTwoControl A strategy hwin
        initialBank × Out₂ := by
  rcases state with ⟨seed, state⟩
  let next := (Member A strategy hwin initialBank seed).noRecvTwo state input
  exact (⟨seed, next.1⟩, next.2)

/-- Same-seed receives dispatch to that literal-product member.  The
unequal-seed branch uses the receiving member's own initial partner state and
only totalizes unreachable mismatched bank tags. -/
noncomputable def literalProductBankRecvOne
    (initialBank : ProfiledRawJointInitialControllerBank A strategy)
    (one : ProfiledRawJointGuardedCommonLiteralProductBankOneControl A
      strategy hwin initialBank) (own : In₁)
    (two : ProfiledRawJointGuardedCommonLiteralProductBankTwoControl A
      strategy hwin initialBank) (delivered : In₂) :
    ProfiledRawJointGuardedCommonLiteralProductBankOneControl A strategy hwin
        initialBank × Out₁ := by
  rcases one with ⟨seedOne, one⟩
  rcases two with ⟨seedTwo, two⟩
  classical
  by_cases hseed : seedTwo = seedOne
  · subst seedTwo
    let next := (Member A strategy hwin initialBank seedOne).recvOne one own two
      delivered
    exact (⟨seedOne, next.1⟩, next.2)
  · let next := (Member A strategy hwin initialBank seedOne).recvOne one own
      (Member A strategy hwin initialBank seedOne).initialTwo delivered
    exact (⟨seedOne, next.1⟩, next.2)

/-- Process-two mirror. -/
noncomputable def literalProductBankRecvTwo
    (initialBank : ProfiledRawJointInitialControllerBank A strategy)
    (two : ProfiledRawJointGuardedCommonLiteralProductBankTwoControl A
      strategy hwin initialBank) (own : In₂)
    (one : ProfiledRawJointGuardedCommonLiteralProductBankOneControl A
      strategy hwin initialBank) (delivered : In₁) :
    ProfiledRawJointGuardedCommonLiteralProductBankTwoControl A strategy hwin
        initialBank × Out₂ := by
  rcases two with ⟨seedTwo, two⟩
  rcases one with ⟨seedOne, one⟩
  classical
  by_cases hseed : seedOne = seedTwo
  · subst seedOne
    let next := (Member A strategy hwin initialBank seedTwo).recvTwo two own one
      delivered
    exact (⟨seedTwo, next.1⟩, next.2)
  · let next := (Member A strategy hwin initialBank seedTwo).recvTwo two own
      (Member A strategy hwin initialBank seedTwo).initialOne delivered
    exact (⟨seedTwo, next.1⟩, next.2)

@[simp] theorem literalProductBankNoRecvOne_seed
    (initialBank : ProfiledRawJointInitialControllerBank A strategy)
    (state : ProfiledRawJointGuardedCommonLiteralProductBankOneControl A
      strategy hwin initialBank) (input : In₁) :
    (literalProductBankNoRecvOne A strategy hwin initialBank state input).1.1 =
      state.1 := by
  rcases state with ⟨seed, state⟩
  rfl

@[simp] theorem literalProductBankNoRecvTwo_seed
    (initialBank : ProfiledRawJointInitialControllerBank A strategy)
    (state : ProfiledRawJointGuardedCommonLiteralProductBankTwoControl A
      strategy hwin initialBank) (input : In₂) :
    (literalProductBankNoRecvTwo A strategy hwin initialBank state input).1.1 =
      state.1 := by
  rcases state with ⟨seed, state⟩
  rfl

@[simp] theorem literalProductBankRecvOne_seed
    (initialBank : ProfiledRawJointInitialControllerBank A strategy)
    (one : ProfiledRawJointGuardedCommonLiteralProductBankOneControl A
      strategy hwin initialBank) (own : In₁)
    (two : ProfiledRawJointGuardedCommonLiteralProductBankTwoControl A
      strategy hwin initialBank) (delivered : In₂) :
    (literalProductBankRecvOne A strategy hwin initialBank one own two
      delivered).1.1 = one.1 := by
  rcases one with ⟨seedOne, one⟩
  rcases two with ⟨seedTwo, two⟩
  classical
  by_cases hseed : seedTwo = seedOne
  · subst seedTwo
    simp [literalProductBankRecvOne]
  · simp [literalProductBankRecvOne, hseed]

@[simp] theorem literalProductBankRecvTwo_seed
    (initialBank : ProfiledRawJointInitialControllerBank A strategy)
    (two : ProfiledRawJointGuardedCommonLiteralProductBankTwoControl A
      strategy hwin initialBank) (own : In₂)
    (one : ProfiledRawJointGuardedCommonLiteralProductBankOneControl A
      strategy hwin initialBank) (delivered : In₁) :
    (literalProductBankRecvTwo A strategy hwin initialBank two own one
      delivered).1.1 = two.1 := by
  rcases two with ⟨seedTwo, two⟩
  rcases one with ⟨seedOne, one⟩
  classical
  by_cases hseed : seedOne = seedTwo
  · subst seedOne
    simp [literalProductBankRecvTwo]
  · simp [literalProductBankRecvTwo, hseed]

/-! ## A total controller and its honest activation contract -/

/-- Total controller over the finite bank.  Its default-seed initial fields
exist only to satisfy the standalone controller interface.  Global use must
enter through `literalProductBankActivateOne/Two` after the seed is known. -/
noncomputable def literalProductBankMealyController
    (initialBank : ProfiledRawJointInitialControllerBank A strategy) :
    FinitePairedMealyController In₁ In₂ Out₁ Out₂ where
  OneControl :=
    ProfiledRawJointGuardedCommonLiteralProductBankOneControl A strategy hwin
      initialBank
  TwoControl :=
    ProfiledRawJointGuardedCommonLiteralProductBankTwoControl A strategy hwin
      initialBank
  oneFinite := inferInstance
  twoFinite := inferInstance
  initialOne := literalProductBankActivateOne A strategy hwin initialBank
    ((default, default), (default, default))
  initialTwo := literalProductBankActivateTwo A strategy hwin initialBank
    ((default, default), (default, default))
  noRecvOne := literalProductBankNoRecvOne A strategy hwin initialBank
  noRecvTwo := literalProductBankNoRecvTwo A strategy hwin initialBank
  recvOne := literalProductBankRecvOne A strategy hwin initialBank
  recvTwo := literalProductBankRecvTwo A strategy hwin initialBank

/-- Activating both endpoints with the same revealed seed establishes the
bank-tag agreement needed by every honest receive dispatch. -/
theorem literalProductBankActivate_seeds_agree
    (initialBank : ProfiledRawJointInitialControllerBank A strategy)
    (seed : Seed (In₁ := In₁) (In₂ := In₂)) :
    (literalProductBankActivateOne A strategy hwin initialBank seed).1 =
      (literalProductBankActivateTwo A strategy hwin initialBank seed).1 :=
  rfl

end ProfiledRawJointGuardedCommonDecoratedPolicyPackage

end

end DetParityAutomaton

end DistributedSynthesis
