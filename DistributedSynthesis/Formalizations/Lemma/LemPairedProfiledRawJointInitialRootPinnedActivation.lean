/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointInitialFreshPolicyActivation
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedFirstPolicyBank

/-!
# Root-pinned activation at the exceptional raw-joint seam

The ordinary policy root selected from a guarded initial key does not by
itself preserve the key's overlap table: provenance may choose another
same-code semantic source.  The exceptional first recurrent block therefore
uses a one-shot root predicate.  For an initial-left key it requires the
installed process-one/right lambda to match the stored process-one overlap;
the initial-right predicate is the exact mirror.

The key's literal-boundary witness proves this predicate for the original
semantic root.  Root-pinned finite-code rationalization then preserves it at
the unique fresh root.  Immediately below that root, the overlap disappears
and the already established finite bank of fresh ordinary child policies is
used.  Neither the selected side nor any boundary history is runtime input.
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

/-! ## Key-specific one-shot predicates -/

/-- The exceptional right-block root must select a process-one lambda which
matches the overlap table carried by the initial-left key. -/
def ProfiledRawJointInitialLeftRootPredicate
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (key : ProfiledRawJointInitialLeftGuardedKey A strategy)
    (rawMove : ProfiledRawJointLambdaFamilyMove A (I := Unit)) : Prop :=
  ∃ lambda : ProcOnePairedRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂),
    rawMove.rightLambda () = some lambda ∧ key.1.2.Matches lambda

/-- Mirror one-shot predicate at an initial-right key. -/
def ProfiledRawJointInitialRightRootPredicate
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (key : ProfiledRawJointInitialRightGuardedKey A strategy)
    (rawMove : ProfiledRawJointLambdaFamilyMove A (I := Unit)) : Prop :=
  ∃ lambda : ProcTwoPairedLeftLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂),
    rawMove.leftLambda () = some lambda ∧ key.1.2.Matches lambda

/-! ## Complete proof-side activations -/

/-- A literal semantic boundary and its one-shot overlap-pinned rational
policy.  The `source_boundary` witness is proof data only. -/
structure ProfiledRawJointInitialLeftRootPinnedActivation
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (key : ProfiledRawJointInitialLeftGuardedKey A strategy) where
  source : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit)
  source_boundary : ∃ past : List (In₁ × In₂), ∃ move : In₁ × In₂,
    source = profiledRawJointInitialLeftBoundaryState A strategy past move
  source_code : source.code A = key.1.1
  literal_root : ProfiledRawJointInitialLeftRootPredicate A strategy key
    (source.move A)
  pinned : ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
    source (ProfiledRawJointInitialLeftRootPredicate A strategy key)

/-- Initial-right mirror. -/
structure ProfiledRawJointInitialRightRootPinnedActivation
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (key : ProfiledRawJointInitialRightGuardedKey A strategy) where
  source : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit)
  source_boundary : ∃ past : List (In₂ × In₁), ∃ move : In₂ × In₁,
    source = profiledRawJointInitialRightBoundaryState A strategy past move
  source_code : source.code A = key.1.1
  literal_root : ProfiledRawJointInitialRightRootPredicate A strategy key
    (source.move A)
  pinned : ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
    source (ProfiledRawJointInitialRightRootPredicate A strategy key)

omit [DecidableEq In₁] [DecidableEq In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- The original winner supplies the complete overlap-pinned left-key
activation unconditionally. -/
theorem nonempty_profiledRawJointInitialLeftRootPinnedActivation
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (key : ProfiledRawJointInitialLeftGuardedKey A strategy) :
    Nonempty
      (ProfiledRawJointInitialLeftRootPinnedActivation A strategy key) := by
  rcases key.2 with ⟨past, move, hkey⟩
  let source := profiledRawJointInitialLeftBoundaryState A strategy past move
  have hcode : source.code A = key.1.1 := by
    have hfst := congrArg Prod.fst hkey
    change key.1.1 = source.code A at hfst
    exact hfst.symm
  have hoverlap :
      key.1.2 = initialLeftNextBothProfile strategy past move := by
    exact congrArg Prod.snd hkey
  have hroot : ProfiledRawJointInitialLeftRootPredicate A strategy key
      (source.move A) := by
    let world := profiledRawJointInitialLeftBoundaryWorld A strategy past move
    refine ⟨(world.procOne A).lambdaOfStrategy, rfl, ?_⟩
    rw [hoverlap]
    change (initialLeftNextBothProfile strategy past move).Matches
      ((profiledRawJointInitialLeftBoundaryWorld A strategy past move).procOne
        A).lambdaOfStrategy
    exact initialLeftNextBothProfile_matches_generated strategy past move
  let pinned := Classical.choice
    (nonempty_profiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      hwin source (ProfiledRawJointInitialLeftRootPredicate A strategy key)
      hroot)
  exact ⟨{
    source := source
    source_boundary := ⟨past, move, rfl⟩
    source_code := hcode
    literal_root := hroot
    pinned := pinned }⟩

omit [DecidableEq In₁] [DecidableEq In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Mirror unconditional activation. -/
theorem nonempty_profiledRawJointInitialRightRootPinnedActivation
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (key : ProfiledRawJointInitialRightGuardedKey A strategy) :
    Nonempty
      (ProfiledRawJointInitialRightRootPinnedActivation A strategy key) := by
  rcases key.2 with ⟨past, move, hkey⟩
  let source := profiledRawJointInitialRightBoundaryState A strategy past move
  have hcode : source.code A = key.1.1 := by
    have hfst := congrArg Prod.fst hkey
    change key.1.1 = source.code A at hfst
    exact hfst.symm
  have hoverlap :
      key.1.2 = initialRightNextBothProfile strategy past move := by
    exact congrArg Prod.snd hkey
  have hroot : ProfiledRawJointInitialRightRootPredicate A strategy key
      (source.move A) := by
    let world := profiledRawJointInitialRightBoundaryWorld A strategy past move
    refine ⟨(world.procTwo A).lambdaOfStrategy, rfl, ?_⟩
    rw [hoverlap]
    change (initialRightNextBothProfile strategy past move).Matches
      ((profiledRawJointInitialRightBoundaryWorld A strategy past move).procTwo
        A).lambdaOfStrategy
    exact initialRightNextBothProfile_matches_generated strategy past move
  let pinned := Classical.choice
    (nonempty_profiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      hwin source (ProfiledRawJointInitialRightRootPredicate A strategy key)
      hroot)
  exact ⟨{
    source := source
    source_boundary := ⟨past, move, rfl⟩
    source_code := hcode
    literal_root := hroot
    pinned := pinned }⟩

/-! ## Once-selected activations and root readback -/

noncomputable def profiledRawJointInitialLeftRootPinnedActivation
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (key : ProfiledRawJointInitialLeftGuardedKey A strategy) :
    ProfiledRawJointInitialLeftRootPinnedActivation A strategy key :=
  Classical.choice
    (nonempty_profiledRawJointInitialLeftRootPinnedActivation A strategy hwin
      key)

noncomputable def profiledRawJointInitialRightRootPinnedActivation
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (key : ProfiledRawJointInitialRightGuardedKey A strategy) :
    ProfiledRawJointInitialRightRootPinnedActivation A strategy key :=
  Classical.choice
    (nonempty_profiledRawJointInitialRightRootPinnedActivation A strategy hwin
      key)

section
omit [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂]

/-- The move actually installed at a left-key guarded root selects a right
lambda matching the key's overlap. -/
theorem ProfiledRawJointInitialLeftRootPinnedActivation.rootMove_matches
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {key : ProfiledRawJointInitialLeftGuardedKey A strategy}
    (activation : ProfiledRawJointInitialLeftRootPinnedActivation A strategy
      key) :
    ProfiledRawJointInitialLeftRootPredicate A strategy key
      activation.pinned.rootMove :=
  activation.pinned.rootMove_realizes.2.1

/-- Mirror root readback. -/
theorem ProfiledRawJointInitialRightRootPinnedActivation.rootMove_matches
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {key : ProfiledRawJointInitialRightGuardedKey A strategy}
    (activation : ProfiledRawJointInitialRightRootPinnedActivation A strategy
      key) :
    ProfiledRawJointInitialRightRootPredicate A strategy key
      activation.pinned.rootMove :=
  activation.pinned.rootMove_realizes.2.1

/-- The semantic source installed by the guarded rational root still has the
finite code carried by the left key. -/
theorem ProfiledRawJointInitialLeftRootPinnedActivation.selectedSource_code
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {key : ProfiledRawJointInitialLeftGuardedKey A strategy}
    (activation : ProfiledRawJointInitialLeftRootPinnedActivation A strategy
      key) :
    (profiledRawJointRootPinnedSelectedSource A strategy activation.source
        (ProfiledRawJointInitialLeftRootPredicate A strategy key)
        activation.pinned).code A = key.1.1 := by
  exact (profiledRawJointRootPinnedSelectedSource_code A strategy
    activation.source
    (ProfiledRawJointInitialLeftRootPredicate A strategy key)
    activation.pinned).trans activation.source_code

/-- Mirror selected-source code. -/
theorem ProfiledRawJointInitialRightRootPinnedActivation.selectedSource_code
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {key : ProfiledRawJointInitialRightGuardedKey A strategy}
    (activation : ProfiledRawJointInitialRightRootPinnedActivation A strategy
      key) :
    (profiledRawJointRootPinnedSelectedSource A strategy activation.source
        (ProfiledRawJointInitialRightRootPredicate A strategy key)
        activation.pinned).code A = key.1.1 := by
  exact (profiledRawJointRootPinnedSelectedSource_code A strategy
    activation.source
    (ProfiledRawJointInitialRightRootPredicate A strategy key)
    activation.pinned).trans activation.source_code

end

/-! ## The ordinary child-policy banks below the exceptional root -/

/-- Once the exceptional right block chooses a literal child code, all later
blocks use the corresponding ordinary fixed provenance policy. -/
noncomputable def
    ProfiledRawJointInitialLeftRootPinnedActivation.childPolicyBank
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {key : ProfiledRawJointInitialLeftGuardedKey A strategy}
    (activation : ProfiledRawJointInitialLeftRootPinnedActivation A strategy
      key)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env)) :
    ProfiledRawJointOneSidedLiteralChildPolicyBank A strategy
      (profiledRawJointRootPinnedSelectedSource A strategy activation.source
        (ProfiledRawJointInitialLeftRootPredicate A strategy key)
        activation.pinned) :=
  profiledRawJointRootPinnedLiteralChildPolicyBank A strategy hwin
    activation.source
    (ProfiledRawJointInitialLeftRootPredicate A strategy key)
    activation.pinned

/-- Mirror child-policy bank. -/
noncomputable def
    ProfiledRawJointInitialRightRootPinnedActivation.childPolicyBank
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {key : ProfiledRawJointInitialRightGuardedKey A strategy}
    (activation : ProfiledRawJointInitialRightRootPinnedActivation A strategy
      key)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env)) :
    ProfiledRawJointOneSidedLiteralChildPolicyBank A strategy
      (profiledRawJointRootPinnedSelectedSource A strategy activation.source
        (ProfiledRawJointInitialRightRootPredicate A strategy key)
        activation.pinned) :=
  profiledRawJointRootPinnedLiteralChildPolicyBank A strategy hwin
    activation.source
    (ProfiledRawJointInitialRightRootPredicate A strategy key)
    activation.pinned

end

end DetParityAutomaton

end DistributedSynthesis
