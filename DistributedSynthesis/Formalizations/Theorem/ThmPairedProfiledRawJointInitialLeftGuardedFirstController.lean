/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointInitialRootPinnedActivation
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledRawJointGuardedFirstRightBlockMonitor
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledRawJointGuardedFirstPolicyRootHandoff

/-!
# Initial-left key to the exceptional right controller

This is the concrete adapter between the finite guarded initial key and the
generic root-pinned right-block monitor.  The key proves that the selected
incidence code is right-live.  Its one-shot root predicate proves that the
lambda actually installed by rationalization matches the stored overlap
table.  Everything below the block is indexed by the emitted finite literal
child and therefore uses a fresh ordinary policy.

The adapter is proof-side bank construction.  Its local controller receives
neither an orientation nor a strict-leader signal.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

/-- Complete exceptional right-controller package at one initial-left key. -/
structure ProfiledRawJointInitialLeftGuardedFirstControllerPackage
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (key : ProfiledRawJointInitialLeftGuardedKey A strategy)
    (activation : ProfiledRawJointInitialLeftRootPinnedActivation A strategy
      key) where
  source : ProfiledRawRightSlot A
  source_active : (activation.source.code A).family.right () = some source
  block : ProfiledRawJointGuardedFirstRightBlockActivation A strategy
    activation.source
    (ProfiledRawJointInitialLeftRootPredicate A strategy key)
    activation.pinned source
  overlap_matches : key.1.2.Matches block.lambda

omit [DecidableEq In₁] [DecidableEq In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- The key-specific root-pinned activation supplies the complete exceptional
right controller without an additional hypothesis. -/
theorem nonempty_profiledRawJointInitialLeftGuardedFirstControllerPackage
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (key : ProfiledRawJointInitialLeftGuardedKey A strategy)
    (activation : ProfiledRawJointInitialLeftRootPinnedActivation A strategy
      key) :
    Nonempty (ProfiledRawJointInitialLeftGuardedFirstControllerPackage A
      strategy key activation) := by
  rcases profiledRawJointInitialLeftGuardedKey_right_live A strategy key with
    ⟨source, hkeySource, _hleftEmpty⟩
  have hsource : (activation.source.code A).family.right () = some source := by
    rw [activation.source_code]
    exact hkeySource
  let block := Classical.choice
    (nonempty_profiledRawJointGuardedFirstRightBlockActivation A strategy
      activation.source
      (ProfiledRawJointInitialLeftRootPredicate A strategy key)
      activation.pinned source hsource)
  have hoverlap : key.1.2.Matches block.lambda := by
    rcases activation.rootMove_matches A with
      ⟨rootLambda, hrootLambda, hmatches⟩
    have hlambda : rootLambda = block.lambda := by
      exact Option.some.inj
        (hrootLambda.symm.trans block.lambda_selected)
    simpa [hlambda] using hmatches
  exact ⟨{
    source := source
    source_active := hsource
    block := block
    overlap_matches := hoverlap }⟩

/-- Select the finite exceptional package once for a fixed activation. -/
noncomputable def profiledRawJointInitialLeftGuardedFirstControllerPackage
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (key : ProfiledRawJointInitialLeftGuardedKey A strategy)
    (activation : ProfiledRawJointInitialLeftRootPinnedActivation A strategy
      key) :
    ProfiledRawJointInitialLeftGuardedFirstControllerPackage A strategy key
      activation :=
  Classical.choice
    (nonempty_profiledRawJointInitialLeftGuardedFirstControllerPackage A
      strategy key activation)

/-- Unconditional finite narrowing of the exceptional block stored in the
key package.  Keeping the controller existential outside the dependent
package avoids adding any runtime datum; callers choose it once for the
finite key bank. -/
theorem
    ProfiledRawJointInitialLeftGuardedFirstControllerPackage.existsController
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {key : ProfiledRawJointInitialLeftGuardedKey A strategy}
    {activation : ProfiledRawJointInitialLeftRootPinnedActivation A strategy
      key}
    (package : ProfiledRawJointInitialLeftGuardedFirstControllerPackage A
      strategy key activation) :
    ∃ controller :
        TransitionRationalTree.{u, max u v x y s, max u v x y s} In₁
        (NarrowedBlockLabel In₂ In₁
          (ProfiledRawJointGuardedFirstRightReceiverOutput A strategy
            activation.source
            (ProfiledRawJointInitialLeftRootPredicate A strategy key)
            activation.pinned) Out₁
          (profiledRawJointGuardedFirstRightBlockMonitor A strategy
            activation.source
            (ProfiledRawJointInitialLeftRootPredicate A strategy key)
            activation.pinned package.source).State),
      NarrowedAllThreadsWin
        (profiledRawJointGuardedFirstRightBlockMonitor A strategy
          activation.source
          (ProfiledRawJointInitialLeftRootPredicate A strategy key)
          activation.pinned package.source) controller.labeledTree :=
  exists_profiledRawJointGuardedFirstRightController A package.source
    package.block

/-! ## Literal-child readback and ordinary-policy handoff -/

/-- Every target emitted by the exceptional controller has exactly the
finite type indexing the ordinary child-policy bank. -/
noncomputable def
    ProfiledRawJointInitialLeftGuardedFirstControllerPackage.childPolicyFor
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {key : ProfiledRawJointInitialLeftGuardedKey A strategy}
    {activation : ProfiledRawJointInitialLeftRootPinnedActivation A strategy
      key}
    (package : ProfiledRawJointInitialLeftGuardedFirstControllerPackage A
      strategy key activation)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (child : ProfiledRawJointOneSidedLiteralChildCode A strategy
      (profiledRawJointRootPinnedSelectedSource A strategy activation.source
        (ProfiledRawJointInitialLeftRootPredicate A strategy key)
        activation.pinned)) :
    ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy child.1 :=
  activation.childPolicyBank A hwin child

/-- Read the child key out of one controller label and hand it directly to
the fresh ordinary bank. -/
noncomputable def
    ProfiledRawJointInitialLeftGuardedFirstControllerPackage.childPolicyForOutput
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {key : ProfiledRawJointInitialLeftGuardedKey A strategy}
    {activation : ProfiledRawJointInitialLeftRootPinnedActivation A strategy
      key}
    (package : ProfiledRawJointInitialLeftGuardedFirstControllerPackage A
      strategy key activation)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (output : ProfiledRawJointGuardedFirstRightReceiverOutput A strategy
      activation.source
      (ProfiledRawJointInitialLeftRootPredicate A strategy key)
      activation.pinned)
    (row : PairedEntryRow) :
    ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (output.target row).1 :=
  package.childPolicyFor A hwin (output.target row)

/-- At the semantic realizing receiver, the preceding handoff policy is
rooted at the exact raw child of the concrete physical row/past/input. -/
noncomputable def
    ProfiledRawJointInitialLeftGuardedFirstControllerPackage.exactChildPolicy
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {key : ProfiledRawJointInitialLeftGuardedKey A strategy}
    {activation : ProfiledRawJointInitialLeftRootPinnedActivation A strategy
      key}
    (package : ProfiledRawJointInitialLeftGuardedFirstControllerPackage A
      strategy key activation)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (row : PairedEntryRow) (past : List (In₂ × In₁))
    (input : In₂ × In₁) :
    ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (profiledRawJointGuardedFirstRightTarget A strategy activation.source
        (ProfiledRawJointInitialLeftRootPredicate A strategy key)
        activation.pinned row past input).1 :=
  package.childPolicyFor A hwin
    (profiledRawJointGuardedFirstRightTarget A strategy activation.source
      (ProfiledRawJointInitialLeftRootPredicate A strategy key)
      activation.pinned row past input)

/-- Strong operational handoff: the exact child is packaged as the reachable
left-policy root macro consumed by the alternating controller.  Its state is
definitionally the selected ordinary policy's `run []`. -/
noncomputable def
    ProfiledRawJointInitialLeftGuardedFirstControllerPackage.exactChildRootMacro
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {key : ProfiledRawJointInitialLeftGuardedKey A strategy}
    {activation : ProfiledRawJointInitialLeftRootPinnedActivation A strategy
      key}
    (package : ProfiledRawJointInitialLeftGuardedFirstControllerPackage A
      strategy key activation)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (row : PairedEntryRow) (past : List (In₂ × In₁))
    (input : In₂ × In₁) :
    let child := profiledRawJointGuardedFirstRightTarget A strategy
      activation.source
      (ProfiledRawJointInitialLeftRootPredicate A strategy key)
      activation.pinned row past input
    let bank := activation.childPolicyBank A hwin
    ProfiledRawJointUnitLeftPolicyMacro A strategy child.1 (bank child) :=
  profiledRawJointGuardedFirstRightChildRootMacro A strategy hwin
    activation.source
    (ProfiledRawJointInitialLeftRootPredicate A strategy key)
    activation.pinned package.source package.block row past input

/-- Fully unconditional selection from the original winner and a finite
initial-left key. -/
noncomputable def profiledRawJointInitialLeftGuardedFirstControllerOfWinning
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (key : ProfiledRawJointInitialLeftGuardedKey A strategy) :
    Σ activation : ProfiledRawJointInitialLeftRootPinnedActivation A strategy
        key,
      ProfiledRawJointInitialLeftGuardedFirstControllerPackage A strategy key
        activation :=
  let activation := profiledRawJointInitialLeftRootPinnedActivation A strategy
    hwin key
  ⟨activation,
    profiledRawJointInitialLeftGuardedFirstControllerPackage A strategy key
      activation⟩

end


end DetParityAutomaton

end DistributedSynthesis
