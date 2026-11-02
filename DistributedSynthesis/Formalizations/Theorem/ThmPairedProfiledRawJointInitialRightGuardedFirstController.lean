/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointInitialRootPinnedActivation
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledRawJointGuardedFirstLeftBlockMonitor
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledRawJointGuardedFirstPolicyRootHandoff

/-!
# Initial-right key to the exceptional left controller

This is the concrete adapter between the finite guarded initial key and the
generic root-pinned left-block monitor.  The key proves that the selected
incidence code is left-live.  Its one-shot root predicate proves that the
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

/-- Complete exceptional left-controller package at one initial-right key. -/
structure ProfiledRawJointInitialRightGuardedFirstControllerPackage
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (key : ProfiledRawJointInitialRightGuardedKey A strategy)
    (activation : ProfiledRawJointInitialRightRootPinnedActivation A strategy
      key) where
  source : ProfiledRawLeftSlot A
  source_active : (activation.source.code A).family.left () = some source
  block : ProfiledRawJointGuardedFirstLeftBlockActivation A strategy
    activation.source
    (ProfiledRawJointInitialRightRootPredicate A strategy key)
    activation.pinned source
  overlap_matches : key.1.2.Matches block.lambda

omit [DecidableEq In₁] [DecidableEq In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- The key-specific root-pinned activation supplies the complete exceptional
left controller without an additional hypothesis. -/
theorem nonempty_profiledRawJointInitialRightGuardedFirstControllerPackage
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (key : ProfiledRawJointInitialRightGuardedKey A strategy)
    (activation : ProfiledRawJointInitialRightRootPinnedActivation A strategy
      key) :
    Nonempty (ProfiledRawJointInitialRightGuardedFirstControllerPackage A
      strategy key activation) := by
  rcases profiledRawJointInitialRightGuardedKey_left_live A strategy key with
    ⟨source, hkeySource, _hrightEmpty⟩
  have hsource : (activation.source.code A).family.left () = some source := by
    rw [activation.source_code]
    exact hkeySource
  let block := Classical.choice
    (nonempty_profiledRawJointGuardedFirstLeftBlockActivation A strategy
      activation.source
      (ProfiledRawJointInitialRightRootPredicate A strategy key)
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
noncomputable def profiledRawJointInitialRightGuardedFirstControllerPackage
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (key : ProfiledRawJointInitialRightGuardedKey A strategy)
    (activation : ProfiledRawJointInitialRightRootPinnedActivation A strategy
      key) :
    ProfiledRawJointInitialRightGuardedFirstControllerPackage A strategy key
      activation :=
  Classical.choice
    (nonempty_profiledRawJointInitialRightGuardedFirstControllerPackage A
      strategy key activation)

/-- Unconditional finite narrowing of the exceptional block stored in the
key package.  Keeping the controller existential outside the dependent
package avoids adding any runtime datum; callers choose it once for the
finite key bank. -/
theorem
    ProfiledRawJointInitialRightGuardedFirstControllerPackage.existsController
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {key : ProfiledRawJointInitialRightGuardedKey A strategy}
    {activation : ProfiledRawJointInitialRightRootPinnedActivation A strategy
      key}
    (package : ProfiledRawJointInitialRightGuardedFirstControllerPackage A
      strategy key activation) :
    ∃ controller :
        TransitionRationalTree.{v, max u v x y s, max u v x y s} In₂
        (NarrowedBlockLabel In₁ In₂
          (ProfiledRawJointGuardedFirstLeftReceiverOutput A strategy
            activation.source
            (ProfiledRawJointInitialRightRootPredicate A strategy key)
            activation.pinned) Out₂
          (profiledRawJointGuardedFirstLeftBlockMonitor A strategy
            activation.source
            (ProfiledRawJointInitialRightRootPredicate A strategy key)
            activation.pinned package.source).State),
      NarrowedAllThreadsWin
        (profiledRawJointGuardedFirstLeftBlockMonitor A strategy
          activation.source
          (ProfiledRawJointInitialRightRootPredicate A strategy key)
          activation.pinned package.source) controller.labeledTree :=
  exists_profiledRawJointGuardedFirstLeftController A package.source
    package.block

/-! ## Literal-child readback and ordinary-policy handoff -/

/-- Every target emitted by the exceptional controller has exactly the
finite type indexing the ordinary child-policy bank. -/
noncomputable def
    ProfiledRawJointInitialRightGuardedFirstControllerPackage.childPolicyFor
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {key : ProfiledRawJointInitialRightGuardedKey A strategy}
    {activation : ProfiledRawJointInitialRightRootPinnedActivation A strategy
      key}
    (package : ProfiledRawJointInitialRightGuardedFirstControllerPackage A
      strategy key activation)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (child : ProfiledRawJointOneSidedLiteralChildCode A strategy
      (profiledRawJointRootPinnedSelectedSource A strategy activation.source
        (ProfiledRawJointInitialRightRootPredicate A strategy key)
        activation.pinned)) :
    ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy child.1 :=
  activation.childPolicyBank A hwin child

/-- Read the child key out of one controller label and hand it directly to
the fresh ordinary bank. -/
noncomputable def
    ProfiledRawJointInitialRightGuardedFirstControllerPackage.childPolicyForOutput
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {key : ProfiledRawJointInitialRightGuardedKey A strategy}
    {activation : ProfiledRawJointInitialRightRootPinnedActivation A strategy
      key}
    (package : ProfiledRawJointInitialRightGuardedFirstControllerPackage A
      strategy key activation)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (output : ProfiledRawJointGuardedFirstLeftReceiverOutput A strategy
      activation.source
      (ProfiledRawJointInitialRightRootPredicate A strategy key)
      activation.pinned)
    (row : PairedEntryRow) :
    ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (output.target row).1 :=
  package.childPolicyFor A hwin (output.target row)

/-- At the semantic realizing receiver, the preceding handoff policy is
rooted at the exact raw child of the concrete physical row/past/input. -/
noncomputable def
    ProfiledRawJointInitialRightGuardedFirstControllerPackage.exactChildPolicy
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {key : ProfiledRawJointInitialRightGuardedKey A strategy}
    {activation : ProfiledRawJointInitialRightRootPinnedActivation A strategy
      key}
    (package : ProfiledRawJointInitialRightGuardedFirstControllerPackage A
      strategy key activation)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (row : PairedEntryRow) (past : List (In₁ × In₂))
    (input : In₁ × In₂) :
    ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (profiledRawJointGuardedFirstLeftTarget A strategy activation.source
        (ProfiledRawJointInitialRightRootPredicate A strategy key)
        activation.pinned row past input).1 :=
  package.childPolicyFor A hwin
    (profiledRawJointGuardedFirstLeftTarget A strategy activation.source
      (ProfiledRawJointInitialRightRootPredicate A strategy key)
      activation.pinned row past input)

/-- Strong operational handoff: the exact child is packaged as the reachable
right-policy root macro consumed by the alternating controller.  Its state is
definitionally the selected ordinary policy's `run []`. -/
noncomputable def
    ProfiledRawJointInitialRightGuardedFirstControllerPackage.exactChildRootMacro
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {key : ProfiledRawJointInitialRightGuardedKey A strategy}
    {activation : ProfiledRawJointInitialRightRootPinnedActivation A strategy
      key}
    (package : ProfiledRawJointInitialRightGuardedFirstControllerPackage A
      strategy key activation)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (row : PairedEntryRow) (past : List (In₁ × In₂))
    (input : In₁ × In₂) :
    let child := profiledRawJointGuardedFirstLeftTarget A strategy
      activation.source
      (ProfiledRawJointInitialRightRootPredicate A strategy key)
      activation.pinned row past input
    let bank := activation.childPolicyBank A hwin
    ProfiledRawJointUnitRightPolicyMacro A strategy child.1 (bank child) :=
  profiledRawJointGuardedFirstLeftChildRootMacro A strategy hwin
    activation.source
    (ProfiledRawJointInitialRightRootPredicate A strategy key)
    activation.pinned package.source package.block row past input

/-- Fully unconditional selection from the original winner and a finite
initial-right key. -/
noncomputable def profiledRawJointInitialRightGuardedFirstControllerOfWinning
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (key : ProfiledRawJointInitialRightGuardedKey A strategy) :
    Σ activation : ProfiledRawJointInitialRightRootPinnedActivation A strategy
        key,
      ProfiledRawJointInitialRightGuardedFirstControllerPackage A strategy key
        activation :=
  let activation := profiledRawJointInitialRightRootPinnedActivation A strategy
    hwin key
  ⟨activation,
    profiledRawJointInitialRightGuardedFirstControllerPackage A strategy key
      activation⟩

end


end DetParityAutomaton

end DistributedSynthesis
