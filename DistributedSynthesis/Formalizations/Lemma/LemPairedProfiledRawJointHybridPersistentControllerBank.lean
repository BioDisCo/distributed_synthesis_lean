/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPersistentRightBlock
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPersistentLeftBlock

/-!
# One finite controller bank inside a persistent hybrid policy

The recurrent indices are the finite live right/left macros of one fixed
hybrid rational policy.  At every macro we choose the installed raw move once
and store the unconditional target-checking controller proved by the
target-parametric block layer.

The emitted target alphabet is the complete state alphabet of that same
hybrid policy.  The monitor projection accepts only a literal opposite live
slot, and its second target test is literally `AllowedTarget` from the source
state.  The edge packages below expose those two facts without changing or
reselecting the policy.  The side index remains proof-side finite data; no
process is given a graph, orientation, or strict-leader signal.
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

/-! ## The exact fixed-policy monitor interfaces -/

/-- Complete finite target alphabet shared by every controller in the bank. -/
abbrev ProfiledRawJointHybridPersistentTarget
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initialCode : ProfiledRawJointHybridCode A) :=
  ProfiledRawJointHybridProvenancePolicyState A strategy initialCode

/-- Receiver certificate type at a persistent right-live macro. -/
abbrev ProfiledRawJointHybridPersistentRightReceiverOutput
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initialCode : ProfiledRawJointHybridCode A) :=
  ProfiledRawJointTargetRightReceiverOutput
    (Out₁ := Out₁) (Out₂ := Out₂)
    (ProfiledRawJointHybridPersistentTarget A strategy initialCode)

/-- Receiver certificate type at a persistent left-live macro. -/
abbrev ProfiledRawJointHybridPersistentLeftReceiverOutput
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initialCode : ProfiledRawJointHybridCode A) :=
  ProfiledRawJointTargetLeftReceiverOutput
    (Out₁ := Out₁) (Out₂ := Out₂)
    (ProfiledRawJointHybridPersistentTarget A strategy initialCode)

/-- The exact monitor installed at a persistent right-live macro. -/
abbrev profiledRawJointHybridPersistentRightBlockMonitor
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initialCode : ProfiledRawJointHybridCode A)
    (policy : ProfiledRawJointHybridProvenanceRationalPolicy A strategy
      initialCode)
    (source : ProfiledRawJointHybridPersistentRightMacro A strategy
      initialCode policy) :=
  profiledRawJointTargetRightBlockMonitor A
    (ProfiledRawJointHybridPersistentTarget A strategy initialCode)
    (profiledRawJointHybridPersistentRightTargetProfiledState A)
    (ProfiledRawJointHybridProvenanceAllowedTarget A strategy initialCode
      policy source.key.state)
    source.slot

/-- Left-live mirror. -/
abbrev profiledRawJointHybridPersistentLeftBlockMonitor
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initialCode : ProfiledRawJointHybridCode A)
    (policy : ProfiledRawJointHybridProvenanceRationalPolicy A strategy
      initialCode)
    (source : ProfiledRawJointHybridPersistentLeftMacro A strategy initialCode
      policy) :=
  profiledRawJointTargetLeftBlockMonitor A
    (ProfiledRawJointHybridPersistentTarget A strategy initialCode)
    (profiledRawJointHybridPersistentLeftTargetProfiledState A)
    (ProfiledRawJointHybridProvenanceAllowedTarget A strategy initialCode
      policy source.key.state)
    source.slot

/-! ## Once-selected installed moves and controllers -/

/-- Select the installed one-sided move once at a reachable live key. -/
noncomputable def profiledRawJointHybridPersistentInstalledMoveAt
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initialCode : ProfiledRawJointHybridCode A)
    (policy : ProfiledRawJointHybridProvenanceRationalPolicy A strategy
      initialCode)
    (key : ProfiledRawJointHybridOneSidedPolicyKey A strategy initialCode
      policy) :
    ProfiledRawJointHybridOneSidedInstalledMove A strategy initialCode policy
      key :=
  Classical.choice
    (nonempty_profiledRawJointHybridOneSidedInstalledMove A strategy
      initialCode policy key)

/-- The finite controller chosen at one persistent right-live macro. -/
noncomputable def profiledRawJointHybridPersistentRightController
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (initialCode : ProfiledRawJointHybridCode A)
    (policy : ProfiledRawJointHybridProvenanceRationalPolicy A strategy
      initialCode)
    (source : ProfiledRawJointHybridPersistentRightMacro A strategy
      initialCode policy) :
    TransitionRationalTree.{u, max u v x y s, max u v x y s} In₁
      (NarrowedBlockLabel In₂ In₁
        (ProfiledRawJointHybridPersistentRightReceiverOutput A strategy
          initialCode)
        Out₁
        (profiledRawJointHybridPersistentRightBlockMonitor A strategy
          initialCode policy source).State) := by
  let installed := profiledRawJointHybridPersistentInstalledMoveAt A strategy
    initialCode policy source.key
  exact Classical.choose
    (exists_profiledRawJointHybridPersistentRightController A hwin installed
      source.slot source.active_slot)

/-- The selected right controller wins the exact same-policy target monitor. -/
theorem profiledRawJointHybridPersistentRightController_wins
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (initialCode : ProfiledRawJointHybridCode A)
    (policy : ProfiledRawJointHybridProvenanceRationalPolicy A strategy
      initialCode)
    (source : ProfiledRawJointHybridPersistentRightMacro A strategy
      initialCode policy) :
    NarrowedAllThreadsWin
      (profiledRawJointHybridPersistentRightBlockMonitor A strategy
        initialCode policy source)
      (profiledRawJointHybridPersistentRightController A strategy hwin
        initialCode policy source).labeledTree := by
  let installed := profiledRawJointHybridPersistentInstalledMoveAt A strategy
    initialCode policy source.key
  exact Classical.choose_spec
    (exists_profiledRawJointHybridPersistentRightController A hwin installed
      source.slot source.active_slot)

/-- The finite controller chosen at one persistent left-live macro. -/
noncomputable def profiledRawJointHybridPersistentLeftController
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (initialCode : ProfiledRawJointHybridCode A)
    (policy : ProfiledRawJointHybridProvenanceRationalPolicy A strategy
      initialCode)
    (source : ProfiledRawJointHybridPersistentLeftMacro A strategy initialCode
      policy) :
    TransitionRationalTree.{v, max u v x y s, max u v y s} In₂
      (NarrowedBlockLabel In₁ In₂
        (ProfiledRawJointHybridPersistentLeftReceiverOutput A strategy
          initialCode)
        Out₂
        (profiledRawJointHybridPersistentLeftBlockMonitor A strategy
          initialCode policy source).State) := by
  let installed := profiledRawJointHybridPersistentInstalledMoveAt A strategy
    initialCode policy source.key
  exact Classical.choose
    (exists_profiledRawJointHybridPersistentLeftController A hwin installed
      source.slot source.active_slot)

/-- The selected left controller wins the exact same-policy target monitor. -/
theorem profiledRawJointHybridPersistentLeftController_wins
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (initialCode : ProfiledRawJointHybridCode A)
    (policy : ProfiledRawJointHybridProvenanceRationalPolicy A strategy
      initialCode)
    (source : ProfiledRawJointHybridPersistentLeftMacro A strategy initialCode
      policy) :
    NarrowedAllThreadsWin
      (profiledRawJointHybridPersistentLeftBlockMonitor A strategy initialCode
        policy source)
      (profiledRawJointHybridPersistentLeftController A strategy hwin
        initialCode policy source).labeledTree := by
  let installed := profiledRawJointHybridPersistentInstalledMoveAt A strategy
    initialCode policy source.key
  exact Classical.choose_spec
    (exists_profiledRawJointHybridPersistentLeftController A hwin installed
      source.slot source.active_slot)

/-! ## The finite controller bank -/

abbrev ProfiledRawJointHybridPersistentRightControllerAt
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initialCode : ProfiledRawJointHybridCode A)
    (policy : ProfiledRawJointHybridProvenanceRationalPolicy A strategy
      initialCode)
    (source : ProfiledRawJointHybridPersistentRightMacro A strategy
      initialCode policy) :=
  { controller :
      TransitionRationalTree.{u, max u v x y s, max u v x y s} In₁
        (NarrowedBlockLabel In₂ In₁
          (ProfiledRawJointHybridPersistentRightReceiverOutput A strategy
            initialCode)
          Out₁
          (profiledRawJointHybridPersistentRightBlockMonitor A strategy
            initialCode policy source).State) //
    NarrowedAllThreadsWin
      (profiledRawJointHybridPersistentRightBlockMonitor A strategy
        initialCode policy source)
      controller.labeledTree }

abbrev ProfiledRawJointHybridPersistentLeftControllerAt
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initialCode : ProfiledRawJointHybridCode A)
    (policy : ProfiledRawJointHybridProvenanceRationalPolicy A strategy
      initialCode)
    (source : ProfiledRawJointHybridPersistentLeftMacro A strategy initialCode
      policy) :=
  { controller :
      TransitionRationalTree.{v, max u v x y s, max u v y s} In₂
        (NarrowedBlockLabel In₁ In₂
          (ProfiledRawJointHybridPersistentLeftReceiverOutput A strategy
            initialCode)
          Out₂
          (profiledRawJointHybridPersistentLeftBlockMonitor A strategy
            initialCode policy source).State) //
    NarrowedAllThreadsWin
      (profiledRawJointHybridPersistentLeftBlockMonitor A strategy initialCode
        policy source)
      controller.labeledTree }

/-- All recurrent controllers indexed by the finite live macros of one fixed
hybrid policy. -/
structure ProfiledRawJointHybridPersistentControllerBank
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initialCode : ProfiledRawJointHybridCode A)
    (policy : ProfiledRawJointHybridProvenanceRationalPolicy A strategy
      initialCode) where
  right : ∀ source, ProfiledRawJointHybridPersistentRightControllerAt A
    strategy initialCode policy source
  left : ∀ source, ProfiledRawJointHybridPersistentLeftControllerAt A
    strategy initialCode policy source

abbrev ProfiledRawJointHybridPersistentControllerBank.rightController
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {initialCode : ProfiledRawJointHybridCode A}
    {policy : ProfiledRawJointHybridProvenanceRationalPolicy A strategy
      initialCode}
    (bank : ProfiledRawJointHybridPersistentControllerBank A strategy
      initialCode policy)
    (source : ProfiledRawJointHybridPersistentRightMacro A strategy
      initialCode policy) :=
  (bank.right source).1

abbrev ProfiledRawJointHybridPersistentControllerBank.leftController
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {initialCode : ProfiledRawJointHybridCode A}
    {policy : ProfiledRawJointHybridProvenanceRationalPolicy A strategy
      initialCode}
    (bank : ProfiledRawJointHybridPersistentControllerBank A strategy
      initialCode policy)
    (source : ProfiledRawJointHybridPersistentLeftMacro A strategy initialCode
      policy) :=
  (bank.left source).1

omit [Inhabited Out₁] [Inhabited Out₂] in
theorem ProfiledRawJointHybridPersistentControllerBank.rightController_wins
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {initialCode : ProfiledRawJointHybridCode A}
    {policy : ProfiledRawJointHybridProvenanceRationalPolicy A strategy
      initialCode}
    (bank : ProfiledRawJointHybridPersistentControllerBank A strategy
      initialCode policy)
    (source : ProfiledRawJointHybridPersistentRightMacro A strategy
      initialCode policy) :
    NarrowedAllThreadsWin
      (profiledRawJointHybridPersistentRightBlockMonitor A strategy
        initialCode policy source)
      ((bank.right source).1).labeledTree :=
  (bank.right source).2

omit [Inhabited Out₁] [Inhabited Out₂] in
theorem ProfiledRawJointHybridPersistentControllerBank.leftController_wins
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {initialCode : ProfiledRawJointHybridCode A}
    {policy : ProfiledRawJointHybridProvenanceRationalPolicy A strategy
      initialCode}
    (bank : ProfiledRawJointHybridPersistentControllerBank A strategy
      initialCode policy)
    (source : ProfiledRawJointHybridPersistentLeftMacro A strategy initialCode
      policy) :
    NarrowedAllThreadsWin
      (profiledRawJointHybridPersistentLeftBlockMonitor A strategy initialCode
        policy source)
      ((bank.left source).1).labeledTree :=
  (bank.left source).2

/-- Assemble the bank from the two unconditional controller theorems. -/
noncomputable def profiledRawJointHybridPersistentControllerBank
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (initialCode : ProfiledRawJointHybridCode A)
    (policy : ProfiledRawJointHybridProvenanceRationalPolicy A strategy
      initialCode) :
    ProfiledRawJointHybridPersistentControllerBank A strategy initialCode
      policy where
  right := fun source ↦
    ⟨profiledRawJointHybridPersistentRightController A strategy hwin
        initialCode policy source,
      profiledRawJointHybridPersistentRightController_wins A strategy hwin
        initialCode policy source⟩
  left := fun source ↦
    ⟨profiledRawJointHybridPersistentLeftController A strategy hwin
        initialCode policy source,
      profiledRawJointHybridPersistentLeftController_wins A strategy hwin
        initialCode policy source⟩

/-! ## Exact same-policy target edges -/

/-- A right close carries the literal target policy state, its tagged
one-sided code and live left slot, and the exact `AllowedTarget` edge from the
source. -/
structure ProfiledRawJointHybridPersistentRightTargetEdge
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initialCode : ProfiledRawJointHybridCode A)
    (policy : ProfiledRawJointHybridProvenanceRationalPolicy A strategy
      initialCode)
    (source : ProfiledRawJointHybridPersistentRightMacro A strategy
      initialCode policy) where
  target : ProfiledRawJointHybridPersistentTarget A strategy initialCode
  code : ProfiledRawJointIncidenceCode A (I := Unit)
  slot : ProfiledRawLeftSlot A
  allowed : ProfiledRawJointHybridProvenanceAllowedTarget A strategy
    initialCode policy source.key.state target
  target_code : target.1 = .oneSided code
  active_slot : code.family.left () = some slot

/-- Left-close mirror. -/
structure ProfiledRawJointHybridPersistentLeftTargetEdge
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initialCode : ProfiledRawJointHybridCode A)
    (policy : ProfiledRawJointHybridProvenanceRationalPolicy A strategy
      initialCode)
    (source : ProfiledRawJointHybridPersistentLeftMacro A strategy initialCode
      policy) where
  target : ProfiledRawJointHybridPersistentTarget A strategy initialCode
  code : ProfiledRawJointIncidenceCode A (I := Unit)
  slot : ProfiledRawRightSlot A
  allowed : ProfiledRawJointHybridProvenanceAllowedTarget A strategy
    initialCode policy source.key.state target
  target_code : target.1 = .oneSided code
  active_slot : code.family.right () = some slot

/-- Stage the exact target state of a right-close edge as a left macro in the
same policy. -/
def ProfiledRawJointHybridPersistentRightTargetEdge.toMacro
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {initialCode : ProfiledRawJointHybridCode A}
    {policy : ProfiledRawJointHybridProvenanceRationalPolicy A strategy
      initialCode}
    {source : ProfiledRawJointHybridPersistentRightMacro A strategy
      initialCode policy}
    (edge : ProfiledRawJointHybridPersistentRightTargetEdge A strategy
      initialCode policy source) :
    ProfiledRawJointHybridPersistentLeftMacro A strategy initialCode policy :=
  profiledRawJointHybridPersistentStageLeftOfAllowed A strategy initialCode
    policy source edge.target edge.code edge.slot edge.allowed edge.target_code
      edge.active_slot

/-- Stage the exact target state of a left-close edge as a right macro. -/
def ProfiledRawJointHybridPersistentLeftTargetEdge.toMacro
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {initialCode : ProfiledRawJointHybridCode A}
    {policy : ProfiledRawJointHybridProvenanceRationalPolicy A strategy
      initialCode}
    {source : ProfiledRawJointHybridPersistentLeftMacro A strategy initialCode
      policy}
    (edge : ProfiledRawJointHybridPersistentLeftTargetEdge A strategy
      initialCode policy source) :
    ProfiledRawJointHybridPersistentRightMacro A strategy initialCode policy :=
  profiledRawJointHybridPersistentStageRightOfAllowed A strategy initialCode
    policy source edge.target edge.code edge.slot edge.allowed edge.target_code
      edge.active_slot

omit [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂] in
@[simp] theorem ProfiledRawJointHybridPersistentRightTargetEdge.toMacro_state
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {initialCode : ProfiledRawJointHybridCode A}
    {policy : ProfiledRawJointHybridProvenanceRationalPolicy A strategy
      initialCode}
    {source : ProfiledRawJointHybridPersistentRightMacro A strategy
      initialCode policy}
    (edge : ProfiledRawJointHybridPersistentRightTargetEdge A strategy
      initialCode policy source) :
    (edge.toMacro A).key.state = edge.target :=
  rfl

omit [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂] in
@[simp] theorem ProfiledRawJointHybridPersistentLeftTargetEdge.toMacro_state
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {initialCode : ProfiledRawJointHybridCode A}
    {policy : ProfiledRawJointHybridProvenanceRationalPolicy A strategy
      initialCode}
    {source : ProfiledRawJointHybridPersistentLeftMacro A strategy initialCode
      policy}
    (edge : ProfiledRawJointHybridPersistentLeftTargetEdge A strategy
      initialCode policy source) :
    (edge.toMacro A).key.state = edge.target :=
  rfl

omit [DecidableEq In₁] [DecidableEq In₂] [Inhabited Out₁] [Inhabited Out₂] in
theorem ProfiledRawJointHybridPersistentRightTargetEdge.target_profiledState
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {initialCode : ProfiledRawJointHybridCode A}
    {policy : ProfiledRawJointHybridProvenanceRationalPolicy A strategy
      initialCode}
    {source : ProfiledRawJointHybridPersistentRightMacro A strategy
      initialCode policy}
    (edge : ProfiledRawJointHybridPersistentRightTargetEdge A strategy
      initialCode policy source) :
    profiledRawJointHybridPersistentRightTargetProfiledState A edge.target =
      .inr (.inr edge.slot) :=
  profiledRawJointHybridPersistentRightTargetProfiledState_eq A edge.target
    edge.code edge.slot edge.target_code edge.active_slot

omit [DecidableEq In₁] [DecidableEq In₂] [Inhabited Out₁] [Inhabited Out₂] in
theorem ProfiledRawJointHybridPersistentLeftTargetEdge.target_profiledState
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {initialCode : ProfiledRawJointHybridCode A}
    {policy : ProfiledRawJointHybridProvenanceRationalPolicy A strategy
      initialCode}
    {source : ProfiledRawJointHybridPersistentLeftMacro A strategy initialCode
      policy}
    (edge : ProfiledRawJointHybridPersistentLeftTargetEdge A strategy
      initialCode policy source) :
    profiledRawJointHybridPersistentLeftTargetProfiledState A edge.target =
      .inr (.inl edge.slot) :=
  profiledRawJointHybridPersistentLeftTargetProfiledState_eq A edge.target
    edge.code edge.slot edge.target_code edge.active_slot

end

end DetParityAutomaton

end DistributedSynthesis
