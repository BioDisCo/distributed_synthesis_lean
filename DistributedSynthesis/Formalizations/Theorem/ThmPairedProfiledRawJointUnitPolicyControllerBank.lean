/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledRawJointUnitLeftPolicyHandoff

/-!
# One finite raw-joint controller bank under the fixed policy

Every reachable finite policy state installs one raw joint move.  When its
`Unit` code has an active right or left slot, the corresponding unconditional
block theorem narrows that component of the installed move to a finite
controller.  This file makes those choices once and packages all controllers
under the one fixed rational policy.

The runtime bank keys are the finite policy macros from the handoff layer.
The installed semantic source, raw move, proof-tree side, and narrowing
witness are proof-side choices.  In particular, selecting a controller from
this bank requires no graph, orientation, or strict-leader input.
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

/-! ## The once-selected installed move -/

/-- Proof-side package selecting a raw joint move at one reachable state. -/
structure ProfiledRawJointUnitInstalledMoveAt
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initialCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      initialCode)
    (state : ProfiledRawJointOneSidedProvenancePolicyState A strategy
      initialCode) where
  move : ProfiledRawJointLambdaFamilyMove A (I := Unit)
  realizes : ProfiledRawJointOneSidedProvenanceMoveRealizesAt A strategy
    initialCode policy state move

omit [DecidableEq In₁] [DecidableEq In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Every reachable policy state has an installed move package. -/
theorem nonempty_profiledRawJointUnitInstalledMoveAt
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initialCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      initialCode)
    (state : ProfiledRawJointOneSidedProvenancePolicyState A strategy
      initialCode)
    (hreachable : ProfiledRawJointUnitPolicyReachable A strategy initialCode
      policy state) :
    Nonempty (ProfiledRawJointUnitInstalledMoveAt A strategy initialCode
      policy state) := by
  obtain ⟨move, _semantic, hmove, _hcode, _hsemanticMove⟩ :=
    exists_profiledRawJointOneSidedProvenanceInstalledMove A strategy
      initialCode policy state hreachable
  exact ⟨⟨move, hmove⟩⟩

/-- The move selected once for a reachable policy state. -/
noncomputable def profiledRawJointUnitInstalledMoveAt
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initialCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      initialCode)
    (state : ProfiledRawJointOneSidedProvenancePolicyState A strategy
      initialCode)
    (hreachable : ProfiledRawJointUnitPolicyReachable A strategy initialCode
      policy state) :
    ProfiledRawJointUnitInstalledMoveAt A strategy initialCode policy state :=
  Classical.choice
    (nonempty_profiledRawJointUnitInstalledMoveAt A strategy initialCode
      policy state hreachable)

/-! ## Policy-indexed right and left controllers -/

/-- The finite right controller chosen for one reachable right macro. -/
noncomputable def profiledRawJointUnitRightPolicyController
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (initial.code A))
    (source : ProfiledRawJointUnitRightPolicyMacro A strategy
      (initial.code A) policy) :
    TransitionRationalTree.{u, max u v x y s, max u v x y s} In₁
      (NarrowedBlockLabel In₂ In₁
        (ProfiledRawJointUnitRightReceiverOutput A strategy (initial.code A))
        Out₁
        (profiledRawJointUnitRightBlockMonitor.{u, v, x, y, s,
            max u v x y s} A strategy
          (initial.code A) policy source.state source.slot).State) := by
  let installed := profiledRawJointUnitInstalledMoveAt A strategy
    (initial.code A) policy source.state source.reachable
  exact Classical.choose
    (exists_profiledRawJointUnitRightController A strategy initial policy
      source.state source.reachable installed.move installed.realizes
      source.slot source.active_slot)

/-- The chosen right controller wins its complete target-checking monitor. -/
theorem profiledRawJointUnitRightPolicyController_wins
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (initial.code A))
    (source : ProfiledRawJointUnitRightPolicyMacro A strategy
      (initial.code A) policy) :
    NarrowedAllThreadsWin
      (profiledRawJointUnitRightBlockMonitor.{u, v, x, y, s,
          max u v x y s} A strategy
        (initial.code A) policy source.state source.slot)
      (profiledRawJointUnitRightPolicyController A strategy initial policy
        source).labeledTree := by
  let installed := profiledRawJointUnitInstalledMoveAt A strategy
    (initial.code A) policy source.state source.reachable
  exact Classical.choose_spec
    (exists_profiledRawJointUnitRightController A strategy initial policy
      source.state source.reachable installed.move installed.realizes
      source.slot source.active_slot)

/-- The finite left controller chosen for one reachable left macro. -/
noncomputable def profiledRawJointUnitLeftPolicyController
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (initial.code A))
    (source : ProfiledRawJointUnitLeftPolicyMacro A strategy
      (initial.code A) policy) :
    TransitionRationalTree.{v, max u v x y s, max u v x y s} In₂
      (NarrowedBlockLabel In₁ In₂
        (ProfiledRawJointUnitLeftReceiverOutput A strategy (initial.code A))
        Out₂
        (profiledRawJointUnitLeftBlockMonitor.{u, v, x, y, s,
            max u v x y s} A strategy
          (initial.code A) policy source.state source.slot).State) := by
  let installed := profiledRawJointUnitInstalledMoveAt A strategy
    (initial.code A) policy source.state source.reachable
  exact Classical.choose
    (exists_profiledRawJointUnitLeftController A strategy initial policy
      source.state source.reachable installed.move installed.realizes
      source.slot source.active_slot)

/-- The chosen left controller wins its complete target-checking monitor. -/
theorem profiledRawJointUnitLeftPolicyController_wins
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (initial.code A))
    (source : ProfiledRawJointUnitLeftPolicyMacro A strategy
      (initial.code A) policy) :
    NarrowedAllThreadsWin
      (profiledRawJointUnitLeftBlockMonitor.{u, v, x, y, s,
          max u v x y s} A strategy
        (initial.code A) policy source.state source.slot)
      (profiledRawJointUnitLeftPolicyController A strategy initial policy
        source).labeledTree := by
  let installed := profiledRawJointUnitInstalledMoveAt A strategy
    (initial.code A) policy source.state source.reachable
  exact Classical.choose_spec
    (exists_profiledRawJointUnitLeftController A strategy initial policy
      source.state source.reachable installed.move installed.realizes
      source.slot source.active_slot)

/-! ## One finite controller bank -/

/-- A controller and its winning proof at one reachable right macro.  Keeping
the proof next to the controller avoids a large dependent equality when all
macros are collected into one bank. -/
abbrev ProfiledRawJointUnitRightPolicyControllerAt
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (initial.code A))
    (source : ProfiledRawJointUnitRightPolicyMacro A strategy
      (initial.code A) policy) :=
  { controller :
      TransitionRationalTree.{u, max u v x y s, max u v x y s} In₁
        (NarrowedBlockLabel In₂ In₁
          (ProfiledRawJointUnitRightReceiverOutput A strategy
            (initial.code A))
          Out₁
          (profiledRawJointUnitRightBlockMonitor.{u, v, x, y, s,
              max u v x y s} A strategy (initial.code A) policy source.state
            source.slot).State) //
    NarrowedAllThreadsWin
      (profiledRawJointUnitRightBlockMonitor.{u, v, x, y, s,
          max u v x y s} A strategy (initial.code A) policy source.state
        source.slot)
      controller.labeledTree }

/-- A controller and its winning proof at one reachable left macro. -/
abbrev ProfiledRawJointUnitLeftPolicyControllerAt
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (initial.code A))
    (source : ProfiledRawJointUnitLeftPolicyMacro A strategy
      (initial.code A) policy) :=
  { controller :
      TransitionRationalTree.{v, max u v x y s, max u v x y s} In₂
        (NarrowedBlockLabel In₁ In₂
          (ProfiledRawJointUnitLeftReceiverOutput A strategy
            (initial.code A))
          Out₂
          (profiledRawJointUnitLeftBlockMonitor.{u, v, x, y, s,
              max u v x y s} A strategy (initial.code A) policy source.state
            source.slot).State) //
    NarrowedAllThreadsWin
      (profiledRawJointUnitLeftBlockMonitor.{u, v, x, y, s,
          max u v x y s} A strategy (initial.code A) policy source.state
        source.slot)
      controller.labeledTree }

/-- All recurrent right and left controllers below one fixed raw-joint
policy.  The index types are finite and contain no observable orientation
bit. -/
structure ProfiledRawJointUnitPolicyControllerBank
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (initial.code A)) where
  right : ∀ source, ProfiledRawJointUnitRightPolicyControllerAt A strategy
    initial policy source
  left : ∀ source, ProfiledRawJointUnitLeftPolicyControllerAt A strategy
    initial policy source

/-- Read the controller stored at a right macro. -/
abbrev ProfiledRawJointUnitPolicyControllerBank.rightController
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit)}
    {policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (initial.code A)}
    (bank : ProfiledRawJointUnitPolicyControllerBank A strategy initial policy)
    (source : ProfiledRawJointUnitRightPolicyMacro A strategy
      (initial.code A) policy) :=
  (bank.right source).1

/-- Read the controller stored at a left macro. -/
abbrev ProfiledRawJointUnitPolicyControllerBank.leftController
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit)}
    {policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (initial.code A)}
    (bank : ProfiledRawJointUnitPolicyControllerBank A strategy initial policy)
    (source : ProfiledRawJointUnitLeftPolicyMacro A strategy
      (initial.code A) policy) :=
  (bank.left source).1

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- The right controller read from the bank retains its winning proof. -/
theorem ProfiledRawJointUnitPolicyControllerBank.rightController_wins
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit)}
    {policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (initial.code A)}
    (bank : ProfiledRawJointUnitPolicyControllerBank A strategy initial policy)
    (source : ProfiledRawJointUnitRightPolicyMacro A strategy
      (initial.code A) policy) :
    NarrowedAllThreadsWin
      (profiledRawJointUnitRightBlockMonitor.{u, v, x, y, s,
          max u v x y s} A strategy (initial.code A) policy source.state
        source.slot)
      ((bank.right source).1).labeledTree :=
  (bank.right source).2

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- The left controller read from the bank retains its winning proof. -/
theorem ProfiledRawJointUnitPolicyControllerBank.leftController_wins
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit)}
    {policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (initial.code A)}
    (bank : ProfiledRawJointUnitPolicyControllerBank A strategy initial policy)
    (source : ProfiledRawJointUnitLeftPolicyMacro A strategy
      (initial.code A) policy) :
    NarrowedAllThreadsWin
      (profiledRawJointUnitLeftBlockMonitor.{u, v, x, y, s,
          max u v x y s} A strategy (initial.code A) policy source.state
        source.slot)
      ((bank.left source).1).labeledTree :=
  (bank.left source).2

/-- The unconditional bank assembled from the once-selected controllers. -/
noncomputable def profiledRawJointUnitPolicyControllerBank
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (initial.code A)) :
    ProfiledRawJointUnitPolicyControllerBank A strategy initial policy where
  right := fun source ↦
    ⟨profiledRawJointUnitRightPolicyController A strategy initial policy source,
      profiledRawJointUnitRightPolicyController_wins A strategy initial policy
        source⟩
  left := fun source ↦
    ⟨profiledRawJointUnitLeftPolicyController A strategy initial policy source,
      profiledRawJointUnitLeftPolicyController_wins A strategy initial policy
        source⟩

end

end DetParityAutomaton

end DistributedSynthesis
