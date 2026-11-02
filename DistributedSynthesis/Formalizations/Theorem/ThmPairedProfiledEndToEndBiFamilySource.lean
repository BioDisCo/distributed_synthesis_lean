/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledEndToEndRootFamilyOverlay
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledEndToEndOperationalRealInvariant

set_option synthInstance.maxHeartbeats 400000

/-!
# Orientation-free recurrent family sources

After the exceptional block, the recurrent controller stays below one finite
guarded child.  This file makes that child the outer dependent index.  Its
ordinary rational policy is therefore definitionally common to both shadow
orientations; no equality or transport between independently selected
policies is needed.

A bidirectional source stores *both* right-root candidates and *both*
left-root candidates.  It has no constructor selecting the current
orientation and no actual-root member bit.  The only Boolean outside the two
families is the already existing past overlap anchor, which is synchronized
at a receive and is not a current strict-leader signal.
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

open PairedStrategyMemory
open PairedStrategyMemory.PairedInitialProfiledRationalPackage

variable (package : PairedInitialProfiledRationalPackage A)

/-! ## The one historical child-policy index -/

/-- The guarded child selected at the first real close.  Its two constructors
record the historical initial-block origin, not the current orientation. -/
inductive EndToEndCommonChildIndex where
  | fromInitialLeft
      (key : EndToEndInitialLeftBoundaryKey A package)
      (child : EndToEndGuardedRightChild A key.1.2.2.2
        (endToEndInitialLeftBoundaryActivation A package key).profile
        (endToEndInitialLeftBoundaryActivation A package key).policy)
  | fromInitialRight
      (key : EndToEndInitialRightBoundaryKey A package)
      (child : EndToEndGuardedLeftChild A key.1.2.2.2
        (endToEndInitialRightBoundaryActivation A package key).profile
        (endToEndInitialRightBoundaryActivation A package key).policy)

noncomputable instance : Fintype (EndToEndCommonChildIndex A package) := by
  classical
  let LeftRep := Σ key : EndToEndInitialLeftBoundaryKey A package,
    EndToEndGuardedRightChild A key.1.2.2.2
      (endToEndInitialLeftBoundaryActivation A package key).profile
      (endToEndInitialLeftBoundaryActivation A package key).policy
  let RightRep := Σ key : EndToEndInitialRightBoundaryKey A package,
    EndToEndGuardedLeftChild A key.1.2.2.2
      (endToEndInitialRightBoundaryActivation A package key).profile
      (endToEndInitialRightBoundaryActivation A package key).policy
  let Rep := LeftRep ⊕ RightRep
  let e : EndToEndCommonChildIndex A package ≃ Rep :=
    { toFun := fun index =>
        match index with
        | .fromInitialLeft key child => .inl ⟨key, child⟩
        | .fromInitialRight key child => .inr ⟨key, child⟩
      invFun := fun index =>
        match index with
        | .inl ⟨key, child⟩ => .fromInitialLeft key child
        | .inr ⟨key, child⟩ => .fromInitialRight key child
      left_inv := by intro index; cases index <;> rfl
      right_inv := by
        intro index
        cases index with
        | inl value => rcases value with ⟨key, child⟩; rfl
        | inr value => rcases value with ⟨key, child⟩; rfl }
  exact Fintype.ofEquiv Rep e.symm

noncomputable instance : DecidableEq
    (EndToEndCommonChildIndex A package) := Classical.decEq _

namespace EndToEndCommonChildIndex

/-- Initial state of the ordinary policy below the selected child. -/
def state : EndToEndCommonChildIndex A package → PairedProfiledTreeState A
  | .fromInitialLeft _ child => child.1
  | .fromInitialRight _ child => child.1

/-- The one ordinary rational policy below the historical child.  The result
type uses `state index`, so the common-policy equality is definitional. -/
noncomputable def policy (index : EndToEndCommonChildIndex A package) :
    (pairedProfiledEntryRunAutomaton A
      (index.state A package)).RationalTransitionPolicy :=
  match index with
  | .fromInitialLeft _ child => child.policy A
  | .fromInitialRight _ child => child.policy A

omit [Inhabited Out₁] [Inhabited Out₂] [Inhabited In₁] [Inhabited In₂] in
@[simp] theorem state_fromInitialLeft
    (key : EndToEndInitialLeftBoundaryKey A package)
    (child : EndToEndGuardedRightChild A key.1.2.2.2
      (endToEndInitialLeftBoundaryActivation A package key).profile
      (endToEndInitialLeftBoundaryActivation A package key).policy) :
    (EndToEndCommonChildIndex.fromInitialLeft key child).state A package =
      child.1 := rfl

omit [Inhabited Out₁] [Inhabited Out₂] [Inhabited In₁] [Inhabited In₂] in
@[simp] theorem state_fromInitialRight
    (key : EndToEndInitialRightBoundaryKey A package)
    (child : EndToEndGuardedLeftChild A key.1.2.2.2
      (endToEndInitialRightBoundaryActivation A package key).profile
      (endToEndInitialRightBoundaryActivation A package key).policy) :
    (EndToEndCommonChildIndex.fromInitialRight key child).state A package =
      child.1 := rfl

end EndToEndCommonChildIndex

/-! ## Policy-native restarted roots -/

variable (index : EndToEndCommonChildIndex A package)

/-- A recurrent right root and the exact current state of its monitor. -/
abbrev EndToEndPolicyRightRestartRoot :=
  Σ source : ProfiledPolicyRightMacro A (index.policy A package),
    (profiledPolicyRightMonitor A (index.policy A package) source).State

/-- Recurrent left mirror. -/
abbrev EndToEndPolicyLeftRestartRoot :=
  Σ source : ProfiledPolicyLeftMacro A (index.policy A package),
    (profiledPolicyLeftMonitor A (index.policy A package) source).State

noncomputable instance : Fintype
    (EndToEndPolicyRightRestartRoot
      (A := A) (package := package) (index := index)) := by
  classical
  infer_instance

noncomputable instance : Fintype
    (EndToEndPolicyLeftRestartRoot
      (A := A) (package := package) (index := index)) := by
  classical
  infer_instance

noncomputable instance : DecidableEq
    (EndToEndPolicyRightRestartRoot
      (A := A) (package := package) (index := index)) := Classical.decEq _

noncomputable instance : DecidableEq
    (EndToEndPolicyLeftRestartRoot
      (A := A) (package := package) (index := index)) := Classical.decEq _

/-- Restart a right fixed-policy monitor at the exact stored state. -/
noncomputable def endToEndPolicyRightRestartMonitor
    (root : EndToEndPolicyRightRestartRoot
      (A := A) (package := package) (index := index)) :
    BlockRecordMonitor In₂ In₁ (ProfiledRightReceiverOutput A) Out₁ :=
  (profiledPolicyRightMonitor A
    (index.policy A package) root.1).restartAt root.2

/-- Left mirror. -/
noncomputable def endToEndPolicyLeftRestartMonitor
    (root : EndToEndPolicyLeftRestartRoot
      (A := A) (package := package) (index := index)) :
    BlockRecordMonitor In₁ In₂ (ProfiledLeftReceiverOutput A) Out₂ :=
  (profiledPolicyLeftMonitor A
    (index.policy A package) root.1).restartAt root.2

/-! ## One orientation-free bidirectional source -/

/-- Both shadow families below one common child policy.  No field selects a
right or left family member as the actual root. -/
structure EndToEndRecurrentBiFamilySource where
  commonChild : EndToEndCommonChildIndex A package
  pastAnchor : Bool
  rightRoots : Bool →
    EndToEndPolicyRightRestartRoot
      (A := A) (package := package) (index := commonChild)
  leftRoots : Bool →
    EndToEndPolicyLeftRestartRoot
      (A := A) (package := package) (index := commonChild)

noncomputable instance : Fintype
    (EndToEndRecurrentBiFamilySource A package) := by
  classical
  let Rep := Σ commonChild : EndToEndCommonChildIndex A package,
    Bool ×
      (Bool → EndToEndPolicyRightRestartRoot
        (A := A) (package := package) (index := commonChild)) ×
      (Bool → EndToEndPolicyLeftRestartRoot
        (A := A) (package := package) (index := commonChild))
  let e : EndToEndRecurrentBiFamilySource A package ≃ Rep :=
    { toFun := fun source =>
        ⟨source.commonChild, source.pastAnchor, source.rightRoots,
          source.leftRoots⟩
      invFun := fun source =>
        ⟨source.1, source.2.1, source.2.2.1, source.2.2.2⟩
      left_inv := by intro source; cases source; rfl
      right_inv := by
        intro source
        rcases source with ⟨commonChild, anchor, rightRoots, leftRoots⟩
        rfl }
  exact Fintype.ofEquiv Rep e.symm

noncomputable instance : DecidableEq
    (EndToEndRecurrentBiFamilySource A package) := Classical.decEq _

/-! ## Simultaneous move alphabet for both orientations -/

/-- Right family monitors of one orientation-free source. -/
noncomputable abbrev endToEndBiFamilyRightMonitors
    (source : EndToEndRecurrentBiFamilySource A package) :=
  fun member => endToEndPolicyRightRestartMonitor A package
    source.commonChild (source.rightRoots member)

/-- Left family monitors of the same source. -/
noncomputable abbrev endToEndBiFamilyLeftMonitors
    (source : EndToEndRecurrentBiFamilySource A package) :=
  fun member => endToEndPolicyLeftRestartMonitor A package
    source.commonChild (source.leftRoots member)

noncomputable abbrev EndToEndBiFamilyRightTable
    (source : EndToEndRecurrentBiFamilySource A package) :=
  FiniteRootFamilyTable (endToEndBiFamilyRightMonitors A package source)

noncomputable abbrev EndToEndBiFamilyLeftTable
    (source : EndToEndRecurrentBiFamilySource A package) :=
  FiniteRootFamilyTable (endToEndBiFamilyLeftMonitors A package source)

private noncomputable abbrev endToEndBiFamilyRightTableFintype
    (source : EndToEndRecurrentBiFamilySource A package) :
    Fintype (EndToEndBiFamilyRightTable A package source) := by
  classical
  infer_instance

private noncomputable abbrev endToEndBiFamilyLeftTableFintype
    (source : EndToEndRecurrentBiFamilySource A package) :
    Fintype (EndToEndBiFamilyLeftTable A package source) := by
  classical
  infer_instance

/-- One public move contains both family tables.  It does not select which
orientation or which member is actual. -/
abbrev EndToEndRecurrentBiFamilyMove :=
  Σ source : EndToEndRecurrentBiFamilySource A package,
    EndToEndBiFamilyRightTable A package source ×
      EndToEndBiFamilyLeftTable A package source

noncomputable instance : Fintype
    (EndToEndRecurrentBiFamilyMove A package) := by
  classical
  letI (source : EndToEndRecurrentBiFamilySource A package) :
      Fintype (EndToEndBiFamilyRightTable A package source) :=
    endToEndBiFamilyRightTableFintype A package source
  letI (source : EndToEndRecurrentBiFamilySource A package) :
      Fintype (EndToEndBiFamilyLeftTable A package source) :=
    endToEndBiFamilyLeftTableFintype A package source
  infer_instance

/-- Both simultaneous tables carry their universal member certificates. -/
def EndToEndRecurrentBiFamilyMove.Wins
    (move : EndToEndRecurrentBiFamilyMove A package) : Prop :=
  NarrowedAllThreadsWin
      (finiteRootFamilyMonitor
        (endToEndBiFamilyRightMonitors A package move.1))
      move.2.1.toTransitionRationalTree.labeledTree ∧
    NarrowedAllThreadsWin
      (finiteRootFamilyMonitor
        (endToEndBiFamilyLeftMonitors A package move.1))
      move.2.2.toTransitionRationalTree.labeledTree

/-- Current-source validity for an outer observable move.  Successor
completeness is deliberately a later model law: it must reconstruct the next
bidirectional source from the two actual receiver exits. -/
def EndToEndRecurrentBiFamilyMove.ValidAt
    (source : EndToEndRecurrentBiFamilySource A package)
    (move : EndToEndRecurrentBiFamilyMove A package) : Prop :=
  move.1 = source ∧ move.Wins A package

noncomputable instance : DecidableRel
    (EndToEndRecurrentBiFamilyMove.ValidAt A package) :=
  fun _ _ => Classical.propDecidable _

/-! ## Existing recurrent macros enter the common-child presentation -/

def commonChildOfRightOriginRight
    (source : EndToEndRightOriginRecurrentRightMacro A package) :
    EndToEndCommonChildIndex A package :=
  .fromInitialLeft source.1 source.2.1

def commonChildOfRightOriginLeft
    (source : EndToEndRightOriginRecurrentLeftMacro A package) :
    EndToEndCommonChildIndex A package :=
  .fromInitialLeft source.1 source.2.1

def commonChildOfLeftOriginRight
    (source : EndToEndLeftOriginRecurrentRightMacro A package) :
    EndToEndCommonChildIndex A package :=
  .fromInitialRight source.1 source.2.1

def commonChildOfLeftOriginLeft
    (source : EndToEndLeftOriginRecurrentLeftMacro A package) :
    EndToEndCommonChildIndex A package :=
  .fromInitialRight source.1 source.2.1

/-- The current monitor state of a right-origin/right phase becomes a
policy-native restarted root without transport. -/
def policyRightRestartRootOfRightOrigin
    (source : EndToEndRightOriginRecurrentRightMacro A package)
    (state : (endToEndGuardedRightRecurrentRightMonitor A source.2).State) :
    EndToEndPolicyRightRestartRoot A package
      (commonChildOfRightOriginRight A package source) :=
  ⟨source.2.2, state⟩

def policyLeftRestartRootOfRightOrigin
    (source : EndToEndRightOriginRecurrentLeftMacro A package)
    (state : (endToEndGuardedRightRecurrentLeftMonitor A source.2).State) :
    EndToEndPolicyLeftRestartRoot A package
      (commonChildOfRightOriginLeft A package source) :=
  ⟨source.2.2, state⟩

def policyRightRestartRootOfLeftOrigin
    (source : EndToEndLeftOriginRecurrentRightMacro A package)
    (state : (endToEndGuardedLeftRecurrentRightMonitor A source.2).State) :
    EndToEndPolicyRightRestartRoot A package
      (commonChildOfLeftOriginRight A package source) :=
  ⟨source.2.2, state⟩

def policyLeftRestartRootOfLeftOrigin
    (source : EndToEndLeftOriginRecurrentLeftMacro A package)
    (state : (endToEndGuardedLeftRecurrentLeftMonitor A source.2).State) :
    EndToEndPolicyLeftRestartRoot A package
      (commonChildOfLeftOriginLeft A package source) :=
  ⟨source.2.2, state⟩

/-! The two exceptional phase cases already carry a pending recurrent macro,
but `IsRealEndToEndPhase` currently stores it as an unconstrained `some`.
Constructing the first `EndToEndRecurrentBiFamilySource` therefore needs the
stronger initial-root equation proved at the concrete close.  The recurrent
four cases above are definitionally embedded; assembling their two current
roots with the two opposite staged roots is the remaining carrier invariant. -/

end

end DetParityAutomaton

end DistributedSynthesis
