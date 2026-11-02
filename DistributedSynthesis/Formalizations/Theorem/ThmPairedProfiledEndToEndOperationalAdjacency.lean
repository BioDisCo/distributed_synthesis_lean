/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledEndToEndBiFamilySource
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledEndToEndOperationalRealClosure

set_option maxHeartbeats 800000

/-!
# Exact pending adjacency of the six end-to-end phases

`IsRealEndToEndPhase` remembers the concrete prefix and its staged target, but
in the four recurrent cases its type does not say that the target is below the
same guarded child as the current source.  That equality is essential when a
simultaneous family is handed from one orientation to the other.

`IsAdjacentRealEndToEndPhase` is the reachable-state strengthening.  In every
recurrent constructor the current and staged macros are written with one
literal boundary key and one literal guarded child.  Thus their common policy
is definitional, rather than an equality transported between dependent
packages.  The two exceptional constructors retain the exact staged child
from which recurrence starts.

The closure proofs below use the `*_real_close_allowed` lemmas, not merely
`isSome`: those lemmas are exactly what prevents a close from changing child.
No field is runtime data and no orientation or leader bit is added to either
local controller.
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

/-- Concrete-prefix reality strengthened by literal source--pending adjacency.
The six disjuncts are the six phase constructors. -/
def IsAdjacentRealEndToEndPhase
    (phase : EndToEndMatchedPhase A package) : Prop :=
  (exists (key : EndToEndInitialLeftBoundaryKey A package)
      (row : PairedEntryRow) (past : List (In₂ × In₁))
      (target : EndToEndGuardedRightRecurrentLeftMacro A
        (rightGuarded :=
          (endToEndInitialLeftBoundaryActivation A package key).policy)),
    IsRealEndToEndFirstRightPhaseAt A package key row past target phase) ∨
  (exists (key : EndToEndInitialRightBoundaryKey A package)
      (row : PairedEntryRow) (past : List (In₁ × In₂))
      (target : EndToEndGuardedLeftRecurrentRightMacro A
        (leftGuarded :=
          (endToEndInitialRightBoundaryActivation A package key).policy)),
    IsRealEndToEndFirstLeftPhaseAt A package key row past target phase) ∨
  (exists (key : EndToEndInitialLeftBoundaryKey A package)
      (child : EndToEndGuardedRightChild A key.1.2.2.2
        (endToEndInitialLeftBoundaryActivation A package key).profile
        (endToEndInitialLeftBoundaryActivation A package key).policy)
      (source : ProfiledPolicyRightMacro A (child.policy A))
      (row : PairedEntryRow) (past : List (In₂ × In₁))
      (target : ProfiledPolicyLeftMacro A (child.policy A)),
    IsRealEndToEndRightOriginRightPhaseAt A package
      ⟨key, child, source⟩ row past ⟨key, child, target⟩ phase) ∨
  (exists (key : EndToEndInitialLeftBoundaryKey A package)
      (child : EndToEndGuardedRightChild A key.1.2.2.2
        (endToEndInitialLeftBoundaryActivation A package key).profile
        (endToEndInitialLeftBoundaryActivation A package key).policy)
      (source : ProfiledPolicyLeftMacro A (child.policy A))
      (row : PairedEntryRow) (past : List (In₁ × In₂))
      (target : ProfiledPolicyRightMacro A (child.policy A)),
    IsRealEndToEndRightOriginLeftPhaseAt A package
      ⟨key, child, source⟩ row past ⟨key, child, target⟩ phase) ∨
  (exists (key : EndToEndInitialRightBoundaryKey A package)
      (child : EndToEndGuardedLeftChild A key.1.2.2.2
        (endToEndInitialRightBoundaryActivation A package key).profile
        (endToEndInitialRightBoundaryActivation A package key).policy)
      (source : ProfiledPolicyRightMacro A (child.policy A))
      (row : PairedEntryRow) (past : List (In₂ × In₁))
      (target : ProfiledPolicyLeftMacro A (child.policy A)),
    IsRealEndToEndLeftOriginRightPhaseAt A package
      ⟨key, child, source⟩ row past ⟨key, child, target⟩ phase) ∨
  (exists (key : EndToEndInitialRightBoundaryKey A package)
      (child : EndToEndGuardedLeftChild A key.1.2.2.2
        (endToEndInitialRightBoundaryActivation A package key).profile
        (endToEndInitialRightBoundaryActivation A package key).policy)
      (source : ProfiledPolicyLeftMacro A (child.policy A))
      (row : PairedEntryRow) (past : List (In₁ × In₂))
      (target : ProfiledPolicyRightMacro A (child.policy A)),
    IsRealEndToEndLeftOriginLeftPhaseAt A package
      ⟨key, child, source⟩ row past ⟨key, child, target⟩ phase)

/-- Forgetting adjacency recovers the old componentwise reality predicate. -/
theorem isRealEndToEndPhase_of_adjacent
    (phase : EndToEndMatchedPhase A package)
    (hphase : IsAdjacentRealEndToEndPhase A package phase) :
    IsRealEndToEndPhase A package phase := by
  rcases hphase with hfirstRight | hfirstLeft | hrightRight | hrightLeft |
      hleftRight | hleftLeft
  · rcases hfirstRight with ⟨key, row, past, target, hphase⟩
    exact Or.inl ⟨key, row, past, target, hphase⟩
  · rcases hfirstLeft with ⟨key, row, past, target, hphase⟩
    exact Or.inr (Or.inl ⟨key, row, past, target, hphase⟩)
  · rcases hrightRight with ⟨key, child, source, row, past, target, hphase⟩
    exact Or.inr (Or.inr (Or.inl
      ⟨⟨key, child, source⟩, row, past, ⟨key, child, target⟩, hphase⟩))
  · rcases hrightLeft with ⟨key, child, source, row, past, target, hphase⟩
    exact Or.inr (Or.inr (Or.inr (Or.inl
      ⟨⟨key, child, source⟩, row, past, ⟨key, child, target⟩, hphase⟩)))
  · rcases hleftRight with ⟨key, child, source, row, past, target, hphase⟩
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨⟨key, child, source⟩, row, past, ⟨key, child, target⟩, hphase⟩))))
  · rcases hleftLeft with ⟨key, child, source, row, past, target, hphase⟩
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨⟨key, child, source⟩, row, past, ⟨key, child, target⟩, hphase⟩))))

/-! ## Closure under an ordinary round -/

/-- An ordinary round preserves the literal source--pending child.  The
recurrent cases deliberately use the `allowed` close theorem, whose returned
target is typed at the current child's policy. -/
theorem isAdjacentRealEndToEndPhase_continue
    (phase : EndToEndMatchedPhase A package)
    (hphase : IsAdjacentRealEndToEndPhase A package phase)
    (move : In₁ × In₂) :
    IsAdjacentRealEndToEndPhase A package
      (phase.continue A package move).2 := by
  rcases hphase with hfirstRight | hfirstLeft | hrightRight | hrightLeft |
      hleftRight | hleftLeft
  · rcases hfirstRight with ⟨key, row, past, pending, rfl⟩
    have hsome := endToEndFirstRight_real_close_staged A package key row past
      (move.2, move.1)
    rw [Option.isSome_iff_exists] at hsome
    rcases hsome with ⟨target, hstaged⟩
    left
    refine ⟨key, row, past ++ [(move.2, move.1)], target, ?_⟩
    unfold IsRealEndToEndFirstRightPhaseAt
    exact endToEndFirstRight_continue_eq_real_phase A package key row past
      (some pending) (move.2, move.1) target hstaged
  · rcases hfirstLeft with ⟨key, row, past, pending, rfl⟩
    have hsome := endToEndFirstLeft_real_close_staged A package key row past move
    rw [Option.isSome_iff_exists] at hsome
    rcases hsome with ⟨target, hstaged⟩
    right; left
    refine ⟨key, row, past ++ [move], target, ?_⟩
    unfold IsRealEndToEndFirstLeftPhaseAt
    exact endToEndFirstLeft_continue_eq_real_phase A package key row past
      (some pending) move target hstaged
  · rcases hrightRight with
      ⟨key, child, source, row, past, pending, rfl⟩
    let fullSource : EndToEndRightOriginRecurrentRightMacro A package :=
      ⟨key, child, source⟩
    rcases endToEndRightOriginRecurrentRight_real_close_allowed A package
      fullSource row past (move.2, move.1) with
      ⟨target, hstaged, _hallowed⟩
    right; right; left
    refine ⟨key, child, source, row, past ++ [(move.2, move.1)], target, ?_⟩
    unfold IsRealEndToEndRightOriginRightPhaseAt
    exact endToEndRightOriginRight_continue_eq_real_phase A package fullSource
      row past (some ⟨key, child, pending⟩) (move.2, move.1)
      ⟨key, child, target⟩ hstaged
  · rcases hrightLeft with
      ⟨key, child, source, row, past, pending, rfl⟩
    let fullSource : EndToEndRightOriginRecurrentLeftMacro A package :=
      ⟨key, child, source⟩
    rcases endToEndRightOriginRecurrentLeft_real_close_allowed A package
      fullSource row past move with ⟨target, hstaged, _hallowed⟩
    right; right; right; left
    refine ⟨key, child, source, row, past ++ [move], target, ?_⟩
    unfold IsRealEndToEndRightOriginLeftPhaseAt
    exact endToEndRightOriginLeft_continue_eq_real_phase A package fullSource
      row past (some ⟨key, child, pending⟩) move
      ⟨key, child, target⟩ hstaged
  · rcases hleftRight with
      ⟨key, child, source, row, past, pending, rfl⟩
    let fullSource : EndToEndLeftOriginRecurrentRightMacro A package :=
      ⟨key, child, source⟩
    rcases endToEndLeftOriginRecurrentRight_real_close_allowed A package
      fullSource row past (move.2, move.1) with
      ⟨target, hstaged, _hallowed⟩
    right; right; right; right; left
    refine ⟨key, child, source, row, past ++ [(move.2, move.1)], target, ?_⟩
    unfold IsRealEndToEndLeftOriginRightPhaseAt
    exact endToEndLeftOriginRight_continue_eq_real_phase A package fullSource
      row past (some ⟨key, child, pending⟩) (move.2, move.1)
      ⟨key, child, target⟩ hstaged
  · rcases hleftLeft with
      ⟨key, child, source, row, past, pending, rfl⟩
    let fullSource : EndToEndLeftOriginRecurrentLeftMacro A package :=
      ⟨key, child, source⟩
    rcases endToEndLeftOriginRecurrentLeft_real_close_allowed A package
      fullSource row past move with ⟨target, hstaged, _hallowed⟩
    right; right; right; right; right
    refine ⟨key, child, source, row, past ++ [move], target, ?_⟩
    unfold IsRealEndToEndLeftOriginLeftPhaseAt
    exact endToEndLeftOriginLeft_continue_eq_real_phase A package fullSource
      row past (some ⟨key, child, pending⟩) move
      ⟨key, child, target⟩ hstaged

/-! ## Closure across a strict reversal -/

/-- A strict right-to-left reversal consumes exactly the staged adjacent
macro and remains below its literal child. -/
theorem isAdjacentRealEndToEndPhase_reverseRightToLeft
    (phase : EndToEndMatchedPhase A package)
    (hphase : IsAdjacentRealEndToEndPhase A package phase)
    (hright : phase.IsRight) (move : In₁ × In₂)
    (previouslyReceived : Bool) :
    ∃ next,
      (phase.reverseRightToLeft A package move previouslyReceived).2 =
          some next ∧
        IsAdjacentRealEndToEndPhase A package next := by
  rcases hphase with hfirstRight | hfirstLeft | hrightRight | hrightLeft |
      hleftRight | hleftLeft
  · rcases hfirstRight with ⟨key, row, past, pending, rfl⟩
    rcases pending with ⟨child, pending⟩
    let source : EndToEndRightOriginRecurrentLeftMacro A package :=
      ⟨key, child, pending⟩
    let newRow := guardedEntryRowOfReceived previouslyReceived
    rcases endToEndRightOriginRecurrentLeft_real_close_allowed A package
      source newRow [] move with ⟨target, hstaged, _hallowed⟩
    let base : EndToEndMatchedPhase A package := .rightOriginLeft
      (initialEndToEndRightOriginRecurrentLeftReceiver A package source newRow)
      (initialEndToEndRightOriginRecurrentLeftOwner A package source) rfl
    have hbase := endToEndRightOriginLeft_continue_eq_real_phase A package
      source newRow [] none move ⟨key, child, target⟩ hstaged
    refine ⟨(base.continue A package move).2, ?_, ?_⟩
    · simp [source, newRow, EndToEndMatchedPhase.reverseRightToLeft,
        switchEndToEndFirstRightOwnerToRecurrentLeftReceiver,
        switchEndToEndFirstRightReceiverToRecurrentLeftOwner,
        EndToEndMatchedPhase.continue, base]
    · right; right; right; left
      refine ⟨key, child, pending, newRow, [move], target, ?_⟩
      unfold IsRealEndToEndRightOriginLeftPhaseAt
      exact hbase
  · rcases hfirstLeft with ⟨key, row, past, target, hbad⟩
    unfold IsRealEndToEndFirstLeftPhaseAt at hbad
    rw [hbad] at hright
    simp [EndToEndMatchedPhase.IsRight] at hright
  · rcases hrightRight with
      ⟨key, child, current, row, past, pending, rfl⟩
    let source : EndToEndRightOriginRecurrentLeftMacro A package :=
      ⟨key, child, pending⟩
    let newRow := guardedEntryRowOfReceived previouslyReceived
    rcases endToEndRightOriginRecurrentLeft_real_close_allowed A package
      source newRow [] move with ⟨target, hstaged, _hallowed⟩
    let base : EndToEndMatchedPhase A package := .rightOriginLeft
      (initialEndToEndRightOriginRecurrentLeftReceiver A package source newRow)
      (initialEndToEndRightOriginRecurrentLeftOwner A package source) rfl
    have hbase := endToEndRightOriginLeft_continue_eq_real_phase A package
      source newRow [] none move ⟨key, child, target⟩ hstaged
    refine ⟨(base.continue A package move).2, ?_, ?_⟩
    · simp [source, newRow, EndToEndMatchedPhase.reverseRightToLeft,
        switchEndToEndRightOriginRightOwnerToLeftReceiver,
        switchEndToEndRightOriginRightReceiverToLeftOwner,
        EndToEndMatchedPhase.continue, base]
    · right; right; right; left
      refine ⟨key, child, pending, newRow, [move], target, ?_⟩
      unfold IsRealEndToEndRightOriginLeftPhaseAt
      exact hbase
  · rcases hrightLeft with
      ⟨key, child, source, row, past, target, hbad⟩
    unfold IsRealEndToEndRightOriginLeftPhaseAt at hbad
    rw [hbad] at hright
    simp [EndToEndMatchedPhase.IsRight] at hright
  · rcases hleftRight with
      ⟨key, child, current, row, past, pending, rfl⟩
    let source : EndToEndLeftOriginRecurrentLeftMacro A package :=
      ⟨key, child, pending⟩
    let newRow := guardedEntryRowOfReceived previouslyReceived
    rcases endToEndLeftOriginRecurrentLeft_real_close_allowed A package
      source newRow [] move with ⟨target, hstaged, _hallowed⟩
    let base : EndToEndMatchedPhase A package := .leftOriginLeft
      (initialEndToEndLeftOriginRecurrentLeftReceiver A package source newRow)
      (initialEndToEndLeftOriginRecurrentLeftOwner A package source) rfl
    have hbase := endToEndLeftOriginLeft_continue_eq_real_phase A package
      source newRow [] none move ⟨key, child, target⟩ hstaged
    refine ⟨(base.continue A package move).2, ?_, ?_⟩
    · simp [source, newRow, EndToEndMatchedPhase.reverseRightToLeft,
        switchEndToEndLeftOriginRightOwnerToLeftReceiver,
        switchEndToEndLeftOriginRightReceiverToLeftOwner,
        EndToEndMatchedPhase.continue, base]
    · right; right; right; right; right
      refine ⟨key, child, pending, newRow, [move], target, ?_⟩
      unfold IsRealEndToEndLeftOriginLeftPhaseAt
      exact hbase
  · rcases hleftLeft with
      ⟨key, child, source, row, past, target, hbad⟩
    unfold IsRealEndToEndLeftOriginLeftPhaseAt at hbad
    rw [hbad] at hright
    simp [EndToEndMatchedPhase.IsRight] at hright

/-- Left-to-right mirror of the exact adjacency closure. -/
theorem isAdjacentRealEndToEndPhase_reverseLeftToRight
    (phase : EndToEndMatchedPhase A package)
    (hphase : IsAdjacentRealEndToEndPhase A package phase)
    (hleft : phase.IsLeft) (move : In₁ × In₂)
    (previouslyReceived : Bool) :
    ∃ next,
      (phase.reverseLeftToRight A package (move.2, move.1)
          previouslyReceived).2 = some next ∧
        IsAdjacentRealEndToEndPhase A package next := by
  rcases hphase with hfirstRight | hfirstLeft | hrightRight | hrightLeft |
      hleftRight | hleftLeft
  · rcases hfirstRight with ⟨key, row, past, target, hbad⟩
    unfold IsRealEndToEndFirstRightPhaseAt at hbad
    rw [hbad] at hleft
    simp [EndToEndMatchedPhase.IsLeft] at hleft
  · rcases hfirstLeft with ⟨key, row, past, pending, rfl⟩
    rcases pending with ⟨child, pending⟩
    let source : EndToEndLeftOriginRecurrentRightMacro A package :=
      ⟨key, child, pending⟩
    let newRow := guardedEntryRowOfReceived previouslyReceived
    rcases endToEndLeftOriginRecurrentRight_real_close_allowed A package
      source newRow [] (move.2, move.1) with
      ⟨target, hstaged, _hallowed⟩
    let base : EndToEndMatchedPhase A package := .leftOriginRight
      (initialEndToEndLeftOriginRecurrentRightOwner A package source)
      (initialEndToEndLeftOriginRecurrentRightReceiver A package source newRow)
      rfl
    have hbase := endToEndLeftOriginRight_continue_eq_real_phase A package
      source newRow [] none (move.2, move.1) ⟨key, child, target⟩ hstaged
    refine ⟨(base.continue A package move).2, ?_, ?_⟩
    · simp [source, newRow, EndToEndMatchedPhase.reverseLeftToRight,
        switchEndToEndFirstLeftOwnerToRecurrentRightReceiver,
        switchEndToEndFirstLeftReceiverToRecurrentRightOwner,
        EndToEndMatchedPhase.continue, base]
    · right; right; right; right; left
      refine ⟨key, child, pending, newRow, [(move.2, move.1)], target, ?_⟩
      unfold IsRealEndToEndLeftOriginRightPhaseAt
      exact hbase
  · rcases hrightRight with
      ⟨key, child, source, row, past, target, hbad⟩
    unfold IsRealEndToEndRightOriginRightPhaseAt at hbad
    rw [hbad] at hleft
    simp [EndToEndMatchedPhase.IsLeft] at hleft
  · rcases hrightLeft with
      ⟨key, child, current, row, past, pending, rfl⟩
    let source : EndToEndRightOriginRecurrentRightMacro A package :=
      ⟨key, child, pending⟩
    let newRow := guardedEntryRowOfReceived previouslyReceived
    rcases endToEndRightOriginRecurrentRight_real_close_allowed A package
      source newRow [] (move.2, move.1) with
      ⟨target, hstaged, _hallowed⟩
    let base : EndToEndMatchedPhase A package := .rightOriginRight
      (initialEndToEndRightOriginRecurrentRightOwner A package source)
      (initialEndToEndRightOriginRecurrentRightReceiver A package source newRow)
      rfl
    have hbase := endToEndRightOriginRight_continue_eq_real_phase A package
      source newRow [] none (move.2, move.1) ⟨key, child, target⟩ hstaged
    refine ⟨(base.continue A package move).2, ?_, ?_⟩
    · simp [source, newRow, EndToEndMatchedPhase.reverseLeftToRight,
        switchEndToEndRightOriginLeftOwnerToRightReceiver,
        switchEndToEndRightOriginLeftReceiverToRightOwner,
        EndToEndMatchedPhase.continue, base]
    · right; right; left
      refine ⟨key, child, pending, newRow, [(move.2, move.1)], target, ?_⟩
      unfold IsRealEndToEndRightOriginRightPhaseAt
      exact hbase
  · rcases hleftRight with
      ⟨key, child, source, row, past, target, hbad⟩
    unfold IsRealEndToEndLeftOriginRightPhaseAt at hbad
    rw [hbad] at hleft
    simp [EndToEndMatchedPhase.IsLeft] at hleft
  · rcases hleftLeft with
      ⟨key, child, current, row, past, pending, rfl⟩
    let source : EndToEndLeftOriginRecurrentRightMacro A package :=
      ⟨key, child, pending⟩
    let newRow := guardedEntryRowOfReceived previouslyReceived
    rcases endToEndLeftOriginRecurrentRight_real_close_allowed A package
      source newRow [] (move.2, move.1) with
      ⟨target, hstaged, _hallowed⟩
    let base : EndToEndMatchedPhase A package := .leftOriginRight
      (initialEndToEndLeftOriginRecurrentRightOwner A package source)
      (initialEndToEndLeftOriginRecurrentRightReceiver A package source newRow)
      rfl
    have hbase := endToEndLeftOriginRight_continue_eq_real_phase A package
      source newRow [] none (move.2, move.1) ⟨key, child, target⟩ hstaged
    refine ⟨(base.continue A package move).2, ?_, ?_⟩
    · simp [source, newRow, EndToEndMatchedPhase.reverseLeftToRight,
        switchEndToEndLeftOriginLeftOwnerToRightReceiver,
        switchEndToEndLeftOriginLeftReceiverToRightOwner,
        EndToEndMatchedPhase.continue, base]
    · right; right; right; right; left
      refine ⟨key, child, pending, newRow, [(move.2, move.1)], target, ?_⟩
      unfold IsRealEndToEndLeftOriginRightPhaseAt
      exact hbase

/-! ## Exact mixed restart-root extractors -/

/-- Proof data carried by a real right phase: its exact current mixed restart
root and the exact fresh left root stored in its pending slot.  The three
constructors cover first, right-origin recurrent, and left-origin recurrent
phases. -/
inductive EndToEndRightPendingAdjacency
    (phase : EndToEndMatchedPhase A package) : Type (max u v x y s)
  | first
      (key : EndToEndInitialLeftBoundaryKey A package)
      (row : PairedEntryRow) (past : List (In₂ × In₁))
      (target : EndToEndGuardedRightRecurrentLeftMacro A
        (rightGuarded :=
          (endToEndInitialLeftBoundaryActivation A package key).policy))
      (hphase : IsRealEndToEndFirstRightPhaseAt A package key row past target
        phase)
  | rightOrigin
      (key : EndToEndInitialLeftBoundaryKey A package)
      (child : EndToEndGuardedRightChild A key.1.2.2.2
        (endToEndInitialLeftBoundaryActivation A package key).profile
        (endToEndInitialLeftBoundaryActivation A package key).policy)
      (source : ProfiledPolicyRightMacro A (child.policy A))
      (row : PairedEntryRow) (past : List (In₂ × In₁))
      (target : ProfiledPolicyLeftMacro A (child.policy A))
      (hphase : IsRealEndToEndRightOriginRightPhaseAt A package
        ⟨key, child, source⟩ row past ⟨key, child, target⟩ phase)
  | leftOrigin
      (key : EndToEndInitialRightBoundaryKey A package)
      (child : EndToEndGuardedLeftChild A key.1.2.2.2
        (endToEndInitialRightBoundaryActivation A package key).profile
        (endToEndInitialRightBoundaryActivation A package key).policy)
      (source : ProfiledPolicyRightMacro A (child.policy A))
      (row : PairedEntryRow) (past : List (In₂ × In₁))
      (target : ProfiledPolicyLeftMacro A (child.policy A))
      (hphase : IsRealEndToEndLeftOriginRightPhaseAt A package
        ⟨key, child, source⟩ row past ⟨key, child, target⟩ phase)

/-- Left-oriented mirror. -/
inductive EndToEndLeftPendingAdjacency
    (phase : EndToEndMatchedPhase A package) : Type (max u v x y s)
  | first
      (key : EndToEndInitialRightBoundaryKey A package)
      (row : PairedEntryRow) (past : List (In₁ × In₂))
      (target : EndToEndGuardedLeftRecurrentRightMacro A
        (leftGuarded :=
          (endToEndInitialRightBoundaryActivation A package key).policy))
      (hphase : IsRealEndToEndFirstLeftPhaseAt A package key row past target
        phase)
  | rightOrigin
      (key : EndToEndInitialLeftBoundaryKey A package)
      (child : EndToEndGuardedRightChild A key.1.2.2.2
        (endToEndInitialLeftBoundaryActivation A package key).profile
        (endToEndInitialLeftBoundaryActivation A package key).policy)
      (source : ProfiledPolicyLeftMacro A (child.policy A))
      (row : PairedEntryRow) (past : List (In₁ × In₂))
      (target : ProfiledPolicyRightMacro A (child.policy A))
      (hphase : IsRealEndToEndRightOriginLeftPhaseAt A package
        ⟨key, child, source⟩ row past ⟨key, child, target⟩ phase)
  | leftOrigin
      (key : EndToEndInitialRightBoundaryKey A package)
      (child : EndToEndGuardedLeftChild A key.1.2.2.2
        (endToEndInitialRightBoundaryActivation A package key).profile
        (endToEndInitialRightBoundaryActivation A package key).policy)
      (source : ProfiledPolicyLeftMacro A (child.policy A))
      (row : PairedEntryRow) (past : List (In₁ × In₂))
      (target : ProfiledPolicyRightMacro A (child.policy A))
      (hphase : IsRealEndToEndLeftOriginLeftPhaseAt A package
        ⟨key, child, source⟩ row past ⟨key, child, target⟩ phase)

namespace EndToEndRightPendingAdjacency

/-- Current mixed restart root, including the exact monitor state reached by
the concrete prefix. -/
def currentRoot {phase : EndToEndMatchedPhase A package}
    (adj : EndToEndRightPendingAdjacency A package phase) :
    EndToEndRightRestartRoot A package :=
  match adj with
  | .first key _ past _ _ =>
      ⟨EndToEndRightMonitorSource.first key,
        (endToEndFirstRightFiniteStateAfter A package key past).2⟩
  | .rightOrigin key child source _ past _ _ =>
      ⟨EndToEndRightMonitorSource.rightOrigin ⟨key, child, source⟩,
        (profiledPolicyRightFiniteStateAfter A (child.policy A) source past).2⟩
  | .leftOrigin key child source _ past _ _ =>
      ⟨EndToEndRightMonitorSource.leftOrigin ⟨key, child, source⟩,
        (profiledPolicyRightFiniteStateAfter A (child.policy A) source past).2⟩

/-- Fresh opposite root literally stored by the current receiver. -/
def pendingRoot {phase : EndToEndMatchedPhase A package}
    (adj : EndToEndRightPendingAdjacency A package phase) :
    EndToEndLeftRestartRoot A package :=
  match adj with
  | .first key _ _ target _ =>
      ⟨EndToEndLeftMonitorSource.rightOrigin ⟨key, target⟩,
        (endToEndGuardedRightRecurrentLeftMonitor A target).initial⟩
  | .rightOrigin key child _ _ _ target _ =>
      ⟨EndToEndLeftMonitorSource.rightOrigin ⟨key, child, target⟩,
        (profiledPolicyLeftMonitor A (child.policy A) target).initial⟩
  | .leftOrigin key child _ _ _ target _ =>
      ⟨EndToEndLeftMonitorSource.leftOrigin ⟨key, child, target⟩,
        (profiledPolicyLeftMonitor A (child.policy A) target).initial⟩

/-- Orientation is derivable from the witness and remains proof-only. -/
theorem isRight {phase : EndToEndMatchedPhase A package}
    (adj : EndToEndRightPendingAdjacency A package phase) : phase.IsRight := by
  cases adj with
  | first key row past target hphase =>
      unfold IsRealEndToEndFirstRightPhaseAt at hphase
      subst phase
      trivial
  | rightOrigin key child source row past target hphase =>
      unfold IsRealEndToEndRightOriginRightPhaseAt at hphase
      subst phase
      trivial
  | leftOrigin key child source row past target hphase =>
      unfold IsRealEndToEndLeftOriginRightPhaseAt at hphase
      subst phase
      trivial

/-- The extracted current root agrees with the generic phase extractor. -/
theorem currentRoot_eq {phase : EndToEndMatchedPhase A package}
    (adj : EndToEndRightPendingAdjacency A package phase) :
    adj.currentRoot A package =
      endToEndRightRestartRootOfPhase A package phase (adj.isRight A package) := by
  cases adj with
  | first key row past target hphase =>
      unfold IsRealEndToEndFirstRightPhaseAt at hphase
      subst phase
      rfl
  | rightOrigin key child source row past target hphase =>
      unfold IsRealEndToEndRightOriginRightPhaseAt at hphase
      subst phase
      rfl
  | leftOrigin key child source row past target hphase =>
      unfold IsRealEndToEndLeftOriginRightPhaseAt at hphase
      subst phase
      rfl

end EndToEndRightPendingAdjacency

namespace EndToEndLeftPendingAdjacency

def currentRoot {phase : EndToEndMatchedPhase A package}
    (adj : EndToEndLeftPendingAdjacency A package phase) :
    EndToEndLeftRestartRoot A package :=
  match adj with
  | .first key _ past _ _ =>
      ⟨EndToEndLeftMonitorSource.first key,
        (endToEndFirstLeftFiniteStateAfter A package key past).2⟩
  | .rightOrigin key child source _ past _ _ =>
      ⟨EndToEndLeftMonitorSource.rightOrigin ⟨key, child, source⟩,
        (profiledPolicyLeftFiniteStateAfter A (child.policy A) source past).2⟩
  | .leftOrigin key child source _ past _ _ =>
      ⟨EndToEndLeftMonitorSource.leftOrigin ⟨key, child, source⟩,
        (profiledPolicyLeftFiniteStateAfter A (child.policy A) source past).2⟩

def pendingRoot {phase : EndToEndMatchedPhase A package}
    (adj : EndToEndLeftPendingAdjacency A package phase) :
    EndToEndRightRestartRoot A package :=
  match adj with
  | .first key _ _ target _ =>
      ⟨EndToEndRightMonitorSource.leftOrigin ⟨key, target⟩,
        (endToEndGuardedLeftRecurrentRightMonitor A target).initial⟩
  | .rightOrigin key child _ _ _ target _ =>
      ⟨EndToEndRightMonitorSource.rightOrigin ⟨key, child, target⟩,
        (profiledPolicyRightMonitor A (child.policy A) target).initial⟩
  | .leftOrigin key child _ _ _ target _ =>
      ⟨EndToEndRightMonitorSource.leftOrigin ⟨key, child, target⟩,
        (profiledPolicyRightMonitor A (child.policy A) target).initial⟩

theorem isLeft {phase : EndToEndMatchedPhase A package}
    (adj : EndToEndLeftPendingAdjacency A package phase) : phase.IsLeft := by
  cases adj with
  | first key row past target hphase =>
      unfold IsRealEndToEndFirstLeftPhaseAt at hphase
      subst phase
      trivial
  | rightOrigin key child source row past target hphase =>
      unfold IsRealEndToEndRightOriginLeftPhaseAt at hphase
      subst phase
      trivial
  | leftOrigin key child source row past target hphase =>
      unfold IsRealEndToEndLeftOriginLeftPhaseAt at hphase
      subst phase
      trivial

theorem currentRoot_eq {phase : EndToEndMatchedPhase A package}
    (adj : EndToEndLeftPendingAdjacency A package phase) :
    adj.currentRoot A package =
      endToEndLeftRestartRootOfPhase A package phase (adj.isLeft A package) := by
  cases adj with
  | first key row past target hphase =>
      unfold IsRealEndToEndFirstLeftPhaseAt at hphase
      subst phase
      rfl
  | rightOrigin key child source row past target hphase =>
      unfold IsRealEndToEndRightOriginLeftPhaseAt at hphase
      subst phase
      rfl
  | leftOrigin key child source row past target hphase =>
      unfold IsRealEndToEndLeftOriginLeftPhaseAt at hphase
      subst phase
      rfl

end EndToEndLeftPendingAdjacency

/-! ## Extraction from the strengthened reachable-state invariant -/

theorem exists_rightPendingAdjacency_of_adjacent
    (phase : EndToEndMatchedPhase A package)
    (hphase : IsAdjacentRealEndToEndPhase A package phase)
    (hright : phase.IsRight) :
    Nonempty (EndToEndRightPendingAdjacency A package phase) := by
  rcases hphase with hfirstRight | hfirstLeft | hrightRight | hrightLeft |
      hleftRight | hleftLeft
  · rcases hfirstRight with ⟨key, row, past, target, hphase⟩
    exact ⟨EndToEndRightPendingAdjacency.first key row past target hphase⟩
  · rcases hfirstLeft with ⟨key, row, past, target, hbad⟩
    unfold IsRealEndToEndFirstLeftPhaseAt at hbad
    rw [hbad] at hright
    simp [EndToEndMatchedPhase.IsRight] at hright
  · rcases hrightRight with
      ⟨key, child, source, row, past, target, hphase⟩
    exact ⟨EndToEndRightPendingAdjacency.rightOrigin key child source row
      past target hphase⟩
  · rcases hrightLeft with
      ⟨key, child, source, row, past, target, hbad⟩
    unfold IsRealEndToEndRightOriginLeftPhaseAt at hbad
    rw [hbad] at hright
    simp [EndToEndMatchedPhase.IsRight] at hright
  · rcases hleftRight with
      ⟨key, child, source, row, past, target, hphase⟩
    exact ⟨EndToEndRightPendingAdjacency.leftOrigin key child source row
      past target hphase⟩
  · rcases hleftLeft with
      ⟨key, child, source, row, past, target, hbad⟩
    unfold IsRealEndToEndLeftOriginLeftPhaseAt at hbad
    rw [hbad] at hright
    simp [EndToEndMatchedPhase.IsRight] at hright

theorem exists_leftPendingAdjacency_of_adjacent
    (phase : EndToEndMatchedPhase A package)
    (hphase : IsAdjacentRealEndToEndPhase A package phase)
    (hleft : phase.IsLeft) :
    Nonempty (EndToEndLeftPendingAdjacency A package phase) := by
  rcases hphase with hfirstRight | hfirstLeft | hrightRight | hrightLeft |
      hleftRight | hleftLeft
  · rcases hfirstRight with ⟨key, row, past, target, hbad⟩
    unfold IsRealEndToEndFirstRightPhaseAt at hbad
    rw [hbad] at hleft
    simp [EndToEndMatchedPhase.IsLeft] at hleft
  · rcases hfirstLeft with ⟨key, row, past, target, hphase⟩
    exact ⟨EndToEndLeftPendingAdjacency.first key row past target hphase⟩
  · rcases hrightRight with
      ⟨key, child, source, row, past, target, hbad⟩
    unfold IsRealEndToEndRightOriginRightPhaseAt at hbad
    rw [hbad] at hleft
    simp [EndToEndMatchedPhase.IsLeft] at hleft
  · rcases hrightLeft with
      ⟨key, child, source, row, past, target, hphase⟩
    exact ⟨EndToEndLeftPendingAdjacency.rightOrigin key child source row
      past target hphase⟩
  · rcases hleftRight with
      ⟨key, child, source, row, past, target, hbad⟩
    unfold IsRealEndToEndLeftOriginRightPhaseAt at hbad
    rw [hbad] at hleft
    simp [EndToEndMatchedPhase.IsLeft] at hleft
  · rcases hleftLeft with
      ⟨key, child, source, row, past, target, hphase⟩
    exact ⟨EndToEndLeftPendingAdjacency.leftOrigin key child source row
      past target hphase⟩

/-! ## The two-shadow source consumed by simultaneous family narrowing -/

/-- Both candidates carry exact source--pending adjacency. -/
def EndToEndBothCandidates.AdjacentReal
    (candidates : EndToEndBothCandidates A package) : Prop :=
  IsAdjacentRealEndToEndPhase A package candidates.right ∧
    IsAdjacentRealEndToEndPhase A package candidates.left

theorem EndToEndBothCandidates.real_of_adjacentReal
    (candidates : EndToEndBothCandidates A package)
    (hreal : candidates.AdjacentReal A package) :
    candidates.Real A package :=
  ⟨isRealEndToEndPhase_of_adjacent A package candidates.right hreal.1,
    isRealEndToEndPhase_of_adjacent A package candidates.left hreal.2⟩

/-- Proof-only data from which the two orientation-specific mixed root
families are read. -/
structure EndToEndBothPendingAdjacency
    (candidates : EndToEndBothCandidates A package) where
  right : EndToEndRightPendingAdjacency A package candidates.right
  left : EndToEndLeftPendingAdjacency A package candidates.left

theorem exists_bothPendingAdjacency_of_adjacentReal
    (candidates : EndToEndBothCandidates A package)
    (hreal : candidates.AdjacentReal A package) :
    Nonempty (EndToEndBothPendingAdjacency A package candidates) := by
  obtain ⟨right⟩ := exists_rightPendingAdjacency_of_adjacent A package
    candidates.right hreal.1 candidates.right_oriented
  obtain ⟨left⟩ := exists_leftPendingAdjacency_of_adjacent A package
    candidates.left hreal.2 candidates.left_oriented
  exact ⟨⟨right, left⟩⟩

namespace EndToEndBothPendingAdjacency

/-- The exact right-family roots at the dangerous left-to-right seam.  Member
`false` is the current right shadow; member `true` is the fresh right root
staged by the left shadow.  The members may have different guarded children. -/
def rightFamilySource {candidates : EndToEndBothCandidates A package}
    (adj : EndToEndBothPendingAdjacency A package candidates) :
    Bool → EndToEndRightRestartRoot A package
  | false => adj.right.currentRoot A package
  | true => adj.left.pendingRoot A package

/-- Left-family mirror.  It intentionally uses mixed restart roots, not one
global common-child index: the continued exceptional and recurrent shadows
can belong to different children. -/
def leftFamilySource {candidates : EndToEndBothCandidates A package}
    (adj : EndToEndBothPendingAdjacency A package candidates) :
    Bool → EndToEndLeftRestartRoot A package
  | false => adj.left.currentRoot A package
  | true => adj.right.pendingRoot A package

@[simp] theorem rightFamilySource_false
    {candidates : EndToEndBothCandidates A package}
    (adj : EndToEndBothPendingAdjacency A package candidates) :
    adj.rightFamilySource A package false =
      adj.right.currentRoot A package := rfl

@[simp] theorem rightFamilySource_true
    {candidates : EndToEndBothCandidates A package}
    (adj : EndToEndBothPendingAdjacency A package candidates) :
    adj.rightFamilySource A package true =
      adj.left.pendingRoot A package := rfl

@[simp] theorem leftFamilySource_false
    {candidates : EndToEndBothCandidates A package}
    (adj : EndToEndBothPendingAdjacency A package candidates) :
    adj.leftFamilySource A package false =
      adj.left.currentRoot A package := rfl

@[simp] theorem leftFamilySource_true
    {candidates : EndToEndBothCandidates A package}
    (adj : EndToEndBothPendingAdjacency A package candidates) :
    adj.leftFamilySource A package true =
      adj.right.pendingRoot A package := rfl

/-- The current members of the two source maps are exactly the roots extracted
from the operational phases; no independently selected controller appears. -/
theorem rightFamilySource_false_eq_phaseRoot
    {candidates : EndToEndBothCandidates A package}
    (adj : EndToEndBothPendingAdjacency A package candidates) :
    adj.rightFamilySource A package false =
      endToEndRightRestartRootOfPhase A package candidates.right
        (adj.right.isRight A package) :=
  adj.right.currentRoot_eq A package

theorem leftFamilySource_false_eq_phaseRoot
    {candidates : EndToEndBothCandidates A package}
    (adj : EndToEndBothPendingAdjacency A package candidates) :
    adj.leftFamilySource A package false =
      endToEndLeftRestartRootOfPhase A package candidates.left
        (adj.left.isLeft A package) :=
  adj.left.currentRoot_eq A package

end EndToEndBothPendingAdjacency

/-! ## Strong two-shadow closure -/

/-- Entering overlap from a strongly reachable right phase yields two
strongly reachable, exactly adjacent candidates. -/
theorem exists_adjacent_endToEnd_candidates_enterBothFromRight
    (phase : EndToEndMatchedPhase A package)
    (hphase : IsAdjacentRealEndToEndPhase A package phase)
    (hright : phase.IsRight) (move : In₁ × In₂) :
    ∃ candidates,
      (phase.enterBothFromRight A package move).2 = some candidates ∧
        candidates.AdjacentReal A package := by
  obtain ⟨left, hleft, hadjLeft⟩ :=
    isAdjacentRealEndToEndPhase_reverseRightToLeft A package phase hphase
      hright move false
  have horientLeft : left.IsLeft :=
    endToEndReverseRightToLeft_isLeft_of_eq_some A package phase left move
      false hleft
  have horientRight : (phase.continue A package move).2.IsRight :=
    phase.continue_isRight A package move hright
  let candidates : EndToEndBothCandidates A package :=
    ⟨(phase.continue A package move).2, left, horientRight, horientLeft⟩
  refine ⟨candidates, ?_, ?_, hadjLeft⟩
  · simp [EndToEndMatchedPhase.enterBothFromRight, hleft, horientRight,
      horientLeft, candidates]
  · exact isAdjacentRealEndToEndPhase_continue A package phase hphase move

/-- Left-oriented mirror. -/
theorem exists_adjacent_endToEnd_candidates_enterBothFromLeft
    (phase : EndToEndMatchedPhase A package)
    (hphase : IsAdjacentRealEndToEndPhase A package phase)
    (hleft : phase.IsLeft) (move : In₁ × In₂) :
    ∃ candidates,
      (phase.enterBothFromLeft A package move).2 = some candidates ∧
        candidates.AdjacentReal A package := by
  obtain ⟨right, hright, hadjRight⟩ :=
    isAdjacentRealEndToEndPhase_reverseLeftToRight A package phase hphase
      hleft move false
  have horientRight : right.IsRight :=
    endToEndReverseLeftToRight_isRight_of_eq_some A package phase right move
      false hright
  have horientLeft : (phase.continue A package move).2.IsLeft :=
    phase.continue_isLeft A package move hleft
  let candidates : EndToEndBothCandidates A package :=
    ⟨right, (phase.continue A package move).2, horientRight, horientLeft⟩
  refine ⟨candidates, ?_, hadjRight, ?_⟩
  · simp [EndToEndMatchedPhase.enterBothFromLeft, hright, horientRight,
      horientLeft, candidates]
  · exact isAdjacentRealEndToEndPhase_continue A package phase hphase move

/-- Consecutive ambiguous rounds preserve the exact adjacency relation. -/
theorem exists_adjacent_endToEnd_candidates_repeatBoth
    (anchor : Bool) (candidates : EndToEndBothCandidates A package)
    (hreal : candidates.AdjacentReal A package) (move : In₁ × In₂) :
    ∃ next,
      (if anchor then candidates.repeatBothFromLeft A package move
        else candidates.repeatBothFromRight A package move).2 = some next ∧
      next.AdjacentReal A package := by
  cases anchor with
  | false =>
      simpa [EndToEndBothCandidates.repeatBothFromRight] using
        exists_adjacent_endToEnd_candidates_enterBothFromRight A package
          candidates.right hreal.1 candidates.right_oriented move
  | true =>
      simpa [EndToEndBothCandidates.repeatBothFromLeft] using
        exists_adjacent_endToEnd_candidates_enterBothFromLeft A package
          candidates.left hreal.2 candidates.left_oriented move
end

end DetParityAutomaton

end DistributedSynthesis
