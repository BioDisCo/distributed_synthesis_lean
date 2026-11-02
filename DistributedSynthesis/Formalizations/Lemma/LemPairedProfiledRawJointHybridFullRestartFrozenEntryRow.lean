/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridFullRestartFirstThenBothScan

/-!
# A phase detector separated from the semantic entry row

The payload-linked FullRestart controller currently reuses `lastRecv` twice:
it detects an orientation change, and it selects `.first` or `.both` in the
paired table.  The first use is local and sound.  The second use creates the
unsupported `.first, .both, .both, ...` scan.

This file isolates the smallest finite repair.  A local state keeps the
receive bit and the semantic row as distinct fields.  On the first receive of
a phase the row is reset to `.first`; subsequent receives retain it.  Starting
from the actual initial state, the reachable row is therefore always
`.first`.  No graph, leader, hierarchy side, history, or proof witness enters
the update.

The last section records the payoff: the resulting DPA current/minimum pair
is exactly the already checked constant-`.first` scan, and its infinite tail
acceptance is an existing component of `PairedRightForeverAccepts` (and its
left mirror).  Thus this repair needs no third semantic acceptance axiom.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

/-! ## The implementable local field -/

/-- The phase-change bit and the semantic row are intentionally distinct.
Both fields are finite and local. -/
structure ProfiledRawJointFrozenEntryRowControl where
  lastRecv : Bool
  entryRow : PairedEntryRow
deriving DecidableEq, Fintype

/-- Initial control before any receive. -/
def profiledRawJointFrozenEntryRowInitial :
    ProfiledRawJointFrozenEntryRowControl :=
  ⟨false, .first⟩

/-- Row used for the current receive.  A receive after a blind round starts a
fresh semantic phase at `.first`; a repeated receive keeps the installed
row. -/
def profiledRawJointFrozenEntryRowSelected
    (control : ProfiledRawJointFrozenEntryRowControl) : PairedEntryRow :=
  if control.lastRecv then control.entryRow else .first

/-- Local receive update. -/
def profiledRawJointFrozenEntryRowRecv
    (control : ProfiledRawJointFrozenEntryRowControl) :
    ProfiledRawJointFrozenEntryRowControl :=
  ⟨true, profiledRawJointFrozenEntryRowSelected control⟩

/-- Local blind/no-receive update.  It changes only the phase detector. -/
def profiledRawJointFrozenEntryRowNoRecv
    (control : ProfiledRawJointFrozenEntryRowControl) :
    ProfiledRawJointFrozenEntryRowControl :=
  ⟨false, control.entryRow⟩

@[simp] theorem profiledRawJointFrozenEntryRowSelected_initial :
    profiledRawJointFrozenEntryRowSelected
      profiledRawJointFrozenEntryRowInitial = .first := by
  rfl

@[simp] theorem profiledRawJointFrozenEntryRowSelected_after_noRecv
    (control : ProfiledRawJointFrozenEntryRowControl) :
    profiledRawJointFrozenEntryRowSelected
        (profiledRawJointFrozenEntryRowNoRecv control) = .first := by
  rfl

@[simp] theorem profiledRawJointFrozenEntryRowSelected_after_recv
    (control : ProfiledRawJointFrozenEntryRowControl) :
    profiledRawJointFrozenEntryRowSelected
        (profiledRawJointFrozenEntryRowRecv control) =
      profiledRawJointFrozenEntryRowSelected control := by
  simp [profiledRawJointFrozenEntryRowSelected,
    profiledRawJointFrozenEntryRowRecv]

@[simp] theorem profiledRawJointFrozenEntryRowRecv_entryRow
    (control : ProfiledRawJointFrozenEntryRowControl) :
    (profiledRawJointFrozenEntryRowRecv control).entryRow =
      profiledRawJointFrozenEntryRowSelected control := by
  rfl

@[simp] theorem profiledRawJointFrozenEntryRowNoRecv_entryRow
    (control : ProfiledRawJointFrozenEntryRowControl) :
    (profiledRawJointFrozenEntryRowNoRecv control).entryRow =
      control.entryRow := by
  rfl

/-- Reachability invariant needed by the repaired controller. -/
def ProfiledRawJointFrozenEntryRowInvariant
    (control : ProfiledRawJointFrozenEntryRowControl) : Prop :=
  control.entryRow = .first

theorem profiledRawJointFrozenEntryRowInvariant_initial :
    ProfiledRawJointFrozenEntryRowInvariant
      profiledRawJointFrozenEntryRowInitial := by
  rfl

theorem ProfiledRawJointFrozenEntryRowInvariant.recv
    {control : ProfiledRawJointFrozenEntryRowControl}
    (hcontrol : ProfiledRawJointFrozenEntryRowInvariant control) :
    ProfiledRawJointFrozenEntryRowInvariant
      (profiledRawJointFrozenEntryRowRecv control) := by
  unfold ProfiledRawJointFrozenEntryRowInvariant at hcontrol ⊢
  simp [profiledRawJointFrozenEntryRowRecv,
    profiledRawJointFrozenEntryRowSelected, hcontrol]

theorem ProfiledRawJointFrozenEntryRowInvariant.noRecv
    {control : ProfiledRawJointFrozenEntryRowControl}
    (hcontrol : ProfiledRawJointFrozenEntryRowInvariant control) :
    ProfiledRawJointFrozenEntryRowInvariant
      (profiledRawJointFrozenEntryRowNoRecv control) := by
  exact hcontrol

theorem ProfiledRawJointFrozenEntryRowInvariant.selected
    {control : ProfiledRawJointFrozenEntryRowControl}
    (hcontrol : ProfiledRawJointFrozenEntryRowInvariant control) :
    profiledRawJointFrozenEntryRowSelected control = .first := by
  unfold ProfiledRawJointFrozenEntryRowInvariant at hcontrol
  simp [profiledRawJointFrozenEntryRowSelected, hcontrol]

/-! ## Exact fixed-row DPA scan -/

/-- Current/minimum projection of the old two-row right scan on the reachable
frozen row. -/
def profiledRawJointRightFrozenFirstStateMin
    (code : A.State × A.State)
    (lambda : ProcOnePairedRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (past : List (In₂ × In₁)) : A.State × A.State :=
  let scan := pairedRightScanAfter A code lambda past
  (scan.1.1, scan.2.1)

/-- Left projection. -/
def profiledRawJointLeftFrozenFirstStateMin
    (code : A.State × A.State)
    (lambda : ProcTwoPairedLeftLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (past : List (In₁ × In₂)) : A.State × A.State :=
  let scan := pairedLeftScanAfter A code lambda past
  (scan.1.1, scan.2.1)

theorem profiledRawJointRightFrozenFirstStateMin_eq_blockEndAndMin
    (code : A.State × A.State)
    (lambda : ProcOnePairedRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (past : List (In₂ × In₁)) :
    profiledRawJointRightFrozenFirstStateMin A code lambda past =
      blockEndAndMin A code.1 (lambda.leftWord past) := by
  unfold profiledRawJointRightFrozenFirstStateMin pairedRightScanAfter
    pairedRightSuccessorCode
  apply Prod.ext
  · exact (blockEndAndMin_fst_eq_foldl A _ _).symm
  · rfl

theorem profiledRawJointLeftFrozenFirstStateMin_eq_blockEndAndMin
    (code : A.State × A.State)
    (lambda : ProcTwoPairedLeftLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (past : List (In₁ × In₂)) :
    profiledRawJointLeftFrozenFirstStateMin A code lambda past =
      blockEndAndMin A code.1 (lambda.rightWord past) := by
  unfold profiledRawJointLeftFrozenFirstStateMin pairedLeftScanAfter
    pairedLeftSuccessorCode
  apply Prod.ext
  · exact (blockEndAndMin_fst_eq_foldl A _ _).symm
  · rfl

/-! ## Existing semantic acceptance discharges the frozen lane -/

theorem PairedRightForeverAccepts.frozenFirst
    {code : A.State × A.State}
    {lambda : ProcOnePairedRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)}
    (hforever : PairedRightForeverAccepts A code lambda)
    (env : Nat → In₂ × In₁) :
    A.AcceptsFrom code.1
      (pairedRightOmegaWord lambda.blind lambda.informedLeft env) :=
  hforever.1 env

theorem PairedLeftForeverAccepts.frozenFirst
    {code : A.State × A.State}
    {lambda : ProcTwoPairedLeftLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)}
    (hforever : PairedLeftForeverAccepts A code lambda)
    (env : Nat → In₁ × In₂) :
    A.AcceptsFrom code.1
      (pairedLeftOmegaWord lambda.blind lambda.informedRight env) :=
  hforever.1 env

end DetParityAutomaton

end DistributedSynthesis
