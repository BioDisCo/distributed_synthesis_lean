/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteRootFamilyNarrowing
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledEndToEndOverlapInvariant

/-!
# Restarted monitor roots of the one-policy end-to-end phases

Simultaneous family narrowing needs a finite descriptor for the exact monitor
currently carried by an oriented phase.  The old profiled root-family adapter
cannot be reused directly: its recurrent roots select a fresh feasible policy,
whereas the end-to-end construction retains one fixed policy below its initial
guarded child.

The source types below therefore have exactly three finite cases per
orientation: the exceptional first block, a recurrent block descended from an
initial-left boundary, and one descended from an initial-right boundary.  A
restart root is only such a source paired with the current state of its monitor.
It contains no owner-controller state, staged successor, anchor, or strict-
leader signal.
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

/-- The three possible monitor sources of a right-oriented end-to-end phase. -/
inductive EndToEndRightMonitorSource where
  | first (key : EndToEndInitialLeftBoundaryKey A package)
  | rightOrigin
      (source : EndToEndRightOriginRecurrentRightMacro A package)
  | leftOrigin
      (source : EndToEndLeftOriginRecurrentRightMacro A package)

/-- The three possible monitor sources of a left-oriented end-to-end phase. -/
inductive EndToEndLeftMonitorSource where
  | first (key : EndToEndInitialRightBoundaryKey A package)
  | rightOrigin
      (source : EndToEndRightOriginRecurrentLeftMacro A package)
  | leftOrigin
      (source : EndToEndLeftOriginRecurrentLeftMacro A package)

noncomputable instance : Fintype (EndToEndRightMonitorSource A package) := by
  classical
  let Rep := EndToEndInitialLeftBoundaryKey A package ⊕
    EndToEndRightOriginRecurrentRightMacro A package ⊕
      EndToEndLeftOriginRecurrentRightMacro A package
  let e : EndToEndRightMonitorSource A package ≃ Rep :=
    { toFun := fun source =>
        match source with
        | .first key => .inl key
        | .rightOrigin recurrent => .inr (.inl recurrent)
        | .leftOrigin recurrent => .inr (.inr recurrent)
      invFun := fun source =>
        match source with
        | .inl key => .first key
        | .inr (.inl recurrent) => .rightOrigin recurrent
        | .inr (.inr recurrent) => .leftOrigin recurrent
      left_inv := by intro source; cases source <;> rfl
      right_inv := by
        intro source
        rcases source with first | (right | left) <;> rfl }
  exact Fintype.ofEquiv Rep e.symm

noncomputable instance : Fintype (EndToEndLeftMonitorSource A package) := by
  classical
  let Rep := EndToEndInitialRightBoundaryKey A package ⊕
    EndToEndRightOriginRecurrentLeftMacro A package ⊕
      EndToEndLeftOriginRecurrentLeftMacro A package
  let e : EndToEndLeftMonitorSource A package ≃ Rep :=
    { toFun := fun source =>
        match source with
        | .first key => .inl key
        | .rightOrigin recurrent => .inr (.inl recurrent)
        | .leftOrigin recurrent => .inr (.inr recurrent)
      invFun := fun source =>
        match source with
        | .inl key => .first key
        | .inr (.inl recurrent) => .rightOrigin recurrent
        | .inr (.inr recurrent) => .leftOrigin recurrent
      left_inv := by intro source; cases source <;> rfl
      right_inv := by
        intro source
        rcases source with first | (right | left) <;> rfl }
  exact Fintype.ofEquiv Rep e.symm

noncomputable instance : DecidableEq (EndToEndRightMonitorSource A package) :=
  Classical.decEq _

noncomputable instance : DecidableEq (EndToEndLeftMonitorSource A package) :=
  Classical.decEq _

/-- Base monitor selected by a right-oriented source. -/
noncomputable abbrev EndToEndRightMonitorSource.monitor :
    EndToEndRightMonitorSource A package →
      BlockRecordMonitor In₂ In₁ (ProfiledRightReceiverOutput A) Out₁
  | .first key => endToEndFirstRightMonitor.{u, v, x, y, s, 1}
      A package key
  | .rightOrigin source =>
      endToEndGuardedRightRecurrentRightMonitor A source.2
  | .leftOrigin source =>
      endToEndGuardedLeftRecurrentRightMonitor A source.2

/-- Base monitor selected by a left-oriented source. -/
noncomputable abbrev EndToEndLeftMonitorSource.monitor :
    EndToEndLeftMonitorSource A package →
      BlockRecordMonitor In₁ In₂ (ProfiledLeftReceiverOutput A) Out₂
  | .first key => endToEndFirstLeftMonitor.{u, v, x, y, s, 1}
      A package key
  | .rightOrigin source =>
      endToEndGuardedRightRecurrentLeftMonitor A source.2
  | .leftOrigin source =>
      endToEndGuardedLeftRecurrentLeftMonitor A source.2

/-- A right monitor source paired with its exact current monitor state. -/
abbrev EndToEndRightRestartRoot :=
  Σ source : EndToEndRightMonitorSource A package,
    (source.monitor A package).State

/-- Left mirror. -/
abbrev EndToEndLeftRestartRoot :=
  Σ source : EndToEndLeftMonitorSource A package,
    (source.monitor A package).State

noncomputable instance : Fintype (EndToEndRightRestartRoot A package) := by
  classical
  infer_instance

noncomputable instance : Fintype (EndToEndLeftRestartRoot A package) := by
  classical
  infer_instance

noncomputable instance : DecidableEq (EndToEndRightRestartRoot A package) :=
  Classical.decEq _

noncomputable instance : DecidableEq (EndToEndLeftRestartRoot A package) :=
  Classical.decEq _

/-- Restart the selected right monitor at the state stored by the root. -/
noncomputable def endToEndRightRestartRootMonitor
    (root : EndToEndRightRestartRoot A package) :
    BlockRecordMonitor In₂ In₁ (ProfiledRightReceiverOutput A) Out₁ :=
  (root.1.monitor A package).restartAt root.2

/-- Left mirror. -/
noncomputable def endToEndLeftRestartRootMonitor
    (root : EndToEndLeftRestartRoot A package) :
    BlockRecordMonitor In₁ In₂ (ProfiledLeftReceiverOutput A) Out₂ :=
  (root.1.monitor A package).restartAt root.2

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem endToEndRightRestartRootMonitor_initial
    (root : EndToEndRightRestartRoot A package) :
    (endToEndRightRestartRootMonitor A package root).initial = root.2 :=
  rfl

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem endToEndLeftRestartRootMonitor_initial
    (root : EndToEndLeftRestartRoot A package) :
    (endToEndLeftRestartRootMonitor A package root).initial = root.2 :=
  rfl

/-- Extract the exact restarted right monitor from a proof-level phase. -/
def endToEndRightRestartRootOfPhase
    (phase : EndToEndMatchedPhase A package) (hright : phase.IsRight) :
    EndToEndRightRestartRoot A package := by
  cases phase with
  | firstRight owner receiver sameSource =>
      exact ⟨.first receiver.1, receiver.2.2.1⟩
  | firstLeft receiver owner sameSource =>
      simp [EndToEndMatchedPhase.IsRight] at hright
  | rightOriginRight owner receiver sameSource =>
      exact ⟨.rightOrigin receiver.1, receiver.2.2.1⟩
  | rightOriginLeft receiver owner sameSource =>
      simp [EndToEndMatchedPhase.IsRight] at hright
  | leftOriginRight owner receiver sameSource =>
      exact ⟨.leftOrigin receiver.1, receiver.2.2.1⟩
  | leftOriginLeft receiver owner sameSource =>
      simp [EndToEndMatchedPhase.IsRight] at hright

/-- Extract the exact restarted left monitor from a proof-level phase. -/
def endToEndLeftRestartRootOfPhase
    (phase : EndToEndMatchedPhase A package) (hleft : phase.IsLeft) :
    EndToEndLeftRestartRoot A package := by
  cases phase with
  | firstRight owner receiver sameSource =>
      simp [EndToEndMatchedPhase.IsLeft] at hleft
  | firstLeft receiver owner sameSource =>
      exact ⟨.first receiver.1, receiver.2.2.1⟩
  | rightOriginRight owner receiver sameSource =>
      simp [EndToEndMatchedPhase.IsLeft] at hleft
  | rightOriginLeft receiver owner sameSource =>
      exact ⟨.rightOrigin receiver.1, receiver.2.2.1⟩
  | leftOriginRight owner receiver sameSource =>
      simp [EndToEndMatchedPhase.IsLeft] at hleft
  | leftOriginLeft receiver owner sameSource =>
      exact ⟨.leftOrigin receiver.1, receiver.2.2.1⟩

/-! Constructor equations make the adapter convenient for the later family
table installation proof. -/

@[simp] theorem endToEndRightRestartRootOfPhase_firstRight
    (owner : EndToEndGuardedFirstRightOwnerControl A package)
    (receiver : EndToEndGuardedFirstRightReceiverControl A package)
    (sameSource : owner.1 = receiver.1) :
    endToEndRightRestartRootOfPhase A package
        (.firstRight owner receiver sameSource) trivial =
      ⟨.first receiver.1, receiver.2.2.1⟩ :=
  rfl

@[simp] theorem endToEndRightRestartRootOfPhase_rightOriginRight
    (owner : EndToEndRightOriginRecurrentRightOwnerControl A package)
    (receiver : EndToEndRightOriginRecurrentRightReceiverControl A package)
    (sameSource : owner.1 = receiver.1) :
    endToEndRightRestartRootOfPhase A package
        (.rightOriginRight owner receiver sameSource) trivial =
      ⟨.rightOrigin receiver.1, receiver.2.2.1⟩ :=
  rfl

@[simp] theorem endToEndRightRestartRootOfPhase_leftOriginRight
    (owner : EndToEndLeftOriginRecurrentRightOwnerControl A package)
    (receiver : EndToEndLeftOriginRecurrentRightReceiverControl A package)
    (sameSource : owner.1 = receiver.1) :
    endToEndRightRestartRootOfPhase A package
        (.leftOriginRight owner receiver sameSource) trivial =
      ⟨.leftOrigin receiver.1, receiver.2.2.1⟩ :=
  rfl

@[simp] theorem endToEndLeftRestartRootOfPhase_firstLeft
    (receiver : EndToEndGuardedFirstLeftReceiverControl A package)
    (owner : EndToEndGuardedFirstLeftOwnerControl A package)
    (sameSource : receiver.1 = owner.1) :
    endToEndLeftRestartRootOfPhase A package
        (.firstLeft receiver owner sameSource) trivial =
      ⟨.first receiver.1, receiver.2.2.1⟩ :=
  rfl

@[simp] theorem endToEndLeftRestartRootOfPhase_rightOriginLeft
    (receiver : EndToEndRightOriginRecurrentLeftReceiverControl A package)
    (owner : EndToEndRightOriginRecurrentLeftOwnerControl A package)
    (sameSource : receiver.1 = owner.1) :
    endToEndLeftRestartRootOfPhase A package
        (.rightOriginLeft receiver owner sameSource) trivial =
      ⟨.rightOrigin receiver.1, receiver.2.2.1⟩ :=
  rfl

@[simp] theorem endToEndLeftRestartRootOfPhase_leftOriginLeft
    (receiver : EndToEndLeftOriginRecurrentLeftReceiverControl A package)
    (owner : EndToEndLeftOriginRecurrentLeftOwnerControl A package)
    (sameSource : receiver.1 = owner.1) :
    endToEndLeftRestartRootOfPhase A package
        (.leftOriginLeft receiver owner sameSource) trivial =
      ⟨.leftOrigin receiver.1, receiver.2.2.1⟩ :=
  rfl

end


end DetParityAutomaton

end DistributedSynthesis
