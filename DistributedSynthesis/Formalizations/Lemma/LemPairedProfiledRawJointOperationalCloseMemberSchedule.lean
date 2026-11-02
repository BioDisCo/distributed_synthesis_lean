/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOperationalCloseCuts
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleSuccessorOperationalClose

/-!
# The proof-side member schedule of operational close cuts

An operational close block has one Boolean closing interpretation.  The bit
is computed proof-side from the graph at the block start: `true` for a
simultaneous singleton close and `false` for a strict close.  The cut package
already proves that the closing graph equals the start graph, so this is also
exactly the bit of the physical closing round.

This module packages that schedule and proves its complete graph shape.  It
does not define or alter an endpoint transition.  In particular no graph,
orientation, hierarchy side, leader bit, history, or view is supplied to a
local controller.
-/

namespace DistributedSynthesis

/-- An operational cut package equipped with its canonical proof-side close
member.  The member is derived below rather than stored as independent data,
so it cannot drift from the physical graph word. -/
structure OperationalCloseMemberSchedule (graphs : Nat → Graph) where
  cutPackage : OperationalCloseCutPackage graphs

namespace OperationalCloseMemberSchedule

variable {graphs : Nat → Graph}

/-- The fresh close member of block `k`: simultaneous/closed is `true`, and
strict/open is `false`. -/
def closeMember (schedule : OperationalCloseMemberSchedule graphs)
    (k : Nat) : Bool :=
  if graphs (schedule.cutPackage.cuts k) = .both then true else false

@[simp] theorem closeMember_eq_true_iff
    (schedule : OperationalCloseMemberSchedule graphs) (k : Nat) :
    schedule.closeMember k = true ↔
      graphs (schedule.cutPackage.cuts k) = .both := by
  simp [closeMember]

@[simp] theorem closeMember_eq_false_iff
    (schedule : OperationalCloseMemberSchedule graphs) (k : Nat) :
    schedule.closeMember k = false ↔
      graphs (schedule.cutPackage.cuts k) ≠ .both := by
  simp [closeMember]

/-- The member can equivalently be read from the unique closing round, not
only from the block start. -/
theorem closing_graph_eq_both_iff_closeMember
    (schedule : OperationalCloseMemberSchedule graphs) (k : Nat) :
    graphs (schedule.cutPackage.cuts (k + 1) - 1) = .both ↔
      schedule.closeMember k = true := by
  rw [schedule.cutPackage.closing_graph_eq]
  exact (schedule.closeMember_eq_true_iff k).symm

/-- False is exactly the strict homogeneous-block case.  Every one of the
package's `openLength k` open rounds has the closing graph, and neither that
graph nor the closing graph is simultaneous.  The statement also covers a
strict singleton block, whose open length is zero. -/
theorem closeMember_eq_false_iff_strict_homogeneous
    (schedule : OperationalCloseMemberSchedule graphs) (k : Nat) :
    schedule.closeMember k = false ↔
      graphs (schedule.cutPackage.cuts (k + 1) - 1) ≠ .both ∧
        ∀ j, j < schedule.cutPackage.openLength k →
          graphs (schedule.cutPackage.cuts k + j) =
              graphs (schedule.cutPackage.cuts (k + 1) - 1) ∧
            graphs (schedule.cutPackage.cuts k + j) ≠ .both := by
  constructor
  · intro hmember
    have hstart : graphs (schedule.cutPackage.cuts k) ≠ .both :=
      (schedule.closeMember_eq_false_iff k).mp hmember
    have hclosing :
        graphs (schedule.cutPackage.cuts (k + 1) - 1) ≠ .both := by
      rw [schedule.cutPackage.closing_graph_eq]
      exact hstart
    refine ⟨hclosing, ?_⟩
    intro j hj
    have hopen := schedule.cutPackage.homogeneous k j hj
    have hclose := schedule.cutPackage.closing_graph_eq k
    exact ⟨hopen.trans hclose.symm,
      schedule.cutPackage.open_graph_ne_both k j hj⟩
  · rintro ⟨hclosing, _hhomogeneous⟩
    apply (schedule.closeMember_eq_false_iff k).mpr
    intro hstart
    apply hclosing
    rw [schedule.cutPackage.closing_graph_eq]
    exact hstart

/-- A true member is a zero-open singleton block.  The four conclusions make
the timing explicit: the next cut is one round later, the closing position is
the current cut, and that round is simultaneous. -/
theorem singleton_of_closeMember_eq_true
    (schedule : OperationalCloseMemberSchedule graphs) (k : Nat)
    (hmember : schedule.closeMember k = true) :
    schedule.cutPackage.openLength k = 0 ∧
      schedule.cutPackage.cuts (k + 1) =
        schedule.cutPackage.cuts k + 1 ∧
      schedule.cutPackage.cuts (k + 1) - 1 =
        schedule.cutPackage.cuts k ∧
      graphs (schedule.cutPackage.cuts (k + 1) - 1) = .both := by
  have hstart : graphs (schedule.cutPackage.cuts k) = .both :=
    (schedule.closeMember_eq_true_iff k).mp hmember
  have hzero := schedule.cutPackage.zero_open_of_both k hstart
  have hstep := schedule.cutPackage.step_eq k
  have hclosing := schedule.cutPackage.closing_graph_eq k
  refine ⟨hzero, ?_, ?_, ?_⟩
  · omega
  · omega
  · rw [hclosing]
    exact hstart

/-- Forget a member schedule and recover its cut package. -/
def ofCutPackage (cuts : OperationalCloseCutPackage graphs) :
    OperationalCloseMemberSchedule graphs :=
  ⟨cuts⟩

/-- Direct schedule in the recurrent-synchronization regime. -/
noncomputable def ofGraphBothRecurrent
    (graphs : Nat → Graph) (hboth : GraphBothRecurrent graphs) :
    OperationalCloseMemberSchedule graphs :=
  ⟨operationalCloseCutPackageOfGraphBothRecurrent graphs hboth⟩

/-- Direct schedule in the persistent strict-reversal regime. -/
noncomputable def ofPersistentStrictReversalTail
    (graphs : Nat → Graph) (h : PersistentStrictReversalTail graphs) :
    OperationalCloseMemberSchedule graphs :=
  ⟨operationalCloseCutPackageOfPersistentStrictReversalTail graphs h⟩

end OperationalCloseMemberSchedule

/-! ## The two concrete row names are one interpretation -/

namespace DetParityAutomaton

/-- The pending-handler row and the physical close-packet row are literally
the same interpretation of the acknowledged member. -/
theorem
    profiledRawJointHybridPhysicalCompatiblePendingRow_eq_scheduledCloseRowOfMember
    (member : Bool) :
    profiledRawJointHybridPhysicalCompatiblePendingRow member =
      profiledRawJointCloseRowOfMember member := by
  cases member <;> rfl

/-- Schedule-indexed row bridge used by the operational slice induction. -/
theorem OperationalCloseMemberSchedule.pendingRow_eq_closeRowOfMember
    {graphs : Nat → Graph}
    (schedule : OperationalCloseMemberSchedule graphs) (k : Nat) :
    profiledRawJointHybridPhysicalCompatiblePendingRow
        (schedule.closeMember k) =
      profiledRawJointCloseRowOfMember (schedule.closeMember k) :=
  profiledRawJointHybridPhysicalCompatiblePendingRow_eq_scheduledCloseRowOfMember
    _

end DetParityAutomaton

end DistributedSynthesis
