/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemProfiledRawJointFiniteCodeFailFast
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralPhaseLiveCodeLineageCutAudit

/-!
# Depth-two audit of the common-linked clock

The common-linked successor follows a literal `.both` child at every physical
input.  A right seam table target of positive depth instead follows the
literal one-sided history through its strict prefix and closes with `.both`.
This file checks the first nontrivial instance, a strict prefix of length two.

The difference is semantic, not merely a choice of representative.  A finite
strategy which outputs `true` after two consecutive no-receive observations
separates the right initial-action profiles of the two literal worlds.  Hence
their incidence codes differ.  Consequently the common-linked successor may
be used for the depth-zero seam law, but it cannot provide the positive-depth
table-target lineage without an additional block-clock construction.

This is a proof-side audit only.  The strategy is uniform in its local view;
no process is told the graph, the active orientation, or which process is the
strict leader.
-/

namespace DistributedSynthesis

namespace DetParityAutomaton

noncomputable section

private abbrev linkedClockAuditDPA := rawJointCodeCollisionDPA

/-- Number of consecutive no-receive observations at the end of a local
view.  A receive resets the counter because its predecessor is inspected
recursively and the current constructor is not `noRecv`. -/
private def linkedClockAuditNoRecvCount : {p : Proc} →
    View Unit Unit p → Nat
  | _, .empty _ => 0
  | _, .recv previous _ _ _ => linkedClockAuditNoRecvCount previous
  | _, .noRecv previous _ => linkedClockAuditNoRecvCount previous + 1

/-- A finite local-view strategy separating two strict rounds from three
simultaneous rounds. -/
private def linkedClockAuditStrategy : StrategyPair Unit Unit Bool Bool where
  one := fun _ ↦ false
  two := fun view ↦ decide (2 ≤ linkedClockAuditNoRecvCount view)

private def linkedClockAuditPoint :
    ProfiledRawJointGuardedCommonSemanticPoint linkedClockAuditDPA
      linkedClockAuditStrategy :=
  ⟨profiledRawJointInitialCommonBaseWorld linkedClockAuditDPA
      linkedClockAuditStrategy () (), ((), ())⟩

/-- The literal world used by a right seam target after two strict-left
rounds and its simultaneous closing round. -/
private def linkedClockAuditStrictWorld :
    ProfiledRawJointCommonBaseWorld linkedClockAuditDPA
      linkedClockAuditStrategy :=
  let sourceWorld := linkedClockAuditPoint.world linkedClockAuditDPA
    linkedClockAuditStrategy
  profiledRawLeftCommonBaseWorld linkedClockAuditDPA
    (sourceWorld.procTwoMember linkedClockAuditDPA) .both
    [((), ()), ((), ())] ((), ())

/-- Three literal common-linked successors from the same initial point. -/
private def linkedClockAuditCommonPoint :=
  ((linkedClockAuditPoint.step linkedClockAuditDPA linkedClockAuditStrategy
      ((), ())).step linkedClockAuditDPA linkedClockAuditStrategy ((), ()))
    |>.step linkedClockAuditDPA linkedClockAuditStrategy ((), ())

private def linkedClockAuditStrictCode :
    ProfiledRawJointIncidenceCode linkedClockAuditDPA (I := Unit) :=
  (profiledRawJointCommonWorldFamily linkedClockAuditDPA
    linkedClockAuditStrictWorld).incidenceCode linkedClockAuditDPA

private def linkedClockAuditCommonCode :
    ProfiledRawJointIncidenceCode linkedClockAuditDPA (I := Unit) :=
  (profiledRawJointCommonWorldFamily linkedClockAuditDPA
    (linkedClockAuditCommonPoint.world linkedClockAuditDPA
      linkedClockAuditStrategy)).incidenceCode linkedClockAuditDPA

/-- The strict-block clock makes the right process output `true`. -/
theorem literalStrictBlockLinkedClockAudit_strict_profile :
    ((linkedClockAuditStrictWorld.procOneSlot linkedClockAuditDPA).2
      ((), ())) = true := by
  decide

/-- The common-linked clock makes the same right process output `false`. -/
theorem literalStrictBlockLinkedClockAudit_common_profile :
    (((linkedClockAuditCommonPoint.world linkedClockAuditDPA
      linkedClockAuditStrategy).procOneSlot linkedClockAuditDPA).2
        ((), ())) = false := by
  decide

/-- At strict depth two, the literal seam world and the three-step
common-linked world already have different finite incidence codes. -/
theorem literalStrictBlockLinkedClockAudit_incidenceCode_ne :
    linkedClockAuditStrictCode ≠ linkedClockAuditCommonCode := by
  intro hcode
  have hright := congrArg (fun code => code.family.right ()) hcode
  change
    some (linkedClockAuditStrictWorld.procOneSlot linkedClockAuditDPA) =
      some ((linkedClockAuditCommonPoint.world linkedClockAuditDPA
        linkedClockAuditStrategy).procOneSlot linkedClockAuditDPA) at hright
  have hslot :
      linkedClockAuditStrictWorld.procOneSlot linkedClockAuditDPA =
        (linkedClockAuditCommonPoint.world linkedClockAuditDPA
          linkedClockAuditStrategy).procOneSlot linkedClockAuditDPA :=
    Option.some.inj hright
  have hprofile := congrArg (fun slot => slot.2 ((), ())) hslot
  change
    ((linkedClockAuditStrictWorld.procOneSlot linkedClockAuditDPA).2
        ((), ())) =
      (((linkedClockAuditCommonPoint.world linkedClockAuditDPA
        linkedClockAuditStrategy).procOneSlot linkedClockAuditDPA).2
          ((), ())) at hprofile
  rw [literalStrictBlockLinkedClockAudit_strict_profile,
    literalStrictBlockLinkedClockAudit_common_profile] at hprofile
  contradiction

end

end DetParityAutomaton

end DistributedSynthesis
