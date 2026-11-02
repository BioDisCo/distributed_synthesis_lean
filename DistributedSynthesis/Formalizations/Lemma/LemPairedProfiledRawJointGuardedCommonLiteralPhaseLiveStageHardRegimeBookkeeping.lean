/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralPhaseLiveStageFixedTailBookkeeping
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointUnitCanonicalMemberTraceAlignment

/-!
# Canonical hard-regime bookkeeping for the phase/live-stage trace

The two hard physical regimes use the repository's canonical operational
close schedule.  Its graph arithmetic, productive cuts, charged slices, and
parity transfer are already proved.  A corrected local controller therefore
owes only the two fields of
`ProfiledRawJointGuardedCommonLiteralCrossCanonicalTraceAlignment`:

* the DPA state at every canonical cut is the scheduled query entry state;
* every literal record emitted before the close is the scheduled query
  record.

This file removes the remaining administrative inputs around those fields.
Strict-run termination for an arbitrary later base is derived automatically
from recurrent `.both` or persistent strict reversal.  A graph-split trace
invariant plus the two canonical alignment fields is converted to the
existing controller trace witness.  Finally the hard-regime bookkeeping is
combined with the live-stage fixed-tail bookkeeping to produce the complete
`FinitePairedPhysicalControllerLiteralCrossTraceExtraction`.

All regimes, bases, anchors, rows, schedules, and alignments below are
proof-side.  No executable endpoint receives any of them.
-/

namespace DistributedSynthesis

universe u v x y s w₁ w₂

/-! ## Strict-run termination survives an arbitrary finite shift -/

/-- Recurrent simultaneous rounds terminate every strict run after any
chosen physical base. -/
theorem operationalStrictRunsTerminate_physicalGraphTail_of_graphBothRecurrent
    {In₁ : Type u} {In₂ : Type v}
    (physicalEnv : EnvironmentSequence In₁ In₂)
    (hboth : GraphBothRecurrent (fun n ↦ (physicalEnv n).graph))
    (base : Nat) :
    OperationalStrictRunsTerminate
      (DetParityAutomaton.profiledRawJointPhysicalGraphTail physicalEnv
        base) := by
  apply operationalStrictRunsTerminate_of_graphBothRecurrent
  intro start
  rcases hboth (base + start) with ⟨m, hm, hgraph⟩
  refine ⟨m - base, ?_, ?_⟩
  · omega
  · have hbase : base ≤ m := by omega
    simpa [DetParityAutomaton.profiledRawJointPhysicalGraphTail,
      Nat.add_sub_of_le hbase] using hgraph

/-- Persistent reversal likewise terminates every shifted strict run. -/
theorem
    operationalStrictRunsTerminate_physicalGraphTail_of_persistentReversal
    {In₁ : Type u} {In₂ : Type v}
    (physicalEnv : EnvironmentSequence In₁ In₂)
    (hreversal :
      PersistentStrictReversalTail (fun n ↦ (physicalEnv n).graph))
    (base : Nat) :
    OperationalStrictRunsTerminate
      (DetParityAutomaton.profiledRawJointPhysicalGraphTail physicalEnv
        base) := by
  apply operationalStrictRunsTerminate_of_bothStrictDirectionsRecurrent
  constructor
  · intro start
    rcases hreversal.2.1 (base + start) with ⟨m, hm, hgraph⟩
    refine ⟨m - base, ?_, ?_⟩
    · omega
    · have hbase : base ≤ m := by omega
      simpa [DetParityAutomaton.profiledRawJointPhysicalGraphTail,
        Nat.add_sub_of_le hbase] using hgraph
  · intro start
    rcases hreversal.2.2 (base + start) with ⟨m, hm, hgraph⟩
    refine ⟨m - base, ?_, ?_⟩
    · omega
    · have hbase : base ≤ m := by omega
      simpa [DetParityAutomaton.profiledRawJointPhysicalGraphTail,
        Nat.add_sub_of_le hbase] using hgraph

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

variable (strategy : StrategyPair In₁ In₂ Out₁ Out₂)

private abbrev Controller :=
  FinitePairedPhysicalController.{u, v, x, y, w₁, w₂}
    In₁ In₂ Out₁ Out₂

/-! ## Actual canonical alignment to controller trace witness -/

/-- A graph-split trace invariant and a canonical alignment on the actual
controller word produce the repository's reference-word trace witness.

The only work is transporting the two alignment fields across the generic
trace/reference-word equality. -/
noncomputable def
    finitePairedPhysicalControllerCanonicalLiteralCrossTraceWitness_of_alignment
    (controller : Controller (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂))
    (physicalEnv : EnvironmentSequence In₁ In₂)
    (trace : controller.LiteralCrossGraphTraceInvariant physicalEnv)
    (base : Nat)
    (anchor : ProfiledRawJointGuardedCommonTailPolicyAnchor A strategy)
    (hterm : OperationalStrictRunsTerminate
      (profiledRawJointPhysicalGraphTail physicalEnv base))
    (rowAt : Nat → PairedEntryRow)
    (alignment :
      ProfiledRawJointGuardedCommonLiteralCrossCanonicalTraceAlignment A
        strategy anchor.initial anchor.policy anchor.bank
          controller.globalMachine controller.globalOutputOne
            controller.globalOutputTwo physicalEnv base hterm anchor.seed
              rowAt) :
    FinitePairedPhysicalControllerCanonicalLiteralCrossTraceWitness A strategy
      controller physicalEnv where
  trace := trace
  base := base
  anchor := anchor
  hterm := hterm
  rowAt := rowAt
  referenceEntryStateAt := by
    intro k
    rw [← trace.globalMachineTraceWord_eq_referenceWord controller]
    exact alignment.entryStateAt k
  referenceEmittedRoundAt := by
    intro k
    dsimp only
    intro j hj
    rw [← trace.globalMachineTraceWord_eq_referenceWord controller]
    exact alignment.emittedRoundAt k j hj

/-! ## Minimal data in the recurrent-`.both` branch -/

/-- All administrative hard-regime data with the productive-cut proof
removed.  The corrected trace owes only its graph-split invariant and the two
canonical pointwise alignment fields stored in `alignment`. -/
structure LiteralCombinedFreshPhaseLiveRecurrentTraceBookkeeping
    (controller : Controller (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂))
    (physicalEnv : EnvironmentSequence In₁ In₂)
    (hboth : GraphBothRecurrent (fun n ↦ (physicalEnv n).graph)) where
  trace : controller.LiteralCrossGraphTraceInvariant physicalEnv
  base : Nat
  anchor : ProfiledRawJointGuardedCommonTailPolicyAnchor A strategy
  rowAt : Nat → PairedEntryRow
  alignment :
    ProfiledRawJointGuardedCommonLiteralCrossCanonicalTraceAlignment A
      strategy anchor.initial anchor.policy anchor.bank
        controller.globalMachine controller.globalOutputOne
          controller.globalOutputTwo physicalEnv base
            (operationalStrictRunsTerminate_physicalGraphTail_of_graphBothRecurrent
              physicalEnv hboth base) anchor.seed rowAt

namespace LiteralCombinedFreshPhaseLiveRecurrentTraceBookkeeping

/-- The recurrent bookkeeping is already the complete hard-regime trace
witness consumed by the global extraction. -/
noncomputable def toTraceWitness
    {controller : Controller (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂)}
    {physicalEnv : EnvironmentSequence In₁ In₂}
    {hboth : GraphBothRecurrent (fun n ↦ (physicalEnv n).graph)}
    (bookkeeping :
      LiteralCombinedFreshPhaseLiveRecurrentTraceBookkeeping A strategy
        controller physicalEnv hboth) :
    FinitePairedPhysicalControllerCanonicalLiteralCrossTraceWitness A strategy
      controller physicalEnv :=
  finitePairedPhysicalControllerCanonicalLiteralCrossTraceWitness_of_alignment
    A strategy controller physicalEnv bookkeeping.trace bookkeeping.base
      bookkeeping.anchor
      (operationalStrictRunsTerminate_physicalGraphTail_of_graphBothRecurrent
        physicalEnv hboth bookkeeping.base)
      bookkeeping.rowAt bookkeeping.alignment

end LiteralCombinedFreshPhaseLiveRecurrentTraceBookkeeping

/-! ## Recurrent bookkeeping with checker states derived -/

/-- Recurrent hard-regime data stated without an `entryStateAt` field.
The close member fixes every row after the initial cut, and the exact open
slices plus closing records force all later checker states by induction. -/
structure LiteralCombinedFreshPhaseLiveRecurrentMemberSliceBookkeeping
    (controller : Controller (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂))
    (physicalEnv : EnvironmentSequence In₁ In₂)
    (hboth : GraphBothRecurrent (fun n ↦ (physicalEnv n).graph)) where
  trace : controller.LiteralCrossGraphTraceInvariant physicalEnv
  base : Nat
  anchor : ProfiledRawJointGuardedCommonTailPolicyAnchor A strategy
  initialRow : PairedEntryRow
  memberAt : Nat → Bool
  slices :
    ProfiledRawJointUnitCanonicalMemberSliceAlignment A strategy
      anchor.initial anchor.policy anchor.bank controller.globalMachine
        controller.globalOutputOne controller.globalOutputTwo physicalEnv base
          (operationalStrictRunsTerminate_physicalGraphTail_of_graphBothRecurrent
            physicalEnv hboth base)
          anchor.seed initialRow memberAt

namespace LiteralCombinedFreshPhaseLiveRecurrentMemberSliceBookkeeping

/-- The member-aware close induction discharges the old canonical checker
alignment wholesale. -/
noncomputable def toTraceBookkeeping
    {controller : Controller (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂)}
    {physicalEnv : EnvironmentSequence In₁ In₂}
    {hboth : GraphBothRecurrent (fun n ↦ (physicalEnv n).graph)}
    (bookkeeping :
      LiteralCombinedFreshPhaseLiveRecurrentMemberSliceBookkeeping A strategy
        controller physicalEnv hboth) :
    LiteralCombinedFreshPhaseLiveRecurrentTraceBookkeeping A strategy
      controller physicalEnv hboth where
  trace := bookkeeping.trace
  base := bookkeeping.base
  anchor := bookkeeping.anchor
  rowAt := profiledRawJointCanonicalMemberRows bookkeeping.initialRow
    bookkeeping.memberAt
  alignment := bookkeeping.slices.toCanonicalTraceAlignment A strategy
    bookkeeping.anchor.initial bookkeeping.anchor.policy bookkeeping.anchor.bank

/-- Exact member slices therefore imply acceptance of the actual recurrent
controller word. -/
theorem accepts
    {controller : Controller (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂)}
    {physicalEnv : EnvironmentSequence In₁ In₂}
    {hboth : GraphBothRecurrent (fun n ↦ (physicalEnv n).graph)}
    (bookkeeping :
      LiteralCombinedFreshPhaseLiveRecurrentMemberSliceBookkeeping A strategy
        controller physicalEnv hboth) :
    A.Accepts
      (controller.globalMachine.globalMachineTraceWord
        controller.globalOutputOne controller.globalOutputTwo physicalEnv) := by
  exact
    (bookkeeping.slices.toCanonicalTraceAlignment A strategy
      bookkeeping.anchor.initial bookkeeping.anchor.policy
        bookkeeping.anchor.bank).accepts A strategy
          bookkeeping.anchor.seed_state

end LiteralCombinedFreshPhaseLiveRecurrentMemberSliceBookkeeping

/-! ## Minimal data in the persistent-reversal branch -/

structure LiteralCombinedFreshPhaseLiveReversalTraceBookkeeping
    (controller : Controller (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂))
    (physicalEnv : EnvironmentSequence In₁ In₂)
    (hreversal :
      PersistentStrictReversalTail (fun n ↦ (physicalEnv n).graph)) where
  trace : controller.LiteralCrossGraphTraceInvariant physicalEnv
  base : Nat
  anchor : ProfiledRawJointGuardedCommonTailPolicyAnchor A strategy
  rowAt : Nat → PairedEntryRow
  alignment :
    ProfiledRawJointGuardedCommonLiteralCrossCanonicalTraceAlignment A
      strategy anchor.initial anchor.policy anchor.bank
        controller.globalMachine controller.globalOutputOne
          controller.globalOutputTwo physicalEnv base
            (operationalStrictRunsTerminate_physicalGraphTail_of_persistentReversal
              physicalEnv hreversal base) anchor.seed rowAt

namespace LiteralCombinedFreshPhaseLiveReversalTraceBookkeeping

noncomputable def toTraceWitness
    {controller : Controller (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂)}
    {physicalEnv : EnvironmentSequence In₁ In₂}
    {hreversal :
      PersistentStrictReversalTail (fun n ↦ (physicalEnv n).graph)}
    (bookkeeping :
      LiteralCombinedFreshPhaseLiveReversalTraceBookkeeping A strategy
        controller physicalEnv hreversal) :
    FinitePairedPhysicalControllerCanonicalLiteralCrossTraceWitness A strategy
      controller physicalEnv :=
  finitePairedPhysicalControllerCanonicalLiteralCrossTraceWitness_of_alignment
    A strategy controller physicalEnv bookkeeping.trace bookkeeping.base
      bookkeeping.anchor
      (operationalStrictRunsTerminate_physicalGraphTail_of_persistentReversal
        physicalEnv hreversal bookkeeping.base)
      bookkeeping.rowAt bookkeeping.alignment

end LiteralCombinedFreshPhaseLiveReversalTraceBookkeeping

/-! ## Both hard branches as one propositional obligation -/

/-- Hard-regime bookkeeping for one controller/environment.  Each branch is
`Nonempty` so this interface remains a proposition and does not add a runtime
branch selector to the controller. -/
structure LiteralCombinedFreshPhaseLiveHardRegimeBookkeeping
    (controller : Controller (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂))
    (physicalEnv : EnvironmentSequence In₁ In₂) : Prop where
  recurrent :
    ∀ hboth : GraphBothRecurrent (fun n ↦ (physicalEnv n).graph),
      Nonempty
        (LiteralCombinedFreshPhaseLiveRecurrentTraceBookkeeping A strategy
          controller physicalEnv hboth)
  reversal :
    ∀ hreversal :
        PersistentStrictReversalTail (fun n ↦ (physicalEnv n).graph),
      Nonempty
        (LiteralCombinedFreshPhaseLiveReversalTraceBookkeeping A strategy
          controller physicalEnv hreversal)

namespace LiteralCombinedFreshPhaseLiveHardRegimeBookkeeping

/-- Eliminate the propositional wrapper only at the proof-side extraction
boundary. -/
noncomputable def recurrentTrace
    {controller : Controller (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂)}
    {physicalEnv : EnvironmentSequence In₁ In₂}
    (bookkeeping :
      LiteralCombinedFreshPhaseLiveHardRegimeBookkeeping A strategy controller
        physicalEnv)
    (hboth : GraphBothRecurrent (fun n ↦ (physicalEnv n).graph)) :
    FinitePairedPhysicalControllerCanonicalLiteralCrossTraceWitness A strategy
      controller physicalEnv :=
  (Classical.choice (bookkeeping.recurrent hboth)).toTraceWitness A strategy

noncomputable def reversalTrace
    {controller : Controller (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂)}
    {physicalEnv : EnvironmentSequence In₁ In₂}
    (bookkeeping :
      LiteralCombinedFreshPhaseLiveHardRegimeBookkeeping A strategy controller
        physicalEnv)
    (hreversal :
      PersistentStrictReversalTail (fun n ↦ (physicalEnv n).graph)) :
    FinitePairedPhysicalControllerCanonicalLiteralCrossTraceWitness A strategy
      controller physicalEnv :=
  (Classical.choice (bookkeeping.reversal hreversal)).toTraceWitness A strategy

end LiteralCombinedFreshPhaseLiveHardRegimeBookkeeping

/-! ## Complete extraction from the two bookkeeping packages -/

variable
  (hwin : ∀ env : EnvironmentSequence In₁ In₂,
    A.Accepts (execution strategy env))

private abbrev CommonPoint :=
  ProfiledRawJointGuardedCommonSemanticPoint A strategy

private abbrev CrossValid :=
  ProfiledRawJointGuardedCommonLiteralCrossExtraValid A strategy hwin

namespace ProfiledRawJointGuardedCommonDecoratedPolicyPackage

variable {initial : CommonPoint A strategy}

private abbrev Package :=
  ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy hwin initial
    (CrossValid A strategy hwin)

/-- The fixed-stage and canonical hard-regime bookkeeping together close all
four fields of the global literal-cross extraction. -/
noncomputable def
    LiteralCombinedFreshPhaseLiveStageFixedTailBookkeeping.toLiteralCrossTraceExtraction_of_hardRegimes
    (package : Package A strategy hwin (initial := initial))
    {controller : Controller (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂)}
    {physicalEnv : EnvironmentSequence In₁ In₂}
    (fixed :
      LiteralCombinedFreshPhaseLiveStageFixedTailBookkeeping A strategy hwin
        package controller physicalEnv)
    (hard : LiteralCombinedFreshPhaseLiveHardRegimeBookkeeping A strategy
      controller physicalEnv) :
    FinitePairedPhysicalControllerLiteralCrossTraceExtraction A strategy
      controller physicalEnv :=
  fixed.toLiteralCrossTraceExtraction A strategy hwin
    (hard.recurrentTrace A strategy) (hard.reversalTrace A strategy)

end ProfiledRawJointGuardedCommonDecoratedPolicyPackage

end

end DetParityAutomaton

end DistributedSynthesis
