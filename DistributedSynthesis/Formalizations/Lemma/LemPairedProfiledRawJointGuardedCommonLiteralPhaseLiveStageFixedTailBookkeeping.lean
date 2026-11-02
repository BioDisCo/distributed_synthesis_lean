/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralStagedFixedTailAcceptance
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCrossControllerTraceInvariant
import DistributedSynthesis.Formalizations.Lemma.LemFiniteGlobalMachineReroot

/-!
# Trace bookkeeping for fixed tails selected by a live seam stage

The corrected phase/live-stage carrier eventually enters an ordinary
one-sided controller through a retained exact stage.  Once that local entry
has been identified, only two proof-side equalities remain:

* the original DPA run at the cut is the row-selected entry state stored by
  the stage; and
* the physical controller re-rooted at the cut emits the ordinary bank word
  selected by that same stage.

This file packages precisely those equalities.  Generic machine re-rooting
turns the second equality into an equality for the dropped original trace;
the fixed-tail theorem for the stage supplies `AcceptsFrom`; and the standard
run/drop equation yields parity at the original physical clock.

The final structure collects one such cut under each eventual fixed-side
hypothesis and fills the `fixedRight` and `fixedLeft` fields of the existing
literal-cross extraction.  No executable transition receives any of the
stage, row, cut, graph regime, or DPA-state data below.
-/

namespace DistributedSynthesis

universe u v x y s w₁ w₂

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

variable
  (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
  (hwin : ∀ env : EnvironmentSequence In₁ In₂,
    A.Accepts (execution strategy env))

private abbrev CommonPoint :=
  ProfiledRawJointGuardedCommonSemanticPoint A strategy

private abbrev CrossValid :=
  ProfiledRawJointGuardedCommonLiteralCrossExtraValid A strategy hwin

namespace ProfiledRawJointGuardedCommonDecoratedPolicyPackage

variable {initial : CommonPoint A strategy}

private abbrev Package (initial : CommonPoint A strategy) :=
  ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy hwin initial
    (CrossValid A strategy hwin)

private abbrev Controller :=
  FinitePairedPhysicalController.{u, v, x, y, w₁, w₂}
    In₁ In₂ Out₁ Out₂

private abbrev RightStage
    (package : Package A strategy hwin initial) :=
  ProfiledRawJointGuardedCommonLiteralRightSeamStage A strategy hwin package

private abbrev LeftStage
    (package : Package A strategy hwin initial) :=
  ProfiledRawJointGuardedCommonLiteralLeftSeamStage A strategy hwin package

private abbrev TraceWord
    (controller : Controller (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂))
    (physicalEnv : EnvironmentSequence In₁ In₂) :=
  controller.globalMachine.globalMachineTraceWord controller.globalOutputOne
    controller.globalOutputTwo physicalEnv

/-! ## One right-stage cut -/

/-- Exact bookkeeping at a cut where the corrected carrier has activated a
live right stage.

`rerootWord` is intentionally stated on the actual re-rooted global machine.
Thus a concrete corrected-state invariant can prove it by identifying the
two local recurrent controls; no separate equality of complete prefixes is
needed. -/
structure LiteralRightSeamStageTailCut
    (package : Package A strategy hwin initial)
    (controller : Controller (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂))
    (physicalEnv : EnvironmentSequence In₁ In₂) where
  start : Nat
  stage : RightStage A strategy hwin package
  row : PairedEntryRow
  inputs : Nat → In₂ × In₁
  dpaStateAt :
    A.run (TraceWord controller physicalEnv) start =
      pairedCodeStateForRow A row stage.root.slot.1.1
  rerootWord :
    (controller.globalMachine.reroot
        (controller.globalMachine.globalStateTrace physicalEnv start)
      ).globalMachineTraceWord controller.globalOutputOne
        controller.globalOutputTwo (OmegaWord.drop physicalEnv start) =
      fun n ↦ pairedRightRecordForRow row
        (profiledRawJointUnitRightPhysicalLetter A
          (profiledRawJointUnitRightPolicyOmegaPlay A
            (package.literalRightSeamTaggedChildControllerBank A strategy hwin
              stage.child) stage.root inputs n))

namespace LiteralRightSeamStageTailCut

/-- The cut's re-rooted-word equality is exactly an equality for the suffix
of the original physical trace. -/
theorem suffixWord
    {package : Package A strategy hwin initial}
    {controller : Controller (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂)}
    {physicalEnv : EnvironmentSequence In₁ In₂}
    (cut : LiteralRightSeamStageTailCut A strategy hwin package controller
      physicalEnv) :
    OmegaWord.drop (TraceWord controller physicalEnv) cut.start =
      fun n ↦ pairedRightRecordForRow cut.row
        (profiledRawJointUnitRightPhysicalLetter A
          (profiledRawJointUnitRightPolicyOmegaPlay A
            (package.literalRightSeamTaggedChildControllerBank A strategy hwin
              cut.stage.child) cut.stage.root cut.inputs n)) := by
  rw [← cut.rerootWord]
  exact
    (controller.globalMachine.reroot_globalMachineTraceWord_drop
      controller.globalOutputOne controller.globalOutputTwo physicalEnv
        cut.start).symm

/-- Acceptance of the actual dropped trace from the actual DPA state at the
cut. -/
theorem acceptsFrom_actual
    {package : Package A strategy hwin initial}
    {controller : Controller (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂)}
    {physicalEnv : EnvironmentSequence In₁ In₂}
    (cut : LiteralRightSeamStageTailCut A strategy hwin package controller
      physicalEnv) :
    A.AcceptsFrom
      (A.run (TraceWord controller physicalEnv) cut.start)
      (OmegaWord.drop (TraceWord controller physicalEnv) cut.start) := by
  rw [cut.dpaStateAt, cut.suffixWord A strategy hwin]
  cases cut.row with
  | first =>
      simpa [pairedCodeStateForRow] using
        package.literalRightSeamStage_physical_acceptsFrom A strategy hwin
          cut.stage .first cut.inputs
  | both =>
      simpa [pairedCodeStateForRow] using
        package.literalRightSeamStage_physical_acceptsFrom A strategy hwin
          cut.stage .both cut.inputs

/-- Min-even parity at the original physical clock, without restarting the
DPA checker. -/
theorem tailParity
    {package : Package A strategy hwin initial}
    {controller : Controller (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂)}
    {physicalEnv : EnvironmentSequence In₁ In₂}
    (cut : LiteralRightSeamStageTailCut A strategy hwin package controller
      physicalEnv) :
    NatSeqMinEvenParity (fun n ↦ A.priority
      (A.run (TraceWord controller physicalEnv) (cut.start + n))) := by
  let word := TraceWord controller physicalEnv
  have haccepts := cut.acceptsFrom_actual A strategy hwin
  have hparity :
      NatSeqMinEvenParity (fun n ↦ A.priority
        (A.runFrom (A.run word cut.start) (OmegaWord.drop word cut.start) n)) :=
    haccepts
  have heq :
      (fun n ↦ A.priority
        (A.runFrom (A.run word cut.start) (OmegaWord.drop word cut.start) n)) =
      (fun n ↦ A.priority (A.run word (cut.start + n))) := by
    funext n
    exact congrArg A.priority (A.runFrom_drop A.initial word cut.start n)
  rw [heq] at hparity
  exact hparity

end LiteralRightSeamStageTailCut

/-! ## One left-stage cut -/

/-- Mirror bookkeeping at a cut where a live left stage has been activated. -/
structure LiteralLeftSeamStageTailCut
    (package : Package A strategy hwin initial)
    (controller : Controller (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂))
    (physicalEnv : EnvironmentSequence In₁ In₂) where
  start : Nat
  stage : LeftStage A strategy hwin package
  row : PairedEntryRow
  inputs : Nat → In₁ × In₂
  dpaStateAt :
    A.run (TraceWord controller physicalEnv) start =
      pairedCodeStateForRow A row stage.root.slot.1.1
  rerootWord :
    (controller.globalMachine.reroot
        (controller.globalMachine.globalStateTrace physicalEnv start)
      ).globalMachineTraceWord controller.globalOutputOne
        controller.globalOutputTwo (OmegaWord.drop physicalEnv start) =
      fun n ↦ pairedLeftRecordForRow row
        (profiledRawJointUnitLeftPhysicalLetter A
          (profiledRawJointUnitLeftPolicyOmegaPlay A
            (package.literalLeftSeamTaggedChildControllerBank A strategy hwin
              stage.child) stage.root inputs n))

namespace LiteralLeftSeamStageTailCut

theorem suffixWord
    {package : Package A strategy hwin initial}
    {controller : Controller (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂)}
    {physicalEnv : EnvironmentSequence In₁ In₂}
    (cut : LiteralLeftSeamStageTailCut A strategy hwin package controller
      physicalEnv) :
    OmegaWord.drop (TraceWord controller physicalEnv) cut.start =
      fun n ↦ pairedLeftRecordForRow cut.row
        (profiledRawJointUnitLeftPhysicalLetter A
          (profiledRawJointUnitLeftPolicyOmegaPlay A
            (package.literalLeftSeamTaggedChildControllerBank A strategy hwin
              cut.stage.child) cut.stage.root cut.inputs n)) := by
  rw [← cut.rerootWord]
  exact
    (controller.globalMachine.reroot_globalMachineTraceWord_drop
      controller.globalOutputOne controller.globalOutputTwo physicalEnv
        cut.start).symm

theorem acceptsFrom_actual
    {package : Package A strategy hwin initial}
    {controller : Controller (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂)}
    {physicalEnv : EnvironmentSequence In₁ In₂}
    (cut : LiteralLeftSeamStageTailCut A strategy hwin package controller
      physicalEnv) :
    A.AcceptsFrom
      (A.run (TraceWord controller physicalEnv) cut.start)
      (OmegaWord.drop (TraceWord controller physicalEnv) cut.start) := by
  rw [cut.dpaStateAt, cut.suffixWord A strategy hwin]
  cases cut.row with
  | first =>
      simpa [pairedCodeStateForRow] using
        package.literalLeftSeamStage_physical_acceptsFrom A strategy hwin
          cut.stage .first cut.inputs
  | both =>
      simpa [pairedCodeStateForRow] using
        package.literalLeftSeamStage_physical_acceptsFrom A strategy hwin
          cut.stage .both cut.inputs

theorem tailParity
    {package : Package A strategy hwin initial}
    {controller : Controller (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂)}
    {physicalEnv : EnvironmentSequence In₁ In₂}
    (cut : LiteralLeftSeamStageTailCut A strategy hwin package controller
      physicalEnv) :
    NatSeqMinEvenParity (fun n ↦ A.priority
      (A.run (TraceWord controller physicalEnv) (cut.start + n))) := by
  let word := TraceWord controller physicalEnv
  have haccepts := cut.acceptsFrom_actual A strategy hwin
  have hparity :
      NatSeqMinEvenParity (fun n ↦ A.priority
        (A.runFrom (A.run word cut.start) (OmegaWord.drop word cut.start) n)) :=
    haccepts
  have heq :
      (fun n ↦ A.priority
        (A.runFrom (A.run word cut.start) (OmegaWord.drop word cut.start) n)) =
      (fun n ↦ A.priority (A.run word (cut.start + n))) := by
    funext n
    exact congrArg A.priority (A.runFrom_drop A.initial word cut.start n)
  rw [heq] at hparity
  exact hparity

end LiteralLeftSeamStageTailCut

/-! ## Fixed-tail fields and extraction assembly -/

/-- The exact data owed by the corrected phase/live-stage trace in the two
eventually fixed regimes.  The stage cuts are proof-side witnesses and may be
chosen after any harmless finite prefix. -/
structure LiteralCombinedFreshPhaseLiveStageFixedTailBookkeeping
    (package : Package A strategy hwin initial)
    (controller : Controller (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂))
    (physicalEnv : EnvironmentSequence In₁ In₂) : Prop where
  right :
    EventuallyStrictRight (fun n ↦ (physicalEnv n).graph) →
      Nonempty
        (LiteralRightSeamStageTailCut A strategy hwin package controller
          physicalEnv)
  left :
    EventuallyStrictLeft (fun n ↦ (physicalEnv n).graph) →
      Nonempty
        (LiteralLeftSeamStageTailCut A strategy hwin package controller
          physicalEnv)

namespace LiteralCombinedFreshPhaseLiveStageFixedTailBookkeeping

theorem fixedRight
    {package : Package A strategy hwin initial}
    {controller : Controller (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂)}
    {physicalEnv : EnvironmentSequence In₁ In₂}
    (bookkeeping :
      LiteralCombinedFreshPhaseLiveStageFixedTailBookkeeping A strategy hwin
        package controller physicalEnv) :
    EventuallyStrictRight (fun n ↦ (physicalEnv n).graph) →
      ∃ start : Nat, NatSeqMinEvenParity
        (fun n ↦ A.priority
          (A.run (TraceWord controller physicalEnv) (start + n))) := by
  intro hright
  obtain ⟨cut⟩ := bookkeeping.right hright
  exact ⟨cut.start, cut.tailParity A strategy hwin⟩

theorem fixedLeft
    {package : Package A strategy hwin initial}
    {controller : Controller (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂)}
    {physicalEnv : EnvironmentSequence In₁ In₂}
    (bookkeeping :
      LiteralCombinedFreshPhaseLiveStageFixedTailBookkeeping A strategy hwin
        package controller physicalEnv) :
    EventuallyStrictLeft (fun n ↦ (physicalEnv n).graph) →
      ∃ start : Nat, NatSeqMinEvenParity
        (fun n ↦ A.priority
          (A.run (TraceWord controller physicalEnv) (start + n))) := by
  intro hleft
  obtain ⟨cut⟩ := bookkeeping.left hleft
  exact ⟨cut.start, cut.tailParity A strategy hwin⟩

/-- Supply the two fixed-tail fields of the global trace extraction from live
stage cuts; only the already separate hard-regime trace witnesses remain as
arguments. -/
noncomputable def toLiteralCrossTraceExtraction
    {package : Package A strategy hwin initial}
    {controller : Controller (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂)}
    {physicalEnv : EnvironmentSequence In₁ In₂}
    (bookkeeping :
      LiteralCombinedFreshPhaseLiveStageFixedTailBookkeeping A strategy hwin
        package controller physicalEnv)
    (recurrentTrace :
      ∀ _hboth : GraphBothRecurrent (fun n ↦ (physicalEnv n).graph),
        FinitePairedPhysicalControllerCanonicalLiteralCrossTraceWitness A
          strategy controller physicalEnv)
    (reversalTrace :
      ∀ _hreversal :
          PersistentStrictReversalTail (fun n ↦ (physicalEnv n).graph),
        FinitePairedPhysicalControllerCanonicalLiteralCrossTraceWitness A
          strategy controller physicalEnv) :
    FinitePairedPhysicalControllerLiteralCrossTraceExtraction A strategy
      controller physicalEnv where
  fixedRight := bookkeeping.fixedRight A strategy hwin
  fixedLeft := bookkeeping.fixedLeft A strategy hwin
  recurrentTrace := recurrentTrace
  reversalTrace := reversalTrace

end LiteralCombinedFreshPhaseLiveStageFixedTailBookkeeping

end ProfiledRawJointGuardedCommonDecoratedPolicyPackage

end

end DetParityAutomaton

end DistributedSynthesis
