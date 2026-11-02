/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleValidatedLiteralPrefixPolicy
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleLiteralPrefixPhysicalTargetSafe

/-!
# Tail-facing laws of a validated current literal table

The finite literal-table alphabet permits arbitrary stored restart states.
Tables constructed from a semantic occurrence use the initial state of their
base physical monitor.  `RightWellRooted` and `LeftWellRooted` isolate this
small fact, after which guard erasure gives an un-restarted physical winning
play and hence target safety at every letter.

The current-provenance eliminators below will establish well-rootedness for
the table actually stored at a validated policy state.  The controller itself
is retained through the first strict input; no sender or monitor restart is
introduced here.
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

variable
  (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
  (hwin : ∀ env : EnvironmentSequence In₁ In₂,
    A.Accepts (execution strategy env))

/-- Harmless filler used only by total narrowed-record operations.  Every
target emitted by a live table is still checked by its literal descriptor. -/
private noncomputable instance :
    Inhabited (ProfiledRawJointUnitTarget A) :=
  ⟨{
    family := {
      right := fun _ ↦ none
      left := fun _ ↦ none
      rightPattern := fun _ _ ↦ false
      leftPattern := fun _ _ ↦ false
    }
    cross := fun _ _ ↦ false
  }⟩

/-! ## Intrinsic table laws -/

/-- Every member of a semantically constructed right table starts at the
initial state of the physical monitor named by that member's descriptor. -/
def ProfiledRawJointRightLiteralPrefixWellRooted
    (move : ProfiledRawJointGuardedCommonRightLiteralCrossMove A) : Prop :=
  ∀ anchor,
    move.1.start anchor =
      (profiledRawJointRightPhysicalSiblingMonitor A
        (move.1.descriptor anchor).base false).initial

/-- Left mirror, stated against the unraised physical monitor. -/
def ProfiledRawJointLeftLiteralPrefixWellRooted
    (move : ProfiledRawJointGuardedCommonLeftLiteralCrossMove A) : Prop :=
  ∀ anchor,
    (move.1.start anchor).down =
      (profiledRawJointLeftPhysicalSiblingMonitor A
        (move.1.descriptor anchor).base false).initial

/-! ## Current-provenance elimination -/

/-- Every right table admitted by the concrete current-origin invariant is
well rooted.  The proof eliminates the root seed or the actual incoming edge;
impossible dead/simultaneous cases have no present right component. -/
theorem
    ProfiledRawJointHybridRightLiteralPrefixCurrentMoveValid.wellRooted
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    {source : ProfiledRawJointHybridSemanticState A strategy}
    {move : ProfiledRawJointGuardedCommonRightLiteralCrossMove A}
    (hvalid :
      ProfiledRawJointHybridRightLiteralPrefixCurrentMoveValid A strategy hwin
        initial source move) :
    ProfiledRawJointRightLiteralPrefixWellRooted A move := by
  classical
  rcases hvalid with hseed | ⟨parent, old, direction, _hsource, hmove⟩
  · rcases hseed with ⟨_, rfl⟩
    intro anchor
    rfl
  · cases parent with
    | common world =>
        cases direction with
        | simultaneous input =>
            change
              (profiledRawJointHybridLiteralPrefixAnnotationOf A strategy hwin
                (profiledRawJointCommonWorldFamily A world)
                (profiledRawJointBothRestartDirection input)).1 = some move
              at hmove
            obtain ⟨member, hmember, rfl⟩ :=
              profiledRawJointRightLiteralPrefixMoveOption_spec A strategy hwin
                (profiledRawJointCommonWorldFamily A world)
                (profiledRawJointBothRestartDirection input) move (by
                  simpa [profiledRawJointHybridLiteralPrefixAnnotationOf]
                    using hmove)
            intro anchor
            rfl
        | strict actual =>
            change
              (profiledRawJointHybridLiteralPrefixAnnotationOf A strategy hwin
                (profiledRawJointCommonWorldFamily A world)
                (profiledRawJointCommonActualDirection actual).direction).1 =
                  some move at hmove
            obtain ⟨member, hmember, rfl⟩ :=
              profiledRawJointRightLiteralPrefixMoveOption_spec A strategy hwin
                (profiledRawJointCommonWorldFamily A world)
                (profiledRawJointCommonActualDirection actual).direction move
                  (by
                    simpa [profiledRawJointHybridLiteralPrefixAnnotationOf]
                      using hmove)
            intro anchor
            rfl
    | oneSided parent =>
        cases direction with
        | simultaneous input =>
            simp [profiledRawJointHybridLiteralPrefixAnnotationAdvance,
              profiledRawJointHybridInitialLiteralPrefixAnnotation] at hmove
        | strict actual =>
            change
              (profiledRawJointHybridLiteralPrefixAnnotationOf A strategy hwin
                parent.family actual.direction).1 = some move at hmove
            obtain ⟨member, hmember, rfl⟩ :=
              profiledRawJointRightLiteralPrefixMoveOption_spec A strategy hwin
                parent.family actual.direction move (by
                  simpa [profiledRawJointHybridLiteralPrefixAnnotationOf]
                    using hmove)
            intro anchor
            rfl
    | dead =>
        cases direction <;>
          simp [profiledRawJointHybridLiteralPrefixAnnotationAdvance,
            profiledRawJointHybridInitialLiteralPrefixAnnotation] at hmove

/-- Left mirror of current-origin well-rootedness. -/
theorem
    ProfiledRawJointHybridLeftLiteralPrefixCurrentMoveValid.wellRooted
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    {source : ProfiledRawJointHybridSemanticState A strategy}
    {move : ProfiledRawJointGuardedCommonLeftLiteralCrossMove A}
    (hvalid :
      ProfiledRawJointHybridLeftLiteralPrefixCurrentMoveValid A strategy hwin
        initial source move) :
    ProfiledRawJointLeftLiteralPrefixWellRooted A move := by
  classical
  rcases hvalid with hseed | ⟨parent, old, direction, _hsource, hmove⟩
  · rcases hseed with ⟨_, rfl⟩
    intro anchor
    rfl
  · cases parent with
    | common world =>
        cases direction with
        | simultaneous input =>
            change
              (profiledRawJointHybridLiteralPrefixAnnotationOf A strategy hwin
                (profiledRawJointCommonWorldFamily A world)
                (profiledRawJointBothRestartDirection input)).2 = some move
              at hmove
            obtain ⟨member, hmember, rfl⟩ :=
              profiledRawJointLeftLiteralPrefixMoveOption_spec A strategy hwin
                (profiledRawJointCommonWorldFamily A world)
                (profiledRawJointBothRestartDirection input) move (by
                  simpa [profiledRawJointHybridLiteralPrefixAnnotationOf]
                    using hmove)
            intro anchor
            rfl
        | strict actual =>
            change
              (profiledRawJointHybridLiteralPrefixAnnotationOf A strategy hwin
                (profiledRawJointCommonWorldFamily A world)
                (profiledRawJointCommonActualDirection actual).direction).2 =
                  some move at hmove
            obtain ⟨member, hmember, rfl⟩ :=
              profiledRawJointLeftLiteralPrefixMoveOption_spec A strategy hwin
                (profiledRawJointCommonWorldFamily A world)
                (profiledRawJointCommonActualDirection actual).direction move
                  (by
                    simpa [profiledRawJointHybridLiteralPrefixAnnotationOf]
                      using hmove)
            intro anchor
            rfl
    | oneSided parent =>
        cases direction with
        | simultaneous input =>
            simp [profiledRawJointHybridLiteralPrefixAnnotationAdvance,
              profiledRawJointHybridInitialLiteralPrefixAnnotation] at hmove
        | strict actual =>
            change
              (profiledRawJointHybridLiteralPrefixAnnotationOf A strategy hwin
                parent.family actual.direction).2 = some move at hmove
            obtain ⟨member, hmember, rfl⟩ :=
              profiledRawJointLeftLiteralPrefixMoveOption_spec A strategy hwin
                parent.family actual.direction move (by
                  simpa [profiledRawJointHybridLiteralPrefixAnnotationOf]
                    using hmove)
            intro anchor
            rfl
    | dead =>
        cases direction <;>
          simp [profiledRawJointHybridLiteralPrefixAnnotationAdvance,
            profiledRawJointHybridInitialLiteralPrefixAnnotation] at hmove

/-- Physical play generated by one retained right table member. -/
noncomputable def profiledRawJointRightLiteralPrefixCurrentPhysicalPlay
    (move : ProfiledRawJointGuardedCommonRightLiteralCrossMove A)
    (anchor : Bool) (env : Nat → In₂ × In₁) :
    Nat → RealizedBlockRound In₂ In₁
      (ProfiledRawJointTargetRightReceiverOutput
        (Out₁ := Out₁) (Out₂ := Out₂) (ProfiledRawJointUnitTarget A)) Out₁ :=
  let monitorFamily :=
    fun descriptor : ProfiledRawJointRightPhysicalSiblingDescriptor A ↦
      profiledRawJointRightPhysicalSiblingMonitor A descriptor false
  let monitor := finiteCrossAnchorLiteralPrefixMonitor monitorFamily
  let firstAllowed := finiteCrossAnchorLiteralPrefixFirstAllowed monitorFamily
  let secondAllowed :=
    finiteCrossAnchorLiteralPrefixSecondAllowed monitorFamily
  let guard := finiteCrossAnchorFirstTwoGuardFamily
    (fun member ↦ monitor (move.1.descriptor member)) move.1.start
    (firstAllowed move.1) (secondAllowed move.1) anchor
  let controller := move.memberController monitor anchor
  treePlay (narrowedInducedTree guard controller.labeledTree) env

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Guard erasure at a well-rooted current right table yields a winning play
of the original physical monitor, not merely a restarted one. -/
theorem profiledRawJointRightLiteralPrefixCurrentPhysicalPlay_wins
    (move : ProfiledRawJointGuardedCommonRightLiteralCrossMove A)
    (hrooted : ProfiledRawJointRightLiteralPrefixWellRooted A move)
    (anchor : Bool) (env : Nat → In₂ × In₁) :
    (profiledRawJointRightPhysicalSiblingMonitor A
      (move.1.descriptor anchor).base false).WinsPlay
      (profiledRawJointRightLiteralPrefixCurrentPhysicalPlay A move anchor
        env) := by
  let monitorFamily :=
    fun descriptor : ProfiledRawJointRightPhysicalSiblingDescriptor A ↦
      profiledRawJointRightPhysicalSiblingMonitor A descriptor false
  let monitor := finiteCrossAnchorLiteralPrefixMonitor monitorFamily
  have hbase := move.memberController_base_wins monitor anchor env
  have hstart := hrooted anchor
  simpa [profiledRawJointRightLiteralPrefixCurrentPhysicalPlay, monitor,
    monitorFamily, finiteCrossAnchorRestartFamily,
    BlockRecordMonitor.restartAt, hstart] using hbase

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Every target emitted by a well-rooted current right table is legal for
the descriptor stored in that same literal table. -/
theorem profiledRawJointRightLiteralPrefixCurrent_targetSafe
    (move : ProfiledRawJointGuardedCommonRightLiteralCrossMove A)
    (hrooted : ProfiledRawJointRightLiteralPrefixWellRooted A move)
    (anchor : Bool) (env : Nat → In₂ × In₁) (n : Nat)
    (row : PairedEntryRow) :
    let descriptor := (move.1.descriptor anchor).base
    let monitor :=
      profiledRawJointRightPhysicalSiblingMonitor A descriptor false
    let play :=
      profiledRawJointRightLiteralPrefixCurrentPhysicalPlay A move anchor env
    erasePairedProfiledState A
        (profiledRawJointUnitRightTargetProjection A
          ((play n).2.1.target row)) =
        pairedRightCloseTarget A ((monitor.run play n).2.1) row
          (profiledRawJointTargetRightPhysicalLetter A (play n)) ∧
      profiledRawJointRightPhysicalSiblingAllowed A descriptor
        ((play n).2.1.target row) := by
  dsimp only
  exact profiledRawJointTargetRight_targetsSafe_of_wins A
    (profiledRawJointUnitRightTargetProjection A)
    (profiledRawJointRightPhysicalSiblingAllowed A
      (move.1.descriptor anchor).base)
    (move.1.descriptor anchor).base.source
    (profiledRawJointRightLiteralPrefixCurrentPhysicalPlay A move anchor env)
    (profiledRawJointRightLiteralPrefixCurrentPhysicalPlay_wins A move hrooted
      anchor env) n row

/-- Physical play generated by one retained left table member. -/
noncomputable def profiledRawJointLeftLiteralPrefixCurrentPhysicalPlay
    (move : ProfiledRawJointGuardedCommonLeftLiteralCrossMove A)
    (anchor : Bool) (env : Nat → In₁ × In₂) :
    Nat → RealizedBlockRound In₁ In₂
      (ProfiledRawJointTargetLeftReceiverOutput
        (Out₁ := Out₁) (Out₂ := Out₂) (ProfiledRawJointUnitTarget A)) Out₂ :=
  let monitorFamily :=
    fun descriptor : ProfiledRawJointLeftPhysicalSiblingDescriptor A ↦
      profiledRawJointGuardedCommonLeftLiteralCrossMonitor A descriptor
  let monitor := finiteCrossAnchorLiteralPrefixMonitor monitorFamily
  let firstAllowed := finiteCrossAnchorLiteralPrefixFirstAllowed monitorFamily
  let secondAllowed :=
    finiteCrossAnchorLiteralPrefixSecondAllowed monitorFamily
  let guard := finiteCrossAnchorFirstTwoGuardFamily
    (fun member ↦ monitor (move.1.descriptor member)) move.1.start
    (firstAllowed move.1) (secondAllowed move.1) anchor
  let controller := move.memberController monitor anchor
  treePlay (narrowedInducedTree guard controller.labeledTree) env

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Left guard erasure followed by removal of the harmless state lift. -/
theorem profiledRawJointLeftLiteralPrefixCurrentPhysicalPlay_wins
    (move : ProfiledRawJointGuardedCommonLeftLiteralCrossMove A)
    (hrooted : ProfiledRawJointLeftLiteralPrefixWellRooted A move)
    (anchor : Bool) (env : Nat → In₁ × In₂) :
    (profiledRawJointLeftPhysicalSiblingMonitor A
      (move.1.descriptor anchor).base false).WinsPlay
      (profiledRawJointLeftLiteralPrefixCurrentPhysicalPlay A move anchor
        env) := by
  let baseMonitor :=
    profiledRawJointLeftPhysicalSiblingMonitor A
      (move.1.descriptor anchor).base false
  let monitorFamily :=
    fun descriptor : ProfiledRawJointLeftPhysicalSiblingDescriptor A ↦
      profiledRawJointGuardedCommonLeftLiteralCrossMonitor A descriptor
  let monitor := finiteCrossAnchorLiteralPrefixMonitor monitorFamily
  have hbase := move.memberController_base_wins monitor anchor env
  have hstart : move.1.start anchor =
      (profiledRawJointGuardedCommonLeftLiteralCrossMonitor A
        (move.1.descriptor anchor).base).initial := by
    apply ULift.ext
    exact hrooted anchor
  apply (BlockRecordMonitor.raiseState_winsPlay_iff baseMonitor _).mp
  simpa [profiledRawJointLeftLiteralPrefixCurrentPhysicalPlay, monitor,
    monitorFamily, baseMonitor, finiteCrossAnchorRestartFamily,
    BlockRecordMonitor.restartAt,
    profiledRawJointGuardedCommonLeftLiteralCrossMonitor, hstart] using hbase

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Left current-table target safety. -/
theorem profiledRawJointLeftLiteralPrefixCurrent_targetSafe
    (move : ProfiledRawJointGuardedCommonLeftLiteralCrossMove A)
    (hrooted : ProfiledRawJointLeftLiteralPrefixWellRooted A move)
    (anchor : Bool) (env : Nat → In₁ × In₂) (n : Nat)
    (row : PairedEntryRow) :
    let descriptor := (move.1.descriptor anchor).base
    let monitor :=
      profiledRawJointLeftPhysicalSiblingMonitor A descriptor false
    let play :=
      profiledRawJointLeftLiteralPrefixCurrentPhysicalPlay A move anchor env
    erasePairedProfiledState A
        (profiledRawJointUnitLeftTargetProjection A
          ((play n).2.1.target row)) =
        pairedLeftCloseTarget A ((monitor.run play n).2.1) row
          (profiledRawJointTargetLeftPhysicalLetter A (play n)) ∧
      profiledRawJointLeftPhysicalSiblingAllowed A descriptor
        ((play n).2.1.target row) := by
  dsimp only
  exact profiledRawJointTargetLeft_targetsSafe_of_wins A
    (profiledRawJointUnitLeftTargetProjection A)
    (profiledRawJointLeftPhysicalSiblingAllowed A
      (move.1.descriptor anchor).base)
    (move.1.descriptor anchor).base.source
    (profiledRawJointLeftLiteralPrefixCurrentPhysicalPlay A move anchor env)
    (profiledRawJointLeftLiteralPrefixCurrentPhysicalPlay_wins A move hrooted
      anchor env) n row

/-! ## Direct validated-current adapters -/

/-- A present right table in a current-compatible annotation is well rooted,
without selecting another semantic representative. -/
theorem
    ProfiledRawJointHybridLiteralPrefixCurrentCompatible.rightWellRooted
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    {source : ProfiledRawJointHybridSemanticState A strategy}
    {extra : ProfiledRawJointHybridLiteralPrefixEdgeAnnotation A}
    (hcurrent :
      ProfiledRawJointHybridLiteralPrefixCurrentCompatible A strategy hwin
        initial source extra)
    {move : ProfiledRawJointGuardedCommonRightLiteralCrossMove A}
    (hmove : extra.1 = some move) :
    ProfiledRawJointRightLiteralPrefixWellRooted A move :=
  (hcurrent.rightMoveValid A strategy hwin hmove).wellRooted A strategy hwin

/-- Left mirror. -/
theorem
    ProfiledRawJointHybridLiteralPrefixCurrentCompatible.leftWellRooted
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    {source : ProfiledRawJointHybridSemanticState A strategy}
    {extra : ProfiledRawJointHybridLiteralPrefixEdgeAnnotation A}
    (hcurrent :
      ProfiledRawJointHybridLiteralPrefixCurrentCompatible A strategy hwin
        initial source extra)
    {move : ProfiledRawJointGuardedCommonLeftLiteralCrossMove A}
    (hmove : extra.2 = some move) :
    ProfiledRawJointLeftLiteralPrefixWellRooted A move :=
  (hcurrent.leftMoveValid A strategy hwin hmove).wellRooted A strategy hwin

/-- Tail-facing right target safety, discharged directly from the current
validated annotation and its literally stored table ID. -/
theorem
    ProfiledRawJointHybridLiteralPrefixCurrentCompatible.rightTargetSafe
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    {source : ProfiledRawJointHybridSemanticState A strategy}
    {extra : ProfiledRawJointHybridLiteralPrefixEdgeAnnotation A}
    (hcurrent :
      ProfiledRawJointHybridLiteralPrefixCurrentCompatible A strategy hwin
        initial source extra)
    {move : ProfiledRawJointGuardedCommonRightLiteralCrossMove A}
    (hmove : extra.1 = some move)
    (anchor : Bool) (env : Nat → In₂ × In₁) (n : Nat)
    (row : PairedEntryRow) :
    let descriptor := (move.1.descriptor anchor).base
    let monitor :=
      profiledRawJointRightPhysicalSiblingMonitor A descriptor false
    let play :=
      profiledRawJointRightLiteralPrefixCurrentPhysicalPlay A move anchor env
    erasePairedProfiledState A
        (profiledRawJointUnitRightTargetProjection A
          ((play n).2.1.target row)) =
        pairedRightCloseTarget A ((monitor.run play n).2.1) row
          (profiledRawJointTargetRightPhysicalLetter A (play n)) ∧
      profiledRawJointRightPhysicalSiblingAllowed A descriptor
        ((play n).2.1.target row) := by
  exact profiledRawJointRightLiteralPrefixCurrent_targetSafe A move
    (hcurrent.rightWellRooted A strategy hwin hmove) anchor env n row

/-- Left Tail-facing target safety. -/
theorem
    ProfiledRawJointHybridLiteralPrefixCurrentCompatible.leftTargetSafe
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    {source : ProfiledRawJointHybridSemanticState A strategy}
    {extra : ProfiledRawJointHybridLiteralPrefixEdgeAnnotation A}
    (hcurrent :
      ProfiledRawJointHybridLiteralPrefixCurrentCompatible A strategy hwin
        initial source extra)
    {move : ProfiledRawJointGuardedCommonLeftLiteralCrossMove A}
    (hmove : extra.2 = some move)
    (anchor : Bool) (env : Nat → In₁ × In₂) (n : Nat)
    (row : PairedEntryRow) :
    let descriptor := (move.1.descriptor anchor).base
    let monitor :=
      profiledRawJointLeftPhysicalSiblingMonitor A descriptor false
    let play :=
      profiledRawJointLeftLiteralPrefixCurrentPhysicalPlay A move anchor env
    erasePairedProfiledState A
        (profiledRawJointUnitLeftTargetProjection A
          ((play n).2.1.target row)) =
        pairedLeftCloseTarget A ((monitor.run play n).2.1) row
          (profiledRawJointTargetLeftPhysicalLetter A (play n)) ∧
      profiledRawJointLeftPhysicalSiblingAllowed A descriptor
        ((play n).2.1.target row) := by
  exact profiledRawJointLeftLiteralPrefixCurrent_targetSafe A move
    (hcurrent.leftWellRooted A strategy hwin hmove) anchor env n row

end

end DetParityAutomaton

end DistributedSynthesis
