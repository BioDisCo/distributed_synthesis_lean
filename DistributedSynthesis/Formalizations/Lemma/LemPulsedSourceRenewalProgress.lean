/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemOwnerOpenPairDynamics

namespace DistributedSynthesis
namespace PulsedSourceInstallationAudit
open DetParityAutomaton TwoProcessNoResetReversalObstruction
open TwoProcessPhysicalTargetAudit (pulsedSource pulsedSource_wins strictState)

noncomputable section

theorem pulse_clock_next (p : Proc)
    (history : History Unit Unit Graph Bool Bool)
    (env : EnvironmentRound Unit Unit) :
    clock (nextView p history env) = decide ((history.length + 1) % 2 = 0) := by
  have h := StarReadback.viewRounds_currentView p history
  cases p <;> cases env with
  | mk one two graph =>
    cases graph <;>
      simpa [clock, nextView, advanceViewsWithEnvironment, StarReadback.viewRounds,
        currentView] using congrArg (fun n ↦ decide ((n + 1) % 2 = 0)) h

theorem pulse_extend_length (strategy : StrategyPair Unit Unit Bool Bool)
    (history : History Unit Unit Graph Bool Bool)
    (envs : List (EnvironmentRound Unit Unit)) :
    (extendPrefix strategy history envs).length = history.length + envs.length := by
  induction envs generalizing history with
  | nil => simp [extendPrefix]
  | cons env envs ih =>
      change (extendPrefix strategy (History.append history
        (nextRound strategy history env)) envs).length = _
      rw [ih]
      simp only [History.append, History.length, List.length_append,
        List.length_cons, List.length_nil]
      omega

theorem pulse_right_outputs (entry : ProcOnePairedEntryRep pulsedSource)
    (past : List (Unit × Unit)) :
    entry.lambdaOfStrategy.blind (senderWord past) () =
        decide ((entry.leftHistory.length + past.length + 1) % 2 = 0) ∧
    entry.lambdaOfStrategy.informedLeft past ((), ()) =
        decide ((entry.leftHistory.length + past.length + 1) % 2 = 0) ∧
    entry.lambdaOfStrategy.informedBoth past ((), ()) =
        decide ((entry.leftHistory.length + past.length + 1) % 2 = 0) := by
  have hlength : entry.bothHistory.length = entry.leftHistory.length := by
    have h := congrArg StarReadback.viewRounds entry.view_eq
    simpa only [StarReadback.viewRounds_currentView] using h.symm
  simp [ProcOnePairedEntryRep.lambdaOfStrategy, blockSenderOne, blockReceiverTwo,
    pulsedSource, pulse_clock_next, pulse_extend_length, senderWord, hlength]

theorem pulse_right_child_profile (entry : ProcOnePairedEntryRep pulsedSource)
    (source : ProfiledRawRightSlot objective)
    (row : PairedEntryRow) (past : List (Unit × Unit)) :
    let slot := profiledRawRightChildSlot objective source entry.lambdaOfStrategy row past ((), ())
    slot.1.1.2 = true ∧ slot.2 ((), ()) = !slot.1.1.1 := by
  have hs := pulse_right_outputs entry past
  have hlength : entry.bothHistory.length = entry.leftHistory.length := by
    have h := congrArg StarReadback.viewRounds entry.view_eq
    simpa only [StarReadback.viewRounds_currentView] using h.symm
  cases row <;>
    simp only [profiledRawRightChildSlot, pairedRightFreshChildCodeLeft,
      pairedRightFreshChildCodeBoth, objective, grant, rightRoundRecord,
      bothRoundRecord, hs.1, hs.2.1, hs.2.2]
  all_goals
    simp [rightClosingProfile,
      ProcOnePairedEntryRep.lambdaOfStrategy, pulsedSource, pulse_clock_next,
      pulse_extend_length, hlength]
  all_goals
    by_cases h : (entry.leftHistory.length + past.length + 1) % 2 = 0 <;>
      simp [h] <;> omega

theorem right_projection_currentSlot (target : ProfiledRawJointUnitTarget objective)
    (slot : ProfiledRawLeftSlot objective)
    (h : profiledRawJointUnitRightTargetProjection objective target = .inr (.inr slot)) :
    profiledRawJointOneSidedCurrentSlots objective .left target () = some (.inr slot) := by
  unfold profiledRawJointUnitRightTargetProjection at h
  cases hs : target.family.left () with
  | none => simp [hs] at h
  | some found =>
    simp only [hs, Sum.inr.injEq] at h
    simp only [profiledRawJointOneSidedCurrentSlots, hs, Option.map_some, h]

theorem right_allowed_live_source
    (family : ProfiledRawJointSemanticFamily objective pulsedSource (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := Unit) (In₂ := Unit))
    (member : ProcOnePairedEntryRep pulsedSource × objective.State)
    (hmember : (family.semanticChild objective direction).right () = some member)
    (target : ProfiledRawJointUnitTarget objective)
    (hallowed : ProfiledRawJointRightSiblingSharedAllowedTarget objective family direction target) :
    ∃ slot : ProfiledRawLeftSlot objective,
      profiledRawJointOneSidedCurrentSlots objective .left target () = some (.inr slot) := by
  obtain ⟨row, past, input, rfl⟩ := hallowed
  have hp := (profiledRawJointRightSiblingActivation objective pulsedSource_wins
    family direction member hmember false).target_state row past input
  exact ⟨_, right_projection_currentSlot _ _ hp⟩

/-- Every non-granting semantic right target, not just the two targets of
the original clock test, pins the next left profile to `true`. The stored
minimum may be arbitrary and is not used as a progress argument. -/
theorem right_allowed_nongranting_source
    (family : ProfiledRawJointSemanticFamily objective pulsedSource (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := Unit) (In₂ := Unit))
    (member : ProcOnePairedEntryRep pulsedSource × objective.State)
    (hmember : (family.semanticChild objective direction).right () = some member)
    (target : ProfiledRawJointUnitTarget objective)
    (hallowed : ProfiledRawJointRightSiblingSharedAllowedTarget objective
      family direction target)
    (hfalse : strictState (erasePairedProfiledState objective
      (profiledRawJointUnitRightTargetProjection objective target)) = false) :
    ∃ minimum : Bool,
      profiledRawJointOneSidedCurrentSlots objective .left target () =
        some (.inr (((false, true), minimum), fun _ ↦ true)) := by
  obtain ⟨row, past, input, rfl⟩ := hallowed
  rcases input with ⟨⟨⟩, ⟨⟩⟩
  have hp := (profiledRawJointRightSiblingActivation objective pulsedSource_wins
    family direction member hmember false).target_state row past ((), ())
  dsimp only [profiledRawJointRightSiblingActivation] at hp
  let slot := profiledRawRightChildSlot objective
    (profiledRawRightSlotOfSemanticPair objective member)
    member.1.lambdaOfStrategy row past ((), ())
  have hslot : profiledRawJointOneSidedCurrentSlots objective .left
      (profiledRawJointOneSidedNext objective
        ((profiledRawJointRightSiblingFamily objective family direction false).incidenceCode objective)
        ((profiledRawJointRightSiblingFamily objective family direction false).move objective)
        (profiledRawJointUnitRightActualDirection row past ((), ()))) () =
      some (.inr slot) := right_projection_currentSlot _ slot hp
  rw [hp] at hfalse
  change slot.1.1.1 = false at hfalse
  have hprofile := pulse_right_child_profile member.1
    (profiledRawRightSlotOfSemanticPair objective member) row past
  change slot.1.1.2 = true ∧ slot.2 ((), ()) = !slot.1.1.1 at hprofile
  have hnormalize : slot = (((false, true), slot.1.2), fun _ ↦ true) := by
    apply Prod.ext
    · exact Prod.ext (Prod.ext hfalse hprofile.1) rfl
    · funext input
      rcases input with ⟨⟨⟩, ⟨⟩⟩
      simpa only [hfalse, Bool.not_false] using hprofile.2
  refine ⟨slot.1.2, ?_⟩
  rw [hslot, hnormalize]
  rfl

universe m
variable {Memory : Type m}

/-- A valid owner fibre supplies the literal target effect even when its
virtual receiver was selected at a different representative prefix. -/
theorem right_fibre_target_effect
    (fibre : ProfiledRawJointRightOwnerFibreControl objective)
    (hvalid : ProfiledRawJointRightOwnerFibreValid objective fibre)
    (row : PairedEntryRow) :
    let target := (((fibre.1.memberController objective false).labelOf fibre.2.1).2
      fibre.2.2 ((), ()) |>.target row)
    profiledRawJointRightPhysicalSiblingAllowed objective fibre.1.1 target ∧
    strictState (erasePairedProfiledState objective
      (profiledRawJointUnitRightTargetProjection objective target)) =
      ((((fibre.1.memberController objective false).labelOf fibre.2.1).1 ()) &&
       (stepProfiledRawJointRightPhysicalSiblingReceiverFor objective fibre.1
         fibre.2.1 row fibre.2.2 ((), ())).1) := by
  obtain ⟨past, howner, hstate⟩ := hvalid
  let env : Nat → Unit × Unit := omegaOfList (past ++ [((), ())])
  have hs := fibre.1.memberController_targetSafe objective false env past.length row
  have hat := profiledRawJointRightPhysicalSibling_treePlay_at_prefix objective
    fibre.1 past ((), ())
  dsimp only at hs hat
  rw [hat] at hs
  have heffect := congrArg strictState hs.1
  rw [TwoProcessPhysicalTargetAudit.strictState_rightClose] at heffect
  dsimp only [narrowedRecord] at hs heffect
  rw [← howner, ← hstate] at hs heffect
  refine ⟨hs.2, ?_⟩
  cases row <;> exact heffect

/-- Source-sensitive progress after an arbitrary non-granting right target.
This applies to every accepted installed table with the realized semantic
descriptor, irrespective of its chosen finite grant schedule. -/
theorem realized_nongranting_target_first_left_grants
    (tables : ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection
      (Memory := Memory) objective pulsedSource)
    (state : ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryBankControl
      (Memory := Memory) objective pulsedSource)
    (family : ProfiledRawJointSemanticFamily objective pulsedSource (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := Unit) (In₂ := Unit))
    (member : ProcOnePairedEntryRep pulsedSource × objective.State)
    (hmember : (family.semanticChild objective direction).right () = some member)
    (target : ProfiledRawJointUnitTarget objective)
    (hallowed : ProfiledRawJointRightSiblingSharedAllowedTarget objective family direction target)
    (hfalse : strictState (erasePairedProfiledState objective
      (profiledRawJointUnitRightTargetProjection objective target)) = false)
    (hrealizes : tables.ChildRealizes objective pulsedSource pulsedSource_wins state target
      (tables.resolveTarget objective pulsedSource pulsedSource_wins state target))
    (move : ProfiledRawJointLeftPhysicalSiblingMove objective)
    (hmove : (tables.resolvePacket objective pulsedSource pulsedSource_wins
      state target).successor.2.1.1.2.2 = some move) :
    ((stepProfiledRawJointLeftPhysicalSiblingReceiverFor objective move
      (move.memberController objective false).initial .first
      (profiledRawJointLeftPhysicalSiblingMonitor objective move.1 false).initial ((), ())).1,
     ((move.memberController objective false).labelOf
       (move.memberController objective false).initial).1 ()) = (true, true) := by
  obtain ⟨minimum, hslot⟩ := right_allowed_nongranting_source
    family direction member hmember target hallowed hfalse
  obtain ⟨childFamily, childDirection, child, hc, hs, hd⟩ :=
    realized_packet_left_provenance_at tables state target _ hslot hrealizes move hmove
  have hg := Bool.and_eq_true_iff.mp
    (left_first_outputs_grant childFamily childDirection child hc hs move hd)
  exact Prod.ext hg.1 hg.2

def strictOutputGrant (output : Bool × Bool) : Bool := output.1 && output.2

/-- A genuine two-round progress disjunction in the raw kernel. From the
equal-open state, either the right round grants, or its fresh left reversal
grants. The hypotheses are local source provenance, fibre validity, and
target realization; no mixed-run acceptance or progress invariant is assumed. -/
theorem open_pair_right_left_progress
    (tables : ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection
      (Memory := Memory) objective pulsedSource)
    (pair : OpenOwnerPair (Memory := Memory) objective pulsedSource)
    (hvalid : ProfiledRawJointRightOwnerFibreValid objective pair.right)
    (family : ProfiledRawJointSemanticFamily objective pulsedSource (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := Unit) (In₂ := Unit))
    (member : ProcOnePairedEntryRep pulsedSource × objective.State)
    (hmember : (family.semanticChild objective direction).right () = some member)
    (hdescriptor : pair.right.1.1 = profiledRawJointRightPhysicalSiblingDescriptorOf
      objective family direction member)
    (hrealizes :
      let data := (pair.rightPhaseData objective pulsedSource).1
      let target := data.target objective pulsedSource ((), ())
      tables.ChildRealizes objective pulsedSource pulsedSource_wins data.1 target
        (tables.resolveTarget objective pulsedSource pulsedSource_wins data.1 target)) :
    let first := tables.ownerFibreRound objective pulsedSource pulsedSource_wins
      (pair.controls objective pulsedSource) ((), ()) .right
    strictOutputGrant first.2 = true ∨
      strictOutputGrant (tables.ownerFibreRound objective pulsedSource pulsedSource_wins
        first.1 ((), ()) .left).2 = true := by
  dsimp only
  by_cases hg : strictOutputGrant (tables.ownerFibreRound objective pulsedSource
      pulsedSource_wins (pair.controls objective pulsedSource) ((), ()) .right).2 = true
  · exact Or.inl hg
  right
  let data := (pair.rightPhaseData objective pulsedSource).1
  let target := data.target objective pulsedSource ((), ())
  have hs := right_fibre_target_effect pair.right hvalid pair.rightReceivers.openControl.2.2.1
  have ha : profiledRawJointRightPhysicalSiblingAllowed objective pair.right.1.1 target := hs.1
  nth_rw 1 [hdescriptor] at ha
  rw [profiledRawJointRightPhysicalSiblingDescriptorOf_allowed_iff] at ha
  have hf : strictState (erasePairedProfiledState objective
      (profiledRawJointUnitRightTargetProjection objective target)) = false := by
    rw [pair.round_right_outputs objective pulsedSource pulsedSource_wins tables ((), ())]
      at hg
    change ¬ (_ && _) = true at hg
    have he := hs.2
    change strictState (erasePairedProfiledState objective
      (profiledRawJointUnitRightTargetProjection objective target)) = _ at he
    rw [he]
    exact Bool.eq_false_iff.mpr hg
  obtain ⟨minimum, hslot⟩ := right_allowed_nongranting_source
    family direction member hmember target ha hf
  obtain ⟨move, hmove⟩ :=
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTable.childRealizes_resolvePacket_leftMove_exists
      objective pulsedSource pulsedSource_wins tables data.1 target hrealizes
        (.inr (((false, true), minimum), fun _ ↦ true)) hslot
  have hgrant := realized_nongranting_target_first_left_grants tables data.1
    family direction member hmember target ha hf hrealizes move hmove
  rw [pair.round_right objective pulsedSource pulsedSource_wins tables ((), ())]
  rw [StagedRightOwnerPair.round_left objective pulsedSource pulsedSource_wins
    (pair.stepRight objective pulsedSource pulsedSource_wins tables ((), ()))
    tables move hmove ((), ())]
  rw [hgrant]
  rfl

/-- These are local installation premises, not an acceptance certificate.
The resolver contract concerns one fixed right bank cell; the return cycle
keeps that cell and that right physical move. -/
structure RenewalReady
    (tables : ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection
      (Memory := Memory) objective pulsedSource)
    (pair : StagedRightOwnerPair (Memory := Memory) objective pulsedSource) : Prop where
  valid : ProfiledRawJointRightOwnerFibreValid objective pair.right
  anchor : pair.twoCoordinates.1 = pair.state
  installed : ∃ move : ProfiledRawJointLeftPhysicalSiblingMove objective,
    pair.packet.successor.2.1.1.2.2 = some move
  semantic : ∃
    (family : ProfiledRawJointSemanticFamily objective pulsedSource (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := Unit) (In₂ := Unit))
    (member : ProcOnePairedEntryRep pulsedSource × objective.State),
    (family.semanticChild objective direction).right () = some member ∧
    pair.right.1.1 = profiledRawJointRightPhysicalSiblingDescriptorOf objective family direction member
  resolve : ∀ target : ProfiledRawJointUnitTarget objective,
    profiledRawJointRightPhysicalSiblingAllowed objective pair.right.1.1 target →
    tables.ChildRealizes objective pulsedSource pulsedSource_wins pair.state target
      (tables.resolveTarget objective pulsedSource pulsedSource_wins pair.state target)

def preRenewal
    (tables : ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection
      (Memory := Memory) objective pulsedSource)
    (pair : StagedRightOwnerPair (Memory := Memory) objective pulsedSource)
    (move : ProfiledRawJointLeftPhysicalSiblingMove objective) :
    OpenOwnerPair (Memory := Memory) objective pulsedSource :=
  ((pair.stepLeft objective pulsedSource pulsedSource_wins tables move ((), ())).stepRight
    objective pulsedSource pulsedSource_wins tables ((), ())).stepLeft
    objective pulsedSource pulsedSource_wins tables ((), ())

theorem preRenewal_valid
    (tables : ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection
      (Memory := Memory) objective pulsedSource)
    (pair : StagedRightOwnerPair (Memory := Memory) objective pulsedSource)
    (h : RenewalReady tables pair) (move : ProfiledRawJointLeftPhysicalSiblingMove objective) :
    ProfiledRawJointRightOwnerFibreValid objective (preRenewal tables pair move).right := by
  apply OpenOwnerPair.stepLeft_right_valid
  apply InstalledLeftOwnerPair.stepRight_right_valid
  exact pair.stepLeft_right_valid objective pulsedSource pulsedSource_wins tables h.valid move ((), ())

theorem preRenewal_right_move
    (tables : ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection
      (Memory := Memory) objective pulsedSource)
    (pair : StagedRightOwnerPair (Memory := Memory) objective pulsedSource)
    (move : ProfiledRawJointLeftPhysicalSiblingMove objective) :
    (preRenewal tables pair move).right.1 = pair.right.1 := rfl

theorem preRenewal_state
    (tables : ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection
      (Memory := Memory) objective pulsedSource)
    (pair : StagedRightOwnerPair (Memory := Memory) objective pulsedSource)
    (move : ProfiledRawJointLeftPhysicalSiblingMove objective) :
    ((preRenewal tables pair move).rightPhaseData objective pulsedSource).1.1 =
      pair.twoCoordinates.1 := rfl

theorem renew_eq_preRenewal_stepRight
    (tables : ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection
      (Memory := Memory) objective pulsedSource)
    (pair : StagedRightOwnerPair (Memory := Memory) objective pulsedSource)
    (move : ProfiledRawJointLeftPhysicalSiblingMove objective) :
    pair.renew objective pulsedSource pulsedSource_wins tables move (fun _ ↦ ((), ())) =
      (preRenewal tables pair move).stepRight objective pulsedSource pulsedSource_wins
        tables ((), ()) := rfl

attribute [irreducible] preRenewal

theorem open_pair_staged_ready
    (tables : ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection
      (Memory := Memory) objective pulsedSource)
    (pair : StagedRightOwnerPair (Memory := Memory) objective pulsedSource)
    (h : RenewalReady tables pair)
    (mid : OpenOwnerPair (Memory := Memory) objective pulsedSource)
    (hv : ProfiledRawJointRightOwnerFibreValid objective mid.right)
    (hmoveEq : mid.right.1 = pair.right.1)
    (hmidState : (mid.rightPhaseData objective pulsedSource).1.1 = pair.state) :
    RenewalReady tables (mid.stepRight objective pulsedSource pulsedSource_wins tables ((), ())) := by
  let target := (mid.rightPhaseData objective pulsedSource).1.target objective pulsedSource ((), ())
  have ha : profiledRawJointRightPhysicalSiblingAllowed objective pair.right.1.1 target := by
    rw [← hmoveEq]
    exact hv.targetSafe objective mid.right ((), ()) mid.rightReceivers.openControl.2.2.1
  have hrealizes := h.resolve target ha
  obtain ⟨family, direction, member, hm, hd⟩ := h.semantic
  have ha' := ha
  nth_rw 1 [hd] at ha'
  rw [profiledRawJointRightPhysicalSiblingDescriptorOf_allowed_iff] at ha'
  obtain ⟨slot, hs⟩ := right_allowed_live_source family direction member hm target ha'
  obtain ⟨nextMove, hn⟩ :=
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTable.childRealizes_resolvePacket_leftMove_exists
      objective pulsedSource pulsedSource_wins tables pair.state target hrealizes (.inr slot) hs
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact hv.noRecv objective mid.right ()
  · rfl
  · refine ⟨nextMove, ?_⟩
    change (tables.resolvePacket objective pulsedSource pulsedSource_wins
      (mid.rightPhaseData objective pulsedSource).1.1 target).successor.2.1.1.2.2 = some nextMove
    rw [hmidState]
    exact hn
  · refine ⟨family, direction, member, hm, ?_⟩
    change mid.right.1.1 = _
    rw [hmoveEq]
    exact hd
  · intro t ht
    change tables.ChildRealizes objective pulsedSource pulsedSource_wins
      (mid.rightPhaseData objective pulsedSource).1.1 t
      (tables.resolveTarget objective pulsedSource pulsedSource_wins
        (mid.rightPhaseData objective pulsedSource).1.1 t)
    rw [hmidState]
    change profiledRawJointRightPhysicalSiblingAllowed objective mid.right.1.1 t at ht
    rw [hmoveEq] at ht
    exact h.resolve t ht

theorem RenewalReady.renew
    (tables : ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection
      (Memory := Memory) objective pulsedSource)
    (pair : StagedRightOwnerPair (Memory := Memory) objective pulsedSource)
    (h : RenewalReady tables pair) (move : ProfiledRawJointLeftPhysicalSiblingMove objective) :
    RenewalReady tables (pair.renew objective pulsedSource pulsedSource_wins tables move
      (fun _ ↦ ((), ()))) := by
  rw [renew_eq_preRenewal_stepRight]
  exact open_pair_staged_ready tables pair h (preRenewal tables pair move)
    (preRenewal_valid tables pair h move) (preRenewal_right_move tables pair move)
    ((preRenewal_state tables pair move).trans h.anchor)

theorem open_pair_ready_progress
    (tables : ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection
      (Memory := Memory) objective pulsedSource)
    (pair : StagedRightOwnerPair (Memory := Memory) objective pulsedSource)
    (h : RenewalReady tables pair)
    (mid : OpenOwnerPair (Memory := Memory) objective pulsedSource)
    (hv : ProfiledRawJointRightOwnerFibreValid objective mid.right)
    (hmoveEq : mid.right.1 = pair.right.1)
    (hmidState : (mid.rightPhaseData objective pulsedSource).1.1 = pair.state) :
    let first := tables.ownerFibreRound objective pulsedSource pulsedSource_wins
      (mid.controls objective pulsedSource) ((), ()) .right
    strictOutputGrant first.2 = true ∨
      strictOutputGrant (tables.ownerFibreRound objective pulsedSource pulsedSource_wins
        first.1 ((), ()) .left).2 = true := by
  obtain ⟨family, direction, member, hm, hd⟩ := h.semantic
  have hd' : mid.right.1.1 = profiledRawJointRightPhysicalSiblingDescriptorOf
      objective family direction member := by rw [hmoveEq]; exact hd
  apply open_pair_right_left_progress tables mid hv family direction member hm hd'
  dsimp only
  rw [hmidState]
  apply h.resolve
  rw [← hmoveEq]
  exact hv.targetSafe objective _ ((), ()) _

/-- At the end of every return cycle, the last right round or the following
fresh left round grants. The local hypotheses persist by `RenewalReady.renew`. -/
theorem renewal_progress
    (tables : ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection
      (Memory := Memory) objective pulsedSource)
    (pair : StagedRightOwnerPair (Memory := Memory) objective pulsedSource)
    (h : RenewalReady tables pair) (move : ProfiledRawJointLeftPhysicalSiblingMove objective) :
    let mid := preRenewal tables pair move
    let first := tables.ownerFibreRound objective pulsedSource pulsedSource_wins
      (mid.controls objective pulsedSource) ((), ()) .right
    strictOutputGrant first.2 = true ∨
      strictOutputGrant (tables.ownerFibreRound objective pulsedSource pulsedSource_wins
        first.1 ((), ()) .left).2 = true :=
  open_pair_ready_progress tables pair h (preRenewal tables pair move)
    (preRenewal_valid tables pair h move) (preRenewal_right_move tables pair move)
    ((preRenewal_state tables pair move).trans h.anchor)

end
end PulsedSourceInstallationAudit
end DistributedSynthesis
