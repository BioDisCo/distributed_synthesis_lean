/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleLiteralPrefixCurrentTailAdapter

/-!
# Finite target rows bridge consecutive literal tables

The recurrent block monitor stores, for every closing row, the action profile
of the finite target emitted at that row.  A fresh crossed table whose finite
descriptor is rooted at the target's live slot therefore emits exactly the
old closing action on its first row.  This is the finite-code form of the
dangerous switch seam; it needs no semantic target representative and no
leader or hierarchy observation.
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

/-! ## Winning physical tables: the two reusable row laws -/

section
omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]

/-- The first informed output of any winning left physical table is the
profile stored in its descriptor source. -/
theorem profiledRawJointLeftPhysicalSiblingWinningPlay_rootProfile
    (descriptor : ProfiledRawJointLeftPhysicalSiblingDescriptor A)
    (play : Nat → RealizedBlockRound In₁ In₂
      (ProfiledRawJointTargetLeftReceiverOutput
        (Out₁ := Out₁) (Out₂ := Out₂) (ProfiledRawJointUnitTarget A)) Out₂)
    (hwins : (profiledRawJointLeftPhysicalSiblingMonitor A descriptor false).WinsPlay
      play) :
    pairedLeftInformedForRow .first (play 0).2.1.physical =
      descriptor.source.2 (play 0).1 := by
  have hsafe := profiledRawJointTargetLeftBlockMonitor_safe_of_wins A
    (profiledRawJointUnitLeftTargetProjection A)
    (profiledRawJointLeftPhysicalSiblingAllowed A descriptor)
    descriptor.source play hwins 1
  rw [BlockRecordMonitor.run] at hsafe
  simp only [profiledRawJointTargetLeftBlockMonitor, Bool.and_eq_true,
    decide_eq_true_eq] at hsafe
  simpa [BlockRecordMonitor.run,
    profiledRawJointLeftPhysicalSiblingMonitor] using hsafe.1.1

/-- Right-table mirror of the generic root-profile law. -/
theorem profiledRawJointRightPhysicalSiblingWinningPlay_rootProfile
    (descriptor : ProfiledRawJointRightPhysicalSiblingDescriptor A)
    (play : Nat → RealizedBlockRound In₂ In₁
      (ProfiledRawJointTargetRightReceiverOutput
        (Out₁ := Out₁) (Out₂ := Out₂) (ProfiledRawJointUnitTarget A)) Out₁)
    (hwins : (profiledRawJointRightPhysicalSiblingMonitor A descriptor false).WinsPlay
      play) :
    pairedRightInformedForRow .first (play 0).2.1.physical =
      descriptor.source.2 (play 0).1 := by
  have hsafe := profiledRawJointTargetRightBlockMonitor_safe_of_wins A
    (profiledRawJointUnitRightTargetProjection A)
    (profiledRawJointRightPhysicalSiblingAllowed A descriptor)
    descriptor.source play hwins 1
  rw [BlockRecordMonitor.run] at hsafe
  simp only [profiledRawJointTargetRightBlockMonitor, Bool.and_eq_true,
    decide_eq_true_eq] at hsafe
  simpa [BlockRecordMonitor.run,
    profiledRawJointRightPhysicalSiblingMonitor] using hsafe.1.1

/-- A live target emitted by any winning right physical table is realized by
the following record at the same row. -/
theorem profiledRawJointRightPhysicalSiblingWinningPlay_delayedLiveSlot
    (descriptor : ProfiledRawJointRightPhysicalSiblingDescriptor A)
    (play : Nat → RealizedBlockRound In₂ In₁
      (ProfiledRawJointTargetRightReceiverOutput
        (Out₁ := Out₁) (Out₂ := Out₂) (ProfiledRawJointUnitTarget A)) Out₁)
    (hwins : (profiledRawJointRightPhysicalSiblingMonitor A descriptor false).WinsPlay
      play)
    (n : Nat) (row : PairedEntryRow) (slot : ProfiledRawLeftSlot A)
    (hlive : ((play n).2.1.target row).family.left () = some slot) :
    pairedRightClosingForRow row (play (n + 1)).2.1.physical =
      slot.2 ((play (n + 1)).1.2, (play (n + 1)).1.1) := by
  let monitor := profiledRawJointRightPhysicalSiblingMonitor A descriptor false
  have hpending :
      (monitor.run play (n + 1)).2.2.1 row = some slot.2 := by
    rw [BlockRecordMonitor.run]
    simp [monitor, profiledRawJointTargetRightBlockMonitor,
      profiledRawJointUnitRightTargetProjection, leftProfileOfProfiledState,
      hlive]
  have hsafe := profiledRawJointTargetRightBlockMonitor_safe_of_wins A
    (profiledRawJointUnitRightTargetProjection A)
    (profiledRawJointRightPhysicalSiblingAllowed A descriptor)
    descriptor.source play hwins (n + 2)
  rw [show n + 2 = (n + 1) + 1 by omega, BlockRecordMonitor.run] at hsafe
  simp only [profiledRawJointTargetRightBlockMonitor, Bool.and_eq_true,
    decide_eq_true_eq] at hsafe
  exact hsafe.1.2 row slot.2 hpending

/-- Left-table mirror of the generic delayed live-slot law. -/
theorem profiledRawJointLeftPhysicalSiblingWinningPlay_delayedLiveSlot
    (descriptor : ProfiledRawJointLeftPhysicalSiblingDescriptor A)
    (play : Nat → RealizedBlockRound In₁ In₂
      (ProfiledRawJointTargetLeftReceiverOutput
        (Out₁ := Out₁) (Out₂ := Out₂) (ProfiledRawJointUnitTarget A)) Out₂)
    (hwins : (profiledRawJointLeftPhysicalSiblingMonitor A descriptor false).WinsPlay
      play)
    (n : Nat) (row : PairedEntryRow) (slot : ProfiledRawRightSlot A)
    (hlive : ((play n).2.1.target row).family.right () = some slot) :
    pairedLeftClosingForRow row (play (n + 1)).2.1.physical =
      slot.2 ((play (n + 1)).1.2, (play (n + 1)).1.1) := by
  let monitor := profiledRawJointLeftPhysicalSiblingMonitor A descriptor false
  have hpending :
      (monitor.run play (n + 1)).2.2.1 row = some slot.2 := by
    rw [BlockRecordMonitor.run]
    simp [monitor, profiledRawJointTargetLeftBlockMonitor,
      profiledRawJointUnitLeftTargetProjection, rightProfileOfProfiledState,
      hlive]
  have hsafe := profiledRawJointTargetLeftBlockMonitor_safe_of_wins A
    (profiledRawJointUnitLeftTargetProjection A)
    (profiledRawJointLeftPhysicalSiblingAllowed A descriptor)
    descriptor.source play hwins (n + 2)
  rw [show n + 2 = (n + 1) + 1 by omega, BlockRecordMonitor.run] at hsafe
  simp only [profiledRawJointTargetLeftBlockMonitor, Bool.and_eq_true,
    decide_eq_true_eq] at hsafe
  exact hsafe.1.2 row slot.2 hpending

end

/-! ## Fresh roots read the descriptor's stored profile -/

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- At the first letter of a winning, well-rooted left literal table, the
fresh `.first` informed output is exactly its finite descriptor source
profile. -/
theorem profiledRawJointLeftLiteralPrefixCurrentPhysicalPlay_rootProfile
    (move : ProfiledRawJointGuardedCommonLeftLiteralCrossMove A)
    (hrooted : ProfiledRawJointLeftLiteralPrefixWellRooted A move)
    (anchor : Bool) (env : Nat → In₁ × In₂) :
    pairedLeftInformedForRow .first
        ((profiledRawJointLeftLiteralPrefixCurrentPhysicalPlay A move anchor
          env 0).2.1.physical) =
      (move.1.descriptor anchor).base.source.2 (env 0) := by
  let descriptor := (move.1.descriptor anchor).base
  let monitor := profiledRawJointLeftPhysicalSiblingMonitor A descriptor false
  let play :=
    profiledRawJointLeftLiteralPrefixCurrentPhysicalPlay A move anchor env
  have hwins : monitor.WinsPlay play :=
    profiledRawJointLeftLiteralPrefixCurrentPhysicalPlay_wins A move hrooted
      anchor env
  have hsafe := profiledRawJointTargetLeftBlockMonitor_safe_of_wins A
    (profiledRawJointUnitLeftTargetProjection A)
    (profiledRawJointLeftPhysicalSiblingAllowed A descriptor)
    descriptor.source play hwins 1
  rw [BlockRecordMonitor.run] at hsafe
  simp only [profiledRawJointTargetLeftBlockMonitor, Bool.and_eq_true,
    decide_eq_true_eq] at hsafe
  simpa [descriptor, monitor, play, BlockRecordMonitor.run,
    profiledRawJointLeftPhysicalSiblingMonitor] using hsafe.1.1

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Right-table mirror of the fresh-root profile equation. -/
theorem profiledRawJointRightLiteralPrefixCurrentPhysicalPlay_rootProfile
    (move : ProfiledRawJointGuardedCommonRightLiteralCrossMove A)
    (hrooted : ProfiledRawJointRightLiteralPrefixWellRooted A move)
    (anchor : Bool) (env : Nat → In₂ × In₁) :
    pairedRightInformedForRow .first
        ((profiledRawJointRightLiteralPrefixCurrentPhysicalPlay A move anchor
          env 0).2.1.physical) =
      (move.1.descriptor anchor).base.source.2 (env 0) := by
  let descriptor := (move.1.descriptor anchor).base
  let monitor := profiledRawJointRightPhysicalSiblingMonitor A descriptor false
  let play :=
    profiledRawJointRightLiteralPrefixCurrentPhysicalPlay A move anchor env
  have hwins : monitor.WinsPlay play :=
    profiledRawJointRightLiteralPrefixCurrentPhysicalPlay_wins A move hrooted
      anchor env
  have hsafe := profiledRawJointTargetRightBlockMonitor_safe_of_wins A
    (profiledRawJointUnitRightTargetProjection A)
    (profiledRawJointRightPhysicalSiblingAllowed A descriptor)
    descriptor.source play hwins 1
  rw [BlockRecordMonitor.run] at hsafe
  simp only [profiledRawJointTargetRightBlockMonitor, Bool.and_eq_true,
    decide_eq_true_eq] at hsafe
  simpa [descriptor, monitor, play, BlockRecordMonitor.run,
    profiledRawJointRightPhysicalSiblingMonitor] using hsafe.1.1

/-! ## A live target is the next closing profile -/

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- If a right literal table emits a target whose crossed left slot is
`slot`, its next physical record realizes exactly `slot`'s stored action
profile.  The statement is valid at an arbitrary rational-controller depth. -/
theorem profiledRawJointRightLiteralPrefixCurrentPhysicalPlay_delayedLiveSlot
    (move : ProfiledRawJointGuardedCommonRightLiteralCrossMove A)
    (hrooted : ProfiledRawJointRightLiteralPrefixWellRooted A move)
    (anchor : Bool) (env : Nat → In₂ × In₁) (n : Nat)
    (row : PairedEntryRow) (slot : ProfiledRawLeftSlot A)
    (hlive :
      ((profiledRawJointRightLiteralPrefixCurrentPhysicalPlay A move anchor
        env n).2.1.target row).family.left () = some slot) :
    pairedRightClosingForRow row
        ((profiledRawJointRightLiteralPrefixCurrentPhysicalPlay A move anchor
          env (n + 1)).2.1.physical) =
      slot.2 ((env (n + 1)).2, (env (n + 1)).1) := by
  let descriptor := (move.1.descriptor anchor).base
  let monitor := profiledRawJointRightPhysicalSiblingMonitor A descriptor false
  let play :=
    profiledRawJointRightLiteralPrefixCurrentPhysicalPlay A move anchor env
  have hwins : monitor.WinsPlay play :=
    profiledRawJointRightLiteralPrefixCurrentPhysicalPlay_wins A move hrooted
      anchor env
  have hpending :
      (monitor.run play (n + 1)).2.2.1 row = some slot.2 := by
    rw [BlockRecordMonitor.run]
    simp [monitor, profiledRawJointTargetRightBlockMonitor,
      profiledRawJointUnitRightTargetProjection, leftProfileOfProfiledState,
      play, hlive]
  have hsafe := profiledRawJointTargetRightBlockMonitor_safe_of_wins A
    (profiledRawJointUnitRightTargetProjection A)
    (profiledRawJointRightPhysicalSiblingAllowed A descriptor)
    descriptor.source play hwins (n + 2)
  rw [show n + 2 = (n + 1) + 1 by omega, BlockRecordMonitor.run] at hsafe
  simp only [profiledRawJointTargetRightBlockMonitor, Bool.and_eq_true,
    decide_eq_true_eq] at hsafe
  exact hsafe.1.2 row slot.2 hpending

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Left-to-right delayed live-slot mirror. -/
theorem profiledRawJointLeftLiteralPrefixCurrentPhysicalPlay_delayedLiveSlot
    (move : ProfiledRawJointGuardedCommonLeftLiteralCrossMove A)
    (hrooted : ProfiledRawJointLeftLiteralPrefixWellRooted A move)
    (anchor : Bool) (env : Nat → In₁ × In₂) (n : Nat)
    (row : PairedEntryRow) (slot : ProfiledRawRightSlot A)
    (hlive :
      ((profiledRawJointLeftLiteralPrefixCurrentPhysicalPlay A move anchor
        env n).2.1.target row).family.right () = some slot) :
    pairedLeftClosingForRow row
        ((profiledRawJointLeftLiteralPrefixCurrentPhysicalPlay A move anchor
          env (n + 1)).2.1.physical) =
      slot.2 ((env (n + 1)).2, (env (n + 1)).1) := by
  let descriptor := (move.1.descriptor anchor).base
  let monitor := profiledRawJointLeftPhysicalSiblingMonitor A descriptor false
  let play :=
    profiledRawJointLeftLiteralPrefixCurrentPhysicalPlay A move anchor env
  have hwins : monitor.WinsPlay play :=
    profiledRawJointLeftLiteralPrefixCurrentPhysicalPlay_wins A move hrooted
      anchor env
  have hpending :
      (monitor.run play (n + 1)).2.2.1 row = some slot.2 := by
    rw [BlockRecordMonitor.run]
    simp [monitor, profiledRawJointTargetLeftBlockMonitor,
      profiledRawJointUnitLeftTargetProjection, rightProfileOfProfiledState,
      play, hlive]
  have hsafe := profiledRawJointTargetLeftBlockMonitor_safe_of_wins A
    (profiledRawJointUnitLeftTargetProjection A)
    (profiledRawJointLeftPhysicalSiblingAllowed A descriptor)
    descriptor.source play hwins (n + 2)
  rw [show n + 2 = (n + 1) + 1 by omega, BlockRecordMonitor.run] at hsafe
  simp only [profiledRawJointTargetLeftBlockMonitor, Bool.and_eq_true,
    decide_eq_true_eq] at hsafe
  exact hsafe.1.2 row slot.2 hpending

/-! ## Exact finite-code switch seams -/

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- A right target and a fresh left table rooted at its live slot satisfy the
correct row-aware strict-switch equation.  The old row is arbitrary; the new
receiver uses its actual fresh row `.first`. -/
theorem profiledRawJointRightLiteralPrefixCurrentPhysicalPlay_switchesToFreshLeft
    (rightMove : ProfiledRawJointGuardedCommonRightLiteralCrossMove A)
    (hrightRooted :
      ProfiledRawJointRightLiteralPrefixWellRooted A rightMove)
    (rightAnchor : Bool) (rightEnv : Nat → In₂ × In₁) (n : Nat)
    (rightRow : PairedEntryRow) (slot : ProfiledRawLeftSlot A)
    (hlive :
      ((profiledRawJointRightLiteralPrefixCurrentPhysicalPlay A rightMove
        rightAnchor rightEnv n).2.1.target rightRow).family.left () =
          some slot)
    (leftMove : ProfiledRawJointGuardedCommonLeftLiteralCrossMove A)
    (hleftRooted : ProfiledRawJointLeftLiteralPrefixWellRooted A leftMove)
    (leftAnchor : Bool)
    (hsource : (leftMove.1.descriptor leftAnchor).base.source = slot) :
    let nextInput : In₁ × In₂ :=
      ((rightEnv (n + 1)).2, (rightEnv (n + 1)).1)
    pairedRightClosingForRow rightRow
        ((profiledRawJointRightLiteralPrefixCurrentPhysicalPlay A rightMove
          rightAnchor rightEnv (n + 1)).2.1.physical) =
      pairedLeftInformedForRow .first
        ((profiledRawJointLeftLiteralPrefixCurrentPhysicalPlay A leftMove
          leftAnchor (fun _ ↦ nextInput) 0).2.1.physical) := by
  dsimp only
  rw [profiledRawJointRightLiteralPrefixCurrentPhysicalPlay_delayedLiveSlot A
    rightMove hrightRooted rightAnchor rightEnv n rightRow slot hlive]
  rw [profiledRawJointLeftLiteralPrefixCurrentPhysicalPlay_rootProfile A
    leftMove hleftRooted leftAnchor]
  rw [hsource]

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Fresh-right mirror of the exact finite-code switch seam. -/
theorem profiledRawJointLeftLiteralPrefixCurrentPhysicalPlay_switchesToFreshRight
    (leftMove : ProfiledRawJointGuardedCommonLeftLiteralCrossMove A)
    (hleftRooted : ProfiledRawJointLeftLiteralPrefixWellRooted A leftMove)
    (leftAnchor : Bool) (leftEnv : Nat → In₁ × In₂) (n : Nat)
    (leftRow : PairedEntryRow) (slot : ProfiledRawRightSlot A)
    (hlive :
      ((profiledRawJointLeftLiteralPrefixCurrentPhysicalPlay A leftMove
        leftAnchor leftEnv n).2.1.target leftRow).family.right () = some slot)
    (rightMove : ProfiledRawJointGuardedCommonRightLiteralCrossMove A)
    (hrightRooted :
      ProfiledRawJointRightLiteralPrefixWellRooted A rightMove)
    (rightAnchor : Bool)
    (hsource : (rightMove.1.descriptor rightAnchor).base.source = slot) :
    let nextInput : In₂ × In₁ :=
      ((leftEnv (n + 1)).2, (leftEnv (n + 1)).1)
    pairedLeftClosingForRow leftRow
        ((profiledRawJointLeftLiteralPrefixCurrentPhysicalPlay A leftMove
          leftAnchor leftEnv (n + 1)).2.1.physical) =
      pairedRightInformedForRow .first
        ((profiledRawJointRightLiteralPrefixCurrentPhysicalPlay A rightMove
          rightAnchor (fun _ ↦ nextInput) 0).2.1.physical) := by
  dsimp only
  rw [profiledRawJointLeftLiteralPrefixCurrentPhysicalPlay_delayedLiveSlot A
    leftMove hleftRooted leftAnchor leftEnv n leftRow slot hlive]
  rw [profiledRawJointRightLiteralPrefixCurrentPhysicalPlay_rootProfile A
    rightMove hrightRooted rightAnchor]
  rw [hsource]

end

end DetParityAutomaton

end DistributedSynthesis
