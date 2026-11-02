/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralHeterogeneousSeam
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledRawJointGuardedFirstPolicyHandoff

/-!
# The exact hidden seam hands off to the ordinary recurrent policy

The unconditional heterogeneous seam has a proof-side `true` projection.
That projection checks the exact root-pinned left-block monitor.  This file
forgets the product receiver coordinate and the finite two-letter guard,
then installs the checked literal child in the already existing ordinary
right-policy bank.

The Boolean selecting the projection occurs only in this proof-side
readback.  It is not an input to either local transition table.
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

/-- The root-pinned package checked by the exact (`true`) seam member. -/
noncomputable abbrev ProfiledRawJointLiteralExactLeftPackage
    (installed : ProfiledRawJointHybridCommonMoveData A strategy) :=
  profiledRawJointHybridExactLeftPolicy A hwin installed

/-- The exact receiver alphabet, exposed publicly for the projected play. -/
abbrev ProfiledRawJointLiteralExactLeftReceiverOutput
    (installed : ProfiledRawJointHybridCommonMoveData A strategy) :=
  ProfiledRawJointGuardedFirstLeftReceiverOutput A strategy
    (installed.world.oneSidedState A .left)
    (profiledRawJointHybridExactLeftRootPredicate A installed)
    (ProfiledRawJointLiteralExactLeftPackage A strategy hwin installed)

/-- The physical play of the proof-side exact projection.  The controller is
still the member of the one shared heterogeneous table; only its receiver
output is projected after the physical record has been produced. -/
noncomputable def profiledRawJointLiteralRightBothExactTruePlay
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (env : Nat → In₁ × In₂) :
    Nat → RealizedBlockRound In₁ In₂
      (ProfiledRawJointLiteralExactLeftReceiverOutput A strategy hwin
        installed) Out₂ :=
  let table :=
    profiledRawJointLiteralRightBothExactHeterogeneousLeftTable A strategy
      hwin installed
  let controller := table.memberController true
  BlockRecordMonitor.projectReceiverPlay Prod.snd
    (treePlay (narrowedInducedTree _ controller.labeledTree) env)

/-- The exact projected physical play wins the unguarded root-pinned
monitor.  This is the product-coordinate and prefix-guard erasure needed
before the ordinary-policy handoff can be reused. -/
theorem profiledRawJointLiteralRightBothExactTruePlay_wins
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (env : Nat → In₁ × In₂) :
    (profiledRawJointHybridExactLeftMonitor.{u, v, x, y, s,
      max u v y s} A installed
      (ProfiledRawJointLiteralExactLeftPackage A strategy hwin installed)
      ).WinsPlay
        (profiledRawJointLiteralRightBothExactTruePlay A strategy hwin
          installed env) := by
  let table :=
    profiledRawJointLiteralRightBothExactHeterogeneousLeftTable A strategy
      hwin installed
  let controller := table.memberController true
  let productPlay := treePlay
    (narrowedInducedTree _ controller.labeledTree) env
  let exactMonitor := profiledRawJointHybridExactLeftMonitor.{u, v, x, y, s,
    max u v y s} A installed
    (ProfiledRawJointLiteralExactLeftPackage A strategy hwin installed)
  have hproduct := table.memberController_base_wins true env
  have hcomap :
      (exactMonitor.restartAt exactMonitor.initial |>.comapReceiverOutput
        Prod.snd).WinsPlay productPlay := by
    simpa [table, controller, productPlay, exactMonitor,
      finiteCrossAnchorRestartFamily,
      finiteCrossAnchorHeterogeneousMonitor,
      finiteCrossAnchorHeterogeneousStart,
      BlockRecordMonitor.restartAt,
      BlockRecordMonitor.comapReceiverOutput] using hproduct
  have hexactRestart :=
    (BlockRecordMonitor.comapReceiverOutput_wins_iff
      (exactMonitor.restartAt exactMonitor.initial) Prod.snd productPlay).mp
      hcomap
  simpa [profiledRawJointLiteralRightBothExactTruePlay, table, controller,
    productPlay, exactMonitor, BlockRecordMonitor.restartAt] using
    hexactRestart

/-- The exact hidden member closes into the ordinary recurrent right-policy
bank.  The installed key is the literal child actually emitted by the shared
finite table, its recurrent control is exactly `run []`, and the monitor's
pending profile agrees with the active slot carried by that control.

This is the complete one-block handoff: after this checked exceptional
letter, no root predicate or hidden seam member remains in the continuation
state. -/
theorem
    exists_profiledRawJointLiteralRightBothExactTruePolicyRoot
    (installed : ProfiledRawJointHybridCommonMoveData A strategy)
    (env : Nat → In₁ × In₂) (n : Nat) (row : PairedEntryRow) :
    let initial := installed.world.oneSidedState A .left
    let RootPred := profiledRawJointHybridExactLeftRootPredicate A installed
    let package := ProfiledRawJointLiteralExactLeftPackage A strategy hwin
      installed
    let selected := profiledRawJointRootPinnedSelectedSource A strategy
      initial RootPred package
    let bank := profiledRawJointRootPinnedLiteralChildPolicyBank A strategy
      hwin initial RootPred package
    let base := profiledRawJointGuardedFirstLeftBlockMonitor.{u, v, x, y, s,
      max u v y s} A strategy initial RootPred package
        (installed.world.procTwoSlot A)
    let play := profiledRawJointLiteralRightBothExactTruePlay A strategy hwin
      installed env
    ∃ (child : ProfiledRawJointOneSidedLiteralChildCode A strategy selected)
        (target : ProfiledRawJointUnitRightPolicyMacro A strategy child.1
          (bank child)),
      child = (play n).2.1.target row ∧
      target.state = (bank child).run [] ∧
      (base.run play (n + 1)).2.2.1 row = some target.slot.2 := by
  classical
  let initial := installed.world.oneSidedState A .left
  let RootPred := profiledRawJointHybridExactLeftRootPredicate A installed
  let package := ProfiledRawJointLiteralExactLeftPackage A strategy hwin
    installed
  let selected := profiledRawJointRootPinnedSelectedSource A strategy
    initial RootPred package
  let bank := profiledRawJointRootPinnedLiteralChildPolicyBank A strategy
    hwin initial RootPred package
  let base := profiledRawJointGuardedFirstLeftBlockMonitor.{u, v, x, y, s,
    max u v y s} A strategy initial RootPred package
      (installed.world.procTwoSlot A)
  let allowed := profiledRawJointHybridExactLeftAllowed A installed package
  let play := profiledRawJointLiteralRightBothExactTruePlay A strategy hwin
    installed env
  have hexact : (base.firstLetterGuard allowed).WinsPlay play := by
    simpa [base, allowed, play, initial, RootPred, package] using
      (profiledRawJointLiteralRightBothExactTruePlay_wins A strategy hwin
        installed env)
  have hbase : base.WinsPlay play :=
    BlockRecordMonitor.firstLetterGuard_base_wins_of_wins base allowed play
      hexact
  have hbaseRestart : (base.restartAt base.initial).WinsPlay play := by
    simpa [BlockRecordMonitor.restartAt] using hbase
  have hsafeNext := base.restartAt_safe_of_wins
    (fun state ↦ state.2.2.2.2)
    (by
      intro state round hfalse
      change state.2.2.2.2 = false at hfalse
      change ((state.2.2.2.2 && _ && decide _ && decide _) = false)
      rw [hfalse]
      rfl)
    (by
      intro state hfalse
      change state.2.2.2.2 = false at hfalse
      change (if state.2.2.2.2 then _ else 1) = 1
      rw [hfalse]
      rfl)
    base.initial play hbaseRestart (n + 1)
  rw [BlockRecordMonitor.run] at hsafeNext
  simp only [base, profiledRawJointGuardedFirstLeftBlockMonitor,
    BlockRecordMonitor.restartAt, Bool.and_eq_true, decide_eq_true_eq] at hsafeNext
  have hclose := hsafeNext.2 row
  obtain ⟨slot, hslot⟩ : ∃ slot : ProfiledRawRightSlot A,
      ((play n).2.1.target row).1.family.right () = some slot := by
    cases hslot : ((play n).2.1.target row).1.family.right () with
    | none =>
        simp [profiledRawJointGuardedFirstLeftTargetProfiledState, hslot,
          erasePairedProfiledState, pairedLeftCloseTarget] at hclose
    | some slot => exact ⟨slot, rfl⟩
  have hpending :
      (base.run play (n + 1)).2.2.1 row = some slot.2 := by
    rw [BlockRecordMonitor.run]
    simp only [base, profiledRawJointGuardedFirstLeftBlockMonitor]
    simp [profiledRawJointGuardedFirstLeftTargetProfiledState, hslot,
      rightProfileOfProfiledState]
  let child := (play n).2.1.target row
  let target := profiledRawJointLiteralChildRightPolicyRoot A strategy selected
    bank child slot hslot
  exact ⟨child, target, rfl, rfl, hpending⟩

end

end DetParityAutomaton

end DistributedSynthesis
