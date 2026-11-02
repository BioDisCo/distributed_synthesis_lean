/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledEndToEndInitialRegularization

/-!
# Readback of the one-policy initial controllers

This file inverts the sticky monitors used to stream the two initial
orientations.  The statements apply to every controller returned by sender
narrowing, not merely to the raw witnesses from which existence was proved.
Consequently every staged state seen at a possible reversal belongs to the
image of the one common rational policy, has the checked delayed DPA target,
and carries the overlap profile checked against the following round.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Inhabited In₁] [Inhabited In₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

open PairedStrategyMemory

namespace PairedStrategyMemory.PairedInitialProfiledRationalPackage

/-! ## Left-initial orientation -/

section
omit [Inhabited In₁] [Inhabited In₂]

/-- Once the one-policy left-initial monitor becomes unsafe, it remains
unsafe. -/
theorem endToEndInitialLeft_safe_false_persists
    (package : PairedInitialProfiledRationalPackage A)
    (play : Nat → RealizedBlockRound In₁ In₂
      (EndToEndInitialLeftReceiverOutput A) Out₂)
    {N : Nat}
    (hfalse : ((endToEndInitialLeftBlockMonitor A package).run play N).2 = false) :
    ∀ n, N ≤ n →
      ((endToEndInitialLeftBlockMonitor A package).run play n).2 = false := by
  classical
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  induction k with
  | zero => simpa using hfalse
  | succ k ih =>
      rw [Nat.add_succ, BlockRecordMonitor.run]
      simp only [endToEndInitialLeftBlockMonitor]
      change
        (((endToEndInitialLeftBlockMonitor A package).run play (N + k)).2 &&
          decide _ && decide _) = false
      rw [ih (Nat.le_add_right N k)]
      rfl

/-- A winning left-initial monitor play is safe at every prefix. -/
theorem endToEndInitialLeft_safe_of_wins
    (package : PairedInitialProfiledRationalPackage A)
    (play : Nat → RealizedBlockRound In₁ In₂
      (EndToEndInitialLeftReceiverOutput A) Out₂)
    (hwin : (endToEndInitialLeftBlockMonitor A package).WinsPlay play)
    (n : Nat) :
    ((endToEndInitialLeftBlockMonitor A package).run play n).2 = true := by
  by_contra hnot
  have hfalse :
      ((endToEndInitialLeftBlockMonitor A package).run play n).2 = false :=
    Bool.eq_false_of_not_eq_true hnot
  have hpersist := endToEndInitialLeft_safe_false_persists A package play hfalse
  have heventual : ∀ k, n ≤ k →
      (endToEndInitialLeftBlockMonitor A package).priority
        ((endToEndInitialLeftBlockMonitor A package).run play k) = 1 := by
    intro k hk
    have hs := hpersist k hk
    change
      (if ((endToEndInitialLeftBlockMonitor A package).run play k).2
        then _ else 1) = 1
    rw [hs]
    rfl
  exact not_natSeqMinEvenParity_of_eventually_one _ n heventual hwin

/-- Every state emitted on a winning left-initial play is a checked state in
the image of the one common rational policy. -/
theorem endToEndInitialLeft_sourceOK_of_wins
    (package : PairedInitialProfiledRationalPackage A)
    (play : Nat → RealizedBlockRound In₁ In₂
      (EndToEndInitialLeftReceiverOutput A) Out₂)
    (hwin : (endToEndInitialLeftBlockMonitor A package).WinsPlay play)
    (n : Nat) :
    endToEndInitialLeftSourceOK A package
      ((endToEndInitialLeftBlockMonitor A package).run play n).1.1
      (endToEndInitialLeftPhysicalLetter A (play n))
      (play n).2.1.2 := by
  classical
  have hsafeNext := endToEndInitialLeft_safe_of_wins A package play hwin (n + 1)
  rw [BlockRecordMonitor.run] at hsafeNext
  simp only [endToEndInitialLeftBlockMonitor, Bool.and_eq_true,
    decide_eq_true_eq] at hsafeNext
  exact hsafeNext.1.2

/-- The pending overlap profile on a winning left-initial play agrees with
the current physical informed output. -/
theorem endToEndInitialLeft_overlapOK_of_wins
    (package : PairedInitialProfiledRationalPackage A)
    (play : Nat → RealizedBlockRound In₁ In₂
      (EndToEndInitialLeftReceiverOutput A) Out₂)
    (hwin : (endToEndInitialLeftBlockMonitor A package).WinsPlay play)
    (n : Nat) :
    endToEndInitialLeftOverlapOK A
      ((endToEndInitialLeftBlockMonitor A package).run play n).1.2
      (play n) := by
  classical
  have hsafeNext := endToEndInitialLeft_safe_of_wins A package play hwin (n + 1)
  rw [BlockRecordMonitor.run] at hsafeNext
  simp only [endToEndInitialLeftBlockMonitor, Bool.and_eq_true,
    decide_eq_true_eq] at hsafeNext
  exact hsafeNext.2

/-- Image membership is strong enough to activate the exact guarded subtree
of the common policy.  In particular the target equality and the profiled
root guard refer to the very state emitted by the streaming controller. -/
theorem endToEndInitialLeft_activate_of_sourceOK
    (package : PairedInitialProfiledRationalPackage A)
    (scan : InitialBlockScan A)
    (letter : InitialLeftLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (source : PairedInitialProfiledBankState A)
    (hsource : endToEndInitialLeftSourceOK A package scan letter source) :
    ∃ profile : ProcOneEntryOverlapProfile
        (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁),
      ∃ direction : PairedEntryDirection (In₁ := In₁) (In₂ := In₂),
        ∃ next : PairedEntryDirection (In₁ := In₁) (In₂ := In₂) →
            PairedProfiledTreeState A,
          source.1 = some (Sum.inl profile) ∧
          package.next direction = source ∧
          erasePairedProfiledState A source.2 =
            initialLeftDelayedTarget A scan letter ∧
          pairedProfiledEntryRootGuard A source.2
            profile.Matches (fun _ => True) next ∧
          ∀ first,
            (package.guardedPolicyAt A direction).run [first] =
              (none, next first) := by
  rcases hsource with ⟨⟨profile, hpending⟩, htarget, direction, himage⟩
  rcases package.exists_profiledRootGuard_at_image_left A direction source profile
      himage hpending with ⟨next, hguard, hchildren⟩
  exact ⟨profile, direction, next, hpending, himage, htarget, hguard, hchildren⟩

end

/-- Proof-side activation witness at one streamed left-initial boundary.
The runtime key is the finite `source`.  The direction may contain an
arbitrarily long finite history and is retained only as evidence that this
source occurs in the common global run; it is not local control state. -/
structure EndToEndInitialLeftActivation
    (package : PairedInitialProfiledRationalPackage A)
    (scan : InitialBlockScan A)
    (letter : InitialLeftLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (source : PairedInitialProfiledBankState A) where
  profile : ProcOneEntryOverlapProfile
    (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)
  direction : PairedEntryDirection (In₁ := In₁) (In₂ := In₂)
  pending : source.1 = some (Sum.inl profile)
  image : package.next direction = source
  target : erasePairedProfiledState A source.2 =
    initialLeftDelayedTarget A scan letter

omit [Inhabited In₁] [Inhabited In₂] in
theorem nonempty_endToEndInitialLeftActivation_of_sourceOK
    (package : PairedInitialProfiledRationalPackage A)
    (scan : InitialBlockScan A)
    (letter : InitialLeftLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (source : PairedInitialProfiledBankState A)
    (hsource : endToEndInitialLeftSourceOK A package scan letter source) :
    Nonempty (EndToEndInitialLeftActivation A package scan letter source) := by
  rcases hsource with ⟨⟨profile, hpending⟩, htarget, direction, himage⟩
  exact ⟨⟨profile, direction, hpending, himage, htarget⟩⟩

/-- The guarded-first policy selected by an activation key is definitionally
derived from the common global policy. -/
noncomputable def EndToEndInitialLeftActivation.policy
    {package : PairedInitialProfiledRationalPackage A}
    {scan : InitialBlockScan A}
    {letter : InitialLeftLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)}
    {source : PairedInitialProfiledBankState A}
    (activation : EndToEndInitialLeftActivation A package scan letter source) :
    (rightProfiledGuardedAutomaton A source.2
      activation.profile).RationalTransitionPolicy :=
  package.profiledGuardedPolicyAt_image_left A activation.direction source
    activation.profile activation.image activation.pending

/-- Concrete play generated by an arbitrary narrowed left-initial controller. -/
def endToEndInitialLeftControllerPlay
    (package : PairedInitialProfiledRationalPackage A)
    (controller : TransitionRationalTree.{v, max u v x y s, max u v x y s}
      In₂ (NarrowedBlockLabel In₁ In₂
        (EndToEndInitialLeftReceiverOutput A) Out₂
        (endToEndInitialLeftBlockMonitor A package).State))
    (env : Nat → In₁ × In₂) :
    Nat → RealizedBlockRound In₁ In₂
      (EndToEndInitialLeftReceiverOutput A) Out₂ :=
  treePlay
    (narrowedInducedTree (endToEndInitialLeftBlockMonitor A package)
      controller.labeledTree) env

omit [Inhabited In₁] [Inhabited In₂] in
/-- All-threads winning of an arbitrary narrowed controller gives ordinary
monitor winning on every concrete environment. -/
theorem endToEndInitialLeftControllerPlay_wins
    (package : PairedInitialProfiledRationalPackage A)
    (controller : TransitionRationalTree.{v, max u v x y s, max u v x y s}
      In₂ (NarrowedBlockLabel In₁ In₂
        (EndToEndInitialLeftReceiverOutput A) Out₂
        (endToEndInitialLeftBlockMonitor A package).State))
    (hthreads : NarrowedAllThreadsWin (endToEndInitialLeftBlockMonitor A package)
      controller.labeledTree)
    (env : Nat → In₁ × In₂) :
    (endToEndInitialLeftBlockMonitor A package).WinsPlay
      (endToEndInitialLeftControllerPlay A package controller env) := by
  let monitor := endToEndInitialLeftBlockMonitor A package
  let tree := narrowedInducedTree monitor controller.labeledTree
  have htree := narrowedInducedTree_winningTree_of_allThreadsWin monitor hthreads
  exact (monitor.lift_winningTree_iff tree).mp htree env

/-- Physical all-left word carried by an arbitrary realized controller play. -/
def endToEndInitialLeftPlayWord
    (play : Nat -> RealizedBlockRound In₁ In₂
      (EndToEndInitialLeftReceiverOutput A) Out₂) :
    OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂) :=
  fun n =>
    let physical := endToEndInitialLeftPhysicalLetter A (play n)
    leftRoundRecord physical.1 physical.2.1.informedOne physical.2.2

section
omit [Inhabited In₁] [Inhabited In₂]

/-- The first component of the arbitrary-play monitor scan is exactly the DPA
run over its physical all-left word. -/
theorem endToEndInitialLeft_run_state_eq
    (package : PairedInitialProfiledRationalPackage A)
    (play : Nat -> RealizedBlockRound In₁ In₂
      (EndToEndInitialLeftReceiverOutput A) Out₂) : ∀ n,
    ((endToEndInitialLeftBlockMonitor A package).run play n).1.1.1 =
      A.run (endToEndInitialLeftPlayWord A play) n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [BlockRecordMonitor.run, DetParityAutomaton.run]
      simp only [endToEndInitialLeftBlockMonitor, initialLeftScanStep,
        initialBlockScanStep, endToEndInitialLeftPlayWord]
      change A.step
        (((endToEndInitialLeftBlockMonitor A package).run play n).1.1.1)
        (leftRoundRecord (endToEndInitialLeftPhysicalLetter A (play n)).1
          (endToEndInitialLeftPhysicalLetter A (play n)).2.1.informedOne
          (endToEndInitialLeftPhysicalLetter A (play n)).2.2) = _
      rw [ih]
      rfl

/-- Winning the left initial monitor is already semantic DPA acceptance when
the environment remains in that orientation forever. -/
theorem endToEndInitialLeftPlay_accepts_of_wins
    (package : PairedInitialProfiledRationalPackage A)
    (play : Nat -> RealizedBlockRound In₁ In₂
      (EndToEndInitialLeftReceiverOutput A) Out₂)
    (hwins : (endToEndInitialLeftBlockMonitor A package).WinsPlay play) :
    A.Accepts (endToEndInitialLeftPlayWord A play) := by
  unfold BlockRecordMonitor.WinsPlay at hwins
  have heq :
      (fun n => (endToEndInitialLeftBlockMonitor A package).priority
        ((endToEndInitialLeftBlockMonitor A package).run play n)) =
      fun n => A.priority (A.run (endToEndInitialLeftPlayWord A play) n) + 2 := by
    funext n
    have hsafe := endToEndInitialLeft_safe_of_wins A package play hwins n
    change (if ((endToEndInitialLeftBlockMonitor A package).run play n).2
      then A.priority
        ((endToEndInitialLeftBlockMonitor A package).run play n).1.1.1 + 2
      else 1) = _
    rw [hsafe, if_pos rfl, endToEndInitialLeft_run_state_eq A package play n]
  rw [heq] at hwins
  exact (natSeqMinEvenParity_add_const (d := 2) ⟨1, rfl⟩).mp hwins

/-- Controller-level boundary inversion for the left-initial orientation. -/
theorem endToEndInitialLeftController_sourceOK
    (package : PairedInitialProfiledRationalPackage A)
    (controller : TransitionRationalTree.{v, max u v x y s, max u v x y s}
      In₂ (NarrowedBlockLabel In₁ In₂
        (EndToEndInitialLeftReceiverOutput A) Out₂
        (endToEndInitialLeftBlockMonitor A package).State))
    (hthreads : NarrowedAllThreadsWin (endToEndInitialLeftBlockMonitor A package)
      controller.labeledTree)
    (env : Nat → In₁ × In₂) (n : Nat) :
    endToEndInitialLeftSourceOK A package
      ((endToEndInitialLeftBlockMonitor A package).run
        (endToEndInitialLeftControllerPlay A package controller env) n).1.1
      (endToEndInitialLeftPhysicalLetter A
        (endToEndInitialLeftControllerPlay A package controller env n))
      (endToEndInitialLeftControllerPlay A package controller env n).2.1.2 :=
  endToEndInitialLeft_sourceOK_of_wins A package _
    (endToEndInitialLeftControllerPlay_wins A package controller hthreads env) n

theorem nonempty_endToEndInitialLeftController_activation
    (package : PairedInitialProfiledRationalPackage A)
    (controller : TransitionRationalTree.{v, max u v x y s, max u v x y s}
      In₂ (NarrowedBlockLabel In₁ In₂
        (EndToEndInitialLeftReceiverOutput A) Out₂
        (endToEndInitialLeftBlockMonitor A package).State))
    (hthreads : NarrowedAllThreadsWin (endToEndInitialLeftBlockMonitor A package)
      controller.labeledTree)
    (env : Nat → In₁ × In₂) (n : Nat) :
    Nonempty (EndToEndInitialLeftActivation A package
      ((endToEndInitialLeftBlockMonitor A package).run
        (endToEndInitialLeftControllerPlay A package controller env) n).1.1
      (endToEndInitialLeftPhysicalLetter A
        (endToEndInitialLeftControllerPlay A package controller env n))
      (endToEndInitialLeftControllerPlay A package controller env n).2.1.2) :=
  nonempty_endToEndInitialLeftActivation_of_sourceOK A package _ _ _
    (endToEndInitialLeftController_sourceOK A package controller hthreads env n)

end

/-! ## Right-initial orientation -/

section
omit [Inhabited In₁] [Inhabited In₂]

theorem endToEndInitialRight_safe_false_persists
    (package : PairedInitialProfiledRationalPackage A)
    (play : Nat → RealizedBlockRound In₂ In₁
      (EndToEndInitialRightReceiverOutput A) Out₁)
    {N : Nat}
    (hfalse : ((endToEndInitialRightBlockMonitor A package).run play N).2 = false) :
    ∀ n, N ≤ n →
      ((endToEndInitialRightBlockMonitor A package).run play n).2 = false := by
  classical
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  induction k with
  | zero => simpa using hfalse
  | succ k ih =>
      rw [Nat.add_succ, BlockRecordMonitor.run]
      simp only [endToEndInitialRightBlockMonitor]
      change
        (((endToEndInitialRightBlockMonitor A package).run play (N + k)).2 &&
          decide _ && decide _) = false
      rw [ih (Nat.le_add_right N k)]
      rfl

theorem endToEndInitialRight_safe_of_wins
    (package : PairedInitialProfiledRationalPackage A)
    (play : Nat → RealizedBlockRound In₂ In₁
      (EndToEndInitialRightReceiverOutput A) Out₁)
    (hwin : (endToEndInitialRightBlockMonitor A package).WinsPlay play)
    (n : Nat) :
    ((endToEndInitialRightBlockMonitor A package).run play n).2 = true := by
  by_contra hnot
  have hfalse :
      ((endToEndInitialRightBlockMonitor A package).run play n).2 = false :=
    Bool.eq_false_of_not_eq_true hnot
  have hpersist := endToEndInitialRight_safe_false_persists A package play hfalse
  have heventual : ∀ k, n ≤ k →
      (endToEndInitialRightBlockMonitor A package).priority
        ((endToEndInitialRightBlockMonitor A package).run play k) = 1 := by
    intro k hk
    have hs := hpersist k hk
    change
      (if ((endToEndInitialRightBlockMonitor A package).run play k).2
        then _ else 1) = 1
    rw [hs]
    rfl
  exact not_natSeqMinEvenParity_of_eventually_one _ n heventual hwin

theorem endToEndInitialRight_sourceOK_of_wins
    (package : PairedInitialProfiledRationalPackage A)
    (play : Nat → RealizedBlockRound In₂ In₁
      (EndToEndInitialRightReceiverOutput A) Out₁)
    (hwin : (endToEndInitialRightBlockMonitor A package).WinsPlay play)
    (n : Nat) :
    endToEndInitialRightSourceOK A package
      ((endToEndInitialRightBlockMonitor A package).run play n).1.1
      (endToEndInitialRightPhysicalLetter A (play n))
      (play n).2.1.2 := by
  classical
  have hsafeNext := endToEndInitialRight_safe_of_wins A package play hwin (n + 1)
  rw [BlockRecordMonitor.run] at hsafeNext
  simp only [endToEndInitialRightBlockMonitor, Bool.and_eq_true,
    decide_eq_true_eq] at hsafeNext
  exact hsafeNext.1.2

theorem endToEndInitialRight_overlapOK_of_wins
    (package : PairedInitialProfiledRationalPackage A)
    (play : Nat → RealizedBlockRound In₂ In₁
      (EndToEndInitialRightReceiverOutput A) Out₁)
    (hwin : (endToEndInitialRightBlockMonitor A package).WinsPlay play)
    (n : Nat) :
    endToEndInitialRightOverlapOK A
      ((endToEndInitialRightBlockMonitor A package).run play n).1.2
      (play n) := by
  classical
  have hsafeNext := endToEndInitialRight_safe_of_wins A package play hwin (n + 1)
  rw [BlockRecordMonitor.run] at hsafeNext
  simp only [endToEndInitialRightBlockMonitor, Bool.and_eq_true,
    decide_eq_true_eq] at hsafeNext
  exact hsafeNext.2

theorem endToEndInitialRight_activate_of_sourceOK
    (package : PairedInitialProfiledRationalPackage A)
    (scan : InitialBlockScan A)
    (letter : InitialRightLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (source : PairedInitialProfiledBankState A)
    (hsource : endToEndInitialRightSourceOK A package scan letter source) :
    ∃ profile : ProcTwoEntryOverlapProfile
        (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂),
      ∃ direction : PairedEntryDirection (In₁ := In₁) (In₂ := In₂),
        ∃ next : PairedEntryDirection (In₁ := In₁) (In₂ := In₂) →
            PairedProfiledTreeState A,
          source.1 = some (Sum.inr profile) ∧
          package.next direction = source ∧
          erasePairedProfiledState A source.2 =
            initialRightDelayedTarget A scan letter ∧
          pairedProfiledEntryRootGuard A source.2
            (fun _ => True) profile.Matches next ∧
          ∀ first,
            (package.guardedPolicyAt A direction).run [first] =
              (none, next first) := by
  rcases hsource with ⟨⟨profile, hpending⟩, htarget, direction, himage⟩
  rcases package.exists_profiledRootGuard_at_image_right A direction source profile
      himage hpending with ⟨next, hguard, hchildren⟩
  exact ⟨profile, direction, next, hpending, himage, htarget, hguard, hchildren⟩

end

structure EndToEndInitialRightActivation
    (package : PairedInitialProfiledRationalPackage A)
    (scan : InitialBlockScan A)
    (letter : InitialRightLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (source : PairedInitialProfiledBankState A) where
  profile : ProcTwoEntryOverlapProfile
    (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂)
  direction : PairedEntryDirection (In₁ := In₁) (In₂ := In₂)
  pending : source.1 = some (Sum.inr profile)
  image : package.next direction = source
  target : erasePairedProfiledState A source.2 =
    initialRightDelayedTarget A scan letter

omit [Inhabited In₁] [Inhabited In₂] in
theorem nonempty_endToEndInitialRightActivation_of_sourceOK
    (package : PairedInitialProfiledRationalPackage A)
    (scan : InitialBlockScan A)
    (letter : InitialRightLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (source : PairedInitialProfiledBankState A)
    (hsource : endToEndInitialRightSourceOK A package scan letter source) :
    Nonempty (EndToEndInitialRightActivation A package scan letter source) := by
  rcases hsource with ⟨⟨profile, hpending⟩, htarget, direction, himage⟩
  exact ⟨⟨profile, direction, hpending, himage, htarget⟩⟩

noncomputable def EndToEndInitialRightActivation.policy
    {package : PairedInitialProfiledRationalPackage A}
    {scan : InitialBlockScan A}
    {letter : InitialRightLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)}
    {source : PairedInitialProfiledBankState A}
    (activation : EndToEndInitialRightActivation A package scan letter source) :
    (leftProfiledGuardedAutomaton A source.2
      activation.profile).RationalTransitionPolicy :=
  package.profiledGuardedPolicyAt_image_right A activation.direction source
    activation.profile activation.image activation.pending

def endToEndInitialRightControllerPlay
    (package : PairedInitialProfiledRationalPackage A)
    (controller : TransitionRationalTree.{u, max u v x y s, max u v x y s}
      In₁ (NarrowedBlockLabel In₂ In₁
        (EndToEndInitialRightReceiverOutput A) Out₁
        (endToEndInitialRightBlockMonitor A package).State))
    (env : Nat → In₂ × In₁) :
    Nat → RealizedBlockRound In₂ In₁
      (EndToEndInitialRightReceiverOutput A) Out₁ :=
  treePlay
    (narrowedInducedTree (endToEndInitialRightBlockMonitor A package)
      controller.labeledTree) env

omit [Inhabited In₁] [Inhabited In₂] in
theorem endToEndInitialRightControllerPlay_wins
    (package : PairedInitialProfiledRationalPackage A)
    (controller : TransitionRationalTree.{u, max u v x y s, max u v x y s}
      In₁ (NarrowedBlockLabel In₂ In₁
        (EndToEndInitialRightReceiverOutput A) Out₁
        (endToEndInitialRightBlockMonitor A package).State))
    (hthreads : NarrowedAllThreadsWin (endToEndInitialRightBlockMonitor A package)
      controller.labeledTree)
    (env : Nat → In₂ × In₁) :
    (endToEndInitialRightBlockMonitor A package).WinsPlay
      (endToEndInitialRightControllerPlay A package controller env) := by
  let monitor := endToEndInitialRightBlockMonitor A package
  let tree := narrowedInducedTree monitor controller.labeledTree
  have htree := narrowedInducedTree_winningTree_of_allThreadsWin monitor hthreads
  exact (monitor.lift_winningTree_iff tree).mp htree env

/-- Physical all-right word carried by an arbitrary realized controller play. -/
def endToEndInitialRightPlayWord
    (play : Nat -> RealizedBlockRound In₂ In₁
      (EndToEndInitialRightReceiverOutput A) Out₁) :
    OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂) :=
  fun n =>
    let physical := endToEndInitialRightPhysicalLetter A (play n)
    rightRoundRecord physical.1 physical.2.2 physical.2.1.informedTwo

section
omit [Inhabited In₁] [Inhabited In₂]

theorem endToEndInitialRight_run_state_eq
    (package : PairedInitialProfiledRationalPackage A)
    (play : Nat -> RealizedBlockRound In₂ In₁
      (EndToEndInitialRightReceiverOutput A) Out₁) : ∀ n,
    ((endToEndInitialRightBlockMonitor A package).run play n).1.1.1 =
      A.run (endToEndInitialRightPlayWord A play) n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [BlockRecordMonitor.run, DetParityAutomaton.run]
      simp only [endToEndInitialRightBlockMonitor, initialRightScanStep,
        initialBlockScanStep, endToEndInitialRightPlayWord]
      change A.step
        (((endToEndInitialRightBlockMonitor A package).run play n).1.1.1)
        (rightRoundRecord (endToEndInitialRightPhysicalLetter A (play n)).1
          (endToEndInitialRightPhysicalLetter A (play n)).2.2
          (endToEndInitialRightPhysicalLetter A (play n)).2.1.informedTwo) = _
      rw [ih]
      rfl

/-- Right-initial semantic endpoint. -/
theorem endToEndInitialRightPlay_accepts_of_wins
    (package : PairedInitialProfiledRationalPackage A)
    (play : Nat -> RealizedBlockRound In₂ In₁
      (EndToEndInitialRightReceiverOutput A) Out₁)
    (hwins : (endToEndInitialRightBlockMonitor A package).WinsPlay play) :
    A.Accepts (endToEndInitialRightPlayWord A play) := by
  unfold BlockRecordMonitor.WinsPlay at hwins
  have heq :
      (fun n => (endToEndInitialRightBlockMonitor A package).priority
        ((endToEndInitialRightBlockMonitor A package).run play n)) =
      fun n => A.priority (A.run (endToEndInitialRightPlayWord A play) n) + 2 := by
    funext n
    have hsafe := endToEndInitialRight_safe_of_wins A package play hwins n
    change (if ((endToEndInitialRightBlockMonitor A package).run play n).2
      then A.priority
        ((endToEndInitialRightBlockMonitor A package).run play n).1.1.1 + 2
      else 1) = _
    rw [hsafe, if_pos rfl, endToEndInitialRight_run_state_eq A package play n]
  rw [heq] at hwins
  exact (natSeqMinEvenParity_add_const (d := 2) ⟨1, rfl⟩).mp hwins

theorem endToEndInitialRightController_sourceOK
    (package : PairedInitialProfiledRationalPackage A)
    (controller : TransitionRationalTree.{u, max u v x y s, max u v x y s}
      In₁ (NarrowedBlockLabel In₂ In₁
        (EndToEndInitialRightReceiverOutput A) Out₁
        (endToEndInitialRightBlockMonitor A package).State))
    (hthreads : NarrowedAllThreadsWin (endToEndInitialRightBlockMonitor A package)
      controller.labeledTree)
    (env : Nat → In₂ × In₁) (n : Nat) :
    endToEndInitialRightSourceOK A package
      ((endToEndInitialRightBlockMonitor A package).run
        (endToEndInitialRightControllerPlay A package controller env) n).1.1
      (endToEndInitialRightPhysicalLetter A
        (endToEndInitialRightControllerPlay A package controller env n))
      (endToEndInitialRightControllerPlay A package controller env n).2.1.2 :=
  endToEndInitialRight_sourceOK_of_wins A package _
    (endToEndInitialRightControllerPlay_wins A package controller hthreads env) n

theorem nonempty_endToEndInitialRightController_activation
    (package : PairedInitialProfiledRationalPackage A)
    (controller : TransitionRationalTree.{u, max u v x y s, max u v x y s}
      In₁ (NarrowedBlockLabel In₂ In₁
        (EndToEndInitialRightReceiverOutput A) Out₁
        (endToEndInitialRightBlockMonitor A package).State))
    (hthreads : NarrowedAllThreadsWin (endToEndInitialRightBlockMonitor A package)
      controller.labeledTree)
    (env : Nat → In₂ × In₁) (n : Nat) :
    Nonempty (EndToEndInitialRightActivation A package
      ((endToEndInitialRightBlockMonitor A package).run
        (endToEndInitialRightControllerPlay A package controller env) n).1.1
      (endToEndInitialRightPhysicalLetter A
        (endToEndInitialRightControllerPlay A package controller env n))
      (endToEndInitialRightControllerPlay A package controller env n).2.1.2) :=
  nonempty_endToEndInitialRightActivation_of_sourceOK A package _ _ _
    (endToEndInitialRightController_sourceOK A package controller hthreads env n)

end

end PairedStrategyMemory.PairedInitialProfiledRationalPackage

end

end DetParityAutomaton

end DistributedSynthesis
