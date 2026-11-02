/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleSuccessorScheduledPhysicalAlignment

/-!
# Live-overlay laws for the compatible-successor controller

The first concrete deferred handler was intentionally fail-fast.  It retains
the selected pending table, but a repeated one-way receive replaces the live
receiver by a freshly initialized receiver.  Consequently that particular
handler cannot prove the matched-prefix induction needed by the physical cut
stream.

This file freezes the already proved schedule/cut mathematics behind the
small interface that a corrected operational controller must implement.  A
live overlay is proof-side only.  The laws say that

* a same-orientation round preserves the live table;
* the first round after a switch installs and advances the opposite table;
* a simultaneous round reforks both live tables; and
* the emitted physical output pair is the one named by the live table.

The finite homogeneous-block induction below converts those one-round laws
into the exact `closing_inputs` and `closing_outputs` fields of
`ProfiledRawJointHybridPhysicalCompatible*ScheduledAlignmentAt`, while also
returning the live overlay after the closing round.  Thus a future controller
repair changes only the implementation of this interface; all graph clocks,
fresh-member selection, DPA slices, and transition packets remain unchanged.

No executable transition receives a graph, orientation, hierarchy side,
leader bit, strict-leader bit, history, or view.
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

private abbrev CompatiblePolicy
    (initial : ProfiledRawJointCommonBaseWorld A strategy) :=
  ProfiledRawJointHybridPhysicalCompatibleRationalPolicy A strategy hwin
    initial

private abbrev CompatibleState
    (initial : ProfiledRawJointCommonBaseWorld A strategy) :=
  ProfiledRawJointHybridPhysicalCompatiblePolicyState A strategy hwin initial

private abbrev PhysicalWord :=
  OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂)

/-! ## The controller-repair interface -/

/-- Proof-side operational laws for a controller carrying a live right or
left compatible-successor table.

`RightLive n` and `LeftLive n` describe the pre-round controller state at
physical time `n`.  They are deliberately abstract: a concrete controller may
use phases, a product overlay, or a tagged dormant root.  The output functions
name the table record expected at time `n`; `bothOutput` is common because a
simultaneous physical round has only one output pair.

The interface distinguishes preservation from output correctness.  This is
useful for a fail-fast implementation: loss of a live receiver violates a
single preservation field before any parity argument is involved. -/
structure ProfiledRawJointHybridPhysicalCompatibleSuccessorLiveOverlayLaws
    (word : PhysicalWord (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂))
    (inputAt : Nat → In₁ × In₂)
    (rightOutput leftOutput bothOutput : Nat → Out₁ × Out₂)
    (RightLive LeftLive : Nat → Prop) : Prop where
  physical_inputs : ∀ n,
    ((word n).inputOne, (word n).inputTwo) = inputAt n
  right_same : ∀ n, RightLive n → (word n).graph = .right →
    RightLive (n + 1)
  right_switch : ∀ n, LeftLive n → (word n).graph = .right →
    RightLive (n + 1)
  left_same : ∀ n, LeftLive n → (word n).graph = .left →
    LeftLive (n + 1)
  left_switch : ∀ n, RightLive n → (word n).graph = .left →
    LeftLive (n + 1)
  both_from_right : ∀ n, RightLive n → (word n).graph = .both →
    RightLive (n + 1) ∧ LeftLive (n + 1)
  both_from_left : ∀ n, LeftLive n → (word n).graph = .both →
    RightLive (n + 1) ∧ LeftLive (n + 1)
  right_output : ∀ n, (RightLive n ∨ LeftLive n) →
    (word n).graph = .right → (word n).outputPair = rightOutput n
  left_output : ∀ n, (RightLive n ∨ LeftLive n) →
    (word n).graph = .left → (word n).outputPair = leftOutput n
  both_output : ∀ n, (RightLive n ∨ LeftLive n) →
    (word n).graph = .both → (word n).outputPair = bothOutput n

namespace
    ProfiledRawJointHybridPhysicalCompatibleSuccessorLiveOverlayLaws

variable {word : PhysicalWord (In₁ := In₁) (In₂ := In₂)
  (Out₁ := Out₁) (Out₂ := Out₂)}
variable {inputAt : Nat → In₁ × In₂}
variable {rightOutput leftOutput bothOutput : Nat → Out₁ × Out₂}
variable {RightLive LeftLive : Nat → Prop}
variable
  (laws :
    ProfiledRawJointHybridPhysicalCompatibleSuccessorLiveOverlayLaws
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
      word inputAt rightOutput leftOutput bothOutput RightLive LeftLive)

include laws

section
omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂]

/-- One strict-right round, whether it continues the current right table or
switches from a live left table. -/
theorem right_step (n : Nat) (hlive : RightLive n ∨ LeftLive n)
    (hgraph : (word n).graph = .right) :
    (word n).outputPair = rightOutput n ∧ RightLive (n + 1) := by
  refine ⟨ProfiledRawJointHybridPhysicalCompatibleSuccessorLiveOverlayLaws.right_output
    laws n hlive hgraph, ?_⟩
  rcases hlive with hright | hleft
  · exact
      ProfiledRawJointHybridPhysicalCompatibleSuccessorLiveOverlayLaws.right_same
        laws n hright hgraph
  · exact
      ProfiledRawJointHybridPhysicalCompatibleSuccessorLiveOverlayLaws.right_switch
        laws n hleft hgraph

/-- Left mirror. -/
theorem left_step (n : Nat) (hlive : RightLive n ∨ LeftLive n)
    (hgraph : (word n).graph = .left) :
    (word n).outputPair = leftOutput n ∧ LeftLive (n + 1) := by
  refine ⟨ProfiledRawJointHybridPhysicalCompatibleSuccessorLiveOverlayLaws.left_output
    laws n hlive hgraph, ?_⟩
  rcases hlive with hright | hleft
  · exact
      ProfiledRawJointHybridPhysicalCompatibleSuccessorLiveOverlayLaws.left_switch
        laws n hright hgraph
  · exact
      ProfiledRawJointHybridPhysicalCompatibleSuccessorLiveOverlayLaws.left_same
        laws n hleft hgraph

/-- A simultaneous round emits the common output and leaves both overlays
live. -/
theorem both_step (n : Nat) (hlive : RightLive n ∨ LeftLive n)
    (hgraph : (word n).graph = .both) :
    (word n).outputPair = bothOutput n ∧
      RightLive (n + 1) ∧ LeftLive (n + 1) := by
  refine ⟨ProfiledRawJointHybridPhysicalCompatibleSuccessorLiveOverlayLaws.both_output
    laws n hlive hgraph, ?_⟩
  rcases hlive with hright | hleft
  · exact
      ProfiledRawJointHybridPhysicalCompatibleSuccessorLiveOverlayLaws.both_from_right
        laws n hright hgraph
  · exact
      ProfiledRawJointHybridPhysicalCompatibleSuccessorLiveOverlayLaws.both_from_left
        laws n hleft hgraph

end

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- Iterate the same/switch law through a finite homogeneous strict-right
block, including its closing round. -/
theorem right_homogeneous
    (start length : Nat) (hlive : RightLive start ∨ LeftLive start)
    (hgraph : ∀ j, j ≤ length → (word (start + j)).graph = .right) :
    (word (start + length)).outputPair = rightOutput (start + length) ∧
      RightLive (start + length + 1) := by
  induction length generalizing start with
  | zero =>
      simpa using right_step laws start hlive (hgraph 0 (Nat.zero_le 0))
  | succ length ih =>
      have hfirst := right_step laws start hlive
        (hgraph 0 (Nat.zero_le (length + 1)))
      have htail : ∀ j, j ≤ length →
          (word ((start + 1) + j)).graph = .right := by
        intro j hj
        have h := hgraph (j + 1) (Nat.succ_le_succ hj)
        simpa only [Nat.add_assoc, Nat.one_add] using h
      have hrest := ih (start := start + 1) (Or.inl hfirst.2) htail
      simpa only [Nat.add_assoc, Nat.one_add] using hrest

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- Homogeneous strict-left mirror. -/
theorem left_homogeneous
    (start length : Nat) (hlive : RightLive start ∨ LeftLive start)
    (hgraph : ∀ j, j ≤ length → (word (start + j)).graph = .left) :
    (word (start + length)).outputPair = leftOutput (start + length) ∧
      LeftLive (start + length + 1) := by
  induction length generalizing start with
  | zero =>
      simpa using left_step laws start hlive (hgraph 0 (Nat.zero_le 0))
  | succ length ih =>
      have hfirst := left_step laws start hlive
        (hgraph 0 (Nat.zero_le (length + 1)))
      have htail : ∀ j, j ≤ length →
          (word ((start + 1) + j)).graph = .left := by
        intro j hj
        have h := hgraph (j + 1) (Nat.succ_le_succ hj)
        simpa only [Nat.add_assoc, Nat.one_add] using h
      have hrest := ih (start := start + 1) (Or.inr hfirst.2) htail
      simpa only [Nat.add_assoc, Nat.one_add] using hrest

/-! ## Operational-close consequences -/

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- At a scheduled right boundary, the live-overlay laws determine the
physical closing output and preserve a right overlay after the close.  A true
member additionally leaves the left overlay live. -/
theorem right_scheduled_close
    (schedule : OperationalCloseMemberSchedule (fun j ↦ (word j).graph))
    (k : Nat)
    (hstrict : (word (schedule.cutPackage.cuts k)).graph ≠ .both →
      (word (schedule.cutPackage.cuts k)).graph = .right)
    (hlive : RightLive (schedule.cutPackage.cuts k) ∨
      LeftLive (schedule.cutPackage.cuts k))
    (target : Out₁ × Out₂)
    (hright : rightOutput (schedule.cutPackage.cuts (k + 1) - 1) = target)
    (hboth : bothOutput (schedule.cutPackage.cuts (k + 1) - 1) = target) :
    (word (schedule.cutPackage.cuts (k + 1) - 1)).outputPair = target ∧
      RightLive (schedule.cutPackage.cuts (k + 1)) ∧
      (schedule.closeMember k = true →
        LeftLive (schedule.cutPackage.cuts (k + 1))) := by
  cases hmember : schedule.closeMember k with
  | false =>
      have hstartNe : (word (schedule.cutPackage.cuts k)).graph ≠ .both :=
        (schedule.closeMember_eq_false_iff k).mp hmember
      have hstart : (word (schedule.cutPackage.cuts k)).graph = .right :=
        hstrict hstartNe
      have hhomogeneous : ∀ j, j ≤ schedule.cutPackage.openLength k →
          (word (schedule.cutPackage.cuts k + j)).graph = .right := by
        intro j hj
        rcases Nat.lt_or_eq_of_le hj with hj | rfl
        · exact (schedule.cutPackage.homogeneous k j hj).trans hstart
        · rw [schedule.start_add_openLength_eq_closingIndex k]
          exact (schedule.cutPackage.closing_graph_eq k).trans hstart
      have hrun := right_homogeneous laws
        (schedule.cutPackage.cuts k) (schedule.cutPackage.openLength k) hlive
          hhomogeneous
      have hindex := schedule.start_add_openLength_eq_closingIndex k
      have hnext := schedule.cutPackage.step_eq k
      refine ⟨?_, ?_, ?_⟩
      · rw [← hright, ← hindex]
        exact hrun.1
      · rw [hnext]
        exact hrun.2
      · intro htrue
        simp only [Bool.false_eq_true] at htrue
  | true =>
      obtain ⟨hzero, hnext, hindex, hgraph⟩ :=
        schedule.singleton_of_closeMember_eq_true k hmember
      have hgraphStart : (word (schedule.cutPackage.cuts k)).graph = .both := by
        rw [← hindex]
        exact hgraph
      have hrun := both_step laws (schedule.cutPackage.cuts k) hlive hgraphStart
      refine ⟨?_, ?_, ?_⟩
      · rw [← hboth, hindex]
        exact hrun.1
      · rw [hnext]
        exact hrun.2.1
      · intro _
        rw [hnext]
        exact hrun.2.2

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- Left scheduled boundary. -/
theorem left_scheduled_close
    (schedule : OperationalCloseMemberSchedule (fun j ↦ (word j).graph))
    (k : Nat)
    (hstrict : (word (schedule.cutPackage.cuts k)).graph ≠ .both →
      (word (schedule.cutPackage.cuts k)).graph = .left)
    (hlive : RightLive (schedule.cutPackage.cuts k) ∨
      LeftLive (schedule.cutPackage.cuts k))
    (target : Out₁ × Out₂)
    (hleft : leftOutput (schedule.cutPackage.cuts (k + 1) - 1) = target)
    (hboth : bothOutput (schedule.cutPackage.cuts (k + 1) - 1) = target) :
    (word (schedule.cutPackage.cuts (k + 1) - 1)).outputPair = target ∧
      LeftLive (schedule.cutPackage.cuts (k + 1)) ∧
      (schedule.closeMember k = true →
        RightLive (schedule.cutPackage.cuts (k + 1))) := by
  cases hmember : schedule.closeMember k with
  | false =>
      have hstartNe : (word (schedule.cutPackage.cuts k)).graph ≠ .both :=
        (schedule.closeMember_eq_false_iff k).mp hmember
      have hstart : (word (schedule.cutPackage.cuts k)).graph = .left :=
        hstrict hstartNe
      have hhomogeneous : ∀ j, j ≤ schedule.cutPackage.openLength k →
          (word (schedule.cutPackage.cuts k + j)).graph = .left := by
        intro j hj
        rcases Nat.lt_or_eq_of_le hj with hj | rfl
        · exact (schedule.cutPackage.homogeneous k j hj).trans hstart
        · rw [schedule.start_add_openLength_eq_closingIndex k]
          exact (schedule.cutPackage.closing_graph_eq k).trans hstart
      have hrun := left_homogeneous laws
        (schedule.cutPackage.cuts k) (schedule.cutPackage.openLength k) hlive
          hhomogeneous
      have hindex := schedule.start_add_openLength_eq_closingIndex k
      have hnext := schedule.cutPackage.step_eq k
      refine ⟨?_, ?_, ?_⟩
      · rw [← hleft, ← hindex]
        exact hrun.1
      · rw [hnext]
        exact hrun.2
      · intro htrue
        simp only [Bool.false_eq_true] at htrue
  | true =>
      obtain ⟨hzero, hnext, hindex, hgraph⟩ :=
        schedule.singleton_of_closeMember_eq_true k hmember
      have hgraphStart : (word (schedule.cutPackage.cuts k)).graph = .both := by
        rw [← hindex]
        exact hgraph
      have hrun := both_step laws (schedule.cutPackage.cuts k) hlive hgraphStart
      refine ⟨?_, ?_, ?_⟩
      · rw [← hboth, hindex]
        exact hrun.1
      · rw [hnext]
        exact hrun.2.2
      · intro _
        rw [hnext]
        exact hrun.2.1

end
  ProfiledRawJointHybridPhysicalCompatibleSuccessorLiveOverlayLaws

/-! ## Adapter to the existing scheduled-alignment packets -/

theorem
    profiledRawJointHybridPhysicalCompatibleRightScheduledAlignmentAt_of_liveOverlay
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial)
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (tableMember : Bool) (entryRow : PairedEntryRow)
    (localEnv : Nat → In₂ × In₁) (n : Nat)
    (physicalState : A.State)
    (word : PhysicalWord (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂))
    (inputAt : Nat → In₁ × In₂)
    (rightOutput leftOutput bothOutput : Nat → Out₁ × Out₂)
    (RightLive LeftLive : Nat → Prop)
    (laws :
      ProfiledRawJointHybridPhysicalCompatibleSuccessorLiveOverlayLaws
        (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
        word inputAt rightOutput leftOutput bothOutput RightLive LeftLive)
    (schedule : OperationalCloseMemberSchedule (fun j ↦ (word j).graph))
    (k : Nat)
    (hlive : RightLive (schedule.cutPackage.cuts k) ∨
      LeftLive (schedule.cutPackage.cuts k))
    (hstrict : (word (schedule.cutPackage.cuts k)).graph ≠ .both →
      (word (schedule.cutPackage.cuts k)).graph = .right)
    (hentry :
      A.runFrom physicalState word (schedule.cutPackage.cuts k) =
        pairedCodeStateForRow A entryRow move.1.source.1.1)
    (hlength :
      (profiledRawJointTargetRightPhysicalPrefixRecords A entryRow
        (omegaPrefix
          (profiledRawJointHybridPhysicalCompatibleRightPhysicalPlay A strategy
            hwin policy state move tableMember localEnv) n)).length =
        schedule.cutPackage.openLength k)
    (hslice :
      omegaPrefix (OmegaWord.drop word (schedule.cutPackage.cuts k))
          (profiledRawJointTargetRightPhysicalPrefixRecords A entryRow
            (omegaPrefix
              (profiledRawJointHybridPhysicalCompatibleRightPhysicalPlay A
                strategy hwin policy state move tableMember localEnv) n)).length =
        profiledRawJointTargetRightPhysicalPrefixRecords A entryRow
          (omegaPrefix
            (profiledRawJointHybridPhysicalCompatibleRightPhysicalPlay A
              strategy hwin policy state move tableMember localEnv) n))
    (hinput :
      ((inputAt (schedule.cutPackage.cuts (k + 1) - 1)).2,
          (inputAt (schedule.cutPackage.cuts (k + 1) - 1)).1) =
        (profiledRawJointTargetRightPhysicalLetter A
          (profiledRawJointHybridPhysicalCompatibleRightPhysicalPlay A strategy
            hwin policy state move tableMember localEnv n)).1)
    (hright :
      rightOutput (schedule.cutPackage.cuts (k + 1) - 1) =
        (profiledRawJointTargetRightClosingRecordForMember
          (schedule.closeMember k) entryRow
          (profiledRawJointTargetRightPhysicalLetter A
            (profiledRawJointHybridPhysicalCompatibleRightPhysicalPlay A
              strategy hwin policy state move tableMember localEnv n))).outputPair)
    (hboth :
      bothOutput (schedule.cutPackage.cuts (k + 1) - 1) =
        (profiledRawJointTargetRightClosingRecordForMember
          (schedule.closeMember k) entryRow
          (profiledRawJointTargetRightPhysicalLetter A
            (profiledRawJointHybridPhysicalCompatibleRightPhysicalPlay A
              strategy hwin policy state move tableMember localEnv n))).outputPair) :
    ∃ alignment :
        ProfiledRawJointHybridPhysicalCompatibleRightScheduledAlignmentAt A
          strategy hwin policy state move tableMember entryRow localEnv n
            physicalState word schedule k,
      RightLive (schedule.cutPackage.cuts (k + 1)) ∧
        (schedule.closeMember k = true →
          LeftLive (schedule.cutPackage.cuts (k + 1))) := by
  let target :=
    (profiledRawJointTargetRightClosingRecordForMember
      (schedule.closeMember k) entryRow
      (profiledRawJointTargetRightPhysicalLetter A
        (profiledRawJointHybridPhysicalCompatibleRightPhysicalPlay A strategy
          hwin policy state move tableMember localEnv n))).outputPair
  have hclose :=
    ProfiledRawJointHybridPhysicalCompatibleSuccessorLiveOverlayLaws.right_scheduled_close
      laws schedule k hstrict hlive target
        (by simpa [target] using hright) (by simpa [target] using hboth)
  have hphysicalInput :=
    ProfiledRawJointHybridPhysicalCompatibleSuccessorLiveOverlayLaws.physical_inputs laws
    (schedule.cutPackage.cuts (k + 1) - 1)
  refine ⟨{
    strict_orientation := hstrict
    entry_state := hentry
    records_length := hlength
    records_eq_slice := hslice
    closing_inputs := ?_
    closing_outputs := by simpa [target] using hclose.1 }, hclose.2.1,
      hclose.2.2⟩
  apply Prod.ext
  · exact (congrArg Prod.snd hphysicalInput).trans (congrArg Prod.fst hinput)
  · exact (congrArg Prod.fst hphysicalInput).trans (congrArg Prod.snd hinput)

/-- Left mirror of the live-overlay adapter. -/
theorem
    profiledRawJointHybridPhysicalCompatibleLeftScheduledAlignmentAt_of_liveOverlay
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (tableMember : Bool) (entryRow : PairedEntryRow)
    (localEnv : Nat → In₁ × In₂) (n : Nat)
    (physicalState : A.State)
    (word : PhysicalWord (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂))
    (inputAt : Nat → In₁ × In₂)
    (rightOutput leftOutput bothOutput : Nat → Out₁ × Out₂)
    (RightLive LeftLive : Nat → Prop)
    (laws :
      ProfiledRawJointHybridPhysicalCompatibleSuccessorLiveOverlayLaws
        (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
        word inputAt rightOutput leftOutput bothOutput RightLive LeftLive)
    (schedule : OperationalCloseMemberSchedule (fun j ↦ (word j).graph))
    (k : Nat)
    (hlive : RightLive (schedule.cutPackage.cuts k) ∨
      LeftLive (schedule.cutPackage.cuts k))
    (hstrict : (word (schedule.cutPackage.cuts k)).graph ≠ .both →
      (word (schedule.cutPackage.cuts k)).graph = .left)
    (hentry :
      A.runFrom physicalState word (schedule.cutPackage.cuts k) =
        pairedCodeStateForRow A entryRow move.1.source.1.1)
    (hlength :
      (profiledRawJointTargetLeftPhysicalPrefixRecords A entryRow
        (omegaPrefix
          (profiledRawJointHybridPhysicalCompatibleLeftPhysicalPlay A strategy
            hwin policy state move tableMember localEnv) n)).length =
        schedule.cutPackage.openLength k)
    (hslice :
      omegaPrefix (OmegaWord.drop word (schedule.cutPackage.cuts k))
          (profiledRawJointTargetLeftPhysicalPrefixRecords A entryRow
            (omegaPrefix
              (profiledRawJointHybridPhysicalCompatibleLeftPhysicalPlay A
                strategy hwin policy state move tableMember localEnv) n)).length =
        profiledRawJointTargetLeftPhysicalPrefixRecords A entryRow
          (omegaPrefix
            (profiledRawJointHybridPhysicalCompatibleLeftPhysicalPlay A
              strategy hwin policy state move tableMember localEnv) n))
    (hinput : inputAt (schedule.cutPackage.cuts (k + 1) - 1) =
      (profiledRawJointTargetLeftPhysicalLetter A
        (profiledRawJointHybridPhysicalCompatibleLeftPhysicalPlay A strategy
          hwin policy state move tableMember localEnv n)).1)
    (hleft :
      leftOutput (schedule.cutPackage.cuts (k + 1) - 1) =
        (profiledRawJointTargetLeftClosingRecordForMember
          (schedule.closeMember k) entryRow
          (profiledRawJointTargetLeftPhysicalLetter A
            (profiledRawJointHybridPhysicalCompatibleLeftPhysicalPlay A strategy
              hwin policy state move tableMember localEnv n))).outputPair)
    (hboth :
      bothOutput (schedule.cutPackage.cuts (k + 1) - 1) =
        (profiledRawJointTargetLeftClosingRecordForMember
          (schedule.closeMember k) entryRow
          (profiledRawJointTargetLeftPhysicalLetter A
            (profiledRawJointHybridPhysicalCompatibleLeftPhysicalPlay A strategy
              hwin policy state move tableMember localEnv n))).outputPair) :
    ∃ alignment :
        ProfiledRawJointHybridPhysicalCompatibleLeftScheduledAlignmentAt A
          strategy hwin policy state move tableMember entryRow localEnv n
            physicalState word schedule k,
      LeftLive (schedule.cutPackage.cuts (k + 1)) ∧
        (schedule.closeMember k = true →
          RightLive (schedule.cutPackage.cuts (k + 1))) := by
  let target :=
    (profiledRawJointTargetLeftClosingRecordForMember
      (schedule.closeMember k) entryRow
      (profiledRawJointTargetLeftPhysicalLetter A
        (profiledRawJointHybridPhysicalCompatibleLeftPhysicalPlay A strategy
          hwin policy state move tableMember localEnv n))).outputPair
  have hclose :=
    ProfiledRawJointHybridPhysicalCompatibleSuccessorLiveOverlayLaws.left_scheduled_close
      laws schedule k hstrict hlive target
        (by simpa [target] using hleft) (by simpa [target] using hboth)
  have hphysicalInput :=
    ProfiledRawJointHybridPhysicalCompatibleSuccessorLiveOverlayLaws.physical_inputs laws
    (schedule.cutPackage.cuts (k + 1) - 1)
  refine ⟨{
    strict_orientation := hstrict
    entry_state := hentry
    records_length := hlength
    records_eq_slice := hslice
    closing_inputs := ?_
    closing_outputs := by simpa [target] using hclose.1 }, hclose.2.1,
      hclose.2.2⟩
  exact hphysicalInput.trans hinput

end

end DetParityAutomaton

end DistributedSynthesis
