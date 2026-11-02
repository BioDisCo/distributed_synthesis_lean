/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledEndToEndOperationalSemantics

/-!
# Homogeneous executions of the operational automaton

The no-reversal cases are the base cases of the final phase decomposition.
They are proved here directly against the two root-pinned initial controller
plays.  This is semantic acceptance of the actual distributed readback, not
only safety of an auxiliary monitor.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

variable (bundle : EndToEndOperationalControllerPackage A)

open PairedStrategyMemory.PairedInitialProfiledRationalPackage

def endToEndAllLeftEnvironment
    (inputs : Nat -> In₁ × In₂) : EnvironmentSequence In₁ In₂ :=
  fun n => ⟨(inputs n).1, (inputs n).2, .left⟩

def endToEndAllRightEnvironment
    (inputs : Nat -> In₂ × In₁) : EnvironmentSequence In₁ In₂ :=
  fun n => ⟨(inputs n).2, (inputs n).1, .right⟩

/-- Direct iteration of the two left-initial local carriers. -/
def endToEndLeftReceiverState
    (inputs : Nat -> In₁ × In₂) : Nat ->
      EndToEndOperationalInitialLeft A bundle
  | 0 => initialEndToEndOperationalInitialLeft A bundle
  | n + 1 =>
      (endToEndOperationalInitialLeftRecv A bundle
        (endToEndLeftReceiverState inputs n) (inputs n)).2

def endToEndLeftBlindState
    (inputs : Nat -> In₁ × In₂) : Nat -> bundle.leftController.Control
  | 0 => bundle.leftController.initial
  | n + 1 =>
      (endToEndOperationalInitialLeftBlind A bundle
        (endToEndLeftBlindState inputs n) (inputs n).2).2

/-- Direct right-initial mirror. -/
def endToEndRightBlindState
    (inputs : Nat -> In₂ × In₁) : Nat -> bundle.rightController.Control
  | 0 => bundle.rightController.initial
  | n + 1 =>
      (endToEndOperationalInitialRightBlind A bundle
        (endToEndRightBlindState inputs n) (inputs n).2).2

def endToEndRightReceiverState
    (inputs : Nat -> In₂ × In₁) : Nat ->
      EndToEndOperationalInitialRight A bundle
  | 0 => initialEndToEndOperationalInitialRight A bundle
  | n + 1 =>
      (endToEndOperationalInitialRightRecv A bundle
        (endToEndRightReceiverState inputs n) (inputs n)).2

section
omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]

/-- The record-monitor run used in the controller play is the narrowed
control at the corresponding full branch node. -/
theorem endToEndLeftInitialPlay_run_eq_narrowedControl
    (inputs : Nat -> In₁ × In₂) (n : Nat) :
    (endToEndInitialLeftPinnedMonitor A bundle.rational).run
        (bundle.leftInitialPlay A inputs) n =
      narrowedControl (endToEndInitialLeftPinnedMonitor A bundle.rational)
        bundle.leftController.labeledTree (branchNode inputs n) := by
  let monitor := endToEndInitialLeftPinnedMonitor A bundle.rational
  let tree := narrowedInducedTree monitor bundle.leftController.labeledTree
  simpa [monitor, tree,
    EndToEndOperationalControllerPackage.leftInitialPlay] using
    ((monitor.lift_control_branchNode tree inputs n).symm.trans
      (lift_control_narrowedInducedTree monitor
        bundle.leftController.labeledTree (branchNode inputs n)))

/-- The iterated left receiver carries exactly the narrowed control and pinned
monitor run used in the concrete controller play. -/
theorem endToEndLeftReceiverState_fst
    (inputs : Nat -> In₁ × In₂) : ∀ n,
    (endToEndLeftReceiverState A bundle inputs n).1 =
      (bundle.leftController.controlAt
          (senderWord (branchNode inputs n)),
        (endToEndInitialLeftPinnedMonitor A bundle.rational).run
          (bundle.leftInitialPlay A inputs) n) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [endToEndLeftReceiverState]
      simp only [endToEndOperationalInitialLeftRecv]
      rw [ih, BlockRecordMonitor.run]
      rw [endToEndLeftInitialPlay_run_eq_narrowedControl A bundle inputs n]
      simp [TransitionRationalTree.controlAt, branchNode, senderWord_append,
        List.foldl_append, EndToEndOperationalControllerPackage.leftInitialPlay,
        treePlay, blockLabelApply, narrowedInducedTree,
        TransitionRationalTree.labeledTree]

theorem endToEndLeftBlindState_eq
    (inputs : Nat -> In₁ × In₂) : ∀ n,
    endToEndLeftBlindState A bundle inputs n =
      bundle.leftController.controlAt
        (senderWord (branchNode inputs n)) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [endToEndLeftBlindState, ih]
      simp [endToEndOperationalInitialLeftBlind,
        TransitionRationalTree.controlAt, branchNode, senderWord_append,
        List.foldl_append]

/-- One direct left step emits exactly the corresponding physical controller
play outputs. -/
theorem endToEndLeft_step_outputs
    (inputs : Nat -> In₁ × In₂) (n : Nat) :
    ((endToEndOperationalInitialLeftRecv A bundle
        (endToEndLeftReceiverState A bundle inputs n) (inputs n)).1,
      (endToEndOperationalInitialLeftBlind A bundle
        (endToEndLeftBlindState A bundle inputs n) (inputs n).2).1) =
      ((bundle.leftInitialPlay A inputs n).2.1.1.informedOne,
        (bundle.leftInitialPlay A inputs n).2.2) := by
  simp only [endToEndOperationalInitialLeftRecv,
    endToEndOperationalInitialLeftBlind]
  rw [endToEndLeftReceiverState_fst A bundle inputs n,
    endToEndLeftBlindState_eq A bundle inputs n]
  rw [endToEndLeftInitialPlay_run_eq_narrowedControl A bundle inputs n]
  simp [endToEndOperationalInitialLeftRecv,
    endToEndOperationalInitialLeftBlind,
    EndToEndOperationalControllerPackage.leftInitialPlay, treePlay,
    blockLabelApply, narrowedInducedTree, TransitionRationalTree.labeledTree,
    narrowedControl, senderWord]

/-- Every nonempty left prefix has a successfully checked staged boundary.
This is the fact that prevents the hybrid/seam receive table from taking its
fallback branch on a genuine homogeneous execution. -/
theorem endToEndLeftReceiverState_key_ne_none
    (inputs : Nat -> In₁ × In₂) (n : Nat) :
    (endToEndLeftReceiverState A bundle inputs (n + 1)).2 ≠ none := by
  rw [endToEndLeftReceiverState]
  simp only [endToEndOperationalInitialLeftRecv]
  rw [endToEndLeftReceiverState_fst A bundle inputs n]
  have hsource := bundle.leftInitialPlay_sourceOK A inputs n
  rw [← (endToEndInitialLeftBlockMonitor A bundle.rational).rootPinned_run_base
      (endToEndInitialLeftExpected A bundle.rational)
      (bundle.leftInitialPlay A inputs) n] at hsource
  have hplay :
      bundle.leftInitialPlay A inputs n =
        (inputs n,
          (bundle.leftController.labelOf
            (bundle.leftController.controlAt
              (senderWord (branchNode inputs n)))).2
            ((endToEndInitialLeftPinnedMonitor A bundle.rational).run
              (bundle.leftInitialPlay A inputs) n) (inputs n),
          (bundle.leftController.labelOf
            (bundle.leftController.controlAt
              (senderWord (branchNode inputs n)))).1 (inputs n).2) := by
    rw [endToEndLeftInitialPlay_run_eq_narrowedControl A bundle inputs n]
    simp [EndToEndOperationalControllerPackage.leftInitialPlay, treePlay,
      blockLabelApply, narrowedInducedTree,
      TransitionRationalTree.labeledTree]
  simp only [endToEndOperationalInitialLeftKey]
  rw [dif_pos (by simpa [hplay] using hsource)]
  simp

end

/-- After the first all-left round the receiver retains both root shadows,
while the nonreceiving process is already in its ordinary blind controller. -/
theorem endToEndOperationalTrace_allLeft_one
    (inputs : Nat -> In₁ × In₂) :
    ∃ shadow : bundle.rightController.Control,
      endToEndOperationalTrace A bundle (endToEndAllLeftEnvironment inputs) 1 =
        (((EndToEndOperationalOneControl.rootHybrid
            (endToEndLeftReceiverState A bundle inputs 1, shadow) :
              EndToEndOperationalOneControl A bundle),
            (bundle.leftInitialPlay A inputs 0).2.1.1.informedOne),
          ((EndToEndOperationalTwoControl.initialLeftBlind
              (endToEndLeftBlindState A bundle inputs 1) :
                EndToEndOperationalTwoControl A bundle),
            (bundle.leftInitialPlay A inputs 0).2.2)) := by
  refine ⟨(endToEndOperationalInitialRightBlind A bundle
      bundle.rightController.initial (inputs 0).1).2, ?_⟩
  change
    (((EndToEndOperationalOneControl.rootHybrid
        (endToEndOperationalRootRecvOne A bundle (inputs 0)).2 :
          EndToEndOperationalOneControl A bundle),
        (endToEndOperationalRootRecvOne A bundle (inputs 0)).1),
      ((EndToEndOperationalTwoControl.initialLeftBlind
          (endToEndOperationalInitialLeftBlind A bundle
            bundle.leftController.initial (inputs 0).2).2 :
              EndToEndOperationalTwoControl A bundle),
        (endToEndOperationalInitialLeftBlind A bundle
          bundle.leftController.initial (inputs 0).2).1)) = _
  have hout := endToEndLeft_step_outputs A bundle inputs 0
  rw [show (endToEndOperationalRootRecvOne A bundle (inputs 0)).1 =
      (bundle.leftInitialPlay A inputs 0).2.1.1.informedOne by
        exact congrArg Prod.fst hout]
  rw [show (endToEndOperationalInitialLeftBlind A bundle
      bundle.leftController.initial (inputs 0).2).1 =
      (bundle.leftInitialPlay A inputs 0).2.2 by
        exact congrArg Prod.snd hout]
  rfl

/-- From the second all-left round onward the receiver carries its genuine
left anchor together with one hypothetical first-right pair.  The pair is
existential proof state; no local transition reads an orientation bit. -/
theorem endToEndOperationalTrace_allLeft_later
    (inputs : Nat -> In₁ × In₂) : ∀ n,
    ∃ pair : EndToEndGuardedFirstRightOwnerControl A bundle.rational ×
        EndToEndGuardedFirstRightReceiverControl A bundle.rational,
      endToEndOperationalTrace A bundle (endToEndAllLeftEnvironment inputs)
          (n + 2) =
        (((EndToEndOperationalOneControl.initialLeftSeam
            (endToEndLeftReceiverState A bundle inputs (n + 2), pair) :
              EndToEndOperationalOneControl A bundle),
            (bundle.leftInitialPlay A inputs (n + 1)).2.1.1.informedOne),
          ((EndToEndOperationalTwoControl.initialLeftBlind
              (endToEndLeftBlindState A bundle inputs (n + 2)) :
                EndToEndOperationalTwoControl A bundle),
            (bundle.leftInitialPlay A inputs (n + 1)).2.2)) := by
  intro n
  induction n with
  | zero =>
      obtain ⟨shadow, htrace⟩ :=
        endToEndOperationalTrace_allLeft_one A bundle inputs
      rw [endToEndOperationalTrace_succ, htrace]
      have hkey := endToEndLeftReceiverState_key_ne_none A bundle inputs 0
      cases hstaged : (endToEndLeftReceiverState A bundle inputs 1).2 with
      | none => exact False.elim (hkey hstaged)
      | some key =>
          let pair :=
            ((stepEndToEndGuardedFirstRightOwner A bundle.rational
                (initialEndToEndGuardedFirstRightOwner A bundle.rational key)
                (inputs 1).1).2,
              (continueEndToEndGuardedFirstRightReceiver A bundle.rational
                (initialEndToEndGuardedFirstRightReceiver A bundle.rational key
                  (guardedEntryRowOfReceived false))
                (initialEndToEndGuardedFirstRightOwner A bundle.rational key)
                ((inputs 1).2, (inputs 1).1)).2)
          refine ⟨pair, ?_⟩
          simp only [endToEndAllLeftEnvironment,
            LocalSummaryAutomaton.advance, endToEndOperationalM,
            endToEndOperationalSummaryAutomaton]
          simp [endToEndOperationalRecvPair,
            endToEndOperationalInitialLeftOneAnchor,
            endToEndOperationalInitialLeftTwoAnchor,
            endToEndOperationalInitialLeftSeamRecv,
            endToEndOperationalFreshFirstRight, hstaged, pair,
            endToEndOperationalNoRecvTwo,
            endToEndLeftBlindState]
          have hout := endToEndLeft_step_outputs A bundle inputs 1
          exact ⟨⟨rfl, congrArg Prod.fst hout⟩,
            congrArg Prod.snd hout⟩
  | succ n ih =>
      obtain ⟨oldPair, htrace⟩ := ih
      rw [endToEndOperationalTrace_succ, htrace]
      have hkey := endToEndLeftReceiverState_key_ne_none A bundle inputs (n + 1)
      cases hstaged : (endToEndLeftReceiverState A bundle inputs (n + 2)).2 with
      | none => exact False.elim (hkey hstaged)
      | some key =>
          let pair :=
            ((stepEndToEndGuardedFirstRightOwner A bundle.rational
                (initialEndToEndGuardedFirstRightOwner A bundle.rational key)
                (inputs (n + 2)).1).2,
              (continueEndToEndGuardedFirstRightReceiver A bundle.rational
                (initialEndToEndGuardedFirstRightReceiver A bundle.rational key
                  (guardedEntryRowOfReceived false))
                (initialEndToEndGuardedFirstRightOwner A bundle.rational key)
                ((inputs (n + 2)).2, (inputs (n + 2)).1)).2)
          refine ⟨pair, ?_⟩
          simp only [endToEndAllLeftEnvironment,
            LocalSummaryAutomaton.advance, endToEndOperationalM,
            endToEndOperationalSummaryAutomaton]
          simp [endToEndOperationalRecvPair,
            endToEndOperationalInitialLeftOneAnchor,
            endToEndOperationalInitialLeftTwoAnchor,
            endToEndOperationalInitialLeftSeamRecv,
            endToEndOperationalFreshFirstRight, hstaged, pair,
            endToEndOperationalNoRecvTwo,
            endToEndLeftBlindState]
          have hout := endToEndLeft_step_outputs A bundle inputs (n + 2)
          exact ⟨⟨rfl, congrArg Prod.fst hout⟩,
            congrArg Prod.snd hout⟩

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- Fieldwise extensionality used for concrete execution records. -/
private theorem roundRecord_eq_of_fields
    {left right : RoundRecord In₁ In₂ Graph Out₁ Out₂}
    (hinputOne : left.inputOne = right.inputOne)
    (hinputTwo : left.inputTwo = right.inputTwo)
    (hgraph : left.graph = right.graph)
    (houtputOne : left.outputOne = right.outputOne)
    (houtputTwo : left.outputTwo = right.outputTwo) :
    left = right := by
  cases left
  cases right
  simp_all

/-- The actual distributed readback wins every all-left environment. -/
theorem endToEndOperational_accepts_allLeft
    (inputs : Nat -> In₁ × In₂) :
    A.Accepts
      (execution (endToEndOperationalStrategy A bundle)
        (endToEndAllLeftEnvironment inputs)) := by
  let env := endToEndAllLeftEnvironment inputs
  have hword :
      execution (endToEndOperationalStrategy A bundle) env =
        endToEndInitialLeftPlayWord A (bundle.leftInitialPlay A inputs) := by
    funext n
    have hout := endToEndOperational_execution_outputs A bundle env n
    cases n with
    | zero =>
        obtain ⟨shadow, htrace⟩ :=
          endToEndOperationalTrace_allLeft_one A bundle inputs
        rw [htrace] at hout
        apply roundRecord_eq_of_fields
        · simp [execution_apply, env, endToEndAllLeftEnvironment,
            endToEndInitialLeftPlayWord,
            nextRound, endToEndInitialLeftPhysicalLetter,
            EndToEndOperationalControllerPackage.leftInitialPlay,
            treePlay, blockLabelApply, leftRoundRecord]
        · simp [execution_apply, env, endToEndAllLeftEnvironment,
            endToEndInitialLeftPlayWord,
            nextRound, endToEndInitialLeftPhysicalLetter,
            EndToEndOperationalControllerPackage.leftInitialPlay,
            treePlay, blockLabelApply, leftRoundRecord]
        · simp [execution_apply, env, endToEndAllLeftEnvironment,
            endToEndInitialLeftPlayWord,
            nextRound, endToEndInitialLeftPhysicalLetter,
            EndToEndOperationalControllerPackage.leftInitialPlay,
            treePlay, blockLabelApply, leftRoundRecord]
        · exact congrArg Prod.fst hout
        · exact congrArg Prod.snd hout
    | succ k =>
        obtain ⟨pair, htrace⟩ :=
          endToEndOperationalTrace_allLeft_later A bundle inputs k
        rw [htrace] at hout
        apply roundRecord_eq_of_fields
        · simp [execution_apply, env, endToEndAllLeftEnvironment,
            endToEndInitialLeftPlayWord,
            nextRound, endToEndInitialLeftPhysicalLetter,
            EndToEndOperationalControllerPackage.leftInitialPlay,
            treePlay, blockLabelApply, leftRoundRecord]
        · simp [execution_apply, env, endToEndAllLeftEnvironment,
            endToEndInitialLeftPlayWord,
            nextRound, endToEndInitialLeftPhysicalLetter,
            EndToEndOperationalControllerPackage.leftInitialPlay,
            treePlay, blockLabelApply, leftRoundRecord]
        · simp [execution_apply, env, endToEndAllLeftEnvironment,
            endToEndInitialLeftPlayWord,
            nextRound, endToEndInitialLeftPhysicalLetter,
            EndToEndOperationalControllerPackage.leftInitialPlay,
            treePlay, blockLabelApply, leftRoundRecord]
        · exact congrArg Prod.fst hout
        · exact congrArg Prod.snd hout
  rw [hword]
  exact bundle.leftInitialPlay_accepts A inputs

/-! ## Right-initial mirror -/

section
omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]

theorem endToEndRightInitialPlay_run_eq_narrowedControl
    (inputs : Nat -> In₂ × In₁) (n : Nat) :
    (endToEndInitialRightPinnedMonitor A bundle.rational).run
        (bundle.rightInitialPlay A inputs) n =
      narrowedControl (endToEndInitialRightPinnedMonitor A bundle.rational)
        bundle.rightController.labeledTree (branchNode inputs n) := by
  let monitor := endToEndInitialRightPinnedMonitor A bundle.rational
  let tree := narrowedInducedTree monitor bundle.rightController.labeledTree
  simpa [monitor, tree,
    EndToEndOperationalControllerPackage.rightInitialPlay] using
    ((monitor.lift_control_branchNode tree inputs n).symm.trans
      (lift_control_narrowedInducedTree monitor
        bundle.rightController.labeledTree (branchNode inputs n)))

theorem endToEndRightReceiverState_fst
    (inputs : Nat -> In₂ × In₁) : ∀ n,
    (endToEndRightReceiverState A bundle inputs n).1 =
      (bundle.rightController.controlAt (senderWord (branchNode inputs n)),
        (endToEndInitialRightPinnedMonitor A bundle.rational).run
          (bundle.rightInitialPlay A inputs) n) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [endToEndRightReceiverState]
      simp only [endToEndOperationalInitialRightRecv]
      rw [ih, BlockRecordMonitor.run]
      rw [endToEndRightInitialPlay_run_eq_narrowedControl A bundle inputs n]
      simp [TransitionRationalTree.controlAt, branchNode, senderWord_append,
        List.foldl_append,
        EndToEndOperationalControllerPackage.rightInitialPlay,
        treePlay, blockLabelApply, narrowedInducedTree,
        TransitionRationalTree.labeledTree]

theorem endToEndRightBlindState_eq
    (inputs : Nat -> In₂ × In₁) : ∀ n,
    endToEndRightBlindState A bundle inputs n =
      bundle.rightController.controlAt (senderWord (branchNode inputs n)) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [endToEndRightBlindState, ih]
      simp [endToEndOperationalInitialRightBlind,
        TransitionRationalTree.controlAt, branchNode, senderWord_append,
        List.foldl_append]

theorem endToEndRight_step_outputs
    (inputs : Nat -> In₂ × In₁) (n : Nat) :
    ((endToEndOperationalInitialRightBlind A bundle
        (endToEndRightBlindState A bundle inputs n) (inputs n).2).1,
      (endToEndOperationalInitialRightRecv A bundle
        (endToEndRightReceiverState A bundle inputs n) (inputs n)).1) =
      ((bundle.rightInitialPlay A inputs n).2.2,
        (bundle.rightInitialPlay A inputs n).2.1.1.informedTwo) := by
  simp only [endToEndOperationalInitialRightRecv,
    endToEndOperationalInitialRightBlind]
  rw [endToEndRightReceiverState_fst A bundle inputs n,
    endToEndRightBlindState_eq A bundle inputs n]
  rw [endToEndRightInitialPlay_run_eq_narrowedControl A bundle inputs n]
  simp [EndToEndOperationalControllerPackage.rightInitialPlay, treePlay,
    blockLabelApply, narrowedInducedTree, TransitionRationalTree.labeledTree,
    narrowedControl, senderWord]

theorem endToEndRightReceiverState_key_ne_none
    (inputs : Nat -> In₂ × In₁) (n : Nat) :
    (endToEndRightReceiverState A bundle inputs (n + 1)).2 ≠ none := by
  rw [endToEndRightReceiverState]
  simp only [endToEndOperationalInitialRightRecv]
  rw [endToEndRightReceiverState_fst A bundle inputs n]
  have hsource := bundle.rightInitialPlay_sourceOK A inputs n
  rw [← (endToEndInitialRightBlockMonitor A bundle.rational).rootPinned_run_base
      (endToEndInitialRightExpected A bundle.rational)
      (bundle.rightInitialPlay A inputs) n] at hsource
  have hplay :
      bundle.rightInitialPlay A inputs n =
        (inputs n,
          (bundle.rightController.labelOf
            (bundle.rightController.controlAt
              (senderWord (branchNode inputs n)))).2
            ((endToEndInitialRightPinnedMonitor A bundle.rational).run
              (bundle.rightInitialPlay A inputs) n) (inputs n),
          (bundle.rightController.labelOf
            (bundle.rightController.controlAt
              (senderWord (branchNode inputs n)))).1 (inputs n).2) := by
    rw [endToEndRightInitialPlay_run_eq_narrowedControl A bundle inputs n]
    simp [EndToEndOperationalControllerPackage.rightInitialPlay, treePlay,
      blockLabelApply, narrowedInducedTree,
      TransitionRationalTree.labeledTree]
  simp only [endToEndOperationalInitialRightKey]
  rw [dif_pos (by simpa [hplay] using hsource)]
  simp

end

theorem endToEndOperationalTrace_allRight_one
    (inputs : Nat -> In₂ × In₁) :
    ∃ shadow : bundle.leftController.Control,
      endToEndOperationalTrace A bundle (endToEndAllRightEnvironment inputs) 1 =
        (((EndToEndOperationalOneControl.initialRightBlind
            (endToEndRightBlindState A bundle inputs 1) :
              EndToEndOperationalOneControl A bundle),
            (bundle.rightInitialPlay A inputs 0).2.2),
          ((EndToEndOperationalTwoControl.rootHybrid
            (shadow, endToEndRightReceiverState A bundle inputs 1) :
              EndToEndOperationalTwoControl A bundle),
            (bundle.rightInitialPlay A inputs 0).2.1.1.informedTwo)) := by
  refine ⟨(endToEndOperationalInitialLeftBlind A bundle
      bundle.leftController.initial (inputs 0).1).2, ?_⟩
  change
    (((EndToEndOperationalOneControl.initialRightBlind
        (endToEndOperationalInitialRightBlind A bundle
          bundle.rightController.initial (inputs 0).2).2 :
            EndToEndOperationalOneControl A bundle),
        (endToEndOperationalInitialRightBlind A bundle
          bundle.rightController.initial (inputs 0).2).1),
      ((EndToEndOperationalTwoControl.rootHybrid
        (endToEndOperationalRootRecvTwo A bundle
          ((inputs 0).2, (inputs 0).1)).2 :
            EndToEndOperationalTwoControl A bundle),
        (endToEndOperationalRootRecvTwo A bundle
          ((inputs 0).2, (inputs 0).1)).1)) = _
  have hout := endToEndRight_step_outputs A bundle inputs 0
  rw [show (endToEndOperationalInitialRightBlind A bundle
      bundle.rightController.initial (inputs 0).2).1 =
      (bundle.rightInitialPlay A inputs 0).2.2 by
        exact congrArg Prod.fst hout]
  rw [show (endToEndOperationalRootRecvTwo A bundle
      ((inputs 0).2, (inputs 0).1)).1 =
      (bundle.rightInitialPlay A inputs 0).2.1.1.informedTwo by
        exact congrArg Prod.snd hout]
  rfl

theorem endToEndOperationalTrace_allRight_later
    (inputs : Nat -> In₂ × In₁) : ∀ n,
    ∃ pair : EndToEndGuardedFirstLeftOwnerControl A bundle.rational ×
        EndToEndGuardedFirstLeftReceiverControl A bundle.rational,
      endToEndOperationalTrace A bundle (endToEndAllRightEnvironment inputs)
          (n + 2) =
        (((EndToEndOperationalOneControl.initialRightBlind
            (endToEndRightBlindState A bundle inputs (n + 2)) :
              EndToEndOperationalOneControl A bundle),
            (bundle.rightInitialPlay A inputs (n + 1)).2.2),
          ((EndToEndOperationalTwoControl.initialRightSeam
            (endToEndRightReceiverState A bundle inputs (n + 2), pair) :
              EndToEndOperationalTwoControl A bundle),
            (bundle.rightInitialPlay A inputs (n + 1)).2.1.1.informedTwo)) := by
  intro n
  induction n with
  | zero =>
      obtain ⟨shadow, htrace⟩ :=
        endToEndOperationalTrace_allRight_one A bundle inputs
      rw [endToEndOperationalTrace_succ, htrace]
      have hkey := endToEndRightReceiverState_key_ne_none A bundle inputs 0
      cases hstaged : (endToEndRightReceiverState A bundle inputs 1).2 with
      | none => exact False.elim (hkey hstaged)
      | some key =>
          let pair :=
            ((stepEndToEndGuardedFirstLeftOwner A bundle.rational
                (initialEndToEndGuardedFirstLeftOwner A bundle.rational key)
                (inputs 1).1).2,
              (continueEndToEndGuardedFirstLeftReceiver A bundle.rational
                (initialEndToEndGuardedFirstLeftReceiver A bundle.rational key
                  (guardedEntryRowOfReceived false))
                (initialEndToEndGuardedFirstLeftOwner A bundle.rational key)
                ((inputs 1).2, (inputs 1).1)).2)
          refine ⟨pair, ?_⟩
          simp only [endToEndAllRightEnvironment,
            LocalSummaryAutomaton.advance, endToEndOperationalM,
            endToEndOperationalSummaryAutomaton]
          simp [endToEndOperationalRecvPair,
            endToEndOperationalInitialLeftOneAnchor,
            endToEndOperationalInitialLeftTwoAnchor,
            endToEndOperationalInitialRightOneAnchor,
            endToEndOperationalInitialRightTwoAnchor,
            endToEndOperationalInitialRightSeamRecv,
            endToEndOperationalFreshFirstLeft, hstaged, pair,
            endToEndOperationalNoRecvOne,
            endToEndRightBlindState]
          have hout := endToEndRight_step_outputs A bundle inputs 1
          exact ⟨congrArg Prod.fst hout,
            ⟨rfl, congrArg Prod.snd hout⟩⟩
  | succ n ih =>
      obtain ⟨oldPair, htrace⟩ := ih
      rw [endToEndOperationalTrace_succ, htrace]
      have hkey := endToEndRightReceiverState_key_ne_none A bundle inputs (n + 1)
      cases hstaged : (endToEndRightReceiverState A bundle inputs (n + 2)).2 with
      | none => exact False.elim (hkey hstaged)
      | some key =>
          let pair :=
            ((stepEndToEndGuardedFirstLeftOwner A bundle.rational
                (initialEndToEndGuardedFirstLeftOwner A bundle.rational key)
                (inputs (n + 2)).1).2,
              (continueEndToEndGuardedFirstLeftReceiver A bundle.rational
                (initialEndToEndGuardedFirstLeftReceiver A bundle.rational key
                  (guardedEntryRowOfReceived false))
                (initialEndToEndGuardedFirstLeftOwner A bundle.rational key)
                ((inputs (n + 2)).2, (inputs (n + 2)).1)).2)
          refine ⟨pair, ?_⟩
          simp only [endToEndAllRightEnvironment,
            LocalSummaryAutomaton.advance, endToEndOperationalM,
            endToEndOperationalSummaryAutomaton]
          simp [endToEndOperationalRecvPair,
            endToEndOperationalInitialLeftOneAnchor,
            endToEndOperationalInitialLeftTwoAnchor,
            endToEndOperationalInitialRightOneAnchor,
            endToEndOperationalInitialRightTwoAnchor,
            endToEndOperationalInitialRightSeamRecv,
            endToEndOperationalFreshFirstLeft, hstaged, pair,
            endToEndOperationalNoRecvOne,
            endToEndRightBlindState]
          have hout := endToEndRight_step_outputs A bundle inputs (n + 2)
          exact ⟨congrArg Prod.fst hout,
            ⟨rfl, congrArg Prod.snd hout⟩⟩

/-- The actual distributed readback wins every all-right environment. -/
theorem endToEndOperational_accepts_allRight
    (inputs : Nat -> In₂ × In₁) :
    A.Accepts
      (execution (endToEndOperationalStrategy A bundle)
        (endToEndAllRightEnvironment inputs)) := by
  let env := endToEndAllRightEnvironment inputs
  have hword :
      execution (endToEndOperationalStrategy A bundle) env =
        endToEndInitialRightPlayWord A (bundle.rightInitialPlay A inputs) := by
    funext n
    have hout := endToEndOperational_execution_outputs A bundle env n
    cases n with
    | zero =>
        obtain ⟨shadow, htrace⟩ :=
          endToEndOperationalTrace_allRight_one A bundle inputs
        rw [htrace] at hout
        apply roundRecord_eq_of_fields
        · simp [execution_apply, env, endToEndAllRightEnvironment,
            endToEndInitialRightPlayWord,
            nextRound, endToEndInitialRightPhysicalLetter,
            EndToEndOperationalControllerPackage.rightInitialPlay,
            treePlay, blockLabelApply, rightRoundRecord]
        · simp [execution_apply, env, endToEndAllRightEnvironment,
            endToEndInitialRightPlayWord,
            nextRound, endToEndInitialRightPhysicalLetter,
            EndToEndOperationalControllerPackage.rightInitialPlay,
            treePlay, blockLabelApply, rightRoundRecord]
        · simp [execution_apply, env, endToEndAllRightEnvironment,
            endToEndInitialRightPlayWord,
            nextRound, endToEndInitialRightPhysicalLetter,
            EndToEndOperationalControllerPackage.rightInitialPlay,
            treePlay, blockLabelApply, rightRoundRecord]
        · exact congrArg Prod.fst hout
        · exact congrArg Prod.snd hout
    | succ k =>
        obtain ⟨pair, htrace⟩ :=
          endToEndOperationalTrace_allRight_later A bundle inputs k
        rw [htrace] at hout
        apply roundRecord_eq_of_fields
        · simp [execution_apply, env, endToEndAllRightEnvironment,
            endToEndInitialRightPlayWord,
            nextRound, endToEndInitialRightPhysicalLetter,
            EndToEndOperationalControllerPackage.rightInitialPlay,
            treePlay, blockLabelApply, rightRoundRecord]
        · simp [execution_apply, env, endToEndAllRightEnvironment,
            endToEndInitialRightPlayWord,
            nextRound, endToEndInitialRightPhysicalLetter,
            EndToEndOperationalControllerPackage.rightInitialPlay,
            treePlay, blockLabelApply, rightRoundRecord]
        · simp [execution_apply, env, endToEndAllRightEnvironment,
            endToEndInitialRightPlayWord,
            nextRound, endToEndInitialRightPhysicalLetter,
            EndToEndOperationalControllerPackage.rightInitialPlay,
            treePlay, blockLabelApply, rightRoundRecord]
        · exact congrArg Prod.fst hout
        · exact congrArg Prod.snd hout
  rw [hword]
  exact bundle.rightInitialPlay_accepts A inputs

end

end DetParityAutomaton

end DistributedSynthesis
