/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointFreshPolicyCanonicalPhysicalSchedule

/-!
# Canonical physical schedule aligned at a strict reversal

The total root-oriented clock has a deliberately permissive mismatch branch:
it consumes one physical round while the proof-side fixed-policy root still
changes orientation.  That branch is useful for total definitions, but it is
not the invariant used by the persistent-reversal proof.

After the last simultaneous round, start instead at a genuine strict
reversal whose physical graph agrees with the selected fixed-policy root.
Every canonical close then consumes the complete maximal homogeneous strict
block.  Its successor cut has the opposite strict graph, and the checked
policy target has the opposite orientation as well.  Thus graph/root
alignment is preserved forever and the mismatch branch is unreachable.

All orientations and cuts below are proof-side.  No local process receives a
leader, side, graph, row, or phase bit.
-/

namespace DistributedSynthesis

universe u v x y s t

/-! ## Pure graph lemma -/

/-- At the end of a maximal strict run in an everywhere-strict suffix, the
graph is exactly the opposite strict graph. -/
theorem operationalCloseNext_eq_strictFlip_of_everywhere_strict
    (graphs : Nat → Graph) (hterm : OperationalStrictRunsTerminate graphs)
    (hstrict : ∀ n : Nat, graphs n ≠ .both) (n : Nat) :
    graphs (operationalCloseNext graphs hterm n) =
      DetParityAutomaton.profiledRawJointStrictGraphFlip (graphs n) := by
  have hne := operationalCloseNext_graph_ne_of_strict graphs hterm (hstrict n)
  have hnext := hstrict (operationalCloseNext graphs hterm n)
  cases hcurrent : graphs n with
  | both => exact False.elim (hstrict n hcurrent)
  | left =>
      cases htarget : graphs (operationalCloseNext graphs hterm n) with
      | both => exact False.elim (hnext htarget)
      | left => exact False.elim (hne (htarget.trans hcurrent.symm))
      | right => rfl
  | right =>
      cases htarget : graphs (operationalCloseNext graphs hterm n) with
      | both => exact False.elim (hnext htarget)
      | left => rfl
      | right => exact False.elim (hne (htarget.trans hcurrent.symm))

namespace FiniteGlobalRoundMachine

universe w

variable {In₁ : Type u} {In₂ : Type v}
variable (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)

/-- Equality of the first transition propagates to every positive rerooted
state index.  This is the state-level companion of the existing Moore-word
lemma `reroot_globalMachineTraceWord_eq_of_first_step_eq`. -/
theorem reroot_globalStateTrace_eq_of_first_step_eq
    (env : EnvironmentSequence In₁ In₂) (left right : G.State)
    (hfirst : G.step left (env 0) = G.step right (env 0))
    (n : Nat) (hn : 0 < n) :
    (G.reroot left).globalStateTrace env n =
      (G.reroot right).globalStateTrace env n := by
  have hstate : ∀ k : Nat,
      (G.reroot left).globalStateTrace env (k + 1) =
        (G.reroot right).globalStateTrace env (k + 1) := by
    intro k
    induction k with
    | zero => exact hfirst
    | succ k ih =>
        change G.step
            ((G.reroot left).globalStateTrace env (k + 1)) (env (k + 1)) =
          G.step ((G.reroot right).globalStateTrace env (k + 1))
            (env (k + 1))
        rw [ih]
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  subst n
  simpa using hstate k

end FiniteGlobalRoundMachine

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
  (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
  (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
    (initial.code A))
  (bank : ProfiledRawJointUnitPolicyControllerBank A strategy initial policy)

/-! ## Generic finite-slice state bookkeeping -/

section
omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂]

/-- A DPA run over `n` letters is the list fold over its omega prefix. -/
theorem runFrom_eq_omegaPrefix_foldl
    (state : A.State)
    (word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂)) :
    ∀ n : Nat,
      A.runFrom state word n = (omegaPrefix word n).foldl A.step state := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [omegaPrefix_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      exact congrArg (fun current ↦ A.step current (word n)) ih

/-- Exact state propagation across one cut block.  `block` excludes the
closing letter, matching `cutBlockMin`; the closing letter produces the next
cut state. -/
theorem run_at_nextCut_eq_of_slice_and_closing
    (word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (start : Nat) (cuts : Nat → Nat) (k : Nat)
    (state : A.State)
    (block : List (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (closing : RoundRecord In₁ In₂ Graph Out₁ Out₂)
    (targetState : A.State)
    (hcut : cuts k < cuts (k + 1))
    (hstate : A.run word (start + cuts k) = state)
    (hlength : block.length = cuts (k + 1) - cuts k - 1)
    (hslice : omegaPrefix (OmegaWord.drop word (start + cuts k))
      block.length = block)
    (hclosing : OmegaWord.drop word (start + cuts k) block.length = closing)
    (htarget : targetState = A.step (block.foldl A.step state) closing) :
    A.run word (start + cuts (k + 1)) = targetState := by
  let localWord := OmegaWord.drop word (start + cuts k)
  have hclosingLocal : localWord block.length = closing := by
    exact hclosing
  have hdelta : cuts (k + 1) = cuts k + (block.length + 1) := by
    omega
  have hdrop := A.runFrom_drop A.initial word (start + cuts k)
    (block.length + 1)
  calc
    A.run word (start + cuts (k + 1)) =
        A.runFrom (A.run word (start + cuts k)) localWord
          (block.length + 1) := by
      rw [hdelta]
      symm
      simpa [DetParityAutomaton.run, localWord, Nat.add_assoc] using hdrop
    _ = A.runFrom state localWord (block.length + 1) := by rw [hstate]
    _ = (omegaPrefix localWord (block.length + 1)).foldl A.step state :=
      runFrom_eq_omegaPrefix_foldl A state localWord (block.length + 1)
    _ = (block ++ [closing]).foldl A.step state := by
      rw [omegaPrefix_succ, hslice, hclosingLocal]
    _ = A.step (block.foldl A.step state) closing := by
      rw [List.foldl_append]
      rfl
    _ = targetState := htarget.symm

/-- State-relative presentation of the same next-cut propagation. -/
theorem runFrom_at_nextCut_eq_of_slice_and_closing
    (physicalState : A.State)
    (word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (cuts : Nat → Nat) (k : Nat)
    (state : A.State)
    (block : List (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (closing : RoundRecord In₁ In₂ Graph Out₁ Out₂)
    (targetState : A.State)
    (hcut : cuts k < cuts (k + 1))
    (hstate : A.runFrom physicalState word (cuts k) = state)
    (hlength : block.length = cuts (k + 1) - cuts k - 1)
    (hslice : omegaPrefix (OmegaWord.drop word (cuts k)) block.length = block)
    (hclosing : OmegaWord.drop word (cuts k) block.length = closing)
    (htarget : targetState = A.step (block.foldl A.step state) closing) :
    A.runFrom physicalState word (cuts (k + 1)) = targetState := by
  have hstate' :
      (A.withInitial physicalState).run word (0 + cuts k) = state := by
    simpa only [Nat.zero_add, withInitial_run] using hstate
  have hslice' :
      omegaPrefix (OmegaWord.drop word (0 + cuts k)) block.length = block := by
    simpa only [Nat.zero_add] using hslice
  have hclosing' :
      OmegaWord.drop word (0 + cuts k) block.length = closing := by
    simpa only [Nat.zero_add] using hclosing
  simpa only [Nat.zero_add, withInitial_run] using
    (run_at_nextCut_eq_of_slice_and_closing (A.withInitial physicalState)
      word 0 cuts k state block closing targetState hcut hstate' hlength
      hslice' hclosing' htarget)

/-- State-relative finite-slice block-minimum alignment. -/
theorem cutBlockMin_runFrom_eq_priority_blockMinState_of_slice_alignment
    (physicalState : A.State)
    (word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (cuts : Nat → Nat) (k : Nat)
    (state : A.State)
    (block : List (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (hstate : A.runFrom physicalState word (cuts k) = state)
    (hlength : block.length = cuts (k + 1) - cuts k - 1)
    (hslice : omegaPrefix (OmegaWord.drop word (cuts k)) block.length =
      block) :
    cutBlockMin
        (fun n ↦ A.priority (A.runFrom physicalState word n)) cuts k =
      A.priority (blockMinState A state block) := by
  have hstate' :
      (A.withInitial physicalState).run word (0 + cuts k) = state := by
    simpa only [Nat.zero_add, withInitial_run] using hstate
  have hslice' :
      omegaPrefix (OmegaWord.drop word (0 + cuts k)) block.length = block := by
    simpa only [Nat.zero_add] using hslice
  simpa only [Nat.zero_add, withInitial_run] using
    (cutBlockMin_eq_priority_blockMinState_of_slice_alignment
      (A.withInitial physicalState) word 0 cuts k state block hstate' hlength
        hslice')

end

/-! ## Alignment of the concrete simultaneous cut/root recursion -/

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- If the seed agrees with the first graph of an everywhere-strict suffix,
then every root of the canonical physical recursion agrees with the graph at
its projected cut.  In particular the total mismatch branch is never used. -/
theorem profiledRawJointUnitPolicyPhysicalThread_graph_aligned
    (physicalEnv : EnvironmentSequence In₁ In₂) (base : Nat)
    (hterm : OperationalStrictRunsTerminate
      (profiledRawJointPhysicalGraphTail physicalEnv base))
    (seed : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy)
    (rowAt : Nat → PairedEntryRow)
    (hstrict : ∀ n : Nat,
      profiledRawJointPhysicalGraphTail physicalEnv base n ≠ .both)
    (hseed : profiledRawJointPhysicalGraphTail physicalEnv base 0 =
      seed.graph A strategy initial policy) : ∀ k : Nat,
    profiledRawJointPhysicalGraphTail physicalEnv base
        (profiledRawJointUnitPolicyPhysicalThreadCuts A strategy initial
          policy bank physicalEnv base hterm seed rowAt k) =
      (profiledRawJointUnitPolicyPhysicalThreadRoot A strategy initial policy
        bank physicalEnv base hterm seed rowAt k).graph A strategy initial
          policy := by
  intro k
  induction k with
  | zero => exact hseed
  | succ k ih =>
      let current := profiledRawJointUnitPolicyPhysicalThreadState A strategy
        initial policy bank physicalEnv base hterm seed rowAt k
      have hmatch :
          profiledRawJointPhysicalGraphTail physicalEnv base current.1 =
            current.2.graph A strategy initial policy := by
        simpa [current, profiledRawJointUnitPolicyPhysicalThreadCuts,
          profiledRawJointUnitPolicyPhysicalThreadRoot] using ih
      change profiledRawJointPhysicalGraphTail physicalEnv base
          (rootOrientedCloseNext
            (profiledRawJointPhysicalGraphTail physicalEnv base) hterm
              (current.2.graph A strategy initial policy) current.1) =
        ((profiledRawJointUnitPolicyPhysicalCloseQuery A strategy initial
          policy physicalEnv (base + current.1)
            (base + rootOrientedCloseNext
              (profiledRawJointPhysicalGraphTail physicalEnv base) hterm
                (current.2.graph A strategy initial policy) current.1)
            (rowAt k) current.2).target A strategy initial policy bank).graph
              A strategy initial policy
      rw [rootOrientedCloseNext_of_match _ _ _ hmatch]
      rw [ProfiledRawJointUnitPolicyCloseQuery.target_graph]
      rw [← hmatch]
      exact operationalCloseNext_eq_strictFlip_of_everywhere_strict
        (profiledRawJointPhysicalGraphTail physicalEnv base) hterm hstrict
          current.1

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Schedule/cut projection of the same no-mismatch theorem.  This is the
form consumed by `ProfiledRawJointUnitPolicyFixedRerootControlEquations`. -/
theorem profiledRawJointUnitPolicyPhysicalCloseSchedule_graph_aligned
    (physicalEnv : EnvironmentSequence In₁ In₂) (base : Nat)
    (hterm : OperationalStrictRunsTerminate
      (profiledRawJointPhysicalGraphTail physicalEnv base))
    (seed : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy)
    (rowAt : Nat → PairedEntryRow)
    (hstrict : ∀ n : Nat,
      profiledRawJointPhysicalGraphTail physicalEnv base n ≠ .both)
    (hseed : profiledRawJointPhysicalGraphTail physicalEnv base 0 =
      seed.graph A strategy initial policy) : ∀ k : Nat,
    let schedule := profiledRawJointUnitPolicyPhysicalCloseSchedule A strategy
      initial policy bank physicalEnv base hterm seed rowAt
    profiledRawJointPhysicalGraphTail physicalEnv base
        (profiledRawJointUnitPolicyRootOrientedCuts A strategy initial policy
          bank physicalEnv base hterm seed schedule k) =
      profiledRawJointUnitPolicyScheduledGraph A strategy initial policy bank
        seed schedule k := by
  intro k
  dsimp only
  rw [profiledRawJointUnitPolicyRootOrientedCuts_physicalCloseSchedule,
    show profiledRawJointUnitPolicyScheduledGraph A strategy initial policy
          bank seed
            (profiledRawJointUnitPolicyPhysicalCloseSchedule A strategy
              initial policy bank physicalEnv base hterm seed rowAt) k =
        (profiledRawJointUnitPolicyPhysicalThreadRoot A strategy initial policy
          bank physicalEnv base hterm seed rowAt k).graph A strategy initial
            policy by
      unfold profiledRawJointUnitPolicyScheduledGraph
      rw [profiledRawJointUnitPolicyScheduledRoot_physicalCloseSchedule]]
  exact profiledRawJointUnitPolicyPhysicalThread_graph_aligned A strategy
    initial policy bank physicalEnv base hterm seed rowAt hstrict hseed k

/-! ## One exact aligned close endpoint -/

private abbrev UnitKernel
    {InitialOne : Type*} {InitialTwo : Type*}
    {ExceptionalOne : Type*} {ExceptionalTwo : Type*}
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo) :=
  profiledRawJointUnitPolicyLeaderFreeKernel A strategy initial policy bank
    adapter

section
omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂]

/-- The fresh-row coordinate of an exact checked right target is the actual
current coordinate obtained by feeding the strict-right closing letter to the
scan.  The restriction to `.first` is essential: the `.both` coordinate of
the target stores the counterfactual simultaneous closing round. -/
theorem pairedCodeStateForRow_first_eq_rightScanStep_current_of_exactTarget
    (slot : ProfiledRawLeftSlot A) (scan : PairedRightScanState A)
    (letter : PairedRightBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hexact : erasePairedProfiledState A (.inr (.inr slot)) =
      pairedRightCloseTarget A scan .first letter) :
    pairedCodeStateForRow A .first slot.1.1 =
      (pairedRightScanPairForRow A .first
        (pairedRightScanStep A scan letter)).1 := by
  simp [erasePairedProfiledState, pairedRightCloseTarget,
    pairedCodeStateForRow, pairedRightScanPairForRow,
    pairedRightScanStep] at hexact ⊢
  exact congrArg (fun value ↦ value.1.1) hexact

/-- More importantly, a close selected from *either* old row stores its
actual strict successor in the fresh `.first` coordinate of the child code.
The old row is used only to select the old current state and the physical
receiver output.  This is the exact proof-side restart equation: it resets no
executable bit and tells no endpoint which row was selected. -/
theorem
    pairedCodeStateForRow_first_eq_rightScanStep_selected_current_of_exactTarget
    (slot : ProfiledRawLeftSlot A) (scan : PairedRightScanState A)
    (row : PairedEntryRow)
    (letter : PairedRightBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hexact : erasePairedProfiledState A (.inr (.inr slot)) =
      pairedRightCloseTarget A scan row letter) :
    pairedCodeStateForRow A .first slot.1.1 =
      (pairedRightScanPairForRow A row
        (pairedRightScanStep A scan letter)).1 := by
  cases row <;>
    simp [erasePairedProfiledState, pairedRightCloseTarget,
      pairedCodeStateForRow, pairedRightScanPairForRow,
      pairedRightScanStep] at hexact ⊢ <;>
    exact congrArg (fun value ↦ value.1.1) hexact

/-- Left-target mirror. -/
theorem pairedCodeStateForRow_first_eq_leftScanStep_current_of_exactTarget
    (slot : ProfiledRawRightSlot A) (scan : PairedLeftScanState A)
    (letter : PairedLeftBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hexact : erasePairedProfiledState A (.inr (.inl slot)) =
      pairedLeftCloseTarget A scan .first letter) :
    pairedCodeStateForRow A .first slot.1.1 =
      (pairedLeftScanPairForRow A .first
        (pairedLeftScanStep A scan letter)).1 := by
  simp [erasePairedProfiledState, pairedLeftCloseTarget,
    pairedCodeStateForRow, pairedLeftScanPairForRow,
    pairedLeftScanStep] at hexact ⊢
  exact congrArg (fun value ↦ value.1.1) hexact

/-- Left-close mirror of the row-independent fresh-coordinate restart. -/
theorem
    pairedCodeStateForRow_first_eq_leftScanStep_selected_current_of_exactTarget
    (slot : ProfiledRawRightSlot A) (scan : PairedLeftScanState A)
    (row : PairedEntryRow)
    (letter : PairedLeftBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hexact : erasePairedProfiledState A (.inr (.inl slot)) =
      pairedLeftCloseTarget A scan row letter) :
    pairedCodeStateForRow A .first slot.1.1 =
      (pairedLeftScanPairForRow A row
        (pairedLeftScanStep A scan letter)).1 := by
  cases row <;>
    simp [erasePairedProfiledState, pairedLeftCloseTarget,
      pairedCodeStateForRow, pairedLeftScanPairForRow,
      pairedLeftScanStep] at hexact ⊢ <;>
    exact congrArg (fun value ↦ value.1.1) hexact

end

/-! ## Exact simultaneous-close state -/

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- For a simultaneous close the actual successor is the target's `.both`
coordinate.  The old row still selects the current scan state, but it is not
stored or observed by the executable controller. -/
theorem
    pairedCodeStateForRow_both_eq_rightBothStep_selected_current_of_exactTarget
    (slot : ProfiledRawLeftSlot A) (scan : PairedRightScanState A)
    (row : PairedEntryRow)
    (letter : PairedRightBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hexact : erasePairedProfiledState A (.inr (.inr slot)) =
      pairedRightCloseTarget A scan row letter) :
    pairedCodeStateForRow A .both slot.1.1 =
      A.step (pairedRightScanPairForRow A row scan).1
        (bothRoundRecord (letter.1.2, letter.1.1)
          (pairedRightClosingForRow row letter.2.1)
          (pairedRightInformedForRow row letter.2.1)) := by
  cases row <;>
    simp [erasePairedProfiledState, pairedRightCloseTarget,
      pairedCodeStateForRow, pairedRightScanPairForRow,
      pairedRightClosingForRow, pairedRightInformedForRow] at hexact ⊢ <;>
    exact congrArg (fun value ↦ value.1.2) hexact

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- Simultaneous left-close mirror. -/
theorem
    pairedCodeStateForRow_both_eq_leftBothStep_selected_current_of_exactTarget
    (slot : ProfiledRawRightSlot A) (scan : PairedLeftScanState A)
    (row : PairedEntryRow)
    (letter : PairedLeftBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hexact : erasePairedProfiledState A (.inr (.inl slot)) =
      pairedLeftCloseTarget A scan row letter) :
    pairedCodeStateForRow A .both slot.1.1 =
      A.step (pairedLeftScanPairForRow A row scan).1
        (bothRoundRecord letter.1
          (pairedLeftInformedForRow row letter.2.1)
          (pairedLeftClosingForRow row letter.2.1)) := by
  cases row <;>
    simp [erasePairedProfiledState, pairedLeftCloseTarget,
      pairedCodeStateForRow, pairedLeftScanPairForRow,
      pairedLeftClosingForRow, pairedLeftInformedForRow] at hexact ⊢ <;>
    exact congrArg (fun value ↦ value.1.2) hexact

/-! ## Row-free packets exposed by a checked strict close -/

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- A checked right close carries both pieces needed by the alternating
macro-thread pasting argument.  Its root priority is the selected old row's
physical block minimum, while its fresh `.first` code coordinate is the
actual state after the strict closing round.  Thus the proof lineage may
refresh at the cut without changing the executable receiver row. -/
theorem pairedRightClose_freshState_and_blockPriority_of_exactTarget
    (slot : ProfiledRawLeftSlot A) (scan : PairedRightScanState A)
    (row : PairedEntryRow)
    (letter : PairedRightBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hexact : erasePairedProfiledState A (.inr (.inr slot)) =
      pairedRightCloseTarget A scan row letter) :
    pairedCodeStateForRow A .first slot.1.1 =
        (pairedRightScanPairForRow A row
          (pairedRightScanStep A scan letter)).1 ∧
      profiledRawJointThreadRootPriority A (.inr slot) =
        A.priority (pairedRightScanPairForRow A row scan).2 := by
  constructor
  · exact
      pairedCodeStateForRow_first_eq_rightScanStep_selected_current_of_exactTarget
        A slot scan row letter hexact
  · exact pairedProfiledEntryPriority_eq_rightScanPairForRow_min_of_erase_eq
      A (.inr (.inr slot)) scan row letter hexact

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- Left-close mirror of the row-free cut packet. -/
theorem pairedLeftClose_freshState_and_blockPriority_of_exactTarget
    (slot : ProfiledRawRightSlot A) (scan : PairedLeftScanState A)
    (row : PairedEntryRow)
    (letter : PairedLeftBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (hexact : erasePairedProfiledState A (.inr (.inl slot)) =
      pairedLeftCloseTarget A scan row letter) :
    pairedCodeStateForRow A .first slot.1.1 =
        (pairedLeftScanPairForRow A row
          (pairedLeftScanStep A scan letter)).1 ∧
      profiledRawJointThreadRootPriority A (.inl slot) =
        A.priority (pairedLeftScanPairForRow A row scan).2 := by
  constructor
  · exact
      pairedCodeStateForRow_first_eq_leftScanStep_selected_current_of_exactTarget
        A slot scan row letter hexact
  · exact pairedProfiledEntryPriority_eq_leftScanPairForRow_min_of_erase_eq
      A (.inr (.inl slot)) scan row letter hexact

/-! ## Target-parametric monitor lift -/

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype Out₂] in
/-- Any winning target-parametric right controller exposes the same row-free
packet at an emitted live left target.  This is the form consumed by linked
targets: narrowing may replace the target payload, but the target monitor's
checked erasure still supplies the exact close equation. -/
theorem profiledRawJointTargetRight_freshState_and_blockPriority_of_wins
    {Target : Type t} [Fintype Target]
    (targetState : Target → PairedProfiledTreeState A)
    (Allowed : Target → Prop)
    (source : ProfiledRawRightSlot A)
    (play : Nat → RealizedBlockRound In₂ In₁
      (ProfiledRawJointTargetRightReceiverOutput
        (Out₁ := Out₁) (Out₂ := Out₂) Target) Out₁)
    (hwin : (profiledRawJointTargetRightBlockMonitor A Target targetState
      Allowed source).WinsPlay play)
    (n : Nat) (row : PairedEntryRow) (slot : ProfiledRawLeftSlot A)
    (htarget : targetState ((play n).2.1.target row) =
      .inr (.inr slot)) :
    pairedCodeStateForRow A .first slot.1.1 =
        (pairedRightScanPairForRow A row
          (pairedRightScanStep A
            ((profiledRawJointTargetRightBlockMonitor A Target targetState
              Allowed source).run play n).2.1
            (profiledRawJointTargetRightPhysicalLetter A (play n)))).1 ∧
      profiledRawJointThreadRootPriority A (.inr slot) =
        A.priority
          (blockMinState A
            (pairedCodeStateForRow A row source.1.1)
            (profiledRawJointTargetRightPhysicalPrefixRecords A row
              (omegaPrefix play n))) := by
  have hsafe := profiledRawJointTargetRight_targetsSafe_of_wins A targetState
    Allowed source play hwin n row
  have hexact : erasePairedProfiledState A (.inr (.inr slot)) =
      pairedRightCloseTarget A
        ((profiledRawJointTargetRightBlockMonitor A Target targetState Allowed
          source).run play n).2.1 row
        (profiledRawJointTargetRightPhysicalLetter A (play n)) := by
    rw [← htarget]
    exact hsafe.1
  constructor
  · exact
      pairedCodeStateForRow_first_eq_rightScanStep_selected_current_of_exactTarget
        A slot
          ((profiledRawJointTargetRightBlockMonitor A Target targetState
            Allowed source).run play n).2.1 row
          (profiledRawJointTargetRightPhysicalLetter A (play n)) hexact
  · have hpriority :=
      profiledRawJointTargetRight_targetPriority_eq_blockMin_of_wins A
        targetState Allowed source play hwin n row
    rw [htarget] at hpriority
    exact hpriority

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype Out₁] in
/-- Left-target mirror of the target-parametric row-free packet. -/
theorem profiledRawJointTargetLeft_freshState_and_blockPriority_of_wins
    {Target : Type t} [Fintype Target]
    (targetState : Target → PairedProfiledTreeState A)
    (Allowed : Target → Prop)
    (source : ProfiledRawLeftSlot A)
    (play : Nat → RealizedBlockRound In₁ In₂
      (ProfiledRawJointTargetLeftReceiverOutput
        (Out₁ := Out₁) (Out₂ := Out₂) Target) Out₂)
    (hwin : (profiledRawJointTargetLeftBlockMonitor A Target targetState
      Allowed source).WinsPlay play)
    (n : Nat) (row : PairedEntryRow) (slot : ProfiledRawRightSlot A)
    (htarget : targetState ((play n).2.1.target row) =
      .inr (.inl slot)) :
    pairedCodeStateForRow A .first slot.1.1 =
        (pairedLeftScanPairForRow A row
          (pairedLeftScanStep A
            ((profiledRawJointTargetLeftBlockMonitor A Target targetState
              Allowed source).run play n).2.1
            (profiledRawJointTargetLeftPhysicalLetter A (play n)))).1 ∧
      profiledRawJointThreadRootPriority A (.inl slot) =
        A.priority
          (blockMinState A
            (pairedCodeStateForRow A row source.1.1)
            (profiledRawJointTargetLeftPhysicalPrefixRecords A row
              (omegaPrefix play n))) := by
  have hsafe := profiledRawJointTargetLeft_targetsSafe_of_wins A targetState
    Allowed source play hwin n row
  have hexact : erasePairedProfiledState A (.inr (.inl slot)) =
      pairedLeftCloseTarget A
        ((profiledRawJointTargetLeftBlockMonitor A Target targetState Allowed
          source).run play n).2.1 row
        (profiledRawJointTargetLeftPhysicalLetter A (play n)) := by
    rw [← htarget]
    exact hsafe.1
  constructor
  · exact
      pairedCodeStateForRow_first_eq_leftScanStep_selected_current_of_exactTarget
        A slot
          ((profiledRawJointTargetLeftBlockMonitor A Target targetState
            Allowed source).run play n).2.1 row
          (profiledRawJointTargetLeftPhysicalLetter A (play n)) hexact
  · have hpriority :=
      profiledRawJointTargetLeft_targetPriority_eq_blockMin_of_wins A
        targetState Allowed source play hwin n row
    rw [htarget] at hpriority
    exact hpriority

/-! ## Target-parametric simultaneous-close packet -/

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype Out₂] in
/-- A winning right target table also exposes the exact simultaneous
successor coordinate.  This is a *one-step* state packet for an actual
`.both` closing round; it does not by itself justify iterating with the
receiver's retained source row.  Such an iteration must separately establish
the next segment's fresh receiver initialization.  The block-priority
component is unchanged. -/
theorem profiledRawJointTargetRight_bothState_and_blockPriority_of_wins
    {Target : Type t} [Fintype Target]
    (targetState : Target → PairedProfiledTreeState A)
    (Allowed : Target → Prop)
    (source : ProfiledRawRightSlot A)
    (play : Nat → RealizedBlockRound In₂ In₁
      (ProfiledRawJointTargetRightReceiverOutput
        (Out₁ := Out₁) (Out₂ := Out₂) Target) Out₁)
    (hwin : (profiledRawJointTargetRightBlockMonitor A Target targetState
      Allowed source).WinsPlay play)
    (n : Nat) (row : PairedEntryRow) (slot : ProfiledRawLeftSlot A)
    (htarget : targetState ((play n).2.1.target row) =
      .inr (.inr slot)) :
    pairedCodeStateForRow A .both slot.1.1 =
        A.step
          (pairedRightScanPairForRow A row
            ((profiledRawJointTargetRightBlockMonitor A Target targetState
              Allowed source).run play n).2.1).1
          (bothRoundRecord
            ((profiledRawJointTargetRightPhysicalLetter A (play n)).1.2,
              (profiledRawJointTargetRightPhysicalLetter A (play n)).1.1)
            (pairedRightClosingForRow row
              (profiledRawJointTargetRightPhysicalLetter A (play n)).2.1)
            (pairedRightInformedForRow row
              (profiledRawJointTargetRightPhysicalLetter A (play n)).2.1)) ∧
      profiledRawJointThreadRootPriority A (.inr slot) =
        A.priority
          (blockMinState A
            (pairedCodeStateForRow A row source.1.1)
            (profiledRawJointTargetRightPhysicalPrefixRecords A row
              (omegaPrefix play n))) := by
  have hsafe := profiledRawJointTargetRight_targetsSafe_of_wins A targetState
    Allowed source play hwin n row
  have hexact : erasePairedProfiledState A (.inr (.inr slot)) =
      pairedRightCloseTarget A
        ((profiledRawJointTargetRightBlockMonitor A Target targetState Allowed
          source).run play n).2.1 row
        (profiledRawJointTargetRightPhysicalLetter A (play n)) := by
    rw [← htarget]
    exact hsafe.1
  constructor
  · exact
      pairedCodeStateForRow_both_eq_rightBothStep_selected_current_of_exactTarget
        A slot
          ((profiledRawJointTargetRightBlockMonitor A Target targetState
            Allowed source).run play n).2.1 row
          (profiledRawJointTargetRightPhysicalLetter A (play n)) hexact
  · have hpriority :=
      profiledRawJointTargetRight_targetPriority_eq_blockMin_of_wins A
        targetState Allowed source play hwin n row
    rw [htarget] at hpriority
    exact hpriority

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype Out₁] in
/-- Left simultaneous-close mirror.  Like the right packet, this is only a
one-step fact until fresh receiver initialization is supplied explicitly. -/
theorem profiledRawJointTargetLeft_bothState_and_blockPriority_of_wins
    {Target : Type t} [Fintype Target]
    (targetState : Target → PairedProfiledTreeState A)
    (Allowed : Target → Prop)
    (source : ProfiledRawLeftSlot A)
    (play : Nat → RealizedBlockRound In₁ In₂
      (ProfiledRawJointTargetLeftReceiverOutput
        (Out₁ := Out₁) (Out₂ := Out₂) Target) Out₂)
    (hwin : (profiledRawJointTargetLeftBlockMonitor A Target targetState
      Allowed source).WinsPlay play)
    (n : Nat) (row : PairedEntryRow) (slot : ProfiledRawRightSlot A)
    (htarget : targetState ((play n).2.1.target row) =
      .inr (.inl slot)) :
    pairedCodeStateForRow A .both slot.1.1 =
        A.step
          (pairedLeftScanPairForRow A row
            ((profiledRawJointTargetLeftBlockMonitor A Target targetState
              Allowed source).run play n).2.1).1
          (bothRoundRecord
            (profiledRawJointTargetLeftPhysicalLetter A (play n)).1
            (pairedLeftInformedForRow row
              (profiledRawJointTargetLeftPhysicalLetter A (play n)).2.1)
            (pairedLeftClosingForRow row
              (profiledRawJointTargetLeftPhysicalLetter A (play n)).2.1)) ∧
      profiledRawJointThreadRootPriority A (.inl slot) =
        A.priority
          (blockMinState A
            (pairedCodeStateForRow A row source.1.1)
            (profiledRawJointTargetLeftPhysicalPrefixRecords A row
              (omegaPrefix play n))) := by
  have hsafe := profiledRawJointTargetLeft_targetsSafe_of_wins A targetState
    Allowed source play hwin n row
  have hexact : erasePairedProfiledState A (.inr (.inl slot)) =
      pairedLeftCloseTarget A
        ((profiledRawJointTargetLeftBlockMonitor A Target targetState Allowed
          source).run play n).2.1 row
        (profiledRawJointTargetLeftPhysicalLetter A (play n)) := by
    rw [← htarget]
    exact hsafe.1
  constructor
  · exact
      pairedCodeStateForRow_both_eq_leftBothStep_selected_current_of_exactTarget
        A slot
          ((profiledRawJointTargetLeftBlockMonitor A Target targetState
            Allowed source).run play n).2.1 row
          (profiledRawJointTargetLeftPhysicalLetter A (play n)) hexact
  · have hpriority :=
      profiledRawJointTargetLeft_targetPriority_eq_blockMin_of_wins A
        targetState Allowed source play hwin n row
    rw [htarget] at hpriority
    exact hpriority

/-! ## Literal segment to cut-block alignment -/

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype Out₂] in
/-- Once a linked right segment is aligned with the actual physical slice,
the generic target packet is exactly the block-min/root equation consumed by
both state-relative alternating-thread acceptance and compatible-path
acceptance. -/
theorem profiledRawJointTargetRight_cutBlockMin_eq_threadRootPriority_of_wins
    {Target : Type t} [Fintype Target]
    (targetState : Target → PairedProfiledTreeState A)
    (Allowed : Target → Prop)
    (source : ProfiledRawRightSlot A)
    (play : Nat → RealizedBlockRound In₂ In₁
      (ProfiledRawJointTargetRightReceiverOutput
        (Out₁ := Out₁) (Out₂ := Out₂) Target) Out₁)
    (hwin : (profiledRawJointTargetRightBlockMonitor A Target targetState
      Allowed source).WinsPlay play)
    (n : Nat) (row : PairedEntryRow) (slot : ProfiledRawLeftSlot A)
    (htarget : targetState ((play n).2.1.target row) =
      .inr (.inr slot))
    (word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (start : Nat) (cuts : Nat → Nat) (k : Nat)
    (hstate : A.run word (start + cuts k) =
      pairedCodeStateForRow A row source.1.1)
    (hlength :
      (profiledRawJointTargetRightPhysicalPrefixRecords A row
          (omegaPrefix play n)).length =
        cuts (k + 1) - cuts k - 1)
    (hslice : omegaPrefix (OmegaWord.drop word (start + cuts k))
        (profiledRawJointTargetRightPhysicalPrefixRecords A row
          (omegaPrefix play n)).length =
      profiledRawJointTargetRightPhysicalPrefixRecords A row
        (omegaPrefix play n)) :
    cutBlockMin
        (fun j ↦ A.priority (A.run word (start + j))) cuts k =
      profiledRawJointThreadRootPriority A (.inr slot) := by
  have hpacket :=
    profiledRawJointTargetRight_freshState_and_blockPriority_of_wins A
      targetState Allowed source play hwin n row slot htarget
  rw [cutBlockMin_eq_priority_blockMinState_of_slice_alignment A word start
    cuts k (pairedCodeStateForRow A row source.1.1)
    (profiledRawJointTargetRightPhysicalPrefixRecords A row
      (omegaPrefix play n)) hstate hlength hslice]
  exact hpacket.2.symm

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype Out₁] in
/-- Left linked-segment mirror. -/
theorem profiledRawJointTargetLeft_cutBlockMin_eq_threadRootPriority_of_wins
    {Target : Type t} [Fintype Target]
    (targetState : Target → PairedProfiledTreeState A)
    (Allowed : Target → Prop)
    (source : ProfiledRawLeftSlot A)
    (play : Nat → RealizedBlockRound In₁ In₂
      (ProfiledRawJointTargetLeftReceiverOutput
        (Out₁ := Out₁) (Out₂ := Out₂) Target) Out₂)
    (hwin : (profiledRawJointTargetLeftBlockMonitor A Target targetState
      Allowed source).WinsPlay play)
    (n : Nat) (row : PairedEntryRow) (slot : ProfiledRawRightSlot A)
    (htarget : targetState ((play n).2.1.target row) =
      .inr (.inl slot))
    (word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (start : Nat) (cuts : Nat → Nat) (k : Nat)
    (hstate : A.run word (start + cuts k) =
      pairedCodeStateForRow A row source.1.1)
    (hlength :
      (profiledRawJointTargetLeftPhysicalPrefixRecords A row
          (omegaPrefix play n)).length =
        cuts (k + 1) - cuts k - 1)
    (hslice : omegaPrefix (OmegaWord.drop word (start + cuts k))
        (profiledRawJointTargetLeftPhysicalPrefixRecords A row
          (omegaPrefix play n)).length =
      profiledRawJointTargetLeftPhysicalPrefixRecords A row
        (omegaPrefix play n)) :
    cutBlockMin
        (fun j ↦ A.priority (A.run word (start + j))) cuts k =
      profiledRawJointThreadRootPriority A (.inl slot) := by
  have hpacket :=
    profiledRawJointTargetLeft_freshState_and_blockPriority_of_wins A
      targetState Allowed source play hwin n row slot htarget
  rw [cutBlockMin_eq_priority_blockMinState_of_slice_alignment A word start
    cuts k (pairedCodeStateForRow A row source.1.1)
    (profiledRawJointTargetLeftPhysicalPrefixRecords A row
      (omegaPrefix play n)) hstate hlength hslice]
  exact hpacket.2.symm

/-! ## State-relative literal segment alignment -/

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype Out₂] in
/-- State-relative form of the right linked-segment block-minimum equation.
This is the literal socket required by
`physicalTail_acceptsFrom_of_threadRootPriority`: the finite activated prefix
has already selected `physicalState`, and no restart at `A.initial` occurs. -/
theorem
    profiledRawJointTargetRight_cutBlockMinFrom_eq_threadRootPriority_of_wins
    {Target : Type t} [Fintype Target]
    (targetState : Target → PairedProfiledTreeState A)
    (Allowed : Target → Prop)
    (source : ProfiledRawRightSlot A)
    (play : Nat → RealizedBlockRound In₂ In₁
      (ProfiledRawJointTargetRightReceiverOutput
        (Out₁ := Out₁) (Out₂ := Out₂) Target) Out₁)
    (hwin : (profiledRawJointTargetRightBlockMonitor A Target targetState
      Allowed source).WinsPlay play)
    (n : Nat) (row : PairedEntryRow) (slot : ProfiledRawLeftSlot A)
    (htarget : targetState ((play n).2.1.target row) =
      .inr (.inr slot))
    (physicalState : A.State)
    (word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (cuts : Nat → Nat) (k : Nat)
    (hstate : A.runFrom physicalState word (cuts k) =
      pairedCodeStateForRow A row source.1.1)
    (hlength :
      (profiledRawJointTargetRightPhysicalPrefixRecords A row
          (omegaPrefix play n)).length =
        cuts (k + 1) - cuts k - 1)
    (hslice : omegaPrefix (OmegaWord.drop word (cuts k))
        (profiledRawJointTargetRightPhysicalPrefixRecords A row
          (omegaPrefix play n)).length =
      profiledRawJointTargetRightPhysicalPrefixRecords A row
        (omegaPrefix play n)) :
    cutBlockMin
        (fun j ↦ A.priority (A.runFrom physicalState word j)) cuts k =
      profiledRawJointThreadRootPriority A (.inr slot) := by
  have hpacket :=
    profiledRawJointTargetRight_freshState_and_blockPriority_of_wins A
      targetState Allowed source play hwin n row slot htarget
  rw [cutBlockMin_runFrom_eq_priority_blockMinState_of_slice_alignment A
    physicalState word cuts k (pairedCodeStateForRow A row source.1.1)
    (profiledRawJointTargetRightPhysicalPrefixRecords A row
      (omegaPrefix play n)) hstate hlength hslice]
  exact hpacket.2.symm

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype Out₁] in
/-- State-relative left linked-segment mirror. -/
theorem
    profiledRawJointTargetLeft_cutBlockMinFrom_eq_threadRootPriority_of_wins
    {Target : Type t} [Fintype Target]
    (targetState : Target → PairedProfiledTreeState A)
    (Allowed : Target → Prop)
    (source : ProfiledRawLeftSlot A)
    (play : Nat → RealizedBlockRound In₁ In₂
      (ProfiledRawJointTargetLeftReceiverOutput
        (Out₁ := Out₁) (Out₂ := Out₂) Target) Out₂)
    (hwin : (profiledRawJointTargetLeftBlockMonitor A Target targetState
      Allowed source).WinsPlay play)
    (n : Nat) (row : PairedEntryRow) (slot : ProfiledRawRightSlot A)
    (htarget : targetState ((play n).2.1.target row) =
      .inr (.inl slot))
    (physicalState : A.State)
    (word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (cuts : Nat → Nat) (k : Nat)
    (hstate : A.runFrom physicalState word (cuts k) =
      pairedCodeStateForRow A row source.1.1)
    (hlength :
      (profiledRawJointTargetLeftPhysicalPrefixRecords A row
          (omegaPrefix play n)).length =
        cuts (k + 1) - cuts k - 1)
    (hslice : omegaPrefix (OmegaWord.drop word (cuts k))
        (profiledRawJointTargetLeftPhysicalPrefixRecords A row
          (omegaPrefix play n)).length =
      profiledRawJointTargetLeftPhysicalPrefixRecords A row
        (omegaPrefix play n)) :
    cutBlockMin
        (fun j ↦ A.priority (A.runFrom physicalState word j)) cuts k =
      profiledRawJointThreadRootPriority A (.inl slot) := by
  have hpacket :=
    profiledRawJointTargetLeft_freshState_and_blockPriority_of_wins A
      targetState Allowed source play hwin n row slot htarget
  rw [cutBlockMin_runFrom_eq_priority_blockMinState_of_slice_alignment A
    physicalState word cuts k (pairedCodeStateForRow A row source.1.1)
    (profiledRawJointTargetLeftPhysicalPrefixRecords A row
      (omegaPrefix play n)) hstate hlength hslice]
  exact hpacket.2.symm

/-! ## Fresh target state at the following physical cut -/

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype Out₂] in
/-- Before the closing letter, an aligned right-block slice reaches exactly
the current component of the literal two-row scan.  This is the state-level
bridge between a represented common entry and the guarded finite monitor; it
does not use a priority-only surrogate or restart the checker. -/
theorem profiledRawJointTargetRight_run_add_eq_scanCurrent_of_slice
    {Target : Type t} [Fintype Target]
    (targetState : Target → PairedProfiledTreeState A)
    (Allowed : Target → Prop)
    (source : ProfiledRawRightSlot A)
    (play : Nat → RealizedBlockRound In₂ In₁
      (ProfiledRawJointTargetRightReceiverOutput
        (Out₁ := Out₁) (Out₂ := Out₂) Target) Out₁)
    (n : Nat) (row : PairedEntryRow)
    (word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (start : Nat)
    (hstate : A.run word start =
      pairedCodeStateForRow A row source.1.1)
    (hslice : omegaPrefix (OmegaWord.drop word start)
        (profiledRawJointTargetRightPhysicalPrefixRecords A row
          (omegaPrefix play n)).length =
      profiledRawJointTargetRightPhysicalPrefixRecords A row
        (omegaPrefix play n)) :
    A.run word
        (start +
          (profiledRawJointTargetRightPhysicalPrefixRecords A row
            (omegaPrefix play n)).length) =
      (pairedRightScanPairForRow A row
        ((profiledRawJointTargetRightBlockMonitor A Target targetState Allowed
          source).run play n).2.1).1 := by
  let monitor := profiledRawJointTargetRightBlockMonitor A Target targetState
    Allowed source
  let letters := (omegaPrefix play n).map
    (profiledRawJointTargetRightPhysicalLetter A)
  let block := profiledRawJointTargetRightPhysicalPrefixRecords A row
    (omegaPrefix play n)
  have hscan := profiledRawJointTargetRightBlockMonitor_run_scan_eq_physicalFold
    A targetState Allowed source play n
  have hfold := congrArg Prod.fst
    (pairedRightScanFold_pairForRow_eq_blockEndAndMin A row source.1.1
      letters)
  have hend :
      (pairedRightScanPairForRow A row (monitor.run play n).2.1).1 =
        block.foldl A.step (pairedCodeStateForRow A row source.1.1) := by
    rw [hscan]
    rw [blockEndAndMin_fst_eq_foldl A] at hfold
    simpa [letters, block,
      profiledRawJointTargetRightPhysicalPrefixRecords, List.map_map,
      Function.comp_apply] using hfold
  have hdrop := A.runFrom_drop A.initial word start block.length
  calc
    A.run word (start + block.length) =
        A.runFrom (A.run word start) (OmegaWord.drop word start)
          block.length := by
      symm
      simpa [DetParityAutomaton.run] using hdrop
    _ = A.runFrom (pairedCodeStateForRow A row source.1.1)
          (OmegaWord.drop word start) block.length := by rw [hstate]
    _ = (omegaPrefix (OmegaWord.drop word start) block.length).foldl A.step
          (pairedCodeStateForRow A row source.1.1) :=
      runFrom_eq_omegaPrefix_foldl A _ _ block.length
    _ = block.foldl A.step (pairedCodeStateForRow A row source.1.1) := by
      rw [hslice]
    _ = (pairedRightScanPairForRow A row
          (monitor.run play n).2.1).1 := hend.symm

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype Out₁] in
/-- Left-block mirror of the exact pre-closing scan-state alignment. -/
theorem profiledRawJointTargetLeft_run_add_eq_scanCurrent_of_slice
    {Target : Type t} [Fintype Target]
    (targetState : Target → PairedProfiledTreeState A)
    (Allowed : Target → Prop)
    (source : ProfiledRawLeftSlot A)
    (play : Nat → RealizedBlockRound In₁ In₂
      (ProfiledRawJointTargetLeftReceiverOutput
        (Out₁ := Out₁) (Out₂ := Out₂) Target) Out₂)
    (n : Nat) (row : PairedEntryRow)
    (word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (start : Nat)
    (hstate : A.run word start =
      pairedCodeStateForRow A row source.1.1)
    (hslice : omegaPrefix (OmegaWord.drop word start)
        (profiledRawJointTargetLeftPhysicalPrefixRecords A row
          (omegaPrefix play n)).length =
      profiledRawJointTargetLeftPhysicalPrefixRecords A row
        (omegaPrefix play n)) :
    A.run word
        (start +
          (profiledRawJointTargetLeftPhysicalPrefixRecords A row
            (omegaPrefix play n)).length) =
      (pairedLeftScanPairForRow A row
        ((profiledRawJointTargetLeftBlockMonitor A Target targetState Allowed
          source).run play n).2.1).1 := by
  let monitor := profiledRawJointTargetLeftBlockMonitor A Target targetState
    Allowed source
  let letters := (omegaPrefix play n).map
    (profiledRawJointTargetLeftPhysicalLetter A)
  let block := profiledRawJointTargetLeftPhysicalPrefixRecords A row
    (omegaPrefix play n)
  have hscan := profiledRawJointTargetLeftBlockMonitor_run_scan_eq_physicalFold
    A targetState Allowed source play n
  have hfold := congrArg Prod.fst
    (pairedLeftScanFold_pairForRow_eq_blockEndAndMin A row source.1.1
      letters)
  have hend :
      (pairedLeftScanPairForRow A row (monitor.run play n).2.1).1 =
        block.foldl A.step (pairedCodeStateForRow A row source.1.1) := by
    rw [hscan]
    rw [blockEndAndMin_fst_eq_foldl A] at hfold
    simpa [letters, block,
      profiledRawJointTargetLeftPhysicalPrefixRecords, List.map_map,
      Function.comp_apply] using hfold
  have hdrop := A.runFrom_drop A.initial word start block.length
  calc
    A.run word (start + block.length) =
        A.runFrom (A.run word start) (OmegaWord.drop word start)
          block.length := by
      symm
      simpa [DetParityAutomaton.run] using hdrop
    _ = A.runFrom (pairedCodeStateForRow A row source.1.1)
          (OmegaWord.drop word start) block.length := by rw [hstate]
    _ = (omegaPrefix (OmegaWord.drop word start) block.length).foldl A.step
          (pairedCodeStateForRow A row source.1.1) :=
      runFrom_eq_omegaPrefix_foldl A _ _ block.length
    _ = block.foldl A.step (pairedCodeStateForRow A row source.1.1) := by
      rw [hslice]
    _ = (pairedLeftScanPairForRow A row
          (monitor.run play n).2.1).1 := hend.symm

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype Out₂] in
/-- The same right linked segment also propagates the actual DPA state to the
fresh `.first` coordinate of the emitted target.  In particular, when the
next linked table is entered through its `.first` cell, its required entry
state follows automatically rather than being postulated at every cut. -/
theorem profiledRawJointTargetRight_run_at_nextCut_eq_freshState_of_wins
    {Target : Type t} [Fintype Target]
    (targetState : Target → PairedProfiledTreeState A)
    (Allowed : Target → Prop)
    (source : ProfiledRawRightSlot A)
    (play : Nat → RealizedBlockRound In₂ In₁
      (ProfiledRawJointTargetRightReceiverOutput
        (Out₁ := Out₁) (Out₂ := Out₂) Target) Out₁)
    (hwin : (profiledRawJointTargetRightBlockMonitor A Target targetState
      Allowed source).WinsPlay play)
    (n : Nat) (row : PairedEntryRow) (slot : ProfiledRawLeftSlot A)
    (htarget : targetState ((play n).2.1.target row) =
      .inr (.inr slot))
    (word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (start : Nat) (cuts : Nat → Nat) (k : Nat)
    (hcut : cuts k < cuts (k + 1))
    (hstate : A.run word (start + cuts k) =
      pairedCodeStateForRow A row source.1.1)
    (hlength :
      (profiledRawJointTargetRightPhysicalPrefixRecords A row
          (omegaPrefix play n)).length =
        cuts (k + 1) - cuts k - 1)
    (hslice : omegaPrefix (OmegaWord.drop word (start + cuts k))
        (profiledRawJointTargetRightPhysicalPrefixRecords A row
          (omegaPrefix play n)).length =
      profiledRawJointTargetRightPhysicalPrefixRecords A row
        (omegaPrefix play n))
    (hclosing : OmegaWord.drop word (start + cuts k)
        (profiledRawJointTargetRightPhysicalPrefixRecords A row
          (omegaPrefix play n)).length =
      pairedRightRecordForRow row
        (profiledRawJointTargetRightPhysicalLetter A (play n))) :
    A.run word (start + cuts (k + 1)) =
      pairedCodeStateForRow A .first slot.1.1 := by
  let monitor := profiledRawJointTargetRightBlockMonitor A Target targetState
    Allowed source
  let letters := (omegaPrefix play n).map
    (profiledRawJointTargetRightPhysicalLetter A)
  let block := profiledRawJointTargetRightPhysicalPrefixRecords A row
    (omegaPrefix play n)
  let closing := pairedRightRecordForRow row
    (profiledRawJointTargetRightPhysicalLetter A (play n))
  have hpacket :=
    profiledRawJointTargetRight_freshState_and_blockPriority_of_wins A
      targetState Allowed source play hwin n row slot htarget
  have hscan := profiledRawJointTargetRightBlockMonitor_run_scan_eq_physicalFold
    A targetState Allowed source play n
  have hfold := congrArg Prod.fst
    (pairedRightScanFold_pairForRow_eq_blockEndAndMin A row source.1.1
      letters)
  have hend :
      (pairedRightScanPairForRow A row (monitor.run play n).2.1).1 =
        block.foldl A.step (pairedCodeStateForRow A row source.1.1) := by
    rw [hscan]
    rw [blockEndAndMin_fst_eq_foldl A] at hfold
    simpa [letters, block,
      profiledRawJointTargetRightPhysicalPrefixRecords, List.map_map,
      Function.comp_apply] using hfold
  have htargetState :
      pairedCodeStateForRow A .first slot.1.1 =
        A.step
          (block.foldl A.step
            (pairedCodeStateForRow A row source.1.1)) closing := by
    calc
      pairedCodeStateForRow A .first slot.1.1 =
          (pairedRightScanPairForRow A row
            (pairedRightScanStep A (monitor.run play n).2.1
              (profiledRawJointTargetRightPhysicalLetter A (play n)))).1 :=
        hpacket.1
      _ = A.step
            (pairedRightScanPairForRow A row
              (monitor.run play n).2.1).1 closing := by
          cases row <;> rfl
      _ = A.step
            (block.foldl A.step
              (pairedCodeStateForRow A row source.1.1)) closing := by
          rw [hend]
  exact run_at_nextCut_eq_of_slice_and_closing A word start cuts k
    (pairedCodeStateForRow A row source.1.1) block closing
    (pairedCodeStateForRow A .first slot.1.1) hcut hstate
    (by simpa [block] using hlength) (by simpa [block] using hslice)
    (by simpa [block, closing] using hclosing) htargetState

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype Out₁] in
/-- Left linked-segment mirror of fresh-state propagation. -/
theorem profiledRawJointTargetLeft_run_at_nextCut_eq_freshState_of_wins
    {Target : Type t} [Fintype Target]
    (targetState : Target → PairedProfiledTreeState A)
    (Allowed : Target → Prop)
    (source : ProfiledRawLeftSlot A)
    (play : Nat → RealizedBlockRound In₁ In₂
      (ProfiledRawJointTargetLeftReceiverOutput
        (Out₁ := Out₁) (Out₂ := Out₂) Target) Out₂)
    (hwin : (profiledRawJointTargetLeftBlockMonitor A Target targetState
      Allowed source).WinsPlay play)
    (n : Nat) (row : PairedEntryRow) (slot : ProfiledRawRightSlot A)
    (htarget : targetState ((play n).2.1.target row) =
      .inr (.inl slot))
    (word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (start : Nat) (cuts : Nat → Nat) (k : Nat)
    (hcut : cuts k < cuts (k + 1))
    (hstate : A.run word (start + cuts k) =
      pairedCodeStateForRow A row source.1.1)
    (hlength :
      (profiledRawJointTargetLeftPhysicalPrefixRecords A row
          (omegaPrefix play n)).length =
        cuts (k + 1) - cuts k - 1)
    (hslice : omegaPrefix (OmegaWord.drop word (start + cuts k))
        (profiledRawJointTargetLeftPhysicalPrefixRecords A row
          (omegaPrefix play n)).length =
      profiledRawJointTargetLeftPhysicalPrefixRecords A row
        (omegaPrefix play n))
    (hclosing : OmegaWord.drop word (start + cuts k)
        (profiledRawJointTargetLeftPhysicalPrefixRecords A row
          (omegaPrefix play n)).length =
      pairedLeftRecordForRow row
        (profiledRawJointTargetLeftPhysicalLetter A (play n))) :
    A.run word (start + cuts (k + 1)) =
      pairedCodeStateForRow A .first slot.1.1 := by
  let monitor := profiledRawJointTargetLeftBlockMonitor A Target targetState
    Allowed source
  let letters := (omegaPrefix play n).map
    (profiledRawJointTargetLeftPhysicalLetter A)
  let block := profiledRawJointTargetLeftPhysicalPrefixRecords A row
    (omegaPrefix play n)
  let closing := pairedLeftRecordForRow row
    (profiledRawJointTargetLeftPhysicalLetter A (play n))
  have hpacket :=
    profiledRawJointTargetLeft_freshState_and_blockPriority_of_wins A
      targetState Allowed source play hwin n row slot htarget
  have hscan := profiledRawJointTargetLeftBlockMonitor_run_scan_eq_physicalFold
    A targetState Allowed source play n
  have hfold := congrArg Prod.fst
    (pairedLeftScanFold_pairForRow_eq_blockEndAndMin A row source.1.1
      letters)
  have hend :
      (pairedLeftScanPairForRow A row (monitor.run play n).2.1).1 =
        block.foldl A.step (pairedCodeStateForRow A row source.1.1) := by
    rw [hscan]
    rw [blockEndAndMin_fst_eq_foldl A] at hfold
    simpa [letters, block,
      profiledRawJointTargetLeftPhysicalPrefixRecords, List.map_map,
      Function.comp_apply] using hfold
  have htargetState :
      pairedCodeStateForRow A .first slot.1.1 =
        A.step
          (block.foldl A.step
            (pairedCodeStateForRow A row source.1.1)) closing := by
    calc
      pairedCodeStateForRow A .first slot.1.1 =
          (pairedLeftScanPairForRow A row
            (pairedLeftScanStep A (monitor.run play n).2.1
              (profiledRawJointTargetLeftPhysicalLetter A (play n)))).1 :=
        hpacket.1
      _ = A.step
            (pairedLeftScanPairForRow A row
              (monitor.run play n).2.1).1 closing := by
          cases row <;> rfl
      _ = A.step
            (block.foldl A.step
              (pairedCodeStateForRow A row source.1.1)) closing := by
          rw [hend]
  exact run_at_nextCut_eq_of_slice_and_closing A word start cuts k
    (pairedCodeStateForRow A row source.1.1) block closing
    (pairedCodeStateForRow A .first slot.1.1) hcut hstate
    (by simpa [block] using hlength) (by simpa [block] using hslice)
    (by simpa [block, closing] using hclosing) htargetState

/-! ## State-relative fresh target state -/

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype Out₂] in
/-- State-relative right next-cut propagation.  Together with
`profiledRawJointTargetRight_cutBlockMinFrom_eq_threadRootPriority_of_wins`,
this is the complete cut packet: the emitted target records both the literal
minimum of the block just closed and the actual entry state of the next
block. -/
theorem
    profiledRawJointTargetRight_runFrom_at_nextCut_eq_freshState_of_wins
    {Target : Type t} [Fintype Target]
    (targetState : Target → PairedProfiledTreeState A)
    (Allowed : Target → Prop)
    (source : ProfiledRawRightSlot A)
    (play : Nat → RealizedBlockRound In₂ In₁
      (ProfiledRawJointTargetRightReceiverOutput
        (Out₁ := Out₁) (Out₂ := Out₂) Target) Out₁)
    (hwin : (profiledRawJointTargetRightBlockMonitor A Target targetState
      Allowed source).WinsPlay play)
    (n : Nat) (row : PairedEntryRow) (slot : ProfiledRawLeftSlot A)
    (htarget : targetState ((play n).2.1.target row) =
      .inr (.inr slot))
    (physicalState : A.State)
    (word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (cuts : Nat → Nat) (k : Nat)
    (hcut : cuts k < cuts (k + 1))
    (hstate : A.runFrom physicalState word (cuts k) =
      pairedCodeStateForRow A row source.1.1)
    (hlength :
      (profiledRawJointTargetRightPhysicalPrefixRecords A row
          (omegaPrefix play n)).length =
        cuts (k + 1) - cuts k - 1)
    (hslice : omegaPrefix (OmegaWord.drop word (cuts k))
        (profiledRawJointTargetRightPhysicalPrefixRecords A row
          (omegaPrefix play n)).length =
      profiledRawJointTargetRightPhysicalPrefixRecords A row
        (omegaPrefix play n))
    (hclosing : OmegaWord.drop word (cuts k)
        (profiledRawJointTargetRightPhysicalPrefixRecords A row
          (omegaPrefix play n)).length =
      pairedRightRecordForRow row
        (profiledRawJointTargetRightPhysicalLetter A (play n))) :
    A.runFrom physicalState word (cuts (k + 1)) =
      pairedCodeStateForRow A .first slot.1.1 := by
  let monitor := profiledRawJointTargetRightBlockMonitor A Target targetState
    Allowed source
  let letters := (omegaPrefix play n).map
    (profiledRawJointTargetRightPhysicalLetter A)
  let block := profiledRawJointTargetRightPhysicalPrefixRecords A row
    (omegaPrefix play n)
  let closing := pairedRightRecordForRow row
    (profiledRawJointTargetRightPhysicalLetter A (play n))
  have hpacket :=
    profiledRawJointTargetRight_freshState_and_blockPriority_of_wins A
      targetState Allowed source play hwin n row slot htarget
  have hscan := profiledRawJointTargetRightBlockMonitor_run_scan_eq_physicalFold
    A targetState Allowed source play n
  have hfold := congrArg Prod.fst
    (pairedRightScanFold_pairForRow_eq_blockEndAndMin A row source.1.1
      letters)
  have hend :
      (pairedRightScanPairForRow A row (monitor.run play n).2.1).1 =
        block.foldl A.step (pairedCodeStateForRow A row source.1.1) := by
    rw [hscan]
    rw [blockEndAndMin_fst_eq_foldl A] at hfold
    simpa [letters, block,
      profiledRawJointTargetRightPhysicalPrefixRecords, List.map_map,
      Function.comp_apply] using hfold
  have htargetState :
      pairedCodeStateForRow A .first slot.1.1 =
        A.step
          (block.foldl A.step
            (pairedCodeStateForRow A row source.1.1)) closing := by
    calc
      pairedCodeStateForRow A .first slot.1.1 =
          (pairedRightScanPairForRow A row
            (pairedRightScanStep A (monitor.run play n).2.1
              (profiledRawJointTargetRightPhysicalLetter A (play n)))).1 :=
        hpacket.1
      _ = A.step
            (pairedRightScanPairForRow A row
              (monitor.run play n).2.1).1 closing := by
          cases row <;> rfl
      _ = A.step
            (block.foldl A.step
              (pairedCodeStateForRow A row source.1.1)) closing := by
          rw [hend]
  exact runFrom_at_nextCut_eq_of_slice_and_closing A physicalState word cuts k
    (pairedCodeStateForRow A row source.1.1) block closing
    (pairedCodeStateForRow A .first slot.1.1) hcut hstate
    (by simpa [block] using hlength) (by simpa [block] using hslice)
    (by simpa [block, closing] using hclosing) htargetState

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype Out₁] in
/-- State-relative left next-cut mirror. -/
theorem
    profiledRawJointTargetLeft_runFrom_at_nextCut_eq_freshState_of_wins
    {Target : Type t} [Fintype Target]
    (targetState : Target → PairedProfiledTreeState A)
    (Allowed : Target → Prop)
    (source : ProfiledRawLeftSlot A)
    (play : Nat → RealizedBlockRound In₁ In₂
      (ProfiledRawJointTargetLeftReceiverOutput
        (Out₁ := Out₁) (Out₂ := Out₂) Target) Out₂)
    (hwin : (profiledRawJointTargetLeftBlockMonitor A Target targetState
      Allowed source).WinsPlay play)
    (n : Nat) (row : PairedEntryRow) (slot : ProfiledRawRightSlot A)
    (htarget : targetState ((play n).2.1.target row) =
      .inr (.inl slot))
    (physicalState : A.State)
    (word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (cuts : Nat → Nat) (k : Nat)
    (hcut : cuts k < cuts (k + 1))
    (hstate : A.runFrom physicalState word (cuts k) =
      pairedCodeStateForRow A row source.1.1)
    (hlength :
      (profiledRawJointTargetLeftPhysicalPrefixRecords A row
          (omegaPrefix play n)).length =
        cuts (k + 1) - cuts k - 1)
    (hslice : omegaPrefix (OmegaWord.drop word (cuts k))
        (profiledRawJointTargetLeftPhysicalPrefixRecords A row
          (omegaPrefix play n)).length =
      profiledRawJointTargetLeftPhysicalPrefixRecords A row
        (omegaPrefix play n))
    (hclosing : OmegaWord.drop word (cuts k)
        (profiledRawJointTargetLeftPhysicalPrefixRecords A row
          (omegaPrefix play n)).length =
      pairedLeftRecordForRow row
        (profiledRawJointTargetLeftPhysicalLetter A (play n))) :
    A.runFrom physicalState word (cuts (k + 1)) =
      pairedCodeStateForRow A .first slot.1.1 := by
  let monitor := profiledRawJointTargetLeftBlockMonitor A Target targetState
    Allowed source
  let letters := (omegaPrefix play n).map
    (profiledRawJointTargetLeftPhysicalLetter A)
  let block := profiledRawJointTargetLeftPhysicalPrefixRecords A row
    (omegaPrefix play n)
  let closing := pairedLeftRecordForRow row
    (profiledRawJointTargetLeftPhysicalLetter A (play n))
  have hpacket :=
    profiledRawJointTargetLeft_freshState_and_blockPriority_of_wins A
      targetState Allowed source play hwin n row slot htarget
  have hscan := profiledRawJointTargetLeftBlockMonitor_run_scan_eq_physicalFold
    A targetState Allowed source play n
  have hfold := congrArg Prod.fst
    (pairedLeftScanFold_pairForRow_eq_blockEndAndMin A row source.1.1
      letters)
  have hend :
      (pairedLeftScanPairForRow A row (monitor.run play n).2.1).1 =
        block.foldl A.step (pairedCodeStateForRow A row source.1.1) := by
    rw [hscan]
    rw [blockEndAndMin_fst_eq_foldl A] at hfold
    simpa [letters, block,
      profiledRawJointTargetLeftPhysicalPrefixRecords, List.map_map,
      Function.comp_apply] using hfold
  have htargetState :
      pairedCodeStateForRow A .first slot.1.1 =
        A.step
          (block.foldl A.step
            (pairedCodeStateForRow A row source.1.1)) closing := by
    calc
      pairedCodeStateForRow A .first slot.1.1 =
          (pairedLeftScanPairForRow A row
            (pairedLeftScanStep A (monitor.run play n).2.1
              (profiledRawJointTargetLeftPhysicalLetter A (play n)))).1 :=
        hpacket.1
      _ = A.step
            (pairedLeftScanPairForRow A row
              (monitor.run play n).2.1).1 closing := by
          cases row <;> rfl
      _ = A.step
            (block.foldl A.step
              (pairedCodeStateForRow A row source.1.1)) closing := by
          rw [hend]
  exact runFrom_at_nextCut_eq_of_slice_and_closing A physicalState word cuts k
    (pairedCodeStateForRow A row source.1.1) block closing
    (pairedCodeStateForRow A .first slot.1.1) hcut hstate
    (by simpa [block] using hlength) (by simpa [block] using hslice)
    (by simpa [block, closing] using hclosing) htargetState

/-! ## State-relative simultaneous-close cut packet -/

/-- Proof-side interpretation of the acknowledged carrier's candidate bit at
a physical close.  `false` is the open/strict candidate and `true` is the
closed/simultaneous candidate.  This is not an executable graph test: the
carrier advances both candidates until a later locally delivered
acknowledgement resolves the bit. -/
def profiledRawJointCloseRowOfMember (member : Bool) : PairedEntryRow :=
  if member then .both else .first

@[simp] theorem profiledRawJointCloseRowOfMember_false :
    profiledRawJointCloseRowOfMember false = .first :=
  rfl

@[simp] theorem profiledRawJointCloseRowOfMember_true :
    profiledRawJointCloseRowOfMember true = .both :=
  rfl

/-- The literal right closing record represented by one delayed-carrier
candidate. -/
def profiledRawJointTargetRightClosingRecordForMember
    (member : Bool) (row : PairedEntryRow)
    (letter : PairedRightBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)) :
    RoundRecord In₁ In₂ Graph Out₁ Out₂ :=
  if member then
    bothRoundRecord (letter.1.2, letter.1.1)
      (pairedRightClosingForRow row letter.2.1)
      (pairedRightInformedForRow row letter.2.1)
  else
    pairedRightRecordForRow row letter

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
@[simp] theorem profiledRawJointTargetRightClosingRecordForMember_false
    (row : PairedEntryRow)
    (letter : PairedRightBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)) :
    profiledRawJointTargetRightClosingRecordForMember false row letter =
      pairedRightRecordForRow row letter :=
  rfl

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
@[simp] theorem profiledRawJointTargetRightClosingRecordForMember_true
    (row : PairedEntryRow)
    (letter : PairedRightBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)) :
    profiledRawJointTargetRightClosingRecordForMember true row letter =
      bothRoundRecord (letter.1.2, letter.1.1)
        (pairedRightClosingForRow row letter.2.1)
        (pairedRightInformedForRow row letter.2.1) :=
  rfl

/-- Left closing-record mirror. -/
def profiledRawJointTargetLeftClosingRecordForMember
    (member : Bool) (row : PairedEntryRow)
    (letter : PairedLeftBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)) :
    RoundRecord In₁ In₂ Graph Out₁ Out₂ :=
  if member then
    bothRoundRecord letter.1
      (pairedLeftInformedForRow row letter.2.1)
      (pairedLeftClosingForRow row letter.2.1)
  else
    pairedLeftRecordForRow row letter

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
@[simp] theorem profiledRawJointTargetLeftClosingRecordForMember_false
    (row : PairedEntryRow)
    (letter : PairedLeftBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)) :
    profiledRawJointTargetLeftClosingRecordForMember false row letter =
      pairedLeftRecordForRow row letter :=
  rfl

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
@[simp] theorem profiledRawJointTargetLeftClosingRecordForMember_true
    (row : PairedEntryRow)
    (letter : PairedLeftBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)) :
    profiledRawJointTargetLeftClosingRecordForMember true row letter =
      bothRoundRecord letter.1
        (pairedLeftInformedForRow row letter.2.1)
        (pairedLeftClosingForRow row letter.2.1) :=
  rfl

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype Out₂] in
/-- State propagation for a right table whose physical closing graph is
simultaneous.  The old row selects the scan of the block just completed, but
the actual DPA successor is the emitted target's `.both` coordinate.

This theorem is deliberately local to one cut.  It does not identify the
row stored by any old Unit receiver with `.both`; a recurrent construction
must instead install its next fresh receiver (and its entry row) explicitly.
-/
theorem
    profiledRawJointTargetRight_runFrom_at_nextCut_eq_bothState_of_wins
    {Target : Type t} [Fintype Target]
    (targetState : Target → PairedProfiledTreeState A)
    (Allowed : Target → Prop)
    (source : ProfiledRawRightSlot A)
    (play : Nat → RealizedBlockRound In₂ In₁
      (ProfiledRawJointTargetRightReceiverOutput
        (Out₁ := Out₁) (Out₂ := Out₂) Target) Out₁)
    (hwin : (profiledRawJointTargetRightBlockMonitor A Target targetState
      Allowed source).WinsPlay play)
    (n : Nat) (row : PairedEntryRow) (slot : ProfiledRawLeftSlot A)
    (htarget : targetState ((play n).2.1.target row) =
      .inr (.inr slot))
    (physicalState : A.State)
    (word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (cuts : Nat → Nat) (k : Nat)
    (hcut : cuts k < cuts (k + 1))
    (hstate : A.runFrom physicalState word (cuts k) =
      pairedCodeStateForRow A row source.1.1)
    (hlength :
      (profiledRawJointTargetRightPhysicalPrefixRecords A row
          (omegaPrefix play n)).length =
        cuts (k + 1) - cuts k - 1)
    (hslice : omegaPrefix (OmegaWord.drop word (cuts k))
        (profiledRawJointTargetRightPhysicalPrefixRecords A row
          (omegaPrefix play n)).length =
      profiledRawJointTargetRightPhysicalPrefixRecords A row
        (omegaPrefix play n))
    (hclosing : OmegaWord.drop word (cuts k)
        (profiledRawJointTargetRightPhysicalPrefixRecords A row
          (omegaPrefix play n)).length =
      bothRoundRecord
        ((profiledRawJointTargetRightPhysicalLetter A (play n)).1.2,
          (profiledRawJointTargetRightPhysicalLetter A (play n)).1.1)
        (pairedRightClosingForRow row
          (profiledRawJointTargetRightPhysicalLetter A (play n)).2.1)
        (pairedRightInformedForRow row
          (profiledRawJointTargetRightPhysicalLetter A (play n)).2.1)) :
    A.runFrom physicalState word (cuts (k + 1)) =
      pairedCodeStateForRow A .both slot.1.1 := by
  let monitor := profiledRawJointTargetRightBlockMonitor A Target targetState
    Allowed source
  let letters := (omegaPrefix play n).map
    (profiledRawJointTargetRightPhysicalLetter A)
  let block := profiledRawJointTargetRightPhysicalPrefixRecords A row
    (omegaPrefix play n)
  let closing :=
    bothRoundRecord
      ((profiledRawJointTargetRightPhysicalLetter A (play n)).1.2,
        (profiledRawJointTargetRightPhysicalLetter A (play n)).1.1)
      (pairedRightClosingForRow row
        (profiledRawJointTargetRightPhysicalLetter A (play n)).2.1)
      (pairedRightInformedForRow row
        (profiledRawJointTargetRightPhysicalLetter A (play n)).2.1)
  have hpacket :=
    profiledRawJointTargetRight_bothState_and_blockPriority_of_wins A
      targetState Allowed source play hwin n row slot htarget
  have hscan := profiledRawJointTargetRightBlockMonitor_run_scan_eq_physicalFold
    A targetState Allowed source play n
  have hfold := congrArg Prod.fst
    (pairedRightScanFold_pairForRow_eq_blockEndAndMin A row source.1.1
      letters)
  have hend :
      (pairedRightScanPairForRow A row (monitor.run play n).2.1).1 =
        block.foldl A.step (pairedCodeStateForRow A row source.1.1) := by
    rw [hscan]
    rw [blockEndAndMin_fst_eq_foldl A] at hfold
    simpa [letters, block,
      profiledRawJointTargetRightPhysicalPrefixRecords, List.map_map,
      Function.comp_apply] using hfold
  have htargetState :
      pairedCodeStateForRow A .both slot.1.1 =
        A.step
          (block.foldl A.step
            (pairedCodeStateForRow A row source.1.1)) closing := by
    calc
      pairedCodeStateForRow A .both slot.1.1 =
          A.step
            (pairedRightScanPairForRow A row
              (monitor.run play n).2.1).1 closing := by
        simpa [closing, monitor] using hpacket.1
      _ = A.step
            (block.foldl A.step
              (pairedCodeStateForRow A row source.1.1)) closing := by
        rw [hend]
  exact runFrom_at_nextCut_eq_of_slice_and_closing A physicalState word cuts k
    (pairedCodeStateForRow A row source.1.1) block closing
    (pairedCodeStateForRow A .both slot.1.1) hcut hstate
    (by simpa [block] using hlength) (by simpa [block] using hslice)
    (by simpa [block, closing] using hclosing) htargetState

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype Out₁] in
/-- Left-table mirror of simultaneous state propagation. -/
theorem
    profiledRawJointTargetLeft_runFrom_at_nextCut_eq_bothState_of_wins
    {Target : Type t} [Fintype Target]
    (targetState : Target → PairedProfiledTreeState A)
    (Allowed : Target → Prop)
    (source : ProfiledRawLeftSlot A)
    (play : Nat → RealizedBlockRound In₁ In₂
      (ProfiledRawJointTargetLeftReceiverOutput
        (Out₁ := Out₁) (Out₂ := Out₂) Target) Out₂)
    (hwin : (profiledRawJointTargetLeftBlockMonitor A Target targetState
      Allowed source).WinsPlay play)
    (n : Nat) (row : PairedEntryRow) (slot : ProfiledRawRightSlot A)
    (htarget : targetState ((play n).2.1.target row) =
      .inr (.inl slot))
    (physicalState : A.State)
    (word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (cuts : Nat → Nat) (k : Nat)
    (hcut : cuts k < cuts (k + 1))
    (hstate : A.runFrom physicalState word (cuts k) =
      pairedCodeStateForRow A row source.1.1)
    (hlength :
      (profiledRawJointTargetLeftPhysicalPrefixRecords A row
          (omegaPrefix play n)).length =
        cuts (k + 1) - cuts k - 1)
    (hslice : omegaPrefix (OmegaWord.drop word (cuts k))
        (profiledRawJointTargetLeftPhysicalPrefixRecords A row
          (omegaPrefix play n)).length =
      profiledRawJointTargetLeftPhysicalPrefixRecords A row
        (omegaPrefix play n))
    (hclosing : OmegaWord.drop word (cuts k)
        (profiledRawJointTargetLeftPhysicalPrefixRecords A row
          (omegaPrefix play n)).length =
      bothRoundRecord
        (profiledRawJointTargetLeftPhysicalLetter A (play n)).1
        (pairedLeftInformedForRow row
          (profiledRawJointTargetLeftPhysicalLetter A (play n)).2.1)
        (pairedLeftClosingForRow row
          (profiledRawJointTargetLeftPhysicalLetter A (play n)).2.1)) :
    A.runFrom physicalState word (cuts (k + 1)) =
      pairedCodeStateForRow A .both slot.1.1 := by
  let monitor := profiledRawJointTargetLeftBlockMonitor A Target targetState
    Allowed source
  let letters := (omegaPrefix play n).map
    (profiledRawJointTargetLeftPhysicalLetter A)
  let block := profiledRawJointTargetLeftPhysicalPrefixRecords A row
    (omegaPrefix play n)
  let closing :=
    bothRoundRecord
      (profiledRawJointTargetLeftPhysicalLetter A (play n)).1
      (pairedLeftInformedForRow row
        (profiledRawJointTargetLeftPhysicalLetter A (play n)).2.1)
      (pairedLeftClosingForRow row
        (profiledRawJointTargetLeftPhysicalLetter A (play n)).2.1)
  have hpacket :=
    profiledRawJointTargetLeft_bothState_and_blockPriority_of_wins A
      targetState Allowed source play hwin n row slot htarget
  have hscan := profiledRawJointTargetLeftBlockMonitor_run_scan_eq_physicalFold
    A targetState Allowed source play n
  have hfold := congrArg Prod.fst
    (pairedLeftScanFold_pairForRow_eq_blockEndAndMin A row source.1.1
      letters)
  have hend :
      (pairedLeftScanPairForRow A row (monitor.run play n).2.1).1 =
        block.foldl A.step (pairedCodeStateForRow A row source.1.1) := by
    rw [hscan]
    rw [blockEndAndMin_fst_eq_foldl A] at hfold
    simpa [letters, block,
      profiledRawJointTargetLeftPhysicalPrefixRecords, List.map_map,
      Function.comp_apply] using hfold
  have htargetState :
      pairedCodeStateForRow A .both slot.1.1 =
        A.step
          (block.foldl A.step
            (pairedCodeStateForRow A row source.1.1)) closing := by
    calc
      pairedCodeStateForRow A .both slot.1.1 =
          A.step
            (pairedLeftScanPairForRow A row
              (monitor.run play n).2.1).1 closing := by
        simpa [closing, monitor] using hpacket.1
      _ = A.step
            (block.foldl A.step
              (pairedCodeStateForRow A row source.1.1)) closing := by
        rw [hend]
  exact runFrom_at_nextCut_eq_of_slice_and_closing A physicalState word cuts k
    (pairedCodeStateForRow A row source.1.1) block closing
    (pairedCodeStateForRow A .both slot.1.1) hcut hstate
    (by simpa [block] using hlength) (by simpa [block] using hslice)
    (by simpa [block, closing] using hclosing) htargetState

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype Out₂] in
/-- The complete proof-side two-candidate cut packet for a right table.

The delayed-carrier witness `member = false` selects the ordinary strict
closing record and the target's fresh `.first` coordinate.  The witness
`member = true` selects the simultaneous closing record and the target's
`.both` coordinate.  In both cases the emitted root stores the same literal
minimum of the preceding physical block.  The executable close need not and
does not distinguish these cases. -/
theorem profiledRawJointTargetRight_memberCutPacket_of_wins
    {Target : Type t} [Fintype Target]
    (targetState : Target → PairedProfiledTreeState A)
    (Allowed : Target → Prop)
    (source : ProfiledRawRightSlot A)
    (play : Nat → RealizedBlockRound In₂ In₁
      (ProfiledRawJointTargetRightReceiverOutput
        (Out₁ := Out₁) (Out₂ := Out₂) Target) Out₁)
    (hwin : (profiledRawJointTargetRightBlockMonitor A Target targetState
      Allowed source).WinsPlay play)
    (n : Nat) (row : PairedEntryRow) (slot : ProfiledRawLeftSlot A)
    (htarget : targetState ((play n).2.1.target row) = .inr (.inr slot))
    (member : Bool) (physicalState : A.State)
    (word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (cuts : Nat → Nat) (k : Nat)
    (hcut : cuts k < cuts (k + 1))
    (hstate : A.runFrom physicalState word (cuts k) =
      pairedCodeStateForRow A row source.1.1)
    (hlength :
      (profiledRawJointTargetRightPhysicalPrefixRecords A row
          (omegaPrefix play n)).length = cuts (k + 1) - cuts k - 1)
    (hslice : omegaPrefix (OmegaWord.drop word (cuts k))
        (profiledRawJointTargetRightPhysicalPrefixRecords A row
          (omegaPrefix play n)).length =
      profiledRawJointTargetRightPhysicalPrefixRecords A row
        (omegaPrefix play n))
    (hclosing : OmegaWord.drop word (cuts k)
        (profiledRawJointTargetRightPhysicalPrefixRecords A row
          (omegaPrefix play n)).length =
      profiledRawJointTargetRightClosingRecordForMember member row
        (profiledRawJointTargetRightPhysicalLetter A (play n))) :
    cutBlockMin
        (fun j ↦ A.priority (A.runFrom physicalState word j)) cuts k =
        profiledRawJointThreadRootPriority A (.inr slot) ∧
      A.runFrom physicalState word (cuts (k + 1)) =
        pairedCodeStateForRow A (profiledRawJointCloseRowOfMember member)
          slot.1.1 := by
  constructor
  · exact
      profiledRawJointTargetRight_cutBlockMinFrom_eq_threadRootPriority_of_wins
        A targetState Allowed source play hwin n row slot htarget
          physicalState word cuts k hstate hlength hslice
  · cases member with
    | false =>
        apply
          profiledRawJointTargetRight_runFrom_at_nextCut_eq_freshState_of_wins
            A targetState Allowed source play hwin n row slot htarget
              physicalState word cuts k hcut hstate hlength hslice
        simpa using hclosing
    | true =>
        apply
          profiledRawJointTargetRight_runFrom_at_nextCut_eq_bothState_of_wins
            A targetState Allowed source play hwin n row slot htarget
              physicalState word cuts k hcut hstate hlength hslice
        simpa using hclosing

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype Out₁] in
/-- Left-table mirror of the complete proof-side two-candidate cut packet. -/
theorem profiledRawJointTargetLeft_memberCutPacket_of_wins
    {Target : Type t} [Fintype Target]
    (targetState : Target → PairedProfiledTreeState A)
    (Allowed : Target → Prop)
    (source : ProfiledRawLeftSlot A)
    (play : Nat → RealizedBlockRound In₁ In₂
      (ProfiledRawJointTargetLeftReceiverOutput
        (Out₁ := Out₁) (Out₂ := Out₂) Target) Out₂)
    (hwin : (profiledRawJointTargetLeftBlockMonitor A Target targetState
      Allowed source).WinsPlay play)
    (n : Nat) (row : PairedEntryRow) (slot : ProfiledRawRightSlot A)
    (htarget : targetState ((play n).2.1.target row) = .inr (.inl slot))
    (member : Bool) (physicalState : A.State)
    (word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (cuts : Nat → Nat) (k : Nat)
    (hcut : cuts k < cuts (k + 1))
    (hstate : A.runFrom physicalState word (cuts k) =
      pairedCodeStateForRow A row source.1.1)
    (hlength :
      (profiledRawJointTargetLeftPhysicalPrefixRecords A row
          (omegaPrefix play n)).length = cuts (k + 1) - cuts k - 1)
    (hslice : omegaPrefix (OmegaWord.drop word (cuts k))
        (profiledRawJointTargetLeftPhysicalPrefixRecords A row
          (omegaPrefix play n)).length =
      profiledRawJointTargetLeftPhysicalPrefixRecords A row
        (omegaPrefix play n))
    (hclosing : OmegaWord.drop word (cuts k)
        (profiledRawJointTargetLeftPhysicalPrefixRecords A row
          (omegaPrefix play n)).length =
      profiledRawJointTargetLeftClosingRecordForMember member row
        (profiledRawJointTargetLeftPhysicalLetter A (play n))) :
    cutBlockMin
        (fun j ↦ A.priority (A.runFrom physicalState word j)) cuts k =
        profiledRawJointThreadRootPriority A (.inl slot) ∧
      A.runFrom physicalState word (cuts (k + 1)) =
        pairedCodeStateForRow A (profiledRawJointCloseRowOfMember member)
          slot.1.1 := by
  constructor
  · exact
      profiledRawJointTargetLeft_cutBlockMinFrom_eq_threadRootPriority_of_wins
        A targetState Allowed source play hwin n row slot htarget
          physicalState word cuts k hstate hlength hslice
  · cases member with
    | false =>
        apply
          profiledRawJointTargetLeft_runFrom_at_nextCut_eq_freshState_of_wins
            A targetState Allowed source play hwin n row slot htarget
              physicalState word cuts k hcut hstate hlength hslice
        simpa using hclosing
    | true =>
        apply
          profiledRawJointTargetLeft_runFrom_at_nextCut_eq_bothState_of_wins
            A targetState Allowed source play hwin n row slot htarget
              physicalState word cuts k hcut hstate hlength hslice
        simpa using hclosing

section
omit [Inhabited Out₁] [Inhabited Out₂]

/-- A completed matched-left state selected by a nonempty strict-right block
ends in a completed matched-right state.  Its receiver stores exactly the
query target and retains the same latent row.  This is the missing
cut-to-cut *state* equation; the earlier trace theorem only identified the
emitted Moore word. -/
theorem profiledRawJointUnitMatchedLeft_right_close_endpoint
    {InitialOne InitialTwo ExceptionalOne ExceptionalTwo : Type*}
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (source : ProfiledRawJointUnitRightPolicyMacro A strategy
      (initial.code A) policy)
    (row : PairedEntryRow) (past : List (In₂ × In₁))
    (move : In₂ × In₁)
    (left : ProfiledRawJointUnitLeftPolicyReceiverControl A strategy initial
      policy)
    (owner : ProfiledRawJointUnitLeftPolicyOwnerControl A strategy initial
      policy bank)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (htarget : profiledRawJointUnitPolicyLeftReceiverTarget A strategy initial
      policy bank left = source)
    (hrow : left.2.1 = row) :
    let query : ProfiledRawJointUnitPolicyCloseQuery A strategy initial policy
        (.inl source) := .right source row past move
    let blockInputs : Nat → In₂ × In₁ := omegaOfList (past ++ [move])
    ∃ nextOwner : ProfiledRawJointUnitRightPolicyOwnerControl A strategy
          initial policy bank,
      ∃ nextReceiver : ProfiledRawJointUnitRightPolicyReceiverControl A
          strategy initial policy,
      ∃ outputOne outputTwo,
        ((UnitKernel A strategy initial policy bank adapter).globalMachine.reroot
          (profiledRawJointUnitMatchedLeftState A strategy initial policy bank
            adapter left owner oldOutputOne oldOutputTwo)).globalStateTrace
              (profiledRawJointUnitStrictRightEnvironment blockInputs)
              (past.length + 1) =
            profiledRawJointUnitMatchedRightState A strategy initial policy
              bank adapter nextOwner nextReceiver outputOne outputTwo ∧
        (.inr (profiledRawJointUnitPolicyRightReceiverTarget A strategy initial
            policy bank nextReceiver) :
          ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
            policy) = query.target A strategy initial policy bank ∧
        nextReceiver.2.1 = row := by
  dsimp only
  let blockInputs : Nat → In₂ × In₁ := omegaOfList (past ++ [move])
  let fresh := profiledRawJointUnitFreshMatchedRightState A strategy initial
    policy bank adapter source row oldOutputOne oldOutputTwo
  have hfirst :
      (UnitKernel A strategy initial policy bank adapter).globalMachine.step
          (profiledRawJointUnitMatchedLeftState A strategy initial policy bank
            adapter left owner oldOutputOne oldOutputTwo)
          (profiledRawJointUnitStrictRightEnvironment blockInputs 0) =
        (UnitKernel A strategy initial policy bank adapter).globalMachine.step
          fresh (profiledRawJointUnitStrictRightEnvironment blockInputs 0) := by
    simpa [fresh, htarget, hrow,
      profiledRawJointUnitStrictRightEnvironment] using
      (profiledRawJointUnitMatchedLeft_right_step_eq_freshMatchedRight A
        strategy initial policy bank adapter left owner oldOutputOne
          oldOutputTwo (blockInputs 0).2 (blockInputs 0).1)
  have hstates :=
    (UnitKernel A strategy initial policy bank adapter).globalMachine
      |>.reroot_globalStateTrace_eq_of_first_step_eq
        (profiledRawJointUnitStrictRightEnvironment blockInputs)
        (profiledRawJointUnitMatchedLeftState A strategy initial policy bank
          adapter left owner oldOutputOne oldOutputTwo)
        fresh hfirst (past.length + 1) (by omega)
  obtain ⟨outputOne, outputTwo, hfresh⟩ :=
    profiledRawJointUnitFreshMatchedRight_controls A strategy initial policy
      bank adapter source row oldOutputOne oldOutputTwo blockInputs
        (past.length + 1)
  let nextOwner : ProfiledRawJointUnitRightPolicyOwnerControl A strategy
      initial policy bank :=
    ⟨source,
      (profiledRawJointUnitRightPolicyFiniteStateAfter A strategy initial
        policy bank source (omegaPrefix blockInputs (past.length + 1))).1⟩
  let nextReceiver : ProfiledRawJointUnitRightPolicyReceiverControl A strategy
      initial policy :=
    ⟨source, row,
      (profiledRawJointUnitRightPolicyFiniteStateAfter A strategy initial
        policy bank source (omegaPrefix blockInputs (past.length + 1))).2,
      profiledRawJointUnitRightStagedAfter A strategy initial policy bank
        source row blockInputs (past.length + 1)⟩
  refine ⟨nextOwner, nextReceiver, outputOne, outputTwo, ?_, ?_, rfl⟩
  · exact hstates.trans (by simpa [fresh, nextOwner, nextReceiver] using hfresh)
  · have hpast : omegaPrefix blockInputs past.length = past := by
      apply List.ext_get
      · simp [omegaPrefix]
      · intro n hnLeft hnRight
        rw [List.get_eq_getElem, List.get_eq_getElem]
        simp only [omegaPrefix, List.getElem_ofFn]
        have hnPrefix : n < (past ++ [move]).length := by simp; omega
        change omegaOfList (past ++ [move]) n = past[n]
        rw [omegaOfList_eq_getElem (past ++ [move]) n hnPrefix]
        simp [hnRight]
    have hmove : blockInputs past.length = move := by
      have hnPrefix : past.length < (past ++ [move]).length := by simp
      change omegaOfList (past ++ [move]) past.length = move
      rw [omegaOfList_eq_getElem (past ++ [move]) past.length hnPrefix]
      simp
    let target := Classical.choose
      (exists_profiledRawJointUnitLeft_step_priority_of_realRightClose A
        strategy initial policy bank source row past move)
    have hstage :
        (stepProfiledRawJointUnitRightPolicyReceiverFor A strategy initial
          policy bank source
            (profiledRawJointUnitRightPolicyFiniteStateAfter A strategy initial
              policy bank source past).1 row
            (profiledRawJointUnitRightPolicyFiniteStateAfter A strategy initial
              policy bank source past).2 move).2.2 = some target :=
      (Classical.choose_spec
        (exists_profiledRawJointUnitLeft_step_priority_of_realRightClose A
          strategy initial policy bank source row past move)).1
    have hqueryTarget :
        (ProfiledRawJointUnitPolicyCloseQuery.right source row past move
          ).target A strategy initial policy bank = Sum.inr target := by
      rfl
    change Sum.inr
      ((profiledRawJointUnitRightStagedAfter A strategy initial policy bank
        source row blockInputs (past.length + 1)).getD _) = _
    simp only [profiledRawJointUnitRightStagedAfter]
    rw [hpast, hmove]
    rw [hqueryTarget]
    congr 1
    rw [hstage]
    rfl

/-- Receiver/receiver-cross variant of the same right-close endpoint.  The
unused right receiver has no influence on a strict-right transition, so the
first step agrees with the completed matched-left presentation above. -/
theorem profiledRawJointUnitCross_right_close_endpoint
    {InitialOne InitialTwo ExceptionalOne ExceptionalTwo : Type*}
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (source : ProfiledRawJointUnitRightPolicyMacro A strategy
      (initial.code A) policy)
    (row : PairedEntryRow) (past : List (In₂ × In₁))
    (move : In₂ × In₁)
    (left : ProfiledRawJointUnitLeftPolicyReceiverControl A strategy initial
      policy)
    (right : ProfiledRawJointUnitRightPolicyReceiverControl A strategy initial
      policy)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (htarget : profiledRawJointUnitPolicyLeftReceiverTarget A strategy initial
      policy bank left = source)
    (hrow : left.2.1 = row) :
    let query : ProfiledRawJointUnitPolicyCloseQuery A strategy initial policy
        (.inl source) := .right source row past move
    let blockInputs : Nat → In₂ × In₁ := omegaOfList (past ++ [move])
    ∃ nextOwner : ProfiledRawJointUnitRightPolicyOwnerControl A strategy
          initial policy bank,
      ∃ nextReceiver : ProfiledRawJointUnitRightPolicyReceiverControl A
          strategy initial policy,
      ∃ outputOne outputTwo,
        ((UnitKernel A strategy initial policy bank adapter).globalMachine.reroot
          (profiledRawJointUnitCrossState A strategy initial policy bank
            adapter left right oldOutputOne oldOutputTwo)).globalStateTrace
              (profiledRawJointUnitStrictRightEnvironment blockInputs)
              (past.length + 1) =
            profiledRawJointUnitMatchedRightState A strategy initial policy
              bank adapter nextOwner nextReceiver outputOne outputTwo ∧
        (Sum.inr
            (profiledRawJointUnitPolicyRightReceiverTarget A strategy initial
              policy bank nextReceiver) :
          ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
            policy) = query.target A strategy initial policy bank ∧
        nextReceiver.2.1 = row := by
  dsimp only
  let blockInputs : Nat → In₂ × In₁ := omegaOfList (past ++ [move])
  let dummyOwner :=
    initialProfiledRawJointUnitLeftPolicyOwner A strategy initial policy bank
      left.1
  obtain ⟨nextOwner, nextReceiver, outputOne, outputTwo, hmatched, htargetNext,
      hrowNext⟩ :=
    profiledRawJointUnitMatchedLeft_right_close_endpoint A strategy initial
      policy bank adapter source row past move left dummyOwner oldOutputOne
        oldOutputTwo htarget hrow
  have hfirst :
      (UnitKernel A strategy initial policy bank adapter).globalMachine.step
          (profiledRawJointUnitCrossState A strategy initial policy bank
            adapter left right oldOutputOne oldOutputTwo)
          (profiledRawJointUnitStrictRightEnvironment blockInputs 0) =
        (UnitKernel A strategy initial policy bank adapter).globalMachine.step
          (profiledRawJointUnitMatchedLeftState A strategy initial policy bank
            adapter left dummyOwner oldOutputOne oldOutputTwo)
          (profiledRawJointUnitStrictRightEnvironment blockInputs 0) := by
    exact
      (profiledRawJointUnitCross_right_step_eq_freshMatchedRight A strategy
        initial policy bank adapter left right oldOutputOne oldOutputTwo
          (blockInputs 0).2 (blockInputs 0).1).trans
      (profiledRawJointUnitMatchedLeft_right_step_eq_freshMatchedRight A
        strategy initial policy bank adapter left dummyOwner oldOutputOne
          oldOutputTwo (blockInputs 0).2 (blockInputs 0).1).symm
  have hstates :=
    (UnitKernel A strategy initial policy bank adapter).globalMachine
      |>.reroot_globalStateTrace_eq_of_first_step_eq
        (profiledRawJointUnitStrictRightEnvironment blockInputs)
        (profiledRawJointUnitCrossState A strategy initial policy bank adapter
          left right oldOutputOne oldOutputTwo)
        (profiledRawJointUnitMatchedLeftState A strategy initial policy bank
          adapter left dummyOwner oldOutputOne oldOutputTwo)
        hfirst (past.length + 1) (by omega)
  exact ⟨nextOwner, nextReceiver, outputOne, outputTwo,
    hstates.trans hmatched, htargetNext, hrowNext⟩

/-- Strict-left mirror of
`profiledRawJointUnitMatchedLeft_right_close_endpoint`. -/
theorem profiledRawJointUnitMatchedRight_left_close_endpoint
    {InitialOne InitialTwo ExceptionalOne ExceptionalTwo : Type*}
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (source : ProfiledRawJointUnitLeftPolicyMacro A strategy
      (initial.code A) policy)
    (row : PairedEntryRow) (past : List (In₁ × In₂))
    (move : In₁ × In₂)
    (owner : ProfiledRawJointUnitRightPolicyOwnerControl A strategy initial
      policy bank)
    (right : ProfiledRawJointUnitRightPolicyReceiverControl A strategy initial
      policy)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (htarget : profiledRawJointUnitPolicyRightReceiverTarget A strategy initial
      policy bank right = source)
    (hrow : right.2.1 = row) :
    let query : ProfiledRawJointUnitPolicyCloseQuery A strategy initial policy
        (.inr source) := .left source row past move
    let blockInputs : Nat → In₁ × In₂ := omegaOfList (past ++ [move])
    ∃ nextReceiver : ProfiledRawJointUnitLeftPolicyReceiverControl A strategy
          initial policy,
      ∃ nextOwner : ProfiledRawJointUnitLeftPolicyOwnerControl A strategy
          initial policy bank,
      ∃ outputOne outputTwo,
        ((UnitKernel A strategy initial policy bank adapter).globalMachine.reroot
          (profiledRawJointUnitMatchedRightState A strategy initial policy bank
            adapter owner right oldOutputOne oldOutputTwo)).globalStateTrace
              (profiledRawJointUnitStrictLeftEnvironment blockInputs)
              (past.length + 1) =
            profiledRawJointUnitMatchedLeftState A strategy initial policy bank
              adapter nextReceiver nextOwner outputOne outputTwo ∧
        (Sum.inl
            (profiledRawJointUnitPolicyLeftReceiverTarget A strategy initial
              policy bank nextReceiver) :
          ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
            policy) = query.target A strategy initial policy bank ∧
        nextReceiver.2.1 = row := by
  dsimp only
  let blockInputs : Nat → In₁ × In₂ := omegaOfList (past ++ [move])
  let fresh := profiledRawJointUnitFreshMatchedLeftState A strategy initial
    policy bank adapter source row oldOutputOne oldOutputTwo
  have hfirst :
      (UnitKernel A strategy initial policy bank adapter).globalMachine.step
          (profiledRawJointUnitMatchedRightState A strategy initial policy bank
            adapter owner right oldOutputOne oldOutputTwo)
          (profiledRawJointUnitStrictLeftEnvironment blockInputs 0) =
        (UnitKernel A strategy initial policy bank adapter).globalMachine.step
          fresh (profiledRawJointUnitStrictLeftEnvironment blockInputs 0) := by
    simpa [fresh, htarget, hrow,
      profiledRawJointUnitStrictLeftEnvironment] using
      (profiledRawJointUnitMatchedRight_left_step_eq_freshMatchedLeft A
        strategy initial policy bank adapter owner right oldOutputOne
          oldOutputTwo (blockInputs 0).1 (blockInputs 0).2)
  have hstates :=
    (UnitKernel A strategy initial policy bank adapter).globalMachine
      |>.reroot_globalStateTrace_eq_of_first_step_eq
        (profiledRawJointUnitStrictLeftEnvironment blockInputs)
        (profiledRawJointUnitMatchedRightState A strategy initial policy bank
          adapter owner right oldOutputOne oldOutputTwo)
        fresh hfirst (past.length + 1) (by omega)
  obtain ⟨outputOne, outputTwo, hfresh⟩ :=
    profiledRawJointUnitFreshMatchedLeft_controls A strategy initial policy
      bank adapter source row oldOutputOne oldOutputTwo blockInputs
        (past.length + 1)
  let nextReceiver : ProfiledRawJointUnitLeftPolicyReceiverControl A strategy
      initial policy :=
    ⟨source, row,
      (profiledRawJointUnitLeftPolicyFiniteStateAfter A strategy initial
        policy bank source (omegaPrefix blockInputs (past.length + 1))).2,
      profiledRawJointUnitLeftStagedAfter A strategy initial policy bank
        source row blockInputs (past.length + 1)⟩
  let nextOwner : ProfiledRawJointUnitLeftPolicyOwnerControl A strategy initial
      policy bank :=
    ⟨source,
      (profiledRawJointUnitLeftPolicyFiniteStateAfter A strategy initial
        policy bank source (omegaPrefix blockInputs (past.length + 1))).1⟩
  refine ⟨nextReceiver, nextOwner, outputOne, outputTwo, ?_, ?_, rfl⟩
  · exact hstates.trans (by simpa [fresh, nextReceiver, nextOwner] using hfresh)
  · have hpast : omegaPrefix blockInputs past.length = past := by
      apply List.ext_get
      · simp [omegaPrefix]
      · intro n hnLeft hnRight
        rw [List.get_eq_getElem, List.get_eq_getElem]
        simp only [omegaPrefix, List.getElem_ofFn]
        have hnPrefix : n < (past ++ [move]).length := by simp; omega
        change omegaOfList (past ++ [move]) n = past[n]
        rw [omegaOfList_eq_getElem (past ++ [move]) n hnPrefix]
        simp [hnRight]
    have hmove : blockInputs past.length = move := by
      have hnPrefix : past.length < (past ++ [move]).length := by simp
      change omegaOfList (past ++ [move]) past.length = move
      rw [omegaOfList_eq_getElem (past ++ [move]) past.length hnPrefix]
      simp
    let target := Classical.choose
      (exists_profiledRawJointUnitRight_step_priority_of_realLeftClose A
        strategy initial policy bank source row past move)
    have hstage :
        (stepProfiledRawJointUnitLeftPolicyReceiverFor A strategy initial
          policy bank source
            (profiledRawJointUnitLeftPolicyFiniteStateAfter A strategy initial
              policy bank source past).1 row
            (profiledRawJointUnitLeftPolicyFiniteStateAfter A strategy initial
              policy bank source past).2 move).2.2 = some target :=
      (Classical.choose_spec
        (exists_profiledRawJointUnitRight_step_priority_of_realLeftClose A
          strategy initial policy bank source row past move)).1
    have hqueryTarget :
        (ProfiledRawJointUnitPolicyCloseQuery.left source row past move
          ).target A strategy initial policy bank = Sum.inl target := by
      rfl
    change Sum.inl
      ((profiledRawJointUnitLeftStagedAfter A strategy initial policy bank
        source row blockInputs (past.length + 1)).getD _) = _
    simp only [profiledRawJointUnitLeftStagedAfter]
    rw [hpast, hmove]
    rw [hqueryTarget]
    congr 1
    rw [hstage]
    rfl

/-- Receiver/receiver-cross mirror for a strict-left close. -/
theorem profiledRawJointUnitCross_left_close_endpoint
    {InitialOne InitialTwo ExceptionalOne ExceptionalTwo : Type*}
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (source : ProfiledRawJointUnitLeftPolicyMacro A strategy
      (initial.code A) policy)
    (row : PairedEntryRow) (past : List (In₁ × In₂))
    (move : In₁ × In₂)
    (left : ProfiledRawJointUnitLeftPolicyReceiverControl A strategy initial
      policy)
    (right : ProfiledRawJointUnitRightPolicyReceiverControl A strategy initial
      policy)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (htarget : profiledRawJointUnitPolicyRightReceiverTarget A strategy initial
      policy bank right = source)
    (hrow : right.2.1 = row) :
    let query : ProfiledRawJointUnitPolicyCloseQuery A strategy initial policy
        (.inr source) := .left source row past move
    let blockInputs : Nat → In₁ × In₂ := omegaOfList (past ++ [move])
    ∃ nextReceiver : ProfiledRawJointUnitLeftPolicyReceiverControl A strategy
          initial policy,
      ∃ nextOwner : ProfiledRawJointUnitLeftPolicyOwnerControl A strategy
          initial policy bank,
      ∃ outputOne outputTwo,
        ((UnitKernel A strategy initial policy bank adapter).globalMachine.reroot
          (profiledRawJointUnitCrossState A strategy initial policy bank
            adapter left right oldOutputOne oldOutputTwo)).globalStateTrace
              (profiledRawJointUnitStrictLeftEnvironment blockInputs)
              (past.length + 1) =
            profiledRawJointUnitMatchedLeftState A strategy initial policy bank
              adapter nextReceiver nextOwner outputOne outputTwo ∧
        (Sum.inl
            (profiledRawJointUnitPolicyLeftReceiverTarget A strategy initial
              policy bank nextReceiver) :
          ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
            policy) = query.target A strategy initial policy bank ∧
        nextReceiver.2.1 = row := by
  dsimp only
  let blockInputs : Nat → In₁ × In₂ := omegaOfList (past ++ [move])
  let dummyOwner :=
    initialProfiledRawJointUnitRightPolicyOwner A strategy initial policy bank
      right.1
  obtain ⟨nextReceiver, nextOwner, outputOne, outputTwo, hmatched, htargetNext,
      hrowNext⟩ :=
    profiledRawJointUnitMatchedRight_left_close_endpoint A strategy initial
      policy bank adapter source row past move dummyOwner right oldOutputOne
        oldOutputTwo htarget hrow
  have hfirst :
      (UnitKernel A strategy initial policy bank adapter).globalMachine.step
          (profiledRawJointUnitCrossState A strategy initial policy bank
            adapter left right oldOutputOne oldOutputTwo)
          (profiledRawJointUnitStrictLeftEnvironment blockInputs 0) =
        (UnitKernel A strategy initial policy bank adapter).globalMachine.step
          (profiledRawJointUnitMatchedRightState A strategy initial policy bank
            adapter dummyOwner right oldOutputOne oldOutputTwo)
          (profiledRawJointUnitStrictLeftEnvironment blockInputs 0) := by
    exact
      (profiledRawJointUnitCross_left_step_eq_freshMatchedLeft A strategy
        initial policy bank adapter left right oldOutputOne oldOutputTwo
          (blockInputs 0).1 (blockInputs 0).2).trans
      (profiledRawJointUnitMatchedRight_left_step_eq_freshMatchedLeft A
        strategy initial policy bank adapter dummyOwner right oldOutputOne
          oldOutputTwo (blockInputs 0).1 (blockInputs 0).2).symm
  have hstates :=
    (UnitKernel A strategy initial policy bank adapter).globalMachine
      |>.reroot_globalStateTrace_eq_of_first_step_eq
        (profiledRawJointUnitStrictLeftEnvironment blockInputs)
        (profiledRawJointUnitCrossState A strategy initial policy bank adapter
          left right oldOutputOne oldOutputTwo)
        (profiledRawJointUnitMatchedRightState A strategy initial policy bank
          adapter dummyOwner right oldOutputOne oldOutputTwo)
        hfirst (past.length + 1) (by omega)
  exact ⟨nextReceiver, nextOwner, outputOne, outputTwo,
    hstates.trans hmatched, htargetNext, hrowNext⟩

end

end

end DetParityAutomaton

end DistributedSynthesis
