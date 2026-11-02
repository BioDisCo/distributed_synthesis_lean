/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointUnitStateRelativeOperationalCloseAcceptance

/-!
# Exact checker state after one fixed-policy close query

A close query already names the finite open record list and the checked
opposite root.  This file records the remaining local fact needed by the
operational-cut induction: after the physical closing record, the original
DPA is exactly at the target root's fresh `.first` coordinate.

The proof only exposes monitor data on the proof side.  It does not add a row,
direction, graph, or target to either executable endpoint.
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
  (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
  (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
    (initial.code A))
  (bank : ProfiledRawJointUnitPolicyControllerBank A strategy initial policy)

private abbrev UnitKernel
    {InitialOne InitialTwo ExceptionalOne ExceptionalTwo : Type*}
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo) :=
  profiledRawJointUnitPolicyLeaderFreeKernel A strategy initial policy bank
    adapter

/-! ## The selected macro is the monitor's literal target -/

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- The canonical target chosen for a right close is exactly the target
state emitted by the monitor on the closing letter. -/
theorem profiledRawJointUnitRightPolicyCloseTarget_state_eq
    (source : ProfiledRawJointUnitRightPolicyMacro A strategy
      (initial.code A) policy)
    (row : PairedEntryRow) (past : List (In₂ × In₁))
    (move : In₂ × In₁) :
    (profiledRawJointUnitRightPolicyCloseTarget A strategy initial policy bank
      source row past move).state =
      ((profiledRawJointUnitRightPolicyPlay A strategy initial policy bank
        source past move past.length).2.1.target row) := by
  classical
  let target := profiledRawJointUnitRightPolicyCloseTarget A strategy initial
    policy bank source row past move
  have hselected :
      (stepProfiledRawJointUnitRightPolicyReceiverFor A strategy initial policy
        bank source
          (profiledRawJointUnitRightPolicyFiniteStateAfter A strategy initial
            policy bank source past).1 row
          (profiledRawJointUnitRightPolicyFiniteStateAfter A strategy initial
            policy bank source past).2 move).2.2 = some target :=
    (Classical.choose_spec
      (exists_profiledRawJointUnitLeft_step_priority_of_realRightClose A
        strategy initial policy bank source row past move)).1
  obtain ⟨exactTarget, hexactStage, hexactState⟩ :=
    profiledRawJointUnitRightPolicy_real_close_stages_exact A strategy initial
      policy bank source row past move
  have htargetEq : exactTarget = target :=
    Option.some.inj (hexactStage.symm.trans hselected)
  subst exactTarget
  rw [profiledRawJointUnitRightPolicyFiniteStateAfter_eq A strategy initial
    policy bank source] at hexactState
  let monitor := profiledRawJointUnitRightBlockMonitor.{u, v, x, y, s,
    max u v x y s} A strategy (initial.code A) policy source.state source.slot
  let controller := (bank.right source).1
  let play := profiledRawJointUnitRightPolicyPlay A strategy initial policy bank
    source past move
  have hat := profiledRawJointUnitRightPolicy_treePlay_at_prefix A strategy
    initial policy bank source past move
  change play past.length = _ at hat
  have hplayTarget :
      ((play past.length).2.1.target row) =
        (((controller.labelOf (controller.controlAt (senderWord past))).2
          (narrowedControl monitor controller.labeledTree past) move).target
            row) := by
    rw [hat]
    rfl
  exact hexactState.trans hplayTarget.symm

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Left-close mirror of
`profiledRawJointUnitRightPolicyCloseTarget_state_eq`. -/
theorem profiledRawJointUnitLeftPolicyCloseTarget_state_eq
    (source : ProfiledRawJointUnitLeftPolicyMacro A strategy
      (initial.code A) policy)
    (row : PairedEntryRow) (past : List (In₁ × In₂))
    (move : In₁ × In₂) :
    (profiledRawJointUnitLeftPolicyCloseTarget A strategy initial policy bank
      source row past move).state =
      ((profiledRawJointUnitLeftPolicyPlay A strategy initial policy bank
        source past move past.length).2.1.target row) := by
  classical
  let target := profiledRawJointUnitLeftPolicyCloseTarget A strategy initial
    policy bank source row past move
  have hselected :
      (stepProfiledRawJointUnitLeftPolicyReceiverFor A strategy initial policy
        bank source
          (profiledRawJointUnitLeftPolicyFiniteStateAfter A strategy initial
            policy bank source past).1 row
          (profiledRawJointUnitLeftPolicyFiniteStateAfter A strategy initial
            policy bank source past).2 move).2.2 = some target :=
    (Classical.choose_spec
      (exists_profiledRawJointUnitRight_step_priority_of_realLeftClose A
        strategy initial policy bank source row past move)).1
  obtain ⟨exactTarget, hexactStage, hexactState⟩ :=
    profiledRawJointUnitLeftPolicy_real_close_stages_exact A strategy initial
      policy bank source row past move
  have htargetEq : exactTarget = target :=
    Option.some.inj (hexactStage.symm.trans hselected)
  subst exactTarget
  rw [profiledRawJointUnitLeftPolicyFiniteStateAfter_eq A strategy initial
    policy bank source] at hexactState
  let monitor := profiledRawJointUnitLeftBlockMonitor.{u, v, x, y, s,
    max u v x y s} A strategy (initial.code A) policy source.state source.slot
  let controller := (bank.left source).1
  let play := profiledRawJointUnitLeftPolicyPlay A strategy initial policy bank
    source past move
  have hat := profiledRawJointUnitLeftPolicy_treePlay_at_prefix A strategy
    initial policy bank source past move
  change play past.length = _ at hat
  have hplayTarget :
      ((play past.length).2.1.target row) =
        (((controller.labelOf (controller.controlAt (senderWord past))).2
          (narrowedControl monitor controller.labeledTree past) move).target
            row) := by
    rw [hat]
    rfl
  exact hexactState.trans hplayTarget.symm

/-! ## Query-level closing record and state propagation -/

/-- The original-DPA row coordinate stored by a fixed-policy root. -/
def ProfiledRawJointUnitFixedPolicyRoot.entryStateForRow
    (row : PairedEntryRow)
    (root : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy) : A.State :=
  match root with
  | .inl source => pairedCodeStateForRow A row source.slot.1.1
  | .inr source => pairedCodeStateForRow A row source.slot.1.1

/-- The strict physical closing record of a fixed-policy query. -/
noncomputable def ProfiledRawJointUnitPolicyCloseQuery.strictClosingRecord
    {root : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy}
    (query : ProfiledRawJointUnitPolicyCloseQuery A strategy initial policy
      root) : RoundRecord In₁ In₂ Graph Out₁ Out₂ :=
  match query with
  | .right source row past move =>
      pairedRightRecordForRow row
        (profiledRawJointUnitRightPhysicalLetter A
          (profiledRawJointUnitRightPolicyPlay A strategy initial policy bank
            source past move past.length))
  | .left source row past move =>
      pairedLeftRecordForRow row
        (profiledRawJointUnitLeftPhysicalLetter A
          (profiledRawJointUnitLeftPolicyPlay A strategy initial policy bank
            source past move past.length))

/-- The physical closing record selected by the acknowledged close member.
`false` is the ordinary strict record and `true` is the simultaneous record
built from the same literal monitor letter. -/
noncomputable def ProfiledRawJointUnitPolicyCloseQuery.closingRecordForMember
    {root : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy}
    (query : ProfiledRawJointUnitPolicyCloseQuery A strategy initial policy
      root) (member : Bool) : RoundRecord In₁ In₂ Graph Out₁ Out₂ :=
  match query with
  | .right source row past move =>
      profiledRawJointTargetRightClosingRecordForMember member row
        (profiledRawJointUnitRightPhysicalLetter A
          (profiledRawJointUnitRightPolicyPlay A strategy initial policy bank
            source past move past.length))
  | .left source row past move =>
      profiledRawJointTargetLeftClosingRecordForMember member row
        (profiledRawJointUnitLeftPhysicalLetter A
          (profiledRawJointUnitLeftPolicyPlay A strategy initial policy bank
            source past move past.length))

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Consuming one exact strict close lands at the selected target root's
fresh `.first` coordinate. -/
theorem ProfiledRawJointUnitPolicyCloseQuery.runFrom_at_nextCut_eq_target_first
    {root : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy}
    (query : ProfiledRawJointUnitPolicyCloseQuery A strategy initial policy
      root)
    (physicalState : A.State)
    (word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (cuts : Nat → Nat) (k : Nat)
    (hcut : cuts k < cuts (k + 1))
    (hstate : A.runFrom physicalState word (cuts k) =
      query.entryState A strategy initial policy)
    (hlength : (query.records A strategy initial policy bank).length =
      cuts (k + 1) - cuts k - 1)
    (hslice : omegaPrefix (OmegaWord.drop word (cuts k))
        (query.records A strategy initial policy bank).length =
      query.records A strategy initial policy bank)
    (hclosing : OmegaWord.drop word (cuts k)
        (query.records A strategy initial policy bank).length =
      query.strictClosingRecord A strategy initial policy bank) :
    A.runFrom physicalState word (cuts (k + 1)) =
      (query.target A strategy initial policy bank).entryStateForRow A strategy
        initial policy .first := by
  classical
  cases query with
  | right source row past move =>
      let monitor := profiledRawJointUnitRightBlockMonitor.{u, v, x, y, s,
        max u v x y s} A strategy (initial.code A) policy source.state
          source.slot
      let controller := (bank.right source).1
      let env : Nat → In₂ × In₁ := omegaOfList (past ++ [move])
      let tree := narrowedInducedTree monitor controller.labeledTree
      let play := profiledRawJointUnitRightPolicyPlay A strategy initial policy
        bank source past move
      have htree := narrowedInducedTree_winningTree_of_allThreadsWin monitor
        (bank.right source).2
      have hwin : monitor.WinsPlay play := by
        exact (monitor.lift_winningTree_iff tree).mp htree env
      let target := profiledRawJointUnitRightPolicyCloseTarget A strategy
        initial policy bank source row past move
      have htargetState :=
        profiledRawJointUnitRightPolicyCloseTarget_state_eq A strategy initial
          policy bank source row past move
      have htarget :
          profiledRawJointUnitRightTargetProfiledState A
              ((play past.length).2.1.target row) =
            .inr (.inr target.slot) := by
        rw [← htargetState]
        exact profiledRawJointUnitRightTargetProfiledState_eq_of_active_slot A
          target.state target.slot target.active_slot
      have hsafe := profiledRawJointUnitRight_targetsSafe_of_wins A strategy
        (initial.code A) policy source play hwin past.length row
      have hexact : erasePairedProfiledState A (.inr (.inr target.slot)) =
          pairedRightCloseTarget A (monitor.run play past.length).2.1 row
            (profiledRawJointUnitRightPhysicalLetter A
              (play past.length)) := by
        rw [← htarget]
        exact hsafe.1
      let block := profiledRawJointUnitRightPhysicalPrefixRecords A row
        (omegaPrefix play past.length)
      let closing := pairedRightRecordForRow row
        (profiledRawJointUnitRightPhysicalLetter A (play past.length))
      have hscan := profiledRawJointUnitRightBlockMonitor_run_scan_eq_physicalFold
        A strategy (initial.code A) policy source.state source.slot play
          past.length
      have hfold := congrArg Prod.fst
        (pairedRightScanFold_pairForRow_eq_blockEndAndMin A row source.slot.1.1
          ((omegaPrefix play past.length).map
            (profiledRawJointUnitRightPhysicalLetter A)))
      have hend :
          (pairedRightScanPairForRow A row
            (monitor.run play past.length).2.1).1 =
            block.foldl A.step
              (pairedCodeStateForRow A row source.slot.1.1) := by
        rw [hscan]
        rw [blockEndAndMin_fst_eq_foldl A] at hfold
        simpa [block, profiledRawJointUnitRightPhysicalPrefixRecords,
          List.map_map, Function.comp_apply] using hfold
      have htargetStep :
          pairedCodeStateForRow A .first target.slot.1.1 =
            A.step
              (block.foldl A.step
                (pairedCodeStateForRow A row source.slot.1.1)) closing := by
        calc
          pairedCodeStateForRow A .first target.slot.1.1 =
              (pairedRightScanPairForRow A row
                (pairedRightScanStep A (monitor.run play past.length).2.1
                  (profiledRawJointUnitRightPhysicalLetter A
                    (play past.length)))).1 :=
            pairedCodeStateForRow_first_eq_rightScanStep_selected_current_of_exactTarget
              A target.slot (monitor.run play past.length).2.1 row
                (profiledRawJointUnitRightPhysicalLetter A
                  (play past.length)) hexact
          _ = A.step
                (pairedRightScanPairForRow A row
                  (monitor.run play past.length).2.1).1 closing := by
              cases row <;> rfl
          _ = A.step
                (block.foldl A.step
                  (pairedCodeStateForRow A row source.slot.1.1)) closing := by
              rw [hend]
      apply runFrom_at_nextCut_eq_of_slice_and_closing A physicalState word
        cuts k (pairedCodeStateForRow A row source.slot.1.1) block closing
          (pairedCodeStateForRow A .first target.slot.1.1) hcut
      · simpa [ProfiledRawJointUnitPolicyCloseQuery.entryState] using hstate
      · simpa [block, ProfiledRawJointUnitPolicyCloseQuery.records] using
          hlength
      · simpa [block, ProfiledRawJointUnitPolicyCloseQuery.records] using
          hslice
      · simpa [block, closing,
          ProfiledRawJointUnitPolicyCloseQuery.records,
          ProfiledRawJointUnitPolicyCloseQuery.strictClosingRecord] using
            hclosing
      · exact htargetStep
  | left source row past move =>
      let monitor := profiledRawJointUnitLeftBlockMonitor.{u, v, x, y, s,
        max u v x y s} A strategy (initial.code A) policy source.state
          source.slot
      let controller := (bank.left source).1
      let env : Nat → In₁ × In₂ := omegaOfList (past ++ [move])
      let tree := narrowedInducedTree monitor controller.labeledTree
      let play := profiledRawJointUnitLeftPolicyPlay A strategy initial policy
        bank source past move
      have htree := narrowedInducedTree_winningTree_of_allThreadsWin monitor
        (bank.left source).2
      have hwin : monitor.WinsPlay play := by
        exact (monitor.lift_winningTree_iff tree).mp htree env
      let target := profiledRawJointUnitLeftPolicyCloseTarget A strategy initial
        policy bank source row past move
      have htargetState :=
        profiledRawJointUnitLeftPolicyCloseTarget_state_eq A strategy initial
          policy bank source row past move
      have htarget :
          profiledRawJointUnitLeftTargetProfiledState A
              ((play past.length).2.1.target row) =
            .inr (.inl target.slot) := by
        rw [← htargetState]
        exact profiledRawJointUnitLeftTargetProfiledState_eq_of_active_slot A
          target.state target.slot target.active_slot
      have hsafe := profiledRawJointUnitLeft_targetsSafe_of_wins A strategy
        (initial.code A) policy source play hwin past.length row
      have hexact : erasePairedProfiledState A (.inr (.inl target.slot)) =
          pairedLeftCloseTarget A (monitor.run play past.length).2.1 row
            (profiledRawJointUnitLeftPhysicalLetter A
              (play past.length)) := by
        rw [← htarget]
        exact hsafe.1
      let block := profiledRawJointUnitLeftPhysicalPrefixRecords A row
        (omegaPrefix play past.length)
      let closing := pairedLeftRecordForRow row
        (profiledRawJointUnitLeftPhysicalLetter A (play past.length))
      have hscan := profiledRawJointUnitLeftBlockMonitor_run_scan_eq_physicalFold
        A strategy (initial.code A) policy source.state source.slot play
          past.length
      have hfold := congrArg Prod.fst
        (pairedLeftScanFold_pairForRow_eq_blockEndAndMin A row source.slot.1.1
          ((omegaPrefix play past.length).map
            (profiledRawJointUnitLeftPhysicalLetter A)))
      have hend :
          (pairedLeftScanPairForRow A row
            (monitor.run play past.length).2.1).1 =
            block.foldl A.step
              (pairedCodeStateForRow A row source.slot.1.1) := by
        rw [hscan]
        rw [blockEndAndMin_fst_eq_foldl A] at hfold
        simpa [block, profiledRawJointUnitLeftPhysicalPrefixRecords,
          List.map_map, Function.comp_apply] using hfold
      have htargetStep :
          pairedCodeStateForRow A .first target.slot.1.1 =
            A.step
              (block.foldl A.step
                (pairedCodeStateForRow A row source.slot.1.1)) closing := by
        calc
          pairedCodeStateForRow A .first target.slot.1.1 =
              (pairedLeftScanPairForRow A row
                (pairedLeftScanStep A (monitor.run play past.length).2.1
                  (profiledRawJointUnitLeftPhysicalLetter A
                    (play past.length)))).1 :=
            pairedCodeStateForRow_first_eq_leftScanStep_selected_current_of_exactTarget
              A target.slot (monitor.run play past.length).2.1 row
                (profiledRawJointUnitLeftPhysicalLetter A
                  (play past.length)) hexact
          _ = A.step
                (pairedLeftScanPairForRow A row
                  (monitor.run play past.length).2.1).1 closing := by
              cases row <;> rfl
          _ = A.step
                (block.foldl A.step
                  (pairedCodeStateForRow A row source.slot.1.1)) closing := by
              rw [hend]
      apply runFrom_at_nextCut_eq_of_slice_and_closing A physicalState word
        cuts k (pairedCodeStateForRow A row source.slot.1.1) block closing
          (pairedCodeStateForRow A .first target.slot.1.1) hcut
      · simpa [ProfiledRawJointUnitPolicyCloseQuery.entryState] using hstate
      · simpa [block, ProfiledRawJointUnitPolicyCloseQuery.records] using
          hlength
      · simpa [block, ProfiledRawJointUnitPolicyCloseQuery.records] using
          hslice
      · simpa [block, closing,
          ProfiledRawJointUnitPolicyCloseQuery.records,
          ProfiledRawJointUnitPolicyCloseQuery.strictClosingRecord] using
            hclosing
      · exact htargetStep

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Member-aware state propagation for one fixed-policy close query.  A
strict close installs the selected target's `.first` coordinate, while a
simultaneous close installs its `.both` coordinate.  Both cases use the same
literal policy target and the same represented open prefix. -/
theorem ProfiledRawJointUnitPolicyCloseQuery.runFrom_at_nextCut_eq_target_row
    {root : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy}
    (query : ProfiledRawJointUnitPolicyCloseQuery A strategy initial policy
      root)
    (member : Bool)
    (physicalState : A.State)
    (word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (cuts : Nat → Nat) (k : Nat)
    (hcut : cuts k < cuts (k + 1))
    (hstate : A.runFrom physicalState word (cuts k) =
      query.entryState A strategy initial policy)
    (hlength : (query.records A strategy initial policy bank).length =
      cuts (k + 1) - cuts k - 1)
    (hslice : omegaPrefix (OmegaWord.drop word (cuts k))
        (query.records A strategy initial policy bank).length =
      query.records A strategy initial policy bank)
    (hclosing : OmegaWord.drop word (cuts k)
        (query.records A strategy initial policy bank).length =
      query.closingRecordForMember A strategy initial policy bank member) :
    A.runFrom physicalState word (cuts (k + 1)) =
      (query.target A strategy initial policy bank).entryStateForRow A strategy
        initial policy (profiledRawJointCloseRowOfMember member) := by
  classical
  cases query with
  | right source row past move =>
      let monitor := profiledRawJointUnitRightBlockMonitor.{u, v, x, y, s,
        max u v x y s} A strategy (initial.code A) policy source.state
          source.slot
      let controller := (bank.right source).1
      let env : Nat → In₂ × In₁ := omegaOfList (past ++ [move])
      let tree := narrowedInducedTree monitor controller.labeledTree
      let play := profiledRawJointUnitRightPolicyPlay A strategy initial policy
        bank source past move
      have htree := narrowedInducedTree_winningTree_of_allThreadsWin monitor
        (bank.right source).2
      have hwin : monitor.WinsPlay play := by
        exact (monitor.lift_winningTree_iff tree).mp htree env
      let target := profiledRawJointUnitRightPolicyCloseTarget A strategy
        initial policy bank source row past move
      have htargetState :=
        profiledRawJointUnitRightPolicyCloseTarget_state_eq A strategy initial
          policy bank source row past move
      have htarget :
          profiledRawJointUnitRightTargetProfiledState A
              ((play past.length).2.1.target row) =
            .inr (.inr target.slot) := by
        rw [← htargetState]
        exact profiledRawJointUnitRightTargetProfiledState_eq_of_active_slot A
          target.state target.slot target.active_slot
      cases member with
      | false =>
          apply ProfiledRawJointUnitPolicyCloseQuery.runFrom_at_nextCut_eq_target_first
            A strategy initial policy bank (.right source row past move)
              physicalState word cuts k hcut hstate hlength hslice
          simpa [ProfiledRawJointUnitPolicyCloseQuery.strictClosingRecord,
            ProfiledRawJointUnitPolicyCloseQuery.closingRecordForMember] using
              hclosing
      | true =>
          have hsafe := profiledRawJointUnitRight_targetsSafe_of_wins A strategy
            (initial.code A) policy source play hwin past.length row
          have hexact : erasePairedProfiledState A (.inr (.inr target.slot)) =
              pairedRightCloseTarget A (monitor.run play past.length).2.1 row
                (profiledRawJointUnitRightPhysicalLetter A
                  (play past.length)) := by
            rw [← htarget]
            exact hsafe.1
          let block := profiledRawJointUnitRightPhysicalPrefixRecords A row
            (omegaPrefix play past.length)
          let closing := bothRoundRecord
            ((profiledRawJointUnitRightPhysicalLetter A
                (play past.length)).1.2,
              (profiledRawJointUnitRightPhysicalLetter A
                (play past.length)).1.1)
            (pairedRightClosingForRow row
              (profiledRawJointUnitRightPhysicalLetter A
                (play past.length)).2.1)
            (pairedRightInformedForRow row
              (profiledRawJointUnitRightPhysicalLetter A
                (play past.length)).2.1)
          have hscan :=
            profiledRawJointUnitRightBlockMonitor_run_scan_eq_physicalFold A
              strategy (initial.code A) policy source.state source.slot play
                past.length
          have hfold := congrArg Prod.fst
            (pairedRightScanFold_pairForRow_eq_blockEndAndMin A row
              source.slot.1.1
              ((omegaPrefix play past.length).map
                (profiledRawJointUnitRightPhysicalLetter A)))
          have hend :
              (pairedRightScanPairForRow A row
                (monitor.run play past.length).2.1).1 =
                block.foldl A.step
                  (pairedCodeStateForRow A row source.slot.1.1) := by
            rw [hscan]
            rw [blockEndAndMin_fst_eq_foldl A] at hfold
            simpa [block, profiledRawJointUnitRightPhysicalPrefixRecords,
              List.map_map, Function.comp_apply] using hfold
          have htargetStep :
              pairedCodeStateForRow A .both target.slot.1.1 =
                A.step
                  (block.foldl A.step
                    (pairedCodeStateForRow A row source.slot.1.1)) closing := by
            calc
              pairedCodeStateForRow A .both target.slot.1.1 =
                  A.step
                    (pairedRightScanPairForRow A row
                      (monitor.run play past.length).2.1).1 closing := by
                simpa [closing] using
                  (pairedCodeStateForRow_both_eq_rightBothStep_selected_current_of_exactTarget
                    A target.slot (monitor.run play past.length).2.1 row
                      (profiledRawJointUnitRightPhysicalLetter A
                        (play past.length)) hexact)
              _ = A.step
                    (block.foldl A.step
                      (pairedCodeStateForRow A row source.slot.1.1)) closing := by
                rw [hend]
          have hnext := runFrom_at_nextCut_eq_of_slice_and_closing A
            physicalState word cuts k
              (pairedCodeStateForRow A row source.slot.1.1) block closing
                (pairedCodeStateForRow A .both target.slot.1.1) hcut
              (by simpa [ProfiledRawJointUnitPolicyCloseQuery.entryState]
                using hstate)
              (by simpa [block, ProfiledRawJointUnitPolicyCloseQuery.records]
                using hlength)
              (by simpa [block, ProfiledRawJointUnitPolicyCloseQuery.records]
                using hslice)
              (by simpa [block, closing,
                ProfiledRawJointUnitPolicyCloseQuery.records,
                ProfiledRawJointUnitPolicyCloseQuery.closingRecordForMember]
                  using hclosing)
              htargetStep
          simpa [ProfiledRawJointUnitPolicyCloseQuery.target,
            ProfiledRawJointUnitFixedPolicyRoot.entryStateForRow,
            profiledRawJointUnitRightPolicyCloseTarget, target] using hnext
  | left source row past move =>
      let monitor := profiledRawJointUnitLeftBlockMonitor.{u, v, x, y, s,
        max u v x y s} A strategy (initial.code A) policy source.state
          source.slot
      let controller := (bank.left source).1
      let env : Nat → In₁ × In₂ := omegaOfList (past ++ [move])
      let tree := narrowedInducedTree monitor controller.labeledTree
      let play := profiledRawJointUnitLeftPolicyPlay A strategy initial policy
        bank source past move
      have htree := narrowedInducedTree_winningTree_of_allThreadsWin monitor
        (bank.left source).2
      have hwin : monitor.WinsPlay play := by
        exact (monitor.lift_winningTree_iff tree).mp htree env
      let target := profiledRawJointUnitLeftPolicyCloseTarget A strategy
        initial policy bank source row past move
      have htargetState :=
        profiledRawJointUnitLeftPolicyCloseTarget_state_eq A strategy initial
          policy bank source row past move
      have htarget :
          profiledRawJointUnitLeftTargetProfiledState A
              ((play past.length).2.1.target row) =
            .inr (.inl target.slot) := by
        rw [← htargetState]
        exact profiledRawJointUnitLeftTargetProfiledState_eq_of_active_slot A
          target.state target.slot target.active_slot
      cases member with
      | false =>
          apply ProfiledRawJointUnitPolicyCloseQuery.runFrom_at_nextCut_eq_target_first
            A strategy initial policy bank (.left source row past move)
              physicalState word cuts k hcut hstate hlength hslice
          simpa [ProfiledRawJointUnitPolicyCloseQuery.strictClosingRecord,
            ProfiledRawJointUnitPolicyCloseQuery.closingRecordForMember] using
              hclosing
      | true =>
          have hsafe := profiledRawJointUnitLeft_targetsSafe_of_wins A strategy
            (initial.code A) policy source play hwin past.length row
          have hexact : erasePairedProfiledState A (.inr (.inl target.slot)) =
              pairedLeftCloseTarget A (monitor.run play past.length).2.1 row
                (profiledRawJointUnitLeftPhysicalLetter A
                  (play past.length)) := by
            rw [← htarget]
            exact hsafe.1
          let block := profiledRawJointUnitLeftPhysicalPrefixRecords A row
            (omegaPrefix play past.length)
          let closing := bothRoundRecord
            (profiledRawJointUnitLeftPhysicalLetter A
              (play past.length)).1
            (pairedLeftInformedForRow row
              (profiledRawJointUnitLeftPhysicalLetter A
                (play past.length)).2.1)
            (pairedLeftClosingForRow row
              (profiledRawJointUnitLeftPhysicalLetter A
                (play past.length)).2.1)
          have hscan :=
            profiledRawJointUnitLeftBlockMonitor_run_scan_eq_physicalFold A
              strategy (initial.code A) policy source.state source.slot play
                past.length
          have hfold := congrArg Prod.fst
            (pairedLeftScanFold_pairForRow_eq_blockEndAndMin A row
              source.slot.1.1
              ((omegaPrefix play past.length).map
                (profiledRawJointUnitLeftPhysicalLetter A)))
          have hend :
              (pairedLeftScanPairForRow A row
                (monitor.run play past.length).2.1).1 =
                block.foldl A.step
                  (pairedCodeStateForRow A row source.slot.1.1) := by
            rw [hscan]
            rw [blockEndAndMin_fst_eq_foldl A] at hfold
            simpa [block, profiledRawJointUnitLeftPhysicalPrefixRecords,
              List.map_map, Function.comp_apply] using hfold
          have htargetStep :
              pairedCodeStateForRow A .both target.slot.1.1 =
                A.step
                  (block.foldl A.step
                    (pairedCodeStateForRow A row source.slot.1.1)) closing := by
            calc
              pairedCodeStateForRow A .both target.slot.1.1 =
                  A.step
                    (pairedLeftScanPairForRow A row
                      (monitor.run play past.length).2.1).1 closing := by
                simpa [closing] using
                  (pairedCodeStateForRow_both_eq_leftBothStep_selected_current_of_exactTarget
                    A target.slot (monitor.run play past.length).2.1 row
                      (profiledRawJointUnitLeftPhysicalLetter A
                        (play past.length)) hexact)
              _ = A.step
                    (block.foldl A.step
                      (pairedCodeStateForRow A row source.slot.1.1)) closing := by
                rw [hend]
          have hnext := runFrom_at_nextCut_eq_of_slice_and_closing A
            physicalState word cuts k
              (pairedCodeStateForRow A row source.slot.1.1) block closing
                (pairedCodeStateForRow A .both target.slot.1.1) hcut
              (by simpa [ProfiledRawJointUnitPolicyCloseQuery.entryState]
                using hstate)
              (by simpa [block, ProfiledRawJointUnitPolicyCloseQuery.records]
                using hlength)
              (by simpa [block, ProfiledRawJointUnitPolicyCloseQuery.records]
                using hslice)
              (by simpa [block, closing,
                ProfiledRawJointUnitPolicyCloseQuery.records,
                ProfiledRawJointUnitPolicyCloseQuery.closingRecordForMember]
                  using hclosing)
              htargetStep
          simpa [ProfiledRawJointUnitPolicyCloseQuery.target,
            ProfiledRawJointUnitFixedPolicyRoot.entryStateForRow,
            profiledRawJointUnitLeftPolicyCloseTarget, target] using hnext

/-! ## Fresh control endpoints -/

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- A complete strict-right block from the genuine fresh root ends in the
matched-right state that stores the query's exact target. -/
theorem profiledRawJointUnitFreshMatchedRight_close_endpoint
    {InitialOne InitialTwo ExceptionalOne ExceptionalTwo : Type*}
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (source : ProfiledRawJointUnitRightPolicyMacro A strategy
      (initial.code A) policy)
    (row : PairedEntryRow) (past : List (In₂ × In₁))
    (move : In₂ × In₁)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂) :
    let query : ProfiledRawJointUnitPolicyCloseQuery A strategy initial policy
        (.inl source) := .right source row past move
    let blockInputs : Nat → In₂ × In₁ := omegaOfList (past ++ [move])
    ∃ nextOwner : ProfiledRawJointUnitRightPolicyOwnerControl A strategy
          initial policy bank,
      ∃ nextReceiver : ProfiledRawJointUnitRightPolicyReceiverControl A
          strategy initial policy,
      ∃ outputOne outputTwo,
        ((UnitKernel A strategy initial policy bank adapter).globalMachine.reroot
          (profiledRawJointUnitFreshMatchedRightState A strategy initial policy
            bank adapter source row oldOutputOne oldOutputTwo)).globalStateTrace
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
  · simpa [nextOwner, nextReceiver] using hfresh
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
    rw [hpast, hmove, hqueryTarget]
    congr 1
    rw [hstage]
    rfl

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Strict-left mirror of
`profiledRawJointUnitFreshMatchedRight_close_endpoint`. -/
theorem profiledRawJointUnitFreshMatchedLeft_close_endpoint
    {InitialOne InitialTwo ExceptionalOne ExceptionalTwo : Type*}
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (source : ProfiledRawJointUnitLeftPolicyMacro A strategy
      (initial.code A) policy)
    (row : PairedEntryRow) (past : List (In₁ × In₂))
    (move : In₁ × In₂)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂) :
    let query : ProfiledRawJointUnitPolicyCloseQuery A strategy initial policy
        (.inr source) := .left source row past move
    let blockInputs : Nat → In₁ × In₂ := omegaOfList (past ++ [move])
    ∃ nextReceiver : ProfiledRawJointUnitLeftPolicyReceiverControl A strategy
          initial policy,
      ∃ nextOwner : ProfiledRawJointUnitLeftPolicyOwnerControl A strategy
          initial policy bank,
      ∃ outputOne outputTwo,
        ((UnitKernel A strategy initial policy bank adapter).globalMachine.reroot
          (profiledRawJointUnitFreshMatchedLeftState A strategy initial policy
            bank adapter source row oldOutputOne oldOutputTwo)).globalStateTrace
              (profiledRawJointUnitStrictLeftEnvironment blockInputs)
              (past.length + 1) =
            profiledRawJointUnitMatchedLeftState A strategy initial policy bank
              adapter nextReceiver nextOwner outputOne outputTwo ∧
        (.inl (profiledRawJointUnitPolicyLeftReceiverTarget A strategy initial
            policy bank nextReceiver) :
          ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
            policy) = query.target A strategy initial policy bank ∧
        nextReceiver.2.1 = row := by
  dsimp only
  let blockInputs : Nat → In₁ × In₂ := omegaOfList (past ++ [move])
  obtain ⟨outputOne, outputTwo, hfresh⟩ :=
    profiledRawJointUnitFreshMatchedLeft_controls A strategy initial policy bank
      adapter source row oldOutputOne oldOutputTwo blockInputs
        (past.length + 1)
  let nextReceiver : ProfiledRawJointUnitLeftPolicyReceiverControl A strategy
      initial policy :=
    ⟨source, row,
      (profiledRawJointUnitLeftPolicyFiniteStateAfter A strategy initial policy
        bank source (omegaPrefix blockInputs (past.length + 1))).2,
      profiledRawJointUnitLeftStagedAfter A strategy initial policy bank source
        row blockInputs (past.length + 1)⟩
  let nextOwner : ProfiledRawJointUnitLeftPolicyOwnerControl A strategy initial
      policy bank :=
    ⟨source,
      (profiledRawJointUnitLeftPolicyFiniteStateAfter A strategy initial policy
        bank source (omegaPrefix blockInputs (past.length + 1))).1⟩
  refine ⟨nextReceiver, nextOwner, outputOne, outputTwo, ?_, ?_, rfl⟩
  · simpa [nextReceiver, nextOwner] using hfresh
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
        (stepProfiledRawJointUnitLeftPolicyReceiverFor A strategy initial policy
          bank source
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
    rw [hpast, hmove, hqueryTarget]
    congr 1
    rw [hstage]
    rfl

end

end DetParityAutomaton

end DistributedSynthesis
