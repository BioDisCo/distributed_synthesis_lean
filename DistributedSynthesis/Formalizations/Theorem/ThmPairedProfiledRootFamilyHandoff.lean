/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteRootFamilyNarrowing
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledBankLocalHandoff
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledGuardedFirstLocalHandoff

/-!
# Certified handoff from a simultaneous profiled root family

Simultaneous root narrowing is useful recursively only if every projected
member still emits a certified opposite-orientation macro.  This file proves
that fact directly from the member all-thread theorem and the existing
profiled monitor soundness theorem.

The family index is used only in the receiver component of the simultaneous
controller.  The sender table is the one shared table proved in
`LemFiniteRootFamilyNarrowing`; no process receives the index.
-/

namespace DistributedSynthesis

universe i u v x y s z

namespace DetParityAutomaton

variable {I : Type i}
variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

section

noncomputable section

variable [Inhabited I] [Fintype I] [DecidableEq I]
variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

/-- Monitor family for simultaneously narrowing right-oriented recurrent
anchors. -/
noncomputable abbrev profiledBankRightRootMonitors
    (source : I → ProfiledBankRightMacro A) :=
  fun index => profiledBankRightMonitor A (source index)

/-- Left-oriented mirror. -/
noncomputable abbrev profiledBankLeftRootMonitors
    (source : I → ProfiledBankLeftMacro A) :=
  fun index => profiledBankLeftMonitor A (source index)

/-- Literal finite table type for one right-oriented hidden root family. -/
noncomputable abbrev ProfiledBankRightRootFamilyTable
    (source : I → ProfiledBankRightMacro A) :=
  FiniteRootFamilyTable (profiledBankRightRootMonitors A source)

/-- Left-oriented mirror table type. -/
noncomputable abbrev ProfiledBankLeftRootFamilyTable
    (source : I → ProfiledBankLeftMacro A) :=
  FiniteRootFamilyTable (profiledBankLeftRootMonitors A source)

/-! The actual dangerous case hides at most one bit.  The outer automaton's
move alphabet can therefore be materialized as a finite dependent sum of a
two-root family and its simultaneous state-controlled table. -/

/-- One finite right-family move, including its two proof anchors and shared
controller table. -/
abbrev ProfiledBankRightPairMove :=
  Σ source : Bool → ProfiledBankRightMacro A,
    ProfiledBankRightRootFamilyTable A source

/-- Left-family mirror move. -/
abbrev ProfiledBankLeftPairMove :=
  Σ source : Bool → ProfiledBankLeftMacro A,
    ProfiledBankLeftRootFamilyTable A source

/-- Finite outer move alphabet for the two orientations. -/
abbrev ProfiledBankRootFamilyMove :=
  ProfiledBankRightPairMove A ⊕ ProfiledBankLeftPairMove A

noncomputable instance : Fintype (ProfiledBankRightPairMove A) := by
  classical
  infer_instance

noncomputable instance : Fintype (ProfiledBankLeftPairMove A) := by
  classical
  infer_instance

noncomputable instance : Fintype (ProfiledBankRootFamilyMove A) := by
  classical
  infer_instance

/-! ## The actual mixed exceptional/recurrent family -/

/-- A right root may still be in the exceptional first controller or may
already have restarted in the recurrent bank. -/
abbrev ProfiledRightFamilyRoot :=
  ProfiledGuardedFirstRightMacro A ⊕ ProfiledBankRightMacro A

/-- Left mirror. -/
abbrev ProfiledLeftFamilyRoot :=
  ProfiledGuardedFirstLeftMacro A ⊕ ProfiledBankLeftMacro A

noncomputable abbrev profiledRightFamilyRootMonitor
    (root : ProfiledRightFamilyRoot A) :=
  match root with
  | .inl key => profiledGuardedFirstRightMonitorAt A key
  | .inr source => profiledBankRightMonitor A source

noncomputable abbrev profiledLeftFamilyRootMonitor
    (root : ProfiledLeftFamilyRoot A) :=
  match root with
  | .inl key => profiledGuardedFirstLeftMonitorAt A key
  | .inr source => profiledBankLeftMonitor A source

/-! A mixed-depth root must remember the state at which its monitor is
restarted.  Omitting this state would prove only the fresh-root special case
and would not cover a continued exceptional branch paired with a recurrent
one. -/

/-- Right proof anchor together with its actual finite restart state. -/
abbrev ProfiledRightRestartRoot :=
  Σ root : ProfiledRightFamilyRoot A,
    (profiledRightFamilyRootMonitor A root).State

/-- Left mirror. -/
abbrev ProfiledLeftRestartRoot :=
  Σ root : ProfiledLeftFamilyRoot A,
    (profiledLeftFamilyRootMonitor A root).State

noncomputable instance : Fintype (ProfiledRightRestartRoot A) := by
  classical
  infer_instance

noncomputable instance : Fintype (ProfiledLeftRestartRoot A) := by
  classical
  infer_instance

noncomputable abbrev profiledRightRestartRootMonitor
    (root : ProfiledRightRestartRoot A) :=
  (profiledRightFamilyRootMonitor A root.1).restartAt root.2

noncomputable abbrev profiledLeftRestartRootMonitor
    (root : ProfiledLeftRestartRoot A) :=
  (profiledLeftFamilyRootMonitor A root.1).restartAt root.2

section
omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]

private theorem profiledGuardedFirstRight_targetsSafe_of_restartAt_wins
    (key : ProfiledGuardedFirstRightMacro A)
    (start : (profiledGuardedFirstRightMonitorAt A key).State)
    (play : Nat → RealizedBlockRound In₂ In₁
      (ProfiledRightReceiverOutput A) Out₁)
    (hwin : ((profiledGuardedFirstRightMonitorAt A key).restartAt start).WinsPlay
      play) (n : Nat) :
    ∀ row,
      erasePairedProfiledState A ((play n).2.1.target row) =
          pairedRightCloseTarget A
            ((((profiledGuardedFirstRightMonitorAt A key).restartAt start).run
              play n).2.1) row (profiledRightPhysicalLetter A (play n)) ∧
        (pairedProfiledEntryRunAutomaton A
          ((play n).2.1.target row)).HasRationalRun := by
  classical
  let base := profiledGuardedFirstRightMonitorAt A key
  have hsafe := base.restartAt_safe_of_wins
    (fun state => state.2.2.2.2)
    (by
      intro state round hfalse
      change state.2.2.2.2 = false at hfalse
      change (((((state.2.2.2.2 && _) && _) && decide _) && decide _) = false)
      rw [hfalse]
      rfl)
    (by
      intro state hfalse
      change state.2.2.2.2 = false at hfalse
      change (if state.2.2.2.2 then _ else 1) = 1
      rw [hfalse]
      rfl)
    start play hwin (n + 1)
  rw [BlockRecordMonitor.run] at hsafe
  simp only [base, BlockRecordMonitor.restartAt,
    profiledGuardedFirstRightMonitorAt,
    profiledGuardedFirstRightBlockMonitor, Bool.and_eq_true,
    decide_eq_true_eq] at hsafe
  exact hsafe.2

private theorem profiledGuardedFirstLeft_targetsSafe_of_restartAt_wins
    (key : ProfiledGuardedFirstLeftMacro A)
    (start : (profiledGuardedFirstLeftMonitorAt A key).State)
    (play : Nat → RealizedBlockRound In₁ In₂
      (ProfiledLeftReceiverOutput A) Out₂)
    (hwin : ((profiledGuardedFirstLeftMonitorAt A key).restartAt start).WinsPlay
      play) (n : Nat) :
    ∀ row,
      erasePairedProfiledState A ((play n).2.1.target row) =
          pairedLeftCloseTarget A
            ((((profiledGuardedFirstLeftMonitorAt A key).restartAt start).run
              play n).2.1) row (profiledLeftPhysicalLetter A (play n)) ∧
        (pairedProfiledEntryRunAutomaton A
          ((play n).2.1.target row)).HasRationalRun := by
  classical
  let base := profiledGuardedFirstLeftMonitorAt A key
  have hsafe := base.restartAt_safe_of_wins
    (fun state => state.2.2.2.2)
    (by
      intro state round hfalse
      change state.2.2.2.2 = false at hfalse
      change (((((state.2.2.2.2 && _) && _) && decide _) && decide _) = false)
      rw [hfalse]
      rfl)
    (by
      intro state hfalse
      change state.2.2.2.2 = false at hfalse
      change (if state.2.2.2.2 then _ else 1) = 1
      rw [hfalse]
      rfl)
    start play hwin (n + 1)
  rw [BlockRecordMonitor.run] at hsafe
  simp only [base, BlockRecordMonitor.restartAt,
    profiledGuardedFirstLeftMonitorAt,
    profiledGuardedFirstLeftBlockMonitor, Bool.and_eq_true,
    decide_eq_true_eq] at hsafe
  exact hsafe.2

private theorem profiledBankRight_targetsSafe_of_restartAt_wins
    (source : ProfiledBankRightMacro A)
    (start : (profiledBankRightMonitor A source).State)
    (play : Nat → RealizedBlockRound In₂ In₁
      (ProfiledRightReceiverOutput A) Out₁)
    (hwin : ((profiledBankRightMonitor A source).restartAt start).WinsPlay play)
    (n : Nat) :
    ∀ row,
      erasePairedProfiledState A ((play n).2.1.target row) =
          pairedRightCloseTarget A
            ((((profiledBankRightMonitor A source).restartAt start).run
              play n).2.1) row (profiledRightPhysicalLetter A (play n)) ∧
        PairedProfiledRationalPolicy.Allowed A
          (feasibleProfiledPolicy A source.1)
          (.inr (.inl source.2.1)) ((play n).2.1.target row) := by
  classical
  let base := profiledBankRightMonitor A source
  have hsafe := base.restartAt_safe_of_wins
    (fun state => state.2.2.2.2)
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
    start play hwin (n + 1)
  rw [BlockRecordMonitor.run] at hsafe
  simp only [base, BlockRecordMonitor.restartAt, profiledBankRightMonitor,
    profiledRightBlockMonitor, Bool.and_eq_true, decide_eq_true_eq] at hsafe
  exact hsafe.2

private theorem profiledBankLeft_targetsSafe_of_restartAt_wins
    (source : ProfiledBankLeftMacro A)
    (start : (profiledBankLeftMonitor A source).State)
    (play : Nat → RealizedBlockRound In₁ In₂
      (ProfiledLeftReceiverOutput A) Out₂)
    (hwin : ((profiledBankLeftMonitor A source).restartAt start).WinsPlay play)
    (n : Nat) :
    ∀ row,
      erasePairedProfiledState A ((play n).2.1.target row) =
          pairedLeftCloseTarget A
            ((((profiledBankLeftMonitor A source).restartAt start).run
              play n).2.1) row (profiledLeftPhysicalLetter A (play n)) ∧
        PairedProfiledRationalPolicy.Allowed A
          (feasibleProfiledPolicy A source.1)
          (.inr (.inr source.2.1)) ((play n).2.1.target row) := by
  classical
  let base := profiledBankLeftMonitor A source
  have hsafe := base.restartAt_safe_of_wins
    (fun state => state.2.2.2.2)
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
    start play hwin (n + 1)
  rw [BlockRecordMonitor.run] at hsafe
  simp only [base, BlockRecordMonitor.restartAt, profiledBankLeftMonitor,
    profiledLeftBlockMonitor, Bool.and_eq_true, decide_eq_true_eq] at hsafe
  exact hsafe.2

end

noncomputable abbrev profiledRightFamilyRootMonitors
    (source : I → ProfiledRightRestartRoot A) :=
  fun index => profiledRightRestartRootMonitor A (source index)

noncomputable abbrev profiledLeftFamilyRootMonitors
    (source : I → ProfiledLeftRestartRoot A) :=
  fun index => profiledLeftRestartRootMonitor A (source index)

noncomputable abbrev ProfiledRightFamilyRootTable
    (source : I → ProfiledRightRestartRoot A) :=
  FiniteRootFamilyTable (profiledRightFamilyRootMonitors A source)

noncomputable abbrev ProfiledLeftFamilyRootTable
    (source : I → ProfiledLeftRestartRoot A) :=
  FiniteRootFamilyTable (profiledLeftFamilyRootMonitors A source)

/-- Literal finite move type for the dangerous two-anchor right family. -/
abbrev ProfiledRightFamilyPairMove :=
  Σ source : Bool → ProfiledRightRestartRoot A,
    ProfiledRightFamilyRootTable A source

/-- Left mirror. -/
abbrev ProfiledLeftFamilyPairMove :=
  Σ source : Bool → ProfiledLeftRestartRoot A,
    ProfiledLeftFamilyRootTable A source

section
omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]

/-- The two right-family projections have the same blind process-one control
at every local input word.  This is the stateful form of cross-anchor local
consistency: it survives arbitrarily many consecutive blind rounds, rather
than merely equating the first output. -/
theorem profiledRightFamilyPairMove_control_eq
    (move : ProfiledRightFamilyPairMove A) (word : List In₁) :
    (finiteRootMemberController
        (profiledRightFamilyRootMonitors A move.1)
        move.2.toTransitionRationalTree false).controlAt word =
      (finiteRootMemberController
        (profiledRightFamilyRootMonitors A move.1)
        move.2.toTransitionRationalTree true).controlAt word := by
  exact finiteRootMemberController_control_eq
    (profiledRightFamilyRootMonitors A move.1)
    move.2.toTransitionRationalTree false true word

/-- Consequently the two right-family projections emit the same blind
process-one output function after every local input word. -/
theorem profiledRightFamilyPairMove_sender_eq
    (move : ProfiledRightFamilyPairMove A) (word : List In₁) :
    ((finiteRootMemberController
        (profiledRightFamilyRootMonitors A move.1)
        move.2.toTransitionRationalTree false).labeledTree word).1 =
      ((finiteRootMemberController
        (profiledRightFamilyRootMonitors A move.1)
        move.2.toTransitionRationalTree true).labeledTree word).1 := by
  exact finiteRootMemberController_sender_eq
    (profiledRightFamilyRootMonitors A move.1)
    move.2.toTransitionRationalTree false true word

/-- Pointwise form used by an actual blind process-one step. -/
theorem profiledRightFamilyPairMove_blind_output_eq
    (move : ProfiledRightFamilyPairMove A)
    (left right : Bool) (word : List In₁) (input : In₁) :
    ((finiteRootMemberController
        (profiledRightFamilyRootMonitors A move.1)
        move.2.toTransitionRationalTree left).labeledTree word).1 input =
      ((finiteRootMemberController
        (profiledRightFamilyRootMonitors A move.1)
        move.2.toTransitionRationalTree right).labeledTree word).1 input := by
  exact congrFun
    (finiteRootMemberController_sender_eq
      (profiledRightFamilyRootMonitors A move.1)
      move.2.toTransitionRationalTree left right word) input

/-- Left-family mirror: both projections carry one process-two control. -/
theorem profiledLeftFamilyPairMove_control_eq
    (move : ProfiledLeftFamilyPairMove A) (word : List In₂) :
    (finiteRootMemberController
        (profiledLeftFamilyRootMonitors A move.1)
        move.2.toTransitionRationalTree false).controlAt word =
      (finiteRootMemberController
        (profiledLeftFamilyRootMonitors A move.1)
        move.2.toTransitionRationalTree true).controlAt word := by
  exact finiteRootMemberController_control_eq
    (profiledLeftFamilyRootMonitors A move.1)
    move.2.toTransitionRationalTree false true word

/-- Both left-family projections emit the same blind process-two output
function after every local input word. -/
theorem profiledLeftFamilyPairMove_sender_eq
    (move : ProfiledLeftFamilyPairMove A) (word : List In₂) :
    ((finiteRootMemberController
        (profiledLeftFamilyRootMonitors A move.1)
        move.2.toTransitionRationalTree false).labeledTree word).1 =
      ((finiteRootMemberController
        (profiledLeftFamilyRootMonitors A move.1)
        move.2.toTransitionRationalTree true).labeledTree word).1 := by
  exact finiteRootMemberController_sender_eq
    (profiledLeftFamilyRootMonitors A move.1)
    move.2.toTransitionRationalTree false true word

/-- Pointwise process-two mirror used at the other alternating seam. -/
theorem profiledLeftFamilyPairMove_blind_output_eq
    (move : ProfiledLeftFamilyPairMove A)
    (left right : Bool) (word : List In₂) (input : In₂) :
    ((finiteRootMemberController
        (profiledLeftFamilyRootMonitors A move.1)
        move.2.toTransitionRationalTree left).labeledTree word).1 input =
      ((finiteRootMemberController
        (profiledLeftFamilyRootMonitors A move.1)
        move.2.toTransitionRationalTree right).labeledTree word).1 input := by
  exact congrFun
    (finiteRootMemberController_sender_eq
      (profiledLeftFamilyRootMonitors A move.1)
      move.2.toTransitionRationalTree left right word) input

end

noncomputable instance : Fintype (ProfiledRightFamilyPairMove A) := by
  classical
  infer_instance

noncomputable instance : Fintype (ProfiledLeftFamilyPairMove A) := by
  classical
  infer_instance

/-- A winning simultaneous mixed right family always hands each member to a
genuine recurrent left macro.  This includes the exceptional/recurrent pair
in the dangerous `both; right; left` seam. -/
noncomputable def profiledRightFamilyRootChild
    (source : I → ProfiledRightRestartRoot A)
    (family : TransitionRationalTree In₁
      (NarrowedBlockLabel (I × In₂) In₁ (ProfiledRightReceiverOutput A) Out₁
        (finiteRootFamilyMonitor
          (profiledRightFamilyRootMonitors A source)).State))
    (hfamily : NarrowedAllThreadsWin
      (finiteRootFamilyMonitor (profiledRightFamilyRootMonitors A source))
      family.labeledTree)
    (index : I) (env : Nat → In₂ × In₁) (n : Nat)
    (row : PairedEntryRow) : ProfiledBankLeftMacro A := by
  let monitor := profiledRightRestartRootMonitor A (source index)
  let member := finiteRootMemberController
    (profiledRightFamilyRootMonitors A source) family index
  let tree := narrowedInducedTree monitor member.labeledTree
  have hmember : NarrowedAllThreadsWin monitor member.labeledTree :=
    finiteRootMemberController_allThreadsWin
      (profiledRightFamilyRootMonitors A source) family hfamily index
  have htree :=
    narrowedInducedTree_winningTree_of_allThreadsWin monitor hmember
  have hwin : monitor.WinsPlay (treePlay tree env) :=
    (monitor.lift_winningTree_iff tree).mp htree env
  let output := (treePlay tree env n).2.1
  let letter := profiledRightPhysicalLetter A (treePlay tree env n)
  rcases hsource : source index with ⟨kind, start⟩
  dsimp [monitor, profiledRightRestartRootMonitor] at hwin
  rw [hsource] at hwin
  cases kind with
  | inl key =>
      have hwin' : ((profiledGuardedFirstRightMonitorAt A key).restartAt
          start).WinsPlay
          (treePlay tree env) := by
        simpa [monitor, profiledRightRestartRootMonitor,
          profiledRightFamilyRootMonitor] using hwin
      have hsafe := profiledGuardedFirstRight_targetsSafe_of_restartAt_wins A
        key start (treePlay tree env) hwin' n row
      exact profiledBankLeftRootOfFirstRightCertificate A
        (output.target row)
        ((((profiledGuardedFirstRightMonitorAt A key).restartAt start).run
          (treePlay tree env) n).2.1) row letter hsafe.1 hsafe.2
  | inr bank =>
      have hwin' : ((profiledBankRightMonitor A bank).restartAt start).WinsPlay
          (treePlay tree env) := by
        simpa [monitor, profiledRightRestartRootMonitor,
          profiledRightFamilyRootMonitor] using hwin
      have hsafe := profiledBankRight_targetsSafe_of_restartAt_wins A
        bank start (treePlay tree env) hwin' n row
      exact profiledBankLeftMacroOfRightCertificate A bank
        (output.target row)
        ((((profiledBankRightMonitor A bank).restartAt start).run
          (treePlay tree env) n).2.1) row letter hsafe.1 hsafe.2

/-- Mixed left-family mirror. -/
noncomputable def profiledLeftFamilyRootChild
    (source : I → ProfiledLeftRestartRoot A)
    (family : TransitionRationalTree In₂
      (NarrowedBlockLabel (I × In₁) In₂ (ProfiledLeftReceiverOutput A) Out₂
        (finiteRootFamilyMonitor
          (profiledLeftFamilyRootMonitors A source)).State))
    (hfamily : NarrowedAllThreadsWin
      (finiteRootFamilyMonitor (profiledLeftFamilyRootMonitors A source))
      family.labeledTree)
    (index : I) (env : Nat → In₁ × In₂) (n : Nat)
    (row : PairedEntryRow) : ProfiledBankRightMacro A := by
  let monitor := profiledLeftRestartRootMonitor A (source index)
  let member := finiteRootMemberController
    (profiledLeftFamilyRootMonitors A source) family index
  let tree := narrowedInducedTree monitor member.labeledTree
  have hmember : NarrowedAllThreadsWin monitor member.labeledTree :=
    finiteRootMemberController_allThreadsWin
      (profiledLeftFamilyRootMonitors A source) family hfamily index
  have htree :=
    narrowedInducedTree_winningTree_of_allThreadsWin monitor hmember
  have hwin : monitor.WinsPlay (treePlay tree env) :=
    (monitor.lift_winningTree_iff tree).mp htree env
  let output := (treePlay tree env n).2.1
  let letter := profiledLeftPhysicalLetter A (treePlay tree env n)
  rcases hsource : source index with ⟨kind, start⟩
  dsimp [monitor, profiledLeftRestartRootMonitor] at hwin
  rw [hsource] at hwin
  cases kind with
  | inl key =>
      have hwin' : ((profiledGuardedFirstLeftMonitorAt A key).restartAt
          start).WinsPlay
          (treePlay tree env) := by
        simpa [monitor, profiledLeftRestartRootMonitor,
          profiledLeftFamilyRootMonitor] using hwin
      have hsafe := profiledGuardedFirstLeft_targetsSafe_of_restartAt_wins A
        key start (treePlay tree env) hwin' n row
      exact profiledBankRightRootOfFirstLeftCertificate A
        (output.target row)
        ((((profiledGuardedFirstLeftMonitorAt A key).restartAt start).run
          (treePlay tree env) n).2.1) row letter hsafe.1 hsafe.2
  | inr bank =>
      have hwin' : ((profiledBankLeftMonitor A bank).restartAt start).WinsPlay
          (treePlay tree env) := by
        simpa [monitor, profiledLeftRestartRootMonitor,
          profiledLeftFamilyRootMonitor] using hwin
      have hsafe := profiledBankLeft_targetsSafe_of_restartAt_wins A
        bank start (treePlay tree env) hwin' n row
      exact profiledBankRightMacroOfLeftCertificate A bank
        (output.target row)
        ((((profiledBankLeftMonitor A bank).restartAt start).run
          (treePlay tree env) n).2.1) row letter hsafe.1 hsafe.2

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁]
    [DecidableEq In₂] in
theorem profiledBankLeftMacroOfRightCertificate_bank
    (source : ProfiledBankRightMacro A)
    (target : PairedProfiledTreeState A)
    (scan : PairedRightScanState A) (row : PairedEntryRow)
    (letter : PairedRightBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (herase : erasePairedProfiledState A target =
      pairedRightCloseTarget A scan row letter)
    (hallowed : PairedProfiledRationalPolicy.Allowed A
      (feasibleProfiledPolicy A source.1) (.inr (.inl source.2.1)) target) :
    (profiledBankLeftMacroOfRightCertificate A source target scan row letter
      herase hallowed).1 = source.1 := by
  cases target with
  | inl trivial =>
      cases row <;>
        simp [erasePairedProfiledState, pairedRightCloseTarget] at herase
  | inr live =>
      cases live with
      | inl rightLive =>
          cases row <;>
            simp [erasePairedProfiledState, pairedRightCloseTarget] at herase
      | inr leftLive => rfl

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁]
    [DecidableEq In₂] in
theorem profiledBankRightMacroOfLeftCertificate_bank
    (source : ProfiledBankLeftMacro A)
    (target : PairedProfiledTreeState A)
    (scan : PairedLeftScanState A) (row : PairedEntryRow)
    (letter : PairedLeftBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (herase : erasePairedProfiledState A target =
      pairedLeftCloseTarget A scan row letter)
    (hallowed : PairedProfiledRationalPolicy.Allowed A
      (feasibleProfiledPolicy A source.1) (.inr (.inr source.2.1)) target) :
    (profiledBankRightMacroOfLeftCertificate A source target scan row letter
      herase hallowed).1 = source.1 := by
  cases target with
  | inl trivial =>
      cases row <;>
        simp [erasePairedProfiledState, pairedLeftCloseTarget] at herase
  | inr live =>
      cases live with
      | inl rightLive => rfl
      | inr leftLive =>
          cases row <;>
            simp [erasePairedProfiledState, pairedLeftCloseTarget] at herase

/-- Every certificate emitted by one projection of a winning simultaneous
right-family controller is a genuine next left macro. -/
noncomputable def profiledBankRightRootFamilyChild
    (source : I → ProfiledBankRightMacro A)
    (family : TransitionRationalTree In₁
      (NarrowedBlockLabel (I × In₂) In₁ (ProfiledRightReceiverOutput A) Out₁
        (finiteRootFamilyMonitor
          (profiledBankRightRootMonitors A source)).State))
    (hfamily : NarrowedAllThreadsWin
      (finiteRootFamilyMonitor (profiledBankRightRootMonitors A source))
      family.labeledTree)
    (index : I) (env : Nat → In₂ × In₁) (n : Nat)
    (row : PairedEntryRow) : ProfiledBankLeftMacro A := by
  let monitor := profiledBankRightMonitor A (source index)
  let member := finiteRootMemberController
    (profiledBankRightRootMonitors A source) family index
  let tree := narrowedInducedTree monitor member.labeledTree
  have hmember : NarrowedAllThreadsWin monitor member.labeledTree :=
    finiteRootMemberController_allThreadsWin
      (profiledBankRightRootMonitors A source) family hfamily index
  have htree :=
    narrowedInducedTree_winningTree_of_allThreadsWin monitor hmember
  have hwin : monitor.WinsPlay (treePlay tree env) :=
    (monitor.lift_winningTree_iff tree).mp htree env
  let output := (treePlay tree env n).2.1
  let letter := profiledRightPhysicalLetter A (treePlay tree env n)
  have hsafe := profiledRight_targetsSafe_of_wins A
    (feasibleProfiledPolicy A (source index).1)
    (source index).2.1.1.1 (source index).2.1.1.2 (source index).2.1.2
    (treePlay tree env) hwin n row
  exact profiledBankLeftMacroOfRightCertificate A (source index)
    (output.target row)
    ((monitor.run (treePlay tree env) n).2.1) row letter hsafe.1 hsafe.2

omit [Inhabited I] [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- The next macro remains in the selected member's paired-policy component;
no policy identity can be invented by the family handoff. -/
@[simp] theorem profiledBankRightRootFamilyChild_bank
    (source : I → ProfiledBankRightMacro A)
    (family : TransitionRationalTree In₁
      (NarrowedBlockLabel (I × In₂) In₁ (ProfiledRightReceiverOutput A) Out₁
        (finiteRootFamilyMonitor
          (profiledBankRightRootMonitors A source)).State))
    (hfamily : NarrowedAllThreadsWin
      (finiteRootFamilyMonitor (profiledBankRightRootMonitors A source))
      family.labeledTree)
    (index : I) (env : Nat → In₂ × In₁) (n : Nat)
    (row : PairedEntryRow) :
    (profiledBankRightRootFamilyChild A source family hfamily index env n row).1 =
      (source index).1 := by
  unfold profiledBankRightRootFamilyChild
  dsimp only
  apply profiledBankLeftMacroOfRightCertificate_bank

/-- Left-family mirror. -/
noncomputable def profiledBankLeftRootFamilyChild
    (source : I → ProfiledBankLeftMacro A)
    (family : TransitionRationalTree In₂
      (NarrowedBlockLabel (I × In₁) In₂ (ProfiledLeftReceiverOutput A) Out₂
        (finiteRootFamilyMonitor
          (profiledBankLeftRootMonitors A source)).State))
    (hfamily : NarrowedAllThreadsWin
      (finiteRootFamilyMonitor (profiledBankLeftRootMonitors A source))
      family.labeledTree)
    (index : I) (env : Nat → In₁ × In₂) (n : Nat)
    (row : PairedEntryRow) : ProfiledBankRightMacro A := by
  let monitor := profiledBankLeftMonitor A (source index)
  let member := finiteRootMemberController
    (profiledBankLeftRootMonitors A source) family index
  let tree := narrowedInducedTree monitor member.labeledTree
  have hmember : NarrowedAllThreadsWin monitor member.labeledTree :=
    finiteRootMemberController_allThreadsWin
      (profiledBankLeftRootMonitors A source) family hfamily index
  have htree :=
    narrowedInducedTree_winningTree_of_allThreadsWin monitor hmember
  have hwin : monitor.WinsPlay (treePlay tree env) :=
    (monitor.lift_winningTree_iff tree).mp htree env
  let output := (treePlay tree env n).2.1
  let letter := profiledLeftPhysicalLetter A (treePlay tree env n)
  have hsafe := profiledLeft_targetsSafe_of_wins A
    (feasibleProfiledPolicy A (source index).1)
    (source index).2.1.1.1 (source index).2.1.1.2 (source index).2.1.2
    (treePlay tree env) hwin n row
  exact profiledBankRightMacroOfLeftCertificate A (source index)
    (output.target row)
    ((monitor.run (treePlay tree env) n).2.1) row letter hsafe.1 hsafe.2

omit [Inhabited I] [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem profiledBankLeftRootFamilyChild_bank
    (source : I → ProfiledBankLeftMacro A)
    (family : TransitionRationalTree In₂
      (NarrowedBlockLabel (I × In₁) In₂ (ProfiledLeftReceiverOutput A) Out₂
        (finiteRootFamilyMonitor
          (profiledBankLeftRootMonitors A source)).State))
    (hfamily : NarrowedAllThreadsWin
      (finiteRootFamilyMonitor (profiledBankLeftRootMonitors A source))
      family.labeledTree)
    (index : I) (env : Nat → In₁ × In₂) (n : Nat)
    (row : PairedEntryRow) :
    (profiledBankLeftRootFamilyChild A source family hfamily index env n row).1 =
      (source index).1 := by
  unfold profiledBankLeftRootFamilyChild
  dsimp only
  apply profiledBankRightMacroOfLeftCertificate_bank

end


end


end DetParityAutomaton

end DistributedSynthesis
