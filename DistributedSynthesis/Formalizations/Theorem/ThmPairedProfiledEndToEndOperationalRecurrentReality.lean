/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledEndToEndOperationalFirstReality

/-!
# Reality of recurrent fixed-policy controller prefixes

The recurrent banks on both sides are instances of one fixed-policy
construction.  We prove staging once for that construction; the four
origin/orientation wrappers then inherit it definitionally.
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
variable {initialState : PairedProfiledTreeState A}
variable (policy :
  (pairedProfiledEntryRunAutomaton A initialState).RationalTransitionPolicy)

/-! ## Generic right-oriented fixed-policy controller -/

abbrev ProfiledPolicyRightFiniteState
    (source : ProfiledPolicyRightMacro A policy) :=
  (profiledPolicyRightController A policy source).Control ×
    (profiledPolicyRightMonitor A policy source).State

noncomputable def stepProfiledPolicyRightFiniteState
    (source : ProfiledPolicyRightMacro A policy)
    (state : ProfiledPolicyRightFiniteState A policy source)
    (move : In₂ × In₁) : ProfiledPolicyRightFiniteState A policy source :=
  let controller := profiledPolicyRightController A policy source
  let monitor := profiledPolicyRightMonitor A policy source
  let label := controller.labelOf state.1
  (controller.step state.1 move.2,
    monitor.step state.2 (narrowedRecord monitor label state.2 move))

noncomputable def profiledPolicyRightFiniteStateAfter
    (source : ProfiledPolicyRightMacro A policy) (past : List (In₂ × In₁)) :
    ProfiledPolicyRightFiniteState A policy source :=
  past.foldl (stepProfiledPolicyRightFiniteState A policy source)
    ((profiledPolicyRightController A policy source).initial,
      (profiledPolicyRightMonitor A policy source).initial)

theorem profiledPolicyRightFiniteStateAfter_eq
    (source : ProfiledPolicyRightMacro A policy) : ∀ past : List (In₂ × In₁),
    profiledPolicyRightFiniteStateAfter A policy source past =
      ((profiledPolicyRightController A policy source).controlAt
          (senderWord past),
        narrowedControl (profiledPolicyRightMonitor A policy source)
          (profiledPolicyRightController A policy source).labeledTree past) := by
  intro past
  induction past using List.reverseRecOn with
  | nil => rfl
  | append_singleton past move ih =>
      rw [profiledPolicyRightFiniteStateAfter, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      change stepProfiledPolicyRightFiniteState A policy source
        (profiledPolicyRightFiniteStateAfter A policy source past) move = _
      rw [ih, senderWord_append, TransitionRationalTree.controlAt_append,
        narrowedControl_append]
      rfl

private theorem profiledPolicyRight_treePlay_at_prefix
    (source : ProfiledPolicyRightMacro A policy)
    (past : List (In₂ × In₁)) (move : In₂ × In₁) :
    let monitor := profiledPolicyRightMonitor A policy source
    let controller := profiledPolicyRightController A policy source
    let env := omegaOfList (past ++ [move])
    treePlay (narrowedInducedTree monitor controller.labeledTree) env
        past.length =
      narrowedRecord monitor
        (controller.labelOf (controller.controlAt (senderWord past)))
        (narrowedControl monitor controller.labeledTree past) move := by
  dsimp only
  let finiteWord := past ++ [move]
  let env : Nat → In₂ × In₁ := omegaOfList finiteWord
  have hpast : omegaPrefix env past.length = past := by
    apply List.ext_get
    · simp [omegaPrefix]
    · intro n hnLeft hnRight
      rw [List.get_eq_getElem, List.get_eq_getElem]
      simp only [omegaPrefix, List.getElem_ofFn]
      have hnPrefix : n < finiteWord.length := by simp [finiteWord]; omega
      change omegaOfList finiteWord n = past[n]
      rw [omegaOfList_eq_getElem finiteWord n hnPrefix]
      simp [finiteWord, hnRight]
  simp [treePlay, narrowedInducedTree, blockLabelApply, narrowedRecord,
    TransitionRationalTree.labeledTree, branchNode_eq_omegaPrefix,
    hpast, senderWord, env, finiteWord]

theorem profiledPolicyRight_real_close_staged
    (source : ProfiledPolicyRightMacro A policy) (row : PairedEntryRow)
    (past : List (In₂ × In₁)) (move : In₂ × In₁) :
    (stepProfiledPolicyRightReceiverFor A policy source
      (profiledPolicyRightFiniteStateAfter A policy source past).1 row
      (profiledPolicyRightFiniteStateAfter A policy source past).2 move).2.2.isSome := by
  rw [profiledPolicyRightFiniteStateAfter_eq A policy source]
  let monitor := profiledPolicyRightMonitor A policy source
  let controller := profiledPolicyRightController A policy source
  let env : Nat → In₂ × In₁ := omegaOfList (past ++ [move])
  let tree := narrowedInducedTree monitor controller.labeledTree
  have htree := narrowedInducedTree_winningTree_of_allThreadsWin monitor
    (profiledPolicyRightController_wins A policy source)
  have hwin : monitor.WinsPlay (treePlay tree env) :=
    (monitor.lift_winningTree_iff tree).mp htree env
  have hsafe := profiledRight_targetsSafe_of_wins A policy
    source.1.1.1 source.1.1.2 source.1.2
    (treePlay tree env) hwin past.length row
  have hat := profiledPolicyRight_treePlay_at_prefix A policy source past move
  change treePlay tree env past.length = _ at hat
  rw [hat] at hsafe
  have hpast : omegaPrefix env past.length = past := by
    apply List.ext_get
    · simp [omegaPrefix]
    · intro n hnLeft hnRight
      rw [List.get_eq_getElem, List.get_eq_getElem]
      simp only [omegaPrefix, List.getElem_ofFn]
      have hnPrefix : n < (past ++ [move]).length := by simp; omega
      change omegaOfList (past ++ [move]) n = past[n]
      rw [omegaOfList_eq_getElem (past ++ [move]) n hnPrefix]
      simp [hnRight]
  have hrun : monitor.run (treePlay tree env) past.length =
      narrowedControl monitor controller.labeledTree past := by
    rw [← monitor.lift_control_branchNode tree env,
      lift_control_narrowedInducedTree, branchNode_eq_omegaPrefix, hpast]
  rw [hrun] at hsafe
  apply stepProfiledPolicyRightReceiverFor_staged_of_safe A policy
  simpa [narrowedRecord] using hsafe

/-- A real recurrent right close exposes both the staged macro and the exact
fixed-policy edge to its profiled state.  This is stronger than the
`isSome` closure fact and is the form consumed by the epoch-state thread. -/
theorem profiledPolicyRight_real_close_allowed
    (source : ProfiledPolicyRightMacro A policy) (row : PairedEntryRow)
    (past : List (In₂ × In₁)) (move : In₂ × In₁) :
    ∃ target : ProfiledPolicyLeftMacro A policy,
      (stepProfiledPolicyRightReceiverFor A policy source
        (profiledPolicyRightFiniteStateAfter A policy source past).1 row
        (profiledPolicyRightFiniteStateAfter A policy source past).2
        move).2.2 = some target ∧
      PairedProfiledRationalPolicy.Allowed A policy
        (.inr (.inl source.1)) (.inr (.inr target.1)) := by
  have hsome := profiledPolicyRight_real_close_staged A policy source row past
    move
  rw [Option.isSome_iff_exists] at hsome
  rcases hsome with ⟨target, hstage⟩
  exact ⟨target, hstage,
    stepProfiledPolicyRightReceiverFor_allowed_of_staged A policy source
      (profiledPolicyRightFiniteStateAfter A policy source past).1 row
      (profiledPolicyRightFiniteStateAfter A policy source past).2 move target
      hstage⟩

/-- A pending opposite-orientation profile stored at a real prefix of a
fixed-policy right controller is honored on the following physical round. -/
theorem profiledPolicyRight_real_overlap
    (source : ProfiledPolicyRightMacro A policy) (row : PairedEntryRow)
    (past : List (In₂ × In₁)) (move : In₂ × In₁)
    (expected : LeftInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁))
    (hpending :
      (profiledPolicyRightFiniteStateAfter A policy source past).2.2.2.1 row =
        some expected) :
    pairedRightClosingForRow row
        (((profiledPolicyRightController A policy source).labelOf
          (profiledPolicyRightFiniteStateAfter A policy source past).1).2
          (profiledPolicyRightFiniteStateAfter A policy source past).2
          move).physical =
      expected (move.2, move.1) := by
  rw [profiledPolicyRightFiniteStateAfter_eq A policy source] at hpending ⊢
  let monitor := profiledPolicyRightMonitor A policy source
  let controller := profiledPolicyRightController A policy source
  let env : Nat → In₂ × In₁ := omegaOfList (past ++ [move])
  let tree := narrowedInducedTree monitor controller.labeledTree
  have htree := narrowedInducedTree_winningTree_of_allThreadsWin monitor
    (profiledPolicyRightController_wins A policy source)
  have hwin : monitor.WinsPlay (treePlay tree env) :=
    (monitor.lift_winningTree_iff tree).mp htree env
  have hoverlap := profiledRight_overlap_of_wins A policy
    source.1.1.1 source.1.1.2 source.1.2
    (treePlay tree env) hwin past.length row expected
  have hat := profiledPolicyRight_treePlay_at_prefix A policy source past move
  change treePlay tree env past.length = _ at hat
  rw [hat] at hoverlap
  have hpast : omegaPrefix env past.length = past := by
    apply List.ext_get
    · simp [omegaPrefix]
    · intro n hnLeft hnRight
      rw [List.get_eq_getElem, List.get_eq_getElem]
      simp only [omegaPrefix, List.getElem_ofFn]
      have hnPrefix : n < (past ++ [move]).length := by simp; omega
      change omegaOfList (past ++ [move]) n = past[n]
      rw [omegaOfList_eq_getElem (past ++ [move]) n hnPrefix]
      simp [hnRight]
  have hrun : monitor.run (treePlay tree env) past.length =
      narrowedControl monitor controller.labeledTree past := by
    rw [← monitor.lift_control_branchNode tree env,
      lift_control_narrowedInducedTree, branchNode_eq_omegaPrefix, hpast]
  apply hoverlap
  rw [hrun]
  exact hpending

/-- The root of a fixed-policy right controller realizes the action profile
stored in its macro. -/
theorem profiledPolicyRight_root_profile
    (source : ProfiledPolicyRightMacro A policy) (move : In₂ × In₁) :
    pairedRightInformedForRow .first
        (((profiledPolicyRightController A policy source).labelOf
          (profiledPolicyRightController A policy source).initial).2
          (profiledPolicyRightMonitor A policy source).initial move).physical =
      source.1.2 move := by
  let monitor := profiledPolicyRightMonitor A policy source
  let controller := profiledPolicyRightController A policy source
  let env : Nat → In₂ × In₁ := fun _ => move
  let tree := narrowedInducedTree monitor controller.labeledTree
  have htree := narrowedInducedTree_winningTree_of_allThreadsWin monitor
    (profiledPolicyRightController_wins A policy source)
  have hwin : monitor.WinsPlay (treePlay tree env) :=
    (monitor.lift_winningTree_iff tree).mp htree env
  have hroot := profiledRight_rootProfile_of_wins A policy
    source.1.1.1 source.1.1.2 source.1.2 (treePlay tree env) hwin
  simpa [treePlay, tree, env, narrowedInducedTree, blockLabelApply,
    narrowedRecord, TransitionRationalTree.labeledTree, narrowedControl,
    narrowedControlAux, controller, monitor] using hroot

/-! ## Generic left-oriented fixed-policy controller -/

abbrev ProfiledPolicyLeftFiniteState
    (source : ProfiledPolicyLeftMacro A policy) :=
  (profiledPolicyLeftController A policy source).Control ×
    (profiledPolicyLeftMonitor A policy source).State

noncomputable def stepProfiledPolicyLeftFiniteState
    (source : ProfiledPolicyLeftMacro A policy)
    (state : ProfiledPolicyLeftFiniteState A policy source)
    (move : In₁ × In₂) : ProfiledPolicyLeftFiniteState A policy source :=
  let controller := profiledPolicyLeftController A policy source
  let monitor := profiledPolicyLeftMonitor A policy source
  let label := controller.labelOf state.1
  (controller.step state.1 move.2,
    monitor.step state.2 (narrowedRecord monitor label state.2 move))

noncomputable def profiledPolicyLeftFiniteStateAfter
    (source : ProfiledPolicyLeftMacro A policy) (past : List (In₁ × In₂)) :
    ProfiledPolicyLeftFiniteState A policy source :=
  past.foldl (stepProfiledPolicyLeftFiniteState A policy source)
    ((profiledPolicyLeftController A policy source).initial,
      (profiledPolicyLeftMonitor A policy source).initial)

theorem profiledPolicyLeftFiniteStateAfter_eq
    (source : ProfiledPolicyLeftMacro A policy) : ∀ past : List (In₁ × In₂),
    profiledPolicyLeftFiniteStateAfter A policy source past =
      ((profiledPolicyLeftController A policy source).controlAt
          (senderWord past),
        narrowedControl (profiledPolicyLeftMonitor A policy source)
          (profiledPolicyLeftController A policy source).labeledTree past) := by
  intro past
  induction past using List.reverseRecOn with
  | nil => rfl
  | append_singleton past move ih =>
      rw [profiledPolicyLeftFiniteStateAfter, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      change stepProfiledPolicyLeftFiniteState A policy source
        (profiledPolicyLeftFiniteStateAfter A policy source past) move = _
      rw [ih, senderWord_append, TransitionRationalTree.controlAt_append,
        narrowedControl_append]
      rfl

private theorem profiledPolicyLeft_treePlay_at_prefix
    (source : ProfiledPolicyLeftMacro A policy)
    (past : List (In₁ × In₂)) (move : In₁ × In₂) :
    let monitor := profiledPolicyLeftMonitor A policy source
    let controller := profiledPolicyLeftController A policy source
    let env := omegaOfList (past ++ [move])
    treePlay (narrowedInducedTree monitor controller.labeledTree) env
        past.length =
      narrowedRecord monitor
        (controller.labelOf (controller.controlAt (senderWord past)))
        (narrowedControl monitor controller.labeledTree past) move := by
  dsimp only
  let finiteWord := past ++ [move]
  let env : Nat → In₁ × In₂ := omegaOfList finiteWord
  have hpast : omegaPrefix env past.length = past := by
    apply List.ext_get
    · simp [omegaPrefix]
    · intro n hnLeft hnRight
      rw [List.get_eq_getElem, List.get_eq_getElem]
      simp only [omegaPrefix, List.getElem_ofFn]
      have hnPrefix : n < finiteWord.length := by simp [finiteWord]; omega
      change omegaOfList finiteWord n = past[n]
      rw [omegaOfList_eq_getElem finiteWord n hnPrefix]
      simp [finiteWord, hnRight]
  simp [treePlay, narrowedInducedTree, blockLabelApply, narrowedRecord,
    TransitionRationalTree.labeledTree, branchNode_eq_omegaPrefix,
    hpast, senderWord, env, finiteWord]

theorem profiledPolicyLeft_real_close_staged
    (source : ProfiledPolicyLeftMacro A policy) (row : PairedEntryRow)
    (past : List (In₁ × In₂)) (move : In₁ × In₂) :
    (stepProfiledPolicyLeftReceiverFor A policy source
      (profiledPolicyLeftFiniteStateAfter A policy source past).1 row
      (profiledPolicyLeftFiniteStateAfter A policy source past).2 move).2.2.isSome := by
  rw [profiledPolicyLeftFiniteStateAfter_eq A policy source]
  let monitor := profiledPolicyLeftMonitor A policy source
  let controller := profiledPolicyLeftController A policy source
  let env : Nat → In₁ × In₂ := omegaOfList (past ++ [move])
  let tree := narrowedInducedTree monitor controller.labeledTree
  have htree := narrowedInducedTree_winningTree_of_allThreadsWin monitor
    (profiledPolicyLeftController_wins A policy source)
  have hwin : monitor.WinsPlay (treePlay tree env) :=
    (monitor.lift_winningTree_iff tree).mp htree env
  have hsafe := profiledLeft_targetsSafe_of_wins A policy
    source.1.1.1 source.1.1.2 source.1.2
    (treePlay tree env) hwin past.length row
  have hat := profiledPolicyLeft_treePlay_at_prefix A policy source past move
  change treePlay tree env past.length = _ at hat
  rw [hat] at hsafe
  have hpast : omegaPrefix env past.length = past := by
    apply List.ext_get
    · simp [omegaPrefix]
    · intro n hnLeft hnRight
      rw [List.get_eq_getElem, List.get_eq_getElem]
      simp only [omegaPrefix, List.getElem_ofFn]
      have hnPrefix : n < (past ++ [move]).length := by simp; omega
      change omegaOfList (past ++ [move]) n = past[n]
      rw [omegaOfList_eq_getElem (past ++ [move]) n hnPrefix]
      simp [hnRight]
  have hrun : monitor.run (treePlay tree env) past.length =
      narrowedControl monitor controller.labeledTree past := by
    rw [← monitor.lift_control_branchNode tree env,
      lift_control_narrowedInducedTree, branchNode_eq_omegaPrefix, hpast]
  rw [hrun] at hsafe
  apply stepProfiledPolicyLeftReceiverFor_staged_of_safe A policy
  simpa [narrowedRecord] using hsafe

/-- Process-swapped fixed-policy edge exposed by a real recurrent left
close. -/
theorem profiledPolicyLeft_real_close_allowed
    (source : ProfiledPolicyLeftMacro A policy) (row : PairedEntryRow)
    (past : List (In₁ × In₂)) (move : In₁ × In₂) :
    ∃ target : ProfiledPolicyRightMacro A policy,
      (stepProfiledPolicyLeftReceiverFor A policy source
        (profiledPolicyLeftFiniteStateAfter A policy source past).1 row
        (profiledPolicyLeftFiniteStateAfter A policy source past).2
        move).2.2 = some target ∧
      PairedProfiledRationalPolicy.Allowed A policy
        (.inr (.inr source.1)) (.inr (.inl target.1)) := by
  have hsome := profiledPolicyLeft_real_close_staged A policy source row past
    move
  rw [Option.isSome_iff_exists] at hsome
  rcases hsome with ⟨target, hstage⟩
  exact ⟨target, hstage,
    stepProfiledPolicyLeftReceiverFor_allowed_of_staged A policy source
      (profiledPolicyLeftFiniteStateAfter A policy source past).1 row
      (profiledPolicyLeftFiniteStateAfter A policy source past).2 move target
      hstage⟩

/-- Left-oriented mirror of `profiledPolicyRight_real_overlap`. -/
theorem profiledPolicyLeft_real_overlap
    (source : ProfiledPolicyLeftMacro A policy) (row : PairedEntryRow)
    (past : List (In₁ × In₂)) (move : In₁ × In₂)
    (expected : RightInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂))
    (hpending :
      (profiledPolicyLeftFiniteStateAfter A policy source past).2.2.2.1 row =
        some expected) :
    pairedLeftClosingForRow row
        (((profiledPolicyLeftController A policy source).labelOf
          (profiledPolicyLeftFiniteStateAfter A policy source past).1).2
          (profiledPolicyLeftFiniteStateAfter A policy source past).2
          move).physical =
      expected (move.2, move.1) := by
  rw [profiledPolicyLeftFiniteStateAfter_eq A policy source] at hpending ⊢
  let monitor := profiledPolicyLeftMonitor A policy source
  let controller := profiledPolicyLeftController A policy source
  let env : Nat → In₁ × In₂ := omegaOfList (past ++ [move])
  let tree := narrowedInducedTree monitor controller.labeledTree
  have htree := narrowedInducedTree_winningTree_of_allThreadsWin monitor
    (profiledPolicyLeftController_wins A policy source)
  have hwin : monitor.WinsPlay (treePlay tree env) :=
    (monitor.lift_winningTree_iff tree).mp htree env
  have hoverlap := profiledLeft_overlap_of_wins A policy
    source.1.1.1 source.1.1.2 source.1.2
    (treePlay tree env) hwin past.length row expected
  have hat := profiledPolicyLeft_treePlay_at_prefix A policy source past move
  change treePlay tree env past.length = _ at hat
  rw [hat] at hoverlap
  have hpast : omegaPrefix env past.length = past := by
    apply List.ext_get
    · simp [omegaPrefix]
    · intro n hnLeft hnRight
      rw [List.get_eq_getElem, List.get_eq_getElem]
      simp only [omegaPrefix, List.getElem_ofFn]
      have hnPrefix : n < (past ++ [move]).length := by simp; omega
      change omegaOfList (past ++ [move]) n = past[n]
      rw [omegaOfList_eq_getElem (past ++ [move]) n hnPrefix]
      simp [hnRight]
  have hrun : monitor.run (treePlay tree env) past.length =
      narrowedControl monitor controller.labeledTree past := by
    rw [← monitor.lift_control_branchNode tree env,
      lift_control_narrowedInducedTree, branchNode_eq_omegaPrefix, hpast]
  apply hoverlap
  rw [hrun]
  exact hpending

/-- Left mirror of `profiledPolicyRight_root_profile`. -/
theorem profiledPolicyLeft_root_profile
    (source : ProfiledPolicyLeftMacro A policy) (move : In₁ × In₂) :
    pairedLeftInformedForRow .first
        (((profiledPolicyLeftController A policy source).labelOf
          (profiledPolicyLeftController A policy source).initial).2
          (profiledPolicyLeftMonitor A policy source).initial move).physical =
      source.1.2 move := by
  let monitor := profiledPolicyLeftMonitor A policy source
  let controller := profiledPolicyLeftController A policy source
  let env : Nat → In₁ × In₂ := fun _ => move
  let tree := narrowedInducedTree monitor controller.labeledTree
  have htree := narrowedInducedTree_winningTree_of_allThreadsWin monitor
    (profiledPolicyLeftController_wins A policy source)
  have hwin : monitor.WinsPlay (treePlay tree env) :=
    (monitor.lift_winningTree_iff tree).mp htree env
  have hroot := profiledLeft_rootProfile_of_wins A policy
    source.1.1.1 source.1.1.2 source.1.2 (treePlay tree env) hwin
  simpa [treePlay, tree, env, narrowedInducedTree, blockLabelApply,
    narrowedRecord, TransitionRationalTree.labeledTree, narrowedControl,
    narrowedControlAux, controller, monitor] using hroot

/-! ## The fixed-policy alternating boundary diamond -/

/-- After a real right prefix stages a left target, the old right closing
output and the fresh left root output agree on the following round. -/
theorem profiledPolicyRight_real_boundary_output
    (source : ProfiledPolicyRightMacro A policy) (row : PairedEntryRow)
    (past : List (In₂ × In₁)) (stagingMove : In₂ × In₁)
    (move : In₁ × In₂) :
    ∃ target : ProfiledPolicyLeftMacro A policy,
      (stepProfiledPolicyRightReceiverFor A policy source
        (profiledPolicyRightFiniteStateAfter A policy source past).1 row
        (profiledPolicyRightFiniteStateAfter A policy source past).2
        stagingMove).2.2 = some target ∧
      pairedRightClosingForRow row
          (((profiledPolicyRightController A policy source).labelOf
            (profiledPolicyRightFiniteStateAfter A policy source
              (past ++ [stagingMove])).1).2
            (profiledPolicyRightFiniteStateAfter A policy source
              (past ++ [stagingMove])).2 (move.2, move.1)).physical =
        pairedLeftInformedForRow .first
          (((profiledPolicyLeftController A policy target).labelOf
            (profiledPolicyLeftController A policy target).initial).2
            (profiledPolicyLeftMonitor A policy target).initial move).physical := by
  classical
  have hsome := profiledPolicyRight_real_close_staged A policy source row past
    stagingMove
  rw [Option.isSome_iff_exists] at hsome
  rcases hsome with ⟨target, hstage⟩
  refine ⟨target, hstage, ?_⟩
  have hpendingStep :=
    stepProfiledPolicyRightReceiverFor_pending_of_staged A policy source
      (profiledPolicyRightFiniteStateAfter A policy source past).1 row
      (profiledPolicyRightFiniteStateAfter A policy source past).2 stagingMove
      target hstage
  have hafter :
      profiledPolicyRightFiniteStateAfter A policy source
          (past ++ [stagingMove]) =
        stepProfiledPolicyRightFiniteState A policy source
          (profiledPolicyRightFiniteStateAfter A policy source past)
          stagingMove := by
    simp [profiledPolicyRightFiniteStateAfter, List.foldl_append]
  have hpending :
      (profiledPolicyRightFiniteStateAfter A policy source
        (past ++ [stagingMove])).2.2.2.1 row = some target.1.2 := by
    rw [hafter]
    rw [stepProfiledPolicyRightReceiverFor_monitor] at hpendingStep
    simpa [stepProfiledPolicyRightFiniteState, narrowedRecord] using
      hpendingStep
  have hold := profiledPolicyRight_real_overlap A policy source row
    (past ++ [stagingMove]) (move.2, move.1) target.1.2 hpending
  have hfresh := profiledPolicyLeft_root_profile A policy target move
  exact hold.trans hfresh.symm

/-- Left-to-right mirror of `profiledPolicyRight_real_boundary_output`. -/
theorem profiledPolicyLeft_real_boundary_output
    (source : ProfiledPolicyLeftMacro A policy) (row : PairedEntryRow)
    (past : List (In₁ × In₂)) (stagingMove : In₁ × In₂)
    (move : In₂ × In₁) :
    ∃ target : ProfiledPolicyRightMacro A policy,
      (stepProfiledPolicyLeftReceiverFor A policy source
        (profiledPolicyLeftFiniteStateAfter A policy source past).1 row
        (profiledPolicyLeftFiniteStateAfter A policy source past).2
        stagingMove).2.2 = some target ∧
      pairedLeftClosingForRow row
          (((profiledPolicyLeftController A policy source).labelOf
            (profiledPolicyLeftFiniteStateAfter A policy source
              (past ++ [stagingMove])).1).2
            (profiledPolicyLeftFiniteStateAfter A policy source
              (past ++ [stagingMove])).2 (move.2, move.1)).physical =
        pairedRightInformedForRow .first
          (((profiledPolicyRightController A policy target).labelOf
            (profiledPolicyRightController A policy target).initial).2
            (profiledPolicyRightMonitor A policy target).initial move).physical := by
  classical
  have hsome := profiledPolicyLeft_real_close_staged A policy source row past
    stagingMove
  rw [Option.isSome_iff_exists] at hsome
  rcases hsome with ⟨target, hstage⟩
  refine ⟨target, hstage, ?_⟩
  have hpendingStep :=
    stepProfiledPolicyLeftReceiverFor_pending_of_staged A policy source
      (profiledPolicyLeftFiniteStateAfter A policy source past).1 row
      (profiledPolicyLeftFiniteStateAfter A policy source past).2 stagingMove
      target hstage
  have hafter :
      profiledPolicyLeftFiniteStateAfter A policy source
          (past ++ [stagingMove]) =
        stepProfiledPolicyLeftFiniteState A policy source
          (profiledPolicyLeftFiniteStateAfter A policy source past)
          stagingMove := by
    simp [profiledPolicyLeftFiniteStateAfter, List.foldl_append]
  have hpending :
      (profiledPolicyLeftFiniteStateAfter A policy source
        (past ++ [stagingMove])).2.2.2.1 row = some target.1.2 := by
    rw [hafter]
    rw [stepProfiledPolicyLeftReceiverFor_monitor] at hpendingStep
    simpa [stepProfiledPolicyLeftFiniteState, narrowedRecord] using
      hpendingStep
  have hold := profiledPolicyLeft_real_overlap A policy source row
    (past ++ [stagingMove]) (move.2, move.1) target.1.2 hpending
  have hfresh := profiledPolicyRight_root_profile A policy target move
  exact hold.trans hfresh.symm

/-! ## Exceptional first-block boundary diamonds -/

variable (package : PairedStrategyMemory.PairedInitialProfiledRationalPackage A)

/-- After a real exceptional first-right prefix stages its recurrent-left
target, its closing output agrees with that target's fresh root output on the
following physical round. -/
theorem endToEndFirstRight_real_boundary_output
    (key : EndToEndInitialLeftBoundaryKey A package) (row : PairedEntryRow)
    (past : List (In₂ × In₁)) (stagingMove : In₂ × In₁)
    (move : In₁ × In₂) :
    ∃ target : EndToEndGuardedRightRecurrentLeftMacro A
        (rightGuarded :=
          (endToEndInitialLeftBoundaryActivation A package key).policy),
      (stepEndToEndGuardedFirstRightReceiverFor A package key
        (endToEndFirstRightFiniteStateAfter A package key past).1 row
        (endToEndFirstRightFiniteStateAfter A package key past).2
        stagingMove).2.2 = some target ∧
      pairedRightClosingForRow row
          (((endToEndInitialLeftBoundaryController A package key).labelOf
            (endToEndFirstRightFiniteStateAfter A package key
              (past ++ [stagingMove])).1).2
            (endToEndFirstRightFiniteStateAfter A package key
              (past ++ [stagingMove])).2 (move.2, move.1)).physical =
        pairedLeftInformedForRow .first
          (((profiledPolicyLeftController A (target.1.policy A)
            target.2).labelOf
              (profiledPolicyLeftController A (target.1.policy A)
                target.2).initial).2
            (profiledPolicyLeftMonitor A (target.1.policy A)
              target.2).initial move).physical := by
  classical
  have hsome := endToEndFirstRight_real_close_staged A package key row past
    stagingMove
  rw [Option.isSome_iff_exists] at hsome
  rcases hsome with ⟨target, hstage⟩
  refine ⟨target, hstage, ?_⟩
  have hpendingStep :=
    stepEndToEndGuardedFirstRightReceiverFor_pending_of_staged A package key
      (endToEndFirstRightFiniteStateAfter A package key past).1 row
      (endToEndFirstRightFiniteStateAfter A package key past).2 stagingMove
      target hstage
  have hafter :
      endToEndFirstRightFiniteStateAfter A package key
          (past ++ [stagingMove]) =
        stepEndToEndFirstRightFiniteState A package key
          (endToEndFirstRightFiniteStateAfter A package key past)
          stagingMove := by
    simp [endToEndFirstRightFiniteStateAfter, List.foldl_append]
  have hpending :
      (endToEndFirstRightFiniteStateAfter A package key
        (past ++ [stagingMove])).2.2.2.1 row = some target.2.1.2 := by
    rw [hafter]
    rw [stepEndToEndGuardedFirstRightReceiverFor_monitor] at hpendingStep
    simpa [stepEndToEndFirstRightFiniteState, narrowedRecord] using
      hpendingStep
  have hold := endToEndFirstRight_real_overlap A package key row
    (past ++ [stagingMove]) (move.2, move.1) target.2.1.2 hpending
  have hfresh := profiledPolicyLeft_root_profile A (target.1.policy A)
    target.2 move
  exact hold.trans hfresh.symm

/-- Process-swapped exceptional boundary diamond. -/
theorem endToEndFirstLeft_real_boundary_output
    (key : EndToEndInitialRightBoundaryKey A package) (row : PairedEntryRow)
    (past : List (In₁ × In₂)) (stagingMove : In₁ × In₂)
    (move : In₂ × In₁) :
    ∃ target : EndToEndGuardedLeftRecurrentRightMacro A
        (leftGuarded :=
          (endToEndInitialRightBoundaryActivation A package key).policy),
      (stepEndToEndGuardedFirstLeftReceiverFor A package key
        (endToEndFirstLeftFiniteStateAfter A package key past).1 row
        (endToEndFirstLeftFiniteStateAfter A package key past).2
        stagingMove).2.2 = some target ∧
      pairedLeftClosingForRow row
          (((endToEndInitialRightBoundaryController A package key).labelOf
            (endToEndFirstLeftFiniteStateAfter A package key
              (past ++ [stagingMove])).1).2
            (endToEndFirstLeftFiniteStateAfter A package key
              (past ++ [stagingMove])).2 (move.2, move.1)).physical =
        pairedRightInformedForRow .first
          (((profiledPolicyRightController A (target.1.policy A)
            target.2).labelOf
              (profiledPolicyRightController A (target.1.policy A)
                target.2).initial).2
            (profiledPolicyRightMonitor A (target.1.policy A)
              target.2).initial move).physical := by
  classical
  have hsome := endToEndFirstLeft_real_close_staged A package key row past
    stagingMove
  rw [Option.isSome_iff_exists] at hsome
  rcases hsome with ⟨target, hstage⟩
  refine ⟨target, hstage, ?_⟩
  have hpendingStep :=
    stepEndToEndGuardedFirstLeftReceiverFor_pending_of_staged A package key
      (endToEndFirstLeftFiniteStateAfter A package key past).1 row
      (endToEndFirstLeftFiniteStateAfter A package key past).2 stagingMove
      target hstage
  have hafter :
      endToEndFirstLeftFiniteStateAfter A package key
          (past ++ [stagingMove]) =
        stepEndToEndFirstLeftFiniteState A package key
          (endToEndFirstLeftFiniteStateAfter A package key past)
          stagingMove := by
    simp [endToEndFirstLeftFiniteStateAfter, List.foldl_append]
  have hpending :
      (endToEndFirstLeftFiniteStateAfter A package key
        (past ++ [stagingMove])).2.2.2.1 row = some target.2.1.2 := by
    rw [hafter]
    rw [stepEndToEndGuardedFirstLeftReceiverFor_monitor] at hpendingStep
    simpa [stepEndToEndFirstLeftFiniteState, narrowedRecord] using
      hpendingStep
  have hold := endToEndFirstLeft_real_overlap A package key row
    (past ++ [stagingMove]) (move.2, move.1) target.2.1.2 hpending
  have hfresh := profiledPolicyRight_root_profile A (target.1.policy A)
    target.2 move
  exact hold.trans hfresh.symm

/-! ## The four origin/orientation wrappers -/

theorem endToEndRightOriginRecurrentRight_real_close_staged
    (source : EndToEndRightOriginRecurrentRightMacro A package)
    (row : PairedEntryRow) (past : List (In₂ × In₁))
    (move : In₂ × In₁) :
    (stepEndToEndRightOriginRecurrentRightReceiverFor A package source
      (profiledPolicyRightFiniteStateAfter A (source.2.1.policy A)
        source.2.2 past).1 row
      (profiledPolicyRightFiniteStateAfter A (source.2.1.policy A)
        source.2.2 past).2 move).2.2.isSome := by
  simpa [stepEndToEndRightOriginRecurrentRightReceiverFor] using
    (profiledPolicyRight_real_close_staged A (source.2.1.policy A)
      source.2.2 row past move)

/-- The right-origin/right-orientation wrapper retains the concrete target
as a macro of the source child's policy, rather than merely exposing package
reachability. -/
theorem endToEndRightOriginRecurrentRight_real_close_allowed
    (source : EndToEndRightOriginRecurrentRightMacro A package)
    (row : PairedEntryRow) (past : List (In₂ × In₁))
    (move : In₂ × In₁) :
    ∃ target : ProfiledPolicyLeftMacro A (source.2.1.policy A),
      (stepEndToEndRightOriginRecurrentRightReceiverFor A package source
        (profiledPolicyRightFiniteStateAfter A (source.2.1.policy A)
          source.2.2 past).1 row
        (profiledPolicyRightFiniteStateAfter A (source.2.1.policy A)
          source.2.2 past).2 move).2.2 =
          some ⟨source.1, source.2.1, target⟩ ∧
      PairedProfiledRationalPolicy.Allowed A (source.2.1.policy A)
        (.inr (.inl source.2.2.1)) (.inr (.inr target.1)) := by
  rcases profiledPolicyRight_real_close_allowed A (source.2.1.policy A)
      source.2.2 row past move with ⟨target, htarget, hallowed⟩
  refine ⟨target, ?_, hallowed⟩
  simpa [stepEndToEndRightOriginRecurrentRightReceiverFor, htarget]

theorem endToEndRightOriginRecurrentLeft_real_close_staged
    (source : EndToEndRightOriginRecurrentLeftMacro A package)
    (row : PairedEntryRow) (past : List (In₁ × In₂))
    (move : In₁ × In₂) :
    (stepEndToEndRightOriginRecurrentLeftReceiverFor A package source
      (profiledPolicyLeftFiniteStateAfter A (source.2.1.policy A)
        source.2.2 past).1 row
      (profiledPolicyLeftFiniteStateAfter A (source.2.1.policy A)
        source.2.2 past).2 move).2.2.isSome := by
  simpa [stepEndToEndRightOriginRecurrentLeftReceiverFor] using
    (profiledPolicyLeft_real_close_staged A (source.2.1.policy A)
      source.2.2 row past move)

/-- Right-origin/left-orientation mirror with its exact fixed-policy edge. -/
theorem endToEndRightOriginRecurrentLeft_real_close_allowed
    (source : EndToEndRightOriginRecurrentLeftMacro A package)
    (row : PairedEntryRow) (past : List (In₁ × In₂))
    (move : In₁ × In₂) :
    ∃ target : ProfiledPolicyRightMacro A (source.2.1.policy A),
      (stepEndToEndRightOriginRecurrentLeftReceiverFor A package source
        (profiledPolicyLeftFiniteStateAfter A (source.2.1.policy A)
          source.2.2 past).1 row
        (profiledPolicyLeftFiniteStateAfter A (source.2.1.policy A)
          source.2.2 past).2 move).2.2 =
          some ⟨source.1, source.2.1, target⟩ ∧
      PairedProfiledRationalPolicy.Allowed A (source.2.1.policy A)
        (.inr (.inr source.2.2.1)) (.inr (.inl target.1)) := by
  rcases profiledPolicyLeft_real_close_allowed A (source.2.1.policy A)
      source.2.2 row past move with ⟨target, htarget, hallowed⟩
  refine ⟨target, ?_, hallowed⟩
  simpa [stepEndToEndRightOriginRecurrentLeftReceiverFor, htarget]

theorem endToEndLeftOriginRecurrentRight_real_close_staged
    (source : EndToEndLeftOriginRecurrentRightMacro A package)
    (row : PairedEntryRow) (past : List (In₂ × In₁))
    (move : In₂ × In₁) :
    (stepEndToEndLeftOriginRecurrentRightReceiverFor A package source
      (profiledPolicyRightFiniteStateAfter A (source.2.1.policy A)
        source.2.2 past).1 row
      (profiledPolicyRightFiniteStateAfter A (source.2.1.policy A)
        source.2.2 past).2 move).2.2.isSome := by
  simpa [stepEndToEndLeftOriginRecurrentRightReceiverFor] using
    (profiledPolicyRight_real_close_staged A (source.2.1.policy A)
      source.2.2 row past move)

/-- Left-origin/right-orientation wrapper with its exact fixed-policy edge. -/
theorem endToEndLeftOriginRecurrentRight_real_close_allowed
    (source : EndToEndLeftOriginRecurrentRightMacro A package)
    (row : PairedEntryRow) (past : List (In₂ × In₁))
    (move : In₂ × In₁) :
    ∃ target : ProfiledPolicyLeftMacro A (source.2.1.policy A),
      (stepEndToEndLeftOriginRecurrentRightReceiverFor A package source
        (profiledPolicyRightFiniteStateAfter A (source.2.1.policy A)
          source.2.2 past).1 row
        (profiledPolicyRightFiniteStateAfter A (source.2.1.policy A)
          source.2.2 past).2 move).2.2 =
          some ⟨source.1, source.2.1, target⟩ ∧
      PairedProfiledRationalPolicy.Allowed A (source.2.1.policy A)
        (.inr (.inl source.2.2.1)) (.inr (.inr target.1)) := by
  rcases profiledPolicyRight_real_close_allowed A (source.2.1.policy A)
      source.2.2 row past move with ⟨target, htarget, hallowed⟩
  refine ⟨target, ?_, hallowed⟩
  simpa [stepEndToEndLeftOriginRecurrentRightReceiverFor, htarget]

theorem endToEndLeftOriginRecurrentLeft_real_close_staged
    (source : EndToEndLeftOriginRecurrentLeftMacro A package)
    (row : PairedEntryRow) (past : List (In₁ × In₂))
    (move : In₁ × In₂) :
    (stepEndToEndLeftOriginRecurrentLeftReceiverFor A package source
      (profiledPolicyLeftFiniteStateAfter A (source.2.1.policy A)
        source.2.2 past).1 row
      (profiledPolicyLeftFiniteStateAfter A (source.2.1.policy A)
        source.2.2 past).2 move).2.2.isSome := by
  simpa [stepEndToEndLeftOriginRecurrentLeftReceiverFor] using
    (profiledPolicyLeft_real_close_staged A (source.2.1.policy A)
      source.2.2 row past move)

/-- Left-origin/left-orientation mirror with its exact fixed-policy edge. -/
theorem endToEndLeftOriginRecurrentLeft_real_close_allowed
    (source : EndToEndLeftOriginRecurrentLeftMacro A package)
    (row : PairedEntryRow) (past : List (In₁ × In₂))
    (move : In₁ × In₂) :
    ∃ target : ProfiledPolicyRightMacro A (source.2.1.policy A),
      (stepEndToEndLeftOriginRecurrentLeftReceiverFor A package source
        (profiledPolicyLeftFiniteStateAfter A (source.2.1.policy A)
          source.2.2 past).1 row
        (profiledPolicyLeftFiniteStateAfter A (source.2.1.policy A)
          source.2.2 past).2 move).2.2 =
          some ⟨source.1, source.2.1, target⟩ ∧
      PairedProfiledRationalPolicy.Allowed A (source.2.1.policy A)
        (.inr (.inr source.2.2.1)) (.inr (.inl target.1)) := by
  rcases profiledPolicyLeft_real_close_allowed A (source.2.1.policy A)
      source.2.2 row past move with ⟨target, htarget, hallowed⟩
  refine ⟨target, ?_, hallowed⟩
  simpa [stepEndToEndLeftOriginRecurrentLeftReceiverFor, htarget]

end


end DetParityAutomaton

end DistributedSynthesis
