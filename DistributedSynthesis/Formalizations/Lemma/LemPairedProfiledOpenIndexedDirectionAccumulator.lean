/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenIndexedDirectionSummary

/-!
# Streaming the finite indexed direction summary

`LemPairedProfiledOpenIndexedDirectionSummary` proves that the unbounded
tagged prefixes in one hidden direction have a finite quotient.  This file
makes that quotient operational.  For one fixed selected pair of classified
tables, its two finite controls are initialized and updated one tagged letter
at a time; at the reversal boundary the resulting accumulator is exactly the
previously defined direction summary.

The accumulator is a proof-side scan of Nature's tagged direction.  It is not
a local process state: its narrowed monitor component sees the decoded full
round.  The final section therefore separately exposes the smaller installed
local overlays.  The right table's overlay is advanced only by process one's
input, and the left table's mirror only by process two's input.  Neither
overlay contains a strict-leader, graph, lineage, or hidden-root coordinate.

Everything here is relative to one fixed selected move/table pair.  In
particular, no coherence between tables selected at different rational-policy
states is assumed; that is the separate gate isolated in
`LemPairedProfiledOpenIndexedPolicyUniformityGate`.
-/

namespace DistributedSynthesis

universe i u v x y s

namespace DetParityAutomaton

variable {I : Type i}
variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Fintype I]
variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
  [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

/-! ## One-step laws for the complete induced controls -/

/-- Initial complete control of one right classified table. -/
noncomputable def profiledOpenRightClassifiedInducedControlInitial
    (source : ProfiledOpenRightViewClass A)
    (table : ProfiledOpenRightClassifiedTable A source) :
    ProfiledOpenRightClassifiedInducedControl A source table :=
  let monitors := fun member : {root // root ∈ source.1} =>
    profiledOpenRightClassifiedRootMonitor A member.1
  let family := table.toTransitionRationalTree
  (family.initial, (finiteRootFamilyMonitor monitors).initial)

/-- Advance the complete right induced control by one decoded tagged round. -/
noncomputable def profiledOpenRightClassifiedInducedControlStep
    (source : ProfiledOpenRightViewClass A)
    (table : ProfiledOpenRightClassifiedTable A source)
    (control : ProfiledOpenRightClassifiedInducedControl A source table)
    (letter : (({root // root ∈ source.1} × In₂) × In₁)) :
    ProfiledOpenRightClassifiedInducedControl A source table :=
  let monitors := fun member : {root // root ∈ source.1} =>
    profiledOpenRightClassifiedRootMonitor A member.1
  let monitor := finiteRootFamilyMonitor monitors
  let family := table.toTransitionRationalTree
  (family.step control.1 letter.2,
    monitor.step control.2
      (narrowedRecord monitor (family.labelOf control.1) control.2 letter))

/-- Initial complete control of one left classified table. -/
noncomputable def profiledOpenLeftClassifiedInducedControlInitial
    (source : ProfiledOpenLeftViewClass A)
    (table : ProfiledOpenLeftClassifiedTable A source) :
    ProfiledOpenLeftClassifiedInducedControl A source table :=
  let monitors := fun member : {root // root ∈ source.1} =>
    profiledOpenLeftClassifiedRootMonitor A member.1
  let family := table.toTransitionRationalTree
  (family.initial, (finiteRootFamilyMonitor monitors).initial)

/-- Advance the complete left induced control by one decoded tagged round. -/
noncomputable def profiledOpenLeftClassifiedInducedControlStep
    (source : ProfiledOpenLeftViewClass A)
    (table : ProfiledOpenLeftClassifiedTable A source)
    (control : ProfiledOpenLeftClassifiedInducedControl A source table)
    (letter : (({root // root ∈ source.1} × In₁) × In₂)) :
    ProfiledOpenLeftClassifiedInducedControl A source table :=
  let monitors := fun member : {root // root ∈ source.1} =>
    profiledOpenLeftClassifiedRootMonitor A member.1
  let monitor := finiteRootFamilyMonitor monitors
  let family := table.toTransitionRationalTree
  (family.step control.1 letter.2,
    monitor.step control.2
      (narrowedRecord monitor (family.labelOf control.1) control.2 letter))

section
omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]

@[simp] theorem profiledOpenRightClassifiedInducedControlAt_nil
    (source : ProfiledOpenRightViewClass A)
    (table : ProfiledOpenRightClassifiedTable A source) :
    profiledOpenRightClassifiedInducedControlAt A source table [] =
      profiledOpenRightClassifiedInducedControlInitial A source table := by
  rfl

@[simp] theorem profiledOpenLeftClassifiedInducedControlAt_nil
    (source : ProfiledOpenLeftViewClass A)
    (table : ProfiledOpenLeftClassifiedTable A source) :
    profiledOpenLeftClassifiedInducedControlAt A source table [] =
      profiledOpenLeftClassifiedInducedControlInitial A source table := by
  rfl

/-- Appending a decoded right round is exactly the executable control step. -/
theorem profiledOpenRightClassifiedInducedControlAt_append
    (source : ProfiledOpenRightViewClass A)
    (table : ProfiledOpenRightClassifiedTable A source)
    (node : List ((({root // root ∈ source.1} × In₂) × In₁)))
    (letter : (({root // root ∈ source.1} × In₂) × In₁)) :
    profiledOpenRightClassifiedInducedControlAt A source table
        (node ++ [letter]) =
      profiledOpenRightClassifiedInducedControlStep A source table
        (profiledOpenRightClassifiedInducedControlAt A source table node)
        letter := by
  rw [profiledOpenRightClassifiedInducedControlAt, senderWord_append,
    TransitionRationalTree.controlAt_append, narrowedControl_append]
  rfl

/-- Left append law. -/
theorem profiledOpenLeftClassifiedInducedControlAt_append
    (source : ProfiledOpenLeftViewClass A)
    (table : ProfiledOpenLeftClassifiedTable A source)
    (node : List ((({root // root ∈ source.1} × In₁) × In₂)))
    (letter : (({root // root ∈ source.1} × In₁) × In₂)) :
    profiledOpenLeftClassifiedInducedControlAt A source table
        (node ++ [letter]) =
      profiledOpenLeftClassifiedInducedControlStep A source table
        (profiledOpenLeftClassifiedInducedControlAt A source table node)
        letter := by
  rw [profiledOpenLeftClassifiedInducedControlAt, senderWord_append,
    TransitionRationalTree.controlAt_append, narrowedControl_append]
  rfl

end

/-! ## Packed fixed-move streaming controls -/

/-- Initial packed right component for one fixed selected move. -/
noncomputable def profiledOpenIndexedRightDirectionControlInitial :
    (move : ProfiledOpenClassifiedMove A) →
      ProfiledOpenIndexedRightDirectionControl A move
  | .right source table =>
      Fintype.equivFin
        (ProfiledOpenRightClassifiedInducedControl.{u, v, x, y, s, 0, 0}
          A source table)
        (profiledOpenRightClassifiedInducedControlInitial A source table)
  | .sink => PUnit.unit
  | .left _ _ => PUnit.unit

/-- One raw tagged right letter advances the packed finite component. -/
noncomputable def profiledOpenIndexedRightDirectionControlStep
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I)) :
    (move : ProfiledOpenClassifiedMove A) →
      ProfiledOpenIndexedRightDirectionControl A move →
        ((I × In₂) × In₁) →
          ProfiledOpenIndexedRightDirectionControl A move
  | .right source table, packed, tagged =>
      Fintype.equivFin
        (ProfiledOpenRightClassifiedInducedControl.{u, v, x, y, s, 0, 0}
          A source table)
        (profiledOpenRightClassifiedInducedControlStep A source table
          ((Fintype.equivFin
            (ProfiledOpenRightClassifiedInducedControl.{u, v, x, y, s,
              0, 0} A source table)).symm packed)
          (((profiledOpenIndexedRightSourceMember A code source tagged.1.1),
            tagged.1.2), tagged.2))
  | .sink, _, _ => PUnit.unit
  | .left _ _, _, _ => PUnit.unit

/-- Initial packed left component. -/
noncomputable def profiledOpenIndexedLeftDirectionControlInitial :
    (move : ProfiledOpenClassifiedMove A) →
      ProfiledOpenIndexedLeftDirectionControl A move
  | .left source table =>
      Fintype.equivFin
        (ProfiledOpenLeftClassifiedInducedControl.{u, v, x, y, s, 0, 0}
          A source table)
        (profiledOpenLeftClassifiedInducedControlInitial A source table)
  | .sink => PUnit.unit
  | .right _ _ => PUnit.unit

/-- One raw tagged left letter advances the packed finite component. -/
noncomputable def profiledOpenIndexedLeftDirectionControlStep
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I)) :
    (move : ProfiledOpenClassifiedMove A) →
      ProfiledOpenIndexedLeftDirectionControl A move →
        ((I × In₁) × In₂) →
          ProfiledOpenIndexedLeftDirectionControl A move
  | .left source table, packed, tagged =>
      Fintype.equivFin
        (ProfiledOpenLeftClassifiedInducedControl.{u, v, x, y, s, 0, 0}
          A source table)
        (profiledOpenLeftClassifiedInducedControlStep A source table
          ((Fintype.equivFin
            (ProfiledOpenLeftClassifiedInducedControl.{u, v, x, y, s,
              0, 0} A source table)).symm packed)
          (((profiledOpenIndexedLeftSourceMember A code source tagged.1.1),
            tagged.1.2), tagged.2))
  | .sink, _, _ => PUnit.unit
  | .right _ _, _, _ => PUnit.unit

/-- Executable scan of a right tagged prefix. -/
noncomputable def profiledOpenIndexedRightDirectionControlScan
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (move : ProfiledOpenClassifiedMove A)
    (past : List ((I × In₂) × In₁)) :
    ProfiledOpenIndexedRightDirectionControl A move :=
  past.foldl (profiledOpenIndexedRightDirectionControlStep A code move)
    (profiledOpenIndexedRightDirectionControlInitial A move)

/-- Executable scan of a left tagged prefix. -/
noncomputable def profiledOpenIndexedLeftDirectionControlScan
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (move : ProfiledOpenClassifiedMove A)
    (past : List ((I × In₁) × In₂)) :
    ProfiledOpenIndexedLeftDirectionControl A move :=
  past.foldl (profiledOpenIndexedLeftDirectionControlStep A code move)
    (profiledOpenIndexedLeftDirectionControlInitial A move)

omit [Fintype I] [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledOpenIndexedRightDirectionControlScan_eq_ofPast
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (move : ProfiledOpenClassifiedMove A) :
    ∀ past : List ((I × In₂) × In₁),
      profiledOpenIndexedRightDirectionControlScan A code move past =
        profiledOpenIndexedRightDirectionControlOfPast A code move past := by
  intro past
  induction past using List.reverseRecOn with
  | nil =>
      cases move <;> rfl
  | append_singleton past tagged ih =>
      rw [profiledOpenIndexedRightDirectionControlScan, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      change profiledOpenIndexedRightDirectionControlStep A code move
          (profiledOpenIndexedRightDirectionControlScan A code move past)
          tagged = _
      rw [ih]
      cases move with
      | sink => rfl
      | left source table => rfl
      | right source table =>
          simp only [profiledOpenIndexedRightDirectionControlStep,
            profiledOpenIndexedRightDirectionControlOfPast,
            Equiv.symm_apply_apply]
          apply congrArg (Fintype.equivFin
            (ProfiledOpenRightClassifiedInducedControl.{u, v, x, y, s,
              0, 0} A source table))
          rw [← profiledOpenRightClassifiedInducedControlAt_append]
          simp [profiledOpenIndexedRightSharedNode]

omit [Fintype I] [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledOpenIndexedLeftDirectionControlScan_eq_ofPast
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (move : ProfiledOpenClassifiedMove A) :
    ∀ past : List ((I × In₁) × In₂),
      profiledOpenIndexedLeftDirectionControlScan A code move past =
        profiledOpenIndexedLeftDirectionControlOfPast A code move past := by
  intro past
  induction past using List.reverseRecOn with
  | nil =>
      cases move <;> rfl
  | append_singleton past tagged ih =>
      rw [profiledOpenIndexedLeftDirectionControlScan, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      change profiledOpenIndexedLeftDirectionControlStep A code move
          (profiledOpenIndexedLeftDirectionControlScan A code move past)
          tagged = _
      rw [ih]
      cases move with
      | sink => rfl
      | right source table => rfl
      | left source table =>
          simp only [profiledOpenIndexedLeftDirectionControlStep,
            profiledOpenIndexedLeftDirectionControlOfPast,
            Equiv.symm_apply_apply]
          apply congrArg (Fintype.equivFin
            (ProfiledOpenLeftClassifiedInducedControl.{u, v, x, y, s,
              0, 0} A source table))
          rw [← profiledOpenLeftClassifiedInducedControlAt_append]
          simp [profiledOpenIndexedLeftSharedNode]

/-! ## Two-lane accumulator and reversal boundary -/

/-- The running finite state before the two pivots and current inputs are
installed at a reversal boundary. -/
structure ProfiledOpenIndexedDirectionAccumulator
    (move : ProfiledOpenIndexedBiBeliefMove A) where
  rightControl : ProfiledOpenIndexedRightDirectionControl A move.1
  leftControl : ProfiledOpenIndexedLeftDirectionControl A move.2

noncomputable instance profiledOpenIndexedDirectionAccumulator_fintype
    (move : ProfiledOpenIndexedBiBeliefMove A) :
    Fintype (ProfiledOpenIndexedDirectionAccumulator A move) := by
  classical
  let encode := fun state :
      ProfiledOpenIndexedDirectionAccumulator A move =>
    (state.rightControl, state.leftControl)
  exact Fintype.ofInjective encode (by
    intro left right heq
    rcases left with ⟨leftR, leftL⟩
    rcases right with ⟨rightR, rightL⟩
    simp only [encode, Prod.mk.injEq] at heq
    rcases heq with ⟨rfl, rfl⟩
    rfl)

/-- Initial accumulator for one installed pair of selected tables. -/
noncomputable def profiledOpenIndexedDirectionAccumulatorInitial
    (move : ProfiledOpenIndexedBiBeliefMove A) :
    ProfiledOpenIndexedDirectionAccumulator A move :=
  ⟨profiledOpenIndexedRightDirectionControlInitial A move.1,
    profiledOpenIndexedLeftDirectionControlInitial A move.2⟩

/-- Advance only the right proof-side lane. -/
noncomputable def profiledOpenIndexedDirectionAccumulatorStepRight
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (state : ProfiledOpenIndexedDirectionAccumulator A move)
    (tagged : (I × In₂) × In₁) :
    ProfiledOpenIndexedDirectionAccumulator A move :=
  ⟨profiledOpenIndexedRightDirectionControlStep A code move.1
      state.rightControl tagged,
    state.leftControl⟩

/-- Advance only the left proof-side lane. -/
noncomputable def profiledOpenIndexedDirectionAccumulatorStepLeft
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (state : ProfiledOpenIndexedDirectionAccumulator A move)
    (tagged : (I × In₁) × In₂) :
    ProfiledOpenIndexedDirectionAccumulator A move :=
  ⟨state.rightControl,
    profiledOpenIndexedLeftDirectionControlStep A code move.2
      state.leftControl tagged⟩

/-- Scan both stored prefixes into the two-lane finite accumulator. -/
noncomputable def profiledOpenIndexedDirectionAccumulatorScan
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (rightPast : List ((I × In₂) × In₁))
    (leftPast : List ((I × In₁) × In₂)) :
    ProfiledOpenIndexedDirectionAccumulator A move :=
  ⟨profiledOpenIndexedRightDirectionControlScan A code move.1 rightPast,
    profiledOpenIndexedLeftDirectionControlScan A code move.2 leftPast⟩

/-- Install the finite boundary data and finish one direction summary. -/
noncomputable def ProfiledOpenIndexedDirectionAccumulator.finish
    {move : ProfiledOpenIndexedBiBeliefMove A}
    (state : ProfiledOpenIndexedDirectionAccumulator A move)
    (rightPivot : IndexedLineageCandidate I) (rightInput : In₂ × In₁)
    (leftPivot : IndexedLineageCandidate I) (leftInput : In₁ × In₂) :
    ProfiledOpenIndexedDirectionSummary A (I := I) move :=
  { rightPivot := rightPivot
    rightControl := state.rightControl
    rightInput := rightInput
    leftPivot := leftPivot
    leftControl := state.leftControl
    leftInput := leftInput }

omit [Fintype I] [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- At reversal, the executable scan is exactly the extensional finite
summary used by the successor-factorization theorem. -/
theorem profiledOpenIndexedDirectionAccumulator_finish_scan
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (direction : ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)) :
    (profiledOpenIndexedDirectionAccumulatorScan A code move
        direction.rightTaggedPast direction.leftTaggedPast).finish A
        direction.rightPivot direction.rightInput
        direction.leftPivot direction.leftInput =
      profiledOpenIndexedDirectionSummarize A code move direction := by
  unfold ProfiledOpenIndexedDirectionAccumulator.finish
    profiledOpenIndexedDirectionAccumulatorScan
    profiledOpenIndexedDirectionSummarize
  rw [profiledOpenIndexedRightDirectionControlScan_eq_ofPast,
    profiledOpenIndexedLeftDirectionControlScan_eq_ofPast]

/-! ## The smaller graph-blind installed local overlays -/

/-- Process one's complete installed local state for one fixed right table.
It is exactly the shared rational-table control and its active Boolean. -/
abbrev ProfiledOpenIndexedProcessOneGraphBlindOverlay
    (source : ProfiledOpenRightViewClass A)
    (table : ProfiledOpenRightClassifiedTable A source) :=
  ProfiledOpenRightClassifiedLocalControl A source table

/-- Process two's mirror for one fixed left table. -/
abbrev ProfiledOpenIndexedProcessTwoGraphBlindOverlay
    (source : ProfiledOpenLeftViewClass A)
    (table : ProfiledOpenLeftClassifiedTable A source) :=
  ProfiledOpenLeftClassifiedLocalControl A source table

/-- Install the process-one overlay at the selected right table's root. -/
noncomputable def profiledOpenIndexedProcessOneGraphBlindOverlayInitial
    (source : ProfiledOpenRightViewClass A)
    (table : ProfiledOpenRightClassifiedTable A source) :
    ProfiledOpenIndexedProcessOneGraphBlindOverlay A source table :=
  FiniteRootFamilyLocalOverlay.initial
    (fun member : {root // root ∈ source.1} =>
      profiledOpenRightClassifiedRootMonitor A member.1)
    table.toTransitionRationalTree

/-- One local process-one input advances the installed right-table overlay. -/
noncomputable def profiledOpenIndexedProcessOneGraphBlindOverlayStep
    (source : ProfiledOpenRightViewClass A)
    (table : ProfiledOpenRightClassifiedTable A source)
    (state : ProfiledOpenIndexedProcessOneGraphBlindOverlay A source table)
    (input : In₁) :
    ProfiledOpenIndexedProcessOneGraphBlindOverlay A source table :=
  state.step
    (fun member : {root // root ∈ source.1} =>
      profiledOpenRightClassifiedRootMonitor A member.1)
    table.toTransitionRationalTree input

/-- Process one's output uses only its installed state and current input. -/
noncomputable def profiledOpenIndexedProcessOneGraphBlindOverlayOutput
    (source : ProfiledOpenRightViewClass A)
    (table : ProfiledOpenRightClassifiedTable A source)
    (state : ProfiledOpenIndexedProcessOneGraphBlindOverlay A source table)
    (input : In₁) : Out₁ :=
  state.output
    (fun member : {root // root ∈ source.1} =>
      profiledOpenRightClassifiedRootMonitor A member.1)
    table.toTransitionRationalTree input

/-- Install the process-two overlay at the selected left table's root. -/
noncomputable def profiledOpenIndexedProcessTwoGraphBlindOverlayInitial
    (source : ProfiledOpenLeftViewClass A)
    (table : ProfiledOpenLeftClassifiedTable A source) :
    ProfiledOpenIndexedProcessTwoGraphBlindOverlay A source table :=
  FiniteRootFamilyLocalOverlay.initial
    (fun member : {root // root ∈ source.1} =>
      profiledOpenLeftClassifiedRootMonitor A member.1)
    table.toTransitionRationalTree

/-- One local process-two input advances the installed left-table overlay. -/
noncomputable def profiledOpenIndexedProcessTwoGraphBlindOverlayStep
    (source : ProfiledOpenLeftViewClass A)
    (table : ProfiledOpenLeftClassifiedTable A source)
    (state : ProfiledOpenIndexedProcessTwoGraphBlindOverlay A source table)
    (input : In₂) :
    ProfiledOpenIndexedProcessTwoGraphBlindOverlay A source table :=
  state.step
    (fun member : {root // root ∈ source.1} =>
      profiledOpenLeftClassifiedRootMonitor A member.1)
    table.toTransitionRationalTree input

/-- Process two's output uses only its installed state and current input. -/
noncomputable def profiledOpenIndexedProcessTwoGraphBlindOverlayOutput
    (source : ProfiledOpenLeftViewClass A)
    (table : ProfiledOpenLeftClassifiedTable A source)
    (state : ProfiledOpenIndexedProcessTwoGraphBlindOverlay A source table)
    (input : In₂) : Out₂ :=
  state.output
    (fun member : {root // root ∈ source.1} =>
      profiledOpenLeftClassifiedRootMonitor A member.1)
    table.toTransitionRationalTree input

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- The fixed right-table member implementation is exactly the graph-blind
process-one overlay step, independently of the proof-side member. -/
theorem profiledOpenRightClassifiedLocalMemberStep_eq_graphBlindOverlay
    (source : ProfiledOpenRightViewClass A)
    (table : ProfiledOpenRightClassifiedTable A source)
    (state : ProfiledOpenIndexedProcessOneGraphBlindOverlay A source table)
    (member : {root // root ∈ source.1}) (input : In₁) :
    profiledOpenRightClassifiedLocalMemberStep A source table state member input =
      (profiledOpenIndexedProcessOneGraphBlindOverlayOutput A source table
          state input,
        profiledOpenIndexedProcessOneGraphBlindOverlayStep A source table
          state input) := by
  rfl

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Left fixed-table mirror. -/
theorem profiledOpenLeftClassifiedLocalMemberStep_eq_graphBlindOverlay
    (source : ProfiledOpenLeftViewClass A)
    (table : ProfiledOpenLeftClassifiedTable A source)
    (state : ProfiledOpenIndexedProcessTwoGraphBlindOverlay A source table)
    (member : {root // root ∈ source.1}) (input : In₂) :
    profiledOpenLeftClassifiedLocalMemberStep A source table state member input =
      (profiledOpenIndexedProcessTwoGraphBlindOverlayOutput A source table
          state input,
        profiledOpenIndexedProcessTwoGraphBlindOverlayStep A source table
          state input) := by
  rfl

end

end DetParityAutomaton

end DistributedSynthesis
