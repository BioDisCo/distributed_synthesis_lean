/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledOpenPairCompatibility

/-!
# View-class handoff for pre-policy profiled roots

The Boolean pair used by the first fail-fast interface is not stable under a
reversal: the next blind process must group successors by equality of its new
local view, not by the old proof-side anchor.  This file states compatibility
for an arbitrary finite view class and constructs the semantic successor
classes before rationalization.

The class index is proof-side data.  The shared sender below receives neither
that index nor a leader/orientation flag.
-/

namespace DistributedSynthesis

universe i j u v x y s w

namespace DetParityAutomaton

variable {I : Type i}
variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

section

noncomputable section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

/-- A right-oriented view class has one receiver continuation per semantic
member and one blind process-one sender shared by the entire class. -/
def ProfiledOpenRightFamilyCompatible
    (source : I → ProfiledOpenRightRoot A) : Prop :=
  ∃ receiver : ∀ index : I,
      ReceiverBlockStrategy In₂ In₁ (ProfiledRightReceiverOutput A),
    ∃ sender : SenderBlockStrategy In₁ Out₁,
      ∀ index env,
        (profiledOpenRightRootMonitor.{u, v, x, y, s, w}
          A (source index)).WinsPlay
          (pairPlay (receiver index) sender env)

/-- Left-oriented mirror. -/
def ProfiledOpenLeftFamilyCompatible
    (source : I → ProfiledOpenLeftRoot A) : Prop :=
  ∃ receiver : ∀ index : I,
      ReceiverBlockStrategy In₁ In₂ (ProfiledLeftReceiverOutput A),
    ∃ sender : SenderBlockStrategy In₂ Out₂,
      ∀ index env,
        (profiledOpenLeftRootMonitor.{u, v, x, y, s, w}
          A (source index)).WinsPlay
          (pairPlay (receiver index) sender env)

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Compatibility is stable under arbitrary reindexing.  In particular, a
semantic class may be collapsed to one representative of each finite root
descriptor without changing the shared-sender invariant. -/
theorem ProfiledOpenRightFamilyCompatible.reindex
    {J : Type j} {source : I → ProfiledOpenRightRoot A}
    (hcompatible : ProfiledOpenRightFamilyCompatible.{i, u, v, x, y, s, w}
      A source) (representative : J → I) :
    ProfiledOpenRightFamilyCompatible.{j, u, v, x, y, s, w} A (fun index =>
      source (representative index)) := by
  exact ⟨(fun index => hcompatible.choose (representative index)),
    hcompatible.choose_spec.choose, fun index =>
      hcompatible.choose_spec.choose_spec (representative index)⟩

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Left-oriented reindexing. -/
theorem ProfiledOpenLeftFamilyCompatible.reindex
    {J : Type j} {source : I → ProfiledOpenLeftRoot A}
    (hcompatible : ProfiledOpenLeftFamilyCompatible.{i, u, v, x, y, s, w}
      A source) (representative : J → I) :
    ProfiledOpenLeftFamilyCompatible.{j, u, v, x, y, s, w} A (fun index =>
      source (representative index)) := by
  exact ⟨(fun index => hcompatible.choose (representative index)),
    hcompatible.choose_spec.choose, fun index =>
      hcompatible.choose_spec.choose_spec (representative index)⟩

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Every semantic process-one view class supplied by one winning strategy is
compatible.  `pivot` is used only to choose the common sender extension. -/
theorem profiledOpenRightFamilyCompatible_of_winning
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (entry : I → ProcOnePairedEntryRep strategy)
    (minimum : I → A.State) (pivot : I)
    (hview : ∀ index,
      currentView Proc.one (entry index).leftHistory =
        currentView Proc.one (entry pivot).leftHistory)
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis) :
    ProfiledOpenRightFamilyCompatible.{i, u, v, x, y, s, w} A
      (fun index => profiledOpenRightRootOfWinning A strategy hwin
        (entry index) (minimum index) basis) := by
  refine ⟨(fun index => profiledRightReceiverStrategy A
      (entry index).code (entry index).lambdaOfStrategy),
    pairedRightSenderStrategy (entry pivot).lambdaOfStrategy, ?_⟩
  intro index env
  have hindex := profiledOpenRightBlockMonitor_realizable_of_winning A
    strategy hwin (entry index) (minimum index) basis env
  have hsender :
      pairedRightSenderStrategy (entry index).lambdaOfStrategy =
        pairedRightSenderStrategy (entry pivot).lambdaOfStrategy := by
    unfold pairedRightSenderStrategy
    exact blockSenderOne_eq_of_view_eq strategy (hview index)
  rw [← hsender]
  simpa [profiledOpenRightRootOfWinning] using hindex

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Process-two view-class mirror. -/
theorem profiledOpenLeftFamilyCompatible_of_winning
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (entry : I → ProcTwoPairedEntryRep strategy)
    (minimum : I → A.State) (pivot : I)
    (hview : ∀ index,
      currentView Proc.two (entry index).rightHistory =
        currentView Proc.two (entry pivot).rightHistory)
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis) :
    ProfiledOpenLeftFamilyCompatible.{i, u, v, x, y, s, w} A
      (fun index => profiledOpenLeftRootOfWinning A strategy hwin
        (entry index) (minimum index) basis) := by
  refine ⟨(fun index => profiledLeftReceiverStrategy A
      (entry index).code (entry index).lambdaOfStrategy),
    pairedLeftSenderStrategy (entry pivot).lambdaOfStrategy, ?_⟩
  intro index env
  have hindex := profiledOpenLeftBlockMonitor_realizable_of_winning A
    strategy hwin (entry index) (minimum index) basis env
  have hsender :
      pairedLeftSenderStrategy (entry index).lambdaOfStrategy =
        pairedLeftSenderStrategy (entry pivot).lambdaOfStrategy := by
    unfold pairedLeftSenderStrategy
    exact blockSenderTwo_eq_of_view_eq strategy (hview index)
  rw [← hsender]
  simpa [profiledOpenLeftRootOfWinning] using hindex

/-- Materialize any finite compatible right view class as one simultaneous
finite table. -/
noncomputable def profiledOpenRightFamilyTableOfCompatible
    [Inhabited I] [Fintype I] [DecidableEq I]
    (source : I → ProfiledOpenRightRoot A)
    (hcompatible : ProfiledOpenRightFamilyCompatible.{i, u, v, x, y, s, w}
      A source) :
    FiniteRootFamilyTable (fun index : I =>
      profiledOpenRightRootMonitor A (source index)) :=
  finiteRootFamilyTable
    (fun index : I => profiledOpenRightRootMonitor A (source index))
    hcompatible.choose hcompatible.choose_spec.choose
    hcompatible.choose_spec.choose_spec

/-- The materialized right-class table carries the combined all-thread
certificate. -/
theorem profiledOpenRightFamilyTableOfCompatible_wins
    [Inhabited I] [Fintype I] [DecidableEq I]
    (source : I → ProfiledOpenRightRoot A)
    (hcompatible : ProfiledOpenRightFamilyCompatible.{i, u, v, x, y, s, w}
      A source) :
    NarrowedAllThreadsWin
      (finiteRootFamilyMonitor (fun index : I =>
        profiledOpenRightRootMonitor A (source index)))
      (profiledOpenRightFamilyTableOfCompatible A source hcompatible).toTransitionRationalTree.labeledTree := by
  simpa [profiledOpenRightFamilyTableOfCompatible] using
    (finiteRootFamilyTable_wins
      (fun index : I => profiledOpenRightRootMonitor A (source index))
      hcompatible.choose hcompatible.choose_spec.choose
      hcompatible.choose_spec.choose_spec)

/-- Left-class materialization. -/
noncomputable def profiledOpenLeftFamilyTableOfCompatible
    [Inhabited I] [Fintype I] [DecidableEq I]
    (source : I → ProfiledOpenLeftRoot A)
    (hcompatible : ProfiledOpenLeftFamilyCompatible.{i, u, v, x, y, s, w}
      A source) :
    FiniteRootFamilyTable (fun index : I =>
      profiledOpenLeftRootMonitor A (source index)) :=
  finiteRootFamilyTable
    (fun index : I => profiledOpenLeftRootMonitor A (source index))
    hcompatible.choose hcompatible.choose_spec.choose
    hcompatible.choose_spec.choose_spec

theorem profiledOpenLeftFamilyTableOfCompatible_wins
    [Inhabited I] [Fintype I] [DecidableEq I]
    (source : I → ProfiledOpenLeftRoot A)
    (hcompatible : ProfiledOpenLeftFamilyCompatible.{i, u, v, x, y, s, w}
      A source) :
    NarrowedAllThreadsWin
      (finiteRootFamilyMonitor (fun index : I =>
        profiledOpenLeftRootMonitor A (source index)))
      (profiledOpenLeftFamilyTableOfCompatible A source hcompatible).toTransitionRationalTree.labeledTree := by
  simpa [profiledOpenLeftFamilyTableOfCompatible] using
    (finiteRootFamilyTable_wins
      (fun index : I => profiledOpenLeftRootMonitor A (source index))
      hcompatible.choose hcompatible.choose_spec.choose
      hcompatible.choose_spec.choose_spec)

/-- The semantic process-two child selected after resolving one member of a
process-one family and taking the reversing receive. -/
def procTwoViewClassChild
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (entry : I → ProcOnePairedEntryRep strategy)
    (past : List (In₂ × In₁)) (input : In₂ × In₁)
    (candidate : I × PairedEntryRow) : ProcTwoPairedEntryRep strategy :=
  match candidate.2 with
  | .first => procTwoFreshPair strategy
      (extendPrefix strategy (entry candidate.1).leftHistory
        (past.map rightEnvironment))
      (strategyGenerated_extendPrefix_basic strategy
        (entry candidate.1).leftGenerated _)
      input.2 input.1
  | .both => procTwoFreshPair strategy
      (extendPrefix strategy (entry candidate.1).bothHistory
        (past.map rightEnvironment))
      (strategyGenerated_extendPrefix_basic strategy
        (entry candidate.1).bothGenerated _)
      input.2 input.1

/-- Minimum priority carried by the same semantic process-two child. -/
def procTwoViewClassChildMinimum
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (entry : I → ProcOnePairedEntryRep
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) strategy)
    (past : List (In₂ × In₁)) (candidate : I × PairedEntryRow) : A.State :=
  match candidate.2 with
  | .first => blockMinState A (entry candidate.1).code.1
      ((entry candidate.1).lambdaOfStrategy.leftWord past)
  | .both => blockMinState A (entry candidate.1).code.2
      ((entry candidate.1).lambdaOfStrategy.bothWord past)

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- The semantic child retained by a right-to-left view-class handoff is not
a spliced representative: together with its stored block minimum it is
literally one step of the original strategy memory.  This equality is the
one-step invariant needed by the history-indexed alternating construction. -/
theorem pairedStrategyMemory_step_eq_procTwoViewClassChild
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (entry : I → ProcOnePairedEntryRep strategy)
    (minimum : I → A.State) (member : I)
    (past : List (In₂ × In₁)) (move : In₂ × In₁)
    (row : PairedEntryRow) :
    PairedStrategyMemory.step (A := A)
        (.processOne (entry member) (minimum member))
        (.fromOne row past move) =
      .processTwo
        (procTwoViewClassChild strategy entry past move (member, row))
        (procTwoViewClassChildMinimum A entry past (member, row)) := by
  cases row <;> rfl

/-- The finite class of all semantic children whose new process-two blind
view equals that of `pivot`. -/
noncomputable def procTwoChildViewClass
    [Fintype I]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (entry : I → ProcOnePairedEntryRep strategy)
    (past : List (In₂ × In₁)) (input : In₂ × In₁)
    (pivot : I × PairedEntryRow) : Finset (I × PairedEntryRow) := by
  classical
  exact Finset.univ.filter fun candidate =>
    currentView Proc.two
        (procTwoViewClassChild strategy entry past input candidate).rightHistory =
      currentView Proc.two
        (procTwoViewClassChild strategy entry past input pivot).rightHistory

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
@[simp] theorem mem_procTwoChildViewClass
    [Fintype I]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (entry : I → ProcOnePairedEntryRep strategy)
    (past : List (In₂ × In₁)) (input : In₂ × In₁)
    (pivot candidate : I × PairedEntryRow) :
    candidate ∈ procTwoChildViewClass strategy entry past input pivot ↔
      currentView Proc.two
          (procTwoViewClassChild strategy entry past input candidate).rightHistory =
        currentView Proc.two
          (procTwoViewClassChild strategy entry past input pivot).rightHistory := by
  classical
  simp [procTwoChildViewClass]

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
@[simp] theorem pivot_mem_procTwoChildViewClass
    [Fintype I]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (entry : I → ProcOnePairedEntryRep strategy)
    (past : List (In₂ × In₁)) (input : In₂ × In₁)
    (pivot : I × PairedEntryRow) :
    pivot ∈ procTwoChildViewClass strategy entry past input pivot := by
  simp

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- The semantic successor view class itself has one common process-two
sender.  This is the corrected right-to-left handoff: membership is decided
by the new blind view, not by the old anchor or row. -/
theorem profiledOpenLeftViewClassCompatible_of_winning
    [Fintype I]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (entry : I → ProcOnePairedEntryRep strategy)
    (past : List (In₂ × In₁)) (input : In₂ × In₁)
    (pivot : I × PairedEntryRow)
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis) :
    let members := {candidate // candidate ∈
      procTwoChildViewClass strategy entry past input pivot}
    ProfiledOpenLeftFamilyCompatible.{i, u, v, x, y, s, w} A
      (fun member : members =>
        profiledOpenLeftRootOfWinning A strategy hwin
          (procTwoViewClassChild strategy entry past input member.1)
          (procTwoViewClassChildMinimum A entry past member.1) basis) := by
  dsimp only
  let pivotMember : {candidate // candidate ∈
      procTwoChildViewClass strategy entry past input pivot} :=
    ⟨pivot, pivot_mem_procTwoChildViewClass strategy entry past input pivot⟩
  apply profiledOpenLeftFamilyCompatible_of_winning A strategy hwin
    (fun member => procTwoViewClassChild strategy entry past input member.1)
    (fun member => procTwoViewClassChildMinimum A entry past member.1)
    pivotMember
  · intro member
    exact (mem_procTwoChildViewClass strategy entry past input pivot
      member.1).mp member.2

/-! ## Left-to-right mirror -/

/-- Semantic process-one child after resolving a process-two family member. -/
def procOneViewClassChild
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (entry : I → ProcTwoPairedEntryRep strategy)
    (past : List (In₁ × In₂)) (input : In₁ × In₂)
    (candidate : I × PairedEntryRow) : ProcOnePairedEntryRep strategy :=
  match candidate.2 with
  | .first => procOneFreshPair strategy
      (extendPrefix strategy (entry candidate.1).rightHistory
        (past.map leftEnvironment))
      (strategyGenerated_extendPrefix_basic strategy
        (entry candidate.1).rightGenerated _)
      input.1 input.2
  | .both => procOneFreshPair strategy
      (extendPrefix strategy (entry candidate.1).bothHistory
        (past.map leftEnvironment))
      (strategyGenerated_extendPrefix_basic strategy
        (entry candidate.1).bothGenerated _)
      input.1 input.2

/-- Minimum priority carried by the same semantic process-one child. -/
def procOneViewClassChildMinimum
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (entry : I → ProcTwoPairedEntryRep
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) strategy)
    (past : List (In₁ × In₂)) (candidate : I × PairedEntryRow) : A.State :=
  match candidate.2 with
  | .first => blockMinState A (entry candidate.1).code.1
      ((entry candidate.1).lambdaOfStrategy.rightWord past)
  | .both => blockMinState A (entry candidate.1).code.2
      ((entry candidate.1).lambdaOfStrategy.bothWord past)

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- Left-to-right mirror of the exact semantic-memory handoff. -/
theorem pairedStrategyMemory_step_eq_procOneViewClassChild
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (entry : I → ProcTwoPairedEntryRep strategy)
    (minimum : I → A.State) (member : I)
    (past : List (In₁ × In₂)) (move : In₁ × In₂)
    (row : PairedEntryRow) :
    PairedStrategyMemory.step (A := A)
        (.processTwo (entry member) (minimum member))
        (.fromTwo row past move) =
      .processOne
        (procOneViewClassChild strategy entry past move (member, row))
        (procOneViewClassChildMinimum A entry past (member, row)) := by
  cases row <;> rfl

/-- Finite class selected by equality of the new process-one blind view. -/
noncomputable def procOneChildViewClass
    [Fintype I]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (entry : I → ProcTwoPairedEntryRep strategy)
    (past : List (In₁ × In₂)) (input : In₁ × In₂)
    (pivot : I × PairedEntryRow) : Finset (I × PairedEntryRow) := by
  classical
  exact Finset.univ.filter fun candidate =>
    currentView Proc.one
        (procOneViewClassChild strategy entry past input candidate).leftHistory =
      currentView Proc.one
        (procOneViewClassChild strategy entry past input pivot).leftHistory

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
@[simp] theorem mem_procOneChildViewClass
    [Fintype I]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (entry : I → ProcTwoPairedEntryRep strategy)
    (past : List (In₁ × In₂)) (input : In₁ × In₂)
    (pivot candidate : I × PairedEntryRow) :
    candidate ∈ procOneChildViewClass strategy entry past input pivot ↔
      currentView Proc.one
          (procOneViewClassChild strategy entry past input candidate).leftHistory =
        currentView Proc.one
          (procOneViewClassChild strategy entry past input pivot).leftHistory := by
  classical
  simp [procOneChildViewClass]

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
@[simp] theorem pivot_mem_procOneChildViewClass
    [Fintype I]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (entry : I → ProcTwoPairedEntryRep strategy)
    (past : List (In₁ × In₂)) (input : In₁ × In₂)
    (pivot : I × PairedEntryRow) :
    pivot ∈ procOneChildViewClass strategy entry past input pivot := by
  simp

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Corrected left-to-right semantic handoff by the new process-one view
class. -/
theorem profiledOpenRightViewClassCompatible_of_winning
    [Fintype I]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (entry : I → ProcTwoPairedEntryRep strategy)
    (past : List (In₁ × In₂)) (input : In₁ × In₂)
    (pivot : I × PairedEntryRow)
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis) :
    let members := {candidate // candidate ∈
      procOneChildViewClass strategy entry past input pivot}
    ProfiledOpenRightFamilyCompatible.{i, u, v, x, y, s, w} A
      (fun member : members =>
        profiledOpenRightRootOfWinning A strategy hwin
          (procOneViewClassChild strategy entry past input member.1)
          (procOneViewClassChildMinimum A entry past member.1) basis) := by
  dsimp only
  let pivotMember : {candidate // candidate ∈
      procOneChildViewClass strategy entry past input pivot} :=
    ⟨pivot, pivot_mem_procOneChildViewClass strategy entry past input pivot⟩
  apply profiledOpenRightFamilyCompatible_of_winning A strategy hwin
    (fun member => procOneViewClassChild strategy entry past input member.1)
    (fun member => procOneViewClassChildMinimum A entry past member.1)
    pivotMember
  intro member
  exact (mem_procOneChildViewClass strategy entry past input pivot
    member.1).mp member.2

end

end


end DetParityAutomaton

end DistributedSynthesis
