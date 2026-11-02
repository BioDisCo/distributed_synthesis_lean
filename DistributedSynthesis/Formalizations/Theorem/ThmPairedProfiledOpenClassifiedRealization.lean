/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledOpenClassifiedMove

/-!
# Semantic realization of successor-classified moves

The annotations of a classified move are not guessed finite data.  They are
obtained from one winning distributed strategy: after each reversing receive
we partition all semantic children by equality of the local view of the
newly blind process, and then collapse that class to its finite set of open
root descriptors.
-/

namespace DistributedSynthesis

universe i u v x y s w

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

/-! ## Exact semantic child equation -/

omit [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- The profiled target emitted by a semantic right receiver is literally the
live descriptor of the semantic process-two child used by the corrected view
class handoff. -/
theorem profiledRightReceiverTarget_eq_procTwoViewClassChildRoot
    [Fintype I]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (entry : I → ProcOnePairedEntryRep strategy)
    (minimum : I → A.State)
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
    (index : I) (past : List (In₂ × In₁)) (move : In₂ × In₁)
    (row : PairedEntryRow) :
    (profiledRightReceiverStrategy A (entry index).code
        (entry index).lambdaOfStrategy past move).target row =
      .inr (.inr
        (profiledOpenLeftRootOfWinning A strategy hwin
          (procTwoViewClassChild strategy entry past move (index, row))
          (procTwoViewClassChildMinimum A entry past (index, row)) basis).1) := by
  cases row <;>
    simp [profiledRightReceiverStrategy, profiledOpenLeftRootOfWinning,
      procTwoViewClassChild, procTwoViewClassChildMinimum,
      pairedProfiledOneChild, pairedOneChild,
      pairedRightFreshChildCodeLeft_lambdaOfStrategy,
      pairedRightFreshChildCodeBoth_lambdaOfStrategy,
      rightClosingProfile_lambdaOfStrategy]

omit [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- Left-to-right mirror of the exact semantic child equation. -/
theorem profiledLeftReceiverTarget_eq_procOneViewClassChildRoot
    [Fintype I]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (entry : I → ProcTwoPairedEntryRep strategy)
    (minimum : I → A.State)
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
    (index : I) (past : List (In₁ × In₂)) (move : In₁ × In₂)
    (row : PairedEntryRow) :
    (profiledLeftReceiverStrategy A (entry index).code
        (entry index).lambdaOfStrategy past move).target row =
      .inr (.inl
        (profiledOpenRightRootOfWinning A strategy hwin
          (procOneViewClassChild strategy entry past move (index, row))
          (procOneViewClassChildMinimum A entry past (index, row)) basis).1) := by
  cases row <;>
    simp [profiledLeftReceiverStrategy, profiledOpenRightRootOfWinning,
      procOneViewClassChild, procOneViewClassChildMinimum,
      pairedProfiledTwoChild, pairedTwoChild,
      pairedLeftFreshChildCodeRight_lambdaOfStrategy,
      pairedLeftFreshChildCodeBoth_lambdaOfStrategy,
      leftClosingProfile_lambdaOfStrategy]

/-! ## Canonical semantic right-to-left annotation -/

/-- The semantic root attached to one right-to-left row. -/
noncomputable def profiledOpenRightSemanticChildRoot
    (source : ProfiledOpenRightViewClass A)
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (entry : {root // root ∈ source.1} → ProcOnePairedEntryRep strategy)
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
    (member : {root // root ∈ source.1})
    (past : List (In₂ × In₁)) (move : In₂ × In₁)
    (row : PairedEntryRow) : ProfiledOpenLeftRoot A :=
  profiledOpenLeftRootOfWinning A strategy hwin
    (procTwoViewClassChild strategy entry past move (member, row))
    (procTwoViewClassChildMinimum A entry past (member, row)) basis

/-- Canonical finite descriptor set of the new process-two local-view class
containing a selected child. -/
noncomputable def profiledOpenRightSemanticChildClass
    (source : ProfiledOpenRightViewClass A)
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (entry : {root // root ∈ source.1} → ProcOnePairedEntryRep strategy)
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
    (member : {root // root ∈ source.1})
    (past : List (In₂ × In₁)) (move : In₂ × In₁)
    (row : PairedEntryRow) : ProfiledOpenLeftViewClass A := by
  classical
  let pivot := (member, row)
  let members := {candidate // candidate ∈
    procTwoChildViewClass strategy entry past move pivot}
  letI : Inhabited members :=
    ⟨⟨pivot, pivot_mem_procTwoChildViewClass
      strategy entry past move pivot⟩⟩
  let roots : members → ProfiledOpenLeftRoot A := fun candidate =>
    profiledOpenLeftRootOfWinning A strategy hwin
      (procTwoViewClassChild strategy entry past move candidate.1)
      (procTwoViewClassChildMinimum A entry past candidate.1) basis
  have hcompatible : ProfiledOpenLeftFamilyCompatible A roots := by
    simpa [roots, members, pivot] using
      (profiledOpenLeftViewClassCompatible_of_winning A strategy hwin
        entry past move pivot basis)
  exact profiledOpenLeftViewClassOfCompatible A roots hcompatible

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- The pivot child is contained in the canonical class advertised for it. -/
theorem profiledOpenRightSemanticChildRoot_mem_class
    (source : ProfiledOpenRightViewClass A)
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (entry : {root // root ∈ source.1} → ProcOnePairedEntryRep strategy)
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
    (member : {root // root ∈ source.1})
    (past : List (In₂ × In₁)) (move : In₂ × In₁)
    (row : PairedEntryRow) :
    profiledOpenRightSemanticChildRoot A source strategy hwin entry basis
        member past move row ∈
      (profiledOpenRightSemanticChildClass A source strategy hwin entry basis
        member past move row).1 := by
  classical
  let pivot := (member, row)
  let members := {candidate // candidate ∈
    procTwoChildViewClass strategy entry past move pivot}
  let pivotMember : members :=
    ⟨pivot, pivot_mem_procTwoChildViewClass strategy entry past move pivot⟩
  change profiledOpenRightSemanticChildRoot A source strategy hwin entry basis
      member past move row ∈
    profiledOpenLeftRootImage A
      (fun candidate : members =>
        profiledOpenLeftRootOfWinning A strategy hwin
          (procTwoViewClassChild strategy entry past move candidate.1)
          (procTwoViewClassChildMinimum A entry past candidate.1) basis)
  apply Finset.mem_image.mpr
  refine ⟨pivotMember, Finset.mem_univ _, ?_⟩
  rfl

/-- Classified semantic receiver for one fixed source-class member. -/
noncomputable def profiledOpenRightSemanticClassifiedReceiver
    (source : ProfiledOpenRightViewClass A)
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (entry : {root // root ∈ source.1} → ProcOnePairedEntryRep strategy)
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
    (member : {root // root ∈ source.1}) :
    ReceiverBlockStrategy In₂ In₁ (ProfiledOpenRightClassifiedOutput A) :=
  fun past move =>
    (profiledRightReceiverStrategy A (entry member).code
      (entry member).lambdaOfStrategy past move,
      fun row =>
        (profiledOpenRightSemanticChildRoot A source strategy hwin entry basis
          member past move row,
         profiledOpenRightSemanticChildClass A source strategy hwin entry basis
          member past move row))

/-- Combining the member receivers keeps the source member hidden from the
sender and presents one complete response table to the environment. -/
noncomputable def profiledOpenRightSemanticClassifiedFamilyReceiver
    (source : ProfiledOpenRightViewClass A)
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (entry : {root // root ∈ source.1} → ProcOnePairedEntryRep strategy)
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis) :
    ReceiverBlockStrategy ({root // root ∈ source.1} × In₂) In₁
      (ProfiledOpenRightClassifiedOutput A) :=
  finiteRootFamilyReceiver
    (profiledOpenRightSemanticClassifiedReceiver A source strategy hwin
      entry basis)

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Every semantic classified family table satisfies the exact target and
successor-membership law, on every finite past (including pasts with changing
proof-side member tags). -/
theorem profiledOpenRightSemanticClassifiedFamilyReceiver_allowed
    (source : ProfiledOpenRightViewClass A)
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (entry : {root // root ∈ source.1} → ProcOnePairedEntryRep strategy)
    (minimum : {root // root ∈ source.1} → A.State)
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
    (past : List (({root // root ∈ source.1} × In₂) × In₁)) :
    ProfiledOpenRightClassifiedTableAllowed A source
      (profiledOpenRightSemanticClassifiedFamilyReceiver A source strategy
        hwin entry basis past) := by
  intro member move row
  let physicalPast := past.map fun old => (old.1.2, old.2)
  constructor
  · simpa [profiledOpenRightSemanticClassifiedFamilyReceiver,
      finiteRootFamilyReceiver,
      profiledOpenRightSemanticClassifiedReceiver,
      profiledOpenRightSemanticChildRoot, physicalPast] using
      (profiledRightReceiverTarget_eq_procTwoViewClassChildRoot A strategy
        hwin entry minimum basis member physicalPast move row)
  · exact profiledOpenRightSemanticChildRoot_mem_class A source strategy hwin
      entry basis member physicalPast move row

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- The semantic classified family has one genuinely shared process-one
sender.  The source member is a proof-side receiver tag only; it is absent
from the sender word. -/
theorem profiledOpenRightSemanticClassifiedFamily_realizable
    (source : ProfiledOpenRightViewClass A)
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (entry : {root // root ∈ source.1} → ProcOnePairedEntryRep strategy)
    (minimum : {root // root ∈ source.1} → A.State)
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
    (hroot : ∀ member,
      profiledOpenRightRootOfWinning A strategy hwin (entry member)
        (minimum member) basis = member.1)
    (pivot : {root // root ∈ source.1})
    (hview : ∀ member,
      currentView Proc.one (entry member).leftHistory =
        currentView Proc.one (entry pivot).leftHistory) :
    ∀ env,
      (finiteRootFamilyMonitor
        (fun member : {root // root ∈ source.1} =>
          profiledOpenRightClassifiedRootMonitor A member.1)).WinsPlay
        (pairPlay
          (profiledOpenRightSemanticClassifiedFamilyReceiver A source strategy
            hwin entry basis)
          (pairedRightSenderStrategy (entry pivot).lambdaOfStrategy) env) := by
  apply finiteRootFamily_realizable
  intro member env
  apply (BlockRecordMonitor.comapReceiverOutput_wins_iff
    (profiledOpenRightRootMonitor A member.1)
    (fun output : ProfiledOpenRightClassifiedOutput A => output.1) _).mpr
  have hmember := profiledOpenRightBlockMonitor_realizable_of_winning A
    strategy hwin (entry member) (minimum member) basis env
  have hsender :
      pairedRightSenderStrategy (entry member).lambdaOfStrategy =
        pairedRightSenderStrategy (entry pivot).lambdaOfStrategy := by
    unfold pairedRightSenderStrategy
    exact blockSenderOne_eq_of_view_eq strategy (hview member)
  have hrootmember :
      (profiledOpenRightRootMonitor A
        (profiledOpenRightRootOfWinning A strategy hwin (entry member)
          (minimum member) basis)).WinsPlay
        (pairPlay
          (profiledRightReceiverStrategy A (entry member).code
            (entry member).lambdaOfStrategy)
          (pairedRightSenderStrategy (entry member).lambdaOfStrategy) env) := by
    simpa [profiledOpenRightRootOfWinning] using hmember
  rw [hroot member, hsender] at hrootmember
  simpa [BlockRecordMonitor.projectReceiverPlay,
    profiledOpenRightSemanticClassifiedReceiver, pairPlay, treePlay,
    treeOfPair, blockLabelApply] using hrootmember

/-! ## Fixed finite classified table -/

noncomputable local instance rightSemanticClassifiedAllowedDecidable
    (source : ProfiledOpenRightViewClass A) :
    DecidablePred (ProfiledOpenRightClassifiedTableAllowed A source) :=
  fun _ => Classical.propDecidable _

/-- A winning semantic right view class yields one literal finite table whose
receiver entries retain the complete successor partition law. -/
noncomputable def profiledOpenRightClassifiedTableOfWinning
    (source : ProfiledOpenRightViewClass A)
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (entry : {root // root ∈ source.1} → ProcOnePairedEntryRep strategy)
    (minimum : {root // root ∈ source.1} → A.State)
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
    (hroot : ∀ member,
      profiledOpenRightRootOfWinning A strategy hwin (entry member)
        (minimum member) basis = member.1)
    (pivot : {root // root ∈ source.1})
    (hview : ∀ member,
      currentView Proc.one (entry member).leftHistory =
        currentView Proc.one (entry pivot).leftHistory) :
    ProfiledOpenRightClassifiedTable A source := by
  classical
  letI : Inhabited {root // root ∈ source.1} := ⟨pivot⟩
  let receiver :=
    profiledOpenRightSemanticClassifiedFamilyReceiver A source strategy hwin
      entry basis
  let sender := pairedRightSenderStrategy (entry pivot).lambdaOfStrategy
  letI : Inhabited (ProfiledOpenRightClassifiedOutput A) :=
    ⟨receiver [] default⟩
  exact locallyConsistentTableOfStrategies
    (finiteRootFamilyMonitor
      (fun member : {root // root ∈ source.1} =>
        profiledOpenRightClassifiedRootMonitor A member.1))
    (ProfiledOpenRightClassifiedTableAllowed A source)
    (receiver [])
    (profiledOpenRightSemanticClassifiedFamilyReceiver_allowed A source
      strategy hwin entry minimum basis [])
    receiver sender
    (profiledOpenRightSemanticClassifiedFamily_realizable A source strategy
      hwin entry minimum basis hroot pivot hview)
    (profiledOpenRightSemanticClassifiedFamilyReceiver_allowed A source
      strategy hwin entry minimum basis)

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- The fixed table retains universal-thread parity for every hidden source
member. -/
theorem profiledOpenRightClassifiedTableOfWinning_wins
    (source : ProfiledOpenRightViewClass A)
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (entry : {root // root ∈ source.1} → ProcOnePairedEntryRep strategy)
    (minimum : {root // root ∈ source.1} → A.State)
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
    (hroot : ∀ member,
      profiledOpenRightRootOfWinning A strategy hwin (entry member)
        (minimum member) basis = member.1)
    (pivot : {root // root ∈ source.1})
    (hview : ∀ member,
      currentView Proc.one (entry member).leftHistory =
        currentView Proc.one (entry pivot).leftHistory) :
    NarrowedAllThreadsWin
      (finiteRootFamilyMonitor
        (fun member : {root // root ∈ source.1} =>
          profiledOpenRightClassifiedRootMonitor A member.1))
      (profiledOpenRightClassifiedTableOfWinning A source strategy hwin entry
        minimum basis hroot pivot hview).toTransitionRationalTree.labeledTree := by
  classical
  letI : Inhabited {root // root ∈ source.1} := ⟨pivot⟩
  let receiver :=
    profiledOpenRightSemanticClassifiedFamilyReceiver A source strategy hwin
      entry basis
  let sender := pairedRightSenderStrategy (entry pivot).lambdaOfStrategy
  letI : Inhabited (ProfiledOpenRightClassifiedOutput A) :=
    ⟨receiver [] default⟩
  simpa [profiledOpenRightClassifiedTableOfWinning, receiver, sender] using
    (locallyConsistentTableOfStrategies_wins
      (finiteRootFamilyMonitor
        (fun member : {root // root ∈ source.1} =>
          profiledOpenRightClassifiedRootMonitor A member.1))
      (ProfiledOpenRightClassifiedTableAllowed A source)
      (receiver [])
      (profiledOpenRightSemanticClassifiedFamilyReceiver_allowed A source
        strategy hwin entry minimum basis [])
      receiver sender
      (profiledOpenRightSemanticClassifiedFamily_realizable A source strategy
        hwin entry minimum basis hroot pivot hview)
      (profiledOpenRightSemanticClassifiedFamilyReceiver_allowed A source
        strategy hwin entry minimum basis))

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- The extracted rational tree retains the complete successor-class law at
every node. -/
theorem profiledOpenRightClassifiedTableOfWinning_allowed
    (source : ProfiledOpenRightViewClass A)
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (entry : {root // root ∈ source.1} → ProcOnePairedEntryRep strategy)
    (minimum : {root // root ∈ source.1} → A.State)
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
    (hroot : ∀ member,
      profiledOpenRightRootOfWinning A strategy hwin (entry member)
        (minimum member) basis = member.1)
    (pivot : {root // root ∈ source.1})
    (hview : ∀ member,
      currentView Proc.one (entry member).leftHistory =
        currentView Proc.one (entry pivot).leftHistory) :
    NarrowedTablesAllowed
      (finiteRootFamilyMonitor
        (fun member : {root // root ∈ source.1} =>
          profiledOpenRightClassifiedRootMonitor A member.1))
      (ProfiledOpenRightClassifiedTableAllowed A source)
      (profiledOpenRightClassifiedTableOfWinning A source strategy hwin entry
        minimum basis hroot pivot hview).toTransitionRationalTree.labeledTree := by
  classical
  letI : Inhabited {root // root ∈ source.1} := ⟨pivot⟩
  let receiver :=
    profiledOpenRightSemanticClassifiedFamilyReceiver A source strategy hwin
      entry basis
  let sender := pairedRightSenderStrategy (entry pivot).lambdaOfStrategy
  letI : Inhabited (ProfiledOpenRightClassifiedOutput A) :=
    ⟨receiver [] default⟩
  simpa [profiledOpenRightClassifiedTableOfWinning, receiver, sender] using
    (locallyConsistentTableOfStrategies_allowed
      (finiteRootFamilyMonitor
        (fun member : {root // root ∈ source.1} =>
          profiledOpenRightClassifiedRootMonitor A member.1))
      (ProfiledOpenRightClassifiedTableAllowed A source)
      (receiver [])
      (profiledOpenRightSemanticClassifiedFamilyReceiver_allowed A source
        strategy hwin entry minimum basis [])
      receiver sender
      (profiledOpenRightSemanticClassifiedFamily_realizable A source strategy
        hwin entry minimum basis hroot pivot hview)
      (profiledOpenRightSemanticClassifiedFamilyReceiver_allowed A source
        strategy hwin entry minimum basis))

/-! ## Adapter from an arbitrary semantic view class -/

/-- Canonical root class obtained from any nonempty finite process-one view
class of one winning strategy. -/
noncomputable def profiledOpenRightSemanticSourceClass
    [Inhabited I] [Fintype I]
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
    ProfiledOpenRightViewClass A :=
  profiledOpenRightViewClassOfCompatible A
    (fun index => profiledOpenRightRootOfWinning A strategy hwin
      (entry index) (minimum index) basis)
    (profiledOpenRightFamilyCompatible_of_winning A strategy hwin entry
      minimum pivot hview basis)

/-- Semantic representative chosen for a member of the canonical source
class. -/
noncomputable def profiledOpenRightSemanticSourceEntry
    [Inhabited I] [Fintype I]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (entry : I → ProcOnePairedEntryRep strategy)
    (minimum : I → A.State) (pivot : I)
    (hview : ∀ index,
      currentView Proc.one (entry index).leftHistory =
        currentView Proc.one (entry pivot).leftHistory)
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
    (member : {root // root ∈
      (profiledOpenRightSemanticSourceClass A strategy hwin entry minimum
        pivot hview basis).1}) : ProcOnePairedEntryRep strategy :=
  entry (profiledOpenRightRootRepresentative A
    (fun index => profiledOpenRightRootOfWinning A strategy hwin
      (entry index) (minimum index) basis) member)

/-- Minimum summary paired with the same chosen representative. -/
noncomputable def profiledOpenRightSemanticSourceMinimum
    [Inhabited I] [Fintype I]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (entry : I → ProcOnePairedEntryRep strategy)
    (minimum : I → A.State) (pivot : I)
    (hview : ∀ index,
      currentView Proc.one (entry index).leftHistory =
        currentView Proc.one (entry pivot).leftHistory)
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
    (member : {root // root ∈
      (profiledOpenRightSemanticSourceClass A strategy hwin entry minimum
        pivot hview basis).1}) : A.State :=
  minimum (profiledOpenRightRootRepresentative A
    (fun index => profiledOpenRightRootOfWinning A strategy hwin
      (entry index) (minimum index) basis) member)

omit [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledOpenRightSemanticSource_root
    [Inhabited I] [Fintype I]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (entry : I → ProcOnePairedEntryRep strategy)
    (minimum : I → A.State) (pivot : I)
    (hview : ∀ index,
      currentView Proc.one (entry index).leftHistory =
        currentView Proc.one (entry pivot).leftHistory)
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
    (member : {root // root ∈
      (profiledOpenRightSemanticSourceClass A strategy hwin entry minimum
        pivot hview basis).1}) :
    profiledOpenRightRootOfWinning A strategy hwin
        (profiledOpenRightSemanticSourceEntry A strategy hwin entry minimum
          pivot hview basis member)
        (profiledOpenRightSemanticSourceMinimum A strategy hwin entry minimum
          pivot hview basis member) basis = member.1 := by
  exact profiledOpenRightRootRepresentative_spec A
    (fun index => profiledOpenRightRootOfWinning A strategy hwin
      (entry index) (minimum index) basis) member

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- End-to-end right classified move from an arbitrary finite semantic view
class.  The result exposes only the finite canonical source and finite table;
semantic histories occur solely in its proof. -/
theorem exists_profiledOpenRightClassifiedTable_of_winning_family
    [Inhabited I] [Fintype I]
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
    ∃ source : ProfiledOpenRightViewClass A,
      ∃ table : ProfiledOpenRightClassifiedTable A source,
        NarrowedAllThreadsWin
          (finiteRootFamilyMonitor
            (fun member : {root // root ∈ source.1} =>
              profiledOpenRightClassifiedRootMonitor A member.1))
          table.toTransitionRationalTree.labeledTree ∧
        NarrowedTablesAllowed
          (finiteRootFamilyMonitor
            (fun member : {root // root ∈ source.1} =>
              profiledOpenRightClassifiedRootMonitor A member.1))
          (ProfiledOpenRightClassifiedTableAllowed A source)
          table.toTransitionRationalTree.labeledTree := by
  classical
  let source := profiledOpenRightSemanticSourceClass A strategy hwin entry
    minimum pivot hview basis
  let canonicalEntry := profiledOpenRightSemanticSourceEntry A strategy hwin
    entry minimum pivot hview basis
  let canonicalMinimum := profiledOpenRightSemanticSourceMinimum A strategy
    hwin entry minimum pivot hview basis
  let canonicalPivot : {root // root ∈ source.1} :=
    ⟨source.2.1.choose, source.2.1.choose_spec⟩
  have hcanonicalView : ∀ member,
      currentView Proc.one (canonicalEntry member).leftHistory =
        currentView Proc.one (canonicalEntry canonicalPivot).leftHistory := by
    intro member
    exact (hview _).trans (hview _).symm
  have hcanonicalRoot : ∀ member,
      profiledOpenRightRootOfWinning A strategy hwin (canonicalEntry member)
        (canonicalMinimum member) basis = member.1 := by
    intro member
    exact profiledOpenRightSemanticSource_root A strategy hwin entry minimum
      pivot hview basis member
  let table := profiledOpenRightClassifiedTableOfWinning A source strategy hwin
    canonicalEntry canonicalMinimum basis hcanonicalRoot canonicalPivot
    hcanonicalView
  refine ⟨source, table, ?_, ?_⟩
  · exact profiledOpenRightClassifiedTableOfWinning_wins A source strategy hwin
      canonicalEntry canonicalMinimum basis hcanonicalRoot canonicalPivot
      hcanonicalView
  · exact profiledOpenRightClassifiedTableOfWinning_allowed A source strategy
      hwin canonicalEntry canonicalMinimum basis hcanonicalRoot canonicalPivot
      hcanonicalView

/-! ## Left-to-right mirror -/

noncomputable def profiledOpenLeftSemanticChildRoot
    (source : ProfiledOpenLeftViewClass A)
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (entry : {root // root ∈ source.1} → ProcTwoPairedEntryRep strategy)
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
    (member : {root // root ∈ source.1})
    (past : List (In₁ × In₂)) (move : In₁ × In₂)
    (row : PairedEntryRow) : ProfiledOpenRightRoot A :=
  profiledOpenRightRootOfWinning A strategy hwin
    (procOneViewClassChild strategy entry past move (member, row))
    (procOneViewClassChildMinimum A entry past (member, row)) basis

noncomputable def profiledOpenLeftSemanticChildClass
    (source : ProfiledOpenLeftViewClass A)
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (entry : {root // root ∈ source.1} → ProcTwoPairedEntryRep strategy)
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
    (member : {root // root ∈ source.1})
    (past : List (In₁ × In₂)) (move : In₁ × In₂)
    (row : PairedEntryRow) : ProfiledOpenRightViewClass A := by
  classical
  let pivot := (member, row)
  let members := {candidate // candidate ∈
    procOneChildViewClass strategy entry past move pivot}
  letI : Inhabited members :=
    ⟨⟨pivot, pivot_mem_procOneChildViewClass
      strategy entry past move pivot⟩⟩
  let roots : members → ProfiledOpenRightRoot A := fun candidate =>
    profiledOpenRightRootOfWinning A strategy hwin
      (procOneViewClassChild strategy entry past move candidate.1)
      (procOneViewClassChildMinimum A entry past candidate.1) basis
  have hcompatible : ProfiledOpenRightFamilyCompatible A roots := by
    simpa [roots, members, pivot] using
      (profiledOpenRightViewClassCompatible_of_winning A strategy hwin
        entry past move pivot basis)
  exact profiledOpenRightViewClassOfCompatible A roots hcompatible

omit [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledOpenLeftSemanticChildRoot_mem_class
    (source : ProfiledOpenLeftViewClass A)
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (entry : {root // root ∈ source.1} → ProcTwoPairedEntryRep strategy)
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
    (member : {root // root ∈ source.1})
    (past : List (In₁ × In₂)) (move : In₁ × In₂)
    (row : PairedEntryRow) :
    profiledOpenLeftSemanticChildRoot A source strategy hwin entry basis
        member past move row ∈
      (profiledOpenLeftSemanticChildClass A source strategy hwin entry basis
        member past move row).1 := by
  classical
  let pivot := (member, row)
  let members := {candidate // candidate ∈
    procOneChildViewClass strategy entry past move pivot}
  let pivotMember : members :=
    ⟨pivot, pivot_mem_procOneChildViewClass strategy entry past move pivot⟩
  change profiledOpenLeftSemanticChildRoot A source strategy hwin entry basis
      member past move row ∈
    profiledOpenRightRootImage A
      (fun candidate : members =>
        profiledOpenRightRootOfWinning A strategy hwin
          (procOneViewClassChild strategy entry past move candidate.1)
          (procOneViewClassChildMinimum A entry past candidate.1) basis)
  apply Finset.mem_image.mpr
  refine ⟨pivotMember, Finset.mem_univ _, ?_⟩
  rfl

noncomputable def profiledOpenLeftSemanticClassifiedReceiver
    (source : ProfiledOpenLeftViewClass A)
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (entry : {root // root ∈ source.1} → ProcTwoPairedEntryRep strategy)
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
    (member : {root // root ∈ source.1}) :
    ReceiverBlockStrategy In₁ In₂ (ProfiledOpenLeftClassifiedOutput A) :=
  fun past move =>
    (profiledLeftReceiverStrategy A (entry member).code
      (entry member).lambdaOfStrategy past move,
      fun row =>
        (profiledOpenLeftSemanticChildRoot A source strategy hwin entry basis
          member past move row,
         profiledOpenLeftSemanticChildClass A source strategy hwin entry basis
          member past move row))

noncomputable def profiledOpenLeftSemanticClassifiedFamilyReceiver
    (source : ProfiledOpenLeftViewClass A)
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (entry : {root // root ∈ source.1} → ProcTwoPairedEntryRep strategy)
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis) :
    ReceiverBlockStrategy ({root // root ∈ source.1} × In₁) In₂
      (ProfiledOpenLeftClassifiedOutput A) :=
  finiteRootFamilyReceiver
    (profiledOpenLeftSemanticClassifiedReceiver A source strategy hwin
      entry basis)

omit [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledOpenLeftSemanticClassifiedFamilyReceiver_allowed
    (source : ProfiledOpenLeftViewClass A)
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (entry : {root // root ∈ source.1} → ProcTwoPairedEntryRep strategy)
    (minimum : {root // root ∈ source.1} → A.State)
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
    (past : List (({root // root ∈ source.1} × In₁) × In₂)) :
    ProfiledOpenLeftClassifiedTableAllowed A source
      (profiledOpenLeftSemanticClassifiedFamilyReceiver A source strategy
        hwin entry basis past) := by
  intro member move row
  let physicalPast := past.map fun old => (old.1.2, old.2)
  constructor
  · simpa [profiledOpenLeftSemanticClassifiedFamilyReceiver,
      finiteRootFamilyReceiver,
      profiledOpenLeftSemanticClassifiedReceiver,
      profiledOpenLeftSemanticChildRoot, physicalPast] using
      (profiledLeftReceiverTarget_eq_procOneViewClassChildRoot A strategy
        hwin entry minimum basis member physicalPast move row)
  · exact profiledOpenLeftSemanticChildRoot_mem_class A source strategy hwin
      entry basis member physicalPast move row

omit [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledOpenLeftSemanticClassifiedFamily_realizable
    (source : ProfiledOpenLeftViewClass A)
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (entry : {root // root ∈ source.1} → ProcTwoPairedEntryRep strategy)
    (minimum : {root // root ∈ source.1} → A.State)
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
    (hroot : ∀ member,
      profiledOpenLeftRootOfWinning A strategy hwin (entry member)
        (minimum member) basis = member.1)
    (pivot : {root // root ∈ source.1})
    (hview : ∀ member,
      currentView Proc.two (entry member).rightHistory =
        currentView Proc.two (entry pivot).rightHistory) :
    ∀ env,
      (finiteRootFamilyMonitor
        (fun member : {root // root ∈ source.1} =>
          profiledOpenLeftClassifiedRootMonitor A member.1)).WinsPlay
        (pairPlay
          (profiledOpenLeftSemanticClassifiedFamilyReceiver A source strategy
            hwin entry basis)
          (pairedLeftSenderStrategy (entry pivot).lambdaOfStrategy) env) := by
  apply finiteRootFamily_realizable
  intro member env
  apply (BlockRecordMonitor.comapReceiverOutput_wins_iff
    (profiledOpenLeftRootMonitor A member.1)
    (fun output : ProfiledOpenLeftClassifiedOutput A => output.1) _).mpr
  have hmember := profiledOpenLeftBlockMonitor_realizable_of_winning A
    strategy hwin (entry member) (minimum member) basis env
  have hsender :
      pairedLeftSenderStrategy (entry member).lambdaOfStrategy =
        pairedLeftSenderStrategy (entry pivot).lambdaOfStrategy := by
    unfold pairedLeftSenderStrategy
    exact blockSenderTwo_eq_of_view_eq strategy (hview member)
  have hrootmember :
      (profiledOpenLeftRootMonitor A
        (profiledOpenLeftRootOfWinning A strategy hwin (entry member)
          (minimum member) basis)).WinsPlay
        (pairPlay
          (profiledLeftReceiverStrategy A (entry member).code
            (entry member).lambdaOfStrategy)
          (pairedLeftSenderStrategy (entry member).lambdaOfStrategy) env) := by
    simpa [profiledOpenLeftRootOfWinning] using hmember
  rw [hroot member, hsender] at hrootmember
  simpa [BlockRecordMonitor.projectReceiverPlay,
    profiledOpenLeftSemanticClassifiedReceiver, pairPlay, treePlay,
    treeOfPair, blockLabelApply] using hrootmember

noncomputable local instance leftSemanticClassifiedAllowedDecidable
    (source : ProfiledOpenLeftViewClass A) :
    DecidablePred (ProfiledOpenLeftClassifiedTableAllowed A source) :=
  fun _ => Classical.propDecidable _

noncomputable def profiledOpenLeftClassifiedTableOfWinning
    (source : ProfiledOpenLeftViewClass A)
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (entry : {root // root ∈ source.1} → ProcTwoPairedEntryRep strategy)
    (minimum : {root // root ∈ source.1} → A.State)
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
    (hroot : ∀ member,
      profiledOpenLeftRootOfWinning A strategy hwin (entry member)
        (minimum member) basis = member.1)
    (pivot : {root // root ∈ source.1})
    (hview : ∀ member,
      currentView Proc.two (entry member).rightHistory =
        currentView Proc.two (entry pivot).rightHistory) :
    ProfiledOpenLeftClassifiedTable A source := by
  classical
  letI : Inhabited {root // root ∈ source.1} := ⟨pivot⟩
  let receiver :=
    profiledOpenLeftSemanticClassifiedFamilyReceiver A source strategy hwin
      entry basis
  let sender := pairedLeftSenderStrategy (entry pivot).lambdaOfStrategy
  letI : Inhabited (ProfiledOpenLeftClassifiedOutput A) :=
    ⟨receiver [] default⟩
  exact locallyConsistentTableOfStrategies
    (finiteRootFamilyMonitor
      (fun member : {root // root ∈ source.1} =>
        profiledOpenLeftClassifiedRootMonitor A member.1))
    (ProfiledOpenLeftClassifiedTableAllowed A source)
    (receiver [])
    (profiledOpenLeftSemanticClassifiedFamilyReceiver_allowed A source
      strategy hwin entry minimum basis [])
    receiver sender
    (profiledOpenLeftSemanticClassifiedFamily_realizable A source strategy
      hwin entry minimum basis hroot pivot hview)
    (profiledOpenLeftSemanticClassifiedFamilyReceiver_allowed A source
      strategy hwin entry minimum basis)

omit [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledOpenLeftClassifiedTableOfWinning_wins
    (source : ProfiledOpenLeftViewClass A)
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (entry : {root // root ∈ source.1} → ProcTwoPairedEntryRep strategy)
    (minimum : {root // root ∈ source.1} → A.State)
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
    (hroot : ∀ member,
      profiledOpenLeftRootOfWinning A strategy hwin (entry member)
        (minimum member) basis = member.1)
    (pivot : {root // root ∈ source.1})
    (hview : ∀ member,
      currentView Proc.two (entry member).rightHistory =
        currentView Proc.two (entry pivot).rightHistory) :
    NarrowedAllThreadsWin
      (finiteRootFamilyMonitor
        (fun member : {root // root ∈ source.1} =>
          profiledOpenLeftClassifiedRootMonitor A member.1))
      (profiledOpenLeftClassifiedTableOfWinning A source strategy hwin entry
        minimum basis hroot pivot hview).toTransitionRationalTree.labeledTree := by
  classical
  letI : Inhabited {root // root ∈ source.1} := ⟨pivot⟩
  let receiver :=
    profiledOpenLeftSemanticClassifiedFamilyReceiver A source strategy hwin
      entry basis
  let sender := pairedLeftSenderStrategy (entry pivot).lambdaOfStrategy
  letI : Inhabited (ProfiledOpenLeftClassifiedOutput A) :=
    ⟨receiver [] default⟩
  simpa [profiledOpenLeftClassifiedTableOfWinning, receiver, sender] using
    (locallyConsistentTableOfStrategies_wins
      (finiteRootFamilyMonitor
        (fun member : {root // root ∈ source.1} =>
          profiledOpenLeftClassifiedRootMonitor A member.1))
      (ProfiledOpenLeftClassifiedTableAllowed A source)
      (receiver [])
      (profiledOpenLeftSemanticClassifiedFamilyReceiver_allowed A source
        strategy hwin entry minimum basis [])
      receiver sender
      (profiledOpenLeftSemanticClassifiedFamily_realizable A source strategy
        hwin entry minimum basis hroot pivot hview)
      (profiledOpenLeftSemanticClassifiedFamilyReceiver_allowed A source
        strategy hwin entry minimum basis))

omit [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledOpenLeftClassifiedTableOfWinning_allowed
    (source : ProfiledOpenLeftViewClass A)
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (entry : {root // root ∈ source.1} → ProcTwoPairedEntryRep strategy)
    (minimum : {root // root ∈ source.1} → A.State)
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
    (hroot : ∀ member,
      profiledOpenLeftRootOfWinning A strategy hwin (entry member)
        (minimum member) basis = member.1)
    (pivot : {root // root ∈ source.1})
    (hview : ∀ member,
      currentView Proc.two (entry member).rightHistory =
        currentView Proc.two (entry pivot).rightHistory) :
    NarrowedTablesAllowed
      (finiteRootFamilyMonitor
        (fun member : {root // root ∈ source.1} =>
          profiledOpenLeftClassifiedRootMonitor A member.1))
      (ProfiledOpenLeftClassifiedTableAllowed A source)
      (profiledOpenLeftClassifiedTableOfWinning A source strategy hwin entry
        minimum basis hroot pivot hview).toTransitionRationalTree.labeledTree := by
  classical
  letI : Inhabited {root // root ∈ source.1} := ⟨pivot⟩
  let receiver :=
    profiledOpenLeftSemanticClassifiedFamilyReceiver A source strategy hwin
      entry basis
  let sender := pairedLeftSenderStrategy (entry pivot).lambdaOfStrategy
  letI : Inhabited (ProfiledOpenLeftClassifiedOutput A) :=
    ⟨receiver [] default⟩
  simpa [profiledOpenLeftClassifiedTableOfWinning, receiver, sender] using
    (locallyConsistentTableOfStrategies_allowed
      (finiteRootFamilyMonitor
        (fun member : {root // root ∈ source.1} =>
          profiledOpenLeftClassifiedRootMonitor A member.1))
      (ProfiledOpenLeftClassifiedTableAllowed A source)
      (receiver [])
      (profiledOpenLeftSemanticClassifiedFamilyReceiver_allowed A source
        strategy hwin entry minimum basis [])
      receiver sender
      (profiledOpenLeftSemanticClassifiedFamily_realizable A source strategy
        hwin entry minimum basis hroot pivot hview)
      (profiledOpenLeftSemanticClassifiedFamilyReceiver_allowed A source
        strategy hwin entry minimum basis))

noncomputable def profiledOpenLeftSemanticSourceClass
    [Inhabited I] [Fintype I]
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
    ProfiledOpenLeftViewClass A :=
  profiledOpenLeftViewClassOfCompatible A
    (fun index => profiledOpenLeftRootOfWinning A strategy hwin
      (entry index) (minimum index) basis)
    (profiledOpenLeftFamilyCompatible_of_winning A strategy hwin entry
      minimum pivot hview basis)

noncomputable def profiledOpenLeftSemanticSourceEntry
    [Inhabited I] [Fintype I]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (entry : I → ProcTwoPairedEntryRep strategy)
    (minimum : I → A.State) (pivot : I)
    (hview : ∀ index,
      currentView Proc.two (entry index).rightHistory =
        currentView Proc.two (entry pivot).rightHistory)
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
    (member : {root // root ∈
      (profiledOpenLeftSemanticSourceClass A strategy hwin entry minimum
        pivot hview basis).1}) : ProcTwoPairedEntryRep strategy :=
  entry (profiledOpenLeftRootRepresentative A
    (fun index => profiledOpenLeftRootOfWinning A strategy hwin
      (entry index) (minimum index) basis) member)

noncomputable def profiledOpenLeftSemanticSourceMinimum
    [Inhabited I] [Fintype I]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (entry : I → ProcTwoPairedEntryRep strategy)
    (minimum : I → A.State) (pivot : I)
    (hview : ∀ index,
      currentView Proc.two (entry index).rightHistory =
        currentView Proc.two (entry pivot).rightHistory)
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
    (member : {root // root ∈
      (profiledOpenLeftSemanticSourceClass A strategy hwin entry minimum
        pivot hview basis).1}) : A.State :=
  minimum (profiledOpenLeftRootRepresentative A
    (fun index => profiledOpenLeftRootOfWinning A strategy hwin
      (entry index) (minimum index) basis) member)

omit [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledOpenLeftSemanticSource_root
    [Inhabited I] [Fintype I]
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (entry : I → ProcTwoPairedEntryRep strategy)
    (minimum : I → A.State) (pivot : I)
    (hview : ∀ index,
      currentView Proc.two (entry index).rightHistory =
        currentView Proc.two (entry pivot).rightHistory)
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
    (member : {root // root ∈
      (profiledOpenLeftSemanticSourceClass A strategy hwin entry minimum
        pivot hview basis).1}) :
    profiledOpenLeftRootOfWinning A strategy hwin
        (profiledOpenLeftSemanticSourceEntry A strategy hwin entry minimum
          pivot hview basis member)
        (profiledOpenLeftSemanticSourceMinimum A strategy hwin entry minimum
          pivot hview basis member) basis = member.1 := by
  exact profiledOpenLeftRootRepresentative_spec A
    (fun index => profiledOpenLeftRootOfWinning A strategy hwin
      (entry index) (minimum index) basis) member

omit [Inhabited Out₁] [Inhabited Out₂] in
theorem exists_profiledOpenLeftClassifiedTable_of_winning_family
    [Inhabited I] [Fintype I]
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
    ∃ source : ProfiledOpenLeftViewClass A,
      ∃ table : ProfiledOpenLeftClassifiedTable A source,
        NarrowedAllThreadsWin
          (finiteRootFamilyMonitor
            (fun member : {root // root ∈ source.1} =>
              profiledOpenLeftClassifiedRootMonitor A member.1))
          table.toTransitionRationalTree.labeledTree ∧
        NarrowedTablesAllowed
          (finiteRootFamilyMonitor
            (fun member : {root // root ∈ source.1} =>
              profiledOpenLeftClassifiedRootMonitor A member.1))
          (ProfiledOpenLeftClassifiedTableAllowed A source)
          table.toTransitionRationalTree.labeledTree := by
  classical
  let source := profiledOpenLeftSemanticSourceClass A strategy hwin entry
    minimum pivot hview basis
  let canonicalEntry := profiledOpenLeftSemanticSourceEntry A strategy hwin
    entry minimum pivot hview basis
  let canonicalMinimum := profiledOpenLeftSemanticSourceMinimum A strategy
    hwin entry minimum pivot hview basis
  let canonicalPivot : {root // root ∈ source.1} :=
    ⟨source.2.1.choose, source.2.1.choose_spec⟩
  have hcanonicalView : ∀ member,
      currentView Proc.two (canonicalEntry member).rightHistory =
        currentView Proc.two (canonicalEntry canonicalPivot).rightHistory := by
    intro member
    exact (hview _).trans (hview _).symm
  have hcanonicalRoot : ∀ member,
      profiledOpenLeftRootOfWinning A strategy hwin (canonicalEntry member)
        (canonicalMinimum member) basis = member.1 := by
    intro member
    exact profiledOpenLeftSemanticSource_root A strategy hwin entry minimum
      pivot hview basis member
  let table := profiledOpenLeftClassifiedTableOfWinning A source strategy hwin
    canonicalEntry canonicalMinimum basis hcanonicalRoot canonicalPivot
    hcanonicalView
  refine ⟨source, table, ?_, ?_⟩
  · exact profiledOpenLeftClassifiedTableOfWinning_wins A source strategy hwin
      canonicalEntry canonicalMinimum basis hcanonicalRoot canonicalPivot
      hcanonicalView
  · exact profiledOpenLeftClassifiedTableOfWinning_allowed A source strategy
      hwin canonicalEntry canonicalMinimum basis hcanonicalRoot canonicalPivot
      hcanonicalView

end

end


end DetParityAutomaton

end DistributedSynthesis
