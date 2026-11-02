/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledOpenClassifiedPolicy

/-!
# Semantic representability of classified successor families

Compatibility says that a finite root family has one common blind sender.
For recursive assembly we retain the stronger, but still proof-only, fact
that the family is the canonical image of entries of one winning distributed
strategy with one common blind local view.  This property contains no local
leader or orientation signal and does not enlarge the finite move alphabet.

The semantic classified receiver advertises exactly such families.  A later
label restriction can therefore preserve representability through the single
state-controlled extraction, making the next history move available without
a continuation quotient or a circular monitor definition.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

section

noncomputable section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

/-- A canonical right class is represented by entries of one winning raw
strategy that have one process-one local view.  The classical rational-run
basis is recorded only because it is used to package the finite open roots. -/
def ProfiledOpenRightViewClass.SemanticallyRepresentable
    (source : ProfiledOpenRightViewClass A) : Prop :=
  ∃ (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
      (hwin : ∀ env : EnvironmentSequence In₁ In₂,
        A.Accepts (execution strategy env))
      (basis : ∀ state : PairedProfiledTreeState A,
        (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
      (entry : {root // root ∈ source.1} → ProcOnePairedEntryRep strategy)
      (minimum : {root // root ∈ source.1} → A.State)
      (pivot : {root // root ∈ source.1}),
    (∀ member,
      currentView Proc.one (entry member).leftHistory =
        currentView Proc.one (entry pivot).leftHistory) ∧
    (∀ member,
      profiledOpenRightRootOfWinning A strategy hwin (entry member)
        (minimum member) basis = member.1)

/-- Left-oriented semantic representation. -/
def ProfiledOpenLeftViewClass.SemanticallyRepresentable
    (source : ProfiledOpenLeftViewClass A) : Prop :=
  ∃ (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
      (hwin : ∀ env : EnvironmentSequence In₁ In₂,
        A.Accepts (execution strategy env))
      (basis : ∀ state : PairedProfiledTreeState A,
        (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
      (entry : {root // root ∈ source.1} → ProcTwoPairedEntryRep strategy)
      (minimum : {root // root ∈ source.1} → A.State)
      (pivot : {root // root ∈ source.1}),
    (∀ member,
      currentView Proc.two (entry member).rightHistory =
        currentView Proc.two (entry pivot).rightHistory) ∧
    (∀ member,
      profiledOpenLeftRootOfWinning A strategy hwin (entry member)
        (minimum member) basis = member.1)

section
omit [Inhabited Out₁] [Inhabited Out₂]

/-- Every canonical source class built from a raw process-one view class
retains its semantic representatives. -/
theorem profiledOpenRightSemanticSourceClass_representable
    {I : Type*} [Inhabited I] [Fintype I]
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
    (profiledOpenRightSemanticSourceClass A strategy hwin entry minimum pivot
      hview basis).SemanticallyRepresentable A := by
  let source := profiledOpenRightSemanticSourceClass A strategy hwin entry
    minimum pivot hview basis
  let canonicalEntry := profiledOpenRightSemanticSourceEntry A strategy hwin
    entry minimum pivot hview basis
  let canonicalMinimum := profiledOpenRightSemanticSourceMinimum A strategy
    hwin entry minimum pivot hview basis
  let canonicalPivot : {root // root ∈ source.1} :=
    ⟨source.2.1.choose, source.2.1.choose_spec⟩
  refine ⟨strategy, hwin, basis, canonicalEntry, canonicalMinimum,
    canonicalPivot, ?_, ?_⟩
  · intro member
    exact (hview _).trans (hview _).symm
  · intro member
    exact profiledOpenRightSemanticSource_root A strategy hwin entry minimum
      pivot hview basis member

/-- Left source mirror. -/
theorem profiledOpenLeftSemanticSourceClass_representable
    {I : Type*} [Inhabited I] [Fintype I]
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
    (profiledOpenLeftSemanticSourceClass A strategy hwin entry minimum pivot
      hview basis).SemanticallyRepresentable A := by
  let source := profiledOpenLeftSemanticSourceClass A strategy hwin entry
    minimum pivot hview basis
  let canonicalEntry := profiledOpenLeftSemanticSourceEntry A strategy hwin
    entry minimum pivot hview basis
  let canonicalMinimum := profiledOpenLeftSemanticSourceMinimum A strategy
    hwin entry minimum pivot hview basis
  let canonicalPivot : {root // root ∈ source.1} :=
    ⟨source.2.1.choose, source.2.1.choose_spec⟩
  refine ⟨strategy, hwin, basis, canonicalEntry, canonicalMinimum,
    canonicalPivot, ?_, ?_⟩
  · intro member
    exact (hview _).trans (hview _).symm
  · intro member
    exact profiledOpenLeftSemanticSource_root A strategy hwin entry minimum
      pivot hview basis member

/-- Every process-two successor class advertised by the semantic right block
is itself represented by the corresponding fresh entries of the same raw
winning strategy. -/
theorem profiledOpenRightSemanticChildClass_representable
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
    (profiledOpenRightSemanticChildClass A source strategy hwin entry basis
      member past move row).SemanticallyRepresentable A := by
  classical
  let pivot := (member, row)
  let members := {candidate // candidate ∈
    procTwoChildViewClass strategy entry past move pivot}
  let pivotMember : members :=
    ⟨pivot, pivot_mem_procTwoChildViewClass strategy entry past move pivot⟩
  letI : Inhabited members := ⟨pivotMember⟩
  let childEntry : members → ProcTwoPairedEntryRep strategy := fun candidate =>
    procTwoViewClassChild strategy entry past move candidate.1
  let childMinimum : members → A.State := fun candidate =>
    procTwoViewClassChildMinimum A entry past candidate.1
  have hchildView : ∀ candidate,
      currentView Proc.two (childEntry candidate).rightHistory =
        currentView Proc.two (childEntry pivotMember).rightHistory := by
    intro candidate
    exact (mem_procTwoChildViewClass strategy entry past move pivot
      candidate.1).mp candidate.2
  have hclass :
      profiledOpenRightSemanticChildClass A source strategy hwin entry basis
          member past move row =
        profiledOpenLeftSemanticSourceClass A strategy hwin childEntry
          childMinimum pivotMember hchildView basis := by
    apply Subtype.ext
    rfl
  rw [hclass]
  exact profiledOpenLeftSemanticSourceClass_representable A strategy hwin
    childEntry childMinimum pivotMember hchildView basis

/-- Left-to-right successor mirror. -/
theorem profiledOpenLeftSemanticChildClass_representable
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
    (profiledOpenLeftSemanticChildClass A source strategy hwin entry basis
      member past move row).SemanticallyRepresentable A := by
  classical
  let pivot := (member, row)
  let members := {candidate // candidate ∈
    procOneChildViewClass strategy entry past move pivot}
  let pivotMember : members :=
    ⟨pivot, pivot_mem_procOneChildViewClass strategy entry past move pivot⟩
  letI : Inhabited members := ⟨pivotMember⟩
  let childEntry : members → ProcOnePairedEntryRep strategy := fun candidate =>
    procOneViewClassChild strategy entry past move candidate.1
  let childMinimum : members → A.State := fun candidate =>
    procOneViewClassChildMinimum A entry past candidate.1
  have hchildView : ∀ candidate,
      currentView Proc.one (childEntry candidate).leftHistory =
        currentView Proc.one (childEntry pivotMember).leftHistory := by
    intro candidate
    exact (mem_procOneChildViewClass strategy entry past move pivot
      candidate.1).mp candidate.2
  have hclass :
      profiledOpenLeftSemanticChildClass A source strategy hwin entry basis
          member past move row =
        profiledOpenRightSemanticSourceClass A strategy hwin childEntry
          childMinimum pivotMember hchildView basis := by
    apply Subtype.ext
    rfl
  rw [hclass]
  exact profiledOpenRightSemanticSourceClass_representable A strategy hwin
    childEntry childMinimum pivotMember hchildView basis

end

/-! ## Sticky representability law for complete receiver tables -/

/-- The corrected right table law: besides the exact target/class equation,
every advertised successor class carries a raw semantic representation from
which its next finite move can be built. -/
def ProfiledOpenRightRepresentableTableAllowed
    (source : ProfiledOpenRightViewClass A)
    (responses :
      ({root // root ∈ source.1} × In₂) × In₁ →
        ProfiledOpenRightClassifiedOutput A) : Prop :=
  ProfiledOpenRightClassifiedTableAllowed A source responses ∧
    ∀ member (move : In₂ × In₁) row,
      ProfiledOpenLeftViewClass.SemanticallyRepresentable A
        ((responses ((member, move.1), move.2)).2 row).2

/-- Left corrected table law. -/
def ProfiledOpenLeftRepresentableTableAllowed
    (source : ProfiledOpenLeftViewClass A)
    (responses :
      ({root // root ∈ source.1} × In₁) × In₂ →
        ProfiledOpenLeftClassifiedOutput A) : Prop :=
  ProfiledOpenLeftClassifiedTableAllowed A source responses ∧
    ∀ member (move : In₁ × In₂) row,
      ProfiledOpenRightViewClass.SemanticallyRepresentable A
        ((responses ((member, move.1), move.2)).2 row).2

noncomputable local instance rightRepresentableAllowedDecidable
    (source : ProfiledOpenRightViewClass A) :
    DecidablePred (ProfiledOpenRightRepresentableTableAllowed A source) :=
  fun _ => Classical.propDecidable _

noncomputable local instance leftRepresentableAllowedDecidable
    (source : ProfiledOpenLeftViewClass A) :
    DecidablePred (ProfiledOpenLeftRepresentableTableAllowed A source) :=
  fun _ => Classical.propDecidable _

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- The complete semantic receiver table satisfies the strengthened law at
every past.  This is the closure fact that was absent from the first
classified automaton. -/
theorem profiledOpenRightSemanticClassifiedFamilyReceiver_representable
    (source : ProfiledOpenRightViewClass A)
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (entry : {root // root ∈ source.1} → ProcOnePairedEntryRep strategy)
    (minimum : {root // root ∈ source.1} → A.State)
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
    (past : List (({root // root ∈ source.1} × In₂) × In₁)) :
    ProfiledOpenRightRepresentableTableAllowed A source
      (profiledOpenRightSemanticClassifiedFamilyReceiver A source strategy
        hwin entry basis past) := by
  constructor
  · exact profiledOpenRightSemanticClassifiedFamilyReceiver_allowed A source
      strategy hwin entry minimum basis past
  · intro member move row
    let physicalPast := past.map fun old => (old.1.2, old.2)
    simpa [profiledOpenRightSemanticClassifiedFamilyReceiver,
      finiteRootFamilyReceiver,
      profiledOpenRightSemanticClassifiedReceiver, physicalPast] using
      (profiledOpenRightSemanticChildClass_representable A source strategy
        hwin entry basis member physicalPast move row)

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Left semantic table mirror. -/
theorem profiledOpenLeftSemanticClassifiedFamilyReceiver_representable
    (source : ProfiledOpenLeftViewClass A)
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (entry : {root // root ∈ source.1} → ProcTwoPairedEntryRep strategy)
    (minimum : {root // root ∈ source.1} → A.State)
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
    (past : List (({root // root ∈ source.1} × In₁) × In₂)) :
    ProfiledOpenLeftRepresentableTableAllowed A source
      (profiledOpenLeftSemanticClassifiedFamilyReceiver A source strategy
        hwin entry basis past) := by
  constructor
  · exact profiledOpenLeftSemanticClassifiedFamilyReceiver_allowed A source
      strategy hwin entry minimum basis past
  · intro member move row
    let physicalPast := past.map fun old => (old.1.2, old.2)
    simpa [profiledOpenLeftSemanticClassifiedFamilyReceiver,
      finiteRootFamilyReceiver,
      profiledOpenLeftSemanticClassifiedReceiver, physicalPast] using
      (profiledOpenLeftSemanticChildClass_representable A source strategy
        hwin entry basis member physicalPast move row)

/-- Literal finite right table type whose accepting labels retain semantic
representability of every successor class. -/
noncomputable abbrev ProfiledOpenRightRepresentableTable
    (source : ProfiledOpenRightViewClass A) :=
  LocallyConsistentNarrowedTable
    (finiteRootFamilyMonitor
      (fun member : {root // root ∈ source.1} =>
        profiledOpenRightClassifiedRootMonitor A member.1))
    (ProfiledOpenRightRepresentableTableAllowed A source)

/-- Left strengthened finite table type. -/
noncomputable abbrev ProfiledOpenLeftRepresentableTable
    (source : ProfiledOpenLeftViewClass A) :=
  LocallyConsistentNarrowedTable
    (finiteRootFamilyMonitor
      (fun member : {root // root ∈ source.1} =>
        profiledOpenLeftClassifiedRootMonitor A member.1))
    (ProfiledOpenLeftRepresentableTableAllowed A source)

noncomputable instance (source : ProfiledOpenRightViewClass A) :
    Fintype (ProfiledOpenRightRepresentableTable A source) := by
  classical
  infer_instance

noncomputable instance (source : ProfiledOpenLeftViewClass A) :
    Fintype (ProfiledOpenLeftRepresentableTable A source) := by
  classical
  infer_instance

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- A represented right class yields one strengthened finite table.  Both
universal-thread parity and successor representability survive the same
state-controlled extraction. -/
theorem ProfiledOpenRightViewClass.exists_representableTable
    (source : ProfiledOpenRightViewClass A)
    (hrep : source.SemanticallyRepresentable A) :
    ∃ table : ProfiledOpenRightRepresentableTable A source,
      NarrowedAllThreadsWin
          (finiteRootFamilyMonitor
            (fun member : {root // root ∈ source.1} =>
              profiledOpenRightClassifiedRootMonitor A member.1))
          table.toTransitionRationalTree.labeledTree ∧
        NarrowedTablesAllowed
          (finiteRootFamilyMonitor
            (fun member : {root // root ∈ source.1} =>
              profiledOpenRightClassifiedRootMonitor A member.1))
          (ProfiledOpenRightRepresentableTableAllowed A source)
          table.toTransitionRationalTree.labeledTree := by
  classical
  rcases hrep with
    ⟨strategy, hwin, basis, entry, minimum, pivot, hview, hroot⟩
  let receiver :=
    profiledOpenRightSemanticClassifiedFamilyReceiver A source strategy hwin
      entry basis
  let sender := pairedRightSenderStrategy (entry pivot).lambdaOfStrategy
  letI : Inhabited {root // root ∈ source.1} := ⟨pivot⟩
  letI : Inhabited (ProfiledOpenRightClassifiedOutput A) :=
    ⟨receiver [] default⟩
  let table : ProfiledOpenRightRepresentableTable A source :=
    locallyConsistentTableOfStrategies
      (finiteRootFamilyMonitor
        (fun member : {root // root ∈ source.1} =>
          profiledOpenRightClassifiedRootMonitor A member.1))
      (ProfiledOpenRightRepresentableTableAllowed A source)
      (receiver [] )
      (profiledOpenRightSemanticClassifiedFamilyReceiver_representable A
        source strategy hwin entry minimum basis [])
      receiver sender
      (profiledOpenRightSemanticClassifiedFamily_realizable A source strategy
        hwin entry minimum basis hroot pivot hview)
      (profiledOpenRightSemanticClassifiedFamilyReceiver_representable A
        source strategy hwin entry minimum basis)
  refine ⟨table, ?_, ?_⟩
  · exact locallyConsistentTableOfStrategies_wins
      (finiteRootFamilyMonitor
        (fun member : {root // root ∈ source.1} =>
          profiledOpenRightClassifiedRootMonitor A member.1))
      (ProfiledOpenRightRepresentableTableAllowed A source)
      (receiver [])
      (profiledOpenRightSemanticClassifiedFamilyReceiver_representable A
        source strategy hwin entry minimum basis [])
      receiver sender
      (profiledOpenRightSemanticClassifiedFamily_realizable A source strategy
        hwin entry minimum basis hroot pivot hview)
      (profiledOpenRightSemanticClassifiedFamilyReceiver_representable A
        source strategy hwin entry minimum basis)
  · exact locallyConsistentTableOfStrategies_allowed
      (finiteRootFamilyMonitor
        (fun member : {root // root ∈ source.1} =>
          profiledOpenRightClassifiedRootMonitor A member.1))
      (ProfiledOpenRightRepresentableTableAllowed A source)
      (receiver [])
      (profiledOpenRightSemanticClassifiedFamilyReceiver_representable A
        source strategy hwin entry minimum basis [])
      receiver sender
      (profiledOpenRightSemanticClassifiedFamily_realizable A source strategy
        hwin entry minimum basis hroot pivot hview)
      (profiledOpenRightSemanticClassifiedFamilyReceiver_representable A
        source strategy hwin entry minimum basis)

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Strengthened left extraction. -/
theorem ProfiledOpenLeftViewClass.exists_representableTable
    (source : ProfiledOpenLeftViewClass A)
    (hrep : source.SemanticallyRepresentable A) :
    ∃ table : ProfiledOpenLeftRepresentableTable A source,
      NarrowedAllThreadsWin
          (finiteRootFamilyMonitor
            (fun member : {root // root ∈ source.1} =>
              profiledOpenLeftClassifiedRootMonitor A member.1))
          table.toTransitionRationalTree.labeledTree ∧
        NarrowedTablesAllowed
          (finiteRootFamilyMonitor
            (fun member : {root // root ∈ source.1} =>
              profiledOpenLeftClassifiedRootMonitor A member.1))
          (ProfiledOpenLeftRepresentableTableAllowed A source)
          table.toTransitionRationalTree.labeledTree := by
  classical
  rcases hrep with
    ⟨strategy, hwin, basis, entry, minimum, pivot, hview, hroot⟩
  let receiver :=
    profiledOpenLeftSemanticClassifiedFamilyReceiver A source strategy hwin
      entry basis
  let sender := pairedLeftSenderStrategy (entry pivot).lambdaOfStrategy
  letI : Inhabited {root // root ∈ source.1} := ⟨pivot⟩
  letI : Inhabited (ProfiledOpenLeftClassifiedOutput A) :=
    ⟨receiver [] default⟩
  let table : ProfiledOpenLeftRepresentableTable A source :=
    locallyConsistentTableOfStrategies
      (finiteRootFamilyMonitor
        (fun member : {root // root ∈ source.1} =>
          profiledOpenLeftClassifiedRootMonitor A member.1))
      (ProfiledOpenLeftRepresentableTableAllowed A source)
      (receiver [])
      (profiledOpenLeftSemanticClassifiedFamilyReceiver_representable A
        source strategy hwin entry minimum basis [])
      receiver sender
      (profiledOpenLeftSemanticClassifiedFamily_realizable A source strategy
        hwin entry minimum basis hroot pivot hview)
      (profiledOpenLeftSemanticClassifiedFamilyReceiver_representable A
        source strategy hwin entry minimum basis)
  refine ⟨table, ?_, ?_⟩
  · exact locallyConsistentTableOfStrategies_wins
      (finiteRootFamilyMonitor
        (fun member : {root // root ∈ source.1} =>
          profiledOpenLeftClassifiedRootMonitor A member.1))
      (ProfiledOpenLeftRepresentableTableAllowed A source)
      (receiver [])
      (profiledOpenLeftSemanticClassifiedFamilyReceiver_representable A
        source strategy hwin entry minimum basis [])
      receiver sender
      (profiledOpenLeftSemanticClassifiedFamily_realizable A source strategy
        hwin entry minimum basis hroot pivot hview)
      (profiledOpenLeftSemanticClassifiedFamilyReceiver_representable A
        source strategy hwin entry minimum basis)
  · exact locallyConsistentTableOfStrategies_allowed
      (finiteRootFamilyMonitor
        (fun member : {root // root ∈ source.1} =>
          profiledOpenLeftClassifiedRootMonitor A member.1))
      (ProfiledOpenLeftRepresentableTableAllowed A source)
      (receiver [])
      (profiledOpenLeftSemanticClassifiedFamilyReceiver_representable A
        source strategy hwin entry minimum basis [])
      receiver sender
      (profiledOpenLeftSemanticClassifiedFamily_realizable A source strategy
        hwin entry minimum basis hroot pivot hview)
      (profiledOpenLeftSemanticClassifiedFamilyReceiver_representable A
        source strategy hwin entry minimum basis)

/-! ## Coherent actual-play readback -/

/-- Induced receiver output of a strengthened right table on the genuine
monitor thread. -/
noncomputable def profiledOpenRightRepresentableOutputAt
    (source : ProfiledOpenRightViewClass A)
    (table : ProfiledOpenRightRepresentableTable A source)
    (member : {root // root ∈ source.1})
    (env : Nat → In₂ × In₁) (n : Nat) :
    ProfiledOpenRightClassifiedOutput A :=
  (treePlay
    (narrowedInducedTree
      (finiteRootFamilyMonitor
        (fun candidate : {root // root ∈ source.1} =>
          profiledOpenRightClassifiedRootMonitor A candidate.1))
      table.toTransitionRationalTree.labeledTree)
    (tagFiniteRootEnvironment member env) n).2.1

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- The successor class actually emitted by a strengthened right table is
semantically represented. -/
theorem profiledOpenRightRepresentableOutputAt_class
    (source : ProfiledOpenRightViewClass A)
    (table : ProfiledOpenRightRepresentableTable A source)
    (hallowed : NarrowedTablesAllowed
      (finiteRootFamilyMonitor
        (fun candidate : {root // root ∈ source.1} =>
          profiledOpenRightClassifiedRootMonitor A candidate.1))
      (ProfiledOpenRightRepresentableTableAllowed A source)
      table.toTransitionRationalTree.labeledTree)
    (member : {root // root ∈ source.1})
    (env : Nat → In₂ × In₁) (n : Nat) (row : PairedEntryRow) :
    (((profiledOpenRightRepresentableOutputAt A source table member env n).2
      row).2).SemanticallyRepresentable A := by
  let fullEnv := tagFiniteRootEnvironment member env
  let node := branchNode fullEnv n
  have hall := narrowedInducedTree_receiver_allowed
    (finiteRootFamilyMonitor
      (fun candidate : {root // root ∈ source.1} =>
        profiledOpenRightClassifiedRootMonitor A candidate.1))
    (ProfiledOpenRightRepresentableTableAllowed A source)
    table.toTransitionRationalTree.labeledTree hallowed node
  have hentry := hall.2 member (env n) row
  simpa [profiledOpenRightRepresentableOutputAt, fullEnv, node,
    treePlay, blockLabelApply] using hentry

/-- Left strengthened output. -/
noncomputable def profiledOpenLeftRepresentableOutputAt
    (source : ProfiledOpenLeftViewClass A)
    (table : ProfiledOpenLeftRepresentableTable A source)
    (member : {root // root ∈ source.1})
    (env : Nat → In₁ × In₂) (n : Nat) :
    ProfiledOpenLeftClassifiedOutput A :=
  (treePlay
    (narrowedInducedTree
      (finiteRootFamilyMonitor
        (fun candidate : {root // root ∈ source.1} =>
          profiledOpenLeftClassifiedRootMonitor A candidate.1))
      table.toTransitionRationalTree.labeledTree)
    (tagFiniteRootEnvironment member env) n).2.1

section
omit [Inhabited Out₁] [Inhabited Out₂]

/-- Actual left-to-right successor classes remain represented. -/
theorem profiledOpenLeftRepresentableOutputAt_class
    (source : ProfiledOpenLeftViewClass A)
    (table : ProfiledOpenLeftRepresentableTable A source)
    (hallowed : NarrowedTablesAllowed
      (finiteRootFamilyMonitor
        (fun candidate : {root // root ∈ source.1} =>
          profiledOpenLeftClassifiedRootMonitor A candidate.1))
      (ProfiledOpenLeftRepresentableTableAllowed A source)
      table.toTransitionRationalTree.labeledTree)
    (member : {root // root ∈ source.1})
    (env : Nat → In₁ × In₂) (n : Nat) (row : PairedEntryRow) :
    (((profiledOpenLeftRepresentableOutputAt A source table member env n).2
      row).2).SemanticallyRepresentable A := by
  let fullEnv := tagFiniteRootEnvironment member env
  let node := branchNode fullEnv n
  have hall := narrowedInducedTree_receiver_allowed
    (finiteRootFamilyMonitor
      (fun candidate : {root // root ∈ source.1} =>
        profiledOpenLeftClassifiedRootMonitor A candidate.1))
    (ProfiledOpenLeftRepresentableTableAllowed A source)
    table.toTransitionRationalTree.labeledTree hallowed node
  have hentry := hall.2 member (env n) row
  simpa [profiledOpenLeftRepresentableOutputAt, fullEnv, node,
    treePlay, blockLabelApply] using hentry

/-- Representability is exactly the non-circular premise needed to produce
the next valid right classified move. -/
theorem ProfiledOpenRightViewClass.exists_valid_classifiedMove
    (source : ProfiledOpenRightViewClass A)
    (hrep : source.SemanticallyRepresentable A) :
    ∃ move : ProfiledOpenClassifiedMove A,
      move.Valid A ∧ move.roots A = profiledOpenRightClassifiedRoots A source := by
  rcases hrep with
    ⟨strategy, hwin, basis, entry, minimum, pivot, hview, hroot⟩
  let table := profiledOpenRightClassifiedTableOfWinning A source strategy hwin
    entry minimum basis hroot pivot hview
  refine ⟨.right source table, ⟨?_, ?_⟩, rfl⟩
  · exact profiledOpenRightClassifiedTableOfWinning_wins A source strategy
      hwin entry minimum basis hroot pivot hview
  · exact profiledOpenRightClassifiedTableOfWinning_allowed A source
      strategy hwin entry minimum basis hroot pivot hview

/-- Left move mirror. -/
theorem ProfiledOpenLeftViewClass.exists_valid_classifiedMove
    (source : ProfiledOpenLeftViewClass A)
    (hrep : source.SemanticallyRepresentable A) :
    ∃ move : ProfiledOpenClassifiedMove A,
      move.Valid A ∧ move.roots A = profiledOpenLeftClassifiedRoots A source := by
  rcases hrep with
    ⟨strategy, hwin, basis, entry, minimum, pivot, hview, hroot⟩
  let table := profiledOpenLeftClassifiedTableOfWinning A source strategy hwin
    entry minimum basis hroot pivot hview
  refine ⟨.left source table, ⟨?_, ?_⟩, rfl⟩
  · exact profiledOpenLeftClassifiedTableOfWinning_wins A source strategy
      hwin entry minimum basis hroot pivot hview
  · exact profiledOpenLeftClassifiedTableOfWinning_allowed A source strategy
      hwin entry minimum basis hroot pivot hview

end

end

end


end DetParityAutomaton

end DistributedSynthesis
