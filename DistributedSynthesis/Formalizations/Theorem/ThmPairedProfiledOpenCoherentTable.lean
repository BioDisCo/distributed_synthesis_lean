/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledOpenRepresentableAutomaton

/-!
# Provenance-preserving classified tables

The finite outer move must retain more than existential representability while
we prove epoch parity.  Every receiver table used by the extracted controller
is therefore first restricted to a literal table of one fixed semantic
receiver at some history.  We then forget that stronger law without changing
the controller or any label.  This prevents the second, independent Rabin
choice that would otherwise permit an unsound accepted-word mosaic.
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

/-- A complete right receiver table has semantic provenance when it is
literally the table produced by the fixed raw strategy at some finite tagged
history. -/
def ProfiledOpenRightSemanticTableAllowed
    (source : ProfiledOpenRightViewClass A)
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (entry : {root // root ∈ source.1} → ProcOnePairedEntryRep strategy)
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
    (responses :
      ({root // root ∈ source.1} × In₂) × In₁ →
        ProfiledOpenRightClassifiedOutput A) : Prop :=
  ∃ past, responses =
    profiledOpenRightSemanticClassifiedFamilyReceiver A source strategy hwin
      entry basis past

/-- Left semantic provenance law. -/
def ProfiledOpenLeftSemanticTableAllowed
    (source : ProfiledOpenLeftViewClass A)
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (entry : {root // root ∈ source.1} → ProcTwoPairedEntryRep strategy)
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
    (responses :
      ({root // root ∈ source.1} × In₁) × In₂ →
        ProfiledOpenLeftClassifiedOutput A) : Prop :=
  ∃ past, responses =
    profiledOpenLeftSemanticClassifiedFamilyReceiver A source strategy hwin
      entry basis past

noncomputable local instance rightSemanticTableAllowedDecidable
    (source : ProfiledOpenRightViewClass A)
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (entry : {root // root ∈ source.1} → ProcOnePairedEntryRep strategy)
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis) :
    DecidablePred
      (ProfiledOpenRightSemanticTableAllowed A source strategy hwin entry
        basis) := fun _ => Classical.propDecidable _

noncomputable local instance leftSemanticTableAllowedDecidable
    (source : ProfiledOpenLeftViewClass A)
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (entry : {root // root ∈ source.1} → ProcTwoPairedEntryRep strategy)
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis) :
    DecidablePred
      (ProfiledOpenLeftSemanticTableAllowed A source strategy hwin entry
        basis) := fun _ => Classical.propDecidable _

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Semantic provenance implies the finite outer interface's sticky
representability law. -/
theorem profiledOpenRightSemanticTableAllowed_implies_representable
    (source : ProfiledOpenRightViewClass A)
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (entry : {root // root ∈ source.1} → ProcOnePairedEntryRep strategy)
    (minimum : {root // root ∈ source.1} → A.State)
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
    (responses :
      ({root // root ∈ source.1} × In₂) × In₁ →
        ProfiledOpenRightClassifiedOutput A)
    (hsemantic : ProfiledOpenRightSemanticTableAllowed A source strategy hwin
      entry basis responses) :
    ProfiledOpenRightRepresentableTableAllowed A source responses := by
  rcases hsemantic with ⟨past, rfl⟩
  exact profiledOpenRightSemanticClassifiedFamilyReceiver_representable A
    source strategy hwin entry minimum basis past

omit [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledOpenLeftSemanticTableAllowed_implies_representable
    (source : ProfiledOpenLeftViewClass A)
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (entry : {root // root ∈ source.1} → ProcTwoPairedEntryRep strategy)
    (minimum : {root // root ∈ source.1} → A.State)
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
    (responses :
      ({root // root ∈ source.1} × In₁) × In₂ →
        ProfiledOpenLeftClassifiedOutput A)
    (hsemantic : ProfiledOpenLeftSemanticTableAllowed A source strategy hwin
      entry basis responses) :
    ProfiledOpenLeftRepresentableTableAllowed A source responses := by
  rcases hsemantic with ⟨past, rfl⟩
  exact profiledOpenLeftSemanticClassifiedFamilyReceiver_representable A
    source strategy hwin entry minimum basis past

/-- A finite right outer table together with the stronger provenance law on
the very same labeled tree. -/
structure ProfiledOpenRightCoherentTable
    (source : ProfiledOpenRightViewClass A)
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (entry : {root // root ∈ source.1} → ProcOnePairedEntryRep strategy)
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis) where
  table : ProfiledOpenRightRepresentableTable.{u, v, x, y, s, 0} A source
  wins : NarrowedAllThreadsWin
    (finiteRootFamilyMonitor
      (fun member : {root // root ∈ source.1} =>
        profiledOpenRightClassifiedRootMonitor A member.1))
    table.toTransitionRationalTree.labeledTree
  representable : NarrowedTablesAllowed
    (finiteRootFamilyMonitor
      (fun member : {root // root ∈ source.1} =>
        profiledOpenRightClassifiedRootMonitor A member.1))
    (ProfiledOpenRightRepresentableTableAllowed A source)
    table.toTransitionRationalTree.labeledTree
  provenance : NarrowedTablesAllowed
    (finiteRootFamilyMonitor
      (fun member : {root // root ∈ source.1} =>
        profiledOpenRightClassifiedRootMonitor A member.1))
    (ProfiledOpenRightSemanticTableAllowed A source strategy hwin entry basis)
    table.toTransitionRationalTree.labeledTree

/-- Left coherent table package. -/
structure ProfiledOpenLeftCoherentTable
    (source : ProfiledOpenLeftViewClass A)
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (entry : {root // root ∈ source.1} → ProcTwoPairedEntryRep strategy)
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis) where
  table : ProfiledOpenLeftRepresentableTable.{u, v, x, y, s, 0} A source
  wins : NarrowedAllThreadsWin
    (finiteRootFamilyMonitor
      (fun member : {root // root ∈ source.1} =>
        profiledOpenLeftClassifiedRootMonitor A member.1))
    table.toTransitionRationalTree.labeledTree
  representable : NarrowedTablesAllowed
    (finiteRootFamilyMonitor
      (fun member : {root // root ∈ source.1} =>
        profiledOpenLeftClassifiedRootMonitor A member.1))
    (ProfiledOpenLeftRepresentableTableAllowed A source)
    table.toTransitionRationalTree.labeledTree
  provenance : NarrowedTablesAllowed
    (finiteRootFamilyMonitor
      (fun member : {root // root ∈ source.1} =>
        profiledOpenLeftClassifiedRootMonitor A member.1))
    (ProfiledOpenLeftSemanticTableAllowed A source strategy hwin entry basis)
    table.toTransitionRationalTree.labeledTree

/-- Extract once under semantic provenance, then weaken the predicate without
changing the finite controller or its labels. -/
noncomputable def profiledOpenRightCoherentTableOfRealization
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
    ProfiledOpenRightCoherentTable A source strategy hwin entry basis := by
  classical
  let M := finiteRootFamilyMonitor
    (fun member : {root // root ∈ source.1} =>
      profiledOpenRightClassifiedRootMonitor A member.1)
  let Strong := ProfiledOpenRightSemanticTableAllowed A source strategy hwin
    entry basis
  let Weak := ProfiledOpenRightRepresentableTableAllowed A source
  let receiver := profiledOpenRightSemanticClassifiedFamilyReceiver A source
    strategy hwin entry basis
  let sender := pairedRightSenderStrategy (entry pivot).lambdaOfStrategy
  letI : Inhabited {root // root ∈ source.1} := ⟨pivot⟩
  letI : Inhabited (ProfiledOpenRightClassifiedOutput A) :=
    ⟨receiver [] default⟩
  let strongTable : LocallyConsistentNarrowedTable M Strong :=
    locallyConsistentTableOfStrategies M Strong (receiver []) ⟨[], rfl⟩
      receiver sender
      (profiledOpenRightSemanticClassifiedFamily_realizable A source strategy
        hwin entry minimum basis hroot pivot hview)
      (fun past => ⟨past, rfl⟩)
  have hstrongWins : NarrowedAllThreadsWin M
      strongTable.toTransitionRationalTree.labeledTree :=
    locallyConsistentTableOfStrategies_wins M Strong (receiver []) ⟨[], rfl⟩
      receiver sender
      (profiledOpenRightSemanticClassifiedFamily_realizable A source strategy
        hwin entry minimum basis hroot pivot hview)
      (fun past => ⟨past, rfl⟩)
  have hstrongAllowed : NarrowedTablesAllowed M Strong
      strongTable.toTransitionRationalTree.labeledTree :=
    locallyConsistentTableOfStrategies_allowed M Strong (receiver [])
      ⟨[], rfl⟩ receiver sender
      (profiledOpenRightSemanticClassifiedFamily_realizable A source strategy
        hwin entry minimum basis hroot pivot hview)
      (fun past => ⟨past, rfl⟩)
  let table : ProfiledOpenRightRepresentableTable.{u, v, x, y, s, 0} A source :=
    strongTable.weaken M Strong Weak
  refine ⟨table, ?_, ?_, ?_⟩
  · exact LocallyConsistentNarrowedTable.weaken_wins M Strong Weak strongTable
      hstrongWins
  · exact LocallyConsistentNarrowedTable.weaken_allowed M Strong Weak
      (profiledOpenRightSemanticTableAllowed_implies_representable A source
        strategy hwin entry minimum basis) strongTable hstrongAllowed
  · simpa [table] using hstrongAllowed

/-- Left coherent extraction. -/
noncomputable def profiledOpenLeftCoherentTableOfRealization
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
    ProfiledOpenLeftCoherentTable A source strategy hwin entry basis := by
  classical
  let M := finiteRootFamilyMonitor
    (fun member : {root // root ∈ source.1} =>
      profiledOpenLeftClassifiedRootMonitor A member.1)
  let Strong := ProfiledOpenLeftSemanticTableAllowed A source strategy hwin
    entry basis
  let Weak := ProfiledOpenLeftRepresentableTableAllowed A source
  let receiver := profiledOpenLeftSemanticClassifiedFamilyReceiver A source
    strategy hwin entry basis
  let sender := pairedLeftSenderStrategy (entry pivot).lambdaOfStrategy
  letI : Inhabited {root // root ∈ source.1} := ⟨pivot⟩
  letI : Inhabited (ProfiledOpenLeftClassifiedOutput A) :=
    ⟨receiver [] default⟩
  let strongTable : LocallyConsistentNarrowedTable M Strong :=
    locallyConsistentTableOfStrategies M Strong (receiver []) ⟨[], rfl⟩
      receiver sender
      (profiledOpenLeftSemanticClassifiedFamily_realizable A source strategy
        hwin entry minimum basis hroot pivot hview)
      (fun past => ⟨past, rfl⟩)
  have hstrongWins : NarrowedAllThreadsWin M
      strongTable.toTransitionRationalTree.labeledTree :=
    locallyConsistentTableOfStrategies_wins M Strong (receiver []) ⟨[], rfl⟩
      receiver sender
      (profiledOpenLeftSemanticClassifiedFamily_realizable A source strategy
        hwin entry minimum basis hroot pivot hview)
      (fun past => ⟨past, rfl⟩)
  have hstrongAllowed : NarrowedTablesAllowed M Strong
      strongTable.toTransitionRationalTree.labeledTree :=
    locallyConsistentTableOfStrategies_allowed M Strong (receiver [])
      ⟨[], rfl⟩ receiver sender
      (profiledOpenLeftSemanticClassifiedFamily_realizable A source strategy
        hwin entry minimum basis hroot pivot hview)
      (fun past => ⟨past, rfl⟩)
  let table : ProfiledOpenLeftRepresentableTable.{u, v, x, y, s, 0} A source :=
    strongTable.weaken M Strong Weak
  refine ⟨table, ?_, ?_, ?_⟩
  · exact LocallyConsistentNarrowedTable.weaken_wins M Strong Weak strongTable
      hstrongWins
  · exact LocallyConsistentNarrowedTable.weaken_allowed M Strong Weak
      (profiledOpenLeftSemanticTableAllowed_implies_representable A source
        strategy hwin entry minimum basis) strongTable hstrongAllowed
  · simpa [table] using hstrongAllowed

/-! ## Provenance on the genuine induced monitor thread -/

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Reading the weakened finite table at an actual right play position still
returns a response of the original semantic receiver at some tagged semantic
history.  The statement is deliberately about the complete response table;
all row-specific child equations follow by function congruence. -/
theorem profiledOpenRightCoherentOutputAt_semantic
    (source : ProfiledOpenRightViewClass A)
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (entry : {root // root ∈ source.1} → ProcOnePairedEntryRep strategy)
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
    (coherent : ProfiledOpenRightCoherentTable A source strategy hwin entry
      basis)
    (member : {root // root ∈ source.1})
    (env : Nat → In₂ × In₁) (n : Nat) :
    ∃ semanticPast,
      profiledOpenRightRepresentableOutputAt A source coherent.table member
          env n =
        profiledOpenRightSemanticClassifiedFamilyReceiver A source strategy
          hwin entry basis semanticPast ((member, (env n).1), (env n).2) := by
  let fullEnv := tagFiniteRootEnvironment member env
  let node := branchNode fullEnv n
  have htable := narrowedInducedTree_receiver_allowed
    (finiteRootFamilyMonitor
      (fun member : {root // root ∈ source.1} =>
        profiledOpenRightClassifiedRootMonitor A member.1))
    (ProfiledOpenRightSemanticTableAllowed A source strategy hwin entry basis)
    coherent.table.toTransitionRationalTree.labeledTree coherent.provenance node
  rcases htable with ⟨semanticPast, hsemantic⟩
  refine ⟨semanticPast, ?_⟩
  have hat := congrFun hsemantic ((member, (env n).1), (env n).2)
  simpa [profiledOpenRightRepresentableOutputAt,
    profiledOpenRightClassifiedOutputAt,
    profiledOpenRightClassifiedInducedTree, fullEnv, node,
    treePlay, blockLabelApply] using hat

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Left actual-thread provenance. -/
theorem profiledOpenLeftCoherentOutputAt_semantic
    (source : ProfiledOpenLeftViewClass A)
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (entry : {root // root ∈ source.1} → ProcTwoPairedEntryRep strategy)
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
    (coherent : ProfiledOpenLeftCoherentTable A source strategy hwin entry
      basis)
    (member : {root // root ∈ source.1})
    (env : Nat → In₁ × In₂) (n : Nat) :
    ∃ semanticPast,
      profiledOpenLeftRepresentableOutputAt A source coherent.table member env
          n =
        profiledOpenLeftSemanticClassifiedFamilyReceiver A source strategy
          hwin entry basis semanticPast ((member, (env n).1), (env n).2) := by
  let fullEnv := tagFiniteRootEnvironment member env
  let node := branchNode fullEnv n
  have htable := narrowedInducedTree_receiver_allowed
    (finiteRootFamilyMonitor
      (fun member : {root // root ∈ source.1} =>
        profiledOpenLeftClassifiedRootMonitor A member.1))
    (ProfiledOpenLeftSemanticTableAllowed A source strategy hwin entry basis)
    coherent.table.toTransitionRationalTree.labeledTree coherent.provenance node
  rcases htable with ⟨semanticPast, hsemantic⟩
  refine ⟨semanticPast, ?_⟩
  have hat := congrFun hsemantic ((member, (env n).1), (env n).2)
  simpa [profiledOpenLeftRepresentableOutputAt,
    profiledOpenLeftClassifiedOutputAt,
    profiledOpenLeftClassifiedInducedTree, fullEnv, node,
    treePlay, blockLabelApply] using hat

end

end


end DetParityAutomaton

end DistributedSynthesis
