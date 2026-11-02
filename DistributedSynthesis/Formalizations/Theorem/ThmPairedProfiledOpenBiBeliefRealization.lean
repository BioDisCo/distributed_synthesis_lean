/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledOpenBiBeliefNode
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledOpenPointedRealization

/-!
# Raw realizations label a package-free belief node

The semantic extraction first gives a table with the strengthened
representability law.  The source-free belief-node alphabet needs only the
classified table law.  This file forgets the stronger law on the *same*
finite controller and proves that its labels, universal-thread parity, and
classified validity are unchanged.

Consequently one right and one left realization of a fixed raw winning
strategy produce a structurally valid, thread-valid shared belief move at one
node.  No successor-correlation theorem is claimed here.  That separate
`hthread` obligation must use the indexed equality pattern and persistent
lineage construction; arbitrary independent right/left directions are not
licensed by this lemma.
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

/-! ## Literal weakening of representable tables -/

/-- Forget successor representability on a right table, retaining its exact
finite state transition and label functions. -/
noncomputable def ProfiledOpenRightRepresentableTable.toClassified
    (source : ProfiledOpenRightViewClass A)
    (table : ProfiledOpenRightRepresentableTable A source) :
    ProfiledOpenRightClassifiedTable A source := by
  classical
  let M := finiteRootFamilyMonitor
    (fun member : {root // root ∈ source.1} =>
      profiledOpenRightClassifiedRootMonitor A member.1)
  let Strong := ProfiledOpenRightRepresentableTableAllowed A source
  let Weak := ProfiledOpenRightClassifiedTableAllowed A source
  letI : DecidablePred Strong := fun _ => Classical.propDecidable _
  letI : DecidablePred Weak := fun _ => Classical.propDecidable _
  exact table.weaken M Strong Weak

/-- Left mirror. -/
noncomputable def ProfiledOpenLeftRepresentableTable.toClassified
    (source : ProfiledOpenLeftViewClass A)
    (table : ProfiledOpenLeftRepresentableTable A source) :
    ProfiledOpenLeftClassifiedTable A source := by
  classical
  let M := finiteRootFamilyMonitor
    (fun member : {root // root ∈ source.1} =>
      profiledOpenLeftClassifiedRootMonitor A member.1)
  let Strong := ProfiledOpenLeftRepresentableTableAllowed A source
  let Weak := ProfiledOpenLeftClassifiedTableAllowed A source
  letI : DecidablePred Strong := fun _ => Classical.propDecidable _
  letI : DecidablePred Weak := fun _ => Classical.propDecidable _
  exact table.weaken M Strong Weak

section
omit [Inhabited Out₁] [Inhabited Out₂]

@[simp] theorem ProfiledOpenRightRepresentableTable.toClassified_labeledTree
    (source : ProfiledOpenRightViewClass A)
    (table : ProfiledOpenRightRepresentableTable A source) :
    (table.toClassified A source).toTransitionRationalTree.labeledTree =
      table.toTransitionRationalTree.labeledTree := by
  rfl

@[simp] theorem ProfiledOpenLeftRepresentableTable.toClassified_labeledTree
    (source : ProfiledOpenLeftViewClass A)
    (table : ProfiledOpenLeftRepresentableTable A source) :
    (table.toClassified A source).toTransitionRationalTree.labeledTree =
      table.toTransitionRationalTree.labeledTree := by
  rfl

/-- The coherent right table remains universally winning after forgetting
the representability conjunct. -/
theorem ProfiledOpenRightCoherentTable.toClassified_wins
    (source : ProfiledOpenRightViewClass A)
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (entry : {root // root ∈ source.1} → ProcOnePairedEntryRep strategy)
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
    (coherent : ProfiledOpenRightCoherentTable A source strategy hwin entry
      basis) :
    NarrowedAllThreadsWin
      (finiteRootFamilyMonitor
        (fun member : {root // root ∈ source.1} =>
          profiledOpenRightClassifiedRootMonitor A member.1))
      (coherent.table.toClassified A source).toTransitionRationalTree.labeledTree := by
  simpa using coherent.wins

/-- The classified table law is the first conjunct of representability and
is inherited pointwise on the literal table. -/
theorem ProfiledOpenRightCoherentTable.toClassified_allowed
    (source : ProfiledOpenRightViewClass A)
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (entry : {root // root ∈ source.1} → ProcOnePairedEntryRep strategy)
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
    (coherent : ProfiledOpenRightCoherentTable A source strategy hwin entry
      basis) :
    NarrowedTablesAllowed
      (finiteRootFamilyMonitor
        (fun member : {root // root ∈ source.1} =>
          profiledOpenRightClassifiedRootMonitor A member.1))
      (ProfiledOpenRightClassifiedTableAllowed A source)
      (coherent.table.toClassified A source).toTransitionRationalTree.labeledTree := by
  intro node q
  simpa using (coherent.representable node q).1

theorem ProfiledOpenLeftCoherentTable.toClassified_wins
    (source : ProfiledOpenLeftViewClass A)
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (entry : {root // root ∈ source.1} → ProcTwoPairedEntryRep strategy)
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
    (coherent : ProfiledOpenLeftCoherentTable A source strategy hwin entry
      basis) :
    NarrowedAllThreadsWin
      (finiteRootFamilyMonitor
        (fun member : {root // root ∈ source.1} =>
          profiledOpenLeftClassifiedRootMonitor A member.1))
      (coherent.table.toClassified A source).toTransitionRationalTree.labeledTree := by
  simpa using coherent.wins

theorem ProfiledOpenLeftCoherentTable.toClassified_allowed
    (source : ProfiledOpenLeftViewClass A)
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (entry : {root // root ∈ source.1} → ProcTwoPairedEntryRep strategy)
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
    (coherent : ProfiledOpenLeftCoherentTable A source strategy hwin entry
      basis) :
    NarrowedTablesAllowed
      (finiteRootFamilyMonitor
        (fun member : {root // root ∈ source.1} =>
          profiledOpenLeftClassifiedRootMonitor A member.1))
      (ProfiledOpenLeftClassifiedTableAllowed A source)
      (coherent.table.toClassified A source).toTransitionRationalTree.labeledTree := by
  intro node q
  simpa using (coherent.representable node q).1

end

/-! ## One raw semantic node supplies one source-free move -/

/-- Classified belief move read from one right and one left realization of
the same raw winner. -/
noncomputable def profiledOpenBiBeliefMoveOfRealizations
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env)}
    {basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis}
    {rightSource : ProfiledOpenRightViewClass A}
    {leftSource : ProfiledOpenLeftViewClass A}
    (right : ProfiledOpenRightRealization A strategy hwin basis rightSource)
    (left : ProfiledOpenLeftRealization A strategy hwin basis leftSource) :
    ProfiledOpenBiBeliefMove A :=
  (.right rightSource
      ((right.coherentTable A).table.toClassified A rightSource),
    .left leftSource
      ((left.coherentTable A).table.toClassified A leftSource))

/-- Public finite code of those two source families. -/
noncomputable def profiledOpenBiBeliefCodeOfRealizations
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env)}
    {basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis}
    {rightSource : ProfiledOpenRightViewClass A}
    {leftSource : ProfiledOpenLeftViewClass A}
    (_right : ProfiledOpenRightRealization A strategy hwin basis rightSource)
    (_left : ProfiledOpenLeftRealization A strategy hwin basis leftSource) :
    ProfiledOpenBiBeliefCode A :=
  (profiledOpenRightClassifiedRoots A rightSource,
    profiledOpenLeftClassifiedRoots A leftSource)

section
omit [Inhabited Out₁] [Inhabited Out₂]

theorem profiledOpenBiBeliefMoveOfRealizations_valid
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env)}
    {basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis}
    {rightSource : ProfiledOpenRightViewClass A}
    {leftSource : ProfiledOpenLeftViewClass A}
    (right : ProfiledOpenRightRealization A strategy hwin basis rightSource)
    (left : ProfiledOpenLeftRealization A strategy hwin basis leftSource) :
    ProfiledOpenBiBeliefValid A
      (profiledOpenBiBeliefCodeOfRealizations A right left)
      (profiledOpenBiBeliefMoveOfRealizations A right left) := by
  simp [ProfiledOpenBiBeliefValid, profiledOpenBiBeliefCodeOfRealizations,
    profiledOpenBiBeliefMoveOfRealizations]

theorem profiledOpenBiBeliefMoveOfRealizations_threadValid
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env)}
    {basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis}
    {rightSource : ProfiledOpenRightViewClass A}
    {leftSource : ProfiledOpenLeftViewClass A}
    (right : ProfiledOpenRightRealization A strategy hwin basis rightSource)
    (left : ProfiledOpenLeftRealization A strategy hwin basis leftSource) :
    ProfiledOpenBiBeliefThreadValid A
      (profiledOpenBiBeliefMoveOfRealizations A right left) := by
  change
    ProfiledOpenClassifiedMove.Valid A
        (.right rightSource
          ((right.coherentTable A).table.toClassified A rightSource)) ∧
      ProfiledOpenClassifiedMove.Valid A
        (.left leftSource
          ((left.coherentTable A).table.toClassified A leftSource))
  exact
    ⟨⟨(right.coherentTable A).toClassified_wins A rightSource strategy hwin
          right.entry basis,
        (right.coherentTable A).toClassified_allowed A rightSource strategy
          hwin right.entry basis⟩,
      ⟨(left.coherentTable A).toClassified_wins A leftSource strategy hwin
          left.entry basis,
        (left.coherentTable A).toClassified_allowed A leftSource strategy hwin
          left.entry basis⟩⟩

/-- The local source-free T1 law follows immediately for the raw label. -/
theorem profiledOpenBiBeliefMoveOfRealizations_T1
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env)}
    {basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis}
    {rightSource : ProfiledOpenRightViewClass A}
    {leftSource : ProfiledOpenLeftViewClass A}
    (right : ProfiledOpenRightRealization A strategy hwin basis rightSource)
    (left : ProfiledOpenLeftRealization A strategy hwin basis leftSource) :
    ProfiledOpenBiBeliefT1 A
      (profiledOpenBiBeliefCodeOfRealizations A right left)
      (profiledOpenBiBeliefMoveOfRealizations A right left) :=
  profiledOpenBiBeliefT1_of_valid A _ _
    (profiledOpenBiBeliefMoveOfRealizations_valid A right left)

end

end


end DetParityAutomaton

end DistributedSynthesis
