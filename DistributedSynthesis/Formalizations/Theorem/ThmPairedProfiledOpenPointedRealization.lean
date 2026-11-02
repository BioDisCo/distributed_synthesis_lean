/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledOpenCoherentTable

/-!
# Pointed semantic realizations of finite view classes

Epoch parity needs the actual semantic child, not merely some history with the
same finite root.  These structures retain one fixed winning strategy and a
representative for every root of a canonical view class.  The `force` lemmas
replace one representative by the actual child while preserving the class
invariant; they are proof-side operations and expose no leader bit locally.
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

/-- A right class realized by one fixed winning strategy. -/
structure ProfiledOpenRightRealization
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
    (source : ProfiledOpenRightViewClass A) where
  entry : {root // root ∈ source.1} → ProcOnePairedEntryRep strategy
  minimum : {root // root ∈ source.1} → A.State
  pivot : {root // root ∈ source.1}
  view_eq : ∀ member,
    currentView Proc.one (entry member).leftHistory =
      currentView Proc.one (entry pivot).leftHistory
  root_eq : ∀ member,
    profiledOpenRightRootOfWinning A strategy hwin (entry member)
      (minimum member) basis = member.1

/-- Left realization. -/
structure ProfiledOpenLeftRealization
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
    (source : ProfiledOpenLeftViewClass A) where
  entry : {root // root ∈ source.1} → ProcTwoPairedEntryRep strategy
  minimum : {root // root ∈ source.1} → A.State
  pivot : {root // root ∈ source.1}
  view_eq : ∀ member,
    currentView Proc.two (entry member).rightHistory =
      currentView Proc.two (entry pivot).rightHistory
  root_eq : ∀ member,
    profiledOpenLeftRootOfWinning A strategy hwin (entry member)
      (minimum member) basis = member.1

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Forget the fixed-strategy witness to the finite recursive invariant. -/
theorem ProfiledOpenRightRealization.semBehavior
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env)}
    {basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis}
    {source : ProfiledOpenRightViewClass A}
    (realization : ProfiledOpenRightRealization A strategy hwin basis source) :
    source.SemanticallyRepresentable A :=
  ⟨strategy, hwin, basis, realization.entry, realization.minimum,
    realization.pivot, realization.view_eq, realization.root_eq⟩

omit [Inhabited Out₁] [Inhabited Out₂] in
theorem ProfiledOpenLeftRealization.semBehavior
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env)}
    {basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis}
    {source : ProfiledOpenLeftViewClass A}
    (realization : ProfiledOpenLeftRealization A strategy hwin basis source) :
    source.SemanticallyRepresentable A :=
  ⟨strategy, hwin, basis, realization.entry, realization.minimum,
    realization.pivot, realization.view_eq, realization.root_eq⟩

/-- The coherent finite right table attached to a fixed realization. -/
noncomputable def ProfiledOpenRightRealization.coherentTable
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env)}
    {basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis}
    {source : ProfiledOpenRightViewClass A}
    (realization : ProfiledOpenRightRealization A strategy hwin basis source) :
    ProfiledOpenRightCoherentTable A source strategy hwin realization.entry
      basis :=
  profiledOpenRightCoherentTableOfRealization A source strategy hwin
    realization.entry realization.minimum basis realization.root_eq
    realization.pivot realization.view_eq

noncomputable def ProfiledOpenLeftRealization.coherentTable
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env)}
    {basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis}
    {source : ProfiledOpenLeftViewClass A}
    (realization : ProfiledOpenLeftRealization A strategy hwin basis source) :
    ProfiledOpenLeftCoherentTable A source strategy hwin realization.entry
      basis :=
  profiledOpenLeftCoherentTableOfRealization A source strategy hwin
    realization.entry realization.minimum basis realization.root_eq
    realization.pivot realization.view_eq

/-! ## Canonical realization of a semantic finite view class -/

noncomputable def profiledOpenRightSemanticSourceRealization
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
    ProfiledOpenRightRealization A strategy hwin basis
      (profiledOpenRightSemanticSourceClass A strategy hwin entry minimum
        pivot hview basis) := by
  let source := profiledOpenRightSemanticSourceClass A strategy hwin entry
    minimum pivot hview basis
  let canonicalEntry := profiledOpenRightSemanticSourceEntry A strategy hwin
    entry minimum pivot hview basis
  let canonicalMinimum := profiledOpenRightSemanticSourceMinimum A strategy
    hwin entry minimum pivot hview basis
  let canonicalPivot : {root // root ∈ source.1} :=
    ⟨source.2.1.choose, source.2.1.choose_spec⟩
  refine {
    entry := canonicalEntry
    minimum := canonicalMinimum
    pivot := canonicalPivot
    view_eq := ?_
    root_eq := ?_ }
  · intro member
    exact (hview _).trans (hview _).symm
  · intro member
    exact profiledOpenRightSemanticSource_root A strategy hwin entry minimum
      pivot hview basis member

noncomputable def profiledOpenLeftSemanticSourceRealization
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
    ProfiledOpenLeftRealization A strategy hwin basis
      (profiledOpenLeftSemanticSourceClass A strategy hwin entry minimum
        pivot hview basis) := by
  let source := profiledOpenLeftSemanticSourceClass A strategy hwin entry
    minimum pivot hview basis
  let canonicalEntry := profiledOpenLeftSemanticSourceEntry A strategy hwin
    entry minimum pivot hview basis
  let canonicalMinimum := profiledOpenLeftSemanticSourceMinimum A strategy
    hwin entry minimum pivot hview basis
  let canonicalPivot : {root // root ∈ source.1} :=
    ⟨source.2.1.choose, source.2.1.choose_spec⟩
  refine {
    entry := canonicalEntry
    minimum := canonicalMinimum
    pivot := canonicalPivot
    view_eq := ?_
    root_eq := ?_ }
  · intro member
    exact (hview _).trans (hview _).symm
  · intro member
    exact profiledOpenLeftSemanticSource_root A strategy hwin entry minimum
      pivot hview basis member

/-- Replace one right representative by an extensionally compatible actual
history.  The finite source class and every other representative are kept. -/
noncomputable def ProfiledOpenRightRealization.force
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env)}
    {basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis}
    {source : ProfiledOpenRightViewClass A}
    (realization : ProfiledOpenRightRealization A strategy hwin basis source)
    (selected : {root // root ∈ source.1})
    (actual : ProcOnePairedEntryRep strategy) (actualMinimum : A.State)
    (hactualView : currentView Proc.one actual.leftHistory =
      currentView Proc.one (realization.entry realization.pivot).leftHistory)
    (hactualRoot : profiledOpenRightRootOfWinning A strategy hwin actual
      actualMinimum basis = selected.1) :
    ProfiledOpenRightRealization A strategy hwin basis source := by
  classical
  let newEntry := fun member => if member = selected then actual
    else realization.entry member
  let newMinimum := fun member => if member = selected then actualMinimum
    else realization.minimum member
  refine {
    entry := newEntry
    minimum := newMinimum
    pivot := realization.pivot
    view_eq := ?_
    root_eq := ?_ }
  · intro member
    by_cases hm : member = selected
    · subst member
      by_cases hp : realization.pivot = selected
      · subst selected
        simpa [newEntry] using hactualView.symm
      · simpa [newEntry, hp] using hactualView
    · simp [newEntry, hm]
      by_cases hp : realization.pivot = selected
      · subst selected
        simpa [newEntry] using (realization.view_eq member).trans
          hactualView.symm
      · simpa [newEntry, hp] using realization.view_eq member
  · intro member
    by_cases hm : member = selected
    · subst member
      simpa [newEntry, newMinimum] using hactualRoot
    · simpa [newEntry, newMinimum, hm] using realization.root_eq member

/-- Left force operation. -/
noncomputable def ProfiledOpenLeftRealization.force
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env)}
    {basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis}
    {source : ProfiledOpenLeftViewClass A}
    (realization : ProfiledOpenLeftRealization A strategy hwin basis source)
    (selected : {root // root ∈ source.1})
    (actual : ProcTwoPairedEntryRep strategy) (actualMinimum : A.State)
    (hactualView : currentView Proc.two actual.rightHistory =
      currentView Proc.two (realization.entry realization.pivot).rightHistory)
    (hactualRoot : profiledOpenLeftRootOfWinning A strategy hwin actual
      actualMinimum basis = selected.1) :
    ProfiledOpenLeftRealization A strategy hwin basis source := by
  classical
  let newEntry := fun member => if member = selected then actual
    else realization.entry member
  let newMinimum := fun member => if member = selected then actualMinimum
    else realization.minimum member
  refine {
    entry := newEntry
    minimum := newMinimum
    pivot := realization.pivot
    view_eq := ?_
    root_eq := ?_ }
  · intro member
    by_cases hm : member = selected
    · subst member
      by_cases hp : realization.pivot = selected
      · subst selected
        simpa [newEntry] using hactualView.symm
      · simpa [newEntry, hp] using hactualView
    · simp [newEntry, hm]
      by_cases hp : realization.pivot = selected
      · subst selected
        simpa [newEntry] using (realization.view_eq member).trans
          hactualView.symm
      · simpa [newEntry, hp] using realization.view_eq member
  · intro member
    by_cases hm : member = selected
    · subst member
      simpa [newEntry, newMinimum] using hactualRoot
    · simpa [newEntry, newMinimum, hm] using realization.root_eq member

/-! ## Pointed successor packages -/

structure ProfiledOpenRightPointedRealization
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
    (source : ProfiledOpenRightViewClass A) where
  realization : ProfiledOpenRightRealization A strategy hwin basis source
  selected : {root // root ∈ source.1}
  actualEntry : ProcOnePairedEntryRep strategy
  actualMinimum : A.State
  entry_selected : realization.entry selected = actualEntry
  minimum_selected : realization.minimum selected = actualMinimum

structure ProfiledOpenLeftPointedRealization
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
    (source : ProfiledOpenLeftViewClass A) where
  realization : ProfiledOpenLeftRealization A strategy hwin basis source
  selected : {root // root ∈ source.1}
  actualEntry : ProcTwoPairedEntryRep strategy
  actualMinimum : A.State
  entry_selected : realization.entry selected = actualEntry
  minimum_selected : realization.minimum selected = actualMinimum

/-- The semantic right-to-left child class has a realization pointed at the
actual child history that generated the advertised root. -/
noncomputable def profiledOpenRightSemanticChildPointedRealization
    (source : ProfiledOpenRightViewClass A)
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
    (realization : ProfiledOpenRightRealization A strategy hwin basis source)
    (member : {root // root ∈ source.1})
    (past : List (In₂ × In₁)) (move : In₂ × In₁)
    (row : PairedEntryRow) :
    ProfiledOpenLeftPointedRealization A strategy hwin basis
      (profiledOpenRightSemanticChildClass A source strategy hwin
        realization.entry basis member past move row) := by
  classical
  let pivot := (member, row)
  let members := {candidate // candidate ∈
    procTwoChildViewClass strategy realization.entry past move pivot}
  let pivotMember : members :=
    ⟨pivot, pivot_mem_procTwoChildViewClass strategy realization.entry past
      move pivot⟩
  letI : Inhabited members := ⟨pivotMember⟩
  let childEntry : members → ProcTwoPairedEntryRep strategy := fun candidate =>
    procTwoViewClassChild strategy realization.entry past move candidate.1
  let childMinimum : members → A.State := fun candidate =>
    procTwoViewClassChildMinimum A realization.entry past candidate.1
  have hchildView : ∀ candidate,
      currentView Proc.two (childEntry candidate).rightHistory =
        currentView Proc.two (childEntry pivotMember).rightHistory := by
    intro candidate
    exact (mem_procTwoChildViewClass strategy realization.entry past move pivot
      candidate.1).mp candidate.2
  let canonicalSource := profiledOpenLeftSemanticSourceClass A strategy hwin
    childEntry childMinimum pivotMember hchildView basis
  have hclass :
      profiledOpenRightSemanticChildClass A source strategy hwin
          realization.entry basis member past move row = canonicalSource := by
    apply Subtype.ext
    rfl
  let base : ProfiledOpenLeftRealization A strategy hwin basis canonicalSource :=
    profiledOpenLeftSemanticSourceRealization A strategy hwin childEntry
      childMinimum pivotMember hchildView basis
  let actual := childEntry pivotMember
  let actualMinimum := childMinimum pivotMember
  let actualRoot := profiledOpenLeftRootOfWinning A strategy hwin actual
    actualMinimum basis
  have hactualMem : actualRoot ∈ canonicalSource.1 := by
    apply Finset.mem_image.mpr
    refine ⟨pivotMember, Finset.mem_univ _, ?_⟩
    rfl
  let selected : {root // root ∈ canonicalSource.1} :=
    ⟨actualRoot, hactualMem⟩
  have hactualView : currentView Proc.two actual.rightHistory =
      currentView Proc.two (base.entry base.pivot).rightHistory := by
    let representative := profiledOpenLeftRootRepresentative A
      (fun index : members => profiledOpenLeftRootOfWinning A strategy hwin
        (childEntry index) (childMinimum index) basis) base.pivot
    have hv := hchildView representative
    simpa [base, profiledOpenLeftSemanticSourceRealization,
      profiledOpenLeftSemanticSourceEntry, childEntry, actual] using hv.symm
  let forced := base.force A selected actual actualMinimum hactualView rfl
  have hentry : forced.entry selected = actual := by
    simp [forced, ProfiledOpenLeftRealization.force]
  have hminimum : forced.minimum selected = actualMinimum := by
    simp [forced, ProfiledOpenLeftRealization.force]
  rw [hclass]
  exact ⟨forced, selected, actual, actualMinimum, hentry, hminimum⟩

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- The pointed semantic child is literally the operational successor of its
selected source representative.  In particular, no representative splicing
occurs across an alternating right-to-left handoff. -/
theorem profiledOpenRightSemanticChildPointedRealization_memory_step
    (source : ProfiledOpenRightViewClass A)
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
    (realization : ProfiledOpenRightRealization A strategy hwin basis source)
    (member : {root // root ∈ source.1})
    (past : List (In₂ × In₁)) (move : In₂ × In₁)
    (row : PairedEntryRow) :
    let child := profiledOpenRightSemanticChildPointedRealization A source
      strategy hwin basis realization member past move row
    PairedStrategyMemory.step (A := A)
        (.processOne (realization.entry member) (realization.minimum member))
        (.fromOne row past move) =
      .processTwo child.actualEntry child.actualMinimum := by
  classical
  dsimp only
  rw [pairedStrategyMemory_step_eq_procTwoViewClassChild]
  rfl

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- The point selected in the semantic child is the root emitted by the
semantic receiver. -/
theorem profiledOpenRightSemanticChildPointedRealization_selected
    (source : ProfiledOpenRightViewClass A)
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
    (realization : ProfiledOpenRightRealization A strategy hwin basis source)
    (member : {root // root ∈ source.1})
    (past : List (In₂ × In₁)) (move : In₂ × In₁)
    (row : PairedEntryRow) :
    let child := profiledOpenRightSemanticChildPointedRealization A source
      strategy hwin basis realization member past move row
    child.selected.1 =
      profiledOpenRightSemanticChildRoot A source strategy hwin
        realization.entry basis member past move row := by
  rfl

/-- Left-to-right pointed semantic child. -/
noncomputable def profiledOpenLeftSemanticChildPointedRealization
    (source : ProfiledOpenLeftViewClass A)
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
    (realization : ProfiledOpenLeftRealization A strategy hwin basis source)
    (member : {root // root ∈ source.1})
    (past : List (In₁ × In₂)) (move : In₁ × In₂)
    (row : PairedEntryRow) :
    ProfiledOpenRightPointedRealization A strategy hwin basis
      (profiledOpenLeftSemanticChildClass A source strategy hwin
        realization.entry basis member past move row) := by
  classical
  let pivot := (member, row)
  let members := {candidate // candidate ∈
    procOneChildViewClass strategy realization.entry past move pivot}
  let pivotMember : members :=
    ⟨pivot, pivot_mem_procOneChildViewClass strategy realization.entry past
      move pivot⟩
  letI : Inhabited members := ⟨pivotMember⟩
  let childEntry : members → ProcOnePairedEntryRep strategy := fun candidate =>
    procOneViewClassChild strategy realization.entry past move candidate.1
  let childMinimum : members → A.State := fun candidate =>
    procOneViewClassChildMinimum A realization.entry past candidate.1
  have hchildView : ∀ candidate,
      currentView Proc.one (childEntry candidate).leftHistory =
        currentView Proc.one (childEntry pivotMember).leftHistory := by
    intro candidate
    exact (mem_procOneChildViewClass strategy realization.entry past move pivot
      candidate.1).mp candidate.2
  let canonicalSource := profiledOpenRightSemanticSourceClass A strategy hwin
    childEntry childMinimum pivotMember hchildView basis
  have hclass :
      profiledOpenLeftSemanticChildClass A source strategy hwin
          realization.entry basis member past move row = canonicalSource := by
    apply Subtype.ext
    rfl
  let base : ProfiledOpenRightRealization A strategy hwin basis canonicalSource :=
    profiledOpenRightSemanticSourceRealization A strategy hwin childEntry
      childMinimum pivotMember hchildView basis
  let actual := childEntry pivotMember
  let actualMinimum := childMinimum pivotMember
  let actualRoot := profiledOpenRightRootOfWinning A strategy hwin actual
    actualMinimum basis
  have hactualMem : actualRoot ∈ canonicalSource.1 := by
    apply Finset.mem_image.mpr
    refine ⟨pivotMember, Finset.mem_univ _, ?_⟩
    rfl
  let selected : {root // root ∈ canonicalSource.1} :=
    ⟨actualRoot, hactualMem⟩
  have hactualView : currentView Proc.one actual.leftHistory =
      currentView Proc.one (base.entry base.pivot).leftHistory := by
    let representative := profiledOpenRightRootRepresentative A
      (fun index : members => profiledOpenRightRootOfWinning A strategy hwin
        (childEntry index) (childMinimum index) basis) base.pivot
    have hv := hchildView representative
    simpa [base, profiledOpenRightSemanticSourceRealization,
      profiledOpenRightSemanticSourceEntry, childEntry, actual] using hv.symm
  let forced := base.force A selected actual actualMinimum hactualView rfl
  have hentry : forced.entry selected = actual := by
    simp [forced, ProfiledOpenRightRealization.force]
  have hminimum : forced.minimum selected = actualMinimum := by
    simp [forced, ProfiledOpenRightRealization.force]
  rw [hclass]
  exact ⟨forced, selected, actual, actualMinimum, hentry, hminimum⟩

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Left-to-right mirror of the exact operational-successor law. -/
theorem profiledOpenLeftSemanticChildPointedRealization_memory_step
    (source : ProfiledOpenLeftViewClass A)
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
    (realization : ProfiledOpenLeftRealization A strategy hwin basis source)
    (member : {root // root ∈ source.1})
    (past : List (In₁ × In₂)) (move : In₁ × In₂)
    (row : PairedEntryRow) :
    let child := profiledOpenLeftSemanticChildPointedRealization A source
      strategy hwin basis realization member past move row
    PairedStrategyMemory.step (A := A)
        (.processTwo (realization.entry member) (realization.minimum member))
        (.fromTwo row past move) =
      .processOne child.actualEntry child.actualMinimum := by
  classical
  dsimp only
  rw [pairedStrategyMemory_step_eq_procOneViewClassChild]
  rfl

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- The selected point of the left-to-right child is its emitted semantic
root. -/
theorem profiledOpenLeftSemanticChildPointedRealization_selected
    (source : ProfiledOpenLeftViewClass A)
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
    (realization : ProfiledOpenLeftRealization A strategy hwin basis source)
    (member : {root // root ∈ source.1})
    (past : List (In₁ × In₂)) (move : In₁ × In₂)
    (row : PairedEntryRow) :
    let child := profiledOpenLeftSemanticChildPointedRealization A source
      strategy hwin basis realization member past move row
    child.selected.1 =
      profiledOpenLeftSemanticChildRoot A source strategy hwin
        realization.entry basis member past move row := by
  rfl

/-! ## Pointed handoff from the finite coherent controller -/

/-- The actual output of the finite right controller yields an
opposite-orientation realization pointed at the genuine semantic child. -/
noncomputable def profiledOpenRightCoherentChildPointed
    (source : ProfiledOpenRightViewClass A)
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
    (realization : ProfiledOpenRightRealization A strategy hwin basis source)
    (member : {root // root ∈ source.1})
    (env : Nat → In₂ × In₁) (n : Nat) (row : PairedEntryRow) :
    let output := profiledOpenRightRepresentableOutputAt A source
      (realization.coherentTable A).table member env n
    ProfiledOpenLeftPointedRealization A strategy hwin basis
      (output.2 row).2 := by
  let coherent := realization.coherentTable A
  have hex :=
    profiledOpenRightCoherentOutputAt_semantic A source strategy hwin
      realization.entry basis coherent member env n
  let semanticPast := Classical.choose hex
  have houtput := Classical.choose_spec hex
  let physicalPast := semanticPast.map fun old => (old.1.2, old.2)
  rw [houtput]
  simpa [profiledOpenRightSemanticClassifiedFamilyReceiver,
    finiteRootFamilyReceiver, profiledOpenRightSemanticClassifiedReceiver,
    physicalPast] using
    (profiledOpenRightSemanticChildPointedRealization A source strategy hwin
      basis realization member physicalPast (env n) row)

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Exact provenance for an alternating right-to-left coherent handoff.
Besides retaining the semantic history hidden by table weakening, the package
identifies the emitted root and proves that its pointed child is the literal
next `PairedStrategyMemory` state. -/
theorem exists_profiledOpenRightCoherentChildStep
    (source : ProfiledOpenRightViewClass A)
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
    (realization : ProfiledOpenRightRealization A strategy hwin basis source)
    (member : {root // root ∈ source.1})
    (env : Nat → In₂ × In₁) (n : Nat) (row : PairedEntryRow) :
    let output := profiledOpenRightRepresentableOutputAt A source
      (realization.coherentTable A).table member env n
    ∃ semanticPast :
        List ((({root // root ∈ source.1} × In₂) × In₁)),
      ∃ child : ProfiledOpenLeftPointedRealization A strategy hwin basis
          (output.2 row).2,
        output =
            profiledOpenRightSemanticClassifiedFamilyReceiver A source strategy
              hwin realization.entry basis semanticPast
              ((member, (env n).1), (env n).2) ∧
          child.selected.1 = (output.2 row).1 ∧
          PairedStrategyMemory.step (A := A)
              (.processOne (realization.entry member)
                (realization.minimum member))
              (.fromOne row (semanticPast.map fun old => (old.1.2, old.2))
                (env n)) =
            .processTwo child.actualEntry child.actualMinimum := by
  classical
  dsimp only
  let coherent := realization.coherentTable A
  obtain ⟨semanticPast, houtput⟩ :=
    profiledOpenRightCoherentOutputAt_semantic A source strategy hwin
      realization.entry basis coherent member env n
  let physicalPast := semanticPast.map fun old => (old.1.2, old.2)
  rw [houtput]
  let child := profiledOpenRightSemanticChildPointedRealization A source
    strategy hwin basis realization member physicalPast (env n) row
  refine ⟨semanticPast, ?_, rfl, ?_, ?_⟩
  · simpa [profiledOpenRightSemanticClassifiedFamilyReceiver,
      finiteRootFamilyReceiver, profiledOpenRightSemanticClassifiedReceiver,
      physicalPast] using child
  · exact profiledOpenRightSemanticChildPointedRealization_selected A source
      strategy hwin basis realization member physicalPast (env n) row
  · exact
      profiledOpenRightSemanticChildPointedRealization_memory_step A source
        strategy hwin basis realization member physicalPast (env n) row

/-- Left finite-controller pointed handoff. -/
noncomputable def profiledOpenLeftCoherentChildPointed
    (source : ProfiledOpenLeftViewClass A)
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
    (realization : ProfiledOpenLeftRealization A strategy hwin basis source)
    (member : {root // root ∈ source.1})
    (env : Nat → In₁ × In₂) (n : Nat) (row : PairedEntryRow) :
    let output := profiledOpenLeftRepresentableOutputAt A source
      (realization.coherentTable A).table member env n
    ProfiledOpenRightPointedRealization A strategy hwin basis
      (output.2 row).2 := by
  let coherent := realization.coherentTable A
  have hex :=
    profiledOpenLeftCoherentOutputAt_semantic A source strategy hwin
      realization.entry basis coherent member env n
  let semanticPast := Classical.choose hex
  have houtput := Classical.choose_spec hex
  let physicalPast := semanticPast.map fun old => (old.1.2, old.2)
  rw [houtput]
  simpa [profiledOpenLeftSemanticClassifiedFamilyReceiver,
    finiteRootFamilyReceiver, profiledOpenLeftSemanticClassifiedReceiver,
    physicalPast] using
    (profiledOpenLeftSemanticChildPointedRealization A source strategy hwin
      basis realization member physicalPast (env n) row)

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Exact left-to-right mirror of
`exists_profiledOpenRightCoherentChildStep`. -/
theorem exists_profiledOpenLeftCoherentChildStep
    (source : ProfiledOpenLeftViewClass A)
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
    (realization : ProfiledOpenLeftRealization A strategy hwin basis source)
    (member : {root // root ∈ source.1})
    (env : Nat → In₁ × In₂) (n : Nat) (row : PairedEntryRow) :
    let output := profiledOpenLeftRepresentableOutputAt A source
      (realization.coherentTable A).table member env n
    ∃ semanticPast :
        List ((({root // root ∈ source.1} × In₁) × In₂)),
      ∃ child : ProfiledOpenRightPointedRealization A strategy hwin basis
          (output.2 row).2,
        output =
            profiledOpenLeftSemanticClassifiedFamilyReceiver A source strategy
              hwin realization.entry basis semanticPast
              ((member, (env n).1), (env n).2) ∧
          child.selected.1 = (output.2 row).1 ∧
          PairedStrategyMemory.step (A := A)
              (.processTwo (realization.entry member)
                (realization.minimum member))
              (.fromTwo row (semanticPast.map fun old => (old.1.2, old.2))
                (env n)) =
            .processOne child.actualEntry child.actualMinimum := by
  classical
  dsimp only
  let coherent := realization.coherentTable A
  obtain ⟨semanticPast, houtput⟩ :=
    profiledOpenLeftCoherentOutputAt_semantic A source strategy hwin
      realization.entry basis coherent member env n
  let physicalPast := semanticPast.map fun old => (old.1.2, old.2)
  rw [houtput]
  let child := profiledOpenLeftSemanticChildPointedRealization A source
    strategy hwin basis realization member physicalPast (env n) row
  refine ⟨semanticPast, ?_, rfl, ?_, ?_⟩
  · simpa [profiledOpenLeftSemanticClassifiedFamilyReceiver,
      finiteRootFamilyReceiver, profiledOpenLeftSemanticClassifiedReceiver,
      physicalPast] using child
  · exact profiledOpenLeftSemanticChildPointedRealization_selected A source
      strategy hwin basis realization member physicalPast (env n) row
  · exact
      profiledOpenLeftSemanticChildPointedRealization_memory_step A source
        strategy hwin basis realization member physicalPast (env n) row

end

end


end DetParityAutomaton

end DistributedSynthesis
