/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledOpenBiBeliefRealization
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenSharedNodeOutput
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenIndexedLineage

/-!
# Common provenance for a correlated indexed handoff

Evaluating the old classified successor separately for each family member
selects a member-dependent narrowed monitor state and yields only
`forall member, exists semanticPast`.  That API is too weak for a correlated
successor class, which needs one block history for all candidates.

The repair is structural and unconditional: evaluate one complete receiver
response table at one shared full family-tree node, then query every current
member in that table.  The coherent table's sticky provenance law now has the
required order `exists semanticPast, forall member` immediately.  This file
proves the shared-node theorem in both orientations and connects its common
history to the exact semantic child roots and finite child-view partition.

The older memberwise interface and its initial-control special case are kept
as an audit: they explain exactly why shared-node evaluation is necessary.
The shared-node result is the local mathematics consumed by
`ProfiledOpenIndexedCorrelatedSuccessorClosure`.

No orientation, member, or strict-leader bit is made observable.  Members and
rows below are proof-side coordinates only.
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

/-! ## The missing correlated quantifier -/

/-- All members of one right family table label have one common semantic
history witness.  The physical block past is public environment data; the
tagged `semanticPast` is proof-side provenance hidden by the finite table.
-/
def ProfiledOpenRightFamilyUniformProvenance
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env)}
    {basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis}
    {source : ProfiledOpenRightViewClass A}
    (realization : ProfiledOpenRightRealization A strategy hwin basis source) :
    Prop :=
  ∀ (past : List (In₂ × In₁)) (input : In₂ × In₁),
    ∃ semanticPast :
        List ((({root // root ∈ source.1} × In₂) × In₁)),
      ∀ member : {root // root ∈ source.1},
        profiledOpenRightRepresentableOutputAt A source
            (realization.coherentTable A).table member
            (omegaOfList (past ++ [input])) past.length =
          profiledOpenRightSemanticClassifiedFamilyReceiver A source strategy
            hwin realization.entry basis semanticPast
            ((member, input.1), input.2)

/-- Left-to-right mirror of family-uniform provenance. -/
def ProfiledOpenLeftFamilyUniformProvenance
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env)}
    {basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis}
    {source : ProfiledOpenLeftViewClass A}
    (realization : ProfiledOpenLeftRealization A strategy hwin basis source) :
    Prop :=
  ∀ (past : List (In₁ × In₂)) (input : In₁ × In₂),
    ∃ semanticPast :
        List ((({root // root ∈ source.1} × In₁) × In₂)),
      ∀ member : {root // root ∈ source.1},
        profiledOpenLeftRepresentableOutputAt A source
            (realization.coherentTable A).table member
            (omegaOfList (past ++ [input])) past.length =
          profiledOpenLeftSemanticClassifiedFamilyReceiver A source strategy
            hwin realization.entry basis semanticPast
            ((member, input.1), input.2)

/-! ## The common witness exists at the initial control -/

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- At block length zero every member reads the same initial narrowed state,
so the coherent table's complete-response-table provenance already gives one
common witness. -/
theorem profiledOpenRightFamilyUniformProvenance_nil
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env)}
    {basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis}
    {source : ProfiledOpenRightViewClass A}
    (realization : ProfiledOpenRightRealization A strategy hwin basis source)
    (input : In₂ × In₁) :
    ∃ semanticPast :
        List ((({root // root ∈ source.1} × In₂) × In₁)),
      ∀ member : {root // root ∈ source.1},
        profiledOpenRightRepresentableOutputAt A source
            (realization.coherentTable A).table member
            (omegaOfList ([] ++ [input])) 0 =
          profiledOpenRightSemanticClassifiedFamilyReceiver A source strategy
            hwin realization.entry basis semanticPast
            ((member, input.1), input.2) := by
  classical
  let coherent := realization.coherentTable A
  let M := finiteRootFamilyMonitor
    (fun member : {root // root ∈ source.1} =>
      profiledOpenRightClassifiedRootMonitor A member.1)
  have htable := coherent.provenance ([] : List In₁) M.initial
  rcases htable with ⟨semanticPast, hsemantic⟩
  refine ⟨semanticPast, ?_⟩
  intro member
  have hat := congrFun hsemantic ((member, input.1), input.2)
  simpa [profiledOpenRightRepresentableOutputAt, treePlay,
    blockLabelApply, tagFiniteRootEnvironment, omegaOfList, M, coherent] using
    hat

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Left initial-control mirror. -/
theorem profiledOpenLeftFamilyUniformProvenance_nil
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env)}
    {basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis}
    {source : ProfiledOpenLeftViewClass A}
    (realization : ProfiledOpenLeftRealization A strategy hwin basis source)
    (input : In₁ × In₂) :
    ∃ semanticPast :
        List ((({root // root ∈ source.1} × In₁) × In₂)),
      ∀ member : {root // root ∈ source.1},
        profiledOpenLeftRepresentableOutputAt A source
            (realization.coherentTable A).table member
            (omegaOfList ([] ++ [input])) 0 =
          profiledOpenLeftSemanticClassifiedFamilyReceiver A source strategy
            hwin realization.entry basis semanticPast
            ((member, input.1), input.2) := by
  classical
  let coherent := realization.coherentTable A
  let M := finiteRootFamilyMonitor
    (fun member : {root // root ∈ source.1} =>
      profiledOpenLeftClassifiedRootMonitor A member.1)
  have htable := coherent.provenance ([] : List In₂) M.initial
  rcases htable with ⟨semanticPast, hsemantic⟩
  refine ⟨semanticPast, ?_⟩
  intro member
  have hat := congrFun hsemantic ((member, input.1), input.2)
  simpa [profiledOpenLeftRepresentableOutputAt, treePlay,
    blockLabelApply, tagFiniteRootEnvironment, omegaOfList, M, coherent] using
    hat

/-! ## One common witness restores the semantic indexed handoff -/

section
omit [Inhabited Out₁] [Inhabited Out₂]

/-- Under one common provenance witness, every finite right-table child root
is exactly the root of the corresponding literal raw-strategy child. -/
theorem profiledOpenRightOutput_root_eq_of_uniformProvenance
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env)}
    {basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis}
    {source : ProfiledOpenRightViewClass A}
    (realization : ProfiledOpenRightRealization A strategy hwin basis source)
    (past : List (In₂ × In₁)) (input : In₂ × In₁)
    (semanticPast :
      List ((({root // root ∈ source.1} × In₂) × In₁)))
    (huniform : ∀ member : {root // root ∈ source.1},
      profiledOpenRightRepresentableOutputAt A source
          (realization.coherentTable A).table member
          (omegaOfList (past ++ [input])) past.length =
        profiledOpenRightSemanticClassifiedFamilyReceiver A source strategy
          hwin realization.entry basis semanticPast
          ((member, input.1), input.2))
    (member : {root // root ∈ source.1}) (row : PairedEntryRow) :
    ((profiledOpenRightRepresentableOutputAt A source
        (realization.coherentTable A).table member
        (omegaOfList (past ++ [input])) past.length).2 row).1 =
      profiledOpenLeftRootOfWinning A strategy hwin
        (procTwoViewClassChild strategy realization.entry
          (semanticPast.map fun old => (old.1.2, old.2)) input (member, row))
        (procTwoViewClassChildMinimum A realization.entry
          (semanticPast.map fun old => (old.1.2, old.2)) (member, row)) basis := by
  rw [huniform member]
  rfl

/-- Left root mirror. -/
theorem profiledOpenLeftOutput_root_eq_of_uniformProvenance
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env)}
    {basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis}
    {source : ProfiledOpenLeftViewClass A}
    (realization : ProfiledOpenLeftRealization A strategy hwin basis source)
    (past : List (In₁ × In₂)) (input : In₁ × In₂)
    (semanticPast :
      List ((({root // root ∈ source.1} × In₁) × In₂)))
    (huniform : ∀ member : {root // root ∈ source.1},
      profiledOpenLeftRepresentableOutputAt A source
          (realization.coherentTable A).table member
          (omegaOfList (past ++ [input])) past.length =
        profiledOpenLeftSemanticClassifiedFamilyReceiver A source strategy
          hwin realization.entry basis semanticPast
          ((member, input.1), input.2))
    (member : {root // root ∈ source.1}) (row : PairedEntryRow) :
    ((profiledOpenLeftRepresentableOutputAt A source
        (realization.coherentTable A).table member
        (omegaOfList (past ++ [input])) past.length).2 row).1 =
      profiledOpenRightRootOfWinning A strategy hwin
        (procOneViewClassChild strategy realization.entry
          (semanticPast.map fun old => (old.1.2, old.2)) input (member, row))
        (procOneViewClassChildMinimum A realization.entry
          (semanticPast.map fun old => (old.1.2, old.2)) (member, row)) basis := by
  rw [huniform member]
  rfl

/-- With the same common semantic past, the finite old-opposite-view pattern
is exactly equality of the literal right-to-left child views.  This is the
partition equation needed by the indexed successor code. -/
theorem procTwoUniformProvenance_child_view_eq_iff_oldPattern
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env)}
    {basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis}
    {source : ProfiledOpenRightViewClass A}
    (realization : ProfiledOpenRightRealization A strategy hwin basis source)
    (semanticPast :
      List ((({root // root ∈ source.1} × In₂) × In₁)))
    (input : In₂ × In₁)
    (left right : {root // root ∈ source.1} × PairedEntryRow) :
    currentView Proc.two
        (procTwoViewClassChild strategy realization.entry
          (semanticPast.map fun old => (old.1.2, old.2)) input left).rightHistory =
      currentView Proc.two
        (procTwoViewClassChild strategy realization.entry
          (semanticPast.map fun old => (old.1.2, old.2)) input right).rightHistory ↔
      procOneEntryOppositeViewPattern strategy realization.entry left right =
        true := by
  classical
  rw [procTwoViewClassChild_view_eq_iff strategy realization.entry
    (fun l r => (realization.view_eq l).trans
      (realization.view_eq r).symm)]
  change _ ↔ decide (_ = _) = true
  simp

/-- Left-to-right partition mirror. -/
theorem procOneUniformProvenance_child_view_eq_iff_oldPattern
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env)}
    {basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis}
    {source : ProfiledOpenLeftViewClass A}
    (realization : ProfiledOpenLeftRealization A strategy hwin basis source)
    (semanticPast :
      List ((({root // root ∈ source.1} × In₁) × In₂)))
    (input : In₁ × In₂)
    (left right : {root // root ∈ source.1} × PairedEntryRow) :
    currentView Proc.one
        (procOneViewClassChild strategy realization.entry
          (semanticPast.map fun old => (old.1.2, old.2)) input left).leftHistory =
      currentView Proc.one
        (procOneViewClassChild strategy realization.entry
          (semanticPast.map fun old => (old.1.2, old.2)) input right).leftHistory ↔
      procTwoEntryOppositeViewPattern strategy realization.entry left right =
        true := by
  classical
  rw [procOneViewClassChild_view_eq_iff strategy realization.entry
    (fun l r => (realization.view_eq l).trans
      (realization.view_eq r).symm)]
  change _ ↔ decide (_ = _) = true
  simp

end

/-! ## Shared-node evaluation removes the residual -/

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- The desired quantifier order is automatic at a shared right-family node:
the sticky law applies to the complete response table before any current
member is queried. -/
theorem exists_profiledOpenRightSharedNode_semanticPast
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env)}
    {basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis}
    {source : ProfiledOpenRightViewClass A}
    (realization : ProfiledOpenRightRealization A strategy hwin basis source)
    (node : List ((({root // root ∈ source.1} × In₂) × In₁)))
    (input : In₂ × In₁) :
    ∃ semanticPast :
        List ((({root // root ∈ source.1} × In₂) × In₁)),
      ∀ member : {root // root ∈ source.1},
        profiledOpenRightSharedNodeOutput A source
            (realization.coherentTable A).table node member input =
          profiledOpenRightSemanticClassifiedFamilyReceiver A source strategy
            hwin realization.entry basis semanticPast
            ((member, input.1), input.2) := by
  let coherent := realization.coherentTable A
  have htable := narrowedInducedTree_receiver_allowed
    (finiteRootFamilyMonitor
      (fun member : {root // root ∈ source.1} =>
        profiledOpenRightClassifiedRootMonitor A member.1))
    (ProfiledOpenRightSemanticTableAllowed A source strategy hwin
      realization.entry basis)
    coherent.table.toTransitionRationalTree.labeledTree coherent.provenance
    node
  rcases htable with ⟨semanticPast, hsemantic⟩
  refine ⟨semanticPast, ?_⟩
  intro member
  exact congrFun hsemantic ((member, input.1), input.2)

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Left shared-node provenance. -/
theorem exists_profiledOpenLeftSharedNode_semanticPast
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env)}
    {basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis}
    {source : ProfiledOpenLeftViewClass A}
    (realization : ProfiledOpenLeftRealization A strategy hwin basis source)
    (node : List ((({root // root ∈ source.1} × In₁) × In₂)))
    (input : In₁ × In₂) :
    ∃ semanticPast :
        List ((({root // root ∈ source.1} × In₁) × In₂)),
      ∀ member : {root // root ∈ source.1},
        profiledOpenLeftSharedNodeOutput A source
            (realization.coherentTable A).table node member input =
          profiledOpenLeftSemanticClassifiedFamilyReceiver A source strategy
            hwin realization.entry basis semanticPast
            ((member, input.1), input.2) := by
  let coherent := realization.coherentTable A
  have htable := narrowedInducedTree_receiver_allowed
    (finiteRootFamilyMonitor
      (fun member : {root // root ∈ source.1} =>
        profiledOpenLeftClassifiedRootMonitor A member.1))
    (ProfiledOpenLeftSemanticTableAllowed A source strategy hwin
      realization.entry basis)
    coherent.table.toTransitionRationalTree.labeledTree coherent.provenance
    node
  rcases htable with ⟨semanticPast, hsemantic⟩
  refine ⟨semanticPast, ?_⟩
  intro member
  exact congrFun hsemantic ((member, input.1), input.2)

/-! ## Exact public-table correlated handoff -/

section
omit [Inhabited Out₁] [Inhabited Out₂]

/-- At one shared right node, the weakened public table emits exactly the
literal raw-strategy child root for every member and row, all under one
semantic block past. -/
theorem exists_profiledOpenRightClassifiedSharedNode_correlatedRoots
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env)}
    {basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis}
    {source : ProfiledOpenRightViewClass A}
    (realization : ProfiledOpenRightRealization A strategy hwin basis source)
    (node : List ((({root // root ∈ source.1} × In₂) × In₁)))
    (input : In₂ × In₁) :
    ∃ semanticPast :
        List ((({root // root ∈ source.1} × In₂) × In₁)),
      ∀ (member : {root // root ∈ source.1}) (row : PairedEntryRow),
        ((profiledOpenRightClassifiedSharedNodeOutput A source
            ((realization.coherentTable A).table.toClassified A source)
            node member input).2 row).1 =
          profiledOpenLeftRootOfWinning A strategy hwin
            (procTwoViewClassChild strategy realization.entry
              (semanticPast.map fun old => (old.1.2, old.2)) input
              (member, row))
            (procTwoViewClassChildMinimum A realization.entry
              (semanticPast.map fun old => (old.1.2, old.2)) (member, row))
            basis := by
  rcases exists_profiledOpenRightSharedNode_semanticPast A realization node
      input with ⟨semanticPast, huniform⟩
  refine ⟨semanticPast, ?_⟩
  intro member row
  rw [profiledOpenRightClassifiedSharedNodeOutput_toClassified,
    huniform member]
  rfl

/-- Left public-table correlated root theorem. -/
theorem exists_profiledOpenLeftClassifiedSharedNode_correlatedRoots
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env)}
    {basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis}
    {source : ProfiledOpenLeftViewClass A}
    (realization : ProfiledOpenLeftRealization A strategy hwin basis source)
    (node : List ((({root // root ∈ source.1} × In₁) × In₂)))
    (input : In₁ × In₂) :
    ∃ semanticPast :
        List ((({root // root ∈ source.1} × In₁) × In₂)),
      ∀ (member : {root // root ∈ source.1}) (row : PairedEntryRow),
        ((profiledOpenLeftClassifiedSharedNodeOutput A source
            ((realization.coherentTable A).table.toClassified A source)
            node member input).2 row).1 =
          profiledOpenRightRootOfWinning A strategy hwin
            (procOneViewClassChild strategy realization.entry
              (semanticPast.map fun old => (old.1.2, old.2)) input
              (member, row))
            (procOneViewClassChildMinimum A realization.entry
              (semanticPast.map fun old => (old.1.2, old.2)) (member, row))
            basis := by
  rcases exists_profiledOpenLeftSharedNode_semanticPast A realization node
      input with ⟨semanticPast, huniform⟩
  refine ⟨semanticPast, ?_⟩
  intro member row
  rw [profiledOpenLeftClassifiedSharedNodeOutput_toClassified,
    huniform member]
  rfl

/-- Full right correlated step: one common hidden past simultaneously
identifies every public child root and the exact child-view partition carried
by the finite old-opposite-view pattern. -/
theorem exists_profiledOpenRightClassifiedSharedNode_correlatedStep
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env)}
    {basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis}
    {source : ProfiledOpenRightViewClass A}
    (realization : ProfiledOpenRightRealization A strategy hwin basis source)
    (node : List ((({root // root ∈ source.1} × In₂) × In₁)))
    (input : In₂ × In₁) :
    ∃ semanticPast :
        List ((({root // root ∈ source.1} × In₂) × In₁)),
      (∀ (member : {root // root ∈ source.1}) (row : PairedEntryRow),
        ((profiledOpenRightClassifiedSharedNodeOutput A source
            ((realization.coherentTable A).table.toClassified A source)
            node member input).2 row).1 =
          profiledOpenLeftRootOfWinning A strategy hwin
            (procTwoViewClassChild strategy realization.entry
              (semanticPast.map fun old => (old.1.2, old.2)) input
              (member, row))
            (procTwoViewClassChildMinimum A realization.entry
              (semanticPast.map fun old => (old.1.2, old.2)) (member, row))
            basis) ∧
      (∀ left right : {root // root ∈ source.1} × PairedEntryRow,
        currentView Proc.two
            (procTwoViewClassChild strategy realization.entry
              (semanticPast.map fun old => (old.1.2, old.2)) input
              left).rightHistory =
          currentView Proc.two
            (procTwoViewClassChild strategy realization.entry
              (semanticPast.map fun old => (old.1.2, old.2)) input
              right).rightHistory ↔
        procOneEntryOppositeViewPattern strategy realization.entry left right =
          true) := by
  rcases exists_profiledOpenRightClassifiedSharedNode_correlatedRoots A
      realization node input with ⟨semanticPast, hroots⟩
  refine ⟨semanticPast, hroots, ?_⟩
  exact procTwoUniformProvenance_child_view_eq_iff_oldPattern A realization
    semanticPast input

/-- Full left correlated step. -/
theorem exists_profiledOpenLeftClassifiedSharedNode_correlatedStep
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env)}
    {basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis}
    {source : ProfiledOpenLeftViewClass A}
    (realization : ProfiledOpenLeftRealization A strategy hwin basis source)
    (node : List ((({root // root ∈ source.1} × In₁) × In₂)))
    (input : In₁ × In₂) :
    ∃ semanticPast :
        List ((({root // root ∈ source.1} × In₁) × In₂)),
      (∀ (member : {root // root ∈ source.1}) (row : PairedEntryRow),
        ((profiledOpenLeftClassifiedSharedNodeOutput A source
            ((realization.coherentTable A).table.toClassified A source)
            node member input).2 row).1 =
          profiledOpenRightRootOfWinning A strategy hwin
            (procOneViewClassChild strategy realization.entry
              (semanticPast.map fun old => (old.1.2, old.2)) input
              (member, row))
            (procOneViewClassChildMinimum A realization.entry
              (semanticPast.map fun old => (old.1.2, old.2)) (member, row))
            basis) ∧
      (∀ left right : {root // root ∈ source.1} × PairedEntryRow,
        currentView Proc.one
            (procOneViewClassChild strategy realization.entry
              (semanticPast.map fun old => (old.1.2, old.2)) input
              left).leftHistory =
          currentView Proc.one
            (procOneViewClassChild strategy realization.entry
              (semanticPast.map fun old => (old.1.2, old.2)) input
              right).leftHistory ↔
        procTwoEntryOppositeViewPattern strategy realization.entry left right =
          true) := by
  rcases exists_profiledOpenLeftClassifiedSharedNode_correlatedRoots A
      realization node input with ⟨semanticPast, hroots⟩
  refine ⟨semanticPast, hroots, ?_⟩
  exact procOneUniformProvenance_child_view_eq_iff_oldPattern A realization
    semanticPast input

end

end

end DetParityAutomaton

end DistributedSynthesis
