/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemHiddenCodeContinuityBundle
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledOpenIndexedCodeParity
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledOpenIndexedFiniteDirectionSemantic

/-!
# Hidden continuity for the indexed profiled code objective

The public family carrier and simultaneous family move are parameters.
The hidden state consists of a `ProfiledOpenIndexedBiBeliefCode` and the
control of `profiledOpenIndexedBiBeliefCodeParityDPA`.

Parity ranges over every persistent exact code thread admitted by
`ExactEdge`. The descriptor selected by a `TwoSortedFamilyRun` is not used
to justify parity.
-/

namespace DistributedSynthesis

universe i u v x y s f m

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

variable {FamilyCode : Type f} {FamilyMove : Type m}

/-- The model-specific exact successor law.  Its public arguments are one
simultaneous family move and the next public family code; its endpoints are
proof-only actual indexed belief codes. -/
abbrev ProfiledOpenIndexedExactFamilyEdge :=
  ProfiledOpenIndexedBiBeliefCode A (I := I) →
    FamilyMove → FamilyCode →
      ProfiledOpenIndexedBiBeliefCode A (I := I) → Prop

/-- Concrete hidden `(code, code-parity control)` bundle. -/
noncomputable def profiledOpenIndexedHiddenCodeContinuitySystem
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (ExactEdge : ProfiledOpenIndexedExactFamilyEdge A
      (I := I) (FamilyCode := FamilyCode) (FamilyMove := FamilyMove)) :=
  hiddenCodeContinuitySystem
    (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode)
    initialCode ExactEdge

/-- Persistent exact hidden code trajectory below a public family word. -/
abbrev ProfiledOpenIndexedHiddenCodeThread
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (ExactEdge : ProfiledOpenIndexedExactFamilyEdge A
      (I := I) (FamilyCode := FamilyCode) (FamilyMove := FamilyMove))
    (word : OmegaWord (FamilyMove × FamilyCode)) :=
  HiddenCodeContinuityThread initialCode ExactEdge word

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- The anti-mosaic theorem specialized to the actual indexed code-parity
objective. -/
theorem profiledOpenIndexedHiddenCodeContinuity_accepts_iff
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (ExactEdge : ProfiledOpenIndexedExactFamilyEdge A
      (I := I) (FamilyCode := FamilyCode) (FamilyMove := FamilyMove))
    (word : OmegaWord (FamilyMove × FamilyCode)) :
    (profiledOpenIndexedHiddenCodeContinuitySystem A initialCode ExactEdge).universalRunDPA.Accepts
        word ↔
      ∀ thread : ProfiledOpenIndexedHiddenCodeThread A initialCode ExactEdge
          word,
        (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode).Accepts
          thread.childCodeWord := by
  exact hiddenCodeContinuitySystem_universalRunDPA_accepts_iff
    (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode)
    initialCode ExactEdge word

variable [Fintype FamilyCode] [Fintype FamilyMove] [Inhabited FamilyCode]

/-- Concrete public family monitor.  The move is simultaneous and the
observation is the next finite family code; neither reveals the actual code. -/
noncomputable def profiledOpenIndexedHiddenCodeTreeMonitor
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (ExactEdge : ProfiledOpenIndexedExactFamilyEdge A
      (I := I) (FamilyCode := FamilyCode) (FamilyMove := FamilyMove))
    (initialFamily : FamilyCode)
    (Valid : FamilyCode → FamilyMove → Prop) [DecidableRel Valid] :=
  hiddenCodeContinuityTreeMonitor
    (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode)
    initialCode ExactEdge initialFamily Valid

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Exact concrete winning condition.  This is the interface the staged
semantic extraction must discharge; no selected-descriptor parity premise
appears. -/
theorem profiledOpenIndexedHiddenCodeTreeMonitor_winning_iff
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (ExactEdge : ProfiledOpenIndexedExactFamilyEdge A
      (I := I) (FamilyCode := FamilyCode) (FamilyMove := FamilyMove))
    (initialFamily : FamilyCode)
    (Valid : FamilyCode → FamilyMove → Prop) [DecidableRel Valid]
    (tree : LabeledTree FamilyCode FamilyMove) :
    (profiledOpenIndexedHiddenCodeTreeMonitor A initialCode ExactEdge
      initialFamily Valid).WinningTree tree ↔
      ObservableMovesValid initialFamily Valid tree ∧
        ∀ branch : Nat → FamilyCode,
          ∀ thread : ProfiledOpenIndexedHiddenCodeThread A initialCode
            ExactEdge (observableThreadWord tree branch),
          (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode).Accepts
            thread.childCodeWord := by
  exact hiddenCodeContinuityTreeMonitor_winning_iff
    (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode)
    initialCode ExactEdge initialFamily Valid tree

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Once a staged semantic family tree supplies validity and persistent
exact-thread parity, checked extraction returns one finite public family
controller. -/
theorem exists_profiledOpenIndexedHiddenCodeFamilyController
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (ExactEdge : ProfiledOpenIndexedExactFamilyEdge A
      (I := I) (FamilyCode := FamilyCode) (FamilyMove := FamilyMove))
    (initialFamily : FamilyCode)
    (Valid : FamilyCode → FamilyMove → Prop) [DecidableRel Valid]
    (tree : LabeledTree FamilyCode FamilyMove)
    (hvalid : ObservableMovesValid initialFamily Valid tree)
    (hthreads : ∀ branch : Nat → FamilyCode,
      ∀ thread : ProfiledOpenIndexedHiddenCodeThread A initialCode ExactEdge
        (observableThreadWord tree branch),
      (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode).Accepts
        thread.childCodeWord) :
    ∃ table : RunParityTreeAutomaton.StateControlledTreeTable
        (profiledOpenIndexedHiddenCodeTreeMonitor A initialCode ExactEdge
          initialFamily Valid).toRunAutomaton,
      (profiledOpenIndexedHiddenCodeTreeMonitor A initialCode ExactEdge
        initialFamily Valid).WinningTree
          table.toTransitionRationalTree.labeledTree := by
  exact exists_stateControlled_hiddenCodeContinuityTree
    (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode)
    initialCode ExactEdge initialFamily Valid tree hvalid hthreads

/-! ## Bridge from the coded finite-direction semantic certificate -/

variable (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
variable (hwin : ∀ env : EnvironmentSequence In₁ In₂,
  A.Accepts (execution strategy env))
variable (basis : ∀ state : PairedProfiledTreeState A,
  (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)

/-- The precise lifting obligation owed by a staged public family tree.

Every persistent exact hidden thread below a public family branch must be the
code word of one branch of the already-verified finite-direction correlated
semantic tree.  This statement preserves one whole thread; it is deliberately
stronger than saying that each next family merely contains some acceptable
code. -/
def ProfiledOpenIndexedHiddenFiniteTagLift
    (initial : ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin
      basis (I := I))
    (ExactEdge : ProfiledOpenIndexedExactFamilyEdge A
      (I := I) (FamilyCode := FamilyCode) (FamilyMove := FamilyMove))
    (tree : LabeledTree FamilyCode FamilyMove) : Prop :=
  ∀ branch : Nat → FamilyCode,
    ∀ thread : ProfiledOpenIndexedHiddenCodeThread A
      (initial.code A strategy hwin basis) ExactEdge
      (observableThreadWord tree branch),
      ∃ finiteBranch : Nat →
          ProfiledOpenIndexedFiniteDirectionTag A (I := I),
        thread.childCodeWord =
          (profiledOpenIndexedCorrelatedFiniteTagSemanticTree A strategy hwin
            basis initial).childCodeWord finiteBranch

omit [Fintype FamilyCode] [Fintype FamilyMove] [Inhabited FamilyCode] [Inhabited Out₁]
    [Inhabited Out₂] in
/-- The existing coded finite-direction semantic proof discharges every
hidden exact thread as soon as the staged extraction supplies the literal
thread lift above. -/
theorem profiledOpenIndexedHiddenThreads_accept_of_finiteTagLift
    (initial : ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin
      basis (I := I))
    (ExactEdge : ProfiledOpenIndexedExactFamilyEdge A
      (I := I) (FamilyCode := FamilyCode) (FamilyMove := FamilyMove))
    (tree : LabeledTree FamilyCode FamilyMove)
    (hlift : ProfiledOpenIndexedHiddenFiniteTagLift A strategy hwin basis
      initial ExactEdge tree) :
    ∀ branch : Nat → FamilyCode,
      ∀ thread : ProfiledOpenIndexedHiddenCodeThread A
        (initial.code A strategy hwin basis) ExactEdge
        (observableThreadWord tree branch),
      (profiledOpenIndexedBiBeliefCodeParityDPA A
        (initial.code A strategy hwin basis)).Accepts
          thread.childCodeWord := by
  intro branch thread
  obtain ⟨finiteBranch, hword⟩ := hlift branch thread
  rw [hword]
  exact profiledOpenIndexedCorrelatedFiniteTagSemanticTree_codeDPA_accepts A
    strategy hwin basis initial finiteBranch

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- End-to-end checked finite-controller extraction from the model-facing
finite-tag lift.  This is the reusable handoff to staged family
rationalization. -/
theorem exists_profiledOpenIndexedHiddenCodeFamilyController_of_finiteTagLift
    (initial : ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin
      basis (I := I))
    (ExactEdge : ProfiledOpenIndexedExactFamilyEdge A
      (I := I) (FamilyCode := FamilyCode) (FamilyMove := FamilyMove))
    (initialFamily : FamilyCode)
    (Valid : FamilyCode → FamilyMove → Prop) [DecidableRel Valid]
    (tree : LabeledTree FamilyCode FamilyMove)
    (hvalid : ObservableMovesValid initialFamily Valid tree)
    (hlift : ProfiledOpenIndexedHiddenFiniteTagLift A strategy hwin basis
      initial ExactEdge tree) :
    ∃ table : RunParityTreeAutomaton.StateControlledTreeTable
        (profiledOpenIndexedHiddenCodeTreeMonitor A
          (initial.code A strategy hwin basis) ExactEdge initialFamily Valid
            |>.toRunAutomaton),
      (profiledOpenIndexedHiddenCodeTreeMonitor A
        (initial.code A strategy hwin basis) ExactEdge initialFamily Valid).WinningTree
          table.toTransitionRationalTree.labeledTree := by
  apply exists_profiledOpenIndexedHiddenCodeFamilyController A
    (initial.code A strategy hwin basis) ExactEdge initialFamily Valid tree
    hvalid
  exact profiledOpenIndexedHiddenThreads_accept_of_finiteTagLift A strategy
    hwin basis initial ExactEdge tree hlift

end

end DetParityAutomaton

end DistributedSynthesis
