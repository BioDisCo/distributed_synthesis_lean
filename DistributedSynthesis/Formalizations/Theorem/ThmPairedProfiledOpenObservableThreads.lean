/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemObservableThreadTreeRationalization
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledOpenPointedRealization

/-!
# Observable-class trees with coherent open-root threads

The old two-sorted outer run selected a proof-side root and then forgot it
before the next family move.  That permits an unsound root mosaic.  Here the
tree branch contains only the newly observable finite view class, while a
universal hidden thread retains the actual open root.  A shared table is
therefore chosen from observation history only, but parity is checked on every
coherent actual-root trajectory.
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

/-- Public observation at an epoch boundary.  It contains the whole finite
class, never a distinguished root or a strict-leader bit. -/
inductive ProfiledOpenObservation where
  | sink
  | right (source : ProfiledOpenRightViewClass A)
  | left (source : ProfiledOpenLeftViewClass A)

noncomputable instance : Fintype (ProfiledOpenObservation A) := by
  classical
  let Rep := Unit ⊕
    (ProfiledOpenRightViewClass A ⊕ ProfiledOpenLeftViewClass A)
  let e : ProfiledOpenObservation A ≃ Rep :=
    { toFun := fun observation =>
        match observation with
        | .sink => .inl ()
        | .right source => .inr (.inl source)
        | .left source => .inr (.inr source)
      invFun := fun observation =>
        match observation with
        | .inl _ => .sink
        | .inr (.inl source) => .right source
        | .inr (.inr source) => .left source
      left_inv := by intro observation; cases observation <;> rfl
      right_inv := by
        intro observation
        rcases observation with empty | (right | left)
        · cases empty; rfl
        · rfl
        · rfl }
  exact Fintype.ofEquiv Rep e.symm

noncomputable instance : DecidableEq (ProfiledOpenObservation A) :=
  Classical.decEq _

instance : Inhabited (ProfiledOpenObservation A) := ⟨.sink⟩

/-- Root family publicly represented by an observation. -/
noncomputable def ProfiledOpenObservation.roots :
    ProfiledOpenObservation A → Finset (ProfiledOpenClassifiedAnchor A)
  | .sink => {.sink}
  | .right source => profiledOpenRightClassifiedRoots A source
  | .left source => profiledOpenLeftClassifiedRoots A source

/-- A move is legal at an observation precisely when it is a checked finite
table for exactly that public family. -/
def ProfiledOpenObservableMoveValid
    (observation : ProfiledOpenObservation A)
    (move : ProfiledOpenRepresentableMove A) : Prop :=
  move.Valid A ∧ move.roots A = observation.roots A

noncomputable instance : DecidableRel (ProfiledOpenObservableMoveValid A) :=
  fun _ _ => Classical.propDecidable _

/-- The proof-side root named by an exit direction. -/
def ProfiledOpenClassifiedDirection.anchor :
    ProfiledOpenClassifiedDirection A → ProfiledOpenClassifiedAnchor A
  | .fromOne root _ _ _ => .right root
  | .fromTwo root _ _ _ => .left root

/-- Hidden thread state.  `initial` is used only before the first epoch exit;
`dead` is the harmless destination of an observation-inconsistent resolution.
-/
inductive ProfiledOpenThreadState where
  | initial
  | live (anchor : ProfiledOpenClassifiedAnchor A)
  | dead

noncomputable instance : Fintype (ProfiledOpenThreadState A) := by
  classical
  let Rep := Bool ⊕ ProfiledOpenClassifiedAnchor A
  let e : ProfiledOpenThreadState A ≃ Rep :=
    { toFun := fun state =>
        match state with
        | .initial => .inl false
        | .dead => .inl true
        | .live anchor => .inr anchor
      invFun := fun state =>
        match state with
        | .inl false => .initial
        | .inl true => .dead
        | .inr anchor => .live anchor
      left_inv := by intro state; cases state <;> rfl
      right_inv := by
        intro state
        rcases state with bit | anchor
        · cases bit <;> rfl
        · rfl }
  exact Fintype.ofEquiv Rep e.symm

/-- One coherent hidden-root step.  The public letter announces the shared
table and the next observed class.  The hidden resolution supplies the
concrete root/row/block exit. -/
noncomputable def profiledOpenThreadStep
    (initialObservation : ProfiledOpenObservation A)
    (state : ProfiledOpenThreadState A)
    (letter : ProfiledOpenRepresentableMove A × ProfiledOpenObservation A)
    (direction : ProfiledOpenClassifiedDirection A) :
    ProfiledOpenThreadState A := by
  classical
  match state with
  | .dead => exact .dead
  | .initial =>
      if hsource : direction.anchor A ∈ initialObservation.roots A then
        let child := letter.1.successor A direction
        if hclass : child.2 = letter.2.roots A then
          exact .live child.1
        else exact .dead
      else exact .dead
  | .live current =>
      if hsource : direction.anchor A = current then
        let child := letter.1.successor A direction
        if hclass : child.2 = letter.2.roots A then
          exact .live child.1
        else exact .dead
      else exact .dead

/-- Finite universal thread system for coherent epoch roots. -/
noncomputable def profiledOpenThreadSystem
    (initialObservation : ProfiledOpenObservation A) :
    FiniteThreadSystem
      (ProfiledOpenRepresentableMove A × ProfiledOpenObservation A) where
  State := ProfiledOpenThreadState A
  stateFinite := inferInstance
  initial := .initial
  Resolution := ProfiledOpenClassifiedDirection A
  step := profiledOpenThreadStep A initialObservation
  priority := fun state =>
    match state with
    | .initial | .dead => 0
    | .live anchor => profiledOpenClassifiedAnchorPriority A anchor

/-- Model-specific observable coupled monitor. -/
noncomputable abbrev profiledOpenObservableTreeMonitor
    (initialObservation : ProfiledOpenObservation A) :=
  observableThreadTreeMonitor
    (profiledOpenThreadSystem A initialObservation)
    initialObservation (ProfiledOpenObservableMoveValid A)

/-! ## Fixed-strategy realizations supply legal public moves -/

/-- The public right move extracted from one fixed-strategy realization. -/
noncomputable def ProfiledOpenRightRealization.observableMove
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env)}
    {basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis}
    {source : ProfiledOpenRightViewClass A}
    (realization : ProfiledOpenRightRealization A strategy hwin basis source) :
    ProfiledOpenRepresentableMove A :=
  .right source (realization.coherentTable A).table

/-- Left public move. -/
noncomputable def ProfiledOpenLeftRealization.observableMove
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env)}
    {basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis}
    {source : ProfiledOpenLeftViewClass A}
    (realization : ProfiledOpenLeftRealization A strategy hwin basis source) :
    ProfiledOpenRepresentableMove A :=
  .left source (realization.coherentTable A).table

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- The realization move is valid at exactly its public right class. -/
theorem ProfiledOpenRightRealization.observableMove_valid
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env)}
    {basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis}
    {source : ProfiledOpenRightViewClass A}
    (realization : ProfiledOpenRightRealization A strategy hwin basis source) :
    ProfiledOpenObservableMoveValid A (.right source)
      (realization.observableMove A) := by
  let coherent := realization.coherentTable A
  exact ⟨⟨coherent.wins, coherent.representable⟩, rfl⟩

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Left validity mirror. -/
theorem ProfiledOpenLeftRealization.observableMove_valid
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env)}
    {basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis}
    {source : ProfiledOpenLeftViewClass A}
    (realization : ProfiledOpenLeftRealization A strategy hwin basis source) :
    ProfiledOpenObservableMoveValid A (.left source)
      (realization.observableMove A) := by
  let coherent := realization.coherentTable A
  exact ⟨⟨coherent.wins, coherent.representable⟩, rfl⟩

section
omit [Inhabited Out₁] [Inhabited Out₂]

@[simp] theorem profiledOpenThreadStep_dead
    (initialObservation : ProfiledOpenObservation A)
    (letter : ProfiledOpenRepresentableMove A × ProfiledOpenObservation A)
    (direction : ProfiledOpenClassifiedDirection A) :
    profiledOpenThreadStep A initialObservation .dead letter direction =
      .dead := by
  rfl

/-- Exact live-step equation for a coherent noninitial thread. -/
theorem profiledOpenThreadStep_live_of
    (initialObservation : ProfiledOpenObservation A)
    (current : ProfiledOpenClassifiedAnchor A)
    (letter : ProfiledOpenRepresentableMove A × ProfiledOpenObservation A)
    (direction : ProfiledOpenClassifiedDirection A)
    (hsource : direction.anchor A = current)
    (hclass : (letter.1.successor A direction).2 = letter.2.roots A) :
    profiledOpenThreadStep A initialObservation (.live current) letter
        direction =
      .live (letter.1.successor A direction).1 := by
  classical
  simp [profiledOpenThreadStep, hsource, hclass]

/-- An observation-inconsistent live resolution falls to the even sink. -/
theorem profiledOpenThreadStep_live_dead_of_anchor_ne
    (initialObservation : ProfiledOpenObservation A)
    (current : ProfiledOpenClassifiedAnchor A)
    (letter : ProfiledOpenRepresentableMove A × ProfiledOpenObservation A)
    (direction : ProfiledOpenClassifiedDirection A)
    (hsource : direction.anchor A ≠ current) :
    profiledOpenThreadStep A initialObservation (.live current) letter
        direction = .dead := by
  classical
  simp [profiledOpenThreadStep, hsource]

/-- A winning observable move tree has legal shared tables at every public
node and universal min-even parity on every coherent hidden-root run. -/
theorem profiledOpenObservableTree_winning_iff
    (initialObservation : ProfiledOpenObservation A)
    (tree : LabeledTree (ProfiledOpenObservation A)
      (ProfiledOpenRepresentableMove A)) :
    (profiledOpenObservableTreeMonitor A initialObservation).WinningTree tree ↔
      ObservableMovesValid initialObservation
          (ProfiledOpenObservableMoveValid A) tree ∧
        ∀ branch : Nat → ProfiledOpenObservation A,
          (profiledOpenThreadSystem A initialObservation).universalRunDPA.Accepts
            (observableThreadWord tree branch) := by
  exact observableThreadTreeMonitor_winning_iff
    (profiledOpenThreadSystem A initialObservation) initialObservation
      (ProfiledOpenObservableMoveValid A) tree

/-- Once a semantic winning tree is supplied, the shared observable policy
has a fixed finite state-controlled implementation. -/
theorem exists_finite_profiledOpenObservableTable_of_winning
    (initialObservation : ProfiledOpenObservation A)
    (tree : LabeledTree (ProfiledOpenObservation A)
      (ProfiledOpenRepresentableMove A))
    (hwin : (profiledOpenObservableTreeMonitor A initialObservation).WinningTree
      tree) :
    ∃ table : RunParityTreeAutomaton.StateControlledTreeTable
        (profiledOpenObservableTreeMonitor A initialObservation).toRunAutomaton,
      (profiledOpenObservableTreeMonitor A initialObservation).WinningTree
        table.toTransitionRationalTree.labeledTree := by
  exact exists_stateControlled_observableThreadTree_of_winning
    (profiledOpenThreadSystem A initialObservation) initialObservation
      (ProfiledOpenObservableMoveValid A) tree hwin

end

end

end


end DetParityAutomaton

end DistributedSynthesis
