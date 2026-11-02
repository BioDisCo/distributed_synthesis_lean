/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmParityTreeEmptinessGame

/-!
# State-controlled rational tree extraction

The ordinary Rabin-basis interface existentially hides the finite controller
type.  Recursive controller-family constructions need the stronger fact that,
for a nonempty branch type, the extracted controller can use the parity tree
automaton's own finite state type.  This file exposes that already-proved
construction without adding a new automata assumption.
-/

namespace DistributedSynthesis

universe u v w

namespace RunParityTreeAutomaton

variable {Branch : Type u} {Alphabet : Type v}
variable [Fintype Branch] [Fintype Alphabet] [Nonempty Branch]
variable (A : RunParityTreeAutomaton.{u, v, w} Branch Alphabet)

/-- A transition-rational tree with its control type fixed to the automaton
state type.  Unlike `TransitionRationalTree`, this is itself a finite type and
can therefore be used as the move alphabet of another finite game. -/
structure StateControlledTreeTable where
  step : A.State → Branch → A.State
  label : A.State → Alphabet

noncomputable instance : Fintype (StateControlledTreeTable A) := by
  classical
  let e : StateControlledTreeTable A ≃
      ((A.State → Branch → A.State) × (A.State → Alphabet)) :=
    { toFun := fun table => (table.step, table.label)
      invFun := fun table => ⟨table.1, table.2⟩
      left_inv := by intro table; cases table; rfl
      right_inv := by intro table; cases table; rfl }
  exact Fintype.ofEquiv _ e.symm

namespace StateControlledTreeTable

/-- Interpret a finite table as a transition-rational tree. -/
def toTransitionRationalTree (table : StateControlledTreeTable A) :
    TransitionRationalTree.{u, v, w} Branch Alphabet where
  Control := A.State
  controlFinite := A.stateFinite
  initial := A.initial
  step := table.step
  labelOf := table.label

end StateControlledTreeTable

/-- Acceptance puts the initial emptiness-game position in Even's positional
winning region. -/
theorem exists_evenPositionalStrategy_of_accepts
    (haccepts : ∃ tree : LabeledTree Branch Alphabet, A.acceptsTree tree) :
    ∃ σ : (emptinessGame A).PositionalStrategy ParityPlayer.even,
      CountableParityGame.PositionalStrategy.WinningFrom
        (G := emptinessGame A) σ (some (Sum.inl A.initial)) := by
  classical
  obtain ⟨tree, htree⟩ := haccepts
  rcases (emptinessGame A).positionalGameDetermined
      (some (Sum.inl A.initial)) with heven | hodd
  · exact heven
  · exact absurd hodd (not_positionalWinningRegion_odd_of_accepts A htree)

/-- Canonical accepted controller.  Its control type is definitionally
`A.State`, rather than an existentially hidden finite type. -/
noncomputable def stateControlledAcceptedTree
    (haccepts : ∃ tree : LabeledTree Branch Alphabet, A.acceptsTree tree) :
    TransitionRationalTree.{u, v, w} Branch Alphabet :=
  let witness := Classical.choose haccepts
  let strategy := Classical.choose
    (A.exists_evenPositionalStrategy_of_accepts haccepts)
  extractedTree A strategy (witness [])

theorem stateControlledAcceptedTree_accepts
    (haccepts : ∃ tree : LabeledTree Branch Alphabet, A.acceptsTree tree) :
    A.acceptsTree (A.stateControlledAcceptedTree haccepts).labeledTree := by
  let hstrategy := Classical.choose_spec
    (A.exists_evenPositionalStrategy_of_accepts haccepts)
  exact acceptsTree_extractedTree A
    (Classical.choose (A.exists_evenPositionalStrategy_of_accepts haccepts))
    (Classical.choose haccepts []) hstrategy

/-- The advertised fixed-control fact. -/
theorem stateControlledAcceptedTree_control_eq
    (haccepts : ∃ tree : LabeledTree Branch Alphabet, A.acceptsTree tree) :
    (A.stateControlledAcceptedTree haccepts).Control = A.State := rfl

/-- Finite-table form of the Rabin basis theorem.  The witness space is now
literally finite, which removes the apparent self-reference when these
controllers are selected by an outer parity policy. -/
theorem exists_stateControlledTreeTable_accepted
    (haccepts : ∃ tree : LabeledTree Branch Alphabet, A.acceptsTree tree) :
    ∃ table : StateControlledTreeTable A,
      A.acceptsTree table.toTransitionRationalTree.labeledTree := by
  classical
  let witness := Classical.choose haccepts
  let strategy := Classical.choose
    (A.exists_evenPositionalStrategy_of_accepts haccepts)
  have hstrategy := Classical.choose_spec
    (A.exists_evenPositionalStrategy_of_accepts haccepts)
  let table : StateControlledTreeTable A :=
    { step := chosenChildren A strategy
      label := chosenLabel A strategy (witness []) }
  refine ⟨table, ?_⟩
  exact acceptsTree_extractedTree A strategy (witness []) hstrategy

end RunParityTreeAutomaton

end DistributedSynthesis
