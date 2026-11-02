/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.Definition.DefPathSummary
import DistributedSynthesis.Formalizations.Definition.DefViews

/-!
# Paired-copy game and locally uniform strategies

This file formalizes Definitions `def:localuniform` and `def:pairedcopy`
from `paper.tex` at the abstraction level used by the appendix.
-/

namespace DistributedSynthesis

universe u v w x y z q

/-- The two values of a pending one-bit acknowledgement copy. -/
abbrev PendingCopy := Bool

/-- A paired copy is indexed by process `1`'s bit and process `2`'s bit. -/
abbrev PairedCopyIndex := PendingCopy × PendingCopy

/-- The graph used for process `1`'s current pending receive bit in a copy. -/
def graphForProcessOneCopy : PendingCopy -> Graph
  | false => .left
  | true => .both

/-- The graph used for process `2`'s current pending receive bit in a copy. -/
def graphForProcessTwoCopy : PendingCopy -> Graph
  | false => .right
  | true => .both

/-- A contingent paired-copy action. -/
structure PairedContingentAction (Out₁ : Type w) (Out₂ : Type x) where
  outputOne : PendingCopy -> Out₁
  outputTwo : PendingCopy -> Out₂

/-- The output pair applied in copy `(i,j)`. -/
def PairedContingentAction.outputInCopy
    {Out₁ : Type w} {Out₂ : Type x}
    (action : PairedContingentAction Out₁ Out₂)
    (copy : PairedCopyIndex) :
    Out₁ × Out₂ :=
  (action.outputOne copy.2, action.outputTwo copy.1)

/--
An abstract paired-history arena provides the copy-local views used to state
local uniformity.
-/
structure PairedHistoryArena
    (In₁ : Type u) (In₂ : Type v) (Out₁ : Type w) (Out₂ : Type x) where
  History : Type y
  viewOne : History -> PairedCopyIndex -> View In₁ In₂ Proc.one
  viewTwo : History -> PairedCopyIndex -> View In₁ In₂ Proc.two

/-- A paired strategy chooses a contingent action after each paired history. -/
abbrev PairedStrategy
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type w} {Out₂ : Type x}
    (arena : PairedHistoryArena In₁ In₂ Out₁ Out₂) :=
  arena.History -> PairedContingentAction Out₁ Out₂

/--
Definition `def:localuniform`: equal copy-local views force equal actual
outputs in the compared copies.
-/
def LocallyUniform
    {In₁ : Type u} {In₂ : Type v} {Out₁ : Type w} {Out₂ : Type x}
    (arena : PairedHistoryArena In₁ In₂ Out₁ Out₂)
    (τ : PairedStrategy arena) : Prop :=
  (∀ ρ ρ' copy copy',
    arena.viewOne ρ copy = arena.viewOne ρ' copy' ->
      (τ ρ).outputOne copy.2 = (τ ρ').outputOne copy'.2) ∧
  (∀ ρ ρ' copy copy',
    arena.viewTwo ρ copy = arena.viewTwo ρ' copy' ->
      (τ ρ).outputTwo copy.1 = (τ ρ').outputTwo copy'.1)

/-- The automaton state and consistency data tracked by the paired-copy game. -/
structure PairedCopyState (State : Type y) where
  copyState : PairedCopyIndex -> State
  consistent : PairedCopyIndex -> Prop

/--
Definition `def:pairedcopy`: the abstract four-copy game data for a
deterministic parity automaton.
-/
structure PairedCopyGame
    (Alphabet : Type u)
    (In₁ : Type v) (In₂ : Type w) (Out₁ : Type x) (Out₂ : Type y) where
  automaton : DetParityAutomaton.{u, z} Alphabet
  arena : PairedHistoryArena.{v, w, x, y, q} In₁ In₂ Out₁ Out₂
  state : PairedCopyState automaton.State
  priorityForInconsistent : Nat
  inconsistentEven :
    ∀ copy, ¬ state.consistent copy -> priorityForInconsistent % 2 = 0
  winningInConsistentCopies : (PairedCopyIndex -> automaton.State) -> Prop

end DistributedSynthesis
