/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentTrees.Nodes
import DistributedSynthesis.Formalizations.ComponentTrees.Liveness

/-! Global component trees, reusing `LabeledTree`, `publicSupport`,
`SupportedMovesValid`, and the existing history-run type.

Directions are actual successor positions. An edge is supported exactly
when it names a full successor component with the computed state labels.
Thus every component occurs, not merely a chosen subset. Labels at
unsupported addresses have no semantic effect. There is no finite-state
or regularity restriction on a tree.
-/
namespace Characterisation.ComponentTrees
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks
open Characterisation.ComponentGames Characterisation.ComponentGames.HistoryGame
noncomputable section
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false

variable {I₁ I₂ O₁ O₂ G : Type} {D : Nat}
variable [Fintype I₁] [Fintype I₂] [DecidableEq I₁] [DecidableEq I₂]
variable (B : DetParityAutomaton (BlockWord (ContinuationLetter I₁ I₂ O₁ O₂) D))
variable (M : Recognizer Graph G) [DecidablePred (· ∈ M.accept)]

/-- A full component and a rule, before introducing any reduction. -/
structure UncompressedNode where
  position : Position I₁ I₂ B.State D
  valid : PositionValid B M position
  rule : ClosingPolicy position.Root I₁ I₂ O₁ O₂ D
  distributed : ClosingPolicyCoherent position.shape rule

/-- Successor labels use the BLOCK transition, rather than the old games'
per-round state update. The component and finite-history types are reused. -/
def ComponentSuccessor (m : Move I₁ I₂ O₁ O₂ B.State D)
    (P : Position I₁ I₂ B.State D) : Prop :=
  ∃ C : Finset m.source.End, IsComponent M m C ∧
    P.phase = m.source.phase + 1 ∧ P.histories = C.image m.source.history ∧
    ∀ (h : P.Root) (e : C), h.val = m.source.history e.val →
      P.state h = blockSuccessor B m.source.state m.rule e.val

namespace UncompressedNode
variable {B M} (N : UncompressedNode B M)
def move : Move I₁ I₂ O₁ O₂ B.State D := ⟨N.position, N.rule, id⟩
def Successor := ComponentSuccessor B M N.move
def offers (P : Position I₁ I₂ B.State D) : Bool := decide (N.Successor P)
end UncompressedNode

namespace CompressedNode
variable {B M} {bound : Nat} (N : CompressedNode B M bound)
/-- Only the source and replacement fields are used by `CompatibleRun`.
The rule is its genuine pullback to K, not an unrelated dummy policy. -/
def runMove : Move I₁ I₂ O₁ O₂ B.State D :=
  ⟨N.position, restrictClosingPolicy (N.reduction.imageProjection N.position) N.rule,
    N.reduction.map.edge⟩
def offers (P : Position I₁ I₂ B.State D) : Bool := decide (N.Successor P)
theorem successor_iff (P : Position I₁ I₂ B.State D) :
    N.Successor P ↔ ComponentSuccessor B M N.extensionMove P := Iff.rfl
end CompressedNode

abbrev UncompressedTree := LabeledTree (Position I₁ I₂ B.State D) (UncompressedNode B M)
abbrev CompressedTree (bound : Nat) := LabeledTree (Position I₁ I₂ B.State D) (CompressedNode B M bound)

namespace UncompressedTree
variable {B M} (tree : UncompressedTree B M)
def Valid : Prop := SupportedMovesValid UncompressedNode.offers (Position.initial B.initial)
  (fun P N => N.position = P) tree
abbrev Run (branch : Nat → Position I₁ I₂ B.State D) :=
  HistoryGame.CompatibleRun (fun node => (tree node).move) branch
def Accepting : Prop := tree.Valid ∧
  ∀ branch : Nat → Position I₁ I₂ B.State D,
    (∀ n, publicSupport UncompressedNode.offers tree (branchNode branch n) = true) →
    ∀ run : tree.Run branch,
      NatSeqMinEvenParity (fun n => B.priority ((tree (branchNode branch n)).position.state (run.history n)))
end UncompressedTree

namespace CompressedTree
variable {B M} {bound : Nat} (tree : CompressedTree B M bound)
def Valid : Prop := SupportedMovesValid CompressedNode.offers (Position.initial B.initial)
  (fun P N => N.position = P) tree
abbrev Run (branch : Nat → Position I₁ I₂ B.State D) :=
  HistoryGame.CompatibleRun (fun node => (tree node).runMove) branch
def Accepting : Prop := tree.Valid ∧
  ∀ branch : Nat → Position I₁ I₂ B.State D,
    (∀ n, publicSupport CompressedNode.offers tree (branchNode branch n) = true) →
    ∀ run : tree.Run branch,
      NatSeqMinEvenParity (fun n => B.priority ((tree (branchNode branch n)).position.state (run.history n)))
end CompressedTree

end
end Characterisation.ComponentTrees
