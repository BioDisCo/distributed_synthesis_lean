/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentTrees.EncodeTree
import DistributedSynthesis.Formalizations.ComponentGames.ExecutableIsomorphisms

/-! Reconstruct one entire concrete child from its finite numbering.
The map is a finite bijection preserving all vertices and block states.
-/
namespace Characterisation.ComponentTrees
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks
open Characterisation.ComponentTrees.FiniteTransport
open Characterisation.ComponentTrees.FiniteDecode
open Characterisation.ComponentGames Characterisation.ComponentGames.HistoryGame
open scoped Characterisation.ComponentGames.Representation DistributedSynthesis.FiniteOrders
open scoped Characterisation.ComponentGames.FiniteEnumeration
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false
variable {I₁ I₂ O₁ O₂ G : Type} {D capacity : Nat}
variable [Fintype I₁] [Fintype I₂] [DecidableEq I₁] [DecidableEq I₂]
variable [Fintype O₁] [Fintype O₂] [DecidableEq O₁] [DecidableEq O₂]
variable (B : DetParityAutomaton (BlockWord (ContinuationLetter I₁ I₂ O₁ O₂) D))
variable [DecidableEq B.State]
variable (M : Recognizer Graph G) [DecidablePred (· ∈ M.accept)]
variable (live : B.State → Bool)
variable (liveCorrect : ∀ h q, StateReachable B h q →
  (live q = true ↔ M.eval (History.graphSequence h) ∈ M.accept))
include liveCorrect
variable {bound : Nat}
variable [LinearOrder I₁] [LinearOrder I₂]

/-- Both recursive transports follow `lem:tree-mso`: all components and all
compatible runs are preserved. The reverse transport is executable. -/
theorem model_tree_iff (positive : 0 < capacity)
    (initialLive : M.eval [] ∈ M.accept)
    (fits : bound * Nat.card (RoundRecord I₁ I₂ Graph Unit Unit) ^ D ≤ capacity) :
    (∃ code, FiniteRunMSO.Accepting (FiniteAlphabet.tables B live bound positive) code) ↔
      ∃ tree : CompressedTree B M bound, tree.Accepting := by
  constructor
  · rintro ⟨code,accepting⟩
    exact ⟨ModelDecode.tree B M live liveCorrect positive initialLive code accepting.1,
      ModelDecode.tree_accepting B M live liveCorrect positive initialLive code accepting.1 accepting⟩
  · rintro ⟨tree,accepting⟩
    exact ⟨ModelEncode.code B M live liveCorrect positive fits tree accepting.1,
      ModelEncode.code_accepting B M live liveCorrect positive fits tree accepting.1 accepting⟩

variable [LinearOrder O₁] [LinearOrder O₂] [LinearOrder B.State]

/-- The finite formula is equivalent to actual compressed-tree existence;
no table-realizability or run-lifting hypothesis remains. -/
theorem mso_compressed_iff (positive : 0 < capacity)
    (initialLive : M.eval [] ∈ M.accept)
    (fits : bound * Nat.card (RoundRecord I₁ I₂ Graph Unit Unit) ^ D ≤ capacity) :
    (∃ code, MSO.Tree.Satisfies code (FiniteAlphabet.sentence B live bound positive)) ↔
      ∃ tree : CompressedTree B M bound, tree.Accepting :=
  (exists_congr (FiniteAlphabet.sentence_correct B live bound positive)).trans
    (model_tree_iff B M live liveCorrect positive initialLive fits)

theorem finite_satisfiable_correct (positive : 0 < capacity)
    (initialLive : M.eval [] ∈ M.accept)
    (fits : bound * Nat.card (RoundRecord I₁ I₂ Graph Unit Unit) ^ D ≤ capacity) :
    FiniteAlphabet.satisfiable B live bound positive = true ↔
      ∃ tree : CompressedTree B M bound, tree.Accepting :=
  (FiniteAlphabet.satisfiable_correct B live bound positive).trans
    (model_tree_iff B M live liveCorrect positive initialLive fits)

end Characterisation.ComponentTrees
