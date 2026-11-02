/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentTrees.CanonicalChildren
import DistributedSynthesis.Formalizations.ComponentTrees.FiniteChild
import DistributedSynthesis.Formalizations.ComponentGames.ExecutableIsomorphisms

/-! Reconstruct one entire concrete child from its finite numbering.
The map is a finite bijection preserving all vertices and block states.
-/
namespace Characterisation.ComponentTrees.CanonicalEncode
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks
open Characterisation.ComponentTrees.FiniteTransport
open Characterisation.ComponentGames Characterisation.ComponentGames.HistoryGame
open scoped Characterisation.ComponentGames.Representation DistributedSynthesis.FiniteOrders
open scoped Characterisation.ComponentGames.FiniteEnumeration
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false
variable {I₁ I₂ O₁ O₂ G : Type} {D capacity : Nat}
variable [Fintype I₁] [Fintype I₂] [DecidableEq I₁] [DecidableEq I₂]
variable [Fintype O₁] [Fintype O₂] [DecidableEq O₁] [DecidableEq O₂]
variable (B : DetParityAutomaton (BlockWord (ContinuationLetter I₁ I₂ O₁ O₂) D))
variable [LinearOrder B.State]
variable (M : Recognizer Graph G) [DecidablePred (· ∈ M.accept)]
variable (live : B.State → Bool)
variable (liveCorrect : ∀ h q, StateReachable B h q →
  (live q = true ↔ M.eval (History.graphSequence h) ∈ M.accept))
variable {bound : Nat}
variable [LinearOrder I₁] [LinearOrder I₂]
variable (positive : 0 < capacity)
variable (fits : bound * Nat.card (RoundRecord I₁ I₂ Graph Unit Unit) ^ D ≤ capacity)
variable (N : CompressedNode B M bound)
variable (A : FinitePositions.Position B.State capacity)
variable (e : Representation.Iso (FinitePositions.historyData N.position) A.2)

abbrev move : FiniteAlphabet.Move (capacity:=capacity) B := FiniteEncode.move B M N A e

def letter : {raw : FiniteAlphabet.Raw (capacity:=capacity) B // FiniteAlphabet.Legal B live bound raw} :=
  CanonicalChildren.normalizeLetter B live bound (FiniteAlphabet.initialPosition B positive)
    (FiniteEncode.letter B M live liveCorrect fits N A e)

variable (d : Fin capacity) (c : FiniteAlphabet.Child B (move B M N A e))
variable (entry : (letter B M live liveCorrect positive fits N A e).val.2 d = some c)

def child : Position I₁ I₂ B.State D :=
  FiniteTransport.childPosition B M live liveCorrect N.position N.valid N.reduction N.runMove.rule A e c
    ((letter B M live liveCorrect positive fits N A e).property.2.2.2.2.1 d c entry)

theorem child_next : N.Successor (child B M live liveCorrect positive fits N A e d c entry) :=
  (FullExtensions.original_successor_iff B M N _).mpr
    (FiniteTransport.childPosition_next B M live liveCorrect N.position N.valid N.reduction N.runMove.rule A e c _)

def childIso : Representation.Iso
    (FinitePositions.historyData (child B M live liveCorrect positive fits N A e d c entry)) c.1.2 :=
  FiniteTransport.childIso B M live liveCorrect N.position N.valid N.reduction N.runMove.rule A e c _

theorem child_trace (k : c.1.Root) (h : N.position.Root) (u : BlockInput I₁ I₂ D)
    (endpoint : c.2 k = wordScenario ((move B M N A e).replacement (e.toEquiv h)) u) :
    ((childIso B M live liveCorrect positive fits N A e d c entry).toEquiv.symm k).val =
      (N.reduction.map.edge h).val ++ u.val :=
  FiniteTransport.childIso_trace B M live liveCorrect N.position N.valid N.reduction N.runMove.rule A e c _ k h u endpoint

include entry in
theorem child_normalized :
    CanonicalPositions.normalizeWith (FiniteAlphabet.initialPosition B positive) c.1 = c.1 :=
  CanonicalChildren.child_normalized B live bound (FiniteAlphabet.initialPosition B positive)
    (FiniteEncode.letter B M live liveCorrect fits N A e) d c entry

/-- The component enumeration fills precisely the first k directions. -/
theorem children_packed : ∃ k : Fin (capacity+1), ∀ d : Fin capacity,
    ((letter B M live liveCorrect positive fits N A e).val.2 d).isSome = decide (d.val < k.val) := by
  let m := FiniteEncode.move B M N A e
  let small := (FiniteEncode.move_checks B M N A e).2.2.2
  let count := Fintype.card (FiniteAlphabet.Components B live m)
  have boundCount : count ≤ capacity := FiniteAlphabet.components_card B live bound m small fits
  refine ⟨⟨count,by omega⟩,fun d => ?_⟩
  change ((FiniteAlphabet.children B live bound m small fits d).map _).isSome = _
  rw [Option.isSome_map]
  unfold FiniteAlphabet.children
  split_ifs with before
  · exact (decide_eq_true before).symm
  · exact (decide_eq_false before).symm

end
end Characterisation.ComponentTrees.CanonicalEncode
