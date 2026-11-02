/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentTrees.EncodeLetter
import DistributedSynthesis.Formalizations.ComponentTrees.FiniteChild
import DistributedSynthesis.Formalizations.ComponentGames.ExecutableIsomorphisms

/-! Reconstruct one entire concrete child from its finite numbering.
The map is a finite bijection preserving all vertices and block states.
-/
namespace Characterisation.ComponentTrees.FiniteEncode
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
variable [DecidableEq B.State]
variable (M : Recognizer Graph G) [DecidablePred (· ∈ M.accept)]
variable (live : B.State → Bool)
variable (liveCorrect : ∀ h q, StateReachable B h q →
  (live q = true ↔ M.eval (History.graphSequence h) ∈ M.accept))
variable {bound : Nat}
variable [LinearOrder I₁] [LinearOrder I₂]
variable (fits : bound * Nat.card (RoundRecord I₁ I₂ Graph Unit Unit) ^ D ≤ capacity)
variable (N : CompressedNode B M bound)
variable (A : FinitePositions.Position B.State capacity)
variable (e : Representation.Iso (FinitePositions.historyData N.position) A.2)

def move : FiniteAlphabet.Move (capacity:=capacity) B :=
  pushMove B N.position N.reduction N.runMove.rule A e

theorem move_checks : FinitePositions.ReductionChecks A.2 bound (move B M N A e).replacement := by
  apply (FinitePositions.reductionChecks_transport (FinitePositions.historyData N.position) A.2 e bound _).mpr
  apply (FinitePositions.reductionChecks_history N.position bound N.reduction.map.edge).mpr
  refine ⟨N.reduction,rfl,?_⟩
  rw [← N.reduction.imagePosition_card N.position]
  exact N.small

theorem move_coherent : ClosingPolicyCoherent A.2.shape (move B M N A e).rule := by
  apply (Representation.coherent_iff e.toEquiv N.position.shape A.2.shape
    (root_shapes B N.position A e) N.runMove.rule).mpr
  exact simulation_rule_coherent N.position.past (N.reduction.imagePosition N.position).past
    (N.reduction.imageProjection N.position) N.reduction.map.preserves_views N.rule N.distributed

def letter : {raw : FiniteAlphabet.Raw (capacity:=capacity) B // FiniteAlphabet.Legal B live bound raw} := by
  let m := move B M N A e
  have checks := move_checks B M N A e
  refine ⟨⟨m,FiniteAlphabet.children B live bound m checks.2.2.2 fits⟩,
    FiniteAlphabet.raw_legal B live bound m checks.2.2.2 fits ?_ ?_ checks (move_coherent B M N A e)⟩
  · obtain ⟨h,mem⟩ := N.position.nonempty
    have index := (e.toEquiv ⟨h,mem⟩).isLt
    change 0 < A.1.val
    omega
  · intro j
    obtain ⟨h,rfl⟩ := e.toEquiv.surjective j
    exact (liveCorrect h.val (N.position.state h) (N.valid.2.2 h)).mpr (N.valid.1 h) |>
      fun alive => (congrArg live (e.state_same h)).trans alive

variable (d : Fin capacity) (c : FiniteAlphabet.Child B (move B M N A e))
variable (entry : (letter B M live liveCorrect fits N A e).val.2 d = some c)

def child : Position I₁ I₂ B.State D :=
  FiniteTransport.childPosition B M live liveCorrect N.position N.valid N.reduction N.runMove.rule A e c
    ((letter B M live liveCorrect fits N A e).property.2.2.2.2.1 d c entry)

theorem child_next : N.Successor (child B M live liveCorrect fits N A e d c entry) :=
  (FullExtensions.original_successor_iff B M N _).mpr
    (FiniteTransport.childPosition_next B M live liveCorrect N.position N.valid N.reduction N.runMove.rule A e c _)

def childIso : Representation.Iso
    (FinitePositions.historyData (child B M live liveCorrect fits N A e d c entry)) c.1.2 :=
  FiniteTransport.childIso B M live liveCorrect N.position N.valid N.reduction N.runMove.rule A e c _

theorem child_trace (k : c.1.Root) (h : N.position.Root) (u : BlockInput I₁ I₂ D)
    (endpoint : c.2 k = wordScenario ((move B M N A e).replacement (e.toEquiv h)) u) :
    ((childIso B M live liveCorrect fits N A e d c entry).toEquiv.symm k).val =
      (N.reduction.map.edge h).val ++ u.val :=
  FiniteTransport.childIso_trace B M live liveCorrect N.position N.valid N.reduction N.runMove.rule A e c _ k h u endpoint

end
end Characterisation.ComponentTrees.FiniteEncode
