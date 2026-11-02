/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentTrees.FullExtensions
import DistributedSynthesis.Formalizations.ComponentTrees.FiniteAlphabet
import DistributedSynthesis.Formalizations.ComponentTrees.ExecutableReverse

/-! Transport between concrete history positions and the finite alphabet.
Liveness is used only through its exact specification on reachable states.
-/
namespace Characterisation.ComponentTrees.FiniteTransport
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks
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
variable (P : Position I₁ I₂ B.State D) (valid : PositionValid B M P)
variable (r : Reduction P.past P.state) (out : ClosingPolicy P.Root I₁ I₂ O₁ O₂ D)
variable (A : FinitePositions.Position B.State capacity)
variable (e : Representation.Iso (FinitePositions.historyData P) A.2)

def pushMove : FiniteAlphabet.Move (capacity:=capacity) B :=
  ⟨A,Representation.policy e.toEquiv out,Representation.replacement e.toEquiv r.map.edge⟩

theorem root_shapes (p : Proc) (h k : P.Root) :
    A.2.shape p (e.toEquiv h) (e.toEquiv k) = P.shape p h k := by
  simpa only [FinitePositions.historyData,ExecutableHistories.shape_eq] using e.shape_same p h k

theorem states (h : P.Root) : A.2.state (e.toEquiv h) = P.state h := e.state_same h

include liveCorrect valid in
theorem liveEnd_map (s : P.End) :
    FiniteAlphabet.liveEnd B live (pushMove B P r out A e) (mapClosingLayer e.toEquiv D s) =
      extensionLive M (FullExtensions.full B P r out) s := by
  have state : FiniteAlphabet.endState B (pushMove B P r out A e) (mapClosingLayer e.toEquiv D s) =
      blockSuccessor B P.state out s :=
    FinitePositions.blockSuccessor_transport B (FinitePositions.historyData P) A.2 e out s
  have alive := liveCorrect (P.history s) (blockSuccessor B P.state out s)
    (blockSuccessor_reachable B P out valid.2.2 s)
  have fixed : r.map.edge (closingLayerRoot D s) = closingLayerRoot D s ↔
      closingLayerRoot D s ∈ retained (FullExtensions.full B P r out) := by
    constructor
    · intro eq
      exact Finset.mem_image.mpr ⟨closingLayerRoot D s,Finset.mem_univ _,eq⟩
    · intro mem
      obtain ⟨h,_,eq⟩ := Finset.mem_image.mp mem
      change r.map.edge h = closingLayerRoot D s at eq
      rw [← eq]
      exact r.idempotent h
  apply Bool.eq_iff_iff.mpr
  simp only [FiniteAlphabet.liveEnd,Bool.and_eq_true,decide_eq_true_eq,state]
  change (Representation.replacement e.toEquiv r.map.edge
    (closingLayerRoot D (mapClosingLayer e.toEquiv D s)) =
      closingLayerRoot D (mapClosingLayer e.toEquiv D s) ∧ live (blockSuccessor B P.state out s) = true) ↔ _
  rw [closingLayerRoot_map,Representation.replacement_apply,e.toEquiv.injective.eq_iff,fixed,alive]
  simp only [extensionLive,decide_eq_true_eq]
  rfl

include liveCorrect valid in
theorem component_map (K : Finset P.End)
    (component : IsComponent M (FullExtensions.full B P r out) K) :
    FiniteAlphabet.Component B live (pushMove B P r out A e) (K.image (mapClosingLayer e.toEquiv D)) :=
  component_image_retract _ _ _ _ (mapClosingLayer e.toEquiv D) (mapClosingLayer e.toEquiv.symm D)
    (Representation.mapLayer_inverse e.toEquiv D) (fun _ _ => Representation.mapLayer_inverse' e.toEquiv D _)
    (Representation.layerShape_map e.toEquiv P.shape A.2.shape (root_shapes B P A e) D)
    (liveEnd_map B M live liveCorrect P valid r out A e) K component

include liveCorrect valid in
theorem component_back (K : Finset (pushMove B P r out A e).End)
    (component : FiniteAlphabet.Component B live (pushMove B P r out A e) K) :
    IsComponent M (FullExtensions.full B P r out) (K.image (mapClosingLayer e.toEquiv.symm D)) ∧
      (K.image (mapClosingLayer e.toEquiv.symm D)).image (mapClosingLayer e.toEquiv D) = K :=
  component_pullback_retract _ _ _ _ (mapClosingLayer e.toEquiv D) (mapClosingLayer e.toEquiv.symm D)
    (Representation.mapLayer_inverse e.toEquiv D) (fun _ _ => Representation.mapLayer_inverse' e.toEquiv D _)
    (Representation.layerShape_map e.toEquiv P.shape A.2.shape (root_shapes B P A e) D)
    (liveEnd_map B M live liveCorrect P valid r out A e) K component

end Characterisation.ComponentTrees.FiniteTransport
