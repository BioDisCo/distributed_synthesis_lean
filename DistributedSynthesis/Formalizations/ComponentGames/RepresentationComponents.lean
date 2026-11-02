/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentGames.RepresentationTransport

namespace Characterisation.ComponentGames.Representation
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks
set_option maxHeartbeats 2400000
set_option linter.unusedSectionVars false
variable {H J I₁ I₂ O₁ O₂ G Q : Type} {D : Nat}

def observationIso (e : H ≃ J) (shape : InputShape H) (other : InputShape J)
    (same : ∀ p h k, other p (e h) (e k) = shape p h k)
    (live : H → Bool) (otherLive : J → Bool) (liveSame : ∀ h, otherLive (e h) = live h) :
    closingObservationGraph shape live ≃g closingObservationGraph other otherLive where
  toEquiv := e
  map_rel_iff' := by
    intro h k
    simp only [closingObservationGraph,e.injective.ne_iff,liveSame,same]

theorem componentMask_map [Fintype H] [Fintype J] [DecidableEq H] [DecidableEq J]
    (e : H ≃ J) (shape : InputShape H) (other : InputShape J)
    (same : ∀ p h k, other p (e h) (e k) = shape p h k)
    (live : H → Bool) (otherLive : J → Bool) (liveSame : ∀ h, otherLive (e h) = live h)
    (h k : H) :
    closingComponentMask other otherLive (e h) (e k) = closingComponentMask shape live h k := by
  have reach : (closingObservationGraph other otherLive).Reachable (e h) (e k) ↔
      (closingObservationGraph shape live).Reachable h k :=
    (observationIso e shape other same live otherLive liveSame).reachable_iff
  simp only [closingComponentMask,liveSame,reach]

variable [DecidableEq I₁] [DecidableEq I₂]

/-- The finite representation consists of precisely the two view equality
relations and the two automaton-state assignments from the manuscript. -/
structure Data (H G Q : Type) where
  shape : InputShape H
  graph : H → G
  state : H → Q

structure Iso (a : Data H G Q) (b : Data J G Q) extends H ≃ J where
  shape_same : ∀ p h k, b.shape p (toEquiv h) (toEquiv k) = a.shape p h k
  graph_same : ∀ h, b.graph (toEquiv h) = a.graph h
  state_same : ∀ h, b.state (toEquiv h) = a.state h

variable [Fintype H] [Fintype J] [DecidableEq H] [DecidableEq J]
variable [Fintype I₁] [Fintype I₂] [Fintype O₁] [Fintype O₂]
variable [DecidableEq O₁] [DecidableEq O₂] [DecidableEq G] [DecidableEq Q]

def legalMoveEquiv (a : Data H G Q) (b : Data J G Q) (e : Iso a b)
    (M : Recognizer Graph G) (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q) (D W : Nat) :
    (legalMoves a.shape M a.graph step a.state D W) ≃ (legalMoves b.shape M b.graph step b.state D W) :=
  ((policyEquiv e.toEquiv).prodCongr (replacementEquiv e.toEquiv)).subtypeEquiv
    (fun move => (legalMoves_transport e.toEquiv a.shape b.shape e.shape_same M a.graph b.graph
      e.graph_same step a.state b.state e.state_same W move.1 move.2).symm)

variable (M : Recognizer Graph G) [DecidablePred (· ∈ M.accept)]
variable (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q)

def liveEnd (a : Data H G Q) (out : ClosingPolicy H I₁ I₂ O₁ O₂ D) (r : H → H)
    (s : ClosingLayer H I₁ I₂ D) : Bool :=
  decide (closingLayerRoot D s ∈ Finset.univ.image r ∧
    closingLayerLabels (fun g input (_ : O₁ × O₂) => M.step g input.2.2) a.graph out D (Nat.le_refl D) s ∈ M.accept)

theorem liveEnd_map (a : Data H G Q) (b : Data J G Q) (e : Iso a b)
    (out : ClosingPolicy H I₁ I₂ O₁ O₂ D) (r : H → H) (s : ClosingLayer H I₁ I₂ D) :
    liveEnd M b (policy e.toEquiv out) (replacement e.toEquiv r) (mapClosingLayer e.toEquiv D s) =
      liveEnd M a out r s := by
  unfold liveEnd
  rw [closingLayerRoot_map,labels_map e.toEquiv _ a.graph b.graph e.graph_same]
  have kept : e.toEquiv (closingLayerRoot D s) ∈ Finset.univ.image (replacement e.toEquiv r) ↔
      closingLayerRoot D s ∈ Finset.univ.image r := by
    simp only [Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨j,eq⟩
      exact ⟨e.toEquiv.symm j,e.toEquiv.injective eq⟩
    · rintro ⟨h,eq⟩
      exact ⟨e.toEquiv h,(replacement_apply e.toEquiv r h).trans (congrArg e.toEquiv eq)⟩
  simp only [kept]

/-- All live connected components correspond exactly, not only their
members that happen to occur along a selected strategy. -/
theorem endComponentMask_map (a : Data H G Q) (b : Data J G Q) (e : Iso a b)
    (out : ClosingPolicy H I₁ I₂ O₁ O₂ D) (r : H → H) (s t : ClosingLayer H I₁ I₂ D) :
    closingComponentMask (closingLayerShape b.shape D)
      (liveEnd M b (policy e.toEquiv out) (replacement e.toEquiv r))
      (mapClosingLayer e.toEquiv D s) (mapClosingLayer e.toEquiv D t) =
    closingComponentMask (closingLayerShape a.shape D) (liveEnd M a out r) s t :=
  componentMask_map (layerEquiv e.toEquiv D) _ _
    (layerShape_map e.toEquiv a.shape b.shape e.shape_same D)
    _ _ (liveEnd_map M a b e out r) s t

def successor (a : Data H G Q) (out : ClosingPolicy H I₁ I₂ O₁ O₂ D)
    (K : Finset (ClosingLayer H I₁ I₂ D)) : Data K G Q where
  shape := restrictInputShape (closingLayerShape a.shape D) Subtype.val
  graph := fun s => closingLayerLabels (fun g input (_ : O₁ × O₂) => M.step g input.2.2) a.graph out D (Nat.le_refl D) s.val
  state := fun s => closingLayerLabels step a.state out D (Nat.le_refl D) s.val

/-- Restriction to corresponding components preserves the complete next
representation. K may be any subset; component preservation is proved above. -/
def successorIso (a : Data H G Q) (b : Data J G Q) (e : Iso a b)
    (out : ClosingPolicy H I₁ I₂ O₁ O₂ D)
    (K : Finset (ClosingLayer H I₁ I₂ D)) (L : Finset (ClosingLayer J I₁ I₂ D))
    (members : ∀ s, s ∈ K ↔ mapClosingLayer e.toEquiv D s ∈ L) :
    Iso (successor M step a out K) (successor M step b (policy e.toEquiv out) L) where
  toEquiv := (layerEquiv e.toEquiv D).subtypeEquiv members
  shape_same := by
    intro p h k
    exact layerShape_map e.toEquiv a.shape b.shape e.shape_same D p h.val k.val
  graph_same := by
    intro h
    exact labels_map e.toEquiv _ a.graph b.graph e.graph_same out D (Nat.le_refl D) h.val
  state_same := by
    intro h
    exact labels_map e.toEquiv step a.state b.state e.state_same out D (Nat.le_refl D) h.val

end Characterisation.ComponentGames.Representation
