/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentGames.RepresentationComponents
import DistributedSynthesis.Formalizations.ComponentGames.SimulationRuns

namespace Characterisation.ComponentGames.Representation
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks
set_option maxHeartbeats 2400000
set_option linter.unusedSectionVars false
variable {H J I₁ I₂ O₁ O₂ G Q : Type} {D : Nat}
variable [Fintype I₁] [Fintype I₂] [DecidableEq I₁] [DecidableEq I₂]
variable [Fintype O₁] [Fintype O₂] [DecidableEq O₁] [DecidableEq O₂]
variable [DecidableEq G] [DecidableEq Q]
variable (M : Recognizer Graph G) [DecidablePred (· ∈ M.accept)]
variable (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q)

noncomputable def ofHistory (P : HistoryGame.Position I₁ I₂ Q D) : Data P.Root G Q where
  shape := P.shape
  graph := fun h => M.eval (History.graphSequence h.val)
  state := P.state

theorem history_legal_iff (m : HistoryGame.Move I₁ I₂ O₁ O₂ Q D) (W : Nat) :
    HistoryGame.Legal M step (.bounded W) m.source m ↔
      (m.rule,m.replacement) ∈ legalMoves (ofHistory M m.source).shape M (ofHistory M m.source).graph
        step (ofHistory M m.source).state D W := by
  classical
  rw [legalMoves_exact]
  simp only [HistoryGame.Legal,true_and,ofHistory,HistoryGame.retained]

theorem history_liveEnd (m : HistoryGame.Move I₁ I₂ O₁ O₂ Q D) (s : m.source.End) :
    liveEnd M (ofHistory M m.source) m.rule m.replacement s = HistoryGame.extensionLive M m s := by
  classical
  unfold liveEnd ofHistory HistoryGame.extensionLive HistoryGame.retained
  rw [closingLayerLabels_recognizer M m.source.past (fun h => M.eval (History.graphSequence h.val)) (fun _ => rfl)]
  rfl

theorem history_component_iff (m : HistoryGame.Move I₁ I₂ O₁ O₂ Q D) (K : Finset m.source.End) :
    HistoryGame.IsComponent M m K ↔ ∃ anchor,
      liveEnd M (ofHistory M m.source) m.rule m.replacement anchor = true ∧ ∀ e,
        e ∈ K ↔ closingComponentMask (closingLayerShape (ofHistory M m.source).shape D)
          (liveEnd M (ofHistory M m.source) m.rule m.replacement) anchor e = true := by
  classical
  have live : liveEnd M (ofHistory M m.source) m.rule m.replacement = HistoryGame.extensionLive M m :=
    funext (history_liveEnd M m)
  rw [live]
  rfl

/-- No finite-state realization assumption: the source and successor are
the original actual-history positions of BoundedComponent. -/
noncomputable def historySuccessorIso (m : HistoryGame.Move I₁ I₂ O₁ O₂ Q D)
    (P : HistoryGame.Position I₁ I₂ Q D) (K : Finset m.source.End)
    (histories : P.histories = K.image m.source.history)
    (states : ∀ (h : P.Root) (e : m.source.End), e ∈ K → h.val = m.source.history e →
      P.state h = closingLayerLabels step m.source.state m.rule D (Nat.le_refl D) e) :
    Iso (successor M step (ofHistory M m.source) m.rule K) (ofHistory M P) := by
  classical
  let f : K → P.Root := fun e => ⟨m.source.history e.val,by
    change m.source.history e.val ∈ P.histories
    rw [histories]
    exact Finset.mem_image.mpr ⟨e.val,e.property,rfl⟩⟩
  have bijective : Function.Bijective f := by
    constructor
    · intro e d eq
      exact Subtype.ext (m.source.history_injective (congrArg Subtype.val eq))
    · intro h
      have inside := h.property
      change h.val ∈ P.histories at inside
      rw [histories] at inside
      obtain ⟨e,mem,eq⟩ := Finset.mem_image.mp inside
      exact ⟨⟨e,mem⟩,Subtype.ext eq⟩
  refine {toEquiv := Equiv.ofBijective f bijective,shape_same := ?_,graph_same := ?_,state_same := ?_}
  · intro p h k
    apply Bool.eq_iff_iff.mpr
    change extractInputShape P.past p (f h) (f k) = true ↔ _
    rw [extractInputShape_exact]
    exact (closingLayerShape_exact m.source.past m.source.shape (extractInputShape_exact _) D p h.val k.val).symm
  · intro h
    exact (closingLayerLabels_recognizer M m.source.past (fun h => M.eval (History.graphSequence h.val))
      (fun _ => rfl) m.rule D (Nat.le_refl D) h.val).symm
  · intro h
    exact states (f h) h.val h.property rfl

def stateAt (a : Data H G Q) (out : ClosingPolicy H I₁ I₂ O₁ O₂ D) (h : H)
    (w : BlockWord (RoundRecord I₁ I₂ Graph Unit Unit) D) (t : Nat) : Q :=
  let u : BlockWord (RoundRecord I₁ I₂ Graph Unit Unit) (min t D) := ⟨w.val.take t,by simp [w.property]⟩
  closingLayerLabels step a.state out (min t D) (Nat.min_le_right _ _) (wordScenario h u)

theorem stateAt_map (a : Data H G Q) (b : Data J G Q) (e : Iso a b)
    (out : ClosingPolicy H I₁ I₂ O₁ O₂ D) (h : H)
    (w : BlockWord (RoundRecord I₁ I₂ Graph Unit Unit) D) (t : Nat) :
    stateAt step b (policy e.toEquiv out) (e.toEquiv h) w t = stateAt step a out h w t := by
  dsimp only [stateAt]
  rw [← HistoryGame.mapClosingLayer_wordScenario e.toEquiv h (min t D),labels_map e.toEquiv step a.state b.state e.state_same]

theorem phaseMinimum_map (χ : Q → Nat) (a : Data H G Q) (b : Data J G Q) (e : Iso a b)
    (out : ClosingPolicy H I₁ I₂ O₁ O₂ D) (h : H)
    (w : BlockWord (RoundRecord I₁ I₂ Graph Unit Unit) D) :
    rangeMin (fun t => χ (stateAt step b (policy e.toEquiv out) (e.toEquiv h) w t)) 0 (D-1) =
      rangeMin (fun t => χ (stateAt step a out h w t)) 0 (D-1) := by
  simp only [stateAt_map]

end Characterisation.ComponentGames.Representation
