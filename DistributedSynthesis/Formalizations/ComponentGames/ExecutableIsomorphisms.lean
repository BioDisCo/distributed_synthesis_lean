/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentGames.ExecutableHistories
import DistributedSynthesis.Formalizations.ComponentGames.RepresentationLift
import Mathlib.Data.Fintype.Inv

namespace Characterisation.ComponentGames.ExecutableHistories
open scoped DistributedSynthesis.FiniteOrders Characterisation.ComponentGames.FiniteEnumeration Characterisation.ComponentGames.Representation.FiniteArena
open scoped DistributedSynthesis.DecidableViews
open scoped Characterisation.ComponentGames.Representation
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks Representation
set_option maxHeartbeats 2400000
set_option linter.unusedSectionVars false
variable {I₁ I₂ O₁ O₂ G Q : Type} {D B : Nat}
variable [Fintype I₁] [Fintype I₂] [LinearOrder I₁] [LinearOrder I₂]
variable [Fintype O₁] [Fintype O₂] [DecidableEq O₁] [DecidableEq O₂]
variable [DecidableEq G] [DecidableEq Q]
variable (M : Recognizer Graph G) [DecidablePred (· ∈ M.accept)]
variable (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q)

def finiteEquiv {X Y : Type} [Fintype X] [DecidableEq Y] (f : X → Y) (bijective : Function.Bijective f) : X ≃ Y where
  toFun := f
  invFun := Fintype.bijInv bijective
  left_inv := Fintype.leftInverse_bijInv bijective
  right_inv := Fintype.rightInverse_bijInv bijective

theorem finiteEquiv_eq {X Y : Type} [Fintype X] [DecidableEq Y] (f : X → Y) (bijective : Function.Bijective f) :
    finiteEquiv f bijective = Equiv.ofBijective f bijective := Equiv.ext (fun _ => rfl)

theorem iso_ext {H J : Type} {a : Data H G Q} {b : Data J G Q} (e f : Iso a b)
    (eq : e.toEquiv = f.toEquiv) : e = f := by
  cases e
  cases f
  cases eq
  rfl

/-- Inverting the successor history map is a unique finite search. -/
def historyIso (m : HistoryGame.Move I₁ I₂ O₁ O₂ Q D)
    (P : HistoryGame.Position I₁ I₂ Q D) (K : Finset m.source.End)
    (histories : P.histories = K.image m.source.history)
    (states : ∀ (h : P.Root) (e : m.source.End), e ∈ K → h.val = m.source.history e →
      P.state h = closingLayerLabels step m.source.state m.rule D (Nat.le_refl D) e) :
    Iso (successor M step (ofHistory M m.source) m.rule K) (ofHistory M P) := by
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
  refine {toEquiv := finiteEquiv f bijective,shape_same := ?_,graph_same := ?_,state_same := ?_}
  · exact (historySuccessorIso M step m P K histories states).shape_same
  · exact (historySuccessorIso M step m P K histories states).graph_same
  · exact (historySuccessorIso M step m P K histories states).state_same

theorem historyIso_eq (m : HistoryGame.Move I₁ I₂ O₁ O₂ Q D)
    (P : HistoryGame.Position I₁ I₂ Q D) (K : Finset m.source.End)
    (histories : P.histories = K.image m.source.history)
    (states : ∀ (h : P.Root) (e : m.source.End), e ∈ K → h.val = m.source.history e →
      P.state h = closingLayerLabels step m.source.state m.rule D (Nat.le_refl D) e) :
    historyIso M step m P K histories states = historySuccessorIso M step m P K histories states := by
  apply iso_ext
  apply Equiv.ext
  intro h
  rfl

def reached (m : HistoryGame.Move I₁ I₂ O₁ O₂ Q D) (A : Position G Q B)
    (e : Iso (ofHistory M m.source) A.2) (P : HistoryGame.Position I₁ I₂ Q D)
    (K : Finset m.source.End) (L : Finset (ClosingLayer A.Root I₁ I₂ D))
    (members : ∀ s, s ∈ K ↔ mapClosingLayer e.toEquiv D s ∈ L)
    (histories : P.histories = K.image m.source.history)
    (states : ∀ (h : P.Root) (s : m.source.End), s ∈ K → h.val = m.source.history s →
      P.state h = closingLayerLabels step m.source.state m.rule D (Nat.le_refl D) s)
    (bound : L.card ≤ B) :
    Iso (ofHistory M P) (FiniteArena.nextPosition M step ⟨pushMove M m A e,L⟩ bound).2 := by
  let mapped := ((historyIso M step m P K histories states).toEquiv.symm.trans
    ((layerEquiv e.toEquiv D).subtypeEquiv members)).trans (numberSubset L)
  have same : mapped = (reachedIso M step m A e P K L members histories states bound).toEquiv := by
    dsimp only [mapped]
    rw [historyIso_eq]
    rfl
  refine {toEquiv := mapped,shape_same := ?_,graph_same := ?_,state_same := ?_}
  · rw [same]
    exact (reachedIso M step m A e P K L members histories states bound).shape_same
  · rw [same]
    exact (reachedIso M step m A e P K L members histories states bound).graph_same
  · rw [same]
    exact (reachedIso M step m A e P K L members histories states bound).state_same

theorem reached_eq (m : HistoryGame.Move I₁ I₂ O₁ O₂ Q D) (A : Position G Q B)
    (e : Iso (ofHistory M m.source) A.2) (P : HistoryGame.Position I₁ I₂ Q D)
    (K : Finset m.source.End) (L : Finset (ClosingLayer A.Root I₁ I₂ D))
    (members : ∀ s, s ∈ K ↔ mapClosingLayer e.toEquiv D s ∈ L)
    (histories : P.histories = K.image m.source.history)
    (states : ∀ (h : P.Root) (s : m.source.End), s ∈ K → h.val = m.source.history s →
      P.state h = closingLayerLabels step m.source.state m.rule D (Nat.le_refl D) s)
    (bound : L.card ≤ B) : reached M step m A e P K L members histories states bound =
      reachedIso M step m A e P K L members histories states bound := by
  apply iso_ext
  change ((historyIso M step m P K histories states).toEquiv.symm.trans
    ((layerEquiv e.toEquiv D).subtypeEquiv members)).trans (numberSubset L) = _
  rw [historyIso_eq]
  rfl

end Characterisation.ComponentGames.ExecutableHistories
