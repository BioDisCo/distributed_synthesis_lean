/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentGames.FiniteTransitions

namespace Characterisation.ComponentGames.Representation
open scoped Characterisation.ComponentGames.Representation
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks
set_option maxHeartbeats 2400000
set_option linter.unusedSectionVars false
variable {H J I₁ I₂ O₁ O₂ G Q : Type} {D B : Nat}
variable [Fintype H] [DecidableEq H] [Fintype J] [DecidableEq J]
variable [Fintype I₁] [Fintype I₂] [LinearOrder I₁] [LinearOrder I₂]
variable [Fintype O₁] [Fintype O₂] [DecidableEq O₁] [DecidableEq O₂]
variable [DecidableEq G] [DecidableEq Q]
variable (M : Recognizer Graph G) [DecidablePred (· ∈ M.accept)]
variable (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q)

def componentImage (e : H ≃ J) (K : Finset (ClosingLayer H I₁ I₂ D)) : Finset (ClosingLayer J I₁ I₂ D) :=
  K.image (mapClosingLayer e D)

theorem componentImage_members (e : H ≃ J) (K : Finset (ClosingLayer H I₁ I₂ D))
    (s : ClosingLayer H I₁ I₂ D) : s ∈ K ↔ mapClosingLayer e D s ∈ componentImage e K := by
  constructor
  · intro mem; exact Finset.mem_image.mpr ⟨s,mem,rfl⟩
  · intro mem
    obtain ⟨t,inside,eq⟩ := Finset.mem_image.mp mem
    have same : t = s := (layerEquiv e D).injective eq
    exact same ▸ inside

theorem componentImage_card (e : H ≃ J) (K : Finset (ClosingLayer H I₁ I₂ D)) :
    (componentImage e K).card = K.card := Finset.card_image_of_injective K (layerEquiv e D).injective

def pushMove (m : HistoryGame.Move I₁ I₂ O₁ O₂ Q D) (A : Position G Q B)
    (e : Iso (ofHistory M m.source) A.2) : FiniteArena.Move I₁ I₂ O₁ O₂ G Q D B :=
  ⟨A,policy e.toEquiv m.rule,replacement e.toEquiv m.replacement⟩

theorem pushMove_legal (m : HistoryGame.Move I₁ I₂ O₁ O₂ Q D) (A : Position G Q B)
    (e : Iso (ofHistory M m.source) A.2) (W : Nat)
    (legal : HistoryGame.Legal M step (.bounded W) m.source m) :
    ((pushMove M m A e).rule,(pushMove M m A e).replacement) ∈
      legalMoves A.2.shape M A.2.graph step A.2.state D W := by
  classical
  exact (legalMoveEquiv (ofHistory M m.source) A.2 e M step D W
    ⟨(m.rule,m.replacement),(history_legal_iff M step m W).mp legal⟩).property

theorem pushMove_component (m : HistoryGame.Move I₁ I₂ O₁ O₂ Q D) (A : Position G Q B)
    (e : Iso (ofHistory M m.source) A.2) (K : Finset m.source.End) :
    Components M A.2 (pushMove M m A e).rule (pushMove M m A e).replacement (componentImage e.toEquiv K) ↔
      HistoryGame.IsComponent M m K := by
  classical
  exact (components_map M (ofHistory M m.source) A.2 e m.rule m.replacement K
    (componentImage e.toEquiv K) (componentImage_members e.toEquiv K)).trans (history_component_iff M m K).symm

/-- The exact isomorphism for a reached successor, including its fixed
component numbering. Its root map is used below to transfer persistent runs. -/
noncomputable def reachedIso (m : HistoryGame.Move I₁ I₂ O₁ O₂ Q D) (A : Position G Q B)
    (e : Iso (ofHistory M m.source) A.2) (P : HistoryGame.Position I₁ I₂ Q D)
    (K : Finset m.source.End) (L : Finset (ClosingLayer A.Root I₁ I₂ D))
    (members : ∀ s, s ∈ K ↔ mapClosingLayer e.toEquiv D s ∈ L)
    (histories : P.histories = K.image m.source.history)
    (states : ∀ (h : P.Root) (s : m.source.End), s ∈ K → h.val = m.source.history s →
      P.state h = closingLayerLabels step m.source.state m.rule D (Nat.le_refl D) s)
    (bound : L.card ≤ B) :
    Iso (ofHistory M P) (FiniteArena.nextPosition M step ⟨pushMove M m A e,L⟩ bound).2 :=
  ((historySuccessorIso M step m P K histories states).symm.trans
    (successorIso M step (ofHistory M m.source) A.2 e m.rule K L members)).trans
    (packIso L bound (successor M step A.2 (policy e.toEquiv m.rule) L))

theorem reachedIso_trace (m : HistoryGame.Move I₁ I₂ O₁ O₂ Q D) (A : Position G Q B)
    (e : Iso (ofHistory M m.source) A.2) (P : HistoryGame.Position I₁ I₂ Q D)
    (K : Finset m.source.End) (L : Finset (ClosingLayer A.Root I₁ I₂ D))
    (members : ∀ s, s ∈ K ↔ mapClosingLayer e.toEquiv D s ∈ L)
    (histories : P.histories = K.image m.source.history)
    (states : ∀ (h : P.Root) (s : m.source.End), s ∈ K → h.val = m.source.history s →
      P.state h = closingLayerLabels step m.source.state m.rule D (Nat.le_refl D) s)
    (bound : L.card ≤ B) (s : K) (h : P.Root) (eq : h.val = m.source.history s.val) :
    (reachedIso M step m A e P K L members histories states bound).toEquiv h =
      numberSubset L ⟨mapClosingLayer e.toEquiv D s.val,(members s.val).mp s.property⟩ := by
  classical
  have hEq : h = (historySuccessorIso M step m P K histories states).toEquiv s := Subtype.ext eq
  rw [hEq]
  change numberSubset L ((successorIso M step (ofHistory M m.source) A.2 e m.rule K L members).toEquiv
    ((historySuccessorIso M step m P K histories states).toEquiv.symm
      ((historySuccessorIso M step m P K histories states).toEquiv s))) = _
  rw [Equiv.symm_apply_apply]
  rfl

theorem reachedIso_backtrace (m : HistoryGame.Move I₁ I₂ O₁ O₂ Q D) (A : Position G Q B)
    (e : Iso (ofHistory M m.source) A.2) (P : HistoryGame.Position I₁ I₂ Q D)
    (K : Finset m.source.End) (L : Finset (ClosingLayer A.Root I₁ I₂ D))
    (members : ∀ s, s ∈ K ↔ mapClosingLayer e.toEquiv D s ∈ L)
    (histories : P.histories = K.image m.source.history)
    (states : ∀ (h : P.Root) (s : m.source.End), s ∈ K → h.val = m.source.history s →
      P.state h = closingLayerLabels step m.source.state m.rule D (Nat.le_refl D) s)
    (bound : L.card ≤ B) (s : L) (h : P.Root) (a : m.source.Root) (w : FiniteArena.Word I₁ I₂ D)
    (endpoint : s.val = wordScenario ((pushMove M m A e).replacement (e.toEquiv a)) w)
    (eq : (reachedIso M step m A e P K L members histories states bound).toEquiv h = numberSubset L s) :
    h.val = (m.replacement a).val ++ w.val := by
  classical
  let t : m.source.End := wordScenario (m.replacement a) w
  have mapped : mapClosingLayer e.toEquiv D t = s.val := by
    exact (HistoryGame.mapClosingLayer_wordScenario e.toEquiv (m.replacement a) D w).trans
      ((congrArg (fun root => wordScenario root w) (replacement_apply e.toEquiv m.replacement a).symm).trans endpoint.symm)
  have inside : t ∈ K := (members t).mpr (mapped.symm ▸ s.property)
  let old : P.Root := ⟨m.source.history t,by
    change m.source.history t ∈ P.histories
    rw [histories]
    exact Finset.mem_image.mpr ⟨t,inside,rfl⟩⟩
  have numbered := reachedIso_trace M step m A e P K L members histories states bound ⟨t,inside⟩ old rfl
  have same : h = old := by
    apply (reachedIso M step m A e P K L members histories states bound).toEquiv.injective
    rw [eq,numbered]
    exact congrArg (numberSubset L) (Subtype.ext mapped.symm)
  rw [same]
  exact wordScenario_history m.source.past (m.replacement a) w

end Characterisation.ComponentGames.Representation
