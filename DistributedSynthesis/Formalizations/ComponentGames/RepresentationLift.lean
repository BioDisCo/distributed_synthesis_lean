/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentGames.RepresentationSteps
import DistributedSynthesis.Formalizations.ComponentGames.SupportedInterpreter

namespace Characterisation.ComponentGames.Representation
open scoped Characterisation.ComponentGames.Representation
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks
noncomputable section
set_option maxHeartbeats 2400000
set_option linter.unusedSectionVars false
variable {I₁ I₂ O₁ O₂ G Q : Type} {D B : Nat}
variable [Fintype I₁] [Fintype I₂] [LinearOrder I₁] [LinearOrder I₂]
variable [Fintype O₁] [Fintype O₂] [DecidableEq O₁] [DecidableEq O₂]
variable [DecidableEq G] [DecidableEq Q]
variable (M : Recognizer Graph G) [DecidablePred (· ∈ M.accept)]
variable (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q)

/-- Retain the chosen component in the conclusion, rather than just the
existence of some environment successor. -/
def componentPosition (m : HistoryGame.Move I₁ I₂ O₁ O₂ Q D) (K : Finset m.source.End)
    (component : HistoryGame.IsComponent M m K) : HistoryGame.Position I₁ I₂ Q D := by
  have nonempty := component_nonempty M (ofHistory M m.source) m.rule m.replacement K
    ((history_component_iff M m K).mp component)
  let pick (h : K.image m.source.history) := (Finset.mem_image.mp h.property).choose
  refine {phase := m.source.phase+1, histories := K.image m.source.history
          nonempty := nonempty.image _, lengths := ?_
          state := fun h => closingLayerLabels step m.source.state m.rule D (Nat.le_refl D) (pick h)}
  intro h mem
  obtain ⟨s,_,rfl⟩ := Finset.mem_image.mp mem
  exact m.source.history_length s

theorem componentPosition_histories (m : HistoryGame.Move I₁ I₂ O₁ O₂ Q D) (K : Finset m.source.End)
    (component : HistoryGame.IsComponent M m K) :
    (componentPosition M step m K component).histories = K.image m.source.history := rfl

theorem componentPosition_states (m : HistoryGame.Move I₁ I₂ O₁ O₂ Q D) (K : Finset m.source.End)
    (component : HistoryGame.IsComponent M m K)
    (h : (componentPosition M step m K component).Root) (s : m.source.End) (_mem : s ∈ K)
    (eq : h.val = m.source.history s) :
    (componentPosition M step m K component).state h =
      closingLayerLabels step m.source.state m.rule D (Nat.le_refl D) s := by
  have chosen := (Finset.mem_image.mp h.property).choose_spec.2
  have same := m.source.history_injective (chosen.trans eq)
  change closingLayerLabels step m.source.state m.rule D _ ((Finset.mem_image.mp h.property).choose) = _
  rw [same]

theorem componentPosition_next (m : HistoryGame.Move I₁ I₂ O₁ O₂ Q D) (K : Finset m.source.End)
    (component : HistoryGame.IsComponent M m K) :
    HistoryGame.Next M step m (componentPosition M step m K component) :=
  ⟨rfl,K,component,rfl,componentPosition_states M step m K component⟩

def pullMove (m : FiniteArena.Move I₁ I₂ O₁ O₂ G Q D B) (P : HistoryGame.Position I₁ I₂ Q D)
    (e : Iso (ofHistory M P) m.source.2) : HistoryGame.Move I₁ I₂ O₁ O₂ Q D :=
  ⟨P,policy e.toEquiv.symm m.rule,replacement e.toEquiv.symm m.replacement⟩

theorem pullMove_legal (m : FiniteArena.Move I₁ I₂ O₁ O₂ G Q D B) (P : HistoryGame.Position I₁ I₂ Q D)
    (e : Iso (ofHistory M P) m.source.2) (W : Nat)
    (legal : (m.rule,m.replacement) ∈ legalMoves m.source.2.shape M m.source.2.graph step m.source.2.state D W) :
    HistoryGame.Legal M step (.bounded W) P (pullMove M m P e) := by
  apply (history_legal_iff M step (pullMove M m P e) W).mpr
  exact (legalMoveEquiv m.source.2 (ofHistory M P) e.symm M step D W ⟨(m.rule,m.replacement),legal⟩).property

theorem push_pull (m : FiniteArena.Move I₁ I₂ O₁ O₂ G Q D B) (P : HistoryGame.Position I₁ I₂ Q D)
    (e : Iso (ofHistory M P) m.source.2) : pushMove M (pullMove M m P e) m.source e = m := by
  rcases m with ⟨A,out,r⟩
  change (⟨A,policy e.toEquiv (policy e.toEquiv.symm out),replacement e.toEquiv (replacement e.toEquiv.symm r)⟩ : FiniteArena.Move I₁ I₂ O₁ O₂ G Q D B) = ⟨A,out,r⟩
  have pol := policy_inverse e.toEquiv.symm out
  have rep := replacement_inverse e.toEquiv.symm r
  simp only [Equiv.symm_symm] at pol rep
  rw [pol,rep]

def initialIso (q₀ : Q) (positive : 0 < B) :
    Iso (ofHistory (I₁:=I₁) (I₂:=I₂) (D:=D) M (HistoryGame.Position.initial q₀))
      (FiniteArena.initial M q₀ positive).2 := by
  classical
  let P := HistoryGame.Position.initial (I₁:=I₁) (I₂:=I₂) (D:=D) q₀
  have empty (h : P.Root) : h.val = [] := Finset.mem_singleton.mp h.property
  let e : P.Root ≃ Fin 1 :=
    {toFun := fun _ => 0, invFun := fun _ => ⟨[],Finset.mem_singleton_self _⟩
     left_inv := fun h => Subtype.ext (empty h).symm
     right_inv := fun h => Subsingleton.elim _ _}
  refine {toEquiv := e,shape_same := ?_,graph_same := ?_,state_same := ?_}
  · intro p h k
    change true = decide (currentView p h.val = currentView p k.val)
    rw [empty h,empty k]
    simp
  · intro h
    change M.start = M.eval (History.graphSequence h.val)
    rw [empty h]
    rfl
  · intro h; rfl

variable {H J : Type}
def Iso.castTarget {a : Data H G Q} {b c : Data J G Q} (e : Iso a b) (eq : b = c) : Iso a c := eq ▸ e

def Iso.castSource {a b : Data H G Q} {c : Data J G Q} (e : Iso a c) (eq : a = b) : Iso b c := eq ▸ e

end
end Characterisation.ComponentGames.Representation
