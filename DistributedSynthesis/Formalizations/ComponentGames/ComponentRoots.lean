/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentGames.HistoryGames
import DistributedSynthesis.Formalizations.ComponentGames.CommonView

namespace Characterisation.ComponentGames.HistoryGame
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks
noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 100000

variable {I₁ I₂ O₁ O₂ G Q : Type} {D : Nat}
variable [Fintype I₁] [Fintype I₂] [DecidableEq I₁] [DecidableEq I₂]
variable (M : Recognizer Graph G) [DecidablePred (· ∈ M.accept)]

-- The selected component may cover only a subset of all live histories.
-- Only the soundness direction of connectivity is needed; no false
-- assumption that retained histories cover the whole global component.
theorem component_input_connected (m : Move I₁ I₂ O₁ O₂ Q D)
    (K : Finset m.source.End) (component : IsComponent M m K)
    (e f : m.source.End) (he : e ∈ K) (hf : f ∈ K) :
    InputConnected (fun g => M.eval g ∈ M.accept)
      (m.source.history e) (m.source.history f) := by
  obtain ⟨a,_,mask⟩ := component
  have ee := (mask e).mp he
  have ff := (mask f).mp hf
  simp only [closingComponentMask,Bool.and_eq_true,decide_eq_true_eq] at ee ff
  let graph := closingObservationGraph (closingLayerShape m.source.shape D) (extensionLive M m)
  have reach : graph.Reachable e f := ee.2.symm.trans ff.2
  have path := (graph.reachable_iff_reflTransGen e f).mp reach
  apply Relation.ReflTransGen.lift m.source.history _ path
  intro s t edge
  have exactShape := closingLayerShape_exact m.source.past m.source.shape
    (extractInputShape_exact m.source.past) D
  refine ⟨(of_decide_eq_true edge.2.1).2,(of_decide_eq_true edge.2.2.1).2,?_⟩
  obtain ⟨p,eq | eq⟩ := edge.2.2.2
  · cases p
    · exact Or.inl ((exactShape .one s t).mp eq)
    · exact Or.inr ((exactShape .two s t).mp eq)
  · cases p
    · exact Or.inl ((exactShape .one t s).mp eq).symm
    · exact Or.inr ((exactShape .two t s).mp eq).symm

theorem component_common_roots
    (holes : ∀ h, ∃ u : List Graph, u.length = D ∧ M.eval (h ++ u) ∉ M.accept)
    (m : Move I₁ I₂ O₁ O₂ Q D) (K : Finset m.source.End)
    (component : IsComponent M m K) :
    ∃ p, ∀ (e f : m.source.End), e ∈ K → f ∈ K →
      currentView p (closingLayerRoot D e).val =
        currentView p (closingLayerRoot D f).val := by
  obtain ⟨anchor,alive,mask⟩ := component
  have ha : anchor ∈ K := (mask anchor).mpr (by
    simp only [closingComponentMask,alive,Bool.true_and,decide_eq_true_eq]
    exact SimpleGraph.Reachable.refl anchor)
  have live := (of_decide_eq_true alive).2
  obtain ⟨p,shared⟩ := exact_holes_common_view (fun g => M.eval g ∈ M.accept) D holes
    (m.source.history anchor) (by rw [m.source.history_length,Nat.add_mul,one_mul]; omega) live
  have lagged (e : K) : lagView D (currentView p (m.source.history anchor)) =
      lagView D (currentView p (m.source.history e.val)) :=
    shared _ (component_input_connected M m K ⟨anchor,alive,mask⟩ anchor e.val ha e.property)
  have common : ∀ e f : K,
      currentView p (closingLayerRoot D e.val).val =
        currentView p (closingLayerRoot D f.val).val := by
    apply common_roots_of_common_lag
      (fun e : K => (closingLayerRoot D e.val).val)
      (fun e : K => (scenarioWord D e.val).val) D
      (fun e => (scenarioWord D e.val).property) p
    intro e f
    have eq := (lagged e).symm.trans (lagged f)
    simpa only [Position.history,scenarioWord_history,Position.past] using eq
  exact ⟨p,fun e f he hf => common ⟨e,he⟩ ⟨f,hf⟩⟩

def participatingRoots (m : Move I₁ I₂ O₁ O₂ Q D) (K : Finset m.source.End) :
    Finset m.source.Root := K.image (closingLayerRoot D)

theorem participating_roots_common
    (holes : ∀ h, ∃ u : List Graph, u.length = D ∧ M.eval (h ++ u) ∉ M.accept)
    (m : Move I₁ I₂ O₁ O₂ Q D) (K : Finset m.source.End)
    (component : IsComponent M m K) :
    ∃ p, ∀ (i j : participatingRoots m K), currentView p i.val.val = currentView p j.val.val := by
  obtain ⟨p,common⟩ := component_common_roots M holes m K component
  refine ⟨p,?_⟩
  intro i j
  obtain ⟨e,he,eqe⟩ := Finset.mem_image.mp i.property
  obtain ⟨f,hf,eqf⟩ := Finset.mem_image.mp j.property
  rw [← eqe,← eqf]
  exact common e f he hf

end
end Characterisation.ComponentGames.HistoryGame
