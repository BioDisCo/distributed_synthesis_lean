/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentGames.ExecutableHistories
import DistributedSynthesis.Formalizations.ComponentGames.ComponentReadback
import Mathlib.Data.Fintype.Inv

namespace Characterisation.ComponentGames.ExecutableHistories
open scoped DistributedSynthesis.FiniteOrders Characterisation.ComponentGames.FiniteEnumeration Characterisation.ComponentGames.Representation.FiniteArena
open scoped DistributedSynthesis.DecidableViews
open scoped Characterisation.ComponentGames.Representation
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks
set_option maxHeartbeats 2400000
set_option linter.unusedSectionVars false
variable {I₁ I₂ O₁ O₂ G Q : Type} {D : Nat}
variable [Fintype I₁] [Fintype I₂] [DecidableEq I₁] [DecidableEq I₂]
variable [DecidableEq Q]
variable (M : Recognizer Graph G) [DecidablePred (· ∈ M.accept)]
variable (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q)

def preimage (m : HistoryGame.Move I₁ I₂ O₁ O₂ Q D) (K : Finset m.source.End)
    (h : K.image m.source.history) : m.source.End :=
  Fintype.choose (fun e : m.source.End => m.source.history e = h.val) (by
    obtain ⟨e,_,eq⟩ := Finset.mem_image.mp h.property
    exact ⟨e,eq,fun s same => m.source.history_injective (same.trans eq.symm)⟩)

theorem preimage_spec (m : HistoryGame.Move I₁ I₂ O₁ O₂ Q D) (K : Finset m.source.End)
    (h : K.image m.source.history) : m.source.history (preimage m K h) = h.val := by
  unfold preimage
  exact Fintype.choose_spec (fun e : m.source.End => m.source.history e = h.val) _

theorem preimage_mem (m : HistoryGame.Move I₁ I₂ O₁ O₂ Q D) (K : Finset m.source.End)
    (h : K.image m.source.history) : preimage m K h ∈ K := by
  obtain ⟨e,inside,eq⟩ := Finset.mem_image.mp h.property
  have same := m.source.history_injective ((preimage_spec m K h).trans eq.symm)
  exact same.symm ▸ inside

theorem component_nonempty (m : HistoryGame.Move I₁ I₂ O₁ O₂ Q D) (K : Finset m.source.End)
    (component : HistoryGame.IsComponent M m K) : K.Nonempty := by
  obtain ⟨a,alive,members⟩ := component
  exact ⟨a,(members a).mpr (by simp [closingComponentMask,alive])⟩

def componentPosition (m : HistoryGame.Move I₁ I₂ O₁ O₂ Q D) (K : Finset m.source.End)
    (component : HistoryGame.IsComponent M m K) : HistoryGame.Position I₁ I₂ Q D where
  phase := m.source.phase+1
  histories := K.image m.source.history
  nonempty := (component_nonempty M m K component).image _
  lengths := by
    intro h mem
    obtain ⟨e,_,rfl⟩ := Finset.mem_image.mp mem
    exact m.source.history_length e
  state := fun h => closingLayerLabels step m.source.state m.rule D (Nat.le_refl D) (preimage m K h)

theorem componentPosition_states (m : HistoryGame.Move I₁ I₂ O₁ O₂ Q D) (K : Finset m.source.End)
    (component : HistoryGame.IsComponent M m K)
    (h : (componentPosition M step m K component).Root) (e : m.source.End) (_mem : e ∈ K)
    (eq : h.val = m.source.history e) :
    (componentPosition M step m K component).state h = closingLayerLabels step m.source.state m.rule D (Nat.le_refl D) e := by
  have same := m.source.history_injective ((preimage_spec m K h).trans eq)
  change closingLayerLabels step m.source.state m.rule D _ (preimage m K h) = _
  rw [same]

theorem componentPosition_next (m : HistoryGame.Move I₁ I₂ O₁ O₂ Q D) (K : Finset m.source.End)
    (component : HistoryGame.IsComponent M m K) :
    HistoryGame.Next M step m (componentPosition M step m K component) :=
  ⟨rfl,K,component,rfl,componentPosition_states M step m K component⟩

theorem components_eq_of_common (m : HistoryGame.Move I₁ I₂ O₁ O₂ Q D) (K L : Finset m.source.End)
    (first : HistoryGame.IsComponent M m K) (second : HistoryGame.IsComponent M m L)
    (s : m.source.End) (left : s ∈ K) (right : s ∈ L) : K = L := by
  obtain ⟨a,_,membersA⟩ := first
  obtain ⟨b,_,membersB⟩ := second
  have reachA := (membersA s).mp left
  have reachB := (membersB s).mp right
  simp only [closingComponentMask,Bool.and_eq_true,decide_eq_true_eq] at reachA reachB
  have path := reachA.2.trans reachB.2.symm
  have reachable (t : m.source.End) :
      (closingObservationGraph (closingLayerShape m.source.shape D) (HistoryGame.extensionLive M m)).Reachable a t ↔
      (closingObservationGraph (closingLayerShape m.source.shape D) (HistoryGame.extensionLive M m)).Reachable b t :=
    ⟨fun h => path.symm.trans h,fun h => path.trans h⟩
  apply Finset.ext
  intro t
  rw [membersA,membersB]
  simp only [closingComponentMask,Bool.and_eq_true,decide_eq_true_eq,reachable]

variable {P : HistoryGame.Position I₁ I₂ Q D}
variable (m : HistoryGame.Move I₁ I₂ O₁ O₂ Q D) (sim : HistoryGame.Simulation M P m.source)
variable (legal : HistoryGame.Legal M step .replacement m.source m)

def mappedComponent (K : Finset P.End) (component : HistoryGame.IsComponent M (HistoryGame.pullMove M m sim) K) :
    {L : Finset m.source.End // HistoryGame.IsComponent M m L ∧ ∀ e ∈ K, HistoryGame.simulationEnd M m sim e ∈ L} := by
  letI : Fintype P.End := inferInstance
  letI : Fintype m.source.End := inferInstance
  exact Fintype.chooseX (fun L : Finset m.source.End => HistoryGame.IsComponent M m L ∧
    ∀ e ∈ K, HistoryGame.simulationEnd M m sim e ∈ L) (by
      obtain ⟨L,comp,mapped⟩ := HistoryGame.simulation_component M step m sim legal K component
      obtain ⟨a,inside⟩ := component_nonempty M (HistoryGame.pullMove M m sim) K component
      exact ⟨L,⟨comp,mapped⟩,fun J h => components_eq_of_common M m J L h.1 comp
        (HistoryGame.simulationEnd M m sim a) (h.2 a inside) (mapped a inside)⟩)

end Characterisation.ComponentGames.ExecutableHistories
