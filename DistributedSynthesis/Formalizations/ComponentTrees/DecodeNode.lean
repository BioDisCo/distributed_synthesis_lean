/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentTrees.DecodeChild
import DistributedSynthesis.Formalizations.ComponentGames.ExecutableIsomorphisms

/-! Reconstruct one entire concrete child from its finite numbering.
The map is a finite bijection preserving all vertices and block states.
-/
namespace Characterisation.ComponentTrees.FiniteDecode
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks
open Characterisation.ComponentTrees.FiniteTransport
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
variable {bound : Nat}
variable (P : Position I₁ I₂ B.State D) (valid : PositionValid B M P)
variable (a : {raw : FiniteAlphabet.Raw (capacity:=capacity) B // FiniteAlphabet.Legal B live bound raw})
variable (e : Representation.Iso (FinitePositions.historyData P) a.val.1.source.2)


def node : CompressedNode B M bound :=
  FiniteTransport.pullNode B M P valid (a.val.1) e (a.property.2.2.1) a.property.2.2.2.1

theorem node_next (Q : Position I₁ I₂ B.State D) :
    (node B M live P valid a e).Successor Q ↔
      ComponentSuccessor B M (FullExtensions.full B P
        (pullReduction B P a.val.1 e a.property.2.2.1) (pullRule B P a.val.1 e)) Q :=
  FullExtensions.node_successor_iff B M P _ _ valid
    (pullChecks B P a.val.1 e a.property.2.2.1).2.2.2
    (pullRule_coherent B P a.val.1 e a.property.2.2.2.1) Q

def child (d : Fin capacity) (c : FiniteAlphabet.Child B (a.val.1)) (entry : a.val.2 d = some c) :
    Position I₁ I₂ B.State D :=
  childPosition B M live liveCorrect P valid (a.val.1) e (a.property.2.2.1) c (a.property.2.2.2.2.1 d c entry)

theorem child_next (d : Fin capacity) (c : FiniteAlphabet.Child B (a.val.1)) (entry : a.val.2 d = some c) :
    (node B M live P valid a e).Successor (child B M live liveCorrect P valid a e d c entry) := by
  apply (node_next B M live P valid a e _).mpr
  exact childPosition_next B M live liveCorrect P valid (a.val.1) e (a.property.2.2.1) c _

include liveCorrect valid in
theorem child_complete (Q : Position I₁ I₂ B.State D)
    (next : (node B M live P valid a e).Successor Q) :
    ∃ d c, ∃ (entry : a.val.2 d = some c), child B M live liveCorrect P valid a e d c entry = Q := by
  have next' := (node_next B M live P valid a e Q).mp next
  obtain ⟨K,component,phase,histories,states⟩ := next'
  have mapped := component_map B M live liveCorrect P valid (pullReduction B P (a.val.1) e (a.property.2.2.1)) (pullRule B P (a.val.1) e) (a.val.1).source e K component
  change FiniteAlphabet.Component B live
    ⟨(a.val.1).source,Representation.policy e.toEquiv (Representation.policy e.toEquiv.symm (a.val.1).rule),
      Representation.replacement e.toEquiv (Representation.replacement e.toEquiv.symm (a.val.1).replacement)⟩
      (K.image (mapClosingLayer e.toEquiv D)) at mapped
  have pol := Representation.policy_inverse e.toEquiv.symm (a.val.1).rule
  have rep := Representation.replacement_inverse e.toEquiv.symm (a.val.1).replacement
  simp only [Equiv.symm_symm] at pol rep
  rw [pol,rep] at mapped
  obtain ⟨d,c,entry,edges⟩ := a.property.2.2.2.2.2.1 _ mapped
  have components : childComponent B P (a.val.1) e c = K := by
    change (FiniteAlphabet.childEdges B (a.val.1) c).image (mapClosingLayer e.toEquiv.symm D) = K
    rw [edges,Finset.image_image]
    simp only [Function.comp_def,Representation.mapLayer_inverse]
    exact Finset.image_id
  have hist : (child B M live liveCorrect P valid a e d c entry).histories = Q.histories := by
    change (childComponent B P (a.val.1) e c).image P.history = Q.histories
    rw [components]
    exact histories.symm
  obtain ⟨h,mem⟩ := Q.nonempty
  refine ⟨d,c,entry,ExecutableReverse.successor_unique B M (FullExtensions.full B P (pullReduction B P (a.val.1) e (a.property.2.2.1)) (pullRule B P (a.val.1) e)) _ Q ?_ ?_ ⟨h,?_⟩ ⟨h,mem⟩ rfl⟩
  · exact childPosition_next B M live liveCorrect P valid (a.val.1) e (a.property.2.2.1) c _
  · exact ⟨K,component,phase,histories,states⟩
  · change h ∈ (child B M live liveCorrect P valid a e d c entry).histories
    rw [hist]; exact mem

/-- A finite test identifies the concrete successor prescribed at a direction. -/
def Matches (Q : Position I₁ I₂ B.State D) (d : Fin capacity) : Prop :=
  match entry : a.val.2 d with
  | none => False
  | some c => child B M live liveCorrect P valid a e d c entry = Q

instance matchesDecidable (Q : Position I₁ I₂ B.State D) (d : Fin capacity) :
    Decidable (Matches B M live liveCorrect P valid a e Q d) := by
  unfold Matches
  split <;> infer_instance

include liveCorrect valid in
theorem matches_exists (Q : Position I₁ I₂ B.State D)
    (next : (node B M live P valid a e).Successor Q) :
    ∃ d, Matches B M live liveCorrect P valid a e Q d := by
  obtain ⟨d,c,entry,same⟩ := child_complete B M live liveCorrect P valid a e Q next
  refine ⟨d,?_⟩
  unfold Matches
  split
  · rename_i bad
    simp only [entry,Option.some_ne_none] at bad
  · rename_i c' entry'
    have eq : c' = c := Option.some.inj (entry'.symm.trans entry)
    subst c'
    exact same

/-- Search only the finite directions. Its proof of success comes from
coverage of all full components, not an additional model certificate. -/
def direction (Q : Position I₁ I₂ B.State D)
    (next : (node B M live P valid a e).Successor Q) : Fin capacity :=
  (Finset.univ.filter (Matches B M live liveCorrect P valid a e Q)).min' (by
    obtain ⟨d,hd⟩ := matches_exists B M live liveCorrect P valid a e Q next
    exact ⟨d,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hd⟩⟩)

theorem direction_matches (Q : Position I₁ I₂ B.State D)
    (next : (node B M live P valid a e).Successor Q) :
    Matches B M live liveCorrect P valid a e Q (direction B M live liveCorrect P valid a e Q next) :=
  (Finset.mem_filter.mp (Finset.min'_mem _ _)).2

def castPositionIso {Q R : Position I₁ I₂ B.State D} {A : FinitePositions.Position B.State capacity}
    (iso : Representation.Iso (FinitePositions.historyData Q) A.2) (same : Q = R) :
    Representation.Iso (FinitePositions.historyData R) A.2 := same ▸ iso

theorem castPositionIso_history {Q R : Position I₁ I₂ B.State D} {A : FinitePositions.Position B.State capacity}
    (iso : Representation.Iso (FinitePositions.historyData Q) A.2) (same : Q = R) (k : A.Root) :
    ((castPositionIso B iso same).toEquiv.symm k).val = (iso.toEquiv.symm k).val := by cases same; rfl

structure ChildData (Q : Position I₁ I₂ B.State D) where
  direction : Fin capacity
  encoded : FiniteAlphabet.Child B (a.val.1)
  entry : a.val.2 direction = some encoded
  iso : Representation.Iso (FinitePositions.historyData Q) encoded.1.2
  history : ∀ k, (iso.toEquiv.symm k).val = P.history (mapClosingLayer e.toEquiv.symm D (encoded.2 k))

def childData (Q : Position I₁ I₂ B.State D)
    (next : (node B M live P valid a e).Successor Q) : ChildData B live P a e Q := by
  let d := direction B M live liveCorrect P valid a e Q next
  have found := direction_matches B M live liveCorrect P valid a e Q next
  change Matches B M live liveCorrect P valid a e Q d at found
  unfold Matches at found
  split at found
  · exact False.elim found
  · rename_i c entry
    let iso := childIso B M live liveCorrect P valid (a.val.1) e (a.property.2.2.1) c (a.property.2.2.2.2.1 d c entry)
    refine ⟨d,c,entry,castPositionIso B iso found,?_⟩
    intro k
    rw [castPositionIso_history]
    rfl

theorem childData_trace (Q : Position I₁ I₂ B.State D)
    (next : (node B M live P valid a e).Successor Q) (h : Q.Root) (k : P.Root)
    (u : BlockInput I₁ I₂ D) (history : h.val = ((pullReduction B P (a.val.1) e (a.property.2.2.1)).map.edge k).val ++ u.val) :
    let data := childData B M live liveCorrect P valid a e Q next
    data.encoded.2 (data.iso.toEquiv h) = wordScenario ((a.val.1).replacement (e.toEquiv k)) u := by
  dsimp only
  let data := childData B M live liveCorrect P valid a e Q next
  have hh := data.history (data.iso.toEquiv h)
  rw [data.iso.toEquiv.symm_apply_apply] at hh
  have expected : P.history (mapClosingLayer e.toEquiv.symm D
      (wordScenario ((a.val.1).replacement (e.toEquiv k)) u)) = ((pullReduction B P (a.val.1) e (a.property.2.2.1)).map.edge k).val ++ u.val := by
    rw [mapClosingLayer_wordScenario,Position.history,wordScenario_history]
    rfl
  exact (Representation.layerEquiv e.toEquiv.symm D).injective
    (P.history_injective (hh.symm.trans (history.trans expected.symm)))

end Characterisation.ComponentTrees.FiniteDecode
